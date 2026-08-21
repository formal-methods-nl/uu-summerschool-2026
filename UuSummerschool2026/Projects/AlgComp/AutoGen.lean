import Mathlib
import UuSummerschool2026.Projects.AlgComp.AlgComp

/-!
# Automatic generation of cost functions and call graphs

This file automates the constructions from `AlgComp.lean` (following the paper
"The cost of everything" by Wouter Swierstra):

* `#genCost Ind → name` generates a cost function for a call-graph inductive.
* `#genGraph fn → Ind` reifies a function definition into a call-graph inductive,
  then automatically registers it, generates its cost function, and proves it sound.

The call graph of a function `f : A₁ → … → Aₙ → B` is an inductive relation
`Ind : A₁ → … → Aₙ → B → Type`.  Each equation of `f` becomes one constructor:

* the pattern on the left-hand side gives the input indices;
* recursive calls and calls to other functions that already have registered
  graphs become premises;
* the value computed by the outermost call gives the output index.

For example, from

```
def slow_reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => slow_reverse xs ++ [x]
```

the command `#genGraph slow_reverse → SlowReverseGen` produces

```
inductive SlowReverseGen {α : Type} : List α → List α → Type where
| c1 : SlowReverseGen [] []
| c2 {x_1 : α} {xs : List α} {r0 : List α} {r1 : List α} :
    SlowReverseGen xs r0 → LAppendGen r0 [x_1] r1 → SlowReverseGen (x_1 :: xs) r1
```

together with `SlowReverseGen.cost` and `SlowReverseGen.sound`.

Note the order of the `#genGraph` commands matters: a function whose body calls
another function must be processed *after* its callee (or after a manual
`#registerGraph`).
-/

open Lean Elab Command Meta

/-- Normalizes `++` to `List.append`, so that soundness lemmas about
`List.append` apply to goals stated with `++` notation. -/
theorem happend_eq_append {α : Type} (xs ys : List α) : xs ++ ys = List.append xs ys :=
  rfl

namespace GenCost

def runMetaM {α : Type} (x : MetaM α) : CommandElabM α :=
  liftCoreM do
    let (result, _) ← x.run
    return result

/-- Conservative check that `s` can be used as an identifier in generated source. -/
def isValidIdent (s : String) : Bool :=
  !s.isEmpty &&
  (s.front.isAlpha || s.front == '_') &&
  s.all (fun c => c.isAlphanum || c == '_' || c == '\'') &&
  !keywords.contains s
where
  keywords : List String :=
    ["prefix", "infix", "infixl", "infixr", "postfix", "notation", "macro",
     "syntax", "elab", "where", "match", "fun", "let", "if", "then", "else",
     "do", "by", "have", "show", "from", "at", "with", "in", "theorem", "def",
     "lemma", "inductive", "structure", "example", "axiom", "universe",
     "variable", "open", "deriving", "instance", "class", "protected",
     "private", "partial", "noncomputable", "unsafe", "rec"]

/-- Rename the telescope binders whose names cannot be printed as identifiers
(e.g. Lean's internal hygienic names in core definitions such as `List.append`),
and run `k` in the updated context.  Returns the new names, aligned with `vars`.
The renaming is visible to pretty-printing inside `k`. -/
def withSanitizedBinders {α : Type} (vars : Array Expr) (used0 : NameSet)
    (preferred : NameMap String := by exact {})
    (k : Array String → MetaM α) : MetaM α := do
  let mut lctx ← getLCtx
  let mut used := used0
  let mut names : Array String := #[]
  for (v, i) in vars.toList.zipIdx do
    let d := lctx.get! v.fvarId!
    let n := d.userName.toString
    let mut chosen := n
    unless isValidIdent n && !used.contains d.userName do
      match preferred.find? d.userName with
      | some p => chosen := p
      | none =>
        let mut j := 0
        chosen := s!"p{i}"
        while used.contains (Name.mkSimple chosen) do
          chosen := s!"p{i}_{j}"
          j := j + 1
    lctx := lctx.setUserName v.fvarId! (Name.mkSimple chosen)
    used := used.insert (Name.mkSimple chosen)
    names := names.push chosen
  let linsts ← getLocalInstances
  withLCtx lctx linsts (k names)

/-- Parenthesize a printed term unless it is atomic (identifier, numeral,
`[]`, `_`, projections). -/
def parenIfNeeded (str : String) : String :=
  let atomic := str.all fun c =>
    c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '[' || c == ']' || c == '!'
  if atomic then str else "(" ++ str ++ ")"

/-- Pretty-print an expression as source code. -/
def ppString (e : Expr) : MetaM String := do
  let fmt ← PrettyPrinter.ppExpr e
  return fmt.pretty

/-- Format a binder `{nm : t}` (plain concatenation; brace escapes inside
string interpolations do not parse). -/
def mkBinder (nm t : String) : String :=
  "{" ++ nm ++ " : " ++ t ++ "}"

/-- Instantiate universe parameters with level zero, so that types of
universe-polymorphic constants such as `List.append` print concretely. -/
def monoType (ci : ConstantInfo) (t : Expr) : Expr :=
  t.instantiateLevelParams ci.levelParams (ci.levelParams.map (fun _ => Level.zero))

-- ============================================================================
-- Part 1: Analyze call graph inductives — compute cost strings
-- ============================================================================

/-- Is `indName` a call-graph inductive, i.e. does it have an associated cost
function?  `self` is the inductive currently being generated (its cost function
does not exist yet but will reference itself). -/
partial
def isCallGraphInductive (self : Name) (indName : Name) : MetaM Bool := do
  if indName == self then return true
  if indName == ``Nat then return false
  if indName == ``List then return false
  let env ← getEnv
  return env.contains (indName ++ `cost)

def genCostString (self : Name) (ctorName : Name) : MetaM String := do
  let ctorType ← inferType (mkConst ctorName)
  forallTelescope ctorType fun xs _ => do
    let mut parts : Array String := #[]
    let mut explicitIdx : Nat := 0
    for x in xs do
      let localDecl ← getFVarLocalDecl x
      let xType ← inferType x
      if localDecl.binderInfo.isExplicit then
        if xType.isApp then
          let f := xType.getAppFn
          if let .const indName _ := f then
            if ← isCallGraphInductive self indName then
              parts := parts.push (s!"{indName}.cost f{explicitIdx}")
        explicitIdx := explicitIdx + 1
    let subcosts := " + ".intercalate parts.toList
    if subcosts.isEmpty then
      return "1"
    else
      return s!"1 + {subcosts}"

def printAnalysis (inductName : Name) : MetaM Unit := do
  let indVal ← getConstInfoInduct inductName
  for ctorName in indVal.ctors do
    let costStr ← genCostString inductName ctorName
    IO.println s!"  {ctorName.getString!} => {costStr}"

-- ============================================================================
-- Part 2: Generate cost function definitions via string → parse → elaborate
-- ============================================================================

def genExplicitFieldCount (ctorName : Name) : MetaM Nat := do
  let ctorType ← inferType (mkConst ctorName)
  forallTelescope ctorType fun xs _ => do
    let mut count : Nat := 0
    for x in xs do
      let localDecl ← getFVarLocalDecl x
      if localDecl.binderInfo.isExplicit then
        count := count + 1
    return count

/-- Build the binder prefix and `(g : Ind …)` argument of a generated definition
directly from the inductive's own type. -/
def buildTypeSig (inductName : Name) : MetaM String := do
  let ci ← getConstInfo inductName
  forallTelescope (monoType ci ci.type) fun vars _ => do
    withSanitizedBinders vars {} (k := fun names => do
      let mut binders : Array String := #[]
      let mut appNames : Array String := #[]
      for (v, i) in vars.toList.zipIdx do
        let d ← getFVarLocalDecl v
        binders := binders.push (mkBinder names[i]! (← ppString d.type))
        if d.binderInfo.isExplicit then
          appNames := appNames.push names[i]!
      let bindersStr := " ".intercalate binders.toList
      let appStr := " ".intercalate appNames.toList
      return s!"{bindersStr} (g : {inductName} {appStr})")

def buildMatchArm (self : Name) (ctorName : Name) : MetaM String := do
  let costStr ← genCostString self ctorName
  let ctorShortName := ctorName.getString!
  let numExplicit := ← genExplicitFieldCount ctorName
  if numExplicit == 0 then
    return "| ." ++ ctorShortName ++ " => " ++ costStr
  else
    let fieldStr := " ".intercalate (List.range numExplicit |>.map (fun j => s!"f{j}"))
    return "| ." ++ ctorShortName ++ " " ++ fieldStr ++ " => " ++ costStr

def elabStringAsCommand (s : String) : CommandElabM Unit := do
  let env ← liftCoreM <| getEnv
  match Parser.runParserCategory env `command s with
  | .ok stx => elabCommand stx
  | .error e => logError m!"Parse error: {e}\nin:\n{s}"

/-- Elaborate `s` as a command; on failure log a warning and elaborate
`fallback` instead (used to fall back to `sorry`). -/
def elabStringOrFallback (s : String) (fallback : String) : CommandElabM Unit := do
  let env ← liftCoreM <| getEnv
  match Parser.runParserCategory env `command s with
  | .ok stx =>
    try
      elabCommand stx
    catch ex =>
      logWarning m!"auto-generated proof failed ({ex.toMessageData}); falling back to sorry"
      elabStringAsCommand fallback
  | .error e => logError m!"Parse error: {e}"

def genCostFn (inductName : Name) (costFnName : Name) : CommandElabM Unit := do
  let typeSig ← runMetaM <| buildTypeSig inductName
  let indVal : InductiveVal ← runMetaM <| getConstInfoInduct inductName

  let mut arms : Array String := #[]
  for ctorName in indVal.ctors do
    let arm ← runMetaM <| buildMatchArm inductName ctorName
    arms := arms.push arm
  let matchBody := "\n  ".intercalate arms.toList

  let defName := costFnName.toString
  elabStringAsCommand ("def " ++ defName ++ " " ++ typeSig
    ++ " : Nat :=" ++ "\n  match g with" ++ "\n  " ++ matchBody)

-- ============================================================================
-- Part 3: Registry mapping functions to their call-graph inductives
-- ============================================================================

structure GraphEntry where
  /-- The function whose graph this is (used for soundness statements). -/
  fn : Name
  /-- The call-graph inductive. -/
  graph : Name
  /-- Number of explicit arguments of the function. -/
  arity : Nat

deriving Repr

/-- Registry entries are stored in the environment as ordinary definitions
named `GenCost.graphOf_<fn>` (an `initialize`-based registry cannot be accessed
by interpreted code in the same module). -/
def graphEntryPrefix : String := "GenCost.graphOf_"

def entryName (fn : Name) : Name :=
  (graphEntryPrefix ++ fn.toString).toName

/-- Register a mapping from a function to its call-graph inductive by
elaborating a small definition. -/
def registerGraphEntry (e : GraphEntry) : CommandElabM Unit :=
  elabStringAsCommand
    (s!"def {graphEntryPrefix}{e.fn} : GenCost.GraphEntry := ⟨`{e.fn}, `{e.graph}, {e.arity}⟩")

/-- Evaluate a name literal occurring in a definition value. -/
def evalNameExpr : Expr → Option Name
  | .app (.app (.const `Lean.Name.mkStr2 _) (.lit (.strVal a))) (.lit (.strVal b)) =>
      some (Name.mkStr2 a b)
  | .app (.const `Lean.Name.mkStr1 _) (.lit (.strVal a)) => some (Name.mkStr1 a)
  | .lit (.strVal a) => some (Name.mkSimple a)
  | .const n _ => some n
  | _ => none

/-- Evaluate a natural-number literal occurring in a definition value. -/
def evalNatExpr : Expr → Option Nat
  | .lit (Literal.natVal n) => some n
  | .app (.app (.app (.const `OfNat.ofNat _) _) (.lit (Literal.natVal n))) _ => some n
  | _ => none

/-- Decode a registry definition back into a `GraphEntry`. -/
def decodeEntry (ci : ConstantInfo) : Option GraphEntry := do
  let v ← ci.value?
  guard (v.getAppFn.isConstOf ``GenCost.GraphEntry.mk)
  let args := v.getAppArgs
  guard (args.size == 3)
  let fn ← evalNameExpr args[0]!
  let g ← evalNameExpr args[1]!
  match evalNatExpr args[2]! with
  | some ar => some { fn := fn, graph := g, arity := ar }
  | none => none

/-- Look up the registered call-graph inductive of function `fn`. -/
def lookupGraph? (fn : Name) : MetaM (Option GraphEntry) := do
  let env ← getEnv
  let n := entryName fn
  if env.contains n then
    let ci ← getConstInfo n
    return decodeEntry ci
  else
    return none

-- ============================================================================
-- Part 4: Call graph generation
-- ============================================================================

/-- Collect the equation lemmas `fn.eq_i` of a function, sorted by index.
Equation lemmas are generated lazily, so first ask the compiler to produce them. -/
def getEquations (fnName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let pfx := fnName.toString ++ ".eq_"
  let mut eqs : Array (Nat × Name) := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if pfx.isPrefixOf s then
      match (s.drop pfx.length).toNat? with
      | some i => eqs := eqs.push (i, n)
      | none   => pure ()
  -- equation lemmas are generated lazily; force their compilation if missing
  if eqs.isEmpty then
    match ← getEqnsFor? fnName with
    | some ns => return ns
    | none    => return #[]
  return (eqs.qsort (fun a b => a.1 < b.1)).map (·.2)

/-- Number of explicit arguments of the constant `c`. -/
def countExplicit (c : Name) : MetaM Nat := do
  let ci ← getConstInfo c
  let rec go : Expr → Nat → MetaM Nat
    | .forallE _ _ b bi, n => go b (if bi.isExplicit then n + 1 else n)
    | _, n => return n
  go ci.type 0

/-- Given a fully applied call to `c`, extract its explicit arguments. -/
def explicitArgsOfCall (c : Name) (call : Expr) : MetaM (Array Expr) := do
  let ci ← getConstInfo c
  let args := call.getAppArgs
  let rec go (t : Expr) (i : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
    match t with
    | .forallE _ _ b bi =>
      if i ≥ args.size then
        throwError "call to {c} is not fully applied"
      let acc := if bi.isExplicit then acc.push args[i]! else acc
      go b (i + 1) acc
    | _ => return acc
  go ci.type 0 #[]

/-- State threaded through right-hand-side analysis. -/
structure RhsCtx where
  selfFn : Name
  selfGraph : Name
  fresh : Nat := 0
  usedNames : NameSet
  newVars : Array (FVarId × Name × Expr) := #[]   -- fresh result variables
  prems : Array (Array Expr × Expr × Name) := #[] -- premises: (args, result var, graph)

abbrev RhsM := StateT RhsCtx MetaM

/-- Look up the graph entry for the head constant `c`, treating `selfFn` as
registered for `selfGraph`. -/
def entryFor? (c : Name) : RhsM (Option GraphEntry) := do
  match ← lookupGraph? c with
  | some g => return some g
  | none =>
    let ctx ← get
    if c == ctx.selfFn then
      let ar ← liftM <| countExplicit c
      return some { fn := c, graph := ctx.selfGraph, arity := ar }
    return none

mutual

/-- If `e` is a call to a function with a registered graph, replace it by a
fresh result variable and record the corresponding premise and variable. -/
partial def tryRewriteCall (e : Expr) : RhsM (Option Expr) := do
  let ew ← whnf e
  match ew.getAppFn with
  | .const c _ =>
    match ← entryFor? c with
    | some entry => do
        let argEs' ← (← explicitArgsOfCall c ew).mapM rewriteCalls
        let ty ← inferType ew
        -- allocate a fresh result-variable name and id
        let ctx ← get
        let mut k := ctx.fresh
        let mut rName := s!"r{k}"
        while ctx.usedNames.contains (Name.mkSimple rName) do
          k := k + 1
          rName := s!"r{k}"
        let id ← mkFreshFVarId
        modify fun st =>
          { st with fresh := k + 1,
                    usedNames := st.usedNames.insert (Name.mkSimple rName),
                    newVars := st.newVars.push (id, Name.mkSimple rName, ty),
                    prems := st.prems.push (argEs', .fvar id, entry.graph) }
        return some (.fvar id)
    | none => return none
  | _ => return none

/-- Rewrite every call to a function with a registered graph in `e` into a
fresh variable, recording premises along the way. -/
partial def rewriteCalls (e : Expr) : RhsM Expr := do
  match ← tryRewriteCall e with
  | some r => return r
  | none =>
    match e with
    | .app f a => return mkApp (← rewriteCalls f) (← rewriteCalls a)
    | _ => return e

end

/-- Information about one generated constructor. -/
structure CtorInfo where
  name : String
  varNames : Array String     -- pattern variables (for induction case naming)
  rNames : Array String       -- fresh result variables
  premHypNames : Array String -- hypothesis names in the induction case
  premGraphs : Array Name     -- graph of each premise

/-- Compute the parameters of the graph inductive from the function's type:
all implicit binders before the first explicit one (e.g. `{α : Type}`). -/
def fnParams (fnName : Name) : MetaM (Array (String × String)) := do
  let ci ← getConstInfo fnName
  forallTelescope (monoType ci ci.type) fun vars _ => do
    withSanitizedBinders vars {} (k := fun names => do
      let mut acc : Array (String × String) := #[]
      for (v, i) in vars.toList.zipIdx do
        let d ← getFVarLocalDecl v
        unless d.binderInfo.isExplicit do
          acc := acc.push (names[i]!, ← ppString d.type)
      return acc)

/-- The explicit argument types plus the result type of the function;
these become the indices of the graph inductive. -/
def fnIndexTypes (fnName : Name) : MetaM (Array String) := do
  let ci ← getConstInfo fnName
  forallTelescope (monoType ci ci.type) fun vars body => do
    withSanitizedBinders vars {} (k := fun _ => do
      let mut acc : Array String := #[]
      for v in vars do
        let d ← getFVarLocalDecl v
        if d.binderInfo.isExplicit then
          acc := acc.push (← ppString d.type)
      acc := acc.push (← ppString body)
      return acc)

/-- Map from the original user names of the function's implicit-prefix
parameters to their sanitized names, so that equation binders referring to
the same variables print consistently with the generated inductive header. -/
def fnParamPreferred (fnName : Name) : MetaM (NameMap String) := do
  let ci ← getConstInfo fnName
  let prefs ← forallTelescope (monoType ci ci.type) fun vars _ => do
    let mut acc : Array Name := #[]
    for v in vars do
      let d ← getFVarLocalDecl v
      unless d.binderInfo.isExplicit do
        acc := acc.push d.userName
    return acc
  let sannames := (← fnParams fnName).map (·.1)
  let mut m : NameMap String := {}
  for (o, sn) in prefs.toList.zip sannames.toList do
    m := m.insert o sn
  return m

/-- Turn one equation lemma into a constructor of the call-graph inductive. -/
def elabEquation (fnName graphName : Name) (paramNames : NameSet)
    (eqIdx : Nat) (eqName : Name) : MetaM (String × CtorInfo) := do
  let ci ← getConstInfo eqName
  forallTelescope (monoType ci ci.type) fun vars body => do
    -- collect used names, then make all binder names printable;
    -- binders corresponding to the inductive's parameters are renamed to
    -- exactly the parameter names via `preferred`
    let mut baseUsed : NameSet := {}
    for v in vars do
      baseUsed := baseUsed.insert (← getFVarLocalDecl v).userName
    -- decompose the equation
    unless body.isAppOf ``Eq do
      throwError "equation {eqName} is not an equality"
    let args := body.getAppArgs
    if args.size < 3 then
      throwError "unexpected equation shape for {eqName}"
    let lhs := args[1]!
    let rhs := args[2]!
    unless lhs.getAppFn.isConstOf fnName do
      throwError "left-hand side of {eqName} does not start with {fnName}"
    -- everything below pretty-prints, so run it with sanitized binder names
    let preferred ← fnParamPreferred fnName
    return ← withSanitizedBinders vars baseUsed preferred fun _ => do
    let patterns ← explicitArgsOfCall fnName lhs
    -- classify the telescope variables
    let mut varInfos : Array (String × String) := #[]
    for v in vars do
      let d ← getFVarLocalDecl v
      let occurs :=
        patterns.any (·.containsFVar v.fvarId!) || rhs.containsFVar v.fvarId!
      if occurs && !paramNames.contains d.userName then
        varInfos := varInfos.push (d.userName.toString, ← ppString d.type)
    -- analyze the right-hand side
    let (outExpr, res) ← StateT.run (rewriteCalls rhs)
        { selfFn := fnName, selfGraph := graphName, usedNames := baseUsed }
    -- extend the local context with the fresh result variables so that all
    -- pieces can be pretty-printed uniformly
    let lctx := res.newVars.foldl
      (fun l (id, nm, ty) => l.mkLocalDecl id nm ty) (← getLCtx)
    let linsts ← getLocalInstances
    return ← withLCtx lctx linsts do
      let outStr := parenIfNeeded (← ppString outExpr)
      let ctorName := s!"c{eqIdx + 1}"
      let mut binders : Array String := #[]
      for (nm, t) in varInfos do
        binders := binders.push (mkBinder nm t)
      for (_, nm, ty) in res.newVars do
        binders := binders.push (mkBinder nm.toString (← ppString ty))
      let patStrs ← patterns.mapM fun p => parenIfNeeded <$> ppString p
      let patsStr := " ".intercalate patStrs.toList
      let concl := s!"{graphName} {patsStr} {outStr}"
      let mut hyps : Array String := #[]
      for i in [:res.prems.size] do
        hyps := hyps.push s!"f{i}"
      let mut premParts : Array String := #[]
      for (prem, i) in res.prems.toList.zipIdx do
        let (argEs, r, g) := prem
        let argStrs ← argEs.mapM fun a => parenIfNeeded <$> ppString a
        let rStr := parenIfNeeded (← ppString r)
        let prem := g.toString ++ " " ++ " ".intercalate argStrs.toList ++ " " ++ rStr
        premParts := premParts.push s!"(f{i} : {prem})"
      let premisePart :=
        if premParts.isEmpty then ""
        else " → ".intercalate premParts.toList ++ " → "
      let binderPart :=
        if binders.isEmpty then "" else " ".intercalate binders.toList ++ " "
      let ctor := s!"| {ctorName} {binderPart}: {premisePart}{concl}"
      let info : CtorInfo := {
        name := ctorName
        varNames := varInfos.map (·.1)
        rNames := res.newVars.map (fun (_, nm, _) => nm.toString)
        premHypNames := hyps
        premGraphs := res.prems.map (·.2.2)
      }
      return (ctor, info)

/-- Build the tactic block for one constructor case of the soundness proof.
The case arguments are read off the *actual* generated inductive, so Lean's
automatic parameter promotion does not upset the naming. -/
def buildInductionCase (fnName graphName : Name) (numParams : Nat)
    (ctorName : Name) (extra : Array String) : MetaM String := do
  let ci ← getConstInfo ctorName
  forallTelescope (monoType ci ci.type) fun vars _ => do
    withSanitizedBinders vars {} (k := fun names => do
      -- all constructor fields are named first (in declaration order),
      -- followed by one inductive hypothesis per recursive premise
      let mut argNames : Array String := #[]
      let mut ihNames : Array String := #[]
      -- bridge between `++` notation and `List.append` without looping
      -- against the default simp set
      let mut lemmas : Array String := extra
      lemmas := lemmas.push "happend_eq_append"
      lemmas := lemmas.push "-List.append_eq"
      let mut premIdx : Nat := 0
      for (v, i) in vars.toList.zipIdx do
        if i < numParams then continue
        let nm := names[i]!
        let d ← getFVarLocalDecl v
        let ty ← whnf d.type
        if ty.getAppFn.isConstOf graphName then
          -- recursive premise of the graph itself: contributes an ih
          let ih := s!"ih{premIdx}"
          argNames := argNames.push nm
          ihNames := ihNames.push ih
          lemmas := lemmas.push ih
          premIdx := premIdx + 1
        else
          argNames := argNames.push nm
          -- a premise belonging to another registered graph contributes
          -- its soundness lemma
          match ty.getAppFn with
          | .const c _ =>
            if c != graphName && c != fnName then
              let soundName := (s!"{c}.sound" : String).toName
              if (← getEnv).contains soundName then
                lemmas := lemmas.push s!"{c}.sound {nm}"
          | _ => pure ()
      argNames := argNames.append ihNames
      let simpStr := ", ".intercalate lemmas.toList
      let argStr := " ".intercalate argNames.toList
      let shortName := (ctorName.toString.splitOn ".").getLast!
      return s!"  | @{shortName} {argStr} =>\n    first | rfl | simp [{simpStr}]")

/-- Generate the soundness lemma `{graph}.sound : {graph} xs ys → {fn} xs = ys`.
We follow the hand-written proofs: base cases are closed by `rfl`/`simp`,
step cases by `simp` with the inductive hypotheses and the soundness lemmas
of the callee graphs.  Several tactic variants are attempted in order. -/
def genSoundness (fnName graphName : Name) (params : Array (String × String))
    (idxTypes : Array String) : CommandElabM Unit := do
  let k := idxTypes.size - 1  -- last index is the output
  let mut binders : Array String := #[]
  for (nm, t) in params do
    binders := binders.push (mkBinder nm t)
  let mut idxVars : Array String := #[]
  for i in [:idxTypes.size] do
    idxVars := idxVars.push s!"x{i}"
    binders := binders.push (mkBinder s!"x{i}" idxTypes[i]!)
  let inputs := " ".intercalate (idxVars.take k).toList
  let outVar := idxVars[k]!
  let idxVarsStr := " ".intercalate idxVars.toList
  binders := binders.push s!"(g : {graphName} {idxVarsStr})"

  let header := "theorem " ++ graphName.toString ++ ".sound " ++
    " ".intercalate binders.toList ++ " : " ++
    fnName.toString ++ " " ++ inputs ++ " = " ++ outVar ++ " := by\n" ++
    "  induction g with\n"
  let fallback := "theorem " ++ graphName.toString ++ ".sound " ++
    " ".intercalate binders.toList ++ " : " ++
    fnName.toString ++ " " ++ inputs ++ " = " ++ outVar ++ " := sorry"

  let mkStmt (extra : Array String) : CommandElabM String := do
    let indVal ← runMetaM <| getConstInfoInduct graphName
    let mut cases : Array String := #[]
    for ctorName in indVal.ctors do
      let cse ← runMetaM <|
        buildInductionCase fnName graphName indVal.numParams ctorName extra
      cases := cases.push cse
    return "set_option maxRecDepth 8000 in\n" ++ header ++
      "\n".intercalate cases.toList

  -- attempt 1: unfold the function itself
  let stmt1 ← mkStmt #[fnName.toString]
  -- attempt 2: rely on the default simp set (e.g. List.nil_append/cons_append)
  let stmt2 ← mkStmt #[]

  IO.println stmt1
  try
    elabStringAsCommand stmt1
  catch _ =>
    logInfo m!"primary soundness proof failed for {graphName}; trying fallback"
    IO.println stmt2
    elabStringOrFallback stmt2 fallback

/-- Generate the call-graph inductive for `fnName`, register it, generate its
cost function, and prove its soundness lemma. -/
def genGraphCore (fnName : Name) (graphName : Name) : CommandElabM Unit := do
  let eqns ← runMetaM <| getEquations fnName
  if eqns.isEmpty then
    throwError "{fnName} has no equation lemmas; cannot generate a call graph"

  -- parameters of the inductive, taken from the function's own type
  let params ← runMetaM <| fnParams fnName
  let paramNames : NameSet :=
    params.foldl (init := {}) fun acc (nm, _) => acc.insert (Name.mkSimple nm)
  let paramStr := " ".intercalate (params.map (fun (nm, t) => mkBinder nm t)).toList

  -- index types: the explicit argument types plus the result type of the function
  let idxTypes ← runMetaM <| fnIndexTypes fnName

  -- one constructor per equation
  let mut ctors : Array String := #[]
  for (eqName, i) in eqns.toList.zipIdx do
    let (ctor, _) ← runMetaM <| elabEquation fnName graphName paramNames i eqName
    ctors := ctors.push ctor

  let cmd := "inductive " ++ graphName.toString ++ " " ++ paramStr
    ++ " : " ++ " → ".intercalate (idxTypes.toList ++ ["Type"]) ++ " where\n"
    ++ "\n".intercalate ctors.toList
  IO.println cmd
  elabStringAsCommand cmd

  -- register the graph so other functions can use it
  let arity ← runMetaM <| countExplicit fnName
  registerGraphEntry { fn := fnName, graph := graphName, arity }

  -- generate the cost function
  try
    genCostFn graphName (graphName ++ `cost)
  catch ex =>
    logWarning m!"could not generate cost function for {graphName}: {ex.toMessageData}"

  -- prove soundness: Ind xs ys → fn xs = ys
  -- (first make sure the `++`/`List.append` bridge lemma exists in the current
  -- file; it is declared in AutoGen.lean itself, but `#genGraph` may be run
  -- anywhere)
  unless (← getEnv).contains `happend_eq_append do
    elabStringAsCommand
      "theorem happend_eq_append {α : Type} (xs ys : List α) : xs ++ ys = List.append xs ys := rfl"
  genSoundness fnName graphName params idxTypes

end GenCost

-- ============================================================================
-- Commands
-- ============================================================================

open GenCost

def analyzeFnDef (fnName : Name) : MetaM Unit := do
  let defInfo ← getConstInfoDefn fnName
  IO.println s!"Function: {fnName}"
  let typeFmt ← PrettyPrinter.ppExpr defInfo.type
  IO.println s!"  type: {typeFmt.pretty}"
  let valFmt ← PrettyPrinter.ppExpr defInfo.value
  IO.println s!"  body: {valFmt.pretty}"

syntax "#analyzeCost " ident : command
elab_rules : command
  | `(command| #analyzeCost $name:ident) => do
    runMetaM <| GenCost.printAnalysis name.getId

syntax "#genCost " ident " → " ident : command
elab_rules : command
  | `(command| #genCost $indName:ident → $fnName:ident) => do
    GenCost.genCostFn indName.getId fnName.getId

syntax "#analyzeDef " ident : command
elab_rules : command
  | `(command| #analyzeDef $name:ident) => do
    runMetaM <| analyzeFnDef name.getId

syntax "#registerGraph " ident " → " ident : command
elab_rules : command
  | `(command| #registerGraph $fnName:ident → $indName:ident) => do
    let arity ← runMetaM <| GenCost.countExplicit fnName.getId
    GenCost.registerGraphEntry { fn := fnName.getId, graph := indName.getId, arity }

syntax "#genGraph " ident " → " ident : command
elab_rules : command
  | `(command| #genGraph $fnName:ident → $indName:ident) => do
    GenCost.genGraphCore fnName.getId indName.getId

-- ============================================================================
-- Demo: Analyze + generate + verify
-- ============================================================================

-- Analyze existing (hand-written) call graphs
#analyzeCost LAppend
#analyzeCost SlowReverse
#analyzeCost FastReverseAcc
#analyzeCost FastReverse

-- Generate cost functions for the hand-written graphs
#genCost LAppend → LAppend_costGen
#genCost FastReverseAcc → FastReverseAcc_costGen
#genCost SlowReverse → SlowReverse_costGen
#genCost FastReverse → FastReverse_costGen

-- Verify types match hand-written versions
#check @LAppend_costGen
#check @LAppend.cost
#check @FastReverseAcc_costGen
#check @FastReverseAcc.cost
#check @SlowReverse_costGen
#check @SlowReverse.cost
#check @FastReverse_costGen
#check @FastReverse.cost

-- Analyze function definitions
#analyzeDef slow_reverse
#analyzeDef fast_reverse_acc
#analyzeDef fast_reverse

-- ============================================================================
-- Demo: fully automatic call graph generation
-- ============================================================================

-- Step 1: the graph of List.append (needed by slow_reverse).
-- This also registers List.append in the graph registry.
#genGraph List.append → LAppendGen

-- Step 2: the accumulating reverse; registers itself.
#genGraph fast_reverse_acc → FastReverseAccGen

-- Step 3: the wrapper calling fast_reverse_acc.
#genGraph fast_reverse → FastReverseGen

-- Step 4: slow reverse, whose body calls both itself and List.append.
#genGraph slow_reverse → SlowReverseGen

-- Inspect the generated definitions
#print LAppendGen
#print FastReverseAccGen
#print FastReverseGen
#print SlowReverseGen

-- The generated soundness lemmas
#check @LAppendGen.sound
#check @FastReverseAccGen.sound
#check @FastReverseGen.sound
#check @SlowReverseGen.sound

-- The generated cost functions
#check @LAppendGen.cost
#check @FastReverseAccGen.cost
#check @FastReverseGen.cost
#check @SlowReverseGen.cost
