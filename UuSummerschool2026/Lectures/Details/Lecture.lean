import Mathlib

/-!
# Some details: soundness, sorts, namespaces, defeq and computability

In this
lecture we take a step back and look at some of the machinery that makes this work, and at
a few places where it leaks into everyday formalisation. We will cover:

- relation between type theory and set theory
- sorts: `Prop` and `Type u`
- modules, namespaces and dot notation
- definitional equality, "defeq abuse" and transparency
- computable functions and the axiom of choice
-/

section SetsAndTypes

/-!
## Type theory read in naive set theory

Lean is based on dependent type theory, specifically the calculus
of inductive constructions. But almost everyone learns type theory by translating it into
the naive set theory they already know, and that translation is actually a theorem
of mathematics, usually called *soundness*.

The dictionary is roughly:

| type theory                               | set theory                    |
| ----------------------------------------- | ----------------------------- |
| a type `α : Type`                         | a set `A`                     |
| a term `a : α`                            | an element `a ∈ A`            |
| the function type `α → β`                 | the function set `B^A`        |
| the product type `α × β`                  | the product `A × B`           |
| the sum type `α ⊕ β`                      | a disjoint union `A ⊔ B`      |
| a dependent function type `(i : ι) → β i` | an indexed product `∏ i, B i` |
| a sigma type `Σ i, β i`                   | an indexed union `∐ i, B i`   |
| `Set α`, i.e. `α → Prop`                  | the power set `𝒫 A`           |
| a subtype `{x : α // p x}`                | a subset `{x ∈ A : p x}`      |
| `Quotient`                                | a quotient `A/∼`              |
| `Prop`                                    | the truth values `{0, 1}`     |
| `Type u`                                  | an inaccessible cardinal      |


This interpretation fron type theory to set theory gives us the following:

  if ZFC + "there are `n` inaccessible cardinals" (for every `n`) is consistent,
  then Lean's type theory is consistent.
-/

end SetsAndTypes

section Sorts

/-!
## Sorts: `Prop` and `Type u`

Every expression in Lean has a type, and types are themselves expressions, so they have
types too. The types of types are called *sorts*.
-/

#check (2 : ℕ)
#check ℕ
#check Type
#check Type 1

/-
So `2 : ℕ`, `ℕ : Type`, `Type : Type 1`, `Type 1 : Type 2`, and so on. This tower is
indexed by *universe levels* `0, 1, 2, ...`, and there is one more sort sitting below
everything: `Prop`, the sort of propositions.
-/

#check Prop
#check (2 + 2 = 4 : Prop)

/-
Internally there is a single family `Sort u`, and `Prop` and `Type u` are notations:

- `Prop` is `Sort 0`,
- `Type u` is `Sort (u + 1)`.
-/

example : Prop = Sort 0 := rfl
example : Type = Sort 1 := rfl

/-
This hierarchy `Sort 0 : Sort 1 : Sort 2 : ...` is what preserves consistency, as
`Type : Type` would cause paradoxes (Girard's paradox). Nonetheless, we can make definitions
in arbitrary universes by using *universe polymorphic* functions, that use universe
variables.
-/

universe u

example : Type u = Sort (u + 1) := rfl

def MyId (α : Sort u) (a : α) : α := a

#check @MyId

/- It applies to propositions (`Sort 0`), to types (`Sort 1`), to types of types, ... -/
example (p : Prop) (hp : p) : p := MyId p hp
example (n : ℕ) : ℕ := MyId ℕ n
example : Type := MyId Type ℕ

/-!
### What makes `Prop` special

`Prop` is not just "the bottom of the tower"; it behaves differently in two important ways.

**1. Proof irrelevance.** Any two proofs of the same proposition are definitionally equal.
-/

example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl
-- example (A : Type) (n m : A) : n = m := rfl -- fails, of course

/-
**2. Impredicativity.** A `∀` over a family of propositions is again a proposition, no
matter what we quantify over. This is not the case for other sorts.
-/

#check ∀ p : Prop, p → p
#check ∀ α : Type, α → α

/-!
### `Prop` and elimination

Because proofs are irrelevant, we are (mostly) not allowed to extract *data* from a proof.
-/

example (h : ∃ n : ℕ, n > 3) : ∃ n : ℕ, n > 2 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by omega⟩

-- example (h : ∃ n : ℕ, n > 3) : ℕ := by
--   obtain ⟨n, hn⟩ := h
--   exact n

/-
The data-carrying analogue of `∃` is the sigma type `Σ`, which lives in `Type`, and there
the projection is perfectly fine.
-/
def myexample (h : Σ' n : ℕ, (n > 3)) : ℕ := by
  obtain ⟨n, hn⟩ := h
  exact n

/-
There *is* a way to get a natural number out of an existential statement anyway, namely
`Exists.choose`, but it uses the axiom of choice and the result is *noncomputable*.
-/
#check @Exists.choose

noncomputable def myexample' (h : ∃ n : ℕ, n > 3) : ℕ := by
  choose n nh using h
  exact n

#eval myexample ⟨4, by simp⟩
-- #eval myexample' ⟨4, by simp⟩ --errors

/-
The choice between `Exists` and `Sigma` is therefore mostly representing mathematics
faithfully, since Mathlib assumes the axiom of choice everywhere. Does being even or
being finite carry data?
-/

end Sorts

section Namespaces

/-!
## Modules, namespaces and dot notation

### Modules

A *module* is a single `.lean` file, and `import` makes the contents of another module
available. Imports are transitive and may not be cyclic; `import Mathlib` at the top of
this file pulls in all of Mathlib. Note that `import` statements must come first in a
file, before any other command.

Names in Lean are hierarchical: `Nat.succ_le_of_lt` is the name `succ_le_of_lt` in the
namespace `Nat`. Namespaces have nothing to do with which file a declaration lives in;
they are purely a naming device.

### Namespaces

The `namespace ... end` commands prefix every declaration inside them.
-/

namespace Playground

/-- A point in the rational plane. -/
structure Point where
  x : ℚ
  y : ℚ

/- The full name of `Point` is `Playground.Point`. -/
#check Point
#check Playground.Point

/-
Inside the namespace, we may refer to `Point` by its short name; outside we cannot, unless
we `open` the namespace. `open ... in` opens a namespace for a single command only.
-/

def origin : Point := ⟨0, 0⟩

end Playground

/- Outside the namespace the short name is unknown: -/
-- #check origin -- unknown identifier

#check Playground.origin

open Playground in
#check origin

/-
Opening a namespace only affects name *resolution*; it does not move anything.
`section ... end` is the same idea for `variable`s, `open`s and options, without touching
names.
-/

section
variable (p : Playground.Point)

/-- Both `p` from the `variable` command and the `open` are only in scope in this section. -/
example : ℚ := p.x

end

/-!
### Protected and private

`protected` declarations are *not* brought into scope by `open`; this is used when the
short name would clash with something common (compare `Nat.add` and `Nat.rec`).
`private` declarations are only visible inside the current file.
-/

namespace Playground

protected def Point.sum (p : Point) : ℚ := p.x + p.y
private def secret : ℕ := 42

end Playground

open Playground

-- #check Point.sum -- works
-- #check sum -- fails: `Point.sum` is protected, and there is no `Playground.sum`
#check Playground.Point.sum

/-!
### Dot notation

Dot notation (also called *generalised field notation*) is what makes Lean code readable.
If `x : T ...` and there is a declaration `T.f`, then `x.f a b` means `T.f ... x ... a b`,
where `x` is placed at the first explicit argument whose type has head `T`.
-/

namespace Playground

/-- The squared distance of a point to the origin. -/
def Point.normSq (p : Point) : ℚ := p.x ^ 2 + p.y ^ 2

/-- Scaling a point. Note that the `Point` argument is *not* the first one. -/
def Point.scale (r : ℚ) (p : Point) : Point := ⟨r * p.x, r * p.y⟩

example (p : Point) : ℚ := p.normSq

/- `p.scale 2` elaborates to `Point.scale 2 p`: `p` fills the first `Point`-typed slot. -/
example (p : Point) : Point.scale 2 p = p.scale 2 := rfl

end Playground

/-
The same mechanism works for structure projections (`p.x` is `Point.x p`) and, most
importantly, for *proofs*: the relevant namespace is the head symbol of the *statement*.
So for `h : a ∣ b` the statement is `Dvd.dvd a b`, and `h.trans` resolves to
`Dvd.dvd.trans`. Here are some typical examples.
-/

example (l : List ℕ) : ℕ := l.length
example (p q : Prop) (h : p ↔ q) (hp : p) : q := h.mp hp
example (n : ℕ) (h : 0 < n) : n ≠ 0 := h.ne'
example (a b c : ℕ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := h₁.trans h₂

/-
Dot notation is also the reason mathlib's naming convention matters so much: a lemma about
`Function.Injective` is called `Function.Injective.comp`, precisely so that you can write
`hf.comp hg`.
-/
example (α β γ : Type) (f : α → β) (g : β → γ) (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (g ∘ f) :=
  hg.comp hf

end Namespaces

section Defeq

/-!
## Definitional equality, defeq abuse and transparency

Lean has two notions of equality:

- *propositional* equality `a = b`, an ordinary proposition that we prove by `rw`, `simp`,
  `ring`, ...;
- *definitional* equality, a judgement built into the kernel: `a` and `b` become
  syntactically equal after unfolding definitions, β/η-reducing, and computing.

The tactic `rfl` (and the term `rfl`) closes a goal `a = b` exactly when `a` and `b` are
definitionally equal. Everything the kernel can compute is therefore "free".
-/

example : 2 + 2 = 4 := rfl
example : (List.range 5).length = 5 := rfl
example (n : ℕ) : n + 0 = n := rfl

/- But definitional equality is not magic: it can only *compute*, not reason. -/
-- example (n : ℕ) : 0 + n = n := rfl -- fails: `0 + n` is stuck on the variable `n`
example (n : ℕ) : 0 + n = n := by omega

/-
Many definitions unfold to something you already know, and so `rfl` proves statements that
look nontrivial. In `ℕ`, `n < m` is *by definition* `n + 1 ≤ m`:
-/
example (n m : ℕ) : (n < m) = (n + 1 ≤ m) := rfl

/- Structures satisfy eta, so a pair is definitionally the pair of its components: -/
example (α β : Type) (p : α × β) : (p.1, p.2) = p := rfl

/- And `¬ p` is by definition `p → False`, as we saw in the logic lecture: -/
example (p : Prop) : ¬ p ↔ (p → False) := Iff.rfl

/-!
### Defeq abuse

*Defeq abuse* is using such an unfolding in a proof instead of the intended API. It works,
but it makes the proof depend on the *implementation* of a definition rather than on its
*interface*. Here is the same statement proven twice:
-/

/-- Abusing that `Set α` is `α → Prop` and that `⊆` unfolds to an implication. -/
example (α : Type) (s : Set α) : s ⊆ s := fun _ hx ↦ hx

/-- Using the API. -/
example (α : Type) (s : Set α) : s ⊆ s := subset_refl s

/-
The first proof is shorter, so why is it worse? Because if the definition of `Set` or of
`⊆` ever changes (say `Set` becomes a structure), the second proof keeps working and the
first breaks. Some pointer for defeq abuse:

- breaks when definitions are refactored;
- produces terrible error messages when it breaks;
- can be very slow, because the elaborator has to unfold a lot to check it;
- does not tell the reader *why* the statement is true.

A good rule of thumb: use `rfl` when the two sides are the same by *computation*
(`2 + 2 = 4`), or when you are proving the very lemma that exposes the definition. Do not
use it to silently jump between two mathematically different-looking statements.
-/

/-!
### Transparency

Not all definitions are equally eager to unfold. Each declaration has a *reducibility
setting*, and each elaboration task runs at a *transparency* level:

- `@[reducible]` (this is what `abbrev` produces): unfolded even at `reducible`
  transparency, which is what `simp`'s matching and (nearly, see below) typeclass
  inference use;
- default (plain `def`): unfolded at `default` transparency, e.g. by `rfl`, `exact`,
  `decide`;
- `@[irreducible]`: not unfolded automatically at all.
-/

def double (n : ℕ) : ℕ := n + n

abbrev double_r (n : ℕ) : ℕ := n + n
@[reducible] def double_r' (n : ℕ) : ℕ := n + n

@[irreducible] def double_i (n : ℕ) : ℕ := n + n

/- `rfl` runs at default transparency, so it unfolds `double`. -/
example (n : ℕ) : double n = n + n := rfl

/- At `reducible` transparency it does not: -/
-- example (n : ℕ) : double n = n + n := by with_reducible rfl -- fails
example (n : ℕ) : double_r' n = n + n := by with_reducible rfl

-- example (n : ℕ) : double_i n = n + n := by rfl -- fails
example (n : ℕ) : double_i n = n + n := by simp [double_i]

/-
Importantly, typeclass resolution runs at its own transparency level, sitting between
`reducible` and `default`: it unfolds `@[reducible]` definitions and instances, but *not*
plain `def`s. So a definition can be defeq to another type and still inherit none of its
instances.
-/

def MyNat := ℕ

/- `MyNat` and `ℕ` are definitionally equal at `default` transparency: -/
example : MyNat = ℕ := rfl

/- But instance search does not unfold `MyNat`, so `ℕ`'s instances are invisible to it: -/
-- example : Add MyNat := inferInstance -- fails
-- example (n m : MyNat) : MyNat := n + m -- fails

/- With `abbrev`, i.e. `@[reducible]`, they come through: -/
abbrev MyNat' := ℕ

example : Add MyNat' := inferInstance
example (n m : MyNat') : MyNat' := n + m


/-!
### Computation in the kernel can be expensive

`decide` evaluates a `Decidable` instance and hands the result to the kernel. That is
wonderful for small finite checks and catastrophic for large ones.
-/

#synth Decidable (Nat.Prime _)

example : Nat.Prime 7 := by decide

/- This one exhausts the recursion depth: `Nat.decidablePrime` is not efficient enough. -/
-- example : Nat.Prime 104729 := by decide

/- `native_decide` relies instead on a computation by the compiler, which expands the
trusted codebase. -/
lemma myprime : Nat.Prime 104729 := by native_decide

#print axioms myprime


end Defeq

section Computability

/-!
## Computable functions and the axiom of choice

Lean is a programming language as well as a proof assistant: definitions that only use
computable ingredients can actually be run.
-/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 30
#eval (List.range 10).map fib

/-!
### The three axioms

Lean's kernel is small, and everything in mathlib rests on exactly three axioms.
`#print axioms` tells you which ones a declaration uses.
-/

#print axioms fib
#print axioms Nat.add_comm

#check @propext          -- propositional extensionality
#check @Quot.sound       -- quotients respect the relation
#check @Classical.choice -- the axiom of choice

/-
`propext` and `Quot.sound` are harmless computationally: they only equate things that the
evaluator already treats as interchangeable. `Classical.choice` is different: it produces
an element of `α` out of a mere proof of `Nonempty α`. There is no way to run that.
-/

/-- Any declaration that uses choice must be marked `noncomputable`. -/
noncomputable def anElement (α : Type) (h : Nonempty α) : α := Classical.choice h

/- Similarly for `Exists.choose`, which is choice applied to an existential statement. -/
#check @Classical.choose
#check @Classical.choose_spec

noncomputable def someBigNat (h : ∃ n : ℕ, n > 3) : ℕ := h.choose

example (h : ∃ n : ℕ, n > 3) : someBigNat h > 3 := h.choose_spec

/- Without `noncomputable`, Lean complains: -/
-- def someBigNat' (h : ∃ n : ℕ, n > 3) : ℕ := h.choose
-- failed to compile definition, consider marking it as 'noncomputable'

/-
Note that this is *not* a restriction on what we can prove: `someBigNat` exists as a
mathematical function, we simply cannot execute it. `#eval` is the only thing we lose.
-/

/-!
### Decidability

The computational counterpart of a proposition is a `Decidable` instance: a *procedure*
that decides it. This is what makes `if ... then ... else` work.
-/

#check @Decidable

def sign (n : ℤ) : ℤ := if n < 0 then -1 else if n = 0 then 0 else 1

#eval sign (-7)

/-
For an arbitrary proposition there is no such procedure, so this fails to elaborate:
-/
-- def indicator (p : Prop) : ℕ := if p then 1 else 0 -- failed to synthesize `Decidable p`

/-
Classically, every proposition is decidable — this is Diaconescu's theorem, deriving
excluded middle from choice — but the resulting instance computes nothing.
-/

#check @Classical.propDecidable
#print axioms Classical.em

open Classical in
noncomputable def indicator (p : Prop) : ℕ := if p then 1 else 0

/-
In mathlib this pattern appears constantly; `Classical.dec`, `Classical.byCases` and the
`classical` tactic all do the same thing. Inside a proof it is entirely free, since proofs
are never evaluated:
-/
example (p : Prop) : p ∨ ¬ p := by
  classical
  by_cases h : p
  · exact Or.inl h
  · exact Or.inr h

/-!
### Where this shows up in practice

Large parts of mathematics are simply not computable, and mathlib does not pretend
otherwise. Real numbers are the standard example: `ℝ` is a quotient of Cauchy sequences,
and its order — hence almost everything built on it — needs choice.
-/

#print axioms Real.sqrt
#print axioms Function.invFun

/-
Consequently many familiar functions are `noncomputable`, and files doing analysis often
start with `noncomputable section` (as the algebra lecture did) so that every definition
in the file is allowed to use them.
-/

noncomputable def myDist (x y : ℝ) : ℝ := √((x - y) ^ 2)

/-
By contrast, everything about `ℕ`, `ℤ`, `ℚ`, `List`, `Finset`, ... is genuinely
executable, which is why `decide`, `norm_num` and `#eval` are so useful there.
-/

#eval (Finset.range 10).sum id
#eval Nat.gcd 1071 462
#eval (2 : ℚ) / 3 + 1 / 6

/-
Finally: a `noncomputable` definition is not a second-class citizen. It is only the code
generator that refuses to produce a program; the logic is unaffected, and `#print axioms`
is the honest way to see what a theorem really depends on.
-/

#print axioms Real.sqrt_nonneg

end Computability
