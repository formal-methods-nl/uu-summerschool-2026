import Mathlib
import UuSummerschool2026.Projects.AlgComp.AutoGen

/-!
# Verification suite for the automatic call-graph / cost-function generation

* runtime evaluation of every generated cost function on concrete derivations,
  cross-checked against the hand-written graphs from `AlgComp.lean`;
* kernel-checked applications of the generated soundness lemmas;
* a smoke test on a *new* function (`double`) that is not in the paper.
-/

/-! ## Concrete derivations in the *generated* graphs -/

-- derivation of `List.append [1,2] [3,4,5] = [1,2,3,4,5]`
def laG : LAppendGen [1,2] [3,4,5] [1,2,3,4,5] :=
  .c2 (p1 := [3,4,5]) (p2 := 1) (p3 := [2])
    (.c2 (p1 := [3,4,5]) (p2 := 2) (p3 := [])
      (.c1 (p1 := [3,4,5])))

-- derivation of `fast_reverse_acc [1,2,3] [] = [3,2,1]`
def fraG : FastReverseAccGen [1,2,3] [] [3,2,1] :=
  .c2 (p1 := []) (p2 := 1) (p3 := [2,3]) $
  .c2 (p1 := [1]) (p2 := 2) (p3 := [3]) $
  .c2 (p1 := [2,1]) (p2 := 3) (p3 := []) $
  .c1 (p1 := [3,2,1])

-- derivation of `fast_reverse [1,2,3] = [3,2,1]`
def frG : FastReverseGen [1,2,3] [3,2,1] :=
  .c1 (p1 := [1,2,3]) fraG

-- derivation of `slow_reverse [1,2,3] = [3,2,1]`
def srG : SlowReverseGen [1,2,3] [3,2,1] :=
  .c2 (p1 := 1) (p2 := [2,3])
    (.c2 (p1 := 2) (p2 := [3])
      (.c2 (p1 := 3) (p2 := [])
        (.c1)
        (LAppendGen.c1 (p1 := [3])))
      (LAppendGen.c2 (p1 := [2]) (p2 := 3) (p3 := [])
        (LAppendGen.c1 (p1 := [2]))))
    (LAppendGen.c2 (p1 := [1]) (p2 := 3) (p3 := [2])
      (LAppendGen.c2 (p1 := [1]) (p2 := 2) (p3 := [])
        (LAppendGen.c1 (p1 := [1]))))

/-! ## Corresponding derivations in the *hand-written* graphs -/

def laHW : LAppend [1,2] [3,4,5] [1,2,3,4,5] :=
  .step (.step .base)

def fraHW : FastReverseAcc [1,2,3] [] [3,2,1] :=
  .step (.step (.step .base))

def frHW : FastReverse [1,2,3] [3,2,1] :=
  .run fraHW

def srHW : SlowReverse [1,2,3] [3,2,1] :=
  .step
    (.step
      (.step .base (LAppend.base (ys := [3])))
      (LAppend.step (x := 3) (xs := []) (ys := [2])
        (LAppend.base (ys := [2]))))
    (LAppend.step (x := 3) (xs := [2]) (ys := [1])
      (LAppend.step (x := 2) (xs := []) (ys := [1])
        (LAppend.base (ys := [1]))))

/-! ## Runtime evaluation: generated costs -/

-- append of lengths 2 and 3: one node per append-equation used
#eval LAppendGen.cost laG                    -- expect 3
-- accumulating reverse over 3 elements: 3 steps + 1 base
#eval FastReverseAccGen.cost fraG            -- expect 4
-- wrapper adds exactly one call
#eval FastReverseGen.cost frG                -- expect 5
-- slow reverse: 4 SR nodes + appends of cost 1+2+3
#eval SlowReverseGen.cost srG                -- expect 10

/-! ## Cross-check: hand-written graphs give identical numbers -/

#eval LAppend.cost laHW                      -- expect 3
#eval FastReverseAcc.cost fraHW              -- expect 4
#eval FastReverse.cost frHW                  -- expect 5
#eval SlowReverse.cost srHW                  -- expect 10

-- kernel-checked agreement of generated and hand-written costs
example : LAppendGen.cost laG = LAppend.cost laHW := by rfl
example : FastReverseAccGen.cost fraG = FastReverseAcc.cost fraHW := by rfl
example : SlowReverseGen.cost srG = SlowReverse.cost srHW := by rfl

-- NOTE: the hand-written `FastReverse.cost` does not charge for its own root node
-- (`run rev => FastReverseAcc.cost rev`), deviating from the paper's rule that a
-- cost function "counts the size of the call graph".  The generated cost follows
-- the paper, so it is exactly one more than the hand-written one.
example : FastReverseGen.cost frG = FastReverse.cost frHW + 1 := by rfl

-- and the absolute expected values
example : LAppendGen.cost laG = 3 := by rfl
example : FastReverseAccGen.cost fraG = 4 := by rfl
example : FastReverseGen.cost frG = 5 := by rfl
example : SlowReverseGen.cost srG = 10 := by rfl

/-! ## Soundness lemmas, applied end-to-end (kernel-checked) -/

example : List.append [1,2] [3,4,5] = [1,2,3,4,5] := LAppendGen.sound laG
example : fast_reverse_acc [1,2,3] [] = [3,2,1] := FastReverseAccGen.sound fraG
example : fast_reverse [1,2,3] = [3,2,1] := FastReverseGen.sound frG
example : slow_reverse [1,2,3] = [3,2,1] := SlowReverseGen.sound srG

-- generic consequence: a derivation forces the function's result
theorem sound_concrete {α : Type} {xs ys : List α}
    (g : SlowReverseGen xs ys) : slow_reverse xs = ys := SlowReverseGen.sound g

/-! ## Generality: a new function not covered by the paper -/

def double {α : Type} : List α → List α
  | [] => []
  | x :: t => x :: x :: double t

#genGraph double → DoubleGen

#print DoubleGen

-- sanity: the function does what we think
example : double [1,2,3] = [1,1,2,2,3,3] := by simp [double]

-- concrete derivation: `double [1,2,3]`
def dG : DoubleGen [1,2,3] [1,1,2,2,3,3] :=
  .c2 (p1 := 1) (p2 := [2,3])
    (.c2 (p1 := 2) (p2 := [3])
      (.c2 (p1 := 3) (p2 := [])
        (.c1)))

#eval DoubleGen.cost dG                     -- expect 4
example : DoubleGen.cost dG = 4 := by rfl
example : double [1,2,3] = [1,1,2,2,3,3] := DoubleGen.sound dG
