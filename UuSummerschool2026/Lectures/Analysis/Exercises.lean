/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import UuSummerschool2025.Lectures.Analysis.Lecture

/-!
# Exercises for real analysis and linear arithmetic

Try to fill in the following `sorry`s.
-/

example : ∃ (x : ℝ), x + 37 = 42 := by
  sorry

-- Try to prove this only using `rw`, possibly useful lemmas:
-- `pow_two`, `mul_sub`, `add_mul`, `add_sub`, `sub_sub`, `add_zero`
-- Then rewrite the proof using `calc`.
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

example {a b c d : ℝ} (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  sorry

-- Use `apply?` to search for useful lemmas.
example (a b : ℝ) : min a b = min b a := by
  -- Hint: By `le_antisymm`, it suffices to show `LHS ≤ RHS` and `RHS ≤ LHS`.
  apply le_antisymm
  · sorry
  · sorry

example (a b : ℝ) : max a b = max b a := by
  sorry

example (a b c : ℝ) : min (min a b) c = min a (min b c) := by
  sorry

-- Hint for the next one:
#check abs_le'

example (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry

-- Hint: use `abs_add` and `add_sub_cancel_right`
example (a b : ℝ) : |a| - |b| ≤ |a - b| :=
  sorry

lemma eq_zero_of_forall_abs_lt {x : ℝ} (h : ∀ ε > 0, |x| < ε) : x = 0 := by
  -- New tactic: We argue by contradiction, the negated conclusion is named `h`.
  by_contra h
  sorry

-- Hint: `gcongr`
example {a b c d : ℝ} (h : b ≤ d) :
    |a| * b + c * 2 ≤ c * 2 + |a| * d := by
  sorry

example {a b c d : ℝ} (h : b ≤ d) (hc : 1 ≤ c + 1) :
    b * |a| + 2 * c ≤ c * 4 + |a| * d := by
  sorry

section CaseSplitting

-- Hint: use `eq_zero_or_eq_zero_of_mul_eq_zero` and `obtain` to distinguish
-- cases.
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

-- Do not use `lt_abs` here!
example (x y : ℝ) : x < |y| ↔ x < y ∨ x < -y := by
  sorry

-- Do not use `abs_lt` here!
example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by
  sorry

end CaseSplitting

section Casting

/-
Which of the sides is true? Your proof *must* start with `left` or `right`.
Hint: Use `simp` to simplify logical statements.
-/
example : (∀ n, (n / 2) * 2 = n) ∨ ¬ (∀ n, (n / 2) * 2 = n) := by
  sorry

/-
Which of the sides is true? Your proof *must* start with `left` or `right`.
-/
example : (∀ n : ℕ, ((n / 2 : ℕ) : ℝ) = (n : ℝ) / (2 : ℝ)) ∨
    ¬ (∀ n : ℕ, ((n / 2 : ℕ) : ℝ) = (n : ℝ) / (2 : ℝ)) := by
  sorry

example (n : ℕ) (hn : n ≠ 0) : Real.sin ((2 * n / n : ℕ)) = Real.sin 2 := by
  sorry

end Casting

section Convergence

/-- Every constant sequence is bounded. Prove this directly using the definition! -/
lemma Bounded.const (x : ℝ) : Bounded (fun _ ↦ x) := by
  rw [bounded_iff]
  sorry

/-- A sequence `a` is bounded if and only if the sequence of absolute values is bounded. -/
lemma Bounded.iff_bounded_abs {a : ℕ → ℝ} :
    Bounded a ↔ Bounded (fun n ↦ |a n|) :=
  sorry

/-- If `a` converges to `x`, then `-a` converges to `-x`. -/
lemma ConvergesTo.neg {a : ℕ → ℝ} {x : ℝ} (ha : ConvergesTo a x) :
    ConvergesTo (-a) (-x) :=
  sorry

/-- A sequence `a` converges to zero if and only if `|a|` converges to zero. -/
lemma ConvergesTo.zero_iff_convergesTo_abs_zero (a : ℕ → ℝ) :
    ConvergesTo a 0 ↔ ConvergesTo (fun n ↦ |a n|) 0 := by
  sorry

/-- A sequence `a` converges to `x` if and only if `n ↦ x - a n` converges to `0`. -/
lemma ConvergesTo.iff_convergesTo_sub_zero (a : ℕ → ℝ) (x : ℝ) :
    ConvergesTo a x ↔ ConvergesTo (fun n ↦ x - a n) 0 := by
  sorry

/-- If `a`, `b` and `c` are sequences with `a n ≤ b n ≤ c n` and `a` and `c` converge to `x`,
then also `b` converges to `x`. -/
lemma ConvergesTo.sandwich (a b c : ℕ → ℝ) {x : ℝ}
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : ConvergesTo a x) (hc : ConvergesTo c x) :
    ConvergesTo b x := by
  sorry

/-
We now give an alternative proof of `ConvergesTo.mul`.
-/

/--
If `a` converges to `x` and `c` is a constant, then `n ↦ c * a n` converges to `c * x`.
Prove this directly without using `ConvergesTo.mul`!
-/
lemma ConvergesTo.const_mul {a : ℕ → ℝ} {x : ℝ} (c : ℝ) (h : ConvergesTo a x) :
    ConvergesTo (fun n ↦ c * a n) (c * x) := by
  sorry

/--
If `a` converges to `x` and `c` is a constant, then `n ↦ a n * c` converges to `x * c`.
Prove this without using `ConvergesTo.mul`!
-/
lemma ConvergesTo.mul_const {a : ℕ → ℝ} {x : ℝ} (c : ℝ) (h : ConvergesTo a x) :
    ConvergesTo (fun n ↦ a n * c) (x * c) := by
  sorry

/--
If `a` and `b` converge to `0`, also `a * b` converges to `0`.
Prove this directly without using `ConvergesTo.mul`!
-/
lemma ConvergesTo.mul_zero {a b : ℕ → ℝ} (ha : ConvergesTo a 0) (hb : ConvergesTo b 0) :
    ConvergesTo (a * b) 0 := by
  sorry

/--
If `a` converges to `x` and `b` converges to `y`, then `a * b` converges
to `x * y`.
Prove this directly using the above lemmas without using `ConvergesTo.mul`!
-/
example {a b : ℕ → ℝ} {x y : ℝ} (ha : ConvergesTo a x)
    (hb : ConvergesTo b y) :
    ConvergesTo (a * b) (x * y) := by
  rw [ConvergesTo.iff_convergesTo_sub_zero]
  sorry

/--
If `a` converges to both `x` and `y`, `x = y`.
Hint: `eq_zero_of_forall_abs_lt` from above might be useful.
-/
lemma ConvergesTo.unique (a : ℕ → ℝ) {x y : ℝ} (hx : ConvergesTo a x) (hy : ConvergesTo a y) :
    x = y := by
  sorry

end Convergence

namespace Playground

/-
In this section we define what it means for a function to be continuous and
prove a characterisation in terms of converging sequences.
-/

/--
Define what it means that `f` is continuous at `x` using the `ε`-`δ`-definition, i.e.
a function `f` is continuous at `x₀` if and only if
for every `ε > 0`, there exists a `δ > 0` such that for every `y : ℝ` with
`|x₀ - y| < δ`, it follows that `|f x₀ - f y| < ε`.
-/
def ContinuousAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  sorry

/-- If `f` is continuous at `x₀` and `a` is a sequence converging to `x₀`, then
`n ↦ f (a n)` converges to `f x₀`. -/
lemma ContinuousAt.convergesTo {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContinuousAt f x₀)
    {a : ℕ → ℝ} (ha : ConvergesTo a x₀) :
    ConvergesTo (fun n ↦ f (a n)) (f x₀) :=
  sorry

/-- If for every sequence `a` converging to `x₀`, `n ↦ f (a n)` converges to `f x₀`, then
`f` is continuous at `x₀`. -/
lemma ContinuousAt.of_forall_convergesTo {f : ℝ → ℝ} {x₀ : ℝ}
    (H : ∀ {a : ℕ → ℝ} (ha : ConvergesTo a x₀), ConvergesTo (fun n ↦ f (a n)) (f x₀)) :
    ContinuousAt f x₀ :=
  sorry

/-- `f` is continuous at `x₀` if and only if when ever `a` converges to `x₀`,
the sequence `n ↦ f (a n)` converges to `f x₀`. -/
theorem ContinuousAt.iff_forall_convergesTo {f : ℝ → ℝ} {x₀ : ℝ} :
    ContinuousAt f x₀ ↔
      (∀ {a : ℕ → ℝ} (ha : ConvergesTo a x₀), ConvergesTo (fun n ↦ f (a n)) (f x₀)) :=
  sorry

end Playground
