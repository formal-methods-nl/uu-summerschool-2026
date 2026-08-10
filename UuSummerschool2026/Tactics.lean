/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# A tactic cheatsheet

This is a list of the tactics used in this summerschool. Further helpful references are:

- Kevin Buzzard's Tactics documentation of his Formalising Mathematics course:
  https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_C/Part_C.html
- All mathlib tactics:
  https://leanprover-community.github.io/mathlib-manual/html-multi/Tactics/#tactics
- The Lean language reference tactic documentation
  (technical, only recommended for the ambitious reader)
  https://lean-lang.org/doc/reference/latest//Tactic-Proofs/Tactic-Reference/
-/

/- `rfl` closes goals that are true by definition. -/
example : 2 = 1 + 1 := by
  rfl

/- `rw` is for rewriting expressions. -/
example (x y : ℝ) : x + y = y + x := by
  rw [add_comm]

/- `intro` introduces variables as local hypothesis. -/
example : ∀ (n : ℕ), n = n := by
  intro n
  rfl

/- `apply` a lemma or a hypothesis to close the goal. -/
example (n : ℕ) : n ≤ n := by
  apply le_refl

/- `use` provides a witness for an existential. -/
example : ∃ (n : ℕ), 0 < n := by
  use 1
  apply Nat.one_pos

/- `obtain`: extract a witness from an existential. -/
example (h : ∃ (n : ℕ), n < 0) : False := by
  obtain ⟨n, hn⟩ := h
  apply Nat.not_succ_le_zero n hn

/- `constructor`: If the goal's target type is an inductive type, apply the first
matching constructor. -/
example : 1 = 1 ∧ 0 = 0 := by
  constructor
  · rfl
  · rfl

/- `have`: introduce an intermediate fact. -/
example : 3 = 2 + 1 := by
  have : 2 = 1 + 1 := by rfl
  rw [this]

/- `ring` solves identities in commutative rings. -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

/- `norm_num` simplifies numerals. -/
example : (2 : ℝ) + 2 = 4 := by
  norm_num

/- `simp` simplifies expressions using tagged lemmas from the library. -/
example : |(0 : ℝ)| = 0 := by
  simp

/- `positivity` closes goals of the form `0 ≤ x`, `0 < x` or `0 ≠ x`. -/
example (x : ℝ) (hx : x ≠ 0) : 0 < |x| := by
  positivity

/- `linarith` closes linear arithmetic goals. -/
example {a b c : ℝ} (h₁ : a < b) (h₂ : b ≤ c) : a ≤ c := by
  linarith

/- `by_cases`: proof by distinguishing cases. -/
example (n : ℕ) : n + n = 2 * n := by
  by_cases h : n = 0
  · rw [h]
  · rw [two_mul]
