/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Real analysis and linear arithmetic in Lean

In this lecture we cover the basic interactions with the real numbers in Lean.
We will cover

- real (in)equalities
- example: convergence of sequences
- natural numbers, casting and junk values

## References

Some of the examples are taken from:

- Jeremy Avigad, Patrick Massot: Mathematics in Lean
  (https://leanprover-community.github.io/mathematics_in_lean)
- Kevin Buzzard: Formalising Mathematics
  (https://github.com/ImperialCollegeLondon/formalising-mathematics-2024)
-/

section Reals

/-
The real numbers in Lean are actual real numbers, not floating point
approximations.
Internally, they are implemented via Cauchy sequences of rational numbers.
-/

/- The real number `2` is represented by the constant Cauchy sequence `2, 2, 2, ...`. -/
#eval (2 : ℝ)

#eval 3 + 6



/- This is the statement that `2 + 2 = 4` as an equality in the natural numbers. -/
example : 2 + 2 = 4 := by rfl

/- This is the statement that `2 + 2 = 4` as an equality in the real numbers. -/
example : (2 : ℝ) + 2 = 4 := by norm_num



/- Identities with real variables can be proven using `rw` with lemmas from the library. -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  rw [pow_two, sq, sq]
  rw [two_mul]
  sorry

























/- This becomes quite tedious, so there exists the `ring` tactic that proves any
identity that holds in any commutative ring. -/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring

example : ∀ a b : ℝ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  intro a b
  use 3
  ring
























/- `mathlib` defines many standard functions on the real numbers, such as `sin` and `cos`. -/
#check (Real.sin : ℝ → ℝ)
#check Real.cos

--#check Set.mem_add

example (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
  by exact Real.sin_sq_add_cos_sq x
  --sorry


end Reals















section Inequalities

/- The real numbers are ordered and we can use many lemmas from the library to close simple
goals. -/
example (x : ℝ) : x ≤ x := by
  exact Std.IsPreorder.le_refl x

example {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  exact le_trans hxy hyz




/-
We can find lemma names by using the library search tactic `exact?`.
-/
example (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add_le x y

/- We can also use the trans tactic. -/
example {x y z : ℝ} (hxy : x ≤ y) (hyz : y = z) : x ≤ z := by
  trans y
  · exact hxy
  · exact hyz.le
/-
calc
    x ≤ y := by proof
    _ = a_1 := by proof
    _ ≤ a_2 := by proof
    ...
    _ ≤ z := by proof

    -/

#check Eq.symm
/- Or the calc tactic. -/
example {x y z : ℝ} (hxy : x = y) (hyz : y ≤ z) : x ≤ z := by
  /-calc
    z ≥ y := hyz
    _ = x := Eq.symm hxy-/


  calc
    x = y := hxy
    _ ≤ z := hyz

  --sorry


/- Or use `linarith` to close linear arithmetic goals. -/
example {x y z : ℝ} (hxy : x ≤ y) (hyz : y = z) : x ≤ z := by
  linarith


/- A slightly more complicated example. -/
example {a b : ℝ} : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have : 0 ≤ a ^ 2 - 2*a*b + b ^ 2 := by
    calc
      0 ≤ (a - b)^2 := by exact sq_nonneg (a - b)
      _ = a ^ 2 - 2*a*b + b ^ 2 := sub_sq a b
  linarith















/- `gcongr` can be used to prove inequalities of expressions by showing
inequalities between subexpressions. -/
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  gcongr


example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  · linarith
  · bound





end Inequalities




















section Casting

/- The following simple statement seems to resist proofs by the tactics we have seen... -/
example (n : ℕ) : n - 1 + 1 = n := by
  --plausible
  sorry





























/-
This might give a hint as to what is going on...
-/
#eval (2 - 3)
























/- What we might mean instead is: -/
example (n : ℕ) : ((n : ℝ) - 1) + 1 = n := by
  simp

/-
What happens when we have `n : ℕ` and write `(n : ℝ)`?
Lean knows how to convert a natural number to a real number, this is called *casting*.
-/
example (n : ℕ) : ℝ := n

/- Casts can be very annoying to deal with! -/
example (n : ℕ) (hn : 1 ≤ n) :
    Real.sin (n.choose 2) = Real.sin (n * (n - 1) / 2) := by
  by_cases h : n = 0
  · subst h
    simp
  · congr
    rw [Nat.choose_two_right]
    rw [Nat.cast_div]
    · rw [Nat.cast_mul, Nat.cast_two]
      rw [Nat.cast_sub, Nat.cast_one]
      apply hn
    · rw [← even_iff_two_dvd]
      apply Nat.even_mul_pred_self n
    · simp
























/-
Division by `0` is allowed in Lean. Why?

When we write `/`, we don't want to always pass a proof that the denominator is non-zero.
Instead, we allow division by zero and provide a "junk value". In this case,
we arbitrarily chose `1 / 0 = 0`.

Of course, division does not satisfy the property `x * 1 / x = 1` for every `x`, but only
for whenever `x ≠ 0`. Hence, many theorems will have non-zero assumptions, but this does not
stop us from having a definition of `1 / 0`.
-/
example : 1 / 0 = 0 := rfl

example : ∃ (x : ℝ), x * (1 / x) ≠ 1 := by
  use 0
  simp


example (x : ℝ) (hx : 0 ≠ x) : x * (1 / x) = 1 := by
  exact mul_one_div_cancel (id (Ne.symm hx))

end Casting






























section Sequences

/- A sequence of real numbers is a function `ℕ → ℝ`. -/
variable (a : ℕ → ℝ)

/- The `5`-th entry of the sequence `a` is simply `a 5`. -/
#check a 5

/--
The sequence `a : ℕ → ℝ` converges to `x : ℝ` if for every `ε > 0`,
there exists `n₀ : ℕ` such that for all `n ≥ n₀`, `|x - a n| ≤ ε`.
-/
def ConvergesTo (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, |x - a n| ≤ ε

/- Use `rw [convergesTo_iff]` to unfold the definition of convergence. -/
lemma convergesTo_iff (a : ℕ → ℝ) (x : ℝ) :
    ConvergesTo a x ↔ ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, |x - a n| ≤ ε := by rfl

/-- Any constant sequence converges to its value. -/
lemma ConvergesTo.const (a : ℝ) : ConvergesTo (fun _ ↦ a) a := by
  rw [convergesTo_iff]
  intro ε hε
  use 0
  simp
  exact hε.le

#check Filter.Tendsto (fun n ↦ 1 / n : ℝ → ℝ) (Filter.atTop) (nhds 0)

example : ConvergesTo (fun n ↦ 1 / n) 0 := by
  rw [convergesTo_iff]
  intro ε hε
  use ⌈ε⁻¹⌉₊
  intro n hn
  simp
  have : n ≥ ε⁻¹ := by
    exact Nat.ceil_le.mp hn
  apply inv_le_of_inv_le₀
  · exact hε
  · exact this








/-- If `a` converges to `x` and `b` converges to `y`, then
`a + b` converges to `x + y`. -/
lemma ConvergesTo.add {a b : ℕ → ℝ} {x y : ℝ}
    (ha : ConvergesTo a x) (hb : ConvergesTo b y) :
    ConvergesTo (a + b) (x + y) := sorry


/--
The sequence `a : ℕ → ℝ` is bounded if there exists a constant `M : ℝ` such that
`|a n| ≤ M` for all `n`.
-/
def Bounded (a : ℕ → ℝ) : Prop := sorry


lemma bounded_iff (a : ℕ → ℝ) :
    Bounded a ↔ sorry := sorry


/--
If `a : ℕ → ℝ` is bounded by `M` for almost all `n : ℕ`, it is bounded
everywhere.
-/
lemma Bounded.of_le {a : ℕ → ℝ} (M : ℝ) (n₀ : ℕ) (h : ∀ n ≥ n₀, |a n| ≤ M) :
    Bounded a := sorry



set_option backward.isDefEq.respectTransparency false in
/-- Any convergent sequence is bounded. -/
lemma ConvergesTo.bounded {a : ℕ → ℝ} {x : ℝ} (h : ConvergesTo a x) :
    Bounded a := sorry













/-- If `a` converges to `x` and `b` converges to `y`, then `a * b` converges
to `x * y`.

Exercise for the reader!
 -/
lemma ConvergesTo.mul {a b : ℕ → ℝ} {x y : ℝ} (ha : ConvergesTo a x)
    (hb : ConvergesTo b y) :
    ConvergesTo (a * b) (x * y) := by
  sorry

end Sequences
