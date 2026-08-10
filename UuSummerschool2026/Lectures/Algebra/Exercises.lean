/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Exercises for algebraic structures and typeclasses

In the following exercises, you will construct the integers as a quotient
of pairs of natural numbers and show it is a commutative ring.
-/

namespace Playground

/-- Two pairs `x = (a, b)` and `y = (u, v)` are equivalent if `a + v = u + b`-/
def Rel (x y : ℕ × ℕ) : Prop :=
  x.1 + y.2 = y.1 + x.2

lemma Rel.equivalence : Equivalence Rel where
  refl := sorry
  symm := sorry
  trans := sorry

instance setoid : Setoid (ℕ × ℕ) where
  r := Rel
  iseqv := Rel.equivalence

@[simp]
lemma setoid_iff (x y : ℕ × ℕ) : setoid x y ↔ Rel x y := by
  rfl

@[simp]
lemma Int.r_iff (x y : ℕ × ℕ) : x ≈ y ↔ Rel x y := by
  rfl

abbrev Int : Type :=
  Quotient setoid

lemma Int.exists_rep (x : Int) : ∃ (p : ℕ × ℕ), ⟦p⟧ = x :=
  Quotient.mk_surjective x

/-- Any natural number `n` can be regarded as an integer: The representative of `(n, 0)`. -/
def Nat.asInt (n : ℕ) : Int :=
  ⟦(n, 0)⟧

lemma Nat.asInt_injective : Function.Injective Nat.asInt := by
  -- Hint: use `Quotient.eq`
  sorry

/-- Addition on the integers. -/
def Int.add : Int → Int → Int := by
  apply Quotient.lift₂ (fun x y ↦ ⟦x + y⟧)
  sorry

instance : Add Int where
  add := Int.add

lemma Int.mk_add (x y : ℕ × ℕ) : (⟦x + y⟧ : Int) = ⟦x⟧ + ⟦y⟧ :=
  rfl

lemma Int.add_comm (x y : Int) : x + y = y + x := by
  /- By `Int.exists_rep`, there exists a pair representing `x`. -/
  obtain ⟨a, ha⟩ := Int.exists_rep x
  rw [← ha]
  sorry

lemma Int.add_assoc (x y z : Int) : x + y + z = x + (y + z) :=
  sorry

instance : Zero Int where
  zero := Nat.asInt 0

instance : AddMonoid Int where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec

/-- Negation on the integers, i.e. `x ↦ -x`. Use `Quotient.lift`. -/
def Int.neg : Int → Int := sorry

instance : Neg Int where
  neg := Int.neg

lemma Int.neg_add_cancel (x : Int) : (-x) + x = 0 :=
  sorry

/-- The integers form an abelian group. -/
instance : AddCommGroup Int where
  neg_add_cancel := sorry
  add_comm := sorry
  zsmul := zsmulRec

/-- Multiplication on the integers. -/
def Int.mul : Int → Int → Int := sorry

instance : Mul Int where
  mul := Int.mul

lemma Int.mul_comm (x y : Int) : x * y = y * x :=
  sorry

lemma Int.mul_assoc (x y z : Int) : x * y * z = x * (y * z) :=
  sorry

/-
Now show that `Int` is a commutative ring by defining a `CommRing Int` instance.
-/

end Playground
