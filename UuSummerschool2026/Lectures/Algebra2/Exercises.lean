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
  refl := by
    intro
    rw [Rel]
  symm := by
    intro x y rel
    simp only [Rel] at *
    exact rel.symm
  trans := by
    intro ⟨x1,x2⟩ ⟨y1,y2⟩ ⟨z1,z2⟩ hxy hyz
    simp only [Rel] at *
    linarith


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
  unfold Function.Injective
  intro x y h
  unfold Nat.asInt at h
  apply Quotient.eq.mp at h
  simp [setoid, Rel] at h
  exact h

/-- Addition on the integers. -/
def Int.add : Int → Int → Int := by
  apply Quotient.lift₂ (fun x y ↦ ⟦x + y⟧)
  intro x y z w xz yw
  apply Quotient.sound
  simp [Rel] at *
  linarith

instance : Add Int where
  add := Int.add

lemma Int.mk_add (x y : ℕ × ℕ) : (⟦x + y⟧ : Int) = ⟦x⟧ + ⟦y⟧ :=
  rfl

lemma Int.add_comm (x y : Int) : x + y = y + x := by
  /- By `Int.exists_rep`, there exists a pair representing `x`. -/
  obtain ⟨a, ha⟩ := Int.exists_rep x
  obtain ⟨b, hb⟩ := Int.exists_rep y
  rw [← ha, ← hb, ← Int.mk_add, ← Int.mk_add]
  apply Quotient.sound
  simp [Rel]
  linarith

lemma Int.add_assoc (x y z : Int) : x + y + z = x + (y + z) := by
  obtain ⟨a, ha⟩ := Int.exists_rep x
  obtain ⟨b, hb⟩ := Int.exists_rep y
  obtain ⟨c, hc⟩ := Int.exists_rep z
  rw [← ha, ← hb, ← hc, ← Int.mk_add, ← Int.mk_add, ← Int.mk_add, ← Int.mk_add]
  apply Quotient.sound
  simp [Rel]
  linarith

instance : Zero Int where
  zero := Nat.asInt 0

lemma Int.zero_add (x : Int) : 0 + x = x := by
  obtain ⟨a, ha⟩ := Int.exists_rep x
  rw [← ha]
  apply Quotient.sound
  simp [Rel]

instance : AddMonoid Int where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := by
    intro x
    rw [Int.add_comm, Int.zero_add]
  nsmul := nsmulRec

/-- Negation on the integers, i.e. `x ↦ -x`. Use `Quotient.lift`. -/
def Int.neg : Int → Int := by
  apply Quotient.lift (fun a ↦ ⟦(a.2, a.1)⟧)
  intro x y xy
  apply Quotient.sound
  simp [Rel] at *
  linarith

instance : Neg Int where
  neg := Int.neg

lemma Int.neg_add_cancel (x : Int) : (-x) + x = 0 := by
  obtain ⟨a, ha⟩ := Int.exists_rep x
  rw [← ha]
  apply Quotient.sound
  simp [Rel]
  linarith

/-- The integers form an abelian group. -/
instance : AddCommGroup Int where
  neg_add_cancel := Int.neg_add_cancel
  add_comm := Int.add_comm
  zsmul := zsmulRec

/-- Multiplication on the integers. -/
def Int.mul : Int → Int → Int := by
  apply Quotient.lift₂ (fun x y ↦ ⟦(x.1 * y.1 + x.2 * y.2, x.2 * y.1 + x.1 * y.2)⟧)
  intro x y z w xz yw
  apply Quotient.sound
  simp [Rel] at *
  nlinarith

instance : Mul Int where
  mul := Int.mul

lemma Int.mul_comm (x y : Int) : x * y = y * x := by
  obtain ⟨a, ha⟩ := Int.exists_rep x
  obtain ⟨b, hb⟩ := Int.exists_rep y
  rw [← ha, ← hb]
  apply Quotient.sound
  simp [Rel]
  linarith

lemma Int.mul_assoc (x y z : Int) : x * y * z = x * (y * z) :=
  sorry

/-
Now show that `Int` is a commutative ring by defining a `CommRing Int` instance.
-/

end Playground
