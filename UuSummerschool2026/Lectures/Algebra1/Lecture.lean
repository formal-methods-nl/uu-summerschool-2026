/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Algebraic structures and typeclasses 1

In this lecture we cover algebraic structures and typeclasses. We will cover:

- `structure`s
- type `class`es
- algebraic hierarchy in mathlib
-/

noncomputable section

namespace Playground

section Structures

/-
We can define a new type by using the `structure` keyword.
-/
structure PointOnCircle where
  placeholder : sorry


/- To define a term of `PointOnCircle`, we can use the `where` keyword, ... -/
example : PointOnCircle := sorry

/- ... or the `{ ... }` syntax. -/
example : PointOnCircle := sorry

/- ... or the `⟨ ... ⟩` syntax -/
example : PointOnCircle := sorry

/- We can inspect the fields of a structure using `#print`. -/
#print PointOnCircle


/- We can access the fields of a structure using the names of the fields, e.g.: -/
example (p : PointOnCircle) : ℝ := sorry


def northPole : PointOnCircle := sorry





















/-
Let us now consider something more useful.
-/

/--
A multiplicative structure is a

- underlying type `carrier`
- a multiplication `mul : carrier → carrier → carrier`
- a distinguished element `one : carrier`
- an inversion function `inv : carrier → carrier`.

(This does not assume any axioms for compatibilities between these operations!)

We use the `structure` keyword to define a new type.
-/

structure MyMul where
  placeholder : sorry

example : MyMul := sorry

/- `Mul` is a new type, the "type of multiplicative structures". -/
#check MyMul

/- We can use `#print` to inspect the fields of a structure. -/
#print MyMul


























/-
Here's one I prepared earlier
-/
structure Mul where
  carrier : Type
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier

/-
The following allows to write `⋄` for multiplication, `𝟙` for the identity element and
`inv` for the inverse.
-/
notation3:70 x:70 " ⋄ " y:71 => Mul.mul _ x y
notation3 "𝟙" => Mul.one _
notation3:71 x:80 "⁻¹'" => Mul.inv _ x

/--
A group is a multiplicative structure with the usual axioms, i.e.
- associativity: `(x ⋄ y) ⋄ z = x ⋄ (y ⋄ z)`,
- `𝟙` is an identity on the left,
- `inv x ⋄ x = 𝟙` for all `x`.

We use the `extends` keyword to make a new `structure` extending `Mul`.
-/
structure Group extends Mul where
  mul_assoc (x y z : carrier) : (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z)
  one_mul (x : carrier) : 𝟙 ⋄ x = x
  inv_mul_cancel (x : carrier) : inv x ⋄ x = 𝟙

/- Note that `Group` has both the fields of `Mul` and the one specified in `Group`. -/
#print Group

/- ignore this for now -/
instance : CoeSort Group Type where
  coe G := G.carrier














/-
We can prove various expected identities hold for groups
-/

lemma mul_assoc {G : Group} (x y z : G) : (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z) := by
  exact G.mul_assoc x y z


/- We use `@[simp]` to add a lemma to the simplifier. -/
@[simp]
lemma one_mul {G : Group} (x : G) : 𝟙 ⋄ x = x := by
  exact G.one_mul x


@[simp]
lemma inv_mul_cancel {G : Group} (x : G) : x⁻¹' ⋄ x = 𝟙 := by
  exact G.inv_mul_cancel x


/--
If `G` is a group, then also `x ⋄ x⁻¹' = 𝟙`.
(Note: in the definition we asked for `x⁻¹' ⋄ x = 𝟙`.
-/
@[simp]
lemma Group.mul_inv_cancel {G : Group} (x : G) : x ⋄ x⁻¹' = 𝟙 := by
  calc
    x ⋄ x⁻¹' = 𝟙 ⋄ (x ⋄ x⁻¹') := by simp
    _ = ((x ⋄ x⁻¹')⁻¹' ⋄ (x ⋄ x⁻¹')) ⋄ (x ⋄ x⁻¹') := by simp
    _ = ((x ⋄ x⁻¹')⁻¹' ⋄ (x ⋄ ((x⁻¹' ⋄ x) ⋄ x⁻¹'))) := by simp only [mul_assoc]
    _ = 𝟙 := by simp




@[simp]
lemma Group.mul_one {G : Group} (x : G) : x ⋄ 𝟙 = x := by sorry






















/-
The non-zero elements of `ℝ` form a group.

We use the `where` keyword to define terms of a structure.
-/
def units : Group := sorry




























/- `ℝˣ` is not only a group, but also an ordered type; it has a `≤` function. -/

structure Order where
  carrier : Type
  le : carrier → carrier → Prop

/- What do we do to say `Rˣ` is a group with an ordering? -/

def units₂ : Order where
  carrier := ℝˣ
  le a b := a ≤ b

structure GroupAndOrder extends Group, Order

def units₃ : GroupAndOrder := sorry


























/- This becomes very tedious! New attempt! -/

namespace NewAttempt

/-
We can also define structures which take in arguments (rather than having a `carrier` field)

So, perhaps instead of `GroupAndOrder`, we can have a type `G` and assume `Group G` and `Order G`.
This seems like it might scale better!
-/
structure MyMul₂ (G : Type) where
  placeholder : sorry

structure MyOrder₂ (G : Type) where
  placeholder : sorry

def myMulUnits : MyMul₂ ℝˣ := sorry

def myOrderUnits : MyOrder₂ ℝˣ := sorry




















structure Mul₂ (G : Type) where
  mul : G → G → G

structure Order₂ (G : Type) where
  le : G → G → Prop
  le_rfl (g : G) : le g g

def mulUnits : Mul₂ ℝˣ where
  mul x y := x * y

def orderUnits : Order₂ ℝˣ where
  le x y := x ≤ y
  le_rfl := by simp

scoped notation3:70 x:70 " ⋄ " y:71 => Mul₂.mul _ x y


--Uncomment the following and observe the error message:

/-
example {G : Type} (m : Mul₂ G) (x y z : G) :
    (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z) :=
  sorry-/











--Lean complains, that it does not know which multiplication structure it should use on `G`!


/-
We can still state associativity using this method, but it looks very awkward:
-/

example {G : Type} (m : Mul₂ G) (x y z : G) :
    m.mul (m.mul x y) z = m.mul x (m.mul y z) := sorry















end NewAttempt

/-
We would like to have a mechanism that let's Lean automatically figure out
which multiplicative structure on `G` it should use when it sees `x ⋄ y`.
-/

/-
This mechanism is called type classes.

The syntax for defining a `class` is the same as the one for `structure`s.
Only `structure` is replaced by `class`.
-/
class Mul₃ (G : Type) where
  mul : G → G → G

notation3:70 x:70 " ⋄ " y:71 => Mul₃.mul x y













class Semigroup (G : Type) extends Mul₃ G where
  mul_assoc (x y z : G) : (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z)

/- To declare a semigroup structure on `Rˣ` as an instance, use the `instance` keyword. -/
instance : Semigroup ℝˣ where
  mul x y := x * y
  mul_assoc := _root_.mul_assoc

lemma eq_mul (x y : ℝˣ) : x ⋄ y = x * y := rfl

/-
To assume `G` has the structure of some `class`, use `[ ... ]` instead of `( ... )`.
The hypothesis does not have to be named.
-/
example (G : Type) [Semigroup G] (x y z w : G) :
    (x ⋄ y) ⋄ (z ⋄ w) = x ⋄ (y ⋄ z) ⋄ w := by
  simp [Semigroup.mul_assoc]


/-
Why do we get an error when we try and rewrite with `eq_mul` here?
-/
example (x : ℝˣ) [Semigroup ℝˣ] : 1 ⋄ x = x := by
  sorry




















/- The problem is that by assuming `[Semigroup ℝˣ]`, we put a second, completely
unrelated semigroup structure on `ℝˣ` that we know nothing about. -/

example (x : ℝˣ) : 1 ⋄ x = x := by
  rw [eq_mul]
  simp


















/-
Typeclasses operate under the assumption that there is only ever one unique instance
on a type.

Problem: How about rings? A ring has two semigroup structures, one for addition and one for
multiplication!

`mathlib`s solution: distinguish `Semigroup` and `AddSemigroup`.
-/


example {R : Type} [AddSemigroup R] [_root_.Semigroup R] (x y z : R) :
    x * (y + z) = x * y + x * z := sorry


example {R : Type} [Ring R] (x y z : R) :
    x * (y + z) = x * y + x * z := sorry


















end Structures

end Playground

section Hierarchy

/-
Let us now look at `mathlib`s own algebraic typeclasses:
-/

#check Mul
#check Semigroup
#check Monoid
#check Group
#check CommGroup

/- and the same for additive, so e.g. -/

#check AddGroup

end Hierarchy
