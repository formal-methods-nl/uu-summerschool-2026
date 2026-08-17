/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Algebraic structures and typeclasses

In this lecture we cover algebraic structures and typeclasses. We will cover:

- `structure`s
- type `class`es
- algebraic hierarchy in mathlib
- quotients
-/

noncomputable section

namespace Playground

section Structures

/-
We can define a new type by using the `structure` keyword.
-/
structure PointOnCircle where
  x : ℝ
  y : ℝ
  h : x ^ 2 + y ^ 2 = 1

/- To define a term of `PointOnCircle`, we can use the `where` keyword, ... -/
def northPole : PointOnCircle where
  x := 0
  y := 1
  h := by simp

/- ... or the `{ ... }` syntax. -/
example : PointOnCircle :=
  { x := Real.sqrt 2 / 2
    y := Real.sqrt 2 / 2
    h := by rw [div_pow]; norm_num }

/- We can inspect the fields of a structure using `#print`. -/
#print PointOnCircle

/- We can access the fields of a structure using the names of the fields, e.g.: -/
example (p : PointOnCircle) : ℝ :=
  p.x + p.y * 2

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
structure Mul where
  carrier : Type
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier

/- `Mul` is a new type, the "type of multiplicative structures". -/
#check Mul

/- We can use `#print` to inspect the fields of a structure. -/
#print Mul

/-
This allows to write `⋄` for multiplication, `𝟙` for the identity element and
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

lemma mul_assoc {G : Group} (x y z : G) : (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z) :=
  G.mul_assoc x y z

/- We use `@[simp]` to add a lemma to the simplifier. -/
@[simp]
lemma one_mul {G : Group} (x : G) : 𝟙 ⋄ x = x :=
  G.one_mul x

@[simp]
lemma inv_mul_cancel {G : Group} (x : G) : x⁻¹' ⋄ x = 𝟙 :=
  G.inv_mul_cancel x

/--
If `G` is a group, then also `x ⋄ x⁻¹' = 𝟙`.
(Note: in the definition we asked for `x⁻¹' ⋄ x = 𝟙`.
-/
@[simp]
lemma Group.mul_inv_cancel {G : Group} (x : G) : x ⋄ x⁻¹' = 𝟙 := by
  calc x ⋄ x⁻¹' = 𝟙 ⋄ (x ⋄ x⁻¹') := by rw [one_mul]
               _ = ((x ⋄ x⁻¹')⁻¹' ⋄ (x ⋄ x⁻¹')) ⋄ (x ⋄ x⁻¹') := by rw [inv_mul_cancel]
               _ = (x ⋄ x⁻¹')⁻¹' ⋄ (x ⋄ ((x⁻¹' ⋄ x) ⋄ x⁻¹')) := by simp only [mul_assoc]
               _ = 𝟙 := by simp

@[simp]
lemma Group.mul_one {G : Group} (x : G) : x ⋄ 𝟙 = x := by
  rw [← inv_mul_cancel _ x, ← mul_assoc, mul_inv_cancel, one_mul]

/-
The non-zero elements of `ℝ` form a group.

We use the `where` keyword to define terms of a structure.
-/
def units : Group where
  carrier := ℝˣ
  mul x y := x * y
  one := 1
  inv x := x⁻¹
  mul_assoc := _root_.mul_assoc
  one_mul := by simp
  inv_mul_cancel := by simp

/- `ℝˣ` is not only a group, but also an ordered type. -/

structure Order where
  /-- The underlying type. -/
  carrier : Type
  /-- The `≤` relation -/
  le : carrier → carrier → Prop

/- What do we do to say `Rˣ` is a group with an ordering? -/

def units₂ : Order where
  carrier := ℝˣ
  le := (· ≤ ·)

structure GroupAndOrder extends Group, Order

def units₃ : GroupAndOrder where
  carrier := ℝˣ
  mul x y := x * y
  one := 1
  inv x := x⁻¹
  mul_assoc := _root_.mul_assoc
  one_mul := by simp
  inv_mul_cancel := by simp
  le := (· ≤ ·)

/- This becomes very tedious! New attempt! -/

namespace NewAttempt

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

/-
Uncomment the following and observe the error message:

example {G : Type} (m : Mul₂ G) (x y z : G) :
    (x ⋄ y) ⋄ z = x ⋄ (y ⋄ z) :=
  sorry

Lean complains, that it does not know which multiplication structure it should use on `G`!
-/

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

/- A very common mistake. -/
/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?x ⋄ ?y
in the target expression
  1 ⋄ x = x
 x : ℝˣ
inst✝ : Semigroup ℝˣ
⊢ 1 ⋄ x = x
-/
#guard_msgs in
example (x : ℝˣ) [Semigroup ℝˣ] : 1 ⋄ x = x := by
  rw [eq_mul]
  simp

/- The problem is that by assuming `[Semigroup ℝˣ]`, we put a second, completely
unrelated semigroup structure on `ℝˣ` that we know nothing about. -/

/-
Typeclasses operate under the assumption that there is only ever one unique instance
on a type.

Problem: How about rings? A ring has two semigroup structures, one for addition and one for
multiplication!

`mathlib`s solution: distinguish `Semigroup` and `AddSemigroup`.
-/

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

namespace Quotients

/-
Besides the `structure` command, there is a different way to construct new types:
By taking quotients by equivalence relations.
-/

/-- A relation on integers: Two integers are equivalent if and only if their difference is
divisible by `n`. -/
def Rel (n : ℤ) (x y : ℤ) : Prop := n ∣ x - y

/-- `Rel` is an equivalence relation. -/
lemma Rel.equivalence (n : ℤ) : Equivalence (Rel n) where
  refl x := by simp [Rel]
  symm {x y} hxy := by
    dsimp [Rel] at *
    rw [dvd_sub_comm]
    exact hxy
  trans {x y z} hxy hyz := by
    dsimp [Rel] at *
    obtain ⟨k, hk⟩ := hxy
    obtain ⟨m, hm⟩ := hyz
    use k + m
    linarith

/-- An equivalence relation on `ℤ`. -/
def modSetoid (n : ℤ) : Setoid ℤ where
  r := Rel n
  iseqv := Rel.equivalence n

/-- The type of integers modulo `n`: The quotient of `ℤ` by the relation `Rel`. -/
abbrev Mod (n : ℤ) : Type :=
  Quotient (modSetoid n)

/-- An addition on the integers modulo `n`. -/
instance (n : ℤ) : Add (Mod n) where
  add := by
    /- We use the universal property of the quotient: To define a function out of `Mod n`, it suffices
    to define a function out of `ℤ` that is constant on equivalence classes.
    `⟦x⟧` (type with `\[[` and `\]]`) is notation for the image of `x` in the quotient `Mod n`.
    -/
    apply Quotient.lift₂ (fun x y ↦ ⟦x + y⟧)
    intro x y z w hxz hyw
    obtain ⟨k, hk⟩ := hxz
    obtain ⟨m, hm⟩ := hyw
    /- To show two representatives are equal in the quotient, it suffices to show they are related. -/
    apply Quotient.sound
    use k + m
    linarith

end Quotients
