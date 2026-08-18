/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Algebraic structures and typeclasses 2

In this lecture we cover algebraic structures and typeclasses. We will cover:

- quotients
- projects
-/

namespace Quotients

/-
Besides the `structure` command, there is a different way to construct new types:
By taking quotients by equivalence relations.
-/

/-- A relation on integers: Two integers are equivalent if and only if their difference is
divisible by `n`. -/
def Rel (n : ℤ) (x y : ℤ) : Prop := n ∣ (x - y)

/-- `Rel` is an equivalence relation. -/
lemma Rel.equivalence (n : ℤ) : Equivalence (Rel n) where
  refl x := sorry
  symm {x y} hxy := sorry
  trans {x y z} hxy hyz := sorry


/-- An equivalence relation on `ℤ` is called a `Setoid` in lean. -/
def modSetoid (n : ℤ) : Setoid ℤ := sorry

/-- The type of integers modulo `n`: The quotient of `ℤ` by the relation `Rel`. -/
abbrev Mod (n : ℤ) : Type := sorry












/-
Note that `Quotient` is not doing some construction with cosets like we may expect.
When we click through, we see that the existence of quotients is actually an axiom in lean!
-/
#check Quotient
#check Quot.sound










/-
One nice consequence of this is we are forced to use the *universal property* of quotients to formalize proofs about
quotient types

Namely, if we want to define a function from `A ⧸ ~` to `B`, it suffices to give a function from `A` to `B` that sends
elements `x y : A` with `x ~ y` to equal elements in `B`.
-/
#check Quotient.lift


/-
There are a few different variations of this universal property, e.g. one for binary functions.

I.e. if I have a binary function from `(A ⧸ ~₁) × (B ⧸ ~₂)` to `C`, we need to give a function from `A × B` to `C` respecting
`~₁` in the first argument and `~₂` in the second argument.
-/
#check Quotient.lift₂




/-
We can use the usual notation for elements of a quotient by typing `\[[]]`, which produces `⟦⟧`

Can also write `\[[` for `⟦`
-/

/-
#check ⟦0⟧ : Mod 8
-/













/-- An addition on the integers modulo `n`. -/
instance (n : ℤ) : Add (Mod n) where
  add := by

    sorry

/-
Commented out because it does not type check if `Mod` is not defined as a quotient (and the definition
was sorried at the beginning)

example : (⟦2⟧ : Mod 11) + ⟦10⟧ = ⟦1⟧ := by sorry

example (n a : ℤ) (h : n ∣ a) : (⟦a⟧ : Mod n) = ⟦0⟧ := sorry

lemma add_eq (n a b : ℤ) : (⟦a⟧ + ⟦b⟧ : Mod n) = ⟦a + b⟧ := sorry

/-
One lemma that also comes in handy is `Quotient.exact`, which says `⟦a⟧ = ⟦b⟧ → a ≈ b`
-/
example (n a b c : ℤ) (h : (⟦a⟧ + ⟦c⟧ : Mod n) = ⟦b⟧ + ⟦c⟧) : (⟦a⟧ : Mod n) = ⟦b⟧ := sorry
-/












/-
We can also use quotients with a notation that is more like regular mathematics.
For instance, to quotient a ring by an ideal we can just write `R ⧸ I` (which is implemented using
`Quotient` as we've seen above). Write `⧸` with `\quot`.
-/

example (R : Type*) [CommRing R] (I : Ideal R) : (R ⧸ I) = Quotient I.quotientRel := rfl

end Quotients









section Projects

/-
It's time to discuss projects!

Some tips:-

- Pick a topic that you're interested in, but seems like there are some small, achievable goals.

- Talk to other people! There are no requirements on group sizes, but it is always very nice to work
  on things together

- Don't be afraid to retread old ground! Getting a Mathlib contribution can be achievable if you want
  it, but many standard results are in there by now. It's still very nice to have a project where you
  prove something which may have been formalized before. E.g. one group in the past started their
  project trying to formalize a proof of the binomial theorem, and tried generalizing results from
  there.

- That said, if you end up doing something which you think could go in Mathlib, we'll definitely help
  you get it in there!
  Ivan's Mathlib result: https://github.com/leanprover-community/mathlib4/pull/32185
  Pre-Mathlib version: https://github.com/IvanRenison/colorable_two_of_IsAcyclic/blob/master/ColorableTwoOfIsAcyclic/Lemma.lean

- If you want some inspiration, we have the `Projects` folder where we have templates for
  projects (one where we show all Euclidean domains are PIDs, and one where we show
  Wilson's theorem). You can definitely do these as your project if you like, but in general
  you're probably going to have a better time if you do a project in which you have some
  personal investment

- Ansar also did a nice project last year, which he'll talk about now to give you some more inspiration

-/

end Projects
