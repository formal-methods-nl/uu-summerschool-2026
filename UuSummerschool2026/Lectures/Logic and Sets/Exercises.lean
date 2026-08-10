import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Image

open Set Function

section

/-!
# Logic exercises

Try and fill in the following `sorry`s.
-/

example (p q r : Prop) : (p → q) → (p → r) → p → q := sorry

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := sorry

example (p q r s : Prop) : (p → (q → r)) → (p → (r → s)) → (p → (q → s)) := sorry

example (p q : Prop) : (p → q) → (p → ¬ q) → ¬ p := sorry

example (α β : Type) (p : α → β → Prop) : (∀ x y, p x y) → ∀ y x, p x y := sorry

example (α : Type) (p q : α → Prop) :
    (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x := sorry

example (α β : Type) (p : α → β → Prop) (h : ∃ x, ∀ y, p x y) : ∀ y, ∃ x, p x y := sorry

example (α : Type) (p : α → Prop) (h : ∀ x, ¬ p x) : ¬ ∃ x, p x := sorry

example (α : Type) (p : α → Prop) (h : ∃ x, ¬ p x) : ¬ ∀ x, p x := sorry

example (α : Type) (p : α → Prop) (h : ¬ ∀ x, p x) : ∃ x, ¬ p x := sorry

example (α : Type) (p : α → Prop) (h : ¬ ∃ x, p x) : ∀ x, ¬ p x := sorry

example (p q q' : Prop) (h : p ∧ q) (hq : q → q') : p ∧ q' := sorry

example (p : Prop) (h : p ∨ p) : p := sorry

example (α : Type) (p : α → Prop) (q : Prop) (h : ∃ x, p x ∨ q) : (∃ x, p x) ∨ q := sorry

example (p q r : Prop) (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ r := sorry


end

section

/-!
# Set exercises

Try and fill in the following `sorry`s.
-/

variable {α β : Type*} (s t u : Set α)

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := sorry

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := sorry

example : (s \ t) \ u ⊆ s \ (t ∪ u) := sorry

example : s \ (t ∪ u) ⊆ (s \ t) \ u := sorry

example : s ∩ t = t ∩ s := sorry

example : s ∪ s = s := sorry

example : s ∪ s ∩ t = s := sorry

variable {I : Type*}
variable (A B : I → Set α)

/-
Not only can we take the union of sets, but given some indexing type `I` and
a family of sets `A : I → Set α`, we can take the *indexed union* `⋃ i : I, A i`.

Note: this is a different symbol than the usual union, and is written with `\U` or
`\Union` (note these both have capital Us).

We have something very similar with intersection, with the big `⋂` being written `\I`
or `\Inter`.
-/

#check mem_iUnion
#check mem_iInter

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := sorry

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := sorry

end

section
variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := sorry

example : f '' (s ∪ t) = f '' s ∪ f '' t := sorry

example : s ⊆ f ⁻¹' (f '' s) := sorry

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := sorry

/-
We have not yet seen injective (or surjective) functions. Control click (or command click
on mac) on `Injective` to jump to the definition.

Note that these are both defined as forall statements, so we can use `specialize` and
`intro` on them directly without even unfolding them.
-/
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by sorry

example : f '' (f ⁻¹' u) ⊆ u := sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := sorry

end
