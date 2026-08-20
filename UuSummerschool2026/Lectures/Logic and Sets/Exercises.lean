import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Image

open Set Function

section Logic

/-!
# Logic exercises

Try and fill in the following `sorry`s.
-/

example (p q r : Prop) : (p → q) → (p → r) → p → q := by
  intro hpq hpr hp
  specialize hpq hp
  assumption

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  have hq := hpq hp
  have hr := hqr hq
  exact hr

example (p q r s : Prop) : (p → (q → r)) → (p → (r → s)) → (p → (q → s)) := by
  intro hpqr hprs hp hq
  have hr := hpqr hp hq
  have hs := hprs hp hr
  exact hs

example (p q : Prop) : (p → q) → (p → ¬ q) → ¬ p := by
  intro hpq hpnq hp
  have hq  := hpq  hp
  have hnq := hpnq hp
  exact absurd hq hnq

example (α β : Type) (p : α → β → Prop) : (∀ x y, p x y) → ∀ y x, p x y := by
  intro hpab hb ha
  exact hpab ha hb

example (α : Type) (p q : α → Prop) : (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x := by
  intro hpx hpx2qx ha
  have hpa := hpx ha
  have hqa := (hpx2qx ha) hpa
  exact hqa

example (α β : Type) (p : α → β → Prop) (h : ∃ x, ∀ y, p x y) : ∀ y, ∃ x, p x y := by
  intro b
  obtain ⟨ha, hak⟩ := h
  specialize hak b
  use ha

example (α : Type) (p : α → Prop) (h : ∀ x, ¬ p x) : ¬ ∃ x, p x := by
  intro hpx
  obtain ⟨ha, hpa⟩ := hpx
  have hnpa := h ha
  exact absurd hpa hnpa

example (α : Type) (p : α → Prop) (h : ∃ x, ¬ p x) : ¬ ∀ x, p x := by
  intro hpx
  obtain ⟨ha, hnpa⟩ := h
  have hpa := hpx ha
  exact absurd hpa hnpa

example (α : Type) (p : α → Prop) (h : ¬ ∀ x, p x) : ∃ x, ¬ p x := by
  push Not at h
  exact h

example (α : Type) (p : α → Prop) (h : ¬ ∃ x, p x) : ∀ x, ¬ p x := by
  push Not at h
  exact h

example (p q q' : Prop) (h : p ∧ q) (hqq' : q → q') : p ∧ q' := by
  obtain ⟨hp, hq⟩ := h
  have hq' := hqq' hq
  exact ⟨hp, hq'⟩

example (p : Prop) (h : p ∨ p) : p := by
  cases h with
  | inl hp => exact hp
  | inr hp => exact hp

example (α : Type) (p : α → Prop) (q : Prop) (h : ∃ x, p x ∨ q) : (∃ x, p x) ∨ q := by
  obtain ⟨ha, hak⟩ := h
  obtain hpa | hq := hak
  · left
    use ha
  · right
    exact hq

example (p q r : Prop) (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ r := by
  constructor
  · intro hp
    exact hqr.mp (hpq.mp hp)
  · intro hr
    exact hpq.mpr (hqr.mpr hr)

end

section Set

/-!
# Set exercises

Try and fill in the following `sorry`s.
-/

variable {α β : Type*} (s t u : Set α)

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro ha hak
  obtain ⟨ha_s, ha_tUu⟩ := hak
  obtain ha_t | ha_u := ha_tUu
  · left
    exact ⟨ha_s, ha_t⟩
  · right
    exact ⟨ha_s, ha_u⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro ha hak
  obtain ha_sAt | ha_sAu := hak
  · obtain ⟨ha_s, ha_t⟩ := ha_sAt
    constructor
    · exact ha_s
    · left
      exact ha_t
  · obtain ⟨ha_s, ha_u⟩ := ha_sAu
    constructor
    · exact ha_s
    · right
      exact ha_u

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro ha hak
  obtain ⟨h1, h2⟩ := hak
  obtain ⟨h3, h4⟩ := h1
  constructor
  · exact h3
  · intro h5
    obtain h6 | h7 := h5
    · contradiction
    · contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro ha hak
  obtain ⟨ha_s, h0⟩ := hak
  constructor
  · constructor
    · exact ha_s
    · intro ha_t
      apply h0
      left
      exact ha_t
  · intro ha_u
    apply h0
    right
    exact ha_u

example : s ∩ t = t ∩ s := by
  ext ha
  constructor
  · intro ⟨ha_s, ha_t⟩
    exact ⟨ha_t, ha_s⟩
  · intro ⟨ha_t, ha_s⟩
    exact ⟨ha_s, ha_t⟩

-- example : s ∩ t = t ∩ s := by
--   ext a
--   constructor <;> intro ⟨ha_s, ha_t⟩
--   · exact ⟨ha_t, ha_s⟩
--   · exact ⟨ha_t, ha_s⟩

-- example : s ∩ t = t ∩ s := by
--   ext a
--   constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨hb, ha⟩

example : s ∪ s = s := by
  ext x
  constructor
  · intro h
    obtain h1 | h2 := h
    · exact h1
    · exact h2
  · intro h
    left
    apply h

example : s ∪ s ∩ t = s := by
  ext a
  constructor
  · intro h
    obtain a_s | a_st := h
    · exact a_s
    · exact a_st.left
  · intro a_s
    left
    exact a_s

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

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext a
  constructor
  · intro h
    apply mem_iUnion.mpr
    obtain ⟨a_s, a_A⟩ := h
    have ⟨k, a_k⟩ := mem_iUnion.mp a_A
    use k
    exact ⟨a_k, a_s⟩
  · intro h
    have ⟨k, a_ks⟩ := mem_iUnion.mp h
    refine ⟨a_ks.right, ?_⟩
    apply mem_iUnion.mpr
    use k
    exact a_ks.left

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := sorry

end

section Finale

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
