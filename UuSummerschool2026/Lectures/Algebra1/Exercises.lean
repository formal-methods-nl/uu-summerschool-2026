/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib

/-!
# Exercises for algebraic structures and typeclasses

In the following exercises, you will become more acquainted with various algebraic
structures. These exercises are adapted from some notes of Kevin Buzzard's.

Note that there is rather a large spread of exercises here across several different topics in
algebra. This is to give some impression of how different algebraic structures are set up,
as well as to cater to different mathematical backgrounds. Feel free to skip around this file
and not do everything chronologically
-/

section Subgroups

-- let `G` be a group
variable (G : Type) [Group G]

-- The type of subgroups of `G` is `Subgroup G`

-- Let `H` be a subgroup of `G`
variable (H : Subgroup G)

-- Just like subsets, elements of the subgroup `H` are terms `g` of type `G`
-- satisfying `g ∈ H`.

example (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  exact H.mul_mem ha hb -- I found this with `exact?` and then used dot notation.


example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * b⁻¹ * 1 * (a * c) ∈ H := by
  sorry

/-

## Lattice notation for sub-things

Given two subgroups of a group, we can look at their intersection
(which is a subgroup) and their union (which in general isn't).
This means that set-theoretic notations such as `∪` and `∩` are not
always the right concepts in group theory. Instead, Lean uses
"lattice notation". The intersection of two subgroups `H` and `K` of `G`
is `H ⊓ K`, and the subgroup they generate is `H ⊔ K`. To say
that `H` is a subset of `K` we use `H ≤ K`. The smallest subgroup
of `G`, i.e., {e}, is `⊥`, and the biggest subgroup (i.e. G, but
G is a group not a subgroup so it's not G) is `⊤`.

-/

-- intersection of two subgroups, as a subgroup
example (H K : Subgroup G) : Subgroup G := H ⊓ K
-- note that H ∩ K *doesn't work* because `H` and `K` don't
-- have type `Set G`, they have type `Subgroup G`. Lean
-- is very pedantic!

example (H K : Subgroup G) (a : G) : a ∈ H ⊓ K ↔ a ∈ H ∧ a ∈ K := by
  -- true by definition!
  rfl

-- Note that `a ∈ H ⊔ K ↔ a ∈ H ∨ a ∈ K` is not true; only `←` is true.
/-
  Take apart the `Or` and use `exact?` to find the relevant lemmas.
  While `exact?` is running, see if you can find the relevant lemma first on `loogle`
-/
example (H K : Subgroup G) (a : G) : a ∈ H ∨ a ∈ K → a ∈ H ⊔ K := by

  sorry

end Subgroups


/-
New section, meaning all the variables declared above are no longer in scope
-/

section Homomorphisms

-- Let `G` and `H` be groups
variable (G H : Type) [Group G] [Group H]

-- Let `φ` be a group homomorphism
variable (φ : G →* H)

-- `φ` preserves multiplication

example (a b : G) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b -- this is the term: no `by`

example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  -- if `φ.map_mul` means that `φ` preserves multiplication
  -- (and you can rewrite with this) then what do you think
  -- the lemmas that `φ` preserves inverse and one are called?
  sorry

-- Group homomorphisms are extensional: if two group homomorphisms
-- are equal on all inputs the they're the same.

example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  -- Use the `ext` tactic.
  sorry

end Homomorphisms


/-
## Interlude: which structure do you actually need?

The point of the algebraic hierarchy is that a lemma should be stated using the
*weakest* structure for which it is true. Then it applies as widely as possible.

In the next few exercises, try the proof and then experiment: change the typeclass
assumption to something weaker (`Group` → `Monoid`, `CommRing` → `Ring`, ...) and
see which proofs still go through. Lean will tell you when you've gone too far.
-/

section Generality

-- In a monoid there is no `⁻¹`, so we have to *assume* inverses as hypotheses.
-- Show that inverses, when they exist, are unique.
-- (This is exactly why `Group.inv` is well-behaved, and why `mul_one` followed
-- from `one_mul` in the lecture.)
example {M : Type} [Monoid M] (a b c : M) (hab : a * b = 1) (hca : c * a = 1) :
    b = c := by
  -- Hint: start from `b`, insert `1 = c * a`, and use `mul_assoc`.
  -- A `calc` block could be a nice way to write this.
  sorry

-- Now the group version. Once you've done it, try weakening `Group` to `Monoid`
-- and see exactly which step fails.
example {G : Type} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

-- This one is true in every `Ring`, but the `ring` tactic needs commutativity.
-- Try `ring` first, watch it fail, then try `noncomm_ring`.
example {R : Type} [Ring R] (a b : R) :
    (a + b) * (a + b) = a * a + a * b + b * a + b * b := by

  sorry

end Generality


section Rings

/-
## Rings

We now work with a commutative ring `R`. Familiar examples: `ℤ`, `ℚ`, `ℝ`,
`ZMod n`, or polynomial rings.
-/

variable {R : Type} [CommRing R]

/-
The `ring` tactic is very helpful in rings (unsurprisingly), but cannot apply hypotheses on its own
-/
example (a b : R) (h : a = b) : a * a - b * b = 0 := by
  sorry

/-
Now let's prove something from the axioms rather than letting `ring` do it.
The point is to see that `a * 0 = 0` is *not* an axiom: it is forced by
distributivity together with the additive group structure.

Try to do this without using `mul_zero`, `simp` or `grind`.
-/
example (a : R) : a * 0 = 0 := by
  -- Hint: first show `a * 0 + a * 0 = a * 0 + 0`, using `mul_add`/`add_zero`.
  -- Then `add_left_cancel` finishes the job.
  sorry

-- Similarly, a ring in which `1 = 0` has only one element.
example (h : (1 : R) = 0) (a : R) : a = 0 := by
  sorry

/-
## Subrings

A subring of `R` is a subset closed under `+`, `*`, `-` containing `0` and `1`.
The type is `Subring R`, and the API deliberately mirrors `Subgroup` above:
`S.mul_mem`, `S.add_mem`, `S.neg_mem`, `S.one_mem`, and the lattice notation
`⊓`, `⊔`, `≤`, `⊥`, `⊤`.
-/

example (S : Subring R) (a b : R) (ha : a ∈ S) (hb : b ∈ S) : a * b - a + 1 ∈ S := by
  sorry

/-
## Ideals

Reminder: an ideal is *not* a subring: it is closed under multiplication by arbitrary ring
elements, but need not contain `1`. In Lean the type is `Ideal R`.

The key extra closure property is `Ideal.mul_mem_left`.
-/

example (I : Ideal R) (a r : R) (ha : a ∈ I) : r * a ∈ I := by
  sorry

-- An ideal containing `1` is everything. (Look for `Ideal.eq_top_iff_one`.)
example (I : Ideal R) (h : (1 : R) ∈ I) : I = ⊤ := by
  sorry

-- Harder: an ideal containing *any* unit is everything.
-- Recall `IsUnit u` means `∃ v, u * v = 1`; `isUnit_iff_exists_inv` unpacks it.
example (I : Ideal R) (u : R) (hu : IsUnit u) (huI : u ∈ I) : I = ⊤ := by
  sorry


example {K : Type} [Field K] (I : Ideal K) : I = ⊥ ∨ I = ⊤ := by
  -- Hint: split on whether `I = ⊥`. If not, `Submodule.ne_bot_iff` gives you a
  -- nonzero element of `I`, and every nonzero element of a field is a unit.
  sorry

end Rings


section RingHomomorphisms

variable {R T : Type} [CommRing R] [CommRing T]

-- A ring homomorphism preserves `+`, `*`, `0` and `1`. Note the notation `→+*`:
-- it is literally "additive hom and multiplicative hom".
variable (φ : R →+* T)

example (a b : R) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b

-- You can use `exact?` or `loogle` to find this lemma, or use `simp`
-- If you want to see which lemmas `simp` is using, use `simp?`
example : φ 0 = 0 := by

  sorry

/-
`simp` knows a lot of such lemmas, use `simp?` here
-/
example (a b : R) : φ (a * a - b + 1) = φ a * φ a - φ b + 1 := by

  sorry

-- Ring homomorphisms are extensional, just like group homomorphisms.
example (φ ψ : R →+* T) (h : ∀ r : R, φ r = ψ r) : φ = ψ := by
  -- use the `ext` tactic
  sorry

/-
The kernel of `φ` is `RingHom.ker φ`, and it is an *ideal*, not a subring
(compare: the kernel of a group hom is a subgroup). Membership is
`RingHom.mem_ker`.
-/

example (a : R) : a ∈ RingHom.ker φ ↔ φ a = 0 := by
  sorry

-- Harder: `φ` identifies `a` and `b` exactly when their difference is in the kernel.
example (a b : R) : φ a = φ b ↔ a - b ∈ RingHom.ker φ := by
  sorry

end RingHomomorphisms


section VectorSpaces

/-
## Vector spaces

There is no `VectorSpace` class in Mathlib! A vector space over a field `K` is
recorded as an `AddCommGroup V` (you can add and negate vectors) together with
a `Module K V` (you can scale them).

If you don't know what a `Module` is, then I'll lie and say it's French for vector space.
This understanding is sufficient for the exercises below.

If you do know what a `Module` is, note this is a good illustration of how the
hierarchy is factored: `Module` also covers modules over rings, and the field
assumption is only added where it is actually needed. So one doesn't really
need a `VectorSpace` class if they already have a `Module` class.
-/

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

-- The module axioms. Guess the names, or use `exact?`.
example (a : K) (v w : V) : a • (v + w) = a • v + a • w := by
  sorry

example (a b : K) (v : V) : (a * b) • v = a • b • v := by
  sorry

example (v : V) : (0 : K) • v = 0 := by
  sorry

-- Now one that does not follow directly from an axiom.
example (v : V) : (-1 : K) • v = -v := by

  -- Hint: show `v + (-1 : K) • v = 0` and use `neg_eq_of_add_eq_zero_left`,
  -- or if you're feeling lazy, find the one-step lemma with `exact?`.
  sorry

/-
Note: here you will need to use that `K` is a field, this is not true over an arbitrary
ring.
-/
example (a : K) (v : V) (ha : a ≠ 0) (h : a • v = 0) : v = 0 := by
  -- Hint: multiply through by `a⁻¹`. Useful: `inv_mul_cancel₀`, `mul_smul`,
  -- `one_smul`, `smul_zero`.
  sorry

/-
## Subspaces

A linear subspace is a `Submodule K V` — again the same shape of API as
`Subgroup` and `Subring`: `W.add_mem`, `W.smul_mem`, `W.zero_mem`, and the
lattice operations `⊓`, `⊔`, `≤`, `⊥`, `⊤`.
-/

example (W : Submodule K V) (v w : V) (hv : v ∈ W) (hw : w ∈ W) (a b : K) :
    a • v + b • w ∈ W := by
  sorry

-- As for subgroups, `⊔` is the subspace *generated by* the union, so only one
-- direction holds here.
example (W₁ W₂ : Submodule K V) (v : V) (h : v ∈ W₁ ∨ v ∈ W₂) : v ∈ W₁ ⊔ W₂ := by
  sorry

end VectorSpaces


section LinearMaps

variable {K V W : Type} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

-- A linear map is written `V →ₗ[K] W`. The `[K]` is needed because a single
-- pair of abelian groups can be modules over several different rings at once.
variable (f : V →ₗ[K] W)

example (a : K) (v w : V) : f (a • v + w) = a • f v + f w := by
  sorry

-- `LinearMap.ker f` and `LinearMap.range f` are submodules.
-- Membership: `LinearMap.mem_ker`, `LinearMap.mem_range`.
example (v : V) : v ∈ LinearMap.ker f ↔ f v = 0 := by
  sorry

-- Harder: if `f ∘ f = 0` then the image of `f` sits inside its kernel.
-- Hint: to prove `≤` between submodules, use `intro` after `rintro`-ing a
-- membership, or start with `rintro w ⟨v, rfl⟩`.
example (g : V →ₗ[K] V) (h : ∀ v, g (g v) = 0) :
    LinearMap.range g ≤ LinearMap.ker g := by
  sorry

/-
A standard first-course theorem: a linear map is injective iff its kernel is
trivial. Note that this is *false* for general functions, and for group
homomorphisms it becomes the statement about `⊥` you may have seen above —
another instance of the same pattern recurring across the hierarchy.
-/
example : LinearMap.ker f = ⊥ ↔ Function.Injective f := by
  -- Hint: for `→`, given `f a = f b`, show `a - b ∈ ker f`.
  -- `Submodule.mem_bot` and `sub_eq_zero` will be useful.
  sorry

end LinearMaps


namespace BooleanRing

/-
## Boolean rings

A ring is *Boolean* if every element is idempotent: `x * x = x` for all `x`.
The power set of a set is an example, with symmetric difference as addition and
intersection as multiplication.

We are going to show that any such ring is automatically commutative. Note that
because we're not explicitly assuming commutativity, you should use `noncomm_ring`
instead of `ring` if you ever want such a tactic here.
-/

variable {R : Type} [Ring R]

-- Step 1: in a Boolean ring, every element is its own negative.
lemma add_self_eq_zero (h : ∀ x : R, x * x = x) (x : R) : x + x = 0 := by
  -- Hint: apply `h` to `x + x` and expand the left-hand side with
  -- `mul_add` and `add_mul`. Then cancel.
  sorry

-- Step 2: deduce commutativity. You may use step 1, which is now available
-- under the name `add_self_eq_zero`.
lemma mul_comm_of_sq_eq_self (h : ∀ x : R, x * x = x) (x y : R) :
    x * y = y * x := by

  -- Hint: apply `h` to `x + y` and expand as before. After cancelling `x` and
  -- `y` you should be left with `y * x + x * y = 0`. Now compare that with
  -- `add_self_eq_zero h (y * x)`.
  --
  -- To rearrange a sum along the way you can use `abel`, which is the additive
  -- analogue of `ring`: it normalises in an `AddCommGroup`, treating the
  -- products `x * y` and `y * x` as opaque atoms. This is the same story as
  -- above, one level down: the tactic you reach for is dictated by the
  -- structure you have. `ring` wants a `CommRing` and fails here, and
  -- `noncomm_ring` will tell you outright to use `abel` instead.


  sorry

end BooleanRing
