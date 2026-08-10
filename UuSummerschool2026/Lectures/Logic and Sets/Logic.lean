import Mathlib

/-!

# Lecture 1: Logic and Sets: Logic

In this first lecture, we're going to explore how to prove basic statements
in propositional and predicate logic in lean, and we're also going to see
how to work with sets and functions.

-/

section

/-!
# Prop

Throughout this talk we'll see a lot of statements of the form `p : Prop`, so we
should say something about what this means.

`p : Prop` just means that `p` is a type with either zero or one inhabitants. The
inhabitants should be interpreted as proofs of the proposition encoded by `p`.

This makes for quite a convenient encoding of logic since, as we'll see, we can encode
the usual logical operations in terms of operations like functions and products.

Below are some examples of elements of `Prop`:
-/

/-
This encodes the following fact the following fact:

Given an arbitrary proposition `p`, `p` implies `p`.
-/
example (p : Prop) : Prop := p → p

/-
Note that a proposition does not need to be true to be well typed! It just means that we
cannot construct an inhabitnt of this type (i.e. a proof of this proposition).
-/
example : Prop := ∀ n : ℕ, 2*n = n

example (s : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |s n - L| < ε

/-!
## Logical connectives, some examples

The way we prove a statement in logic depends a little bit on the *logical
connectives* involved, so we'll organise our discussion around that. First,
let's discuss *implication*.
-/


/-! ### Implications
An implication `p → q` is encoded by a function from `p` to `q`, the idea being that
one can view such an implication as a machine which turns a proof of `p` into a proof
of `q`.

To write the symbol `→`, use `\to`.

Relevant tactics:

When in goal: `intro`/`intros`
When in hypothesis: `have` or `specialize`
-/

example (p : Prop) : p → p := fun a ↦ a /-by
  intro hp
  exact hp-/


lemma ex (p q : Prop) : p → (q → p) := by
  intro hp hq
  exact hp

#print ex


example (p q r : Prop) : (p → q) → ((p → (q → r)) → (p → r)) := by
  intro pq pqr hp
  have hq : q := pq hp
  --specialize pq hp
  specialize pqr hp hq
  assumption


/-
Note that the above work did not really rely at all on the types in question being
propositions, and we could have just as easily given similar definitions for more
general types (i.e. types which may have more than one inhabitant).
-/

example {α : Type*} : α → α := by
  intro a
  exact a

example (α β : Type*) : α → (β → α) := fun a _ ↦ a

example (α β γ : Type*) : (α → β) → ((α → (β → γ)) → (α → γ)) := sorry


/-! ### Universal quantification
Forall statements are also encoded by functions, but where the
codomain may depend on the bound variable.
Practially speaking, this means that dealing with foralls is
very similar to dealing with implications.

To write the `∀` symbol, use `\forall`

The same tactics used in implications are relevant here.
-/

/-
This is just another way of writing our first example
-/
example : ∀ p : Prop, p → p := by
  intro p hp
  exact hp


example (α : Type) (p q : α → Prop) (h : ∀ x, p x → q x) :
    (∀ x, p x) → ∀ x', q x' := by
  intro hp
  intro x'
  specialize hp x'
  specialize h x' hp
  assumption




/-! ### Existential quantifier
A proof of an existential statemtent `∃ x, p x`
is a pair of an *example* `x` and
a proof that `p x` holds.

To write the `∃` symbol, use `\exists`

Relevant tactics:

When in goal: `use`
When in hypothesis: `obtain`
-/

example : ∃ n : ℕ, n < n + 1 := by
  use 0
  omega

example : ∃ n : ℕ, n < n + 1 := ⟨0, by omega⟩

example : ∃ n : ℕ, n = n := sorry

lemma ex2 (f : ℕ → ℕ)
    (hf : ∀ m, ∃ n, m ≤ f n) :
    ∀ m, ∃ n, m ≤ 2 * f n := by
  intro m
  specialize hf m
  obtain ⟨n, hn⟩ := hf
  use n
  omega


/-! ### Conjunctions

To prove a conjunction `a ∧ b`,
we need to provide a proof of `a`
and a proof of `b`.

To write the `∧` symbol, use `\and`

Relevant tactics:

When in goal: `constructor` (or `use`)
When in hypothesis: `obtain`

If `h : p ∧ q` then `h.1 : p` and `h.2 : q`.
We can also say `h.left` or `h.right`
-/

example (p q : Prop) : p → q → p ∧ q := by
  intro hp hq
  constructor
  · exact hp
  · assumption



example (p q : Prop) : p ∧ q → q ∧ p := by
  --intro pq
  --obtain ⟨hp, hq⟩ := pq
  rintro ⟨hp, hq⟩
  constructor
  · exact hq
  · exact hp

/-! ### Disjunctions
To prove a disjunction `a ∨ b`,
we need to either prove `a` or `b`.

To write the `∨` sumbol, use `\or`

Relevant tactics:

When in goal: `left`/`right`
When in hypothesis: `obtain`
-/

example (p q : Prop) : p → p ∨ q := by
  intro hp
  left
  exact hp


example (p q : Prop) : p ∨ q → q ∨ p := by
  intro pq
  obtain h | h := pq
  · right
    assumption
  · left
    assumption


/-! ### Iffs

To prove an iff statement `p ↔ q`, we need to prove `p → q` and `q → p`.

To write the `↔` symbol, use `\iff`

Relevant tactics:

When in goal: `constructor`/`use`

When in hypothesis: `rw`/`simp`/etc. since we
can rewrite with `↔` statements.

If `h : p ↔ q` then `h.mp : p → q` and `h.mpr : q → p`
-/

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) := by
  constructor
  · intro pq
    rw[pq]
    constructor
    · intro hq
      exact hq
    · intro hq
      exact hq
  · intro h
    constructor
    · exact h.left
    · exact h.right


/-! ### Negation
`¬ p` is actually *defined* in lean to be `p → False`. So we can just work with
it like any other implication.

To write the `¬` symbol, use `\not`

Relevant tactics:

When in goal: `intro`
When in hypothesis: `apply` (if goal is `False`), `have`

-/

/-
Here is an example showing `¬ p` and `p → False` really give the same thing.
-/
example (p : Prop) : ¬ p ↔ (p → False) := Iff.rfl

example (p q : Prop) (h : p → q) : ¬ q → ¬ p := by
  intro nq
  intro hp
  specialize h hp
  exact nq h


/-
From `False` we can derive anything, and we have a few different methods for showing this.
-/
example (p q : Prop) (hp : p) (hpq : ¬ p) : q := by
  exact absurd hp hpq
  -- or contradiction
  -- or exact (hpq hp).elim

/-
Note: `contrapose!` and `push_neg` are useful for manipulating negations too.
-/

example (p : Prop) (hp : ¬ ¬ p) : p := by
  push_neg at hp
  exact hp

example (p q : Prop) (h : ¬ p → ¬ q) : q → p := by
  contrapose
  exact h
