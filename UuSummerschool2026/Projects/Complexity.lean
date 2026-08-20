import Mathlib



section Reverse

def slow_reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => slow_reverse xs ++ [x]

def fast_reverse_acc {α : Type} : List α → List α → List α
  | []     , acc => acc
  | x :: xs, acc => fast_reverse_acc xs (x :: acc)

def fast_reverse {α : Type} (xs : List α) : List α := fast_reverse_acc xs []

end Reverse



section CallGraphs

inductive LAppend {α : Type} : List α → List α → List α → Type where
  | base {ys : List α}               :                    LAppend []        ys ys
  | step {xs ys zs : List α} {x : α} : LAppend xs ys zs → LAppend (x :: xs) ys (x :: zs)

inductive SlowReverse {α : Type} : List α → List α → Type where
  | base                             : SlowReverse [] []
  | step {xs ys zs : List α} {x : α} : SlowReverse xs        ys
                                     → LAppend     ys [x]    zs
                                     → SlowReverse (x :: xs) zs

inductive FastReverseAcc {α : Type} : List α → List α → List α → Type where
  | base {ys : List α}               :                                  FastReverseAcc []        ys ys
  | step {xs ys zs : List α} {x : α} : FastReverseAcc xs (x :: ys) zs → FastReverseAcc (x :: xs) ys zs

inductive FastReverse {α : Type} : List α → List α → Type where
  | run {xs ys : List α} : FastReverseAcc xs [] ys → FastReverse xs ys

end CallGraphs



section Properties

lemma LAppend.sound {α : Type} {xs ys zs : List α}
  : LAppend xs ys zs → xs ++ ys = zs := by
  intro app
  induction app with
  | base      => rfl
  | step _ ih => simp [ih]

theorem SlowReverse.sound {α : Type} {xs ys : List α}
  : SlowReverse xs ys → slow_reverse xs = ys := by
  intro rev
  induction rev with
  | base => rfl
  | step rev app ih => simp [slow_reverse, ih, LAppend.sound app]

lemma FastReverseAcc.sound {α : Type} {xs ys acc : List α}
  : FastReverseAcc xs acc ys → fast_reverse_acc xs acc = ys := by
  intro rev
  induction rev with
  | base      => simp [fast_reverse_acc]
  | step r ih => simp [fast_reverse_acc, ih]

theorem FastReverse.sound {α : Type} {xs ys : List α}
  : FastReverse xs ys → fast_reverse xs = ys := by
  intro rev
  cases rev with
  | run rev' => simp [fast_reverse, FastReverseAcc.sound rev']

lemma LAppend.complete {α : Type} {xs ys zs : List α}
  : xs ++ ys = zs → Nonempty (LAppend xs ys zs) := sorry

theorem SlowReverse.complete {α : Type} {xs ys : List α}
  : slow_reverse xs = ys → Nonempty (SlowReverse xs ys) := sorry

lemma FastReverseAcc.complete {α : Type} {xs ys acc : List α}
  : fast_reverse_acc xs acc = ys → Nonempty (FastReverseAcc xs acc ys) := by
  intro f
  apply Nonempty.intro
  induction xs generalizing acc ys with
  | nil          =>
    simp [fast_reverse_acc] at f
    rw [f]
    exact FastReverseAcc.base
  | cons x xs ih =>
    apply FastReverseAcc.step
    apply ih
    simp [fast_reverse_acc] at f
    exact f

theorem FastReverse.complete {α : Type} {xs ys : List α}
  : fast_reverse xs = ys → Nonempty (FastReverse xs ys) := by
  intro f
  apply Nonempty.map FastReverse.run
  exact FastReverseAcc.complete f

lemma fast_reverse_acc_eq_slow_reverse_append {α : Type} {xs acc : List α}
  : fast_reverse_acc xs acc = slow_reverse xs ++ acc := by
  induction xs generalizing acc with
  | nil          => rfl
  | cons x xs ih => simp [fast_reverse_acc, slow_reverse, ih, List.append_assoc]

theorem fast_reverse_eq_slow_reverse {α : Type} {xs : List α}
  : fast_reverse xs = slow_reverse xs := by
  unfold fast_reverse
  simp [fast_reverse_acc_eq_slow_reverse_append]

lemma LAppend.preserves_length {α : Type} {xs ys zs : List α} (lapp : LAppend xs ys zs)
  : zs.length = xs.length + ys.length := by
  induction lapp with
  | base      => simp
  | step _ ih =>
    simp [ih]
    omega

theorem SlowReverse.preserves_length {α : Type} {xs ys : List α} (rev : SlowReverse xs ys)
  : ys.length = xs.length := by
  induction rev with
  | base           => rfl
  | step _ lapp ih => simp [LAppend.preserves_length lapp, ih]


end Properties



section Cost

def LAppend.cost {α : Type} {xs ys zs : List α} : LAppend xs ys zs → ℕ
  | .base     => 1
  | .step lapp => 1 + LAppend.cost lapp

def SlowReverse.cost {α : Type} {xs ys : List α} : SlowReverse xs ys → ℕ
  | .base          => 1
  | .step rev lapp => 1 + SlowReverse.cost rev + LAppend.cost lapp

def FastReverseAcc.cost {α : Type} {xs ys zs : List α} : FastReverseAcc xs ys zs → ℕ
  | .base     => 1
  | .step rev => 1 + FastReverseAcc.cost rev

def FastReverse.cost {α : Type} {xs ys : List α} : FastReverse xs ys → ℕ
  | .run rev => FastReverseAcc.cost rev

lemma LAppend.exact_steps {α : Type} {xs ys zs : List α} (lapp : LAppend xs ys zs)
  : LAppend.cost lapp = 1 + xs.length := by
  induction lapp with
  | base      => simp [LAppend.cost]
  | step _ ih => simp [LAppend.cost, ih, Nat.add_comm]

theorem SlowReverse.exact_steps {α : Type} {xs ys : List α} (rev : SlowReverse xs ys)
  : SlowReverse.cost rev = 1 + xs.length + xs.length * (xs.length + 1) / 2 := by
  induction rev with
  | base             => simp [SlowReverse.cost]
  | step rev lapp ih =>
      simp only [SlowReverse.cost, ih]
      simp [LAppend.exact_steps lapp, SlowReverse.preserves_length rev]
      grind

lemma FastReverseAcc.exact_steps {α : Type} {xs ys zs : List α} (rev : FastReverseAcc xs ys zs)
  : FastReverseAcc.cost rev = 1 + xs.length := by
  induction rev with
  | base        => rfl
  | step rev ih => simp [FastReverseAcc.cost, ih, Nat.add_comm]

theorem FastReverse.exact_steps {α : Type} {xs ys : List α} (rev : FastReverse xs ys)
  : FastReverse.cost rev = 1 + xs.length := by
  cases rev with
  | run rev => exact FastReverseAcc.exact_steps rev

end Cost



section Complexity

class Size₁ (A : Type) where
  size : A → ℕ

class Size₂ {A B : Type} (P : A → B → Type) where
  size : {x : A} → {y : B} → P x y → Nat

notation "|" x "|₁" => Size₁.size x
notation "|" x "|₂" => Size₂.size x

def BigO {A B : Type} [Size₁ A] (G : A → B → Type) [Size₂ G] (f : ℕ → ℕ) : Prop :=
  ∃ c₀ c : ℕ,
  ∀ {x : A} {y : B} {n : ℕ},
  ∀ g : G x y,
  |x|₁ = n →
  |g|₂ ≤ c₀ + c * f n

infix:50 " ∈O " => BigO

instance {α : Type} : Size₁ (List α) where
  size := List.length

instance {α : Type} {ys : List α}: Size₂ (A := List α) (B := List α)
  (λ xs zs ↦ LAppend xs ys zs) where
  size := LAppend.cost

instance {α : Type} : Size₂ (A := List α) (B := List α) SlowReverse where
  size := SlowReverse.cost

instance {α : Type} : Size₂ (A := List α) (B := List α) FastReverse where
  size := FastReverse.cost

instance {α : Type} {acc : List α}: Size₂ (A := List α) (B := List α)
  (λ xs ys ↦ FastReverseAcc xs acc ys) where
  size := FastReverseAcc.cost

lemma LAppend.linear {α : Type} {ys : List α}
  : (λ (xs : List α) ↦ LAppend xs ys) ∈O (λ n ↦ n) := by
  unfold BigO
  refine ⟨1, 1, ?_⟩
  intro xs zs n lapp h
  induction lapp generalizing n with
  | base         => simp [Size₂.size, LAppend.cost]
  | step lapp ih =>
      specialize ih rfl
      simp [Size₁.size, Size₂.size, LAppend.cost] at *
      omega

-- TODO: reuse LAppend
theorem SlowReverse.quadratic {α : Type}
  : (λ (xs : List α) ↦ SlowReverse xs) ∈O (λ n ↦ n * n) := by
  unfold BigO
  refine ⟨1, 2, ?_⟩
  intro xs ys n rev hxs
  induction rev generalizing n with
  | base                            => simp [Size₁.size, Size₂.size, SlowReverse.cost] at *
  | @step xs' ys' zs' x rev lapp ih =>
      simp [Size₁.size, Size₂.size, SlowReverse.cost, SlowReverse.preserves_length rev, LAppend.exact_steps lapp] at *
      nlinarith

theorem FastReverseAcc.linear {α : Type} {acc : List α}
  : (λ (xs : List α) ↦ FastReverseAcc xs acc) ∈O (λ n ↦ n) := by
    unfold BigO
    refine ⟨1, 1, ?_⟩
    intro xs ys n rev h
    induction rev generalizing n with
    | base      => simp [Size₂.size, FastReverseAcc.cost]
    | step _ ih =>
      specialize ih rfl
      simp [Size₁.size, Size₂.size, FastReverseAcc.cost] at *
      omega

theorem FastReverse.linear {α : Type}
  : (λ (xs : List α) ↦ FastReverse xs) ∈O (λ n ↦ n) := by
  unfold BigO
  rcases FastReverseAcc.linear with ⟨c₀, c, h⟩
  refine ⟨c₀, c, ?_⟩
  intro xs ys n rev hxs
  cases rev with
  | run rev => exact h rev hxs

end Complexity



section Amortization

-- *crickets*

end Amortization
