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
  | base {ys : List α}               : LAppend []        ys ys
  | step {xs ys zs : List α} {x : α} : LAppend xs        ys zs
                                     → LAppend (x :: xs) ys (x :: zs)

inductive SlowReverse {α : Type} : List α → List α → Type where
  | base                             : SlowReverse []        []
  | step {xs ys zs : List α} {x : α} : SlowReverse xs        ys
                                     → LAppend     ys [x]    zs
                                     → SlowReverse (x :: xs) zs

inductive FastReverseAcc {α : Type} : List α → List α → List α → Type where
  | base {ys : List α}               : FastReverseAcc []        ys        ys
  | step {xs ys zs : List α} {x : α} : FastReverseAcc xs        (x :: ys) zs
                                     → FastReverseAcc (x :: xs) ys        zs

inductive FastReverse {α : Type} : List α → List α → Type where
  | run {xs ys : List α} : FastReverseAcc xs [] ys
                         → FastReverse    xs    ys

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
  : xs ++ ys = zs → Nonempty (LAppend xs ys zs) := by
  intro f
  apply Nonempty.intro
  induction xs generalizing ys zs with
  | nil          =>
    simp [· ++ ·] at f
    simp [Append.append] at f
    rw [f]
    exact LAppend.base
  | cons x xs ih =>
    rw [List.cons_append] at f
    subst zs
    apply LAppend.step
    exact ih rfl

-- NOTE: I couldn't figure out how to `Nonempty.intro` like in `FastReverse.complete`
theorem SlowReverse.complete {α : Type} {xs ys : List α}
  : slow_reverse xs = ys → Nonempty (SlowReverse xs ys) := by
  intro f
  apply Nonempty.intro
  induction xs generalizing ys with
  | nil =>
    simp [slow_reverse] at f
    rw [f]
    exact SlowReverse.base
  | cons x xs ih =>
    simp [slow_reverse] at f
    apply SlowReverse.step (ih rfl)
    apply Classical.choice
    exact LAppend.complete f

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

-- TODO: don't grind
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

notation "₁|" x "|₁" => Size₁.size x
notation "₂|" x "|₂" => Size₂.size x

def BigO {A B : Type} [Size₁ A] (G : A → B → Type) [Size₂ G] (f : ℕ → ℕ) : Prop :=
  ∃ c₀ c : ℕ,
  ∀ {x : A} {y : B} {n : ℕ},
  ∀ g : G x y,
  ₁|x|₁ = n →
  ₂|g|₂ ≤ c₀ + c * f n

infix:50 " ∈O " => BigO

instance {α : Type} : Size₁ (List α) where
  size := List.length

instance {α : Type} {ys : List α} : Size₂ (A := List α) (B := List α)
  (λ xs zs ↦ LAppend xs ys zs) where
  size := LAppend.cost

instance {α : Type} : Size₂ (A := List α) (B := List α) SlowReverse where
  size := SlowReverse.cost

instance {α : Type} : Size₂ (A := List α) (B := List α) FastReverse where
  size := FastReverse.cost

instance {α : Type} {acc : List α} : Size₂ (A := List α) (B := List α)
  (λ xs ys ↦ FastReverseAcc xs acc ys) where
  size := FastReverseAcc.cost

lemma LAppend.worst_case {α : Type} {ys : List α}
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
theorem SlowReverse.worst_case {α : Type}
  : (λ (xs : List α) ↦ SlowReverse xs) ∈O (λ n ↦ n * n) := by
  unfold BigO
  refine ⟨1, 2, ?_⟩
  intro xs ys n rev hxs
  induction rev generalizing n with
  | base                            => simp [Size₁.size, Size₂.size, SlowReverse.cost] at *
  | @step xs' ys' zs' x rev lapp ih =>
    simp [Size₁.size, Size₂.size, SlowReverse.cost, SlowReverse.preserves_length rev, LAppend.exact_steps lapp] at *
    nlinarith

theorem FastReverseAcc.worst_case {α : Type} {acc : List α}
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

theorem FastReverse.worst_case {α : Type}
  : (λ (xs : List α) ↦ FastReverse xs) ∈O (λ n ↦ n) := by
  unfold BigO
  rcases FastReverseAcc.worst_case with ⟨c₀, c, h⟩
  refine ⟨c₀, c, ?_⟩
  intro xs ys n rev hxs
  cases rev with
  | run rev => exact h rev hxs

end Complexity



section Invariants

inductive Tree' : Type where
  | leaf : Tree'
  | node : Tree' → ℕ → Tree' → Tree'

-- NOTE: shouldn't this be called elem?
def find : ℕ → Tree' → Bool
  | _, .leaf => false
  | k, .node l b r =>
    if k == b then true
    else if k < b then find k l
    else find k r

def Tree'.size : Tree' → ℕ
  | .leaf       => 1
  | .node l _ r => 1 + size l + size r

instance : Size₁ Tree' where
  size := Tree'.size

inductive Find (k : ℕ) : Tree' → Bool → Type where
 | base                                                   : Find k .leaf         false
 | stop  {l r : Tree'}                                    : Find k (.node l k r) true
 | left  {l r : Tree'} {x : ℕ} {b : Bool} {hkltx : k < x} : Find k l             b
                                                          → Find k (.node l x r) b
 | right {l r : Tree'} {x : ℕ} {b : Bool} {hkgtx : k > x} : Find k r             b
                                                          → Find k (.node l x r) b

theorem Find.sound    {k : ℕ} {t : Tree'} {b : Bool} : Find k t b   → find k t = b          := sorry
theorem Find.complete {k : ℕ} {t : Tree'} {b : Bool} : find k t = b → Nonempty (Find k t b) := sorry

def Find.cost {k : ℕ} {t : Tree'} {b : Bool} : Find k t b → ℕ
  | .base      => 1
  | .stop      => 1
  | .left  f => 1 + Find.cost f
  | .right f => 1 + Find.cost f

instance {k : ℕ} : Size₂ (Find k) where
  size := Find.cost

theorem Find.worst_case {k : ℕ} : (Find k) ∈O (λ n ↦ n) := by
  unfold BigO
  refine ⟨1, 1, ?_⟩
  intro t b n find ht
  induction find generalizing n with
  | base => simp [Size₂.size, Find.cost]
  | stop => simp [Size₂.size, Find.cost]
  | @left l r x b' hklex find' ih =>
    specialize ih rfl
    simp [Size₁.size, Size₂.size, Find.cost, Tree'.size] at *
    omega
  | @right l r x b' h f ih =>
    specialize ih rfl
    simp [Size₁.size, Size₂.size, Find.cost, Tree'.size] at *
    omega

def Tree'.Balanced (l r : Tree') : Prop := Tree'.size l = Tree'.size r

inductive FindBalanced (k : ℕ) : Tree' → Bool → Type where
  | base                                                                             : FindBalanced k .leaf         false
  | stop  {l r : Tree'}                                                              : FindBalanced k (.node l k r) true
  | left  {l r : Tree'} {x : ℕ} {b : Bool} {hb : Tree'.Balanced l r} {hkltx : k < x} : FindBalanced k l             b
                                                                                     → FindBalanced k (.node l x r) b
  | right {l r : Tree'} {x : ℕ} {b : Bool} {hb : Tree'.Balanced l r} {hkgtx : k > x} : FindBalanced k r             b
                                                                                     → FindBalanced k (.node l x r) b

theorem FindBalanced.sound    {k : ℕ} {t : Tree'} {b : Bool} : FindBalanced k t b → find k t = b                  := sorry
theorem FindBalanced.complete {k : ℕ} {t : Tree'} {b : Bool} : find k t = b       → Nonempty (FindBalanced k t b) := sorry

def FindBalanced.cost {k : ℕ} {t : Tree'} {b : Bool} : FindBalanced k t b → ℕ
  | .base    => 1
  | .stop    => 1
  | .left  f => 1 + FindBalanced.cost f
  | .right f => 1 + FindBalanced.cost f

instance {k : ℕ} : Size₂ (FindBalanced k) where
  size := FindBalanced.cost

lemma Tree'.size_pos (t : Tree') : 0 < Tree'.size t := by
  cases t with
  | leaf       => simp only [Tree'.size]; omega
  | node l b r => simp only [Tree'.size]; omega

lemma nat_log2_double_add_one_le {m : ℕ} (hm : 0 < m)
  : Nat.log2 m + 1 ≤ Nat.log2 (1 + 2 * m) := by
  rw [← Nat.log2_two_mul (by omega)]
  apply (Nat.le_log2 (by omega)).mpr
  exact Nat.le_trans (Nat.log2_self_le (by omega)) (by omega)

theorem FindBalanced.worst_case {k : ℕ} : (FindBalanced k) ∈O (λ n ↦ Nat.log2 n) := by
  unfold BigO
  refine ⟨2, 1, ?_⟩
  intro t b n find ht
  induction find generalizing n with
  | base =>
    simp [Size₁.size, Size₂.size, FindBalanced.cost] at *
    omega
  | stop =>
    simp [Size₁.size, Size₂.size, FindBalanced.cost] at *
    omega
  | @left l r x b' hb hkltx find' ih =>
    unfold Tree'.Balanced at hb
    specialize ih rfl
    simp [Size₁.size, Size₂.size, FindBalanced.cost, Tree'.size] at *
    simp only [← ht, ← hb, Nat.add_assoc, ← Nat.two_mul]
    linarith [nat_log2_double_add_one_le (Tree'.size_pos l)]
  | @right l r x b' hb hkgtx find' ih =>
    unfold Tree'.Balanced at hb
    specialize ih rfl
    simp [Size₁.size, Size₂.size, FindBalanced.cost, Tree'.size] at *
    simp only [← ht, hb, Nat.add_assoc, ← Nat.two_mul]
    linarith [nat_log2_double_add_one_le (Tree'.size_pos r)]

end Invariants



section Amortized

structure Q (α : Type) where
  front : List α
  rear  : List α
  inv   : front = [] → rear = []

def Q.empty {α : Type} : Q α := ⟨[], [], fun _ => rfl⟩
def Q.credit {α : Type} (q : Q α) : ℕ := q.rear.length

def balance {α : Type} : List α × List α → Q α
  | ([], r)      => ⟨r.reverse, [], fun _ => rfl⟩
  | (x :: xs, r) => ⟨x :: xs, r, fun h => absurd h (List.cons_ne_nil x xs)⟩

def enq {α : Type} (x : α) (q : Q α) : Q α :=
  balance (q.front, x :: q.rear)

def deq {α : Type} (q : Q α) : Option (α × Q α) :=
  match q.front with
  | []      => none
  | x :: xs => some (x, balance (xs, q.rear))

inductive Balance {α : Type} : List α × List α → Q α → Type where
  | stop {x : α} {xs ys : List α} : Balance (x :: xs, ys) ⟨x :: xs, ys, fun h => absurd h (List.cons_ne_nil x xs)⟩
  | work {xs ys : List α} (rev : FastReverseAcc xs [] ys) : Balance ([], xs) ⟨ys, [], fun _ => rfl⟩

def Balance.cost {α : Type} {p : List α × List α} {q : Q α} : Balance p q → ℕ
  | .stop    => 1
  | .work rv => 1 + FastReverseAcc.cost rv

lemma Balance.cost_bound {α : Type} {front rear : List α} {q : Q α} (bal : Balance (front, rear) q)
  : rear.length ≤ Balance.cost bal + q.rear.length := by
  cases bal with
  | stop   => simp [Balance.cost]
  | work rv =>
    simp [Balance.cost]
    rw [FastReverseAcc.exact_steps rv]
    omega

instance {α : Type} : Size₁ (List α × List α) where
  size := fun p => p.2.length

instance {α : Type} : Size₂ (A := List α × List α) (B := Q α) Balance where
  size := Balance.cost

theorem Balance.worst_case {α : Type}
  : (λ (p : List α × List α) ↦ Balance p) ∈O (λ n ↦ n) := by
  unfold BigO
  refine ⟨2, 1, ?_⟩
  intro p q n bal h
  cases bal with
  | stop =>
    simp [Size₁.size, Size₂.size, Balance.cost] at *
    omega
  | work rv =>
    simp [Size₁.size, Size₂.size, Balance.cost, FastReverseAcc.exact_steps rv] at *
    omega

inductive Enq {α : Type} (x : α) : Q α → Q α → Type where
  | mk {front rear : List α} {inv} {q1 : Q α} (bal : Balance (front, x :: rear) q1) : Enq x ⟨front, rear, inv⟩ q1

def Enq.cost {α : Type} {x : α} {q0 q1 : Q α} : Enq x q0 q1 → ℕ
  | .mk bal => Balance.cost bal

inductive Deq {α : Type} : Q α → Q α → Type where
  | mk {f : α} {fs rs : List α} {inv} {q1 : Q α} (bal : Balance (fs, rs) q1) : Deq ⟨f :: fs, rs, inv⟩ q1

def Deq.cost {α : Type} {q0 q1 : Q α} : Deq q0 q1 → ℕ
  | .mk bal => Balance.cost bal

inductive Op {α : Type} : Q α → Q α → Type where
  | enq {x : α} {q0 q1 : Q α} (e : Enq x q0 q1) : Op q0 q1
  | deq {q0 q1 : Q α} (d : Deq q0 q1)         : Op q0 q1

def Op.cost {α : Type} {q0 q1 : Q α} : Op q0 q1 → ℕ
  | .enq e => Enq.cost e
  | .deq d => Deq.cost d

inductive Ops {α : Type} : Q α → Q α → Type where
  | stop {q : Q α} : Ops q q
  | step {q0 q1 q2 : Q α} (op : Op q0 q1) (ops : Ops q1 q2) : Ops q0 q2

def Ops.cost {α : Type} {q0 q1 : Q α} : Ops q0 q1 → ℕ
  | .stop        => 0
  | .step op ops => Op.cost op + Ops.cost ops

def Ops.length {α : Type} {q0 q1 : Q α} : Ops q0 q1 → ℕ
  | .stop        => 0
  | .step _ ops  => 1 + Ops.length ops

def amortized_cost_op {α : Type} {q0 q1 : Q α} (op : Op q0 q1) : ℕ :=
  Op.cost op + Q.credit q1 - Q.credit q0

def amortized_cost_ops {α : Type} {q0 q1 : Q α} : Ops q0 q1 → ℕ
  | .stop        => 0
  | .step op ops => amortized_cost_op op + amortized_cost_ops ops

theorem amortized_cost_positive {α : Type} {q0 q1 : Q α} (op : Op q0 q1)
    : Q.credit q0 ≤ Op.cost op + Q.credit q1 := by
  cases op with
  | enq e =>
    cases e with
    | mk bal =>
      simp [Op.cost, Enq.cost, Q.credit]
      have h := Balance.cost_bound bal
      simp [List.length_cons] at h
      omega
  | deq d =>
    cases d with
    | mk bal =>
      simp [Op.cost, Deq.cost, Q.credit]
      have h := Balance.cost_bound bal
      omega

theorem amortized_bound {α : Type} {q0 q1 : Q α} (op : Op q0 q1)
    : amortized_cost_op op ≤ 3 := by
  unfold amortized_cost_op
  cases op with
  | enq e =>
    cases e with
    | mk bal =>
      cases bal with
      | stop =>
        simp [Op.cost, Enq.cost, Balance.cost, Q.credit, List.length_cons]
        omega
      | work rv =>
        simp [Op.cost, Enq.cost, Balance.cost, Q.credit]
        rw [FastReverseAcc.exact_steps rv]
        simp [List.length_cons]
        omega
  | deq d =>
    cases d with
    | mk bal =>
      cases bal with
      | stop =>
        simp [Op.cost, Deq.cost, Balance.cost, Q.credit]
      | work rv =>
        simp [Op.cost, Deq.cost, Balance.cost, Q.credit]
        rw [FastReverseAcc.exact_steps rv]
        omega

theorem amortized_property {α : Type} {q0 q1 : Q α} (ops : Ops q0 q1)
    : Q.credit q0 + amortized_cost_ops ops = Ops.cost ops + Q.credit q1 := by
  induction ops with
  | stop        => simp [amortized_cost_ops, Ops.cost]
  | step op ops ih =>
    simp only [amortized_cost_ops, amortized_cost_op, Ops.cost]
    have := amortized_cost_positive op
    omega

theorem amortized_bound_ops {α : Type} {q0 q1 : Q α} (ops : Ops q0 q1)
    : amortized_cost_ops ops ≤ 3 * ops.length := by
  induction ops with
  | stop        => simp [amortized_cost_ops, Ops.length]
  | step op ops ih =>
    simp only [amortized_cost_ops, Ops.length]
    have := amortized_bound op
    omega

theorem amortized_constant {α : Type} {q : Q α} (ops : Ops Q.empty q)
    : Ops.cost ops ≤ 3 * ops.length := by
  have h := amortized_property ops
  have h' : amortized_cost_ops ops = Ops.cost ops + Q.credit q := by
    simpa [Q.credit, Q.empty] using h
  calc
    Ops.cost ops ≤ Ops.cost ops + Q.credit q := by omega
    _ = amortized_cost_ops ops := h'.symm
    _ ≤ 3 * ops.length := amortized_bound_ops ops

end Amortized



section Laziness

-- *crickets*

end
