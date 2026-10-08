import LowLogitRank.Coupling.TV

/-!
# Finite sequential experiments (`lem:coupling`, `eq:target-telescope`)

A sequential experiment over a finite response type `α` is a kernel `K : List α → α → ℝ`: after
the past `x` (the earlier responses, in order) the next response is `a` with probability `K x a`.
The probability of the continuation `l` after the past `x` is `seqProb K x l`, and the law of an
`n`-round transcript is `seqLaw K n`. An adaptive algorithm interacting with an oracle is the
special case where `K x` is the oracle's reply law at the query that the algorithm computes from
the past replies `x`. A randomized algorithm draws a coin `ω` first (`jointLaw`).

The hybrid inequality `tv_seqProb_le` bounds the TV between two such laws by the expected
one-step discrepancies along the first law. It is `eq:target-telescope` for a general finite
alphabet and gives the transcript bounds of `lem:coupling`.
-/

namespace LowLogitRank.Coupling

open Finset

variable {α Ω : Type*}

/-! ### Vectors -/

/-- Splitting a vector of length `n + 1` into its first entry and the rest. -/
def vecConsEquiv (α : Type*) (n : ℕ) : α × List.Vector α n ≃ List.Vector α (n + 1) where
  toFun x := List.Vector.cons x.1 x.2
  invFun v := (v.head, v.tail)
  left_inv x := by simp
  right_inv v := by simp

theorem sum_vector_succ [Fintype α] {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : List.Vector α (n + 1) → M) :
    ∑ v, F v = ∑ a : α, ∑ v : List.Vector α n, F (List.Vector.cons a v) := by
  rw [← (vecConsEquiv α n).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_vector_zero [Fintype α] {M : Type*} [AddCommMonoid M] (F : List.Vector α 0 → M) :
    ∑ v, F v = F List.Vector.nil := by
  have : (univ : Finset (List.Vector α 0)) = {List.Vector.nil} := by
    ext v; simp [List.Vector.eq_nil v]
  rw [this, sum_singleton]

/-! ### Sequential laws -/

/-- `seqProb K x l`: the probability that the responses following the past `x` are `l`, by the
product rule. -/
def seqProb (K : List α → α → ℝ) : List α → List α → ℝ
  | _, [] => 1
  | x, a :: l => K x a * seqProb K (x ++ [a]) l

@[simp] theorem seqProb_nil (K : List α → α → ℝ) (x : List α) : seqProb K x [] = 1 := rfl

@[simp] theorem seqProb_cons (K : List α → α → ℝ) (x : List α) (a : α) (l : List α) :
    seqProb K x (a :: l) = K x a * seqProb K (x ++ [a]) l := rfl

theorem seqProb_append (K : List α → α → ℝ) (x l l' : List α) :
    seqProb K x (l ++ l') = seqProb K x l * seqProb K (x ++ l) l' := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih, mul_assoc]

/-- Shifting the past: running the kernel `y ↦ K (h ++ y)` from the past `x` is running `K` from
the past `h ++ x`. -/
theorem seqProb_shift (K : List α → α → ℝ) (h x l : List α) :
    seqProb (fun y => K (h ++ y)) x l = seqProb K (h ++ x) l := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The law of an `n`-round transcript, started from the empty past. -/
def seqLaw (K : List α → α → ℝ) (n : ℕ) : List.Vector α n → ℝ :=
  fun v => seqProb K [] v.toList

theorem seqProb_nonneg (K : List α → α → ℝ) (x l : List α)
    (hK : ∀ l' : List α, l'.length < l.length → ∀ a, 0 ≤ K (x ++ l') a) :
    0 ≤ seqProb K x l := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    rw [seqProb_cons]
    refine mul_nonneg (by simpa using hK [] (by simp) a) (ih (x ++ [a]) fun l' hl' b => ?_)
    simpa using hK (a :: l') (by simpa using hl') b

theorem sum_seqProb [Fintype α] (K : List α → α → ℝ) (m : ℕ) (x : List α)
    (hK : ∀ l : List α, l.length < m → ∑ a, K (x ++ l) a = 1) :
    ∑ v : List.Vector α m, seqProb K x v.toList = 1 := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [sum_vector_succ]
    simp only [List.Vector.toList_cons, seqProb_cons, ← mul_sum]
    have h1 : ∀ a, ∑ v : List.Vector α m, seqProb K (x ++ [a]) v.toList = 1 := fun a =>
      ih (x ++ [a]) fun l hl => by simpa using hK (a :: l) (by simpa using hl)
    simp only [h1, mul_one]
    simpa using hK [] (by simp)

/-- Under kernels that are probability vectors at the relevant pasts, the continuation law is a
probability vector. -/
theorem seqProb_isProbVec [Fintype α] (K : List α → α → ℝ) (m : ℕ) (x : List α)
    (hK : ∀ l : List α, l.length < m → IsProbVec (K (x ++ l))) :
    IsProbVec fun v : List.Vector α m => seqProb K x v.toList :=
  ⟨fun v => seqProb_nonneg K x v.toList fun l hl a => (hK l (by simpa using hl)).nonneg a,
    sum_seqProb K m x fun l hl => (hK l hl).sum_eq_one⟩

theorem seqLaw_isProbVec [Fintype α] (K : List α → α → ℝ) (n : ℕ)
    (hK : ∀ x : List α, x.length < n → IsProbVec (K x)) : IsProbVec (seqLaw K n) :=
  seqProb_isProbVec K n [] fun l hl => by simpa using hK l hl

/-! ### The hybrid inequality -/

/-- One step of the hybrid argument: the first response is drawn from `K x` or `K' x`, and the
rest of the continuation from the respective laws. -/
theorem tv_seqProb_succ_le [Fintype α] (K K' : List α → α → ℝ) (m : ℕ) (x : List α)
    (hKx : ∀ a, 0 ≤ K x a)
    (hK' : ∀ a, IsProbVec fun v : List.Vector α m => seqProb K' (x ++ [a]) v.toList) :
    tv (fun v : List.Vector α (m + 1) => seqProb K x v.toList)
        (fun v => seqProb K' x v.toList) ≤
      tv (K x) (K' x) + ∑ a, K x a *
        tv (fun v : List.Vector α m => seqProb K (x ++ [a]) v.toList)
          (fun v => seqProb K' (x ++ [a]) v.toList) := by
  unfold tv
  rw [sum_vector_succ]
  simp only [List.Vector.toList_cons, seqProb_cons]
  have hstep : ∀ a, ∑ v : List.Vector α m,
      |K x a * seqProb K (x ++ [a]) v.toList - K' x a * seqProb K' (x ++ [a]) v.toList| ≤
      K x a * ∑ v : List.Vector α m,
          |seqProb K (x ++ [a]) v.toList - seqProb K' (x ++ [a]) v.toList| +
        |K x a - K' x a| := by
    intro a
    have hsum := (hK' a).sum_eq_one
    calc ∑ v : List.Vector α m,
          |K x a * seqProb K (x ++ [a]) v.toList - K' x a * seqProb K' (x ++ [a]) v.toList|
        ≤ ∑ v : List.Vector α m,
            (K x a * |seqProb K (x ++ [a]) v.toList - seqProb K' (x ++ [a]) v.toList| +
              |K x a - K' x a| * seqProb K' (x ++ [a]) v.toList) := by
          refine sum_le_sum fun v _ => ?_
          have hv := (hK' a).nonneg v
          have e : K x a * seqProb K (x ++ [a]) v.toList - K' x a * seqProb K' (x ++ [a]) v.toList
              = K x a * (seqProb K (x ++ [a]) v.toList - seqProb K' (x ++ [a]) v.toList) +
                (K x a - K' x a) * seqProb K' (x ++ [a]) v.toList := by ring
          rw [e]
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (hKx a), abs_of_nonneg hv]
      _ = K x a * ∑ v : List.Vector α m,
            |seqProb K (x ++ [a]) v.toList - seqProb K' (x ++ [a]) v.toList| +
          |K x a - K' x a| := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, hsum, mul_one]
  have := sum_le_sum fun a (_ : a ∈ univ) => hstep a
  rw [sum_add_distrib] at this
  simp only [mul_div_assoc']
  rw [← sum_div]
  linarith

/-- The `i`-th term of the hybrid bound: the expected one-step TV at depth `i` along `K`. -/
noncomputable def hybridTerm [Fintype α] (K K' : List α → α → ℝ) (x : List α) (i : ℕ) : ℝ :=
  ∑ v : List.Vector α i, seqProb K x v.toList * tv (K (x ++ v.toList)) (K' (x ++ v.toList))

theorem hybridTerm_zero [Fintype α] (K K' : List α → α → ℝ) (x : List α) :
    hybridTerm K K' x 0 = tv (K x) (K' x) := by
  simp [hybridTerm]

theorem hybridTerm_succ [Fintype α] (K K' : List α → α → ℝ) (x : List α) (i : ℕ) :
    hybridTerm K K' x (i + 1) = ∑ a, K x a * hybridTerm K K' (x ++ [a]) i := by
  unfold hybridTerm
  rw [sum_vector_succ]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun v _ => ?_
  simp [mul_assoc]

/-- `eq:target-telescope` for a finite alphabet, started at the past `x`: the TV between the
laws of `m`-step continuations under the kernels `K` and `K'` is at most the sum over depths
`i < m` of the expected one-step TV `tv (K y) (K' y)`, the expectation over the depth-`i` past
`y` drawn along `K`. The kernels must be probability vectors at the pasts `x ++ l`, `|l| < m`. -/
theorem tv_seqProb_le [Fintype α] (K K' : List α → α → ℝ) (m : ℕ) (x : List α)
    (hK : ∀ l : List α, l.length < m → IsProbVec (K (x ++ l)))
    (hK' : ∀ l : List α, l.length < m → IsProbVec (K' (x ++ l))) :
    tv (fun v : List.Vector α m => seqProb K x v.toList) (fun v => seqProb K' x v.toList) ≤
      ∑ i ∈ range m, ∑ v : List.Vector α i,
        seqProb K x v.toList * tv (K (x ++ v.toList)) (K' (x ++ v.toList)) := by
  change _ ≤ ∑ i ∈ range m, hybridTerm K K' x i
  induction m generalizing x with
  | zero => simp [tv]
  | succ m ih =>
    have hKa : ∀ a, ∀ l : List α, l.length < m → IsProbVec (K (x ++ [a] ++ l)) :=
      fun a l hl => by simpa using hK (a :: l) (by simpa using hl)
    have hK'a : ∀ a, ∀ l : List α, l.length < m → IsProbVec (K' (x ++ [a] ++ l)) :=
      fun a l hl => by simpa using hK' (a :: l) (by simpa using hl)
    have hKx : IsProbVec (K x) := by simpa using hK [] (by simp)
    refine (tv_seqProb_succ_le K K' m x hKx.nonneg
      fun a => seqProb_isProbVec K' m (x ++ [a]) (hK'a a)).trans ?_
    rw [sum_range_succ', hybridTerm_zero, add_comm]
    simp only [hybridTerm_succ]
    rw [sum_comm]
    gcongr with a
    simp only [← mul_sum]
    exact mul_le_mul_of_nonneg_left (ih (x ++ [a]) (hKa a) (hK'a a)) (hKx.nonneg a)

/-- Uniform form of `tv_seqProb_le`: if the one-step TV is at most `ε` at every relevant past,
the continuation laws of length `m` differ in TV by at most `m * ε`. -/
theorem tv_seqProb_le_mul [Fintype α] (K K' : List α → α → ℝ) (m : ℕ) (x : List α) (ε : ℝ)
    (hK : ∀ l : List α, l.length < m → IsProbVec (K (x ++ l)))
    (hK' : ∀ l : List α, l.length < m → IsProbVec (K' (x ++ l)))
    (hε : ∀ l : List α, l.length < m → tv (K (x ++ l)) (K' (x ++ l)) ≤ ε) :
    tv (fun v : List.Vector α m => seqProb K x v.toList) (fun v => seqProb K' x v.toList) ≤
      m * ε := by
  refine (tv_seqProb_le K K' m x hK hK').trans ?_
  have hterm : ∀ i ∈ range m, ∑ v : List.Vector α i,
      seqProb K x v.toList * tv (K (x ++ v.toList)) (K' (x ++ v.toList)) ≤ ε := by
    intro i hi
    have hi : i < m := mem_range.mp hi
    have hP := seqProb_isProbVec K i x fun l hl => hK l (by omega)
    calc ∑ v : List.Vector α i,
          seqProb K x v.toList * tv (K (x ++ v.toList)) (K' (x ++ v.toList))
        ≤ ∑ v : List.Vector α i, seqProb K x v.toList * ε :=
          sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
            (hε v.toList (by simpa using hi)) (hP.nonneg v)
      _ = ε := by rw [← sum_mul, hP.sum_eq_one, one_mul]
  calc _ ≤ ∑ _i ∈ range m, ε := sum_le_sum hterm
    _ = m * ε := by simp

/-- `lem:coupling` (adaptive transcript, refined form) and `eq:target-telescope`: the TV between
the `n`-round transcript laws is at most `∑_{i<n} E_{x ∼ law_i} tv (K x) (K' x)`. -/
theorem tv_seqLaw_le [Fintype α] (K K' : List α → α → ℝ) (n : ℕ)
    (hK : ∀ x : List α, x.length < n → IsProbVec (K x))
    (hK' : ∀ x : List α, x.length < n → IsProbVec (K' x)) :
    tv (seqLaw K n) (seqLaw K' n) ≤
      ∑ i ∈ range n, ∑ v : List.Vector α i, seqLaw K i v * tv (K v.toList) (K' v.toList) := by
  have := tv_seqProb_le K K' n [] (fun l hl => by simpa using hK l hl)
    (fun l hl => by simpa using hK' l hl)
  unfold seqLaw
  simpa using this

/-- `lem:coupling` (adaptive transcript, uniform form): if the reply laws at every past of
length `< n` differ in TV by at most `ε`, the `n`-round transcript laws differ by at most
`n * ε`. -/
theorem tv_seqLaw_le_mul [Fintype α] (K K' : List α → α → ℝ) (n : ℕ) (ε : ℝ)
    (hK : ∀ x : List α, x.length < n → IsProbVec (K x))
    (hK' : ∀ x : List α, x.length < n → IsProbVec (K' x))
    (hε : ∀ x : List α, x.length < n → tv (K x) (K' x) ≤ ε) :
    tv (seqLaw K n) (seqLaw K' n) ≤ n * ε :=
  tv_seqProb_le_mul K K' n [] ε (fun l hl => by simpa using hK l hl)
    (fun l hl => by simpa using hK' l hl) (fun l hl => by simpa using hε l hl)

/-! ### Randomized strategies -/

/-- The joint law of the coin `ω` (drawn from `μ`) and the `n`-round transcript of the kernel
`K ω`. The coin law is the same under both oracles. -/
def jointLaw (μ : Ω → ℝ) (K : Ω → List α → α → ℝ) (n : ℕ) : Ω × List.Vector α n → ℝ :=
  fun z => μ z.1 * seqLaw (K z.1) n z.2

theorem jointLaw_isProbVec [Fintype α] [Fintype Ω] {μ : Ω → ℝ} (hμ : IsProbVec μ)
    (K : Ω → List α → α → ℝ) (n : ℕ)
    (hK : ∀ ω, ∀ x : List α, x.length < n → IsProbVec (K ω x)) :
    IsProbVec (jointLaw μ K n) := by
  refine ⟨fun z => mul_nonneg (hμ.nonneg z.1) ((seqLaw_isProbVec _ n (hK z.1)).nonneg z.2), ?_⟩
  unfold jointLaw
  rw [Fintype.sum_prod_type]
  simp only [← mul_sum, (seqLaw_isProbVec _ n (hK _)).sum_eq_one, mul_one, hμ.sum_eq_one]

/-- TV of the joint (coin, transcript) laws is the coin-average of the transcript TV. -/
theorem tv_jointLaw_eq [Fintype α] [Fintype Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (K K' : Ω → List α → α → ℝ) (n : ℕ) :
    tv (jointLaw μ K n) (jointLaw μ K' n) = ∑ ω, μ ω * tv (seqLaw (K ω) n) (seqLaw (K' ω) n) :=
  tv_mix μ hμ (fun ω => seqLaw (K ω) n) (fun ω => seqLaw (K' ω) n)

/-- `lem:coupling` for randomized algorithms, refined form. -/
theorem tv_jointLaw_le [Fintype α] [Fintype Ω] {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω)
    (K K' : Ω → List α → α → ℝ) (n : ℕ)
    (hK : ∀ ω, ∀ x : List α, x.length < n → IsProbVec (K ω x))
    (hK' : ∀ ω, ∀ x : List α, x.length < n → IsProbVec (K' ω x)) :
    tv (jointLaw μ K n) (jointLaw μ K' n) ≤
      ∑ i ∈ range n, ∑ ω, ∑ v : List.Vector α i,
        μ ω * seqLaw (K ω) i v * tv (K ω v.toList) (K' ω v.toList) := by
  rw [tv_jointLaw_eq hμ]
  calc ∑ ω, μ ω * tv (seqLaw (K ω) n) (seqLaw (K' ω) n)
      ≤ ∑ ω, μ ω * ∑ i ∈ range n, ∑ v : List.Vector α i,
          seqLaw (K ω) i v * tv (K ω v.toList) (K' ω v.toList) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
          (tv_seqLaw_le (K ω) (K' ω) n (hK ω) (hK' ω)) (hμ ω)
    _ = _ := by
        simp only [mul_sum]
        rw [sum_comm]
        simp only [mul_assoc]

/-- `lem:coupling` for randomized algorithms, uniform form: with the same coin law under both
oracles, the joint (coin, transcript) laws differ in TV by at most `n * ε`. -/
theorem tv_jointLaw_le_mul [Fintype α] [Fintype Ω] {μ : Ω → ℝ} (hμ : IsProbVec μ)
    (K K' : Ω → List α → α → ℝ) (n : ℕ) (ε : ℝ)
    (hK : ∀ ω, ∀ x : List α, x.length < n → IsProbVec (K ω x))
    (hK' : ∀ ω, ∀ x : List α, x.length < n → IsProbVec (K' ω x))
    (hε : ∀ ω, ∀ x : List α, x.length < n → tv (K ω x) (K' ω x) ≤ ε) :
    tv (jointLaw μ K n) (jointLaw μ K' n) ≤ n * ε := by
  rw [tv_jointLaw_eq hμ.nonneg]
  calc ∑ ω, μ ω * tv (seqLaw (K ω) n) (seqLaw (K' ω) n)
      ≤ ∑ ω, μ ω * (n * ε) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
          (tv_seqLaw_le_mul (K ω) (K' ω) n ε (hK ω) (hK' ω) (hε ω)) (hμ.nonneg ω)
    _ = n * ε := by rw [← sum_mul, hμ.sum_eq_one, one_mul]

/-- Data processing for outputs (`lem:coupling`: "coins and the output program may be included
in the transcript"): any function of the coin and the transcript has output laws within
`n * ε` in TV. -/
theorem tv_push_jointLaw_le_mul [Fintype α] [Fintype Ω] {β : Type*} [Fintype β] [DecidableEq β]
    {μ : Ω → ℝ} (hμ : IsProbVec μ) (K K' : Ω → List α → α → ℝ) (n : ℕ) (ε : ℝ)
    (hK : ∀ ω, ∀ x : List α, x.length < n → IsProbVec (K ω x))
    (hK' : ∀ ω, ∀ x : List α, x.length < n → IsProbVec (K' ω x))
    (hε : ∀ ω, ∀ x : List α, x.length < n → tv (K ω x) (K' ω x) ≤ ε)
    (out : Ω × List.Vector α n → β) :
    tv (push out (jointLaw μ K n)) (push out (jointLaw μ K' n)) ≤ n * ε :=
  (tv_push_le out _ _).trans (tv_jointLaw_le_mul hμ K K' n ε hK hK' hε)

end LowLogitRank.Coupling
