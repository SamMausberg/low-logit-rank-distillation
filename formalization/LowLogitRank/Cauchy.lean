import LowLogitRank.Basic

/-!
# `prop:cauchy`: logit rank two, exponential probability rank

For `n = ⌊(T-1)/2⌋` the example generates two fair strings `X, F` of length `n`, then a label with
`P(Y = 1 | x, f) = σ(s(x) - s(f))`, where `s(x) = ∑_{i ≥ 1} 2^{-i} x_i`, then zero or one fair
padding bit. Its only nonzero centered logit is `(s(x) - s(f))/2` at the label, so every logit
matrix has rank at most two, while at cut `n` the probability matrix contains the nonsingular
Cauchy-type matrix `2^{-n} diag(a_x) (1/(a_x + b_f))` with `a_x = e^{s(x)}`, `b_f = e^{s(f)}`.

The paper states the proposition for `T ≥ 32`; the proof works for every `T ≥ 1`, and that is the
version proved here (`prop_cauchy`).
-/

namespace LowLogitRank.Cauchy

open Finset

/-! ### Small facts about `σ` -/

theorem sigmoid_zero : sigmoid 0 = 1 / 2 := by
  simp only [sigmoid, neg_zero, Real.exp_zero]
  norm_num

theorem sigmoid_mono {u v : ℝ} (h : u ≤ v) : sigmoid u ≤ sigmoid v := by
  unfold sigmoid
  apply inv_anti₀ (by positivity)
  have := Real.exp_le_exp.mpr (neg_le_neg h)
  linarith

theorem sigmoid_neg_one : sigmoid (-1) = 1 / (1 + Real.exp 1) := by
  simp [sigmoid]

theorem sigmoid_one : sigmoid 1 = Real.exp 1 / (1 + Real.exp 1) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  simp only [sigmoid, Real.exp_neg]
  field_simp
  ring

/-- `σ(a - b) = e^a / (e^a + e^b)`. -/
theorem sigmoid_sub (a b : ℝ) :
    sigmoid (a - b) = Real.exp a / (Real.exp a + Real.exp b) := by
  have ha : 0 < Real.exp a := Real.exp_pos a
  have hb : 0 < Real.exp b := Real.exp_pos b
  rw [sigmoid, neg_sub, Real.exp_sub]
  field_simp

/-! ### The dyadic score `s` -/

/-- The value `0` or `1` of a bit. -/
def bitVal (b : Bool) : ℝ := if b then 1 else 0

theorem bitVal_nonneg (b : Bool) : 0 ≤ bitVal b := by cases b <;> simp [bitVal]

theorem bitVal_le_one (b : Bool) : bitVal b ≤ 1 := by cases b <;> simp [bitVal]

/-- The dyadic score `s(x) = ∑_{i ≥ 1} 2^{-i} x_i`, computed from the front
(see `score_eq_sum`). -/
noncomputable def score : List Bool → ℝ
  | [] => 0
  | b :: z => (bitVal b + score z) / 2

@[simp] theorem score_nil : score [] = 0 := rfl

@[simp] theorem score_cons (b : Bool) (z : List Bool) :
    score (b :: z) = (bitVal b + score z) / 2 := rfl

/-- The recursive score is the weighted sum `∑_{i < |x|} 2^{-(i+1)} x_i`. -/
theorem score_eq_sum (x : List Bool) :
    score x = ∑ i ∈ range x.length, bitVal (x.getD i false) / 2 ^ (i + 1) := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [score_cons, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_succ]
    rw [add_div, sum_div]
    simp only [pow_zero, one_mul, add_comm (bitVal b / 2)]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [div_div]

theorem score_nonneg (z : List Bool) : 0 ≤ score z := by
  induction z with
  | nil => simp
  | cons b z ih =>
    have := bitVal_nonneg b
    simp only [score_cons]
    positivity

theorem score_lt_one (z : List Bool) : score z < 1 := by
  induction z with
  | nil => simp
  | cons b z ih =>
    have := bitVal_le_one b
    simp only [score_cons]
    linarith

theorem score_append (x y : List Bool) :
    score (x ++ y) = score x + score y / 2 ^ x.length := by
  induction x with
  | nil => simp
  | cons b x ih =>
    simp only [List.cons_append, score_cons, ih, List.length_cons, pow_succ]
    field_simp
    ring

/-- `s` is injective on strings of a fixed length. -/
theorem score_injective {x y : List Bool} (hl : x.length = y.length)
    (h : score x = score y) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons => simp at hl
  | cons b x ih =>
    cases y with
    | nil => simp at hl
    | cons c y =>
      simp only [score_cons] at h
      have hl' : x.length = y.length := by simpa using hl
      have hx0 := score_nonneg x
      have hx1 := score_lt_one x
      have hy0 := score_nonneg y
      have hy1 := score_lt_one y
      have hbc : b = c := by
        cases b <;> cases c
        · rfl
        · exfalso; simp only [bitVal] at h; norm_num at h; linarith
        · exfalso; simp only [bitVal] at h; norm_num at h; linarith
        · rfl
      subst hbc
      have hs : score x = score y := by linarith
      rw [ih hl' hs]

/-! ### The example -/

/-- The centered logit of the example: `(s(x) - s(f))/2` at prefixes `xf` of length `2n`
(`x` the first `n` bits, `f` the next `n`), zero at every other prefix. -/
noncomputable def ell (n : ℕ) (w : List Bool) : ℝ :=
  if w.length = 2 * n then (score (w.take n) - score (w.drop n)) / 2 else 0

/-- The example of `prop:cauchy` for length `T`, with `n = ⌊(T-1)/2⌋`: two fair strings of length
`n`, the label with `P(Y = 1 | x, f) = σ(s(x) - s(f))`, then zero or one fair padding bit. -/
noncomputable def cauchyModel (T : ℕ) : NextBit := ofLogit (ell ((T - 1) / 2))

theorem abs_ell_lt (n : ℕ) (w : List Bool) : |ell n w| < 1 / 2 := by
  unfold ell
  split_ifs
  · have := score_nonneg (w.take n)
    have := score_lt_one (w.take n)
    have := score_nonneg (w.drop n)
    have := score_lt_one (w.drop n)
    rw [abs_lt]
    constructor <;> linarith
  · norm_num

theorem logit_cauchyModel (T : ℕ) (h : List Bool) :
    logit (cauchyModel T) h = ell ((T - 1) / 2) h :=
  logit_ofLogit _ h

/-- Away from the label position the example emits fair bits. -/
theorem cauchyModel_fair (T : ℕ) {n : ℕ} (hn : (T - 1) / 2 = n) (g : List Bool)
    (hg : g.length ≠ 2 * n) : cauchyModel T g = 1 / 2 := by
  subst hn
  simp [cauchyModel, ofLogit, ell, hg, sigmoid_zero]

/-- The next-bit probability at the label `xf`. -/
theorem cauchyModel_label (T : ℕ) (x f : List Bool) (hx : x.length = (T - 1) / 2)
    (hf : f.length = (T - 1) / 2) :
    cauchyModel T (x ++ f) = sigmoid (score x - score f) := by
  have hlen : (x ++ f).length = 2 * ((T - 1) / 2) := by simp [hx, hf]; ring
  simp only [cauchyModel, ofLogit, ell, hlen, ite_true, List.take_left' hx, List.drop_left' hx]
  congr 1
  ring

/-- Every bit probability lies in `[1/(1+e), e/(1+e)]`. -/
theorem bitProb_bounds (T : ℕ) (h : List Bool) (b : Bool) :
    1 / (1 + Real.exp 1) ≤ bitProb (cauchyModel T) h b ∧
      bitProb (cauchyModel T) h b ≤ Real.exp 1 / (1 + Real.exp 1) := by
  have hl := abs_ell_lt ((T - 1) / 2) h
  rw [abs_lt] at hl
  have h1 : -1 ≤ 2 * ell ((T - 1) / 2) h := by linarith
  have h2 : 2 * ell ((T - 1) / 2) h ≤ 1 := by linarith
  rw [← sigmoid_neg_one, ← sigmoid_one]
  cases b
  · simp only [bitProb, Bool.false_eq_true, ite_false, cauchyModel, ofLogit, one_sub_sigmoid]
    exact ⟨sigmoid_mono (by linarith), sigmoid_mono (by linarith)⟩
  · simp only [bitProb, ite_true, cauchyModel, ofLogit]
    exact ⟨sigmoid_mono h1, sigmoid_mono h2⟩

/-! ### Logit rank at most two -/

/-- A matrix of the form `A i * c j + d j` has rank at most two. -/
theorem rank_le_two {m k : Type*} [Fintype k] (M : Matrix m k ℝ) (A : m → ℝ)
    (c d : k → ℝ) (h : ∀ i j, M i j = A i * c j + d j) : M.rank ≤ 2 := by
  have hM : M = (Matrix.of fun i (r : Fin 2) => ![A i, 1] r) *
      Matrix.of (fun (r : Fin 2) j => ![c j, d j] r) := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two, h]
  rw [hM]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width (Matrix.of fun i (r : Fin 2) => ![A i, 1] r)

/-- At a cut `t`, the logit of `hf` (with `|h| = t`) is a prefix score plus a future score at the
label, and zero elsewhere. -/
theorem ell_append (n t : ℕ) (h f : List Bool) (ht : h.length = t) :
    ell n (h ++ f) =
      (score (h.take n) - score (h.drop n)) / 2 * (if t + f.length = 2 * n then 1 else 0) +
      (if t + f.length = 2 * n then 1 else 0) *
        ((score (f.take (n - t)) / 2 ^ min n t - score (f.drop (n - t)) / 2 ^ (t - n)) / 2) := by
  unfold ell
  rw [List.length_append, ht]
  split_ifs
  · rw [List.take_append, List.drop_append, score_append, score_append, List.length_take,
      List.length_drop, ht]
    ring
  · ring

theorem logit_rank_le_two (T t : ℕ) :
    (logitCutMatrix (logit (cauchyModel T)) T t).rank ≤ 2 := by
  refine rank_le_two _ (fun h => (score (h.toList.take ((T - 1) / 2)) -
      score (h.toList.drop ((T - 1) / 2))) / 2)
    (fun f => if t + f.2.toList.length = 2 * ((T - 1) / 2) then 1 else 0)
    (fun f => (if t + f.2.toList.length = 2 * ((T - 1) / 2) then 1 else 0) *
      ((score (f.2.toList.take ((T - 1) / 2 - t)) / 2 ^ min ((T - 1) / 2) t -
        score (f.2.toList.drop ((T - 1) / 2 - t)) / 2 ^ (t - (T - 1) / 2)) / 2)) ?_
  intro h f
  simp only [logitCutMatrix, logit_cauchyModel]
  exact ell_append _ t _ _ (List.Vector.toList_length h)

/-- The example lies in `𝒞_{T,2}` with logit bound `1/2`. -/
theorem cauchyModel_logitClass (T : ℕ) : LogitClass T (1 / 2) 2 (cauchyModel T) where
  fullSupport := ofLogit_fullSupport _ T
  logit_le h _ := by
    rw [logit_cauchyModel]
    exact (abs_ell_lt _ h).le
  rank_le t _ := logit_rank_le_two T t

theorem logitClass_mono {T : ℕ} {Λ Λ' : ℝ} {d : ℕ} {p : NextBit} (hp : LogitClass T Λ d p)
    (hΛ : Λ ≤ Λ') : LogitClass T Λ' d p where
  fullSupport := hp.fullSupport
  logit_le h hh := (hp.logit_le h hh).trans hΛ
  rank_le := hp.rank_le

theorem cauchyModel_inClass (T : ℕ) (hT : 1 ≤ T) : InClass T 2 (cauchyModel T) :=
  logitClass_mono (cauchyModel_logitClass T) (by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith)

/-! ### Nonsingularity of the Cauchy-type matrix -/

open Polynomial in
/-- If `∑_j c_j / (a_i + b_j) = 0` for every `i`, with distinct `a`'s, distinct `b`'s and
`a_i + b_j ≠ 0`, then `c = 0` (the polynomial argument of `prop:cauchy`). -/
theorem cauchy_kernel {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i + b j ≠ 0)
    (c : ι → ℝ) (h : ∀ i, ∑ j, c j / (a i + b j) = 0) : c = 0 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · funext i
    exact (IsEmpty.false i).elim
  set N : ℝ[X] := ∑ j, C (c j) * ∏ k ∈ univ.erase j, (X + C (b k)) with hN
  have hdeg : N.natDegree < Fintype.card ι := by
    have hle : N.natDegree ≤ Fintype.card ι - 1 := by
      apply natDegree_sum_le_of_forall_le
      intro j _
      refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
      simp [Finset.card_erase_of_mem (mem_univ j)]
    have := Fintype.card_pos (α := ι)
    omega
  have heval : ∀ i, N.eval (a i) = 0 := by
    intro i
    have hprod : ∀ j, c j * ∏ k ∈ univ.erase j, (a i + b k) =
        c j / (a i + b j) * ∏ k, (a i + b k) := by
      intro j
      rw [← Finset.mul_prod_erase univ (fun k => a i + b k) (mem_univ j)]
      field_simp [hab i j]
    simp only [hN, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
    rw [Finset.sum_congr rfl fun j _ => hprod j, ← Finset.sum_mul, h i, zero_mul]
  have hN0 : N = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero N ha heval hdeg
  funext j
  have hj : N.eval (-b j) = c j * ∏ k ∈ univ.erase j, (-b j + b k) := by
    simp only [hN, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
    rw [Finset.sum_eq_single j]
    · intro j' _ hj'
      rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨fun e => hj' e.symm, mem_univ j⟩)
        (by ring), mul_zero]
    · intro hj; exact absurd (mem_univ j) hj
  rw [hN0, eval_zero] at hj
  have hp : ∏ k ∈ univ.erase j, (-b j + b k) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk e
    have : b k = b j := by linarith
    exact (Finset.mem_erase.mp hk).1 (hb this)
  simpa [hp] using hj.symm

/-! ### Exponential probability rank -/

/-- `condProb` over a stretch of fair bits. -/
theorem condProb_eq_half_pow (p : NextBit) (h f : List Bool)
    (hp : ∀ g : List Bool, h.length ≤ g.length → g.length < h.length + f.length → p g = 1 / 2) :
    condProb p h f = (1 / 2) ^ f.length := by
  induction f generalizing h with
  | nil => simp
  | cons b f ih =>
    rw [condProb_cons, ih (h ++ [b])]
    · have hph : p h = 1 / 2 := hp h le_rfl (by simp)
      have : bitProb p h b = 1 / 2 := by
        cases b <;> norm_num [bitProb, hph]
      rw [this, List.length_cons, pow_succ]
      ring
    · intro g h1 h2
      apply hp g
      · simp at h1; omega
      · simp at h1 h2 ⊢; omega

/-- The selected complete future `(f, 1)` followed by the padding (all zeros). -/
def selWord (T n : ℕ) (hn : 2 * n + 1 ≤ T) (f : Word n) : Word (T - n) :=
  ⟨f.toList ++ true :: List.replicate (T - 2 * n - 1) false, by simp; omega⟩

/-- The selected entries: `P((f, 1, 0…) | x) = 2^{-n} σ(s(x) - s(f)) 2^{-(T-2n-1)}`. -/
theorem selected_entry (T n : ℕ) (hn : (T - 1) / 2 = n) (hT : 2 * n + 1 ≤ T) (x f : Word n) :
    condProb (cauchyModel T) x.toList (selWord T n hT f).toList =
      (1 / 2) ^ n * sigmoid (score x.toList - score f.toList) * (1 / 2) ^ (T - 2 * n - 1) := by
  have hx := List.Vector.toList_length x
  have hf := List.Vector.toList_length f
  have hsel : (selWord T n hT f).toList =
      f.toList ++ true :: List.replicate (T - 2 * n - 1) false := rfl
  rw [hsel, condProb_append, condProb_cons]
  have e1 : condProb (cauchyModel T) x.toList f.toList = (1 / 2) ^ n := by
    rw [condProb_eq_half_pow, hf]
    intro g h1 h2
    apply cauchyModel_fair T hn
    rw [hx, hf] at *
    omega
  have e2 : bitProb (cauchyModel T) (x.toList ++ f.toList) true =
      sigmoid (score x.toList - score f.toList) := by
    simp only [bitProb, ite_true]
    exact cauchyModel_label T _ _ (hx.trans hn.symm) (hf.trans hn.symm)
  have e3 : condProb (cauchyModel T) (x.toList ++ f.toList ++ [true])
      (List.replicate (T - 2 * n - 1) false) = (1 / 2) ^ (T - 2 * n - 1) := by
    rw [condProb_eq_half_pow, List.length_replicate]
    intro g h1 _
    apply cauchyModel_fair T hn
    simp only [List.length_append, hx, hf, List.length_singleton] at h1
    omega
  rw [e1, e2, e3]
  ring

/-- The selected `2^n × 2^n` matrix is nonsingular. -/
theorem selected_rank (T n : ℕ) (hn : (T - 1) / 2 = n) (hT : 2 * n + 1 ≤ T) :
    (Matrix.of fun x f : Word n => condProb (cauchyModel T) x.toList
      (selWord T n hT f).toList).rank = 2 ^ n := by
  set S : Matrix (Word n) (Word n) ℝ := Matrix.of fun x f : Word n =>
    condProb (cauchyModel T) x.toList (selWord T n hT f).toList with hSdef
  set K : ℝ := (1 / 2) ^ n * (1 / 2) ^ (T - 2 * n - 1) with hK
  have hS : ∀ x f, S x f = K * (Real.exp (score x.toList) /
      (Real.exp (score x.toList) + Real.exp (score f.toList))) := by
    intro x f
    rw [hSdef, Matrix.of_apply, selected_entry T n hn hT, sigmoid_sub, hK]
    ring
  have hKpos : 0 < K := by positivity
  have hinj : Function.Injective S.mulVec := by
    intro c c' hcc
    have hzero : S.mulVec (c - c') = 0 := by rw [Matrix.mulVec_sub, hcc, sub_self]
    have key : ∀ x : Word n, ∑ f, (c - c') f /
        (Real.exp (score x.toList) + Real.exp (score f.toList)) = 0 := by
      intro x
      have hx := congrFun hzero x
      simp only [Matrix.mulVec, dotProduct, hS, Pi.zero_apply] at hx
      have hex : 0 < Real.exp (score x.toList) := Real.exp_pos _
      have : ∑ f, (c - c') f / (Real.exp (score x.toList) + Real.exp (score f.toList)) =
          (∑ f, K * (Real.exp (score x.toList) /
            (Real.exp (score x.toList) + Real.exp (score f.toList))) * (c - c') f) /
            (K * Real.exp (score x.toList)) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun f _ => ?_
        have hd : 0 < Real.exp (score x.toList) + Real.exp (score f.toList) := by positivity
        field_simp
      rw [this, hx, zero_div]
    have hsc : Function.Injective fun x : Word n => Real.exp (score x.toList) := by
      intro x y hxy
      apply List.Vector.toList_injective
      apply score_injective (by simp)
      exact Real.exp_injective hxy
    have := cauchy_kernel _ _ hsc hsc (fun i j => by positivity) _ key
    exact sub_eq_zero.mp this
  rw [Matrix.rank_of_isUnit S (Matrix.mulVec_injective_iff_isUnit.mp hinj), card_vector,
    Fintype.card_bool]

/-- `prop:cauchy` (rank part): the probability rank of the example is at least
`2^{⌊(T-1)/2⌋}`, witnessed at cut `n = ⌊(T-1)/2⌋` by the complete futures `(f, 1)` (followed by a
zero padding bit when `T` is even). -/
theorem probRank_cauchyModel (T : ℕ) (hT : 1 ≤ T) :
    2 ^ ((T - 1) / 2) ≤ probRank (cauchyModel T) T := by
  obtain ⟨n, hn⟩ : ∃ n, (T - 1) / 2 = n := ⟨_, rfl⟩
  rw [hn]
  have hnT : n < T := by omega
  have hsel : 2 * n + 1 ≤ T := by omega
  let Sel : Matrix (Word (T - n)) (Word n) ℝ :=
    Matrix.of fun g f => if g = selWord T n hsel f then 1 else 0
  have hprod : probCutMatrix (cauchyModel T) T n * Sel = Matrix.of fun x f : Word n =>
      condProb (cauchyModel T) x.toList (selWord T n hsel f).toList := by
    ext x f
    simp [Sel, Matrix.mul_apply, probCutMatrix]
  calc 2 ^ n = (probCutMatrix (cauchyModel T) T n * Sel).rank := by
        rw [hprod, selected_rank T n hn hsel]
    _ ≤ (probCutMatrix (cauchyModel T) T n).rank := Matrix.rank_mul_le_left _ _
    _ ≤ probRank (cauchyModel T) T := le_probRank _ hnT

/-- `prop:cauchy`: for every `T ≥ 1` (the paper assumes `T ≥ 32`) there is a distribution with
centered logits bounded by `1/2` and logit rank at most two at every cut (so it lies in
`𝒞_{T,2}`), every bit probability in `[1/(1+e), e/(1+e)]`, and probability rank at least
`2^{⌊(T-1)/2⌋}`. -/
theorem prop_cauchy (T : ℕ) (hT : 1 ≤ T) :
    ∃ p : NextBit, LogitClass T (1 / 2) 2 p ∧ InClass T 2 p ∧
      (∀ (h : List Bool) (b : Bool), 1 / (1 + Real.exp 1) ≤ bitProb p h b ∧
        bitProb p h b ≤ Real.exp 1 / (1 + Real.exp 1)) ∧
      2 ^ ((T - 1) / 2) ≤ probRank p T :=
  ⟨cauchyModel T, cauchyModel_logitClass T, cauchyModel_inClass T hT, bitProb_bounds T,
    probRank_cauchyModel T hT⟩

end LowLogitRank.Cauchy
