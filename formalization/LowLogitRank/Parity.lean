import LowLogitRank.Hardness.Teacher

/-!
# Noisy parity has logit rank one (`sec:parity`)

The noisy-parity distribution draws `n` fair input bits `X` and the label
`Y = ⟨s, X⟩ ⊕ E` with `E ∼ Ber(ν)`. Its next-bit probabilities lie in `[ν, 1-ν]`, its label logit
is `-B(-1)^{⟨s,x⟩}` with `B = ½ log((1-ν)/ν)`, every other logit is zero, the logit rank is at most
one at every cut, and it belongs to `𝒞_{n+1,1}` when `B ≤ n + 1`. Querying the basis vector `e_i`
returns `s_i` with probability `1 - ν`.
-/

namespace LowLogitRank.Parity

open Finset LowLogitRank.Hardness

variable {n : ℕ}

/-- The inner product `⟨s, x⟩` over `𝔽₂`. -/
def innerF2 (s x : Word n) : ZMod 2 := ∑ i : Fin n, if s.get i && x.get i then 1 else 0

/-- The noisy-parity model as a next-bit model: fair input bits, then
`P(Y = 1 | x) = P(⟨s,x⟩ ⊕ E = 1)`, which is `1 - ν` if `⟨s, x⟩ = 1` and `ν` otherwise. -/
noncomputable def parityModel (s : Word n) (ν : ℝ) : NextBit := fun h =>
  if h.length = n then (if innerF2 s (inputOf n h) = 1 then 1 - ν else ν) else 1 / 2

/-- `B = ½ log((1-ν)/ν)`. -/
noncomputable def parityB (ν : ℝ) : ℝ := Real.log ((1 - ν) / ν) / 2

/-- The parity sign `(-1)^{⟨s,x⟩}`. -/
noncomputable def paritySign (s x : Word n) : ℝ := (-1) ^ (innerF2 s x).val

/-- The logits claimed in `sec:parity`: `-B(-1)^{⟨s,x⟩}` at the label, zero elsewhere. -/
noncomputable def parityLogit (s : Word n) (B : ℝ) (h : List Bool) : ℝ :=
  if h.length = n then -B * paritySign s (inputOf n h) else 0

variable (s : Word n) {ν : ℝ}

/-- `sec:parity`: the model generates the noisy-parity distribution, the string `x y` has
probability `2^{-n} P(⟨s,x⟩ ⊕ E = y)` with `E ∼ Ber(ν)`. -/
theorem condProb_parityModel (x : Word n) (y : Bool) :
    condProb (parityModel s ν) [] (x.toList ++ [y]) =
      (1 / 2) ^ n * (if y = decide (innerF2 s x = 1) then 1 - ν else ν) := by
  rw [condProb_append, condProb_of_fair]
  · simp only [List.Vector.toList_length, List.nil_append, condProb_cons, condProb_nil, mul_one,
      bitProb, parityModel, List.Vector.toList_length, ↓reduceIte, inputOf_toList]
    congr 1
    by_cases hx : innerF2 s x = 1 <;> cases y <;> simp [hx]
  · intro g _ hg
    simp only [List.length_nil, zero_add, List.Vector.toList_length] at hg
    simp [parityModel, hg.ne]

/-- `sec:parity`: every next-token probability lies in `[ν, 1-ν]`. -/
theorem parityModel_mem (hν : ν < 1 / 2) (h : List Bool) :
    ν ≤ parityModel s ν h ∧ parityModel s ν h ≤ 1 - ν := by
  unfold parityModel
  split_ifs <;> constructor <;> linarith

theorem parityB_pos (hν0 : 0 < ν) (hν : ν < 1 / 2) : 0 < parityB ν := by
  unfold parityB
  have : 1 < (1 - ν) / ν := by rw [one_lt_div hν0]; linarith
  have := Real.log_pos this
  positivity

theorem abs_paritySign (x : Word n) : |paritySign s x| = 1 := by
  simp [paritySign]

/-- `sec:parity`: the centered logits of the noisy-parity model are `-B(-1)^{⟨s,x⟩}` at the
label and zero elsewhere. -/
theorem logit_parityModel (hν0 : 0 < ν) (hν : ν < 1 / 2) :
    logit (parityModel s ν) = parityLogit s (parityB ν) := by
  funext h
  have hν1 : 0 < 1 - ν := by linarith
  unfold logit parityModel parityLogit paritySign parityB
  split_ifs with h1 h2
  · rw [h2, ZMod.val_one, sub_sub_cancel]
    ring
  · have : innerF2 s (inputOf n h) = 0 := by
      generalize innerF2 s (inputOf n h) = a at h2 ⊢
      fin_cases a
      · rfl
      · exact absurd rfl h2
    rw [this, ZMod.val_zero, pow_zero, show ν / (1 - ν) = ((1 - ν) / ν)⁻¹ by
      field_simp, Real.log_inv]
    ring
  · norm_num

/-! ### Rank one through a one-dimensional linear state -/

/-- The number of indices `i < min(|h|, n)` with `s_i = h_i = 1`. -/
def partialCount (h : List Bool) : ℕ :=
  ∑ i ∈ range (min h.length n), if s.toList.getD i false && h.getD i false then 1 else 0

/-- The one-dimensional state `(-1)^{partialCount}`. -/
noncomputable def signState (h : List Bool) : Unit → ℝ := fun _ => (-1) ^ partialCount s h

/-- The scalar update after the bit `b` at position `t`. -/
noncomputable def signStep (t : ℕ) (b : Bool) : (Unit → ℝ) →ₗ[ℝ] (Unit → ℝ) :=
  (if t < n ∧ (s.toList.getD t false && b) = true then (-1 : ℝ) else 1) • LinearMap.id

variable (n) in
/-- The readout at position `t`. -/
noncomputable def signRead (B : ℝ) (t : ℕ) : (Unit → ℝ) →ₗ[ℝ] ℝ :=
  (if t = n then -B else 0) • LinearMap.proj ()

theorem partialCount_snoc (h : List Bool) (b : Bool) :
    partialCount s (h ++ [b]) = partialCount s h +
      if h.length < n ∧ (s.toList.getD h.length false && b) = true then 1 else 0 := by
  unfold partialCount
  have hterm : ∀ i ∈ range (min h.length n),
      (if s.toList.getD i false && (h ++ [b]).getD i false then 1 else 0) =
        (if s.toList.getD i false && h.getD i false then 1 else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [getD_append_of_lt (by omega)]
  by_cases hc : h.length < n
  · rw [List.length_append, List.length_singleton, show min (h.length + 1) n = min h.length n + 1
      by omega, Finset.sum_range_succ, Finset.sum_congr rfl hterm,
      show min h.length n = h.length by omega, getD_snoc_self]
    simp [hc]
  · rw [List.length_append, List.length_singleton, show min (h.length + 1) n = min h.length n
      by omega, Finset.sum_congr rfl hterm]
    simp [hc]

theorem signState_snoc (h : List Bool) (b : Bool) :
    signState s (h ++ [b]) = signStep s h.length b (signState s h) := by
  funext u
  simp only [signState, signStep, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply,
    smul_eq_mul, partialCount_snoc]
  split_ifs <;> simp [pow_succ]

theorem innerF2_val_pow (x : Word n) :
    (-1 : ℝ) ^ (innerF2 s x).val = (-1) ^ partialCount s x.toList := by
  have hcast : innerF2 s x = ((partialCount s x.toList : ℕ) : ZMod 2) := by
    unfold innerF2 partialCount
    rw [List.Vector.toList_length, min_self, Nat.cast_sum, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [word_getD, word_getD]
    split_ifs <;> simp
  rw [hcast, ZMod.val_natCast, ← neg_one_pow_eq_pow_mod_two]

theorem parityLogit_eq_read (B : ℝ) (h : List Bool) :
    parityLogit s B h = signRead n B h.length (signState s h) := by
  simp only [parityLogit, signRead, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul,
    signState]
  split_ifs with hh
  · rw [paritySign, innerF2_val_pow, inputOf_toList_of_length h hh]
  · simp

/-- `sec:parity`: the logit matrix of the noisy-parity model has rank at most one at every cut,
for every horizon `T`. -/
theorem parityModel_rank_le (hν0 : 0 < ν) (hν : ν < 1 / 2) (T t : ℕ) :
    (logitCutMatrix (logit (parityModel s ν)) T t).rank ≤ 1 := by
  rw [logit_parityModel s hν0 hν]
  simpa using rank_le_of_linearState (parityLogit s (parityB ν)) (signState s) (signStep s)
    (signRead n (parityB ν)) (signState_snoc s) (parityLogit_eq_read s _) T t

theorem abs_parityLogit_le {B : ℝ} (hB : 0 ≤ B) (h : List Bool) : |parityLogit s B h| ≤ B := by
  unfold parityLogit
  split_ifs
  · rw [abs_mul, abs_neg, abs_of_nonneg hB, abs_paritySign, mul_one]
  · simpa using hB

/-- `sec:parity`: for `0 < ν < 1/2` and `B = ½ log((1-ν)/ν) ≤ n + 1`, the noisy-parity model
belongs to `𝒞_{n+1,1}`. -/
theorem parityModel_inClass (hν0 : 0 < ν) (hν : ν < 1 / 2) (hB : parityB ν ≤ n + 1) :
    InClass (n + 1) 1 (parityModel s ν) where
  fullSupport h _ := by
    have := parityModel_mem s hν h
    constructor <;> linarith
  logit_le h _ := by
    rw [logit_parityModel s hν0 hν]
    exact (abs_parityLogit_le s (parityB_pos hν0 hν).le h).trans (by exact_mod_cast hB)
  rank_le t _ := parityModel_rank_le s hν0 hν (n + 1) t

/-- The hypotheses are satisfiable: for `ν = 1/4`, `B = ½ log 3 ≤ 1 ≤ n + 1`, so the
noisy-parity model with noise `1/4` is in `𝒞_{n+1,1}` for every `n` and key `s`. -/
theorem parityModel_quarter_inClass : InClass (n + 1) 1 (parityModel s (1 / 4)) := by
  apply parityModel_inClass s (by norm_num) (by norm_num)
  have h3 : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have : parityB (1 / 4) = Real.log 3 / 2 := by unfold parityB; norm_num
  rw [this]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-! ### Chosen inputs reveal the key -/

/-- The standard basis vector `e_i ∈ {0,1}^n`. -/
def basisVec (i : Fin n) : Word n := List.Vector.ofFn fun j => decide (j = i)

theorem innerF2_basisVec (i : Fin n) : innerF2 s (basisVec i) = if s.get i then 1 else 0 := by
  unfold innerF2 basisVec
  rw [Finset.sum_eq_single i]
  · simp [List.Vector.get_ofFn]
  · intro j _ hj
    simp [List.Vector.get_ofFn, hj]
  · simp

/-- `sec:parity`: querying the prefix `e_i` returns a label equal to `s_i` with probability
`1 - ν`. -/
theorem query_basisVec (i : Fin n) :
    bitProb (parityModel s ν) (basisVec i).toList (s.get i) = 1 - ν := by
  simp only [bitProb, parityModel, List.Vector.toList_length, ↓reduceIte, inputOf_toList,
    innerF2_basisVec]
  cases s.get i <;> simp

/-- The repetition count `r = ⌈(2/(1-2ν)²) ⌈log₂(n/δ)⌉⌉` of `sec:parity`. -/
noncomputable def majorityReps (ν δ : ℝ) (n : ℕ) : ℕ :=
  ⌈2 / (1 - 2 * ν) ^ 2 * ⌈Real.logb 2 (n / δ)⌉₊⌉₊

/-- `sec:parity`: with `r = majorityReps ν δ n`, the Hoeffding bound for a wrong majority of `r`
independent answers, `exp(-2r(1/2 - ν)²) = exp(-r(1-2ν)²/2)`, is at most `δ/n` (for
`0 < δ ≤ n`). Hoeffding's inequality itself is not formalized here. -/
theorem hoeffding_majorityReps_le {δ : ℝ} (hν : ν < 1 / 2) (hδ : 0 < δ) (hδn : δ ≤ n) :
    Real.exp (-(majorityReps ν δ n * (1 - 2 * ν) ^ 2 / 2)) ≤ δ / n := by
  have hn : (0 : ℝ) < n := lt_of_lt_of_le hδ hδn
  have hq : 1 ≤ (n : ℝ) / δ := by rw [le_div_iff₀ hδ]; linarith
  have hc : (0 : ℝ) < (1 - 2 * ν) ^ 2 := pow_pos (by linarith) 2
  set k : ℕ := ⌈Real.logb 2 (n / δ)⌉₊
  have hk : Real.log (n / δ) ≤ k := by
    have h1 : Real.logb 2 (n / δ) ≤ k := Nat.le_ceil _
    have h2 : Real.log (n / δ) ≤ Real.logb 2 (n / δ) := by
      rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two)]
      have := Real.log_nonneg hq
      have := Real.log_two_lt_d9
      nlinarith
    linarith
  have hr : (2 / (1 - 2 * ν) ^ 2 * k : ℝ) ≤ majorityReps ν δ n := Nat.le_ceil _
  have hr' : (k : ℝ) ≤ majorityReps ν δ n * (1 - 2 * ν) ^ 2 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hc] at hr
    linarith
  calc Real.exp (-(majorityReps ν δ n * (1 - 2 * ν) ^ 2 / 2))
      ≤ Real.exp (-Real.log (n / δ)) := Real.exp_le_exp.mpr (by linarith)
    _ = δ / n := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]

end LowLogitRank.Parity
