import LowLogitRank.Scalar

/-!
# Non-vacuity of `prop:scalar`: a matching root sampler

The premise of `prop:scalar` is satisfiable in the finite model `CappedAlgo`: the algorithm that
submits the empty prefix `n` times and returns the empirical centered logit
`(1/2) log (p̂ / (1 - p̂))`, with `n = ⌈400 (1 + e^{2T}) / ξ²⌉`, succeeds with probability at least
`0.99` under both teachers (Chebyshev's inequality). So the lower bound `e^{2T}/(30 ξ²)` is attained
up to a constant factor.
-/

namespace LowLogitRank.Scalar

open Finset

/-! ### Elementary bounds -/

theorem abs_log_one_add_le (y : ℝ) (hy : |y| ≤ 1 / 2) : |Real.log (1 + y)| ≤ 2 * |y| := by
  have hy' := abs_le.mp hy
  have hpos : 0 < 1 + y := by linarith
  have hup : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlow : 1 - (1 + y)⁻¹ ≤ Real.log (1 + y) := Real.one_sub_inv_le_log_of_pos hpos
  have hlow' : -2 * |y| ≤ 1 - (1 + y)⁻¹ := by
    have : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
    rw [this, le_div_iff₀ hpos]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_nonpos h]; nlinarith
  rw [abs_le]
  constructor
  · linarith
  · linarith [le_abs_self y]

/-- If `x` is within relative error `ε ≤ 1/2` of `q ≤ 1/2`, the centered logits differ by at most
`2ε`. -/
theorem logit_error (q x ε : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) (hε1 : ε ≤ 1 / 2)
    (hx : |x - q| ≤ ε * q) :
    |Real.log (x / (1 - x)) / 2 - Real.log (q / (1 - q)) / 2| ≤ 2 * ε := by
  have hx' := abs_le.mp hx
  have hε0 : 0 ≤ ε := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.mp h) hq0
    linarith [abs_nonneg (x - q)]
  have hx0 : 0 < x := by nlinarith
  have hx1 : 0 < 1 - x := by nlinarith
  have hq1 : 0 < 1 - q := by linarith
  have e1 : x / q = 1 + (x - q) / q := by field_simp; ring
  have e2 : (1 - x) / (1 - q) = 1 + (q - x) / (1 - q) := by field_simp; ring
  have b1 : |(x - q) / q| ≤ ε := by
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    exact hx
  have b2 : |(q - x) / (1 - q)| ≤ ε := by
    rw [abs_div, abs_of_pos hq1, div_le_iff₀ hq1, abs_sub_comm]
    nlinarith
  have l1 := abs_log_one_add_le _ (b1.trans hε1)
  have l2 := abs_log_one_add_le _ (b2.trans hε1)
  have hdiff : Real.log (x / (1 - x)) / 2 - Real.log (q / (1 - q)) / 2 =
      (Real.log (x / q) - Real.log ((1 - x) / (1 - q))) / 2 := by
    rw [Real.log_div hx0.ne' hx1.ne', Real.log_div hq0.ne' hq1.ne', Real.log_div hx0.ne' hq0.ne',
      Real.log_div hx1.ne' hq1.ne']
    ring
  rw [hdiff, ← e1, ← e2] at *
  rw [abs_div, abs_two, div_le_iff₀ two_pos]
  calc |Real.log (x / q) - Real.log ((1 - x) / (1 - q))|
      ≤ |Real.log (x / q)| + |Real.log ((1 - x) / (1 - q))| := abs_sub _ _
    _ ≤ 2 * |(x - q) / q| + 2 * |(q - x) / (1 - q)| := by rw [e1, e2]; linarith
    _ ≤ 2 * ε * 2 := by linarith

/-! ### Moments of the number of ones under i.i.d. replies -/

/-- The number of ones in a list of replies. -/
noncomputable def numOnes : List Bool → ℝ
  | [] => 0
  | b :: l => Cauchy.bitVal b + numOnes l

theorem condProb_const (q : ℝ) (h f : List Bool) :
    condProb (fun _ => q) h f = condProb (fun _ => q) [] f := by
  induction f generalizing h with
  | nil => simp
  | cons b f ih =>
    rw [condProb_cons, condProb_cons, ih (h ++ [b]), ih ([] ++ [b])]
    rfl

theorem sum_const_succ (q : ℝ) (m : ℕ) (G : List Bool → ℝ) :
    ∑ f : Word (m + 1), condProb (fun _ => q) [] f.toList * G f.toList =
      ∑ b : Bool, bern q b *
        ∑ v : Word m, condProb (fun _ => q) [] v.toList * G (b :: v.toList) := by
  rw [sum_word_succ]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun v _ => ?_
  rw [List.Vector.toList_cons, condProb_cons, condProb_const q ([] ++ [b]), mul_assoc]
  rfl

theorem moment_one (q : ℝ) (m : ℕ) :
    ∑ f : Word m, condProb (fun _ => q) [] f.toList * numOnes f.toList = m * q := by
  induction m with
  | zero => simp [numOnes]
  | succ m ih =>
    rw [sum_const_succ]
    simp only [numOnes, mul_add, sum_add_distrib, ← sum_mul, sum_condProb, ih]
    simp only [Fintype.sum_bool, bern, Cauchy.bitVal, ite_true, Bool.false_eq_true, ite_false]
    push_cast
    ring

theorem moment_two (q : ℝ) (m : ℕ) :
    ∑ f : Word m, condProb (fun _ => q) [] f.toList * numOnes f.toList ^ 2 =
      m * q + m * (m - 1) * q ^ 2 := by
  induction m with
  | zero => simp [numOnes]
  | succ m ih =>
    rw [sum_const_succ q m (fun l => numOnes l ^ 2)]
    have hsq : ∀ (b : Bool) (v : List Bool), numOnes (b :: v) ^ 2 =
        Cauchy.bitVal b + 2 * Cauchy.bitVal b * numOnes v + numOnes v ^ 2 := by
      intro b v
      cases b
      · simp [numOnes, Cauchy.bitVal]
      · simp only [numOnes, Cauchy.bitVal, ite_true]
        ring
    simp only [hsq, mul_add, sum_add_distrib, ← sum_mul, sum_condProb, ih]
    have h1 : ∀ b : Bool, ∑ v : Word m, condProb (fun _ => q) [] v.toList *
        (2 * Cauchy.bitVal b * numOnes v.toList) = 2 * Cauchy.bitVal b * (m * q) := by
      intro b
      rw [← moment_one q m, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      ring
    simp only [h1]
    simp only [Fintype.sum_bool, bern, Cauchy.bitVal, ite_true, Bool.false_eq_true, ite_false]
    push_cast
    ring

/-- The variance of the number of ones is `m q (1 - q)`. -/
theorem variance_numOnes (q : ℝ) (m : ℕ) :
    ∑ f : Word m, condProb (fun _ => q) [] f.toList * (numOnes f.toList - m * q) ^ 2 =
      m * q * (1 - q) := by
  have e : ∀ f : Word m, condProb (fun _ => q) [] f.toList * (numOnes f.toList - m * q) ^ 2 =
      condProb (fun _ => q) [] f.toList * numOnes f.toList ^ 2 -
        2 * (m * q) * (condProb (fun _ => q) [] f.toList * numOnes f.toList) +
        (m * q) ^ 2 * condProb (fun _ => q) [] f.toList := by
    intro f; ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, moment_one, moment_two,
    sum_condProb]
  ring

/-! ### The root sampler -/

/-- The algorithm that submits the empty prefix in each of its `n` rounds and returns the
empirical centered logit `(1/2) log (p̂ / (1 - p̂))`, `p̂` the fraction of ones. -/
noncomputable def rootSampler (n : ℕ) : CappedAlgo Unit n where
  weight _ := 1
  weight_nonneg _ := zero_le_one
  weight_sum := by simp
  query _ _ := []
  estimate _ r := Real.log (numOnes r.toList / n / (1 - numOnes r.toList / n)) / 2

theorem rootSampler_law (n : ℕ) (p : NextBit) (z : Unit × Word n) :
    (rootSampler n).law p z = condProb (fun _ => p []) [] z.2.toList := by
  simp only [CappedAlgo.law, rootSampler, one_mul]
  rfl

/-- Under a teacher with root logit `u ≤ 0`, `n ≥ 400 / (ξ² σ(2u))` root queries give the
centered logit within `ξ ≤ 1` with probability at least `0.99`. -/
theorem rootSampler_successProb (u ξ : ℝ) (n : ℕ) (hu : u ≤ 0) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hn : 400 / (ξ ^ 2 * sigmoid (2 * u)) ≤ n) :
    99 / 100 ≤ (rootSampler n).successProb (teacher u) ξ := by
  classical
  set q := sigmoid (2 * u) with hqdef
  have hq0 : 0 < q := sigmoid_pos _
  have hq1 : q < 1 := sigmoid_lt_one _
  have hqh : q ≤ 1 / 2 := by
    rw [hqdef, ← Cauchy.sigmoid_zero]
    exact Cauchy.sigmoid_mono (by linarith)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  set t := ξ / 2 * n * q with ht
  have htpos : 0 < t := by positivity
  have hP : ∀ g : List Bool, 0 < (fun _ : List Bool => q) g ∧ (fun _ : List Bool => q) g < 1 :=
    fun _ => ⟨hq0, hq1⟩
  -- the good event implies success
  have hgood : ∀ r : Word n, |numOnes r.toList - n * q| < t →
      |(rootSampler n).estimate () r - logit (teacher u) []| ≤ ξ := by
    intro r hr
    have hx : |numOnes r.toList / n - q| ≤ ξ / 2 * q := by
      have : numOnes r.toList / n - q = (numOnes r.toList - n * q) / n := by field_simp
      rw [this, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
      linarith
    have := logit_error q _ (ξ / 2) hq0 hqh (by linarith) hx
    simp only [rootSampler, logit, teacher_nil]
    linarith
  -- pointwise: `1[success] ≥ 1 - (N - nq)² / t²`
  have hpt : ∀ r : Word n,
      1 - (numOnes r.toList - n * q) ^ 2 / t ^ 2 ≤
        if |(rootSampler n).estimate () r - logit (teacher u) []| ≤ ξ then 1 else 0 := by
    intro r
    split_ifs with hs
    · have : 0 ≤ (numOnes r.toList - n * q) ^ 2 / t ^ 2 := by positivity
      linarith
    · have hbad : t ≤ |numOnes r.toList - n * q| := by
        by_contra h
        exact hs (hgood r (not_le.mp h))
      have : 1 ≤ (numOnes r.toList - n * q) ^ 2 / t ^ 2 := by
        have h2 := pow_le_pow_left₀ htpos.le hbad 2
        rw [sq_abs] at h2
        rw [le_div_iff₀ (by positivity), one_mul]
        exact h2
      linarith
  have hsucc : (rootSampler n).successProb (teacher u) ξ =
      ∑ r : Word n, condProb (fun _ => q) [] r.toList *
        (if |(rootSampler n).estimate () r - logit (teacher u) []| ≤ ξ then 1 else 0) := by
    simp only [CappedAlgo.successProb, CappedAlgo.prob, CappedAlgo.successSet, sum_filter,
      Fintype.sum_prod_type, Fintype.sum_unique, rootSampler_law, teacher_nil, mul_ite,
      mul_one, mul_zero]
    rfl
  have hlow : 1 - n * q * (1 - q) / t ^ 2 ≤ (rootSampler n).successProb (teacher u) ξ := by
    rw [hsucc]
    calc 1 - n * q * (1 - q) / t ^ 2 =
          ∑ r : Word n, condProb (fun _ => q) [] r.toList *
            (1 - (numOnes r.toList - n * q) ^ 2 / t ^ 2) := by
          simp only [mul_sub, mul_one, sum_sub_distrib, sum_condProb, mul_div_assoc', ← sum_div,
            variance_numOnes]
      _ ≤ _ := sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_left (hpt r) (condProb_pos _ hP _ _).le
  -- the variance term is at most `1/100`
  have hvar : n * q * (1 - q) / t ^ 2 ≤ 1 / 100 := by
    rw [ht, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hn
    have hq1' : 0 ≤ 1 - q := by linarith
    nlinarith [mul_pos hnpos hq0]
  linarith

/-- Non-vacuity and sharpness of `prop:scalar`: for `T ≥ 1` and `0 < ξ ≤ 1/6` there is a capped
algorithm with `n ≤ 400 (1 + e^{2T}) / ξ² + 1` rounds, all of them empty-prefix queries, that
estimates the initial logit within `ξ` with probability at least `0.99` under both teachers. -/
theorem prop_scalar_attained (T : ℕ) (hT : 1 ≤ T) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) :
    ∃ (n : ℕ) (A : CappedAlgo Unit n), (n : ℝ) ≤ 400 * (1 + Real.exp (2 * T)) / ξ ^ 2 + 1 ∧
      (∀ z, (A.emptyCount z : ℝ) = n) ∧
      99 / 100 ≤ A.successProb (teacher (-T)) ξ ∧
      99 / 100 ≤ A.successProb (teacher (-T + 3 * ξ)) ξ := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set n := ⌈400 * (1 + Real.exp (2 * T)) / ξ ^ 2⌉₊
  have hn : 400 * (1 + Real.exp (2 * T)) / ξ ^ 2 ≤ n := Nat.le_ceil _
  have hp0 : p0 T ≤ sigmoid (2 * -(T : ℝ)) := by rw [p0_eq]; ring_nf; exact le_refl _
  -- `σ(2u) ≥ p₀` for both teachers, so `400 / (ξ² σ(2u)) ≤ 400 (1 + e^{2T}) / ξ²`
  have hbound : ∀ u : ℝ, -T ≤ u → 400 / (ξ ^ 2 * sigmoid (2 * u)) ≤ n := by
    intro u hu
    refine le_trans ?_ hn
    have hs : p0 T ≤ sigmoid (2 * u) := hp0.trans (Cauchy.sigmoid_mono (by linarith))
    have hp0pos := p0_pos T
    have : 400 / (ξ ^ 2 * sigmoid (2 * u)) ≤ 400 / (ξ ^ 2 * p0 T) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hs (by positivity))
    refine this.trans (le_of_eq ?_)
    rw [p0]
    have := Real.exp_pos (2 * (T : ℝ))
    field_simp
  refine ⟨n, rootSampler n, (Nat.ceil_lt_add_one (by positivity)).le, ?_, ?_, ?_⟩
  · intro z
    simp [CappedAlgo.emptyCount, rootSampler]
  · exact rootSampler_successProb _ ξ n (by linarith) hξ0 (by linarith)
      (hbound _ le_rfl)
  · exact rootSampler_successProb _ ξ n (by linarith) hξ0 (by linarith)
      (hbound _ (by linarith))

end LowLogitRank.Scalar
