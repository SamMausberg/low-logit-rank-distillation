import LowLogitRank.Basic

/-!
# Polynomial precision (`sec:finite-bit-lm`)

The arithmetic of the paragraphs "Polynomial precision and exact feasibility" and of the
coefficient-margin paragraph after `lem:rational-spanner`. Here `O` is the alphabet size, `T` the
length, `S` the (enlarged) probability-rank parameter, `K₀` the universal exponent of the tree floor
`b ≥ (OST/η₀)^{-K₀}`, and `c = η₀^{10 O T S}` the cutoff of Assumption 7.1 of Liu and Moitra.
-/

namespace LowLogitRank.Projection

open Finset

/-- The cutoff `c = η₀^{10 O T S}`. -/
noncomputable def cutoff (η₀ : ℝ) (O T S : ℕ) : ℝ := η₀ ^ (10 * O * T * S)

section Cutoff

variable {η₀ : ℝ} {O T S K₀ : ℕ}

/-- `sec:finite-bit-lm`: `c ≤ η₀^{2K₀} ≤ (OST/η₀)^{-K₀}` when `K₀ ≤ S`, `O, T ≥ 1` and
`0 < η₀ ≤ 1/(OST)`. -/
theorem cutoff_le_floor (hO : 1 ≤ O) (hT : 1 ≤ T) (hKS : K₀ ≤ S) (hη0 : 0 < η₀)
    (hη : η₀ ≤ 1 / (O * S * T)) :
    cutoff η₀ O T S ≤ η₀ ^ (2 * K₀) ∧
      η₀ ^ (2 * K₀) ≤ ((O * S * T : ℝ) / η₀) ^ (-(K₀ : ℤ)) := by
  have hO' : (1 : ℝ) ≤ O := by exact_mod_cast hO
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hS' : (1 : ℝ) ≤ S := by
    have : 1 ≤ S := by
      rcases Nat.eq_zero_or_pos K₀ with h | h
      · -- `η₀ ≤ 1/(O S T)` with `S = 0` would force `η₀ ≤ 0`
        by_contra hS
        have : S = 0 := by omega
        subst this
        simp at hη
        linarith
      · omega
    exact_mod_cast this
  have hOST : (1 : ℝ) ≤ O * S * T := by
    have := mul_le_mul hO' hS' zero_le_one (by linarith)
    have := mul_le_mul this hT' zero_le_one (by positivity)
    simpa using this
  have hη1 : η₀ ≤ 1 := hη.trans (by rw [div_le_one (by linarith)]; exact hOST)
  constructor
  · unfold cutoff
    apply pow_le_pow_of_le_one hη0.le hη1
    have : 1 ≤ O * T := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  · rw [zpow_neg, zpow_natCast, ← inv_pow, inv_div, pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    rw [le_div_iff₀ (by linarith), sq, mul_assoc]
    have : η₀ * (O * S * T) ≤ 1 := by
      rw [le_div_iff₀ (by linarith)] at hη; linarith
    nlinarith

/-- `sec:finite-bit-lm`: the empirical tree is `c`-positive, `c ≤ b`, whenever its floor satisfies
`b ≥ (OST/η₀)^{-K₀}`. -/
theorem cutoff_le_of_floor (hO : 1 ≤ O) (hT : 1 ≤ T) (hKS : K₀ ≤ S) (hη0 : 0 < η₀)
    (hη : η₀ ≤ 1 / (O * S * T)) {b : ℝ} (hb : ((O * S * T : ℝ) / η₀) ^ (-(K₀ : ℤ)) ≤ b) :
    cutoff η₀ O T S ≤ b := by
  obtain ⟨h1, h2⟩ := cutoff_le_floor hO hT hKS hη0 hη
  linarith

/-- `η₀ log (1/η₀) ≤ 1/e` for `η₀ > 0`. -/
theorem mul_log_inv_le_exp_neg_one (hη0 : 0 < η₀) : η₀ * Real.log (1 / η₀) ≤ Real.exp (-1) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (Real.log (1 / η₀))
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log hη0, mul_comm] at h
  rwa [one_div, Real.log_inv]

/-- `sec:finite-bit-lm`: `log (1/c^T) = 10 O T² S log (1/η₀) ≤ 10 (OTS)²/η₀`, using
`η₀ log (1/η₀) ≤ 1/e < OS`. -/
theorem log_inv_cutoff_pow (hO : 1 ≤ O) (hS : 1 ≤ S) (hη0 : 0 < η₀) :
    Real.log (1 / cutoff η₀ O T S ^ T) = 10 * O * T ^ 2 * S * Real.log (1 / η₀) ∧
      10 * O * T ^ 2 * S * Real.log (1 / η₀) ≤ 10 * (O * T * S) ^ 2 / η₀ := by
  constructor
  · unfold cutoff
    rw [one_div, Real.log_inv, ← pow_mul, Real.log_pow, one_div, Real.log_inv]
    push_cast
    ring
  · have hO' : (1 : ℝ) ≤ O := by exact_mod_cast hO
    have hS' : (1 : ℝ) ≤ S := by exact_mod_cast hS
    have h1 := mul_log_inv_le_exp_neg_one hη0
    have h2 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hOS : (1 : ℝ) ≤ O * S := by nlinarith
    -- `log (1/η₀) ≤ O S / η₀`
    have h3 : Real.log (1 / η₀) ≤ O * S / η₀ := by
      rw [le_div_iff₀ hη0]; linarith
    have hpos : (0 : ℝ) ≤ 10 * O * T ^ 2 * S := by positivity
    calc 10 * O * T ^ 2 * S * Real.log (1 / η₀) ≤ 10 * O * T ^ 2 * S * (O * S / η₀) :=
          mul_le_mul_of_nonneg_left h3 hpos
      _ = 10 * (O * T * S) ^ 2 / η₀ := by ring

/-- `sec:finite-bit-lm`: the larger positive-representability cutoff `2√c` exceeds `c^T`. -/
theorem cutoff_pow_le_two_sqrt (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1) (hT : 1 ≤ T) :
    cutoff η₀ O T S ^ T ≤ 2 * Real.sqrt (cutoff η₀ O T S) := by
  have hc0 : 0 ≤ cutoff η₀ O T S := by unfold cutoff; positivity
  have hc1 : cutoff η₀ O T S ≤ 1 := by unfold cutoff; exact pow_le_one₀ hη0.le hη1
  have h1 : cutoff η₀ O T S ^ T ≤ cutoff η₀ O T S := pow_le_of_le_one hc0 hc1 (by omega)
  have h2 : cutoff η₀ O T S ≤ Real.sqrt (cutoff η₀ O T S) := by
    rw [Real.le_sqrt hc0 hc0]; nlinarith
  have h3 := Real.sqrt_nonneg (cutoff η₀ O T S)
  linarith

/-- `sec:finite-bit-lm`: if the feasible floor satisfies `μ ≥ c^T/M₀` with `M₀ > 0`, then
`log (1/μ) ≤ 10 O T² S log (1/η₀) + log M₀`. The bound `μ ≥ c^T/M₀` is a hypothesis; it comes
from the rational bounds on the stored coordinates. -/
theorem log_inv_floor_le (hη0 : 0 < η₀) {M₀ μ : ℝ} (hM : 0 < M₀)
    (hμ : cutoff η₀ O T S ^ T / M₀ ≤ μ) :
    Real.log (1 / μ) ≤ 10 * O * T ^ 2 * S * Real.log (1 / η₀) + Real.log M₀ := by
  have hc : 0 < cutoff η₀ O T S ^ T := by unfold cutoff; positivity
  have hq : 0 < cutoff η₀ O T S ^ T / M₀ := div_pos hc hM
  have h1 : Real.log (1 / μ) ≤ Real.log (1 / (cutoff η₀ O T S ^ T / M₀)) := by
    apply Real.log_le_log (by have := hq.trans_le hμ; positivity)
    exact one_div_le_one_div_of_le hq hμ
  have h2 : Real.log (1 / (cutoff η₀ O T S ^ T / M₀)) =
      Real.log (1 / cutoff η₀ O T S ^ T) + Real.log M₀ := by
    rw [one_div_div, Real.log_div hM.ne' hc.ne', one_div, Real.log_inv]
    ring
  have h3 : Real.log (1 / cutoff η₀ O T S ^ T) = 10 * O * T ^ 2 * S * Real.log (1 / η₀) := by
    unfold cutoff
    rw [one_div, Real.log_inv, ← pow_mul, Real.log_pow, one_div, Real.log_inv]
    push_cast
    ring
  linarith

/-- `sec:finite-bit-lm`: `c^{1/10} = η₀^{OTS}`. -/
theorem cutoff_rpow_tenth (hη0 : 0 < η₀) :
    cutoff η₀ O T S ^ ((1 : ℝ) / 10) = η₀ ^ (O * T * S) := by
  unfold cutoff
  have e : η₀ ^ (10 * O * T * S) = (η₀ ^ (O * T * S)) ^ (10 : ℕ) := by
    rw [← pow_mul]; ring_nf
  rw [e, show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)

/-- The hypotheses of `cutoff_le_floor` and `log_inv_floor_le` are satisfiable:
`O = T = S = K₀ = 1`, `η₀ = 1/2`, `M₀ = 1`, `μ = c^T / M₀`. -/
example : cutoff (1 / 2) 1 1 1 ≤ ((1 / 2 : ℝ)) ^ (2 * 1) ∧
    Real.log (1 / (cutoff (1 / 2) 1 1 1 ^ 1 / 1)) ≤
      10 * (1 : ℕ) * (1 : ℕ) ^ 2 * (1 : ℕ) * Real.log (1 / (1 / 2)) + Real.log 1 :=
  ⟨(cutoff_le_floor (η₀ := 1 / 2) (K₀ := 1) le_rfl le_rfl le_rfl (by norm_num)
      (by norm_num)).1,
    log_inv_floor_le (by norm_num) one_pos le_rfl⟩

end Cutoff

/-! ### Rational bounds on the stored coordinates -/

/-- `sec:finite-bit-lm`, stored coordinates: if `b^T ≤ v_i ≤ 1` for the `s ≥ 1` selected histories
and `k ≥ 1`, then `w = 1/(k ∑_i v_i)` satisfies `1/(ks) ≤ w ≤ b^{-T}/k`, and `u_i = v_i w` satisfies
`0 < u_i ≤ 1`. -/
theorem stored_bounds {σ : Type*} [Fintype σ] [Nonempty σ] {v : σ → ℝ} {b k : ℝ} {T : ℕ}
    (hb : 0 < b) (hk : 1 ≤ k) (hv0 : ∀ i, b ^ T ≤ v i) (hv1 : ∀ i, v i ≤ 1) :
    1 / (k * Fintype.card σ) ≤ 1 / (k * ∑ i, v i) ∧ 1 / (k * ∑ i, v i) ≤ (b ^ T)⁻¹ / k ∧
      ∀ i, 0 < v i * (1 / (k * ∑ i, v i)) ∧ v i * (1 / (k * ∑ i, v i)) ≤ 1 := by
  have hbT : 0 < b ^ T := pow_pos hb T
  have hvpos : ∀ i, 0 < v i := fun i => hbT.trans_le (hv0 i)
  obtain ⟨i₀⟩ := ‹Nonempty σ›
  have hle : ∀ i, v i ≤ ∑ j, v j := fun i =>
    single_le_sum (fun j _ => (hvpos j).le) (mem_univ i)
  have hsum_pos : 0 < ∑ i, v i := (hvpos i₀).trans_le (hle i₀)
  have hsum_le : ∑ i, v i ≤ Fintype.card σ := by
    calc ∑ i, v i ≤ ∑ _i : σ, (1 : ℝ) := sum_le_sum fun i _ => hv1 i
      _ = Fintype.card σ := by simp
  have hk0 : 0 < k := by linarith
  refine ⟨?_, ?_, fun i => ⟨by have := hvpos i; positivity, ?_⟩⟩
  · exact one_div_le_one_div_of_le (by positivity) (by gcongr)
  · have h1 : b ^ T ≤ ∑ i, v i := (hv0 i₀).trans (hle i₀)
    have e : (b ^ T)⁻¹ / k = 1 / (k * b ^ T) := by field_simp
    rw [e]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left h1 hk0.le)
  · rw [mul_one_div, div_le_one (by positivity)]
    nlinarith [hle i, hvpos i]

/-! ### Coefficient margin (paragraph after `lem:rational-spanner`) -/

/-- Coefficient margin after `lem:rational-spanner`: composing a `(1,0)` spanner of at most `S`
rows with a `(3/2)`-bounded spanner gives coefficients `|∑_i c'_i c_{i,j}| ≤ 3S/2`. -/
theorem composed_coeff_le {ι : Type*} (I : Finset ι) {S : ℕ} (hI : I.card ≤ S) (c' c : ι → ℝ)
    (hc' : ∀ i ∈ I, |c' i| ≤ 1) (hc : ∀ i ∈ I, |c i| ≤ 3 / 2) :
    |∑ i ∈ I, c' i * c i| ≤ 3 * S / 2 := by
  calc |∑ i ∈ I, c' i * c i| ≤ ∑ i ∈ I, |c' i * c i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, (3 / 2 : ℝ) := by
        refine sum_le_sum fun i hi => ?_
        rw [abs_mul]
        have := hc' i hi; have := hc i hi
        nlinarith [abs_nonneg (c' i), abs_nonneg (c i)]
    _ = I.card * (3 / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ S * (3 / 2) := by gcongr
    _ = 3 * S / 2 := by ring

/-- Coefficient margin after `lem:rational-spanner`: with `|y_j| ≤ 3S/2`, `γ ≤ 1/4` and
`S ≥ 1`, the smoothed coefficient satisfies `|y_j + √γ| ≤ 3S/2 + 1/2 ≤ 2S`. -/
theorem smoothed_coeff_le {y γ S : ℝ} (hy : |y| ≤ 3 * S / 2) (hγ : γ ≤ 1 / 4)
    (hS : 1 ≤ S) : |y + Real.sqrt γ| ≤ 3 * S / 2 + 1 / 2 ∧ 3 * S / 2 + 1 / 2 ≤ 2 * S := by
  have hs : Real.sqrt γ ≤ 1 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num; linarith
  have hs0 := Real.sqrt_nonneg γ
  refine ⟨?_, by linarith⟩
  calc |y + Real.sqrt γ| ≤ |y| + |Real.sqrt γ| := abs_add_le _ _
    _ ≤ 3 * S / 2 + 1 / 2 := by rw [abs_of_nonneg hs0]; linarith

/-! ### The syntactic floor of the computed branch probabilities -/

section Floor

variable {σ ι : Type*} [Fintype σ] [Fintype ι]

omit [Fintype ι] in
/-- The unnormalized next-token vector `q_o = ∑_i α_i P_{i,o}` has `|q_o| ≤ 3S²` when there are at
most `S` coefficients, `|α_i| ≤ 3S` and `|P_{i,o}| ≤ 1`. -/
theorem abs_unnormalized_le {S : ℝ} (hcard : (Fintype.card σ : ℝ) ≤ S) (α : σ → ℝ)
    (P : σ → ι → ℝ) (hα : ∀ i, |α i| ≤ 3 * S) (hP : ∀ i o, |P i o| ≤ 1) (o : ι) :
    |∑ i, α i * P i o| ≤ 3 * S ^ 2 := by
  have hS : 0 ≤ S := by
    have := hα; by_cases h : Nonempty σ
    · obtain ⟨i⟩ := h; have := hα i; linarith [abs_nonneg (α i)]
    · simp only [not_nonempty_iff] at h
      rw [Fintype.card_eq_zero] at hcard; simpa using hcard
  calc |∑ i, α i * P i o| ≤ ∑ i, |α i * P i o| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, 3 * S := by
        refine sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have := hα i; have := hP i o
        nlinarith [abs_nonneg (α i), abs_nonneg (P i o)]
    _ = Fintype.card σ * (3 * S) := by rw [sum_const, nsmul_eq_mul, card_univ]
    _ ≤ S * (3 * S) := by gcongr
    _ = 3 * S ^ 2 := by ring

/-- Clipping at the floor `2c'` with `0 < c' ≤ 1` keeps every coordinate of magnitude at most `3S²`
inside `[2c', 3S² + 2]`. -/
theorem clipped_mem {q c' S : ℝ} (hq : |q| ≤ 3 * S ^ 2) (hc1 : c' ≤ 1) :
    2 * c' ≤ max q (2 * c') ∧ max q (2 * c') ≤ 3 * S ^ 2 + 2 := by
  refine ⟨le_max_right _ _, max_le ?_ (by nlinarith [sq_nonneg S])⟩
  linarith [le_abs_self q]

/-- If every coordinate of a vector with `O` coordinates lies in `[2c', 3S² + 2]`, every normalized
coordinate is at least `2c' / (O (3S² + 2))`. -/
theorem normalized_ge {q : ι → ℝ} {c' S : ℝ} (hc : 0 < c') (hlo : ∀ o, 2 * c' ≤ q o)
    (hhi : ∀ o, q o ≤ 3 * S ^ 2 + 2) (o : ι) :
    2 * c' / (Fintype.card ι * (3 * S ^ 2 + 2)) ≤ q o / ∑ o', q o' := by
  have hsum : ∑ o', q o' ≤ Fintype.card ι * (3 * S ^ 2 + 2) := by
    calc ∑ o', q o' ≤ ∑ _o' : ι, (3 * S ^ 2 + 2) := sum_le_sum fun o' _ => hhi o'
      _ = Fintype.card ι * (3 * S ^ 2 + 2) := by rw [sum_const, nsmul_eq_mul, card_univ]
  have hpos : 0 < ∑ o', q o' :=
    sum_pos (fun o' _ => by linarith [hlo o']) ⟨o, mem_univ o⟩
  calc 2 * c' / (Fintype.card ι * (3 * S ^ 2 + 2)) ≤ 2 * c' / ∑ o', q o' :=
        div_le_div_of_nonneg_left (by linarith) hpos hsum
    _ ≤ q o / ∑ o', q o' := div_le_div_of_nonneg_right (hlo o) hpos.le

/-- The computed next-token probability `p_o = max(q_o, 2c') / ∑_{o'} max(q_{o'}, 2c')`, where
`q_o = ∑_i α_i P_{i,o}`. -/
noncomputable def branchProb (α : σ → ℝ) (P : σ → ι → ℝ) (c' : ℝ) (o : ι) : ℝ :=
  max (∑ i, α i * P i o) (2 * c') / ∑ o', max (∑ i, α i * P i o') (2 * c')

/-- `sec:finite-bit-lm`, syntactic floor: with at most `S` coefficients `|α_i| ≤ 3S`, stored
probabilities `|P_{i,o}| ≤ 1`, and floor `2c'` where `c' = c^{1/10} ∈ (0, 1]`, every computed
branch probability satisfies `p_o ≥ 2c' / (O (3S² + 2))`, `O` the alphabet size. The floor is read
as clipping, `max(q_o, 2c')`. -/
theorem branchProb_ge {S c' : ℝ} (hcard : (Fintype.card σ : ℝ) ≤ S) (α : σ → ℝ)
    (P : σ → ι → ℝ) (hα : ∀ i, |α i| ≤ 3 * S) (hP : ∀ i o, |P i o| ≤ 1) (hc0 : 0 < c')
    (hc1 : c' ≤ 1) (o : ι) :
    2 * c' / (Fintype.card ι * (3 * S ^ 2 + 2)) ≤ branchProb α P c' o :=
  normalized_ge hc0 (fun o => (clipped_mem (abs_unnormalized_le hcard α P hα hP o) hc1).1)
    (fun o => (clipped_mem (abs_unnormalized_le hcard α P hα hP o) hc1).2) o

/-- The updated coefficients `ν_i = α_i P_{i,o} / p_o` have magnitude at most `3S · D / (2c')`
when `p_o ≥ 2c'/D`; with `D = O (3S² + 2)` this is `poly(O, S) c^{-1/10}`. -/
theorem abs_updated_coeff_le {S c' p D α P : ℝ} (hα : |α| ≤ 3 * S) (hP : |P| ≤ 1)
    (hc0 : 0 < c') (hD : 0 < D) (hp : 2 * c' / D ≤ p) :
    |α * P / p| ≤ 3 * S * D / (2 * c') := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  have h1 : |α * P| ≤ 3 * S := by
    rw [abs_mul]; nlinarith [abs_nonneg α, abs_nonneg P]
  rw [abs_div, abs_of_pos hp0, div_le_div_iff₀ hp0 (by positivity)]
  rw [div_le_iff₀ hD] at hp
  nlinarith [abs_nonneg (α * P)]

end Floor

end LowLogitRank.Projection
