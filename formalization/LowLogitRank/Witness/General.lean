import LowLogitRank.Witness.Potential

/-!
# The witness bound, general form (`lem:explicit-gls-token-envelope`, explicit witness bound)

At a fixed cut, the `j`th witness addition comes with a discrepancy row `L_j`, evaluated at the
witness columns `i`. The surrounding argument supplies vectors `v_j, φ_i ∈ ℝ^d` (a difference of
two coefficient combinations of history factors, and the future factor of the `i`th witness
column) with `‖v_j‖ ≤ B`, `‖φ_i‖ ≤ R`, `L_j(i) = 0` for `i < j` (reconstruction equalities),
`|L_j(j)| > g` (discrepancy test) and `|L_j(i) - ⟨v_j, φ_i⟩| ≤ e₀` for `i ≤ j`. These are
hypotheses here; `Witness/Count.lean` derives the norm and error bounds from the coefficient
structure of the discrepancies.

With `λ = (e₀/B)²` and `M_j = λ I + ∑_{i ≤ j} φ_i φ_iᵀ` we prove
`v_jᵀ M_{j-1} v_j ≤ j e₀²`, `|⟨v_j, φ_j⟩| > g - e₀`, `φ_jᵀ M_{j-1}⁻¹ φ_j > (g - e₀)²/(j e₀²)`,
and, when every leverage exceeds one, `M < d log₂ (1 + M a₀ / d)` with `a₀ = (BR/e₀)²`.
-/

namespace LowLogitRank.Witness

open Matrix Finset

variable {d : ℕ}

/-- The hypotheses of the general witness bound, for witnesses `1, …, m` at one cut. -/
structure WitnessData (d m : ℕ) (B R g e₀ : ℝ) (v φ : ℕ → Fin d → ℝ) (Lw : ℕ → ℕ → ℝ) :
    Prop where
  /-- `‖v_j‖₂ ≤ B`. -/
  v_le : ∀ j ∈ Icc 1 m, v j ⬝ᵥ v j ≤ B ^ 2
  /-- `‖φ_i‖₂ ≤ R`. -/
  φ_le : ∀ i ∈ Icc 1 m, φ i ⬝ᵥ φ i ≤ R ^ 2
  /-- Reconstruction equalities: `L_j(i) = 0` for `i < j`. -/
  zero : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i < j → Lw j i = 0
  /-- Discrepancy test: `|L_j(j)| > g`. -/
  disc : ∀ j ∈ Icc 1 m, g < |Lw j j|
  /-- Factorization error: `|L_j(i) - ⟨v_j, φ_i⟩| ≤ e₀` for `i ≤ j`. -/
  approx : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i ≤ j → |Lw j i - v j ⬝ᵥ φ i| ≤ e₀

namespace WitnessData

variable {m : ℕ} {B R g e₀ : ℝ} {v φ : ℕ → Fin d → ℝ} {Lw : ℕ → ℕ → ℝ}

/-- `lem:explicit-gls-token-envelope` (witness bound): `v_jᵀ M_{j-1} v_j ≤ j e₀²` with
`λ = (e₀/B)²`. -/
theorem quad_le (h : WitnessData d m B R g e₀ v φ Lw) (hB : 0 < B) {j : ℕ} (hj : j ∈ Icc 1 m) :
    v j ⬝ᵥ (gram ((e₀ / B) ^ 2) φ (j - 1) *ᵥ v j) ≤ j * e₀ ^ 2 := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
  rw [quad_gram]
  have h1 : (e₀ / B) ^ 2 * (v j ⬝ᵥ v j) ≤ e₀ ^ 2 := by
    calc (e₀ / B) ^ 2 * (v j ⬝ᵥ v j) ≤ (e₀ / B) ^ 2 * B ^ 2 :=
          mul_le_mul_of_nonneg_left (h.v_le j hj) (by positivity)
      _ = e₀ ^ 2 := by field_simp
  have h2 : ∑ i ∈ Icc 1 (j - 1), (v j ⬝ᵥ φ i) ^ 2 ≤ ∑ _i ∈ Icc 1 (j - 1), e₀ ^ 2 := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_Icc.mp hi
    have hz := h.zero j hj i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩) (by omega)
    have ha := h.approx j hj i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩) (by omega)
    rw [hz, zero_sub, abs_neg] at ha
    have := abs_le.mp ha
    nlinarith [this.1, this.2]
  have h3 : ∑ _i ∈ Icc 1 (j - 1), e₀ ^ 2 = ((j : ℝ) - 1) * e₀ ^ 2 := by
    simp [Nat.cast_sub hj1]
  linarith

/-- `lem:explicit-gls-token-envelope` (witness bound): `|⟨v_j, φ_j⟩| > g - e₀`. -/
theorem inner_gt (h : WitnessData d m B R g e₀ v φ Lw) {j : ℕ} (hj : j ∈ Icc 1 m) :
    g - e₀ < |v j ⬝ᵥ φ j| := by
  have h1 := h.disc j hj
  have h2 := h.approx j hj j hj le_rfl
  have h3 := abs_sub_abs_le_abs_sub (Lw j j) (v j ⬝ᵥ φ j)
  linarith

/-- `lem:explicit-gls-token-envelope` (witness bound): Cauchy–Schwarz in the `M_{j-1}` inner
product gives `φ_jᵀ M_{j-1}⁻¹ φ_j > (g - e₀)² / (j e₀²)`. -/
theorem leverage_gt (h : WitnessData d m B R g e₀ v φ Lw) (hB : 0 < B) (he₀ : 0 < e₀)
    (heg : e₀ < g) {j : ℕ} (hj : j ∈ Icc 1 m) :
    (g - e₀) ^ 2 / (j * e₀ ^ 2) < leverage ((e₀ / B) ^ 2) φ j := by
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hlam : 0 < (e₀ / B) ^ 2 := by positivity
  have hCS := dotProduct_sq_le (gram_posDef hlam φ (j - 1)) (v j) (φ j)
  have hq := h.quad_le hB hj
  have hlev := leverage_nonneg hlam φ j
  have hin := h.inner_gt hj
  have hsq : (g - e₀) ^ 2 < (v j ⬝ᵥ φ j) ^ 2 := by
    rw [← sq_abs (v j ⬝ᵥ φ j)]
    exact pow_lt_pow_left₀ hin (by linarith) two_ne_zero
  rw [div_lt_iff₀ (by positivity)]
  have : (v j ⬝ᵥ (gram ((e₀ / B) ^ 2) φ (j - 1) *ᵥ v j)) * leverage ((e₀ / B) ^ 2) φ j ≤
      j * e₀ ^ 2 * leverage ((e₀ / B) ^ 2) φ j := mul_le_mul_of_nonneg_right hq hlev
  unfold leverage at this hlev ⊢
  nlinarith

/-- `lem:explicit-gls-token-envelope` (witness bound), general form. If `m ≥ 1` witnesses
satisfy the hypotheses and `m e₀² ≤ (g - e₀)²` (so every leverage exceeds one), then
`m < d log₂ (1 + m a₀ / d)` with `a₀ = (BR/e₀)²`. -/
theorem lt_logb (h : WitnessData d m B R g e₀ v φ Lw) (hd : 1 ≤ d) (hm : 1 ≤ m) (hB : 0 < B)
    (he₀ : 0 < e₀) (heg : e₀ < g) (hlev : m * e₀ ^ 2 ≤ (g - e₀) ^ 2) :
    (m : ℝ) < d * Real.logb 2 (1 + m * (B * R / e₀) ^ 2 / d) := by
  have hlam : 0 < (e₀ / B) ^ 2 := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have key := lt_of_leverage_gt_one hlam hd φ m hm R h.φ_le fun j hj => by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    have h1 : 1 ≤ (g - e₀) ^ 2 / (j * e₀ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith [h.leverage_gt hB he₀ heg hj]
  have heq : (m : ℝ) * R ^ 2 / (d * (e₀ / B) ^ 2) = m * (B * R / e₀) ^ 2 / d := by
    field_simp
  rwa [heq] at key

end WitnessData

/-- `lem:explicit-gls-token-envelope` (witness bound), general form for vectors in
`EuclideanSpace ℝ (Fin d)`, with norms `‖·‖` and inner products `⟪·, ·⟫`. The hypotheses
come from the surrounding modeling (see `WitnessData`). Conclusion: `m < d log₂ (1 + m a₀ / d)`,
`a₀ = (BR/e₀)²`, provided `m e₀² ≤ (g - e₀)²`. -/
theorem witness_general (hd : 1 ≤ d) {B R g e₀ : ℝ} (hB : 0 < B) (he₀ : 0 < e₀) (heg : e₀ < g)
    (m : ℕ) (hm : 1 ≤ m) (v φ : ℕ → EuclideanSpace ℝ (Fin d)) (Lw : ℕ → ℕ → ℝ)
    (hv : ∀ j ∈ Icc 1 m, ‖v j‖ ≤ B) (hφ : ∀ i ∈ Icc 1 m, ‖φ i‖ ≤ R)
    (hzero : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i < j → Lw j i = 0)
    (hdisc : ∀ j ∈ Icc 1 m, g < |Lw j j|)
    (happrox : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i ≤ j → |Lw j i - inner ℝ (v j) (φ i)| ≤ e₀)
    (hlev : m * e₀ ^ 2 ≤ (g - e₀) ^ 2) :
    (m : ℝ) < d * Real.logb 2 (1 + m * (B * R / e₀) ^ 2 / d) := by
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin d), inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  have hsq : ∀ (x : EuclideanSpace ℝ (Fin d)) (C : ℝ), ‖x‖ ≤ C → x.ofLp ⬝ᵥ x.ofLp ≤ C ^ 2 := by
    intro x C hx
    rw [← hinner, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg x) hx 2
  refine WitnessData.lt_logb (v := fun j => (v j).ofLp) (φ := fun i => (φ i).ofLp) (Lw := Lw)
    ⟨fun j hj => hsq _ _ (hv j hj), fun i hi => hsq _ _ (hφ i hi), hzero, hdisc,
      fun j hj i hi hij => by simpa [hinner] using happrox j hj i hi hij⟩
    hd hm hB he₀ heg hlev

end LowLogitRank.Witness
