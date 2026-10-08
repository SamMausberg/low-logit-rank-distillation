import LowLogitRank.Basic

/-!
# The elliptical potential (explicit witness bound of `lem:explicit-gls-token-envelope`)

For `λ > 0` and vectors `φ_1, φ_2, … ∈ ℝ^d` put `M_j = λ I_d + ∑_{i ≤ j} φ_i φ_iᵀ`.
This file proves the three facts used in the paragraph "Explicit witness bound":

* the matrix determinant lemma `det M_j = det M_{j-1} (1 + φ_jᵀ M_{j-1}⁻¹ φ_j)`, hence
  `det M_m = λ^d ∏_{j ≤ m} (1 + φ_jᵀ M_{j-1}⁻¹ φ_j)`;
* the trace–determinant (AM–GM) inequality `det A ≤ (tr A / d)^d` for positive semidefinite `A`,
  hence `det M_m / det M_0 ≤ (1 + ∑ ‖φ_i‖² / (dλ))^d`;
* Cauchy–Schwarz in the `M` inner product, `⟨v, φ⟩² ≤ (vᵀ M v)(φᵀ M⁻¹ φ)` for positive definite `M`.

Vectors are `Fin d → ℝ`; the Euclidean inner product is `⬝ᵥ` and `‖x‖₂² = x ⬝ᵥ x`.
-/

namespace LowLogitRank.Witness

open Matrix Finset

variable {d : ℕ}

/-! ### The matrices `M_j` -/

/-- `M_j = λ I_d + ∑_{i=1}^{j} φ_i φ_iᵀ`. -/
noncomputable def gram (lam : ℝ) (φ : ℕ → Fin d → ℝ) (j : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  lam • (1 : Matrix (Fin d) (Fin d) ℝ) + ∑ i ∈ Icc 1 j, vecMulVec (φ i) (φ i)

/-- The leverage `φ_jᵀ M_{j-1}⁻¹ φ_j` of the `j`th vector. -/
noncomputable def leverage (lam : ℝ) (φ : ℕ → Fin d → ℝ) (j : ℕ) : ℝ :=
  φ j ⬝ᵥ ((gram lam φ (j - 1))⁻¹ *ᵥ φ j)

theorem gram_zero (lam : ℝ) (φ : ℕ → Fin d → ℝ) : gram lam φ 0 = lam • 1 := by
  simp [gram]

theorem gram_succ (lam : ℝ) (φ : ℕ → Fin d → ℝ) (j : ℕ) :
    gram lam φ (j + 1) = gram lam φ j + vecMulVec (φ (j + 1)) (φ (j + 1)) := by
  simp only [gram, Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1), add_assoc]

theorem posSemidef_vecMulVec_self (u : Fin d → ℝ) : (vecMulVec u u).PosSemidef := by
  simpa using posSemidef_vecMulVec_self_star u

theorem gram_posDef {lam : ℝ} (hlam : 0 < lam) (φ : ℕ → Fin d → ℝ) (j : ℕ) :
    (gram lam φ j).PosDef := by
  have h1 : (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef := PosDef.one.smul hlam
  exact h1.add_posSemidef (posSemidef_sum _ fun i _ => posSemidef_vecMulVec_self (φ i))

/-- The quadratic form of `M_j`: `vᵀ M_j v = λ ‖v‖² + ∑_{i ≤ j} ⟨v, φ_i⟩²`. -/
theorem quad_gram (lam : ℝ) (φ : ℕ → Fin d → ℝ) (j : ℕ) (v : Fin d → ℝ) :
    v ⬝ᵥ (gram lam φ j *ᵥ v) = lam * (v ⬝ᵥ v) + ∑ i ∈ Icc 1 j, (v ⬝ᵥ φ i) ^ 2 := by
  simp only [gram, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm (φ i) v]
  ring

/-! ### The matrix determinant lemma -/

/-- The matrix determinant lemma for a symmetric rank-one update:
`det (A + u uᵀ) = det A · (1 + uᵀ A⁻¹ u)` when `A` is invertible. -/
theorem det_add_vecMulVec {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : IsUnit A.det) (u : n → ℝ) :
    (A + vecMulVec u u).det = A.det * (1 + u ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  rw [vecMulVec_eq Unit, det_add_replicateCol_mul_replicateRow hA, Matrix.mul_assoc,
    ← replicateCol_mulVec, det_unique (n := Unit)]
  rfl

/-- `lem:explicit-gls-token-envelope` (matrix determinant lemma):
`det M_j = det M_{j-1} · (1 + φ_jᵀ M_{j-1}⁻¹ φ_j)`. -/
theorem det_gram_succ {lam : ℝ} (hlam : 0 < lam) (φ : ℕ → Fin d → ℝ) (j : ℕ) :
    (gram lam φ (j + 1)).det = (gram lam φ j).det * (1 + leverage lam φ (j + 1)) := by
  rw [gram_succ, det_add_vecMulVec (isUnit_iff_ne_zero.mpr (gram_posDef hlam φ j).det_pos.ne')]
  simp [leverage]

theorem det_gram_zero (lam : ℝ) (φ : ℕ → Fin d → ℝ) : (gram lam φ 0).det = lam ^ d := by
  simp [gram_zero]

/-- `det M_m = λ^d ∏_{j=1}^{m} (1 + φ_jᵀ M_{j-1}⁻¹ φ_j)`. -/
theorem det_gram_eq_prod {lam : ℝ} (hlam : 0 < lam) (φ : ℕ → Fin d → ℝ) (m : ℕ) :
    (gram lam φ m).det = lam ^ d * ∏ j ∈ Icc 1 m, (1 + leverage lam φ j) := by
  induction m with
  | zero => simp [det_gram_zero]
  | succ m ih => rw [det_gram_succ hlam, ih, Finset.prod_Icc_succ_top (by omega), mul_assoc]

theorem leverage_nonneg {lam : ℝ} (hlam : 0 < lam) (φ : ℕ → Fin d → ℝ) (j : ℕ) :
    0 ≤ leverage lam φ j := by
  simpa [leverage] using
    (gram_posDef hlam φ (j - 1)).inv.posSemidef.dotProduct_mulVec_nonneg (φ j)

/-- The ratio `det M_m / det M_0` is the product of the factors `1 + φ_jᵀ M_{j-1}⁻¹ φ_j`. -/
theorem det_ratio_eq_prod {lam : ℝ} (hlam : 0 < lam) (φ : ℕ → Fin d → ℝ) (m : ℕ) :
    (gram lam φ m).det / (gram lam φ 0).det = ∏ j ∈ Icc 1 m, (1 + leverage lam φ j) := by
  rw [det_gram_eq_prod hlam, det_gram_zero, mul_div_cancel_left₀ _ (by positivity)]

/-- `lem:explicit-gls-token-envelope`:
`log₂ (det M_m / det M_0) = ∑_{j=1}^{m} log₂ (1 + φ_jᵀ M_{j-1}⁻¹ φ_j)`. -/
theorem logb_det_ratio_eq_sum {lam : ℝ} (hlam : 0 < lam) (φ : ℕ → Fin d → ℝ) (m : ℕ) :
    Real.logb 2 ((gram lam φ m).det / (gram lam φ 0).det) =
      ∑ j ∈ Icc 1 m, Real.logb 2 (1 + leverage lam φ j) := by
  rw [det_ratio_eq_prod hlam, Real.logb_prod]
  intro j _
  have := leverage_nonneg hlam φ j
  positivity

/-! ### The trace–determinant inequality -/

/-- Unweighted AM–GM: `∏ z_i ≤ ((∑ z_i) / n)^n` for nonnegative `z_i`, `n = #s`. -/
theorem prod_le_mean_pow {ι : Type*} (s : Finset ι) (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ≤ ((∑ i ∈ s, z i) / s.card) ^ s.card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := Real.geom_mean_le_arith_mean s (fun _ => 1) z (fun _ _ => zero_le_one)
    (by simpa using hcard) hz
  simp only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at h
  have hP : 0 ≤ ∏ i ∈ s, z i := Finset.prod_nonneg hz
  calc ∏ i ∈ s, z i = ((∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹)) ^ s.card := by
        rw [Real.rpow_inv_natCast_pow hP hs.card_pos.ne']
    _ ≤ ((∑ i ∈ s, z i) / s.card) ^ s.card :=
        pow_le_pow_left₀ (Real.rpow_nonneg hP _) h _

/-- `lem:explicit-gls-token-envelope` (trace–determinant inequality): `det A ≤ (tr A / n)^n` for a
positive semidefinite `n × n` matrix. -/
theorem det_le_trace_div_pow {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : A.det ≤ (A.trace / Fintype.card n) ^ Fintype.card n := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  simpa using prod_le_mean_pow Finset.univ _ fun i _ => hA.eigenvalues_nonneg i

theorem trace_gram (lam : ℝ) (φ : ℕ → Fin d → ℝ) (m : ℕ) :
    (gram lam φ m).trace = d * lam + ∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i := by
  simp [gram, trace_sum, mul_comm]

/-- `det M_m / det M_0 ≤ (1 + ∑_{i ≤ m} ‖φ_i‖² / (dλ))^d`. -/
theorem det_ratio_le {lam : ℝ} (hlam : 0 < lam) (hd : 1 ≤ d) (φ : ℕ → Fin d → ℝ) (m : ℕ) :
    (gram lam φ m).det / (gram lam φ 0).det ≤
      (1 + (∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i) / (d * lam)) ^ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have h := det_le_trace_div_pow (gram_posDef hlam φ m).posSemidef
  rw [trace_gram, Fintype.card_fin] at h
  rw [det_gram_zero, div_le_iff₀ (by positivity)]
  calc (gram lam φ m).det ≤ ((d * lam + ∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i) / d) ^ d := h
    _ = (1 + (∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i) / (d * lam)) ^ d * lam ^ d := by
        rw [← mul_pow]
        congr 1
        field_simp

/-- `lem:explicit-gls-token-envelope`:
`log₂ (det M_m / det M_0) ≤ d log₂ (1 + ∑ ‖φ_i‖² / (dλ)) ≤ d log₂ (1 + m R² / (dλ))` when
`‖φ_i‖ ≤ R`. -/
theorem logb_det_ratio_le {lam : ℝ} (hlam : 0 < lam) (hd : 1 ≤ d) (φ : ℕ → Fin d → ℝ) (m : ℕ)
    (R : ℝ) (hφ : ∀ i ∈ Icc 1 m, φ i ⬝ᵥ φ i ≤ R ^ 2) :
    Real.logb 2 ((gram lam φ m).det / (gram lam φ 0).det) ≤
        d * Real.logb 2 (1 + (∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i) / (d * lam)) ∧
      d * Real.logb 2 (1 + (∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i) / (d * lam)) ≤
        d * Real.logb 2 (1 + m * R ^ 2 / (d * lam)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hS0 : 0 ≤ ∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i :=
    Finset.sum_nonneg fun i _ => by simpa using dotProduct_star_self_nonneg (φ i)
  have hS : ∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i ≤ m * R ^ 2 := by
    calc ∑ i ∈ Icc 1 m, φ i ⬝ᵥ φ i ≤ ∑ _i ∈ Icc 1 m, R ^ 2 := Finset.sum_le_sum hφ
      _ = m * R ^ 2 := by simp
  have hpos : 0 < (gram lam φ m).det / (gram lam φ 0).det := by
    rw [det_ratio_eq_prod hlam]
    exact Finset.prod_pos fun j _ => by have := leverage_nonneg hlam φ j; positivity
  refine ⟨?_, ?_⟩
  · rw [← Real.logb_pow]
    exact Real.logb_le_logb_of_le (by norm_num) hpos (det_ratio_le hlam hd φ m)
  · gcongr
    norm_num

/-- `lem:explicit-gls-token-envelope` (elliptical potential): if `m ≥ 1` and every leverage
`φ_jᵀ M_{j-1}⁻¹ φ_j`, `1 ≤ j ≤ m`, exceeds one, then `m < d log₂ (1 + m R² / (dλ))`. -/
theorem lt_of_leverage_gt_one {lam : ℝ} (hlam : 0 < lam) (hd : 1 ≤ d) (φ : ℕ → Fin d → ℝ)
    (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hφ : ∀ i ∈ Icc 1 m, φ i ⬝ᵥ φ i ≤ R ^ 2)
    (hlev : ∀ j ∈ Icc 1 m, 1 < leverage lam φ j) :
    (m : ℝ) < d * Real.logb 2 (1 + m * R ^ 2 / (d * lam)) := by
  have h2 : (2 : ℝ) ^ m < (gram lam φ m).det / (gram lam φ 0).det := by
    rw [det_ratio_eq_prod hlam]
    calc (2 : ℝ) ^ m = ∏ _j ∈ Icc 1 m, (2 : ℝ) := by simp
      _ < ∏ j ∈ Icc 1 m, (1 + leverage lam φ j) :=
        Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => by norm_num)
          (fun j hj => by linarith [hlev j hj]) ⟨1, by simp [hm]⟩
  have hlog : (m : ℝ) < Real.logb 2 ((gram lam φ m).det / (gram lam φ 0).det) := by
    have := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h2
    simpa [Real.logb_pow] using this
  obtain ⟨h1, h2⟩ := logb_det_ratio_le hlam hd φ m R hφ
  linarith

/-! ### Cauchy–Schwarz in the `M` inner product -/

/-- `lem:explicit-gls-token-envelope` (Cauchy–Schwarz in the `A` inner product): for positive
definite `A`, `⟨v, φ⟩² ≤ (vᵀ A v)(φᵀ A⁻¹ φ)`. -/
theorem dotProduct_sq_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosDef) (v φ : n → ℝ) :
    (v ⬝ᵥ φ) ^ 2 ≤ (v ⬝ᵥ (A *ᵥ v)) * (φ ⬝ᵥ (A⁻¹ *ᵥ φ)) := by
  have h := hA.star_dotProduct_mulVec_mul_le v (A⁻¹ *ᵥ φ)
  have hu : A *ᵥ (A⁻¹ *ᵥ φ) = φ := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
  simp only [star_trivial, hu] at h
  rw [dotProduct_comm (A⁻¹ *ᵥ φ) φ] at h
  nlinarith [h]

end LowLogitRank.Witness
