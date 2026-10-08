import LowLogitRank.Basic

/-!
# The final estimate of `lem:rational-spanner`

The rational SVD and the barycentric-spanner search are cited algorithms and are not formalized.
What is formalized is the deterministic estimate at the end of the proof: the residual of the
selected combination splits into `r + 1` pieces orthogonal to the retained basis, each of
Euclidean norm at most `‖(I - Π) M‖_op ≤ 2γ√n`, and `ℓ₁ ≤ √m ℓ₂` on `ℝ^m`.
-/

namespace LowLogitRank.Projection

open Finset

section Spanner

variable {ι : Type*} [Fintype ι]

/-- The `ℓ₁` norm on `ℝ^m`. -/
noncomputable def l1 (x : EuclideanSpace ℝ ι) : ℝ := ∑ i, |x i|

/-- `‖x‖₁ ≤ √m ‖x‖₂` on `ℝ^m`. -/
theorem l1_le_sqrt_card_mul_norm (x : EuclideanSpace ℝ ι) :
    l1 x ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ => (1 : ℝ)) (fun i => |x i|)
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, sq_abs] at h
  rw [EuclideanSpace.norm_eq]
  simpa [l1, Real.norm_eq_abs, sq_abs] using h

/-- The residual of a combination whose projections agree splits into projected-out pieces: if
`P v = ∑_j c_j P w_j`, then `v - ∑_j c_j w_j = (v - P v) - ∑_j c_j (w_j - P w_j)`. -/
theorem residual_split {E : Type*} [AddCommGroup E] [Module ℝ E] (P : E →ₗ[ℝ] E) {r : ℕ}
    (v : E) (w : Fin r → E) (c : Fin r → ℝ) (h : P v = ∑ j, c j • P (w j)) :
    v - ∑ j, c j • w j = (v - P v) - ∑ j, c j • (w j - P (w j)) := by
  simp only [smul_sub, sum_sub_distrib, ← h]
  abel

/-- If `Π = Q ∘ L` and `L v = ∑_j c_j L w_j` (here `L = Uᵀ` and `z_i = Uᵀ v_i`), then
`Π v = ∑_j c_j Π w_j`. -/
theorem proj_combination {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (L : E →ₗ[ℝ] F) (Q : F →ₗ[ℝ] E) {r : ℕ} (v : E) (w : Fin r → E)
    (c : Fin r → ℝ) (h : L v = ∑ j, c j • L (w j)) :
    (Q ∘ₗ L) v = ∑ j, c j • (Q ∘ₗ L) (w j) := by
  simp [h, map_sum, map_smul]

/-- Triangle inequality over the `r + 1` residual pieces, coefficients at most `3/2`. -/
theorem norm_residual_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ}
    (e₀ : E) (e : Fin r → E) (c : Fin r → ℝ) {ε : ℝ} (h0 : ‖e₀‖ ≤ ε) (he : ∀ j, ‖e j‖ ≤ ε)
    (hc : ∀ j, |c j| ≤ 3 / 2) : ‖e₀ - ∑ j, c j • e j‖ ≤ (1 + 3 * r / 2) * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans h0
  calc ‖e₀ - ∑ j, c j • e j‖ ≤ ‖e₀‖ + ‖∑ j, c j • e j‖ := norm_sub_le _ _
    _ ≤ ‖e₀‖ + ∑ j, ‖c j • e j‖ := by gcongr; exact norm_sum_le _ _
    _ ≤ ε + ∑ _j : Fin r, 3 / 2 * ε := by
        gcongr with j
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hc j) (he j) (norm_nonneg _) (by norm_num)
    _ = (1 + 3 * r / 2) * ε := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- A column of a matrix has Euclidean norm at most the operator norm: `‖(I - Π) v_k‖₂ ≤
‖(I - Π) M‖_op` when `(I - Π) M` sends the `k`-th unit vector to `(I - Π) v_k`. -/
theorem norm_column_le_opNorm {κ : Type*} [Fintype κ] [DecidableEq κ]
    (N : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι) (k : κ) :
    ‖N (EuclideanSpace.single k 1)‖ ≤ ‖N‖ := by
  have := N.le_opNorm (EuclideanSpace.single k 1)
  rwa [PiLp.norm_single, norm_one, mul_one] at this

/-- `lem:rational-spanner`, final estimate. Let `Π` be a linear map on `ℝ^m` with
`Π v_i = ∑_j c_j Π v_{i_j}`, `|c_j| ≤ 3/2`, `r ≤ s`, `s ≥ 1`, `γ ≥ 0`, and let every residual
`v - Π v` among the `r + 1` vectors have Euclidean norm at most `2γ√n`. Then
`‖v_i - ∑_j c_j v_{i_j}‖₁ ≤ √m (1 + 3r/2) · 2γ√n ≤ 6γs√(nm)`. -/
theorem spanner_l1_bound {r s n : ℕ} (P : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (v : EuclideanSpace ℝ ι) (w : Fin r → EuclideanSpace ℝ ι) (c : Fin r → ℝ)
    (hP : P v = ∑ j, c j • P (w j)) {γ : ℝ} (hγ : 0 ≤ γ)
    (h0 : ‖v - P v‖ ≤ 2 * γ * Real.sqrt n) (hw : ∀ j, ‖w j - P (w j)‖ ≤ 2 * γ * Real.sqrt n)
    (hc : ∀ j, |c j| ≤ 3 / 2) (hrs : r ≤ s) (hs : 1 ≤ s) :
    l1 (v - ∑ j, c j • w j) ≤
        Real.sqrt (Fintype.card ι) * (1 + 3 * r / 2) * (2 * γ * Real.sqrt n) ∧
      Real.sqrt (Fintype.card ι) * (1 + 3 * r / 2) * (2 * γ * Real.sqrt n) ≤
        6 * γ * s * Real.sqrt (n * Fintype.card ι) := by
  constructor
  · rw [residual_split P v w c hP, mul_assoc]
    refine (l1_le_sqrt_card_mul_norm _).trans ?_
    gcongr
    exact norm_residual_le _ _ c h0 hw hc
  · have hr : (r : ℝ) ≤ s := by exact_mod_cast hrs
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    have hm := Real.sqrt_nonneg (Fintype.card ι : ℝ)
    have hn := Real.sqrt_nonneg (n : ℝ)
    have key : (1 + 3 * (r : ℝ) / 2) * 2 ≤ 6 * s := by linarith
    have := mul_le_mul_of_nonneg_right key (mul_nonneg (mul_nonneg hγ hn) hm)
    nlinarith

/-- The chain of `lem:rational-spanner` actually gives the constant `5`:
`√m (1 + 3r/2) · 2γ√n ≤ 5γs√(nm)` for `r ≤ s`, `s ≥ 1`. -/
theorem spanner_const_five {r s n m : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) (hrs : r ≤ s) (hs : 1 ≤ s) :
    Real.sqrt m * (1 + 3 * r / 2) * (2 * γ * Real.sqrt n) ≤ 5 * γ * s * Real.sqrt (n * m) := by
  have hr : (r : ℝ) ≤ s := by exact_mod_cast hrs
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  have hm := Real.sqrt_nonneg (m : ℝ)
  have hn := Real.sqrt_nonneg (n : ℝ)
  have key : (1 + 3 * (r : ℝ) / 2) * 2 ≤ 5 * s := by linarith
  have := mul_le_mul_of_nonneg_right key (mul_nonneg (mul_nonneg hγ hn) hm)
  nlinarith

/-- Remark after `lem:rational-spanner`: running the spanner with residual `γ/2` turns the bound
`6γ's√(nm)` into the published `3γs√(nm)`. -/
theorem spanner_half_gamma (γ s n m : ℝ) :
    6 * (γ / 2) * s * Real.sqrt (n * m) = 3 * γ * s * Real.sqrt (n * m) := by ring

/-- `lem:rational-spanner`, the count `r ≤ s`: if `a_j ≤ 2σ_j`, `a_j ≥ 0`, and `σ_j ≤ γ√n` for
every index `j > s`, then every index with `a_j² > 4γ²n` is at most `s`; if moreover `a` is
nonincreasing, these indices form an initial segment. -/
theorem retained_le {a σ : ℕ → ℝ} {s n : ℕ} {γ : ℝ} (ha0 : ∀ j, 0 ≤ a j)
    (ha : ∀ j, a j ≤ 2 * σ j) (hσ : ∀ j, s < j → σ j ≤ γ * Real.sqrt n) :
    (∀ j, 4 * γ ^ 2 * n < a j ^ 2 → j ≤ s) ∧
      (Antitone a → ∀ i j, i ≤ j → 4 * γ ^ 2 * n < a j ^ 2 → 4 * γ ^ 2 * n < a i ^ 2) := by
  constructor
  · intro j hj
    by_contra hcon
    rw [not_le] at hcon
    have h1 : a j ≤ 2 * (γ * Real.sqrt n) := (ha j).trans (by linarith [hσ j hcon])
    have h2 : a j ^ 2 ≤ (2 * (γ * Real.sqrt n)) ^ 2 := pow_le_pow_left₀ (ha0 j) h1 2
    have h3 : (2 * (γ * Real.sqrt n)) ^ 2 = 4 * γ ^ 2 * n := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; ring
    linarith
  · intro hanti i j hij hj
    have := hanti hij
    nlinarith [ha0 j]

end Spanner

end LowLogitRank.Projection
