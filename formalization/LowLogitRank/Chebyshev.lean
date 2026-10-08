import LowLogitRank.Basic

/-!
# Chebyshev approximation of functions analytic on a Bernstein ellipse

This file proves `ChebyshevApprox`, the analytic core of `lem:softclip-poly` and
`lem:poly-sigmoid`. For `f` differentiable and bounded by `M` on the closed Bernstein ellipse
`{(w + w⁻¹)/2 : ρ⁻¹ ≤ ‖w‖ ≤ ρ}`:

* the coefficients `c_n = (2π)⁻¹ ∫_0^{2π} f(cos θ) e^{-inθ} dθ` satisfy `‖c_n‖ ≤ M ρ^{-|n|}`
  (Cauchy's estimate, by moving the contour of `∮ G(w) w^{-n-1} dw`, `G(w) = f((w + w⁻¹)/2)`,
  to `|w| = ρ` or `|w| = ρ⁻¹`);
* `f(cos θ) = ∑_n c_n e^{inθ}` (the Fourier series of a continuous function with summable
  coefficients); with `c_{-n} = c_n` this gives the Chebyshev series
  `f(x) = c_0 + 2 ∑_{j ≥ 1} c_j T_j(x)` on `[-1, 1]`;
* the degree-`k` partial sum of the real parts is within `2 M ρ^{-k} / (ρ - 1)` of `Re f`.

The symmetry `c_{-n} = c_n` comes from the substitution `θ ↦ 2π - θ`.
-/

namespace LowLogitRank.Chebyshev

open Complex Set Metric Polynomial Filter
open scoped Real

/-- The hypothesis of `ChebyshevApprox`: `f` is complex differentiable and bounded by `M` at
every point `(w + w⁻¹)/2` with `ρ⁻¹ ≤ ‖w‖ ≤ ρ`, i.e. on the closed Bernstein ellipse of
parameter `ρ`. -/
def BernsteinHyp (f : ℂ → ℂ) (ρ M : ℝ) : Prop :=
  ∀ w : ℂ, ρ⁻¹ ≤ ‖w‖ → ‖w‖ ≤ ρ →
    DifferentiableAt ℂ f ((w + w⁻¹) / 2) ∧ ‖f ((w + w⁻¹) / 2)‖ ≤ M

/-- The Joukowski pullback `G(w) = f((w + w⁻¹)/2)`. -/
noncomputable def pullback (f : ℂ → ℂ) (w : ℂ) : ℂ := f ((w + w⁻¹) / 2)

variable {f : ℂ → ℂ} {ρ M : ℝ}

theorem ne_zero_of_inv_le_norm (hρ : 1 < ρ) {w : ℂ} (h : ρ⁻¹ ≤ ‖w‖) : w ≠ 0 := by
  rintro rfl
  rw [norm_zero] at h
  have : 0 < ρ⁻¹ := inv_pos.mpr (by linarith)
  linarith

theorem bound_nonneg (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) : 0 ≤ M := by
  have h := (hf 1 (by simpa using (inv_le_one₀ (by linarith)).mpr hρ.le) (by simpa using hρ.le)).2
  exact (norm_nonneg _).trans h

theorem pullback_differentiableAt (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) {w : ℂ}
    (h1 : ρ⁻¹ ≤ ‖w‖) (h2 : ‖w‖ ≤ ρ) : DifferentiableAt ℂ (pullback f) w := by
  have hw := ne_zero_of_inv_le_norm hρ h1
  have : DifferentiableAt ℂ (fun z : ℂ => (z + z⁻¹) / 2) w :=
    (differentiableAt_id.add (differentiableAt_inv hw)).div_const 2
  exact (hf w h1 h2).1.comp w this

theorem norm_pullback_le (hf : BernsteinHyp f ρ M) {w : ℂ} (h1 : ρ⁻¹ ≤ ‖w‖) (h2 : ‖w‖ ≤ ρ) :
    ‖pullback f w‖ ≤ M :=
  (hf w h1 h2).2

/-- The integrand `w ↦ w^{-n} G(w)` used for the `n`-th Laurent coefficient. -/
noncomputable def laurentIntegrand (f : ℂ → ℂ) (n : ℤ) (w : ℂ) : ℂ := w ^ (-n) * pullback f w

theorem laurentIntegrand_differentiableAt (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (n : ℤ)
    {w : ℂ} (h1 : ρ⁻¹ ≤ ‖w‖) (h2 : ‖w‖ ≤ ρ) :
    DifferentiableAt ℂ (laurentIntegrand f n) w :=
  ((differentiableAt_zpow).mpr (Or.inl (ne_zero_of_inv_le_norm hρ h1))).mul
    (pullback_differentiableAt hf hρ h1 h2)

/-- Moving the contour inside the closed annulus `ρ⁻¹ ≤ ‖w‖ ≤ ρ`. -/
theorem circleIntegral_laurent_eq (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (n : ℤ) {a b : ℝ}
    (ha : ρ⁻¹ ≤ a) (hab : a ≤ b) (hb : b ≤ ρ) :
    (∮ z in C(0, b), (z - 0)⁻¹ • laurentIntegrand f n z) =
      ∮ z in C(0, a), (z - 0)⁻¹ • laurentIntegrand f n z := by
  have ha0 : 0 < a := lt_of_lt_of_le (inv_pos.mpr (by linarith)) ha
  refine circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable ha0 hab
    (s := ∅) countable_empty ?_ ?_
  · intro z hz
    simp only [Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt] at hz
    exact (laurentIntegrand_differentiableAt hf hρ n (ha.trans hz.2) (hz.1.trans hb)
      ).continuousAt.continuousWithinAt
  · intro z hz
    simp only [Set.mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_le,
      mem_empty_iff_false, not_false_eq_true, and_true] at hz
    exact laurentIntegrand_differentiableAt hf hρ n (ha.trans hz.2.le) (hz.1.le.trans hb)

/-- The `n`-th Laurent coefficient `c_n = (2π)⁻¹ ∫_0^{2π} f(cos θ) e^{-inθ} dθ` of
`G(w) = f((w + w⁻¹)/2)` (`lem:softclip-poly`, `lem:poly-sigmoid`). -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℤ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, exp (-(n * θ * I)) * f (Real.cos θ)

theorem pullback_exp_mul_I (θ : ℝ) : pullback f (exp (θ * I)) = f (Real.cos θ) := by
  unfold pullback
  congr 1
  rw [← exp_neg, ofReal_cos, ← neg_mul, ← two_cos]
  ring

/-- The symmetry `c_{-n} = c_n` (`lem:softclip-poly`, `lem:poly-sigmoid`), from the substitution
`θ ↦ 2π - θ`. -/
theorem coeff_neg (f : ℂ → ℂ) (n : ℤ) : coeff f (-n) = coeff f n := by
  unfold coeff
  congr 1
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => exp (-(((-n : ℤ) : ℂ) * θ * I)) * f (Real.cos θ)) (a := 0) (b := 2 * π) (2 * π)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Real.cos_two_pi_sub]
  congr 1
  rw [show -(((-n : ℤ) : ℂ) * ((2 * π - θ : ℝ) : ℂ) * I) = -(n * θ * I) + n * (2 * π * I) by
    push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- On the unit circle, `∮ G(w) w^{-n-1} dw = 2πi c_n`. -/
theorem circleIntegral_laurent_one (n : ℤ) :
    (∮ z in C(0, 1), (z - 0)⁻¹ • laurentIntegrand f n z) = (2 * π * I) * coeff f n := by
  have key : ∀ θ : ℝ, deriv (circleMap 0 1) θ •
      ((circleMap 0 1 θ - 0)⁻¹ • laurentIntegrand f n (circleMap 0 1 θ)) =
      I * (exp (-(n * θ * I)) * f (Real.cos θ)) := by
    intro θ
    rw [deriv_circleMap, circleMap_zero, ofReal_one, one_mul, sub_zero, smul_eq_mul,
      smul_eq_mul, laurentIntegrand, pullback_exp_mul_I, ← exp_int_mul, ← exp_neg]
    have h1 : exp (θ * I) * exp (-(θ * I)) = 1 := by rw [← exp_add]; simp
    have h2 : exp (((-n : ℤ) : ℂ) * (θ * I)) = exp (-(n * θ * I)) := by push_cast; ring_nf
    rw [h2]
    linear_combination (I * (exp (-(n * θ * I)) * f (Real.cos θ))) * h1
  simp only [circleIntegral]
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul, coeff]
  have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  field_simp

/-- Cauchy's estimate on the circle `|w| = R` inside the annulus: `‖c_n‖ ≤ M R^{-n}`. -/
theorem norm_coeff_le_zpow (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (n : ℤ) {R : ℝ}
    (h1 : ρ⁻¹ ≤ R) (h2 : R ≤ ρ) : ‖coeff f n‖ ≤ M * R ^ (-n) := by
  have hR0 : 0 < R := lt_of_lt_of_le (inv_pos.mpr (by linarith)) h1
  have hρ1 : ρ⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hρ.le
  have heq : (∮ z in C(0, R), (z - 0)⁻¹ • laurentIntegrand f n z) = (2 * π * I) * coeff f n := by
    rw [← circleIntegral_laurent_one]
    rcases le_total R 1 with hR | hR
    · exact (circleIntegral_laurent_eq hf hρ n h1 hR hρ.le).symm
    · exact circleIntegral_laurent_eq hf hρ n hρ1 hR h2
  have hbound := circleIntegral.norm_integral_le_of_norm_le_const (c := 0)
    (f := fun z => (z - 0)⁻¹ • laurentIntegrand f n z) (C := R⁻¹ * (R ^ (-n) * M)) hR0.le
    (by
      intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      rw [sub_zero, smul_eq_mul, laurentIntegrand, norm_mul, norm_mul, norm_inv, norm_zpow, hz]
      gcongr
      exact norm_pullback_le hf (hz ▸ h1) (hz ▸ h2))
  rw [heq, norm_mul] at hbound
  have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_I, mul_one, norm_mul, norm_ofNat, norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2pi] at hbound
  have : 2 * π * R * (R⁻¹ * (R ^ (-n) * M)) = 2 * π * (M * R ^ (-n)) := by
    field_simp
  rw [this] at hbound
  exact le_of_mul_le_mul_left hbound (by positivity)

/-- Cauchy's coefficient estimate `‖c_n‖ ≤ M ρ^{-|n|}` (`lem:softclip-poly`,
`lem:poly-sigmoid`). -/
theorem norm_coeff_le (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (n : ℤ) :
    ‖coeff f n‖ ≤ M * ρ⁻¹ ^ n.natAbs := by
  have hρ' : ρ⁻¹ ≤ ρ := ((inv_le_one₀ (by linarith)).mpr hρ.le).trans hρ.le
  rcases le_total 0 n with hn | hn
  · have h := norm_coeff_le_zpow hf hρ n (R := ρ) hρ' le_rfl
    have e : ρ ^ (-n) = ρ⁻¹ ^ n.natAbs := by
      rw [zpow_neg, ← inv_zpow, ← zpow_natCast, Int.natAbs_of_nonneg hn]
    rwa [e] at h
  · have h := norm_coeff_le_zpow hf hρ n (R := ρ⁻¹) le_rfl hρ'
    have e : ρ⁻¹ ^ (-n) = ρ⁻¹ ^ n.natAbs := by
      rw [← zpow_natCast, Int.ofNat_natAbs_of_nonpos hn]
    rwa [e] at h

/-! ### The Fourier series of `θ ↦ f(cos θ)` -/

local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

theorem fourier_one_coe (θ : ℝ) : (fourier 1 (θ : AddCircle (2 * π)) : ℂ) = exp (θ * I) := by
  rw [fourier_coe_apply]
  congr 1
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp
  push_cast
  ring

theorem fourier_coe_two_pi (n : ℤ) (θ : ℝ) :
    (fourier n (θ : AddCircle (2 * π)) : ℂ) = exp (n * θ * I) := by
  rw [fourier_coe_apply]
  congr 1
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp
  push_cast
  ring

/-- `θ ↦ f(cos θ)` as a continuous function on `ℝ / 2πℤ`, written as `G(e^{iθ})`. -/
noncomputable def circleFun (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) :
    C(AddCircle (2 * π), ℂ) where
  toFun x := pullback f (fourier 1 x)
  continuous_toFun := by
    have hρ1 : ρ⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hρ.le
    have hc : ContinuousOn (pullback f) (sphere 0 1) := fun w hw => by
      rw [mem_sphere_zero_iff_norm] at hw
      exact (pullback_differentiableAt hf hρ (hw ▸ hρ1) (hw ▸ hρ.le)).continuousAt
        |>.continuousWithinAt
    exact hc.comp_continuous (fourier 1).continuous fun x => by
      rw [mem_sphere_zero_iff_norm]
      exact Circle.norm_coe _

theorem circleFun_coe (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (θ : ℝ) :
    circleFun hf hρ (θ : AddCircle (2 * π)) = f (Real.cos θ) := by
  change pullback f (fourier 1 (θ : AddCircle (2 * π))) = _
  rw [fourier_one_coe, pullback_exp_mul_I]

theorem fourierCoeff_circleFun (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (n : ℤ) :
    fourierCoeff (circleFun hf hρ) n = coeff f n := by
  rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add, coeff, real_smul]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [smul_eq_mul, circleFun_coe, fourier_coe_two_pi]
    push_cast
    ring_nf

theorem summable_bound (hρ : 1 < ρ) (M : ℝ) : Summable fun n : ℤ => M * ρ⁻¹ ^ n.natAbs := by
  have h0 : 0 ≤ ρ⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  have hg := (summable_geometric_of_lt_one h0 h1).mul_left M
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hg
  · refine ((summable_nat_add_iff 1).mpr hg).congr fun n => ?_
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this]

theorem summable_coeff (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) : Summable (coeff f) :=
  (summable_bound hρ M).of_norm_bounded (norm_coeff_le hf hρ)

/-- The Fourier expansion `f(cos θ) = ∑_{n ∈ ℤ} c_n e^{inθ}` (`lem:softclip-poly`,
`lem:poly-sigmoid`). -/
theorem hasSum_coeff_exp (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (θ : ℝ) :
    HasSum (fun n : ℤ => coeff f n * exp (n * θ * I)) (f (Real.cos θ)) := by
  have he : fourierCoeff (circleFun hf hρ) = coeff f := funext (fourierCoeff_circleFun hf hρ)
  have hs : Summable (fourierCoeff (circleFun hf hρ)) := he ▸ summable_coeff hf hρ
  have h := has_pointwise_sum_fourier_series_of_summable hs (θ : AddCircle (2 * π))
  simpa only [fourierCoeff_circleFun, circleFun_coe, smul_eq_mul, fourier_coe_two_pi] using h

/-! ### The Chebyshev series on `[-1, 1]` -/

/-- The Chebyshev coefficients of `c_0 + 2 ∑_{j ≥ 1} c_j T_j`: `b_0 = c_0` and `b_j = 2 c_j`
for `j ≥ 1`. -/
noncomputable def chebCoeff (f : ℂ → ℂ) (j : ℕ) : ℂ :=
  if j = 0 then coeff f 0 else 2 * coeff f j

/-- `‖b_j‖ ≤ 2 M ρ^{-j}` (`lem:softclip-poly`, `lem:poly-sigmoid`). -/
theorem norm_chebCoeff_le (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (j : ℕ) :
    ‖chebCoeff f j‖ ≤ 2 * M * ρ⁻¹ ^ j := by
  have hM := bound_nonneg hf hρ
  have h := norm_coeff_le hf hρ j
  rw [Int.natAbs_natCast] at h
  unfold chebCoeff
  split_ifs with hj
  · subst hj
    simp only [Nat.cast_zero, pow_zero, mul_one] at h ⊢
    linarith
  · rw [norm_mul, norm_ofNat, mul_assoc]
    gcongr

/-- The cosine series `f(cos θ) = c_0 + 2 ∑_{j ≥ 1} c_j cos(jθ)`, from the Fourier expansion
and `c_{-j} = c_j`. -/
theorem hasSum_chebCoeff_cos (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (θ : ℝ) :
    HasSum (fun j : ℕ => chebCoeff f j * (Real.cos (j * θ) : ℂ)) (f (Real.cos θ)) := by
  have h1 := ((hasSum_coeff_exp hf hρ θ).nat_add_neg).sub (hasSum_ite_eq 0 (coeff f 0))
  convert h1 using 1
  · funext j
    have e1 : exp (((j : ℤ) : ℂ) * (θ : ℂ) * I) = exp (j * θ * I) := by push_cast; ring_nf
    have e2 : exp (((-(j : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I) = exp (-(j * θ * I)) := by
      push_cast; ring_nf
    have hcos : (Real.cos (j * θ) : ℂ) = (exp (j * θ * I) + exp (-(j * θ * I))) / 2 := by
      rw [ofReal_cos, ← neg_mul, ← two_cos]
      push_cast
      ring
    rw [e1, e2, hcos, chebCoeff, coeff_neg]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · simp only [hj.ne', ↓reduceIte]
      ring
  · simp

/-- The Chebyshev series `f(x) = c_0 + 2 ∑_{j ≥ 1} c_j T_j(x)` on `[-1, 1]` (`lem:softclip-poly`,
`lem:poly-sigmoid`). -/
theorem hasSum_chebCoeff_T (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun j : ℕ => chebCoeff f j * (((Chebyshev.T ℝ j).eval x : ℝ) : ℂ)) (f x) := by
  have h := hasSum_chebCoeff_cos hf hρ (Real.arccos x)
  rw [Real.cos_arccos hx.1 hx.2] at h
  convert h using 3 with j
  rw [← Real.cos_arccos hx.1 hx.2, Chebyshev.T_real_cos, Real.cos_arccos hx.1 hx.2]
  push_cast
  ring_nf

/-! ### Truncation -/

/-- Tail bound for a real series dominated by `B r^j`: the partial sum up to degree `k` is within
`B r^{k+1} / (1 - r)` of the sum. -/
theorem abs_sum_range_sub_le {u : ℕ → ℝ} {s B r : ℝ} (hs : HasSum u s) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hu : ∀ j, |u j| ≤ B * r ^ j) (k : ℕ) :
    |∑ j ∈ Finset.range (k + 1), u j - s| ≤ B * r ^ (k + 1) / (1 - r) := by
  have htail := (hasSum_nat_add_iff' (k + 1)).mpr hs
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (B * r ^ (k + 1))
  have h := htail.norm_le_of_bounded hg fun j => by
    rw [Real.norm_eq_abs]
    calc |u (j + (k + 1))| ≤ B * r ^ (j + (k + 1)) := hu _
      _ = B * r ^ (k + 1) * r ^ j := by ring
  rw [Real.norm_eq_abs, abs_sub_comm] at h
  rwa [div_eq_mul_inv]

theorem abs_eval_T_le_one (j : ℤ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(Chebyshev.T ℝ j).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- The degree-`k` Chebyshev partial sum `∑_{j ≤ k} Re(b_j) T_j` of the real parts. -/
noncomputable def chebPartial (f : ℂ → ℂ) (k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (k + 1), Polynomial.C (chebCoeff f j).re * Chebyshev.T ℝ j

theorem natDegree_chebPartial_le (f : ℂ → ℂ) (k : ℕ) : (chebPartial f k).natDegree ≤ k := by
  unfold chebPartial
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [Chebyshev.natDegree_T, Int.natAbs_natCast]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

theorem eval_chebPartial (f : ℂ → ℂ) (k : ℕ) (x : ℝ) :
    (chebPartial f k).eval x =
      ∑ j ∈ Finset.range (k + 1), (chebCoeff f j).re * (Chebyshev.T ℝ j).eval x := by
  simp [chebPartial, Polynomial.eval_finsetSum]

/-- The truncation bound `|q(x) - Re f(x)| ≤ 2 M ∑_{j > k} ρ^{-j} = 2 M ρ^{-k} / (ρ - 1)` on
`[-1, 1]` for the degree-`k` Chebyshev partial sum (`lem:softclip-poly`,
`lem:poly-sigmoid`). -/
theorem abs_eval_chebPartial_sub_le (hf : BernsteinHyp f ρ M) (hρ : 1 < ρ) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(chebPartial f k).eval x - (f x).re| ≤ 2 * M * ρ⁻¹ ^ k / (ρ - 1) := by
  have hre := Complex.hasSum_re (hasSum_chebCoeff_T hf hρ hx)
  simp only [re_mul_ofReal] at hre
  have hρ0 : 0 < ρ := by linarith
  have h := abs_sum_range_sub_le hre (inv_nonneg.mpr hρ0.le) (inv_lt_one_of_one_lt₀ hρ)
    (B := 2 * M) (fun j => by
      rw [abs_mul]
      calc |(chebCoeff f j).re| * |(Chebyshev.T ℝ j).eval x|
          ≤ ‖chebCoeff f j‖ * 1 :=
            mul_le_mul (abs_re_le_norm _) (abs_eval_T_le_one j hx) (abs_nonneg _) (norm_nonneg _)
        _ ≤ 2 * M * ρ⁻¹ ^ j := by rw [mul_one]; exact norm_chebCoeff_le hf hρ j) k
  rw [eval_chebPartial]
  convert h using 1
  have h1 : ρ - 1 ≠ 0 := by linarith
  have h2 : ρ ≠ 0 := hρ0.ne'
  simp only [inv_pow]
  field_simp
  ring

/-- `lem:softclip-poly`, `lem:poly-sigmoid` (analytic core): if `f` is differentiable and bounded
by `M` on the closed Bernstein ellipse `{(w + w⁻¹)/2 : ρ⁻¹ ≤ ‖w‖ ≤ ρ}`, `ρ > 1`, then for every
`k` some real polynomial of degree at most `k` is within `2 M ρ^{-k} / (ρ - 1)` of `Re f` on
`[-1, 1]`. The polynomial is the degree-`k` Chebyshev partial sum `chebPartial f k`. -/
theorem chebyshevApprox : ChebyshevApprox := fun _ _ _ hρ hf k =>
  ⟨chebPartial _ k, natDegree_chebPartial_le _ k,
    fun _ hx => abs_eval_chebPartial_sub_le hf hρ k hx⟩

end LowLogitRank.Chebyshev
