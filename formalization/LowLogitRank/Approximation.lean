import LowLogitRank.Basic

/-!
# Polynomial approximation of the smoothed logit and of the sigmoid

This file proves `lem:softclip-poly` (`sec:fixed-rank`) and `lem:poly-sigmoid` with the affine
correction `eq:affine-correction` (`sec:probability-route`). Both are derived from the
Bernstein-ellipse approximation theorem, which enters as the hypothesis `H : ChebyshevApprox`
(see `Basic.lean`).

The common step is `strip_approx`: a function analytic and bounded by `M` on the strip
`|Im u| < 1/2` is approximated on `[-T, T]` to accuracy `ε` by a real polynomial of degree
`⌈3T log(4TM/ε)⌉`. It uses the ellipse parameter `ρ = 1 + 1/(2T)`.
-/

namespace LowLogitRank.Approximation

open Complex Polynomial

/-! ### The Bernstein ellipse with parameter `ρ = 1 + 1/(2T)` -/

/-- The ellipse parameter `ρ = 1 + 1/(2T)`. -/
noncomputable def rho (T : ℝ) : ℝ := 1 + 1 / (2 * T)

theorem one_lt_rho {T : ℝ} (hT : 0 < T) : 1 < rho T := by
  have : 0 < 1 / (2 * T) := by positivity
  unfold rho; linarith

theorem rho_sub_one (T : ℝ) : rho T - 1 = 1 / (2 * T) := by
  unfold rho; ring

/-- On the closed Bernstein ellipse, `z = (w + w⁻¹)/2` with `ρ⁻¹ ≤ ‖w‖ ≤ ρ`, the imaginary part
satisfies `|Im z| ≤ (ρ - ρ⁻¹)/2`. -/
theorem abs_im_joukowski_le {ρ : ℝ} {w : ℂ} (hρ : 1 ≤ ρ) (h1 : ρ⁻¹ ≤ ‖w‖) (h2 : ‖w‖ ≤ ρ) :
    |((w + w⁻¹) / 2).im| ≤ (ρ - ρ⁻¹) / 2 := by
  set s := ‖w‖ with hs_def
  have hρ0 : 0 < ρ := by linarith
  have hρi : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
  have hs : 0 < s := lt_of_lt_of_le (inv_pos.mpr hρ0) h1
  have hn : normSq w = s ^ 2 := (Complex.sq_norm w).symm
  have him : ((w + w⁻¹) / 2).im = w.im * (s ^ 2 - 1) / s ^ 2 / 2 := by
    simp only [Complex.div_ofNat_im, Complex.add_im, Complex.inv_im, hn]
    field_simp
    ring
  have hwi : |w.im| ≤ s := Complex.abs_im_le_norm w
  -- `|s² - 1| ≤ s (ρ - ρ⁻¹)` for `ρ⁻¹ ≤ s ≤ ρ`
  have hup : (s - ρ) * (s + ρ⁻¹) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hlo : 0 ≤ (s - ρ⁻¹) * (s + ρ) := mul_nonneg (by linarith) (by positivity)
  have hsq : |s ^ 2 - 1| ≤ s * (ρ - ρ⁻¹) := by
    rw [abs_le]; constructor <;> nlinarith
  have key : |w.im * (s ^ 2 - 1)| ≤ s ^ 2 * (ρ - ρ⁻¹) := by
    rw [abs_mul]
    calc |w.im| * |s ^ 2 - 1| ≤ s * (s * (ρ - ρ⁻¹)) :=
          mul_le_mul hwi hsq (abs_nonneg _) hs.le
      _ = s ^ 2 * (ρ - ρ⁻¹) := by ring
  rw [him, abs_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < s ^ 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- With `ρ = 1 + 1/(2T)` one has `T (ρ - ρ⁻¹)/2 < 1/2`. -/
theorem half_T_rho_sub_inv_lt {T : ℝ} (hT : 0 < T) : T * (rho T - (rho T)⁻¹) / 2 < 1 / 2 := by
  have hρ : 0 < rho T := by linarith [one_lt_rho hT]
  have h2 : rho T * (2 * T) = 2 * T + 1 := by unfold rho; field_simp
  have hinv : (rho T)⁻¹ = 2 * T / (2 * T + 1) := by
    rw [← h2]; field_simp
  rw [hinv]
  unfold rho
  rw [div_lt_div_iff_of_pos_right (by norm_num), ← sub_pos]
  field_simp
  ring_nf
  positivity

/-- Every point `z` of the closed Bernstein ellipse with `ρ = 1 + 1/(2T)` satisfies
`|Im (T z)| ≤ T (ρ - ρ⁻¹)/2 < 1/2`. -/
theorem abs_im_T_joukowski_lt {T : ℝ} (hT : 0 < T) {w : ℂ} (h1 : (rho T)⁻¹ ≤ ‖w‖)
    (h2 : ‖w‖ ≤ rho T) :
    |((T : ℂ) * ((w + w⁻¹) / 2)).im| ≤ T * (rho T - (rho T)⁻¹) / 2 ∧
      |((T : ℂ) * ((w + w⁻¹) / 2)).im| < 1 / 2 := by
  have hle : |((T : ℂ) * ((w + w⁻¹) / 2)).im| ≤ T * (rho T - (rho T)⁻¹) / 2 := by
    rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hT, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_im_joukowski_le (one_lt_rho hT).le h1 h2) hT.le
  exact ⟨hle, hle.trans_lt (half_T_rho_sub_inv_lt hT)⟩

/-- `log ρ ≥ 1/(3T)` for `ρ = 1 + 1/(2T)` and `T ≥ 1`. -/
theorem log_rho_ge {T : ℝ} (hT : 1 ≤ T) : 1 / (3 * T) ≤ Real.log (rho T) := by
  have hT0 : 0 < T := by linarith
  have hρ : 0 < rho T := by linarith [one_lt_rho hT0]
  refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hρ)
  have h2 : rho T * (2 * T) = 2 * T + 1 := by unfold rho; field_simp
  have hinv : (rho T)⁻¹ = 2 * T / (2 * T + 1) := by
    rw [← h2]; field_simp
  rw [hinv, div_le_iff₀ (by positivity)]
  field_simp
  linarith

/-- The geometric tail `∑_{j > k} ρ^{-j} = 2T ρ^{-k}` for `ρ = 1 + 1/(2T)`. -/
theorem tsum_tail_rho {T : ℝ} (hT : 0 < T) (k : ℕ) :
    ∑' j : ℕ, (rho T)⁻¹ ^ (k + 1 + j) = 2 * T * (rho T)⁻¹ ^ k := by
  have hρ := one_lt_rho hT
  have hρ0 : 0 < rho T := by linarith
  have hr0 : 0 ≤ (rho T)⁻¹ := (inv_pos.mpr hρ0).le
  have hr1 : (rho T)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  simp_rw [pow_add]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have h2 : rho T * (2 * T) = 2 * T + 1 := by unfold rho; field_simp
  have hinv : (rho T)⁻¹ = 2 * T / (2 * T + 1) := by
    rw [← h2]; field_simp
  rw [hinv]
  have h3 : (1 : ℝ) - 2 * T / (2 * T + 1) = 1 / (2 * T + 1) := by field_simp; ring
  rw [h3]
  field_simp

/-- The truncation bound of `ChebyshevApprox` at `ρ = 1 + 1/(2T)`:
`2 M ρ^{-k} / (ρ - 1) = 4 T M ρ^{-k}`. -/
theorem cheb_error_eq {T : ℝ} (hT : 0 < T) (M : ℝ) (k : ℕ) :
    2 * M * (rho T)⁻¹ ^ k / (rho T - 1) = 4 * T * M * (rho T)⁻¹ ^ k := by
  rw [rho_sub_one T]
  field_simp
  ring

/-- The same bound written as `2 M ∑_{j > k} ρ^{-j}`. -/
theorem cheb_error_eq_tsum {T : ℝ} (hT : 0 < T) (M : ℝ) (k : ℕ) :
    2 * M * ∑' j : ℕ, (rho T)⁻¹ ^ (k + 1 + j) = 4 * T * M * (rho T)⁻¹ ^ k := by
  rw [tsum_tail_rho hT]; ring

/-- The degree `k ≥ 3T log(A/ε)` makes `A ρ^{-k} ≤ ε` (here `A = 4TM`). -/
theorem error_le_of_degree {T A ε : ℝ} (hT : 1 ≤ T) (hA : 0 < A) (hε : 0 < ε) {k : ℕ}
    (hk : 3 * T * Real.log (A / ε) ≤ k) : A * (rho T)⁻¹ ^ k ≤ ε := by
  have hT0 : 0 < T := by linarith
  have hρ := one_lt_rho hT0
  have hρ0 : 0 < rho T := by linarith
  have hlogρ : 0 < Real.log (rho T) := Real.log_pos hρ
  have hlog := log_rho_ge hT
  -- `log (A/ε) ≤ k log ρ`
  have hk' : Real.log (A / ε) ≤ k * Real.log (rho T) := by
    have h1 : Real.log (A / ε) ≤ k / (3 * T) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc Real.log (A / ε) ≤ k / (3 * T) := h1
      _ = k * (1 / (3 * T)) := by ring
      _ ≤ k * Real.log (rho T) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
  have hpow : A / ε ≤ rho T ^ k := by
    calc A / ε = Real.exp (Real.log (A / ε)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (k * Real.log (rho T)) := Real.exp_le_exp.mpr hk'
      _ = rho T ^ k := by rw [Real.exp_nat_mul, Real.exp_log hρ0]
  rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hε] at hpow
  linarith

/-! ### Approximation of functions analytic on the strip `|Im u| < 1/2` -/

/-- The common step of `lem:softclip-poly` and `lem:poly-sigmoid`. If `f` is complex
differentiable with `‖f‖ ≤ M` on the strip `|Im u| < 1/2` and `Re f = g` on the reals, then
`ChebyshevApprox` applied to `F(z) = f(Tz)` with `ρ = 1 + 1/(2T)`, followed by the rescaling
`u = Tx`, gives a real polynomial of degree at most `⌈3T log(4TM/ε)⌉` that is within `ε` of `g`
on `[-T, T]`. -/
theorem strip_approx (H : ChebyshevApprox) (f : ℂ → ℂ) (g : ℝ → ℝ) {T M ε : ℝ}
    (hT : 1 ≤ T) (hM : 0 < M) (hε : 0 < ε)
    (hf : ∀ u : ℂ, |u.im| < 1 / 2 → DifferentiableAt ℂ f u ∧ ‖f u‖ ≤ M)
    (hfg : ∀ x : ℝ, (f x).re = g x) :
    ∃ r : Polynomial ℝ, r.natDegree ≤ ⌈3 * T * Real.log (4 * T * M / ε)⌉₊ ∧
      ∀ u ∈ Set.Icc (-T) T, |r.eval u - g u| ≤ ε := by
  have hT0 : 0 < T := by linarith
  set k := ⌈3 * T * Real.log (4 * T * M / ε)⌉₊ with hk_def
  obtain ⟨q, hqdeg, hq⟩ := H (fun z => f ((T : ℂ) * z)) (rho T) M (one_lt_rho hT0) (by
    intro w h1 h2
    obtain ⟨hd, hb⟩ := hf _ (abs_im_T_joukowski_lt hT0 h1 h2).2
    exact ⟨hd.comp _ (differentiableAt_id.const_mul (T : ℂ)), hb⟩) k
  refine ⟨q.comp (C T⁻¹ * X), ?_, ?_⟩
  · calc (q.comp (C T⁻¹ * X)).natDegree ≤ q.natDegree * (C T⁻¹ * X).natDegree :=
          natDegree_comp_le
      _ ≤ k * 1 := Nat.mul_le_mul hqdeg ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      _ = k := mul_one k
  · intro u hu
    have hx : T⁻¹ * u ∈ Set.Icc (-1 : ℝ) 1 := by
      obtain ⟨hu1, hu2⟩ := hu
      constructor
      · rw [← div_eq_inv_mul, le_div_iff₀ hT0]; linarith
      · rw [← div_eq_inv_mul, div_le_iff₀ hT0]; linarith
    have hb := hq _ hx
    have hfu : (f ((T : ℂ) * ((T⁻¹ * u : ℝ) : ℂ))).re = g u := by
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
      rw [show (T : ℂ) * ((T⁻¹ * u : ℝ) : ℂ) = ((u : ℝ) : ℂ) by
        push_cast; field_simp]
      exact hfg u
    rw [hfu] at hb
    simp only [eval_comp, eval_mul, eval_C, eval_X]
    calc |q.eval (T⁻¹ * u) - g u| ≤ 2 * M * (rho T)⁻¹ ^ k / (rho T - 1) := hb
      _ = 4 * T * M * (rho T)⁻¹ ^ k := cheb_error_eq hT0 M k
      _ ≤ ε := error_le_of_degree hT (by positivity) hε (Nat.le_ceil _)

/-! ### Elementary facts on the strip `|Im u| < 1/2` -/

theorem cos_one_le_cos {θ : ℝ} (h : |θ| ≤ 1) : Real.cos 1 ≤ Real.cos θ := by
  rw [← Real.cos_abs θ]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) (by linarith [Real.pi_gt_three]) h

theorem cos_pos_of_abs_lt_one {θ : ℝ} (h : |θ| < 1) : 0 < Real.cos θ := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩

theorem half_le_cos_one : 1 / 2 ≤ Real.cos 1 := by
  have := Real.one_sub_sq_div_two_le_cos (x := 1)
  norm_num at this ⊢
  linarith

theorem abs_two_mul_im_lt {u : ℂ} (hu : |u.im| < 1 / 2) : |2 * u.im| < 1 := by
  rw [abs_mul, abs_two]; linarith

/-- For complex `u` with `|Im u| < 1/2`, the number `w = e^{2u}` has argument `2 Im u ∈ (-1, 1)`. -/
theorem arg_exp_two_mul {u : ℂ} (hu : |u.im| < 1 / 2) : (cexp (2 * u)).arg = 2 * u.im := by
  have h := abs_lt.mp (abs_two_mul_im_lt hu)
  have hpi := Real.pi_gt_three
  have him : (2 * u).im = 2 * u.im := by simp
  rw [Complex.arg_exp, him, toIocMod_eq_self]
  constructor <;> linarith

theorem lin_re (c b : ℝ) (u : ℂ) :
    ((c : ℂ) * cexp (2 * u) + b).re = c * Real.exp (2 * u.re) * Real.cos (2 * u.im) + b := by
  simp [Complex.exp_re]; ring

theorem lin_im (c b : ℝ) (u : ℂ) :
    ((c : ℂ) * cexp (2 * u) + b).im = c * Real.exp (2 * u.re) * Real.sin (2 * u.im) := by
  simp [Complex.exp_im]; ring

/-- For `c, b > 0` and `|Im u| < 1/2`, `c e^{2u} + b` has positive real part. -/
theorem lin_re_pos {c b : ℝ} (hc : 0 < c) (hb : 0 < b) {u : ℂ} (hu : |u.im| < 1 / 2) :
    0 < ((c : ℂ) * cexp (2 * u) + b).re := by
  rw [lin_re]
  have := cos_pos_of_abs_lt_one (abs_two_mul_im_lt hu)
  have := Real.exp_pos (2 * u.re)
  positivity

/-- Triangle bound `|c w + b| ≤ c s + b` with `s = |w|`, `w = e^{2u}`. -/
theorem lin_norm_le {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (u : ℂ) :
    ‖(c : ℂ) * cexp (2 * u) + b‖ ≤ c * Real.exp (2 * u.re) + b := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc,
    Real.norm_of_nonneg hb]
  simp

/-- The bound `|c w + b| ≥ cos(1) (c s + b)` from the positive real part. -/
theorem lin_norm_ge {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) {u : ℂ} (hu : |u.im| < 1 / 2) :
    Real.cos 1 * (c * Real.exp (2 * u.re) + b) ≤ ‖(c : ℂ) * cexp (2 * u) + b‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [lin_re]
  have h1 := cos_one_le_cos (abs_two_mul_im_lt hu).le
  have h2 := Real.cos_le_one 1
  have hs := Real.exp_pos (2 * u.re)
  have hcs : 0 ≤ c * Real.exp (2 * u.re) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hcs]

theorem arg_eq_arctan {z : ℂ} (hz : 0 < z.re) : z.arg = Real.arctan (z.im / z.re) := by
  have h := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  rw [← Complex.tan_arg, Real.arctan_tan h.1 h.2]

/-- The argument of `c e^{2u} + b` lies between `0` and `arg e^{2u} = 2 Im u`. -/
theorem lin_arg_between {c b : ℝ} (hc : 0 < c) (hb : 0 < b) {u : ℂ} (hu : |u.im| < 1 / 2) :
    (0 ≤ 2 * u.im → 0 ≤ ((c : ℂ) * cexp (2 * u) + b).arg ∧
        ((c : ℂ) * cexp (2 * u) + b).arg ≤ 2 * u.im) ∧
      (2 * u.im ≤ 0 → 2 * u.im ≤ ((c : ℂ) * cexp (2 * u) + b).arg ∧
        ((c : ℂ) * cexp (2 * u) + b).arg ≤ 0) := by
  have hre := lin_re_pos hc hb hu
  rw [arg_eq_arctan hre, lin_im]
  rw [lin_re] at hre ⊢
  set θ := 2 * u.im with hθ
  set s := Real.exp (2 * u.re)
  have hs : 0 < s := Real.exp_pos _
  have hθ1 := abs_two_mul_im_lt hu
  rw [← hθ] at hθ1
  obtain ⟨hθa, hθb⟩ := abs_lt.mp hθ1
  have hcos := cos_pos_of_abs_lt_one hθ1
  have hpi := Real.pi_gt_three
  have htan : Real.arctan (Real.tan θ) = θ := Real.arctan_tan (by linarith) (by linarith)
  have hmono := Real.arctan_strictMono.monotone
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
    have ht0 : 0 ≤ c * s * Real.sin θ / (c * s * Real.cos θ + b) := by positivity
    have ht1 : c * s * Real.sin θ / (c * s * Real.cos θ + b) ≤ Real.tan θ := by
      rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ hre hcos]
      nlinarith [mul_nonneg hb.le hsin]
    constructor
    · simpa using hmono ht0
    · simpa [htan] using hmono ht1
  · rcases h0.lt_or_eq with h0 | h0
    · have hsin : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt h0 (by linarith)
      have ht0 : c * s * Real.sin θ / (c * s * Real.cos θ + b) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hsin.le) hre.le
      have ht1 : Real.tan θ ≤ c * s * Real.sin θ / (c * s * Real.cos θ + b) := by
        rw [Real.tan_eq_sin_div_cos, div_le_div_iff₀ hcos hre]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hb.le hsin.le]
      constructor
      · simpa [htan] using hmono ht1
      · simpa using hmono ht0
    · simp [h0]

/-- Two numbers that both lie between `0` and `θ` differ by at most `|θ|`. -/
theorem abs_sub_le_of_between {x y θ : ℝ}
    (hx : (0 ≤ θ → 0 ≤ x ∧ x ≤ θ) ∧ (θ ≤ 0 → θ ≤ x ∧ x ≤ 0))
    (hy : (0 ≤ θ → 0 ≤ y ∧ y ≤ θ) ∧ (θ ≤ 0 → θ ≤ y ∧ y ≤ 0)) : |x - y| ≤ |θ| := by
  rcases le_total 0 θ with h | h
  · obtain ⟨h1, h2⟩ := hx.1 h
    obtain ⟨h3, h4⟩ := hy.1 h
    rw [abs_of_nonneg h, abs_le]; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := hx.2 h
    obtain ⟨h3, h4⟩ := hy.2 h
    rw [abs_of_nonpos h, abs_le]; constructor <;> linarith

/-! ### The complex smoothed logit `ψ_τ` -/

/-- The extension of `ψ_τ` (`eq:softclip`) to complex `u`, with principal logarithms:
`ψ_τ(u) = (log((2-τ)e^{2u} + τ) - log(τ e^{2u} + 2 - τ))/2`. -/
noncomputable def cpsi (τ : ℝ) (u : ℂ) : ℂ :=
  (Complex.log (((2 - τ : ℝ) : ℂ) * cexp (2 * u) + (τ : ℂ)) -
    Complex.log ((τ : ℂ) * cexp (2 * u) + ((2 - τ : ℝ) : ℂ))) / 2

/-- On real arguments the complex extension is `softclip τ`. -/
theorem cpsi_ofReal {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2) (x : ℝ) :
    cpsi τ x = (softclip τ x : ℂ) := by
  set E := Real.exp (2 * x) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e : cexp (2 * (x : ℂ)) = (E : ℂ) := by rw [hE, Complex.ofReal_exp]; push_cast; ring_nf
  have hc : 0 < 2 - τ := by linarith
  have hA : 0 < (2 - τ) * E + τ := by positivity
  have hB : 0 < τ * E + (2 - τ) := by positivity
  have h1 : ((2 - τ : ℝ) : ℂ) * (E : ℂ) + (τ : ℂ) = (((2 - τ) * E + τ : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (τ : ℂ) * (E : ℂ) + ((2 - τ : ℝ) : ℂ) = ((τ * E + (2 - τ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [cpsi, e, h1, h2, ← Complex.ofReal_log hA.le, ← Complex.ofReal_log hB.le, softclip,
    Real.log_div hA.ne' hB.ne']
  push_cast
  ring

theorem cpsi_re (τ : ℝ) (u : ℂ) :
    (cpsi τ u).re = (Real.log ‖((2 - τ : ℝ) : ℂ) * cexp (2 * u) + (τ : ℂ)‖ -
      Real.log ‖(τ : ℂ) * cexp (2 * u) + ((2 - τ : ℝ) : ℂ)‖) / 2 := by
  simp [cpsi, Complex.log_re]

theorem cpsi_im (τ : ℝ) (u : ℂ) :
    (cpsi τ u).im = ((((2 - τ : ℝ) : ℂ) * cexp (2 * u) + (τ : ℂ)).arg -
      ((τ : ℂ) * cexp (2 * u) + ((2 - τ : ℝ) : ℂ)).arg) / 2 := by
  simp [cpsi, Complex.log_im]

/-- `ψ_τ` is complex differentiable on the strip `|Im u| < 1/2`: both arguments of the
logarithms have positive real part. -/
theorem differentiableAt_cpsi {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2) {u : ℂ}
    (hu : |u.im| < 1 / 2) : DifferentiableAt ℂ (cpsi τ) u := by
  have hc : (0 : ℝ) < 2 - τ := by linarith
  have h1 : DifferentiableAt ℂ (fun u : ℂ => ((2 - τ : ℝ) : ℂ) * cexp (2 * u) + (τ : ℂ)) u := by
    fun_prop
  have h2 : DifferentiableAt ℂ (fun u : ℂ => (τ : ℂ) * cexp (2 * u) + ((2 - τ : ℝ) : ℂ)) u := by
    fun_prop
  have s1 := Complex.mem_slitPlane_iff.mpr (Or.inl (lin_re_pos hc hτ0 hu))
  have s2 := Complex.mem_slitPlane_iff.mpr (Or.inl (lin_re_pos hτ0 hc hu))
  exact ((h1.clog s1).sub (h2.clog s2)).div_const 2

theorem softclipBound_nonneg {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) : 0 ≤ softclipBound τ := by
  unfold softclipBound
  have : 1 ≤ (2 - τ) / τ := by rw [le_div_iff₀ hτ0]; linarith
  have := Real.log_nonneg this
  linarith

/-- `lem:softclip-poly` (proof): on the strip `|Im u| < 1/2`, with `w = e^{2u}` and
`0 < b ≤ c`, `cos(1) b/c ≤ |cw + b|/|bw + c| ≤ (1/cos(1)) c/b`. -/
theorem lin_ratio_bounds {c b : ℝ} (hb : 0 < b) (hbc : b ≤ c) {u : ℂ} (hu : |u.im| < 1 / 2) :
    Real.cos 1 * (b / c) ≤ ‖(c : ℂ) * cexp (2 * u) + b‖ / ‖(b : ℂ) * cexp (2 * u) + c‖ ∧
      ‖(c : ℂ) * cexp (2 * u) + b‖ / ‖(b : ℂ) * cexp (2 * u) + c‖ ≤
        (Real.cos 1)⁻¹ * (c / b) := by
  have hc : 0 < c := by linarith
  have hs : 0 < Real.exp (2 * u.re) := Real.exp_pos _
  have hcos := Real.cos_one_pos
  have hN₁u := lin_norm_le hc.le hb.le u
  have hN₁l := lin_norm_ge hc.le hb.le hu
  have hN₂u := lin_norm_le hb.le hc.le u
  have hN₂l := lin_norm_ge hb.le hc.le hu
  set s := Real.exp (2 * u.re)
  set N₁ := ‖(c : ℂ) * cexp (2 * u) + (b : ℂ)‖
  set N₂ := ‖(b : ℂ) * cexp (2 * u) + (c : ℂ)‖
  have hN₂ : 0 < N₂ := lt_of_lt_of_le (by positivity) hN₂l
  constructor
  · rw [le_div_iff₀ hN₂]
    calc Real.cos 1 * (b / c) * N₂ ≤ Real.cos 1 * (b / c) * (b * s + c) := by gcongr
      _ ≤ Real.cos 1 * (c * s + b) := by
          rw [mul_assoc]
          gcongr
          rw [div_mul_eq_mul_div, div_le_iff₀ hc]
          nlinarith [mul_le_mul_of_nonneg_left hbc hs.le]
      _ ≤ N₁ := hN₁l
  · rw [div_le_iff₀ hN₂]
    calc N₁ ≤ c * s + b := hN₁u
      _ ≤ (c / b) * (b * s + c) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hb]
          nlinarith
      _ = (Real.cos 1)⁻¹ * (c / b) * (Real.cos 1 * (b * s + c)) := by
          field_simp
      _ ≤ (Real.cos 1)⁻¹ * (c / b) * N₂ := by gcongr

/-- `lem:softclip-poly` (proof): on the strip `|Im u| < 1/2`,
`|Re ψ_τ(u)| ≤ M_τ + (1/2) log sec(1)`. -/
theorem abs_re_cpsi_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {u : ℂ} (hu : |u.im| < 1 / 2) :
    |(cpsi τ u).re| ≤ softclipBound τ + Real.log (Real.cos 1)⁻¹ / 2 := by
  have hc : 0 < 2 - τ := by linarith
  have hcos := Real.cos_one_pos
  obtain ⟨lo, hi⟩ := lin_ratio_bounds (c := 2 - τ) hτ0 (by linarith) hu
  have hN₁ := lt_of_lt_of_le (by positivity) (lin_norm_ge hc.le hτ0.le hu)
  have hN₂ := lt_of_lt_of_le (by positivity) (lin_norm_ge hτ0.le hc.le hu)
  rw [cpsi_re, ← Real.log_div hN₁.ne' hN₂.ne']
  have l1 := Real.log_le_log (div_pos hN₁ hN₂) hi
  have l2 := Real.log_le_log (by positivity) lo
  rw [Real.log_mul (inv_pos.mpr hcos).ne' (by positivity), Real.log_div hc.ne' hτ0.ne'] at l1
  rw [Real.log_mul hcos.ne' (by positivity), Real.log_div hτ0.ne' hc.ne'] at l2
  rw [softclipBound, Real.log_div hc.ne' hτ0.ne', Real.log_inv] at *
  rw [abs_le]
  constructor <;> linarith

/-- `lem:softclip-poly` (proof): on the strip `|Im u| < 1/2`, `|Im ψ_τ(u)| < 1/2`, since both
arguments lie between `0` and `arg e^{2u} = 2 Im u`. -/
theorem abs_im_cpsi_lt {τ : ℝ} (hτ0 : 0 < τ) (hτ2 : τ < 2) {u : ℂ} (hu : |u.im| < 1 / 2) :
    |(cpsi τ u).im| < 1 / 2 := by
  have hc : (0 : ℝ) < 2 - τ := by linarith
  have h := abs_sub_le_of_between (lin_arg_between hc hτ0 hu) (lin_arg_between hτ0 hc hu)
  rw [cpsi_im, abs_div, abs_two]
  have := abs_two_mul_im_lt hu
  linarith

/-- `lem:softclip-poly` (proof): `|ψ_τ(u)| ≤ M_τ + 2` on the strip `|Im u| < 1/2`. -/
theorem norm_cpsi_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {u : ℂ} (hu : |u.im| < 1 / 2) :
    ‖cpsi τ u‖ ≤ softclipBound τ + 2 := by
  have h1 := abs_re_cpsi_le hτ0 hτ1 hu
  have h2 := abs_im_cpsi_lt hτ0 (by linarith) hu
  have hsec : Real.log (Real.cos 1)⁻¹ ≤ 1 := by
    have hc := half_le_cos_one
    have : (Real.cos 1)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ Real.cos_one_pos (by norm_num)]; linarith
    calc Real.log (Real.cos 1)⁻¹ ≤ Real.log 2 :=
          Real.log_le_log (inv_pos.mpr Real.cos_one_pos) this
      _ ≤ 1 := by linarith [Real.log_two_lt_d9]
  calc ‖cpsi τ u‖ ≤ |(cpsi τ u).re| + |(cpsi τ u).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ softclipBound τ + 2 := by linarith

/-- `lem:softclip-poly`, given the Bernstein-ellipse theorem `ChebyshevApprox`: for `T ≥ 1`,
`τ ∈ (0, 1/2)` and `ζ ∈ (0, 1)`, a real polynomial of degree at most
`⌈3T log(4T(M_τ + 2)/ζ)⌉` approximates `ψ_τ` within `ζ` on `[-T, T]`. -/
theorem softclip_poly_of (H : ChebyshevApprox) {T τ ζ : ℝ} (hT : 1 ≤ T) (hτ0 : 0 < τ)
    (hτ1 : τ < 1 / 2) (hζ0 : 0 < ζ) (_hζ1 : ζ < 1) :
    ∃ r : Polynomial ℝ, r.natDegree ≤ ⌈3 * T * Real.log (4 * T * (softclipBound τ + 2) / ζ)⌉₊ ∧
      ∀ u ∈ Set.Icc (-T) T, |r.eval u - softclip τ u| ≤ ζ := by
  have hM : 0 < softclipBound τ + 2 := by
    have := softclipBound_nonneg hτ0 (by linarith); linarith
  refine strip_approx H (cpsi τ) (softclip τ) hT hM hζ0
    (fun u hu => ⟨differentiableAt_cpsi hτ0 (by linarith) hu, norm_cpsi_le hτ0 (by linarith) hu⟩)
    (fun x => ?_)
  rw [cpsi_ofReal hτ0 (by linarith)]
  simp

/-! ### The complex logistic function -/

/-- The complex logistic function `u ↦ σ(2u) = 1/(1 + e^{-2u})`. -/
noncomputable def csig (u : ℂ) : ℂ := (1 + cexp (-(2 * u)))⁻¹

theorem csig_ofReal (x : ℝ) : csig x = (sigmoid (2 * x) : ℂ) := by
  simp [csig, sigmoid]

/-- `lem:poly-sigmoid` (proof): for `u = a + ib` and `r = e^{-2a}`,
`|1 + e^{-2u}|² = 1 + r² + 2 r cos(2b)`. -/
theorem normSq_one_add_exp (u : ℂ) :
    normSq (1 + cexp (-(2 * u))) =
      1 + Real.exp (-(2 * u.re)) ^ 2 + 2 * Real.exp (-(2 * u.re)) * Real.cos (2 * u.im) := by
  have h := Real.sin_sq_add_cos_sq (2 * u.im)
  rw [normSq_apply]
  simp [Complex.exp_re, Complex.exp_im, Real.cos_neg, Real.sin_neg]
  linear_combination Real.exp (-(2 * u.re)) ^ 2 * h

/-- On the strip `|Im u| < 1/2`, `|1 + e^{-2u}| ≥ 1`. -/
theorem one_le_norm_one_add_exp {u : ℂ} (hu : |u.im| < 1 / 2) :
    1 ≤ ‖1 + cexp (-(2 * u))‖ := by
  have hcos := cos_pos_of_abs_lt_one (abs_two_mul_im_lt hu)
  have hr := Real.exp_pos (-(2 * u.re))
  have hsq : 1 ≤ ‖1 + cexp (-(2 * u))‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_one_add_exp]
    nlinarith [mul_pos hr hcos, sq_nonneg (Real.exp (-(2 * u.re)))]
  by_contra h
  have := pow_lt_one₀ (norm_nonneg _) (not_le.mp h) two_ne_zero
  linarith

/-- `lem:poly-sigmoid` (proof): `σ(2u)` has modulus at most one on the strip `|Im u| < 1/2`. -/
theorem norm_csig_le {u : ℂ} (hu : |u.im| < 1 / 2) : ‖csig u‖ ≤ 1 := by
  rw [csig, norm_inv]
  exact inv_le_one_of_one_le₀ (one_le_norm_one_add_exp hu)

/-- `lem:poly-sigmoid` (proof): `σ(2u)` is complex differentiable on the strip `|Im u| < 1/2`. -/
theorem differentiableAt_csig {u : ℂ} (hu : |u.im| < 1 / 2) : DifferentiableAt ℂ csig u := by
  have hne : 1 + cexp (-(2 * u)) ≠ 0 := by
    intro h
    have := one_le_norm_one_add_exp hu
    rw [h, norm_zero] at this
    linarith
  have hd : DifferentiableAt ℂ (fun u : ℂ => 1 + cexp (-(2 * u))) u := by fun_prop
  exact hd.inv hne

/-! ### The affine correction `eq:affine-correction` -/

/-- The affine correction `g = (g₀ + 2β)/(1 + 4β)` of `eq:affine-correction`. -/
noncomputable def affineCorrection (β g₀ : ℝ) : ℝ := (g₀ + 2 * β) / (1 + 4 * β)

/-- `eq:affine-correction`: values of `g₀` in `[-β, 1 + β]` are sent into
`[β/(1+4β), (1+3β)/(1+4β)]`. -/
theorem affineCorrection_mem {β g₀ : ℝ} (hβ : 0 ≤ β) (h1 : -β ≤ g₀) (h2 : g₀ ≤ 1 + β) :
    β / (1 + 4 * β) ≤ affineCorrection β g₀ ∧
      affineCorrection β g₀ ≤ (1 + 3 * β) / (1 + 4 * β) := by
  have hd : 0 < 1 + 4 * β := by linarith
  unfold affineCorrection
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) hd.le
  · exact div_le_div_of_nonneg_right (by linarith) hd.le

/-- `eq:affine-correction`: the interval `[β/(1+4β), (1+3β)/(1+4β)]` lies strictly inside
`(0, 1)` for `β > 0`. -/
theorem affineCorrection_range_pos {β : ℝ} (hβ : 0 < β) :
    0 < β / (1 + 4 * β) ∧ (1 + 3 * β) / (1 + 4 * β) < 1 := by
  have hd : 0 < 1 + 4 * β := by linarith
  exact ⟨div_pos hβ hd, (div_lt_one hd).mpr (by linarith)⟩

/-- `lem:poly-sigmoid` (proof), first step of the error bound:
`|g - p| ≤ (|g₀ - p| + 2β|1 - 2p|)/(1 + 4β)`. -/
theorem abs_affineCorrection_sub_le {β : ℝ} (hβ : 0 ≤ β) (g₀ p : ℝ) :
    |affineCorrection β g₀ - p| ≤ (|g₀ - p| + 2 * β * |1 - 2 * p|) / (1 + 4 * β) := by
  have hd : 0 < 1 + 4 * β := by linarith
  have hid : affineCorrection β g₀ - p = ((g₀ - p) + 2 * β * (1 - 2 * p)) / (1 + 4 * β) := by
    unfold affineCorrection; field_simp; ring
  rw [hid, abs_div, abs_of_pos hd]
  refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans ?_) hd.le
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * β)]

/-- `lem:poly-sigmoid` (proof): if `|g₀ - p| ≤ β` and `p ∈ [0, 1]`, the corrected value is within
`3β` of `p`. -/
theorem abs_affineCorrection_sub_le_three {β g₀ p : ℝ} (hβ : 0 ≤ β) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hg : |g₀ - p| ≤ β) : |affineCorrection β g₀ - p| ≤ 3 * β := by
  have hd : 0 < 1 + 4 * β := by linarith
  have hp : |1 - 2 * p| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  refine (abs_affineCorrection_sub_le hβ g₀ p).trans ?_
  rw [div_le_iff₀ hd]
  nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : (0 : ℝ) ≤ 2 * β)]

/-! ### `lem:poly-sigmoid` -/

/-- `lem:poly-sigmoid` before the affine correction: with `β = η/3`, a real polynomial `g₀` of
degree at most `⌈3T log(4T/β)⌉ = ⌈3T log(12T/η)⌉` approximates `σ(2u)` within `β` on
`[-T, T]`. Uses `ChebyshevApprox` with `F(z) = σ(2Tz)` and `M = 1`. -/
theorem sigmoid_approx_of (H : ChebyshevApprox) {T η : ℝ} (hT : 1 ≤ T) (hη0 : 0 < η) :
    ∃ g₀ : Polynomial ℝ, g₀.natDegree ≤ ⌈3 * T * Real.log (12 * T / η)⌉₊ ∧
      ∀ u ∈ Set.Icc (-T) T, |g₀.eval u - sigmoid (2 * u)| ≤ η / 3 := by
  have hβ : 0 < η / 3 := by positivity
  have h12 : 4 * T * 1 / (η / 3) = 12 * T / η := by field_simp; ring
  rw [← h12]
  exact strip_approx H csig (fun x => sigmoid (2 * x)) hT one_pos hβ
    (fun u hu => ⟨differentiableAt_csig hu, norm_csig_le hu⟩)
    (fun x => by rw [csig_ofReal]; simp)

/-- `lem:poly-sigmoid` with the intermediate claims of its proof: with `β = η/3`, the corrected
polynomial `g = (g₀ + 2β)/(1 + 4β)` (`eq:affine-correction`) has the same degree bound, its
values on `[-T, T]` lie in `[β/(1+4β), (1+3β)/(1+4β)]`, and it is within `3β` of `σ(2u)`. -/
theorem poly_sigmoid_corrected_of (H : ChebyshevApprox) {T η : ℝ} (hT : 1 ≤ T) (hη0 : 0 < η) :
    ∃ g : Polynomial ℝ, g.natDegree ≤ ⌈3 * T * Real.log (12 * T / η)⌉₊ ∧
      ∀ u ∈ Set.Icc (-T) T,
        η / 3 / (1 + 4 * (η / 3)) ≤ g.eval u ∧
        g.eval u ≤ (1 + 3 * (η / 3)) / (1 + 4 * (η / 3)) ∧
        |g.eval u - sigmoid (2 * u)| ≤ 3 * (η / 3) := by
  set β := η / 3 with hβ_def
  have hβ : 0 < β := by positivity
  obtain ⟨g₀, hdeg, happrox⟩ := sigmoid_approx_of H hT hη0
  refine ⟨C (1 + 4 * β)⁻¹ * (g₀ + C (2 * β)), ?_, fun u hu => ?_⟩
  · exact (natDegree_C_mul_le _ _).trans (natDegree_add_C.le.trans hdeg)
  · have heval : (C (1 + 4 * β)⁻¹ * (g₀ + C (2 * β))).eval u = affineCorrection β (g₀.eval u) := by
      simp only [eval_mul, eval_C, eval_add, affineCorrection]
      ring
    rw [heval]
    have hg := happrox u hu
    have hs0 := sigmoid_pos (2 * u)
    have hs1 := sigmoid_lt_one (2 * u)
    obtain ⟨hlo, hhi⟩ := abs_le.mp hg
    obtain ⟨m1, m2⟩ := affineCorrection_mem hβ.le (by linarith) (by linarith)
    exact ⟨m1, m2, abs_affineCorrection_sub_le_three hβ.le hs0.le hs1.le hg⟩

/-- `lem:poly-sigmoid`, given the Bernstein-ellipse theorem `ChebyshevApprox`: for `T ≥ 1` and
`0 < η < 1`, there is a real polynomial `g` of degree at most `⌈3T log(12T/η)⌉` with
`0 < g(u) < 1` and `|g(u) - σ(2u)| ≤ η` for every `u ∈ [-T, T]`. -/
theorem poly_sigmoid_of (H : ChebyshevApprox) {T η : ℝ} (hT : 1 ≤ T) (hη0 : 0 < η)
    (_hη1 : η < 1) :
    ∃ g : Polynomial ℝ, g.natDegree ≤ ⌈3 * T * Real.log (12 * T / η)⌉₊ ∧
      ∀ u ∈ Set.Icc (-T) T, 0 < g.eval u ∧ g.eval u < 1 ∧ |g.eval u - sigmoid (2 * u)| ≤ η := by
  obtain ⟨g, hdeg, hg⟩ := poly_sigmoid_corrected_of H hT hη0
  refine ⟨g, hdeg, fun u hu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hg u hu
  obtain ⟨r1, r2⟩ := affineCorrection_range_pos (by positivity : 0 < η / 3)
  refine ⟨r1.trans_le h1, h2.trans_lt r2, ?_⟩
  linarith

end LowLogitRank.Approximation
