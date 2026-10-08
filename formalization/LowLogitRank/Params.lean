import LowLogitRank.Basic

/-!
# Smoothing identities and parameter arithmetic

This file checks the elementary identities of the smoothing step (`eq:softclip`,
`eq:smoothed-polynomial-tv`) and the finite parameter arithmetic in the proofs of `thm:fixed`
(`eq:smooth-parameters`, `eq:smooth-budget`), of its second proof through probability rank
(`eq:fixed-parameters`, `eq:combined-budget`) and of `cor:power-logits`.

Logarithms in base two are `Real.logb 2`, natural logarithms are `Real.log`.
-/

namespace LowLogitRank.Params

/-! ### Helper bounds for logarithms and powers of two -/

theorem log_two_lt_one : Real.log 2 < 1 := by
  have := Real.log_two_lt_d9
  norm_num at this
  linarith

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two

/-- The natural logarithm is at most the binary logarithm on `[1, ∞)`. -/
theorem log_le_logb_two {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.logb 2 x := by
  rw [← Real.log_div_log, le_div_iff₀ log_two_pos']
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  nlinarith [log_two_lt_one]

theorem logb_two_pow (n : ℕ) : Real.logb 2 ((2 : ℝ) ^ n) = n := by
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

theorem logb_two_two : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one one_lt_two

/-- `x ≤ 2 ^ ⌈log₂ x⌉₊` for `x > 0`. -/
theorem le_two_pow_ceil_logb {x : ℝ} (hx : 0 < x) :
    x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ := by
  have h := Nat.le_ceil (Real.logb 2 x)
  rw [Real.logb_le_iff_le_rpow one_lt_two hx, Real.rpow_natCast] at h
  exact h

/-- `2 ^ ⌈log₂ x⌉₊ < 2 x` for `x ≥ 1`. -/
theorem two_pow_ceil_logb_lt {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ < 2 * x := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.logb 2 x := Real.logb_nonneg one_lt_two hx
  have h := Nat.ceil_lt_add_one hl
  have h2 : (2 : ℝ) ^ ((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) < (2 : ℝ) ^ (Real.logb 2 x + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt one_lt_two h
  rw [Real.rpow_natCast, Real.rpow_add two_pos, Real.rpow_logb two_pos (by norm_num) hx0,
    Real.rpow_one] at h2
  linarith

/-- From `x ≤ 2 ^ n` to `log₂ x ≤ n`. -/
theorem logb_le_of_le_two_pow {x : ℝ} {n : ℕ} (hx : 0 < x) (h : x ≤ (2 : ℝ) ^ n) :
    Real.logb 2 x ≤ n := by
  rw [Real.logb_le_iff_le_rpow one_lt_two hx, Real.rpow_natCast]
  exact h

/-- From `x < 2 ^ n` to `log₂ x < n`. -/
theorem logb_lt_of_lt_two_pow {x : ℝ} {n : ℕ} (hx : 0 < x) (h : x < (2 : ℝ) ^ n) :
    Real.logb 2 x < n := by
  rw [Real.logb_lt_iff_lt_rpow one_lt_two hx, Real.rpow_natCast]
  exact h

/-- `n ≤ 2 ^ n` in `ℝ`. -/
theorem natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  have := (Nat.lt_two_pow_self (n := n)).le
  exact_mod_cast this

/-- `log₂ n ≤ n` for a positive natural number. -/
theorem logb_natCast_le (n : ℕ) (hn : 1 ≤ n) : Real.logb 2 (n : ℝ) ≤ n :=
  logb_le_of_le_two_pow (by exact_mod_cast hn) (natCast_le_two_pow n)

/-- `log y ≤ y - 1`, used in the form `log y ≤ y`. -/
theorem log_le_self' {y : ℝ} (hy : 0 < y) : Real.log y ≤ y :=
  (Real.log_le_sub_one_of_pos hy).trans (by linarith)

/-! ### Smoothing: `eq:softclip` -/

/-- The odds of the smoothed bit, written through the odds `x / (1 - x)` of the original bit. -/
theorem smooth_odds {τ x : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    ((1 - τ) * x + τ / 2) / (1 - ((1 - τ) * x + τ / 2)) =
      ((2 - τ) * (x / (1 - x)) + τ) / (τ * (x / (1 - x)) + (2 - τ)) := by
  have h1 : 1 - x ≠ 0 := by linarith
  have h2 : 1 - ((1 - τ) * x + τ / 2) ≠ 0 := by nlinarith
  have h3 : τ * x + (2 - τ) * (1 - x) ≠ 0 := by nlinarith
  rw [div_eq_div_iff h2 (by
    rw [show τ * (x / (1 - x)) + (2 - τ) = (τ * x + (2 - τ) * (1 - x)) / (1 - x) by
      field_simp]
    exact div_ne_zero h3 h1)]
  field_simp
  ring

/-- `eq:softclip`: for `0 < τ < 1` and a conditional probability `p h ∈ (0,1)`, the centered
logit of the smoothed model `P^τ` is `ψ_τ` of the centered logit of `P`. -/
theorem logit_smooth {τ : ℝ} {p : NextBit} {h : List Bool} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hp0 : 0 < p h) (hp1 : p h < 1) :
    logit (smooth τ p) h = softclip τ (logit p h) := by
  have he : Real.exp (2 * logit p h) = p h / (1 - p h) := by
    rw [logit, show 2 * (Real.log (p h / (1 - p h)) / 2) = Real.log (p h / (1 - p h)) by ring]
    exact Real.exp_log (div_pos hp0 (by linarith))
  rw [softclip, he, logit]
  simp only [smooth]
  rw [smooth_odds hτ0 hτ1 hp0 hp1]

/-- `eq:softclip`, the bound `|ψ_τ(u)| ≤ M_τ = (1/2) log ((2 - τ)/τ)` for `0 < τ < 1`. -/
theorem abs_softclip_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (u : ℝ) :
    |softclip τ u| ≤ softclipBound τ := by
  set w := Real.exp (2 * u) with hw
  have hw0 : 0 < w := Real.exp_pos _
  have hc : 0 < 2 - τ := by linarith
  have hnum : 0 < (2 - τ) * w + τ := by positivity
  have hden : 0 < τ * w + (2 - τ) := by positivity
  have hf : 0 < ((2 - τ) * w + τ) / (τ * w + (2 - τ)) := div_pos hnum hden
  have hcb : 0 < (2 - τ) / τ := div_pos hc hτ0
  have hup : ((2 - τ) * w + τ) / (τ * w + (2 - τ)) ≤ (2 - τ) / τ := by
    rw [div_le_div_iff₀ hden hτ0]
    nlinarith
  have hlo : τ / (2 - τ) ≤ ((2 - τ) * w + τ) / (τ * w + (2 - τ)) := by
    rw [div_le_div_iff₀ hc hden]
    nlinarith
  have hlog_up := Real.log_le_log hf hup
  have hlog_lo := Real.log_le_log (div_pos hτ0 hc) hlo
  have hinv : Real.log (τ / (2 - τ)) = -Real.log ((2 - τ) / τ) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv] at hlog_lo
  unfold softclip softclipBound
  rw [abs_div, abs_two, div_le_div_iff_of_pos_right two_pos, abs_le]
  exact ⟨hlog_lo, hlog_up⟩

/-- `sec:fixed-rank`: for `p ∈ [0,1]` and `τ ≤ 1` the smoothed probability lies in
`[τ/2, 1 - τ/2]`; this is the conditional probability floor `τ/2`. -/
theorem smooth_mem_Icc {τ x : ℝ} (hτ1 : τ ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    τ / 2 ≤ (1 - τ) * x + τ / 2 ∧ (1 - τ) * x + τ / 2 ≤ 1 - τ / 2 := by
  have h0 : 0 ≤ (1 - τ) * x := mul_nonneg (by linarith) hx0
  have h1 : 0 ≤ (1 - τ) * (1 - x) := mul_nonneg (by linarith) (by linarith)
  constructor <;> nlinarith

/-- `sec:fixed-rank`: the next-bit discrepancy `|P^τ(1 | h) - P(1 | h)| ≤ τ/2` behind
`eq:smoothing-tv`. -/
theorem abs_smooth_sub_le {τ x : ℝ} (hτ0 : 0 ≤ τ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(1 - τ) * x + τ / 2 - x| ≤ τ / 2 := by
  have h0 : 0 ≤ τ * x := mul_nonneg hτ0 hx0
  have h1 : 0 ≤ τ * (1 - x) := mul_nonneg hτ0 (by linarith)
  rw [abs_le]
  constructor <;> nlinarith

/-- `sec:fixed-rank`: the smoothed model has the floor `τ/2`, and its next-bit probabilities
are within `τ/2` of those of `P`. -/
theorem smooth_bounds {τ : ℝ} {p : NextBit} {h : List Bool} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hp0 : 0 ≤ p h) (hp1 : p h ≤ 1) :
    τ / 2 ≤ smooth τ p h ∧ smooth τ p h ≤ 1 - τ / 2 ∧ |smooth τ p h - p h| ≤ τ / 2 :=
  ⟨(smooth_mem_Icc hτ1 hp0 hp1).1, (smooth_mem_Icc hτ1 hp0 hp1).2,
    abs_smooth_sub_le hτ0 hp0 hp1⟩

/-- `sec:fixed-rank`: for `0 < τ ≤ 1` the smoothed model of any `P` with conditional
probabilities in `[0,1]` has full support. -/
theorem smooth_fullSupport {τ : ℝ} {p : NextBit} {T : ℕ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1) :
    FullSupport T (smooth τ p) := by
  intro h hh
  obtain ⟨h1, h2, -⟩ := smooth_bounds (p := p) (h := h) hτ0.le hτ1 (hp h hh).1 (hp h hh).2
  constructor <;> linarith

/-- The smoothed logit is bounded by `M_τ` at every prefix where `P` has full support. -/
theorem abs_logit_smooth_le {τ : ℝ} {p : NextBit} {h : List Bool} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hp0 : 0 < p h) (hp1 : p h < 1) :
    |logit (smooth τ p) h| ≤ softclipBound τ := by
  rw [logit_smooth hτ0 hτ1 hp0 hp1]
  exact abs_softclip_le hτ0 hτ1 _

/-! ### The Lipschitz bound for `u ↦ σ(2u)` (`eq:smoothed-polynomial-tv`) -/

theorem sigmoid_eq_real_sigmoid : sigmoid = Real.sigmoid := rfl

theorem hasDerivAt_sigmoid_two_mul (u : ℝ) :
    HasDerivAt (fun x => sigmoid (2 * x))
      (sigmoid (2 * u) * (1 - sigmoid (2 * u)) * 2) u := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have h2 := (Real.hasDerivAt_sigmoid (2 * u)).comp u h1
  rw [sigmoid_eq_real_sigmoid]
  exact h2

theorem abs_sigmoid_deriv_le (v : ℝ) : |sigmoid v * (1 - sigmoid v) * 2| ≤ 1 / 2 := by
  have h0 := sigmoid_pos v
  have h1 := sigmoid_lt_one v
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith [sq_nonneg (sigmoid v - 1 / 2)]

theorem sigmoid_two_mul_sub_le_of_lt {a b : ℝ} (hab : a < b) :
    |sigmoid (2 * b) - sigmoid (2 * a)| ≤ (b - a) / 2 := by
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope (fun x => sigmoid (2 * x))
    (fun x => sigmoid (2 * x) * (1 - sigmoid (2 * x)) * 2) hab
    (fun x _ => (hasDerivAt_sigmoid_two_mul x).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_sigmoid_two_mul x)
  have hba : 0 < b - a := by linarith
  have hq : sigmoid (2 * b) - sigmoid (2 * a) =
      (sigmoid (2 * c) * (1 - sigmoid (2 * c)) * 2) * (b - a) := by
    rw [hc]; field_simp
  rw [hq, abs_mul, abs_of_pos hba]
  have := abs_sigmoid_deriv_le (2 * c)
  nlinarith

/-- `eq:smoothed-polynomial-tv`: the derivative of `u ↦ σ(2u)` has magnitude at most `1/2`,
so `|σ(2a) - σ(2b)| ≤ |a - b|/2`. -/
theorem abs_sigmoid_two_mul_sub_le (a b : ℝ) :
    |sigmoid (2 * a) - sigmoid (2 * b)| ≤ |a - b| / 2 := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [abs_sub_comm, abs_sub_comm a b, abs_of_pos (by linarith : 0 < b - a)]
    exact sigmoid_two_mul_sub_le_of_lt hab
  · simp
  · rw [abs_of_pos (by linarith : 0 < a - b)]
    exact sigmoid_two_mul_sub_le_of_lt hab

/-- `eq:softclip`: `σ(2 ψ_τ(u)) = (1 - τ) σ(2u) + τ/2` for every real `u` and `0 < τ < 1`. -/
theorem sigmoid_two_mul_softclip {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (u : ℝ) :
    sigmoid (2 * softclip τ u) = (1 - τ) * sigmoid (2 * u) + τ / 2 := by
  set p : NextBit := ofLogit (fun _ => u)
  have hp0 : 0 < p [] := sigmoid_pos _
  have hp1 : p [] < 1 := sigmoid_lt_one _
  have hl : logit p [] = u := logit_ofLogit (fun _ => u) []
  have hs0 : 0 < smooth τ p [] := by
    have := (smooth_bounds (p := p) (h := []) hτ0.le hτ1.le hp0.le hp1.le).1; linarith
  have hs1 : smooth τ p [] < 1 := by
    have := (smooth_bounds (p := p) (h := []) hτ0.le hτ1.le hp0.le hp1.le).2.1; linarith
  have key := ofLogit_logit hs0 hs1
  rw [ofLogit, logit_smooth hτ0 hτ1 hp0 hp1, hl] at key
  rw [key]
  rfl

/-- `eq:smoothed-polynomial-tv`: `P^τ(1 | h) = σ(2 ψ_τ(ℓ_P(h)))` at a fully supported prefix. -/
theorem sigmoid_two_mul_softclip_logit {τ : ℝ} {p : NextBit} {h : List Bool} (hτ0 : 0 < τ)
    (hτ1 : τ < 1) (hp0 : 0 < p h) (hp1 : p h < 1) :
    sigmoid (2 * softclip τ (logit p h)) = smooth τ p h := by
  rw [sigmoid_two_mul_softclip hτ0 hτ1, ← ofLogit, ofLogit_logit hp0 hp1]
  rfl

/-- `eq:smoothed-polynomial-tv`: an approximation `r` of `ψ_τ(u)` within `ζ` moves the next-bit
probability `σ(2·)` by at most `ζ/2`, in particular by at most `ζ`. -/
theorem abs_sigmoid_sub_softclip_le {τ ζ r u : ℝ} (hr : |r - softclip τ u| ≤ ζ) :
    |sigmoid (2 * r) - sigmoid (2 * softclip τ u)| ≤ ζ / 2 ∧
      |sigmoid (2 * r) - sigmoid (2 * softclip τ u)| ≤ ζ := by
  have h := abs_sigmoid_two_mul_sub_le r (softclip τ u)
  have hz : 0 ≤ ζ := (abs_nonneg _).trans hr
  constructor <;> linarith

/-- `eq:smoothed-polynomial-tv`, first part: if `P°` has logits `r(ℓ_P(h))` and
`|r(ℓ_P(h)) - ψ_τ(ℓ_P(h))| ≤ ζ`, then `|P°(1 | h) - P^τ(1 | h)| ≤ ζ`. Here `r` is any real
function, for instance the polynomial of `lem:softclip-poly`. -/
theorem abs_ofLogit_sub_smooth_le {τ ζ : ℝ} {p : NextBit} {r : ℝ → ℝ} {h : List Bool}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hp0 : 0 < p h) (hp1 : p h < 1)
    (hr : |r (logit p h) - softclip τ (logit p h)| ≤ ζ) :
    |ofLogit (fun g => r (logit p g)) h - smooth τ p h| ≤ ζ := by
  rw [← sigmoid_two_mul_softclip_logit hτ0 hτ1 hp0 hp1]
  exact (abs_sigmoid_sub_softclip_le hr).2

/-- `lem:logit-lift`, magnitude claim: an approximation within `ζ` of `ψ_τ(u)` has magnitude at
most `M_τ + ζ`. -/
theorem abs_le_softclipBound_add {τ ζ r u : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hr : |r - softclip τ u| ≤ ζ) : |r| ≤ softclipBound τ + ζ := by
  have h1 := abs_softclip_le hτ0 hτ1 u
  calc |r| = |(r - softclip τ u) + softclip τ u| := by ring_nf
    _ ≤ |r - softclip τ u| + |softclip τ u| := abs_add_le _ _
    _ ≤ softclipBound τ + ζ := by linarith

/-! ### Degree arithmetic for the Chebyshev truncation (`lem:softclip-poly`, `lem:poly-sigmoid`)

With `ρ = 1 + 1/(2T)` the truncation bound `2M ρ^{-k}/(ρ - 1)` of `ChebyshevApprox` equals
`4TM ρ^{-k}`, and `log ρ ≥ 1/(3T)` turns a degree `k ≥ 3T log(4TM/ζ)` into error `ζ`. -/

/-- `x/(1+x) ≤ log(1+x)` for `x > -1`. -/
theorem div_one_add_le_log {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ Real.log (1 + x) := by
  have h := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + x)
  have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  linarith

/-- `lem:softclip-poly`, `lem:poly-sigmoid`: `log(1 + 1/(2T)) ≥ 1/(3T)` for `T ≥ 1`. -/
theorem log_rho_ge {T : ℝ} (hT : 1 ≤ T) : 1 / (3 * T) ≤ Real.log (1 + 1 / (2 * T)) := by
  have h := div_one_add_le_log (by positivity : (0 : ℝ) ≤ 1 / (2 * T))
  have e : 1 / (2 * T) / (1 + 1 / (2 * T)) = 1 / (2 * T + 1) := by
    field_simp
  rw [e] at h
  refine le_trans ?_ h
  apply one_div_le_one_div_of_le (by positivity)
  linarith

/-- `lem:softclip-poly`, `lem:poly-sigmoid`: the Bernstein ellipse of parameter `1 + x` has
half-width `((1+x) - (1+x)⁻¹)/2 < x`; with `x = 1/(2T)` this gives `|Im(Tz)| < 1/2`. -/
theorem ellipse_half_width_lt {x : ℝ} (hx : 0 < x) : ((1 + x) - (1 + x)⁻¹) / 2 < x := by
  have e : ((1 + x) - (1 + x)⁻¹) / 2 = x * (2 + x) / (2 * (1 + x)) := by
    field_simp; ring
  rw [e, div_lt_iff₀ (by positivity)]
  nlinarith

/-- `lem:softclip-poly`, `lem:poly-sigmoid`: `2M ρ^{-k}/(ρ - 1) = 4TM ρ^{-k}` for
`ρ = 1 + 1/(2T)`. -/
theorem chebyshev_tail_eq {T : ℝ} (hT : 0 < T) (M : ℝ) (k : ℕ) :
    2 * M * (1 + 1 / (2 * T))⁻¹ ^ k / ((1 + 1 / (2 * T)) - 1) =
      4 * T * M * (1 + 1 / (2 * T))⁻¹ ^ k := by
  field_simp
  ring

/-- `lem:softclip-poly`, `lem:poly-sigmoid`: if `k ≥ 3T log(B/ζ)` with `B, ζ > 0` and `T ≥ 1`,
then `B ρ^{-k} ≤ ζ` for `ρ = 1 + 1/(2T)`. With `B = 4T(M_τ+2)` this is the degree of
`lem:softclip-poly`; with `B = 4T`, `ζ = η/3` it is the degree of `lem:poly-sigmoid`. -/
theorem trunc_le_of_degree {T B ζ : ℝ} (hT : 1 ≤ T) (hB : 0 < B) (hζ : 0 < ζ) {k : ℕ}
    (hk : 3 * T * Real.log (B / ζ) ≤ k) : B * (1 + 1 / (2 * T))⁻¹ ^ k ≤ ζ := by
  have hρ : 0 < 1 + 1 / (2 * T) := by positivity
  have hlog := log_rho_ge hT
  have h3 : (0 : ℝ) < 3 * T := by positivity
  have hKl : Real.log (B / ζ) ≤ k * Real.log (1 + 1 / (2 * T)) := by
    have h1 : Real.log (B / ζ) ≤ k / (3 * T) := by rw [le_div_iff₀ h3]; linarith
    have h2 : (k : ℝ) / (3 * T) ≤ k * Real.log (1 + 1 / (2 * T)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  have hpow : (1 + 1 / (2 * T))⁻¹ ^ k = Real.exp (-(k * Real.log (1 + 1 / (2 * T)))) := by
    rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), inv_pow]
  rw [hpow]
  have hexp : Real.exp (-(k * Real.log (1 + 1 / (2 * T)))) ≤ Real.exp (-Real.log (B / ζ)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg (Real.log (B / ζ)), Real.exp_log (by positivity), inv_div] at hexp
  calc B * Real.exp (-(k * Real.log (1 + 1 / (2 * T)))) ≤ B * (ζ / B) :=
        mul_le_mul_of_nonneg_left hexp hB.le
    _ = ζ := by field_simp

/-! ### `eq:smooth-parameters` and the proof of `thm:fixed`

Throughout, `T ≥ 1` (the paper assumes `T ≥ 32`, which is not needed for this arithmetic),
`0 < ε < 1/2` and `0 < δ < 1/2`. -/

section SmoothParameters

variable {T d : ℕ} {ε δ : ℝ}

/-- The argument `2 T C_q (d+1) L / (εδ)` of the logarithm defining `J`. -/
noncomputable def smoothJArg (T d : ℕ) (ε δ : ℝ) : ℝ :=
  2 * T * Cq * (d + 1) * LOf T ε / (ε * δ)

theorem JOf_eq : JOf T d ε δ = ⌈Real.logb 2 (smoothJArg T d ε δ)⌉₊ + 10 := rfl

theorem Cq_eq : (Cq : ℝ) = 52 := by norm_num [Cq]

theorem two_pow_bTau_ge (hT : 1 ≤ T) (hε0 : 0 < ε) : 8 * T / ε ≤ (2 : ℝ) ^ bTau T ε := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  exact le_two_pow_ceil_logb (by positivity)

theorem two_pow_bTau_lt (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (2 : ℝ) ^ bTau T ε < 16 * T / ε := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hx : 1 ≤ 8 * (T : ℝ) / ε := by
    rw [le_div_iff₀ hε0]; nlinarith
  have := two_pow_ceil_logb_lt hx
  unfold bTau
  calc (2 : ℝ) ^ ⌈Real.logb 2 (8 * T / ε)⌉₊ < 2 * (8 * T / ε) := this
    _ = 16 * T / ε := by ring

/-- `sec:fixed-rank`: `τ = 2^{-⌈log₂(8T/ε)⌉}` satisfies `ε/(16T) ≤ τ ≤ ε/(8T)` (the lower bound
is even strict), `τ ∈ (0, 1/2)`, the floor `τ/2 ≥ ε/(32T)`, and `Tτ/2 ≤ ε/16`
(the bound used with `eq:smoothing-tv`). -/
theorem tauOf_bounds (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ε / (16 * T) < tauOf T ε ∧ ε / (16 * T) ≤ tauOf T ε ∧ tauOf T ε ≤ ε / (8 * T) ∧
      0 < tauOf T ε ∧ tauOf T ε < 1 / 2 ∧ ε / (32 * T) ≤ tauOf T ε / 2 ∧
      T * tauOf T ε / 2 ≤ ε / 16 := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hge := two_pow_bTau_ge hT hε0
  have hlt := two_pow_bTau_lt hT hε0 hε1
  have hP : 0 < (2 : ℝ) ^ bTau T ε := by positivity
  have hτ : tauOf T ε = ((2 : ℝ) ^ bTau T ε)⁻¹ := rfl
  have h1 : ε / (16 * T) < tauOf T ε := by
    rw [hτ, div_lt_iff₀ (by positivity)]
    rw [lt_div_iff₀ hε0] at hlt
    rw [← div_eq_inv_mul, lt_div_iff₀ hP]
    linarith
  have h2 : tauOf T ε ≤ ε / (8 * T) := by
    rw [hτ, le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hε0] at hge
    rw [← div_eq_inv_mul, div_le_iff₀ hP]
    linarith
  have h3 : 0 < tauOf T ε := by rw [hτ]; positivity
  have h4 : ε / (8 * T) < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  refine ⟨h1, h1.le, h2, h3, by linarith, ?_, ?_⟩
  · have : ε / (32 * T) = ε / (16 * T) / 2 := by field_simp; ring
    rw [this]; linarith
  · have : (T : ℝ) * (ε / (8 * T)) = ε / 8 := by field_simp
    nlinarith

/-- `L = ⌈log₂(4/τ)⌉ + 3 = b_τ + 5`. -/
theorem LOf_eq (T : ℕ) (ε : ℝ) : LOf T ε = bTau T ε + 5 := by
  have h : 4 / tauOf T ε = (2 : ℝ) ^ (bTau T ε + 2) := by
    unfold tauOf
    rw [div_inv_eq_mul, pow_add]
    norm_num
    ring
  unfold LOf
  rw [h, logb_two_pow, Nat.ceil_natCast]

/-- `M_τ ≥ 0` for `0 < τ ≤ 1`. -/
theorem softclipBound_nonneg {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) : 0 ≤ softclipBound τ := by
  unfold softclipBound
  have : 1 ≤ (2 - τ) / τ := by rw [le_div_iff₀ hτ0]; linarith
  have := Real.log_nonneg this
  linarith

/-- `M_τ < b_τ + 1` for `τ = 2^{-b_τ}`. -/
theorem softclipBound_tauOf_lt (T : ℕ) (ε : ℝ) :
    softclipBound (tauOf T ε) < bTau T ε + 1 := by
  set b := bTau T ε
  have hτ : tauOf T ε = ((2 : ℝ) ^ b)⁻¹ := rfl
  have hτ0 : 0 < tauOf T ε := by rw [hτ]; positivity
  have hle : (2 - tauOf T ε) / tauOf T ε ≤ (2 : ℝ) ^ (b + 1) := by
    rw [div_le_iff₀ hτ0, hτ, pow_succ]
    have : (2 : ℝ) ^ b * 2 * ((2 : ℝ) ^ b)⁻¹ = 2 := by field_simp
    have : 0 < ((2 : ℝ) ^ b)⁻¹ := by positivity
    nlinarith
  have hpos : 0 < (2 - tauOf T ε) / tauOf T ε := by
    apply div_pos _ hτ0
    have : tauOf T ε ≤ 1 := by rw [hτ]; exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
    linarith
  have h1 := Real.log_le_log hpos hle
  rw [Real.log_pow] at h1
  unfold softclipBound
  have h2 := log_two_lt_one
  have h3 : (0 : ℝ) ≤ (b : ℝ) + 1 := by positivity
  push_cast at h1
  nlinarith

/-- Proof of `thm:fixed`: "The integer `L` exceeds `M_τ + 2`." -/
theorem softclipBound_add_two_lt_LOf (T : ℕ) (ε : ℝ) :
    softclipBound (tauOf T ε) + 2 < LOf T ε := by
  rw [LOf_eq]
  have := softclipBound_tauOf_lt T ε
  push_cast
  linarith

theorem one_le_LOf (T : ℕ) (ε : ℝ) : 1 ≤ LOf T ε := by
  rw [LOf_eq]; omega

theorem one_le_JOf : 1 ≤ JOf T d ε δ := by
  unfold JOf; omega

/-- `1024 X ≤ 2^J`, where `X` is the argument of the logarithm defining `J`. -/
theorem smoothJArg_le (hε0 : 0 < ε) (hδ0 : 0 < δ) :
    1024 * smoothJArg T d ε δ ≤ (2 : ℝ) ^ JOf T d ε δ := by
  have hL : (1 : ℝ) ≤ LOf T ε := by exact_mod_cast one_le_LOf T ε
  rcases Nat.eq_zero_or_pos T with hT | hT
  · have : smoothJArg T d ε δ = 0 := by simp [smoothJArg, hT]
    rw [this, mul_zero]; positivity
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hX : 0 < smoothJArg T d ε δ := by unfold smoothJArg; rw [Cq_eq]; positivity
  have h := le_two_pow_ceil_logb hX
  rw [JOf_eq, pow_add]
  norm_num
  linarith

theorem eps_mul_delta_le (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ1 : δ < 1 / 2) :
    ε * δ ≤ 1 / 4 := by nlinarith

/-- Lower bounds on `X = 2 T C_q (d+1) L / (εδ)` used below. -/
theorem smoothJArg_lower (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    4 * T * LOf T ε ≤ smoothJArg T d ε δ ∧
      8 * (Cq * (d + 1) * T) ≤ smoothJArg T d ε δ ∧
      2 * T * LOf T ε / (ε * δ) ≤ smoothJArg T d ε δ ∧
      T / δ ≤ smoothJArg T d ε δ ∧ T / ε ≤ smoothJArg T d ε δ := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hL : (1 : ℝ) ≤ LOf T ε := by exact_mod_cast one_le_LOf T ε
  have hd : (0 : ℝ) ≤ d := by positivity
  have hεδ := eps_mul_delta_le hε0 hε1 hδ1
  have hεδ0 : 0 < ε * δ := mul_pos hε0 hδ0
  unfold smoothJArg
  rw [Cq_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hεδ0]
    have : 0 ≤ (T : ℝ) * LOf T ε := by positivity
    nlinarith
  · rw [le_div_iff₀ hεδ0]
    have : 0 ≤ 52 * ((d : ℝ) + 1) * T := by positivity
    nlinarith
  · apply div_le_div_of_nonneg_right _ hεδ0.le
    have : 0 ≤ 2 * (T : ℝ) * LOf T ε := by positivity
    nlinarith
  · have e : 2 * (T : ℝ) * 52 * (d + 1) * LOf T ε / (ε * δ) =
        T / δ * (104 * (d + 1) * LOf T ε / ε) := by field_simp; ring
    rw [e]
    apply le_mul_of_one_le_right (by positivity)
    rw [le_div_iff₀ hε0]; nlinarith
  · have e : 2 * (T : ℝ) * 52 * (d + 1) * LOf T ε / (ε * δ) =
        T / ε * (104 * (d + 1) * LOf T ε / δ) := by field_simp; ring
    rw [e]
    apply le_mul_of_one_le_right (by positivity)
    rw [le_div_iff₀ hδ0]; nlinarith

/-- Proof of `thm:fixed`: `log(4T(M_τ+2)) ≤ J ≤ N`. -/
theorem log_le_JOf_le_NOf (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    Real.log (4 * T * (softclipBound (tauOf T ε) + 2)) ≤ JOf T d ε δ ∧
      JOf T d ε δ ≤ NOf T d ε δ := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨-, -, -, hτ0, hτ1, -, -⟩ := tauOf_bounds hT hε0 hε1
  have hM := softclipBound_nonneg hτ0 (by linarith)
  have hML := softclipBound_add_two_lt_LOf T ε
  have hX := (smoothJArg_lower (d := d) hT hε0 hε1 hδ0 hδ1).1
  have h4 : 1 ≤ 4 * (T : ℝ) * (softclipBound (tauOf T ε) + 2) := by nlinarith
  have h5 : 4 * (T : ℝ) * (softclipBound (tauOf T ε) + 2) ≤ smoothJArg T d ε δ := by
    nlinarith
  constructor
  · calc Real.log (4 * T * (softclipBound (tauOf T ε) + 2))
        ≤ Real.log (smoothJArg T d ε δ) := Real.log_le_log (by linarith) h5
      _ ≤ Real.logb 2 (smoothJArg T d ε δ) := log_le_logb_two (by linarith)
      _ ≤ ⌈Real.logb 2 (smoothJArg T d ε δ)⌉₊ := Nat.le_ceil _
      _ ≤ JOf T d ε δ := by rw [JOf_eq]; push_cast; linarith
  · exact Nat.le_mul_of_pos_left _ (by unfold Cq; positivity)

theorem kOf_eq : kOf T d ε δ = 800 * Cq * (d + 1) * T * JOf T d ε δ := by
  unfold kOf NOf; ring

/-- Proof of `thm:fixed`: the degree `⌈3T log(4T(M_τ+2)/ζ)⌉` of `lem:softclip-poly` is at most
`k = 8TN`. -/
theorem softclip_degree_le_kOf (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    ⌈3 * T * Real.log (4 * T * (softclipBound (tauOf T ε) + 2) / zetaOf T d ε δ)⌉₊ ≤
      kOf T d ε δ := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨-, -, -, hτ0, hτ1, -, -⟩ := tauOf_bounds hT hε0 hε1
  have hM := softclipBound_nonneg hτ0 (by linarith)
  obtain ⟨hJ, hJN⟩ := log_le_JOf_le_NOf (d := d) hT hε0 hε1 hδ0 hδ1
  have hpos : 0 < 4 * (T : ℝ) * (softclipBound (tauOf T ε) + 2) := by positivity
  have hlog : Real.log (4 * T * (softclipBound (tauOf T ε) + 2) / zetaOf T d ε δ) =
      Real.log (4 * T * (softclipBound (tauOf T ε) + 2)) + NOf T d ε δ * Real.log 2 := by
    unfold zetaOf
    rw [div_inv_eq_mul, Real.log_mul hpos.ne' (by positivity), Real.log_pow]
  rw [Nat.ceil_le, hlog]
  have hJN' : (JOf T d ε δ : ℝ) ≤ NOf T d ε δ := by exact_mod_cast hJN
  have h2 := log_two_lt_one
  have hN0 : (0 : ℝ) ≤ NOf T d ε δ := by positivity
  have : Real.log (4 * T * (softclipBound (tauOf T ε) + 2)) + NOf T d ε δ * Real.log 2 ≤
      2 * NOf T d ε δ := by nlinarith
  unfold kOf
  push_cast
  have hT0 : (0 : ℝ) ≤ 3 * T := by positivity
  nlinarith

/-- Proof of `thm:fixed`: `D ≤ (d + 800 C_q (d+1) T J)^d ≤ (801 C_q (d+1) T J)^d`. -/
theorem DOf_le (hT : 1 ≤ T) :
    DOf T d ε δ ≤ (d + 800 * Cq * (d + 1) * T * JOf T d ε δ) ^ d ∧
      (d + 800 * Cq * (d + 1) * T * JOf T d ε δ) ^ d ≤
        (801 * Cq * (d + 1) * T * JOf T d ε δ) ^ d := by
  constructor
  · unfold DOf
    rw [← kOf_eq]
    exact Nat.choose_le_pow _ _
  · apply Nat.pow_le_pow_left
    have hJ := one_le_JOf (T := T) (d := d) (ε := ε) (δ := δ)
    have h1 : 1 ≤ Cq * T * JOf T d ε δ := by
      have : 1 ≤ Cq := by norm_num [Cq]
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith

/-- Proof of `thm:fixed`:
`log₂ C_q + log₂ (d+1) + log₂ T + log₂ L + log₂ (1/ε) + log₂ (1/δ) ≤ J - 11`. -/
theorem logb_sum_le_JOf (hT : 1 ≤ T) (hε0 : 0 < ε) (hδ0 : 0 < δ) :
    Real.logb 2 Cq + Real.logb 2 (d + 1) + Real.logb 2 T + Real.logb 2 (LOf T ε) +
        Real.logb 2 (1 / ε) + Real.logb 2 (1 / δ) ≤ (JOf T d ε δ : ℝ) - 11 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hL : (0 : ℝ) < LOf T ε := by exact_mod_cast one_le_LOf T ε
  have hC : (0 : ℝ) < Cq := by rw [Cq_eq]; norm_num
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hsum : Real.logb 2 (smoothJArg T d ε δ) = 1 + (Real.logb 2 Cq + Real.logb 2 (d + 1) +
      Real.logb 2 T + Real.logb 2 (LOf T ε) + Real.logb 2 (1 / ε) + Real.logb 2 (1 / δ)) := by
    unfold smoothJArg
    rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul hε0.ne' hδ0.ne',
      Real.logb_mul (by positivity) hL.ne', Real.logb_mul (by positivity) hd.ne',
      Real.logb_mul (by positivity) hC.ne', Real.logb_mul two_ne_zero hT'.ne', logb_two_two,
      one_div, one_div, Real.logb_inv, Real.logb_inv]
    ring
  have hceil := Nat.le_ceil (Real.logb 2 (smoothJArg T d ε δ))
  rw [JOf_eq]
  push_cast
  linarith

/-- `(801 C_q (d+1) T J) ≤ 2^{3J}`. -/
theorem base_le_two_pow (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    ((801 * Cq * (d + 1) * T * JOf T d ε δ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (3 * JOf T d ε δ) := by
  have hX := smoothJArg_le (T := T) (d := d) hε0 hδ0
  have hlow := (smoothJArg_lower (d := d) hT hε0 hε1 hδ0 hδ1).2.1
  have hJ := natCast_le_two_pow (JOf T d ε δ)
  have hJ0 : (0 : ℝ) ≤ JOf T d ε δ := by positivity
  have hP : (1 : ℝ) ≤ (2 : ℝ) ^ JOf T d ε δ := one_le_pow₀ one_le_two
  have hc : (0 : ℝ) ≤ Cq * (d + 1) * T := by positivity
  have h1 : 801 * (Cq * (d + 1) * T : ℝ) ≤ (2 : ℝ) ^ JOf T d ε δ := by linarith
  have e : (2 : ℝ) ^ (3 * JOf T d ε δ) =
      (2 : ℝ) ^ JOf T d ε δ * (2 : ℝ) ^ JOf T d ε δ * (2 : ℝ) ^ JOf T d ε δ := by
    rw [show 3 * JOf T d ε δ = JOf T d ε δ + JOf T d ε δ + JOf T d ε δ by ring, pow_add,
      pow_add]
  rw [e]
  push_cast
  calc 801 * (Cq : ℝ) * (d + 1) * T * JOf T d ε δ
      = (801 * (Cq * (d + 1) * T)) * JOf T d ε δ := by ring
    _ ≤ (2 : ℝ) ^ JOf T d ε δ * (2 : ℝ) ^ JOf T d ε δ :=
        mul_le_mul h1 hJ hJ0 (by positivity)
    _ ≤ (2 : ℝ) ^ JOf T d ε δ * (2 : ℝ) ^ JOf T d ε δ * (2 : ℝ) ^ JOf T d ε δ := by
        have : (0 : ℝ) ≤ (2 : ℝ) ^ JOf T d ε δ * (2 : ℝ) ^ JOf T d ε δ := by positivity
        nlinarith

/-- Proof of `thm:fixed`: `D ≤ 2^{3dJ}`, i.e. `log₂ D ≤ 3dJ`. -/
theorem DOf_le_two_pow (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    (DOf T d ε δ : ℝ) ≤ (2 : ℝ) ^ (3 * d * JOf T d ε δ) := by
  obtain ⟨h1, h2⟩ := DOf_le (d := d) (ε := ε) (δ := δ) hT
  have h3 : (DOf T d ε δ : ℝ) ≤ ((801 * Cq * (d + 1) * T * JOf T d ε δ : ℕ) : ℝ) ^ d := by
    exact_mod_cast h1.trans h2
  have h4 := base_le_two_pow (d := d) hT hε0 hε1 hδ0 hδ1
  calc (DOf T d ε δ : ℝ) ≤ ((801 * Cq * (d + 1) * T * JOf T d ε δ : ℕ) : ℝ) ^ d := h3
    _ ≤ ((2 : ℝ) ^ (3 * JOf T d ε δ)) ^ d := pow_le_pow_left₀ (by positivity) h4 d
    _ = (2 : ℝ) ^ (3 * d * JOf T d ε δ) := by rw [← pow_mul]; ring_nf

theorem DOf_pos : 0 < DOf T d ε δ := Nat.choose_pos (by omega)

/-- Proof of `thm:fixed`: `log₂ D ≤ 3dJ`. -/
theorem logb_DOf_le (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    Real.logb 2 (DOf T d ε δ) ≤ 3 * d * JOf T d ε δ := by
  have := logb_le_of_le_two_pow (by exact_mod_cast DOf_pos (T := T) (d := d) (ε := ε) (δ := δ))
    (DOf_le_two_pow hT hε0 hε1 hδ0 hδ1)
  push_cast at this
  exact this

/-- `V ≤ 2^{(3d+1)J}` and `1 ≤ V`. -/
theorem VOf_le_two_pow (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    VOf T d ε δ ≤ (2 : ℝ) ^ ((3 * d + 1) * JOf T d ε δ) ∧ 1 ≤ VOf T d ε δ := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hL : (1 : ℝ) ≤ LOf T ε := by exact_mod_cast one_le_LOf T ε
  have hD := DOf_le_two_pow (d := d) hT hε0 hε1 hδ0 hδ1
  have hD1 : (1 : ℝ) ≤ DOf T d ε δ := by
    exact_mod_cast (DOf_pos (T := T) (d := d) (ε := ε) (δ := δ))
  have hX := smoothJArg_le (T := T) (d := d) hε0 hδ0
  have hlow := (smoothJArg_lower (d := d) hT hε0 hε1 hδ0 hδ1).2.2.1
  have hεδ := eps_mul_delta_le hε0 hε1 hδ1
  have hεδ0 : 0 < ε * δ := mul_pos hε0 hδ0
  have hV : VOf T d ε δ = (2 * T * LOf T ε / (ε * δ)) * DOf T d ε δ := by
    unfold VOf; ring
  have hA0 : 0 ≤ 2 * (T : ℝ) * LOf T ε / (ε * δ) := by positivity
  have hA1 : 2 * (T : ℝ) * LOf T ε / (ε * δ) ≤ (2 : ℝ) ^ JOf T d ε δ := by
    have : 0 ≤ smoothJArg T d ε δ := by unfold smoothJArg; rw [Cq_eq]; positivity
    linarith
  have hA2 : 1 ≤ 2 * (T : ℝ) * LOf T ε / (ε * δ) := by
    rw [le_div_iff₀ hεδ0]; nlinarith
  constructor
  · rw [hV, show (3 * d + 1) * JOf T d ε δ = JOf T d ε δ + 3 * d * JOf T d ε δ by ring, pow_add]
    exact mul_le_mul hA1 hD (by positivity) (by positivity)
  · rw [hV]; nlinarith

/-- Proof of `thm:fixed`: `log₂ V ≤ (3d+1) J`. -/
theorem logb_VOf_le (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    Real.logb 2 (VOf T d ε δ) ≤ (3 * d + 1) * JOf T d ε δ := by
  obtain ⟨h1, h2⟩ := VOf_le_two_pow (d := d) hT hε0 hε1 hδ0 hδ1
  have := logb_le_of_le_two_pow (by linarith) h1
  push_cast at this
  exact this

/-- Proof of `thm:fixed`: the inequality `N > C_q log₂ V + 1` used for `ζ ≤ ξ/2`. -/
theorem Cq_logb_VOf_add_one_lt (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    (Cq : ℝ) * Real.logb 2 (VOf T d ε δ) + 1 < NOf T d ε δ := by
  have h := logb_VOf_le (d := d) hT hε0 hε1 hδ0 hδ1
  have hJ : (1 : ℝ) ≤ JOf T d ε δ := by exact_mod_cast one_le_JOf
  have hd : (0 : ℝ) ≤ d := by positivity
  unfold NOf
  push_cast
  rw [Cq_eq]
  nlinarith

theorem budget_exp_le₁ (d J : ℕ) (hJ : 1 ≤ J) :
    Cq * ((3 * d + 1) * J) + 1 ≤ 100 * Cq * (d + 1) * J := by
  simp only [Cq]; nlinarith

theorem budget_exp_le₂ (d J : ℕ) (hJ : 1 ≤ J) :
    2 + 22 * ((3 * d + 1) * J) + J ≤ 100 * Cq * (d + 1) * J := by
  simp only [Cq]; nlinarith

/-- `ζ ≤ 2^{-M}` whenever `M ≤ N`; more precisely `x ≤ 2^M` and `M ≤ N` give `x ζ ≤ 1`. -/
theorem mul_zetaOf_le_one {x : ℝ} {M : ℕ} (hx : x ≤ (2 : ℝ) ^ M) (hM : M ≤ NOf T d ε δ) :
    x * zetaOf T d ε δ ≤ 1 := by
  unfold zetaOf
  rw [← div_eq_mul_inv, div_le_one (by positivity)]
  exact hx.trans (pow_le_pow_right₀ one_le_two hM)

/-- `eq:smooth-budget`. Let `ξ > 0` and `R_s` satisfy `R_s ≤ V^22` and `ξ⁻¹ ≤ V^{C_q}`
(the paper's sentence uses `ξ⁻¹ ≤ V^{C_q}`; `lem:explicit-gls-token-envelope` supplies the
stronger `ξ⁻¹ ≤ V^11`, see `smooth_budget_of_envelope`). Then
`ζ ≤ ξ/2`, `R_s T ζ ≤ δ/4` and `T ζ ≤ ε/8`. -/
theorem smooth_budget (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {Rs ξ : ℝ} (hRs : Rs ≤ VOf T d ε δ ^ 22) (hξ0 : 0 < ξ)
    (hξ : ξ⁻¹ ≤ VOf T d ε δ ^ Cq) :
    zetaOf T d ε δ ≤ ξ / 2 ∧ Rs * T * zetaOf T d ε δ ≤ δ / 4 ∧
      T * zetaOf T d ε δ ≤ ε / 8 := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨hV, hV1⟩ := VOf_le_two_pow (d := d) hT hε0 hε1 hδ0 hδ1
  have hX := smoothJArg_le (T := T) (d := d) hε0 hδ0
  obtain ⟨-, -, -, hXδ, hXε⟩ := smoothJArg_lower (d := d) hT hε0 hε1 hδ0 hδ1
  set J := JOf T d ε δ
  set V := VOf T d ε δ
  have hJ : 1 ≤ J := one_le_JOf
  have hζ0 : 0 < zetaOf T d ε δ := by unfold zetaOf; positivity
  have hN : NOf T d ε δ = 100 * Cq * (d + 1) * J := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- `2 ξ⁻¹ ≤ 2 V^{C_q} ≤ 2^{C_q (3d+1) J + 1} ≤ 2^N`
    have h1 : 2 * ξ⁻¹ ≤ (2 : ℝ) ^ (Cq * ((3 * d + 1) * J) + 1) := by
      rw [pow_succ, pow_mul']
      have : V ^ Cq ≤ ((2 : ℝ) ^ ((3 * d + 1) * J)) ^ Cq :=
        pow_le_pow_left₀ (by linarith) hV Cq
      linarith
    have h2 : Cq * ((3 * d + 1) * J) + 1 ≤ NOf T d ε δ := by
      rw [hN]; exact budget_exp_le₁ d J hJ
    have := mul_zetaOf_le_one h1 h2
    rw [inv_eq_one_div] at this
    have e : 2 * (1 / ξ) * zetaOf T d ε δ = (2 * zetaOf T d ε δ) / ξ := by ring
    rw [e, div_le_one hξ0] at this
    linarith
  · -- `4 R_s (T/δ) ≤ 4 V^22 2^J ≤ 2^N`
    have hTδ : (T : ℝ) / δ ≤ (2 : ℝ) ^ J := by
      have : 0 ≤ smoothJArg T d ε δ := by unfold smoothJArg; rw [Cq_eq]; positivity
      linarith
    have h1 : 4 * Rs * (T / δ) ≤ (2 : ℝ) ^ (2 + 22 * ((3 * d + 1) * J) + J) := by
      have hV22 : V ^ 22 ≤ ((2 : ℝ) ^ ((3 * d + 1) * J)) ^ 22 :=
        pow_le_pow_left₀ (by linarith) hV 22
      have : Rs * (T / δ) ≤ ((2 : ℝ) ^ ((3 * d + 1) * J)) ^ 22 * (2 : ℝ) ^ J :=
        mul_le_mul (hRs.trans hV22) hTδ (by positivity) (by positivity)
      calc 4 * Rs * (T / δ) = 4 * (Rs * (T / δ)) := by ring
        _ ≤ 4 * (((2 : ℝ) ^ ((3 * d + 1) * J)) ^ 22 * (2 : ℝ) ^ J) := by linarith
        _ = (2 : ℝ) ^ (2 + 22 * ((3 * d + 1) * J) + J) := by
          rw [pow_add, pow_add, pow_mul]; ring
    have h2 : 2 + 22 * ((3 * d + 1) * J) + J ≤ NOf T d ε δ := by
      rw [hN]; exact budget_exp_le₂ d J hJ
    have := mul_zetaOf_le_one h1 h2
    have e : 4 * Rs * (T / δ) * zetaOf T d ε δ = 4 * (Rs * T * zetaOf T d ε δ) / δ := by
      field_simp
    rw [e, div_le_one hδ0] at this
    linarith
  · have hTε : 8 * ((T : ℝ) / ε) ≤ (2 : ℝ) ^ J := by
      have : 0 ≤ smoothJArg T d ε δ := by unfold smoothJArg; rw [Cq_eq]; positivity
      linarith
    have h2 : J ≤ NOf T d ε δ := (log_le_JOf_le_NOf hT hε0 hε1 hδ0 hδ1).2
    have := mul_zetaOf_le_one hTε h2
    have e : 8 * ((T : ℝ) / ε) * zetaOf T d ε δ = 8 * (T * zetaOf T d ε δ) / ε := by
      field_simp
    rw [e, div_le_one hε0] at this
    linarith

/-- `eq:smooth-budget` with the bounds `R_ℓ + R_s ≤ V^22`, `ξ⁻¹ ≤ V^11` that
`lem:explicit-gls-token-envelope` supplies (taken here as hypotheses). -/
theorem smooth_budget_of_envelope (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {Rl Rs ξ : ℝ} (hRl0 : 0 ≤ Rl)
    (hR : Rl + Rs ≤ VOf T d ε δ ^ 22) (hξ0 : 0 < ξ) (hξ : ξ⁻¹ ≤ VOf T d ε δ ^ 11) :
    zetaOf T d ε δ ≤ ξ / 2 ∧ Rs * T * zetaOf T d ε δ ≤ δ / 4 ∧
      T * zetaOf T d ε δ ≤ ε / 8 := by
  have hV1 := (VOf_le_two_pow (d := d) hT hε0 hε1 hδ0 hδ1).2
  have hξ' : ξ⁻¹ ≤ VOf T d ε δ ^ Cq :=
    hξ.trans (pow_le_pow_right₀ hV1 (by norm_num [Cq]))
  exact smooth_budget hT hε0 hε1 hδ0 hδ1 (by linarith) hξ0 hξ'

/-- `eq:smooth-budget` exactly as used: `R_s ≤ V^22` and `ξ⁻¹ ≤ V^11` give `ζ ≤ ξ/2`,
`R_s T ζ ≤ δ/4` and `T ζ ≤ ε/8`. -/
theorem smooth_budget_of_V11 (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {Rs ξ : ℝ} (hRs : Rs ≤ VOf T d ε δ ^ 22) (hξ0 : 0 < ξ)
    (hξ : ξ⁻¹ ≤ VOf T d ε δ ^ 11) :
    zetaOf T d ε δ ≤ ξ / 2 ∧ Rs * T * zetaOf T d ε δ ≤ δ / 4 ∧
      T * zetaOf T d ε δ ≤ ε / 8 :=
  smooth_budget_of_envelope hT hε0 hε1 hδ0 hδ1 le_rfl (by linarith) hξ0 hξ

/-- The hypotheses standing for `lem:explicit-gls-token-envelope` in `smooth_budget_of_envelope`
are satisfiable (for instance by `R_ℓ = R_s = 0`, `ξ = 1`), so the budget statements are not
vacuous. -/
theorem envelope_hyps_satisfiable (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    ∃ Rl Rs ξ : ℝ, 0 ≤ Rl ∧ Rl + Rs ≤ VOf T d ε δ ^ 22 ∧ 0 < ξ ∧
      ξ⁻¹ ≤ VOf T d ε δ ^ 11 := by
  have hV1 := (VOf_le_two_pow (d := d) hT hε0 hε1 hδ0 hδ1).2
  refine ⟨0, 0, 1, le_rfl, ?_, one_pos, ?_⟩
  · simp only [add_zero]; positivity
  · rw [inv_one]; exact one_le_pow₀ hV1

/-- Proof of `thm:fixed`, TV ledger: `ε/16 + ε/8 + ε/2 < ε`. -/
theorem tv_ledger (hε0 : 0 < ε) : ε / 16 + ε / 8 + ε / 2 < ε := by linarith

/-- Proof of `thm:fixed`, the TV chain: with `TV(P,P^τ) ≤ Tτ/2`, `TV(P^τ,P°) ≤ Tζ` and
`TV(P°,Q) ≤ ε/2` (supplied by `eq:smoothing-tv`, `eq:smoothed-polynomial-tv` and
`lem:explicit-gls-token-envelope`, taken as hypotheses) the triangle inequality gives
`TV(P,Q) < ε`. -/
theorem tv_chain (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    {Rl Rs ξ : ℝ} (hRl0 : 0 ≤ Rl)
    (hR : Rl + Rs ≤ VOf T d ε δ ^ 22) (hξ0 : 0 < ξ) (hξ : ξ⁻¹ ≤ VOf T d ε δ ^ 11)
    {a b c tvPQ : ℝ} (ha : a ≤ T * tauOf T ε / 2) (hb : b ≤ T * zetaOf T d ε δ)
    (hc : c ≤ ε / 2) (htri : tvPQ ≤ a + b + c) : tvPQ < ε := by
  have h1 := (tauOf_bounds hT hε0 hε1).2.2.2.2.2.2
  have h2 := (smooth_budget_of_envelope hT hε0 hε1 hδ0 hδ1 hRl0 hR hξ0 hξ).2.2
  linarith

/-- Proof of `thm:fixed`, failure ledger: `δ/4 + R_s T ζ ≤ δ/2`. -/
theorem failure_ledger (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {Rl Rs ξ : ℝ} (hRl0 : 0 ≤ Rl)
    (hR : Rl + Rs ≤ VOf T d ε δ ^ 22) (hξ0 : 0 < ξ) (hξ : ξ⁻¹ ≤ VOf T d ε δ ^ 11) :
    δ / 4 + Rs * T * zetaOf T d ε δ ≤ δ / 2 ∧ δ / 4 + δ / 2 = 3 * δ / 4 := by
  have h := (smooth_budget_of_envelope hT hε0 hε1 hδ0 hδ1 hRl0 hR hξ0 hξ).2.1
  constructor <;> linarith

/-- Proof of `thm:fixed`: an oracle answer within `ξ/2` of `ℓ_{P^τ}(h) = ψ_τ(ℓ_P(h))` is within
`ξ` of `ℓ_{P°}(h) = r(ℓ_P(h))` once `|r - ψ_τ| ≤ ζ ≤ ξ/2`. -/
theorem oracle_transfer {A r ψ ζ ξ : ℝ} (hA : |A - ψ| ≤ ξ / 2) (hr : |r - ψ| ≤ ζ)
    (hζ : ζ ≤ ξ / 2) : |A - r| ≤ ξ := by
  have : A - r = (A - ψ) - (r - ψ) := by ring
  rw [this]
  calc |(A - ψ) - (r - ψ)| ≤ |A - ψ| + |r - ψ| := abs_sub _ _
    _ ≤ ξ := by linarith

/-- Proof of `thm:fixed` with `lem:logit-lift`: the logits of `P°` (within `ζ ≤ 1` of `ψ_τ`) have
magnitude at most the integer `L`. -/
theorem abs_le_LOf (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {ζ r u : ℝ} (hζ : ζ ≤ 1)
    (hr : |r - softclip (tauOf T ε) u| ≤ ζ) : |r| ≤ LOf T ε := by
  obtain ⟨-, -, -, hτ0, hτ1, -, -⟩ := tauOf_bounds hT hε0 hε1
  have h1 := abs_le_softclipBound_add hτ0 (by linarith) hr
  have h2 := softclipBound_add_two_lt_LOf T ε
  linarith

end SmoothParameters

/-! ### `eq:fixed-parameters` and `eq:combined-budget` (`sec:probability-route`)

`C ≥ 2` is the universal exponent bounding the implemented Liu–Moitra learner by
`(2TR/a)^C`, and `a = min{ε, δ}/4`. The parameter functions take `a` as an argument; the
statements assume `0 < a ≤ 1`, which holds for `a = min{ε, δ}/4` with `ε, δ ∈ (0, 1/2)`. -/

section ProbabilityRoute

/-- `a = min{ε, δ}/4`. -/
noncomputable def aOf (ε δ : ℝ) : ℝ := min ε δ / 4

/-- The argument `2TC(d+1)/a` of the logarithm defining `J` in `eq:fixed-parameters`. -/
noncomputable def prJArg (T d C : ℕ) (a : ℝ) : ℝ := 2 * T * C * (d + 1) / a

/-- `J = ⌈log₂(2TC(d+1)/a)⌉ + 10`. -/
noncomputable def prJ (T d C : ℕ) (a : ℝ) : ℕ := ⌈Real.logb 2 (prJArg T d C a)⌉₊ + 10

/-- `N = 100 C (d+1) J`. -/
noncomputable def prN (T d C : ℕ) (a : ℝ) : ℕ := 100 * C * (d + 1) * prJ T d C a

/-- `η = 2^{-N}`. -/
noncomputable def prEta (T d C : ℕ) (a : ℝ) : ℝ := ((2 : ℝ) ^ prN T d C a)⁻¹

/-- `k = 8TN`. -/
noncomputable def prK (T d C : ℕ) (a : ℝ) : ℕ := 8 * T * prN T d C a

/-- `R = binom(d + Tk, d)`. -/
noncomputable def prR (T d C : ℕ) (a : ℝ) : ℕ := Nat.choose (d + T * prK T d C a) d

variable {T d C : ℕ} {a : ℝ}

theorem one_le_prJ : 1 ≤ prJ T d C a := by unfold prJ; omega

theorem prJArg_le (ha0 : 0 < a) : 1024 * prJArg T d C a ≤ (2 : ℝ) ^ prJ T d C a := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · have : prJArg T d C a = 0 := by simp [prJArg, hT]
    rw [this, mul_zero]; positivity
  rcases Nat.eq_zero_or_pos C with hC | hC
  · have : prJArg T d C a = 0 := by simp [prJArg, hC]
    rw [this, mul_zero]; positivity
  have hX : 0 < prJArg T d C a := by unfold prJArg; positivity
  have h := le_two_pow_ceil_logb hX
  unfold prJ
  rw [pow_add]
  norm_num
  linarith

/-- Lower bounds on `X = 2TC(d+1)/a`. -/
theorem prJArg_lower (hT : 1 ≤ T) (hd : 1 ≤ d) (hC : 2 ≤ C) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    8 * (T : ℝ) ≤ prJArg T d C a ∧ 2 * ((C : ℝ) * (d + 1) * T) ≤ prJArg T d C a ∧
      4 * (2 * T / a) ≤ prJArg T d C a ∧ 8 * (T / a) ≤ prJArg T d C a := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  unfold prJArg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha0]
    have : (0 : ℝ) ≤ T * C := by positivity
    have h1 : 4 ≤ (C : ℝ) * (d + 1) := by nlinarith
    nlinarith
  · rw [le_div_iff₀ ha0]
    have : (0 : ℝ) ≤ T * C * (d + 1) := by positivity
    nlinarith
  · have e : 2 * (T : ℝ) * C * (d + 1) / a = (2 * T / a) * (C * (d + 1)) := by
      field_simp
    rw [e, mul_comm (4 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  · have e : 2 * (T : ℝ) * C * (d + 1) / a = (T / a) * (2 * C * (d + 1)) := by
      field_simp
    rw [e, mul_comm (8 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith

/-- `sec:probability-route`: `log₂ C + log₂(d+1) + log₂ T + log₂(1/a) ≤ J - 11`. -/
theorem pr_logb_sum_le (hT : 1 ≤ T) (hC : 2 ≤ C) (ha0 : 0 < a) :
    Real.logb 2 C + Real.logb 2 (d + 1) + Real.logb 2 T + Real.logb 2 (1 / a) ≤
      (prJ T d C a : ℝ) - 11 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hC' : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hsum : Real.logb 2 (prJArg T d C a) = 1 + (Real.logb 2 C + Real.logb 2 (d + 1) +
      Real.logb 2 T + Real.logb 2 (1 / a)) := by
    unfold prJArg
    rw [Real.logb_div (by positivity) ha0.ne', Real.logb_mul (by positivity) hd.ne',
      Real.logb_mul (by positivity) hC'.ne', Real.logb_mul two_ne_zero hT'.ne', logb_two_two,
      one_div, Real.logb_inv]
    ring
  have hceil := Nat.le_ceil (Real.logb 2 (prJArg T d C a))
  unfold prJ
  push_cast
  linarith

/-- `sec:probability-route`: the degree of `lem:poly-sigmoid` is at most `k`, since
`3T log(12T/η) = 3T(log(12T) + N log 2) < 6TN < k`. -/
theorem pr_degree (hT : 1 ≤ T) (hd : 1 ≤ d) (hC : 2 ≤ C) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    3 * T * Real.log (12 * T / prEta T d C a) =
        3 * T * (Real.log (12 * T) + prN T d C a * Real.log 2) ∧
      3 * T * (Real.log (12 * T) + prN T d C a * Real.log 2) < 6 * T * (prN T d C a : ℝ) ∧
      6 * T * (prN T d C a : ℝ) < prK T d C a ∧
      ⌈3 * T * Real.log (12 * T / prEta T d C a)⌉₊ ≤ prK T d C a := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hJ1 : 1 ≤ prJ T d C a := one_le_prJ
  have hN1 : 1 ≤ prN T d C a := by
    unfold prN
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hN1' : (1 : ℝ) ≤ prN T d C a := by exact_mod_cast hN1
  have hJN : (prJ T d C a : ℝ) ≤ prN T d C a := by
    have : prJ T d C a ≤ prN T d C a := Nat.le_mul_of_pos_left _ (by positivity)
    exact_mod_cast this
  have e1 : 3 * T * Real.log (12 * T / prEta T d C a) =
      3 * T * (Real.log (12 * T) + prN T d C a * Real.log 2) := by
    unfold prEta
    rw [div_inv_eq_mul, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have h12 : 12 * (T : ℝ) ≤ (2 : ℝ) ^ prJ T d C a := by
    have := prJArg_le (T := T) (d := d) (C := C) ha0
    have := (prJArg_lower hT hd hC ha0 ha1).1
    linarith
  have hlog12 : Real.log (12 * T) ≤ prJ T d C a * Real.log 2 := by
    have := Real.log_le_log (by positivity) h12
    rwa [Real.log_pow] at this
  have hl2 := log_two_lt_one
  have hl2' := log_two_pos'
  have h2 : Real.log (12 * T) + prN T d C a * Real.log 2 < 2 * prN T d C a := by
    nlinarith
  have h3 : 3 * T * (Real.log (12 * T) + prN T d C a * Real.log 2) < 6 * T * (prN T d C a : ℝ) := by
    have : (0 : ℝ) < 3 * T := by positivity
    nlinarith
  have h4 : 6 * T * (prN T d C a : ℝ) < prK T d C a := by
    unfold prK; push_cast
    have : (0 : ℝ) < T * prN T d C a := by positivity
    nlinarith
  refine ⟨e1, h3, h4, ?_⟩
  rw [Nat.ceil_le, e1]
  linarith

/-- `sec:probability-route`: `R ≤ (d + 8T²N)^d ≤ (801 C (d+1) T² J)^d`. -/
theorem prR_le (hT : 1 ≤ T) (hC : 1 ≤ C) :
    prR T d C a ≤ (d + 8 * T ^ 2 * prN T d C a) ^ d ∧
      (d + 8 * T ^ 2 * prN T d C a) ^ d ≤ (801 * C * (d + 1) * T ^ 2 * prJ T d C a) ^ d := by
  constructor
  · unfold prR prK
    rw [show T * (8 * T * prN T d C a) = 8 * T ^ 2 * prN T d C a by ring]
    exact Nat.choose_le_pow _ _
  · apply Nat.pow_le_pow_left
    have hJ := one_le_prJ (T := T) (d := d) (C := C) (a := a)
    have h1 : 1 ≤ C * T ^ 2 * prJ T d C a := Nat.one_le_iff_ne_zero.mpr (by positivity)
    unfold prN
    nlinarith

/-- `801 C (d+1) T² J ≤ 2^{3J}`. -/
theorem pr_base_le_two_pow (hT : 1 ≤ T) (hd : 1 ≤ d) (hC : 2 ≤ C) (ha0 : 0 < a)
    (ha1 : a ≤ 1) :
    ((801 * C * (d + 1) * T ^ 2 * prJ T d C a : ℕ) : ℝ) ≤ (2 : ℝ) ^ (3 * prJ T d C a) := by
  have hX := prJArg_le (T := T) (d := d) (C := C) ha0
  obtain ⟨h8, h2, -, -⟩ := prJArg_lower hT hd hC ha0 ha1
  set J := prJ T d C a
  have hJ := natCast_le_two_pow J
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hP : (1 : ℝ) ≤ (2 : ℝ) ^ J := one_le_pow₀ one_le_two
  have hc : (0 : ℝ) ≤ C * (d + 1) * T := by positivity
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hA : 801 * ((C : ℝ) * (d + 1) * T) ≤ (2 : ℝ) ^ J := by linarith
  have hB : (T : ℝ) ≤ (2 : ℝ) ^ J := by linarith
  have e : (2 : ℝ) ^ (3 * J) = (2 : ℝ) ^ J * (2 : ℝ) ^ J * (2 : ℝ) ^ J := by
    rw [show 3 * J = J + J + J by ring, pow_add, pow_add]
  rw [e]
  push_cast
  calc 801 * (C : ℝ) * (d + 1) * T ^ 2 * J = (801 * (C * (d + 1) * T)) * T * J := by ring
    _ ≤ (2 : ℝ) ^ J * (2 : ℝ) ^ J * (2 : ℝ) ^ J := by
        apply mul_le_mul (mul_le_mul hA hB hT0 (by positivity)) hJ hJ0 (by positivity)

/-- `sec:probability-route`: `log₂(d + 8T²N) ≤ 3J` and `log₂ R ≤ 3dJ`. -/
theorem pr_logb_R_le (hT : 1 ≤ T) (hd : 1 ≤ d) (hC : 2 ≤ C) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    Real.logb 2 ((d + 8 * T ^ 2 * prN T d C a : ℕ) : ℝ) ≤ 3 * prJ T d C a ∧
      (prR T d C a : ℝ) ≤ (2 : ℝ) ^ (3 * d * prJ T d C a) ∧
      Real.logb 2 (prR T d C a) ≤ 3 * d * prJ T d C a := by
  obtain ⟨h1, h2⟩ := prR_le (d := d) (a := a) hT (by omega : 1 ≤ C)
  have h3 := pr_base_le_two_pow hT hd hC ha0 ha1
  have hbase : ((d + 8 * T ^ 2 * prN T d C a : ℕ) : ℝ) ≤ (2 : ℝ) ^ (3 * prJ T d C a) := by
    refine le_trans ?_ h3
    have : d + 8 * T ^ 2 * prN T d C a ≤ 801 * C * (d + 1) * T ^ 2 * prJ T d C a := by
      have hJ := one_le_prJ (T := T) (d := d) (C := C) (a := a)
      have : 1 ≤ C * T ^ 2 * prJ T d C a := Nat.one_le_iff_ne_zero.mpr (by positivity)
      unfold prN; nlinarith
    exact_mod_cast this
  have hpos : (0 : ℝ) < ((d + 8 * T ^ 2 * prN T d C a : ℕ) : ℝ) := by
    have : 0 < d + 8 * T ^ 2 * prN T d C a := by omega
    exact_mod_cast this
  have hR : (prR T d C a : ℝ) ≤ (2 : ℝ) ^ (3 * d * prJ T d C a) := by
    calc (prR T d C a : ℝ) ≤ ((d + 8 * T ^ 2 * prN T d C a : ℕ) : ℝ) ^ d := by exact_mod_cast h1
      _ ≤ ((2 : ℝ) ^ (3 * prJ T d C a)) ^ d := pow_le_pow_left₀ hpos.le hbase d
      _ = (2 : ℝ) ^ (3 * d * prJ T d C a) := by rw [← pow_mul]; ring_nf
  have hRpos : (0 : ℝ) < prR T d C a := by
    have : 0 < prR T d C a := Nat.choose_pos (by omega)
    exact_mod_cast this
  refine ⟨?_, hR, ?_⟩
  · have := logb_le_of_le_two_pow hpos hbase
    push_cast at this ⊢
    exact this
  · have := logb_le_of_le_two_pow hRpos hR
    push_cast at this
    exact this

/-- `eq:combined-budget`. For every base-query count `q ≤ (2TR/a)^C`,
`log₂((q+1)T/a) ≤ 1 + C(1 + log₂ T + 3dJ + log₂(1/a)) + log₂ T + log₂(1/a) < 3C(d+1)J < N`,
hence `(q+1) T η ≤ a`. -/
theorem pr_combined_budget (hT : 1 ≤ T) (hd : 1 ≤ d) (hC : 2 ≤ C) (ha0 : 0 < a)
    (ha1 : a ≤ 1) (q : ℕ) (hq : (q : ℝ) ≤ (2 * T * prR T d C a / a) ^ C) :
    Real.logb 2 ((q + 1) * T / a) ≤
        1 + C * (1 + Real.logb 2 T + 3 * d * prJ T d C a + Real.logb 2 (1 / a)) +
          Real.logb 2 T + Real.logb 2 (1 / a) ∧
      1 + C * (1 + Real.logb 2 T + 3 * d * prJ T d C a + Real.logb 2 (1 / a)) +
          Real.logb 2 T + Real.logb 2 (1 / a) < 3 * C * (d + 1) * prJ T d C a ∧
      (3 * C * (d + 1) * prJ T d C a : ℝ) < prN T d C a ∧
      (q + 1) * T * prEta T d C a ≤ a := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  set J := prJ T d C a
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (one_le_prJ (T := T) (d := d) (C := C) (a := a))
  obtain ⟨-, -, hlogR⟩ := pr_logb_R_le hT hd hC ha0 ha1
  have hR1 : (1 : ℝ) ≤ prR T d C a := by
    have : 0 < prR T d C a := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hY : 1 ≤ 2 * T * (prR T d C a : ℝ) / a := by
    rw [le_div_iff₀ ha0]; nlinarith
  have hYC : 1 ≤ (2 * T * (prR T d C a : ℝ) / a) ^ C := one_le_pow₀ hY
  have hq1 : (q : ℝ) + 1 ≤ 2 * (2 * T * (prR T d C a : ℝ) / a) ^ C := by linarith
  have hq0 : (0 : ℝ) < q + 1 := by positivity
  have hia : 0 < 1 / a := by positivity
  -- logarithmic identities
  have e1 : Real.logb 2 ((q + 1) * T / a) =
      Real.logb 2 (q + 1) + Real.logb 2 T + Real.logb 2 (1 / a) := by
    rw [div_eq_mul_one_div, Real.logb_mul (by positivity) hia.ne',
      Real.logb_mul hq0.ne' hT0.ne']
  have e2 : Real.logb 2 (2 * (2 * T * (prR T d C a : ℝ) / a) ^ C) =
      1 + C * (1 + Real.logb 2 T + Real.logb 2 (prR T d C a) + Real.logb 2 (1 / a)) := by
    rw [Real.logb_mul two_ne_zero (by positivity), Real.logb_pow, logb_two_two,
      div_eq_mul_one_div, Real.logb_mul (by positivity) hia.ne',
      Real.logb_mul (by positivity) (by positivity), Real.logb_mul two_ne_zero hT0.ne',
      logb_two_two]
  have hlq : Real.logb 2 (q + 1) ≤
      1 + C * (1 + Real.logb 2 T + Real.logb 2 (prR T d C a) + Real.logb 2 (1 / a)) := by
    rw [← e2]
    exact (Real.logb_le_logb one_lt_two hq0 (by positivity)).mpr hq1
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have first : Real.logb 2 ((q + 1) * T / a) ≤
      1 + C * (1 + Real.logb 2 T + 3 * d * J + Real.logb 2 (1 / a)) +
        Real.logb 2 T + Real.logb 2 (1 / a) := by
    rw [e1]
    have : (C : ℝ) * Real.logb 2 (prR T d C a) ≤ C * (3 * d * J) :=
      mul_le_mul_of_nonneg_left hlogR hC0
    nlinarith
  -- the margin in `J`
  have hsum := pr_logb_sum_le (d := d) hT hC ha0
  have hlC : 1 ≤ Real.logb 2 (C : ℝ) := by
    have := (Real.logb_le_logb one_lt_two two_pos (by linarith)).mpr hC'
    rwa [logb_two_two] at this
  have hld : 1 ≤ Real.logb 2 ((d : ℝ) + 1) := by
    have := (Real.logb_le_logb one_lt_two two_pos (by linarith)).mpr
      (show (2 : ℝ) ≤ d + 1 by linarith)
    rwa [logb_two_two] at this
  have hlT : 0 ≤ Real.logb 2 (T : ℝ) := Real.logb_nonneg one_lt_two hT'
  have hla : 0 ≤ Real.logb 2 (1 / a) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ ha0]; linarith)
  have hYJ : Real.logb 2 T + Real.logb 2 (1 / a) ≤ J - 13 := by linarith
  have second : 1 + C * (1 + Real.logb 2 T + 3 * d * J + Real.logb 2 (1 / a)) +
      Real.logb 2 T + Real.logb 2 (1 / a) < 3 * C * (d + 1) * J := by
    have h1 : (C : ℝ) * (Real.logb 2 T + Real.logb 2 (1 / a)) ≤ C * (J - 13) :=
      mul_le_mul_of_nonneg_left hYJ hC0
    have h2 : (J : ℝ) ≤ C * J := by nlinarith
    nlinarith
  have third : (3 * C * (d + 1) * J : ℝ) < prN T d C a := by
    unfold prN; push_cast
    have : (0 : ℝ) < C * (d + 1) * J := by positivity
    nlinarith
  refine ⟨first, second, third, ?_⟩
  have hlt : Real.logb 2 ((q + 1) * T / a) < prN T d C a := by linarith
  rw [Real.logb_lt_iff_lt_rpow one_lt_two (by positivity), Real.rpow_natCast] at hlt
  unfold prEta
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ ha0] at hlt
  linarith

/-- `sec:probability-route`, final ledger: with `a = min{ε, δ}/4` and `(q+1)Tη ≤ a`
(from `pr_combined_budget`), `qTη ≤ a`, `TV(P,Q) ≤ Tη + a ≤ 2a ≤ ε` and the failure
probability `a + qTη ≤ 2a ≤ δ`. -/
theorem pr_ledger {ε δ η q T' : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hq : 0 ≤ q) (hT : 0 ≤ T')
    (hη : 0 ≤ η) (hbudget : (q + 1) * T' * η ≤ aOf ε δ) :
    q * T' * η ≤ aOf ε δ ∧ T' * η + aOf ε δ ≤ 2 * aOf ε δ ∧ 2 * aOf ε δ ≤ ε ∧
      2 * aOf ε δ ≤ δ := by
  have h0 : 0 ≤ T' * η := mul_nonneg hT hη
  have h1 : 0 ≤ q * (T' * η) := mul_nonneg hq h0
  have hm1 : min ε δ ≤ ε := min_le_left _ _
  have hm2 : min ε δ ≤ δ := min_le_right _ _
  have hm0 : 0 < min ε δ := lt_min hε hδ
  unfold aOf at *
  refine ⟨by nlinarith, by nlinarith, by linarith, by linarith⟩

/-- `a = min{ε, δ}/4` lies in `(0, 1]` for `ε, δ ∈ (0, 1/2)`. -/
theorem aOf_mem (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ) :
    0 < aOf ε δ ∧ aOf ε δ ≤ 1 := by
  unfold aOf
  have := min_le_left ε δ
  constructor
  · have := lt_min hε0 hδ0; linarith
  · linarith

/-- `sec:probability-route`, second proof of `thm:fixed`: with `a = min{ε, δ}/4` and the
parameters of `eq:fixed-parameters`, every base-query count `q ≤ (2TR/a)^C` satisfies
`(q+1)Tη ≤ a`, so the transfer loss `qTη ≤ a`, `TV(P,Q) ≤ Tη + a ≤ 2a ≤ ε` and the failure
`a + qTη ≤ 2a ≤ δ`. -/
theorem pr_final {ε δ : ℝ} (hT : 1 ≤ T) (hd : 1 ≤ d) (hC : 2 ≤ C) (hε0 : 0 < ε)
    (hε1 : ε < 1 / 2) (hδ0 : 0 < δ) (q : ℕ)
    (hq : (q : ℝ) ≤ (2 * T * prR T d C (aOf ε δ) / aOf ε δ) ^ C) :
    (q + 1) * T * prEta T d C (aOf ε δ) ≤ aOf ε δ ∧
      q * T * prEta T d C (aOf ε δ) ≤ aOf ε δ ∧
      T * prEta T d C (aOf ε δ) + aOf ε δ ≤ 2 * aOf ε δ ∧ 2 * aOf ε δ ≤ ε ∧
      2 * aOf ε δ ≤ δ := by
  obtain ⟨ha0, ha1⟩ := aOf_mem hε0 hε1 hδ0
  have hb := (pr_combined_budget hT hd hC ha0 ha1 q hq).2.2.2
  have hη : 0 ≤ prEta T d C (aOf ε δ) := by unfold prEta; positivity
  obtain ⟨h1, h2, h3, h4⟩ := pr_ledger hε0 hδ0 (Nat.cast_nonneg q) (Nat.cast_nonneg T) hη hb
  exact ⟨hb, h1, h2, h3, h4⟩

end ProbabilityRoute

/-! ### `cor:power-logits` -/

section PowerLogits

/-- `cor:power-logits`: for `θ > 0`, an integer `K ≥ 1/θ` (the paper takes `K ≥ max{1, 1/θ}`;
`K ≥ 1` is not needed here), `T₀ ≥ 1` and the padded length `T = T₀^K`, one has
`T₀ ≤ T^θ`. -/
theorem le_rpow_of_pad {θ : ℝ} (hθ : 0 < θ) {K : ℕ} (hKθ : 1 / θ ≤ K)
    {T₀ : ℕ} (hT₀ : 1 ≤ T₀) : (T₀ : ℝ) ≤ ((T₀ ^ K : ℕ) : ℝ) ^ θ := by
  have hT₀' : (1 : ℝ) ≤ T₀ := by exact_mod_cast hT₀
  have hKθ' : 1 ≤ (K : ℝ) * θ := by rwa [div_le_iff₀ hθ] at hKθ
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  calc (T₀ : ℝ) = (T₀ : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (T₀ : ℝ) ^ ((K : ℝ) * θ) := Real.rpow_le_rpow_of_exponent_le hT₀' hKθ'

/-- The arithmetic of `cor:power-logits`: for `θ > 0`, an integer `K ≥ 1/θ` and `T₀ ≥ 1`, every
real `u` with `|u| ≤ T₀` satisfies `|u| ≤ T^θ` for `T = T₀^K`. -/
theorem abs_le_rpow_of_pad {θ : ℝ} (hθ : 0 < θ) {K : ℕ} (hKθ : 1 / θ ≤ K)
    {T₀ : ℕ} (hT₀ : 1 ≤ T₀) {u : ℝ} (hu : |u| ≤ T₀) : |u| ≤ ((T₀ ^ K : ℕ) : ℝ) ^ θ :=
  hu.trans (le_rpow_of_pad hθ hKθ hT₀)

/-- `cor:power-logits`: if `|ℓ| ≤ Λ` then `σ(2ℓ) ≥ (1 + e^{2Λ})⁻¹` and
`1 - σ(2ℓ) ≥ (1 + e^{2Λ})⁻¹`. -/
theorem sigmoid_floor_of_abs_le {ℓ Λ : ℝ} (hℓ : |ℓ| ≤ Λ) :
    (1 + Real.exp (2 * Λ))⁻¹ ≤ sigmoid (2 * ℓ) ∧
      (1 + Real.exp (2 * Λ))⁻¹ ≤ 1 - sigmoid (2 * ℓ) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hℓ
  have key : ∀ v : ℝ, v ≤ 2 * Λ → (1 + Real.exp (2 * Λ))⁻¹ ≤ (1 + Real.exp v)⁻¹ := by
    intro v hv
    apply inv_anti₀ (by positivity)
    have := Real.exp_le_exp.mpr hv
    linarith
  constructor
  · exact key _ (by linarith)
  · rw [one_sub_sigmoid, sigmoid, neg_neg]
    exact key _ (by linarith)

/-- `cor:power-logits`: every next-bit probability of a fully supported model with
`|ℓ_P(h)| ≤ T^θ` is at least `(1 + e^{2T^θ})⁻¹`, and so is its complement. -/
theorem prob_floor_of_abs_logit_le {p : NextBit} {h : List Bool} {T θ : ℝ}
    (hp0 : 0 < p h) (hp1 : p h < 1) (hl : |logit p h| ≤ T ^ θ) :
    (1 + Real.exp (2 * T ^ θ))⁻¹ ≤ p h ∧ (1 + Real.exp (2 * T ^ θ))⁻¹ ≤ 1 - p h := by
  have e : sigmoid (2 * logit p h) = p h := ofLogit_logit hp0 hp1
  have := sigmoid_floor_of_abs_le hl
  rwa [e] at this

end PowerLogits

end LowLogitRank.Params
