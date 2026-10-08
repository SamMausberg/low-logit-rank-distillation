import LowLogitRank.Cover

/-!
# Dyadic probabilities of `sec:sample-upper`

The Taylor routine for `σ(2u)`, dyadic rounding, the probability floor, the change of
log-probabilities, the log-loss `φ_y`, and the pointwise bound `eq:bestKL`.
-/

namespace LowLogitRank.Cover

open Finset Real

/-! ### The Taylor routine -/

/-- The Taylor sum `E = ∑_{j ≤ M} v^j / j!`. -/
noncomputable def expTaylor (M : ℕ) (v : ℝ) : ℝ := ∑ j ∈ range (M + 1), v ^ j / j.factorial

theorem expTaylor_nonneg {v : ℝ} (hv : 0 ≤ v) (M : ℕ) : 0 ≤ expTaylor M v :=
  Finset.sum_nonneg fun j _ => by positivity

theorem expTaylor_le_exp {v : ℝ} (hv : 0 ≤ v) (M : ℕ) : expTaylor M v ≤ exp v :=
  Real.sum_le_exp_of_nonneg hv _

/-- The Taylor remainder of `sec:sample-upper`: `e^v - E ≤ e^v v^{M+1} / (M+1)!` for `v ≥ 0`. -/
theorem exp_sub_expTaylor_le {v : ℝ} (hv : 0 ≤ v) (M : ℕ) :
    exp v - expTaylor M v ≤ exp v * (v ^ (M + 1) / (M + 1).factorial) := by
  have hs : HasSum (fun n => v ^ n / (n.factorial : ℝ)) (exp v) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp v
  have ht := (hasSum_nat_add_iff' (M + 1)).mpr hs
  have hg := hs.mul_left (v ^ (M + 1) / (M + 1).factorial)
  rw [mul_comm (exp v)]
  refine hasSum_le (fun n => ?_) ht hg
  have hf : ((M + 1).factorial : ℝ) * n.factorial ≤ (n + (M + 1)).factorial := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add (M + 1) n
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (by rwa [add_comm n])
  rw [div_mul_div_comm, ← pow_add, add_comm (M + 1) n]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf

theorem exp_two_le_eight : exp 2 ≤ 8 := by
  have h := Real.exp_one_lt_d9
  have h2 : exp 2 = exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h2]; nlinarith [Real.exp_pos 1]

theorem exp_one_le_three : exp 1 ≤ 3 := by
  have h := Real.exp_one_lt_d9; linarith

/-- `n! ≥ (n/e)^n`. -/
theorem pow_div_exp_le_factorial (n : ℕ) : (n : ℝ) ^ n / exp n ≤ n.factorial := by
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h
  rw [div_le_iff₀ (exp_pos _)]
  linarith [mul_comm (exp (n : ℝ)) (n.factorial : ℝ)]

/-- First step of the Taylor chain of `sec:sample-upper`:
`e^{2T} (2T)^{M+1} / (M+1)! ≤ 2^{3T} (6T/(M+1))^{M+1}`. -/
theorem taylor_chain_one (T M : ℕ) :
    exp (2 * T) * ((2 * T) ^ (M + 1) / (M + 1).factorial) ≤
      2 ^ (3 * T) * (6 * T / (M + 1)) ^ (M + 1) := by
  have h1 : exp (2 * T) ≤ 2 ^ (3 * T) := by
    rw [mul_comm, Real.exp_nat_mul, pow_mul]
    exact pow_le_pow_left₀ (exp_pos _).le (by norm_num [exp_two_le_eight]) T
  have hn0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h2 : ((2 : ℝ) * T) ^ (M + 1) / (M + 1).factorial ≤ (6 * T / ((M : ℝ) + 1)) ^ (M + 1) := by
    have hf := pow_div_exp_le_factorial (M + 1)
    push_cast at hf
    have hpos : (0 : ℝ) < ((M : ℝ) + 1) ^ (M + 1) / exp ((M : ℝ) + 1) := by positivity
    have he : 2 * (T : ℝ) * exp 1 ≤ 6 * T := by
      nlinarith [exp_one_le_three, (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
    calc ((2 : ℝ) * T) ^ (M + 1) / (M + 1).factorial
        ≤ ((2 : ℝ) * T) ^ (M + 1) / (((M : ℝ) + 1) ^ (M + 1) / exp ((M : ℝ) + 1)) :=
          div_le_div_of_nonneg_left (by positivity) hpos (by exact_mod_cast hf)
      _ = (2 * T * exp 1 / ((M : ℝ) + 1)) ^ (M + 1) := by
          have : exp ((M : ℝ) + 1) = exp 1 ^ (M + 1) := by
            rw [← Real.exp_nat_mul]; push_cast; ring_nf
          rw [this, div_pow, mul_pow (2 * (T : ℝ))]; field_simp
      _ ≤ (6 * T / ((M : ℝ) + 1)) ^ (M + 1) :=
          pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right he hn0.le) _
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Second step of the Taylor chain of `sec:sample-upper`:
`2^{3T} (6T/(M+1))^{M+1} ≤ 2^{3T - 2(M+1)}` when `M + 1 ≥ 24 T`. -/
theorem taylor_chain_two (T M : ℕ) (hM : 24 * T ≤ M + 1) :
    (2 : ℝ) ^ (3 * T) * (6 * T / ((M : ℝ) + 1)) ^ (M + 1) ≤
      (2 : ℝ) ^ (((3 * T : ℕ) : ℤ) - ((2 * (M + 1) : ℕ) : ℤ)) := by
  have hq : 6 * (T : ℝ) / ((M : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : (24 * T : ℝ) ≤ M + 1 := by exact_mod_cast hM
    linarith
  have h4 : (2 : ℝ) ^ (((3 * T : ℕ) : ℤ) - ((2 * (M + 1) : ℕ) : ℤ)) =
      2 ^ (3 * T) * (1 / 4) ^ (M + 1) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, div_eq_mul_inv, one_div, inv_pow,
      pow_mul (2 : ℝ) 2 (M + 1)]
    norm_num
  rw [h4]
  gcongr

/-- Third step of the Taylor chain of `sec:sample-upper`: `2^{3T - 2(M+1)} ≤ 2^{-b-2}` when
`2(M+1) ≥ 3T + b + 2`. -/
theorem taylor_chain_three (T b M : ℕ) (hM : 3 * T + b + 2 ≤ 2 * (M + 1)) :
    (2 : ℝ) ^ (((3 * T : ℕ) : ℤ) - ((2 * (M + 1) : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-(b : ℤ) - 2) :=
  zpow_le_zpow_right₀ one_le_two (by push_cast; omega)

theorem two_zpow_neg_eq (b : ℕ) : (2 : ℝ) ^ (-(b : ℤ) - 2) = ((2 : ℝ) ^ (b + 2))⁻¹ := by
  rw [show -(b : ℤ) - 2 = -((b + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

/-- The Taylor routine of `sec:sample-upper`: with `M = 24T + b + 4` and `0 ≤ v ≤ 2T`,
`0 ≤ e^v - E ≤ e^{2T} (2T)^{M+1} / (M+1)! ≤ 2^{-b-2}`. -/
theorem taylor_remainder (T b : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 2 * T) :
    0 ≤ exp v - expTaylor (24 * T + b + 4) v ∧
      exp v - expTaylor (24 * T + b + 4) v ≤
        exp (2 * T) * ((2 * T) ^ (24 * T + b + 4 + 1) / (24 * T + b + 4 + 1).factorial) ∧
      exp (2 * T) * ((2 * T) ^ (24 * T + b + 4 + 1) / (24 * T + b + 4 + 1).factorial) ≤
        ((2 : ℝ) ^ (b + 2))⁻¹ := by
  set M := 24 * T + b + 4
  refine ⟨sub_nonneg.mpr (expTaylor_le_exp hv0 M), ?_, ?_⟩
  · refine (exp_sub_expTaylor_le hv0 M).trans ?_
    gcongr
  · have := (taylor_chain_one T M).trans ((taylor_chain_two T M (by omega)).trans
      (taylor_chain_three T b M (by omega)))
    rwa [two_zpow_neg_eq] at this

/-! ### From `E` to probabilities -/

/-- `E ↦ E / (1 + E)` is 1-Lipschitz on `E ≥ 0` (`sec:sample-upper`). -/
theorem frac_lipschitz {E E' : ℝ} (hE : 0 ≤ E) (hE' : 0 ≤ E') :
    |E / (1 + E) - E' / (1 + E')| ≤ |E - E'| := by
  have h1 : 0 < 1 + E := by linarith
  have h2 : 0 < 1 + E' := by linarith
  have e : E / (1 + E) - E' / (1 + E') = (E - E') / ((1 + E) * (1 + E')) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos h1 h2)]
  exact div_le_self (abs_nonneg _) (by nlinarith)

/-- `E ↦ 1 / (1 + E)` is 1-Lipschitz on `E ≥ 0` (`sec:sample-upper`). -/
theorem inv_lipschitz {E E' : ℝ} (hE : 0 ≤ E) (hE' : 0 ≤ E') :
    |1 / (1 + E) - 1 / (1 + E')| ≤ |E - E'| := by
  have h1 : 0 < 1 + E := by linarith
  have h2 : 0 < 1 + E' := by linarith
  have e : 1 / (1 + E) - 1 / (1 + E') = (E' - E) / ((1 + E) * (1 + E')) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (mul_pos h1 h2), abs_sub_comm]
  exact div_le_self (abs_nonneg _) (by nlinarith)

theorem sigmoid_two_mul_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    sigmoid (2 * u) = exp (2 * |u|) / (1 + exp (2 * |u|)) := by
  rw [abs_of_nonneg hu, sigmoid, Real.exp_neg]
  have := exp_pos (2 * u)
  field_simp
  ring

theorem sigmoid_two_mul_of_neg {u : ℝ} (hu : u < 0) :
    sigmoid (2 * u) = 1 / (1 + exp (2 * |u|)) := by
  rw [abs_of_neg hu, sigmoid, one_div]
  congr 2; ring_nf

/-- The rational routine of `sec:sample-upper` for `σ(2u)`: `E/(1+E)` for `u ≥ 0` and `1/(1+E)`
otherwise, with `E` the Taylor sum of order `M` at `v = 2|u|`. -/
noncomputable def approxSigma (M : ℕ) (u : ℝ) : ℝ :=
  if 0 ≤ u then expTaylor M (2 * |u|) / (1 + expTaylor M (2 * |u|))
  else 1 / (1 + expTaylor M (2 * |u|))

/-- The Taylor routine approximates `σ(2u)` within `2^{-b-2}` for `|u| ≤ T`, `M = 24T + b + 4`
(`sec:sample-upper`). -/
theorem approxSigma_error (T b : ℕ) {u : ℝ} (hu : |u| ≤ T) :
    |approxSigma (24 * T + b + 4) u - sigmoid (2 * u)| ≤ ((2 : ℝ) ^ (b + 2))⁻¹ := by
  have hv0 : 0 ≤ 2 * |u| := by positivity
  obtain ⟨h0, h1, h2⟩ := taylor_remainder T b hv0 (by linarith)
  have hE := expTaylor_nonneg hv0 (24 * T + b + 4)
  have herr : |expTaylor (24 * T + b + 4) (2 * |u|) - exp (2 * |u|)| ≤ ((2 : ℝ) ^ (b + 2))⁻¹ := by
    rw [abs_sub_comm, abs_of_nonneg h0]; exact h1.trans h2
  unfold approxSigma
  split_ifs with hu0
  · rw [sigmoid_two_mul_of_nonneg hu0]
    exact (frac_lipschitz hE (exp_pos _).le).trans herr
  · rw [sigmoid_two_mul_of_neg (lt_of_not_ge hu0)]
    exact (inv_lipschitz hE (exp_pos _).le).trans herr

/-! ### Dyadic rounding and the probability floor -/

/-- Rounding to the nearest multiple of `2^{-b}` (ties broken by `round`). -/
noncomputable def dyadicRound (b : ℕ) (x : ℝ) : ℝ := (round (x * 2 ^ b) : ℝ) / 2 ^ b

theorem abs_dyadicRound_sub (b : ℕ) (x : ℝ) :
    |dyadicRound b x - x| ≤ 2 * ((2 : ℝ) ^ (b + 2))⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  have e : dyadicRound b x - x = ((round (x * 2 ^ b) : ℝ) - x * 2 ^ b) / 2 ^ b := by
    unfold dyadicRound; field_simp
  rw [e, abs_div, abs_of_pos h2, abs_sub_comm, pow_add]
  calc |x * 2 ^ b - (round (x * 2 ^ b) : ℝ)| / 2 ^ b ≤ (1 / 2) / 2 ^ b := by
        gcongr; exact abs_sub_round _
    _ = 2 * (2 ^ b * 2 ^ 2)⁻¹ := by field_simp

/-- `3 · 2^{-b-2} < 2^{-b}`. -/
theorem three_mul_lt (b : ℕ) : 3 * ((2 : ℝ) ^ (b + 2))⁻¹ < ((2 : ℝ) ^ b)⁻¹ := by
  have hx : (0 : ℝ) < ((2 : ℝ) ^ b)⁻¹ := by positivity
  rw [pow_add, mul_inv]
  norm_num
  linarith

/-- Approximation within `2^{-b-2}` followed by dyadic rounding leaves a total probability error
of at most `3 · 2^{-b-2} < 2^{-b}` (`sec:sample-upper`). -/
theorem dyadic_error (T b : ℕ) {u : ℝ} (hu : |u| ≤ T) :
    |dyadicRound b (approxSigma (24 * T + b + 4) u) - sigmoid (2 * u)| ≤
      3 * ((2 : ℝ) ^ (b + 2))⁻¹ := by
  have h1 := abs_dyadicRound_sub b (approxSigma (24 * T + b + 4) u)
  have h2 := approxSigma_error T b hu
  calc _ = |(dyadicRound b (approxSigma (24 * T + b + 4) u) - approxSigma (24 * T + b + 4) u) +
          (approxSigma (24 * T + b + 4) u - sigmoid (2 * u))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * ((2 : ℝ) ^ (b + 2))⁻¹ + ((2 : ℝ) ^ (b + 2))⁻¹ := add_le_add h1 h2
    _ = 3 * ((2 : ℝ) ^ (b + 2))⁻¹ := by ring

/-- Both exact conditional probabilities at `|u| ≤ T` are at least `e^{-2T}/2`
(`sec:sample-upper`); this is the outcome `1`, see `one_sub_sigmoid_two_mul_ge` for `0`. -/
theorem sigmoid_two_mul_ge {T u : ℝ} (hu : |u| ≤ T) : exp (-(2 * T)) / 2 ≤ sigmoid (2 * u) := by
  have hle : exp (-(2 * u)) ≤ exp (2 * T) := by
    rw [exp_le_exp]; have := neg_abs_le u; linarith
  have hpos := exp_pos (-(2 * u))
  have hm : exp (-(2 * T)) * exp (2 * T) = 1 := by rw [← exp_add]; simp
  have hT : exp (-(2 * T)) ≤ 1 := by
    rw [exp_le_one_iff]; have := abs_nonneg u; linarith
  unfold sigmoid
  rw [div_le_iff₀ two_pos, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  nlinarith [exp_pos (-(2 * T))]

theorem one_sub_sigmoid_two_mul_ge {T u : ℝ} (hu : |u| ≤ T) :
    exp (-(2 * T)) / 2 ≤ 1 - sigmoid (2 * u) := by
  rw [one_sub_sigmoid, show -(2 * u) = 2 * (-u) by ring]
  exact sigmoid_two_mul_ge (by rwa [abs_neg])

/-- The probability precision `b = 4T + ⌈log₂ (16/ρ)⌉`. -/
noncomputable def precB (T : ℕ) (ρ : ℝ) : ℕ := 4 * T + ⌈Real.logb 2 (16 / ρ)⌉₊

/-- With `b = 4T + ⌈log₂ (16/ρ)⌉`, `2^{-b} ≤ ρ e^{-2T} / 16` (`sec:sample-upper`). -/
theorem precB_spec (T : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ((2 : ℝ) ^ precB T ρ)⁻¹ ≤ ρ * exp (-(2 * T)) / 16 := by
  have hk : 16 / ρ ≤ (2 : ℝ) ^ ⌈Real.logb 2 (16 / ρ)⌉₊ := by
    have h1 : Real.logb 2 (16 / ρ) ≤ ⌈Real.logb 2 (16 / ρ)⌉₊ := Nat.le_ceil _
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)] at h1
    simpa [Real.rpow_natCast] using h1
  have hT : exp (2 * T) ≤ (2 : ℝ) ^ (4 * T) := by
    rw [mul_comm, Real.exp_nat_mul, pow_mul]
    exact pow_le_pow_left₀ (exp_pos _).le (by norm_num; linarith [exp_two_le_eight]) T
  have hprod : exp (2 * T) * (16 / ρ) ≤ (2 : ℝ) ^ precB T ρ := by
    rw [precB, pow_add]
    exact mul_le_mul hT hk (by positivity) (by positivity)
  rw [exp_neg, inv_le_comm₀ (by positivity) (by positivity)]
  calc (ρ * (exp (2 * T))⁻¹ / 16)⁻¹ = exp (2 * T) * (16 / ρ) := by
        field_simp
    _ ≤ _ := hprod

/-- Changing a probability `p ≥ e^{-2T}/2` by at most `ρ e^{-2T}/16`, `0 ≤ ρ ≤ 4`, keeps it at least
`e^{-2T}/4` and changes its logarithm by at most `ρ` (`sec:sample-upper`). -/
theorem log_change {T p q ρ : ℝ} (hp : exp (-(2 * T)) / 2 ≤ p)
    (hq : |q - p| ≤ ρ * exp (-(2 * T)) / 16) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 4) :
    exp (-(2 * T)) / 4 ≤ q ∧ |log q - log p| ≤ ρ := by
  set F := exp (-(2 * T))
  have hF : 0 < F := exp_pos _
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  rw [abs_le] at hq
  have hqF : F / 4 ≤ q := by nlinarith
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hqF
  refine ⟨hqF, ?_⟩
  rw [← Real.log_div hq0.ne' hp0.ne', abs_le]
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hq0 hp0)
    rw [inv_div] at h
    refine le_trans ?_ h
    rw [show 1 - p / q = (q - p) / q by field_simp, le_div_iff₀ hq0]
    nlinarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
    refine h.trans ?_
    rw [show q / p - 1 = (q - p) / p by field_simp, div_le_iff₀ hp0]
    nlinarith

/-! ### The log-loss `φ_y` -/

/-- The Bernoulli probability of the outcome `y` when `P(1) = x`. -/
def bern (x : ℝ) (y : Bool) : ℝ := if y then x else 1 - x

theorem bitProb_eq_bern (p : NextBit) (h : List Bool) (y : Bool) :
    bitProb p h y = bern (p h) y := rfl

/-- The conditional negative log likelihood `φ_y(u) = ln(1 + e^{2u}) - 2yu`. -/
noncomputable def phi (y : Bool) (u : ℝ) : ℝ :=
  log (1 + exp (2 * u)) - 2 * (if y then 1 else 0) * u

theorem sigmoid_two_mul_eq (u : ℝ) : sigmoid (2 * u) = exp (2 * u) / (1 + exp (2 * u)) := by
  rw [sigmoid, exp_neg]
  have := exp_pos (2 * u)
  field_simp
  ring

/-- `φ_y(u) = -ln P(y)` when `P(1) = σ(2u)` (`sec:sample-upper`). -/
theorem neg_log_bern_sigmoid (y : Bool) (u : ℝ) :
    -log (bern (sigmoid (2 * u)) y) = phi y u := by
  have h1 : 0 < 1 + exp (2 * u) := by positivity
  cases y
  · simp only [bern, phi, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_mul, sub_zero]
    rw [one_sub_sigmoid, sigmoid, neg_neg, Real.log_inv, neg_neg]
  · simp only [bern, phi, ↓reduceIte, mul_one]
    rw [sigmoid_two_mul_eq, Real.log_div (exp_pos _).ne' h1.ne', Real.log_exp]
    ring

/-- The derivative of `φ_y` is `2σ(2u) - 2y`; it has absolute value at most two
(`sec:sample-upper`). -/
theorem hasDerivAt_phi (y : Bool) (u : ℝ) :
    HasDerivAt (phi y) (2 * sigmoid (2 * u) - 2 * (if y then 1 else 0)) u ∧
      |2 * sigmoid (2 * u) - 2 * (if y then 1 else 0)| ≤ 2 := by
  have h1 : 0 < 1 + exp (2 * u) := by positivity
  constructor
  · have hd : HasDerivAt (fun x => 1 + exp (2 * x)) (exp (2 * u) * 2) u := by
      have := ((hasDerivAt_id u).const_mul 2).exp.const_add 1
      simpa using this
    have hl := hd.log h1.ne'
    have hlin : HasDerivAt (fun x => 2 * (if y then (1 : ℝ) else 0) * x)
        (2 * (if y then 1 else 0)) u := by
      simpa using (hasDerivAt_id u).const_mul (2 * (if y then (1 : ℝ) else 0))
    have h := hl.sub hlin
    have e : exp (2 * u) * 2 / (1 + exp (2 * u)) - 2 * (if y then (1 : ℝ) else 0) =
        2 * sigmoid (2 * u) - 2 * (if y then 1 else 0) := by
      rw [sigmoid_two_mul_eq]; field_simp
    rw [e] at h
    exact h
  · have h0 := (sigmoid_pos (2 * u)).le
    have h1' := (sigmoid_lt_one (2 * u)).le
    rw [abs_le]
    cases y <;> simp <;> constructor <;> linarith

theorem log_one_add_exp_mono {u u' : ℝ} (h : u ≤ u') :
    0 ≤ log (1 + exp (2 * u')) - log (1 + exp (2 * u)) ∧
      log (1 + exp (2 * u')) - log (1 + exp (2 * u)) ≤ 2 * (u' - u) := by
  have h1 : 0 < 1 + exp (2 * u) := by positivity
  have h2 : 0 < 1 + exp (2 * u') := by positivity
  constructor
  · have : exp (2 * u) ≤ exp (2 * u') := exp_le_exp.mpr (by linarith)
    linarith [Real.log_le_log h1 (by linarith : 1 + exp (2 * u) ≤ 1 + exp (2 * u'))]
  · have hk : 1 ≤ exp (2 * (u' - u)) := Real.one_le_exp (by linarith)
    have he : exp (2 * u') = exp (2 * (u' - u)) * exp (2 * u) := by rw [← exp_add]; ring_nf
    have hle : 1 + exp (2 * u') ≤ exp (2 * (u' - u)) * (1 + exp (2 * u)) := by
      rw [he]; nlinarith
    have := Real.log_le_log h2 hle
    rw [Real.log_mul (exp_pos _).ne' h1.ne', Real.log_exp] at this
    linarith

/-- `φ_y` is 2-Lipschitz (`sec:sample-upper`). -/
theorem phi_lipschitz (y : Bool) (u u' : ℝ) : |phi y u' - phi y u| ≤ 2 * |u' - u| := by
  have key : ∀ a b : ℝ, a ≤ b → |phi y b - phi y a| ≤ 2 * |b - a| := by
    intro a b hab
    obtain ⟨h1, h2⟩ := log_one_add_exp_mono hab
    rw [abs_of_nonneg (by linarith : 0 ≤ b - a), abs_le]
    cases y <;> simp [phi] <;> constructor <;> linarith
  rcases le_total u u' with h | h
  · exact key u u' h
  · rw [abs_sub_comm, abs_sub_comm u']; exact key u' u h

/-- One step of `eq:bestKL`: for an exact logit `u` and a clipped candidate logit `ũ ∈ [-T, T]`
with `|ũ - u| ≤ ρ`, and a candidate probability `q` within `ρ e^{-2T}/16` of `σ(2ũ)`, `0 ≤ ρ ≤ 4`,
each outcome has candidate probability at least `e^{-2T}/4` and log-loss discrepancy at most
`2ρ + ρ = 3ρ`. -/
theorem step_logloss {T u ũ q ρ : ℝ} (hũ : |ũ| ≤ T) (huu : |ũ - u| ≤ ρ)
    (hq : |q - sigmoid (2 * ũ)| ≤ ρ * exp (-(2 * T)) / 16) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 4)
    (y : Bool) :
    exp (-(2 * T)) / 4 ≤ bern q y ∧
      |log (bern q y) - log (bern (sigmoid (2 * u)) y)| ≤ 3 * ρ := by
  have hfloor : exp (-(2 * T)) / 2 ≤ bern (sigmoid (2 * ũ)) y := by
    cases y
    · exact one_sub_sigmoid_two_mul_ge hũ
    · exact sigmoid_two_mul_ge hũ
  have hdiff : |bern q y - bern (sigmoid (2 * ũ)) y| ≤ ρ * exp (-(2 * T)) / 16 := by
    cases y
    · simp only [bern, Bool.false_eq_true, ↓reduceIte]
      rw [show 1 - q - (1 - sigmoid (2 * ũ)) = -(q - sigmoid (2 * ũ)) by ring, abs_neg]
      exact hq
    · exact hq
  obtain ⟨hq4, hlog⟩ := log_change hfloor hdiff hρ0 hρ
  refine ⟨hq4, ?_⟩
  have hphi : |log (bern (sigmoid (2 * ũ)) y) - log (bern (sigmoid (2 * u)) y)| ≤ 2 * ρ := by
    have e : log (bern (sigmoid (2 * ũ)) y) - log (bern (sigmoid (2 * u)) y) =
        -(phi y ũ - phi y u) := by
      rw [← neg_log_bern_sigmoid, ← neg_log_bern_sigmoid]; ring
    rw [e, abs_neg]
    exact (phi_lipschitz y u ũ).trans (by linarith)
  calc _ = |(log (bern q y) - log (bern (sigmoid (2 * ũ)) y)) +
        (log (bern (sigmoid (2 * ũ)) y) - log (bern (sigmoid (2 * u)) y))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ ρ + 2 * ρ := add_le_add hlog hphi
    _ = 3 * ρ := by ring

/-! ### Products along a path -/

theorem condProb_nonneg (q : NextBit) (hq : ∀ h y, 0 ≤ bitProb q h y) (h f : List Bool) :
    0 ≤ condProb q h f := by
  induction f generalizing h with
  | nil => simp
  | cons b f ih => rw [condProb_cons]; exact mul_nonneg (hq h b) (ih _)

/-- Per-step bounds on log-probabilities add up along a path: if before time `T` all conditional
probabilities of `p` and `q` are positive and their logarithms differ by at most `a₀`, then the
logarithms of `P(f | h)` and `Q(f | h)` differ by at most `|f| a₀` whenever `|h| + |f| ≤ T`. -/
theorem log_condProb_sub_le (p q : NextBit) (T : ℕ) (a₀ : ℝ)
    (hstep : ∀ h : List Bool, h.length < T → ∀ y, 0 < bitProb p h y ∧ 0 < bitProb q h y ∧
      |log (bitProb q h y) - log (bitProb p h y)| ≤ a₀) :
    ∀ f h : List Bool, h.length + f.length ≤ T →
      0 < condProb p h f ∧ 0 < condProb q h f ∧
        |log (condProb q h f) - log (condProb p h f)| ≤ f.length * a₀ := by
  intro f
  induction f with
  | nil => intro h _; simp
  | cons b f ih =>
    intro h hlen
    simp only [List.length_cons] at hlen
    obtain ⟨hp, hq, hb⟩ := hstep h (by omega) b
    obtain ⟨hp', hq', hf⟩ := ih (h ++ [b]) (by simp; omega)
    simp only [condProb_cons]
    refine ⟨mul_pos hp hp', mul_pos hq hq', ?_⟩
    rw [Real.log_mul hq.ne' hq'.ne', Real.log_mul hp.ne' hp'.ne']
    calc _ = |(log (bitProb q h b) - log (bitProb p h b)) +
          (log (condProb q (h ++ [b]) f) - log (condProb p (h ++ [b]) f))| := by ring_nf
      _ ≤ a₀ + f.length * a₀ := (abs_add_le _ _).trans (add_le_add hb hf)
      _ = ((b :: f).length : ℝ) * a₀ := by simp; ring

/-- The pointwise ratio bound behind `eq:bestKL`, for complete words of length `T`. -/
theorem log_wordDist_ratio_le (p q : NextBit) (T : ℕ) (a₀ : ℝ)
    (hstep : ∀ h : List Bool, h.length < T → ∀ y, 0 < bitProb p h y ∧ 0 < bitProb q h y ∧
      |log (bitProb q h y) - log (bitProb p h y)| ≤ a₀) (z : Word T) :
    0 < wordDist p T z ∧ 0 < wordDist q T z ∧
      |log (wordDist q T z / wordDist p T z)| ≤ T * a₀ := by
  obtain ⟨h1, h2, h3⟩ := log_condProb_sub_le p q T a₀ hstep z.toList [] (by simp)
  refine ⟨h1, h2, ?_⟩
  unfold wordDist
  rw [Real.log_div h2.ne' h1.ne']
  simpa using h3

/-! ### The finite-bit candidates and `eq:bestKL` -/

variable {T d : ℕ} {B Δ : ℝ}

/-- The finite-bit candidate of `sec:sample-upper`: clip the computed logit to `[-T, T]`, apply the
Taylor routine of order `M`, and round to a multiple of `2^{-b}`. -/
noncomputable def candModel (P : GridParams T d B Δ) (b M : ℕ) : NextBit :=
  fun h => dyadicRound b (approxSigma M (clip T (candLogit P h)))

/-- Every candidate probability is within `ρ e^{-2T}/16` of `σ(2ũ)`, `ũ` the clipped logit, when
`b = 4T + ⌈log₂ (16/ρ)⌉` and `M = 24T + b + 4`. -/
theorem candModel_error (P : GridParams T d B Δ) {ρ : ℝ} (hρ : 0 < ρ) (h : List Bool) :
    |candModel P (precB T ρ) (24 * T + precB T ρ + 4) h - sigmoid (2 * clip T (candLogit P h))| ≤
      ρ * exp (-(2 * T)) / 16 :=
  (dyadic_error T _ (abs_clip_le (Nat.cast_nonneg T) _)).trans
    ((three_mul_lt _).le.trans (precB_spec T hρ))

/-- Every candidate has both outcome probabilities at least `e^{-2T}/4` (for `0 < ρ ≤ 4`). -/
theorem candModel_floor (P : GridParams T d B Δ) {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 4)
    (h : List Bool) (y : Bool) :
    exp (-(2 * T)) / 4 ≤ bitProb (candModel P (precB T ρ) (24 * T + precB T ρ + 4)) h y :=
  (step_logloss (u := clip T (candLogit P h)) (abs_clip_le (Nat.cast_nonneg T) _)
    (by simpa using hρ.le) (candModel_error P hρ h) hρ.le hρ4 y).1

/-- `ρ = ε² / (16 T)`. -/
noncomputable def coverRho (T : ℕ) (ε : ℝ) : ℝ := ε ^ 2 / (16 * T)

/-- The mesh `Δ = 2^{-k}` of `eq:mesh` with `ρ = ε² / (16 T)`. -/
noncomputable def coverDelta (T d : ℕ) (ε : ℝ) : ℝ := ((2 : ℝ) ^ meshK T d (coverRho T ε))⁻¹

/-- The precision `b = 4T + ⌈log₂ (16/ρ)⌉` with `ρ = ε² / (16 T)`. -/
noncomputable def coverB (T : ℕ) (ε : ℝ) : ℕ := precB T (coverRho T ε)

/-- The candidates of `thm:cover`: readouts in the grid of `[-T, T]`, mesh `coverDelta`. -/
abbrev Candidates (T d : ℕ) (ε : ℝ) := GridParams T d T (coverDelta T d ε)

/-- The finite-bit distribution of a candidate of `thm:cover`. -/
noncomputable def coverModel (P : Candidates T d ε) : NextBit :=
  candModel P (coverB T ε) (24 * T + coverB T ε + 4)

theorem coverRho_pos (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) : 0 < coverRho T ε := by
  have : (1 : ℝ) ≤ T := by exact_mod_cast hT
  unfold coverRho
  positivity

theorem coverRho_le (hT : 1 ≤ T) {ε : ℝ} (hε1 : |ε| ≤ 1) : coverRho T ε ≤ 4 := by
  unfold coverRho
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have : ε ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ε]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Every candidate distribution is a probability vector on `{0,1}^T` with positive entries. -/
theorem coverModel_prob (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (P : Candidates T d ε) :
    (∀ z, 0 < wordDist (coverModel P) T z) ∧ ∑ z, wordDist (coverModel P) T z = 1 := by
  have hρ := coverRho_pos hT hε
  have hρ4 := coverRho_le hT (by rw [abs_of_pos hε]; exact hε1)
  have hfl := candModel_floor P hρ hρ4
  refine ⟨fun z => ?_, sum_condProb _ T []⟩
  have := (log_condProb_sub_le (coverModel P) (coverModel P) T 0 (fun h _ y => ⟨?_, ?_, by simp⟩)
    z.toList [] (by simp)).1
  · exact this
  all_goals exact lt_of_lt_of_le (by positivity) (hfl h y)

/-- `eq:bestKL`: for `p ∈ 𝒞_{T,d}`, `T, d ≥ 1`, `0 < ε ≤ 1`, some grid candidate `Q_*` satisfies
`|ln (Q_*(z) / P(z))| ≤ 3 T ρ = 3 ε² / 16` for every `z ∈ {0,1}^T`, with `Q_*(z) > 0`. -/
theorem bestKL (hT : 1 ≤ T) (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {p : NextBit}
    (hp : InClass T d p) :
    ∃ P : Candidates T d ε, ∀ z : Word T, 0 < wordDist (coverModel P) T z ∧
      |log (wordDist (coverModel P) T z / wordDist p T z)| ≤ 3 * ε ^ 2 / 16 := by
  set ρ := coverRho T ε
  have hρ : 0 < ρ := coverRho_pos hT hε0
  have hρ4 : ρ ≤ 4 := coverRho_le hT (by rw [abs_of_pos hε0]; exact hε1)
  have hΔ : 0 < coverDelta T d ε := by unfold coverDelta; positivity
  have hΔρ : coverDelta T d ε ≤ ρ / (4 * d * ((T : ℝ) + 1) * (2 * d) ^ T) := mesh_le T d hd hρ
  obtain ⟨P, hP⟩ := exists_grid_candidate (ℓ := logit p) (Λ := (T : ℝ)) hd hΔ hΔρ hp.logit_le
    hp.rank_le
  refine ⟨P, fun z => ?_⟩
  have hstep : ∀ h : List Bool, h.length < T → ∀ y, 0 < bitProb p h y ∧
      0 < bitProb (coverModel P) h y ∧
      |log (bitProb (coverModel P) h y) - log (bitProb p h y)| ≤ 3 * ρ := by
    intro h hh y
    have hfs := hp.fullSupport h hh
    have hpe : p h = sigmoid (2 * logit p h) := (ofLogit_logit hfs.1 hfs.2).symm
    have hu := hp.logit_le h hh
    have hũ := abs_clip_le (Nat.cast_nonneg T) (candLogit P h)
    have huu : |clip T (candLogit P h) - logit p h| ≤ ρ :=
      (abs_clip_sub_le hu _).trans (hP h hh)
    obtain ⟨hfl, hlog⟩ := step_logloss hũ huu (candModel_error P hρ h) hρ.le hρ4 y
    refine ⟨?_, lt_of_lt_of_le (by positivity) hfl, ?_⟩
    · cases y
      · simp only [bitProb, Bool.false_eq_true, ↓reduceIte]; linarith [hfs.2]
      · simpa [bitProb] using hfs.1
    · rw [bitProb_eq_bern, bitProb_eq_bern, hpe]; exact hlog
  obtain ⟨-, h2, h3⟩ := log_wordDist_ratio_le p (coverModel P) T (3 * ρ) hstep z
  refine ⟨h2, h3.trans (le_of_eq ?_)⟩
  have : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [ρ, coverRho]
  field_simp

end LowLogitRank.Cover
