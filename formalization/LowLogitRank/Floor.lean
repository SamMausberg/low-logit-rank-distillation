import LowLogitRank.Params

/-!
# Arithmetic of the probability floor (`sec:floor`, `sec:parity`)

The deterministic content of `lem:floor-estimator`, the parameter choices after
`lem:bounded-factors`, the error ledger of `sec:gls-validation-arithmetic`, and the majority
count of `sec:parity`. Probability bounds (multiplicative Chernoff, Hoeffding) are not
formalized; we check the exponent arithmetic that turns them into the stated failure bounds.
-/

namespace LowLogitRank.Floor

open LowLogitRank.Params

/-! ### The floor parameters -/

/-- `λ_γ = (1/2) log((1 - γ)/γ)`. -/
noncomputable def lambdaOf (γ : ℝ) : ℝ := Real.log ((1 - γ) / γ) / 2

/-- `Λ = max{1, λ_γ}`. -/
noncomputable def bigLambdaOf (γ : ℝ) : ℝ := max 1 (lambdaOf γ)

/-- The integer logit bound `L = 1 + ⌈log₂(1/γ)⌉`. -/
noncomputable def floorL (γ : ℝ) : ℕ := 1 + ⌈Real.logb 2 (1 / γ)⌉₊

theorem lambdaOf_nonneg {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) : 0 ≤ lambdaOf γ := by
  unfold lambdaOf
  have : 1 ≤ (1 - γ) / γ := by rw [le_div_iff₀ hγ0]; linarith
  have := Real.log_nonneg this
  linarith

/-- `sec:floor`: if `γ ≤ p ≤ 1 - γ`, the centered logit of `p` has magnitude at most `λ_γ`. -/
theorem abs_centered_logit_le_lambdaOf {γ x : ℝ} (hγ0 : 0 < γ) (hx0 : γ ≤ x)
    (hx1 : x ≤ 1 - γ) : |Real.log (x / (1 - x)) / 2| ≤ lambdaOf γ := by
  have hx : 0 < x := by linarith
  have hx' : 0 < 1 - x := by linarith
  have hr : 0 < x / (1 - x) := div_pos hx hx'
  have hup : x / (1 - x) ≤ (1 - γ) / γ := by
    rw [div_le_div_iff₀ hx' hγ0]; nlinarith
  have hlo : γ / (1 - γ) ≤ x / (1 - x) := by
    rw [div_le_div_iff₀ (by linarith) hx']; nlinarith
  have h1 := Real.log_le_log hr hup
  have h2 := Real.log_le_log (div_pos hγ0 (by linarith)) hlo
  have hinv : Real.log (γ / (1 - γ)) = -Real.log ((1 - γ) / γ) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv] at h2
  unfold lambdaOf
  rw [abs_div, abs_two, div_le_div_iff_of_pos_right two_pos, abs_le]
  exact ⟨h2, h1⟩

/-- `sec:floor`: `λ_γ ≤ L = 1 + ⌈log₂(1/γ)⌉`, hence also `Λ ≤ L`. -/
theorem lambdaOf_le_floorL {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) :
    lambdaOf γ ≤ floorL γ ∧ bigLambdaOf γ ≤ floorL γ := by
  have hg : 1 ≤ 1 / γ := by rw [le_div_iff₀ hγ0]; linarith
  have h1 : Real.log ((1 - γ) / γ) ≤ Real.log (1 / γ) :=
    Real.log_le_log (div_pos (by linarith) hγ0) (div_le_div_of_nonneg_right (by linarith) hγ0.le)
  have h2 := log_le_logb_two hg
  have h3 := Nat.le_ceil (Real.logb 2 (1 / γ))
  have h4 : 0 ≤ Real.log (1 / γ) := Real.log_nonneg hg
  have hl : lambdaOf γ ≤ floorL γ := by
    unfold lambdaOf floorL
    push_cast
    linarith
  refine ⟨hl, max_le ?_ hl⟩
  unfold floorL
  push_cast
  have : (0 : ℝ) ≤ ⌈Real.logb 2 (1 / γ)⌉₊ := by positivity
  linarith

/-- `sec:floor`: the bounded-factor norm `√(dΛ)` of `lem:bounded-factors` is at most the supplied
`α = dL + 1`. -/
theorem sqrt_le_alpha {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (d : ℕ) :
    Real.sqrt (d * bigLambdaOf γ) ≤ d * floorL γ + 1 := by
  have hΛ := (lambdaOf_le_floorL hγ0 hγ1).2
  have hd : (0 : ℝ) ≤ d := by positivity
  have h1 : (d : ℝ) * bigLambdaOf γ ≤ d * floorL γ := mul_le_mul_of_nonneg_left hΛ hd
  have h2 : (0 : ℝ) ≤ d * floorL γ := by positivity
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-! ### `lem:floor-estimator`: the good event -/

/-- A multiplicative error `|x - p| ≤ τ p` with `0 < τ < 1` gives `x > 0` and a logarithmic ratio
error `|log(x/p)| ≤ τ/(1 - τ)`. -/
theorem abs_log_ratio_le {τ p x : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hp : 0 < p)
    (hx : |x - p| ≤ τ * p) : 0 < x ∧ |Real.log (x / p)| ≤ τ / (1 - τ) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  have hx0 : 0 < x := by nlinarith
  have hr : 0 < x / p := div_pos hx0 hp
  have hrl : 1 - τ ≤ x / p := by rw [le_div_iff₀ hp]; linarith
  have hru : x / p ≤ 1 + τ := by rw [div_le_iff₀ hp]; linarith
  have h1τ : 0 < 1 - τ := by linarith
  have hττ : τ ≤ τ / (1 - τ) := by
    rw [le_div_iff₀ h1τ]; nlinarith
  refine ⟨hx0, abs_le.mpr ⟨?_, ?_⟩⟩
  · have := Real.one_sub_inv_le_log_of_pos hr
    have hinv : (x / p)⁻¹ ≤ (1 - τ)⁻¹ := inv_anti₀ h1τ hrl
    have e : -(τ / (1 - τ)) = 1 - (1 - τ)⁻¹ := by field_simp; ring
    linarith
  · have := Real.log_le_sub_one_of_pos hr
    linarith

/-- `lem:floor-estimator`, good event. Let `0 < γ`, `0 < ξ ≤ 1`, `τ = ξ/4`,
`p ∈ [γ, 1 - γ]`, and let `U` satisfy `|U - p| ≤ τ p` and `|(1 - U) - (1 - p)| ≤ τ (1 - p)`.
Then `U ∈ (0, 1)`, both logarithmic ratio errors are at most `τ/(1 - τ) ≤ ξ/3`, and the centered
logits of `U` and `p` differ by at most `ξ/3`. The bound `γ ≤ 1/2` is not needed here. -/
theorem floor_estimator_good_event {γ ξ p U : ℝ} (hγ0 : 0 < γ) (hξ0 : 0 < ξ)
    (hξ1 : ξ ≤ 1) (hp0 : γ ≤ p) (hp1 : p ≤ 1 - γ) (hU : |U - p| ≤ ξ / 4 * p)
    (hU' : |(1 - U) - (1 - p)| ≤ ξ / 4 * (1 - p)) :
    0 < U ∧ U < 1 ∧ |Real.log (U / p)| ≤ ξ / 4 / (1 - ξ / 4) ∧
      |Real.log ((1 - U) / (1 - p))| ≤ ξ / 4 / (1 - ξ / 4) ∧ ξ / 4 / (1 - ξ / 4) ≤ ξ / 3 ∧
      |Real.log (U / (1 - U)) / 2 - Real.log (p / (1 - p)) / 2| ≤ ξ / 3 := by
  have hp : 0 < p := by linarith
  have hq : 0 < 1 - p := by linarith
  obtain ⟨hU0, h1⟩ := abs_log_ratio_le (by linarith) (by linarith) hp hU
  obtain ⟨hU1, h2⟩ := abs_log_ratio_le (by linarith) (by linarith) hq hU'
  have h3 : ξ / 4 / (1 - ξ / 4) ≤ ξ / 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  refine ⟨hU0, by linarith, h1, h2, h3, ?_⟩
  have e : Real.log (U / (1 - U)) / 2 - Real.log (p / (1 - p)) / 2 =
      (Real.log (U / p) - Real.log ((1 - U) / (1 - p))) / 2 := by
    rw [Real.log_div hU0.ne' hU1.ne', Real.log_div hp.ne' hq.ne', Real.log_div hU0.ne' hp.ne',
      Real.log_div hU1.ne' hq.ne']
    ring
  rw [e, abs_div, abs_two]
  have := abs_sub (Real.log (U / p)) (Real.log ((1 - U) / (1 - p)))
  rw [div_le_iff₀ two_pos]
  linarith

/-- `lem:floor-estimator`, sample count: if `m ≥ (48/(γξ²)) ⌈log₂(4/ζ)⌉` then the Chernoff
bound `4 exp(-m γ τ²/3)` with `τ = ξ/4` is at most `ζ`. The multiplicative Chernoff bound itself
is not formalized. -/
theorem chernoff_exponent_le {γ ξ ζ m : ℝ} (hγ : 0 < γ) (hξ : 0 < ξ) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) (hm : 48 / (γ * ξ ^ 2) * ⌈Real.logb 2 (4 / ζ)⌉₊ ≤ m) :
    4 * Real.exp (-(m * γ * (ξ / 4) ^ 2 / 3)) ≤ ζ := by
  have h4 : 1 ≤ 4 / ζ := by rw [le_div_iff₀ hζ0]; linarith
  have hc := Nat.le_ceil (Real.logb 2 (4 / ζ))
  have hl := log_le_logb_two h4
  have hpos : 0 < γ * ξ ^ 2 := by positivity
  have hm' : (⌈Real.logb 2 (4 / ζ)⌉₊ : ℝ) ≤ m * γ * (ξ / 4) ^ 2 / 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at hm
    nlinarith
  have hexp : Real.exp (-(m * γ * (ξ / 4) ^ 2 / 3)) ≤ Real.exp (-Real.log (4 / ζ)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg (Real.log (4 / ζ)), Real.exp_log (by positivity), inv_div] at hexp
  linarith

/-- `lem:floor-estimator`: the paper's sample count
`m = ⌈(48/(γξ²)) ⌈log₂(4/ζ)⌉⌉` makes the Chernoff failure bound at most `ζ`. -/
theorem chernoff_exponent_le_of_ceil {γ ξ ζ : ℝ} (hγ : 0 < γ) (hξ : 0 < ξ) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) :
    4 * Real.exp (-((⌈48 / (γ * ξ ^ 2) * ⌈Real.logb 2 (4 / ζ)⌉₊⌉₊ : ℕ) * γ * (ξ / 4) ^ 2 / 3))
      ≤ ζ :=
  chernoff_exponent_le hγ hξ hζ0 hζ1 (Nat.le_ceil _)

/-- `lem:floor-estimator`: writing a positive number as `2^j y` with `1 ≤ y < 2`. -/
theorem exists_two_zpow_mul {x : ℝ} (hx : 0 < x) :
    ∃ j : ℤ, ∃ y : ℝ, 1 ≤ y ∧ y < 2 ∧ x = (2 : ℝ) ^ j * y := by
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) hx
  have h2 := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
  push_cast at h1 h2
  set j := Int.log 2 x
  have hj : (0 : ℝ) < (2 : ℝ) ^ j := zpow_pos two_pos j
  refine ⟨j, x / (2 : ℝ) ^ j, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hj]; linarith
  · rw [div_lt_iff₀ hj]
    rw [zpow_add_one₀ two_ne_zero] at h2
    linarith
  · field_simp

/-- `lem:floor-estimator`: for `1 ≤ y < 2` the variable `z = (y-1)/(y+1)` lies in `[0, 1/3)`
and `log y = 2 ∑_{r ≥ 0} z^{2r+1}/(2r+1)`. -/
theorem hasSum_log_of_mem_Ico {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y < 2) :
    0 ≤ (y - 1) / (y + 1) ∧ (y - 1) / (y + 1) < 1 / 3 ∧
      HasSum (fun r : ℕ => 2 * (((y - 1) / (y + 1)) ^ (2 * r + 1) / (2 * r + 1)))
        (Real.log y) := by
  set z := (y - 1) / (y + 1) with hz
  have hy : 0 < y + 1 := by linarith
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hy.le
  have hz1 : z < 1 / 3 := by rw [hz, div_lt_iff₀ hy]; linarith
  refine ⟨hz0, hz1, ?_⟩
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := z) (by rw [abs_of_nonneg hz0]; linarith)
  have e : Real.log (1 + z) - Real.log (1 - z) = Real.log y := by
    rw [← Real.log_div (by linarith) (by linarith)]
    congr 1
    rw [hz]
    field_simp
    ring
  rw [e] at h
  convert h using 1
  funext r
  ring

/-- `lem:floor-estimator`: the same series at `z = 1/3` computes `log 2`. -/
theorem hasSum_log_two :
    HasSum (fun r : ℕ => 2 * ((1 / 3 : ℝ) ^ (2 * r + 1) / (2 * r + 1))) (Real.log 2) := by
  have h := Real.hasSum_log_sub_log_of_abs_lt_one (x := (1 / 3 : ℝ)) (by norm_num [abs_of_pos])
  have e : Real.log (1 + 1 / 3) - Real.log (1 - 1 / 3) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [e] at h
  convert h using 1
  funext r
  ring

/-- `lem:floor-estimator`: the geometric tail. For `0 ≤ z < 1`, if the odd series has sum `s`,
then `0 ≤ s - 2∑_{r<n} z^{2r+1}/(2r+1) ≤ 2 z^{2n+1}/(1 - z²)`. -/
theorem odd_series_tail_le {z s : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hs : HasSum (fun r : ℕ => 2 * (z ^ (2 * r + 1) / (2 * r + 1))) s) (n : ℕ) :
    0 ≤ s - ∑ r ∈ Finset.range n, 2 * (z ^ (2 * r + 1) / (2 * r + 1)) ∧
      s - ∑ r ∈ Finset.range n, 2 * (z ^ (2 * r + 1) / (2 * r + 1)) ≤
        2 * z ^ (2 * n + 1) / (1 - z ^ 2) := by
  have htail := (hasSum_nat_add_iff' n).mpr hs
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg z) hz2).mul_left (2 * z ^ (2 * n + 1))
  constructor
  · refine hasSum_le (fun r => ?_) hasSum_zero htail
    positivity
  · have hle : ∀ r : ℕ, 2 * (z ^ (2 * (r + n) + 1) / (2 * ((r + n : ℕ) : ℝ) + 1)) ≤
        2 * z ^ (2 * n + 1) * (z ^ 2) ^ r := by
      intro r
      have hpow : z ^ (2 * (r + n) + 1) = z ^ (2 * n + 1) * (z ^ 2) ^ r := by
        rw [← pow_mul]; ring
      have hd : (1 : ℝ) ≤ 2 * ((r + n : ℕ) : ℝ) + 1 := by
        have : (0 : ℝ) ≤ ((r + n : ℕ) : ℝ) := by positivity
        linarith
      have hp : 0 ≤ z ^ (2 * (r + n) + 1) := by positivity
      rw [hpow] at hp ⊢
      have : z ^ (2 * n + 1) * (z ^ 2) ^ r / (2 * ((r + n : ℕ) : ℝ) + 1) ≤
          z ^ (2 * n + 1) * (z ^ 2) ^ r := div_le_self hp hd
      linarith
    have := hasSum_le hle htail hgeom
    rw [← div_eq_mul_inv] at this
    exact this

/-- `lem:floor-estimator`: for `1 ≤ y < 2` the truncation error after `n` terms is at most
`(3/4) 9^{-n}`, so `O(b)` terms give `b` bits. -/
theorem log_series_error_le {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y < 2) (n : ℕ) :
    0 ≤ Real.log y -
        ∑ r ∈ Finset.range n, 2 * (((y - 1) / (y + 1)) ^ (2 * r + 1) / (2 * r + 1)) ∧
      Real.log y -
        ∑ r ∈ Finset.range n, 2 * (((y - 1) / (y + 1)) ^ (2 * r + 1) / (2 * r + 1)) ≤
        3 / 4 * (1 / 9 : ℝ) ^ n := by
  obtain ⟨hz0, hz1, hs⟩ := hasSum_log_of_mem_Ico hy1 hy2
  obtain ⟨h1, h2⟩ := odd_series_tail_le hz0 (by linarith) hs n
  refine ⟨h1, h2.trans ?_⟩
  set z := (y - 1) / (y + 1)
  have hz2 : z ^ 2 ≤ 1 / 9 := by nlinarith
  have hpow : z ^ (2 * n + 1) ≤ (1 / 3) * (1 / 9 : ℝ) ^ n := by
    rw [pow_succ, pow_mul, mul_comm]
    exact mul_le_mul hz1.le (pow_le_pow_left₀ (sq_nonneg z) hz2 n) (by positivity)
      (by norm_num)
  rw [div_le_iff₀ (by nlinarith)]
  have h9 : (0 : ℝ) ≤ (1 / 9 : ℝ) ^ n := by positivity
  have hzp : 0 ≤ z ^ 2 := sq_nonneg z
  nlinarith

/-! ### Error ledgers -/

/-- `lem:floor-estimator`: the total error `ξ/3 + ξ/2 = 5ξ/6`. -/
theorem floor_error_total (ξ : ℝ) : ξ / 3 + ξ / 2 = 5 * ξ / 6 := by ring

/-- `sec:gls-validation-arithmetic`: `ξ/6 + ξ/8 + ξ/32 = 31ξ/96 < ξ/2`. -/
theorem wrapper_error_total {ξ : ℝ} (hξ : 0 < ξ) :
    ξ / 6 + ξ / 8 + ξ / 32 = 31 * ξ / 96 ∧ 31 * ξ / 96 < ξ / 2 := by
  constructor
  · ring
  · linarith

/-! ### Clipping (`sec:gls-validation-arithmetic`) -/

/-- `sec:gls-validation-arithmetic`: after clipping `U` to `[γ/2, 1 - γ/2]`, its centered logit
has magnitude at most `(1/2) log(2/γ)`. -/
theorem abs_clipped_logit_le {γ U : ℝ} (hγ0 : 0 < γ) (hU0 : γ / 2 ≤ U) (hU1 : U ≤ 1 - γ / 2) :
    |Real.log (U / (1 - U)) / 2| ≤ Real.log (2 / γ) / 2 := by
  have hU : 0 < U := by linarith
  have hU' : 0 < 1 - U := by linarith
  have hr : 0 < U / (1 - U) := div_pos hU hU'
  have hup : U / (1 - U) ≤ 2 / γ := by
    rw [div_le_div_iff₀ hU' hγ0]; nlinarith
  have hlo : γ / 2 ≤ U / (1 - U) := by
    rw [div_le_div_iff₀ two_pos hU']; nlinarith
  have h1 := Real.log_le_log hr hup
  have h2 := Real.log_le_log (by positivity) hlo
  have hinv : Real.log (γ / 2) = -Real.log (2 / γ) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv] at h2
  rw [abs_div, abs_two, div_le_div_iff_of_pos_right two_pos, abs_le]
  exact ⟨h2, h1⟩

/-- `sec:gls-validation-arithmetic`: the clipped magnitude `(1/2) log(2/γ)` is below the integer
`L = 1 + ⌈log₂(1/γ)⌉` of `sec:floor`. -/
theorem half_log_two_div_lt_floorL {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    Real.log (2 / γ) / 2 < floorL γ := by
  have hg : 1 ≤ 1 / γ := by rw [le_div_iff₀ hγ0]; linarith
  have hg2 : 1 ≤ 2 / γ := by rw [le_div_iff₀ hγ0]; linarith
  have h1 := log_le_logb_two hg2
  have e : Real.logb 2 (2 / γ) = 1 + Real.logb 2 (1 / γ) := by
    rw [show 2 / γ = 2 * (1 / γ) by ring, Real.logb_mul two_ne_zero (by positivity),
      logb_two_two]
  have h2 := Nat.le_ceil (Real.logb 2 (1 / γ))
  have h3 := Real.logb_nonneg one_lt_two hg
  unfold floorL
  push_cast
  linarith

/-- `sec:gls-validation-arithmetic`: in the smoothing application the floor is `γ = τ/2`; the
clipped magnitude `(1/2) log(2/γ) = (1/2) log(4/τ)` is below `L = ⌈log₂(4/τ)⌉ + 3`. -/
theorem half_log_lt_LOf (T : ℕ) (ε : ℝ) :
    Real.log (2 / (tauOf T ε / 2)) / 2 < LOf T ε := by
  have hτ : 0 < tauOf T ε := by unfold tauOf; positivity
  have hτ1 : tauOf T ε ≤ 1 := by
    unfold tauOf; exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  have e : 2 / (tauOf T ε / 2) = 4 / tauOf T ε := by field_simp; ring
  have h4 : 1 ≤ 4 / tauOf T ε := by rw [le_div_iff₀ hτ]; linarith
  have h1 := log_le_logb_two h4
  have h2 := Nat.le_ceil (Real.logb 2 (4 / tauOf T ε))
  have h3 := Real.log_nonneg h4
  rw [e]
  unfold LOf
  push_cast
  linarith

/-- `sec:gls-validation-arithmetic`: a cached answer within `1` of a value of magnitude at most
`L` has magnitude at most `L + 1`. -/
theorem abs_answer_le {A c e L : ℝ} (hc : |c| ≤ L) (hA : |A - c| ≤ e) (he : e ≤ 1) :
    |A| ≤ L + 1 := by
  calc |A| = |(A - c) + c| := by ring_nf
    _ ≤ |A - c| + |c| := abs_add_le _ _
    _ ≤ L + 1 := by linarith

/-! ### `sec:parity`: the majority count -/

/-- `sec:parity`: Hoeffding's exponent for the majority of `r` answers that are correct with
probability `1 - ν` is `2 r (1/2 - ν)² = r (1 - 2ν)²/2`. -/
theorem hoeffding_exponent_eq (r ν : ℝ) : 2 * r * (1 / 2 - ν) ^ 2 = r * (1 - 2 * ν) ^ 2 / 2 := by
  ring

/-- `sec:parity`: if `r ≥ (2/(1-2ν)²) ⌈log₂(n/δ)⌉` then `exp(-r(1-2ν)²/2) ≤ δ/n` (for any
noise rate `ν < 1/2`; the paper has `ν ∈ (0, 1/2)`). Hoeffding's inequality, which bounds the
majority error by this exponential, is not formalized. -/
theorem majority_exponent_le {ν δ r : ℝ} {n : ℕ} (hν1 : ν < 1 / 2) (hδ : 0 < δ)
    (hn : 1 ≤ n) (hr : 2 / (1 - 2 * ν) ^ 2 * ⌈Real.logb 2 (n / δ)⌉₊ ≤ r) :
    Real.exp (-(r * (1 - 2 * ν) ^ 2 / 2)) ≤ δ / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < (1 - 2 * ν) ^ 2 := by nlinarith
  have hc := Nat.le_ceil (Real.logb 2 (n / δ))
  have hc0 : (0 : ℝ) ≤ ⌈Real.logb 2 (n / δ)⌉₊ := by positivity
  have hr' : (⌈Real.logb 2 (n / δ)⌉₊ : ℝ) ≤ r * (1 - 2 * ν) ^ 2 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hs] at hr
    linarith
  by_cases hnd : 1 ≤ n / δ
  · have hl := log_le_logb_two hnd
    have hexp : Real.exp (-(r * (1 - 2 * ν) ^ 2 / 2)) ≤ Real.exp (-Real.log (n / δ)) :=
      Real.exp_le_exp.mpr (by linarith)
    rwa [Real.exp_neg (Real.log (n / δ)), Real.exp_log (by positivity), inv_div] at hexp
  · rw [not_le] at hnd
    have h1 : Real.exp (-(r * (1 - 2 * ν) ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 1 < δ / n := by
      rw [div_lt_one hδ] at hnd
      rw [lt_div_iff₀ hn']
      linarith
    linarith

/-- `sec:parity`: the paper's repetition count `r = ⌈(2/(1-2ν)²) ⌈log₂(n/δ)⌉⌉` gives per-coordinate
error exponent at most `δ/n`, and the union bound over the `n` coordinates gives `δ`. -/
theorem majority_union_bound {ν δ : ℝ} {n : ℕ} (hν1 : ν < 1 / 2) (hδ : 0 < δ)
    (hn : 1 ≤ n) :
    n * Real.exp (-((⌈2 / (1 - 2 * ν) ^ 2 * ⌈Real.logb 2 (n / δ)⌉₊⌉₊ : ℕ) *
      (1 - 2 * ν) ^ 2 / 2)) ≤ δ := by
  have h := majority_exponent_le hν1 hδ hn (Nat.le_ceil _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ) * Real.exp (-((⌈2 / (1 - 2 * ν) ^ 2 * ⌈Real.logb 2 (n / δ)⌉₊⌉₊ : ℕ) *
        (1 - 2 * ν) ^ 2 / 2)) ≤ n * (δ / n) := mul_le_mul_of_nonneg_left h hn'.le
    _ = δ := by field_simp

end LowLogitRank.Floor
