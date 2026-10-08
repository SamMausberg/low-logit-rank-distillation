import LowLogitRank.Hardness.Event

/-!
# Advantage arithmetic for `thm:reduction` (`eq:hard-advantage`) and `cor:allTV`
-/

namespace LowLogitRank.Hardness

open Filter Topology

/-- The bracket estimate behind both advantage bounds: for `0 ≤ δ ≤ 1`, `0 ≤ η ≤ 1`, `q ≥ 0`,
`(1-δ)[(1-η)^K (1 - q/2^m) - ε] ≥ (1-δ)(1-ε) - Kη - q/2^m`. -/
theorem bracket_ge {δ ε η q : ℝ} (K m : ℕ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (hq : 0 ≤ q) :
    (1 - δ) * (1 - ε) - K * η - q / 2 ^ m ≤ (1 - δ) * ((1 - η) ^ K * (1 - q / 2 ^ m) - ε) := by
  set u := (1 - η) ^ K
  set w := q / 2 ^ m
  have hw : 0 ≤ w := by positivity
  have hu1 : u ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hu0 : 0 ≤ u := pow_nonneg (by linarith) _
  have hbern : 1 - K * η ≤ u := by
    have := one_add_mul_le_pow (a := -η) (by linarith) K
    rw [← sub_eq_add_neg] at this
    linarith
  have hKη : 0 ≤ (K : ℝ) * η := by positivity
  have huv : (1 - w) - K * η ≤ u * (1 - w) := by
    rcases le_or_gt 0 (1 - w) with hv | hv
    · nlinarith
    · nlinarith
  nlinarith

/-- The advantage bound `eq:hard-advantage`:
`(1-δ)[(1-η)^{L+1}(1 - q/2^n) - ε] - qη - 1/2`. -/
noncomputable def hardAdvantage (n L : ℕ) (ε δ η q : ℝ) : ℝ :=
  (1 - δ) * ((1 - η) ^ (L + 1) * (1 - q / 2 ^ n) - ε) - q * η - 1 / 2

/-- `eq:hard-advantage` at `ε = δ = 1/100` is at least `0.4801 - (L+1)η - q/2^n - qη`, for every
`0 ≤ η ≤ 1` and `q ≥ 0`. -/
theorem hardAdvantage_ge {η q : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hq : 0 ≤ q) (n L : ℕ) :
    4801 / 10000 - (L + 1) * η - q / 2 ^ n - q * η ≤
      hardAdvantage n L (1 / 100) (1 / 100) η q := by
  have := bracket_ge (ε := 1 / 100) (L + 1) n (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num)
    hη0 hη1 hq
  unfold hardAdvantage
  push_cast at this
  linarith

/-- With `η = (1 + 2^{2n})⁻¹ ≤ 2^{-2n}`: the advantage at `ε = δ = 1/100` is at least
`0.4801 - (L + 1 + q)/2^{2n} - q/2^n`. -/
theorem hardAdvantage_ge_hard {q : ℝ} (hq : 0 ≤ q) (n L : ℕ) :
    4801 / 10000 - (L + 1 + q) / 2 ^ (2 * n) - q / 2 ^ n ≤
      hardAdvantage n L (1 / 100) (1 / 100) (hardEta n) q := by
  have h0 := (hardEta_pos n).le
  have h1 : hardEta n ≤ 1 := by rw [← etaOf_hardB]; exact (etaOf_lt_one _).le
  have h2 := hardEta_le n
  have := hardAdvantage_ge h0 h1 hq n L
  have h3 : ((L : ℝ) + 1 + q) * hardEta n ≤ (L + 1 + q) / 2 ^ (2 * n) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

/-- `0.4801 - o(1)`: if `L(n) + 1 ≤ C (n+1)^c` and `0 ≤ q(n) ≤ C (n+1)^c` for all `n`, then for
every `θ > 0` the advantage at `ε = δ = 1/100` is eventually at least `0.4801 - θ`. (The base
`n + 1` keeps the hypotheses satisfiable at `n = 0`; any polynomial bounds, such as
`L = n(S(n)+1)` with `S` polynomial, have this form.) -/
theorem hardAdvantage_eventually (L : ℕ → ℕ) (q : ℕ → ℝ) (C : ℝ) (c : ℕ)
    (hq0 : ∀ n, 0 ≤ q n) (hL : ∀ n, (L n : ℝ) + 1 ≤ C * ((n : ℝ) + 1) ^ c)
    (hq : ∀ n, q n ≤ C * ((n : ℝ) + 1) ^ c) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n in atTop, 4801 / 10000 - θ ≤
      hardAdvantage n (L n) (1 / 100) (1 / 100) (hardEta n) (q n) := by
  have hbase := ((tendsto_pow_const_div_const_pow_of_one_lt c (one_lt_two (α := ℝ))).comp
    (tendsto_add_atTop_nat 1)).const_mul (6 * C)
  rw [mul_zero] at hbase
  have hlim : Tendsto (fun n : ℕ => 3 * C * (((n : ℝ) + 1) ^ c / 2 ^ n)) atTop (𝓝 0) := by
    refine hbase.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    rw [pow_succ]
    field_simp
    ring
  filter_upwards [hlim.eventually (gt_mem_nhds hθ)] with n hn
  have h1 := hardAdvantage_ge_hard (hq0 n) n (L n)
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hle : (2 : ℝ) ^ n ≤ 2 ^ (2 * n) := pow_le_pow_right₀ one_le_two (by omega)
  have hnum : 0 ≤ (L n : ℝ) + 1 + q n := by have := hq0 n; positivity
  have h2 : ((L n : ℝ) + 1 + q n) / 2 ^ (2 * n) ≤ ((L n : ℝ) + 1 + q n) / 2 ^ n :=
    div_le_div_of_nonneg_left hnum hp hle
  have h3 : ((L n : ℝ) + 1 + q n) / 2 ^ n + q n / 2 ^ n ≤
      3 * C * (((n : ℝ) + 1) ^ c / 2 ^ n) := by
    rw [← add_div, mul_div_assoc', div_le_div_iff_of_pos_right hp]
    linarith [hL n, hq n]
  linarith

/-- The hypotheses of `hardAdvantage_eventually` hold for polynomial growth, e.g. `L(n) = n(n+1)`
and `q(n) = n²` with `C = 1`, `c = 2`; for these the advantage is eventually at least
`0.4801 - θ`. -/
theorem hardAdvantage_eventually_example {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n in atTop, 4801 / 10000 - θ ≤
      hardAdvantage n (n * (n + 1)) (1 / 100) (1 / 100) (hardEta n) ((n : ℝ) ^ 2) :=
  hardAdvantage_eventually (fun n => n * (n + 1)) (fun n => (n : ℝ) ^ 2) 1 2
    (fun n => by positivity) (fun n => by push_cast; nlinarith)
    (fun n => by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hθ

/-! ### `cor:allTV` -/

/-- The advantage bound in the proof of `cor:allTV`:
`(1-δ)[(1-η)^{r(L+1)}(1 - q/2^m) - ε] - qη - 2^{-r}`. -/
noncomputable def weakAdvantage (m L r : ℕ) (ε δ η q : ℝ) : ℝ :=
  (1 - δ) * ((1 - η) ^ (r * (L + 1)) * (1 - q / 2 ^ m) - ε) - q * η - (1 / 2) ^ r

/-- `cor:allTV`: with `a₀ = (1-δ)(1-ε)`, the advantage is at least
`a₀ - 2^{-r} - r(L+1)η - q/2^m - qη`. -/
theorem weakAdvantage_ge {ε δ η q : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hq : 0 ≤ q) (m L r : ℕ) :
    (1 - δ) * (1 - ε) - (1 / 2) ^ r - r * (L + 1) * η - q / 2 ^ m - q * η ≤
      weakAdvantage m L r ε δ η q := by
  have := bracket_ge (ε := ε) (r * (L + 1)) m hδ0 hδ1 hη0 hη1 hq
  unfold weakAdvantage
  push_cast at this
  linarith

/-- The block count `r = ⌈log₂(2/a₀)⌉` of `cor:allTV`. -/
noncomputable def blockCount (a₀ : ℝ) : ℕ := ⌈Real.logb 2 (2 / a₀)⌉₊

/-- `cor:allTV`: `2^{-r} ≤ a₀/2` for `r = ⌈log₂(2/a₀)⌉`, so `a₀ - 2^{-r} ≥ a₀/2`. -/
theorem half_pow_blockCount_le {a₀ : ℝ} (ha : 0 < a₀) : (1 / 2 : ℝ) ^ blockCount a₀ ≤ a₀ / 2 := by
  have hr : Real.logb 2 (2 / a₀) ≤ blockCount a₀ := Nat.le_ceil _
  have h2 : (2 : ℝ) / a₀ ≤ 2 ^ blockCount a₀ := by
    calc (2 : ℝ) / a₀ = 2 ^ Real.logb 2 (2 / a₀) :=
          (Real.rpow_logb two_pos (by norm_num) (by positivity)).symm
      _ ≤ (2 : ℝ) ^ (blockCount a₀ : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hr
      _ = 2 ^ blockCount a₀ := Real.rpow_natCast _ _
  rw [one_div_pow]
  rw [div_le_iff₀ ha] at h2
  rw [div_le_div_iff₀ (by positivity) two_pos]
  linarith

theorem sub_half_pow_blockCount {a₀ : ℝ} (ha : 0 < a₀) :
    a₀ / 2 ≤ a₀ - (1 / 2 : ℝ) ^ blockCount a₀ := by
  have := half_pow_blockCount_le ha
  linarith

/-- The index width `s = ⌈log₂ r⌉` of `cor:allTV` accommodates `r` indices: `r ≤ 2^s`. -/
theorem le_two_pow_indexBits {r : ℕ} (hr : 1 ≤ r) : r ≤ 2 ^ ⌈Real.logb 2 r⌉₊ := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have : (r : ℝ) ≤ 2 ^ ⌈Real.logb 2 r⌉₊ := by
    calc (r : ℝ) = 2 ^ Real.logb 2 r := (Real.rpow_logb two_pos (by norm_num) hr').symm
      _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 r⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
      _ = 2 ^ ⌈Real.logb 2 r⌉₊ := Real.rpow_natCast _ _
  exact_mod_cast this

end LowLogitRank.Hardness
