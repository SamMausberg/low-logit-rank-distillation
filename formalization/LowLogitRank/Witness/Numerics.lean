import LowLogitRank.Witness.General

/-!
# The numerical instance of the witness bound (`lem:explicit-gls-token-envelope`)

The parameters of `eq:explicit-gls-parameters` and the arithmetic of the paragraph
"Explicit witness bound": with `e₀ = g / (16 √(d J_b))`, `B = 24 K α`, `R = α`,
`K = 512 T d J_b`, `g = ε / (32 T²)`, every leverage bound `(16 √(d J_b) - 1)² / j` with
`j ≤ 64 d J_b` exceeds one, `B R / e₀ = 3 · 2^21 T³ d^{3/2} J_b^{3/2} α² / ε`,
`log₂ a₀ ≤ 46 + … ≤ 9 J_b`, and `d log₂ (1 + 64 J_b a₀) ≤ d (9 J_b + 7 + log₂ J_b) ≤ 11 d J_b`.
-/

namespace LowLogitRank.Witness

open Finset

/-! ### The parameters of `eq:explicit-gls-parameters` -/

/-- The factor bound `α = dL + 1`. -/
def alphaOf (d L : ℕ) : ℕ := d * L + 1

/-- `J_b = ⌈log₂ (2 T d α / (εδ))⌉ + 64`. -/
noncomputable def JbOf (T d L : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈Real.logb 2 (2 * T * d * alphaOf d L / (ε * δ))⌉₊ + 64

/-- `K = 512 T d J_b`. -/
noncomputable def KOf (T d L : ℕ) (ε δ : ℝ) : ℕ := 512 * T * d * JbOf T d L ε δ

/-- The discrepancy threshold `g = ε / (32 T²)`. -/
noncomputable def gOf (T : ℕ) (ε : ℝ) : ℝ := ε / (32 * T ^ 2)

/-- `b_ξ = min {b ∈ ℤ_{≥0} : 2^{-2b} ≤ g² / (1024² K² d J_b)}`. -/
noncomputable def bXiOf (T d L : ℕ) (ε δ : ℝ) : ℕ :=
  sInf {b : ℕ | ((2 : ℝ) ^ (2 * b))⁻¹ ≤
    gOf T ε ^ 2 / (1024 ^ 2 * (KOf T d L ε δ : ℝ) ^ 2 * d * JbOf T d L ε δ)}

/-- The oracle tolerance `ξ = 2^{-b_ξ}`. -/
noncomputable def xiOf (T d L : ℕ) (ε δ : ℝ) : ℝ := ((2 : ℝ) ^ bXiOf T d L ε δ)⁻¹

/-! ### Elementary facts about `log₂` -/

theorem logb_two_pow (k : ℕ) : Real.logb 2 ((2 : ℝ) ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- `log₂ n < n` for natural `n ≥ 1`. -/
theorem logb_natCast_lt (n : ℕ) (hn : 1 ≤ n) : Real.logb 2 n < n := by
  have h : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have := Real.logb_lt_logb (b := 2) (by norm_num) (by exact_mod_cast hn) h
  rwa [logb_two_pow] at this

/-- `7 + log₂ J ≤ 2 J` for natural `J ≥ 7`. -/
theorem seven_add_logb_le (J : ℕ) (hJ : 7 ≤ J) : 7 + Real.logb 2 J ≤ 2 * J := by
  have h : (J : ℝ) ≤ (2 : ℝ) ^ (J + (J - 7)) := by
    have : J < 2 ^ (J + (J - 7)) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast this.le
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast (by omega : 0 < J)) h
  rw [logb_two_pow] at this
  have hc : ((J + (J - 7) : ℕ) : ℝ) = 2 * J - 7 := by
    rw [Nat.cast_add, Nat.cast_sub hJ]; push_cast; ring
  rw [hc] at this
  linarith

/-! ### The leverage bound -/

/-- `lem:explicit-gls-token-envelope`: with `e₀ = g / (16 x)`,
`(g - e₀)² / (j e₀²) = (16 x - 1)² / j`. -/
theorem leverage_ratio_eq {g x j : ℝ} (hg : 0 < g) (hx : 0 < x) (hj : 0 < j) :
    (g - g / (16 * x)) ^ 2 / (j * (g / (16 * x)) ^ 2) = (16 * x - 1) ^ 2 / j := by
  field_simp

/-- `lem:explicit-gls-token-envelope`: `(16 √(d J_b) - 1)² / j > 1` for `1 ≤ j ≤ 64 d J_b`. -/
theorem one_lt_leverage_bound (d J j : ℕ) (hd : 1 ≤ d) (hJ : 1 ≤ J) (hj : 1 ≤ j)
    (hjle : j ≤ 64 * d * J) : 1 < (16 * √((d : ℝ) * J) - 1) ^ 2 / j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hdJ : (1 : ℝ) ≤ (d : ℝ) * J := by
    have : 1 ≤ d * J := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hx1 : 1 ≤ √((d : ℝ) * J) := Real.one_le_sqrt.mpr hdJ
  have hsq : √((d : ℝ) * J) ^ 2 = d * J := Real.sq_sqrt (by positivity)
  have hjle' : (j : ℝ) ≤ 64 * (d * J) := by
    have : ((j : ℕ) : ℝ) ≤ ((64 * d * J : ℕ) : ℝ) := by exact_mod_cast hjle
    push_cast at this; linarith
  rw [one_lt_div hjpos]
  nlinarith

/-! ### The determinant upper bound -/

/-- `lem:explicit-gls-token-envelope`: if `a₀ ≥ 1`, `log₂ a₀ ≤ 9 J_b` and `J_b ≥ 7`, then
`d log₂ (1 + 64 J_b a₀) ≤ d (9 J_b + 7 + log₂ J_b) ≤ 11 d J_b`. -/
theorem det_upper_le (d J : ℕ) (hJ : 7 ≤ J) {a₀ : ℝ} (ha : 1 ≤ a₀)
    (hlog : Real.logb 2 a₀ ≤ 9 * J) :
    d * Real.logb 2 (1 + 64 * J * a₀) ≤ d * (9 * J + 7 + Real.logb 2 J) ∧
      (d : ℝ) * (9 * J + 7 + Real.logb 2 J) ≤ 11 * d * J := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  constructor
  · apply mul_le_mul_of_nonneg_left _ hd0
    have h1 : 1 + 64 * J * a₀ ≤ (2 : ℝ) ^ 7 * J * a₀ := by nlinarith
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
      (by positivity), logb_two_pow] at h2
    push_cast at h2
    linarith
  · have := seven_add_logb_le J hJ
    nlinarith

/-! ### The substitution `B = 24 K α`, `R = α` -/

/-- `lem:explicit-gls-token-envelope`: with `B = 24 K α`, `R = α`, `K = 512 T d J_b`,
`g = ε/(32T²)` and `e₀ = g / (16 √(d J_b))`,
`B R / e₀ = 3 · 2^21 · T³ d^{3/2} J_b^{3/2} α² / ε`. -/
theorem BR_div_e0 (T d J : ℕ) (hT : 1 ≤ T) (hd : 1 ≤ d) (hJ : 1 ≤ J) (α ε : ℝ) (hε : 0 < ε) :
    24 * ((512 * T * d * J : ℕ) : ℝ) * α * α / ((ε / (32 * T ^ 2)) / (16 * √((d : ℝ) * J))) =
      3 * 2 ^ 21 * (T : ℝ) ^ 3 * (d : ℝ) ^ (3 / 2 : ℝ) * (J : ℝ) ^ (3 / 2 : ℝ) * α ^ 2 / ε := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have h32 : ∀ x : ℝ, 0 < x → x ^ (3 / 2 : ℝ) = x * √x := by
    intro x hx
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [h32 _ hd0, h32 _ hJ0, Real.sqrt_mul hd0.le]
  push_cast
  field_simp
  ring

/-- `a₀ = (B R / e₀)² = 9 · 2^42 · T⁶ d³ J_b³ α⁴ / ε²` for the same substitution. -/
theorem a0_eq (T d J : ℕ) (α ε : ℝ) (hε : 0 < ε) (hT : 1 ≤ T) (hd : 1 ≤ d) (hJ : 1 ≤ J) :
    (24 * ((512 * T * d * J : ℕ) : ℝ) * α * α / ((ε / (32 * T ^ 2)) / (16 * √((d : ℝ) * J))))
        ^ 2 = 9 * 2 ^ 42 * (T : ℝ) ^ 6 * (d : ℝ) ^ 3 * (J : ℝ) ^ 3 * α ^ 4 / ε ^ 2 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hdJ : (0 : ℝ) < d * J := by
    have : 0 < d * J := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hs : √((d : ℝ) * J) ^ 2 = d * J := Real.sq_sqrt hdJ.le
  have hs0 : 0 < √((d : ℝ) * J) := Real.sqrt_pos.mpr hdJ
  push_cast
  field_simp
  rw [hs]
  ring

/-- `lem:explicit-gls-token-envelope`: `log₂ a₀ ≤ 46 + 6 log₂ T + 3 log₂ d + 3 log₂ J_b
+ 4 log₂ α + 2 log₂ (1/ε)`. -/
theorem logb_a0_le (T d J : ℕ) (α ε : ℝ) (hT : 1 ≤ T) (hd : 1 ≤ d) (hJ : 1 ≤ J) (hα : 0 < α)
    (hε : 0 < ε) :
    Real.logb 2 (9 * 2 ^ 42 * (T : ℝ) ^ 6 * (d : ℝ) ^ 3 * (J : ℝ) ^ 3 * α ^ 4 / ε ^ 2) ≤
      46 + 6 * Real.logb 2 T + 3 * Real.logb 2 d + 3 * Real.logb 2 J + 4 * Real.logb 2 α +
        2 * Real.logb 2 (1 / ε) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have h9 : Real.logb 2 9 ≤ 4 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    norm_num
  have hε1 : 0 < 1 / ε := by positivity
  rw [show 9 * 2 ^ 42 * (T : ℝ) ^ 6 * (d : ℝ) ^ 3 * (J : ℝ) ^ 3 * α ^ 4 / ε ^ 2 =
      9 * 2 ^ 42 * (T : ℝ) ^ 6 * (d : ℝ) ^ 3 * (J : ℝ) ^ 3 * α ^ 4 * (1 / ε) ^ 2 by ring]
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    logb_two_pow, Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_pow]
  push_cast
  linarith

/-- `lem:explicit-gls-token-envelope`: if
`log₂ T + log₂ d + log₂ α + log₂ (1/ε) + log₂ (1/δ) ≤ J_b - 65`, the last four logarithms
are nonnegative and `J_b ≥ 1`, then
`46 + 6 log₂ T + 3 log₂ d + 3 log₂ J_b + 4 log₂ α + 2 log₂ (1/ε) ≤ 46 + 6 (J_b - 65) + 3 log₂ J_b
≤ 9 J_b`. -/
theorem logb_bound_le_nine (J : ℕ) (hJ : 1 ≤ J) {lT ld lα lε lδ : ℝ} (hd : 0 ≤ ld)
    (hα : 0 ≤ lα) (hε : 0 ≤ lε) (hδ : 0 ≤ lδ) (hS : lT + ld + lα + lε + lδ ≤ J - 65) :
    46 + 6 * lT + 3 * ld + 3 * Real.logb 2 J + 4 * lα + 2 * lε ≤
        46 + 6 * ((J : ℝ) - 65) + 3 * Real.logb 2 J ∧
      46 + 6 * ((J : ℝ) - 65) + 3 * Real.logb 2 J ≤ 9 * J := by
  have := logb_natCast_lt J hJ
  constructor <;> linarith

/-- `lem:explicit-gls-token-envelope`, from the definition of `J_b` in
`eq:explicit-gls-parameters`:
`log₂ T + log₂ d + log₂ α + log₂ (1/ε) + log₂ (1/δ) ≤ J_b - 65`. -/
theorem logb_sum_le_Jb (T d L : ℕ) (hT : 1 ≤ T) (hd : 1 ≤ d) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) :
    Real.logb 2 T + Real.logb 2 d + Real.logb 2 (alphaOf d L) + Real.logb 2 (1 / ε) +
      Real.logb 2 (1 / δ) ≤ (JbOf T d L ε δ : ℝ) - 65 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hα0 : (0 : ℝ) < alphaOf d L := by unfold alphaOf; positivity
  have hceil := Nat.le_ceil (Real.logb 2 (2 * T * d * alphaOf d L / (ε * δ)))
  have heq : Real.logb 2 (2 * T * d * alphaOf d L / (ε * δ)) =
      1 + Real.logb 2 T + Real.logb 2 d + Real.logb 2 (alphaOf d L) + Real.logb 2 (1 / ε) +
        Real.logb 2 (1 / δ) := by
    rw [show 2 * (T : ℝ) * d * alphaOf d L / (ε * δ) =
        2 * T * d * alphaOf d L * (1 / ε) * (1 / δ) by field_simp]
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
      (by positivity), Real.logb_mul (by positivity) (by positivity), Real.logb_mul
      (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_self_eq_one (by norm_num)]
  unfold JbOf
  push_cast
  linarith

theorem Jb_ge (T d L : ℕ) (ε δ : ℝ) : 64 ≤ JbOf T d L ε δ := by
  unfold JbOf; omega

/-- `lem:explicit-gls-token-envelope` and `sec:gls-validation-arithmetic`: with
`ξ ≤ g / (1024 K √(d J_b))` and `e₀ = g / (16 √(d J_b))`:
`24 K ξ ≤ (3/8) e₀ ≤ e₀`. -/
theorem residual_le (g K x ξ : ℝ) (hg : 0 < g) (hK : 0 < K) (hx : 0 < x)
    (hξ : ξ ≤ g / (1024 * K * x)) :
    24 * K * ξ ≤ 3 / 8 * (g / (16 * x)) ∧ 3 / 8 * (g / (16 * x)) ≤ g / (16 * x) := by
  constructor
  · calc 24 * K * ξ ≤ 24 * K * (g / (1024 * K * x)) := by gcongr
      _ = 3 / 8 * (g / (16 * x)) := by field_simp; ring
  · have : 0 < g / (16 * x) := by positivity
    linarith

/-- `eq:explicit-gls-parameters`: the chosen `ξ = 2^{-b_ξ}` satisfies
`ξ ≤ g / (1024 K √(d J_b))`. -/
theorem xi_le (T d L : ℕ) (hT : 1 ≤ T) (hd : 1 ≤ d) {ε δ : ℝ} (hε : 0 < ε) :
    xiOf T d L ε δ ≤
      gOf T ε / (1024 * KOf T d L ε δ * √((d : ℝ) * JbOf T d L ε δ)) := by
  have hJ : 1 ≤ JbOf T d L ε δ := le_trans (by norm_num) (Jb_ge T d L ε δ)
  have hK : 1 ≤ KOf T d L ε δ := by
    unfold KOf; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hJ0 : (0 : ℝ) < JbOf T d L ε δ := by exact_mod_cast hJ
  have hK0 : (0 : ℝ) < KOf T d L ε δ := by exact_mod_cast hK
  have hg : 0 < gOf T ε := by unfold gOf; positivity
  set X := gOf T ε ^ 2 / (1024 ^ 2 * (KOf T d L ε δ : ℝ) ^ 2 * d * JbOf T d L ε δ) with hX
  have hX0 : 0 < X := by positivity
  have hne : {b : ℕ | ((2 : ℝ) ^ (2 * b))⁻¹ ≤ X}.Nonempty := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hX0 (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    change ((2 : ℝ) ^ (2 * n))⁻¹ ≤ X
    calc ((2 : ℝ) ^ (2 * n))⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ := by
          gcongr
          · norm_num
          · omega
      _ = (1 / 2 : ℝ) ^ n := by rw [one_div, inv_pow]
      _ ≤ X := hn.le
  have hmem : ((2 : ℝ) ^ (2 * bXiOf T d L ε δ))⁻¹ ≤ X := Nat.sInf_mem hne
  have hsq : xiOf T d L ε δ ^ 2 ≤ X := by
    unfold xiOf; rw [inv_pow, ← pow_mul, mul_comm]; exact hmem
  have hxi0 : 0 ≤ xiOf T d L ε δ := by unfold xiOf; positivity
  have hs : √((d : ℝ) * JbOf T d L ε δ) ^ 2 = d * JbOf T d L ε δ := Real.sq_sqrt (by positivity)
  have hs0 : 0 < √((d : ℝ) * JbOf T d L ε δ) := Real.sqrt_pos.mpr (by positivity)
  have hX' : X = (gOf T ε / (1024 * KOf T d L ε δ * √((d : ℝ) * JbOf T d L ε δ))) ^ 2 := by
    rw [hX, div_pow, mul_pow, mul_pow, hs]; ring
  rw [hX'] at hsq
  exact (pow_le_pow_iff_left₀ hxi0 (by positivity) two_ne_zero).mp hsq

/-- `lem:explicit-gls-token-envelope`, all cuts together: if each of the `T ≥ 1` cuts receives
fewer than `64 d J_b` witnesses, the total is fewer than `64 T d J_b = K / 8`. -/
theorem total_lt (T d J : ℕ) (hT : 1 ≤ T) (a : ℕ → ℕ) (ha : ∀ t ∈ range T, a t < 64 * d * J) :
    ∑ t ∈ range T, a t < 64 * T * d * J ∧ 8 * (64 * T * d * J) = 512 * T * d * J := by
  refine ⟨?_, by ring⟩
  calc ∑ t ∈ range T, a t < ∑ _t ∈ range T, 64 * d * J :=
        Finset.sum_lt_sum_of_nonempty ⟨0, by simp; omega⟩ ha
    _ = 64 * T * d * J := by simp; ring

end LowLogitRank.Witness
