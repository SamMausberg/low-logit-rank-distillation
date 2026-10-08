import LowLogitRank.Params

/-!
# Normalization and parameter arithmetic for a finite alphabet (`sec:alphabet`)

The proof of `thm:alphabet` corrects a polynomial approximation `g` of a next-token probability
vector `F` first for its sum and then for positivity. We check that algebra, the truncation
constants of the tensor Chebyshev bound, and the parameter arithmetic. The tensor Chebyshev
coefficient estimate itself is not formalized here.
-/

namespace LowLogitRank.AlphabetAlgebra

open Finset LowLogitRank.Params

/-! ### Normalization -/

section Normalization

variable {α : Type*} [Fintype α]

/-- The sum correction `r_y = g_y + (1 - ∑_z g_z)/A`. -/
noncomputable def sumCorrect (g : α → ℝ) : α → ℝ :=
  fun y => g y + (1 - ∑ z, g z) / Fintype.card α

/-- The positivity correction `q_y = (r_y + 3β)/(1 + 3Aβ)`. -/
noncomputable def posCorrect (β : ℝ) (r : α → ℝ) : α → ℝ :=
  fun y => (r y + 3 * β) / (1 + 3 * Fintype.card α * β)

/-- The uniform probability vector `U`. -/
noncomputable def uniform : α → ℝ := fun _ => 1 / Fintype.card α

variable [Nonempty α]

theorem card_pos_real : (0 : ℝ) < Fintype.card α := by
  exact_mod_cast Fintype.card_pos

/-- `sec:alphabet`: the sum-corrected polynomials sum to one. -/
theorem sum_sumCorrect (g : α → ℝ) : ∑ y, sumCorrect g y = 1 := by
  have hA := (card_pos_real (α := α)).ne'
  simp only [sumCorrect, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp
  ring

/-- `sec:alphabet`: if `|g_y - F_y| ≤ β` for every `y` and `∑ F = 1`, then `r` approximates `F`
within `2β`. -/
theorem abs_sumCorrect_sub_le {F g : α → ℝ} {β : ℝ} (hF : ∑ y, F y = 1)
    (hg : ∀ y, |g y - F y| ≤ β) (y : α) : |sumCorrect g y - F y| ≤ 2 * β := by
  have hA := card_pos_real (α := α)
  have hsum : |1 - ∑ z, g z| ≤ Fintype.card α * β := by
    rw [← hF, ← Finset.sum_sub_distrib]
    calc |∑ z, (F z - g z)| ≤ ∑ z, |F z - g z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _z : α, β := Finset.sum_le_sum (fun z _ => by rw [abs_sub_comm]; exact hg z)
      _ = Fintype.card α * β := by simp
  have e : sumCorrect g y - F y = (g y - F y) + (1 - ∑ z, g z) / Fintype.card α := by
    simp only [sumCorrect]; ring
  rw [e]
  calc |(g y - F y) + (1 - ∑ z, g z) / Fintype.card α|
      ≤ |g y - F y| + |(1 - ∑ z, g z) / Fintype.card α| := abs_add_le _ _
    _ ≤ β + β := by
        gcongr
        · exact hg y
        · rw [abs_div, abs_of_pos hA, div_le_iff₀ hA]; linarith
    _ = 2 * β := by ring

/-- `sec:alphabet`: the positivity-corrected values sum to one when `∑ r = 1` and `β ≥ 0`. -/
theorem sum_posCorrect {r : α → ℝ} {β : ℝ} (hβ : 0 ≤ β) (hr : ∑ y, r y = 1) :
    ∑ y, posCorrect β r y = 1 := by
  have hA := card_pos_real (α := α)
  have hden : 0 < 1 + 3 * (Fintype.card α : ℝ) * β := by positivity
  simp only [posCorrect, ← Finset.sum_div, Finset.sum_add_distrib, hr, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [div_eq_one_iff_eq hden.ne']
  ring

/-- `sec:alphabet`: if `r` is within `2β` of a nonnegative `F` and `β > 0`, every `q_y` is
strictly positive. -/
theorem posCorrect_pos {F r : α → ℝ} {β : ℝ} (hβ : 0 < β) (hF0 : ∀ y, 0 ≤ F y)
    (hr : ∀ y, |r y - F y| ≤ 2 * β) (y : α) : 0 < posCorrect β r y := by
  have hA := card_pos_real (α := α)
  have h := (abs_le.mp (hr y)).1
  have := hF0 y
  apply div_pos _ (by positivity)
  linarith

/-- `sec:alphabet`: the identity `q - F = ((r - F) + 3Aβ(U - F))/(1 + 3Aβ)`. -/
theorem posCorrect_sub_eq {F r : α → ℝ} {β : ℝ} (hβ : 0 ≤ β) (y : α) :
    posCorrect β r y - F y =
      ((r y - F y) + 3 * Fintype.card α * β * (uniform y - F y)) /
        (1 + 3 * Fintype.card α * β) := by
  have hA := card_pos_real (α := α)
  have hden : 0 < 1 + 3 * (Fintype.card α : ℝ) * β := by positivity
  simp only [posCorrect, uniform]
  field_simp
  ring

/-- `sec:alphabet`: the next-token TV discrepancy of `q` from a probability vector `F` is at most
`4Aβ` when `r` is within `2β` of `F` and `β ≥ 0`. -/
theorem tv_posCorrect_le {F r : α → ℝ} {β : ℝ} (hβ : 0 ≤ β) (hF0 : ∀ y, 0 ≤ F y)
    (hF : ∑ y, F y = 1) (hr : ∀ y, |r y - F y| ≤ 2 * β) :
    tv (posCorrect β r) F ≤ 4 * Fintype.card α * β := by
  have hA := card_pos_real (α := α)
  set A : ℝ := (Fintype.card α : ℝ) with hAdef
  have hden : 1 ≤ 1 + 3 * A * β := by
    have : 0 ≤ 3 * A * β := by positivity
    linarith
  have hU : ∑ y, |uniform y - F y| ≤ 2 := by
    calc ∑ y, |uniform y - F y| ≤ ∑ y, (uniform y + F y) := by
          apply Finset.sum_le_sum
          intro y _
          have h1 : 0 ≤ uniform (α := α) y := by simp only [uniform]; positivity
          rw [abs_le]; constructor <;> linarith [hF0 y]
      _ = 2 := by
          rw [Finset.sum_add_distrib, hF]
          simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
          ring
  have hpt : ∀ y, |posCorrect β r y - F y| ≤ |r y - F y| + 3 * A * β * |uniform y - F y| := by
    intro y
    rw [posCorrect_sub_eq hβ, ← hAdef, abs_div,
      abs_of_pos (show (0 : ℝ) < 1 + 3 * A * β by linarith)]
    rw [div_le_iff₀ (by linarith)]
    have h1 := abs_add_le (r y - F y) (3 * A * β * (uniform y - F y))
    rw [abs_mul (3 * A * β), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * A * β)] at h1
    have h2 : 0 ≤ |r y - F y| + 3 * A * β * |uniform y - F y| := by positivity
    nlinarith
  unfold tv
  rw [div_le_iff₀ two_pos]
  calc ∑ y, |posCorrect β r y - F y|
      ≤ ∑ y, (|r y - F y| + 3 * A * β * |uniform y - F y|) := Finset.sum_le_sum (fun y _ => hpt y)
    _ = ∑ y, |r y - F y| + 3 * A * β * ∑ y, |uniform y - F y| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ _y : α, 2 * β + 3 * A * β * 2 := by
        gcongr with y
        · exact hr y
    _ = 4 * A * β * 2 := by simp [A]; ring

/-- `sec:alphabet`, the normalization step of the proof of `thm:alphabet`. For a probability
vector `F` and `g` with `|g_y - F_y| ≤ β`, `β > 0`: `r = sumCorrect g` sums to one and is within
`2β` of `F`; `q = posCorrect β r` is strictly positive, sums to one, and is within TV `4Aβ`
of `F`. -/
theorem alphabet_normalization {F g : α → ℝ} {β : ℝ} (hβ : 0 < β) (hF0 : ∀ y, 0 ≤ F y)
    (hF : ∑ y, F y = 1) (hg : ∀ y, |g y - F y| ≤ β) :
    ∑ y, sumCorrect g y = 1 ∧ (∀ y, |sumCorrect g y - F y| ≤ 2 * β) ∧
      (∀ y, 0 < posCorrect β (sumCorrect g) y) ∧ ∑ y, posCorrect β (sumCorrect g) y = 1 ∧
      tv (posCorrect β (sumCorrect g)) F ≤ 4 * Fintype.card α * β := by
  have hr := abs_sumCorrect_sub_le hF hg
  exact ⟨sum_sumCorrect g, hr, posCorrect_pos hβ hF0 hr, sum_posCorrect hβ.le (sum_sumCorrect g),
    tv_posCorrect_le hβ.le hF0 hF hr⟩

end Normalization

/-! ### Truncation constants -/

section Truncation

variable {d T : ℕ}

/-- The ellipse parameter `ρ = 1 + 1/(4dT)`. -/
noncomputable def rhoOf (d T : ℕ) : ℝ := 1 + 1 / (4 * d * T)

theorem rhoOf_sub_one : rhoOf d T - 1 = 1 / (4 * d * T) := by unfold rhoOf; ring

theorem one_lt_rhoOf (hd : 1 ≤ d) (hT : 1 ≤ T) : 1 < rhoOf d T := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  unfold rhoOf
  have : 0 < 1 / (4 * (d : ℝ) * T) := by positivity
  linarith

/-- `sec:alphabet`: on the Bernstein ellipse of parameter `ρ` the imaginary part is at most
`(ρ - ρ⁻¹)/2 < 1/(4dT)`, so a logit `⟨x, w⟩` with `‖w‖_∞ ≤ T` has imaginary part `< 1/4`. -/
theorem ellipse_imag_bound (hd : 1 ≤ d) (hT : 1 ≤ T) :
    (rhoOf d T - (rhoOf d T)⁻¹) / 2 < 1 / (4 * d * T) ∧
      d * T * ((rhoOf d T - (rhoOf d T)⁻¹) / 2) < 1 / 4 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hρ := one_lt_rhoOf hd hT
  set x : ℝ := 1 / (4 * d * T) with hx
  have hx0 : 0 < x := by positivity
  have hρx : rhoOf d T = 1 + x := rfl
  have h1 : (rhoOf d T - (rhoOf d T)⁻¹) / 2 < x := by
    rw [hρx]
    have e : ((1 + x) - (1 + x)⁻¹) / 2 = x * (2 + x) / (2 * (1 + x)) := by
      field_simp; ring
    rw [e, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨h1, ?_⟩
  have hdt : (0 : ℝ) < d * T := by positivity
  have e : (d : ℝ) * T * x = 1 / 4 := by rw [hx]; field_simp
  calc (d : ℝ) * T * ((rhoOf d T - (rhoOf d T)⁻¹) / 2) < d * T * x :=
        mul_lt_mul_of_pos_left h1 hdt
    _ = 1 / 4 := e

/-- `sec:alphabet`: `1/cos(1/4) < 2`, the modulus bound for `F_{t,y}` on the ellipses. -/
theorem inv_cos_quarter_lt_two : (Real.cos (1 / 4))⁻¹ < 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := 1 / 4)
  have h' : (1 : ℝ) / 2 < 1 - (1 / 4) ^ 2 / 2 := by norm_num
  have hc : 1 / 2 < Real.cos (1 / 4) := lt_of_lt_of_le h' h
  rw [inv_lt_comm₀ (by linarith) two_pos]
  linarith

/-- `sec:alphabet`: `∑_{j > K} 2ρ^{-j} = 2ρ^{-K}/(ρ - 1)` for `ρ > 1`; with `K = 0` this gives
`∑_{j ≥ 0} v_j = 1 + 2/(ρ - 1)` for `v_0 = 1`, `v_j = 2ρ^{-j}`. -/
theorem hasSum_tail {ρ : ℝ} (hρ : 1 < ρ) (K : ℕ) :
    HasSum (fun j : ℕ => 2 * ρ⁻¹ ^ (j + K + 1)) (2 * ρ⁻¹ ^ K / (ρ - 1)) := by
  have hρ0 : 0 < ρ := by linarith
  have h0 : 0 ≤ ρ⁻¹ := by positivity
  have h1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ
  have hg := (hasSum_geometric_of_lt_one h0 h1).mul_left (2 * ρ⁻¹ ^ (K + 1))
  have e : 2 * ρ⁻¹ ^ (K + 1) * (1 - ρ⁻¹)⁻¹ = 2 * ρ⁻¹ ^ K / (ρ - 1) := by
    have h2 : ρ - 1 ≠ 0 := by linarith
    have h3 : 1 - ρ⁻¹ = (ρ - 1) / ρ := by field_simp
    rw [h3, inv_div, pow_succ]
    field_simp
  rw [e] at hg
  convert hg using 1
  funext j
  ring

/-- `sec:alphabet`: the truncation bound
`2d (∑_{j>K} v_j)(∑_{j≥0} v_j)^{d-1} = (4d/(ρ-1))(1 + 2/(ρ-1))^{d-1} ρ^{-K}`. -/
theorem truncation_eq (ρ : ℝ) (d K : ℕ) :
    2 * d * (2 * ρ⁻¹ ^ K / (ρ - 1)) * (1 + 2 * ρ⁻¹ ^ 0 / (ρ - 1)) ^ (d - 1) =
      4 * d / (ρ - 1) * (1 + 2 / (ρ - 1)) ^ (d - 1) * ρ⁻¹ ^ K := by
  simp only [pow_zero, mul_one]
  ring

/-- `sec:alphabet`: `(4d/(ρ-1))(1 + 2/(ρ-1))^{d-1} ≤ 2d(9dT)^d` for `ρ = 1 + 1/(4dT)`. -/
theorem truncation_const_le (hd : 1 ≤ d) (hT : 1 ≤ T) :
    4 * d / (rhoOf d T - 1) * (1 + 2 / (rhoOf d T - 1)) ^ (d - 1) ≤
      2 * d * (9 * d * T : ℝ) ^ d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rw [rhoOf_sub_one]
  have e1 : 4 * (d : ℝ) / (1 / (4 * d * T)) = 16 * d ^ 2 * T := by field_simp; ring
  have e2 : 1 + 2 / (1 / (4 * (d : ℝ) * T)) = 1 + 8 * d * T := by field_simp; ring
  rw [e1, e2]
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ (9 * ((m + 1 : ℕ) : ℝ) * T) m]
  set D : ℝ := ((m + 1 : ℕ) : ℝ)
  have hb : (1 : ℝ) + 8 * D * T ≤ 9 * D * T := by nlinarith
  have hp : (1 + 8 * D * T) ^ m ≤ (9 * D * T) ^ m := pow_le_pow_left₀ (by positivity) hb m
  have hq : (0 : ℝ) ≤ D ^ 2 * T := by positivity
  have hr : (0 : ℝ) ≤ (9 * D * T) ^ m := by positivity
  calc 16 * D ^ 2 * T * (1 + 8 * D * T) ^ m ≤ 16 * D ^ 2 * T * (9 * D * T) ^ m :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 16 * (D ^ 2 * T * (9 * D * T) ^ m) := by ring
    _ ≤ 18 * (D ^ 2 * T * (9 * D * T) ^ m) := by
        have : 0 ≤ D ^ 2 * T * (9 * D * T) ^ m := by positivity
        linarith
    _ = 2 * D * ((9 * D * T) ^ m * (9 * D * T)) := by ring

/-- `sec:alphabet`: `log ρ ≥ 1/(5dT)` for `ρ = 1 + 1/(4dT)`. -/
theorem log_rhoOf_ge (hd : 1 ≤ d) (hT : 1 ≤ T) : 1 / (5 * d * T) ≤ Real.log (rhoOf d T) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hρ := one_lt_rhoOf hd hT
  have h := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < rhoOf d T)
  have e : 1 - (rhoOf d T)⁻¹ = 1 / (4 * d * T + 1) := by
    unfold rhoOf; field_simp; ring
  rw [e] at h
  refine le_trans ?_ h
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- `sec:alphabet`: a degree `K ≥ 5dT log(2d(9dT)^d/β)` makes the truncation error
`2d(9dT)^d ρ^{-K}` at most `β`. -/
theorem truncation_le_of_degree (hd : 1 ≤ d) (hT : 1 ≤ T) {β : ℝ} (hβ : 0 < β) {K : ℕ}
    (hK : 5 * d * T * Real.log (2 * d * (9 * d * T : ℝ) ^ d / β) ≤ K) :
    2 * d * (9 * d * T : ℝ) ^ d * (rhoOf d T)⁻¹ ^ K ≤ β := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hρ := one_lt_rhoOf hd hT
  have hlog := log_rhoOf_ge hd hT
  set M : ℝ := 2 * d * (9 * d * T : ℝ) ^ d
  have hM : 0 < M := by positivity
  have h5 : (0 : ℝ) < 5 * d * T := by positivity
  have hKl : Real.log (M / β) ≤ K * Real.log (rhoOf d T) := by
    have : Real.log (M / β) ≤ K / (5 * d * T) := by
      rw [le_div_iff₀ h5]; linarith
    have h2 : (K : ℝ) / (5 * d * T) ≤ K * Real.log (rhoOf d T) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  have hpow : (rhoOf d T)⁻¹ ^ K = Real.exp (-(K * Real.log (rhoOf d T))) := by
    rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), inv_pow]
  rw [hpow]
  have hexp : Real.exp (-(K * Real.log (rhoOf d T))) ≤ Real.exp (-Real.log (M / β)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg (Real.log (M / β)), Real.exp_log (by positivity), inv_div] at hexp
  calc M * Real.exp (-(K * Real.log (rhoOf d T))) ≤ M * (β / M) :=
        mul_le_mul_of_nonneg_left hexp hM.le
    _ = β := by field_simp

end Truncation

/-! ### Parameters -/

section Parameters

/-- `H = T + A + d + C + ⌈log₂(1/a)⌉ + 10`. -/
noncomputable def alH (T A d C : ℕ) (a : ℝ) : ℕ := T + A + d + C + ⌈Real.logb 2 (1 / a)⌉₊ + 10

/-- `N = 100 H⁴`. -/
noncomputable def alN (T A d C : ℕ) (a : ℝ) : ℕ := 100 * alH T A d C a ^ 4

/-- `η = 2^{-N}`. -/
noncomputable def alEta (T A d C : ℕ) (a : ℝ) : ℝ := ((2 : ℝ) ^ alN T A d C a)⁻¹

/-- `β = η/(4A)`. -/
noncomputable def alBeta (T A d C : ℕ) (a : ℝ) : ℝ := alEta T A d C a / (4 * A)

/-- `K = 10 d T N`. -/
noncomputable def alK (T A d C : ℕ) (a : ℝ) : ℕ := 10 * d * T * alN T A d C a

/-- `R = binom(d + T d K, d)`. -/
noncomputable def alR (T A d C : ℕ) (a : ℝ) : ℕ := Nat.choose (d + T * d * alK T A d C a) d

variable {T A d C : ℕ} {a : ℝ}

theorem log_1001_lt_seven : Real.log 1001 < 7 := by
  have h1 : Real.log 1001 < Real.log ((2 : ℝ) ^ 10) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h1
  have := Real.log_two_lt_d9
  norm_num at h1 this
  linarith

/-- `sec:alphabet`: `log(2d(9dT)^d/β) = N log 2 + log(8Ad) + d log(9dT) ≤ 2N`. -/
theorem al_log_degree (hT : 1 ≤ T) (hA : 2 ≤ A) (hd : 1 ≤ d) :
    Real.log (2 * d * (9 * d * T : ℝ) ^ d / alBeta T A d C a) =
        alN T A d C a * Real.log 2 + Real.log (8 * A * d) + d * Real.log (9 * d * T) ∧
      alN T A d C a * Real.log 2 + Real.log (8 * A * d) + d * Real.log (9 * d * T) ≤
        2 * alN T A d C a := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hA' : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · have e : 2 * d * (9 * d * T : ℝ) ^ d / alBeta T A d C a =
        (2 : ℝ) ^ alN T A d C a * (8 * A * d) * (9 * d * T) ^ d := by
      unfold alBeta alEta
      field_simp
      ring
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow]
  · set H := alH T A d C a
    have hH : (T : ℝ) + A + d ≤ H := by
      unfold H alH; push_cast
      have : (0 : ℝ) ≤ C + ⌈Real.logb 2 (1 / a)⌉₊ := by positivity
      linarith
    have hH1 : (1 : ℝ) ≤ H := by linarith
    have h1 : Real.log (8 * A * d) ≤ 8 * A * d := log_le_self' (by positivity)
    have h2 : Real.log (9 * d * T) ≤ 9 * d * T := log_le_self' (by positivity)
    have h3 : (d : ℝ) * Real.log (9 * d * T) ≤ d * (9 * d * T) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have hAH : (A : ℝ) ≤ H := by linarith
    have hdH : (d : ℝ) ≤ H := by linarith
    have hTH : (T : ℝ) ≤ H := by linarith
    have h4 : 8 * (A : ℝ) * d ≤ 8 * H ^ 2 := by nlinarith
    have h5 : (d : ℝ) * (9 * d * T) ≤ 9 * H ^ 3 := by
      have : (d : ℝ) * d ≤ H * H := by nlinarith
      have : (d : ℝ) * d * T ≤ H * H * H := by
        apply mul_le_mul this hTH (by positivity) (by positivity)
      nlinarith
    have hN : (alN T A d C a : ℝ) = 100 * (H : ℝ) ^ 4 := by unfold alN; push_cast; rfl
    have hl2 := log_two_lt_one
    have hl2' := log_two_pos'
    have hH2 : (H : ℝ) ^ 2 ≤ H ^ 4 := pow_le_pow_right₀ hH1 (by norm_num)
    have hH3 : (H : ℝ) ^ 3 ≤ H ^ 4 := pow_le_pow_right₀ hH1 (by norm_num)
    rw [hN]
    have hH4 : (0 : ℝ) ≤ H ^ 4 := by positivity
    nlinarith

/-- `sec:alphabet`: "These degrees suffice": `5dT log(2d(9dT)^d/β) ≤ K = 10dTN`. -/
theorem al_degree_suffices (hT : 1 ≤ T) (hA : 2 ≤ A) (hd : 1 ≤ d) :
    5 * d * T * Real.log (2 * d * (9 * d * T : ℝ) ^ d / alBeta T A d C a) ≤
      alK T A d C a := by
  obtain ⟨e, h⟩ := al_log_degree (C := C) (a := a) hT hA hd
  rw [e]
  unfold alK
  push_cast
  have : (0 : ℝ) ≤ 5 * d * T := by positivity
  nlinarith

/-- `sec:alphabet`: `R = binom(d + TdK, d) ≤ (1001 H^8)^d`. -/
theorem alR_le : alR T A d C a ≤ (1001 * alH T A d C a ^ 8) ^ d := by
  set H := alH T A d C a
  have hdH : d ≤ H := by unfold H alH; omega
  have hTH : T ≤ H := by unfold H alH; omega
  have hH1 : 1 ≤ H := by unfold H alH; omega
  calc alR T A d C a ≤ (d + T * d * alK T A d C a) ^ d := Nat.choose_le_pow _ _
    _ ≤ (1001 * H ^ 8) ^ d := by
      apply Nat.pow_le_pow_left
      have e : T * d * alK T A d C a = 1000 * (d * T) ^ 2 * H ^ 4 := by
        unfold alK alN; ring
      rw [e]
      have h1 : d * T ≤ H * H := Nat.mul_le_mul hdH hTH
      have h2 : (d * T) ^ 2 ≤ (H * H) ^ 2 := Nat.pow_le_pow_left h1 2
      have h3 : d ≤ H ^ 8 := hdH.trans (Nat.le_self_pow (by norm_num) H)
      have h4 : (H * H) ^ 2 * H ^ 4 = H ^ 8 := by ring
      have h5 : 1000 * (d * T) ^ 2 * H ^ 4 ≤ 1000 * H ^ 8 := by
        calc 1000 * (d * T) ^ 2 * H ^ 4 ≤ 1000 * (H * H) ^ 2 * H ^ 4 := by gcongr
          _ = 1000 * H ^ 8 := by rw [mul_assoc, h4]
      omega

/-- The bound `log((q+1)T/a) ≤ 8H³ + 10H² + 3H + 1` for `q ≤ (2TAR/a)^C`. -/
theorem al_log_query_le (hT : 1 ≤ T) (hA : 2 ≤ A) (hd : 1 ≤ d) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (q : ℕ) (hq : (q : ℝ) ≤ (2 * T * A * alR T A d C a / a) ^ C) :
    Real.log ((q + 1) * T / a) ≤
      8 * (alH T A d C a : ℝ) ^ 3 + 10 * (alH T A d C a : ℝ) ^ 2 + 3 * alH T A d C a + 1 := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hA' : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set H := alH T A d C a
  set c : ℕ := ⌈Real.logb 2 (1 / a)⌉₊
  have hHdef : (H : ℝ) = T + A + d + C + c + 10 := by unfold H alH; push_cast; rfl
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have hH1 : (1 : ℝ) ≤ H := by linarith
  have hia : 1 ≤ 1 / a := by rw [le_div_iff₀ ha0]; linarith
  have hla : Real.log (1 / a) ≤ c := (log_le_logb_two hia).trans (Nat.le_ceil _)
  have hla0 : 0 ≤ Real.log (1 / a) := Real.log_nonneg hia
  have hR1 : (1 : ℝ) ≤ alR T A d C a := by
    have : 0 < alR T A d C a := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hRle : (alR T A d C a : ℝ) ≤ (1001 * (H : ℝ) ^ 8) ^ d := by exact_mod_cast alR_le
  have hlogR : Real.log (alR T A d C a) ≤ d * (Real.log 1001 + 8 * Real.log H) := by
    have := Real.log_le_log (by linarith) hRle
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  have hlogH : Real.log H ≤ H - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogT : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogA : Real.log A ≤ A - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have h1001 := log_1001_lt_seven
  have hl2 := log_two_lt_one
  -- `X = 2TAR/a`
  set X : ℝ := 2 * T * A * alR T A d C a / a with hX
  have hX1 : 1 ≤ X := by
    rw [hX, le_div_iff₀ ha0]
    have : (1 : ℝ) ≤ T * A := by nlinarith
    nlinarith
  have hlogX : Real.log X =
      Real.log 2 + Real.log T + Real.log A + Real.log (alR T A d C a) + Real.log (1 / a) := by
    rw [hX, div_eq_mul_one_div (2 * (T : ℝ) * A * alR T A d C a) a,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hdH : (d : ℝ) ≤ H := by linarith
  have hlogXle : Real.log X ≤ H + 8 * H ^ 2 := by
    have hdl : (d : ℝ) * (Real.log 1001 + 8 * Real.log H) ≤ d * (7 + 8 * (H - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have h1 : (d : ℝ) * (7 + 8 * (H - 1)) ≤ H * (8 * H) := by
      have : (d : ℝ) * (8 * H) ≤ H * (8 * H) := mul_le_mul_of_nonneg_right hdH (by positivity)
      nlinarith
    have h2 : (H : ℝ) * (8 * H) = 8 * H ^ 2 := by ring
    rw [hlogX]
    linarith
  have hCH : (C : ℝ) ≤ H := by linarith
  have hCX : (C : ℝ) * Real.log X ≤ H * (H + 8 * H ^ 2) :=
    mul_le_mul hCH hlogXle hlogX0 (by positivity)
  have hHH : (H : ℝ) * (H + 8 * H ^ 2) = H ^ 2 + 8 * H ^ 3 := by ring
  -- `q + 1 ≤ 2 X^C`
  have hXC : 1 ≤ X ^ C := one_le_pow₀ hX1
  have hq1 : (q : ℝ) + 1 ≤ 2 * X ^ C := by linarith
  have hq0 : (0 : ℝ) < q + 1 := by positivity
  have hlogq : Real.log ((q : ℝ) + 1) ≤ Real.log 2 + C * Real.log X := by
    have := Real.log_le_log hq0 hq1
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow] at this
    exact this
  have hsplit : Real.log ((q + 1) * T / a) =
      Real.log ((q : ℝ) + 1) + Real.log T + Real.log (1 / a) := by
    rw [div_eq_mul_one_div ((q + 1) * (T : ℝ)) a, Real.log_mul (by positivity) (by positivity),
      Real.log_mul hq0.ne' (by positivity)]
  have hH2 : (0 : ℝ) ≤ H ^ 2 := by positivity
  rw [hsplit]
  linarith only [hlogq, hCX, hHH, hlogT, hla, hHdef, hc0, hC0, hl2, hH2, hH1, hA', hd']

theorem al_poly_le {H : ℝ} (hH1 : 1 ≤ H) : 8 * H ^ 3 + 10 * H ^ 2 + 3 * H + 1 ≤ 22 * H ^ 3 := by
  have hH3 : H ≤ H ^ 3 := by
    calc H = H ^ 1 := (pow_one _).symm
      _ ≤ H ^ 3 := pow_le_pow_right₀ hH1 (by norm_num)
  have hH23 : H ^ 2 ≤ H ^ 3 := pow_le_pow_right₀ hH1 (by norm_num)
  have hH03 : 1 ≤ H ^ 3 := one_le_pow₀ hH1
  linarith

theorem al_poly_lt {H : ℝ} (hH1 : 1 ≤ H) : 22 * H ^ 3 < 100 * H ^ 4 * Real.log 2 := by
  have h69 : (69 : ℝ) / 100 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this; linarith
  have h34 : H ^ 3 ≤ H ^ 4 := pow_le_pow_right₀ hH1 (by norm_num)
  have h30 : 0 < H ^ 3 := by positivity
  have h4 : 0 ≤ 100 * H ^ 4 := by positivity
  have := mul_le_mul_of_nonneg_left h69 h4
  linarith

/-- `sec:alphabet`: for the fully inlined query cap `q ≤ (2TAR/a)^C`,
`log((q+1)T/a) ≤ 8H³ + 10H² + 3H + 1 ≤ 22H³ < N log 2`, hence `(q+1)Tη ≤ a`. -/
theorem al_query_budget (hT : 1 ≤ T) (hA : 2 ≤ A) (hd : 1 ≤ d) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (q : ℕ) (hq : (q : ℝ) ≤ (2 * T * A * alR T A d C a / a) ^ C) :
    Real.log ((q + 1) * T / a) ≤
        8 * (alH T A d C a : ℝ) ^ 3 + 10 * (alH T A d C a : ℝ) ^ 2 + 3 * alH T A d C a + 1 ∧
      8 * (alH T A d C a : ℝ) ^ 3 + 10 * (alH T A d C a : ℝ) ^ 2 + 3 * alH T A d C a + 1 ≤
        22 * (alH T A d C a : ℝ) ^ 3 ∧
      22 * (alH T A d C a : ℝ) ^ 3 < alN T A d C a * Real.log 2 ∧
      (q + 1) * T * alEta T A d C a ≤ a := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hH1 : (1 : ℝ) ≤ alH T A d C a := by
    have : 1 ≤ alH T A d C a := by unfold alH; omega
    exact_mod_cast this
  have first := al_log_query_le hT hA hd ha0 ha1 q hq
  have second := al_poly_le hH1
  have hN : (alN T A d C a : ℝ) = 100 * (alH T A d C a : ℝ) ^ 4 := by unfold alN; push_cast; rfl
  have third : 22 * (alH T A d C a : ℝ) ^ 3 < alN T A d C a * Real.log 2 := by
    rw [hN]; exact al_poly_lt hH1
  refine ⟨first, second, third, ?_⟩
  have hlt : Real.log ((q + 1) * T / a) < Real.log ((2 : ℝ) ^ alN T A d C a) := by
    rw [Real.log_pow]; linarith
  have hlt' := (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlt
  unfold alEta
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ ha0] at hlt'
  linarith

end Parameters

end LowLogitRank.AlphabetAlgebra
