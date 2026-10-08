import LowLogitRank.Spanner.Prob

/-!
# The validation threshold (`sec:gls-validation-arithmetic`)

`Z` is the truncated residual of a fresh validation prefix, a random variable with values at most
one on a finite probability space, and `g ≥ 0` is the discrepancy threshold. If `E Z > 2 g`, then
`Pr{Z > g} > g`, and `n ≥ g⁻¹ log (1/δ')` independent copies all stay at or below `g` with
probability at most `δ'`.
-/

namespace LowLogitRank.Spanner

open Finset

variable {α : Type*} [Fintype α]

/-- `sec:gls-validation-arithmetic`: `E Z ≤ g + Pr{Z > g}` for `Z ≤ 1` and `g ≥ 0`. (The paper
has `Z ∈ [0,1]`; the lower bound is not needed.) -/
theorem expect_le_add_prob {μ : α → ℝ} (hμ : IsProb μ) {Z : α → ℝ} (hZ : ∀ a, Z a ≤ 1) {g : ℝ}
    (hg : 0 ≤ g) : expect μ Z ≤ g + wprob μ {a | g < Z a} := by
  classical
  have hpt : ∀ a, μ a * Z a ≤ g * μ a + {a | g < Z a}.indicator μ a := by
    intro a
    have h0 := hμ.nonneg a
    by_cases h : g < Z a
    · rw [Set.indicator_of_mem (show a ∈ {a | g < Z a} from h)]
      nlinarith [hZ a]
    · rw [Set.indicator_of_notMem (show a ∉ {a | g < Z a} from h)]
      push Not at h
      nlinarith
  calc expect μ Z = ∑ a, μ a * Z a := rfl
    _ ≤ ∑ a, (g * μ a + {a | g < Z a}.indicator μ a) := Finset.sum_le_sum fun a _ => hpt a
    _ = g + wprob μ {a | g < Z a} := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hμ.sum_eq, mul_one]; rfl

/-- `sec:gls-validation-arithmetic`: `E Z > 2 g` implies `Pr{Z > g} > g`. -/
theorem prob_gt_of_expect_gt {μ : α → ℝ} (hμ : IsProb μ) {Z : α → ℝ} (hZ : ∀ a, Z a ≤ 1)
    {g : ℝ} (hg : 0 ≤ g) (h : 2 * g < expect μ Z) : g < wprob μ {a | g < Z a} := by
  have := expect_le_add_prob hμ hZ hg
  linarith

/-- For `n` independent copies, `Pr{all copies ≤ g} = (1 - Pr{Z > g})^n`. -/
theorem wprob_all_le_eq (μ : α → ℝ) (hμ : IsProb μ) (Z : α → ℝ) (g : ℝ)
    (n : ℕ) : wprob (piW μ) {ω : Fin n → α | ∀ u, Z (ω u) ≤ g} =
      (1 - wprob μ {a | g < Z a}) ^ n := by
  have h := wprob_pi_forall (ι := Fin n) μ {a | Z a ≤ g}
  rw [Fintype.card_fin] at h
  have hc : {a | Z a ≤ g} = {a | g < Z a}ᶜ := by ext a; simp
  rw [hc, wprob_compl hμ] at h
  simpa [hc] using h

/-- `sec:gls-validation-arithmetic`: if `E Z > 2 g` with `0 < g`, the probability that `n`
independent copies all stay at or below `g` satisfies
`(1 - Pr{Z > g})^n ≤ (1 - g)^n ≤ e^{-g n} ≤ δ'` whenever `n ≥ g⁻¹ log (1/δ')`. -/
theorem miss_prob_chain {μ : α → ℝ} (hμ : IsProb μ) {Z : α → ℝ}
    (hZ : ∀ a, Z a ≤ 1) {g : ℝ} (hg : 0 < g) (h : 2 * g < expect μ Z) {δ' : ℝ} (hδ : 0 < δ')
    {n : ℕ} (hn : g⁻¹ * Real.log (1 / δ') ≤ n) :
    wprob (piW μ) {ω : Fin n → α | ∀ u, Z (ω u) ≤ g} = (1 - wprob μ {a | g < Z a}) ^ n ∧
      (1 - wprob μ {a | g < Z a}) ^ n ≤ (1 - g) ^ n ∧
      (1 - g) ^ n ≤ Real.exp (-(g * n)) ∧ Real.exp (-(g * n)) ≤ δ' := by
  have hp := prob_gt_of_expect_gt hμ hZ hg.le h
  have hp1 := wprob_le_one hμ {a | g < Z a}
  refine ⟨wprob_all_le_eq μ hμ Z g n, ?_, ?_, ?_⟩
  · exact pow_le_pow_left₀ (by linarith) (by linarith) n
  · calc (1 - g) ^ n ≤ Real.exp (-g) ^ n :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg g) n
      _ = Real.exp (-(g * n)) := by rw [← Real.exp_nat_mul]; ring_nf
  · have h1 : Real.log (1 / δ') ≤ g * n := by
      have := mul_le_mul_of_nonneg_left hn hg.le
      rwa [← mul_assoc, mul_inv_cancel₀ hg.ne', one_mul] at this
    calc Real.exp (-(g * n)) ≤ Real.exp (-Real.log (1 / δ')) := Real.exp_le_exp.mpr (by linarith)
      _ = δ' := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]

/-- `sec:gls-validation-arithmetic`: the missed-discrepancy bound. If `E Z > 2 g` and
`n ≥ g⁻¹ log (1/δ')`, all `n` copies stay at or below `g` with probability at most `δ'`. -/
theorem miss_prob_le {μ : α → ℝ} (hμ : IsProb μ) {Z : α → ℝ}
    (hZ : ∀ a, Z a ≤ 1) {g : ℝ} (hg : 0 < g) (h : 2 * g < expect μ Z) {δ' : ℝ} (hδ : 0 < δ')
    {n : ℕ} (hn : g⁻¹ * Real.log (1 / δ') ≤ n) :
    wprob (piW μ) {ω : Fin n → α | ∀ u, Z (ω u) ≤ g} ≤ δ' := by
  obtain ⟨h1, h2, h3, h4⟩ := miss_prob_chain hμ hZ hg h hδ hn
  rw [h1]; exact h2.trans (h3.trans h4)

/-- The validation sample size `n = ⌈g⁻¹ ⌈log₂ y⌉⌉` of `eq:explicit-gls-parameters` satisfies
`n ≥ g⁻¹ log y` for `y ≥ 1` (used with `y = 32 K T / δ`). -/
theorem ceil_validation_ge {g y : ℝ} (hg : 0 < g) (hy : 1 ≤ y) :
    g⁻¹ * Real.log y ≤ (⌈g⁻¹ * (⌈Real.logb 2 y⌉₊ : ℝ)⌉₊ : ℝ) := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hb : Real.log y ≤ ⌈Real.logb 2 y⌉₊ := by
    calc Real.log y ≤ Real.log y / Real.log 2 := by rw [le_div_iff₀ h2]; nlinarith
      _ = Real.logb 2 y := rfl
      _ ≤ _ := Nat.le_ceil _
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hg.le)).trans (Nat.le_ceil _)

/-- `sec:gls-validation-arithmetic`, explicit form: with `y ≥ 1` (the paper's `y = 32 K T / δ`) and
`n = ⌈g⁻¹ ⌈log₂ y⌉⌉` validation samples, a discrepancy with `E Z > 2 g` is missed with
probability at most `1 / y`. -/
theorem miss_prob_le_explicit {μ : α → ℝ} (hμ : IsProb μ) {Z : α → ℝ}
    (hZ : ∀ a, Z a ≤ 1) {g : ℝ} (hg : 0 < g) (h : 2 * g < expect μ Z) {y : ℝ} (hy : 1 ≤ y) :
    wprob (piW μ) {ω : Fin ⌈g⁻¹ * (⌈Real.logb 2 y⌉₊ : ℝ)⌉₊ → α | ∀ u, Z (ω u) ≤ g} ≤ 1 / y := by
  refine miss_prob_le hμ hZ hg h (by positivity) ?_
  rw [one_div_one_div]
  exact ceil_validation_ge hg hy

end LowLogitRank.Spanner
