import LowLogitRank.CoverDyadic

/-!
# Likelihood selection of `sec:sample-upper`

The Hellinger affinity, the selection bound for an empirical maximum-likelihood candidate over a
finite set of candidates, the explicit integer sample size, and the resulting sample bound of
`thm:cover`.

Probabilities over `m` independent samples are finite sums with product weights (`prodProb`).
-/

namespace LowLogitRank.Cover

open Finset Real

variable {Ω : Type*} [Fintype Ω]

/-! ### Hellinger affinity -/

/-- The Hellinger affinity `A(P, Q) = ∑ √(P(z) Q(z))` of `sec:sample-upper`. -/
noncomputable def affinity (P Q : Ω → ℝ) : ℝ := ∑ z, √(P z * Q z)

theorem affinity_nonneg (P Q : Ω → ℝ) : 0 ≤ affinity P Q :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- `sec:sample-upper` (Cauchy–Schwarz): `TV(P,Q)² ≤ 1 - A(P,Q)²` for probability vectors. -/
theorem tv_sq_le (P Q : Ω → ℝ) (hP : ∀ z, 0 ≤ P z) (hQ : ∀ z, 0 ≤ Q z) (hP1 : ∑ z, P z = 1)
    (hQ1 : ∑ z, Q z = 1) : tv P Q ^ 2 ≤ 1 - affinity P Q ^ 2 := by
  have hsP : ∀ z, √(P z) ^ 2 = P z := fun z => Real.sq_sqrt (hP z)
  have hsQ : ∀ z, √(Q z) ^ 2 = Q z := fun z => Real.sq_sqrt (hQ z)
  have hPQ : ∀ z, √(P z * Q z) = √(P z) * √(Q z) := fun z => Real.sqrt_mul (hP z) _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun z => |√(P z) - √(Q z)|)
    (fun z => √(P z) + √(Q z))
  have e1 : ∀ z, |√(P z) - √(Q z)| * (√(P z) + √(Q z)) = |P z - Q z| := by
    intro z
    have h0 : 0 ≤ √(P z) + √(Q z) := by positivity
    calc |√(P z) - √(Q z)| * (√(P z) + √(Q z))
        = |(√(P z) - √(Q z)) * (√(P z) + √(Q z))| := by rw [abs_mul, abs_of_nonneg h0]
      _ = |P z - Q z| := by congr 1; linear_combination hsP z - hsQ z
  have e2 : ∑ z, |√(P z) - √(Q z)| ^ 2 = 2 - 2 * affinity P Q := by
    simp only [sq_abs, sub_sq, hsP, hsQ, affinity, hPQ, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hP1, hQ1, Finset.mul_sum]
    ring_nf
  have e3 : ∑ z, (√(P z) + √(Q z)) ^ 2 = 2 + 2 * affinity P Q := by
    simp only [add_sq, hsP, hsQ, affinity, hPQ, Finset.sum_add_distrib, hP1, hQ1, Finset.mul_sum]
    ring_nf
  simp only [e1, e2, e3] at hcs
  unfold tv
  nlinarith

/-- `√(1 - ε²) ≤ e^{-ε²/2}` (`sec:sample-upper`). -/
theorem sqrt_one_sub_sq_le (ε : ℝ) : √(1 - ε ^ 2) ≤ exp (-(ε ^ 2) / 2) := by
  rw [Real.exp_half]
  exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp (-(ε ^ 2))])

/-- `eq:bestKL` implies `KL(P ‖ Q_*) ≤ a`: if `|ln (Q(z)/P(z))| ≤ a` for all `z` then
`∑ P(z) ln (P(z)/Q(z)) ≤ a`. -/
theorem kl_le_of_abs_log_ratio_le (P Q : Ω → ℝ) (hP : ∀ z, 0 ≤ P z) (hP1 : ∑ z, P z = 1) {a : ℝ}
    (ha : ∀ z, |log (Q z / P z)| ≤ a) : ∑ z, P z * log (P z / Q z) ≤ a := by
  calc ∑ z, P z * log (P z / Q z) ≤ ∑ z, P z * a := by
        refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hP z)
        rw [← inv_div, Real.log_inv]
        exact (neg_le_abs _).trans (ha z)
    _ = a := by rw [← Finset.sum_mul, hP1, one_mul]

/-! ### Probabilities over independent samples -/

open Classical in
/-- The probability of an event under `m` independent samples from `P`: the total product weight
`∏ i, P (Z i)` of the samples `Z : Fin m → Ω` in the event. -/
noncomputable def prodProb (P : Ω → ℝ) (m : ℕ) (S : (Fin m → Ω) → Prop) : ℝ :=
  ∑ Z, if S Z then ∏ i, P (Z i) else 0

theorem prodProb_nonneg (P : Ω → ℝ) (hP : ∀ z, 0 ≤ P z) (m : ℕ) (S : (Fin m → Ω) → Prop) :
    0 ≤ prodProb P m S := by
  classical
  unfold prodProb
  refine Finset.sum_nonneg fun Z _ => ?_
  split_ifs
  · exact Finset.prod_nonneg fun i _ => hP _
  · exact le_rfl

theorem prodProb_mono (P : Ω → ℝ) (hP : ∀ z, 0 ≤ P z) (m : ℕ) {S S' : (Fin m → Ω) → Prop}
    (h : ∀ Z, S Z → S' Z) : prodProb P m S ≤ prodProb P m S' := by
  classical
  unfold prodProb
  refine Finset.sum_le_sum fun Z _ => ?_
  by_cases hS : S Z
  · simp only [hS, h Z hS, ↓reduceIte, le_refl]
  · simp only [hS, ↓reduceIte]; split_ifs
    · exact Finset.prod_nonneg fun i _ => hP _
    · exact le_rfl

theorem prodProb_false (P : Ω → ℝ) (m : ℕ) : prodProb P m (fun _ => False) = 0 := by
  classical
  simp [prodProb]

/-- The union bound. -/
theorem prodProb_le_sum {C : Type*} [Fintype C] (P : Ω → ℝ) (hP : ∀ z, 0 ≤ P z) (m : ℕ)
    (S : (Fin m → Ω) → Prop) (E : C → (Fin m → Ω) → Prop) (h : ∀ Z, S Z → ∃ c, E c Z) :
    prodProb P m S ≤ ∑ c, prodProb P m (E c) := by
  classical
  unfold prodProb
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun Z _ => ?_
  have hw : 0 ≤ ∏ i, P (Z i) := Finset.prod_nonneg fun i _ => hP _
  have hnn : ∀ c ∈ (Finset.univ : Finset C), 0 ≤ if E c Z then ∏ i, P (Z i) else 0 :=
    fun c _ => by split_ifs <;> simp [hw]
  by_cases hS : S Z
  · obtain ⟨c, hc⟩ := h Z hS
    simp only [hS, ↓reduceIte]
    calc ∏ i, P (Z i) = if E c Z then ∏ i, P (Z i) else 0 := by simp only [hc, ↓reduceIte]
      _ ≤ _ := Finset.single_le_sum hnn (Finset.mem_univ c)
  · simp only [hS, ↓reduceIte]; exact Finset.sum_nonneg hnn

/-- `sec:sample-upper`, Markov's inequality applied to the square root of the likelihood ratio:
`Pr{∏ Q(Z_i)/P(Z_i) ≥ θ} ≤ θ^{-1/2} A(P,Q)^m`. -/
theorem markov_sqrt (P Q : Ω → ℝ) (hP : ∀ z, 0 < P z) (hQ : ∀ z, 0 ≤ Q z) (m : ℕ) {θ : ℝ}
    (hθ : 0 < θ) :
    prodProb P m (fun Z => θ ≤ ∏ i, Q (Z i) / P (Z i)) ≤ (√θ)⁻¹ * affinity P Q ^ m := by
  classical
  have hsθ : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hR : ∀ Z : Fin m → Ω, 0 ≤ ∏ i, Q (Z i) / P (Z i) :=
    fun Z => Finset.prod_nonneg fun i _ => div_nonneg (hQ _) (hP _).le
  have hpt : ∀ z, P z * √(Q z / P z) = √(P z * Q z) := by
    intro z
    have hz := hP z
    rw [show P z * Q z = (P z * P z) * (Q z / P z) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_mul_self hz.le]
  calc prodProb P m (fun Z => θ ≤ ∏ i, Q (Z i) / P (Z i))
      ≤ ∑ Z : Fin m → Ω, (√θ)⁻¹ * ((∏ i, P (Z i)) * √(∏ i, Q (Z i) / P (Z i))) := by
        unfold prodProb
        refine Finset.sum_le_sum fun Z _ => ?_
        have hw : 0 ≤ ∏ i, P (Z i) := Finset.prod_nonneg fun i _ => (hP _).le
        split_ifs with hZ
        · have h1 : √θ ≤ √(∏ i, Q (Z i) / P (Z i)) := Real.sqrt_le_sqrt hZ
          rw [← mul_assoc, mul_comm (√θ)⁻¹, mul_assoc]
          refine le_mul_of_one_le_right hw ?_
          rw [inv_mul_eq_div, one_le_div hsθ]; exact h1
        · positivity
    _ = (√θ)⁻¹ * ∑ Z : Fin m → Ω, ∏ i, √(P (Z i) * Q (Z i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [Real.sqrt_prod _ (fun i _ => div_nonneg (hQ _) (hP _).le), ← Finset.prod_mul_distrib]
        simp only [hpt]
    _ = (√θ)⁻¹ * affinity P Q ^ m := by
        rw [← Fintype.prod_sum (fun (_ : Fin m) z => √(P z * Q z))]
        simp [affinity]

/-! ### Likelihood selection -/

/-- The likelihood-selection argument of `sec:sample-upper`. Let `P` be a strictly positive
probability vector, `Q c` (`c ∈ C`, `|C| = N`) probability vectors (not necessarily in the class),
and `Q c_*` strictly positive with `|ln (Q_{c_*}(z)/P(z))| ≤ a` for all `z`. For any rule `ĉ`
choosing, for each sample `Z ∈ Ω^m`, a candidate of maximal likelihood `∏ Q_c(Z_i)`,
`Pr{TV(P, Q_ĉ) > ε} ≤ N e^{ma/2} (√(1 - ε²))^m`, which is the paper's `N e^{ma/2} (1 - ε²)^{m/2}`
for `ε ≤ 1`. -/
theorem likelihood_selection {C : Type*} [Fintype C] (P : Ω → ℝ) (hP : ∀ z, 0 < P z)
    (hP1 : ∑ z, P z = 1) (Q : C → Ω → ℝ) (hQ : ∀ c z, 0 ≤ Q c z) (hQ1 : ∀ c, ∑ z, Q c z = 1)
    (cstar : C) {a : ℝ} (hpos : ∀ z, 0 < Q cstar z) (ha : ∀ z, |log (Q cstar z / P z)| ≤ a)
    (m : ℕ) (sel : (Fin m → Ω) → C)
    (hsel : ∀ Z c, ∏ i, Q c (Z i) ≤ ∏ i, Q (sel Z) (Z i)) {ε : ℝ} (hε : 0 ≤ ε) :
    prodProb P m (fun Z => ε < tv P (Q (sel Z))) ≤
      Fintype.card C * (exp (m * a / 2) * √(1 - ε ^ 2) ^ m) := by
  classical
  have hP0 : ∀ z, 0 ≤ P z := fun z => (hP z).le
  set bound := exp (m * a / 2) * √(1 - ε ^ 2) ^ m
  have hb0 : 0 ≤ bound := by positivity
  -- the event is covered by the events "a bad candidate beats `cstar`"
  let E : C → (Fin m → Ω) → Prop := fun c Z =>
    ε < tv P (Q c) ∧ ∏ i, Q cstar (Z i) ≤ ∏ i, Q c (Z i)
  have hcover := prodProb_le_sum P hP0 m _ E (fun Z hZ => ⟨sel Z, hZ, hsel Z cstar⟩)
  refine hcover.trans ?_
  have hsum : ∑ _c : C, bound = Fintype.card C * bound := by simp
  rw [← hsum]
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases hc : ε < tv P (Q c)
  · -- the affinity of a bad candidate
    have hA : affinity P (Q c) ≤ √(1 - ε ^ 2) := by
      have h1 := tv_sq_le P (Q c) hP0 (hQ c) hP1 (hQ1 c)
      have h2 : ε ^ 2 < tv P (Q c) ^ 2 := by nlinarith
      rw [← Real.sqrt_sq (affinity_nonneg P (Q c))]
      exact Real.sqrt_le_sqrt (by linarith)
    -- beating `cstar` forces a large likelihood ratio
    have hlow : ∀ z, exp (-a) ≤ Q cstar z / P z := by
      intro z
      rw [← Real.le_log_iff_exp_le (div_pos (hpos z) (hP z))]
      have := ha z; rw [abs_le] at this; linarith
    have hsub : ∀ Z, E c Z → exp (-(m * a)) ≤ ∏ i, Q c (Z i) / P (Z i) := by
      intro Z hZ
      have hPZ : 0 < ∏ i, P (Z i) := Finset.prod_pos fun i _ => hP _
      rw [Finset.prod_div_distrib, le_div_iff₀ hPZ]
      calc exp (-(m * a)) * ∏ i, P (Z i) = ∏ i, (exp (-a) * P (Z i)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              ← Real.exp_nat_mul]; ring_nf
        _ ≤ ∏ i, Q cstar (Z i) := by
            refine Finset.prod_le_prod₀ (fun i _ => mul_nonneg (exp_pos _).le (hP _).le)
              (fun i _ => ?_)
            have := hlow (Z i)
            rwa [le_div_iff₀ (hP _)] at this
        _ ≤ ∏ i, Q c (Z i) := hZ.2
    calc prodProb P m (E c) ≤ prodProb P m (fun Z => exp (-(m * a)) ≤ ∏ i, Q c (Z i) / P (Z i)) :=
          prodProb_mono P hP0 m hsub
      _ ≤ (√(exp (-(m * a))))⁻¹ * affinity P (Q c) ^ m := markov_sqrt P (Q c) hP (hQ c) m
          (exp_pos _)
      _ ≤ bound := by
          rw [← Real.exp_half, ← Real.exp_neg]
          simp only [bound]
          rw [show -(-(↑m * a) / 2) = ↑m * a / 2 by ring]
          gcongr
          exact affinity_nonneg _ _
  · have : prodProb P m (E c) = 0 := by
      rw [← prodProb_false P m]
      congr 1; funext Z; simp [E, hc]
    rw [this]; exact hb0

/-- `sec:sample-upper`: with `a = 3ε²/16`, the bound becomes `N e^{-13 m ε² / 32}`. -/
theorem likelihood_selection_exp {C : Type*} [Fintype C] (P : Ω → ℝ) (hP : ∀ z, 0 < P z)
    (hP1 : ∑ z, P z = 1) (Q : C → Ω → ℝ) (hQ : ∀ c z, 0 ≤ Q c z) (hQ1 : ∀ c, ∑ z, Q c z = 1)
    (cstar : C) {ε : ℝ} (hε : 0 ≤ ε) (hpos : ∀ z, 0 < Q cstar z)
    (ha : ∀ z, |log (Q cstar z / P z)| ≤ 3 * ε ^ 2 / 16)
    (m : ℕ) (sel : (Fin m → Ω) → C) (hsel : ∀ Z c, ∏ i, Q c (Z i) ≤ ∏ i, Q (sel Z) (Z i)) :
    prodProb P m (fun Z => ε < tv P (Q (sel Z))) ≤
      Fintype.card C * exp (-(13 * m * ε ^ 2 / 32)) := by
  refine (likelihood_selection P hP hP1 Q hQ hQ1 cstar hpos ha m sel hsel hε).trans ?_
  gcongr
  calc exp (m * (3 * ε ^ 2 / 16) / 2) * √(1 - ε ^ 2) ^ m
      ≤ exp (m * (3 * ε ^ 2 / 16) / 2) * exp (-(ε ^ 2) / 2) ^ m := by
        gcongr; exact sqrt_one_sub_sq_le ε
    _ = exp (-(13 * m * ε ^ 2 / 32)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

/-- `eq:samples`: if `m ≥ (32 / (13 ε²)) ln (N/δ)` the failure probability is at most `δ`. -/
theorem likelihood_selection_delta {C : Type*} [Fintype C] (P : Ω → ℝ) (hP : ∀ z, 0 < P z)
    (hP1 : ∑ z, P z = 1) (Q : C → Ω → ℝ) (hQ : ∀ c z, 0 ≤ Q c z) (hQ1 : ∀ c, ∑ z, Q c z = 1)
    (cstar : C) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hpos : ∀ z, 0 < Q cstar z)
    (ha : ∀ z, |log (Q cstar z / P z)| ≤ 3 * ε ^ 2 / 16)
    (m : ℕ) (hm : 32 / (13 * ε ^ 2) * log (Fintype.card C / δ) ≤ m)
    (sel : (Fin m → Ω) → C) (hsel : ∀ Z c, ∏ i, Q c (Z i) ≤ ∏ i, Q (sel Z) (Z i)) :
    prodProb P m (fun Z => ε < tv P (Q (sel Z))) ≤ δ := by
  refine (likelihood_selection_exp P hP hP1 Q hQ hQ1 cstar hε.le hpos ha m sel hsel).trans ?_
  have hN : (0 : ℝ) < Fintype.card C := by
    have : Nonempty C := ⟨cstar⟩
    exact_mod_cast Fintype.card_pos
  have hm' : log (Fintype.card C / δ) ≤ 13 * m * ε ^ 2 / 32 := by
    have hk : (13 * ε ^ 2 / 32) * (32 / (13 * ε ^ 2)) = 1 := by field_simp
    calc log (Fintype.card C / δ)
        = (13 * ε ^ 2 / 32) * (32 / (13 * ε ^ 2) * log (Fintype.card C / δ)) := by
          rw [← mul_assoc, hk, one_mul]
      _ ≤ (13 * ε ^ 2 / 32) * m := by gcongr
      _ = 13 * m * ε ^ 2 / 32 := by ring
  calc (Fintype.card C : ℝ) * exp (-(13 * m * ε ^ 2 / 32))
      ≤ Fintype.card C * exp (-log (Fintype.card C / δ)) := by gcongr
    _ = δ := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

/-! ### The explicit integer sample size -/

/-- `K = 3 T d² [k + ⌈log₂ (2T+1)⌉] + ⌈log₂ (2/δ)⌉`. -/
noncomputable def coverK (T d k : ℕ) (δ : ℝ) : ℤ :=
  3 * T * d ^ 2 * (k + ⌈Real.logb 2 (2 * T + 1)⌉) + ⌈Real.logb 2 (2 / δ)⌉

/-- `m = ⌈32 K / (13 ε²)⌉`. -/
noncomputable def coverSamples (T d k : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈32 * (coverK T d k δ : ℝ) / (13 * ε ^ 2)⌉₊

theorem log_le_ceil_logb_mul (x : ℝ) : log x ≤ ⌈Real.logb 2 x⌉ * log 2 := by
  have h := Int.le_ceil (Real.logb 2 x)
  rw [← Real.log_div_log, div_le_iff₀ (Real.log_pos one_lt_two)] at h
  exact h

/-- `sec:sample-upper`: `ln (N/δ) ≤ K` whenever `0 < N ≤ (1 + 2T/Δ)^{3Td²}` with `Δ = 2^{-k}` and
`0 < δ ≤ 2`. -/
theorem log_div_le_coverK {T d k : ℕ} {N δ : ℝ} (hN0 : 0 < N)
    (hN : N ≤ (1 + 2 * T / ((2 : ℝ) ^ k)⁻¹) ^ (3 * T * d ^ 2)) (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    log (N / δ) ≤ coverK T d k δ := by
  have hl2 : 0 < log 2 := Real.log_pos one_lt_two
  have hl21 : log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hk1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hbase : 1 + 2 * (T : ℝ) / ((2 : ℝ) ^ k)⁻¹ ≤ (2 * T + 1) * 2 ^ k := by
    rw [div_inv_eq_mul]; nlinarith
  have h1 : log N ≤ (3 * T * d ^ 2 : ℕ) * (log (2 * T + 1) + k * log 2) := by
    calc log N ≤ log ((1 + 2 * T / ((2 : ℝ) ^ k)⁻¹) ^ (3 * T * d ^ 2)) := Real.log_le_log hN0 hN
      _ = (3 * T * d ^ 2 : ℕ) * log (1 + 2 * T / ((2 : ℝ) ^ k)⁻¹) := Real.log_pow _ _
      _ ≤ (3 * T * d ^ 2 : ℕ) * log ((2 * T + 1) * 2 ^ k) := by
          gcongr
      _ = (3 * T * d ^ 2 : ℕ) * (log (2 * T + 1) + k * log 2) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have h2 : log (2 * T + 1) ≤ ⌈Real.logb 2 (2 * T + 1)⌉ * log 2 :=
    log_le_ceil_logb_mul _
  have h3 : -log δ ≤ ⌈Real.logb 2 (2 / δ)⌉ * log 2 := by
    have := log_le_ceil_logb_mul (2 / δ)
    rw [Real.log_div (by norm_num) hδ0.ne'] at this
    linarith
  have c1 : (0 : ℝ) ≤ ⌈Real.logb 2 (2 * T + 1)⌉ := by
    have h : (0 : ℝ) ≤ Real.logb 2 (2 * T + 1) := Real.logb_nonneg one_lt_two (by linarith)
    exact_mod_cast Int.ceil_nonneg h
  have c2 : (0 : ℝ) ≤ ⌈Real.logb 2 (2 / δ)⌉ := by
    have h : (0 : ℝ) ≤ Real.logb 2 (2 / δ) :=
      Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hδ0]; linarith)
    exact_mod_cast Int.ceil_nonneg h
  have hK0 : 0 ≤ (coverK T d k δ : ℝ) := by
    unfold coverK; push_cast; positivity
  rw [Real.log_div hN0.ne' hδ0.ne']
  calc log N - log δ ≤ (3 * T * d ^ 2 : ℕ) * (⌈Real.logb 2 (2 * T + 1)⌉ * log 2 + k * log 2) +
        ⌈Real.logb 2 (2 / δ)⌉ * log 2 := by
        have := mul_le_mul_of_nonneg_left (add_le_add_right h2 (k * log 2))
          (Nat.cast_nonneg (α := ℝ) (3 * T * d ^ 2))
        linarith
    _ = log 2 * coverK T d k δ := by unfold coverK; push_cast; ring
    _ ≤ coverK T d k δ := by nlinarith

/-- `eq:samples` for the explicit integer choice: `m = ⌈32K/(13ε²)⌉ ≥ (32/(13ε²)) ln (N/δ)`. -/
theorem coverSamples_spec {T d k : ℕ} {N ε δ : ℝ} (hε : 0 < ε) (hN0 : 0 < N)
    (hN : N ≤ (1 + 2 * T / ((2 : ℝ) ^ k)⁻¹) ^ (3 * T * d ^ 2)) (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    32 / (13 * ε ^ 2) * log (N / δ) ≤ coverSamples T d k ε δ := by
  calc 32 / (13 * ε ^ 2) * log (N / δ) ≤ 32 / (13 * ε ^ 2) * coverK T d k δ := by
        gcongr; exact log_div_le_coverK hN0 hN hδ0 hδ2
    _ = 32 * (coverK T d k δ : ℝ) / (13 * ε ^ 2) := by ring
    _ ≤ coverSamples T d k ε δ := Nat.le_ceil _

/-! ### The sample bound of `thm:cover` -/

/-- The number of complete samples used for `thm:cover`. -/
noncomputable def coverM (T d : ℕ) (ε δ : ℝ) : ℕ :=
  coverSamples T d (meshK T d (coverRho T ε)) ε δ

theorem wordDist_pos {T : ℕ} {p : NextBit} (hp : FullSupport T p) (z : Word T) :
    0 < wordDist p T z :=
  (log_condProb_sub_le p p T 0 (fun h hh y => ⟨by
      cases y
      · simpa [bitProb] using (hp h hh).2
      · simpa [bitProb] using (hp h hh).1, by
      cases y
      · simpa [bitProb] using (hp h hh).2
      · simpa [bitProb] using (hp h hh).1, by simp⟩) z.toList [] (by simp)).1

/-- The number of grid candidates of `thm:cover` satisfies `eq:coverN`. -/
theorem card_candidates_le (T d : ℕ) (hT : 1 ≤ T) (hd : 1 ≤ d) (ε : ℝ) :
    (Fintype.card (Candidates T d ε) : ℝ) ≤
      (1 + 2 * T / coverDelta T d ε) ^ (3 * T * d ^ 2) :=
  card_gridParams_le T d hd (by exact_mod_cast hT) (by unfold coverDelta; positivity)

/-- An empirical maximum-likelihood rule exists (the hypothesis of `cover_sample_bound` is
satisfiable). -/
theorem exists_mle {C Ω' : Type*} [Finite C] [Nonempty C] (m : ℕ) (Q : C → Ω' → ℝ) :
    ∃ sel : (Fin m → Ω') → C, ∀ Z c, ∏ i, Q c (Z i) ≤ ∏ i, Q (sel Z) (Z i) := by
  choose sel hsel using fun Z : Fin m → Ω' => Finite.exists_max fun c => ∏ i, Q c (Z i)
  exact ⟨sel, fun Z c => hsel Z c⟩

/-- `thm:cover`, sample bound: for `p ∈ 𝒞_{T,d}` with `T, d ≥ 1` and `0 < ε, δ < 1`, take
`m = ⌈32K/(13ε²)⌉` independent complete samples and any empirical maximum-likelihood candidate
`ĉ(Z)` among the grid candidates (finite-bit generators, not necessarily in the class). Then
`Pr{TV(P, Q_ĉ) > ε} ≤ δ`. -/
theorem cover_sample_bound {T d : ℕ} (hT : 1 ≤ T) (hd : 1 ≤ d) {ε δ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) {p : NextBit} (hp : InClass T d p)
    (sel : (Fin (coverM T d ε δ) → Word T) → Candidates T d ε)
    (hsel : ∀ Z (c : Candidates T d ε), ∏ i, wordDist (coverModel c) T (Z i) ≤
      ∏ i, wordDist (coverModel (sel Z)) T (Z i)) :
    prodProb (wordDist p T) (coverM T d ε δ)
      (fun Z => ε < tv (wordDist p T) (wordDist (coverModel (sel Z)) T)) ≤ δ := by
  obtain ⟨cstar, hstar⟩ := bestKL hT hd hε0 hε1.le hp
  have hQ := fun c : Candidates T d ε => coverModel_prob hT hε0 hε1.le c
  have hN0 : (0 : ℝ) < Fintype.card (Candidates T d ε) := by
    have : Nonempty (Candidates T d ε) := ⟨cstar⟩
    exact_mod_cast Fintype.card_pos
  refine likelihood_selection_delta (wordDist p T) (wordDist_pos hp.fullSupport)
    (sum_condProb p T []) (fun c => wordDist (coverModel c) T) (fun c z => ((hQ c).1 z).le)
    (fun c => (hQ c).2) cstar hε0 hδ0 (fun z => (hstar z).1) (fun z => (hstar z).2)
    (coverM T d ε δ) ?_ sel hsel
  exact coverSamples_spec hε0 hN0 (card_candidates_le T d hT hd ε) hδ0 (by linarith)

/-- Token accounting of `thm:cover`: one complete sample costs `∑_{t<T} (t+1) = T(T+1)/2` tokens. -/
theorem sample_tokens (T : ℕ) : 2 * ∑ t ∈ range T, (t + 1) = T * (T + 1) := by
  induction T with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

/-- The uniform distribution is in `𝒞_{T,d}`, so the hypotheses of `cover_sample_bound` are
satisfiable. -/
theorem uniform_inClass (T d : ℕ) : InClass T d (fun _ => 1 / 2) := by
  have hl : logit (fun _ => (1 : ℝ) / 2) = fun _ => 0 := by
    funext h; norm_num [logit]
  refine ⟨fun h _ => by norm_num, fun h _ => by rw [hl]; simp, fun t _ => ?_⟩
  rw [hl]
  have : logitCutMatrix (fun _ => (0 : ℝ)) T t = 0 := by ext; rfl
  rw [this, Matrix.rank_zero]
  exact Nat.zero_le _

end LowLogitRank.Cover
