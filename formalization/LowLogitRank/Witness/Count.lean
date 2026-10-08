import LowLogitRank.Witness.Numerics

/-!
# Fewer than `64 d J_b` witnesses per cut (`lem:explicit-gls-token-envelope`)

The final form of the paragraph "Explicit witness bound": under the parameters of
`eq:explicit-gls-parameters`, a cut cannot receive `64 d J_b` witness additions.

The modeling of a cut is as follows. `H` and `F` are the histories and futures of the cut,
`ℓ h f` is the true (signed) logit entry, `A h f` the numerical entry, with `|A - ℓ| ≤ ξ`.
A bounded factorization `ℓ h f = ⟪x h, y f⟫` with `‖x h‖, ‖y f‖ ≤ α` in `ℝ^d` is a hypothesis;
the paper obtains it from `lem:bounded-factors` (norms at most `√(dL) ≤ α`).
The `j`th discrepancy row is a difference of two coefficient combinations of actual rows,
`D_j(f) = ∑_k c₁ j k A (r₁ j k) f - ∑_k c₂ j k A (r₂ j k) f`, with `n ≤ d̄ ≤ 6K` terms each
and coefficients of magnitude at most two (shorter lists are padded with zero coefficients).
The reconstruction equalities give `D_j(w_i) = 0` at the earlier witness columns `w_i`, `i < j`,
and the discrepancy test gives `|D_j(w_j)| > g`.
-/

namespace LowLogitRank.Witness

open Finset

/-! ### The residual estimate of `sec:gls-validation-arithmetic` -/

/-- `sec:gls-validation-arithmetic` (residual estimate for GLS Lemma 5.6): for two coefficient
lists of length `n` with coefficients bounded by `β`, the history combination
`v = ∑ c₁ₖ x(r₁ₖ) - ∑ c₂ₖ x(r₂ₖ)` has norm at most `2 β n α`, and the numerical discrepancy
differs from `⟪v, y f⟫` by at most `2 β n ξ`. -/
theorem combo_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {H F : Type*}
    (x : H → E) (y : F → E) (A : H → F → ℝ) {α ξ β : ℝ} (hx : ∀ h, ‖x h‖ ≤ α)
    (hA : ∀ h f, |A h f - inner ℝ (x h) (y f)| ≤ ξ) {n : ℕ} (r₁ r₂ : Fin n → H)
    (c₁ c₂ : Fin n → ℝ) (hc₁ : ∀ k, |c₁ k| ≤ β) (hc₂ : ∀ k, |c₂ k| ≤ β) :
    ‖∑ k, c₁ k • x (r₁ k) - ∑ k, c₂ k • x (r₂ k)‖ ≤ 2 * β * n * α ∧
      ∀ f, |(∑ k, c₁ k * A (r₁ k) f - ∑ k, c₂ k * A (r₂ k) f) -
        inner ℝ (∑ k, c₁ k • x (r₁ k) - ∑ k, c₂ k • x (r₂ k)) (y f)| ≤ 2 * β * n * ξ := by
  have hnorm : ∀ (r : Fin n → H) (c : Fin n → ℝ), (∀ k, |c k| ≤ β) →
      ‖∑ k, c k • x (r k)‖ ≤ β * n * α := by
    intro r c hc
    calc ‖∑ k, c k • x (r k)‖ ≤ ∑ k, ‖c k • x (r k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin n, β * α := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (hc k) (hx _) (norm_nonneg _) ((abs_nonneg _).trans (hc k))
      _ = β * n * α := by simp; ring
  have herr : ∀ (r : Fin n → H) (c : Fin n → ℝ), (∀ k, |c k| ≤ β) → ∀ f,
      |∑ k, c k * A (r k) f - inner ℝ (∑ k, c k • x (r k)) (y f)| ≤ β * n * ξ := by
    intro r c hc f
    rw [sum_inner]
    simp only [real_inner_smul_left]
    rw [← Finset.sum_sub_distrib]
    calc |∑ k, (c k * A (r k) f - c k * inner ℝ (x (r k)) (y f))|
        ≤ ∑ k, |c k * A (r k) f - c k * inner ℝ (x (r k)) (y f)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, β * ξ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [← mul_sub, abs_mul]
          exact mul_le_mul (hc k) (hA _ _) (abs_nonneg _) ((abs_nonneg _).trans (hc k))
      _ = β * n * ξ := by simp; ring
  refine ⟨?_, fun f => ?_⟩
  · calc ‖∑ k, c₁ k • x (r₁ k) - ∑ k, c₂ k • x (r₂ k)‖
        ≤ ‖∑ k, c₁ k • x (r₁ k)‖ + ‖∑ k, c₂ k • x (r₂ k)‖ := norm_sub_le _ _
      _ ≤ β * n * α + β * n * α := add_le_add (hnorm r₁ c₁ hc₁) (hnorm r₂ c₂ hc₂)
      _ = 2 * β * n * α := by ring
  · rw [inner_sub_left]
    have h1 := herr r₁ c₁ hc₁ f
    have h2 := herr r₂ c₂ hc₂ f
    calc |(∑ k, c₁ k * A (r₁ k) f - ∑ k, c₂ k * A (r₂ k) f) -
          (inner ℝ (∑ k, c₁ k • x (r₁ k)) (y f) - inner ℝ (∑ k, c₂ k • x (r₂ k)) (y f))|
        = |(∑ k, c₁ k * A (r₁ k) f - inner ℝ (∑ k, c₁ k • x (r₁ k)) (y f)) -
          (∑ k, c₂ k * A (r₂ k) f - inner ℝ (∑ k, c₂ k • x (r₂ k)) (y f))| := by ring_nf
      _ ≤ |∑ k, c₁ k * A (r₁ k) f - inner ℝ (∑ k, c₁ k • x (r₁ k)) (y f)| +
          |∑ k, c₂ k * A (r₂ k) f - inner ℝ (∑ k, c₂ k • x (r₂ k)) (y f)| := abs_sub _ _
      _ ≤ β * n * ξ + β * n * ξ := add_le_add h1 h2
      _ = 2 * β * n * ξ := by ring

/-- `sec:gls-validation-arithmetic`: with `β = 2` and `n ≤ d̄ ≤ 6K`, `2 β n ≤ 24 K`. -/
theorem two_beta_n_le (n K : ℕ) (hn : n ≤ 6 * K) : 2 * (2 : ℝ) * n ≤ 24 * K := by
  have : (n : ℝ) ≤ 6 * K := by exact_mod_cast hn
  linarith

/-- `lem:bounded-factors` with `Λ = L` gives factor norms at most `√(d L)`, and
`√(d L) ≤ α = dL + 1`. -/
theorem sqrt_le_alpha (d L : ℕ) : √((d : ℝ) * L) ≤ alphaOf d L := by
  have h0 : (0 : ℝ) ≤ d * L := by positivity
  rw [Real.sqrt_le_left (by unfold alphaOf; positivity)]
  unfold alphaOf
  push_cast
  nlinarith

/-! ### The witness count -/

/-- `lem:explicit-gls-token-envelope` (explicit witness bound), counting step for abstract
`B, R, g`: put `e₀ = g / (16 √(d J_b))` and `a₀ = (B R / e₀)²`. If `J_b ≥ 7`, `a₀ ≥ 1`,
`log₂ a₀ ≤ 9 J_b`, and `m` witnesses satisfy the hypotheses of `witness_general` with tolerance
`e₀`, then `m < 64 d J_b`: otherwise the first `64 d J_b` witnesses all have leverage
`> (16 √(d J_b) - 1)² / j > 1`, so `64 d J_b < d log₂ (1 + 64 J_b a₀) ≤ 11 d J_b`. -/
theorem witness_count_lt_general {d J : ℕ} (hd : 1 ≤ d) (hJ : 7 ≤ J) {B R g : ℝ} (hB : 0 < B)
    (hg : 0 < g) (ha₁ : 1 ≤ (B * R / (g / (16 * √((d : ℝ) * J)))) ^ 2)
    (hlog : Real.logb 2 ((B * R / (g / (16 * √((d : ℝ) * J)))) ^ 2) ≤ 9 * J)
    (m : ℕ) (v φ : ℕ → EuclideanSpace ℝ (Fin d)) (Lw : ℕ → ℕ → ℝ)
    (hv : ∀ j ∈ Icc 1 m, ‖v j‖ ≤ B) (hφ : ∀ i ∈ Icc 1 m, ‖φ i‖ ≤ R)
    (hzero : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i < j → Lw j i = 0)
    (hdisc : ∀ j ∈ Icc 1 m, g < |Lw j j|)
    (happrox : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i ≤ j →
      |Lw j i - inner ℝ (v j) (φ i)| ≤ g / (16 * √((d : ℝ) * J))) :
    m < 64 * d * J := by
  by_contra hm
  replace hm := not_lt.mp hm
  -- the first `M' = 64 d J_b` witnesses
  set M' := 64 * d * J with hM'
  have hM'1 : 1 ≤ M' := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsub : ∀ j ∈ Icc 1 M', j ∈ Icc 1 m := fun j hj => by
    rw [Finset.mem_Icc] at hj ⊢; omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hx : 0 < √((d : ℝ) * J) := Real.sqrt_pos.mpr (by positivity)
  have hx1 : 1 ≤ √((d : ℝ) * J) := Real.one_le_sqrt.mpr
    (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hd) (by exact_mod_cast (by omega : 1 ≤ J)))
  set e₀ := g / (16 * √((d : ℝ) * J)) with he₀
  have he₀pos : 0 < e₀ := by positivity
  have heg : e₀ < g := by
    rw [he₀, div_lt_iff₀ (by positivity)]
    nlinarith
  have hlev : (M' : ℝ) * e₀ ^ 2 ≤ (g - e₀) ^ 2 := by
    have h1 := one_lt_leverage_bound d J M' hd (by omega) hM'1 le_rfl
    have hM'0 : (0 : ℝ) < M' := by exact_mod_cast hM'1
    rw [← leverage_ratio_eq hg hx hM'0, ← he₀, one_lt_div (by positivity)] at h1
    exact h1.le
  have key := witness_general hd hB he₀pos heg M' hM'1 v φ Lw
    (fun j hj => hv j (hsub j hj)) (fun i hi => hφ i (hsub i hi))
    (fun j hj i hi hij => hzero j (hsub j hj) i (hsub i hi) hij)
    (fun j hj => hdisc j (hsub j hj))
    (fun j hj i hi hij => happrox j (hsub j hj) i (hsub i hi) hij) hlev
  have hup := det_upper_le d J hJ ha₁ hlog
  have heq : (M' : ℝ) * (B * R / e₀) ^ 2 / d = 64 * J * (B * R / e₀) ^ 2 := by
    rw [hM']; push_cast; field_simp
  rw [heq] at key
  have hM'eq : (M' : ℝ) = 64 * d * J := by rw [hM']; push_cast; ring
  have : (11 : ℝ) * d * J < 64 * d * J := by nlinarith
  linarith [hup.1, hup.2]

/-- `lem:explicit-gls-token-envelope` (explicit witness bound), with the vectors `v_j, φ_i`
given: under the parameters of `eq:explicit-gls-parameters`, if `m` witnesses at one cut satisfy
`‖v_j‖ ≤ 24Kα`, `‖φ_i‖ ≤ α`, `L_j(i) = 0` for `i < j`, `|L_j(j)| > g` and
`|L_j(i) - ⟪v_j, φ_i⟫| ≤ 24Kξ` for `i ≤ j`, then `m < 64 d J_b`. The lemma's hypotheses
`T ≥ 32`, `0 < ε, δ < 1/2` imply the weaker ones used here. -/
theorem witness_count_lt_of_bounds {T d L : ℕ} (hT : 1 ≤ T) (hd : 1 ≤ d) {ε δ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (m : ℕ) (v φ : ℕ → EuclideanSpace ℝ (Fin d)) (Lw : ℕ → ℕ → ℝ)
    (hv : ∀ j ∈ Icc 1 m, ‖v j‖ ≤ 24 * (KOf T d L ε δ : ℝ) * alphaOf d L)
    (hφ : ∀ i ∈ Icc 1 m, ‖φ i‖ ≤ alphaOf d L)
    (hzero : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i < j → Lw j i = 0)
    (hdisc : ∀ j ∈ Icc 1 m, gOf T ε < |Lw j j|)
    (happrox : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i ≤ j →
      |Lw j i - inner ℝ (v j) (φ i)| ≤ 24 * (KOf T d L ε δ : ℝ) * xiOf T d L ε δ) :
    m < 64 * d * JbOf T d L ε δ := by
  set J := JbOf T d L ε δ with hJdef
  have hJ64 : 64 ≤ J := Jb_ge T d L ε δ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hK0 : (0 : ℝ) < KOf T d L ε δ := by
    have : 0 < KOf T d L ε δ := by unfold KOf; positivity
    exact_mod_cast this
  have hα1 : (1 : ℝ) ≤ alphaOf d L := by
    have : 1 ≤ alphaOf d L := by unfold alphaOf; omega
    exact_mod_cast this
  have hx : 0 < √((d : ℝ) * J) := Real.sqrt_pos.mpr (by positivity)
  have hg : 0 < gOf T ε := by unfold gOf; positivity
  have hres : 24 * (KOf T d L ε δ : ℝ) * xiOf T d L ε δ ≤ gOf T ε / (16 * √((d : ℝ) * J)) := by
    have h := residual_le (gOf T ε) (KOf T d L ε δ) (√((d : ℝ) * J)) (xiOf T d L ε δ) hg hK0 hx
      (xi_le T d L hT hd hε0)
    exact h.1.trans h.2
  -- the value of `a₀`
  have ha₀eq : (24 * (KOf T d L ε δ : ℝ) * alphaOf d L * alphaOf d L /
      (gOf T ε / (16 * √((d : ℝ) * J)))) ^ 2 = 9 * 2 ^ 42 * (T : ℝ) ^ 6 * (d : ℝ) ^ 3 *
      (J : ℝ) ^ 3 * (alphaOf d L : ℝ) ^ 4 / ε ^ 2 :=
    a0_eq T d J (alphaOf d L) ε hε0 hT hd (by omega)
  have ha₁ : 1 ≤ 9 * 2 ^ 42 * (T : ℝ) ^ 6 * (d : ℝ) ^ 3 * (J : ℝ) ^ 3 *
      (alphaOf d L : ℝ) ^ 4 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
    have hprod : 1 ≤ 9 * 2 ^ 42 * (T : ℝ) ^ 6 * (d : ℝ) ^ 3 * (J : ℝ) ^ 3 *
        (alphaOf d L : ℝ) ^ 4 := by
      have h0 : (1 : ℝ) ≤ 9 * 2 ^ 42 := by norm_num
      have h1 := one_le_mul_of_one_le_of_one_le h0 (one_le_pow₀ hT1 (n := 6))
      have h2 := one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ hd1 (n := 3))
      have h3 := one_le_mul_of_one_le_of_one_le h2 (one_le_pow₀ hJ1 (n := 3))
      exact one_le_mul_of_one_le_of_one_le h3 (one_le_pow₀ hα1 (n := 4))
    nlinarith
  have hlog : Real.logb 2 (9 * 2 ^ 42 * (T : ℝ) ^ 6 * (d : ℝ) ^ 3 * (J : ℝ) ^ 3 *
      (alphaOf d L : ℝ) ^ 4 / ε ^ 2) ≤ 9 * J := by
    have h1 := logb_a0_le T d J (alphaOf d L) ε hT hd (by omega) (by linarith) hε0
    have hS := logb_sum_le_Jb T d L hT hd hε0 hδ0
    have h2 := logb_bound_le_nine J (by omega)
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast hd))
      (Real.logb_nonneg (by norm_num) hα1)
      (Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hε0]; linarith))
      (Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hδ0]; linarith)) hS
    linarith [h2.1, h2.2]
  rw [← ha₀eq] at ha₁ hlog
  exact witness_count_lt_general hd (by omega) (by positivity) hg ha₁ hlog m v φ Lw hv hφ hzero
    hdisc fun j hj i hi hij => (happrox j hj i hi hij).trans hres

/-- `lem:explicit-gls-token-envelope` (explicit witness bound), final form: under the parameters
of `eq:explicit-gls-parameters` (`α = dL + 1`, `J_b`, `K = 512 T d J_b`, `g = ε/(32T²)`,
`ξ = 2^{-b_ξ}`), every cut receives fewer than `64 d J_b` witness additions.

Modeling hypotheses (see the module docstring): the true entries have a factorization
`ℓ h f = ⟪x h, y f⟫` with `‖x h‖, ‖y f‖ ≤ α` (from `lem:bounded-factors`); numerical entries
satisfy `|A h f - ℓ h f| ≤ ξ`; the `j`th discrepancy row is a difference of two combinations of
`n ≤ 6K` numerical rows with coefficients of magnitude at most two; it vanishes at the earlier
witness columns and exceeds `g` in magnitude at its own. The lemma's hypotheses `T ≥ 32`,
`0 < ε, δ < 1/2` imply the weaker ones used here. -/
theorem witness_count_lt {T d L : ℕ} (hT : 1 ≤ T) (hd : 1 ≤ d) {ε δ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {H F : Type*} (ℓ A : H → F → ℝ) (x : H → EuclideanSpace ℝ (Fin d))
    (y : F → EuclideanSpace ℝ (Fin d))
    (hfac : ∀ h f, ℓ h f = inner ℝ (x h) (y f))
    (hx : ∀ h, ‖x h‖ ≤ alphaOf d L) (hy : ∀ f, ‖y f‖ ≤ alphaOf d L)
    (hA : ∀ h f, |A h f - ℓ h f| ≤ xiOf T d L ε δ)
    (n : ℕ) (hn : n ≤ 6 * KOf T d L ε δ) (r₁ r₂ : ℕ → Fin n → H) (c₁ c₂ : ℕ → Fin n → ℝ)
    (hc₁ : ∀ j k, |c₁ j k| ≤ 2) (hc₂ : ∀ j k, |c₂ j k| ≤ 2)
    (m : ℕ) (w : ℕ → F)
    (hzero : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i < j →
      ∑ k, c₁ j k * A (r₁ j k) (w i) - ∑ k, c₂ j k * A (r₂ j k) (w i) = 0)
    (hdisc : ∀ j ∈ Icc 1 m,
      gOf T ε < |∑ k, c₁ j k * A (r₁ j k) (w j) - ∑ k, c₂ j k * A (r₂ j k) (w j)|) :
    m < 64 * d * JbOf T d L ε δ := by
  have hA' : ∀ h f, |A h f - inner ℝ (x h) (y f)| ≤ xiOf T d L ε δ := fun h f => by
    rw [← hfac]; exact hA h f
  have hcb := fun j => combo_bounds x y A hx hA' (r₁ j) (r₂ j) (c₁ j) (c₂ j) (hc₁ j) (hc₂ j)
  have h24 := two_beta_n_le n (KOf T d L ε δ) hn
  have hα0 : (0 : ℝ) ≤ alphaOf d L := Nat.cast_nonneg _
  have hξ0 : (0 : ℝ) ≤ xiOf T d L ε δ := by unfold xiOf; positivity
  refine witness_count_lt_of_bounds hT hd hε0 hε1 hδ0 hδ1 m
    (fun j => ∑ k, c₁ j k • x (r₁ j k) - ∑ k, c₂ j k • x (r₂ j k)) (fun i => y (w i))
    (fun j i => ∑ k, c₁ j k * A (r₁ j k) (w i) - ∑ k, c₂ j k * A (r₂ j k) (w i))
    (fun j _ => (hcb j).1.trans (mul_le_mul_of_nonneg_right h24 hα0))
    (fun i _ => hy (w i)) hzero hdisc
    (fun j _ i _ _ => ((hcb j).2 (w i)).trans (mul_le_mul_of_nonneg_right h24 hξ0))

/-- The hypotheses of `witness_count_lt` are jointly satisfiable in the range of
`lem:explicit-gls-token-envelope` (`T ≥ 32`, `d, L ≥ 1`, `0 < ε, δ < 1/2`) with one witness
(`m = 1`): `T = 32`, `d = L = 1`, `ε = δ = 1/100`, one history, one future, the unit vector as
both factors, exact numerical entries `A = ℓ = 1`, and the discrepancy row `1·A - 0·A`, whose value
`1` exceeds `g`. The conclusion `m < 64 d J_b` then holds. -/
theorem witness_count_lt_satisfiable :
    ∃ (T d L : ℕ) (ε δ : ℝ), 32 ≤ T ∧ 1 ≤ d ∧ 1 ≤ L ∧ 0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ < 1 / 2 ∧
      ∃ (H F : Type) (ℓ A : H → F → ℝ) (x : H → EuclideanSpace ℝ (Fin d))
        (y : F → EuclideanSpace ℝ (Fin d)) (n : ℕ) (r₁ r₂ : ℕ → Fin n → H)
        (c₁ c₂ : ℕ → Fin n → ℝ) (m : ℕ) (w : ℕ → F),
        (∀ h f, ℓ h f = inner ℝ (x h) (y f)) ∧
        (∀ h, ‖x h‖ ≤ alphaOf d L) ∧ (∀ f, ‖y f‖ ≤ alphaOf d L) ∧
        (∀ h f, |A h f - ℓ h f| ≤ xiOf T d L ε δ) ∧
        n ≤ 6 * KOf T d L ε δ ∧
        (∀ j k, |c₁ j k| ≤ 2) ∧ (∀ j k, |c₂ j k| ≤ 2) ∧
        1 ≤ m ∧
        (∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i < j →
          ∑ k, c₁ j k * A (r₁ j k) (w i) - ∑ k, c₂ j k * A (r₂ j k) (w i) = 0) ∧
        (∀ j ∈ Icc 1 m,
          gOf T ε < |∑ k, c₁ j k * A (r₁ j k) (w j) - ∑ k, c₂ j k * A (r₂ j k) (w j)|) ∧
        m < 64 * d * JbOf T d L ε δ := by
  have hα : (1 : ℝ) ≤ alphaOf 1 1 := by norm_num [alphaOf]
  have hξ : (0 : ℝ) ≤ xiOf 32 1 1 (1 / 100) (1 / 100) := by unfold xiOf; positivity
  have he : ‖EuclideanSpace.single (0 : Fin 1) (1 : ℝ)‖ = 1 := by simp [PiLp.norm_single]
  have hK : 1 ≤ 6 * KOf 32 1 1 (1 / 100) (1 / 100) := by
    unfold KOf; have := Jb_ge 32 1 1 (1 / 100) (1 / 100); omega
  have hfac : ∀ (h : Unit) (f : Unit), (fun _ _ => (1 : ℝ)) h f =
      inner ℝ ((fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) h)
        ((fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) f) := fun _ _ => by simp
  have hx : ∀ h : Unit, ‖(fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) h‖ ≤ alphaOf 1 1 :=
    fun _ => by rw [he]; exact hα
  have hA : ∀ (h : Unit) (f : Unit), |(fun _ _ => (1 : ℝ)) h f - (fun _ _ => (1 : ℝ)) h f| ≤
      xiOf 32 1 1 (1 / 100) (1 / 100) := fun _ _ => by simpa using hξ
  have hzero : ∀ j ∈ Icc 1 1, ∀ i ∈ Icc 1 1, i < j →
      ∑ k : Fin 1, (fun (_ : ℕ) (_ : Fin 1) => (1 : ℝ)) j k * (fun _ _ => (1 : ℝ))
          ((fun (_ : ℕ) (_ : Fin 1) => ()) j k) ((fun (_ : ℕ) => ()) i) -
        ∑ k : Fin 1, (fun (_ : ℕ) (_ : Fin 1) => (0 : ℝ)) j k * (fun _ _ => (1 : ℝ))
          ((fun (_ : ℕ) (_ : Fin 1) => ()) j k) ((fun (_ : ℕ) => ()) i) = 0 := by
    intro j hj i hi hij
    simp only [Finset.mem_Icc] at hj hi
    omega
  have hdisc : ∀ j ∈ Icc 1 1, gOf 32 (1 / 100) <
      |∑ k : Fin 1, (fun (_ : ℕ) (_ : Fin 1) => (1 : ℝ)) j k * (fun _ _ => (1 : ℝ))
          ((fun (_ : ℕ) (_ : Fin 1) => ()) j k) ((fun (_ : ℕ) => ()) j) -
        ∑ k : Fin 1, (fun (_ : ℕ) (_ : Fin 1) => (0 : ℝ)) j k * (fun _ _ => (1 : ℝ))
          ((fun (_ : ℕ) (_ : Fin 1) => ()) j k) ((fun (_ : ℕ) => ()) j)| := by
    intro j _
    simp only [Finset.univ_unique, Finset.sum_singleton, mul_one, sub_zero, abs_one]
    unfold gOf
    norm_num
  have hc₁ : ∀ (j : ℕ) (k : Fin 1), |(fun (_ : ℕ) (_ : Fin 1) => (1 : ℝ)) j k| ≤ 2 :=
    fun _ _ => by norm_num
  have hc₂ : ∀ (j : ℕ) (k : Fin 1), |(fun (_ : ℕ) (_ : Fin 1) => (0 : ℝ)) j k| ≤ 2 :=
    fun _ _ => by norm_num
  have hcount := witness_count_lt (T := 32) (d := 1) (L := 1) (ε := 1 / 100) (δ := 1 / 100)
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) (fun _ _ => (1 : ℝ))
    (fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    (fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) hfac hx hx hA 1 hK
    (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => (1 : ℝ)) (fun _ _ => (0 : ℝ)) hc₁ hc₂ 1
    (fun _ => ()) hzero hdisc
  exact ⟨32, 1, 1, 1 / 100, 1 / 100, le_rfl, le_rfl, le_rfl, by norm_num, by norm_num,
    by norm_num, by norm_num, Unit, Unit, fun _ _ => (1 : ℝ), fun _ _ => (1 : ℝ),
    fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ),
    fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ), 1, fun _ _ => (), fun _ _ => (),
    fun _ _ => (1 : ℝ), fun _ _ => (0 : ℝ), 1, fun _ => (), hfac, hx, hx, hA, hK,
    hc₁, hc₂, le_rfl, hzero, hdisc, hcount⟩

end LowLogitRank.Witness
