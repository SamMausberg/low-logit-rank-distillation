import LowLogitRank.Envelope
import LowLogitRank.Witness.Count

/-!
# The witness bound with the envelope's parameters (`lem:explicit-gls-token-envelope`)

`Envelope.lean` and `Witness/Numerics.lean` each define the parameters of
`eq:explicit-gls-parameters` (`Input.Jb`, `Input.K`, `Input.g`, `Input.xi` and `JbOf`, `KOf`,
`gOf`, `xiOf`). This file proves that the two copies agree and restates the witness count
`Witness.witness_count_lt` with the envelope's own `α`, `J_b`, `K`, `g` and `ξ`: each cut receives
fewer than `64 d J_b` witnesses, and all `T` cuts together fewer than `64 T d J_b = K/8 < K/3`.
-/

namespace LowLogitRank.Envelope.Input

open Finset

universe u

variable (p : Input)

theorem alpha_eq_alphaOf : p.alpha = Witness.alphaOf p.d p.L := rfl

theorem Jb_eq_JbOf : p.Jb = Witness.JbOf p.T p.d p.L p.ε p.δ := rfl

theorem K_eq_KOf : p.K = Witness.KOf p.T p.d p.L p.ε p.δ := rfl

theorem g_eq_gOf : p.g = Witness.gOf p.T p.ε := rfl

/-- `b_ξ` as the least element (`Nat.find`, `Input.bXi`) equals `b_ξ` as an infimum
(`sInf`, `Witness.bXiOf`); both are `0` if no `b` qualifies. -/
theorem bXi_eq_bXiOf : p.bXi = Witness.bXiOf p.T p.d p.L p.ε p.δ := by
  classical
  change p.bXi = sInf {b : ℕ | p.XiCond b}
  unfold bXi
  split_ifs with h
  · exact (Nat.sInf_def h).symm
  · have he : {b : ℕ | p.XiCond b} = ∅ := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hb => h ⟨b, hb⟩
    rw [he, Nat.sInf_empty]

/-- The tolerance `ξ = 2^{-b_ξ}` of `Envelope.lean` is `Witness.xiOf`. -/
theorem xi_eq_xiOf : p.xi = Witness.xiOf p.T p.d p.L p.ε p.δ := by
  unfold xi Witness.xiOf
  rw [bXi_eq_bXiOf]

/-- `lem:explicit-gls-token-envelope` (explicit witness bound) with the envelope's parameters:
for a valid input, a cut whose witness additions satisfy the modeling hypotheses of
`Witness.witness_count_lt` (bounded factorization with norms at most `α`, numerical entries
within `ξ`, discrepancy rows built from `n ≤ 6K` rows with coefficients at most two, vanishing at
earlier witness columns and exceeding `g` at their own) receives fewer than `64 d J_b`
witnesses. -/
theorem witness_count_lt (hp : p.Valid) {H F : Type*} (ℓ A : H → F → ℝ)
    (x : H → EuclideanSpace ℝ (Fin p.d)) (y : F → EuclideanSpace ℝ (Fin p.d))
    (hfac : ∀ h f, ℓ h f = inner ℝ (x h) (y f))
    (hx : ∀ h, ‖x h‖ ≤ p.alpha) (hy : ∀ f, ‖y f‖ ≤ p.alpha)
    (hA : ∀ h f, |A h f - ℓ h f| ≤ p.xi)
    (n : ℕ) (hn : n ≤ 6 * p.K) (r₁ r₂ : ℕ → Fin n → H) (c₁ c₂ : ℕ → Fin n → ℝ)
    (hc₁ : ∀ j k, |c₁ j k| ≤ 2) (hc₂ : ∀ j k, |c₂ j k| ≤ 2)
    (m : ℕ) (w : ℕ → F)
    (hzero : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i < j →
      ∑ k, c₁ j k * A (r₁ j k) (w i) - ∑ k, c₂ j k * A (r₂ j k) (w i) = 0)
    (hdisc : ∀ j ∈ Icc 1 m,
      p.g < |∑ k, c₁ j k * A (r₁ j k) (w j) - ∑ k, c₂ j k * A (r₂ j k) (w j)|) :
    m < 64 * p.d * p.Jb := by
  rw [xi_eq_xiOf] at hA
  exact Witness.witness_count_lt (by have := hp.T_ge; omega) hp.d_pos hp.ε_pos
    (by linarith [hp.ε_lt]) hp.δ_pos (by linarith [hp.δ_lt]) ℓ A x y hfac hx hy hA n hn r₁ r₂
    c₁ c₂ hc₁ hc₂ m w hzero hdisc

/-- The witness additions at one cut, with the modeling hypotheses of `witness_count_lt` for the
envelope's parameters: a bounded factorization `ℓ = ⟪x, y⟫` with norms at most `α`, numerical
entries `A` within `ξ`, and `m` discrepancy rows (two combinations of `n ≤ 6K` rows with
coefficients at most two) that vanish at the earlier witness columns `w i` and exceed `g` in
magnitude at their own column. -/
structure CutWitnesses where
  H : Type u
  F : Type u
  ℓ : H → F → ℝ
  A : H → F → ℝ
  x : H → EuclideanSpace ℝ (Fin p.d)
  y : F → EuclideanSpace ℝ (Fin p.d)
  fac : ∀ h f, ℓ h f = inner ℝ (x h) (y f)
  x_le : ∀ h, ‖x h‖ ≤ p.alpha
  y_le : ∀ f, ‖y f‖ ≤ p.alpha
  A_close : ∀ h f, |A h f - ℓ h f| ≤ p.xi
  n : ℕ
  n_le : n ≤ 6 * p.K
  r₁ : ℕ → Fin n → H
  r₂ : ℕ → Fin n → H
  c₁ : ℕ → Fin n → ℝ
  c₂ : ℕ → Fin n → ℝ
  c₁_le : ∀ j k, |c₁ j k| ≤ 2
  c₂_le : ∀ j k, |c₂ j k| ≤ 2
  m : ℕ
  w : ℕ → F
  zero : ∀ j ∈ Icc 1 m, ∀ i ∈ Icc 1 m, i < j →
    ∑ k, c₁ j k * A (r₁ j k) (w i) - ∑ k, c₂ j k * A (r₂ j k) (w i) = 0
  disc : ∀ j ∈ Icc 1 m,
    p.g < |∑ k, c₁ j k * A (r₁ j k) (w j) - ∑ k, c₂ j k * A (r₂ j k) (w j)|

/-- The hypotheses of `CutWitnesses` are satisfiable with one witness for every valid input:
one history, one future, a unit vector as both factors, exact entries `A = ℓ = 1`, and the
discrepancy row `1·A - 0·A`, whose value `1` exceeds `g`. -/
theorem exists_cutWitnesses (hp : p.Valid) : ∃ W : CutWitnesses.{0} p, W.m = 1 := by
  set e := EuclideanSpace.single (⟨0, hp.d_pos⟩ : Fin p.d) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hα : ‖e‖ ≤ p.alpha := by
    rw [he, alpha_cast]
    have := d_ge_one hp
    have := L_ge_one hp
    nlinarith
  have hK : 1 ≤ 6 * p.K := by
    have : (1 : ℝ) ≤ p.K := K_ge_one hp
    have : 1 ≤ p.K := by exact_mod_cast this
    omega
  have hξ : 0 ≤ p.xi := xi_pos.le
  refine ⟨⟨Unit, Unit, fun _ _ => 1, fun _ _ => 1, fun _ => e, fun _ => e, fun _ _ => ?_,
    fun _ => hα, fun _ => hα, fun _ _ => by simpa using hξ, 1, hK, fun _ _ => (),
    fun _ _ => (), fun _ _ => 1, fun _ _ => 0, fun _ _ => by norm_num, fun _ _ => by norm_num,
    1, fun _ => (), fun j hj i hi hij => ?_, fun j _ => ?_⟩, rfl⟩
  · rw [real_inner_self_eq_norm_sq, he]; norm_num
  · simp only [Finset.mem_Icc] at hj hi
    omega
  · simp only [Finset.univ_unique, Finset.sum_singleton, mul_one, sub_zero, abs_one]
    exact g_lt_one hp

/-- `lem:explicit-gls-token-envelope` (explicit witness bound and "Explicit success and accuracy
margins"): for a valid input, if the witness additions at each of the `T` cuts satisfy the
hypotheses of `CutWitnesses`, then all cuts together receive fewer than `64 T d J_b = K/8`
witnesses, which is less than the `K/3` feasible epochs. -/
theorem witnesses_total_lt (hp : p.Valid) (W : Fin p.T → CutWitnesses.{u} p) :
    ∑ t, (W t).m < 64 * p.T * p.d * p.Jb ∧ (64 * p.T * p.d * p.Jb : ℝ) = p.K / 8 ∧
      (p.K : ℝ) / 8 < p.K / 3 := by
  have hcut : ∀ t, (W t).m < 64 * p.d * p.Jb := fun t =>
    witness_count_lt p hp (W t).ℓ (W t).A (W t).x (W t).y (W t).fac (W t).x_le (W t).y_le
      (W t).A_close (W t).n (W t).n_le (W t).r₁ (W t).r₂ (W t).c₁ (W t).c₂ (W t).c₁_le
      (W t).c₂_le (W t).m (W t).w (W t).zero (W t).disc
  have hT : 1 ≤ p.T := by have := hp.T_ge; omega
  have htot := Witness.total_lt p.T p.d p.Jb hT
    (fun t => if h : t < p.T then (W ⟨t, h⟩).m else 0)
    (fun t ht => by
      have ht' : t < p.T := Finset.mem_range.mp ht
      simp only [ht', ↓reduceDIte]
      exact hcut _)
  have hsum : ∑ t, (W t).m = ∑ t ∈ range p.T, (if h : t < p.T then (W ⟨t, h⟩).m else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun t _ => by simp [t.isLt]
  rw [hsum]
  exact ⟨htot.1, (witnesses_lt_feasible hp).1, (witnesses_lt_feasible hp).2⟩

end LowLogitRank.Envelope.Input
