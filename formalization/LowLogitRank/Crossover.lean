import LowLogitRank.Envelope

/-!
# The numerical tenfold crossover (`sec:crossover`, `cor:tenfold2048`)

The learner's training-token budget `W` is bounded by `V^{C_q}` (`eq:gls-polynomial-envelope`,
with `V = VOf T d ε δ` of `Basic.lean`); the faithful GLS simulation's expected training replies
are bounded below by `e^{2T}/(30 ξ²)` (`lem:gls-root-simulation`). This file proves the
comparison of these numbers: for `T ≥ T_10`, `10 W ≤ (6/5) e^{2T} ≤ e^{2T}/(30 ξ²)`, and the
concrete case `d = 1`, `ε = δ = 1/100`, `T ≥ 2048`.

The lower bound is `Scalar.gls_root_simulation`, built on `Scalar.prop_scalar`, in the finite
model `Scalar.CappedAlgo`; there the faithfulness of the GLS root entry (the requested component
is within `ξ` of the centered logit of the sampled token with probability `0.99`) is a
hypothesis. `CrossoverRoot.lean` composes the two (`crossover_root`, `tenfold2048_root`).
-/

namespace LowLogitRank.Crossover

open Real LowLogitRank.Envelope

/-- `⌈log₂ (1/x)⌉`; `E = logCeil ε` and `F = logCeil δ`. -/
noncomputable def logCeil (x : ℝ) : ℕ := ⌈logb 2 (1 / x)⌉₊

/-- `B = 2(C_q + d + E + F + 20)`. -/
noncomputable def B (d : ℕ) (ε δ : ℝ) : ℕ := 2 * (Cq + d + logCeil ε + logCeil δ + 20)

/-- `A = (2/(εδ))^{C_q} [801 C_q (d+1)]^{C_q d}`. -/
noncomputable def A (d : ℕ) (ε δ : ℝ) : ℝ :=
  (2 / (ε * δ)) ^ Cq * (801 * Cq * (d + 1) : ℝ) ^ (Cq * d)

/-- The exponent `p = C_q (2d + 2)`. -/
def pExp (d : ℕ) : ℕ := Cq * (2 * d + 2)

/-- `T_10 = max(64, B, p², ⌈log₂ (25A/3)⌉)`. -/
noncomputable def T10 (d : ℕ) (ε δ : ℝ) : ℕ :=
  max (max (max 64 (B d ε δ)) (pExp d ^ 2)) ⌈logb 2 (25 * A d ε δ / 3)⌉₊

theorem Cq_eq : Cq = 52 := rfl

/-! ### The smoothing parameters -/

/-- `L = ⌈log₂ (4/τ)⌉ + 3 = b_τ + 5`. -/
theorem LOf_eq (T : ℕ) (ε : ℝ) : LOf T ε = bTau T ε + 5 := by
  have h : 4 / tauOf T ε = (2 : ℝ) ^ (bTau T ε + 2) := by
    rw [tauOf, div_inv_eq_mul, pow_add]; ring
  rw [LOf, h, logb_two_pow, Nat.ceil_natCast]

theorem logb_eight_T_div {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    logb 2 (8 * T / ε) = 3 + logb 2 T + logb 2 (1 / ε) := by
  rw [show 8 * T / ε = 8 * T * (1 / ε) by ring, Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by norm_num) hT.ne', show (8 : ℝ) = 2 ^ 3 by norm_num, logb_two_pow]
  norm_num

theorem logb_inv_le_logCeil (x : ℝ) : logb 2 (1 / x) ≤ logCeil x := Nat.le_ceil _

/-- `sec:crossover`: `L ≤ log₂ T + E + 10` (from `τ ≥ ε/(16T)`). -/
theorem LOf_le {T : ℕ} {ε : ℝ} (hT : 1 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    (LOf T ε : ℝ) ≤ logb 2 T + logCeil ε + 10 := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hx : 1 ≤ 8 * (T : ℝ) / ε := by rw [one_le_div hε0]; linarith
  have h1 := Nat.ceil_lt_add_one (Real.logb_nonneg one_lt_two hx)
  have h3 := logb_eight_T_div (T := (T : ℝ)) (by linarith) hε0
  have h2 := logb_inv_le_logCeil ε
  rw [LOf_eq]; push_cast
  unfold bTau
  linarith

theorem logb_T_le {T : ℕ} (hT : 64 ≤ T) : logb 2 (T : ℝ) ≤ T / 8 :=
  logb_le_div_8 (by exact_mod_cast hT)

theorem B_cast (d : ℕ) (ε δ : ℝ) :
    (B d ε δ : ℝ) = 2 * (52 + d + logCeil ε + logCeil δ + 20) := by
  simp [B, Cq]

/-- `sec:crossover`: for `T ≥ max(64, B)`, `L ≤ log₂ T + E + 10 ≤ T`. -/
theorem LOf_bound {d T : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (h64 : 64 ≤ T) (hB : B d ε δ ≤ T) :
    (LOf T ε : ℝ) ≤ logb 2 T + logCeil ε + 10 ∧ logb 2 T + logCeil ε + 10 ≤ T := by
  have h1 := LOf_le (T := T) (by omega) hε0 hε1
  have h2 := logb_T_le h64
  have hB' : (B d ε δ : ℝ) ≤ T := by exact_mod_cast hB
  rw [B_cast] at hB'
  have : (0 : ℝ) ≤ logCeil δ := Nat.cast_nonneg _
  exact ⟨h1, by linarith⟩

theorem LOf_le_T {d T : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (h64 : 64 ≤ T) (hB : B d ε δ ≤ T) : LOf T ε ≤ T := by
  have h := LOf_bound hε0 hε1 h64 hB
  have : (LOf T ε : ℝ) ≤ T := h.1.trans h.2
  exact_mod_cast this

/-- `sec:crossover`: for `T ≥ max(64, B)`, `J ≤ 4 log₂ T + E + F + 12 ≤ T`. -/
theorem JOf_le {d T : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (h64 : 64 ≤ T) (hB : B d ε δ ≤ T) :
    (JOf T d ε δ : ℝ) ≤ 4 * logb 2 T + logCeil ε + logCeil δ + 12 ∧
      4 * logb 2 T + logCeil ε + logCeil δ + 12 ≤ T := by
  have hT : (64 : ℝ) ≤ T := by exact_mod_cast h64
  have hB' : (B d ε δ : ℝ) ≤ T := by exact_mod_cast hB
  rw [B_cast] at hB'
  have hL : (LOf T ε : ℝ) ≤ T := by exact_mod_cast LOf_le_T hε0 hε1 h64 hB
  have hL1 : (1 : ℝ) ≤ LOf T ε := by
    have : (0 : ℝ) ≤ bTau T ε := Nat.cast_nonneg _
    rw [LOf_eq]; push_cast; linarith
  have hd1 : (d : ℝ) + 1 ≤ T := by
    have : (0 : ℝ) ≤ logCeil ε := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ logCeil δ := Nat.cast_nonneg _
    linarith
  have hεδ : ε * δ < 1 := by nlinarith
  have hεδ0 : 0 < ε * δ := mul_pos hε0 hδ0
  have hCq : (Cq : ℝ) = 52 := by simp [Cq]
  have hX1 : 1 ≤ 2 * (T : ℝ) * Cq * (d + 1) * LOf T ε / (ε * δ) := by
    rw [one_le_div hεδ0, hCq]
    have : (1 : ℝ) ≤ 2 * T * 52 * (d + 1) * LOf T ε := by
      have : (1 : ℝ) ≤ d + 1 := by linarith [(d.cast_nonneg : (0 : ℝ) ≤ d)]
      calc (1 : ℝ) ≤ 2 * 1 * 52 * 1 * 1 := by norm_num
        _ ≤ 2 * T * 52 * (d + 1) * LOf T ε := by gcongr; linarith
    linarith
  have hX : 2 * (T : ℝ) * Cq * (d + 1) * LOf T ε / (ε * δ) ≤ 2 * T ^ 4 * (1 / ε) * (1 / δ) := by
    rw [div_le_iff₀ hεδ0]
    have heq : 2 * (T : ℝ) ^ 4 * (1 / ε) * (1 / δ) * (ε * δ) = 2 * T ^ 4 := by
      field_simp
    rw [heq, hCq]
    have hT0 : (0 : ℝ) ≤ T := by linarith
    calc 2 * (T : ℝ) * 52 * (d + 1) * LOf T ε ≤ 2 * T * T * T * T := by
          gcongr
          · linarith
      _ = 2 * T ^ 4 := by ring
  have h := ceil_logb_lt_of_le hX1 hX
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
    (by positivity), Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one one_lt_two] at h
  have hE := logb_inv_le_logCeil ε
  have hF := logb_inv_le_logCeil δ
  have h2 := logb_T_le h64
  constructor
  · rw [JOf]; push_cast
    push_cast at h
    linarith
  · linarith

theorem JOf_le_T {d T : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (h64 : 64 ≤ T) (hB : B d ε δ ≤ T) : JOf T d ε δ ≤ T := by
  have h := JOf_le hε0 hε1 hδ0 hδ1 h64 hB
  have : (JOf T d ε δ : ℝ) ≤ T := h.1.trans h.2
  exact_mod_cast this

/-- `sec:crossover`: `D ≤ [801 C_q (d+1) T²]^d`. -/
theorem DOf_le {d T : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (h64 : 64 ≤ T) (hB : B d ε δ ≤ T) :
    DOf T d ε δ ≤ (801 * Cq * (d + 1) * T ^ 2) ^ d := by
  have hJ := JOf_le_T hε0 hε1 hδ0 hδ1 h64 hB
  have hk : kOf T d ε δ ≤ 800 * Cq * (d + 1) * T ^ 2 := by
    have : kOf T d ε δ = 800 * Cq * (d + 1) * (T * JOf T d ε δ) := by
      simp only [kOf, NOf]; ring
    rw [this, sq]
    gcongr
  have hd : d ≤ Cq * (d + 1) * T ^ 2 := by
    have : 1 ≤ Cq * T ^ 2 := by
      have : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ (by omega)
      simp only [Cq]; omega
    calc d ≤ (d + 1) * 1 := by omega
      _ ≤ (d + 1) * (Cq * T ^ 2) := by gcongr
      _ = Cq * (d + 1) * T ^ 2 := by ring
  have h801 : 801 * Cq * (d + 1) * T ^ 2 = 800 * Cq * (d + 1) * T ^ 2 + Cq * (d + 1) * T ^ 2 := by
    ring
  calc DOf T d ε δ ≤ (d + kOf T d ε δ) ^ d := Nat.choose_le_pow _ _
    _ ≤ (801 * Cq * (d + 1) * T ^ 2) ^ d := Nat.pow_le_pow_left (by omega) d

/-- `sec:crossover`: `V ≤ (2/(εδ)) [801 C_q (d+1)]^d T^{2d+2}`. -/
theorem VOf_le {d T : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (h64 : 64 ≤ T) (hB : B d ε δ ≤ T) :
    VOf T d ε δ ≤ 2 / (ε * δ) * (801 * Cq * (d + 1) : ℝ) ^ d * (T : ℝ) ^ (2 * d + 2) := by
  have hD : (DOf T d ε δ : ℝ) ≤ (801 * Cq * (d + 1) * (T : ℝ) ^ 2) ^ d := by
    exact_mod_cast DOf_le hε0 hε1 hδ0 hδ1 h64 hB
  have hL : (LOf T ε : ℝ) ≤ T := by exact_mod_cast LOf_le_T hε0 hε1 h64 hB
  have hεδ0 : 0 < ε * δ := mul_pos hε0 hδ0
  unfold VOf
  calc 2 * (T : ℝ) * DOf T d ε δ * LOf T ε / (ε * δ)
      ≤ 2 * (T : ℝ) * (801 * Cq * (d + 1) * (T : ℝ) ^ 2) ^ d * T / (ε * δ) := by
        apply div_le_div_of_nonneg_right _ hεδ0.le
        gcongr
    _ = 2 / (ε * δ) * (801 * Cq * (d + 1) : ℝ) ^ d * (T : ℝ) ^ (2 * d + 2) := by
        rw [mul_pow, ← pow_mul]
        field_simp
        ring

/-- `sec:crossover`: every `W ≤ V^{C_q}` satisfies `W ≤ A T^p`. -/
theorem W_le_A_mul_pow {d T : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) (h64 : 64 ≤ T) (hB : B d ε δ ≤ T) {W : ℝ} (hW : W ≤ VOf T d ε δ ^ Cq) :
    W ≤ A d ε δ * (T : ℝ) ^ pExp d := by
  have hV := VOf_le hε0 hε1 hδ0 hδ1 h64 hB
  have hV0 : 0 ≤ VOf T d ε δ := by
    unfold VOf; have := mul_pos hε0 hδ0; positivity
  refine hW.trans ((pow_le_pow_left₀ hV0 hV Cq).trans (le_of_eq ?_))
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, A, pExp, mul_comm d Cq, mul_comm (2 * d + 2) Cq]

/-- `sec:crossover`: `log T ≤ √T` (stated for all `T > 0`). -/
theorem log_le_sqrt {x : ℝ} (hx : 0 < x) : log x ≤ √x := by
  have hs : 0 < √x := Real.sqrt_pos.mpr hx
  have he : 0 < exp 1 := exp_pos 1
  have h1 : log (√x / exp 1) ≤ √x / exp 1 - 1 := Real.log_le_sub_one_of_pos (div_pos hs he)
  rw [Real.log_div hs.ne' he.ne', Real.log_exp] at h1
  have h2 : log x = 2 * log √x := by rw [Real.log_sqrt hx.le]; ring
  have h3 : 2 < exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h4 : 2 * (√x / exp 1) ≤ √x := by
    rw [mul_div_assoc', div_le_iff₀ he]; nlinarith
  linarith

/-- `sec:crossover`: if `T ≥ 1`, `T ≥ p²` and `T ≥ ⌈log₂ (25A/3)⌉` with `A > 0`, then
`A T^p ≤ (3/25) e^{2T}`. -/
theorem A_mul_pow_le {Aval : ℝ} {p T : ℕ} (hA : 0 < Aval) (hT : 1 ≤ T) (hp : p ^ 2 ≤ T)
    (hlog : ⌈logb 2 (25 * Aval / 3)⌉₊ ≤ T) :
    Aval * (T : ℝ) ^ p ≤ 3 / 25 * exp (2 * T) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hy : 0 < 25 * Aval / 3 := by linarith
  have h1 : 25 * Aval / 3 ≤ exp T := by
    have hl : logb 2 (25 * Aval / 3) ≤ T :=
      (Nat.le_ceil _).trans (by exact_mod_cast hlog)
    have hlog2 : log (25 * Aval / 3) = logb 2 (25 * Aval / 3) * log 2 := by
      rw [Real.logb, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
    have h2 := Real.log_two_lt_d9
    have h3 := Real.log_two_gt_d9
    have : log (25 * Aval / 3) ≤ T := by
      rw [hlog2]; nlinarith
    rw [← Real.exp_log hy]
    exact Real.exp_le_exp.mpr this
  have h2 : (T : ℝ) ^ p ≤ exp T := by
    have hp' : (p : ℝ) ≤ √(T : ℝ) := by
      rw [Real.le_sqrt (by positivity) hT0.le]; exact_mod_cast hp
    have hsq : √(T : ℝ) * √(T : ℝ) = T := Real.mul_self_sqrt hT0.le
    have hlogT := log_le_sqrt hT0
    have hlog0 : 0 ≤ log (T : ℝ) := Real.log_nonneg hT'
    have : (p : ℝ) * log T ≤ T := by
      calc (p : ℝ) * log T ≤ √(T : ℝ) * √(T : ℝ) := by
            apply mul_le_mul hp' hlogT hlog0 (Real.sqrt_nonneg _)
        _ = T := hsq
    calc (T : ℝ) ^ p = exp (p * log T) := by rw [Real.exp_nat_mul, Real.exp_log hT0]
      _ ≤ exp T := Real.exp_le_exp.mpr this
  have h3 : exp (2 * (T : ℝ)) = exp T * exp T := by rw [← Real.exp_add]; ring_nf
  rw [h3]
  have hTp : 0 ≤ (T : ℝ) ^ p := by positivity
  calc Aval * (T : ℝ) ^ p = 3 / 25 * ((25 * Aval / 3) * (T : ℝ) ^ p) := by ring
    _ ≤ 3 / 25 * (exp T * exp T) := by gcongr

/-- `sec:crossover`, the baseline comparison: for `0 < ξ ≤ 1/6`, `(6/5) e^{2T} ≤ e^{2T}/(30 ξ²)`. -/
theorem six_fifths_le {x ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) :
    6 / 5 * exp x ≤ exp x / (30 * ξ ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  have : ξ ^ 2 ≤ 1 / 36 := by nlinarith
  have := exp_pos x
  nlinarith

theorem A_pos {d : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hδ0 : 0 < δ) : 0 < A d ε δ := by
  have hc : (0 : ℝ) < 801 * Cq * (d + 1) := by rw [Cq_eq]; positivity
  unfold A
  exact mul_pos (pow_pos (div_pos two_pos (mul_pos hε0 hδ0)) _) (pow_pos hc _)

/-- `sec:crossover`: for every natural `T ≥ T_10` and every `W ≤ V^{C_q}`,
`W ≤ A T^p ≤ (3/25) e^{2T}`, and for `0 < ξ ≤ 1/6`, `10 W ≤ (6/5) e^{2T} ≤ e^{2T}/(30 ξ²)`.
Here `W ≤ V^{C_q}` is the token envelope (`eq:gls-polynomial-envelope`) and `e^{2T}/(30 ξ²)` is the
reply lower bound of `lem:gls-root-simulation`; neither is proved in this file. -/
theorem crossover {d : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {T : ℕ} (hT : T10 d ε δ ≤ T) {W : ℝ} (hW : W ≤ VOf T d ε δ ^ Cq)
    {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) :
    W ≤ A d ε δ * (T : ℝ) ^ pExp d ∧ A d ε δ * (T : ℝ) ^ pExp d ≤ 3 / 25 * exp (2 * T) ∧
      10 * W ≤ 6 / 5 * exp (2 * T) ∧ 6 / 5 * exp (2 * T) ≤ exp (2 * T) / (30 * ξ ^ 2) := by
  simp only [T10, max_le_iff] at hT
  obtain ⟨⟨⟨h64, hB⟩, hp⟩, hlog⟩ := hT
  have h1 := W_le_A_mul_pow hε0 hε1 hδ0 hδ1 h64 hB hW
  have h2 := A_mul_pow_le (A_pos hε0 hδ0) (by omega) hp hlog
  exact ⟨h1, h2, by linarith, six_fifths_le hξ0 hξ1⟩

/-- `sec:crossover`, the tenfold conclusion: `10 W ≤ e^{2T}/(30 ξ²)` for `T ≥ T_10`. -/
theorem crossover_tenfold {d : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {T : ℕ} (hT : T10 d ε δ ≤ T) {W : ℝ} (hW : W ≤ VOf T d ε δ ^ Cq)
    {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) :
    10 * W ≤ exp (2 * T) / (30 * ξ ^ 2) := by
  have h := crossover hε0 hε1 hδ0 hδ1 hT hW hξ0 hξ1
  linarith [h.2.2.1, h.2.2.2]

/-! ### The concrete crossover `cor:tenfold2048` -/

/-- `cor:tenfold2048`: `E = F = ⌈log₂ 100⌉ = 7`. -/
theorem logCeil_hundredth : logCeil (1 / 100) = 7 := by
  unfold logCeil
  rw [show (1 : ℝ) / (1 / 100) = 100 by norm_num, Nat.ceil_eq_iff (by norm_num)]
  constructor
  · have h := Real.logb_lt_logb one_lt_two (by norm_num) (show (2 : ℝ) ^ 6 < 100 by norm_num)
    rw [logb_two_pow] at h
    norm_num at h ⊢; exact h
  · have h := Real.logb_le_logb_of_le one_lt_two (by norm_num)
      (show (100 : ℝ) ≤ 2 ^ 7 by norm_num)
    rw [logb_two_pow] at h
    exact_mod_cast h

/-- `cor:tenfold2048`: `B = 174` for `d = 1`, `ε = δ = 1/100`. -/
theorem B_tenfold : B 1 (1 / 100) (1 / 100) = 174 := by
  rw [B, logCeil_hundredth, Cq_eq]

/-- `cor:tenfold2048`: `p = 208` for `d = 1`. -/
theorem pExp_one : pExp 1 = 208 := by rw [pExp, Cq_eq]

/-- `cor:tenfold2048`: `A = 1666080000^{52}` for `d = 1`, `ε = δ = 1/100`. -/
theorem A_tenfold : A 1 (1 / 100) (1 / 100) = 1666080000 ^ 52 := by
  rw [A, Cq_eq, show (1666080000 : ℝ) = 20000 * 83304 by norm_num, mul_pow]
  norm_num

/-- `cor:tenfold2048`: `A < 2^{31 ⋅ 52} = 2^{1612}`. -/
theorem A_tenfold_lt : A 1 (1 / 100) (1 / 100) < 2 ^ 1612 := by
  rw [A_tenfold, show (1612 : ℕ) = 31 * 52 by norm_num, pow_mul]
  exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by norm_num)

/-- `cor:tenfold2048`: `(25/3) A 2048^{208} < 2^{3904} < e^{4096}`. -/
theorem tenfold_numeric :
    25 / 3 * A 1 (1 / 100) (1 / 100) * 2048 ^ 208 < 2 ^ 3904 ∧ (2 : ℝ) ^ 3904 < exp 4096 := by
  constructor
  · have hA := A_tenfold_lt
    have hA0 : 0 < A 1 (1 / 100) (1 / 100) := A_pos (by norm_num) (by norm_num)
    have h1 : 25 / 3 * A 1 (1 / 100) (1 / 100) < 2 ^ 4 * 2 ^ 1612 :=
      mul_lt_mul'' (by norm_num) hA (by norm_num) hA0.le
    calc 25 / 3 * A 1 (1 / 100) (1 / 100) * 2048 ^ 208 < 2 ^ 4 * 2 ^ 1612 * 2048 ^ 208 :=
          mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ 3904 := by
          rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
  · have h2 : (2 : ℝ) < exp 1 := by have := Real.exp_one_gt_d9; linarith
    calc (2 : ℝ) ^ 3904 < exp 1 ^ 3904 := pow_lt_pow_left₀ h2 (by norm_num) (by norm_num)
      _ = exp 3904 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ exp 4096 := Real.exp_le_exp.mpr (by norm_num)

/-- `cor:tenfold2048`: `W ≤ A T^{208}` already holds for `T ≥ 174`. -/
theorem W_le_tenfold {T : ℕ} (hT : 174 ≤ T) {W : ℝ}
    (hW : W ≤ VOf T 1 (1 / 100) (1 / 100) ^ Cq) :
    W ≤ A 1 (1 / 100) (1 / 100) * (T : ℝ) ^ 208 := by
  have h := W_le_A_mul_pow (d := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by rw [B_tenfold]; exact hT) hW
  rwa [pExp_one] at h

/-- `e^{2x}/x^p` is nondecreasing on `x ≥ p/2`. -/
theorem exp_div_pow_mono {p : ℕ} {x y : ℝ} (hx : (p : ℝ) ≤ 2 * x) (hx0 : 0 < x) (hxy : x ≤ y) :
    exp (2 * x) / x ^ p ≤ exp (2 * y) / y ^ p := by
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : y / x ≤ exp (y / x - 1) := by linarith [Real.add_one_le_exp (y / x - 1)]
  have h2 : (y / x) ^ p ≤ exp (p * (y / x - 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h1 p
  have h3 : (p : ℝ) * (y / x - 1) ≤ 2 * (y - x) := by
    rw [show (p : ℝ) * (y / x - 1) = p * (y - x) / x by field_simp]
    rw [div_le_iff₀ hx0]
    nlinarith
  have h4 : y ^ p ≤ x ^ p * exp (2 * (y - x)) := by
    have : y ^ p = x ^ p * (y / x) ^ p := by rw [div_pow]; field_simp
    rw [this]
    gcongr
    exact h2.trans (Real.exp_le_exp.mpr h3)
  have he : exp (2 * y) = exp (2 * x) * exp (2 * (y - x)) := by rw [← Real.exp_add]; ring_nf
  calc exp (2 * x) * y ^ p ≤ exp (2 * x) * (x ^ p * exp (2 * (y - x))) := by gcongr
    _ = exp (2 * y) * x ^ p := by rw [he]; ring

/-- `cor:tenfold2048`: `e^{2T}/T^{208}` is nondecreasing for `T ≥ 104`. -/
theorem exp_div_pow_208_mono {x y : ℝ} (hx : 104 ≤ x) (hxy : x ≤ y) :
    exp (2 * x) / x ^ 208 ≤ exp (2 * y) / y ^ 208 :=
  exp_div_pow_mono (by push_cast; linarith) (by linarith) hxy

/-- `cor:tenfold2048`: for `d = 1`, `ε = δ = 1/100`, every natural `T ≥ 2048`, every token budget
`W ≤ V^{C_q}` and every tolerance `0 < ξ ≤ 1/6`, `10 W < e^{2T}/(30 ξ²)`. -/
theorem tenfold2048 {T : ℕ} (hT : 2048 ≤ T) {W : ℝ}
    (hW : W ≤ VOf T 1 (1 / 100) (1 / 100) ^ Cq) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) :
    10 * W < exp (2 * T) / (30 * ξ ^ 2) := by
  have hT' : (2048 : ℝ) ≤ T := by exact_mod_cast hT
  have hW' := W_le_tenfold (by omega) hW
  have hA0 : 0 < A 1 (1 / 100) (1 / 100) := A_pos (by norm_num) (by norm_num)
  have hnum := tenfold_numeric
  have hmono := exp_div_pow_208_mono (by norm_num) hT'
  have hT208 : (T : ℝ) ^ 208 ≤ exp (2 * T) * 2048 ^ 208 / exp 4096 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hmono
    rw [le_div_iff₀ (exp_pos _)]
    norm_num at hmono
    linarith
  have hkey : A 1 (1 / 100) (1 / 100) * (T : ℝ) ^ 208 < 3 / 25 * exp (2 * T) := by
    have hlt : 25 / 3 * A 1 (1 / 100) (1 / 100) * 2048 ^ 208 < exp 4096 :=
      hnum.1.trans hnum.2
    have he : 0 < exp (2 * (T : ℝ)) := exp_pos _
    calc A 1 (1 / 100) (1 / 100) * (T : ℝ) ^ 208
        ≤ A 1 (1 / 100) (1 / 100) * (exp (2 * T) * 2048 ^ 208 / exp 4096) :=
          mul_le_mul_of_nonneg_left hT208 hA0.le
      _ = 3 / 25 * exp (2 * T) * ((25 / 3 * A 1 (1 / 100) (1 / 100) * 2048 ^ 208) / exp 4096) := by
          ring
      _ < 3 / 25 * exp (2 * T) * 1 := by
          gcongr
          rw [div_lt_one (exp_pos _)]; exact hlt
      _ = 3 / 25 * exp (2 * T) := by ring
  have h6 := six_fifths_le (x := 2 * T) hξ0 hξ1
  linarith

/-! ### The envelope's token count satisfies the crossover hypothesis -/

/-- The input of `lem:explicit-gls-token-envelope` used by Algorithm `alg:fixed`: rank
`D = DOf T d ε δ` and integer logit bound `L = LOf T ε` of `eq:smooth-parameters`. -/
noncomputable def envInput (T d : ℕ) (ε δ : ℝ) : Input := ⟨T, DOf T d ε δ, LOf T ε, ε, δ⟩

/-- The envelope's `V = 2TDL/(εδ)` is `VOf` of `eq:gls-polynomial-envelope`. -/
theorem envInput_V (T d : ℕ) (ε δ : ℝ) : (envInput T d ε δ).V = VOf T d ε δ := rfl

theorem envInput_valid {T d : ℕ} {ε δ : ℝ} (hT : 32 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) : (envInput T d ε δ).Valid where
  T_ge := hT
  d_pos := Nat.choose_pos (Nat.le_add_right d _)
  L_pos := by change 1 ≤ LOf T ε; rw [LOf_eq]; omega
  ε_pos := hε0
  ε_lt := hε1
  δ_pos := hδ0
  δ_lt := hδ1

/-- `eq:gls-polynomial-envelope`: the full training-token count of the envelope with rank `D`
and logit bound `L` is at most `V^{C_q}`, `C_q = 52`. -/
theorem envelope_tokens_le {T d : ℕ} {ε δ : ℝ} (hT : 32 ≤ T) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) : (envInput T d ε δ).tokens ≤ VOf T d ε δ ^ Cq := by
  have h := (Input.explicit_gls_token_envelope (envInput_valid (d := d) hT hε0 hε1 hδ0 hδ1)).2.2
  rwa [envInput_V] at h

/-- `sec:crossover` applied to the envelope's own token count: for `T ≥ T_10` and
`0 < ξ ≤ 1/6`, `10 W ≤ e^{2T}/(30 ξ²)`. -/
theorem crossover_envelope {d : ℕ} {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {T : ℕ} (hT : T10 d ε δ ≤ T) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) :
    10 * (envInput T d ε δ).tokens ≤ exp (2 * T) / (30 * ξ ^ 2) := by
  have h64 : 64 ≤ T := le_trans (by simp [T10]) hT
  exact crossover_tenfold hε0 hε1 hδ0 hδ1 hT
    (envelope_tokens_le (by omega) hε0 hε1 hδ0 hδ1) hξ0 hξ1

/-- `cor:tenfold2048` applied to the envelope's own token count. -/
theorem tenfold2048_envelope {T : ℕ} (hT : 2048 ≤ T) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) :
    10 * (envInput T 1 (1 / 100) (1 / 100)).tokens < exp (2 * T) / (30 * ξ ^ 2) :=
  tenfold2048 hT (envelope_tokens_le (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)) hξ0 hξ1

end LowLogitRank.Crossover
