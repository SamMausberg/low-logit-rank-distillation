import LowLogitRank.Basic

/-!
# Explicit parameters of the robust learner (`lem:explicit-gls-token-envelope`)

This file formalizes the arithmetic of `sec:explicit-gls-procedure`,
`lem:explicit-gls-token-envelope` and `sec:gls-validation-arithmetic`:

* the parameter tuple `eq:explicit-gls-parameters` (`Input` and its fields),
* the tolerance `eq:explicit-gls-tolerance` and the fact that `ξ` is the largest power of two
  below `g / (1024 K √(d J_b))`,
* the success and accuracy margins ("Explicit success and accuracy margins"),
* the request counting ("Explicit request caps preserving the sharper rate",
  `eq:global-future-dimension`, `eq:explicit-gls-request-caps`),
* the numerical polynomial envelope ("A numerical polynomial envelope").

The probabilistic and algorithmic statements that these numbers feed are proved elsewhere: the
spanner guarantee, the validation tail bound and the adapted Hoeffding bound in `Spanner/*`, the
determinant witness bound and the TV telescope in `Witness/*` (applied to these parameters in
`Envelope/Witness.lean`). Here their numerical consequences take the corresponding quantities
as hypotheses.
Logarithmic ceilings `⌈log₂ x⌉` are `Nat.ceil (Real.logb 2 x)`; all their arguments are `≥ 1`.
-/

namespace LowLogitRank.Envelope

open Real Finset

/-! ### Elementary logarithm and ceiling bounds -/

theorem logb_two_pow (k : ℕ) : logb 2 ((2 : ℝ) ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- `log₂ x ≤ x / c` for `x ≥ 2^k`, provided `k c ≤ 2^k` and `3 c ≤ 2 ⋅ 2^k`. -/
theorem logb_two_le_div {k : ℕ} {c x : ℝ} (hc : 0 < c) (hk : (k : ℝ) * c ≤ 2 ^ k)
    (hc' : 3 * c ≤ 2 * 2 ^ k) (hx : (2 : ℝ) ^ k ≤ x) : logb 2 x ≤ x / c := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hx0 : 0 < x := lt_of_lt_of_le h2k hx
  have hl2 := Real.log_two_gt_d9
  have hlog : log (x / 2 ^ k) ≤ x / 2 ^ k - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hx0.ne' h2k.ne', Real.log_pow] at hlog
  rw [Real.logb, div_le_div_iff₀ (Real.log_pos one_lt_two) hc]
  set y := x / 2 ^ k with hy
  have hxy : x = y * 2 ^ k := by rw [hy]; field_simp
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ h2k]; linarith
  have hlogx : log x ≤ k * log 2 + (y - 1) := by linarith
  have hcl : c ≤ 2 ^ k * log 2 := by nlinarith
  calc log x * c ≤ (k * log 2 + (y - 1)) * c := by gcongr
    _ = (k * c) * log 2 + (y - 1) * c := by ring
    _ ≤ 2 ^ k * log 2 + (y - 1) * (2 ^ k * log 2) := by
        gcongr
    _ = x * log 2 := by rw [hxy]; ring

/-- The elementary inequality `log₂ V ≤ V / 32` for `V ≥ 256`. -/
theorem logb_le_div_32 {x : ℝ} (hx : 256 ≤ x) : logb 2 x ≤ x / 32 :=
  logb_two_le_div (k := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num; exact hx)

/-- `log₂ T ≤ T / 8` for `T ≥ 64`. -/
theorem logb_le_div_8 {x : ℝ} (hx : 64 ≤ x) : logb 2 x ≤ x / 8 :=
  logb_two_le_div (k := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num; exact hx)

/-- The natural logarithm is at most the base-two logarithm on `[1, ∞)`. -/
theorem log_le_logb_two {x : ℝ} (hx : 1 ≤ x) : log x ≤ logb 2 x := by
  have h0 := Real.log_nonneg hx
  have hl2 := Real.log_two_lt_d9
  rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two)]
  nlinarith

/-- A base-two logarithmic ceiling is less than the logarithm of any upper bound plus one. -/
theorem ceil_logb_lt_of_le {X Y : ℝ} (hX : 1 ≤ X) (h : X ≤ Y) :
    (⌈logb 2 X⌉₊ : ℝ) < logb 2 Y + 1 := by
  have h1 : logb 2 X ≤ logb 2 Y := Real.logb_le_logb_of_le one_lt_two (by linarith) h
  have := Nat.ceil_lt_add_one (Real.logb_nonneg one_lt_two hX)
  linarith

/-- The logarithmic ceiling of a quantity bounded by `2^b V^a`. -/
theorem ceil_logb_lt {X V : ℝ} {a b : ℕ} (hX : 1 ≤ X) (hV : 0 < V) (h : X ≤ 2 ^ b * V ^ a) :
    (⌈logb 2 X⌉₊ : ℝ) < a * logb 2 V + b + 1 := by
  have h1 := ceil_logb_lt_of_le hX h
  rw [Real.logb_mul (by positivity) (by positivity), logb_two_pow, Real.logb_pow] at h1
  linarith

theorem one_le_ceil_logb {X : ℝ} (hX : 1 < X) : 1 ≤ ⌈logb 2 X⌉₊ :=
  Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (Nat.ceil_pos.mpr (Real.logb_pos one_lt_two hX)))

/-- `2^{⌈log₂ x⌉} < 2x` for `x ≥ 1`. -/
theorem two_pow_ceil_logb_lt {x : ℝ} (hx : 1 ≤ x) : (2 : ℝ) ^ ⌈logb 2 x⌉₊ < 2 * x := by
  have h := Nat.ceil_lt_add_one (Real.logb_nonneg one_lt_two hx)
  have hx0 : 0 < x := by linarith
  calc (2 : ℝ) ^ ⌈logb 2 x⌉₊ = (2 : ℝ) ^ ((⌈logb 2 x⌉₊ : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ < (2 : ℝ) ^ (logb 2 x + 1) := Real.rpow_lt_rpow_of_exponent_lt one_lt_two h
    _ = 2 * x := by
        rw [Real.rpow_add two_pos, Real.rpow_logb two_pos (by norm_num) hx0, Real.rpow_one]
        ring

/-- `x ≤ 2^{⌈log₂ x⌉}` for `x > 0`. -/
theorem le_two_pow_ceil_logb {x : ℝ} (hx : 0 < x) : x ≤ (2 : ℝ) ^ ⌈logb 2 x⌉₊ := by
  calc x = (2 : ℝ) ^ logb 2 x := (Real.rpow_logb two_pos (by norm_num) hx).symm
    _ ≤ (2 : ℝ) ^ ((⌈logb 2 x⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
    _ = (2 : ℝ) ^ ⌈logb 2 x⌉₊ := Real.rpow_natCast _ _

/-- `x^{3/2} = x √x` for `x ≥ 0`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * √x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

/-! ### The parameter tuple `eq:explicit-gls-parameters` -/

/-- The inputs of `lem:explicit-gls-token-envelope`: length `T`, rank `d`, integer logit bound `L`,
accuracy `ε` and confidence `δ`. -/
structure Input where
  T : ℕ
  d : ℕ
  L : ℕ
  ε : ℝ
  δ : ℝ

namespace Input

/-- The hypotheses of `lem:explicit-gls-token-envelope`: `T ≥ 32`, `d, L ≥ 1`, `0 < ε, δ < 1/2`.
(The paper asks for rational `ε, δ`; only their real values matter for the arithmetic.) -/
structure Valid (p : Input) : Prop where
  T_ge : 32 ≤ p.T
  d_pos : 1 ≤ p.d
  L_pos : 1 ≤ p.L
  ε_pos : 0 < p.ε
  ε_lt : p.ε < 1 / 2
  δ_pos : 0 < p.δ
  δ_lt : p.δ < 1 / 2

variable (p : Input)

/-- The factor bound `α = dL + 1`. -/
def alpha : ℕ := p.d * p.L + 1

/-- `V = 2TdL/(εδ)`. -/
noncomputable def V : ℝ := 2 * p.T * p.d * p.L / (p.ε * p.δ)

/-- `J_b = ⌈log₂ (2Tdα/(εδ))⌉ + 64`. -/
noncomputable def Jb : ℕ := ⌈logb 2 (2 * p.T * p.d * p.alpha / (p.ε * p.δ))⌉₊ + 64

/-- The epoch bound `K = 512 T d J_b`. -/
noncomputable def K : ℕ := 512 * p.T * p.d * p.Jb

/-- The discrepancy threshold `g = ε/(32T²)`. -/
noncomputable def g : ℝ := p.ε / (32 * p.T ^ 2)

/-- The condition `2^{-2b} ≤ g² / (1024² K² d J_b)` defining `b_ξ`. -/
def XiCond (b : ℕ) : Prop :=
  ((2 : ℝ) ^ (2 * b))⁻¹ ≤ p.g ^ 2 / (1024 ^ 2 * p.K ^ 2 * p.d * p.Jb)

/-- `b_ξ`, the least natural `b` with `2^{-2b} ≤ g² / (1024² K² d J_b)` (`Nat.find`; the junk
value `0` is used only if no such `b` exists, which never happens under `Valid`). -/
noncomputable def bXi : ℕ := by
  classical exact if h : ∃ b, p.XiCond b then Nat.find h else 0

/-- The robust tolerance `ξ = 2^{-b_ξ}`. -/
noncomputable def xi : ℝ := ((2 : ℝ) ^ p.bXi)⁻¹

/-- The number of validation samples `n = ⌈g⁻¹ ⌈log₂ (32KT/δ)⌉⌉`. -/
noncomputable def n : ℕ := ⌈p.g⁻¹ * ⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊⌉₊

/-- The spanner's missed-mass allowance `η = ε/(3T²n)`. -/
noncomputable def eta : ℝ := p.ε / (3 * p.T ^ 2 * p.n)

/-- The spanner failure allowance `δ_s = δ/(32KT)`. -/
noncomputable def deltaS : ℝ := p.δ / (32 * p.K * p.T)

/-- `H_⋆ = max(⌈log₂ (12K/η)⌉, ⌈log₂ ((6K+1)/δ_s)⌉)`. -/
noncomputable def Hstar : ℕ :=
  max ⌈logb 2 (12 * p.K / p.eta)⌉₊ ⌈logb 2 ((6 * p.K + 1) / p.deltaS)⌉₊

/-- The request cap `Q` of `eq:explicit-gls-request-caps`. -/
noncomputable def Q : ℕ :=
  ⌈900 * p.Hstar * p.K ^ 3 / p.eta⌉₊ + 24 * p.n * p.T ^ 3 * p.K ^ 2 + p.K * p.n + 18 * p.T * p.K

/-- The numerical-logit request cap `R_ℓ = Q`. -/
noncomputable def Rl : ℕ := p.Q

/-- The complete-sample request cap `R_s = Q`. -/
noncomputable def Rs : ℕ := p.Q

/-- The smoothing floor `γ = τ/2` with `τ = 2^{-b_τ}`, `b_τ = ⌈log₂ (8T/ε)⌉` (`tauOf`). -/
noncomputable def gamma : ℝ := tauOf p.T p.ε / 2

/-- The estimator's simulated conditional bits per numerical request,
`M_est = ⌈(192/(γ ξ²)) ⌈log₂ (16 R_ℓ/δ)⌉⌉`. -/
noncomputable def Mest : ℕ := ⌈192 / (p.gamma * p.xi ^ 2) * ⌈logb 2 (16 * p.Rl / p.δ)⌉₊⌉₊

/-- The token bound `W = R_ℓ M_est V² + R_s T V²` of the last display of the proof. -/
noncomputable def W : ℝ := p.Rl * p.Mest * p.V ^ 2 + p.Rs * p.T * p.V ^ 2

/-- The full training-token count charged in the proof: every simulated conditional bit costs
`T + b_τ + 1` tokens (prefix, returned bit and the `b_τ` fair branch coins), with `M_est` bits
per numerical request and `T` bits per complete sample. -/
noncomputable def tokens : ℝ :=
  p.Rl * p.Mest * (p.T + bTau p.T p.ε + 1) + p.Rs * p.T * (p.T + bTau p.T p.ε + 1)

/-- The real number `g / (1024 K √(d J_b))` whose largest power-of-two minorant is `ξ`. -/
noncomputable def xiTarget : ℝ := p.g / (1024 * p.K * √(p.d * p.Jb))

/-- The analysis scale `e₀ = g / (16 √(d J_b))` of the witness bound. -/
noncomputable def e0 : ℝ := p.g / (16 * √(p.d * p.Jb))

/-! ### Basic facts under the hypotheses -/

variable {p}

theorem alpha_cast : (p.alpha : ℝ) = p.d * p.L + 1 := by simp [alpha]

theorem Jb_ge : 64 ≤ p.Jb := by simp [Jb]

theorem K_cast : (p.K : ℝ) = 512 * p.T * p.d * p.Jb := by simp [K]

theorem Jb_ge_real : (64 : ℝ) ≤ p.Jb := by exact_mod_cast Jb_ge (p := p)

theorem g_inv_eq : p.g⁻¹ = 32 * p.T ^ 2 / p.ε := by rw [g, inv_div]

theorem xi_pos : 0 < p.xi := by unfold xi; positivity

/-- `sec:gls-validation-arithmetic`: the oracle grid has `b_A = ⌈log₂ (16/ξ)⌉ = b_ξ + 4`
fractional bits. -/
theorem ceil_logb_sixteen_div_xi : ⌈logb 2 (16 / p.xi)⌉₊ = p.bXi + 4 := by
  have : 16 / p.xi = (2 : ℝ) ^ (p.bXi + 4) := by
    rw [xi, div_inv_eq_mul, pow_add]; norm_num; ring
  rw [this, logb_two_pow]
  exact_mod_cast Nat.ceil_natCast _

section Basic

variable (hp : p.Valid)
include hp

theorem T_ge_real : (32 : ℝ) ≤ p.T := by exact_mod_cast hp.T_ge
theorem T_pos : (0 : ℝ) < p.T := by have := T_ge_real hp; linarith
theorem d_ge_one : (1 : ℝ) ≤ p.d := by exact_mod_cast hp.d_pos
theorem L_ge_one : (1 : ℝ) ≤ p.L := by exact_mod_cast hp.L_pos
theorem eps_delta_lt : p.ε * p.δ < 1 / 4 := by
  have := mul_lt_mul'' hp.ε_lt hp.δ_lt hp.ε_pos.le hp.δ_pos.le
  linarith
theorem eps_delta_pos : 0 < p.ε * p.δ := mul_pos hp.ε_pos hp.δ_pos

theorem K_ge_one : (1 : ℝ) ≤ p.K := by
  rw [K_cast]
  have := T_ge_real hp; have := d_ge_one hp; have := Jb_ge_real (p := p)
  calc (1 : ℝ) ≤ 512 * 32 * 1 * 64 := by norm_num
    _ ≤ 512 * p.T * p.d * p.Jb := by gcongr

theorem K_pos : (0 : ℝ) < p.K := by have := K_ge_one hp; linarith

theorem g_pos : 0 < p.g := by
  unfold g; have := T_pos hp; have := hp.ε_pos; positivity

theorem g_lt_one : p.g < 1 := by
  have hT := T_ge_real hp
  rw [g, div_lt_one (by positivity)]
  have := hp.ε_lt
  nlinarith

theorem dJb_ge_one : (1 : ℝ) ≤ p.d * p.Jb := by
  have := d_ge_one hp; have := Jb_ge_real (p := p); nlinarith

end Basic

/-! ### The tolerance `ξ` (`eq:explicit-gls-parameters`, `eq:explicit-gls-tolerance`) -/

section Xi

variable (hp : p.Valid)
include hp

theorem xiTarget_pos : 0 < p.xiTarget := by
  have := g_pos hp; have := K_pos hp; have := dJb_ge_one hp
  unfold xiTarget; positivity

theorem xiTarget_le_g : p.xiTarget ≤ p.g := by
  have hK := K_ge_one hp
  have hs : 1 ≤ √(p.d * p.Jb : ℝ) := Real.one_le_sqrt.mpr (dJb_ge_one hp)
  unfold xiTarget
  apply div_le_self (g_pos hp).le
  nlinarith

theorem xiCond_iff (b : ℕ) : p.XiCond b ↔ ((2 : ℝ) ^ b)⁻¹ ≤ p.xiTarget := by
  have hsq : p.xiTarget ^ 2 = p.g ^ 2 / (1024 ^ 2 * p.K ^ 2 * p.d * p.Jb) := by
    have h0 : (0 : ℝ) ≤ p.d * p.Jb := by have := dJb_ge_one hp; linarith
    rw [xiTarget, div_pow, mul_pow, mul_pow, Real.sq_sqrt h0]
    ring
  have hl : ((2 : ℝ) ^ (2 * b))⁻¹ = (((2 : ℝ) ^ b)⁻¹) ^ 2 := by
    rw [pow_mul', inv_pow]
  rw [XiCond, ← hsq, hl, pow_le_pow_iff_left₀ (by positivity) (xiTarget_pos hp).le two_ne_zero]

theorem exists_xiCond : ∃ b, p.XiCond b := by
  obtain ⟨b, hb⟩ := exists_pow_lt_of_lt_one (xiTarget_pos hp) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨b, (xiCond_iff hp b).mpr ?_⟩
  rw [one_div, inv_pow] at hb
  exact hb.le

theorem xiCond_bXi : p.XiCond p.bXi := by
  classical
  unfold bXi
  split_ifs with h
  · convert Nat.find_spec h
  · exact absurd (exists_xiCond hp) h

theorem not_xiCond_of_lt {b : ℕ} (hb : b < p.bXi) : ¬ p.XiCond b := by
  classical
  unfold bXi at hb
  split_ifs at hb with h
  · convert Nat.find_min h hb
  · exact absurd (exists_xiCond hp) h

/-- `ξ ≤ g / (1024 K √(d J_b))`. -/
theorem xi_le_xiTarget : p.xi ≤ p.xiTarget := (xiCond_iff hp _).mp (xiCond_bXi hp)

theorem bXi_pos : 0 < p.bXi := by
  rcases Nat.eq_zero_or_pos p.bXi with h | h
  · have h1 := xi_le_xiTarget hp
    have h2 := xiTarget_le_g hp
    have h3 := g_lt_one hp
    rw [xi, h] at h1
    norm_num at h1
    linarith
  · exact h

/-- `g / (1024 K √(d J_b)) < 2 ξ`. -/
theorem xiTarget_lt_two_mul_xi : p.xiTarget < 2 * p.xi := by
  have h := not_xiCond_of_lt hp (Nat.sub_lt (bXi_pos hp) one_pos)
  rw [xiCond_iff hp, not_le] at h
  have he : ((2 : ℝ) ^ (p.bXi - 1))⁻¹ = 2 * p.xi := by
    have : p.bXi = (p.bXi - 1) + 1 := (Nat.sub_add_cancel (bXi_pos hp)).symm
    rw [xi, this, pow_succ, Nat.add_sub_cancel]
    field_simp
  rwa [he] at h

/-- `eq:explicit-gls-parameters`: `ξ = 2^{-b_ξ}` is the largest power of two (with any integer
exponent) not exceeding `g / (1024 K √(d J_b))`. -/
theorem xi_isGreatest_pow_two :
    p.xi = (2 : ℝ) ^ (-(p.bXi : ℤ)) ∧ p.xi ≤ p.xiTarget ∧
      ∀ k : ℤ, (2 : ℝ) ^ k ≤ p.xiTarget → (2 : ℝ) ^ k ≤ p.xi := by
  have hxi : p.xi = (2 : ℝ) ^ (-(p.bXi : ℤ)) := by rw [xi, zpow_neg, zpow_natCast]
  refine ⟨hxi, xi_le_xiTarget hp, fun k hk => ?_⟩
  by_contra hcon
  rw [not_le, hxi, zpow_lt_zpow_iff_right₀ one_lt_two] at hcon
  have h1 : (2 : ℝ) ^ (-(p.bXi : ℤ) + 1) ≤ 2 ^ k :=
    zpow_le_zpow_right₀ one_le_two (by omega)
  rw [zpow_add₀ two_ne_zero, zpow_one, ← hxi] at h1
  have := xiTarget_lt_two_mul_xi hp
  linarith

/-- The closed form `g / (1024 K √(d J_b)) = ε / (2^24 T³ d^{3/2} J_b^{3/2})`. -/
theorem xiTarget_eq :
    p.xiTarget = p.ε / (2 ^ 24 * p.T ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) *
      (p.Jb : ℝ) ^ ((3 : ℝ) / 2)) := by
  have hd : (0 : ℝ) ≤ p.d := by have := d_ge_one hp; linarith
  have hJ : (0 : ℝ) ≤ p.Jb := by have := Jb_ge_real (p := p); linarith
  have hT := T_pos hp
  have hsd : 0 < √(p.d : ℝ) := Real.sqrt_pos.mpr (by have := d_ge_one hp; linarith)
  have hsJ : 0 < √(p.Jb : ℝ) := Real.sqrt_pos.mpr (by have := Jb_ge_real (p := p); linarith)
  have hd1 : (0 : ℝ) < p.d := by have := d_ge_one hp; linarith
  have hJ1 : (0 : ℝ) < p.Jb := by have := Jb_ge_real (p := p); linarith
  rw [xiTarget, g, K_cast, rpow_three_halves hd, rpow_three_halves hJ, Real.sqrt_mul hd]
  field_simp
  ring

/-- `eq:explicit-gls-tolerance`:
`ε / (2^25 T³ d^{3/2} J_b^{3/2}) < ξ ≤ ε / (2^24 T³ d^{3/2} J_b^{3/2})`. -/
theorem xi_tolerance :
    p.ε / (2 ^ 25 * p.T ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) * (p.Jb : ℝ) ^ ((3 : ℝ) / 2)) < p.xi ∧
      p.xi ≤ p.ε / (2 ^ 24 * p.T ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) *
        (p.Jb : ℝ) ^ ((3 : ℝ) / 2)) := by
  have h1 := xi_le_xiTarget hp
  have h2 := xiTarget_lt_two_mul_xi hp
  rw [xiTarget_eq hp] at h1 h2
  refine ⟨?_, h1⟩
  have he : p.ε / (2 ^ 25 * p.T ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) * (p.Jb : ℝ) ^ ((3 : ℝ) / 2)) =
      p.ε / (2 ^ 24 * p.T ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) * (p.Jb : ℝ) ^ ((3 : ℝ) / 2)) / 2 := by
    rw [div_div]; ring_nf
  rw [he]
  linarith

theorem xi_le_g : p.xi ≤ p.g := (xi_le_xiTarget hp).trans (xiTarget_le_g hp)

/-- `24 K ξ ≤ (3/8) e₀ ≤ e₀` for `e₀ = g / (16 √(d J_b))` (explicit witness bound). -/
theorem residual_le_e0 : 24 * p.K * p.xi ≤ 3 / 8 * p.e0 ∧ 3 / 8 * p.e0 ≤ p.e0 := by
  have hK := K_pos hp
  have hs : 0 < √(p.d * p.Jb : ℝ) := Real.sqrt_pos.mpr (by have := dJb_ge_one hp; linarith)
  have he0 : 0 ≤ p.e0 := by have := g_pos hp; unfold e0; positivity
  refine ⟨?_, by linarith⟩
  calc 24 * p.K * p.xi ≤ 24 * p.K * p.xiTarget := by
        gcongr; exact xi_le_xiTarget hp
    _ = 3 / 8 * p.e0 := by
        rw [xiTarget, e0]; field_simp; ring

end Xi

/-! ### Explicit success and accuracy margins -/

section Margins

variable (hp : p.Valid)
include hp

theorem jbArg_ge_one : 1 ≤ 2 * p.T * p.d * p.alpha / (p.ε * p.δ) := by
  rw [one_le_div (eps_delta_pos hp), alpha_cast]
  have := T_ge_real hp; have := d_ge_one hp; have := L_ge_one hp; have := eps_delta_lt hp
  have h : (2 : ℝ) * 32 * 1 * (1 * 1 + 1) ≤ 2 * p.T * p.d * (p.d * p.L + 1) := by gcongr
  linarith

omit hp in
theorem Jb_ge_logb : logb 2 (2 * p.T * p.d * p.alpha / (p.ε * p.δ)) + 64 ≤ p.Jb := by
  rw [Jb]; push_cast
  have := Nat.le_ceil (logb 2 (2 * p.T * p.d * p.alpha / (p.ε * p.δ)))
  linarith

/-- "Explicit success and accuracy margins": `K ≥ 18 log (32/δ)` follows from
`eq:explicit-gls-parameters`. -/
theorem K_ge_log : 18 * log (32 / p.δ) ≤ p.K := by
  set X := 2 * p.T * p.d * p.alpha / (p.ε * p.δ) with hX
  have hX1 : 1 ≤ X := jbArg_ge_one hp
  have hδ := hp.δ_pos
  have h32 : 1 ≤ 32 / p.δ := by rw [one_le_div hδ]; linarith [hp.δ_lt]
  have hY : 1 ≤ 2 * p.T * p.d * p.alpha / p.ε := by
    have h1 : 1 ≤ X * p.δ := by
      rw [hX, div_mul_eq_mul_div, mul_comm p.ε p.δ, ← div_div, mul_div_assoc,
        div_self hδ.ne', mul_one, one_le_div hp.ε_pos, alpha_cast]
      have := T_ge_real hp; have := d_ge_one hp; have := L_ge_one hp
      have h : (2 : ℝ) * 32 * 1 * (1 * 1 + 1) ≤ 2 * p.T * p.d * (p.d * p.L + 1) := by gcongr
      linarith [hp.ε_lt]
    have h2 : X * p.δ = 2 * p.T * p.d * p.alpha / p.ε := by
      rw [hX]; field_simp
    linarith
  have hle : 32 / p.δ ≤ 32 * X := by
    have h2 : X = 2 * p.T * p.d * p.alpha / p.ε / p.δ := by rw [hX, div_div]
    rw [h2, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hlogb : logb 2 (32 * X) = 5 + logb 2 X := by
    rw [Real.logb_mul (by norm_num) (by linarith), show (32 : ℝ) = 2 ^ 5 by norm_num,
      logb_two_pow]
    norm_num
  have h1 : log (32 / p.δ) ≤ logb 2 (32 / p.δ) := log_le_logb_two h32
  have h2 : logb 2 (32 / p.δ) ≤ logb 2 (32 * X) :=
    Real.logb_le_logb_of_le one_lt_two (by linarith) hle
  have h3 := Jb_ge_logb (p := p)
  have h4 : 18 * (p.Jb : ℝ) ≤ p.K := by
    rw [K_cast]
    have := T_ge_real hp; have := d_ge_one hp; have := Jb_ge_real (p := p)
    have h5 : (18 : ℝ) ≤ 512 * p.T * p.d := by nlinarith
    nlinarith
  linarith

/-- "Explicit success and accuracy margins": `e^{-K/18} ≤ δ/32`. -/
theorem exp_neg_K_le : exp (-(p.K : ℝ) / 18) ≤ p.δ / 32 := by
  have h := K_ge_log hp
  have h32 : 0 < 32 / p.δ := by have := hp.δ_pos; positivity
  calc exp (-(p.K : ℝ) / 18) ≤ exp (-log (32 / p.δ)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = p.δ / 32 := by rw [Real.exp_neg, Real.exp_log h32, inv_div]

theorem nArg_gt_one : 1 < 32 * p.K * p.T / p.δ := by
  rw [one_lt_div hp.δ_pos]
  have := K_ge_one hp; have := T_ge_real hp
  have : (32 : ℝ) * 1 * 32 ≤ 32 * p.K * p.T := by gcongr
  linarith [hp.δ_lt]

theorem g_inv_ge_two : 2 ≤ p.g⁻¹ := by
  rw [g_inv_eq, le_div_iff₀ hp.ε_pos]
  have := T_ge_real hp; have := hp.ε_lt
  nlinarith

/-- "Explicit success and accuracy margins": `n ≥ 2`. -/
theorem two_le_n : 2 ≤ p.n := by
  have h1 : (1 : ℝ) ≤ ⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊ := by
    exact_mod_cast one_le_ceil_logb (nArg_gt_one hp)
  have h2 := g_inv_ge_two hp
  have h3 : p.g⁻¹ * ⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊ ≤ p.n := Nat.le_ceil _
  have h4 : (2 : ℝ) ≤ p.n := by nlinarith
  exact_mod_cast h4

/-- `sec:gls-validation-arithmetic`: `n ≥ g⁻¹ log (32TK/δ)` (natural logarithm). -/
theorem n_ge_log : p.g⁻¹ * log (32 * p.T * p.K / p.δ) ≤ p.n := by
  have hc : (32 : ℝ) * p.T * p.K = 32 * p.K * p.T := by ring
  have h1 := log_le_logb_two (nArg_gt_one hp).le
  have h2 : logb 2 (32 * p.K * p.T / p.δ) ≤ ⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊ := Nat.le_ceil _
  have h3 : p.g⁻¹ * ⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊ ≤ p.n := Nat.le_ceil _
  have hg : 0 ≤ p.g⁻¹ := inv_nonneg.mpr (g_pos hp).le
  rw [hc]
  calc p.g⁻¹ * log (32 * p.K * p.T / p.δ)
      ≤ p.g⁻¹ * ⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊ := by gcongr; linarith
    _ ≤ p.n := h3

/-- `sec:gls-validation-arithmetic`: `(1 - g)^n ≤ δ/(32TK)`; a discrepancy of probability `> g` is
missed with probability at most `δ/(32TK)`. -/
theorem one_sub_g_pow_le : (1 - p.g) ^ p.n ≤ p.δ / (32 * p.T * p.K) := by
  have hg := g_pos hp
  have h1 := n_ge_log hp
  have hpos : 0 < 32 * p.T * p.K / p.δ := by
    have := K_pos hp; have := T_pos hp; have := hp.δ_pos; positivity
  have h2 : log (32 * p.T * p.K / p.δ) ≤ p.g * p.n := by
    rw [← inv_mul_le_iff₀ hg]; exact h1
  calc (1 - p.g) ^ p.n ≤ exp (-p.g) ^ p.n :=
        pow_le_pow_left₀ (by linarith [g_lt_one hp]) (by linarith [Real.add_one_le_exp (-p.g)]) _
    _ = exp (-(p.g * p.n)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ exp (-log (32 * p.T * p.K / p.δ)) := Real.exp_le_exp.mpr (by linarith)
    _ = p.δ / (32 * p.T * p.K) := by rw [Real.exp_neg, Real.exp_log hpos, inv_div]

/-- "Explicit success and accuracy margins": the union bound over `T` cuts and `K` epochs,
`TK ⋅ δ/(32TK) = δ/32`. -/
theorem union_over_cuts_epochs : (p.T * p.K : ℝ) * (p.δ / (32 * p.T * p.K)) = p.δ / 32 := by
  have := K_pos hp; have := T_pos hp
  field_simp

/-- "Explicit success and accuracy margins": the spanner union bound over the at most `KT` calls,
`KT ⋅ δ_s = δ/32`. -/
theorem spanner_union : (p.K * p.T : ℝ) * p.deltaS = p.δ / 32 := by
  have := K_pos hp; have := T_pos hp
  rw [deltaS]; field_simp

/-- "Explicit success and accuracy margins", the arithmetic: `64 T d J_b = K/8 < K/3`. That all
cuts together receive fewer than `64 T d J_b` witnesses is `Input.witnesses_total_lt`
(`Envelope/Witness.lean`), from the witness count of `Witness.witness_count_lt`. -/
theorem witnesses_lt_feasible :
    (64 * p.T * p.d * p.Jb : ℝ) = p.K / 8 ∧ (p.K : ℝ) / 8 < p.K / 3 := by
  have := K_pos hp
  exact ⟨by rw [K_cast]; ring, by linarith⟩

/-- "Explicit success and accuracy margins": the accuracy ledger
`2T²g + T²η + Tξ + ε/8 ≤ ε/16 + ε/6 + ε/(32T) + ε/8 ≤ 37ε/96 < ε/2`. -/
theorem accuracy_ledger :
    2 * p.T ^ 2 * p.g + p.T ^ 2 * p.eta + p.T * p.xi + p.ε / 8 ≤
        p.ε / 16 + p.ε / 6 + p.ε / (32 * p.T) + p.ε / 8 ∧
      p.ε / 16 + p.ε / 6 + p.ε / (32 * p.T) + p.ε / 8 ≤ 37 / 96 * p.ε ∧
      37 / 96 * p.ε < p.ε / 2 := by
  have hT := T_ge_real hp
  have hT0 := T_pos hp
  have hε := hp.ε_pos
  have hn : (2 : ℝ) ≤ p.n := by exact_mod_cast two_le_n hp
  have h1 : 2 * p.T ^ 2 * p.g = p.ε / 16 := by rw [g]; field_simp; ring
  have h2 : (p.T : ℝ) ^ 2 * p.eta ≤ p.ε / 6 := by
    have he : (p.T : ℝ) ^ 2 * p.eta = p.ε / (3 * p.n) := by
      rw [eta]; field_simp
    rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h3 : (p.T : ℝ) * p.xi ≤ p.ε / (32 * p.T) := by
    calc (p.T : ℝ) * p.xi ≤ p.T * p.g := by gcongr; exact xi_le_g hp
      _ = p.ε / (32 * p.T) := by rw [g]; field_simp
  have h4 : p.ε / (32 * p.T) ≤ p.ε / 32 := by
    apply div_le_div_of_nonneg_left hε.le (by norm_num); linarith
  refine ⟨by linarith, by linarith, by linarith⟩

/-- "Explicit success and accuracy margins": three failure events of probability at most `δ/32`
each have total probability less than `δ/4`. -/
theorem failure_budget {f₁ f₂ f₃ : ℝ} (h₁ : f₁ ≤ p.δ / 32) (h₂ : f₂ ≤ p.δ / 32)
    (h₃ : f₃ ≤ p.δ / 32) : f₁ + f₂ + f₃ < p.δ / 4 := by
  have := hp.δ_pos; linarith

/-- `sec:gls-validation-arithmetic`: `η T² n = ε/3`, so an epoch is feasible with conditional
probability at least `1 - ηT²n ≥ 1/2`. -/
theorem eta_T_sq_n : p.eta * p.T ^ 2 * p.n = p.ε / 3 ∧ 1 / 2 ≤ 1 - p.eta * p.T ^ 2 * p.n := by
  have hn : (0 : ℝ) < p.n := by have := two_le_n hp; positivity
  have := T_pos hp
  have h : p.eta * p.T ^ 2 * p.n = p.ε / 3 := by rw [eta]; field_simp
  exact ⟨h, by rw [h]; linarith [hp.ε_lt]⟩

end Margins

end Input

/-! ### Validation-section ledger and the Hoeffding exponent -/

theorem sum_range_cast_le (T : ℕ) : ∑ t ∈ range T, (t : ℝ) ≤ (T : ℝ) ^ 2 / 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ]; push_cast
    nlinarith

/-- `sec:gls-validation-arithmetic`: summing the next-token errors `2tg + ξ + ηt` over the
hybrids `t = 0, …, T-1` gives at most `T²g + Tξ + ηT²/2`. -/
theorem sum_next_token_errors (T : ℕ) {g ξ η : ℝ} (hg : 0 ≤ g) (hη : 0 ≤ η) :
    ∑ t ∈ range T, (2 * t * g + ξ + η * t) ≤ T ^ 2 * g + T * ξ + η * T ^ 2 / 2 := by
  have hS := sum_range_cast_le T
  rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, ← sum_mul, ← mul_sum,
    ← mul_sum, nsmul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hS hg, mul_le_mul_of_nonneg_left hS hη]

namespace Input

variable {p : Input}

/-- `sec:gls-validation-arithmetic`: the summed error `T²g + Tξ + ηT²/2 + ε/8` of the validation
section is at most the lemma's ledger `2T²g + T²η + Tξ + ε/8`, hence at most `37ε/96`. -/
theorem validation_ledger (hp : p.Valid) :
    ∑ t ∈ range p.T, (2 * t * p.g + p.xi + p.eta * t) + p.ε / 8 ≤
        p.T ^ 2 * p.g + p.T * p.xi + p.eta * p.T ^ 2 / 2 + p.ε / 8 ∧
      p.T ^ 2 * p.g + p.T * p.xi + p.eta * p.T ^ 2 / 2 + p.ε / 8 ≤
        2 * p.T ^ 2 * p.g + p.T ^ 2 * p.eta + p.T * p.xi + p.ε / 8 ∧
      2 * p.T ^ 2 * p.g + p.T ^ 2 * p.eta + p.T * p.xi + p.ε / 8 ≤ 37 / 96 * p.ε := by
  have hg := (g_pos hp).le
  have hη : 0 ≤ p.eta := by
    unfold eta; have := hp.ε_pos; positivity
  have h1 := sum_next_token_errors p.T (ξ := p.xi) hg hη
  have hT2 : (0 : ℝ) ≤ p.T ^ 2 := by positivity
  have h3 := accuracy_ledger hp
  refine ⟨by linarith, ?_, by linarith [h3.1, h3.2.1]⟩
  nlinarith [mul_nonneg hT2 hg, mul_nonneg hT2 hη]

end Input

/-- `sec:gls-validation-arithmetic`: the conditional moment step of the adapted Hoeffding bound.
If `I ∈ {0,1}` equals one with probability `q ≥ 1/2`, then for `a ≥ 0`,
`E e^{-a(I - 1/2)} = q e^{-a/2} + (1-q) e^{a/2} ≤ cosh (a/2) ≤ e^{a²/8}`. -/
theorem hoeffding_step {q a : ℝ} (hq : 1 / 2 ≤ q) (ha : 0 ≤ a) :
    q * exp (-(a / 2)) + (1 - q) * exp (a / 2) ≤ cosh (a / 2) ∧
      cosh (a / 2) ≤ exp (a ^ 2 / 8) := by
  constructor
  · rw [Real.cosh_eq]
    have : exp (-(a / 2)) ≤ exp (a / 2) := Real.exp_le_exp.mpr (by linarith)
    nlinarith
  · have := Real.cosh_le_exp_half_sq (a / 2)
    calc cosh (a / 2) ≤ exp ((a / 2) ^ 2 / 2) := this
      _ = exp (a ^ 2 / 8) := by ring_nf

/-- `sec:gls-validation-arithmetic`: with `a = 2/3`, multiplying the `K` moment bounds and the
Markov factor `e^{-aK/6}` gives `e^{-K/18}`. -/
theorem hoeffding_exponent (K : ℝ) :
    exp (K * ((2 / 3 : ℝ) ^ 2 / 8)) * exp (-(2 / 3) * K / 6) = exp (-K / 18) := by
  rw [← Real.exp_add]; ring_nf

/-! ### A numerical polynomial envelope -/

/-- `c V^a ≤ V^{a+b}` when `c ≤ 256^b` and `V ≥ 256`. -/
theorem const_mul_pow_le {V c : ℝ} (hV : 256 ≤ V) {a b : ℕ} (hc : c ≤ 256 ^ b) :
    c * V ^ a ≤ V ^ (a + b) := by
  have h1 : (256 : ℝ) ^ b ≤ V ^ b := pow_le_pow_left₀ (by norm_num) hV b
  have h2 : 0 ≤ V ^ a := pow_nonneg (by linarith) a
  calc c * V ^ a ≤ 256 ^ b * V ^ a := by gcongr
    _ ≤ V ^ b * V ^ a := by gcongr
    _ = V ^ (a + b) := by ring

namespace Input

variable {p : Input}

section Numerical

variable (hp : p.Valid)
include hp

theorem V_mul : p.V * (p.ε * p.δ) = 2 * p.T * p.d * p.L :=
  div_mul_cancel₀ _ (eps_delta_pos hp).ne'

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `V > 256`. -/
theorem V_gt : 256 < p.V := by
  rw [V, lt_div_iff₀ (eps_delta_pos hp)]
  have := eps_delta_lt hp
  have h : (64 : ℝ) ≤ 2 * p.T * p.d * p.L := by
    have := T_ge_real hp; have := d_ge_one hp; have := L_ge_one hp
    calc (64 : ℝ) = 2 * 32 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  linarith

theorem V_pos : 0 < p.V := by have := V_gt hp; linarith

theorem one_le_V : 1 ≤ p.V := by have := V_gt hp; linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `α ≤ 2dL`. -/
theorem alpha_le : (p.alpha : ℝ) ≤ 2 * p.d * p.L := by
  rw [alpha_cast]
  have := d_ge_one hp; have := L_ge_one hp
  nlinarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `Td ≤ V/8`. -/
theorem Td_le : (p.T : ℝ) * p.d ≤ p.V / 8 := by
  have hTd : 0 ≤ (p.T : ℝ) * p.d := by positivity
  rw [le_div_iff₀ (by norm_num), V, le_div_iff₀ (eps_delta_pos hp)]
  have h1 := eps_delta_lt hp; have hL := L_ge_one hp
  nlinarith [mul_le_mul_of_nonneg_left h1.le hTd, mul_le_mul_of_nonneg_left hL hTd]

theorem T_le : (p.T : ℝ) ≤ p.V / 8 := by
  have := Td_le hp; have := d_ge_one hp; have := T_pos hp
  nlinarith

theorem d_le : (p.d : ℝ) ≤ p.V / 256 := by
  have := Td_le hp; have := d_ge_one hp; have := T_ge_real hp
  nlinarith

theorem inv_eps_le : p.ε⁻¹ ≤ p.V / 128 := by
  have hε := hp.ε_pos
  rw [inv_eq_one_div, div_le_div_iff₀ hε (by norm_num)]
  have h1 := V_mul hp
  have h2 : (64 : ℝ) ≤ 2 * p.T * p.d * p.L := by
    have := T_ge_real hp; have := d_ge_one hp; have := L_ge_one hp
    calc (64 : ℝ) = 2 * 32 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have h3 : 0 < p.V * p.ε := mul_pos (V_pos hp) hε
  nlinarith [mul_lt_mul_of_pos_left hp.δ_lt h3]

theorem inv_delta_le : p.δ⁻¹ ≤ p.V / 128 := by
  have hδ := hp.δ_pos
  rw [inv_eq_one_div, div_le_div_iff₀ hδ (by norm_num)]
  have h1 := V_mul hp
  have h2 : (64 : ℝ) ≤ 2 * p.T * p.d * p.L := by
    have := T_ge_real hp; have := d_ge_one hp; have := L_ge_one hp
    calc (64 : ℝ) = 2 * 32 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have h3 : 0 < p.V * p.δ := mul_pos (V_pos hp) hδ
  nlinarith [mul_lt_mul_of_pos_left hp.ε_lt h3]

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `4T/ε ≤ V`. -/
theorem four_T_div_eps_le : 4 * p.T / p.ε ≤ p.V := by
  have hε := hp.ε_pos
  rw [div_le_iff₀ hε]
  have h1 := V_mul hp
  have h2 : 2 * (p.T : ℝ) ≤ 2 * p.T * p.d * p.L := by
    have := T_pos hp; have := d_ge_one hp; have := L_ge_one hp
    have : (1 : ℝ) ≤ p.d * p.L := by nlinarith
    nlinarith
  have h3 : 0 < p.V * p.ε := mul_pos (V_pos hp) hε
  nlinarith [mul_lt_mul_of_pos_left hp.δ_lt h3]

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `log₂ V ≤ V/32`. -/
theorem logV_le : logb 2 p.V ≤ p.V / 32 := logb_le_div_32 (V_gt hp).le

theorem logV_gt : 8 < logb 2 p.V := by
  have h := Real.logb_lt_logb one_lt_two (by norm_num) (V_gt hp)
  rwa [show (256 : ℝ) = 2 ^ 8 by norm_num, logb_two_pow] at h

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `J_b ≤ 2 log₂ V + 65 ≤ V`. -/
theorem Jb_le : (p.Jb : ℝ) ≤ 2 * logb 2 p.V + 65 ∧ 2 * logb 2 p.V + 65 ≤ p.V := by
  have hX : 2 * p.T * p.d * p.alpha / (p.ε * p.δ) ≤ 2 ^ 0 * p.V ^ 2 := by
    calc 2 * p.T * p.d * p.alpha / (p.ε * p.δ)
        ≤ 2 * p.T * p.d * (2 * p.d * p.L) / (p.ε * p.δ) := by
          apply div_le_div_of_nonneg_right _ (eps_delta_pos hp).le
          gcongr; exact alpha_le hp
      _ = 2 * p.d * p.V := by rw [V]; ring
      _ ≤ 2 ^ 0 * p.V ^ 2 := by have := d_le hp; have := V_gt hp; nlinarith
  have h := ceil_logb_lt (jbArg_ge_one hp) (V_pos hp) hX
  norm_num at h
  rw [Jb]; push_cast
  have := logV_le hp; have := V_gt hp
  constructor <;> linarith

theorem Jb_le_V : (p.Jb : ℝ) ≤ p.V := (Jb_le hp).1.trans (Jb_le hp).2

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `K ≤ 64 V² ≤ V³`. -/
theorem K_le : (p.K : ℝ) ≤ 64 * p.V ^ 2 ∧ 64 * p.V ^ 2 ≤ p.V ^ 3 := by
  have hJ := Jb_le_V hp
  have hV := V_gt hp
  constructor
  · rw [K_cast]
    calc 512 * (p.T : ℝ) * p.d * p.Jb = 512 * (p.T * p.d) * p.Jb := by ring
      _ ≤ 512 * (p.V / 8) * p.V := by gcongr; exact Td_le hp
      _ = 64 * p.V ^ 2 := by ring
  · nlinarith [mul_nonneg (sq_nonneg p.V) (by linarith : (0 : ℝ) ≤ p.V - 64)]

theorem K_le_V3 : (p.K : ℝ) ≤ p.V ^ 3 := (K_le hp).1.trans (K_le hp).2

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `V² g = d²L²/(8εδ²)`. -/
theorem V_sq_mul_g : p.V ^ 2 * p.g = p.d ^ 2 * p.L ^ 2 / (8 * p.ε * p.δ ^ 2) := by
  have := hp.ε_pos; have := hp.δ_pos; have := T_pos hp
  rw [V, g]; field_simp; ring

theorem one_lt_V_sq_mul_g : 1 < p.V ^ 2 * p.g := by
  have hε := hp.ε_pos; have hδ := hp.δ_pos
  rw [V_sq_mul_g hp, lt_div_iff₀ (by positivity), one_mul]
  have h1 : p.δ ^ 2 < 1 / 4 := by nlinarith [hp.δ_lt]
  have h2 : p.ε * p.δ ^ 2 < 1 / 8 := by nlinarith [hp.ε_lt]
  have h3 : (1 : ℝ) ≤ (p.d : ℝ) ^ 2 * p.L ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (d_ge_one hp)) (one_le_pow₀ (L_ge_one hp))
  linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `g⁻¹ ≤ V²`. -/
theorem g_inv_le : p.g⁻¹ ≤ p.V ^ 2 := by
  have hg := g_pos hp
  have h := one_lt_V_sq_mul_g hp
  calc p.g⁻¹ = p.g⁻¹ * 1 := by ring
    _ ≤ p.g⁻¹ * (p.V ^ 2 * p.g) := by gcongr
    _ = p.V ^ 2 := by field_simp

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `32KT/δ ≤ 2V⁴`. -/
theorem nArg_le : 32 * p.K * p.T / p.δ ≤ 2 * p.V ^ 4 := by
  have hK := (K_le hp).1; have hT := T_le hp; have hδ := inv_delta_le hp
  have hδ0 : 0 ≤ p.δ⁻¹ := inv_nonneg.mpr hp.δ_pos.le
  rw [div_eq_mul_inv]
  have hV0 := (V_pos hp).le
  calc 32 * (p.K : ℝ) * p.T * p.δ⁻¹ ≤ 32 * (64 * p.V ^ 2) * (p.V / 8) * (p.V / 128) := by
        gcongr
    _ = 2 * p.V ^ 4 := by ring

/-- `lem:explicit-gls-token-envelope` (numerical envelope): the logarithmic ceiling in `n` is at
most `6 log₂ V + 1 ≤ V`. -/
theorem nlog_le : (⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊ : ℝ) ≤ 6 * logb 2 p.V + 1 ∧
    6 * logb 2 p.V + 1 ≤ p.V := by
  have h := ceil_logb_lt (a := 4) (b := 1) (nArg_gt_one hp).le (V_pos hp) (by
    rw [pow_one]; exact nArg_le hp)
  have := logV_gt hp; have := logV_le hp; have := V_gt hp
  norm_num at h
  constructor <;> linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `n ≤ V⁴`. -/
theorem n_le : (p.n : ℝ) ≤ p.V ^ 4 := by
  have hc := nlog_le hp
  have hg := g_inv_le hp
  have hg0 : 0 ≤ p.g⁻¹ := inv_nonneg.mpr (g_pos hp).le
  have hV := V_gt hp
  have h0 : 0 ≤ p.g⁻¹ * ⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊ := by positivity
  have h1 := Nat.ceil_lt_add_one h0
  have h2 : p.g⁻¹ * ⌈logb 2 (32 * p.K * p.T / p.δ)⌉₊ ≤ p.V ^ 2 * p.V := by
    gcongr; linarith [hc.1, hc.2]
  have h3 : p.V ^ 2 * p.V + 1 ≤ p.V ^ 4 := by
    have : 2 * p.V ^ 3 ≤ p.V ^ 4 := const_mul_pow_le (a := 3) (b := 1) hV.le (by norm_num)
    have : (1 : ℝ) ≤ p.V ^ 3 := one_le_pow₀ (one_le_V hp)
    nlinarith
  unfold n
  linarith

theorem n_pos : (0 : ℝ) < p.n := by have := two_le_n hp; positivity

theorem eta_pos : 0 < p.eta := by
  have := n_pos hp; have := T_pos hp; have := hp.ε_pos
  unfold eta; positivity

theorem eta_lt_one : p.eta < 1 := by
  have := n_pos hp; have hT := T_ge_real hp; have := hp.ε_lt
  have hn : (2 : ℝ) ≤ p.n := by exact_mod_cast two_le_n hp
  unfold eta
  rw [div_lt_one (by positivity)]
  nlinarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): the identity `η⁻¹ = (3/32) g⁻¹ n`. -/
theorem eta_inv_eq : p.eta⁻¹ = 3 / 32 * p.g⁻¹ * p.n := by
  have := hp.ε_pos; have := T_pos hp
  rw [eta, g, inv_div, inv_div]; field_simp

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `η⁻¹ ≤ V⁶`. -/
theorem eta_inv_le : p.eta⁻¹ ≤ p.V ^ 6 := by
  rw [eta_inv_eq hp]
  have hg := g_inv_le hp; have hn := n_le hp
  have hg0 : 0 ≤ p.g⁻¹ := inv_nonneg.mpr (g_pos hp).le
  have hV := V_gt hp
  calc 3 / 32 * p.g⁻¹ * p.n ≤ 3 / 32 * p.V ^ 2 * p.V ^ 4 := by gcongr
    _ ≤ p.V ^ 6 := by
        have : (0 : ℝ) ≤ p.V ^ 6 := by positivity
        nlinarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `6K ≤ V⁴`. -/
theorem six_K_le : 6 * (p.K : ℝ) ≤ p.V ^ 4 := by
  have h := (K_le hp).1
  have : 384 * p.V ^ 2 ≤ p.V ^ 4 := const_mul_pow_le (a := 2) (b := 2) (V_gt hp).le (by norm_num)
  linarith

theorem deltaS_pos : 0 < p.deltaS := by
  have := K_pos hp; have := T_pos hp; have := hp.δ_pos
  unfold deltaS; positivity

omit hp in
theorem deltaS_inv_eq : p.deltaS⁻¹ = 32 * p.K * p.T / p.δ := by rw [deltaS, inv_div]

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `δ_s⁻¹ ≤ V⁶`. -/
theorem deltaS_inv_le : p.deltaS⁻¹ ≤ p.V ^ 6 := by
  rw [deltaS_inv_eq]
  have := nArg_le hp
  have : 2 * p.V ^ 4 ≤ p.V ^ 6 := const_mul_pow_le (a := 4) (b := 2) (V_gt hp).le (by norm_num)
  linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): both logarithmic ceilings in `H_⋆` are
at most `10 log₂ V + 2 ≤ V`. -/
theorem Hstar_le : (p.Hstar : ℝ) ≤ 10 * logb 2 p.V + 2 ∧ 10 * logb 2 p.V + 2 ≤ p.V := by
  have hV := V_gt hp
  have hl := logV_gt hp
  have hl2 := logV_le hp
  have hK := K_ge_one hp
  have hη := eta_pos hp
  have hη1 := eta_lt_one hp
  have hηi : 1 ≤ p.eta⁻¹ := one_le_inv_iff₀.mpr ⟨hη, hη1.le⟩
  have h1 : (⌈logb 2 (12 * p.K / p.eta)⌉₊ : ℝ) < 8 * logb 2 p.V + 10 + 1 := by
    have hX1 : 1 ≤ 12 * (p.K : ℝ) / p.eta := by
      rw [div_eq_mul_inv]; nlinarith
    have hX : 12 * (p.K : ℝ) / p.eta ≤ 2 ^ 10 * p.V ^ 8 := by
      rw [div_eq_mul_inv]
      have := (K_le hp).1; have := eta_inv_le hp
      calc 12 * (p.K : ℝ) * p.eta⁻¹ ≤ 12 * (64 * p.V ^ 2) * p.V ^ 6 := by gcongr
        _ ≤ 2 ^ 10 * p.V ^ 8 := by
            have : (0 : ℝ) ≤ p.V ^ 8 := by positivity
            nlinarith
    have := ceil_logb_lt hX1 (V_pos hp) hX
    push_cast at this; linarith
  have h2 : (⌈logb 2 ((6 * p.K + 1) / p.deltaS)⌉₊ : ℝ) < 6 * logb 2 p.V + 10 + 1 := by
    have hs := deltaS_pos hp
    have hsi : 1 ≤ p.deltaS⁻¹ := by
      rw [deltaS_inv_eq, one_le_div hp.δ_pos]
      have := T_ge_real hp
      have : (32 : ℝ) * 1 * 32 ≤ 32 * p.K * p.T := by gcongr
      linarith [hp.δ_lt]
    have hX1 : 1 ≤ (6 * (p.K : ℝ) + 1) / p.deltaS := by
      rw [div_eq_mul_inv]; nlinarith
    have hX : (6 * (p.K : ℝ) + 1) / p.deltaS ≤ 2 ^ 10 * p.V ^ 6 := by
      rw [div_eq_mul_inv, deltaS_inv_eq]
      have hK6 : 6 * (p.K : ℝ) + 1 ≤ 385 * p.V ^ 2 := by
        have := (K_le hp).1; have : (1 : ℝ) ≤ p.V ^ 2 := one_le_pow₀ (one_le_V hp)
        linarith
      have := nArg_le hp
      have h0 : 0 ≤ 32 * (p.K : ℝ) * p.T / p.δ := by
        have := hp.δ_pos; positivity
      calc (6 * (p.K : ℝ) + 1) * (32 * p.K * p.T / p.δ) ≤ (385 * p.V ^ 2) * (2 * p.V ^ 4) := by
            gcongr
        _ ≤ 2 ^ 10 * p.V ^ 6 := by
            have : (0 : ℝ) ≤ p.V ^ 6 := by positivity
            nlinarith
    have := ceil_logb_lt hX1 (V_pos hp) hX
    push_cast at this; linarith
  have hmax : (p.Hstar : ℝ) = max (⌈logb 2 (12 * p.K / p.eta)⌉₊ : ℝ)
      (⌈logb 2 ((6 * p.K + 1) / p.deltaS)⌉₊ : ℝ) := by
    rw [Hstar]; push_cast; rfl
  rw [hmax]
  refine ⟨max_le (by linarith) (by linarith), by linarith⟩

theorem Hstar_le_V : (p.Hstar : ℝ) ≤ p.V := (Hstar_le hp).1.trans (Hstar_le hp).2

/-- `eq:explicit-gls-request-caps`: `Q ≤ V^19 + V^14 + V^7 + V^5 ≤ V^20`. -/
theorem Q_le : (p.Q : ℝ) ≤ p.V ^ 19 + p.V ^ 14 + p.V ^ 7 + p.V ^ 5 ∧
    p.V ^ 19 + p.V ^ 14 + p.V ^ 7 + p.V ^ 5 ≤ p.V ^ 20 := by
  have hV := V_gt hp
  have hV1 := one_le_V hp
  have hH := Hstar_le_V hp
  have hK := K_le_V3 hp
  have hn := n_le hp
  have hη := eta_inv_le hp
  have hT : (p.T : ℝ) ≤ p.V := by have := T_le hp; linarith
  have hη0 : 0 ≤ p.eta⁻¹ := inv_nonneg.mpr (eta_pos hp).le
  have h1 : (⌈900 * p.Hstar * p.K ^ 3 / p.eta⌉₊ : ℝ) ≤ p.V ^ 19 := by
    have h0 : 0 ≤ 900 * (p.Hstar : ℝ) * p.K ^ 3 / p.eta :=
      div_nonneg (by positivity) (eta_pos hp).le
    have hc := Nat.ceil_lt_add_one h0
    have hb : 900 * (p.Hstar : ℝ) * p.K ^ 3 / p.eta ≤ 900 * p.V ^ 16 := by
      rw [div_eq_mul_inv]
      calc 900 * (p.Hstar : ℝ) * p.K ^ 3 * p.eta⁻¹ ≤ 900 * p.V * (p.V ^ 3) ^ 3 * p.V ^ 6 := by
            gcongr
        _ = 900 * p.V ^ 16 := by ring
    have h16 : (1 : ℝ) ≤ p.V ^ 16 := one_le_pow₀ hV1
    have : 901 * p.V ^ 16 ≤ p.V ^ 19 := const_mul_pow_le (a := 16) (b := 3) hV.le (by norm_num)
    linarith
  have h2 : 24 * (p.n : ℝ) * p.T ^ 3 * p.K ^ 2 ≤ p.V ^ 14 := by
    calc 24 * (p.n : ℝ) * p.T ^ 3 * p.K ^ 2 ≤ 24 * p.V ^ 4 * p.V ^ 3 * (p.V ^ 3) ^ 2 := by gcongr
      _ = 24 * p.V ^ 13 := by ring
      _ ≤ p.V ^ 14 := const_mul_pow_le (a := 13) (b := 1) hV.le (by norm_num)
  have h3 : (p.K : ℝ) * p.n ≤ p.V ^ 7 := by
    calc (p.K : ℝ) * p.n ≤ p.V ^ 3 * p.V ^ 4 := by gcongr
      _ = p.V ^ 7 := by ring
  have h4 : 18 * (p.T : ℝ) * p.K ≤ p.V ^ 5 := by
    calc 18 * (p.T : ℝ) * p.K ≤ 18 * p.V * p.V ^ 3 := by gcongr
      _ = 18 * p.V ^ 4 := by ring
      _ ≤ p.V ^ 5 := const_mul_pow_le (a := 4) (b := 1) hV.le (by norm_num)
  constructor
  · rw [Q]; push_cast; linarith
  · have e1 : p.V ^ 14 ≤ p.V ^ 19 := pow_le_pow_right₀ hV1 (by norm_num)
    have e2 : p.V ^ 7 ≤ p.V ^ 19 := pow_le_pow_right₀ hV1 (by norm_num)
    have e3 : p.V ^ 5 ≤ p.V ^ 19 := pow_le_pow_right₀ hV1 (by norm_num)
    have : 4 * p.V ^ 19 ≤ p.V ^ 20 := const_mul_pow_le (a := 19) (b := 1) hV.le (by norm_num)
    linarith

theorem Q_le_V20 : (p.Q : ℝ) ≤ p.V ^ 20 := (Q_le hp).1.trans (Q_le hp).2

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `R_ℓ + R_s = 2Q ≤ V^22`. -/
theorem Rl_add_Rs_le : (p.Rl : ℝ) + p.Rs ≤ p.V ^ 22 := by
  have h := Q_le_V20 hp
  have : 2 * p.V ^ 20 ≤ p.V ^ 22 := const_mul_pow_le (a := 20) (b := 2) (V_gt hp).le (by norm_num)
  rw [Rl, Rs]; linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `ξ⁻¹ < 2^25 T³ d^{3/2} J_b^{3/2} / ε ≤
2^25 V^7 < V^11`. -/
theorem xi_inv_bounds :
    p.xi⁻¹ < 2 ^ 25 * p.T ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) * (p.Jb : ℝ) ^ ((3 : ℝ) / 2) / p.ε ∧
      2 ^ 25 * p.T ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) * (p.Jb : ℝ) ^ ((3 : ℝ) / 2) / p.ε ≤
        2 ^ 25 * p.V ^ 7 ∧
      2 ^ 25 * p.V ^ 7 < p.V ^ 11 := by
  have hV := V_gt hp
  have hd1 := d_ge_one hp
  have hJ1 : (1 : ℝ) ≤ p.Jb := by have := Jb_ge_real (p := p); linarith
  have hε := hp.ε_pos
  have hT := T_pos hp
  have hdr : (p.d : ℝ) ^ ((3 : ℝ) / 2) ≤ (p.d : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
  have hJr : (p.Jb : ℝ) ^ ((3 : ℝ) / 2) ≤ (p.Jb : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hJ1 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have h := (xi_tolerance hp).1
    have ha : 0 < p.ε / (2 ^ 25 * p.T ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) *
        (p.Jb : ℝ) ^ ((3 : ℝ) / 2)) := by positivity
    have := (inv_lt_inv₀ (xi_pos (p := p)) ha).mpr h
    rwa [inv_div] at this
  · have hTd := Td_le hp
    have hJ := Jb_le_V hp
    have hεi := inv_eps_le hp
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) ^ ((3 : ℝ) / 2) := by positivity
    have hJ0 : (0 : ℝ) ≤ (p.Jb : ℝ) ^ ((3 : ℝ) / 2) := by positivity
    rw [div_eq_mul_inv]
    calc 2 ^ 25 * (p.T : ℝ) ^ 3 * (p.d : ℝ) ^ ((3 : ℝ) / 2) * (p.Jb : ℝ) ^ ((3 : ℝ) / 2) * p.ε⁻¹
        ≤ 2 ^ 25 * (p.T : ℝ) ^ 3 * (p.d : ℝ) ^ 2 * (p.Jb : ℝ) ^ 2 * p.ε⁻¹ := by
          have : 0 ≤ p.ε⁻¹ := by positivity
          gcongr
      _ = 2 ^ 25 * ((p.T * p.d) ^ 2 * p.T) * (p.Jb : ℝ) ^ 2 * p.ε⁻¹ := by ring
      _ ≤ 2 ^ 25 * ((p.V / 8) ^ 2 * (p.V / 8)) * p.V ^ 2 * (p.V / 128) := by
          have : 0 ≤ p.ε⁻¹ := by positivity
          have hT8 := T_le hp
          gcongr
      _ ≤ 2 ^ 25 * p.V ^ 7 := by
          have h6 : (0 : ℝ) ≤ p.V ^ 6 := by positivity
          have : p.V ^ 6 ≤ p.V ^ 7 := pow_le_pow_right₀ (one_le_V hp) (by norm_num)
          nlinarith
  · have h7 : (0 : ℝ) < p.V ^ 7 := by positivity
    have : (2 : ℝ) ^ 25 * p.V ^ 7 < 256 ^ 4 * p.V ^ 7 := by nlinarith
    have h4 : (256 : ℝ) ^ 4 * p.V ^ 7 ≤ p.V ^ 11 :=
      const_mul_pow_le (a := 7) (b := 4) hV.le le_rfl
    linarith

theorem xi_inv_le : p.xi⁻¹ ≤ p.V ^ 11 := by
  have h := xi_inv_bounds hp
  linarith [h.1, h.2.1, h.2.2]

/-- `lem:explicit-gls-token-envelope` (numerical envelope): the smoothing floor: `ε/(32T) < γ =
τ/2`. -/
theorem gamma_gt : p.ε / (32 * p.T) < p.gamma := by
  have hε := hp.ε_pos; have hT := T_pos hp
  have hx : 1 ≤ 8 * (p.T : ℝ) / p.ε := by
    rw [one_le_div hε]; have := T_ge_real hp; linarith [hp.ε_lt]
  have h := two_pow_ceil_logb_lt hx
  have h2 : (2 : ℝ) ^ bTau p.T p.ε < 16 * p.T / p.ε := by
    unfold bTau; linarith [show 2 * (8 * (p.T : ℝ) / p.ε) = 16 * p.T / p.ε by ring]
  have h3 : (16 * (p.T : ℝ) / p.ε)⁻¹ < tauOf p.T p.ε := by
    unfold tauOf
    exact (inv_lt_inv₀ (by positivity) (by positivity)).mpr h2
  rw [inv_div] at h3
  unfold gamma
  have : p.ε / (32 * p.T) = p.ε / (16 * p.T) / 2 := by field_simp; ring
  rw [this]
  linarith

theorem gamma_pos : 0 < p.gamma := by
  have := gamma_gt hp; have := hp.ε_pos; have := T_pos hp
  have : 0 < p.ε / (32 * p.T) := by positivity
  linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `γ⁻¹ ≤ 8V ≤ V²`. -/
theorem gamma_inv_le : p.gamma⁻¹ ≤ 8 * p.V ∧ 8 * p.V ≤ p.V ^ 2 := by
  have hε := hp.ε_pos; have hT := T_pos hp
  have h1 := gamma_gt hp
  have h2 : p.gamma⁻¹ < (p.ε / (32 * p.T))⁻¹ :=
    (inv_lt_inv₀ (gamma_pos hp) (by positivity)).mpr h1
  rw [inv_div] at h2
  have h3 := four_T_div_eps_le hp
  have hV := V_gt hp
  constructor
  · have : 32 * (p.T : ℝ) / p.ε = 8 * (4 * p.T / p.ε) := by ring
    linarith
  · nlinarith

theorem Rl_ge_one : (1 : ℝ) ≤ p.Rl := by
  have h : 1 ≤ p.Rl := by
    have h1 : 1 ≤ 18 * p.T * p.K := by
      have := hp.T_ge
      have hK : 1 ≤ p.K := by exact_mod_cast K_ge_one hp
      calc 1 ≤ 18 * 32 * 1 := by norm_num
        _ ≤ 18 * p.T * p.K := by gcongr
    unfold Rl Q; omega
  exact_mod_cast h

/-- `lem:explicit-gls-token-envelope` (numerical envelope): the logarithmic ceiling in `M_est` is at
most `24 log₂ V + 1 ≤ V`. -/
theorem Mest_log_le : (⌈logb 2 (16 * p.Rl / p.δ)⌉₊ : ℝ) ≤ 24 * logb 2 p.V + 1 ∧
    24 * logb 2 p.V + 1 ≤ p.V := by
  have hV := V_gt hp
  have hl := logV_gt hp
  have hl2 := logV_le hp
  have hR := Rl_ge_one hp
  have hX1 : 1 ≤ 16 * (p.Rl : ℝ) / p.δ := by
    rw [one_le_div hp.δ_pos]; linarith [hp.δ_lt]
  have hX : 16 * (p.Rl : ℝ) / p.δ ≤ 2 ^ 0 * p.V ^ 21 := by
    rw [div_eq_mul_inv]
    have hQ := Q_le_V20 hp
    have hδ := inv_delta_le hp
    have : (p.Rl : ℝ) = p.Q := rfl
    calc 16 * (p.Rl : ℝ) * p.δ⁻¹ ≤ 16 * p.V ^ 20 * (p.V / 128) := by
          have : 0 ≤ p.δ⁻¹ := inv_nonneg.mpr hp.δ_pos.le
          gcongr; linarith
      _ ≤ 2 ^ 0 * p.V ^ 21 := by
          have : (0 : ℝ) ≤ p.V ^ 21 := by positivity
          ring_nf; nlinarith
  have := ceil_logb_lt hX1 (V_pos hp) hX
  push_cast at this
  constructor <;> linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `M_est ≤ V^27`. -/
theorem Mest_le : (p.Mest : ℝ) ≤ p.V ^ 27 := by
  have hV := V_gt hp
  have hγ := gamma_inv_le hp
  have hγ0 : 0 ≤ p.gamma⁻¹ := inv_nonneg.mpr (gamma_pos hp).le
  have hξ := xi_inv_le hp
  have hξ0 : 0 ≤ p.xi⁻¹ := inv_nonneg.mpr (xi_pos (p := p)).le
  have hc := Mest_log_le hp
  set c : ℝ := (⌈logb 2 (16 * p.Rl / p.δ)⌉₊ : ℝ) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have he : 192 / (p.gamma * p.xi ^ 2) * c = 192 * p.gamma⁻¹ * (p.xi⁻¹) ^ 2 * c := by
    rw [div_eq_mul_inv, mul_inv, inv_pow]; ring
  have h0 : 0 ≤ 192 / (p.gamma * p.xi ^ 2) * c := by rw [he]; positivity
  have h1 := Nat.ceil_lt_add_one h0
  have h2 : 192 / (p.gamma * p.xi ^ 2) * c ≤ 1536 * p.V ^ 24 := by
    rw [he]
    calc 192 * p.gamma⁻¹ * (p.xi⁻¹) ^ 2 * c ≤ 192 * (8 * p.V) * (p.V ^ 11) ^ 2 * p.V := by
          gcongr
          · exact hγ.1
          · linarith [hc.1, hc.2]
      _ = 1536 * p.V ^ 24 := by ring
  have h3 : (1 : ℝ) ≤ p.V ^ 24 := one_le_pow₀ (one_le_V hp)
  have h4 : 1537 * p.V ^ 24 ≤ p.V ^ 27 := const_mul_pow_le (a := 24) (b := 3) hV.le (by norm_num)
  unfold Mest
  rw [← hcdef]
  linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `b_τ + 1 ≤ log₂ V + 3 ≤ V`. -/
theorem bTau_le : (bTau p.T p.ε : ℝ) + 1 ≤ logb 2 p.V + 3 ∧ logb 2 p.V + 3 ≤ p.V := by
  have hε := hp.ε_pos
  have hx : 1 ≤ 8 * (p.T : ℝ) / p.ε := by
    rw [one_le_div hε]; have := T_ge_real hp; linarith [hp.ε_lt]
  have hle : 8 * (p.T : ℝ) / p.ε ≤ 2 * p.V := by
    have := four_T_div_eps_le hp
    have : 8 * (p.T : ℝ) / p.ε = 2 * (4 * p.T / p.ε) := by ring
    linarith
  have h := ceil_logb_lt_of_le hx hle
  rw [Real.logb_mul (by norm_num) (V_pos hp).ne', Real.logb_self_eq_one one_lt_two] at h
  have := logV_le hp; have := V_gt hp
  unfold bTau
  constructor <;> linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): one simulated conditional bit costs at
most `T + b_τ + 1 ≤ 2V ≤ V²` tokens. -/
theorem bitCost_le : (p.T : ℝ) + bTau p.T p.ε + 1 ≤ 2 * p.V ∧ 2 * p.V ≤ p.V ^ 2 := by
  have h := bTau_le hp
  have hT := T_le hp
  have hV := V_gt hp
  constructor
  · linarith [h.1, h.2]
  · nlinarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): `W = R_ℓ M_est V² + R_s T V² ≤ V^51 +
V^25 ≤ V^52`. -/
theorem W_le : p.W ≤ p.V ^ 51 + p.V ^ 25 ∧ p.V ^ 51 + p.V ^ 25 ≤ p.V ^ 52 := by
  have hV := V_gt hp
  have hV1 := one_le_V hp
  have hR : (p.Rl : ℝ) ≤ p.V ^ 20 := Q_le_V20 hp
  have hRs : (p.Rs : ℝ) ≤ p.V ^ 20 := Q_le_V20 hp
  have hM := Mest_le hp
  have hT : (p.T : ℝ) ≤ p.V := by have := T_le hp; linarith
  constructor
  · unfold W
    have h1 : (p.Rl : ℝ) * p.Mest * p.V ^ 2 ≤ p.V ^ 51 := by
      calc (p.Rl : ℝ) * p.Mest * p.V ^ 2 ≤ p.V ^ 20 * p.V ^ 27 * p.V ^ 2 := by gcongr
        _ = p.V ^ 49 := by ring
        _ ≤ p.V ^ 51 := pow_le_pow_right₀ hV1 (by norm_num)
    have h2 : (p.Rs : ℝ) * p.T * p.V ^ 2 ≤ p.V ^ 25 := by
      calc (p.Rs : ℝ) * p.T * p.V ^ 2 ≤ p.V ^ 20 * p.V * p.V ^ 2 := by gcongr
        _ = p.V ^ 23 := by ring
        _ ≤ p.V ^ 25 := pow_le_pow_right₀ hV1 (by norm_num)
    linarith
  · have e : p.V ^ 25 ≤ p.V ^ 51 := pow_le_pow_right₀ hV1 (by norm_num)
    have : 2 * p.V ^ 51 ≤ p.V ^ 52 := const_mul_pow_le (a := 51) (b := 1) hV.le (by norm_num)
    linarith

/-- `lem:explicit-gls-token-envelope` (numerical envelope): the full token count, charging `T + b_τ
+ 1` tokens for every simulated conditional bit
(`M_est` bits per numerical request, `T` bits per complete sample), is at most `W`. -/
theorem tokens_le_W : p.tokens ≤ p.W := by
  have h := bitCost_le hp
  have hc : (p.T : ℝ) + bTau p.T p.ε + 1 ≤ p.V ^ 2 := h.1.trans h.2
  unfold tokens W
  gcongr

/-- `lem:explicit-gls-token-envelope`, numerical part: `R_ℓ + R_s ≤ V^22`, `ξ⁻¹ ≤ V^11`, and the
full training-token count (with the bit cost `T + b_τ + 1`) is at most `W ≤ V^52`. -/
theorem explicit_gls_token_envelope :
    (p.Rl : ℝ) + p.Rs ≤ p.V ^ 22 ∧ p.xi⁻¹ ≤ p.V ^ 11 ∧ p.tokens ≤ p.V ^ 52 :=
  ⟨Rl_add_Rs_le hp, xi_inv_le hp,
    (tokens_le_W hp).trans ((W_le hp).1.trans (W_le hp).2)⟩

end Numerical

end Input

/-! ### Counting future columns and requests (`sec:explicit-gls-procedure`) -/

section Counting

/-- The extended future set `F̃ = F̂ ∪ (Σ ∘ F̂')`, `Σ = {0,1}`, of `sec:explicit-gls-procedure`. -/
def extendFutures (A B : Finset (List Bool)) : Finset (List Bool) :=
  A ∪ ((univ : Finset Bool) ×ˢ B).image (fun x => x.1 :: x.2)

theorem card_extendFutures_le (A B : Finset (List Bool)) :
    (extendFutures A B).card ≤ A.card + 2 * B.card := by
  unfold extendFutures
  calc _ ≤ A.card + (((univ : Finset Bool) ×ˢ B).image (fun x => x.1 :: x.2)).card :=
        card_union_le _ _
    _ ≤ A.card + ((univ : Finset Bool) ×ˢ B).card := by gcongr; exact card_image_le
    _ = A.card + 2 * B.card := by rw [card_product]; simp

/-- `sec:explicit-gls-procedure`: with `|F̂_t| ≤ 2 + a_t` and `|F̂_{t+1}| ≤ 2 + a_{t+1}`
(two initial one-token futures plus the witnesses), `m_t = |F̃_t| ≤ 6 + a_t + 2 a_{t+1}`. -/
theorem card_extendFutures_le_witnesses {A B : Finset (List Bool)} {a a' : ℕ}
    (hA : A.card ≤ 2 + a) (hB : B.card ≤ 2 + a') :
    (extendFutures A B).card ≤ 6 + a + 2 * a' := by
  have := card_extendFutures_le A B; omega

/-- `sec:gls-validation-arithmetic`: `|F̂_t| ≤ K + 1` gives `d̄ ≤ 3(K+1) ≤ 6K`. -/
theorem card_extendFutures_le_dbar {A B : Finset (List Bool)} {K : ℕ} (hK : 1 ≤ K)
    (hA : A.card ≤ K + 1) (hB : B.card ≤ K + 1) :
    (extendFutures A B).card ≤ 3 * (K + 1) ∧ 3 * (K + 1) ≤ 6 * K := by
  have := card_extendFutures_le A B; omega

theorem sum_Icc_shift_add (a : ℕ → ℕ) (T : ℕ) :
    ∑ t ∈ Icc 1 T, a (t + 1) + a 1 = ∑ t ∈ Icc 1 T, a t + a (T + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
    omega

theorem sq_six_add_le (x : ℕ) : (6 + x) ^ 2 ≤ 72 + 2 * x ^ 2 := by
  zify; nlinarith [sq_nonneg ((x : ℤ) - 6)]

theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (b : ι → ℕ) :
    ∑ i ∈ s, b i ^ 2 ≤ (∑ i ∈ s, b i) ^ 2 := by
  rw [sq, sum_mul]
  apply sum_le_sum
  intro i hi
  rw [sq]
  exact Nat.mul_le_mul_left _ (single_le_sum (fun _ _ => Nat.zero_le _) hi)

/-- `sec:explicit-gls-procedure`: if `a_t` witnesses were added at cut `t`, `∑_t a_t ≤ k`,
`a_{T+1} = 0` and `m_t ≤ 6 + a_t + 2a_{t+1}`, then `∑_{t=1}^T m_t² ≤ 72T + 18k²`. -/
theorem sum_sq_futures_le (T k : ℕ) (a m : ℕ → ℕ) (haT : a (T + 1) = 0)
    (hsum : ∑ t ∈ Icc 1 T, a t ≤ k)
    (hm : ∀ t ∈ Icc 1 T, m t ≤ 6 + a t + 2 * a (t + 1)) :
    ∑ t ∈ Icc 1 T, m t ^ 2 ≤ 72 * T + 18 * k ^ 2 := by
  have hshift := sum_Icc_shift_add a T
  rw [haT] at hshift
  have hb : ∑ t ∈ Icc 1 T, (a t + 2 * a (t + 1)) ≤ 3 * k := by
    rw [sum_add_distrib, ← mul_sum]; omega
  have h1 : ∑ t ∈ Icc 1 T, m t ^ 2 ≤ ∑ t ∈ Icc 1 T, (72 + 2 * (a t + 2 * a (t + 1)) ^ 2) := by
    apply sum_le_sum
    intro t ht
    have := hm t ht
    calc m t ^ 2 ≤ (6 + (a t + 2 * a (t + 1))) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ _ := sq_six_add_le _
  have h2 := sum_sq_le_sq_sum (Icc 1 T) (fun t => a t + 2 * a (t + 1))
  have h3 : (∑ t ∈ Icc 1 T, (a t + 2 * a (t + 1))) ^ 2 ≤ (3 * k) ^ 2 := Nat.pow_le_pow_left hb 2
  rw [sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, ← mul_sum] at h1
  simp only [Nat.add_sub_cancel] at h1
  nlinarith

/-- `eq:global-future-dimension`: summing `72T + 18k²` over the epochs `k = 1, …, K` gives at most
`90K³` when `K ≥ T`. -/
theorem sum_epochs_le {T K : ℕ} (hTK : T ≤ K) :
    ∑ k ∈ Icc 1 K, (72 * T + 18 * k ^ 2) ≤ 90 * K ^ 3 := by
  calc ∑ k ∈ Icc 1 K, (72 * T + 18 * k ^ 2) ≤ ∑ _k ∈ Icc 1 K, (72 * K + 18 * K ^ 2) := by
        apply sum_le_sum; intro k hk
        rw [mem_Icc] at hk
        have : k ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left hk.2 2
        omega
    _ = K * (72 * K + 18 * K ^ 2) := by simp
    _ ≤ 90 * K ^ 3 := by
        rcases Nat.eq_zero_or_pos K with h | h
        · simp [h]
        · have : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right h (by norm_num)
          nlinarith

/-- `eq:global-future-dimension`: the same bound with the epochs indexed `k = 0, …, K-1`. -/
theorem sum_epochs_range_le {T K : ℕ} (hTK : T ≤ K) :
    ∑ k ∈ range K, (72 * T + 18 * k ^ 2) ≤ 90 * K ^ 3 := by
  calc ∑ k ∈ range K, (72 * T + 18 * k ^ 2) ≤ ∑ _k ∈ range K, (72 * K + 18 * K ^ 2) := by
        apply sum_le_sum; intro k hk
        rw [mem_range] at hk
        have : k ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left hk.le 2
        omega
    _ = K * (72 * K + 18 * K ^ 2) := by simp
    _ ≤ 90 * K ^ 3 := by
        rcases Nat.eq_zero_or_pos K with h | h
        · simp [h]
        · have : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right h (by norm_num)
          nlinarith

/-- `eq:global-future-dimension`: summing the cutwise bound over at most `K ≥ T` epochs,
`∑_{k,t} m_t(k)² ≤ 90K³`. Epoch `k ∈ {1, …, K}` starts with `∑_t a_t(k) ≤ k` witnesses. -/
theorem global_future_dimension {T K : ℕ} (hTK : T ≤ K) (a m : ℕ → ℕ → ℕ)
    (haT : ∀ k ∈ Icc 1 K, a k (T + 1) = 0)
    (hsum : ∀ k ∈ Icc 1 K, ∑ t ∈ Icc 1 T, a k t ≤ k)
    (hm : ∀ k ∈ Icc 1 K, ∀ t ∈ Icc 1 T, m k t ≤ 6 + a k t + 2 * a k (t + 1)) :
    ∑ k ∈ Icc 1 K, ∑ t ∈ Icc 1 T, m k t ^ 2 ≤ 90 * K ^ 3 :=
  (sum_le_sum fun k hk =>
    sum_sq_futures_le T k (a k) (m k) (haT k hk) (hsum k hk) (hm k hk)).trans (sum_epochs_le hTK)

/-- The validated index pairs `(s, r)` with `1 ≤ s ≤ t` and `s ≤ r ≤ t + 1`. -/
def validationPairs (t : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 t ×ˢ Icc 1 (t + 1)).filter (fun x => x.1 ≤ x.2)

theorem card_validationPairs_eq_sum (t : ℕ) :
    (validationPairs t).card = ∑ s ∈ Icc 1 t, (t + 2 - s) := by
  unfold validationPairs
  rw [card_filter, sum_product]
  apply sum_congr rfl
  intro s hs
  rw [mem_Icc] at hs
  rw [← card_filter]
  have : (Icc 1 (t + 1)).filter (fun r => s ≤ r) = Icc s (t + 1) := by
    ext r; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc]

theorem two_mul_sum_Icc_sub (t : ℕ) : 2 * ∑ s ∈ Icc 1 t, (t + 2 - s) = t * (t + 3) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h : ∑ s ∈ Icc 1 t, (t + 1 + 2 - s) = ∑ s ∈ Icc 1 t, ((t + 2 - s) + 1) :=
      sum_congr rfl (fun s hs => by rw [mem_Icc] at hs; omega)
    rw [h, sum_add_distrib, sum_const, Nat.card_Icc, smul_eq_mul, mul_one, mul_add, mul_add, ih,
      Nat.add_sub_cancel, Nat.add_sub_cancel_left]
    ring

/-- `sec:explicit-gls-procedure`: there are `t(t+3)/2` pairs `(s, r)` with `1 ≤ s ≤ t`,
`s ≤ r ≤ t + 1`. -/
theorem two_mul_card_validationPairs (t : ℕ) : 2 * (validationPairs t).card = t * (t + 3) := by
  rw [card_validationPairs_eq_sum, two_mul_sum_Icc_sub]

/-- "Explicit request caps": validation requests for one epoch, cut `t ≤ T - 1` and sample:
`t(t+3)/2` pairs, two final symbols and at most `2d̄` numerical values per residual, i.e. `2 d̄ t
(t+3) ≤ 24 K T²` when `d̄ ≤ 6K`. -/
theorem validation_requests_le {t T K dbar : ℕ} (ht : t ≤ T - 1) (hd : dbar ≤ 6 * K) :
    (validationPairs t).card * 2 * (2 * dbar) = 2 * dbar * (t * (t + 3)) ∧
      2 * dbar * (t * (t + 3)) ≤ 24 * K * T ^ 2 := by
  constructor
  · rw [← two_mul_card_validationPairs]; ring
  · have h2 : t * (t + 3) ≤ 2 * T ^ 2 := by
      rcases Nat.eq_zero_or_pos T with h | h
      · subst h; simp at ht; simp [ht]
      · have h1 : t + 1 ≤ T := by omega
        have := Nat.mul_le_mul h1 h1
        nlinarith
    calc 2 * dbar * (t * (t + 3)) ≤ 2 * (6 * K) * (2 * T ^ 2) := by gcongr
      _ = 24 * K * T ^ 2 := by ring

/-- "Explicit request caps": the validation count over `K` epochs, cuts `t = 1, …, T-1` and `n`
samples is at most `24 n T³ K²`. -/
theorem validation_total_le {T K n dbar : ℕ} (hd : dbar ≤ 6 * K) :
    K * n * ∑ t ∈ Icc 1 (T - 1), (validationPairs t).card * 2 * (2 * dbar) ≤
      24 * n * T ^ 3 * K ^ 2 := by
  have h : ∑ t ∈ Icc 1 (T - 1), (validationPairs t).card * 2 * (2 * dbar) ≤
      ∑ _t ∈ Icc 1 (T - 1), 24 * K * T ^ 2 :=
    sum_le_sum fun t ht => by
      rw [mem_Icc] at ht
      have h := validation_requests_le (T := T) (K := K) ht.2 hd
      rw [h.1]; exact h.2
  rw [sum_const, Nat.card_Icc, smul_eq_mul] at h
  have hT : T - 1 + 1 - 1 ≤ T := by omega
  calc K * n * ∑ t ∈ Icc 1 (T - 1), (validationPairs t).card * 2 * (2 * dbar)
      ≤ K * n * ((T - 1 + 1 - 1) * (24 * K * T ^ 2)) := by gcongr
    _ ≤ K * n * (T * (24 * K * T ^ 2)) := by gcongr
    _ = 24 * n * T ^ 3 * K ^ 2 := by ring

/-- "Explicit request caps": the completed emission cache uses at most `3 T d̄ ≤ 18 T K` numerical
requests. -/
theorem emission_cache_le {T K dbar : ℕ} (hd : dbar ≤ 6 * K) : 3 * T * dbar ≤ 18 * T * K := by
  calc 3 * T * dbar ≤ 3 * T * (6 * K) := by gcongr
    _ = 18 * T * K := by ring

/-- The sample size `N_s` of `lem:compression-spanner` at dimension `m`, missed mass `η` and
failure probability `δs`. -/
noncomputable def spannerN (m : ℕ) (η δs : ℝ) : ℕ :=
  ⌈2 / η * (m * ⌈logb 2 (2 * m / η)⌉₊ + ⌈logb 2 ((m + 1) / δs)⌉₊)⌉₊

/-- "Explicit request caps preserving the sharper rate": at dimension `1 ≤ m ≤ 6K`, if `H`
dominates both logarithmic ceilings of `H_⋆`, then `N ≤ 2H(m+1)/η + 1 ≤ 5Hm/η`. -/
theorem spannerN_le {m K H : ℕ} {η δs : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hδs : 0 < δs)
    (hm1 : 1 ≤ m) (hmK : m ≤ 6 * K)
    (hH1 : ⌈logb 2 (12 * K / η)⌉₊ ≤ H) (hH2 : ⌈logb 2 ((6 * K + 1) / δs)⌉₊ ≤ H) :
    (spannerN m η δs : ℝ) ≤ 2 * H * (m + 1) / η + 1 ∧
      2 * H * (m + 1) / η + 1 ≤ 5 * H * m / η := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmK' : (m : ℝ) ≤ 6 * K := by exact_mod_cast hmK
  have hK1 : 1 ≤ K := by omega
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hc1 : ⌈logb 2 (2 * m / η)⌉₊ ≤ H := by
    refine le_trans (Nat.ceil_mono ?_) hH1
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hη0.le
  have hc2 : ⌈logb 2 ((m + 1) / δs)⌉₊ ≤ H := by
    refine le_trans (Nat.ceil_mono ?_) hH2
    apply Real.logb_le_logb_of_le one_lt_two (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hδs.le
  have hc1' : (⌈logb 2 (2 * m / η)⌉₊ : ℝ) ≤ H := by exact_mod_cast hc1
  have hc2' : (⌈logb 2 ((m + 1) / δs)⌉₊ : ℝ) ≤ H := by exact_mod_cast hc2
  have hH : (1 : ℝ) ≤ H := by
    have h12 : 1 < 12 * (K : ℝ) / η := by
      rw [one_lt_div hη0]; linarith
    exact_mod_cast (one_le_ceil_logb h12).trans hH1
  constructor
  · have h0 : 0 ≤ 2 / η * (m * (⌈logb 2 (2 * m / η)⌉₊ : ℝ) + ⌈logb 2 ((m + 1) / δs)⌉₊) :=
      mul_nonneg (div_nonneg (by norm_num) hη0.le) (by positivity)
    have hlt := Nat.ceil_lt_add_one h0
    have hle : 2 / η * (m * (⌈logb 2 (2 * m / η)⌉₊ : ℝ) + ⌈logb 2 ((m + 1) / δs)⌉₊) ≤
        2 * H * (m + 1) / η := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hη0]
      have hm0 : (0 : ℝ) ≤ m := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hc1' hm0]
    unfold spannerN; linarith
  · rw [div_add_one hη0.ne', div_le_div_iff_of_pos_right hη0]
    nlinarith

/-- "Explicit request caps preserving the sharper rate": if every spanner call has dimension
`1 ≤ m ≤ 6K` and `∑ m² ≤ 90K³` (`eq:global-future-dimension`), then the combined spanner
requests `∑ N (1 + m)` (one complete sample and at most `m` numerical values per row) are at
most `900 H K³/η`. -/
theorem spanner_requests_le {ι : Type*} (s : Finset ι) (m : ι → ℕ) {K H : ℕ} {η δs : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδs : 0 < δs)
    (hm1 : ∀ i ∈ s, 1 ≤ m i) (hmK : ∀ i ∈ s, m i ≤ 6 * K)
    (hH1 : ⌈logb 2 (12 * K / η)⌉₊ ≤ H) (hH2 : ⌈logb 2 ((6 * K + 1) / δs)⌉₊ ≤ H)
    (hsq : ∑ i ∈ s, m i ^ 2 ≤ 90 * K ^ 3) :
    ∑ i ∈ s, (spannerN (m i) η δs : ℝ) * (1 + m i) ≤ 900 * H * K ^ 3 / η := by
  have hsq' : ∑ i ∈ s, (m i : ℝ) ^ 2 ≤ 90 * K ^ 3 := by exact_mod_cast hsq
  have hc : 0 ≤ 10 * (H : ℝ) / η := div_nonneg (by positivity) hη0.le
  calc ∑ i ∈ s, (spannerN (m i) η δs : ℝ) * (1 + m i)
      ≤ ∑ i ∈ s, 10 * (H : ℝ) / η * (m i : ℝ) ^ 2 := by
        apply sum_le_sum; intro i hi
        have h := spannerN_le hη0 hη1 hδs (hm1 i hi) (hmK i hi) hH1 hH2
        have hm : (1 : ℝ) ≤ m i := by exact_mod_cast hm1 i hi
        have hN : (spannerN (m i) η δs : ℝ) ≤ 5 * H * m i / η := h.1.trans h.2
        have h5 : 0 ≤ 5 * (H : ℝ) * m i / η := div_nonneg (by positivity) hη0.le
        calc (spannerN (m i) η δs : ℝ) * (1 + m i) ≤ (5 * H * m i / η) * (1 + m i) := by
              gcongr
          _ ≤ (5 * H * m i / η) * (2 * m i) := by gcongr; linarith
          _ = 10 * H / η * (m i : ℝ) ^ 2 := by ring
    _ = 10 * (H : ℝ) / η * ∑ i ∈ s, (m i : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 10 * (H : ℝ) / η * (90 * K ^ 3) := by gcongr
    _ = 900 * H * K ^ 3 / η := by ring

end Counting

namespace Input

variable {p : Input}

/-- "Explicit request caps preserving the sharper rate", with the parameters of
`eq:explicit-gls-parameters`: at dimension `1 ≤ m ≤ 6K`,
`N ≤ 2H_⋆(m+1)/η + 1 ≤ 5H_⋆m/η`. -/
theorem spannerN_le_Hstar (hp : p.Valid) {m : ℕ} (hm1 : 1 ≤ m) (hmK : m ≤ 6 * p.K) :
    (spannerN m p.eta p.deltaS : ℝ) ≤ 2 * p.Hstar * (m + 1) / p.eta + 1 ∧
      2 * p.Hstar * (m + 1) / p.eta + 1 ≤ 5 * p.Hstar * m / p.eta :=
  spannerN_le (eta_pos hp) (eta_lt_one hp) (deltaS_pos hp) hm1 hmK (le_max_left _ _)
    (le_max_right _ _)

/-- "Explicit request caps preserving the sharper rate": spanner requests over any family of
calls with dimensions in `[1, 6K]` and `∑ m² ≤ 90K³` are at most `900 H_⋆ K³/η`. -/
theorem spanner_requests_le_Hstar (hp : p.Valid) {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (hm1 : ∀ i ∈ s, 1 ≤ m i) (hmK : ∀ i ∈ s, m i ≤ 6 * p.K)
    (hsq : ∑ i ∈ s, m i ^ 2 ≤ 90 * p.K ^ 3) :
    ∑ i ∈ s, (spannerN (m i) p.eta p.deltaS : ℝ) * (1 + m i) ≤
      900 * p.Hstar * p.K ^ 3 / p.eta :=
  spanner_requests_le s m (eta_pos hp) (eta_lt_one hp) (deltaS_pos hp) hm1 hmK
    (le_max_left _ _) (le_max_right _ _) hsq

/-- `eq:explicit-gls-request-caps`: spanner requests (at most `900 H_⋆ K³/η`), validation
requests (at most `24 n T³ K²`), complete validation samples (at most `Kn`) and the emission
cache (at most `18TK`) together are at most `Q`. -/
theorem requests_le_Q {S_span : ℝ} {S_val S_samp S_cache : ℕ}
    (h1 : S_span ≤ 900 * p.Hstar * p.K ^ 3 / p.eta) (h2 : S_val ≤ 24 * p.n * p.T ^ 3 * p.K ^ 2)
    (h3 : S_samp ≤ p.K * p.n) (h4 : S_cache ≤ 18 * p.T * p.K) :
    S_span + S_val + S_samp + S_cache ≤ p.Q := by
  have hc := Nat.le_ceil (900 * p.Hstar * p.K ^ 3 / p.eta)
  have h2' : (S_val : ℝ) ≤ 24 * p.n * p.T ^ 3 * p.K ^ 2 := by exact_mod_cast h2
  have h3' : (S_samp : ℝ) ≤ p.K * p.n := by exact_mod_cast h3
  have h4' : (S_cache : ℝ) ≤ 18 * p.T * p.K := by exact_mod_cast h4
  rw [Q]; push_cast
  linarith


/-- The hypotheses of `lem:explicit-gls-token-envelope` are satisfiable. -/
theorem valid_example : (Input.mk 32 1 1 (1 / 4) (1 / 4)).Valid :=
  ⟨le_rfl, le_rfl, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `K ≥ T`, as used for `eq:global-future-dimension`. -/
theorem T_le_K (hp : p.Valid) : p.T ≤ p.K := by
  have := hp.d_pos; have := Jb_ge (p := p)
  unfold K
  calc p.T = 1 * p.T * 1 * 1 := by ring
    _ ≤ 512 * p.T * p.d * p.Jb := by gcongr <;> omega

/-- "Explicit request caps preserving the sharper rate", all epochs and cuts together: if epoch
`k ∈ {1, …, K}` has row dimensions `m_t(k) ∈ [1, 6K]` at cuts `t ∈ {1, …, T}` obeying the
witness accounting of `sec:explicit-gls-procedure`, the spanner requests
`∑_{k,t} N_t(k) (1 + m_t(k))` are at most `900 H_⋆ K³/η`. -/
theorem spanner_requests_global (hp : p.Valid) (a m : ℕ → ℕ → ℕ)
    (haT : ∀ k ∈ Icc 1 p.K, a k (p.T + 1) = 0)
    (hsum : ∀ k ∈ Icc 1 p.K, ∑ t ∈ Icc 1 p.T, a k t ≤ k)
    (hm : ∀ k ∈ Icc 1 p.K, ∀ t ∈ Icc 1 p.T, m k t ≤ 6 + a k t + 2 * a k (t + 1))
    (hm1 : ∀ k ∈ Icc 1 p.K, ∀ t ∈ Icc 1 p.T, 1 ≤ m k t)
    (hmK : ∀ k ∈ Icc 1 p.K, ∀ t ∈ Icc 1 p.T, m k t ≤ 6 * p.K) :
    ∑ k ∈ Icc 1 p.K, ∑ t ∈ Icc 1 p.T, (spannerN (m k t) p.eta p.deltaS : ℝ) * (1 + m k t) ≤
      900 * p.Hstar * p.K ^ 3 / p.eta := by
  have hglob := global_future_dimension (T_le_K hp) a m haT hsum hm
  have hsq : ∑ x ∈ Icc 1 p.K ×ˢ Icc 1 p.T, m x.1 x.2 ^ 2 ≤ 90 * p.K ^ 3 := by
    rw [sum_product]; exact hglob
  have h := spanner_requests_le_Hstar hp (Icc 1 p.K ×ˢ Icc 1 p.T) (fun x => m x.1 x.2)
    (fun x hx => by rw [mem_product] at hx; exact hm1 _ hx.1 _ hx.2)
    (fun x hx => by rw [mem_product] at hx; exact hmK _ hx.1 _ hx.2) hsq
  rw [sum_product] at h
  exact h

/-- `sec:gls-validation-arithmetic`: rounding to the grid with `b_A = b_ξ + 4` fractional bits
costs at most half a grid step, `2^{-b_A}/2 = ξ/32`. -/
theorem grid_half_step : ((2 : ℝ) ^ (p.bXi + 4))⁻¹ / 2 = p.xi / 32 := by
  rw [xi, pow_add]; norm_num; ring

/-- `sec:gls-validation-arithmetic`: the wrapper's error budget
`ξ/6 + ξ/8 + ξ/32 = 31ξ/96 < ξ/2`. -/
theorem wrapper_error_budget {ξ : ℝ} (hξ : 0 < ξ) :
    ξ / 6 + ξ / 8 + ξ / 32 = 31 / 96 * ξ ∧ 31 / 96 * ξ < ξ / 2 :=
  ⟨by ring, by linarith⟩

end Input

end LowLogitRank.Envelope
