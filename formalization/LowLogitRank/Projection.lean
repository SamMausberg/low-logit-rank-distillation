import LowLogitRank.Basic

/-!
# Approximate relative-entropy projection (`lem:approx-projection`)

Relative entropy `D(x‖v) = ∑ x_j log (x_j / v_j)` on a finite index type, and the projection
lemma of `sec:finite-bit-lm` with an approximately optimal feasible point.
-/

namespace LowLogitRank.Projection

open Finset Filter Topology

/-- Relative entropy `D(x‖v) = ∑ x_j log (x_j / v_j)`. The second argument need not sum to one. -/
noncomputable def relEnt {ι : Type*} [Fintype ι] (x v : ι → ℝ) : ℝ :=
  ∑ j, x j * Real.log (x j / v j)

/-! ### One-variable inequalities -/

/-- `log u ≤ (u - u⁻¹)/2` for `u ≥ 1`. -/
theorem log_le_half_sub_inv {u : ℝ} (hu : 1 ≤ u) : Real.log u ≤ (u - u⁻¹) / 2 := by
  have hu0 : 0 < u := by linarith
  set x := (u - 1) / (u + 1) with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) (by linarith)
  have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
  have h := Real.log_div_le_sum_range_add hx0 hx1 0
  have e1 : (1 + x) / (1 - x) = u := by
    rw [hx]; field_simp; ring
  have hx2 : 1 - x ^ 2 = 4 * u / (u + 1) ^ 2 := by
    rw [hx]; field_simp; ring
  have e2 : x ^ (2 * 0 + 1) / (1 - x ^ 2) = (u - u⁻¹) / 4 := by
    have h1 : u + 1 ≠ 0 := by linarith
    rw [hx2, hx, pow_one, div_div_eq_mul_div]
    field_simp
    ring
  rw [e1, e2] at h
  simp only [range_zero, sum_empty, zero_add] at h
  linarith

/-- `log c ≤ (c - 1) - (c - 1)²/2` for `0 < c ≤ 1`. -/
theorem log_le_sub_sub_sq {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Real.log c ≤ (c - 1) - (c - 1) ^ 2 / 2 := by
  have hx : |1 - c| < 1 := by rw [abs_lt]; constructor <;> linarith
  have h := Real.hasSum_pow_div_log_of_abs_lt_one hx
  have h2 := sum_le_hasSum (range 2) (fun i _ => by
    have : 0 ≤ 1 - c := by linarith
    positivity) h
  simp only [sum_range_succ, range_zero, sum_empty] at h2
  rw [show (1 : ℝ) - (1 - c) = c by ring] at h2
  norm_num at h2
  nlinarith

/-- Pointwise strong convexity: `(a - b)²/2 ≤ a log (a/b) - a + b` for `a, b ∈ (0, 1]`. -/
theorem half_sq_le_mul_log {a b : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    (a - b) ^ 2 / 2 ≤ a * Real.log (a / b) - a + b := by
  rcases le_total b a with hba | hab
  · -- `b = a (1 - x)` with `x ∈ [0, 1)`
    have hc0 : 0 < b / a := div_pos hb0 ha0
    have hc1 : b / a ≤ 1 := (div_le_one ha0).2 hba
    have h := log_le_sub_sub_sq hc0 hc1
    have hlog : Real.log (a / b) = - Real.log (b / a) := by
      rw [← Real.log_inv, inv_div]
    rw [hlog]
    have key : a * ((b / a - 1) - (b / a - 1) ^ 2 / 2) = (b - a) - (a - b) ^ 2 / (2 * a) := by
      field_simp; ring
    have h1 : a * Real.log (b / a) ≤ (b - a) - (a - b) ^ 2 / (2 * a) := by
      rw [← key]; exact mul_le_mul_of_nonneg_left h ha0.le
    have h2 : (a - b) ^ 2 / 2 ≤ (a - b) ^ 2 / (2 * a) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity); linarith
    nlinarith
  · -- `u = b / a ≥ 1`
    have hu : 1 ≤ b / a := (one_le_div ha0).2 hab
    have h := log_le_half_sub_inv hu
    have hlog : Real.log (a / b) = - Real.log (b / a) := by
      rw [← Real.log_inv, inv_div]
    rw [hlog]
    have key : a * ((b / a - (b / a)⁻¹) / 2) = (b ^ 2 - a ^ 2) / (2 * b) := by
      field_simp
    have h1 : a * Real.log (b / a) ≤ (b ^ 2 - a ^ 2) / (2 * b) := by
      rw [← key]; exact mul_le_mul_of_nonneg_left h ha0.le
    have h2 : (a - b) ^ 2 / 2 + (b ^ 2 - a ^ 2) / (2 * b) ≤ b - a := by
      rw [div_add_div _ _ (by norm_num) (by positivity), div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg (a - b)) (sub_nonneg.2 hb1)]
    linarith

/-- `log (a/b) ≤ (a - b)/b` for `a, b > 0`. -/
theorem log_div_le_sub_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a / b) ≤ (a - b) / b := by
  have := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [sub_div, div_self hb.ne']
  exact this


/-- `|log a - log b| ≤ |a - b| / μ` when `a, b ≥ μ > 0`. -/
theorem abs_log_sub_log_le {a b μ : ℝ} (hμ : 0 < μ) (ha : μ ≤ a) (hb : μ ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / μ := by
  have ha0 : 0 < a := hμ.trans_le ha
  have hb0 : 0 < b := hμ.trans_le hb
  rw [abs_le]
  constructor
  · have h := log_div_le_sub_div hb0 ha0
    rw [Real.log_div hb0.ne' ha0.ne'] at h
    have h2 : (b - a) / a ≤ |a - b| / μ := by
      rw [abs_sub_comm]
      calc (b - a) / a ≤ |b - a| / a := by gcongr; exact le_abs_self _
        _ ≤ |b - a| / μ := by gcongr
    linarith
  · have h := log_div_le_sub_div ha0 hb0
    rw [Real.log_div ha0.ne' hb0.ne'] at h
    have h2 : (a - b) / b ≤ |a - b| / μ := by
      calc (a - b) / b ≤ |a - b| / b := by gcongr; exact le_abs_self _
        _ ≤ |a - b| / μ := by gcongr
    linarith

/-! ### Slopes and one-sided derivatives -/

/-- If `φ t ≤ φ 0 + t M` for `t ∈ (0, 1)`, then `φ'(0) ≤ M`. -/
theorem deriv_le_of_le_add_mul {φ : ℝ → ℝ} {φ' M : ℝ} (hφ : HasDerivAt φ φ' 0)
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, φ t ≤ φ 0 + t * M) : φ' ≤ M := by
  refine le_of_tendsto hφ.tendsto_slope_zero_right ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have := h t ht
  simp only [zero_add, smul_eq_mul]
  rw [inv_mul_le_iff₀ ht.1]
  linarith

/-- If `φ 0 ≤ φ t` for `t ∈ (0, 1)`, then `0 ≤ φ'(0)`. -/
theorem deriv_nonneg_of_le {φ : ℝ → ℝ} {φ' : ℝ} (hφ : HasDerivAt φ φ' 0)
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, φ 0 ≤ φ t) : 0 ≤ φ' := by
  have := deriv_le_of_le_add_mul hφ.neg (M := 0) (fun t ht => by simp [h t ht])
  linarith

/-! ### Relative entropy -/

section RelEnt

variable {ι : Type*} [Fintype ι]

/-- `x` is a probability vector. -/
def ProbVec (x : ι → ℝ) : Prop := (∀ j, 0 ≤ x j) ∧ ∑ j, x j = 1

theorem ProbVec.le_one {x : ι → ℝ} (hx : ProbVec x) (j : ι) : x j ≤ 1 := by
  rw [← hx.2]
  exact single_le_sum (fun i _ => hx.1 i) (mem_univ j)

/-- Splitting `D(x‖v)` through an intermediate positive vector `y`:
`D(x‖v) - D(y‖v) = D(x‖y) + ∑ (x_j - y_j) log (y_j / v_j)`. -/
theorem relEnt_sub_relEnt {x y v : ι → ℝ} (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hv : ∀ j, 0 < v j) :
    relEnt x v - relEnt y v = relEnt x y + ∑ j, (x j - y j) * Real.log (y j / v j) := by
  unfold relEnt
  rw [← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hx0 := hx j; have hy0 := hy j; have hv0 := hv j
  have : Real.log (x j / v j) = Real.log (x j / y j) + Real.log (y j / v j) := by
    rw [← Real.log_mul (div_pos hx0 hy0).ne' (div_pos hy0 hv0).ne']
    congr 1
    field_simp
  rw [this]
  ring

/-- `D(x‖v) ≥ -log ∑_j v_j` for a positive probability vector `x` and `v > 0`. -/
theorem neg_log_sum_le_relEnt {x v : ι → ℝ} (hx : ∀ j, 0 < x j) (hsum : ∑ j, x j = 1)
    (hv : ∀ j, 0 < v j) : -Real.log (∑ j, v j) ≤ relEnt x v := by
  have hne : (univ : Finset ι).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, sum_empty] at hsum
    exact zero_ne_one hsum
  have hV : 0 < ∑ j, v j := sum_pos (fun j _ => hv j) hne
  set V := ∑ j, v j with hVdef
  have key : ∀ j, x j - v j / V - x j * Real.log V ≤ x j * Real.log (x j / v j) := by
    intro j
    have hx0 := hx j; have hv0 := hv j
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < x j * V / v j by positivity)
    have h2 : Real.log (x j * V / v j) = Real.log (x j / v j) + Real.log V := by
      rw [mul_div_right_comm, Real.log_mul (div_pos hx0 hv0).ne' hV.ne']
    rw [h2, inv_div] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hx0.le
    have e : x j * (1 - v j / (x j * V)) = x j - v j / V := by
      field_simp
    rw [e, mul_add] at h3
    linarith
  have := sum_le_sum (fun j (_ : j ∈ univ) => key j)
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_div, ← sum_mul, hsum, ← hVdef,
    div_self hV.ne'] at this
  unfold relEnt
  linarith

/-- `D(x‖v) = D(x‖v/∑v) - log ∑ v` for a positive probability vector `x` and `v > 0`. -/
theorem relEnt_eq_normalize_sub_log {x v : ι → ℝ} (hx : ∀ j, 0 < x j) (hsum : ∑ j, x j = 1)
    (hv : ∀ j, 0 < v j) (hV : 0 < ∑ j, v j) :
    relEnt x v = relEnt x (fun j => v j / ∑ i, v i) - Real.log (∑ j, v j) := by
  unfold relEnt
  have e : ∀ j, x j * Real.log (x j / v j) =
      x j * Real.log (x j / (v j / ∑ i, v i)) - x j * Real.log (∑ i, v i) := by
    intro j
    have hx0 := hx j; have hv0 := hv j
    have h1 : Real.log (x j / (v j / ∑ i, v i)) = Real.log (x j / v j) + Real.log (∑ i, v i) := by
      rw [← Real.log_mul (div_pos hx0 hv0).ne' hV.ne']
      congr 1
      field_simp
    rw [h1]
    ring
  rw [sum_congr rfl fun j _ => e j, sum_sub_distrib, ← sum_mul, hsum, one_mul]

/-- `D(x‖y) ≥ (1/2) ‖x - y‖₂²` for probability vectors with coordinates in `(0, 1]`. -/
theorem half_sum_sq_le_relEnt {x y : ι → ℝ} (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hxs : ∑ j, x j = 1) (hys : ∑ j, y j = 1) (hx1 : ∀ j, x j ≤ 1) (hy1 : ∀ j, y j ≤ 1) :
    (∑ j, (x j - y j) ^ 2) / 2 ≤ relEnt x y := by
  have := sum_le_sum (fun j (_ : j ∈ univ) => half_sq_le_mul_log (hx j) (hx1 j) (hy j) (hy1 j))
  rw [sum_add_distrib, sum_sub_distrib, hxs, hys, ← sum_div] at this
  unfold relEnt
  linarith

/-- The derivative of `t ↦ D(y + t d ‖ v)` at `t = 0` is `∑ d_j (log (y_j / v_j) + 1)`. -/
theorem hasDerivAt_relEnt_line {y d v : ι → ℝ} (hy : ∀ j, 0 < y j) (hv : ∀ j, 0 < v j) :
    HasDerivAt (fun t : ℝ => relEnt (fun j => y j + t * d j) v)
      (∑ j, d j * (Real.log (y j / v j) + 1)) 0 := by
  unfold relEnt
  apply HasDerivAt.fun_sum
  intro j _
  have hy0 := hy j; have hv0 := hv j
  have h1 : HasDerivAt (fun t : ℝ => y j + t * d j) (d j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d j)).const_add (y j)
  have h2 : HasDerivAt (fun t : ℝ => (y j + t * d j) / v j) (d j / v j) 0 := h1.div_const _
  have h3 := h2.log (by simpa using (div_pos hy0 hv0).ne')
  have h4 := h1.mul h3
  convert h4 using 1
  simp only [zero_mul, add_zero]
  field_simp

/-- First-order optimality: if `y_*` minimizes `D(·‖v)` over a convex set `K` containing `x`, the
directional derivative of `D(·‖v)` at `y_*` along `x - y_*` is nonnegative. -/
theorem firstOrder_nonneg {K : Set (ι → ℝ)} (hK : Convex ℝ K) {v ystar x : ι → ℝ}
    (hv : ∀ j, 0 < v j) (hys : ystar ∈ K) (hpos : ∀ j, 0 < ystar j)
    (hmin : ∀ y ∈ K, relEnt ystar v ≤ relEnt y v) (hx : x ∈ K) :
    0 ≤ ∑ j, (x j - ystar j) * (Real.log (ystar j / v j) + 1) := by
  refine deriv_nonneg_of_le (hasDerivAt_relEnt_line (d := fun j => x j - ystar j) hpos hv) ?_
  intro t ht
  have hmem := hK.add_smul_sub_mem hys hx ⟨ht.1.le, ht.2.le⟩
  have e : ystar + t • (x - ystar) = fun j => ystar j + t * (x j - ystar j) := by
    funext j; simp
  rw [e] at hmem
  simpa using hmin _ hmem

/-- The first-order inequality in the form used with probability vectors:
`∑ (x_j - y_{*,j}) log (y_{*,j} / v_j) ≥ 0`. -/
theorem firstOrder_nonneg' {K : Set (ι → ℝ)} (hK : Convex ℝ K) {v ystar x : ι → ℝ}
    (hv : ∀ j, 0 < v j) (hys : ystar ∈ K) (hpos : ∀ j, 0 < ystar j)
    (hmin : ∀ y ∈ K, relEnt ystar v ≤ relEnt y v) (hx : x ∈ K)
    (hxs : ∑ j, x j = 1) (hss : ∑ j, ystar j = 1) :
    0 ≤ ∑ j, (x j - ystar j) * Real.log (ystar j / v j) := by
  have h := firstOrder_nonneg hK hv hys hpos hmin hx
  simp only [mul_add, mul_one, sum_add_distrib, sum_sub_distrib, hxs, hss, sub_self,
    add_zero] at h
  exact h

/-- `D(·‖v)` is continuous when `v > 0`. -/
theorem continuous_relEnt {v : ι → ℝ} (hv : ∀ j, 0 < v j) :
    Continuous fun y : ι → ℝ => relEnt y v := by
  unfold relEnt
  refine continuous_finsetSum _ fun j _ => ?_
  have hv0 := hv j
  have e : (fun y : ι → ℝ => y j * Real.log (y j / v j)) =
      fun y => v j * ((y j / v j) * Real.log (y j / v j)) := by
    funext y; field_simp
  rw [e]
  exact continuous_const.mul (Real.continuous_mul_log.comp ((continuous_apply j).div_const _))

/-! ### The setting of `lem:approx-projection` -/

/-- The hypotheses of `lem:approx-projection` on the feasible set: `K` is convex, contained in the
probability simplex, and every coordinate is at least `μ > 0` on `K`. -/
structure Feasible (K : Set (ι → ℝ)) (μ : ℝ) : Prop where
  convex : Convex ℝ K
  prob : ∀ x ∈ K, ProbVec x
  floor_pos : 0 < μ
  floor : ∀ x ∈ K, ∀ j, μ ≤ x j

namespace Feasible

variable {K : Set (ι → ℝ)} {μ : ℝ}

theorem pos (hK : Feasible K μ) {x : ι → ℝ} (hx : x ∈ K) (j : ι) : 0 < x j :=
  hK.floor_pos.trans_le (hK.floor x hx j)

theorem le_one (hK : Feasible K μ) {x : ι → ℝ} (hx : x ∈ K) (j : ι) : x j ≤ 1 :=
  (hK.prob x hx).le_one j

theorem sum_eq_one (hK : Feasible K μ) {x : ι → ℝ} (hx : x ∈ K) : ∑ j, x j = 1 :=
  (hK.prob x hx).2

end Feasible

/-- On a compact nonempty feasible set a minimizer of `D(·‖v)` exists. -/
theorem exists_minimizer {K : Set (ι → ℝ)} (hc : IsCompact K) (hne : K.Nonempty) {v : ι → ℝ}
    (hv : ∀ j, 0 < v j) : ∃ ystar ∈ K, ∀ y ∈ K, relEnt ystar v ≤ relEnt y v :=
  hc.exists_isMinOn hne (continuous_relEnt hv).continuousOn

variable {K : Set (ι → ℝ)} {μ : ℝ} {v ystar y : ι → ℝ} {ζ : ℝ}

/-- `lem:approx-projection`, strong convexity step:
`D(y‖v) - D(y_*‖v) ≥ (1/2) ‖y - y_*‖₂²`. -/
theorem strongConvexity (hK : Feasible K μ) (hv : ∀ j, 0 < v j) (hys : ystar ∈ K)
    (hmin : ∀ y ∈ K, relEnt ystar v ≤ relEnt y v) (hy : y ∈ K) :
    (∑ j, (y j - ystar j) ^ 2) / 2 ≤ relEnt y v - relEnt ystar v := by
  rw [relEnt_sub_relEnt (hK.pos hy) (hK.pos hys) hv]
  have h1 := half_sum_sq_le_relEnt (hK.pos hy) (hK.pos hys) (hK.sum_eq_one hy)
    (hK.sum_eq_one hys) (hK.le_one hy) (hK.le_one hys)
  have h2 := firstOrder_nonneg' hK.convex hv hys (hK.pos hys) hmin hy (hK.sum_eq_one hy)
    (hK.sum_eq_one hys)
  linarith

/-- `lem:approx-projection`, sup-norm step: `‖y - y_*‖_∞ ≤ √(2ζ)`. -/
theorem abs_sub_le_sqrt (hK : Feasible K μ) (hv : ∀ j, 0 < v j) (hys : ystar ∈ K)
    (hmin : ∀ y ∈ K, relEnt ystar v ≤ relEnt y v) (hy : y ∈ K)
    (hζ : relEnt y v ≤ relEnt ystar v + ζ) (j : ι) :
    |y j - ystar j| ≤ Real.sqrt (2 * ζ) := by
  have h := strongConvexity hK hv hys hmin hy
  have hj : (y j - ystar j) ^ 2 ≤ ∑ i, (y i - ystar i) ^ 2 :=
    single_le_sum (fun i _ => sq_nonneg (y i - ystar i)) (mem_univ j)
  exact Real.abs_le_sqrt (by linarith)

/-- `lem:approx-projection`, exact projection inequality (three-point step):
`D(x‖y_*) ≤ D(x‖v) - D(y_*‖v)`. -/
theorem threePoint (hK : Feasible K μ) (hv : ∀ j, 0 < v j) (hys : ystar ∈ K)
    (hmin : ∀ y ∈ K, relEnt ystar v ≤ relEnt y v) {x : ι → ℝ} (hx : x ∈ K) :
    relEnt x ystar ≤ relEnt x v - relEnt ystar v := by
  rw [relEnt_sub_relEnt (hK.pos hx) (hK.pos hys) hv]
  have := firstOrder_nonneg' hK.convex hv hys (hK.pos hys) hmin hx (hK.sum_eq_one hx)
    (hK.sum_eq_one hys)
  linarith

/-- `D(x‖y) - D(x‖y_*) = ∑ x_j log (y_{*,j} / y_j)` for positive vectors. -/
theorem relEnt_sub_relEnt_left {x y ystar : ι → ℝ} (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hys : ∀ j, 0 < ystar j) :
    relEnt x y - relEnt x ystar = ∑ j, x j * Real.log (ystar j / y j) := by
  unfold relEnt
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  have hx0 := hx j; have hy0 := hy j; have hs0 := hys j
  have : Real.log (x j / y j) = Real.log (x j / ystar j) + Real.log (ystar j / y j) := by
    rw [← Real.log_mul (div_pos hx0 hs0).ne' (div_pos hs0 hy0).ne']
    congr 1
    field_simp
  rw [this]
  ring

/-- `lem:approx-projection`, last display:
`D(x‖y) - D(x‖y_*) ≤ max_j |log y_{*,j} - log y_j| ≤ √(2ζ)/μ`. -/
theorem relEnt_sub_le_max (hK : Feasible K μ) (hv : ∀ j, 0 < v j) (hys : ystar ∈ K)
    (hmin : ∀ y ∈ K, relEnt ystar v ≤ relEnt y v) (hy : y ∈ K)
    (hζ : relEnt y v ≤ relEnt ystar v + ζ) {x : ι → ℝ} (hx : x ∈ K)
    (hne : (univ : Finset ι).Nonempty) :
    relEnt x y - relEnt x ystar ≤
        univ.sup' hne (fun j => |Real.log (ystar j) - Real.log (y j)|) ∧
      univ.sup' hne (fun j => |Real.log (ystar j) - Real.log (y j)|) ≤
        Real.sqrt (2 * ζ) / μ := by
  set B := univ.sup' hne (fun j => |Real.log (ystar j) - Real.log (y j)|) with hB
  constructor
  · rw [relEnt_sub_relEnt_left (hK.pos hx) (hK.pos hy) (hK.pos hys)]
    calc ∑ j, x j * Real.log (ystar j / y j) ≤ ∑ j, x j * B := by
          refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hK.pos hx j).le
          rw [Real.log_div (hK.pos hys j).ne' (hK.pos hy j).ne']
          exact (le_abs_self _).trans (le_sup' (fun j => |Real.log (ystar j) - Real.log (y j)|)
            (mem_univ j))
      _ = B := by rw [← sum_mul, hK.sum_eq_one hx, one_mul]
  · refine sup'_le _ _ fun j _ => ?_
    refine (abs_log_sub_log_le hK.floor_pos (hK.floor _ hys j) (hK.floor _ hy j)).trans ?_
    have := abs_sub_le_sqrt hK hv hys hmin hy hζ j
    rw [abs_sub_comm] at this
    exact div_le_div_of_nonneg_right this hK.floor_pos.le

/-- `lem:approx-projection`. Let `K` be a convex subset of the probability simplex on which every
coordinate is at least `μ > 0`, let `v > 0`, let `y_*` minimize `D(·‖v)` over `K`, and let `y ∈ K`
satisfy `D(y‖v) ≤ D(y_*‖v) + ζ`. Then `D(x‖y) ≤ D(x‖v) + log ∑_j v_j + √(2ζ)/μ` for every
`x ∈ K`. Compactness of `K` is only used for the existence of `y_*` (`exists_minimizer`). -/
theorem approx_projection (hK : Feasible K μ) (hv : ∀ j, 0 < v j) (hys : ystar ∈ K)
    (hmin : ∀ y ∈ K, relEnt ystar v ≤ relEnt y v) (hy : y ∈ K)
    (hζ : relEnt y v ≤ relEnt ystar v + ζ) :
    ∀ x ∈ K, relEnt x y ≤ relEnt x v + Real.log (∑ j, v j) + Real.sqrt (2 * ζ) / μ := by
  intro x hx
  have hne : (univ : Finset ι).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hK.sum_eq_one hx
    rw [h, sum_empty] at this
    exact zero_ne_one this
  have h1 := relEnt_sub_le_max hK hv hys hmin hy hζ hx hne
  have h2 := threePoint hK hv hys hmin hx
  have h3 := neg_log_sum_le_relEnt (hK.pos hys) (hK.sum_eq_one hys) hv
  linarith [h1.1, h1.2]

/-- `lem:approx-projection` with compactness as in the paper: on a compact nonempty feasible set a
minimizer exists, and every `ζ`-optimal feasible point satisfies the projection inequality. -/
theorem approx_projection_compact (hK : Feasible K μ) (hc : IsCompact K) (hne : K.Nonempty)
    (hv : ∀ j, 0 < v j) :
    ∃ ystar ∈ K, (∀ y ∈ K, relEnt ystar v ≤ relEnt y v) ∧
      ∀ y ∈ K, ∀ ζ : ℝ, relEnt y v ≤ relEnt ystar v + ζ →
        ∀ x ∈ K, relEnt x y ≤ relEnt x v + Real.log (∑ j, v j) + Real.sqrt (2 * ζ) / μ := by
  obtain ⟨ystar, hys, hmin⟩ := exists_minimizer hc hne hv
  exact ⟨ystar, hys, hmin, fun y hy ζ hζ => approx_projection hK hv hys hmin hy hζ⟩

/-- The tolerance remark after `lem:approx-projection`: `ζ ≤ μ²τ²/2` gives additive error `τ`. -/
theorem sqrt_div_le_of_tolerance {μ τ ζ : ℝ} (hμ : 0 < μ) (hτ : 0 ≤ τ)
    (hζ : ζ ≤ μ ^ 2 * τ ^ 2 / 2) : Real.sqrt (2 * ζ) / μ ≤ τ := by
  rw [div_le_iff₀ hμ]
  calc Real.sqrt (2 * ζ) ≤ Real.sqrt ((μ * τ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = τ * μ := by rw [Real.sqrt_sq (by positivity)]; ring

/-- `lem:approx-projection` with objective tolerance `ζ ≤ μ²τ²/2`: additive error `τ`. -/
theorem approx_projection_tau (hK : Feasible K μ) (hv : ∀ j, 0 < v j) (hys : ystar ∈ K)
    (hmin : ∀ y ∈ K, relEnt ystar v ≤ relEnt y v) (hy : y ∈ K) {τ : ℝ} (hτ : 0 ≤ τ)
    (hζ' : ζ ≤ μ ^ 2 * τ ^ 2 / 2) (hζ : relEnt y v ≤ relEnt ystar v + ζ) :
    ∀ x ∈ K, relEnt x y ≤ relEnt x v + Real.log (∑ j, v j) + τ := fun x hx => by
  have := approx_projection hK hv hys hmin hy hζ x hx
  have := sqrt_div_le_of_tolerance hK.floor_pos hτ hζ'
  linarith

end RelEnt

/-! ### Non-vacuity of the hypotheses of `lem:approx-projection` -/

/-- A feasible set satisfying the hypotheses of `lem:approx-projection`. -/
theorem feasible_singleton :
    Feasible ({fun _ : Fin 2 => (1 / 2 : ℝ)} : Set (Fin 2 → ℝ)) (1 / 2) where
  convex := convex_singleton _
  prob := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨fun _ => by norm_num, ?_⟩
    simp only [Fin.sum_univ_two]
    norm_num
  floor_pos := by norm_num
  floor := by
    intro x hx j
    rw [Set.mem_singleton_iff] at hx
    subst hx
    norm_num

example : ∀ x ∈ ({fun _ : Fin 2 => (1 / 2 : ℝ)} : Set (Fin 2 → ℝ)),
    relEnt x (fun _ => (1 / 2 : ℝ)) ≤ relEnt x (fun _ => 1) + Real.log (∑ _j : Fin 2, (1 : ℝ)) +
      Real.sqrt (2 * 0) / (1 / 2) :=
  approx_projection feasible_singleton (fun _ => one_pos) rfl
    (fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]) rfl (by simp)

end LowLogitRank.Projection
