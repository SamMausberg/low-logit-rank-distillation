import LowLogitRank.Projection

/-!
# The exactly feasible ellipsoid implementation (`sec:finite-bit-lm`)

The deterministic inequalities behind the ellipsoid paragraphs of `sec:finite-bit-lm`: the
approximate central cut and the acceptance test, the inner ball near an optimizer, the stopping
rule of the binary search, and the rounding step of "Uniform bit length of the generated state".
The finite-bit ellipsoid theorem itself is cited and not formalized.
-/

namespace LowLogitRank.Projection

open Finset Set Metric InnerProductSpace
open scoped RealInnerProductSpace

/-! ### Central cut and acceptance -/

section Cut

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Gradient inequality for a convex function: `⟪∇F(u), x - u⟫ ≤ F(x) - F(u)`. -/
theorem inner_gradient_le_of_convexOn {C : Set E} {F : E → ℝ} (hF : ConvexOn ℝ C F)
    {u x gF : E} (hu : u ∈ C) (hx : x ∈ C) (hg : HasGradientAt F gF u) :
    ⟪gF, x - u⟫ ≤ F x - F u := by
  have hline : HasDerivAt (fun t : ℝ => u + t • (x - u)) (x - u) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x - u)).const_add u
  have hcomp : HasDerivAt (fun t : ℝ => F (u + t • (x - u))) (toDual ℝ E gF (x - u)) 0 :=
    hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  rw [toDual_apply_apply] at hcomp
  refine deriv_le_of_le_add_mul hcomp fun t ht => ?_
  have h := hF.2 hu hx (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
  have e : (1 - t) • u + t • x = u + t • (x - u) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [e] at h
  simp only [smul_eq_mul] at h
  simp only [zero_smul, add_zero]
  linarith

/-- Ellipsoid paragraph of `sec:finite-bit-lm`, central cut: if `F` is convex with gradient `∇F(u)`
at the center `u`, `|f - F(u)| ≤ κ/16`, `‖g - ∇F(u)‖ ≤ κ/(16(D₀+1))`, and `x` is feasible with
`‖x - u‖ ≤ D₀` and `F(x) ≤ b₀`, then
`⟪g, x - u⟫ ≤ b₀ - F(u) + κD₀/(16(D₀+1)) ≤ b₀ - f + κ/8`. -/
theorem centralCut {C : Set E} {F : E → ℝ} (hF : ConvexOn ℝ C F) {u x gF g : E} (hu : u ∈ C)
    (hx : x ∈ C) (hgrad : HasGradientAt F gF u) {f κ D₀ b₀ : ℝ} (hf : |f - F u| ≤ κ / 16)
    (hg : ‖g - gF‖ ≤ κ / (16 * (D₀ + 1))) (hxu : ‖x - u‖ ≤ D₀) (hFx : F x ≤ b₀) :
    ⟪g, x - u⟫ ≤ b₀ - F u + κ * D₀ / (16 * (D₀ + 1)) ∧
      b₀ - F u + κ * D₀ / (16 * (D₀ + 1)) ≤ b₀ - f + κ / 8 := by
  have hD : 0 ≤ D₀ := (norm_nonneg _).trans hxu
  have hκ : 0 ≤ κ := by have := (abs_nonneg _).trans hf; linarith
  have h1 := inner_gradient_le_of_convexOn hF hu hx hgrad
  have h2 : ⟪g - gF, x - u⟫ ≤ κ / (16 * (D₀ + 1)) * D₀ :=
    (real_inner_le_norm _ _).trans (mul_le_mul hg hxu (norm_nonneg _) (by positivity))
  have e : ⟪g, x - u⟫ = ⟪gF, x - u⟫ + ⟪g - gF, x - u⟫ := by rw [inner_sub_left]; ring
  constructor
  · rw [e]
    have : κ / (16 * (D₀ + 1)) * D₀ = κ * D₀ / (16 * (D₀ + 1)) := by ring
    linarith
  · have h3 : κ * D₀ / (16 * (D₀ + 1)) ≤ κ / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h4 := (abs_le.1 hf).2
    linarith

/-- Central cut, rejection case: if moreover `f > b₀ + κ/4`, the cut `⟪g, x - u⟫ ≤ 0` holds
strictly at every feasible `x` with `‖x - u‖ ≤ D₀` and `F(x) ≤ b₀`. -/
theorem centralCut_lt {C : Set E} {F : E → ℝ} (hF : ConvexOn ℝ C F) {u x gF g : E} (hu : u ∈ C)
    (hx : x ∈ C) (hgrad : HasGradientAt F gF u) {f κ D₀ b₀ : ℝ} (hf : |f - F u| ≤ κ / 16)
    (hg : ‖g - gF‖ ≤ κ / (16 * (D₀ + 1))) (hxu : ‖x - u‖ ≤ D₀) (hFx : F x ≤ b₀)
    (hrej : b₀ + κ / 4 < f) : ⟪g, x - u⟫ ≤ b₀ - f + κ / 8 ∧ b₀ - f + κ / 8 < 0 := by
  obtain ⟨h1, h2⟩ := centralCut hF hu hx hgrad hf hg hxu hFx
  have hκ : 0 ≤ κ := by have := (abs_nonneg _).trans hf; linarith
  exact ⟨h1.trans h2, by linarith⟩

/-- Central cut with `g = 0`: on rejection the `b₀`-sublevel set within distance `D₀` is empty. -/
theorem sublevel_empty_of_zero_cut {C : Set E} {F : E → ℝ} (hF : ConvexOn ℝ C F) {u gF : E}
    (hu : u ∈ C) (hgrad : HasGradientAt F gF u) {f κ D₀ b₀ : ℝ} (hf : |f - F u| ≤ κ / 16)
    (hg : ‖(0 : E) - gF‖ ≤ κ / (16 * (D₀ + 1))) (hrej : b₀ + κ / 4 < f) :
    ∀ x ∈ C, ‖x - u‖ ≤ D₀ → b₀ < F x := by
  intro x hx hxu
  by_contra hcon
  have := (centralCut_lt hF hu hx hgrad hf hg hxu (not_lt.1 hcon) hrej)
  rw [inner_zero_left] at this
  linarith [this.1, this.2]

/-- Acceptance test: `|f - F(u)| ≤ κ/16` and `f ≤ b₀ + κ/4` give
`F(u) ≤ f + κ/16 ≤ b₀ + 5κ/16`. -/
theorem accept_le {f Fu κ b₀ : ℝ} (hf : |f - Fu| ≤ κ / 16) (hacc : f ≤ b₀ + κ / 4) :
    Fu ≤ f + κ / 16 ∧ f + κ / 16 ≤ b₀ + 5 * κ / 16 := by
  have := (abs_le.1 hf).1
  constructor <;> linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- With `D₀ = 2R₀`, any two points of `B(0, R₀)` are within distance `D₀`. -/
theorem norm_sub_le_two_mul {x u : E} {R₀ : ℝ} (hx : x ∈ closedBall (0 : E) R₀)
    (hu : u ∈ closedBall (0 : E) R₀) : ‖x - u‖ ≤ 2 * R₀ := by
  rw [mem_closedBall_zero_iff] at hx hu
  calc ‖x - u‖ ≤ ‖x‖ + ‖u‖ := norm_sub_le _ _
    _ ≤ 2 * R₀ := by linarith

end Cut

/-! ### Inner ball near an optimizer -/

section Ball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The step `λ = min {1/2, κ / (4 (L₂+1)(D₀+r₀+1))}`. -/
noncomputable def ballStep (κ L₂ D₀ r₀ : ℝ) : ℝ := min (1 / 2) (κ / (4 * (L₂ + 1) * (D₀ + r₀ + 1)))

/-- Ellipsoid paragraph of `sec:finite-bit-lm`, inner ball: let `A` be convex with
`B(u₀, r₀) ⊆ A`, `u_* ∈ A`, `‖u₀ - u_*‖ ≤ D₀`, and let `F` be `L₂`-Lipschitz on `A`. With
`λ = ballStep κ L₂ D₀ r₀` and `u_λ = (1-λ)u_* + λu₀`, the ball `B(u_λ, λr₀)` lies in `A`, and
throughout it `F(u) ≤ F(u_*) + λ L₂ (D₀ + r₀) ≤ F(u_*) + κ/4`. -/
theorem innerBall {A : Set E} (hA : Convex ℝ A) {F : E → ℝ} {L₂ κ D₀ r₀ : ℝ} (hL : 0 ≤ L₂)
    (hκ : 0 < κ) (hr : 0 < r₀) (hLip : ∀ a ∈ A, ∀ b ∈ A, |F a - F b| ≤ L₂ * ‖a - b‖)
    {u₀ ustar : E} (hball : closedBall u₀ r₀ ⊆ A) (hstar : ustar ∈ A)
    (hD : ‖u₀ - ustar‖ ≤ D₀) :
    0 < ballStep κ L₂ D₀ r₀ ∧
      closedBall ((1 - ballStep κ L₂ D₀ r₀) • ustar + ballStep κ L₂ D₀ r₀ • u₀)
        (ballStep κ L₂ D₀ r₀ * r₀) ⊆ A ∧
      ∀ u ∈ closedBall ((1 - ballStep κ L₂ D₀ r₀) • ustar + ballStep κ L₂ D₀ r₀ • u₀)
          (ballStep κ L₂ D₀ r₀ * r₀),
        F u ≤ F ustar + ballStep κ L₂ D₀ r₀ * L₂ * (D₀ + r₀) ∧
          ballStep κ L₂ D₀ r₀ * L₂ * (D₀ + r₀) ≤ κ / 4 := by
  set lam := ballStep κ L₂ D₀ r₀ with hlam
  have hD0 : 0 ≤ D₀ := (norm_nonneg _).trans hD
  have hlam0 : 0 < lam := lt_min (by norm_num) (by positivity)
  have hlam1 : lam ≤ 1 / 2 := min_le_left _ _
  have hlam2 : lam ≤ κ / (4 * (L₂ + 1) * (D₀ + r₀ + 1)) := min_le_right _ _
  -- every point of the small ball is `(1-λ) u_* + λ w` with `w ∈ B(u₀, r₀)`
  have decomp : ∀ u ∈ closedBall ((1 - lam) • ustar + lam • u₀) (lam * r₀),
      ∃ w ∈ closedBall u₀ r₀, u = (1 - lam) • ustar + lam • w := by
    intro u hu
    refine ⟨u₀ + lam⁻¹ • (u - ((1 - lam) • ustar + lam • u₀)), ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hlam0, inv_mul_le_iff₀ hlam0, ← dist_eq_norm]
      exact hu
    · rw [smul_add, smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul]
      abel
  have hsub : closedBall ((1 - lam) • ustar + lam • u₀) (lam * r₀) ⊆ A := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := decomp u hu
    exact hA hstar (hball hw) (by linarith) hlam0.le (by ring)
  have hkey : lam * L₂ * (D₀ + r₀) ≤ κ / 4 := by
    have h1 : lam * L₂ * (D₀ + r₀) ≤ κ / (4 * (L₂ + 1) * (D₀ + r₀ + 1)) * L₂ * (D₀ + r₀) := by
      gcongr
    have h2 : κ / (4 * (L₂ + 1) * (D₀ + r₀ + 1)) * L₂ * (D₀ + r₀) ≤ κ / 4 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : L₂ * (D₀ + r₀) ≤ (L₂ + 1) * (D₀ + r₀ + 1) := by nlinarith
      nlinarith
    linarith
  refine ⟨hlam0, hsub, fun u hu => ⟨?_, hkey⟩⟩
  obtain ⟨w, hw, hwu⟩ := decomp u hu
  have hdist : ‖u - ustar‖ ≤ lam * (D₀ + r₀) := by
    have e : u - ustar = lam • (w - ustar) := by
      rw [hwu, smul_sub, sub_smul, one_smul]; abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
    gcongr
    calc ‖w - ustar‖ ≤ ‖w - u₀‖ + ‖u₀ - ustar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ r₀ + D₀ := by
          gcongr
          · rw [← dist_eq_norm]; exact hw
      _ = D₀ + r₀ := by ring
  have hl := (abs_le.1 (hLip u (hsub hu) ustar hstar)).2
  have : L₂ * ‖u - ustar‖ ≤ L₂ * (lam * (D₀ + r₀)) := mul_le_mul_of_nonneg_left hdist hL
  nlinarith

/-- Consequence used with the ellipsoid theorem: if `b₀ ≥ F(u_*) + κ/2`, every point of the inner
ball has `F(u) ≤ b₀ - κ/4`, and every estimate `f` with `|f - F(u)| ≤ κ/16` passes the acceptance
test `f ≤ b₀ + κ/4`. -/
theorem innerBall_accept {A : Set E} (hA : Convex ℝ A) {F : E → ℝ} {L₂ κ D₀ r₀ b₀ : ℝ}
    (hL : 0 ≤ L₂) (hκ : 0 < κ) (hr : 0 < r₀)
    (hLip : ∀ a ∈ A, ∀ b ∈ A, |F a - F b| ≤ L₂ * ‖a - b‖) {u₀ ustar : E}
    (hball : closedBall u₀ r₀ ⊆ A) (hstar : ustar ∈ A) (hD : ‖u₀ - ustar‖ ≤ D₀)
    (hb₀ : F ustar + κ / 2 ≤ b₀) :
    ∀ u ∈ closedBall ((1 - ballStep κ L₂ D₀ r₀) • ustar + ballStep κ L₂ D₀ r₀ • u₀)
        (ballStep κ L₂ D₀ r₀ * r₀),
      F u ≤ b₀ - κ / 4 ∧ ∀ f : ℝ, |f - F u| ≤ κ / 16 → f ≤ b₀ + κ / 4 := by
  intro u hu
  obtain ⟨-, -, h⟩ := innerBall hA hL hκ hr hLip hball hstar hD
  obtain ⟨h1, h2⟩ := h u hu
  refine ⟨by linarith, fun f hf => ?_⟩
  have := (abs_le.1 hf).2
  linarith

end Ball

/-! ### Binary search -/

/-- Binary search, update rules: with trial level `b₀ = (lo + hi)/2` and width `W = hi - lo ≥ 4κ`,
acceptance (new upper end `f + κ/16` with `f ≤ b₀ + κ/4`) and rejection (new lower end
`b₀ - κ/2`) both leave width at most `5W/8`. -/
theorem binarySearch_contract {κ lo hi : ℝ} (hκ : 0 ≤ κ) (hW : 4 * κ ≤ hi - lo) :
    (∀ f : ℝ, f ≤ (lo + hi) / 2 + κ / 4 → f + κ / 16 - lo ≤ 5 / 8 * (hi - lo)) ∧
      hi - ((lo + hi) / 2 - κ / 2) ≤ 5 / 8 * (hi - lo) := by
  constructor
  · intro f hf; linarith
  · linarith

/-- Binary search, stopping rule (`sec:finite-bit-lm`): with `κ = ζ/100`, a lower end `lo ≤ F(u_*)`,
a certified upper end `F(û) ≤ hi`, and width `hi - lo ≤ 4κ`, the returned point is within `ζ/2` of
optimal, since `4κ = ζ/25 < ζ/2`. -/
theorem binarySearch_stop {ζ lo hi Fopt Fret : ℝ} (hζ : 0 < ζ) (hlo : lo ≤ Fopt)
    (hhi : Fret ≤ hi) (hw : hi - lo ≤ 4 * (ζ / 100)) :
    4 * (ζ / 100) = ζ / 25 ∧ ζ / 25 < ζ / 2 ∧ Fret ≤ Fopt + ζ / 2 := by
  refine ⟨by ring, by linarith, by linarith⟩

/-! ### Rounding to a fixed dyadic mesh -/

section Rounding

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear functional on `ι → ℝ` is the sum of its partial derivatives times the coordinates. -/
theorem clm_apply_eq_sum (L : (ι → ℝ) →L[ℝ] ℝ) (w : ι → ℝ) :
    L w = ∑ i, w i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  refine sum_congr rfl fun i _ => ?_
  have : Pi.single i (w i) = w i • (Pi.single i 1 : ι → ℝ) := by
    ext j; by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- `sec:finite-bit-lm`, mean value bound for the rounding step: if `F` is differentiable along
the segment `[a, b]`, every partial derivative is bounded by `mG` there, and `|a_i - b_i| ≤ h₀`
for every coordinate, then `|F(a) - F(b)| ≤ s · mG · h₀`, `s` the number of coordinates. -/
theorem abs_sub_le_of_partial_le {F : (ι → ℝ) → ℝ} {F' : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ}
    {a b : ι → ℝ} (hF : ∀ z ∈ segment ℝ a b, HasFDerivAt F (F' z) z) {mG h₀ : ℝ}
    (hpart : ∀ z ∈ segment ℝ a b, ∀ i, |F' z (Pi.single i 1)| ≤ mG)
    (hab : ∀ i, |a i - b i| ≤ h₀) :
    |F a - F b| ≤ Fintype.card ι * mG * h₀ := by
  set φ : ℝ → ℝ := fun t => F (b + t • (a - b)) with hφ
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, b + t • (a - b) ∈ segment ℝ a b := by
    intro t ht
    rw [segment_symm, segment_eq_image']
    exact ⟨t, ht, rfl⟩
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt φ (F' (b + t • (a - b)) (a - b)) t := by
    intro t ht
    have hline : HasDerivAt (fun t : ℝ => b + t • (a - b)) (a - b) t := by
      simpa using ((hasDerivAt_id t).smul_const (a - b)).const_add b
    exact (hF _ (hmem t ht)).comp_hasDerivAt t hline
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖F' (b + t • (a - b)) (a - b)‖ ≤
      Fintype.card ι * mG * h₀ := by
    intro t ht
    have hz := hmem t (Ico_subset_Icc_self ht)
    rw [Real.norm_eq_abs, clm_apply_eq_sum]
    calc |∑ i, (a - b) i * F' (b + t • (a - b)) (Pi.single i 1)|
        ≤ ∑ i, |(a - b) i * F' (b + t • (a - b)) (Pi.single i 1)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, h₀ * mG := by
          refine sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hab i) (hpart _ hz i) (abs_nonneg _) ((abs_nonneg _).trans (hab i))
      _ = Fintype.card ι * mG * h₀ := by rw [sum_const, nsmul_eq_mul, card_univ]; ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ)
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound 1 ⟨zero_le_one, le_rfl⟩
  simpa [hφ] using this

/-- `sec:finite-bit-lm`: the mesh condition `h₀ ≤ ζ / (4 s (mG + 1))` gives `s · mG · h₀ ≤ ζ/4`. -/
theorem mesh_bound {s mG h₀ ζ : ℝ} (hs : 0 < s) (hmG : 0 ≤ mG) (hh0 : 0 ≤ h₀)
    (hh : h₀ ≤ ζ / (4 * s * (mG + 1))) : s * mG * h₀ ≤ ζ / 4 := by
  rw [le_div_iff₀ (by positivity)] at hh
  have : s * mG * h₀ * 4 ≤ h₀ * (4 * s * (mG + 1)) := by nlinarith
  linarith

/-- `sec:finite-bit-lm`, "Uniform bit length of the generated state": if `α̂` is `ζ/2`-optimal,
`α_r` differs from it by at most `h₀ ≤ ζ / (4s(mG+1))` in every coordinate, and the partial
derivatives of `F` are bounded by `mG` on the segment, then `|F(α_r) - F(α̂)| ≤ s·mG·h₀ ≤ ζ/4`
and `α_r` is `ζ`-optimal. -/
theorem rounding_optimal {F : (ι → ℝ) → ℝ} {F' : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ}
    {αr αhat : ι → ℝ} (hF : ∀ z ∈ segment ℝ αr αhat, HasFDerivAt F (F' z) z) {mG h₀ ζ Fopt : ℝ}
    (hpart : ∀ z ∈ segment ℝ αr αhat, ∀ i, |F' z (Pi.single i 1)| ≤ mG)
    (hmG : 0 ≤ mG) (hne : Nonempty ι) (hh0 : 0 ≤ h₀)
    (hh : h₀ ≤ ζ / (4 * Fintype.card ι * (mG + 1))) (hab : ∀ i, |αr i - αhat i| ≤ h₀)
    (hopt : F αhat ≤ Fopt + ζ / 2) :
    |F αr - F αhat| ≤ Fintype.card ι * mG * h₀ ∧ Fintype.card ι * mG * h₀ ≤ ζ / 4 ∧
      F αr ≤ Fopt + ζ := by
  have h1 := abs_sub_le_of_partial_le hF hpart hab
  have hs : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h2 := mesh_bound hs hmG hh0 hh
  have hζ : 0 ≤ ζ := by
    by_contra hc
    rw [not_le] at hc
    have : ζ / (4 * Fintype.card ι * (mG + 1)) < 0 := div_neg_of_neg_of_pos hc (by positivity)
    linarith
  refine ⟨h1, h2, ?_⟩
  have := (abs_le.1 h1).2
  linarith

end Rounding

/-! ### The objective `F(α) = D(Rᵀα‖v)` and its partial derivatives -/

section Objective

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq σ]

/-- The coordinate map `α ↦ y_j(α) = (Rᵀα)_j = ∑_i α_i R_{ij}`. -/
noncomputable def coordMap (R : σ → ι → ℝ) (j : ι) : (σ → ℝ) →L[ℝ] ℝ :=
  ∑ i, R i j • ContinuousLinearMap.proj i

omit [Fintype ι] [DecidableEq σ] in
theorem coordMap_apply (R : σ → ι → ℝ) (j : ι) (α : σ → ℝ) :
    coordMap R j α = ∑ i, α i * R i j := by
  simp [coordMap, mul_comm]

/-- The objective `F(α) = D(y(α)‖v)` with `y(α) = Rᵀα`. -/
noncomputable def objective (R : σ → ι → ℝ) (v : ι → ℝ) (α : σ → ℝ) : ℝ :=
  relEnt (fun j => coordMap R j α) v

/-- The derivative of the objective: `w ↦ ∑_j (log (y_j/v_j) + 1) (Rᵀw)_j`. -/
noncomputable def objectiveDeriv (R : σ → ι → ℝ) (v : ι → ℝ) (α : σ → ℝ) :
    (σ → ℝ) →L[ℝ] ℝ :=
  ∑ j, (Real.log (coordMap R j α / v j) + 1) • coordMap R j

/-- `t ↦ t log (t/v)` has derivative `log (t/v) + 1` at `t > 0`. -/
theorem hasDerivAt_mul_log_div {t w : ℝ} (ht : 0 < t) (hw : 0 < w) :
    HasDerivAt (fun t : ℝ => t * Real.log (t / w)) (Real.log (t / w) + 1) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / w) (1 / w) t := (hasDerivAt_id t).div_const w
  have h2 := h1.log (by simpa using (div_pos ht hw).ne')
  have h3 := (hasDerivAt_id' t).mul h2
  convert h3 using 1
  field_simp

omit [DecidableEq σ] in
theorem hasFDerivAt_objective {R : σ → ι → ℝ} {v : ι → ℝ} {α : σ → ℝ}
    (hy : ∀ j, 0 < coordMap R j α) (hv : ∀ j, 0 < v j) :
    HasFDerivAt (objective R v) (objectiveDeriv R v α) α := by
  unfold objective relEnt objectiveDeriv
  apply HasFDerivAt.fun_sum
  intro j _
  exact (hasDerivAt_mul_log_div (hy j) (hv j)).comp_hasFDerivAt α (coordMap R j).hasFDerivAt

/-- The partial derivatives `∂F/∂α_i = ∑_j R_{ij} (log (y_j/v_j) + 1)`. -/
theorem objectiveDeriv_single (R : σ → ι → ℝ) (v : ι → ℝ) (α : σ → ℝ) (i : σ) :
    objectiveDeriv R v α (Pi.single i 1) =
      ∑ j, R i j * (Real.log (coordMap R j α / v j) + 1) := by
  have hc : ∀ j, coordMap R j (Pi.single i 1) = R i j := by
    intro j
    rw [coordMap_apply]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  unfold objectiveDeriv
  rw [_root_.sum_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [smul_apply, hc, smul_eq_mul, mul_comm]

/-- `sec:finite-bit-lm`: if `|R_{ij}| ≤ 1` and `|log (y_j/v_j) + 1| ≤ G`, every partial derivative
of `F` with respect to a coefficient has magnitude at most `m G`, `m = |ι|`. -/
theorem abs_objectiveDeriv_single_le {R : σ → ι → ℝ} {v : ι → ℝ} {α : σ → ℝ} {G : ℝ}
    (hR : ∀ i j, |R i j| ≤ 1) (hG : ∀ j, |Real.log (coordMap R j α / v j) + 1| ≤ G) (i : σ) :
    |objectiveDeriv R v α (Pi.single i 1)| ≤ Fintype.card ι * G := by
  rw [objectiveDeriv_single]
  calc |∑ j, R i j * (Real.log (coordMap R j α / v j) + 1)|
      ≤ ∑ j, |R i j * (Real.log (coordMap R j α / v j) + 1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, G := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        have := hR i j; have := hG j
        nlinarith [abs_nonneg (R i j), abs_nonneg (Real.log (coordMap R j α / v j) + 1)]
    _ = Fintype.card ι * G := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- `sec:finite-bit-lm`: with `y ∈ [μ, 1]` and `v ∈ [μ, V]`, `V ≥ 1`, the bound
`|log (y/v) + 1| ≤ G = 1 + log (V/μ)` holds. -/
theorem abs_log_div_add_one_le {y w μ V : ℝ} (hμ : 0 < μ) (hy0 : μ ≤ y) (hy1 : y ≤ 1)
    (hw0 : μ ≤ w) (hw1 : w ≤ V) (hV : 1 ≤ V) :
    |Real.log (y / w) + 1| ≤ 1 + Real.log (V / μ) := by
  have hy : 0 < y := hμ.trans_le hy0
  have hw : 0 < w := hμ.trans_le hw0
  have hup : Real.log (y / w) ≤ Real.log (V / μ) := by
    apply Real.log_le_log (div_pos hy hw)
    rw [div_le_div_iff₀ hw hμ]
    nlinarith
  have hlo : -Real.log (V / μ) ≤ Real.log (y / w) := by
    rw [← Real.log_inv, inv_div]
    apply Real.log_le_log (div_pos hμ (by linarith))
    rw [div_le_div_iff₀ (by linarith) hw]
    nlinarith
  have hVμ : 0 ≤ Real.log (V / μ) := Real.log_nonneg (by rw [le_div_iff₀ hμ]; linarith)
  rw [abs_le]; constructor <;> linarith

omit [DecidableEq σ] in
/-- `sec:finite-bit-lm`, "Uniform bit length of the generated state", for the objective
`F(α) = D(Rᵀα‖v)`. Let `𝒜` be convex with `y(α) ∈ [μ, 1]` on `𝒜`, `v ∈ [μ, V]`, `V ≥ 1`,
`|R_{ij}| ≤ 1`, and `G = 1 + log (V/μ)`. If `α̂, α_r ∈ 𝒜` differ by at most `h₀ ≤ ζ / (4s(mG+1))`
in each coordinate and `α̂` is `ζ/2`-optimal, then `|F(α_r) - F(α̂)| ≤ s m G h₀ ≤ ζ/4` and `α_r`
is `ζ`-optimal. -/
theorem objective_rounding {R : σ → ι → ℝ} {v : ι → ℝ} {𝒜 : Set (σ → ℝ)} (h𝒜 : Convex ℝ 𝒜)
    {μ V h₀ ζ Fopt : ℝ} (hμ : 0 < μ) (hV : 1 ≤ V) (hR : ∀ i j, |R i j| ≤ 1)
    (hyA : ∀ α ∈ 𝒜, ∀ j, μ ≤ coordMap R j α ∧ coordMap R j α ≤ 1)
    (hv : ∀ j, μ ≤ v j ∧ v j ≤ V) (hne : Nonempty σ) {αr αhat : σ → ℝ} (hr : αr ∈ 𝒜)
    (hhat : αhat ∈ 𝒜) (hh0 : 0 ≤ h₀)
    (hh : h₀ ≤ ζ / (4 * Fintype.card σ * (Fintype.card ι * (1 + Real.log (V / μ)) + 1)))
    (hab : ∀ i, |αr i - αhat i| ≤ h₀) (hopt : objective R v αhat ≤ Fopt + ζ / 2) :
    |objective R v αr - objective R v αhat| ≤
        Fintype.card σ * (Fintype.card ι * (1 + Real.log (V / μ))) * h₀ ∧
      Fintype.card σ * (Fintype.card ι * (1 + Real.log (V / μ))) * h₀ ≤ ζ / 4 ∧
      objective R v αr ≤ Fopt + ζ := by
  classical
  have hseg : segment ℝ αr αhat ⊆ 𝒜 := h𝒜.segment_subset hr hhat
  have hmG : 0 ≤ (Fintype.card ι : ℝ) * (1 + Real.log (V / μ)) := by
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨j⟩⟩
    · simp
    · have h1 := hyA αr hr j
      have hVμ : 0 ≤ Real.log (V / μ) := Real.log_nonneg (by rw [le_div_iff₀ hμ]; linarith)
      positivity
  refine rounding_optimal (F' := objectiveDeriv R v) (fun z hz => ?_) (fun z hz i => ?_)
    hmG hne hh0 hh hab hopt
  · exact hasFDerivAt_objective (fun j => hμ.trans_le (hyA z (hseg hz) j).1)
      (fun j => hμ.trans_le (hv j).1)
  · exact abs_objectiveDeriv_single_le hR (fun j => abs_log_div_add_one_le hμ
      (hyA z (hseg hz) j).1 (hyA z (hseg hz) j).2 (hv j).1 (hv j).2 hV) i

end Objective

end LowLogitRank.Projection
