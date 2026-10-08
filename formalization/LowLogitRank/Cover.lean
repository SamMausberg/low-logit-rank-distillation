import LowLogitRank.MaxVolume

/-!
# The finite parameter grid of `sec:sample-upper`

Error propagation through rounded transitions and readouts (`eq:mesh`), the bounded grids and the
count `eq:coverN`, and the existence of a grid candidate whose logits are within `ρ` of the
teacher's.
-/

namespace LowLogitRank.Cover

open Finset Matrix LowLogitRank.MaxVolume

/-! ### Error propagation, `eq:mesh` -/

/-- One step of `eq:mesh`: `d Δ (2d)^t + d Δ ≤ Δ (2d)^{t+1}`. -/
theorem mesh_step {d : ℕ} (hd : 1 ≤ d) {Δ : ℝ} (hΔ : 0 ≤ Δ) (t : ℕ) :
    d * (Δ * (2 * d) ^ t) + d * Δ ≤ Δ * (2 * d) ^ (t + 1) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ (2 * d) ^ t := one_le_pow₀ (by linarith)
  rw [pow_succ]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ d) hΔ) (sub_nonneg.mpr h1)]

/-- `eq:mesh`: if `E_{t+1} ≤ d E_t + d Δ` and `E_0 = 0` then `E_t ≤ Δ (2d)^t`. -/
theorem mesh_bound {d : ℕ} (hd : 1 ≤ d) {Δ : ℝ} (hΔ : 0 ≤ Δ) (E : ℕ → ℝ) (h0 : E 0 = 0)
    (hstep : ∀ t, E (t + 1) ≤ d * E t + d * Δ) (t : ℕ) : E t ≤ Δ * (2 * d) ^ t := by
  induction t with
  | zero => simpa [h0] using hΔ
  | succ t ih =>
    calc E (t + 1) ≤ d * E t + d * Δ := hstep t
      _ ≤ d * (Δ * (2 * d) ^ t) + d * Δ := by gcongr
      _ ≤ Δ * (2 * d) ^ (t + 1) := mesh_step hd hΔ t

variable {α : Type*} {d : ℕ}

/-- `eq:mesh` for actual states: exact states `c` with coordinates in `[-1,1]` and transitions `A`,
computed states `c'` from the same initial state and transitions `A'` with entries in `[-1,1]`
within `Δ` of `A`. Then the coordinate error after a prefix of length `t < T` is at most
`Δ (2d)^t`. -/
theorem state_error (hd : 1 ≤ d) {T : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (c c' : List α → Fin d → ℝ) (A A' : ℕ → α → Matrix (Fin d) (Fin d) ℝ)
    (hc : ∀ h : List α, h.length < T → ∀ i, |c h i| ≤ 1)
    (hA' : ∀ t a i j, |A' t a i j| ≤ 1)
    (hAA : ∀ t a i j, t + 1 < T → |A' t a i j - A t a i j| ≤ Δ)
    (h0 : c' [] = c [])
    (hrec : ∀ (h : List α) (a : α), h.length + 1 < T → c (h ++ [a]) = vecMul (c h) (A h.length a))
    (hrec' : ∀ (h : List α) (a : α), c' (h ++ [a]) = vecMul (c' h) (A' h.length a)) :
    ∀ h : List α, h.length < T → ∀ i, |c' h i - c h i| ≤ Δ * (2 * d) ^ h.length := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _ i; simpa [h0] using hΔ
  | append_singleton h a ih =>
    intro hlen i
    have hl : h.length + 1 < T := by simpa using hlen
    have ih' := ih (by omega)
    rw [hrec h a hl, hrec' h a]
    simp only [vecMul, dotProduct, List.length_append, List.length_singleton]
    set E := Δ * (2 * d) ^ h.length
    have e : ∑ k, c' h k * A' h.length a k i - ∑ k, c h k * A h.length a k i =
        ∑ k, ((c' h k - c h k) * A' h.length a k i +
          c h k * (A' h.length a k i - A h.length a k i)) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    calc |∑ k, ((c' h k - c h k) * A' h.length a k i +
            c h k * (A' h.length a k i - A h.length a k i))|
        ≤ ∑ k, |(c' h k - c h k) * A' h.length a k i +
            c h k * (A' h.length a k i - A h.length a k i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin d, (E + Δ) := by
          refine Finset.sum_le_sum fun k _ => (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          have h1 := ih' k
          have h2 := hA' h.length a k i
          have h3 := hc h (by omega) k
          have h4 := hAA h.length a k i hl
          have hE : 0 ≤ E := (abs_nonneg _).trans h1
          nlinarith [abs_nonneg (c' h k - c h k), abs_nonneg (c h k),
            abs_nonneg (A' h.length a k i - A h.length a k i), abs_nonneg (A' h.length a k i)]
      _ = d * E + d * Δ := by simp
      _ ≤ Δ * (2 * d) ^ (h.length + 1) := mesh_step hd hΔ _

/-- The logit error of `eq:mesh`: with readouts `w'` in `[-Λ, Λ]` within `Δ` of `w`, the computed
logit differs from the exact one by at most `d Λ E_t + d Δ`. -/
theorem logit_error {T : ℕ} {Δ Λ : ℝ} (c c' : List α → Fin d → ℝ) (w w' : ℕ → Fin d → ℝ)
    (hc : ∀ h : List α, h.length < T → ∀ i, |c h i| ≤ 1) (hw' : ∀ t < T, ∀ i, |w' t i| ≤ Λ)
    (hww : ∀ t < T, ∀ i, |w' t i - w t i| ≤ Δ) {E : ℕ → ℝ}
    (hcc : ∀ h : List α, h.length < T → ∀ i, |c' h i - c h i| ≤ E h.length) :
    ∀ h : List α, h.length < T →
      |∑ i, c' h i * w' h.length i - ∑ i, c h i * w h.length i| ≤
        d * Λ * E h.length + d * Δ := by
  intro h hh
  have e : ∑ i, c' h i * w' h.length i - ∑ i, c h i * w h.length i =
      ∑ i, ((c' h i - c h i) * w' h.length i + c h i * (w' h.length i - w h.length i)) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e]
  calc _ ≤ ∑ i, |(c' h i - c h i) * w' h.length i + c h i * (w' h.length i - w h.length i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (Λ * E h.length + Δ) := by
        refine Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        have h1 := hcc h hh i
        have h2 := hw' _ hh i
        have h3 := hc h hh i
        have h4 := hww _ hh i
        nlinarith [abs_nonneg (c' h i - c h i), abs_nonneg (c h i),
          abs_nonneg (w' h.length i - w h.length i), abs_nonneg (w' h.length i)]
    _ = d * Λ * E h.length + d * Δ := by simp; ring

/-- The budget of `eq:mesh`: if `Δ ≤ ρ / (4 d (Λ + 1) (2d)^T)` then `d Λ Δ (2d)^t + d Δ ≤ ρ` for
`t ≤ T`. With `Λ = T` this is the paper's `d T E_t + d Δ ≤ ρ`. -/
theorem mesh_budget (hd : 1 ≤ d) {T t : ℕ} (ht : t ≤ T) {Δ Λ ρ : ℝ} (hΔ : 0 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΔρ : Δ ≤ ρ / (4 * d * (Λ + 1) * (2 * d) ^ T)) :
    d * Λ * (Δ * (2 * d) ^ t) + d * Δ ≤ ρ := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h2d : (1 : ℝ) ≤ 2 * d := by linarith
  have hX : 0 < 4 * d * (Λ + 1) * (2 * d) ^ T := by positivity
  have hpow : (2 * (d : ℝ)) ^ t ≤ (2 * d) ^ T := pow_le_pow_right₀ h2d ht
  have hone : (1 : ℝ) ≤ (2 * d) ^ T := one_le_pow₀ h2d
  have hρ : Δ * (4 * d * (Λ + 1) * (2 * d) ^ T) ≤ ρ := (le_div_iff₀ hX).mp hΔρ
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have key : Λ * (2 * (d : ℝ)) ^ t + 1 ≤ (Λ + 1) * (2 * d) ^ T := by nlinarith
  have hdΔ : 0 ≤ (d : ℝ) * Δ := by positivity
  calc d * Λ * (Δ * (2 * d) ^ t) + d * Δ = (d * Δ) * (Λ * (2 * d) ^ t + 1) := by ring
    _ ≤ (d * Δ) * ((Λ + 1) * (2 * d) ^ T) := by gcongr
    _ = (Δ * (4 * d * (Λ + 1) * (2 * d) ^ T)) / 4 := by ring
    _ ≤ ρ / 4 := by gcongr
    _ ≤ ρ := by linarith

/-- `eq:mesh` for rounded parameters: if the transitions `A'` (entries in `[-1,1]`) and readouts
`w'` (entries in `[-Λ,Λ]`) are within `Δ ≤ ρ / (4 d (Λ + 1) (2d)^T)` of the exact `A` and `w`, the
computed states start from the exact initial state, and the exact states have coordinates in
`[-1,1]`, then every computed logit before time `T` is within `ρ` of the exact one. -/
theorem rounded_logit_error (hd : 1 ≤ d) {T : ℕ} {Δ Λ ρ : ℝ} (hΔ : 0 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΔρ : Δ ≤ ρ / (4 * d * (Λ + 1) * (2 * d) ^ T))
    (c c' : List α → Fin d → ℝ) (A A' : ℕ → α → Matrix (Fin d) (Fin d) ℝ)
    (w w' : ℕ → Fin d → ℝ)
    (hc : ∀ h : List α, h.length < T → ∀ i, |c h i| ≤ 1)
    (hA' : ∀ t a i j, |A' t a i j| ≤ 1)
    (hAA : ∀ t a i j, t + 1 < T → |A' t a i j - A t a i j| ≤ Δ)
    (hw' : ∀ t < T, ∀ i, |w' t i| ≤ Λ) (hww : ∀ t < T, ∀ i, |w' t i - w t i| ≤ Δ)
    (h0 : c' [] = c [])
    (hrec : ∀ (h : List α) (a : α), h.length + 1 < T → c (h ++ [a]) = vecMul (c h) (A h.length a))
    (hrec' : ∀ (h : List α) (a : α), c' (h ++ [a]) = vecMul (c' h) (A' h.length a)) :
    ∀ h : List α, h.length < T →
      |∑ i, c' h i * w' h.length i - ∑ i, c h i * w h.length i| ≤ ρ := by
  intro h hh
  have hst := state_error hd hΔ c c' A A' hc hA' hAA h0 hrec hrec'
  exact (logit_error (E := fun t => Δ * (2 * d) ^ t) c c' w w' hc hw' hww hst h hh).trans
    (mesh_budget hd hh.le hΔ hΛ hΔρ)

/-- Clipping to `[-B, B]`. -/
noncomputable def clip (B u : ℝ) : ℝ := max (-B) (min B u)

theorem abs_clip_le {B : ℝ} (hB : 0 ≤ B) (u : ℝ) : |clip B u| ≤ B := by
  unfold clip; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- Clipping the candidate's logit to `[-B, B]` cannot increase its error relative to a true logit
`u` with `|u| ≤ B` (`sec:sample-upper`). -/
theorem abs_clip_sub_le {B u : ℝ} (hu : |u| ≤ B) (v : ℝ) : |clip B v - u| ≤ |v - u| := by
  rw [abs_le] at hu
  unfold clip
  rcases le_total v B with h1 | h1 <;> rcases le_total (-B) v with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2]
  · rw [min_eq_right h1, max_eq_left (by linarith)]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rw [min_eq_left h1, max_eq_right (by linarith)]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [min_eq_left h1, max_eq_right (by linarith)]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-! ### Running a candidate -/

/-- The states computed by a candidate from the state `x` at time `t` with transitions `A`. -/
noncomputable def runFrom (A : ℕ → α → Matrix (Fin d) (Fin d) ℝ) :
    ℕ → (Fin d → ℝ) → List α → Fin d → ℝ
  | _, x, [] => x
  | t, x, a :: f => runFrom A (t + 1) (vecMul x (A t a)) f

theorem runFrom_append (A : ℕ → α → Matrix (Fin d) (Fin d) ℝ) (t : ℕ) (x : Fin d → ℝ)
    (f : List α) (a : α) :
    runFrom A t x (f ++ [a]) = vecMul (runFrom A t x f) (A (t + f.length) a) := by
  induction f generalizing t x with
  | nil => simp [runFrom]
  | cons b f ih =>
    simp only [List.cons_append, runFrom, ih, List.length_cons]
    congr 2; omega

/-! ### Bounded grids, `eq:coverN` -/

/-- The bounded grid `{jΔ : j ∈ ℤ, |j| ≤ ⌊B/Δ⌋}` of multiples of `Δ` in `[-B, B]`. -/
noncomputable def grid (B Δ : ℝ) : Finset ℝ :=
  (Finset.Icc (-⌊B / Δ⌋) ⌊B / Δ⌋).image fun j : ℤ => (j : ℝ) * Δ

theorem abs_le_of_mem_grid {B Δ x : ℝ} (hΔ : 0 < Δ) (hx : x ∈ grid B Δ) : |x| ≤ B := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Icc] at hj
  have h1 : (j : ℝ) ≤ B / Δ := le_trans (by exact_mod_cast hj.2) (Int.floor_le _)
  have h2 : -(B / Δ) ≤ (j : ℝ) := le_trans (neg_le_neg (Int.floor_le _)) (by exact_mod_cast hj.1)
  rw [abs_mul, abs_of_pos hΔ, ← le_div_iff₀ hΔ, abs_le]
  exact ⟨h2, h1⟩

theorem card_grid_le {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 0 < Δ) :
    ((grid B Δ).card : ℝ) ≤ 1 + 2 * B / Δ := by
  have h0 : 0 ≤ ⌊B / Δ⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc : (grid B Δ).card ≤ (2 * ⌊B / Δ⌋ + 1).toNat := by
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Int.card_Icc]; congr 1; ring
  have hc' : ((grid B Δ).card : ℝ) ≤ ((2 * ⌊B / Δ⌋ + 1 : ℤ) : ℝ) := by
    have : ((2 * ⌊B / Δ⌋ + 1).toNat : ℤ) = 2 * ⌊B / Δ⌋ + 1 := Int.toNat_of_nonneg (by omega)
    calc ((grid B Δ).card : ℝ) ≤ ((2 * ⌊B / Δ⌋ + 1).toNat : ℝ) := by exact_mod_cast hc
      _ = (((2 * ⌊B / Δ⌋ + 1).toNat : ℤ) : ℝ) := rfl
      _ = _ := by rw [this]
  calc ((grid B Δ).card : ℝ) ≤ ((2 * ⌊B / Δ⌋ + 1 : ℤ) : ℝ) := hc'
    _ = 2 * (⌊B / Δ⌋ : ℝ) + 1 := by push_cast; ring
    _ ≤ 2 * (B / Δ) + 1 := by gcongr; exact Int.floor_le _
    _ = 1 + 2 * B / Δ := by ring

/-- Rounding into the grid (towards zero). -/
noncomputable def roundGrid (Δ x : ℝ) : ℝ :=
  if 0 ≤ x then (⌊x / Δ⌋ : ℝ) * Δ else -((⌊-x / Δ⌋ : ℝ) * Δ)

theorem roundGrid_nonneg_aux {B Δ x : ℝ} (hΔ : 0 < Δ) (hx0 : 0 ≤ x) (hx : x ≤ B) :
    (⌊x / Δ⌋ : ℝ) * Δ ∈ grid B Δ ∧ |(⌊x / Δ⌋ : ℝ) * Δ - x| ≤ Δ := by
  have hf0 : 0 ≤ ⌊x / Δ⌋ := Int.floor_nonneg.mpr (by positivity)
  have hfB : ⌊x / Δ⌋ ≤ ⌊B / Δ⌋ := Int.floor_le_floor (by gcongr)
  refine ⟨Finset.mem_image.mpr ⟨⌊x / Δ⌋, Finset.mem_Icc.mpr ⟨by omega, hfB⟩, rfl⟩, ?_⟩
  have h1 := Int.floor_le (x / Δ)
  have h2 := Int.lt_floor_add_one (x / Δ)
  have h1' : (⌊x / Δ⌋ : ℝ) * Δ ≤ x := by rwa [le_div_iff₀ hΔ] at h1
  have h2' : x < ((⌊x / Δ⌋ : ℝ) + 1) * Δ := by rwa [div_lt_iff₀ hΔ] at h2
  rw [abs_le]; constructor <;> nlinarith

theorem roundGrid_spec {B Δ x : ℝ} (hΔ : 0 < Δ) (hx : |x| ≤ B) :
    roundGrid Δ x ∈ grid B Δ ∧ |roundGrid Δ x - x| ≤ Δ := by
  rw [abs_le] at hx
  unfold roundGrid
  split_ifs with h
  · exact roundGrid_nonneg_aux hΔ h hx.2
  · obtain ⟨h1, h2⟩ := roundGrid_nonneg_aux (B := B) hΔ (x := -x) (by linarith) (by linarith)
    refine ⟨?_, by rw [← abs_neg]; convert h2 using 2; ring⟩
    obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp h1
    refine Finset.mem_image.mpr ⟨-j, ?_, ?_⟩
    · rw [Finset.mem_Icc] at hj ⊢; omega
    · push_cast; rw [← hj']; ring

theorem zero_mem_grid {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 0 < Δ) : (0 : ℝ) ∈ grid B Δ := by
  refine Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr ⟨?_, ?_⟩, by simp⟩ <;>
  · have : 0 ≤ ⌊B / Δ⌋ := Int.floor_nonneg.mpr (by positivity)
    omega

/-- Grid parameters of a candidate (`sec:sample-upper`): transitions `A_{t,b}` for `t < T - 1`
with entries in the grid of `[-1, 1]`, and readouts `w_t` for `t < T` with entries in the grid of
`[-B, B]`. The initial state is the fixed vector `e_1`. -/
abbrev GridParams (T d : ℕ) (B Δ : ℝ) :=
  (Fin (T - 1) → Bool → Fin d → Fin d → grid 1 Δ) × (Fin T → Fin d → grid B Δ)

/-- The parameter count `2 (T - 1) d² + T d ≤ 3 T d²`. -/
theorem param_count (T d : ℕ) (hd : 1 ≤ d) : 2 * (T - 1) * d ^ 2 + T * d ≤ 3 * T * d ^ 2 := by
  have h1 : 2 * (T - 1) * d ^ 2 ≤ 2 * T * d ^ 2 := by gcongr; omega
  have h2 : T * d ≤ T * d ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith

/-- `eq:coverN` as a counting statement: the number of grid candidates is at most
`(1 + 2B/Δ)^{3 T d²}` (the paper takes `B = T`). -/
theorem card_gridParams_le (T d : ℕ) (hd : 1 ≤ d) {B Δ : ℝ} (hB : 1 ≤ B) (hΔ : 0 < Δ) :
    (Fintype.card (GridParams T d B Δ) : ℝ) ≤ (1 + 2 * B / Δ) ^ (3 * T * d ^ 2) := by
  have hX : 1 ≤ 1 + 2 * B / Δ := by
    have : 0 ≤ 2 * B / Δ := by positivity
    linarith
  have h1 : ((grid 1 Δ).card : ℝ) ≤ 1 + 2 * B / Δ :=
    (card_grid_le zero_le_one hΔ).trans (by gcongr)
  have hB' : ((grid B Δ).card : ℝ) ≤ 1 + 2 * B / Δ := card_grid_le (by linarith) hΔ
  simp only [GridParams, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_coe]
  push_cast
  set x := ((grid 1 Δ).card : ℝ)
  set y := ((grid B Δ).card : ℝ)
  set X := 1 + 2 * B / Δ
  calc (((x ^ d) ^ d) ^ 2) ^ (T - 1) * (y ^ d) ^ T
      ≤ (((X ^ d) ^ d) ^ 2) ^ (T - 1) * (X ^ d) ^ T := by gcongr
    _ = X ^ (2 * (T - 1) * d ^ 2 + T * d) := by
        simp only [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ X ^ (3 * T * d ^ 2) := pow_le_pow_right₀ hX (param_count T d hd)

/-! ### Grid candidates -/

/-- The fixed initial state `e_1`. -/
def e1 (d : ℕ) : Fin d → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0

variable {T : ℕ} {B Δ : ℝ}

/-- The transitions of a grid candidate (zero for `t ≥ T - 1`). -/
noncomputable def gridA (P : GridParams T d B Δ) : ℕ → Bool → Matrix (Fin d) (Fin d) ℝ :=
  fun t b i j => if ht : t < T - 1 then (P.1 ⟨t, ht⟩ b i j : ℝ) else 0

/-- The readouts of a grid candidate (zero for `t ≥ T`). -/
noncomputable def gridW (P : GridParams T d B Δ) : ℕ → Fin d → ℝ :=
  fun t i => if ht : t < T then (P.2 ⟨t, ht⟩ i : ℝ) else 0

/-- The state computed by a grid candidate after the prefix `h`, starting from `e_1`. -/
noncomputable def candState (P : GridParams T d B Δ) (h : List Bool) : Fin d → ℝ :=
  runFrom (gridA P) 0 (e1 d) h

/-- The logit computed by a grid candidate, before clipping. -/
noncomputable def candLogit (P : GridParams T d B Δ) (h : List Bool) : ℝ :=
  ∑ i, candState P h i * gridW P h.length i

/-- `sec:sample-upper` (`eq:canonical` with `eq:mesh`): if `|ℓ h| ≤ Λ` for `|h| < T`, every cut
matrix has rank at most `d ≥ 1`, and `0 < Δ ≤ ρ / (4 d (Λ + 1) (2d)^T)`, then rounding the
transitions and readouts of the canonical representation to the grids, with the exact initial
state `e_1`, gives a grid candidate whose logits are within `ρ` of `ℓ` on every prefix of length
`< T`. The paper takes `Λ = T`. -/
theorem exists_grid_candidate {ℓ : List Bool → ℝ} {Λ ρ : ℝ} (hd : 1 ≤ d) (hΔ : 0 < Δ)
    (hΔρ : Δ ≤ ρ / (4 * d * (Λ + 1) * (2 * d) ^ T))
    (hbound : ∀ h : List Bool, h.length < T → |ℓ h| ≤ Λ)
    (hrank : ∀ t < T, (logitCutMatrix ℓ T t).rank ≤ d) :
    ∃ P : GridParams T d Λ Δ, ∀ h : List Bool, h.length < T → |candLogit P h - ℓ h| ≤ ρ := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · exact ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun h hh => absurd hh (by omega)⟩
  have hΛ : 0 ≤ Λ := (abs_nonneg _).trans (hbound [] hT)
  obtain ⟨c, A, w, hc, hA, hw, hℓ, hrec, h0⟩ := exists_canonical_binary ℓ T d Λ hbound hrank
  let P : GridParams T d Λ Δ :=
    (fun t b i j => ⟨roundGrid Δ (A t b i j), (roundGrid_spec hΔ (hA t b i j)).1⟩,
     fun t i => ⟨roundGrid Δ (w t i), (roundGrid_spec hΔ (hw t t.isLt i)).1⟩)
  refine ⟨P, fun h hh => ?_⟩
  have hA' : ∀ t b i j, |gridA P t b i j| ≤ 1 := by
    intro t b i j; unfold gridA; split_ifs
    · exact abs_le_of_mem_grid hΔ (Subtype.prop _)
    · simp
  have hAA : ∀ t b i j, t + 1 < T → |gridA P t b i j - A t b i j| ≤ Δ := by
    intro t b i j ht
    simp only [gridA, show t < T - 1 by omega, ↓reduceDIte, P]
    exact (roundGrid_spec hΔ (hA t b i j)).2
  have hw' : ∀ t < T, ∀ i, |gridW P t i| ≤ Λ := by
    intro t ht i; simp only [gridW, ht, ↓reduceDIte]; exact abs_le_of_mem_grid hΔ (Subtype.prop _)
  have hww : ∀ t < T, ∀ i, |gridW P t i - w t i| ≤ Δ := by
    intro t ht i; simp only [gridW, ht, ↓reduceDIte, P]; exact (roundGrid_spec hΔ (hw t ht i)).2
  have hinit : candState P [] = c [] := by
    rw [h0 hd hT]; funext i; simp [candState, runFrom, e1, Pi.single_apply, Fin.ext_iff]
  have hst := state_error hd hΔ.le c (candState P) A (gridA P) (fun h _ i => hc h i) hA' hAA
    hinit hrec (fun h b => by simpa [candState] using runFrom_append (gridA P) 0 (e1 d) h b)
  have hlog := logit_error (T := T) (E := fun t => Δ * (2 * d) ^ t) c (candState P) w (gridW P)
    (fun h _ i => hc h i) hw' hww hst h hh
  rw [hℓ h hh]
  exact hlog.trans (mesh_budget hd hh.le hΔ.le hΛ hΔρ)

/-- The dyadic mesh exponent `k = ⌈log₂ (4 d (T+1) (2d)^T / ρ)⌉` of `eq:mesh`. -/
noncomputable def meshK (T d : ℕ) (ρ : ℝ) : ℕ :=
  ⌈Real.logb 2 (4 * d * (T + 1) * (2 * d) ^ T / ρ)⌉₊

/-- `eq:mesh`: `Δ = 2^{-k} ≤ ρ / (4 d (T+1) (2d)^T)`. -/
theorem mesh_le (T d : ℕ) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) :
    ((2 : ℝ) ^ meshK T d ρ)⁻¹ ≤ ρ / (4 * d * (T + 1) * (2 * d) ^ T) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hX : 0 < 4 * (d : ℝ) * (T + 1) * (2 * d) ^ T := by positivity
  have hk : 4 * (d : ℝ) * (T + 1) * (2 * d) ^ T / ρ ≤ (2 : ℝ) ^ meshK T d ρ := by
    have h1 : Real.logb 2 (4 * (d : ℝ) * (T + 1) * (2 * d) ^ T / ρ) ≤ meshK T d ρ :=
      Nat.le_ceil _
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)] at h1
    simpa [Real.rpow_natCast] using h1
  rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
  exact hk

end LowLogitRank.Cover
