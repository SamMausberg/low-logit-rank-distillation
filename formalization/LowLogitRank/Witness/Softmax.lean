import LowLogitRank.Basic

/-!
# The softmax bound and the next-token telescope (`sec:gls-validation-arithmetic`)

* `TV(softmax u, softmax v) ≤ ‖u - v‖_∞` on a nonempty finite index type, proved as in the paper:
  along the segment from `v` to `u`, the derivative of coordinate `i` is `p_i (a_i - ∑_j p_j a_j)`
  with `a = u - v`, and the sum of the absolute values is at most `2 ‖a‖_∞`.
* Binary case: the second coordinate of `softmax (-ℓ, ℓ)` is `σ(2ℓ)`, so
  `|σ(2a) - σ(2b)| ≤ |a - b|`.
* The next-token telescope: `E₁ = 0` and `E_{s+1} = E_s + Δ_s` give `E_{t+1} = ∑_{s ≤ t} Δ_s`.
-/

namespace LowLogitRank.Witness

open Finset

/-! ### Softmax -/

/-- `softmax u i = e^{u_i} / ∑_j e^{u_j}`. -/
noncomputable def softmax {n : Type*} [Fintype n] (u : n → ℝ) (i : n) : ℝ :=
  Real.exp (u i) / ∑ j, Real.exp (u j)

variable {n : Type*} [Fintype n] [Nonempty n]

theorem sum_exp_pos (u : n → ℝ) : 0 < ∑ j, Real.exp (u j) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem softmax_pos (u : n → ℝ) (i : n) : 0 < softmax u i :=
  div_pos (Real.exp_pos _) (sum_exp_pos u)

theorem sum_softmax (u : n → ℝ) : ∑ i, softmax u i = 1 := by
  unfold softmax
  rw [← Finset.sum_div, div_self (sum_exp_pos u).ne']

/-- The derivative of a softmax coordinate along the line `t ↦ v + t a`. -/
theorem hasDerivAt_softmax_line (v a : n → ℝ) (i : n) (t : ℝ) :
    HasDerivAt (fun t => softmax (fun k => v k + t * a k) i)
      (softmax (fun k => v k + t * a k) i *
        (a i - ∑ k, softmax (fun k => v k + t * a k) k * a k)) t := by
  have hE : ∀ k, HasDerivAt (fun t => Real.exp (v k + t * a k))
      (Real.exp (v k + t * a k) * a k) t := by
    intro k
    have h1 : HasDerivAt (fun t => v k + t * a k) (a k) t := by
      simpa using ((hasDerivAt_id t).mul_const (a k)).const_add (v k)
    exact h1.exp
  have hZ : HasDerivAt (fun t => ∑ k, Real.exp (v k + t * a k))
      (∑ k, Real.exp (v k + t * a k) * a k) t :=
    HasDerivAt.fun_sum fun k _ => hE k
  have hZ0 := sum_exp_pos (fun k => v k + t * a k)
  have h := (hE i).fun_div hZ hZ0.ne'
  have hs : ∑ k, Real.exp (v k + t * a k) / (∑ j, Real.exp (v j + t * a j)) * a k =
      (∑ k, Real.exp (v k + t * a k) * a k) / ∑ j, Real.exp (v j + t * a j) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hval : softmax (fun k => v k + t * a k) i *
      (a i - ∑ k, softmax (fun k => v k + t * a k) k * a k) =
      (Real.exp (v i + t * a i) * a i * ∑ k, Real.exp (v k + t * a k) -
        Real.exp (v i + t * a i) * ∑ k, Real.exp (v k + t * a k) * a k) /
      (∑ k, Real.exp (v k + t * a k)) ^ 2 := by
    unfold softmax
    rw [hs]
    field_simp
  rw [hval]
  exact h

/-- `sec:gls-validation-arithmetic`: `TV(softmax u, softmax v) ≤ c` whenever
`|u_i - v_i| ≤ c` for every `i`. -/
theorem tv_softmax_le_of_abs_le (u v : n → ℝ) (c : ℝ) (hc : ∀ i, |u i - v i| ≤ c) :
    tv (softmax u) (softmax v) ≤ c := by
  set a : n → ℝ := fun k => u k - v k with ha
  set P : ℝ → n → ℝ := fun t => softmax (fun k => v k + t * a k) with hP
  have hP1 : P 1 = softmax u := by
    simp only [hP, ha, one_mul, add_sub_cancel]
  have hP0 : P 0 = softmax v := by
    simp only [hP, zero_mul, add_zero]
  set sg : n → ℝ := fun k => if 0 ≤ P 1 k - P 0 k then 1 else -1 with hsg
  set F : ℝ → ℝ := fun t => ∑ k, sg k * P t k with hF
  set F' : ℝ → ℝ := fun t => ∑ k, sg k * (P t k * (a k - ∑ j, P t j * a j)) with hF'
  have hderiv : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_softmax_line v a k t).const_mul (sg k)
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope F F' (zero_lt_one' ℝ)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt) (fun t _ => hderiv t)
  rw [sub_zero, div_one] at hξ
  have hF10 : F 1 - F 0 = ∑ k, |softmax u k - softmax v k| := by
    simp only [hF, ← Finset.sum_sub_distrib, ← mul_sub, ← hP1, ← hP0]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hsg]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc (Classical.arbitrary n))
  have habs_a : ∀ k, |a k| ≤ c := fun k => hc k
  have hPpos : ∀ k, 0 < P ξ k := fun k => softmax_pos _ k
  have hPsum : ∑ k, P ξ k = 1 := sum_softmax _
  have hmean : |∑ j, P ξ j * a j| ≤ c := by
    calc |∑ j, P ξ j * a j| ≤ ∑ j, |P ξ j * a j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, P ξ j * c := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_of_pos (hPpos j)]
          exact mul_le_mul_of_nonneg_left (habs_a j) (hPpos j).le
      _ = c := by rw [← Finset.sum_mul, hPsum, one_mul]
  have hF'le : |F' ξ| ≤ 2 * c := by
    calc |F' ξ| ≤ ∑ k, |sg k * (P ξ k * (a k - ∑ j, P ξ j * a j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, P ξ k * (2 * c) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hsk : |sg k| = 1 := by simp only [hsg]; split_ifs <;> simp
          rw [abs_mul, hsk, one_mul, abs_mul, abs_of_pos (hPpos k)]
          refine mul_le_mul_of_nonneg_left ?_ (hPpos k).le
          calc |a k - ∑ j, P ξ j * a j| ≤ |a k| + |∑ j, P ξ j * a j| := abs_sub _ _
            _ ≤ c + c := add_le_add (habs_a k) hmean
            _ = 2 * c := by ring
      _ = 2 * c := by rw [← Finset.sum_mul, hPsum, one_mul]
  unfold tv
  rw [← hF10, ← hξ]
  have := (abs_le.mp hF'le).2
  linarith

/-- `sec:gls-validation-arithmetic`: `TV(softmax u, softmax v) ≤ ‖u - v‖_∞`. The norm on
`n → ℝ` is the sup norm. -/
theorem tv_softmax_le (u v : n → ℝ) : tv (softmax u) (softmax v) ≤ ‖u - v‖ :=
  tv_softmax_le_of_abs_le u v _ fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (u - v) i

/-- The total variation between two softmax vectors is at most one. -/
theorem tv_softmax_le_one (u v : n → ℝ) : tv (softmax u) (softmax v) ≤ 1 := by
  unfold tv
  have h : ∑ z, |softmax u z - softmax v z| ≤ ∑ z, (softmax u z + softmax v z) :=
    Finset.sum_le_sum fun z _ => by
      have := softmax_pos u z
      have := softmax_pos v z
      rw [abs_le]; constructor <;> linarith
  rw [Finset.sum_add_distrib, sum_softmax, sum_softmax] at h
  linarith

/-! ### The binary case -/

/-- The centered pair `(-ℓ, ℓ)` has softmax probability `σ(2ℓ)` on its second coordinate. -/
theorem softmax_centered_one (ℓ : ℝ) : softmax ![-ℓ, ℓ] 1 = sigmoid (2 * ℓ) := by
  unfold softmax sigmoid
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : Real.exp (-(2 * ℓ)) = Real.exp (-ℓ) * Real.exp (-ℓ) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-ℓ) * Real.exp ℓ = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-ℓ) + Real.exp ℓ := by positivity
  rw [h1, div_eq_iff hpos.ne']
  field_simp
  nlinarith [h2]

/-- The first coordinate of the centered softmax is `1 - σ(2ℓ)`. -/
theorem softmax_centered_zero (ℓ : ℝ) : softmax ![-ℓ, ℓ] 0 = 1 - sigmoid (2 * ℓ) := by
  have h := sum_softmax ![-ℓ, ℓ]
  rw [Fin.sum_univ_two, softmax_centered_one] at h
  linarith

/-- `sec:gls-validation-arithmetic`, binary case: `|σ(2a) - σ(2b)| ≤ |a - b|`. -/
theorem abs_sigmoid_two_mul_sub_le (a b : ℝ) :
    |sigmoid (2 * a) - sigmoid (2 * b)| ≤ |a - b| := by
  have h := tv_softmax_le_of_abs_le ![-a, a] ![-b, b] |a - b| fun i => by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [show -a - -b = -(a - b) by ring, abs_neg]
    · simp
  unfold tv at h
  rw [Fin.sum_univ_two, softmax_centered_zero, softmax_centered_zero, softmax_centered_one,
    softmax_centered_one, show 1 - sigmoid (2 * a) - (1 - sigmoid (2 * b)) =
      -(sigmoid (2 * a) - sigmoid (2 * b)) by ring, abs_neg] at h
  linarith

/-! ### The next-token telescope -/

/-- `sec:gls-validation-arithmetic`: `E₁ = 0` and `E_{s+1} = E_s + Δ_s` for `1 ≤ s ≤ t` give
`E_{t+1} = ∑_{s=1}^{t} Δ_s`. -/
theorem telescope (E Δ : ℕ → ℝ) (t : ℕ) (h1 : E 1 = 0)
    (hstep : ∀ s ∈ Icc 1 t, E (s + 1) = E s + Δ s) : E (t + 1) = ∑ s ∈ Icc 1 t, Δ s := by
  induction t with
  | zero => simpa using h1
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih fun s hs => hstep s (by
      rw [Finset.mem_Icc] at hs ⊢; omega)]
    exact hstep (t + 1) (by simp)

/-- `sec:gls-validation-arithmetic`, the corrected next-token telescope in terms of the
extended-row identities. Fix a token `a`; `hatL s = L̂_s(f_s)`, `S s = ∑_i c_{s,i} L_{s,i}(f_s)`
and `Lstar = 𝓛*(a)`. The identities `L̂_1(f_1) = 𝓛*(a)` and `L̂_{s+1}(f_{s+1}) = S s` give
`E_{t+1} = L̂_{t+1}(f_{t+1}) - 𝓛*(a) = ∑_{s=1}^{t} Δ_s` with `Δ_s = S s - L̂_s(f_s)`. -/
theorem next_token_telescope (hatL S : ℕ → ℝ) (Lstar : ℝ) (t : ℕ) (h1 : hatL 1 = Lstar)
    (hrow : ∀ s ∈ Icc 1 t, hatL (s + 1) = S s) :
    hatL (t + 1) - Lstar = ∑ s ∈ Icc 1 t, (S s - hatL s) :=
  telescope (fun s => hatL s - Lstar) (fun s => S s - hatL s) t (by simp [h1])
    fun s hs => by simp only [hrow s hs]; ring

/-- `|E_{t+1}| ≤ t r` when every telescoped residual satisfies `|Δ_s| ≤ r`. -/
theorem abs_telescope_le (E Δ : ℕ → ℝ) (t : ℕ) (r : ℝ) (h1 : E 1 = 0)
    (hstep : ∀ s ∈ Icc 1 t, E (s + 1) = E s + Δ s) (hΔ : ∀ s ∈ Icc 1 t, |Δ s| ≤ r) :
    |E (t + 1)| ≤ t * r := by
  rw [telescope E Δ t h1 hstep]
  calc |∑ s ∈ Icc 1 t, Δ s| ≤ ∑ s ∈ Icc 1 t, |Δ s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Icc 1 t, r := Finset.sum_le_sum hΔ
    _ = t * r := by simp

/-- Truncation: `min {1, t z} ≤ t min {1, z}` for a natural `t ≥ 1`. -/
theorem min_one_mul_le (t : ℕ) (ht : 1 ≤ t) (z : ℝ) :
    min 1 (t * z) ≤ t * min 1 z := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  rcases le_total z 1 with h | h
  · rw [min_eq_right h]; exact min_le_right _ _
  · rw [min_eq_left h, mul_one]; exact (min_le_left _ _).trans ht'

/-- `sec:gls-validation-arithmetic`: for a fixed prefix and the scalar next-token logits
`L̂_{t+1}(a)`, `𝓛*(a)` over a nonempty finite token set, the next-token TV error is at most
`min {1, t r}` when every telescoped residual is at most `r` in magnitude. -/
theorem tv_next_token_le {V : Type*} [Fintype V] [Nonempty V] (E Δ : V → ℕ → ℝ)
    (hatL Lstar : V → ℝ) (t : ℕ) (r : ℝ)
    (hE : ∀ a, E a (t + 1) = hatL a - Lstar a) (h1 : ∀ a, E a 1 = 0)
    (hstep : ∀ a, ∀ s ∈ Icc 1 t, E a (s + 1) = E a s + Δ a s)
    (hΔ : ∀ a, ∀ s ∈ Icc 1 t, |Δ a s| ≤ r) :
    tv (softmax hatL) (softmax Lstar) ≤ min 1 (t * r) :=
  le_min (tv_softmax_le_one _ _) (tv_softmax_le_of_abs_le _ _ _ fun a => by
    rw [← hE a]; exact abs_telescope_le (E a) (Δ a) t r (h1 a) (hstep a) (hΔ a))

end LowLogitRank.Witness
