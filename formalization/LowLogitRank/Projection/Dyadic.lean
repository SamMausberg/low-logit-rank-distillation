import LowLogitRank.Basic

/-!
# Dyadic probability interfaces (`sec:finite-bit-lm`)

The cached law `r_y = (1 - Ab) n_y / N₀ + b` for an alphabet of size `A`, exact sampling against
its cumulative integer masses, and rounding of cumulative probabilities to a mesh `h` with exact
endpoints (last subsection of `sec:finite-bit-lm`).
-/

namespace LowLogitRank.Projection

open Finset

/-! ### The cached law for an alphabet of size `A` -/

section Law

variable {Y : Type*} [Fintype Y]

/-- The stored law `r_y = (1 - A b) n_y / N₀ + b`, `A = |Y|`. -/
noncomputable def dyadicLaw (n : Y → ℕ) (N₀ : ℕ) (b : ℝ) (y : Y) : ℝ :=
  (1 - Fintype.card Y * b) * n y / N₀ + b

/-- `sec:finite-bit-lm`, alphabet paragraph: the stored law sums to one exactly. -/
theorem dyadicLaw_sum {n : Y → ℕ} {N₀ : ℕ} (hN : ∑ y, n y = N₀) (hN0 : 0 < N₀) (b : ℝ) :
    ∑ y, dyadicLaw n N₀ b y = 1 := by
  have hN' : ((N₀ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  unfold dyadicLaw
  rw [sum_add_distrib, ← sum_div, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  have : (∑ y, (n y : ℝ)) = N₀ := by exact_mod_cast hN
  rw [this]
  field_simp
  ring

/-- `sec:finite-bit-lm`, alphabet paragraph: the stored law has floor `b` when `A b ≤ 1`. -/
theorem le_dyadicLaw {n : Y → ℕ} {N₀ : ℕ} {b : ℝ} (hAb : Fintype.card Y * b ≤ 1) (y : Y) :
    b ≤ dyadicLaw n N₀ b y := by
  unfold dyadicLaw
  have : 0 ≤ (1 - Fintype.card Y * b) * n y / N₀ := by
    apply div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  linarith

/-- `sec:finite-bit-lm`, alphabet paragraph: the stored law is within TV `A b` of the empirical law
`n_y / N₀`. -/
theorem tv_dyadicLaw_le {n : Y → ℕ} {N₀ : ℕ} (hN : ∑ y, n y = N₀) (hN0 : 0 < N₀) {b : ℝ}
    (hb : 0 ≤ b) : tv (dyadicLaw n N₀ b) (fun y => (n y : ℝ) / N₀) ≤ Fintype.card Y * b := by
  have hN' : (0 : ℝ) < N₀ := by exact_mod_cast hN0
  have e : ∀ y, dyadicLaw n N₀ b y - n y / N₀ = b * (1 - Fintype.card Y * (n y / N₀)) := by
    intro y; unfold dyadicLaw; ring
  have hsum : ∑ y, ((n y : ℝ) / N₀) = 1 := by
    rw [← sum_div]
    have : (∑ y, (n y : ℝ)) = N₀ := by exact_mod_cast hN
    rw [this, div_self hN'.ne']
  unfold tv
  rw [div_le_iff₀ (by norm_num)]
  calc ∑ y, |dyadicLaw n N₀ b y - n y / N₀|
        = ∑ y, b * |1 - (Fintype.card Y : ℝ) * ((n y : ℝ) / N₀)| := by
        refine sum_congr rfl fun y _ => ?_
        rw [e, abs_mul, abs_of_nonneg hb]
    _ ≤ ∑ y, b * (1 + (Fintype.card Y : ℝ) * ((n y : ℝ) / N₀)) := by
        refine sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ hb
        have : 0 ≤ (Fintype.card Y : ℝ) * (n y / N₀) := by positivity
        rw [abs_le]; constructor <;> linarith
    _ = Fintype.card Y * b * 2 := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, hsum, sum_const, card_univ, nsmul_eq_mul]
        ring

/-- `sec:finite-bit-lm`, alphabet paragraph: with `N₀ = 2^k` and `b = B / 2^l`, every stored
probability is the dyadic number `((2^l - A B) n_y + B 2^k) / 2^{k+l}`. -/
theorem dyadicLaw_eq_dyadic (n : Y → ℕ) (k l B : ℕ) (y : Y) :
    dyadicLaw n (2 ^ k) ((B : ℝ) / 2 ^ l) y =
      (((2 ^ l - Fintype.card Y * B) * n y + B * 2 ^ k : ℤ) : ℝ) / 2 ^ (k + l) := by
  unfold dyadicLaw
  push_cast
  rw [pow_add]
  field_simp

end Law

/-! ### Exact sampling against cumulative integer masses -/

/-- `sec:finite-bit-lm`: if integer masses `M_0, …, M_{A-1}` sum to `2^{B₀}`, a uniform `B₀`-bit
integer `U` lies in the cumulative interval of token `y` for exactly `M_y` of the `2^{B₀}` values,
so the draw samples the law `M_y / 2^{B₀}` exactly. -/
theorem card_cumulative_select {A B₀ : ℕ} (M : ℕ → ℕ) (hM : ∑ i ∈ range A, M i = 2 ^ B₀)
    {y : ℕ} (hy : y < A) :
    ((range (2 ^ B₀)).filter
        (fun U => ∑ i ∈ range y, M i ≤ U ∧ U < ∑ i ∈ range (y + 1), M i)).card = M y := by
  have hle : ∑ i ∈ range (y + 1), M i ≤ 2 ^ B₀ := by
    rw [← hM]
    exact sum_le_sum_of_subset (range_subset_range.2 (by omega))
  have e : (range (2 ^ B₀)).filter
      (fun U => ∑ i ∈ range y, M i ≤ U ∧ U < ∑ i ∈ range (y + 1), M i) =
      Ico (∑ i ∈ range y, M i) (∑ i ∈ range (y + 1), M i) := by
    ext U
    simp only [mem_filter, mem_range, mem_Ico]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [e, Nat.card_Ico, sum_range_succ]
  omega

/-! ### Rounding cumulative probabilities -/

section Cumulative

/-- Cumulative sums `C_k = ∑_{i<k} p_i`. -/
def cum (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, p i

/-- Cumulative probabilities rounded down to the mesh `h`, with `C_0 = 0` and `C_A = 1` exact. -/
noncomputable def roundCum (h : ℝ) (A : ℕ) (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if A ≤ k then 1 else h * ⌊cum p k / h⌋

/-- The rounded masses, successive differences of the rounded cumulative probabilities. -/
noncomputable def roundMass (h : ℝ) (A : ℕ) (p : ℕ → ℝ) (i : ℕ) : ℝ :=
  roundCum h A p (i + 1) - roundCum h A p i

variable {h : ℝ} {A : ℕ} {p : ℕ → ℝ}

theorem cum_nonneg (hp : ∀ i < A, 0 ≤ p i) {k : ℕ} (hk : k ≤ A) : 0 ≤ cum p k :=
  sum_nonneg fun i hi => hp i (by simp at hi; omega)

theorem cum_mono (hp : ∀ i < A, 0 ≤ p i) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ A) :
    cum p k ≤ cum p l :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hkl) fun i hi _ =>
    hp i (by simp at hi; omega)

theorem floor_mesh_le (hh : 0 < h) (x : ℝ) : h * ⌊x / h⌋ ≤ x := by
  have := Int.floor_le (x / h)
  rw [le_div_iff₀ hh] at this
  linarith

theorem lt_floor_mesh_add (hh : 0 < h) (x : ℝ) : x < h * ⌊x / h⌋ + h := by
  have := Int.lt_floor_add_one (x / h)
  rw [div_lt_iff₀ hh] at this
  linarith

/-- Each rounded cumulative probability is within the mesh: `|Ĉ_k - C_k| < h` for `k ≤ A`, with
equality `Ĉ_k = C_k` at the endpoints. -/
theorem abs_roundCum_sub_lt (hh : 0 < h) (hsum : cum p A = 1) {k : ℕ} (hk : k ≤ A) :
    |roundCum h A p k - cum p k| < h := by
  unfold roundCum
  split_ifs with h0 hA
  · subst h0; simp [cum, hh]
  · have : k = A := le_antisymm hk hA
    subst this; simp [hsum, hh]
  · have h1 := floor_mesh_le hh (cum p k)
    have h2 := lt_floor_mesh_add hh (cum p k)
    rw [abs_lt]; constructor <;> linarith

theorem roundCum_zero : roundCum h A p 0 = 0 := by simp [roundCum]

theorem roundCum_A (hA : 1 ≤ A) : roundCum h A p A = 1 := by
  unfold roundCum
  rw [ite_eq_right (by omega), ite_eq_left le_rfl]

/-- The rounded masses are nonnegative. -/
theorem roundMass_nonneg (hh : 0 < h) (hp : ∀ i < A, 0 ≤ p i) (hsum : cum p A = 1) {i : ℕ}
    (hi : i < A) : 0 ≤ roundMass h A p i := by
  unfold roundMass roundCum
  have hle1 : cum p i ≤ 1 := hsum ▸ cum_mono hp hi.le le_rfl
  by_cases hA : A ≤ i + 1
  · rw [ite_eq_right (by omega), ite_eq_left hA]
    split_ifs with h0 h1
    · norm_num
    · omega
    · linarith [floor_mesh_le hh (cum p i)]
  · rw [ite_eq_right (by omega), ite_eq_right hA]
    split_ifs with h0 h1
    · have : (0 : ℝ) ≤ ⌊cum p (i + 1) / h⌋ := by
        exact_mod_cast Int.floor_nonneg.2 (div_nonneg (cum_nonneg hp hi) hh.le)
      nlinarith
    · omega
    · have : (⌊cum p i / h⌋ : ℝ) ≤ ⌊cum p (i + 1) / h⌋ := by
        exact_mod_cast Int.floor_mono (div_le_div_of_nonneg_right
          (cum_mono hp (Nat.le_succ i) hi) hh.le)
      nlinarith

/-- The rounded masses sum to one. -/
theorem sum_roundMass (hA : 1 ≤ A) : ∑ i ∈ range A, roundMass h A p i = 1 := by
  unfold roundMass
  rw [sum_range_sub (fun k => roundCum h A p k), roundCum_A hA, roundCum_zero, sub_zero]

/-- The `ℓ₁` error of the rounded masses is at most `2 (A - 1) h`. -/
theorem sum_abs_roundMass_sub_le (hh : 0 < h) (hsum : cum p A = 1) (hA : 1 ≤ A) :
    ∑ i ∈ range A, |roundMass h A p i - p i| ≤ 2 * (A - 1) * h := by
  set d : ℕ → ℝ := fun k => roundCum h A p k - cum p k with hd
  have hd0 : d 0 = 0 := by simp [hd, roundCum_zero, cum]
  have hdA : d A = 0 := by simp [hd, roundCum_A hA, hsum]
  have hstep : ∀ i, roundMass h A p i - p i = d (i + 1) - d i := by
    intro i; simp only [hd, roundMass, cum, sum_range_succ]; ring
  obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  have hint : ∀ i ∈ range A', |d (i + 1)| ≤ h := fun i hi =>
    (abs_roundCum_sub_lt hh hsum (by simp at hi; omega)).le
  calc ∑ i ∈ range (A' + 1), |roundMass h (A' + 1) p i - p i|
      ≤ ∑ i ∈ range (A' + 1), (|d (i + 1)| + |d i|) := by
        refine sum_le_sum fun i _ => ?_
        rw [hstep]; exact abs_sub _ _
    _ = ∑ i ∈ range A', |d (i + 1)| + ∑ i ∈ range A', |d (i + 1)| := by
        rw [sum_add_distrib, sum_range_succ, sum_range_succ' (fun i => |d i|), hdA, hd0]
        simp
    _ ≤ ∑ _i ∈ range A', h + ∑ _i ∈ range A', h := add_le_add (sum_le_sum hint) (sum_le_sum hint)
    _ = 2 * ((A' + 1 : ℕ) - 1 : ℝ) * h := by simp; ring

/-- Cumulative rounding (`sec:finite-bit-lm`, last subsection): for a probability vector
`p_0, …, p_{A-1}` and mesh `h > 0`, the rounded masses are nonnegative, sum to one, and have
next-token TV at most `(A - 1) h ≤ A h` from `p`. -/
theorem cumulative_rounding (hh : 0 < h) (hp : ∀ i < A, 0 ≤ p i) (hsum : cum p A = 1) :
    (∀ i < A, 0 ≤ roundMass h A p i) ∧ ∑ i ∈ range A, roundMass h A p i = 1 ∧
      tv (fun z : Fin A => roundMass h A p z) (fun z : Fin A => p z) ≤ (A - 1) * h ∧
      ((A : ℝ) - 1) * h ≤ A * h := by
  have hA : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h0 | h0
    · subst h0; simp [cum] at hsum
    · exact h0
  refine ⟨fun i hi => roundMass_nonneg hh hp hsum hi, sum_roundMass hA, ?_, by linarith⟩
  unfold tv
  rw [Fin.sum_univ_eq_sum_range (fun i => |roundMass h A p i - p i|) A, div_le_iff₀ (by norm_num)]
  have := sum_abs_roundMass_sub_le hh hsum hA
  linarith

/-- With mesh `h ≤ a / (10 A T)`, the per-step error `A h` summed over `T` steps is at most
`a / 10`. -/
theorem total_rounding_allowance {a h : ℝ} {A T : ℕ} (hA : 0 < A) (hT : 0 < T)
    (hh : h ≤ a / (10 * A * T)) : T * (A * h) ≤ a / 10 := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [le_div_iff₀ (by positivity)] at hh
  nlinarith

end Cumulative

end LowLogitRank.Projection
