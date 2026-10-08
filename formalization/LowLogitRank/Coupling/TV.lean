import LowLogitRank.Basic

/-!
# Total variation on a finite set (`sec:model`)

Elementary facts about `tv P Q = (1/2) ∑ |P z - Q z|`: the triangle inequality, the identity
`tv = max_E |P(E) - Q(E)|`, the coupling bound, data processing for deterministic maps and for
stochastic kernels, and the exact formula for mixtures with a common mixing law.
-/

namespace LowLogitRank.Coupling

open Finset

variable {α β Ω : Type*}

/-- A probability vector on a finite set: nonnegative entries summing to one. -/
structure IsProbVec [Fintype α] (P : α → ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ P z
  sum_eq_one : ∑ z, P z = 1

section Basic

variable [Fintype α]

/-- `sec:model`: TV is nonnegative. -/
theorem tv_nonneg (P Q : α → ℝ) : 0 ≤ tv P Q := by
  unfold tv
  have : 0 ≤ ∑ z, |P z - Q z| := sum_nonneg fun z _ => abs_nonneg _
  positivity

/-- `sec:model`: TV is symmetric. -/
theorem tv_comm (P Q : α → ℝ) : tv P Q = tv Q P := by
  unfold tv
  congr 1
  exact sum_congr rfl fun z _ => abs_sub_comm _ _

@[simp] theorem tv_self (P : α → ℝ) : tv P P = 0 := by
  simp [tv]

/-- `sec:model`: the triangle inequality for TV (used in `lem:coupling`, `eq:target-telescope`
and the second proof of `thm:fixed`). -/
theorem tv_triangle (P Q R : α → ℝ) : tv P R ≤ tv P Q + tv Q R := by
  unfold tv
  rw [← add_div, ← sum_add_distrib]
  gcongr with z
  exact abs_sub_le _ _ _

/-- `sec:model`: for two vectors of equal total mass (in particular two probability vectors),
the difference of the masses of every event is at most the total-variation distance. -/
theorem abs_sub_le_tv {P Q : α → ℝ} (hsum : ∑ z, P z = ∑ z, Q z) (E : Finset α) :
    |∑ z ∈ E, P z - ∑ z ∈ E, Q z| ≤ tv P Q := by
  classical
  have htot : ∑ z ∈ E, (P z - Q z) + ∑ z ∈ Eᶜ, (P z - Q z) = 0 := by
    rw [sum_add_sum_compl, sum_sub_distrib, hsum, sub_self]
  have h1 : ∑ z ∈ E, (P z - Q z) ≤ ∑ z ∈ E, |P z - Q z| :=
    sum_le_sum fun z _ => le_abs_self _
  have h2 : ∑ z ∈ Eᶜ, (P z - Q z) ≤ ∑ z ∈ Eᶜ, |P z - Q z| :=
    sum_le_sum fun z _ => le_abs_self _
  have h3 : -∑ z ∈ E, (P z - Q z) ≤ ∑ z ∈ E, |P z - Q z| := by
    rw [← sum_neg_distrib]; exact sum_le_sum fun z _ => neg_le_abs _
  have h4 : -∑ z ∈ Eᶜ, (P z - Q z) ≤ ∑ z ∈ Eᶜ, |P z - Q z| := by
    rw [← sum_neg_distrib]; exact sum_le_sum fun z _ => neg_le_abs _
  have htv : tv P Q = (∑ z ∈ E, |P z - Q z| + ∑ z ∈ Eᶜ, |P z - Q z|) / 2 := by
    rw [tv, sum_add_sum_compl]
  rw [htv, ← sum_sub_distrib, abs_le]
  constructor <;> linarith

/-- `sec:model`: the maximum in `tv = max_E |P(E) - Q(E)|` is attained, at the event
`{z | Q z ≤ P z}`. -/
theorem exists_abs_sub_eq_tv {P Q : α → ℝ} (hsum : ∑ z, P z = ∑ z, Q z) :
    ∃ E : Finset α, |∑ z ∈ E, P z - ∑ z ∈ E, Q z| = tv P Q := by
  classical
  set E : Finset α := univ.filter fun z => Q z ≤ P z with hEdef
  refine ⟨E, ?_⟩
  have htot : ∑ z ∈ E, (P z - Q z) + ∑ z ∈ Eᶜ, (P z - Q z) = 0 := by
    rw [sum_add_sum_compl, sum_sub_distrib, hsum, sub_self]
  have hE : ∑ z ∈ E, |P z - Q z| = ∑ z ∈ E, (P z - Q z) :=
    sum_congr rfl fun z hz => abs_of_nonneg (by simp [E] at hz; linarith)
  have hEc : ∑ z ∈ Eᶜ, |P z - Q z| = -∑ z ∈ Eᶜ, (P z - Q z) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun z hz => abs_of_neg (by simp [E] at hz; linarith)
  have hpos : 0 ≤ ∑ z ∈ E, (P z - Q z) := hE ▸ sum_nonneg fun z _ => abs_nonneg _
  rw [← sum_sub_distrib, abs_of_nonneg hpos, tv, ← sum_add_sum_compl E, hE, hEc]
  linarith

/-- `sec:model`: `TV(P,Q) = max_{E ⊆ Ω} |P(E) - Q(E)|` for vectors of equal total mass, in
particular for probability vectors. Events of a finite set are its finsets. -/
theorem tv_isGreatest {P Q : α → ℝ} (hsum : ∑ z, P z = ∑ z, Q z) :
    IsGreatest (Set.range fun E : Finset α => |∑ z ∈ E, P z - ∑ z ∈ E, Q z|) (tv P Q) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hE⟩ := exists_abs_sub_eq_tv hsum
    exact ⟨E, hE⟩
  · rintro _ ⟨E, rfl⟩
    exact abs_sub_le_tv hsum E

/-- `sec:model`, the identity `TV = max_E |P(E) - Q(E)|` for probability vectors. -/
theorem tv_isGreatest_of_isProbVec {P Q : α → ℝ} (hP : IsProbVec P) (hQ : IsProbVec Q) :
    IsGreatest (Set.range fun E : Finset α => |∑ z ∈ E, P z - ∑ z ∈ E, Q z|) (tv P Q) :=
  tv_isGreatest (by rw [hP.sum_eq_one, hQ.sum_eq_one])

/-- `sec:model`: TV between probability vectors is at most one. -/
theorem tv_le_one {P Q : α → ℝ} (hP : IsProbVec P) (hQ : IsProbVec Q) : tv P Q ≤ 1 := by
  unfold tv
  have h : ∑ z, |P z - Q z| ≤ ∑ z, (P z + Q z) := by
    refine sum_le_sum fun z _ => abs_le.mpr ⟨?_, ?_⟩
    · linarith [hP.nonneg z, hQ.nonneg z]
    · linarith [hP.nonneg z, hQ.nonneg z]
  rw [sum_add_distrib, hP.sum_eq_one, hQ.sum_eq_one] at h
  linarith

/-- `sec:model`, the coupling bound `TV(P,Q) ≤ Pr{U ≠ V}`: if `π` is a nonnegative weight on
`α × α` with marginals `P` and `Q`, then `tv P Q` is at most the `π`-mass off the diagonal. -/
theorem tv_le_coupling [DecidableEq α] {P Q : α → ℝ} (π : α × α → ℝ) (hπ : ∀ z, 0 ≤ π z)
    (hP : ∀ x, ∑ y, π (x, y) = P x) (hQ : ∀ y, ∑ x, π (x, y) = Q y) :
    tv P Q ≤ ∑ z ∈ univ.filter (fun z : α × α => z.1 ≠ z.2), π z := by
  -- off-diagonal masses of row `z` and of column `z`
  set A : α → ℝ := fun z => ∑ y, if z = y then 0 else π (z, y) with hA
  set B : α → ℝ := fun z => ∑ x, if x = z then 0 else π (x, z) with hB
  have hsplitP : ∀ z, P z = π (z, z) + A z := by
    intro z
    rw [← hP z, hA]
    simp only
    have hd : π (z, z) = ∑ y, if z = y then π (z, y) else 0 := by simp
    rw [hd, ← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have hsplitQ : ∀ z, Q z = π (z, z) + B z := by
    intro z
    rw [← hQ z, hB]
    simp only
    have hd : π (z, z) = ∑ x, if x = z then π (x, z) else 0 := by simp
    rw [hd, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have hA0 : ∀ z, 0 ≤ A z := fun z => sum_nonneg fun y _ => by split_ifs <;> simp [hπ]
  have hB0 : ∀ z, 0 ≤ B z := fun z => sum_nonneg fun x _ => by split_ifs <;> simp [hπ]
  have hoff : ∑ z ∈ univ.filter (fun z : α × α => z.1 ≠ z.2), π z = ∑ x, A x := by
    rw [sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    split_ifs <;> simp_all
  have hoff' : ∑ x, A x = ∑ z, B z := by
    simp only [hA, hB]
    exact sum_comm
  have hpt : ∀ z, |P z - Q z| ≤ A z + B z := by
    intro z
    rw [hsplitP z, hsplitQ z]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [hA0 z, hB0 z]
  unfold tv
  rw [hoff]
  have : ∑ z, |P z - Q z| ≤ ∑ z, (A z + B z) := sum_le_sum fun z _ => hpt z
  rw [sum_add_distrib, ← hoff'] at this
  linarith

end Basic

/-! ### Data processing -/

section Processing

variable [Fintype α] [Fintype β]

/-- The pushforward of a weight vector along a map. -/
def push [DecidableEq β] (f : α → β) (P : α → ℝ) : β → ℝ :=
  fun y => ∑ x ∈ univ.filter (fun x => f x = y), P x

theorem sum_push [DecidableEq β] (f : α → β) (P : α → ℝ) : ∑ y, push f P y = ∑ x, P x :=
  sum_fiberwise univ f P

theorem push_isProbVec [DecidableEq β] (f : α → β) {P : α → ℝ} (hP : IsProbVec P) :
    IsProbVec (push f P) :=
  ⟨fun _ => sum_nonneg fun x _ => hP.nonneg x, by rw [sum_push, hP.sum_eq_one]⟩

/-- Data processing (used in `lem:coupling`, "coins and the output program may be included in
the transcript"): a deterministic function of the outcome does not increase TV. -/
theorem tv_push_le [DecidableEq β] (f : α → β) (P Q : α → ℝ) :
    tv (push f P) (push f Q) ≤ tv P Q := by
  unfold tv push
  gcongr
  calc ∑ y, |∑ x ∈ univ.filter (fun x => f x = y), P x
          - ∑ x ∈ univ.filter (fun x => f x = y), Q x|
      ≤ ∑ y, ∑ x ∈ univ.filter (fun x => f x = y), |P x - Q x| := by
        refine sum_le_sum fun y _ => ?_
        rw [← sum_sub_distrib]
        exact abs_sum_le_sum_abs _ _
    _ = ∑ x, |P x - Q x| := sum_fiberwise univ f _

/-- The output law of a stochastic kernel `M` fed with the input law `P`. -/
def kernelPush (M : α → β → ℝ) (P : α → ℝ) : β → ℝ := fun y => ∑ x, P x * M x y

theorem kernelPush_isProbVec {M : α → β → ℝ} (hM : ∀ x, IsProbVec (M x)) {P : α → ℝ}
    (hP : IsProbVec P) : IsProbVec (kernelPush M P) := by
  refine ⟨fun y => sum_nonneg fun x _ => mul_nonneg (hP.nonneg x) ((hM x).nonneg y), ?_⟩
  unfold kernelPush
  rw [sum_comm]
  simp only [← mul_sum, (hM _).sum_eq_one, mul_one, hP.sum_eq_one]

/-- Data processing for a randomized post-processing step: a stochastic kernel does not increase
TV. -/
theorem tv_kernelPush_le {M : α → β → ℝ} (hM : ∀ x, IsProbVec (M x)) (P Q : α → ℝ) :
    tv (kernelPush M P) (kernelPush M Q) ≤ tv P Q := by
  unfold tv kernelPush
  gcongr
  calc ∑ y, |∑ x, P x * M x y - ∑ x, Q x * M x y|
      ≤ ∑ y, ∑ x, |P x - Q x| * M x y := by
        refine sum_le_sum fun y _ => ?_
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun x _ => ?_))
        rw [← sub_mul, abs_mul, abs_of_nonneg ((hM x).nonneg y)]
    _ = ∑ x, |P x - Q x| := by
        rw [sum_comm]
        simp only [← mul_sum, (hM _).sum_eq_one, mul_one]

end Processing

/-! ### Mixtures with a common mixing law -/

/-- TV of two mixtures `(ω, z) ↦ μ ω * P ω z` and `(ω, z) ↦ μ ω * Q ω z` with the same
nonnegative mixing weights is the `μ`-average of the componentwise TV. -/
theorem tv_mix [Fintype Ω] [Fintype β] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (P Q : Ω → β → ℝ) :
    tv (fun z : Ω × β => μ z.1 * P z.1 z.2) (fun z => μ z.1 * Q z.1 z.2) =
      ∑ ω, μ ω * tv (P ω) (Q ω) := by
  unfold tv
  rw [Fintype.sum_prod_type, sum_div]
  refine sum_congr rfl fun ω _ => ?_
  simp only [← mul_sub, abs_mul, abs_of_nonneg (hμ ω), ← mul_sum]
  ring

end LowLogitRank.Coupling
