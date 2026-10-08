import LowLogitRank.Basic

/-!
# Finite probability spaces

Probabilities are finite weighted sums. `wprob μ E` is the total weight of the event `E` under the
weights `μ`, and `piW D` is the product weight of `D` on tuples (independent draws).
-/

namespace LowLogitRank.Spanner

open Finset

section Weights

variable {α : Type*} [Fintype α]

/-- The probability of the event `E` under the weights `μ`. -/
noncomputable def wprob (μ : α → ℝ) (E : Set α) : ℝ := ∑ a, E.indicator μ a

/-- Probability weights: nonnegative with total weight one. -/
structure IsProb (μ : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ μ a
  sum_eq : ∑ a, μ a = 1

theorem wprob_nonneg {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) (E : Set α) : 0 ≤ wprob μ E :=
  Finset.sum_nonneg fun a _ => Set.indicator_nonneg (fun b _ => hμ b) a

theorem wprob_mono {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) {E F : Set α} (h : E ⊆ F) :
    wprob μ E ≤ wprob μ F :=
  Finset.sum_le_sum fun a _ => Set.indicator_le_indicator_of_subset h (fun b => hμ b) a

theorem wprob_univ (μ : α → ℝ) : wprob μ Set.univ = ∑ a, μ a := by
  simp [wprob]

theorem wprob_add_compl (μ : α → ℝ) (E : Set α) : wprob μ E + wprob μ Eᶜ = ∑ a, μ a := by
  simp only [wprob, ← Finset.sum_add_distrib, Set.indicator_self_add_compl_apply]

theorem wprob_compl {μ : α → ℝ} (hμ : IsProb μ) (E : Set α) : wprob μ Eᶜ = 1 - wprob μ E := by
  have := wprob_add_compl μ E
  rw [hμ.sum_eq] at this
  linarith

theorem wprob_le_one {μ : α → ℝ} (hμ : IsProb μ) (E : Set α) : wprob μ E ≤ 1 := by
  have h1 := wprob_add_compl μ E
  have h2 := wprob_nonneg hμ.nonneg Eᶜ
  rw [hμ.sum_eq] at h1
  linarith

theorem wprob_union_le {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) (E F : Set α) :
    wprob μ (E ∪ F) ≤ wprob μ E + wprob μ F := by
  unfold wprob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  classical
  simp only [Set.indicator_apply, Set.mem_union]
  have := hμ a
  split_ifs <;> simp_all

/-- `lem:gls-feasibility`, union-bound step: the probability of a finite union is at most the sum
of the probabilities. -/
theorem wprob_biUnion_le {ι : Type*} {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) (s : Finset ι)
    (E : ι → Set α) : wprob μ (⋃ k ∈ s, E k) ≤ ∑ k ∈ s, wprob μ (E k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wprob]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.set_biUnion_insert]
    exact (wprob_union_le hμ _ _).trans (by linarith)

/-- `lem:gls-feasibility`, union-bound step: if each of `t = #s` events has probability at most
`η`, their union has probability at most `t η`. -/
theorem wprob_biUnion_le_card_mul {ι : Type*} {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) (s : Finset ι)
    (E : ι → Set α) {η : ℝ} (hE : ∀ k ∈ s, wprob μ (E k) ≤ η) :
    wprob μ (⋃ k ∈ s, E k) ≤ s.card * η := by
  refine (wprob_biUnion_le hμ s E).trans ?_
  simpa using Finset.sum_le_sum hE

/-- Expectation of `Z` under the weights `μ`. -/
def expect (μ : α → ℝ) (Z : α → ℝ) : ℝ := ∑ a, μ a * Z a

end Weights

section Product

variable {Ω : Type*}

/-- Product weights on tuples: the law of independent draws from `D`. -/
def piW {ι : Type*} [Fintype ι] (D : Ω → ℝ) (ω : ι → Ω) : ℝ := ∏ i, D (ω i)

theorem piW_nonneg {ι : Type*} [Fintype ι] {D : Ω → ℝ} (hD : ∀ w, 0 ≤ D w) (ω : ι → Ω) :
    0 ≤ piW D ω :=
  Finset.prod_nonneg fun i _ => hD (ω i)

/-- For independent coordinates, the probability that every coordinate lies in `A` is the `n`-th
power of the probability of `A`. -/
theorem wprob_pi_forall [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Ω → ℝ)
    (A : Set Ω) :
    wprob (piW D) {ω : ι → Ω | ∀ i, ω i ∈ A} = wprob D A ^ Fintype.card ι := by
  unfold wprob
  rw [← Finset.card_univ, ← Finset.prod_const, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, piW]
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => by simp [h i]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

theorem isProb_piW [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] {D : Ω → ℝ} (hD : IsProb D) :
    IsProb (piW (ι := ι) D) := by
  refine ⟨piW_nonneg hD.nonneg, ?_⟩
  have := wprob_pi_forall (ι := ι) D Set.univ
  simpa [wprob_univ, hD.sum_eq] using this

end Product

end LowLogitRank.Spanner
