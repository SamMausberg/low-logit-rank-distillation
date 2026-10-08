import LowLogitRank.Spanner.Compression
import LowLogitRank.Spanner.Feasibility
import LowLogitRank.Spanner.Hoeffding
import LowLogitRank.Spanner.Validation

/-!
# Satisfiability of the hypotheses

Concrete instances showing that the hypotheses of the main statements can hold together.
-/

namespace LowLogitRank.Spanner

open Finset

/-- A probability law on a one-point space. -/
theorem isProb_unit : IsProb (fun _ : Unit => (1 : ℝ)) := ⟨fun _ => zero_le_one, by simp⟩

/-- `compression_spanner`: a valid selection rule exists for every row map, so its hypotheses are
satisfiable (`compression_spanner_exists`); here on a one-point space with a nonzero row. -/
example : ∃ sel : (Fin (Ns 1 (1 / 2) (1 / 2)) → Unit) → Finset (Fin (Ns 1 (1 / 2) (1 / 2))),
    (∀ ω, (sel ω).card ≤ 1 ∧
      LinearIndependent ℝ (fun i : sel ω => (fun _ : Unit => (fun _ : Fin 1 => (1 : ℝ))) (ω i)) ∧
      IsBarySpanner 1 (Set.range fun i => (fun _ : Unit => (fun _ : Fin 1 => (1 : ℝ))) (ω i))
        (fun i : sel ω => (fun _ : Unit => (fun _ : Fin 1 => (1 : ℝ))) (ω i))) ∧
    1 - 1 / 2 ≤ wprob (piW (fun _ : Unit => (1 : ℝ))) {ω | IsDistSpanner (1 / 2) 2
      (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => (fun _ : Fin 1 => (1 : ℝ)))
      (fun i : sel ω => (fun _ : Unit => (fun _ : Fin 1 => (1 : ℝ))) (ω i))} :=
  compression_spanner_exists (η := 1 / 2) (δs := 1 / 2) isProb_unit le_rfl
    (fun _ : Unit => (fun _ : Fin 1 => (1 : ℝ))) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- With a zero oracle every row is representable, so the distributional-spanner hypothesis of
`gls_feasibility` holds with `η = 0`. -/
theorem zero_oracle_isDistSpanner {d : ℕ} (hsel : ℕ → Fin d → List Bool)
    (F : ℕ → Set (List Bool)) (p : NextBit) (t s : ℕ) (hs : s - 1 ≤ t)
    (hp : ∀ h : List Bool, h.length < t → 0 ≤ p h ∧ p h ≤ 1) :
    IsDistSpanner 0 2 (prefixLaw p (s - 1)) (fun h => rowAt (fun _ => 0) F s h.toList)
      (fun i => rowAt (fun _ => 0) F s (hsel s i)) := by
  unfold IsDistSpanner
  have huniv : (fun h : Word (s - 1) => rowAt (fun _ => (0 : ℝ)) F s h.toList) ⁻¹'
      zonotope 2 (fun i => rowAt (fun _ => 0) F s (hsel s i)) = Set.univ := by
    ext h
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    refine ⟨fun _ => 0, fun _ => by norm_num, ?_⟩
    funext f
    simp [rowAt]
  rw [huniv, wprob_univ, (isProb_prefixLaw p hs hp).sum_eq]
  norm_num

/-- The hypotheses of `gls_feasibility` hold for the fair-coin model, a zero oracle and `η = 0`;
the conclusion then says the program is feasible with probability one. -/
example (t : ℕ) (F : ℕ → Set (List Bool)) :
    1 - t * 0 ≤ wprob (prefixLaw (fun _ => 1 / 2) t)
      {y | ∃ c Lh, LPFeasible (fun _ => 0) (fun _ (_ : Fin 1) => []) F y.toList c Lh} := by
  have hp : ∀ h : List Bool, h.length < t → 0 ≤ (fun _ => (1 / 2 : ℝ)) h ∧
      (fun _ => (1 / 2 : ℝ)) h ≤ 1 := fun _ _ => by norm_num
  exact gls_feasibility (fun _ => 0) (fun _ _ => []) F _ t hp le_rfl (fun _ => rfl)
    fun s _ hst => zero_oracle_isDistSpanner (fun _ (_ : Fin 1) => []) F _ t s (by omega) hp

/-- The hypotheses of `adapted_hoeffding` hold for fair coins and the indicator that is always
one. -/
example (K : ℕ) :
    wprob (fun ω : List.Vector Bool K => seqProb (fun _ _ => (1 / 2 : ℝ)) [] ω.toList)
        {ω | ∑ k ∈ range K, ind Set.univ (ω.toList.take (k + 1)) < (K : ℝ) / 3} ≤
      Real.exp (-((K : ℝ) / 18)) := by
  refine adapted_hoeffding K _ Set.univ (fun _ _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun h _ _ => ?_)
  simp [ind]
  norm_num

/-- The hypothesis `E Z > 2 g` of `miss_prob_le` is satisfiable: `Z = 1`, `g = 1/4`. -/
example : 2 * (1 / 4 : ℝ) < expect (fun _ : Unit => (1 : ℝ)) (fun _ => 1) := by
  simp [expect]; norm_num

end LowLogitRank.Spanner
