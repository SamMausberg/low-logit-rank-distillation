import LowLogitRank.Coupling.NextBit

/-!
# Transfer of a learning guarantee between close oracles (`sec:probability-route`)

The logical structure of "A second proof of Theorem `thm:fixed`": a randomized learner makes `q`
complete conditional suffix queries and outputs a distribution on `{0,1}^T` computed from its
coin and its transcript. If it succeeds (TV at most `a`) with probability at least `1 - a` when
run against an ideal model `p̃`, and the actual model `p` satisfies `|p - p̃| ≤ η` before time
`T` with `(q + 1) T η ≤ a` (`eq:combined-budget`), then against `p` it reaches TV at most `2a`
with probability at least `1 - 2a`. The success guarantee under `p̃` (Theorem `thm:lm` applied to
the comparison distribution) is a hypothesis here; probabilities are sums of the joint
(coin, transcript) law over events. `Assembly.fixed_second_proof` assembles the second proof,
with Theorem `thm:lm` for the learner as its only hypothesis.
-/

namespace LowLogitRank.Coupling

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- The joint law of the learner's coin and its `n` complete-suffix replies under the oracle
`p`. -/
noncomputable def suffixJoint (μ : Ω → ℝ) (p : NextBit) (T : ℕ)
    (query : Ω → List (Word T) → List Bool) (n : ℕ) : Ω × List.Vector (Word T) n → ℝ :=
  jointLaw μ (fun ω x => suffixReply p T (query ω x)) n

theorem suffixJoint_isProbVec {μ : Ω → ℝ} (hμ : IsProbVec μ) {p : NextBit} {T : ℕ}
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (query : Ω → List (Word T) → List Bool) (n : ℕ)
    (hquery : ∀ ω, ∀ x : List (Word T), x.length < n → (query ω x).length ≤ T) :
    IsProbVec (suffixJoint μ p T query n) :=
  jointLaw_isProbVec hμ _ n fun ω x hx => suffixReply_isProbVec hp (hquery ω x hx)

/-- The second proof of `thm:fixed` (`sec:probability-route`), transfer step: with the ideal
oracle `p̃` the learner's output is within TV `a` of `wordDist p̃ T` with probability at least
`1 - a` (hypothesis `hideal`, standing for Theorem `thm:lm`); with the actual oracle `p` the
same learner's output is within TV `2a` of `wordDist p T` with probability at least `1 - 2a`.
This combines the transcript bound `q T η ≤ a` and `TV(P, P̃) ≤ T η ≤ a` of `lem:coupling`. -/
theorem transfer {μ : Ω → ℝ} (hμ : IsProbVec μ) (T q : ℕ)
    (query : Ω → List (Word T) → List Bool)
    (hquery : ∀ ω, ∀ x : List (Word T), x.length < q → (query ω x).length ≤ T)
    (out : Ω → List.Vector (Word T) q → Word T → ℝ)
    (p pt : NextBit) (η a : ℝ)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hpt : ∀ h : List Bool, h.length < T → 0 ≤ pt h ∧ pt h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - pt h| ≤ η)
    (hbudget : ((q : ℝ) + 1) * T * η ≤ a)
    (hideal : 1 - a ≤ ∑ z ∈ univ.filter
        (fun z : Ω × List.Vector (Word T) q => tv (wordDist pt T) (out z.1 z.2) ≤ a),
        suffixJoint μ pt T query q z) :
    1 - 2 * a ≤ ∑ z ∈ univ.filter
        (fun z : Ω × List.Vector (Word T) q => tv (wordDist p T) (out z.1 z.2) ≤ 2 * a),
        suffixJoint μ p T query q z := by
  have hJ := suffixJoint_isProbVec hμ hp query q hquery
  have hJt := suffixJoint_isProbVec hμ hpt query q hquery
  have hTη : 0 ≤ (T : ℝ) * η := mul_eta_nonneg hη
  have hqTη : 0 ≤ (q : ℝ) * T * η := by
    rw [mul_assoc]; exact mul_nonneg (Nat.cast_nonneg _) hTη
  have hsplit : ((q : ℝ) + 1) * T * η = q * T * η + T * η := by ring
  have htv : tv (suffixJoint μ p T query q) (suffixJoint μ pt T query q) ≤ q * T * η :=
    tv_suffixQuery_le hμ p pt T q η query hp hpt hη hquery
  have hdist : tv (wordDist p T) (wordDist pt T) ≤ T * η := tv_wordDist_le_mul p pt T η hp hpt hη
  have hsub : univ.filter (fun z : Ω × List.Vector (Word T) q =>
        tv (wordDist pt T) (out z.1 z.2) ≤ a)
      ⊆ univ.filter (fun z : Ω × List.Vector (Word T) q =>
          tv (wordDist p T) (out z.1 z.2) ≤ 2 * a) := by
    intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    linarith [tv_triangle (wordDist p T) (wordDist pt T) (out z.1 z.2)]
  have h1 := sum_le_sum_of_subset_of_nonneg (f := suffixJoint μ p T query q) hsub
    fun z _ _ => hJ.nonneg z
  have h2 := abs_sub_le_tv (P := suffixJoint μ p T query q) (Q := suffixJoint μ pt T query q)
    (by rw [hJ.sum_eq_one, hJt.sum_eq_one])
    (univ.filter fun z : Ω × List.Vector (Word T) q => tv (wordDist pt T) (out z.1 z.2) ≤ a)
  have h3 := (abs_le.mp (h2.trans htv)).1
  linarith

/-- The transfer in the form used in the paper: with `2a ≤ ε` and `2a ≤ δ`, the learner run
against `p` outputs a distribution within TV `ε` of `wordDist p T` with probability at least
`1 - δ`. -/
theorem transfer_eps_delta {μ : Ω → ℝ} (hμ : IsProbVec μ) (T q : ℕ)
    (query : Ω → List (Word T) → List Bool)
    (hquery : ∀ ω, ∀ x : List (Word T), x.length < q → (query ω x).length ≤ T)
    (out : Ω → List.Vector (Word T) q → Word T → ℝ)
    (p pt : NextBit) (η a ε δ : ℝ)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hpt : ∀ h : List Bool, h.length < T → 0 ≤ pt h ∧ pt h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - pt h| ≤ η)
    (hbudget : ((q : ℝ) + 1) * T * η ≤ a) (hε : 2 * a ≤ ε) (hδ : 2 * a ≤ δ)
    (hideal : 1 - a ≤ ∑ z ∈ univ.filter
        (fun z : Ω × List.Vector (Word T) q => tv (wordDist pt T) (out z.1 z.2) ≤ a),
        suffixJoint μ pt T query q z) :
    1 - δ ≤ ∑ z ∈ univ.filter
        (fun z : Ω × List.Vector (Word T) q => tv (wordDist p T) (out z.1 z.2) ≤ ε),
        suffixJoint μ p T query q z := by
  have h := transfer hμ T q query hquery out p pt η a hp hpt hη hbudget hideal
  have hJ := suffixJoint_isProbVec hμ hp query q hquery
  have hsub : univ.filter (fun z : Ω × List.Vector (Word T) q =>
        tv (wordDist p T) (out z.1 z.2) ≤ 2 * a)
      ⊆ univ.filter (fun z : Ω × List.Vector (Word T) q =>
          tv (wordDist p T) (out z.1 z.2) ≤ ε) := by
    intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    linarith
  have h1 := sum_le_sum_of_subset_of_nonneg (f := suffixJoint μ p T query q) hsub
    fun z _ _ => hJ.nonneg z
  linarith

/-- The success hypothesis `hideal` of `transfer` is satisfiable: a learner whose output map
always returns `wordDist p̃ T` succeeds with probability one. -/
theorem transfer_hideal_satisfiable {μ : Ω → ℝ} (hμ : IsProbVec μ) (T q : ℕ)
    (query : Ω → List (Word T) → List Bool)
    (hquery : ∀ ω, ∀ x : List (Word T), x.length < q → (query ω x).length ≤ T)
    (out : Ω → List.Vector (Word T) q → Word T → ℝ)
    (pt : NextBit) (hpt : ∀ h : List Bool, h.length < T → 0 ≤ pt h ∧ pt h ≤ 1)
    (hout : ∀ ω v, out ω v = wordDist pt T) (a : ℝ) (ha : 0 ≤ a) :
    1 - a ≤ ∑ z ∈ univ.filter
        (fun z : Ω × List.Vector (Word T) q => tv (wordDist pt T) (out z.1 z.2) ≤ a),
        suffixJoint μ pt T query q z := by
  have hJ := suffixJoint_isProbVec hμ hpt query q hquery
  simp [hout, ha, hJ.sum_eq_one]

end LowLogitRank.Coupling
