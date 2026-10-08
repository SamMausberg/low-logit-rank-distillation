import LowLogitRank.Crossover
import LowLogitRank.Scalar

/-!
# The tenfold crossover against the root lower bound (`sec:crossover`, `cor:tenfold2048`)

`Crossover.lean` compares the envelope's token count with the number `e^{2T}/(30 ξ²)`;
`Scalar.gls_root_simulation` shows that a capped adaptive algorithm (finite model
`Scalar.CappedAlgo`) that is faithful at the root has expected reply count above that number on
the teacher `P₀` of `prop:scalar`. This file composes the two. The faithfulness of the root
component (accuracy `ξ` with probability `0.99` on both teachers of `prop:scalar`) stays a
hypothesis, as in `gls_root_simulation`. The crossover statements take a natural `T`; the scalar
statements are applied at the real number `(T : ℝ)`.
-/

namespace LowLogitRank.Crossover

open Finset Scalar

/-- `prop:scalar`: the teacher `P₀` with initial logit `-T` lies in `𝒞_{T,d}` for every
`d ≥ 1`. -/
theorem teacher0_inClass_of_one_le {T d : ℕ} (hd : 1 ≤ d) : InClass T d (teacher (-T)) :=
  let h := teacher0_inClass T
  ⟨h.fullSupport, h.logit_le, fun t ht => (h.rank_le t ht).trans hd⟩

/-- `sec:crossover` with `lem:gls-root-simulation`: for `0 < ε, δ < 1/2`, `d ≥ 1`, every natural
`T ≥ T_10` and every tolerance `0 < ξ ≤ 1/6`, let `A` be a capped adaptive algorithm that outputs
a token `U₁ = token ω r` and a root component `a = comp ω r` within `ξ` of `(2U₁ - 1) ℓ_P(∅)` with
probability at least `0.99` under both teachers of `prop:scalar` (the faithfulness hypotheses
`h0`, `h1`). Then the teacher `P₀` lies in `𝒞_{T,d}`, and for every reply count `M` dominating the
empty-prefix replies, ten times the envelope's token formula `Input.tokens` (with the parameters
of `alg:fixed`) is below `E_{P₀}[M]`. -/
theorem crossover_root {d : ℕ} (hd : 1 ≤ d) {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) {T : ℕ} (hT : T10 d ε δ ≤ T) {ξ : ℝ} (hξ0 : 0 < ξ)
    (hξ1 : ξ ≤ 1 / 6) {Ω : Type*} [Fintype Ω] {n : ℕ} (A : CappedAlgo Ω n)
    (token : Ω → Word n → Bool) (comp : Ω → Word n → ℝ)
    (h0 : 99 / 100 ≤ A.prob (teacher (-T)) (univ.filter fun z =>
      |comp z.1 z.2 - sgn (token z.1 z.2) * logit (teacher (-T)) []| ≤ ξ))
    (h1 : 99 / 100 ≤ A.prob (teacher (-T + 3 * ξ)) (univ.filter fun z =>
      |comp z.1 z.2 - sgn (token z.1 z.2) * logit (teacher (-T + 3 * ξ)) []| ≤ ξ))
    (M : Ω × Word n → ℝ) (hM : ∀ z, (A.emptyCount z : ℝ) ≤ M z) :
    InClass T d (teacher (-T)) ∧
      10 * (envInput T d ε δ).tokens < A.expect (teacher (-T)) M :=
  ⟨teacher0_inClass_of_one_le hd, (crossover_envelope hε0 hε1 hδ0 hδ1 hT hξ0 hξ1).trans_lt
    (gls_root_simulation A T ξ hξ0 hξ1 token comp h0 h1 M hM)⟩

/-- `cor:tenfold2048` with `lem:gls-root-simulation`: for `d = 1`, `ε = δ = 1/100`, every natural
`T ≥ 2048`, every tolerance `0 < ξ ≤ 1/6` and every capped adaptive algorithm `A` that is faithful
at the root as in `crossover_root` (hypotheses `h0`, `h1`), the teacher `P₀` lies in `𝒞_{T,1}`
and ten times the envelope's token formula is below `E_{P₀}[M]` for every reply count `M`
dominating the empty-prefix replies. -/
theorem tenfold2048_root {T : ℕ} (hT : 2048 ≤ T) {ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6)
    {Ω : Type*} [Fintype Ω] {n : ℕ} (A : CappedAlgo Ω n)
    (token : Ω → Word n → Bool) (comp : Ω → Word n → ℝ)
    (h0 : 99 / 100 ≤ A.prob (teacher (-T)) (univ.filter fun z =>
      |comp z.1 z.2 - sgn (token z.1 z.2) * logit (teacher (-T)) []| ≤ ξ))
    (h1 : 99 / 100 ≤ A.prob (teacher (-T + 3 * ξ)) (univ.filter fun z =>
      |comp z.1 z.2 - sgn (token z.1 z.2) * logit (teacher (-T + 3 * ξ)) []| ≤ ξ))
    (M : Ω × Word n → ℝ) (hM : ∀ z, (A.emptyCount z : ℝ) ≤ M z) :
    InClass T 1 (teacher (-T)) ∧
      10 * (envInput T 1 (1 / 100) (1 / 100)).tokens < A.expect (teacher (-T)) M :=
  ⟨teacher0_inClass T, (tenfold2048_envelope hT hξ0 hξ1).trans
    (gls_root_simulation A T ξ hξ0 hξ1 token comp h0 h1 M hM)⟩

end LowLogitRank.Crossover
