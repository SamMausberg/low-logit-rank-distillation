# Lean formalization

Lean 4 (`leanprover/lean4:v4.34.0-rc2`) with Mathlib at revision `2631d1cc`. The library is
`LowLogitRank`; its root file imports every module. Docstrings cite the paper by TeX label (for
example `lem:coupling`), so the correspondence does not depend on the numbering of the manuscript.

## Building

```sh
lake exe cache get
python3 verify.py
```

`verify.py` scans the sources for `sorry`, `admit`, `axiom`, `native_decide` and similar tokens,
runs `lake build` with warnings treated as errors and with the Mathlib standard linter set
(see `lakefile.toml`; only the Apache-2.0 copyright-header check is off), and runs
`AxiomAudit.lean`. The audit visits every declaration defined in the library and fails unless it
depends only on `propext`, `Classical.choice` and `Quot.sound`. It also lists each theorem whose
docstring cites a paper label. The results go to `lean-verification.json`.

## Map from the paper

All names are in the namespace `LowLogitRank`. Paper statements are named by title and label.

| Paper statement | Main Lean theorems | Coverage |
|---|---|---|
| Model and class `𝒞_{T,d}` (`sec:model`) | `InClass`, `logitCutMatrix`, `probCutMatrix`, `probRank`, `Coupling.wordDist_condOfDist`, `Coupling.condOfDist_wordDist` | Definitions; every fully supported distribution on `{0,1}^T` is given by its next-bit probabilities. |
| Uniform conditional comparison (`lem:coupling`), `eq:target-telescope`, `eq:suffix-charge` | `Coupling.tv_condProb_le_mul`, `Coupling.tv_wordDist_le_mul`, `Coupling.tv_suffixQuery_le`, `Coupling.tv_bitQuery_le`, `Coupling.tv_wordDist_le_sum` | Formalized, including adaptive randomized transcripts of complete-suffix and one-bit queries. |
| Polynomial approximation of the smoothed logit (`lem:softclip-poly`), polynomial probabilities (`lem:poly-sigmoid`) | `Chebyshev.chebyshevApprox`, `Assembly.softclip_poly`, `Assembly.poly_sigmoid` | Formalized: the Bernstein-ellipse Chebyshev theorem (contour shift, Fourier series, coefficient decay) and both lemmas with the stated degrees. |
| Polynomial transformation of the logit matrices (`lem:logit-lift`), sequential polynomial lifting (`lem:lift`) | `PolyRank.rank_logitCutMatrix_logitLift_le`, `PolyRank.probRank_lift_le`, `PolyRank.card_monomials` | Formalized, with the monomial count `binom(d+k, d)`. |
| Smoothing, `eq:softclip`, `eq:smoothing-tv`, `eq:smoothed-polynomial-tv`, `eq:smooth-parameters`, `eq:smooth-budget` (proof of `thm:fixed`) | `Assembly.comparison_distribution`, `Assembly.fixed_rank_comparison_envelope`, `Params.logit_smooth`, `Params.smooth_budget` | The comparison distribution `P°` with every bound and parameter inequality of the proof; the envelope bounds are discharged. The learning guarantee of the robust learner (GLS Theorem 5.11) and the coupling of cached estimates are not formalized. |
| Second proof of `thm:fixed` (`sec:probability-route`), `eq:fixed-parameters`, `eq:combined-budget` | `Assembly.surrogate`, `Assembly.fixed_second_proof`, `Params.pr_combined_budget`, `Coupling.transfer` | Formalized relative to one hypothesis: the Liu–Moitra guarantee (`thm:lm`) for the given learner on distributions of probability rank at most `R`. |
| Token envelope (`lem:explicit-gls-token-envelope`), `eq:explicit-gls-tolerance`, `eq:explicit-gls-request-caps`, `eq:global-future-dimension` | `Envelope.Input.explicit_gls_token_envelope`, `Envelope.Input.xi_tolerance`, `Envelope.Input.witness_count_lt`, `Envelope.Input.witnesses_total_lt` | All numerical claims, the counting, and the determinant witness bound. The statistical guarantees of the robust learner enter as stated assumptions. |
| Distributional spanners (`lem:compression-spanner`), feasibility (`lem:gls-feasibility`), validation and Hoeffding steps (`sec:gls-validation-arithmetic`) | `Spanner.compression_spanner`, `Spanner.gls_feasibility`, `Spanner.prob_gt_of_expect_gt`, `Spanner.adapted_hoeffding`, `Witness.tv_softmax_le` | Formalized for finitely supported row laws (as in the application). The basis-exchange procedure is replaced by an existence argument. |
| Approximate projection (`lem:approx-projection`), finite-bit LM details (`sec:finite-bit-lm`) | `Projection.approx_projection`, `Projection.spanner_l1_bound`, `Projection/*` | The lemma in full; the precision, ellipsoid and rounding inequalities. The rational SVD, ellipsoid iteration counts and bit lengths are not formalized. |
| Hard teacher (`lem:hard-teacher`), simulation, explicit reduction (`thm:reduction`), `eq:hard-advantage` | `Hardness.hardTeacher_inClass`, `Hardness.hardTeacher_rank_ge`, `Hardness.simulator_close_hard`, `Hardness.tv_transcript_simulator_le`, `Hardness.hardTeacher_eventMass`, `Hardness.reduction_real_case`, `Hardness.accept_prob_le_half`, `Hardness.hardAdvantage_ge_hard` | The teacher's class membership, rank bounds, simulator error, the transcript transfer `qη`, event mass, TV to the ideal generator, the real-case acceptance bound, the random-function case (adaptive query trees) and the advantage arithmetic. The random case is proved for query trees; compiling the simulated distinguisher into one is not formalized. Barrington's theorem enters as the consistency hypothesis `eq:hard-consistency`; the pseudorandom-function assumption is not formalized. |
| Weak TV error (`cor:allTV`), power-law logits (`cor:power-logits`) | `Hardness.multiTeacher_inClass_hard`, `Params.abs_le_rpow_of_pad` | Multi-block rank and class membership, the `2^{-r}` random case, and the arithmetic. |
| Exponential probability rank (`prop:cauchy`) | `Cauchy.prop_cauchy` | Formalized for every `T ≥ 1`. |
| Scalar lower bound (`prop:scalar`), root estimate (`lem:gls-root-simulation`) | `Scalar.prop_scalar`, `Scalar.gls_root_simulation` | Formalized for capped adaptive algorithms with finitely many coins, through the stopped-transcript chain rule, data processing and Pinsker's inequality. |
| Tenfold crossover (`sec:crossover`, `cor:tenfold2048`) | `Crossover.crossover`, `Crossover.tenfold2048`, `Crossover.tenfold2048_root` | All numerical comparisons, combined with the lower bound of `prop:scalar` on the same teacher. |
| Bounded factors (`lem:bounded-factors`), canonical coordinates and cover (`thm:cover`, `eq:mesh`, `eq:bestKL`, `eq:samples`) | `MaxVolume.bounded_factors`, `MaxVolume.exists_canonical_binary`, `Cover.cover_sample_bound` | The maximum-volume lemma and the statistical part of `thm:cover` end to end. Running time and the NP-oracle search are not formalized. |
| Probability floor (`sec:floor`, `lem:floor-estimator`), noisy parity (`sec:parity`), finite alphabet (`thm:alphabet`) | `Floor.floor_estimator_good_event`, `Parity.parityModel_inClass`, `AlphabetAlgebra.alphabet_normalization` | The deterministic steps and parameter arithmetic. Multiplicative Chernoff bounds and the multivariate approximation of `thm:alphabet` are not formalized. |
| Finite audit (`sec:audit`) | `Hardness.audit_inClass` | The audit instance's class membership, copy error and TV identity. |

## Hypotheses that stand in for cited results

- The learning theorems of Golowich, Liu and Shetty (Theorem 5.11) and of Liu and Moitra
  (Theorem 1.3) are not formalized. `Assembly.fixed_second_proof` takes the Liu–Moitra guarantee for
  the given learner as the hypothesis `hLM`.
- Barrington's theorem and the public-sweep compilation enter as `Hardness.Consistent`
  (`eq:hard-consistency`). Satisfiable instances are included.
- The faithfulness contract of the GLS sampling simulation enters `Scalar.gls_root_simulation`
  and `Crossover.tenfold2048_root` as a hypothesis.

## Not formalized

- Bit complexity, running time, polynomial description length and generation cost.
- Probability statements resting on multiplicative Chernoff bounds or Hoeffding's inequality for
  independent samples (their exponent arithmetic is formalized).
- The coupling of cached numerical estimates in the first proof of `thm:fixed`.
- The multivariate Chebyshev approximation in `thm:alphabet`, and the mixed-history-length
  convention (`sec:mixed-length`).
- The pseudorandom-function and Naor–Reingold assumptions.
