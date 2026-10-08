import LowLogitRank.Spanner.Prob
import LowLogitRank.Spanner.Compression
import LowLogitRank.Spanner.Feasibility
import LowLogitRank.Spanner.Validation
import LowLogitRank.Spanner.Hoeffding
import LowLogitRank.Spanner.Checks

/-!
# Spanners, feasibility and the validation arithmetic of `sec:finite-bit-gls`

* `Spanner/Prob.lean`: finite probability spaces, union bound.
* `Spanner/Compression.lean`: `lem:compression-spanner` (union bound over index sets, sample size
  `N_s`, existence of a barycentric spanner among the sampled rows).
* `Spanner/Feasibility.lean`: `lem:gls-feasibility`.
* `Spanner/Validation.lean`: the validation threshold of `sec:gls-validation-arithmetic`.
* `Spanner/Hoeffding.lean`: the adapted-indicator Hoeffding bound of
  `sec:gls-validation-arithmetic`.
* `Spanner/Checks.lean`: satisfiability of the hypotheses.
-/
