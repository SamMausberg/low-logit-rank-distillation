import LowLogitRank.Coupling.TV
import LowLogitRank.Coupling.Sequential
import LowLogitRank.Coupling.Words
import LowLogitRank.Coupling.NextBit
import LowLogitRank.Coupling.Transfer

/-!
# Total variation, sequential experiments and `lem:coupling`

* `Coupling/TV.lean`: total variation, the coupling bound, data processing (`sec:model`).
* `Coupling/Sequential.lean`: finite sequential experiments, the general hybrid inequality
  (`eq:target-telescope`) and adaptive transcript bounds (`lem:coupling`).
* `Coupling/Words.lean`: distributions on `{0,1}^T` versus next-bit conditionals (`sec:model`).
* `Coupling/NextBit.lean`: `lem:coupling` for next-bit models, one-bit and complete-suffix
  queries, and `eq:suffix-charge`.
* `Coupling/Transfer.lean`: the transfer step of the second proof of `thm:fixed`.
-/
