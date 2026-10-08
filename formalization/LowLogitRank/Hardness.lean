import LowLogitRank.Hardness.Common
import LowLogitRank.Hardness.Program
import LowLogitRank.Hardness.Teacher
import LowLogitRank.Hardness.State
import LowLogitRank.Hardness.Class
import LowLogitRank.Hardness.Simulation
import LowLogitRank.Hardness.Event
import LowLogitRank.Hardness.Advantage
import LowLogitRank.Hardness.Reduction
import LowLogitRank.Hardness.Transfer
import LowLogitRank.Hardness.WeakError
import LowLogitRank.Hardness.Audit

/-!
# `sec:hardness`, `sec:weak-error`, and the finite audit of `sec:audit`

* `Program.lean`: width-five permutation programs; `R(a) ∈ {-1,1}` for every word.
* `Teacher.lean`: the block layout `X, A, Y, W`, the public schedule, `C(X,A)`, the teacher logits
  `eq:hard-mask`, the parameters `eq:hard-parameters`, and `eq:hard-consistency`.
* `State.lean`: the linear state `(1, X, C, v)` and `eq:counter`; rank `≤ n + 7`.
* `Class.lean`: `lem:hard-teacher`, rationality, the rank lower bound, the label behavior.
* `Simulation.lean`: the simulator and its per-prefix error `η`.
* `Event.lean`: the event mass in the proof of `thm:reduction` and `TV(P_k, D_k)`.
* `Advantage.lean`: `eq:hard-advantage` at `ε = δ = 1/100` and its `0.4801 - o(1)` limit, and the
  `cor:allTV` arithmetic.
* `Reduction.lean`: the real-case event bound and averaging, and the random-function bound of
  `thm:reduction` in a decision-tree model.
* `Transfer.lean`: the transcript transfer `qη` from the teacher to the simulator
  (`lem:coupling`) and the assembled real case of `thm:reduction`.
* `WeakError.lean`: the reset and the multi-block teacher of `cor:allTV` (rank `≤ m + 7`).
* `Audit.lean`: the finite instance of `sec:audit` (`n = 2`, `L = 7`, `T = 128`, `η = 1/65537`),
  and witnesses that `eq:hard-consistency` is satisfiable for every `n` and `L`.

Barrington's theorem and the pseudorandom-function premise are not formalized; the hidden program
enters through the hypothesis `Consistent` (`eq:hard-consistency`). The random case is proved
for membership-query decision trees; that the simulated distinguisher is such a tree is not
formalized.

For `cor:allTV`, the following are formalized: the multi-block teacher with its rank bound
`≤ m + 7` and class membership (`WeakError.lean`), the random case `2^{-r}` with all `r` labels
checked at a fresh payload (`QueryTree.acceptsAll_prob_le`), and the advantage arithmetic
(`weakAdvantage_ge`, `blockCount`, `weak_reduction_accounting`). Not formalized: the closeness of
the multi-block simulator to the teacher and the event mass `(1-η)^{r(L+1)}(1 - q/2^m)`.
The mixed-history-length convention (`sec:mixed-length`, rank `T(n+7)`) is not formalized.
-/
