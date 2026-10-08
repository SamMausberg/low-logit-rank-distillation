import LowLogitRank.Witness.Potential
import LowLogitRank.Witness.General
import LowLogitRank.Witness.Numerics
import LowLogitRank.Witness.Count
import LowLogitRank.Witness.Softmax

/-!
# The explicit witness bound and the validation arithmetic

* `Witness/Potential.lean`: the matrices `M_j = λ I + ∑ φ_i φ_iᵀ`, the matrix determinant lemma,
  the trace–determinant inequality, Cauchy–Schwarz in the `M` inner product, and the elliptical
  potential bound.
* `Witness/General.lean`: the witness bound in general form.
* `Witness/Numerics.lean`: the parameters of `eq:explicit-gls-parameters` and the arithmetic of
  the paragraph "Explicit witness bound".
* `Witness/Count.lean`: the residual estimate (`24Kξ`, `24Kα`) and the final count: every cut
  receives fewer than `64 d J_b` witnesses (`witness_count_lt`). `Envelope/Witness.lean` restates
  it with the parameters of `Envelope.Input` and sums it over the cuts.
* `Witness/Softmax.lean`: the softmax bound and the next-token telescope of
  `sec:gls-validation-arithmetic`.
-/
