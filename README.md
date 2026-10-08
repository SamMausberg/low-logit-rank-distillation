# Learning low-logit-rank distributions from conditional samples

**Samuel Mausberg**

*Learning Low-Logit-Rank Distributions from Conditional Samples.*
Manuscript, a finite structural audit, and a Lean 4 formalization.

**[Read the paper](paper/low_logit_rank_distillation.pdf)** · **[Cite it](CITATION.cff)** ·
**[Lean map](formalization/README.md)**

## Results

The paper studies fully supported distributions on binary strings of length `T` whose centered
next-bit logits have magnitude at most `T` and rank at most `d` at every history cut. The learner
may submit any prefix and receive one sampled next bit.

- Every fixed rank `d` is learnable in polynomial time from such samples, with
  `Õ_d(T^{6d+15})` submitted and generated tokens at fixed accuracy and confidence. The learner
  adds fair-bit noise, approximates the resulting logit transformation by a polynomial, and runs
  a robust logit learner through a cached sampling simulation. A second proof goes through a
  surrogate of low probability rank.
- Under a specified inverse-polynomial probability floor, learning is polynomial in `T` and `d`
  jointly, as a consequence of the published logit simulation of Golowich, Liu and Shetty.
- When the rank grows, strong pseudorandom functions in logarithmic-depth circuits rule out a
  learner polynomial jointly in `T` and `d`.
- Numerical logit simulation needs `e^{2T}/(30ξ²)` samples already at rank one, while
  distribution learning stays polynomial.

## Contents

| Path | Contents |
| --- | --- |
| [`paper/`](paper/) | LaTeX source and PDF (51 pages; the main text ends on page 16). `build.sh` builds it. |
| [`formalization/`](formalization/) | Lean 4 library `LowLogitRank` with Mathlib, the axiom audit `AxiomAudit.lean`, and `verify.py`. [`formalization/README.md`](formalization/README.md) maps each paper statement to its Lean theorems. |
| [`checks/`](checks/) | The exact finite structural audit of the hard construction described in Appendix I, with its recorded output. |

## Verification

- [x] The manuscript builds with no overfull boxes, undefined references or citations.
- [x] All 15 bibliography entries and every pinpoint reference (theorem, lemma, section and page
  numbers, and the two quotations from Golowich, Liu and Shetty) were checked against the
  primary sources.
- [x] The finite audit reproduces its recorded output byte for byte.
- [x] The Lean library builds with warnings treated as errors and with Mathlib's style linters.
  Every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. Theorems
  cite the paper by TeX label.

The formalization covers the paper's own lemmas and constants, including the Chebyshev
approximation on a Bernstein ellipse, both rank lifts, the comparison distributions of the two
positive proofs, the token envelope and witness bound, the hard teacher and its simulator, and
Propositions `prop:cauchy` and `prop:scalar`. The learning theorems of Golowich, Liu and Shetty
and of Liu and Moitra, Barrington's theorem, and the pseudorandom-function assumption enter as
explicit hypotheses. Running-time and bit-complexity claims are not formalized. The
[Lean map](formalization/README.md) lists the coverage statement by statement.

## Building

```sh
make paper     # pdfLaTeX; writes paper/low_logit_rank_distillation.pdf and paper/build.log
make checks    # reruns the finite audit and compares it with the recorded output
make lean      # in formalization/: run `lake exe cache get` first; builds and audits axioms
make lint      # ruff and CITATION.cff validation (pip install -r requirements-dev.txt)
```

The Lean toolchain (`leanprover/lean4:v4.34.0-rc2`) and the Mathlib revision are pinned in
`formalization/`. Continuous integration runs all four targets.

## Citation

```bibtex
@unpublished{mausberg2026lowlogitrank,
  author = {Samuel Mausberg},
  title  = {Learning Low-Logit-Rank Distributions from Conditional Samples},
  year   = {2026},
  note   = {Manuscript},
  url    = {https://github.com/SamMausberg/low-logit-rank-distillation}
}
```

## License

The manuscript and written material are licensed under [CC BY 4.0](LICENSES/CC-BY-4.0.txt).
The Lean formalization, the Python checks and the build scripts are licensed under
[MIT](LICENSES/MIT.txt). See [LICENSE](LICENSE).
