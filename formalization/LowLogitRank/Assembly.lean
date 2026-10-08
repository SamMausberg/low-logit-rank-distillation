import LowLogitRank.Chebyshev
import LowLogitRank.Approximation
import LowLogitRank.PolyRank
import LowLogitRank.Coupling
import LowLogitRank.Params
import LowLogitRank.Crossover

/-!
# Assembly of the comparison distributions

The two positive proofs of `thm:fixed` each define one comparison distribution across all cuts:
`P°` with logits `r(ℓ_P(h))` (`sec:fixed-rank`) and `P̃` with next-bit probabilities `g(ℓ_P(h))`
(`sec:probability-route`). This file combines the Chebyshev theorem, the two approximation lemmas
and the polynomial rank lifts into unconditional statements about these distributions, and
assembles the second proof of `thm:fixed` with Theorem `thm:lm` as its only hypothesis
(`fixed_second_proof`).
-/

namespace LowLogitRank.Assembly

/-- `lem:softclip-poly`: a real polynomial of degree at most `⌈3T log(4T(M_τ+2)/ζ)⌉` within `ζ`
of `ψ_τ` on `[-T, T]`. -/
theorem softclip_poly {T τ ζ : ℝ} (hT : 1 ≤ T) (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (hζ0 : 0 < ζ)
    (hζ1 : ζ < 1) :
    ∃ r : Polynomial ℝ, r.natDegree ≤ ⌈3 * T * Real.log (4 * T * (softclipBound τ + 2) / ζ)⌉₊ ∧
      ∀ u ∈ Set.Icc (-T) T, |r.eval u - softclip τ u| ≤ ζ :=
  Approximation.softclip_poly_of Chebyshev.chebyshevApprox hT hτ0 hτ1 hζ0 hζ1

/-- `lem:poly-sigmoid`: a real polynomial `g` of degree at most `⌈3T log(12T/η)⌉` with
`0 < g < 1` and `|g(u) - σ(2u)| ≤ η` on `[-T, T]`. -/
theorem poly_sigmoid {T η : ℝ} (hT : 1 ≤ T) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ g : Polynomial ℝ, g.natDegree ≤ ⌈3 * T * Real.log (12 * T / η)⌉₊ ∧
      ∀ u ∈ Set.Icc (-T) T, 0 < g.eval u ∧ g.eval u < 1 ∧ |g.eval u - sigmoid (2 * u)| ≤ η :=
  Approximation.poly_sigmoid_of Chebyshev.chebyshevApprox hT hη0 hη1

/-- `lem:softclip-poly` and `lem:logit-lift` together: for `P ∈ 𝒞_{T,d}` and every degree
`k` at least the bound of `lem:softclip-poly`, there is one polynomial `r` of degree `≤ k`,
within `ζ` of `ψ_τ` on `[-T, T]`, such that the single distribution `P°` with logits
`ℓ_{P°}(h) = r(ℓ_P(h))` is fully supported, has logits of magnitude at most `M_τ + ζ`, and has
logit rank at most `D = binom(d + k, d)` at every cut. -/
theorem comparison_logitClass {p : NextBit} {T d k : ℕ} (hT : 1 ≤ T) (hp : InClass T d p)
    {τ ζ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hk : ⌈3 * (T : ℝ) * Real.log (4 * T * (softclipBound τ + 2) / ζ)⌉₊ ≤ k) :
    ∃ r : Polynomial ℝ, r.natDegree ≤ k ∧
      (∀ u : ℝ, |u| ≤ T → |r.eval u - softclip τ u| ≤ ζ) ∧
      LogitClass T (softclipBound τ + ζ) (Nat.choose (d + k) d)
        (ofLogit fun h => r.eval (logit p h)) := by
  obtain ⟨r, hdeg, happ⟩ := softclip_poly (T := (T : ℝ)) (by exact_mod_cast hT) hτ0 hτ1 hζ0 hζ1
  have happ' : ∀ u : ℝ, |u| ≤ T → |r.eval u - softclip τ u| ≤ ζ :=
    fun u hu => happ u (abs_le.mp hu)
  exact ⟨r, hdeg.trans hk, happ',
    PolyRank.logitLift_inClass hp hτ0 (by linarith) r (hdeg.trans hk) happ'⟩

/-- `lem:poly-sigmoid`, `eq:surrogate` and `lem:lift` together: for `P ∈ 𝒞_{T,d}` and every
degree `k` at least the bound of `lem:poly-sigmoid`, there is one polynomial `g` of degree `≤ k`
such that the single distribution `P̃` with `P̃(1 | h) = g(ℓ_P(h))` is fully supported, is
uniformly within `η` of `P` in every next-bit probability, and has probability rank at most
`R = binom(d + Tk, d)`. -/
theorem surrogate {p : NextBit} {T d k : ℕ} (hT : 1 ≤ T) (hp : InClass T d p) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hk : ⌈3 * (T : ℝ) * Real.log (12 * T / η)⌉₊ ≤ k) :
    ∃ g : Polynomial ℝ, g.natDegree ≤ k ∧
      FullSupport T (fun h => g.eval (logit p h)) ∧
      (∀ h : List Bool, h.length < T → |g.eval (logit p h) - p h| ≤ η) ∧
      probRank (fun h => g.eval (logit p h)) T ≤ Nat.choose (d + T * k) d := by
  obtain ⟨g, hdeg, hg⟩ := poly_sigmoid (T := (T : ℝ)) (by exact_mod_cast hT) hη0 hη1
  have hg' : ∀ h : List Bool, h.length < T →
      0 < g.eval (logit p h) ∧ g.eval (logit p h) < 1 ∧
        |g.eval (logit p h) - sigmoid (2 * logit p h)| ≤ η :=
    fun h hh => hg _ (abs_le.mp (hp.logit_le h hh))
  refine ⟨g, hdeg.trans hk, fun h hh => ⟨(hg' h hh).1, (hg' h hh).2.1⟩, fun h hh => ?_,
    PolyRank.probRank_lift_le hp g (hdeg.trans hk)⟩
  obtain ⟨h0, h1⟩ := hp.fullSupport h hh
  have hσ : sigmoid (2 * logit p h) = p h := ofLogit_logit h0 h1
  simpa [hσ] using (hg' h hh).2.2

/-- `sec:fixed-rank`, the comparison distributions of the main proof, for general `τ`, `ζ`, `k`.
For `P ∈ 𝒞_{T,d}`:
* `P^τ` has the conditional floor `τ/2`, satisfies `eq:smoothing-tv`, and has centered logit
  `ψ_τ(ℓ_P(h))` (`eq:softclip`);
* there is one polynomial `r` of degree `≤ k` such that `P°`, with logits `r(ℓ_P(h))`, is fully
  supported with logits bounded by `M_τ + ζ` and logit rank at most `binom(d + k, d)` at every cut
  (`lem:softclip-poly`, `lem:logit-lift`), and is uniformly within `ζ` of `P^τ` in every next-bit
  probability, hence within `Tζ` in TV (`eq:smoothed-polynomial-tv`). -/
theorem comparison_distribution {p : NextBit} {T d k : ℕ} (hT : 1 ≤ T) (hp : InClass T d p)
    {τ ζ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1 / 2) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hk : ⌈3 * (T : ℝ) * Real.log (4 * T * (softclipBound τ + 2) / ζ)⌉₊ ≤ k) :
    ∃ r : Polynomial ℝ, r.natDegree ≤ k ∧
      (∀ u : ℝ, |u| ≤ T → |r.eval u - softclip τ u| ≤ ζ) ∧
      (∀ h : List Bool, h.length < T → τ / 2 ≤ smooth τ p h ∧ smooth τ p h ≤ 1 - τ / 2) ∧
      tv (wordDist p T) (wordDist (smooth τ p) T) ≤ T * (τ / 2) ∧
      (∀ h : List Bool, h.length < T → logit (smooth τ p) h = softclip τ (logit p h)) ∧
      LogitClass T (softclipBound τ + ζ) (Nat.choose (d + k) d)
        (ofLogit fun h => r.eval (logit p h)) ∧
      (∀ h : List Bool, h.length < T →
        |ofLogit (fun h => r.eval (logit p h)) h - smooth τ p h| ≤ ζ) ∧
      tv (wordDist (ofLogit fun h => r.eval (logit p h)) T) (wordDist (smooth τ p) T) ≤ T * ζ := by
  obtain ⟨r, hdeg, happ, hclass⟩ := comparison_logitClass hT hp hτ0 hτ1 hζ0 hζ1 hk
  have hunit := Coupling.FullSupport.unitInterval hp.fullSupport
  have hsm : ∀ h : List Bool, h.length < T →
      τ / 2 ≤ smooth τ p h ∧ smooth τ p h ≤ 1 - τ / 2 ∧ |smooth τ p h - p h| ≤ τ / 2 :=
    fun h hh => Params.smooth_bounds hτ0.le (by linarith) (hunit h hh).1 (hunit h hh).2
  have hsmU : ∀ h : List Bool, h.length < T → 0 ≤ smooth τ p h ∧ smooth τ p h ≤ 1 :=
    fun h hh => ⟨by linarith [(hsm h hh).1], by linarith [(hsm h hh).2.1]⟩
  have hclose : ∀ h : List Bool, h.length < T →
      |ofLogit (fun h => r.eval (logit p h)) h - smooth τ p h| ≤ ζ := by
    intro h hh
    obtain ⟨h0, h1⟩ := hp.fullSupport h hh
    exact Params.abs_ofLogit_sub_smooth_le (r := fun u => r.eval u) hτ0 (by linarith) h0 h1
      (happ _ (hp.logit_le h hh))
  refine ⟨r, hdeg, happ, fun h hh => ⟨(hsm h hh).1, (hsm h hh).2.1⟩, ?_, fun h hh => ?_, hclass,
    hclose, ?_⟩
  · refine Coupling.tv_wordDist_le_mul p (smooth τ p) T (τ / 2) hunit hsmU fun h hh => ?_
    rw [abs_sub_comm]; exact (hsm h hh).2.2
  · obtain ⟨h0, h1⟩ := hp.fullSupport h hh
    exact Params.logit_smooth hτ0 (by linarith) h0 h1
  · exact Coupling.tv_wordDist_le_mul _ _ T ζ
      (Coupling.FullSupport.unitInterval hclass.fullSupport) hsmU hclose

theorem zetaOf_pos (T d : ℕ) (ε δ : ℝ) : 0 < zetaOf T d ε δ := by
  unfold zetaOf; positivity

theorem zetaOf_lt_one (T d : ℕ) (ε δ : ℝ) : zetaOf T d ε δ < 1 := by
  unfold zetaOf
  have hN : 1 ≤ NOf T d ε δ := by
    unfold NOf JOf Cq
    have : 1 ≤ 100 * 52 * (d + 1) := by omega
    nlinarith [Nat.zero_le ⌈Real.logb 2 (2 * T * Cq * (d + 1) * LOf T ε / (ε * δ))⌉₊]
  rw [inv_lt_one₀ (by positivity)]
  exact one_lt_pow₀ one_lt_two (by omega)

/-- Proof of `thm:fixed`, the comparison step with the explicit parameters of
`eq:smooth-parameters` (`τ = tauOf`, `ζ = zetaOf`, `k = kOf`, `D = DOf`, `L = LOf`). For
`P ∈ 𝒞_{T,d}`, `T ≥ 1`, `0 < ε, δ < 1/2`, there is one polynomial `r` of degree `≤ k` such that
`P°` lies in the class with logit bound `L` and rank `D` that the robust learner is run on, with
`TV(P, P^τ) ≤ ε/16`, `TV(P°, P^τ) ≤ ε/8` and smoothing floor `τ/2 ≥ ε/(32T)`. Moreover, for all
request caps `R_ℓ, R_s` and every tolerance `ξ` with `0 ≤ R_ℓ`, `0 < ξ` and the bounds
`R_ℓ + R_s ≤ V^22`, `ξ⁻¹ ≤ V^11` of `lem:explicit-gls-token-envelope`, `eq:smooth-budget` holds and
every estimate within `ξ/2` of the smoothed logit is within `ξ` of the logit of `P°`.
`fixed_rank_comparison_envelope` applies this to the envelope's own caps and tolerance. -/
theorem fixed_rank_comparison {p : NextBit} {T d : ℕ} (hT : 1 ≤ T) (hp : InClass T d p)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ r : Polynomial ℝ, r.natDegree ≤ kOf T d ε δ ∧
      LogitClass T (LOf T ε) (DOf T d ε δ) (ofLogit fun h => r.eval (logit p h)) ∧
      tv (wordDist p T) (wordDist (smooth (tauOf T ε) p) T) ≤ ε / 16 ∧
      tv (wordDist (ofLogit fun h => r.eval (logit p h)) T)
        (wordDist (smooth (tauOf T ε) p) T) ≤ ε / 8 ∧
      (∀ h : List Bool, h.length < T →
        ε / (32 * T) ≤ smooth (tauOf T ε) p h ∧ smooth (tauOf T ε) p h ≤ 1 - ε / (32 * T)) ∧
      ∀ Rl Rs ξ : ℝ, 0 ≤ Rl → Rl + Rs ≤ VOf T d ε δ ^ 22 → 0 < ξ → ξ⁻¹ ≤ VOf T d ε δ ^ 11 →
        zetaOf T d ε δ ≤ ξ / 2 ∧ Rs * T * zetaOf T d ε δ ≤ δ / 4 ∧
        ∀ (h : List Bool) (A : ℝ), h.length < T →
          |A - logit (smooth (tauOf T ε) p) h| ≤ ξ / 2 →
          |A - logit (ofLogit fun h => r.eval (logit p h)) h| ≤ ξ := by
  obtain ⟨-, -, hτle, hτ0, hτ1, hτfloor, hτT⟩ := Params.tauOf_bounds hT hε0 hε1
  obtain ⟨r, hdeg, happ, hsm, htv1, hlogit, hclass, -, htv2⟩ :=
    comparison_distribution (k := kOf T d ε δ) hT hp hτ0 hτ1 (zetaOf_pos T d ε δ)
      (zetaOf_lt_one T d ε δ) (Params.softclip_degree_le_kOf hT hε0 hε1 hδ0 hδ1)
  obtain ⟨Rl0, Rs0, ξ0, hRl0, hR0, hξ00, hξ0⟩ :=
    Params.envelope_hyps_satisfiable (d := d) hT hε0 hε1 hδ0 hδ1
  have hTζ := (Params.smooth_budget_of_envelope hT hε0 hε1 hδ0 hδ1 hRl0 hR0 hξ00 hξ0).2.2
  have hLbound : softclipBound (tauOf T ε) + zetaOf T d ε δ ≤ LOf T ε := by
    have := Params.softclipBound_add_two_lt_LOf T ε
    linarith [zetaOf_lt_one T d ε δ]
  refine ⟨r, hdeg, ⟨hclass.fullSupport, fun h hh => (hclass.logit_le h hh).trans hLbound,
    hclass.rank_le⟩, htv1.trans (by linarith), htv2.trans hTζ, fun h hh => ⟨by
      linarith [(hsm h hh).1], by linarith [(hsm h hh).2]⟩, ?_⟩
  intro Rl Rs ξ hRl hR hξ0' hξ
  obtain ⟨hζξ, hRs, -⟩ := Params.smooth_budget_of_envelope hT hε0 hε1 hδ0 hδ1 hRl hR hξ0' hξ
  refine ⟨hζξ, hRs, fun h A hh hA => ?_⟩
  have hr := happ _ (hp.logit_le h hh)
  rw [logit_ofLogit]
  rw [hlogit h hh] at hA
  exact Params.oracle_transfer hA hr hζξ

/-- Proof of `thm:fixed`, the comparison step with the parameters of
`lem:explicit-gls-token-envelope` filled in. For `T ≥ 32`, `0 < ε, δ < 1/2` and `P ∈ 𝒞_{T,d}`,
take the envelope parameter tuple `Crossover.envInput T d ε δ` (an `Envelope.Input`: rank
`D = binom(d+k, d)`, logit bound `L`, request caps `R_ℓ = R_s = Q`, tolerance `ξ`). There is one
polynomial `r` of degree `≤ k` such that `P°` lies in the class with logit bound `L` and rank `D`,
`TV(P, P^τ) ≤ ε/16`, `TV(P°, P^τ) ≤ ε/8`, the budget `eq:smooth-budget` holds for this `ξ` and
`R_s`, the envelope's token formula `Input.tokens` is at most `V^{C_q}`
(`eq:gls-polynomial-envelope`), and every estimate within `ξ/2` of the smoothed logit is within
`ξ` of the logit of `P°`.

Not formalized: the training-run coupling of the first proof (the cached estimation groups, the
comparison table `A_good`, and the bound `δ/4 + R_s T ζ ≤ δ/2` on the probability that the two
training transcripts disagree; only the arithmetic of that last inequality is checked, in
`Params.failure_ledger`) and the learning guarantee of the robust learner (GLS Theorem 5.11 with
the corrections of the appendix). -/
theorem fixed_rank_comparison_envelope {p : NextBit} {T d : ℕ} (hT : 32 ≤ T)
    (hp : InClass T d p) {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) :
    ∃ r : Polynomial ℝ, r.natDegree ≤ kOf T d ε δ ∧
      LogitClass T (LOf T ε) (DOf T d ε δ) (ofLogit fun h => r.eval (logit p h)) ∧
      tv (wordDist p T) (wordDist (smooth (tauOf T ε) p) T) ≤ ε / 16 ∧
      tv (wordDist (ofLogit fun h => r.eval (logit p h)) T)
        (wordDist (smooth (tauOf T ε) p) T) ≤ ε / 8 ∧
      zetaOf T d ε δ ≤ (Crossover.envInput T d ε δ).xi / 2 ∧
      ((Crossover.envInput T d ε δ).Rs : ℝ) * T * zetaOf T d ε δ ≤ δ / 4 ∧
      (Crossover.envInput T d ε δ).tokens ≤ VOf T d ε δ ^ Cq ∧
      ∀ (h : List Bool) (A : ℝ), h.length < T →
        |A - logit (smooth (tauOf T ε) p) h| ≤ (Crossover.envInput T d ε δ).xi / 2 →
        |A - logit (ofLogit fun h => r.eval (logit p h)) h| ≤ (Crossover.envInput T d ε δ).xi := by
  have hT1 : 1 ≤ T := by omega
  obtain ⟨r, hdeg, hclass, htv1, htv2, -, hbudget⟩ := fixed_rank_comparison hT1 hp hε0 hε1 hδ0 hδ1
  have hval := Crossover.envInput_valid (d := d) hT hε0 hε1 hδ0 hδ1
  obtain ⟨hR, hξ, -⟩ := Envelope.Input.explicit_gls_token_envelope hval
  rw [Crossover.envInput_V] at hR hξ
  obtain ⟨hζ, hRs, htransfer⟩ := hbudget _ _ _ (Nat.cast_nonneg _) hR Envelope.Input.xi_pos hξ
  exact ⟨r, hdeg, hclass, htv1, htv2, hζ, hRs, Crossover.envelope_tokens_le hT hε0 hε1 hδ0 hδ1,
    htransfer⟩

/-- Second proof of `thm:fixed` (`sec:probability-route`, `alg:probability-route`), assembled.

The learner is fixed: coins `ω ∼ μ` on a finite set, `q` adaptive complete conditional suffix
queries at the prefixes `query ω x` (of length at most `T`, `x` the replies so far), and an
output distribution `out ω x` on `{0,1}^T`. Put `a = min{ε, δ}/4` and `R = prR T d C a`
(`eq:fixed-parameters`), and let the query cap satisfy `q ≤ (2TR/a)^C`.

Hypothesis `hLM` is Theorem `thm:lm` (Liu–Moitra) applied to this learner with rank bound `R`
and parameter `a`: run against any fully supported `P̃` of probability rank at most `R`, it
outputs a distribution within TV `a` of `P̃` with probability at least `1 - a`. It is the only
unformalized input. The learner, its query cap `q` and its output map `out` are the same objects
in `hLM` and in the conclusion.

Conclusion: for every `P ∈ 𝒞_{T,d}`, the same learner run against `P` outputs a distribution
within TV `ε` of `P` with probability at least `1 - δ`. The proof applies `hLM` to the comparison
distribution of `eq:surrogate` (`surrogate`, `lem:poly-sigmoid`, `lem:lift`) and transfers the
run to `P` by `lem:coupling` and `eq:combined-budget`. Only `T ≥ 1` is needed (the theorem
assumes `T ≥ 32`), and no upper bound on `δ` is used: `ε < 1/2` already gives `a ≤ 1`. -/
theorem fixed_second_proof {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : Coupling.IsProbVec μ)
    {p : NextBit} {T d C q : ℕ} (hT : 1 ≤ T) (hd : 1 ≤ d) (hC : 2 ≤ C) (hp : InClass T d p)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (hδ0 : 0 < δ)
    (query : Ω → List (Word T) → List Bool)
    (hquery : ∀ ω, ∀ x : List (Word T), x.length < q → (query ω x).length ≤ T)
    (out : Ω → List.Vector (Word T) q → Word T → ℝ)
    (hq : (q : ℝ) ≤ (2 * T * Params.prR T d C (Params.aOf ε δ) / Params.aOf ε δ) ^ C)
    (hLM : ∀ pt : NextBit, FullSupport T pt → probRank pt T ≤ Params.prR T d C (Params.aOf ε δ) →
      1 - Params.aOf ε δ ≤ ∑ z ∈ Finset.univ.filter
        (fun z : Ω × List.Vector (Word T) q => tv (wordDist pt T) (out z.1 z.2) ≤ Params.aOf ε δ),
        Coupling.suffixJoint μ pt T query q z) :
    1 - δ ≤ ∑ z ∈ Finset.univ.filter
        (fun z : Ω × List.Vector (Word T) q => tv (wordDist p T) (out z.1 z.2) ≤ ε),
        Coupling.suffixJoint μ p T query q z := by
  obtain ⟨ha0, ha1⟩ := Params.aOf_mem hε0 hε1 hδ0
  have hdeg := (Params.pr_degree (C := C) (d := d) hT hd hC ha0 ha1).2.2.2
  have hη0 : 0 < Params.prEta T d C (Params.aOf ε δ) := by unfold Params.prEta; positivity
  have hη1 : Params.prEta T d C (Params.aOf ε δ) < 1 := by
    unfold Params.prEta Params.prN
    rw [inv_lt_one₀ (by positivity)]
    apply one_lt_pow₀ one_lt_two
    have := Params.one_le_prJ (T := T) (d := d) (C := C) (a := Params.aOf ε δ)
    positivity
  obtain ⟨g, -, hfs, hclose, hrank⟩ := surrogate hT hp hη0 hη1 hdeg
  obtain ⟨hb, -, -, h2ε, h2δ⟩ := Params.pr_final (C := C) hT hd hC hε0 hε1 hδ0 q hq
  exact Coupling.transfer_eps_delta hμ T q query hquery out p _ _ (Params.aOf ε δ) ε δ
    (Coupling.FullSupport.unitInterval hp.fullSupport) (Coupling.FullSupport.unitInterval hfs)
    (fun h hh => by rw [abs_sub_comm]; exact hclose h hh) (by exact_mod_cast hb) h2ε h2δ
    (hLM _ hfs hrank)

end LowLogitRank.Assembly
