import LowLogitRank.Hardness.Audit
import LowLogitRank.Hardness.Reduction
import LowLogitRank.Coupling.NextBit

/-!
# The transcript transfer of `thm:reduction` and the assembled real case

"Simulation and the sampler test": for `H = F` every simulated next-bit law is within `η` of the
teacher's (`simulator_close_hard`), so by `lem:coupling` the (coin, transcript) laws of every
adaptive `q`-query training run under the teacher and under the simulator differ in TV by at most
`qη` (`tv_transcript_simulator_le`). An acceptance probability that is a `[0,1]`-valued function
of the coins and the transcript then changes by at most `qη` (`abs_expect_sub_le_tv`). With
`student_event_ge` and `average_ge` this gives the real case of `thm:reduction` without the
transfer hypothesis `hSim` of `reduction_accounting` (`reduction_real_case`,
`reduction_advantage`).

A training run is modeled as in `Coupling.tv_bitQuery_le`: coins `ω ∼ μ` on a finite set, and in
round `k` the prefix `query ω x` is submitted after the replies `x` of the earlier rounds.
-/

namespace LowLogitRank.Hardness

open Finset

variable {n L : ℕ} (P : Program)

/-- Every simulated next-bit probability lies in `[0, 1]`. -/
theorem simulator_mem_unit (F : Word n → Bool) (h : List Bool) :
    0 ≤ simulator n L F h ∧ simulator n L F h ≤ 1 := by
  have hb : ∀ b : Bool, 0 ≤ bitValue b ∧ bitValue b ≤ 1 := fun b => by
    cases b <;> simp [bitValue]
  unfold simulator
  split_ifs <;> first | exact hb _ | norm_num

/-- The expectation of a `[0,1]`-valued function changes by at most the TV distance. -/
theorem abs_expect_sub_le_tv {α : Type*} [Fintype α] (P Q : α → ℝ) (hPQ : ∑ z, P z = ∑ z, Q z)
    (f : α → ℝ) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1) :
    |∑ z, P z * f z - ∑ z, Q z * f z| ≤ tv P Q := by
  have h1 : ∑ z, (P z - Q z) * (f z - 1 / 2) =
      (∑ z, P z * f z - ∑ z, Q z * f z) - (∑ z, P z - ∑ z, Q z) / 2 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  rw [hPQ, sub_self, zero_div, sub_zero] at h1
  rw [← h1, tv, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => ?_)
  rw [abs_mul]
  have hf : |f z - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hf0 z], by linarith [hf1 z]⟩
  have := mul_le_mul_of_nonneg_left hf (abs_nonneg (P z - Q z))
  linarith

/-- "Simulation and the sampler test" with `lem:coupling`: under `eq:hard-consistency`, for
`H = F` the joint (coin, transcript) laws of every adaptive one-bit-query strategy with `q`
rounds under the teacher `P_k` and under the simulator differ in TV by at most `qη`,
`η = (1 + 2^{2n})⁻¹`. This is `Coupling.tv_bitQuery_le` without its length restriction on the
submitted prefixes, which is not needed because `simulator_close_hard` holds at every prefix. -/
theorem tv_transcript_simulator_le {F : Word n → Bool} (hcons : Consistent n L P F)
    {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : Coupling.IsProbVec μ) (q : ℕ)
    (query : Ω → List Bool → List Bool) :
    tv (Coupling.jointLaw μ (fun ω x => bitProb (hardTeacher n L P) (query ω x)) q)
        (Coupling.jointLaw μ (fun ω x => bitProb (simulator n L F) (query ω x)) q) ≤
      q * hardEta n :=
  Coupling.tv_jointLaw_le_mul hμ _ _ q (hardEta n)
    (fun _ _ _ => Coupling.bitProb_isProbVec (teacher_mem_unit P (hardB n) _))
    (fun _ _ _ => Coupling.bitProb_isProbVec (simulator_mem_unit F _))
    (fun _ _ _ => by
      rw [Coupling.tv_bitProb, abs_sub_comm]
      exact simulator_close_hard P hcons _)

variable (n L) in
/-- The set `𝒮` of the proof of `thm:reduction`: the inputs `X` of the consistent-label prefixes
(length `n + L` and `C(X, A) = 0`) submitted during the training run with coins `z.1` and
replies `z.2`. These are the only inputs at which the simulator consults `H`
(`simulator_congr`). -/
def labelInputs {Ω : Type*} {q : ℕ} (query : Ω → List Bool → List Bool)
    (z : Ω × List.Vector Bool q) : Finset (Word n) :=
  ((range q).filter fun k => (query z.1 (z.2.toList.take k)).length = n + L ∧
      mismatchCount n L (inputOf n (query z.1 (z.2.toList.take k)))
        (copyOf n L (query z.1 (z.2.toList.take k))) = 0).image
    fun k => inputOf n (query z.1 (z.2.toList.take k))

/-- Each training query adds at most one input to `𝒮`, so `|𝒮| ≤ q`. -/
theorem card_labelInputs_le {Ω : Type*} {q : ℕ} (query : Ω → List Bool → List Bool)
    (z : Ω × List.Vector Bool q) : (labelInputs n L query z).card ≤ q :=
  card_image_le.trans ((card_filter_le _ _).trans (card_range q).le)

/-- Proof of `thm:reduction`, real case, assembled. A learner with coins `ω ∼ μ` makes `q`
adaptive next-bit queries `query ω x` and returns a student `Q z`, a distribution on `{0,1}^T`
computed from its coins and replies `z`. Hypothesis `hlearn` is the learner's guarantee for the
teacher `P_k` (which lies in `𝒞_{T,n+7}` by `lem:hard-teacher`): over the real training run,
`TV(P_k, Q) ≤ ε` with probability at least `1 - δ`. Run instead with the simulator for `H = F`,
the distinguisher (draw one string from `Q` and accept exactly on `E_{F,𝒮}`, i.e. `A = a(X)`,
`X ∉ 𝒮`, `Y = H(X)`) accepts with probability at least
`(1-δ)[(1-η)^{L+1}(1 - q/2^n) - ε] - qη`. The transfer loss `qη` is proved here
(`tv_transcript_simulator_le`), not assumed. -/
theorem reduction_real_case (hn : 1 ≤ n) {F : Word n → Bool} (hcons : Consistent n L P F)
    {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : Coupling.IsProbVec μ) (q : ℕ)
    (query : Ω → List Bool → List Bool)
    (Q : Ω × List.Vector Bool q → Word (hardT n L) → ℝ) (hQ0 : ∀ z w, 0 ≤ Q z w)
    (hQ1 : ∀ z, ∑ w, Q z w = 1) {ε δ : ℝ} (hδ : δ ≤ 1)
    (hlearn : 1 - δ ≤ ∑ z, if tv (wordDist (hardTeacher n L P) (hardT n L)) (Q z) ≤ ε then
      Coupling.jointLaw μ (fun ω x => bitProb (hardTeacher n L P) (query ω x)) q z else 0) :
    (1 - δ) * ((1 - hardEta n) ^ (L + 1) * (1 - q / 2 ^ n) - ε) - q * hardEta n ≤
      ∑ z, Coupling.jointLaw μ (fun ω x => bitProb (simulator n L F) (query ω x)) q z *
        ∑ w, if goodEvent n L F (labelInputs n L query z) w.toList then Q z w else 0 := by
  set real := Coupling.jointLaw μ (fun ω x => bitProb (hardTeacher n L P) (query ω x)) q
  set sim := Coupling.jointLaw μ (fun ω x => bitProb (simulator n L F) (query ω x)) q
  set X : Ω × List.Vector Bool q → ℝ := fun z =>
    ∑ w, if goodEvent n L F (labelInputs n L query z) w.toList then Q z w else 0
  have hreal : Coupling.IsProbVec real := Coupling.jointLaw_isProbVec hμ _ q
    fun _ _ _ => Coupling.bitProb_isProbVec (teacher_mem_unit P (hardB n) _)
  have hsim : Coupling.IsProbVec sim := Coupling.jointLaw_isProbVec hμ _ q
    fun _ _ _ => Coupling.bitProb_isProbVec (simulator_mem_unit F _)
  have hX0 : ∀ z, 0 ≤ X z := fun z =>
    Finset.sum_nonneg fun w _ => by split_ifs <;> simp [hQ0 z w]
  have hX1 : ∀ z, X z ≤ 1 := fun z => by
    rw [← hQ1 z]
    exact Finset.sum_le_sum fun w _ => by split_ifs <;> simp [hQ0 z w]
  have hgood : ∀ z, tv (wordDist (hardTeacher n L P) (hardT n L)) (Q z) ≤ ε →
      (1 - hardEta n) ^ (L + 1) * (1 - q / 2 ^ n) - ε ≤ X z := fun z hz =>
    student_event_ge P hn hcons (Q z) (hQ1 z) hz (labelInputs n L query z)
      (by exact_mod_cast card_labelInputs_le query z)
  have hR := average_ge real X hreal.nonneg hX0
    (fun z => tv (wordDist (hardTeacher n L P) (hardT n L)) (Q z) ≤ ε) hδ hlearn hgood
  have hT := abs_expect_sub_le_tv real sim (by rw [hreal.sum_eq_one, hsim.sum_eq_one]) X hX0 hX1
  have htv : tv real sim ≤ q * hardEta n := tv_transcript_simulator_le P hcons hμ q query
  change _ ≤ ∑ z, sim z * X z
  linarith [(abs_le.mp (hT.trans htv)).2]

/-- `thm:reduction` (`eq:hard-advantage`) with the transfer discharged: for the distinguisher of
`reduction_real_case`, if its acceptance probability for a uniformly random function is some
`accRand ≤ 1/2` (the random case, proved in the decision-tree model by
`QueryTree.accept_prob_le_half`; the identification of the simulated run with such a tree is not
formalized), then its advantage is at least `(1-δ)[(1-η)^{L+1}(1 - q/2^n) - ε] - qη - 1/2`. -/
theorem reduction_advantage (hn : 1 ≤ n) {F : Word n → Bool} (hcons : Consistent n L P F)
    {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : Coupling.IsProbVec μ) (q : ℕ)
    (query : Ω → List Bool → List Bool)
    (Q : Ω × List.Vector Bool q → Word (hardT n L) → ℝ) (hQ0 : ∀ z w, 0 ≤ Q z w)
    (hQ1 : ∀ z, ∑ w, Q z w = 1) {ε δ : ℝ} (hδ : δ ≤ 1)
    (hlearn : 1 - δ ≤ ∑ z, if tv (wordDist (hardTeacher n L P) (hardT n L)) (Q z) ≤ ε then
      Coupling.jointLaw μ (fun ω x => bitProb (hardTeacher n L P) (query ω x)) q z else 0)
    {accRand : ℝ} (hRand : accRand ≤ 1 / 2) :
    hardAdvantage n L ε δ (hardEta n) q ≤
      (∑ z, Coupling.jointLaw μ (fun ω x => bitProb (simulator n L F) (query ω x)) q z *
        ∑ w, if goodEvent n L F (labelInputs n L query z) w.toList then Q z w else 0) -
        accRand := by
  have h := reduction_real_case P hn hcons hμ q query Q hQ0 hQ1 hδ hlearn
  unfold hardAdvantage
  linarith

/-- The hypotheses of `reduction_real_case` are jointly satisfiable for every `n ≥ 1`, `L ≥ 1`,
every training strategy and every `0 ≤ ε`, `0 ≤ δ ≤ 1`: take the dictator program with
`F(x) = x₁` (`dict_consistent`) and the student `Q = P_k`, which has TV `0`. The conclusion of
`reduction_real_case` then holds for this instance. -/
theorem reduction_real_case_satisfiable {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) {Ω : Type*}
    [Fintype Ω] {μ : Ω → ℝ} (hμ : Coupling.IsProbVec μ) (q : ℕ)
    (query : Ω → List Bool → List Bool) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    let F : Word n → Bool := fun x => x.toList.getD 0 false
    let Q : Ω × List.Vector Bool q → Word (hardT n L) → ℝ :=
      fun _ => wordDist (hardTeacher n L dictProgram) (hardT n L)
    Consistent n L dictProgram F ∧ (∀ z w, 0 ≤ Q z w) ∧ (∀ z, ∑ w, Q z w = 1) ∧
      (1 - δ ≤ ∑ z, if tv (wordDist (hardTeacher n L dictProgram) (hardT n L)) (Q z) ≤ ε then
        Coupling.jointLaw μ (fun ω x => bitProb (hardTeacher n L dictProgram) (query ω x)) q z
        else 0) ∧
      (1 - δ) * ((1 - hardEta n) ^ (L + 1) * (1 - q / 2 ^ n) - ε) - q * hardEta n ≤
        ∑ z, Coupling.jointLaw μ (fun ω x => bitProb (simulator n L F) (query ω x)) q z *
          ∑ w, if goodEvent n L F (labelInputs n L query z) w.toList then Q z w else 0 := by
  intro F Q
  have hcons : Consistent n L dictProgram F := dict_consistent n L hL
  have hQ0 : ∀ z w, 0 ≤ Q z w := fun _ w =>
    condProb_nonneg _ (fun h => teacher_mem_unit dictProgram (hardB n) h) [] w.toList
  have hQ1 : ∀ z, ∑ w, Q z w = 1 := fun _ => sum_condProb _ _ _
  have hreal := Coupling.jointLaw_isProbVec hμ
    (fun ω x => bitProb (hardTeacher n L dictProgram) (query ω x)) q
    fun _ _ _ => Coupling.bitProb_isProbVec (teacher_mem_unit dictProgram (hardB n) _)
  have hlearn : 1 - δ ≤ ∑ z, if tv (wordDist (hardTeacher n L dictProgram) (hardT n L)) (Q z) ≤ ε
      then Coupling.jointLaw μ (fun ω x => bitProb (hardTeacher n L dictProgram) (query ω x)) q z
      else 0 := by
    simp only [Q, Coupling.tv_self, hε, ↓reduceIte, hreal.sum_eq_one]
    linarith
  exact ⟨hcons, hQ0, hQ1, hlearn,
    reduction_real_case dictProgram hn hcons hμ q query Q hQ0 hQ1 hδ1 hlearn⟩

end LowLogitRank.Hardness
