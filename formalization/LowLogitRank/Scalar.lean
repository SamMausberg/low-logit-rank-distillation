import LowLogitRank.Cauchy
import LowLogitRank.ScalarKL

/-!
# `prop:scalar` and the root step of `lem:gls-root-simulation`

* The numerical core of `prop:scalar`: `p₀ = (1 + e^{2T})⁻¹`, `p₁ = (1 + e^{2T-6ξ})⁻¹`,
  `A(θ) = log (1 + e^θ)`, the bound `A'' ≤ p₁` on `[-2T, -2T + 6ξ]`, the exponential-family
  identity for `KL(Ber(p₀) ‖ Ber(p₁))`, the bound `≤ 18 e p₀ ξ²`, and the final constant.
* The two teachers (initial centered logit `-T`, resp. `-T + 3ξ`, fair later bits): both lie in
  `𝒞_{T,1}` and are within TV `e^{-2T+1}` of the generator "emit `0`, then fair bits".
* The stopped-transcript argument in a finite model of a capped adaptive algorithm
  (`CappedAlgo`): chain rule, data processing, Pinsker, and the lower bound on the expected
  number of empty-prefix queries under `P₀`, for success `0.99` and for failure `δ < 1/2`.
* The algebraic step of `lem:gls-root-simulation` and its use in the finite model.
-/

namespace LowLogitRank.Scalar

open Finset

/-! ### Logistic function and `A(θ) = log (1 + e^θ)` -/

theorem sigmoid_eq (θ : ℝ) : sigmoid θ = Real.exp θ / (1 + Real.exp θ) := by
  have := Real.exp_pos θ
  rw [sigmoid, Real.exp_neg]
  field_simp
  ring

theorem one_sub_sigmoid_eq (θ : ℝ) : 1 - sigmoid θ = 1 / (1 + Real.exp θ) := by
  have := Real.exp_pos θ
  rw [sigmoid_eq]
  field_simp
  ring

theorem sigmoid_le_exp (θ : ℝ) : sigmoid θ ≤ Real.exp θ := by
  rw [sigmoid_eq]
  exact div_le_self (Real.exp_pos θ).le (by linarith [Real.exp_pos θ])

/-- The log-partition function `A(θ) = log (1 + e^θ)` of the Bernoulli family. -/
noncomputable def logPartition (θ : ℝ) : ℝ := Real.log (1 + Real.exp θ)

theorem hasDerivAt_logPartition (θ : ℝ) : HasDerivAt logPartition (sigmoid θ) θ := by
  have h := ((Real.hasDerivAt_exp θ).const_add 1).log (by positivity)
  rw [sigmoid_eq]
  exact h

theorem hasDerivAt_sigmoid (θ : ℝ) : HasDerivAt sigmoid (sigmoid θ * (1 - sigmoid θ)) θ := by
  have h1 : HasDerivAt (fun x => 1 + Real.exp (-x)) (-Real.exp (-θ)) θ := by
    have := ((Real.hasDerivAt_exp (-θ)).comp θ (hasDerivAt_neg θ)).const_add 1
    simpa using this
  have h2 := h1.inv (by positivity)
  convert h2 using 1
  · funext x
    simp [sigmoid]
  · have := Real.exp_pos (-θ)
    simp only [sigmoid]
    field_simp
    ring

theorem deriv_logPartition : deriv logPartition = sigmoid :=
  funext fun θ => (hasDerivAt_logPartition θ).deriv

theorem deriv_deriv_logPartition (θ : ℝ) :
    deriv (deriv logPartition) θ = sigmoid θ * (1 - sigmoid θ) := by
  rw [deriv_logPartition]
  exact (hasDerivAt_sigmoid θ).deriv

/-- Second-order Taylor bound: if `A'' ≤ M` on `[θ₀, θ₀ + δ]` then
`A(θ₀ + δ) - A(θ₀) - δ A'(θ₀) ≤ M δ² / 2`. -/
theorem logPartition_taylor (θ₀ δ M : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ θ ∈ Set.Icc θ₀ (θ₀ + δ), deriv (deriv logPartition) θ ≤ M) :
    logPartition (θ₀ + δ) - logPartition θ₀ - δ * deriv logPartition θ₀ ≤ M * δ ^ 2 / 2 := by
  rw [deriv_logPartition]
  simp only [deriv_deriv_logPartition] at hM
  -- `h t = σ(θ₀ + t) - σ(θ₀) - M t` is nonpositive on `[0, δ]`
  let h : ℝ → ℝ := fun t => sigmoid (θ₀ + t) - sigmoid θ₀ - M * t
  have hh : ∀ t, HasDerivAt h (sigmoid (θ₀ + t) * (1 - sigmoid (θ₀ + t)) - M) t := by
    intro t
    have h1 := (hasDerivAt_sigmoid (θ₀ + t)).comp_const_add θ₀ t
    have h2 := (h1.sub_const (sigmoid θ₀)).sub ((hasDerivAt_id' t).const_mul M)
    convert h2 using 1
    ring
  have hanti : AntitoneOn h (Set.Icc 0 δ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 δ)
    · exact fun t _ => (hh t).continuousAt.continuousWithinAt
    · exact fun t _ => (hh t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hh t).deriv]
      have := hM (θ₀ + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
  have hle : ∀ t ∈ Set.Icc 0 δ, h t ≤ 0 := by
    intro t ht
    have := hanti ⟨le_refl 0, hδ⟩ ht ht.1
    simpa [h] using this
  -- `g t = A(θ₀ + t) - A(θ₀) - t σ(θ₀) - M t²/2` is antitone on `[0, δ]`
  let g : ℝ → ℝ := fun t =>
    logPartition (θ₀ + t) - logPartition θ₀ - t * sigmoid θ₀ - M * t ^ 2 / 2
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have h1 := (hasDerivAt_logPartition (θ₀ + t)).comp_const_add θ₀ t
    have h2 := ((h1.sub_const (logPartition θ₀)).sub ((hasDerivAt_id' t).mul_const
      (sigmoid θ₀))).sub (((hasDerivAt_pow 2 t).const_mul M).div_const 2)
    convert h2 using 1
    simp only [h]
    push_cast
    ring
  have ganti : AntitoneOn g (Set.Icc 0 δ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 δ)
    · exact fun t _ => (hg t).continuousAt.continuousWithinAt
    · exact fun t _ => (hg t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hg t).deriv]
      exact hle t (interior_subset ht)
  have := ganti ⟨le_refl 0, hδ⟩ ⟨hδ, le_refl δ⟩ hδ
  simp only [g, add_zero, sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, zero_div] at this
  linarith

/-- The exponential-family identity
`KL(Ber(σ θ₀) ‖ Ber(σ θ₁)) = A(θ₁) - A(θ₀) - (θ₁ - θ₀) A'(θ₀)`. -/
theorem binKL_sigmoid (θ₀ θ₁ : ℝ) :
    binKL (sigmoid θ₀) (sigmoid θ₁) =
      logPartition θ₁ - logPartition θ₀ - (θ₁ - θ₀) * deriv logPartition θ₀ := by
  have e0 := Real.exp_pos θ₀
  have e1 := Real.exp_pos θ₁
  have h1 : sigmoid θ₀ / sigmoid θ₁ =
      Real.exp (θ₀ - θ₁) * ((1 + Real.exp θ₁) / (1 + Real.exp θ₀)) := by
    rw [sigmoid_eq, sigmoid_eq, Real.exp_sub]
    field_simp
  have h2 : (1 - sigmoid θ₀) / (1 - sigmoid θ₁) = (1 + Real.exp θ₁) / (1 + Real.exp θ₀) := by
    rw [one_sub_sigmoid_eq, one_sub_sigmoid_eq]
    field_simp
  rw [binKL_eq, h1, h2, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
    Real.log_div (by positivity) (by positivity), deriv_logPartition]
  unfold logPartition
  ring

/-! ### The numerical core of `prop:scalar` -/

/-- `p₀ = (1 + e^{2T})⁻¹`, the root probability of the teacher with initial logit `-T`. -/
noncomputable def p0 (T : ℝ) : ℝ := (1 + Real.exp (2 * T))⁻¹

/-- `p₁ = (1 + e^{2T - 6ξ})⁻¹`, the root probability of the teacher with initial logit
`-T + 3ξ`. -/
noncomputable def p1 (T ξ : ℝ) : ℝ := (1 + Real.exp (2 * T - 6 * ξ))⁻¹

theorem p0_eq (T : ℝ) : p0 T = sigmoid (-2 * T) := by
  rw [p0, sigmoid, show -(-2 * T) = 2 * T by ring]

theorem p1_eq (T ξ : ℝ) : p1 T ξ = sigmoid (-2 * T + 6 * ξ) := by
  rw [p1, sigmoid, show -(-2 * T + 6 * ξ) = 2 * T - 6 * ξ by ring]

theorem p0_pos (T : ℝ) : 0 < p0 T := by rw [p0_eq]; exact sigmoid_pos _

/-- `prop:scalar`: `p₁ ≤ e^{6ξ} p₀`. -/
theorem p1_le_exp_mul_p0 (T ξ : ℝ) (hξ : 0 ≤ ξ) : p1 T ξ ≤ Real.exp (6 * ξ) * p0 T := by
  have hx : 0 < Real.exp (6 * ξ) := Real.exp_pos _
  have h6 : 1 ≤ Real.exp (6 * ξ) := Real.one_le_exp (by linarith)
  have hE : 0 < Real.exp (2 * T) := Real.exp_pos _
  have e1 : p1 T ξ = Real.exp (6 * ξ) / (Real.exp (6 * ξ) + Real.exp (2 * T)) := by
    rw [p1, Real.exp_sub]
    field_simp
  have e2 : Real.exp (6 * ξ) * p0 T = Real.exp (6 * ξ) / (1 + Real.exp (2 * T)) := by
    rw [p0, div_eq_mul_inv]
  rw [e1, e2]
  exact div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)

/-- `prop:scalar`: `p₁ ≤ e^{6ξ} p₀ ≤ e p₀` for `0 ≤ ξ ≤ 1/6`. -/
theorem p1_le_e_mul_p0 (T ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 6) :
    p1 T ξ ≤ Real.exp (6 * ξ) * p0 T ∧ Real.exp (6 * ξ) * p0 T ≤ Real.exp 1 * p0 T :=
  ⟨p1_le_exp_mul_p0 T ξ hξ0,
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (p0_pos T).le⟩

/-- `prop:scalar`: `A'' ≤ p₁` on `[-2T, -2T + 6ξ]`. -/
theorem deriv_deriv_logPartition_le (T ξ θ : ℝ) (hθ : θ ∈ Set.Icc (-2 * T) (-2 * T + 6 * ξ)) :
    deriv (deriv logPartition) θ ≤ p1 T ξ := by
  rw [deriv_deriv_logPartition, p1_eq]
  have h0 := sigmoid_pos θ
  have h1 := sigmoid_lt_one θ
  have := Cauchy.sigmoid_mono hθ.2
  nlinarith

/-- `prop:scalar`: `KL(Ber(p₀) ‖ Ber(p₁)) = A(-2T + 6ξ) - A(-2T) - 6ξ A'(-2T)`. -/
theorem binKL_p0_p1 (T ξ : ℝ) :
    binKL (p0 T) (p1 T ξ) = logPartition (-2 * T + 6 * ξ) - logPartition (-2 * T) -
      6 * ξ * deriv logPartition (-2 * T) := by
  rw [p0_eq, p1_eq, binKL_sigmoid]
  ring

/-- `prop:scalar`: `KL(Ber(p₀) ‖ Ber(p₁)) ≤ 18 e p₀ ξ²` for `0 ≤ ξ ≤ 1/6`. -/
theorem binKL_p0_p1_le (T ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 6) :
    binKL (p0 T) (p1 T ξ) ≤ 18 * Real.exp 1 * p0 T * ξ ^ 2 := by
  rw [binKL_p0_p1]
  have ht := logPartition_taylor (-2 * T) (6 * ξ) (p1 T ξ) (by linarith)
    (fun θ hθ => deriv_deriv_logPartition_le T ξ θ hθ)
  obtain ⟨h1, h2⟩ := p1_le_e_mul_p0 T ξ hξ0 hξ1
  have hp : p1 T ξ ≤ Real.exp 1 * p0 T := h1.trans h2
  have hξ2 : 0 ≤ ξ ^ 2 := sq_nonneg ξ
  nlinarith

/-- `prop:scalar`: `2 (0.98)² / (18 e) · (1 + e^{2T}) / ξ² > e^{2T} / (30 ξ²)`. -/
theorem scalar_constant (T ξ : ℝ) (hξ : 0 < ξ) :
    Real.exp (2 * T) / (30 * ξ ^ 2) <
      2 * (98 / 100) ^ 2 / (18 * Real.exp 1) * ((1 + Real.exp (2 * T)) / ξ ^ 2) := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hE := Real.exp_pos (2 * T)
  have hξ2 : 0 < ξ ^ 2 := by positivity
  rw [div_lt_iff₀ (by positivity)]
  have : 2 * (98 / 100) ^ 2 / (18 * Real.exp 1) * ((1 + Real.exp (2 * T)) / ξ ^ 2) *
      (30 * ξ ^ 2) = 2 * (98 / 100) ^ 2 * 30 * (1 + Real.exp (2 * T)) / (18 * Real.exp 1) := by
    field_simp
  rw [this, lt_div_iff₀ (by positivity)]
  nlinarith

/-! ### The two teachers -/

/-- The teacher with initial centered logit `u` and independent fair later bits. -/
noncomputable def teacher (u : ℝ) : NextBit := ofLogit fun h => if h = [] then u else 0

theorem teacher_nil (u : ℝ) : teacher u [] = sigmoid (2 * u) := by
  simp [teacher, ofLogit]

theorem teacher_of_ne_nil (u : ℝ) {h : List Bool} (hh : h ≠ []) : teacher u h = 1 / 2 := by
  simp [teacher, ofLogit, hh, Cauchy.sigmoid_zero]

theorem teacher_mem (u : ℝ) (h : List Bool) : 0 < teacher u h ∧ teacher u h < 1 :=
  ⟨sigmoid_pos _, sigmoid_lt_one _⟩

theorem logit_teacher (u : ℝ) (h : List Bool) :
    logit (teacher u) h = if h = [] then u else 0 :=
  logit_ofLogit _ h

theorem logit_teacher_nil (u : ℝ) : logit (teacher u) [] = u := by simp [logit_teacher]

theorem teacher_neg_nil (T : ℝ) : teacher (-T) [] = p0 T := by
  rw [teacher_nil, p0_eq]
  ring_nf

theorem teacher_shift_nil (T ξ : ℝ) : teacher (-T + 3 * ξ) [] = p1 T ξ := by
  rw [teacher_nil, p1_eq]
  ring_nf

/-- A teacher with `|u| ≤ T` lies in `𝒞_{T,1}`. -/
theorem teacher_inClass (T : ℕ) (u : ℝ) (hu : |u| ≤ T) : InClass T 1 (teacher u) where
  fullSupport := ofLogit_fullSupport _ T
  logit_le h _ := by
    rw [logit_teacher]
    split_ifs
    · exact hu
    · simp
  rank_le t _ := by
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      refine (Matrix.rank_le_card_height _).trans ?_
      simp [card_vector]
    · have hz : logitCutMatrix (logit (teacher u)) T t = 0 := by
        ext h f
        have hne : h.toList ++ f.2.toList ≠ [] := by
          intro e
          have := congrArg List.length e
          simp only [List.length_append, List.Vector.toList_length, List.length_nil] at this
          omega
        simp [logitCutMatrix, logit_teacher, hne]
      rw [hz, Matrix.rank_zero]
      exact zero_le_one

/-- `prop:scalar`: the teacher `P₀` (initial logit `-T`) lies in `𝒞_{T,1}`. -/
theorem teacher0_inClass (T : ℕ) : InClass T 1 (teacher (-T)) :=
  teacher_inClass T _ (by simp)

/-- `prop:scalar`: the teacher `P₁` (initial logit `-T + 3ξ`) lies in `𝒞_{T,1}` for `T ≥ 1`,
`0 ≤ ξ ≤ 1/6`. -/
theorem teacher1_inClass (T : ℕ) (hT : 1 ≤ T) (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 6) :
    InClass T 1 (teacher (-T + 3 * ξ)) := by
  apply teacher_inClass
  have : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rw [abs_le]
  constructor <;> linarith

/-- The generator that emits `0` and then independent fair bits. -/
noncomputable def zeroThenFair : NextBit := fun h => if h = [] then 0 else 1 / 2

/-- The teacher with initial logit `u` is at TV distance exactly `σ(2u)` from `zeroThenFair`. -/
theorem tv_teacher_zeroThenFair (u : ℝ) (T : ℕ) (hT : 1 ≤ T) :
    tv (wordDist (teacher u) T) (wordDist zeroThenFair T) = sigmoid (2 * u) := by
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
  have hfair : ∀ (p : NextBit), (∀ g : List Bool, g ≠ [] → p g = 1 / 2) →
      ∀ (b : Bool) (v : Word m), condProb p [b] v.toList = (1 / 2) ^ m := by
    intro p hp b v
    rw [Cauchy.condProb_eq_half_pow, List.Vector.toList_length]
    intro g hg _
    apply hp
    intro e
    rw [e] at hg
    simp at hg
  have h1 := hfair (teacher u) (fun g hg => teacher_of_ne_nil u hg)
  have h2 := hfair zeroThenFair (fun g hg => by simp [zeroThenFair, hg])
  have hterm : ∀ (b : Bool) (v : Word m),
      |wordDist (teacher u) (m + 1) (b ::ᵥ v) - wordDist zeroThenFair (m + 1) (b ::ᵥ v)| =
        |bitProb (teacher u) [] b - bitProb zeroThenFair [] b| * (1 / 2) ^ m := by
    intro b v
    simp only [wordDist, List.Vector.toList_cons, condProb_cons, List.nil_append, h1, h2]
    rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2) ^ m)]
  unfold tv
  rw [sum_word_succ]
  simp only [hterm, sum_const, card_univ, card_vector, Fintype.card_bool, nsmul_eq_mul,
    Fintype.sum_bool]
  have hσ := sigmoid_pos (2 * u)
  have hσ1 := sigmoid_lt_one (2 * u)
  simp only [bitProb, teacher_nil, zeroThenFair, ite_true, Bool.false_eq_true, ite_false]
  rw [show sigmoid (2 * u) - 0 = sigmoid (2 * u) by ring,
    show 1 - sigmoid (2 * u) - (1 - 0) = -sigmoid (2 * u) by ring, abs_neg, abs_of_pos hσ]
  push_cast
  have : (2 : ℝ) ^ m * (1 / 2) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination sigmoid (2 * u) * this

/-- `prop:scalar` (remark after the proof): the teacher `P₀` is within TV `e^{-2T+1}` of the
generator that emits `0` and then fair bits. -/
theorem tv_teacher0_le (T : ℕ) (hT : 1 ≤ T) :
    tv (wordDist (teacher (-T)) T) (wordDist zeroThenFair T) ≤ Real.exp (-2 * T + 1) := by
  rw [tv_teacher_zeroThenFair _ T hT]
  refine (sigmoid_le_exp _).trans (Real.exp_le_exp.mpr ?_)
  linarith

/-- `prop:scalar` (remark after the proof): the teacher `P₁` is within TV `e^{-2T+1}` of the
same generator, for `ξ ≤ 1/6`. -/
theorem tv_teacher1_le (T : ℕ) (hT : 1 ≤ T) (ξ : ℝ) (hξ1 : ξ ≤ 1 / 6) :
    tv (wordDist (teacher (-T + 3 * ξ)) T) (wordDist zeroThenFair T) ≤
      Real.exp (-2 * T + 1) := by
  rw [tv_teacher_zeroThenFair _ T hT]
  refine (sigmoid_le_exp _).trans (Real.exp_le_exp.mpr ?_)
  linarith

/-! ### A finite model of a capped adaptive algorithm -/

/-- A capped adaptive algorithm with coin space `Ω` (finite, with weights) and `n` rounds.
In round `k` it submits the prefix `query ω r`, where `ω` are its coins and `r` is the list of
the `k` replies received so far, and receives one bit. After the `n` rounds it outputs
`estimate ω r`. An algorithm that stops earlier is modelled by submitting nonempty prefixes after
its stopping time and ignoring their replies.

The coin space is finite, with real weights (nonnegative, summing to one). An algorithm with a
finite query cap that may use unboundedly many fair coins is not covered by this model, although
the argument for it is the same. -/
structure CappedAlgo (Ω : Type*) [Fintype Ω] (n : ℕ) where
  /-- The law of the coins; it is the same under every teacher. -/
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : ∑ ω, weight ω = 1
  /-- The prefix submitted after the replies `r`, given the coins. -/
  query : Ω → List Bool → List Bool
  /-- The returned estimate. -/
  estimate : Ω → Word n → ℝ

namespace CappedAlgo

variable {Ω : Type*} [Fintype Ω] {n : ℕ} (A : CappedAlgo Ω n)

/-- With coins `ω` and teacher `p`, the next reply after the replies `r` is `1` with
probability `p (query ω r)`: it depends only on the submitted prefix. -/
def replyModel (p : NextBit) (ω : Ω) : NextBit := fun r => p (A.query ω r)

/-- The joint law of the coins and the `n` replies under the teacher `p`. -/
noncomputable def law (p : NextBit) (z : Ω × Word n) : ℝ :=
  A.weight z.1 * condProb (A.replyModel p z.1) [] z.2.toList

/-- `N_∅`: the number of rounds whose submitted prefix is empty. -/
def emptyCount (z : Ω × Word n) : ℕ :=
  ((range n).filter fun k => A.query z.1 (z.2.toList.take k) = []).card

/-- Expectation under the teacher `p`. -/
noncomputable def expect (p : NextBit) (F : Ω × Word n → ℝ) : ℝ := ∑ z, A.law p z * F z

/-- Probability of an event under the teacher `p`. -/
noncomputable def prob (p : NextBit) (S : Finset (Ω × Word n)) : ℝ := ∑ z ∈ S, A.law p z

/-- The event that the estimate is within `ξ` of `u`. -/
noncomputable def successSet (u ξ : ℝ) : Finset (Ω × Word n) :=
  univ.filter fun z => |A.estimate z.1 z.2 - u| ≤ ξ

/-- The probability, under the teacher `P`, that the estimate is within `ξ` of the initial
centered logit `ℓ_P(∅)`. -/
noncomputable def successProb (P : NextBit) (ξ : ℝ) : ℝ :=
  A.prob P (A.successSet (logit P []) ξ)

theorem law_nonneg (p : NextBit) (hp : ∀ g, 0 < p g ∧ p g < 1) (z : Ω × Word n) :
    0 ≤ A.law p z :=
  mul_nonneg (A.weight_nonneg _) (condProb_pos _ (fun _ => hp _) _ _).le

theorem sum_law (p : NextBit) : ∑ z, A.law p z = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [law, ← mul_sum, sum_condProb, mul_one, A.weight_sum]

theorem law_eq_zero_of_eq_zero (p q : NextBit) (hq : ∀ g, 0 < q g ∧ q g < 1)
    (z : Ω × Word n) (hz : A.law q z = 0) : A.law p z = 0 := by
  have hc := condProb_pos (A.replyModel q z.1) (fun _ => hq _) [] z.2.toList
  have hw : A.weight z.1 = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h hc.ne'
  simp [law, hw]

theorem emptyCount_eq_pathSum (z : Ω × Word n) :
    (A.emptyCount z : ℝ) =
      pathSum (fun r => if A.query z.1 r = [] then 1 else 0) [] z.2.toList := by
  rw [pathSum_eq_sum, List.Vector.toList_length, emptyCount, natCast_card_filter]
  simp

theorem emptyCount_le (z : Ω × Word n) : A.emptyCount z ≤ n := by
  unfold emptyCount
  exact (card_filter_le _ _).trans (by simp)

theorem expect_mono (p : NextBit) (hp : ∀ g, 0 < p g ∧ p g < 1) {F G : Ω × Word n → ℝ}
    (hFG : ∀ z, F z ≤ G z) : A.expect p F ≤ A.expect p G :=
  sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hFG z) (A.law_nonneg p hp z)

theorem expect_const (p : NextBit) (c : ℝ) : A.expect p (fun _ => c) = c := by
  rw [expect, ← sum_mul, sum_law, one_mul]

/-- Chain rule for the stopped transcript (`prop:scalar`): if two teachers agree on every
nonempty prefix, the relative entropy between the laws of (coins, replies) is
`E_p[N_∅] · KL(Ber(p ∅) ‖ Ber(q ∅))`. -/
theorem klDiv_law (p q : NextBit) (hp : ∀ g, 0 < p g ∧ p g < 1) (hq : ∀ g, 0 < q g ∧ q g < 1)
    (hpq : ∀ g, g ≠ [] → p g = q g) :
    klDiv (A.law p) (A.law q) =
      A.expect p (fun z => (A.emptyCount z : ℝ)) * binKL (p []) (q []) := by
  set κ := binKL (p []) (q [])
  have hstep : ∀ ω (g : List Bool), binKL (A.replyModel p ω g) (A.replyModel q ω g) =
      κ * (if A.query ω g = [] then 1 else 0) := by
    intro ω g
    simp only [replyModel]
    split_ifs with h
    · rw [h, mul_one]
    · rw [hpq _ h, binKL_self, mul_zero]
  have hω : ∀ ω, ∑ r : Word n, A.law p (ω, r) * Real.log (A.law p (ω, r) / A.law q (ω, r)) =
      ∑ r : Word n, A.law p (ω, r) * (κ * (A.emptyCount (ω, r) : ℝ)) := by
    intro ω
    rcases eq_or_ne (A.weight ω) 0 with hw | hw
    · simp [law, hw]
    have hlog : ∀ r : Word n, A.law p (ω, r) * Real.log (A.law p (ω, r) / A.law q (ω, r)) =
        A.weight ω * (condProb (A.replyModel p ω) [] r.toList *
          Real.log (condProb (A.replyModel p ω) [] r.toList /
            condProb (A.replyModel q ω) [] r.toList)) := by
      intro r
      simp only [law]
      rw [mul_div_mul_left _ _ hw]
      ring
    simp only [hlog, ← mul_sum]
    rw [klDiv_condProb (A.replyModel p ω) (A.replyModel q ω) (fun _ => hp _) (fun _ => hq _) n []]
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    have hN := A.emptyCount_eq_pathSum (ω, r)
    simp only at hN
    rw [pathSum_congr (hstep ω) [] r.toList, pathSum_const_mul, hN]
    simp only [law]
    ring
  rw [klDiv, Fintype.sum_prod_type]
  simp only [hω, expect, Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun ω _ => sum_congr rfl fun r _ => ?_
  ring

/-- `prop:scalar` (chain rule for the two teachers): the relative entropy between the
(coins, replies) laws under `P₀` and `P₁` is `E_{P₀}[N_∅] · KL(Ber(p₀) ‖ Ber(p₁))`. -/
theorem klDiv_law_teachers (T ξ : ℝ) :
    klDiv (A.law (teacher (-T))) (A.law (teacher (-T + 3 * ξ))) =
      A.expect (teacher (-T)) (fun z => (A.emptyCount z : ℝ)) * binKL (p0 T) (p1 T ξ) := by
  rw [A.klDiv_law _ _ (teacher_mem _) (teacher_mem _) (fun g hg => by
    rw [teacher_of_ne_nil _ hg, teacher_of_ne_nil _ hg]), teacher_neg_nil, teacher_shift_nil]

/-! ### The stopped-transcript lower bound -/

/-- `prop:scalar`, capped version with failure probability `δ < 1/2`: if, under each of the two
teachers, the estimate is within `ξ` of the true initial logit with probability at least `1 - δ`,
then `E_{P₀}[N_∅] ≥ (1 - 2δ)² / (9e) · (1 + e^{2T}) / ξ²`. -/
theorem expect_emptyCount_ge (T ξ δ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) (hδ : δ < 1 / 2)
    (h0 : 1 - δ ≤ A.successProb (teacher (-T)) ξ)
    (h1 : 1 - δ ≤ A.successProb (teacher (-T + 3 * ξ)) ξ) :
    (1 - 2 * δ) ^ 2 / (9 * Real.exp 1) * ((1 + Real.exp (2 * T)) / ξ ^ 2) ≤
      A.expect (teacher (-T)) (fun z => (A.emptyCount z : ℝ)) := by
  classical
  set P0 := teacher (-T)
  set P1 := teacher (-T + 3 * ξ)
  have hP0 := teacher_mem (-T)
  have hP1 := teacher_mem (-T + 3 * ξ)
  -- the midpoint test
  set E : Finset (Ω × Word n) := univ.filter fun z => A.estimate z.1 z.2 < -T + 3 * ξ / 2
  set a := ∑ z ∈ E, A.law P0 z
  set b := ∑ z ∈ E, A.law P1 z
  have hS0 : A.successSet (logit P0 []) ξ ⊆ E := by
    intro z hz
    simp only [successSet, logit_teacher_nil, P0, mem_filter, mem_univ, true_and] at hz
    simp only [E, mem_filter, mem_univ, true_and]
    have := (abs_le.mp hz).2
    linarith
  have hS1 : A.successSet (logit P1 []) ξ ⊆ Eᶜ := by
    intro z hz
    simp only [successSet, logit_teacher_nil, P1, mem_filter, mem_univ, true_and] at hz
    simp only [E, mem_compl, mem_filter, mem_univ, true_and, not_lt]
    have := (abs_le.mp hz).1
    linarith
  have ha : 1 - δ ≤ a := h0.trans (sum_le_sum_of_subset_of_nonneg hS0
    fun z _ _ => A.law_nonneg P0 hP0 z)
  have ha1 : a ≤ 1 := by
    rw [← A.sum_law P0]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ E) fun z _ _ => A.law_nonneg P0 hP0 z
  have hb : b ≤ δ := by
    have hc : 1 - δ ≤ ∑ z ∈ Eᶜ, A.law P1 z := h1.trans (sum_le_sum_of_subset_of_nonneg hS1
      fun z _ _ => A.law_nonneg P1 hP1 z)
    have := sum_add_sum_compl E (A.law P1)
    rw [A.sum_law] at this
    linarith
  have hb0 : 0 < b := by
    rcases (sum_nonneg fun z _ => A.law_nonneg P1 hP1 z : 0 ≤ b).eq_or_lt with hb0 | hb0
    · exfalso
      have hz : ∀ z ∈ E, A.law P1 z = 0 :=
        (sum_eq_zero_iff_of_nonneg fun z _ => A.law_nonneg P1 hP1 z).mp hb0.symm
      have : a = 0 := sum_eq_zero fun z hz' => A.law_eq_zero_of_eq_zero P0 P1 hP1 z (hz z hz')
      linarith
    · exact hb0
  -- Pinsker and data processing
  have hpin := pinsker a b (by linarith) ha1 hb0 (by linarith)
  have hdp := binKL_le_klDiv (A.law P0) (A.law P1) (A.law_nonneg P0 hP0) (A.law_nonneg P1 hP1)
    (A.sum_law P0) (A.sum_law P1) (A.law_eq_zero_of_eq_zero P0 P1 hP1) E
  -- chain rule
  have hchain := A.klDiv_law_teachers T ξ
  have hkl := binKL_p0_p1_le T ξ hξ0.le hξ1
  set N := A.expect P0 (fun z => (A.emptyCount z : ℝ))
  have hN : 0 ≤ N := sum_nonneg fun z _ => mul_nonneg (A.law_nonneg P0 hP0 z) (by positivity)
  have hab : (1 - 2 * δ) ^ 2 ≤ (a - b) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith)
    linarith
  -- `2 (1 - 2δ)² ≤ N · 18 e p₀ ξ²`
  have hmain : 2 * (1 - 2 * δ) ^ 2 ≤ N * (18 * Real.exp 1 * p0 T * ξ ^ 2) := by
    calc 2 * (1 - 2 * δ) ^ 2 ≤ 2 * (a - b) ^ 2 := by linarith
      _ ≤ binKL a b := hpin
      _ ≤ klDiv (A.law P0) (A.law P1) := hdp
      _ = N * binKL (p0 T) (p1 T ξ) := hchain
      _ ≤ N * (18 * Real.exp 1 * p0 T * ξ ^ 2) := mul_le_mul_of_nonneg_left hkl hN
  have hK : 0 < 18 * Real.exp 1 * p0 T * ξ ^ 2 := by
    have := p0_pos T
    positivity
  have hL : (1 - 2 * δ) ^ 2 / (9 * Real.exp 1) * ((1 + Real.exp (2 * T)) / ξ ^ 2) =
      2 * (1 - 2 * δ) ^ 2 / (18 * Real.exp 1 * p0 T * ξ ^ 2) := by
    have := Real.exp_pos 1
    have := Real.exp_pos (2 * T)
    rw [p0]
    field_simp
    ring
  rw [hL, div_le_iff₀ hK]
  exact hmain

/-- `prop:scalar` with success probability `0.99`:
`E_{P₀}[N_∅] ≥ 2 (0.98)² / (18 e) · (1 + e^{2T}) / ξ² > e^{2T} / (30 ξ²)`. -/
theorem expect_emptyCount_gt (T ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6)
    (h0 : 99 / 100 ≤ A.successProb (teacher (-T)) ξ)
    (h1 : 99 / 100 ≤ A.successProb (teacher (-T + 3 * ξ)) ξ) :
    2 * (98 / 100) ^ 2 / (18 * Real.exp 1) * ((1 + Real.exp (2 * T)) / ξ ^ 2) ≤
        A.expect (teacher (-T)) (fun z => (A.emptyCount z : ℝ)) ∧
      Real.exp (2 * T) / (30 * ξ ^ 2) <
        A.expect (teacher (-T)) (fun z => (A.emptyCount z : ℝ)) := by
  have h := A.expect_emptyCount_ge T ξ (1 / 100) hξ0 hξ1 (by norm_num)
    (by linarith) (by linarith)
  have heq : (1 - 2 * (1 / 100 : ℝ)) ^ 2 / (9 * Real.exp 1) =
      2 * (98 / 100) ^ 2 / (18 * Real.exp 1) := by
    have := Real.exp_pos 1
    field_simp
    ring
  rw [heq] at h
  exact ⟨h, (scalar_constant T ξ hξ0).trans_le h⟩

end CappedAlgo

/-- `prop:scalar`. Let `T ≥ 1` (the paper assumes `T ≥ 32`) and `0 < ξ ≤ 1/6`. The teachers `P₀`
(initial centered logit `-T`) and `P₁` (initial logit `-T + 3ξ`), with fair later bits, lie in
`𝒞_{T,1}`. Every capped adaptive algorithm (finite model `CappedAlgo`) that estimates
`ℓ_P(∅)` within `ξ` with probability at least `0.99` under both teachers has
`E_{P₀}[N_∅] > e^{2T} / (30 ξ²)`; in particular its cap `n` (its worst-case number of oracle
replies) exceeds this bound. -/
theorem prop_scalar (T : ℕ) (hT : 1 ≤ T) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) :
    InClass T 1 (teacher (-T)) ∧ InClass T 1 (teacher (-T + 3 * ξ)) ∧
      ∀ {Ω : Type*} [Fintype Ω] {n : ℕ} (A : CappedAlgo Ω n),
        99 / 100 ≤ A.successProb (teacher (-T)) ξ →
        99 / 100 ≤ A.successProb (teacher (-T + 3 * ξ)) ξ →
        Real.exp (2 * T) / (30 * ξ ^ 2) <
            A.expect (teacher (-T)) (fun z => (A.emptyCount z : ℝ)) ∧
          Real.exp (2 * T) / (30 * ξ ^ 2) < n := by
  refine ⟨teacher0_inClass T, teacher1_inClass T hT ξ hξ0.le hξ1, ?_⟩
  intro Ω _ n A h0 h1
  have h := (A.expect_emptyCount_gt T ξ hξ0 hξ1 h0 h1).2
  refine ⟨h, h.trans_le ?_⟩
  calc A.expect (teacher (-T)) (fun z => (A.emptyCount z : ℝ))
      ≤ A.expect (teacher (-T)) (fun _ => (n : ℝ)) :=
        A.expect_mono _ (teacher_mem _) fun z => by exact_mod_cast A.emptyCount_le z
    _ = n := A.expect_const _ _

/-! ### `lem:gls-root-simulation` -/

/-- The sign `s = 2U₁ - 1 ∈ {-1, 1}` of a token. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- `lem:gls-root-simulation`, algebraic step: `|s a - u| = |a - s u|` for `s = 2U₁ - 1`. So `s a`
estimates the root logit `u` within `ξ` exactly when the requested component `a` is within `ξ` of
the centered logit `s u` of the token `U₁`. -/
theorem abs_sgn_mul_sub (b : Bool) (a u : ℝ) : |sgn b * a - u| = |a - sgn b * u| := by
  cases b
  · simp only [sgn, Bool.false_eq_true, ite_false]
    rw [show -1 * a - u = -(a - -1 * u) by ring, abs_neg]
  · simp [sgn]

/-- `lem:gls-root-simulation` in the finite model. Let `A` be a capped adaptive algorithm that,
besides its replies, outputs a token `U₁ = token ω r` and a number `a = comp ω r` (the requested
root component). If under each of the two teachers of `prop:scalar`, with probability at least
`0.99`, `a` is within `ξ` of the centered logit `(2U₁ - 1) ℓ_P(∅)` of that token (the faithfulness
contract, taken as a hypothesis), then any reply count `M` that dominates the number of
empty-prefix replies satisfies `E_{P₀}[M] > e^{2T} / (30 ξ²)`. -/
theorem gls_root_simulation {Ω : Type*} [Fintype Ω] {n : ℕ} (A : CappedAlgo Ω n) (T ξ : ℝ)
    (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 6) (token : Ω → Word n → Bool) (comp : Ω → Word n → ℝ)
    (h0 : 99 / 100 ≤ A.prob (teacher (-T)) (univ.filter fun z =>
      |comp z.1 z.2 - sgn (token z.1 z.2) * logit (teacher (-T)) []| ≤ ξ))
    (h1 : 99 / 100 ≤ A.prob (teacher (-T + 3 * ξ)) (univ.filter fun z =>
      |comp z.1 z.2 - sgn (token z.1 z.2) * logit (teacher (-T + 3 * ξ)) []| ≤ ξ))
    (M : Ω × Word n → ℝ) (hM : ∀ z, (A.emptyCount z : ℝ) ≤ M z) :
    Real.exp (2 * T) / (30 * ξ ^ 2) < A.expect (teacher (-T)) M := by
  -- the scalar estimator `ŝ = (2U₁ - 1) a`
  let B : CappedAlgo Ω n :=
    { A with estimate := fun ω r => sgn (token ω r) * comp ω r }
  have hsucc : ∀ P : NextBit, B.successProb P ξ = A.prob P (univ.filter fun z =>
      |comp z.1 z.2 - sgn (token z.1 z.2) * logit P []| ≤ ξ) := by
    intro P
    simp only [CappedAlgo.successProb, CappedAlgo.successSet, B, abs_sgn_mul_sub]
    rfl
  have h := (B.expect_emptyCount_gt T ξ hξ0 hξ1 (by rw [hsucc]; exact h0)
    (by rw [hsucc]; exact h1)).2
  exact h.trans_le (A.expect_mono _ (teacher_mem _) hM)

end LowLogitRank.Scalar
