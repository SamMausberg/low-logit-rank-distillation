import Mathlib

/-!
# The model of `sec:model`

Binary strings are lists of booleans, with `true` standing for the bit `1`. A distribution on
`{0,1}^T` is described by its next-bit probabilities: `p h` is the probability that the bit after
the prefix `h` is `1`. The probability of a continuation `f` after a prefix `h` is the product of
the next-bit probabilities along `f` (`condProb`). Every fully supported distribution on `{0,1}^T`
arises in this way from its own conditionals, see `Coupling.lean`.

The centered logit is `ℓ(h) = (1/2) log (p h / (1 - p h))`, so that `p h = σ(2 ℓ(h))`.
At a cut `t` the logit matrix `H_t` has rows `h ∈ {0,1}^t` and columns `f ∈ {0,1}^{<T-t}`, and the
class `𝒞_{T,d}` asks for full support, `|ℓ| ≤ T` and `rank H_t ≤ d` at every cut `t < T`.
The probability matrix `G_t` has rows `h ∈ {0,1}^t`, columns `f ∈ {0,1}^{T-t}` and entries
`P(f | h)`.
-/

namespace LowLogitRank

open Finset

/-! ### The logistic function -/

/-- The logistic function `σ(u) = (1 + e^{-u})⁻¹`. -/
noncomputable def sigmoid (u : ℝ) : ℝ := (1 + Real.exp (-u))⁻¹

theorem sigmoid_pos (u : ℝ) : 0 < sigmoid u := by
  unfold sigmoid; positivity

theorem sigmoid_lt_one (u : ℝ) : sigmoid u < 1 := by
  unfold sigmoid
  have h : 0 < Real.exp (-u) := Real.exp_pos _
  rw [inv_lt_one₀ (by linarith)]
  linarith

theorem one_sub_sigmoid (u : ℝ) : 1 - sigmoid u = sigmoid (-u) := by
  unfold sigmoid
  have h1 : (0 : ℝ) < 1 + Real.exp (-u) := by positivity
  have h2 : (0 : ℝ) < 1 + Real.exp u := by positivity
  rw [neg_neg]
  field_simp
  have : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  nlinarith [this]

theorem sigmoid_div_one_sub (u : ℝ) : sigmoid u / (1 - sigmoid u) = Real.exp u := by
  rw [one_sub_sigmoid]
  unfold sigmoid
  have h1 : (0 : ℝ) < 1 + Real.exp (-u) := by positivity
  have h2 : (0 : ℝ) < 1 + Real.exp u := by positivity
  rw [neg_neg]
  field_simp
  have : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  nlinarith [this, Real.exp_pos u]

/-! ### Next-bit models and conditional probabilities -/

/-- A binary next-bit model: `p h` is the probability that the bit following the prefix `h` is `1`
(`true`). Only prefixes of length `< T` matter for a length-`T` distribution. -/
abbrev NextBit := List Bool → ℝ

/-- The probability of the bit `b` after the prefix `h`. -/
def bitProb (p : NextBit) (h : List Bool) (b : Bool) : ℝ := if b then p h else 1 - p h

/-- `condProb p h f` is the conditional probability `P(f | h)` of the continuation `f` after the
prefix `h`, given by the autoregressive product rule. -/
def condProb (p : NextBit) : List Bool → List Bool → ℝ
  | _, [] => 1
  | h, b :: f => bitProb p h b * condProb p (h ++ [b]) f

@[simp] theorem condProb_nil (p : NextBit) (h : List Bool) : condProb p h [] = 1 := rfl

@[simp] theorem condProb_cons (p : NextBit) (h : List Bool) (b : Bool) (f : List Bool) :
    condProb p h (b :: f) = bitProb p h b * condProb p (h ++ [b]) f := rfl

theorem bitProb_add (p : NextBit) (h : List Bool) : bitProb p h true + bitProb p h false = 1 := by
  simp [bitProb]

theorem condProb_append (p : NextBit) (h f g : List Bool) :
    condProb p h (f ++ g) = condProb p h f * condProb p (h ++ f) g := by
  induction f generalizing h with
  | nil => simp
  | cons b f ih => simp [ih, mul_assoc]

/-! ### Words -/

/-- Binary words of length `n`. -/
abbrev Word (n : ℕ) := List.Vector Bool n

/-- Binary words of length `< m`, the column index set `{0,1}^{<m}`. -/
abbrev ShortWord (m : ℕ) := Σ j : Fin m, Word j

/-- Splitting a word of length `n + 1` into its first bit and the rest. -/
def wordConsEquiv (n : ℕ) : Bool × Word n ≃ Word (n + 1) where
  toFun x := List.Vector.cons x.1 x.2
  invFun v := (v.head, v.tail)
  left_inv x := by simp
  right_inv v := by simp

theorem sum_word_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (F : Word (n + 1) → M) :
    ∑ v, F v = ∑ b : Bool, ∑ v : Word n, F (List.Vector.cons b v) := by
  rw [← (wordConsEquiv n).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Conditional probabilities of the continuations of a fixed length sum to one. This holds for
every real-valued `p`, since `bitProb p h true + bitProb p h false = 1`. -/
theorem sum_condProb (p : NextBit) (m : ℕ) (h : List Bool) :
    ∑ f : Word m, condProb p h f.toList = 1 := by
  induction m generalizing h with
  | zero => simp
  | succ m ih =>
    rw [sum_word_succ]
    simp only [List.Vector.toList_cons, condProb_cons, ← Finset.mul_sum, ih, mul_one]
    simpa [add_comm] using bitProb_add p h

/-- The distribution on `{0,1}^T` defined by a next-bit model. -/
def wordDist (p : NextBit) (T : ℕ) : Word T → ℝ := fun z => condProb p [] z.toList

/-! ### Centered logits, full support and the class `𝒞_{T,d}` -/

/-- The scalar centered logit `ℓ(h) = (1/2) log (p h / (1 - p h))`. -/
noncomputable def logit (p : NextBit) (h : List Bool) : ℝ := Real.log (p h / (1 - p h)) / 2

/-- The next-bit model with prescribed centered logits, `p h = σ(2 ℓ(h))`. -/
noncomputable def ofLogit (ℓ : List Bool → ℝ) : NextBit := fun h => sigmoid (2 * ℓ h)

theorem logit_ofLogit (ℓ : List Bool → ℝ) (h : List Bool) : logit (ofLogit ℓ) h = ℓ h := by
  simp only [logit, ofLogit, sigmoid_div_one_sub, Real.log_exp]
  ring

/-- Full support of the length-`T` distribution: every conditional probability before time `T`
lies strictly between zero and one. -/
def FullSupport (T : ℕ) (p : NextBit) : Prop :=
  ∀ h : List Bool, h.length < T → 0 < p h ∧ p h < 1

theorem ofLogit_fullSupport (ℓ : List Bool → ℝ) (T : ℕ) : FullSupport T (ofLogit ℓ) :=
  fun _ _ => ⟨sigmoid_pos _, sigmoid_lt_one _⟩

theorem ofLogit_logit {p : NextBit} {h : List Bool} (h0 : 0 < p h) (h1 : p h < 1) :
    ofLogit (logit p) h = p h := by
  have hq : 0 < p h / (1 - p h) := div_pos h0 (by linarith)
  simp only [ofLogit, logit, sigmoid]
  rw [show -(2 * (Real.log (p h / (1 - p h)) / 2)) = -Real.log (p h / (1 - p h)) by ring,
    Real.exp_neg, Real.exp_log hq]
  have : 1 - p h ≠ 0 := by linarith
  field_simp
  ring

/-- The logit matrix `H_t` at cut `t`: rows `h ∈ {0,1}^t`, columns `f ∈ {0,1}^{<T-t}`, entries
`ℓ(hf)`. -/
def logitCutMatrix (ℓ : List Bool → ℝ) (T t : ℕ) : Matrix (Word t) (ShortWord (T - t)) ℝ :=
  fun h f => ℓ (h.toList ++ f.2.toList)

/-- The probability matrix `G_t` at cut `t`: rows `h ∈ {0,1}^t`, columns `f ∈ {0,1}^{T-t}`,
entries `P(f | h)`. -/
def probCutMatrix (p : NextBit) (T t : ℕ) : Matrix (Word t) (Word (T - t)) ℝ :=
  fun h f => condProb p h.toList f.toList

/-- The class `𝒞_{T,d}` with a general logit bound `Λ`: full support, `|ℓ(h)| ≤ Λ` for `|h| < T`,
and logit rank at most `d` at every cut `t < T`. -/
structure LogitClass (T : ℕ) (Λ : ℝ) (d : ℕ) (p : NextBit) : Prop where
  fullSupport : FullSupport T p
  logit_le : ∀ h : List Bool, h.length < T → |logit p h| ≤ Λ
  rank_le : ∀ t < T, (logitCutMatrix (logit p) T t).rank ≤ d

/-- The class `𝒞_{T,d}` of the paper: the logit bound is `T`. -/
abbrev InClass (T d : ℕ) (p : NextBit) : Prop := LogitClass T T d p

/-- The probability rank of the length-`T` distribution: the largest rank of `G_t`, `t < T`. -/
noncomputable def probRank (p : NextBit) (T : ℕ) : ℕ :=
  (Finset.range T).sup fun t => (probCutMatrix p T t).rank

theorem probRank_le_iff (p : NextBit) (T R : ℕ) :
    probRank p T ≤ R ↔ ∀ t < T, (probCutMatrix p T t).rank ≤ R := by
  simp [probRank, Finset.sup_le_iff]

theorem le_probRank (p : NextBit) {T t : ℕ} (ht : t < T) :
    (probCutMatrix p T t).rank ≤ probRank p T :=
  Finset.le_sup (f := fun t => (probCutMatrix p T t).rank) (Finset.mem_range.mpr ht)

/-! ### Total variation -/

/-- Total-variation distance `(1/2) ∑ |P z - Q z|` on a finite set. -/
noncomputable def tv {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ := (∑ z, |P z - Q z|) / 2

/-! ### Smoothing (`sec:fixed-rank`) -/

/-- The smoothed model `P^τ(1 | h) = (1 - τ) P(1 | h) + τ / 2`: with probability `τ` a fair bit. -/
noncomputable def smooth (τ : ℝ) (p : NextBit) : NextBit := fun h => (1 - τ) * p h + τ / 2

/-- The smoothed centered logit `ψ_τ(u)` of `eq:softclip`. -/
noncomputable def softclip (τ u : ℝ) : ℝ :=
  Real.log (((2 - τ) * Real.exp (2 * u) + τ) / (τ * Real.exp (2 * u) + (2 - τ))) / 2

/-- The bound `M_τ = (1/2) log ((2 - τ) / τ)` on `|ψ_τ|`. -/
noncomputable def softclipBound (τ : ℝ) : ℝ := Real.log ((2 - τ) / τ) / 2

/-! ### The Chebyshev approximation interface

`ChebyshevApprox` is the approximation theorem behind `lem:softclip-poly` and `lem:poly-sigmoid`,
stated as a proposition so that its proof (`Chebyshev.lean`) and its two applications
(`Approximation.lean`) can be developed separately. Here `(w + w⁻¹)/2` with
`ρ⁻¹ ≤ ‖w‖ ≤ ρ` ranges over the closed Bernstein ellipse of parameter `ρ`, and the conclusion is
the truncation bound `2 M ∑_{j > k} ρ^{-j} = 2 M ρ^{-k} / (ρ - 1)` for the degree-`k` Chebyshev
partial sum, applied to the real part of `f` on `[-1, 1]`. -/
def ChebyshevApprox : Prop :=
  ∀ (f : ℂ → ℂ) (ρ M : ℝ), 1 < ρ →
    (∀ w : ℂ, ρ⁻¹ ≤ ‖w‖ → ‖w‖ ≤ ρ →
      DifferentiableAt ℂ f ((w + w⁻¹) / 2) ∧ ‖f ((w + w⁻¹) / 2)‖ ≤ M) →
    ∀ k : ℕ, ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        |q.eval x - (f (x : ℂ)).re| ≤ 2 * M * ρ⁻¹ ^ k / (ρ - 1)

/-! ### The parameters of `eq:smooth-parameters`

These are the finite parameter choices of Algorithm `alg:fixed`. `T` is the length, `d` the rank,
and `ε, δ` the accuracy and confidence. -/

/-- The explicit token exponent `C_q = 52` of `eq:gls-polynomial-envelope`. -/
def Cq : ℕ := 52

/-- `b_τ = ⌈log₂ (8T/ε)⌉`. -/
noncomputable def bTau (T : ℕ) (ε : ℝ) : ℕ := ⌈Real.logb 2 (8 * T / ε)⌉₊

/-- The smoothing rate `τ = 2^{-⌈log₂ (8T/ε)⌉}`. -/
noncomputable def tauOf (T : ℕ) (ε : ℝ) : ℝ := ((2 : ℝ) ^ bTau T ε)⁻¹

/-- The integer logit bound `L = ⌈log₂ (4/τ)⌉ + 3`. -/
noncomputable def LOf (T : ℕ) (ε : ℝ) : ℕ := ⌈Real.logb 2 (4 / tauOf T ε)⌉₊ + 3

/-- `J = ⌈log₂ (2 T C_q (d+1) L / (εδ))⌉ + 10`. -/
noncomputable def JOf (T d : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈Real.logb 2 (2 * T * Cq * (d + 1) * LOf T ε / (ε * δ))⌉₊ + 10

/-- `N = 100 C_q (d+1) J`. -/
noncomputable def NOf (T d : ℕ) (ε δ : ℝ) : ℕ := 100 * Cq * (d + 1) * JOf T d ε δ

/-- The approximation error `ζ = 2^{-N}`. -/
noncomputable def zetaOf (T d : ℕ) (ε δ : ℝ) : ℝ := ((2 : ℝ) ^ NOf T d ε δ)⁻¹

/-- The polynomial degree `k = 8TN`. -/
noncomputable def kOf (T d : ℕ) (ε δ : ℝ) : ℕ := 8 * T * NOf T d ε δ

/-- The rank `D = binom(d + k, d)` passed to the robust learner. -/
noncomputable def DOf (T d : ℕ) (ε δ : ℝ) : ℕ := Nat.choose (d + kOf T d ε δ) d

/-- `V = 2 T D L / (εδ)` of `eq:gls-polynomial-envelope`. -/
noncomputable def VOf (T d : ℕ) (ε δ : ℝ) : ℝ := 2 * T * DOf T d ε δ * LOf T ε / (ε * δ)

end LowLogitRank
