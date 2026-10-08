import LowLogitRank.Basic

/-!
# Helpers for `sec:hardness` and `sec:parity`

* `rank_le_of_linearState`: a logit function computed by a linear state machine of dimension
  `card ι` (`s(hb) = A_{t,b} s(h)`, `ℓ(h) = w_t s(h)`) has every cut matrix of rank `≤ card ι`.
  This is the factorization argument in the proof of `lem:hard-teacher`.
* `sum_condProb_prefix`: the mass of the words that start with a fixed prefix `g` is `P(g)`.
* monotonicity of `sigmoid`, and nonnegativity of `condProb`.
-/

namespace LowLogitRank.Hardness

open Finset

/-- The real value `0` or `1` of a bit. -/
def bitValue (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem bitValue_true : bitValue true = 1 := rfl
@[simp] theorem bitValue_false : bitValue false = 0 := rfl

/-! ### Linear state machines -/

section LinearState

variable {ι : Type*} [Fintype ι]

/-- The readout of the continuation `f` from a state at time `t`:
`s ↦ w_{t+m}ᵀ A_{t+m-1,f_m} ⋯ A_{t,f_1} s`. -/
def readout (A : ℕ → Bool → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (w : ℕ → (ι → ℝ) →ₗ[ℝ] ℝ) :
    ℕ → List Bool → (ι → ℝ) →ₗ[ℝ] ℝ
  | t, [] => w t
  | t, b :: f => (readout A w (t + 1) f).comp (A t b)

omit [Fintype ι] in
theorem logit_append_eq_readout (ℓ : List Bool → ℝ) (s : List Bool → ι → ℝ)
    (A : ℕ → Bool → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (w : ℕ → (ι → ℝ) →ₗ[ℝ] ℝ)
    (hA : ∀ h b, s (h ++ [b]) = A h.length b (s h)) (hw : ∀ h, ℓ h = w h.length (s h))
    (h f : List Bool) : ℓ (h ++ f) = readout A w h.length f (s h) := by
  induction f generalizing h with
  | nil => simp [readout, hw]
  | cons b f ih =>
    have := ih (h ++ [b])
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_singleton] at this
    rw [this, hA]
    rfl

/-- A logit function computed by a linear state machine on `ι → ℝ` has rank at most `card ι`
at every cut, for every horizon `T`. -/
theorem rank_le_of_linearState (ℓ : List Bool → ℝ) (s : List Bool → ι → ℝ)
    (A : ℕ → Bool → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (w : ℕ → (ι → ℝ) →ₗ[ℝ] ℝ)
    (hA : ∀ h b, s (h ++ [b]) = A h.length b (s h)) (hw : ∀ h, ℓ h = w h.length (s h))
    (T t : ℕ) : (logitCutMatrix ℓ T t).rank ≤ Fintype.card ι := by
  classical
  let S : Matrix (Word t) ι ℝ := fun h i => s h.toList i
  let W : Matrix ι (ShortWord (T - t)) ℝ := fun i f =>
    readout A w t f.2.toList (fun j => if i = j then 1 else 0)
  have hM : logitCutMatrix ℓ T t = S * W := by
    ext h f
    rw [Matrix.mul_apply]
    simp only [logitCutMatrix, S, W]
    rw [logit_append_eq_readout ℓ s A w hA hw, List.Vector.toList_length,
      LinearMap.pi_apply_eq_sum_univ]
    simp [smul_eq_mul]
  rw [hM]
  exact (Matrix.rank_mul_le_left S W).trans (Matrix.rank_le_card_width S)

end LinearState

/-! ### Prefix events -/

/-- The words of length `m` that continue `h` and start with `g` have total conditional mass
`P(g | h)`. -/
theorem sum_condProb_prefix (p : NextBit) (g : List Bool) :
    ∀ (h : List Bool) (m : ℕ), g.length ≤ m →
      ∑ z : Word m, (if g <+: z.toList then condProb p h z.toList else 0) = condProb p h g := by
  induction g with
  | nil => intro h m _; simp [sum_condProb]
  | cons b g ih =>
    intro h m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    rw [sum_word_succ]
    simp only [List.Vector.toList_cons, List.cons_prefix_cons, condProb_cons]
    have hm' : g.length ≤ m := by simp at hm; omega
    rw [Fintype.sum_bool]
    rw [← ih (h ++ [b]) m hm', Finset.mul_sum]
    cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, true_and,
      ite_false, Finset.sum_const_zero, zero_add, add_zero] <;>
    exact Finset.sum_congr rfl fun z _ => by split_ifs <;> simp

/-! ### Elementary facts -/

theorem sigmoid_le_sigmoid {u v : ℝ} (h : u ≤ v) : sigmoid u ≤ sigmoid v := by
  unfold sigmoid
  apply inv_anti₀ (by positivity)
  have := Real.exp_le_exp.mpr (neg_le_neg h)
  linarith

theorem condProb_nonneg (p : NextBit) (hp : ∀ h, 0 ≤ p h ∧ p h ≤ 1) :
    ∀ h f, 0 ≤ condProb p h f := by
  intro h f
  induction f generalizing h with
  | nil => simp
  | cons b f ih =>
    rw [condProb_cons]
    refine mul_nonneg ?_ (ih _)
    cases b <;> simp [bitProb, (hp h).1, (hp h).2]

/-- A continuation through fair positions has conditional probability `2^{-|f|}`. -/
theorem condProb_of_fair (p : NextBit) (h f : List Bool)
    (hp : ∀ g : List Bool, h.length ≤ g.length → g.length < h.length + f.length → p g = 1 / 2) :
    condProb p h f = (1 / 2) ^ f.length := by
  induction f generalizing h with
  | nil => simp
  | cons b f ih =>
    rw [condProb_cons, ih]
    · have : p h = 1 / 2 := hp h le_rfl (by simp)
      cases b <;> simp [bitProb, this, pow_succ] <;> ring
    · intro g h1 h2
      exact hp g (by simp at h1; omega) (by simp at h2 ⊢; omega)

end LowLogitRank.Hardness
