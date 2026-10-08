import LowLogitRank.Coupling.Words

/-!
# Hybrid inequality and `lem:coupling` for next-bit models

A next-bit model `p` is the sequential experiment with kernel `bitProb p`, so the general bounds
of `Sequential.lean` apply. This file proves the binary hybrid inequality
(`eq:target-telescope`), the suffix and distribution bounds of `lem:coupling`, the transcript
bounds for adaptive one-bit and complete-suffix queries, and the token count
`eq:suffix-charge`.

Throughout, `p` and `q` only need values in `[0,1]` at the prefixes that matter; full support is
not needed (see `FullSupport.unitInterval` to apply the results to fully supported models).
-/

namespace LowLogitRank.Coupling

open Finset

/-! ### Next-bit models as kernels -/

/-- `condProb p` is the sequential law of the kernel `bitProb p`. -/
theorem condProb_eq_seqProb (p : NextBit) (h f : List Bool) :
    condProb p h f = seqProb (bitProb p) h f := by
  induction f generalizing h with
  | nil => rfl
  | cons b f ih => simp [ih]

theorem wordDist_eq_seqLaw (p : NextBit) (T : ℕ) : wordDist p T = seqLaw (bitProb p) T := by
  funext z
  exact condProb_eq_seqProb p [] z.toList

/-- `sec:model`, "successive replies simulate a complete conditional suffix": the transcript of
`m` one-bit queries at `h`, `h f₁`, `h f₁ f₂`, ... has the law `P(f | h)` of the complete
suffix after `h`. -/
theorem seqLaw_successive_bitQuery (p : NextBit) (h : List Bool) (m : ℕ) :
    seqLaw (fun x => bitProb p (h ++ x)) m = fun f => condProb p h f.toList := by
  funext f
  rw [seqLaw, seqProb_shift (bitProb p) h [] f.toList, List.append_nil, condProb_eq_seqProb]

/-- The TV between the next-bit laws at a prefix is `|p h - q h|`. -/
theorem tv_bitProb (p q : NextBit) (h : List Bool) :
    tv (bitProb p h) (bitProb q h) = |p h - q h| := by
  unfold tv
  rw [Fintype.sum_bool]
  simp only [bitProb, ↓reduceIte, Bool.false_eq_true]
  rw [show 1 - p h - (1 - q h) = -(p h - q h) by ring, abs_neg]
  ring

/-- The next-bit law at a prefix where `p` is in `[0,1]` is a probability vector. -/
theorem bitProb_isProbVec {p : NextBit} {h : List Bool} (hp : 0 ≤ p h ∧ p h ≤ 1) :
    IsProbVec (bitProb p h) := by
  refine ⟨fun b => ?_, by rw [Fintype.sum_bool]; exact bitProb_add p h⟩
  cases b <;> simp [bitProb] <;> linarith [hp.1, hp.2]

/-! ### The hybrid inequality -/

/-- `eq:target-telescope` (binary form, after a prefix `h0`): the TV between the continuation
laws of length `m` after `h0` is at most
`∑_{j<m} ∑_{f ∈ {0,1}^j} P(f | h0) |p(h0 f) - q(h0 f)|`, the summed expected next-bit TV along
`p`. Only values in `[0,1]` at the prefixes `h0 f`, `|f| < m`, are assumed. -/
theorem tv_condProb_le_sum (p q : NextBit) (h0 : List Bool) (m : ℕ)
    (hp : ∀ f : List Bool, f.length < m → 0 ≤ p (h0 ++ f) ∧ p (h0 ++ f) ≤ 1)
    (hq : ∀ f : List Bool, f.length < m → 0 ≤ q (h0 ++ f) ∧ q (h0 ++ f) ≤ 1) :
    tv (fun f : Word m => condProb p h0 f.toList) (fun f => condProb q h0 f.toList) ≤
      ∑ j ∈ range m, ∑ f : Word j,
        condProb p h0 f.toList * |p (h0 ++ f.toList) - q (h0 ++ f.toList)| := by
  simp only [condProb_eq_seqProb, ← tv_bitProb]
  exact tv_seqProb_le (bitProb p) (bitProb q) m h0 (fun l hl => bitProb_isProbVec (hp l hl))
    (fun l hl => bitProb_isProbVec (hq l hl))

/-- `eq:target-telescope`: for two next-bit models with values in `[0,1]` before time `T`,
`TV(P, Q) ≤ ∑_{t<T} E_{h ∼ P_{:t}} TV(P(· | h), Q(· | h))`. Here `wordDist p t` is the law of
the first `t` bits of `P` (`prefixMass_wordDist`). -/
theorem tv_wordDist_le_sum (p q : NextBit) (T : ℕ)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1) :
    tv (wordDist p T) (wordDist q T) ≤
      ∑ t ∈ range T, ∑ h : Word t,
        wordDist p t h * tv (bitProb p h.toList) (bitProb q h.toList) := by
  have := tv_condProb_le_sum p q [] T (fun f hf => by simpa using hp f hf)
    (fun f hf => by simpa using hq f hf)
  unfold wordDist
  simpa [tv_bitProb] using this

/-- `eq:target-telescope` with the next-bit TV written as `|p h - q h|`. -/
theorem tv_wordDist_le_sum_abs (p q : NextBit) (T : ℕ)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1) :
    tv (wordDist p T) (wordDist q T) ≤
      ∑ t ∈ range T, ∑ h : Word t, wordDist p t h * |p h.toList - q h.toList| := by
  simpa [tv_bitProb] using tv_wordDist_le_sum p q T hp hq

/-! ### `lem:coupling`: suffix laws and distributions -/

/-- `lem:coupling`, first claim: if `|p h - q h| ≤ η` for every `|h| < T` (with `p, q` in `[0,1]`
there), then at every prefix `h0` the complete conditional suffix laws on `{0,1}^{T-|h0|}`
differ in TV by at most `(T - |h0|) η`. (For `|h0| ≥ T` both sides are zero.) -/
theorem tv_condProb_le_mul (p q : NextBit) (T : ℕ) (η : ℝ)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η) (h0 : List Bool) :
    tv (fun f : Word (T - h0.length) => condProb p h0 f.toList)
        (fun f => condProb q h0 f.toList) ≤ ((T - h0.length : ℕ) : ℝ) * η := by
  simp only [condProb_eq_seqProb]
  refine tv_seqProb_le_mul (bitProb p) (bitProb q) (T - h0.length) h0 η
    (fun l hl => bitProb_isProbVec (hp _ (by simp; omega)))
    (fun l hl => bitProb_isProbVec (hq _ (by simp; omega))) (fun l hl => ?_)
  rw [tv_bitProb]
  exact hη _ (by simp; omega)

/-- `lem:coupling`, last claim: `TV(P, P̃) ≤ T η`. -/
theorem tv_wordDist_le_mul (p q : NextBit) (T : ℕ) (η : ℝ)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η) :
    tv (wordDist p T) (wordDist q T) ≤ T * η := by
  unfold wordDist
  simpa using tv_condProb_le_mul p q T η hp hq hη []

/-- `lem:coupling`, last claim, stated for fully supported distributions `P, P̃` on `{0,1}^T`
through their conditionals `P(1 | h) = P(h1) / P(h)`. -/
theorem tv_le_of_condOfDist {T : ℕ} (P Q : Word T → ℝ) (η : ℝ)
    (hP : ∀ z, 0 < P z) (hP1 : ∑ z, P z = 1) (hQ : ∀ z, 0 < Q z) (hQ1 : ∑ z, Q z = 1)
    (hη : ∀ h : List Bool, h.length < T → |condOfDist P h - condOfDist Q h| ≤ η) :
    tv P Q ≤ T * η := by
  have := tv_wordDist_le_mul (condOfDist P) (condOfDist Q) T η
    (FullSupport.unitInterval (fullSupport_condOfDist hP))
    (FullSupport.unitInterval (fullSupport_condOfDist hQ)) hη
  rwa [wordDist_condOfDist hP hP1, wordDist_condOfDist hQ hQ1] at this

/-- `η ≥ 0` follows from the closeness hypothesis as soon as `T ≥ 1`. -/
theorem mul_eta_nonneg {p q : NextBit} {T : ℕ} {η : ℝ}
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η) : 0 ≤ (T : ℝ) * η := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · simp [hT]
  · exact mul_nonneg (Nat.cast_nonneg T) ((abs_nonneg _).trans (hη [] (by simpa using hT)))

/-! ### Adaptive one-bit queries -/

/-- `lem:coupling` for adaptive one-bit queries (the simulation step of `sec:hardness`): a
randomized algorithm with coin `ω ∼ μ` submits the prefix `query ω x` after the past replies `x`
and receives one bit drawn from the oracle's next-bit law there. If every submitted prefix has
length `< T` and `|p - q| ≤ η` on such prefixes, the joint (coin, transcript) laws of `n` rounds
differ in TV by at most `n η`. -/
theorem tv_bitQuery_le {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : IsProbVec μ) (p q : NextBit)
    (T n : ℕ) (η : ℝ) (query : Ω → List Bool → List Bool)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η)
    (hquery : ∀ ω, ∀ x : List Bool, x.length < n → (query ω x).length < T) :
    tv (jointLaw μ (fun ω x => bitProb p (query ω x)) n)
        (jointLaw μ (fun ω x => bitProb q (query ω x)) n) ≤ n * η :=
  tv_jointLaw_le_mul hμ _ _ n η
    (fun ω x hx => bitProb_isProbVec (hp _ (hquery ω x hx)))
    (fun ω x hx => bitProb_isProbVec (hq _ (hquery ω x hx)))
    (fun ω x hx => by rw [tv_bitProb]; exact hη _ (hquery ω x hx))

/-- Deterministic form of `tv_bitQuery_le`. -/
theorem tv_bitQuery_le_det (p q : NextBit) (T n : ℕ) (η : ℝ) (query : List Bool → List Bool)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η)
    (hquery : ∀ x : List Bool, x.length < n → (query x).length < T) :
    tv (seqLaw (fun x => bitProb p (query x)) n) (seqLaw (fun x => bitProb q (query x)) n) ≤
      n * η :=
  tv_seqLaw_le_mul _ _ n η (fun x hx => bitProb_isProbVec (hp _ (hquery x hx)))
    (fun x hx => bitProb_isProbVec (hq _ (hquery x hx)))
    (fun x hx => by rw [tv_bitProb]; exact hη _ (hquery x hx))

/-! ### Adaptive complete-suffix queries -/

/-- The reply law of a complete conditional suffix query at the prefix `h`: the full word
`z ∈ {0,1}^T` has probability `P(z_{>|h|} | h)` if `h` is a prefix of `z`, and `0` otherwise. -/
noncomputable def suffixReply (p : NextBit) (T : ℕ) (h : List Bool) (z : Word T) : ℝ :=
  if h <+: z.toList then condProb p h (z.toList.drop h.length) else 0

/-- A submitted prefix of length `T` gets a deterministic reply, the same under every oracle.
Such queries can pad an algorithm that makes fewer queries. -/
theorem suffixReply_of_length_eq (p : NextBit) {T : ℕ} (h : List Bool) (hh : h.length = T)
    (z : Word T) : suffixReply p T h z = if z.toList = h then 1 else 0 := by
  unfold suffixReply
  have hd : z.toList.drop h.length = [] := List.drop_eq_nil_of_le (by simp [hh])
  by_cases hz : z.toList = h
  · simp [hz]
  · have : ¬ h <+: z.toList := fun hp =>
      hz (hp.eq_of_length (by simp [hh])).symm
    simp [hz, this]

/-- `lem:coupling`: the reply to a complete suffix query at a prefix of length `≤ T` is a
probability vector on `{0,1}^T`. -/
theorem suffixReply_isProbVec {p : NextBit} {T : ℕ}
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1) {h : List Bool}
    (hh : h.length ≤ T) : IsProbVec (suffixReply p T h) := by
  refine ⟨fun z => ?_, ?_⟩
  · unfold suffixReply
    split_ifs with hz
    · refine condProb_nonneg h _ fun g hg => hp _ ?_
      simp only [List.length_drop, List.Vector.toList_length] at hg
      simp
      omega
    · exact le_rfl
  · unfold suffixReply
    rw [← sum_filter, sum_filter_prefix h hh]
    simp only [extendWord_toList, List.drop_left]
    exact sum_condProb p _ h

/-- The reply TV at a submitted prefix `h` equals the TV of the suffix laws after `h`. -/
theorem tv_suffixReply (p q : NextBit) {T : ℕ} (h : List Bool) (hh : h.length ≤ T) :
    tv (suffixReply p T h) (suffixReply q T h) =
      tv (fun f : Word (T - h.length) => condProb p h f.toList)
        (fun f => condProb q h f.toList) := by
  unfold tv suffixReply
  congr 1
  have : ∀ z : Word T, |(if h <+: z.toList then condProb p h (z.toList.drop h.length) else 0) -
      (if h <+: z.toList then condProb q h (z.toList.drop h.length) else 0)| =
      if h <+: z.toList then
        |condProb p h (z.toList.drop h.length) - condProb q h (z.toList.drop h.length)| else 0 := by
    intro z; split_ifs <;> simp
  simp only [this]
  rw [← sum_filter, sum_filter_prefix h hh]
  simp

/-- `lem:coupling`, at a submitted prefix `h` with `|h| ≤ T`: the reply laws of a complete
suffix query differ in TV by at most `(T - |h|) η`. -/
theorem tv_suffixReply_le_sub (p q : NextBit) (T : ℕ) (η : ℝ)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η) (h : List Bool)
    (hh : h.length ≤ T) :
    tv (suffixReply p T h) (suffixReply q T h) ≤ ((T - h.length : ℕ) : ℝ) * η := by
  rw [tv_suffixReply p q h hh]
  exact tv_condProb_le_mul p q T η hp hq hη h

/-- The per-query bound `T η` used for the transcript claim of `lem:coupling`. -/
theorem tv_suffixReply_le (p q : NextBit) (T : ℕ) (η : ℝ)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η) (h : List Bool)
    (hh : h.length ≤ T) : tv (suffixReply p T h) (suffixReply q T h) ≤ T * η := by
  refine (tv_suffixReply_le_sub p q T η hp hq hη h hh).trans ?_
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  · have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη [] (by simpa using hT))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le T h.length) hη0

/-- `lem:coupling`, adaptive transcript claim: a randomized algorithm (coin `ω ∼ μ`, the same
under both oracles) that makes `n` complete conditional suffix queries, at prefixes of length
`≤ T` chosen from the coin and the past replies, has joint (coin, transcript) laws within TV
`n T η` under the two oracles. An algorithm making at most `n` queries is padded to exactly `n`
(e.g. by `suffixReply_of_length_eq`); its own transcript is a function of the padded one, so
`tv_push_le` applies. -/
theorem tv_suffixQuery_le {Ω : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : IsProbVec μ)
    (p q : NextBit) (T n : ℕ) (η : ℝ) (query : Ω → List (Word T) → List Bool)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η)
    (hquery : ∀ ω, ∀ x : List (Word T), x.length < n → (query ω x).length ≤ T) :
    tv (jointLaw μ (fun ω x => suffixReply p T (query ω x)) n)
        (jointLaw μ (fun ω x => suffixReply q T (query ω x)) n) ≤ n * T * η := by
  rw [mul_assoc]
  exact tv_jointLaw_le_mul hμ _ _ n (T * η)
    (fun ω x hx => suffixReply_isProbVec hp (hquery ω x hx))
    (fun ω x hx => suffixReply_isProbVec hq (hquery ω x hx))
    (fun ω x hx => tv_suffixReply_le p q T η hp hq hη _ (hquery ω x hx))

/-- Deterministic form of `tv_suffixQuery_le`. -/
theorem tv_suffixQuery_le_det (p q : NextBit) (T n : ℕ) (η : ℝ)
    (query : List (Word T) → List Bool)
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1)
    (hq : ∀ h : List Bool, h.length < T → 0 ≤ q h ∧ q h ≤ 1)
    (hη : ∀ h : List Bool, h.length < T → |p h - q h| ≤ η)
    (hquery : ∀ x : List (Word T), x.length < n → (query x).length ≤ T) :
    tv (seqLaw (fun x => suffixReply p T (query x)) n)
        (seqLaw (fun x => suffixReply q T (query x)) n) ≤ n * T * η := by
  rw [mul_assoc]
  exact tv_seqLaw_le_mul _ _ n (T * η) (fun x hx => suffixReply_isProbVec hp (hquery x hx))
    (fun x hx => suffixReply_isProbVec hq (hquery x hx))
    (fun x hx => tv_suffixReply_le p q T η hp hq hη _ (hquery x hx))

/-! ### Token charge of a complete suffix (`eq:suffix-charge`) -/

/-- `eq:suffix-charge`: `∑_{j=t}^{T-1} (j+1) = (T(T+1) - t(t+1))/2`, stated without division. -/
theorem two_mul_suffixCharge {t T : ℕ} (htT : t ≤ T) :
    2 * ∑ j ∈ Ico t T, (j + 1) = T * (T + 1) - t * (t + 1) := by
  induction T, htT using Nat.le_induction with
  | base => simp
  | succ T hT ih =>
    rw [sum_Ico_succ_top hT, mul_add, ih]
    have hle : t * (t + 1) ≤ T * (T + 1) := Nat.mul_le_mul hT (by omega)
    have e : (T + 1) * (T + 1 + 1) = T * (T + 1) + 2 * (T + 1) := by ring
    rw [e]
    omega

/-- `eq:suffix-charge` with the (exact) division by two. -/
theorem suffixCharge {t T : ℕ} (htT : t ≤ T) :
    ∑ j ∈ Ico t T, (j + 1) = (T * (T + 1) - t * (t + 1)) / 2 := by
  have := two_mul_suffixCharge htT
  omega

/-- `eq:suffix-charge` at `t = 0`: a complete string costs `T(T+1)/2` tokens. -/
theorem two_mul_suffixCharge_zero (T : ℕ) : 2 * ∑ j ∈ range T, (j + 1) = T * (T + 1) := by
  have := two_mul_suffixCharge (Nat.zero_le T)
  rw [← range_eq_Ico] at this
  simpa using this

/-- Every complete suffix query costs at most `T(T+1)/2` tokens. -/
theorem two_mul_suffixCharge_le {t T : ℕ} (htT : t ≤ T) :
    2 * ∑ j ∈ Ico t T, (j + 1) ≤ T * (T + 1) := by
  rw [two_mul_suffixCharge htT]
  exact Nat.sub_le _ _

end LowLogitRank.Coupling
