import LowLogitRank.Basic

/-!
# Relative entropy on finite sets (used by `prop:scalar`)

`klDiv P Q = ∑ z, P z log (P z / Q z)` with Lean's conventions `log 0 = 0` and `x / 0 = 0`. When
`Q z = 0` implies `P z = 0` (the only case used below) and `P, Q` are nonnegative, every term with
`P z = 0` vanishes and every other term has `Q z > 0`, so this is the usual relative entropy.

This file proves the three general facts used in the stopped-transcript argument of
`prop:scalar`:
* data processing for an event (`binKL_le_klDiv`, via the log-sum inequality);
* the binary Pinsker inequality `kl(a‖b) ≥ 2 (a - b)²` (`pinsker`);
* the chain rule for autoregressive (next-bit) laws (`klDiv_condProb`).
-/

namespace LowLogitRank.Scalar

open Finset

/-- Relative entropy `∑ z, P z log (P z / Q z)` on a finite set. -/
noncomputable def klDiv {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ :=
  ∑ z, P z * Real.log (P z / Q z)

/-- The Bernoulli law on `Bool` with `P(true) = a`. -/
def bern (a : ℝ) : Bool → ℝ := fun c => if c then a else 1 - a

/-- `KL(Ber(a) ‖ Ber(b))`. -/
noncomputable def binKL (a b : ℝ) : ℝ := klDiv (bern a) (bern b)

theorem binKL_eq (a b : ℝ) :
    binKL a b = a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  simp [binKL, klDiv, bern]

theorem binKL_self (a : ℝ) : binKL a a = 0 := by
  rw [binKL_eq]
  rcases eq_or_ne a 0 with h | h
  · simp [h]
  rcases eq_or_ne (1 - a) 0 with h' | h'
  · simp [h']
  simp [div_self h, div_self h']

theorem binKL_symm (a b : ℝ) : binKL a b = binKL (1 - a) (1 - b) := by
  rw [binKL_eq, binKL_eq]
  simp only [sub_sub_cancel]
  ring

theorem bitProb_eq_bern (p : NextBit) (h : List Bool) (c : Bool) :
    bitProb p h c = bern (p h) c := rfl

/-! ### Data processing for an event -/

/-- The log-sum inequality on a finite set `s`. -/
theorem logSum_le {α : Type*} (s : Finset α) (P Q : α → ℝ) (hP : ∀ z, 0 ≤ P z)
    (hQ : ∀ z, 0 ≤ Q z) (hac : ∀ z, Q z = 0 → P z = 0) :
    (∑ z ∈ s, P z) * Real.log ((∑ z ∈ s, P z) / ∑ z ∈ s, Q z) ≤
      ∑ z ∈ s, P z * Real.log (P z / Q z) := by
  set a := ∑ z ∈ s, P z with ha
  set b := ∑ z ∈ s, Q z with hb
  have hb0 : 0 ≤ b := sum_nonneg fun z _ => hQ z
  rcases hb0.eq_or_lt with hb0 | hbpos
  · -- `b = 0`: everything vanishes on `s`
    have hQz : ∀ z ∈ s, Q z = 0 :=
      (sum_eq_zero_iff_of_nonneg fun z _ => hQ z).mp hb0.symm
    have hPz : ∀ z ∈ s, P z = 0 := fun z hz => hac z (hQz z hz)
    have ha0 : a = 0 := sum_eq_zero hPz
    rw [ha0, zero_mul]
    exact le_of_eq (sum_eq_zero fun z hz => by rw [hPz z hz, zero_mul]).symm
  · -- per-term bound `P log(P/Q) - P log(a/b) ≥ P - Q a/b`
    have key : ∀ z ∈ s, P z - Q z * (a / b) ≤
        P z * Real.log (P z / Q z) - P z * Real.log (a / b) := by
      intro z hz
      rcases (hP z).eq_or_lt with hPz | hPz
      · rw [← hPz]
        have : 0 ≤ Q z * (a / b) :=
          mul_nonneg (hQ z) (div_nonneg (sum_nonneg fun z _ => hP z) hbpos.le)
        simp only [zero_mul, sub_zero, zero_sub]
        linarith
      · have hQz : 0 < Q z := (hQ z).lt_of_ne fun e => hPz.ne' (hac z e.symm)
        have hapos : 0 < a := hPz.trans_le (single_le_sum (fun z _ => hP z) hz)
        have hy : 0 < Q z / P z * (a / b) := by positivity
        have hlog := Real.log_le_sub_one_of_pos hy
        rw [Real.log_mul (by positivity) (by positivity), Real.log_div hQz.ne' hPz.ne',
          Real.log_div hapos.ne' hbpos.ne'] at hlog
        rw [Real.log_div hPz.ne' hQz.ne', Real.log_div hapos.ne' hbpos.ne']
        have h1 : P z * (Q z / P z * (a / b) - 1) = Q z * (a / b) - P z := by
          field_simp
        have h2 := mul_le_mul_of_nonneg_left hlog hPz.le
        rw [h1] at h2
        nlinarith
    have hsum := sum_le_sum key
    rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul, ← ha, ← hb] at hsum
    have : b * (a / b) = a := by field_simp
    linarith

/-- Data processing for an event `s` (used in `prop:scalar`): `kl(P(s) ‖ Q(s)) ≤ KL(P ‖ Q)`. -/
theorem binKL_le_klDiv {α : Type*} [Fintype α] (P Q : α → ℝ)
    (hP : ∀ z, 0 ≤ P z) (hQ : ∀ z, 0 ≤ Q z) (hP1 : ∑ z, P z = 1) (hQ1 : ∑ z, Q z = 1)
    (hac : ∀ z, Q z = 0 → P z = 0) (s : Finset α) :
    binKL (∑ z ∈ s, P z) (∑ z ∈ s, Q z) ≤ klDiv P Q := by
  classical
  have hPc : ∑ z ∈ sᶜ, P z = 1 - ∑ z ∈ s, P z := by
    rw [← hP1, ← sum_add_sum_compl s P]; ring
  have hQc : ∑ z ∈ sᶜ, Q z = 1 - ∑ z ∈ s, Q z := by
    rw [← hQ1, ← sum_add_sum_compl s Q]; ring
  rw [binKL_eq, klDiv, ← sum_add_sum_compl s, ← hPc, ← hQc]
  exact add_le_add (logSum_le s P Q hP hQ hac) (logSum_le sᶜ P Q hP hQ hac)

/-! ### Binary Pinsker inequality -/

/-- Pinsker for `a = 0`: `-log (1 - b) ≥ 2 b²`. -/
theorem pinsker_zero (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : 2 * (0 - b) ^ 2 ≤ binKL 0 b := by
  rw [binKL_eq]
  simp only [zero_mul, zero_add, sub_zero, one_mul]
  -- `G x = log (1/(1-x)) - 2 x²` is monotone on `[0, b]`
  let G : ℝ → ℝ := fun x => -Real.log (1 - x) - 2 * x ^ 2
  have hG : ∀ x, x < 1 → HasDerivAt G (1 / (1 - x) - 4 * x) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h2 := (h1.log (by linarith)).neg
    have h3 : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_mul 2
    convert h2.sub h3 using 1
    field_simp
    ring
  have hmono : MonotoneOn G (Set.Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
    · intro x hx
      exact (hG x (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hG x (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hG x (by linarith [hx.2])).deriv]
      have h1x : 0 < 1 - x := by linarith [hx.2]
      have : 1 / (1 - x) - 4 * x = (1 - 2 * x) ^ 2 / (1 - x) := by
        field_simp
        ring
      rw [this]
      positivity
  have := hmono ⟨le_refl 0, hb0.le⟩ ⟨hb0.le, le_refl b⟩ hb0.le
  simp only [G, sub_zero, Real.log_one, neg_zero] at this
  rw [one_div, Real.log_inv]
  nlinarith [this]

/-- Pinsker for `0 < a < 1`. -/
theorem pinsker_interior (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binKL a b := by
  -- `G x = -a log x - (1-a) log (1-x) - 2 (a - x)²`, so `binKL a x - 2(a-x)² = G x - G a`
  let G : ℝ → ℝ := fun x => -a * Real.log x - (1 - a) * Real.log (1 - x) - 2 * (a - x) ^ 2
  have hG : ∀ x, 0 < x → x < 1 →
      HasDerivAt G ((x - a) * (1 - 2 * x) ^ 2 / (x * (1 - x))) x := by
    intro x hx0 hx1
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have hl1 := ((Real.hasDerivAt_log hx0.ne').const_mul (-a))
    have hl2 := ((h1.log (by linarith)).const_mul (1 - a))
    have hq : HasDerivAt (fun x : ℝ => 2 * (a - x) ^ 2) (2 * (2 * (a - x) * (-1))) x := by
      have := ((hasDerivAt_id x).const_sub a).pow 2
      simpa using this.const_mul 2
    convert (hl1.sub hl2).sub hq using 1
    have : 0 < 1 - x := by linarith
    field_simp
    ring
  have hval : ∀ x, 0 < x → x < 1 → binKL a x - 2 * (a - x) ^ 2 = G x - G a := by
    intro x hx0 hx1
    rw [binKL_eq, Real.log_div ha0.ne' hx0.ne', Real.log_div (by linarith) (by linarith)]
    simp only [G]
    ring
  have hcont : ∀ s ⊆ Set.Ioo (0 : ℝ) 1, ContinuousOn G s := fun s hs x hx =>
    (hG x (hs hx).1 (hs hx).2).continuousAt.continuousWithinAt
  have hdiff : ∀ s ⊆ Set.Ioo (0 : ℝ) 1, DifferentiableOn ℝ G s := fun s hs x hx =>
    (hG x (hs hx).1 (hs hx).2).differentiableAt.differentiableWithinAt
  have key : G a ≤ G b := by
    rcases le_total a b with hab | hab
    · have hsub : Set.Icc a b ⊆ Set.Ioo 0 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hmono : MonotoneOn G (Set.Icc a b) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc a b) (hcont _ hsub)
        · exact hdiff _ (interior_subset.trans hsub)
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hG x (by linarith [hx.1]) (by linarith [hx.2])).deriv]
          have h1 : 0 ≤ x - a := by linarith [hx.1]
          have h2 : 0 < x * (1 - x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
          positivity
      exact hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
    · have hsub : Set.Icc b a ⊆ Set.Ioo 0 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hanti : AntitoneOn G (Set.Icc b a) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc b a) (hcont _ hsub)
        · exact hdiff _ (interior_subset.trans hsub)
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hG x (by linarith [hx.1]) (by linarith [hx.2])).deriv]
          have h1 : 0 ≤ a - x := by linarith [hx.2]
          have h2 : 0 < x * (1 - x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
          have : (x - a) * (1 - 2 * x) ^ 2 / (x * (1 - x)) =
              -((a - x) * (1 - 2 * x) ^ 2 / (x * (1 - x))) := by ring
          rw [this, neg_nonpos]
          positivity
      exact hanti ⟨le_refl b, hab⟩ ⟨hab, le_refl a⟩ hab
  have := hval b hb0 hb1
  linarith

/-- Binary Pinsker inequality (used in `prop:scalar`): `KL(Ber(a) ‖ Ber(b)) ≥ 2 (a - b)²` for
`a ∈ [0,1]`, `b ∈ (0,1)`. -/
theorem pinsker (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ binKL a b := by
  rcases ha0.eq_or_lt with ha | ha
  · rw [← ha]; exact pinsker_zero b hb0 hb1
  rcases ha1.eq_or_lt with ha' | ha'
  · rw [ha', binKL_symm, sub_self]
    have := pinsker_zero (1 - b) (by linarith) (by linarith)
    calc 2 * (1 - b) ^ 2 = 2 * (0 - (1 - b)) ^ 2 := by ring
      _ ≤ _ := this
  exact pinsker_interior a b ha ha' hb0 hb1

/-! ### Chain rule for next-bit laws -/

/-- `pathSum ι h f = ∑_{k < |f|} ι (h ++ f.take k)`: the sum of `ι` over the histories visited
when the continuation `f` is generated after `h` (see `pathSum_eq_sum`). -/
def pathSum (ι : List Bool → ℝ) : List Bool → List Bool → ℝ
  | _, [] => 0
  | h, c :: f => ι h + pathSum ι (h ++ [c]) f

@[simp] theorem pathSum_nil (ι : List Bool → ℝ) (h : List Bool) : pathSum ι h [] = 0 := rfl

@[simp] theorem pathSum_cons (ι : List Bool → ℝ) (h : List Bool) (c : Bool) (f : List Bool) :
    pathSum ι h (c :: f) = ι h + pathSum ι (h ++ [c]) f := rfl

theorem pathSum_eq_sum (ι : List Bool → ℝ) (h f : List Bool) :
    pathSum ι h f = ∑ k ∈ range f.length, ι (h ++ f.take k) := by
  induction f generalizing h with
  | nil => simp
  | cons c f ih =>
    rw [pathSum_cons, ih, List.length_cons, sum_range_succ']
    simp [add_comm]

theorem pathSum_congr {ι ι' : List Bool → ℝ} (hι : ∀ g, ι g = ι' g) (h f : List Bool) :
    pathSum ι h f = pathSum ι' h f := by
  simp only [pathSum_eq_sum, hι]

theorem pathSum_const_mul (κ : ℝ) (ι : List Bool → ℝ) (h f : List Bool) :
    pathSum (fun g => κ * ι g) h f = κ * pathSum ι h f := by
  simp only [pathSum_eq_sum, mul_sum]

theorem condProb_pos (p : NextBit) (hp : ∀ g, 0 < p g ∧ p g < 1) (h f : List Bool) :
    0 < condProb p h f := by
  induction f generalizing h with
  | nil => simp
  | cons c f ih =>
    rw [condProb_cons]
    have : 0 < bitProb p h c := by
      cases c
      · simp [bitProb, (hp h).2]
      · simp [bitProb, (hp h).1]
    exact mul_pos this (ih _)

/-- Chain rule: the relative entropy between the laws of a length-`m` continuation of `h` under
two next-bit models is the expected sum, along the generated path, of the one-step Bernoulli
divergences. -/
theorem klDiv_condProb (a b : NextBit) (ha : ∀ g, 0 < a g ∧ a g < 1)
    (hb : ∀ g, 0 < b g ∧ b g < 1) (m : ℕ) (h : List Bool) :
    ∑ f : Word m, condProb a h f.toList * Real.log (condProb a h f.toList / condProb b h f.toList)
      = ∑ f : Word m, condProb a h f.toList *
          pathSum (fun g => binKL (a g) (b g)) h f.toList := by
  induction m generalizing h with
  | zero => simp
  | succ m ih =>
    rw [sum_word_succ, sum_word_succ]
    simp only [List.Vector.toList_cons, condProb_cons, pathSum_cons]
    have hsplit : ∀ (c : Bool) (v : Word m),
        bitProb a h c * condProb a (h ++ [c]) v.toList *
          Real.log (bitProb a h c * condProb a (h ++ [c]) v.toList /
            (bitProb b h c * condProb b (h ++ [c]) v.toList)) =
        bitProb a h c * Real.log (bitProb a h c / bitProb b h c) *
            condProb a (h ++ [c]) v.toList +
          bitProb a h c * (condProb a (h ++ [c]) v.toList *
            Real.log (condProb a (h ++ [c]) v.toList / condProb b (h ++ [c]) v.toList)) := by
      intro c v
      have hpa := condProb_pos a ha (h ++ [c]) v.toList
      have hpb := condProb_pos b hb (h ++ [c]) v.toList
      have hba : 0 < bitProb a h c := by
        cases c
        · simp [bitProb, (ha h).2]
        · simp [bitProb, (ha h).1]
      have hbb : 0 < bitProb b h c := by
        cases c
        · simp [bitProb, (hb h).2]
        · simp [bitProb, (hb h).1]
      rw [mul_div_mul_comm, Real.log_mul (by positivity) (by positivity)]
      ring
    simp only [hsplit, sum_add_distrib, ← sum_mul, ← mul_sum, sum_condProb, ih]
    have hk : ∑ c : Bool, bitProb a h c * Real.log (bitProb a h c / bitProb b h c) =
        binKL (a h) (b h) := by
      simp only [binKL, klDiv, bitProb_eq_bern]
    rw [hk]
    simp only [mul_add, sum_add_distrib, ← mul_sum, ← sum_mul, sum_condProb, mul_one]
    have hb1 : ∑ c : Bool, bitProb a h c = 1 := by
      rw [Fintype.sum_bool, bitProb_add]
    rw [hb1, one_mul]
    congr 1
    refine sum_congr rfl fun c _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun v _ => ?_
    ring

end LowLogitRank.Scalar
