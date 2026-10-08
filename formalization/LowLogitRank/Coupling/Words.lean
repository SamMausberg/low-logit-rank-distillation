import LowLogitRank.Coupling.Sequential

/-!
# Distributions on `{0,1}^T` and their conditionals (`sec:model`)

A fully supported distribution `P` on `{0,1}^T` defines next-bit conditionals
`P(1 | h) = P(h1) / P(h)` from its prefix masses. We prove that these conditionals are strictly
between zero and one, that the product rule recovers `P`, and conversely that every next-bit
model with conditionals strictly between zero and one defines a fully supported distribution
whose conditionals are the given ones. This justifies describing the distributions of
`sec:model` by next-bit models. We also identify `wordDist p t` with the law of the first `t`
bits of `wordDist p T` (the measure `P_{:t}` of `eq:target-telescope`).
-/

namespace LowLogitRank.Coupling

open Finset

/-! ### Extending a prefix to a word -/

/-- The word `h ++ f` of length `T`, for a prefix `h` with `|h| ≤ T`. -/
def extendWord {T : ℕ} (h : List Bool) (hh : h.length ≤ T) (f : Word (T - h.length)) : Word T :=
  ⟨h ++ f.toList, by simp; omega⟩

@[simp] theorem extendWord_toList {T : ℕ} (h : List Bool) (hh : h.length ≤ T)
    (f : Word (T - h.length)) : (extendWord h hh f).toList = h ++ f.toList := rfl

/-- Sums over the words with a given prefix `h` are sums over the continuations of `h`. -/
theorem sum_filter_prefix {M : Type*} [AddCommMonoid M] {T : ℕ} (h : List Bool)
    (hh : h.length ≤ T) (F : Word T → M) :
    ∑ z ∈ univ.filter (fun z : Word T => h <+: z.toList), F z =
      ∑ f : Word (T - h.length), F (extendWord h hh f) := by
  have hinv : ∀ z : Word T, h <+: z.toList →
      extendWord h hh ⟨z.toList.drop h.length, by simp⟩ = z := by
    intro z hz
    apply List.Vector.toList_injective
    exact List.prefix_iff_eq_append.mp hz
  refine sum_nbij' (fun z => ⟨z.toList.drop h.length, by simp⟩) (extendWord h hh)
    (fun _ _ => mem_univ _) ?_ ?_ ?_ ?_
  · intro f _
    simp
  · intro z hz
    exact hinv z (mem_filter.mp hz).2
  · intro f _
    apply List.Vector.toList_injective
    simp
  · intro z hz
    rw [hinv z (mem_filter.mp hz).2]

theorem exists_prefix_snoc {h z : List Bool} (hp : h <+: z) (hl : h.length < z.length) :
    ∃ b, h ++ [b] <+: z := by
  obtain ⟨r, rfl⟩ := hp
  cases r with
  | nil => simp at hl
  | cons c r => exact ⟨c, r, by simp⟩

theorem eq_of_prefix_snoc {h z : List Bool} {b b' : Bool} (h1 : h ++ [b] <+: z)
    (h2 : h ++ [b'] <+: z) : b = b' := by
  have h3 := (List.prefix_of_prefix_length_le h1 h2 (by simp)).eq_of_length (by simp)
  simpa using h3

/-! ### Prefix masses and conditionals of a distribution -/

/-- The mass `P(h)` of the words with prefix `h`. -/
noncomputable def prefixMass {T : ℕ} (P : Word T → ℝ) (h : List Bool) : ℝ :=
  ∑ z ∈ univ.filter (fun z : Word T => h <+: z.toList), P z

/-- The next-bit conditionals `P(1 | h) = P(h1) / P(h)` of a distribution on `{0,1}^T`. -/
noncomputable def condOfDist {T : ℕ} (P : Word T → ℝ) : NextBit :=
  fun h => prefixMass P (h ++ [true]) / prefixMass P h

theorem prefixMass_nil {T : ℕ} (P : Word T → ℝ) : prefixMass P [] = ∑ z, P z := by
  simp [prefixMass]

theorem prefixMass_word {T : ℕ} (P : Word T → ℝ) (z : Word T) : prefixMass P z.toList = P z := by
  unfold prefixMass
  rw [sum_filter_prefix z.toList (by simp)]
  have hz : T - z.toList.length = 0 := by simp
  have : ∀ f : Word (T - z.toList.length), extendWord z.toList (by simp) f = z := by
    intro f
    apply List.Vector.toList_injective
    have : f.toList = [] := List.eq_nil_of_length_eq_zero (by simp)
    simp [this]
  simp only [this, sum_const]
  rw [hz]
  simp

theorem prefixMass_split {T : ℕ} (P : Word T → ℝ) (h : List Bool) (hh : h.length < T) :
    prefixMass P h = prefixMass P (h ++ [true]) + prefixMass P (h ++ [false]) := by
  unfold prefixMass
  rw [← sum_filter_add_sum_filter_not (univ.filter fun z : Word T => h <+: z.toList)
    (fun z => h ++ [true] <+: z.toList), filter_filter, filter_filter]
  congr 2
  · ext z
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun hz => hz.2, fun hz => ⟨(List.prefix_append h [true]).trans hz, hz⟩⟩
  · ext z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨b, hb⟩ := exists_prefix_snoc h1 (by simpa using hh)
      cases b
      · exact hb
      · exact absurd hb h2
    · intro hz
      exact ⟨(List.prefix_append h [false]).trans hz, fun ht => by
        simpa using eq_of_prefix_snoc ht hz⟩

theorem prefixMass_nonneg {T : ℕ} {P : Word T → ℝ} (hP : ∀ z, 0 ≤ P z) (h : List Bool) :
    0 ≤ prefixMass P h :=
  sum_nonneg fun z _ => hP z

theorem prefixMass_pos {T : ℕ} {P : Word T → ℝ} (hP : ∀ z, 0 < P z) (h : List Bool)
    (hh : h.length ≤ T) : 0 < prefixMass P h := by
  refine sum_pos (fun z _ => hP z) ⟨extendWord h hh (List.Vector.replicate _ false), ?_⟩
  simp

theorem bitProb_condOfDist {T : ℕ} {P : Word T → ℝ} (hP : ∀ z, 0 < P z) (h : List Bool)
    (hh : h.length < T) (b : Bool) :
    bitProb (condOfDist P) h b = prefixMass P (h ++ [b]) / prefixMass P h := by
  have hpos := prefixMass_pos hP h hh.le
  cases b
  · simp only [bitProb, condOfDist, Bool.false_eq_true, ↓reduceIte]
    rw [eq_div_iff hpos.ne', sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul,
      prefixMass_split P h hh]
    ring
  · rfl

/-- The conditional probability `P(f | h)` given by the product rule along `condOfDist P` is the
ratio of prefix masses `P(hf) / P(h)`. -/
theorem condProb_condOfDist {T : ℕ} {P : Word T → ℝ} (hP : ∀ z, 0 < P z) (h f : List Bool)
    (hl : h.length + f.length ≤ T) :
    condProb (condOfDist P) h f = prefixMass P (h ++ f) / prefixMass P h := by
  induction f generalizing h with
  | nil =>
    have := prefixMass_pos hP h (by simpa using hl)
    simp [this.ne']
  | cons b f ih =>
    simp only [List.length_cons] at hl
    have h1 := prefixMass_pos hP h (by omega)
    have h2 := prefixMass_pos hP (h ++ [b]) (by simp; omega)
    rw [condProb_cons, ih (h ++ [b]) (by simp; omega), bitProb_condOfDist hP h (by omega)]
    simp only [List.append_assoc, List.singleton_append]
    field_simp

/-- `sec:model`: the conditionals of a fully supported distribution lie strictly between zero
and one. -/
theorem fullSupport_condOfDist {T : ℕ} {P : Word T → ℝ} (hP : ∀ z, 0 < P z) :
    FullSupport T (condOfDist P) := by
  intro h hh
  have h0 := prefixMass_pos hP h hh.le
  have h1 := prefixMass_pos hP (h ++ [true]) (by simp; omega)
  have h2 := prefixMass_pos hP (h ++ [false]) (by simp; omega)
  refine ⟨div_pos h1 h0, (div_lt_one h0).mpr ?_⟩
  rw [prefixMass_split P h hh]
  linarith

/-- `sec:model`: a fully supported distribution on `{0,1}^T` is the product of its own
next-bit conditionals. -/
theorem wordDist_condOfDist {T : ℕ} {P : Word T → ℝ} (hP : ∀ z, 0 < P z)
    (hP1 : ∑ z, P z = 1) : wordDist (condOfDist P) T = P := by
  funext z
  rw [wordDist, condProb_condOfDist hP [] z.toList (by simp), List.nil_append, prefixMass_word,
    prefixMass_nil, hP1, div_one]

/-! ### Next-bit models define fully supported distributions -/

theorem condProb_nonneg {p : NextBit} (h f : List Bool)
    (hp : ∀ g : List Bool, g.length < f.length → 0 ≤ p (h ++ g) ∧ p (h ++ g) ≤ 1) :
    0 ≤ condProb p h f := by
  induction f generalizing h with
  | nil => simp
  | cons b f ih =>
    rw [condProb_cons]
    have hb : 0 ≤ bitProb p h b := by
      have := hp [] (by simp)
      simp only [List.append_nil] at this
      cases b <;> simp [bitProb] <;> linarith
    refine mul_nonneg hb (ih (h ++ [b]) fun g hg => ?_)
    simpa using hp (b :: g) (by simpa using hg)

theorem condProb_pos {T : ℕ} {p : NextBit} (hp : FullSupport T p) (h f : List Bool)
    (hl : h.length + f.length ≤ T) : 0 < condProb p h f := by
  induction f generalizing h with
  | nil => simp
  | cons b f ih =>
    simp only [List.length_cons] at hl
    rw [condProb_cons]
    have hb : 0 < bitProb p h b := by
      have := hp h (by omega)
      cases b <;> simp [bitProb] <;> linarith
    exact mul_pos hb (ih (h ++ [b]) (by simp; omega))

/-- `sec:model`: a next-bit model with conditionals strictly between zero and one before time
`T` defines a fully supported distribution on `{0,1}^T` (it sums to one by `sum_condProb`). -/
theorem wordDist_pos {T : ℕ} {p : NextBit} (hp : FullSupport T p) (z : Word T) :
    0 < wordDist p T z :=
  condProb_pos hp [] z.toList (by simp)

/-- A next-bit model with values in `[0,1]` before time `T` defines a probability vector on
`{0,1}^T`. -/
theorem wordDist_isProbVec {T : ℕ} {p : NextBit}
    (hp : ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1) : IsProbVec (wordDist p T) :=
  ⟨fun z => condProb_nonneg [] z.toList fun g hg => by simpa using hp g (by simpa using hg),
    sum_condProb p T []⟩

/-- Full support gives conditionals in `[0,1]`, the hypothesis used by the bounds below. -/
theorem FullSupport.unitInterval {T : ℕ} {p : NextBit} (hp : FullSupport T p) :
    ∀ h : List Bool, h.length < T → 0 ≤ p h ∧ p h ≤ 1 :=
  fun h hh => ⟨(hp h hh).1.le, (hp h hh).2.le⟩

/-- `P_{:t}`: the mass of the words of `wordDist p T` with prefix `h` is `condProb p [] h`
(for every real-valued `p`). For `h : Word t` this says that `wordDist p t` is the law of the
first `t` bits of `wordDist p T`. -/
theorem prefixMass_wordDist (p : NextBit) {T : ℕ} (h : List Bool) (hh : h.length ≤ T) :
    prefixMass (wordDist p T) h = condProb p [] h := by
  unfold prefixMass
  rw [sum_filter_prefix h hh]
  simp only [wordDist, extendWord_toList, condProb_append, List.nil_append, ← mul_sum,
    sum_condProb, mul_one]

/-- The conditionals of `wordDist p T` are those of `p`, when `p` has full support. Together with
`wordDist_condOfDist`, next-bit models with full support and fully supported distributions on
`{0,1}^T` correspond one to one (on prefixes of length `< T`). -/
theorem condOfDist_wordDist {T : ℕ} {p : NextBit} (hp : FullSupport T p) (h : List Bool)
    (hh : h.length < T) : condOfDist (wordDist p T) h = p h := by
  have hpos := condProb_pos hp [] h (by simp; omega)
  rw [condOfDist, prefixMass_wordDist p _ (by simp; omega), prefixMass_wordDist p h hh.le,
    condProb_append]
  simp [bitProb]
  field_simp

end LowLogitRank.Coupling
