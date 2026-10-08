import LowLogitRank.Hardness.Simulation

/-!
# The fresh-label event of `thm:reduction` and `TV(P_k, D_k)`

All masses are computed from `wordDist (teacher …) T`, a function on `{0,1}^T`; the padding
block is summed out.
-/

namespace LowLogitRank.Hardness

open Finset

variable {n L : ℕ}

section Event

variable (n L) in
/-- The event `E_S = {A = a(X), Y = F(X), X ∉ S}` of the proof of `thm:reduction`. -/
def goodEvent (F : Word n → Bool) (S : Finset (Word n)) (z : List Bool) : Prop :=
  copyOf n L z = consistentWord n L (inputOf n z) ∧ labelOf n L z = F (inputOf n z) ∧
    inputOf n z ∉ S

instance (F : Word n → Bool) (S : Finset (Word n)) (z : List Bool) :
    Decidable (goodEvent n L F S z) := by
  unfold goodEvent; infer_instance

variable (n L) in
/-- The good prefix `x a(x) F(x)` of length `n + L + 1`. -/
def goodPrefix (F : Word n → Bool) (x : Word n) : List Bool :=
  x.toList ++ (consistentWord n L x).toList ++ [F x]

theorem goodPrefix_length (F : Word n → Bool) (x : Word n) :
    (goodPrefix n L F x).length = n + L + 1 := by
  simp [goodPrefix, add_assoc]

theorem goodPrefix_prefix_iff (F : Word n → Bool) (x : Word n) (z : List Bool)
    (hz : n + L + 1 ≤ z.length) :
    goodPrefix n L F x <+: z ↔
      inputOf n z = x ∧ copyOf n L z = consistentWord n L x ∧ labelOf n L z = F x := by
  rw [List.prefix_iff_eq_take, goodPrefix_length, take_eq_blocks z hz, goodPrefix]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    obtain ⟨h3, h4⟩ := List.append_inj h1 (by simp)
    refine ⟨(List.Vector.toList_injective h3).symm, (List.Vector.toList_injective h4).symm, ?_⟩
    simpa using h2.symm
  · rintro ⟨rfl, h2, h3⟩
    rw [h2, h3]

/-- The indicator of `E_S` is a sum of indicators of the disjoint good prefixes. -/
theorem goodEvent_indicator (F : Word n → Bool) (S : Finset (Word n)) (z : List Bool)
    (hz : n + L + 1 ≤ z.length) (c : ℝ) :
    (if goodEvent n L F S z then c else 0) =
      ∑ x : Word n, if x ∉ S ∧ goodPrefix n L F x <+: z then c else 0 := by
  rw [Finset.sum_eq_single (inputOf n z)]
  · congr 1
    rw [goodPrefix_prefix_iff F _ z hz, goodEvent]
    simp only [true_and]
    apply propext
    tauto
  · intro x _ hx
    rw [ite_eq_right_iff]
    rintro ⟨_, hp⟩
    exact absurd ((goodPrefix_prefix_iff F _ z hz).mp hp).1.symm hx
  · simp

end Event

/-! ### Conditional probabilities of the blocks -/

section Blocks

variable (P : Program) (B : ℝ)

/-- The first `k` consistent copies of `x`. -/
def copyPrefix (n : ℕ) (x : Word n) (k : ℕ) : List Bool :=
  (List.range k).map fun j => x.toList.getD (sched n j) false

theorem consistentWord_toList (x : Word n) :
    (consistentWord n L x).toList = copyPrefix n x L := by
  apply list_ext_getD
  · simp [copyPrefix]
  intro j hj
  simp only [List.Vector.toList_length] at hj
  rw [consistentWord, List.Vector.toList_ofFn, getD_ofFn _ hj, copyPrefix,
    List.getD_eq_getElem (List.map _ (List.range L)) false (by simpa using hj),
    List.getElem_map, List.getElem_range]

/-- The input block is uniform: `P(x) = 2^{-n}`. -/
theorem condProb_input (x : Word n) :
    condProb (teacher n L P B) [] x.toList = (1 / 2) ^ n := by
  rw [condProb_of_fair _ _ _ (fun g _ hg => teacher_fair P B g (Or.inl (by simpa using hg))),
    List.Vector.toList_length]

/-- Consistent copies have conditional probability `(1-η)^k`. -/
theorem condProb_copyPrefix (hn : 0 < n) (x : Word n) (k : ℕ) (hk : k ≤ L) :
    condProb (teacher n L P B) x.toList (copyPrefix n x k) = (1 - etaOf B) ^ k := by
  induction k with
  | zero => simp [copyPrefix]
  | succ k ih =>
    rw [copyPrefix, List.range_succ, List.map_append, condProb_append, ← copyPrefix,
      ih (by omega)]
    simp only [List.map_cons, List.map_nil, condProb_cons, condProb_nil, mul_one]
    have hlen : (x.toList ++ copyPrefix n x k).length = n + k := by simp [copyPrefix]
    have hbit : (x.toList ++ copyPrefix n x k).getD
        (sched n ((x.toList ++ copyPrefix n x k).length - n)) false =
        x.toList.getD (sched n k) false := by
      rw [hlen, show n + k - n = k by omega, getD_append_of_lt (by simpa using sched_lt hn k)]
    have hl1 : n ≤ (x.toList ++ copyPrefix n x k).length := by omega
    have hl2 : (x.toList ++ copyPrefix n x k).length < n + L := by omega
    have := teacher_copy P B (x.toList ++ copyPrefix n x k) hl1 hl2
    rw [hbit] at this
    rw [this, pow_succ]

theorem copyOf_append (x : Word n) (a : Word L) (f : List Bool) :
    copyOf n L (x.toList ++ a.toList ++ f) = a := by
  apply List.Vector.ext
  intro j
  rw [copyOf_get, List.append_assoc, List.getD_append_right _ _ _ _ (by simp),
    List.Vector.toList_length, show n + (j : ℕ) - n = j by omega,
    getD_append_of_lt (by simp), List.getD_eq_getElem _ _ (by simp),
    List.Vector.get_eq_get_toList]
  rfl

/-- The good prefix has mass `2^{-n} (1-η)^{L+1}`. -/
theorem condProb_goodPrefix (hn : 0 < n) {F : Word n → Bool} (hcons : Consistent n L P F)
    (x : Word n) :
    condProb (teacher n L P B) [] (goodPrefix n L F x) = (1 / 2) ^ n * (1 - etaOf B) ^ (L + 1) := by
  rw [goodPrefix, condProb_append, condProb_append, List.nil_append, condProb_input,
    consistentWord_toList, condProb_copyPrefix P B hn x L le_rfl, ← consistentWord_toList]
  simp only [condProb_cons, condProb_nil, mul_one, List.nil_append]
  have hlab := teacher_label_consistent P B hcons (x.toList ++ (consistentWord n L x).toList)
    (by simp) (by rw [inputOf_append, ← List.append_nil (_ ++ _), copyOf_append,
      mismatchCount_consistent])
  rw [inputOf_append] at hlab
  rw [hlab, pow_succ]
  ring

end Blocks

/-! ### The event mass in the proof of `thm:reduction` -/

section Mass

variable (P : Program) (B : ℝ)

theorem sum_ite_not_mem (S : Finset (Word n)) (c : ℝ) :
    ∑ x : Word n, (if x ∉ S then c else 0) = (2 ^ n - S.card) * c := by
  have h1 : ∀ x : Word n, (if x ∉ S then c else 0) = c - (if x ∈ S then c else 0) := by
    intro x; split_ifs <;> simp_all
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_vector,
    Fintype.card_bool, nsmul_eq_mul, Finset.sum_ite_mem, Finset.univ_inter]
  push_cast
  ring

theorem hardT_ge (hn : 1 ≤ n) : n + L + 1 ≤ hardT n L := by
  unfold hardT; nlinarith

/-- Proof of `thm:reduction`: under `eq:hard-consistency`, for every `S ⊆ {0,1}^n` the event
`E_S = {A = a(X), Y = F(X), X ∉ S}` has teacher mass `(1-η)^{L+1} (1 - |S|/2^n)`, for every
length `T ≥ n + L + 1`. -/
theorem teacher_eventMass (hn : 0 < n) {F : Word n → Bool} (hcons : Consistent n L P F)
    (T : ℕ) (hT : n + L + 1 ≤ T) (S : Finset (Word n)) :
    ∑ z : Word T, (if goodEvent n L F S z.toList then wordDist (teacher n L P B) T z else 0) =
      (1 - etaOf B) ^ (L + 1) * (1 - S.card / 2 ^ n) := by
  have hz : ∀ z : Word T, n + L + 1 ≤ z.toList.length := fun z => by simp [hT]
  simp_rw [fun z : Word T => goodEvent_indicator F S z.toList (hz z)
    (wordDist (teacher n L P B) T z)]
  rw [Finset.sum_comm]
  have key : ∀ x : Word n, ∑ z : Word T, (if x ∉ S ∧ goodPrefix n L F x <+: z.toList then
      wordDist (teacher n L P B) T z else 0) =
      if x ∉ S then (1 / 2) ^ n * (1 - etaOf B) ^ (L + 1) else 0 := by
    intro x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp only [hx, not_false_eq_true, true_and, ↓reduceIte, wordDist]
      rw [sum_condProb_prefix _ _ _ _ (by rw [goodPrefix_length]; exact hT),
        condProb_goodPrefix P B hn hcons]
  rw [Finset.sum_congr rfl (fun x _ => key x), sum_ite_not_mem, one_div, inv_pow]
  have : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

/-- The event mass for the parameters of `eq:hard-parameters`:
`P_k(E_S) = (1-η)^{L+1} (1 - |S|/2^n)` with `η = (1 + 2^{2n})⁻¹` and `T = 2n(L+1)`. -/
theorem hardTeacher_eventMass (hn : 1 ≤ n) {F : Word n → Bool} (hcons : Consistent n L P F)
    (S : Finset (Word n)) :
    ∑ z : Word (hardT n L),
        (if goodEvent n L F S z.toList then wordDist (hardTeacher n L P) (hardT n L) z else 0) =
      (1 - hardEta n) ^ (L + 1) * (1 - S.card / 2 ^ n) := by
  rw [← etaOf_hardB]
  exact teacher_eventMass P _ hn hcons _ (hardT_ge hn) S

end Mass

/-! ### `TV(P_k, D_k)` -/

section IdealTV

variable (P : Program) (B : ℝ)

variable (n L) in
/-- The deterministic-copy distribution `D_k` on `{0,1}^T`: uniform `X`, `A = a(X)`,
`Y = F(X)`, and fair padding. -/
noncomputable def idealDist (F : Word n → Bool) (T : ℕ) (z : Word T) : ℝ :=
  if copyOf n L z.toList = consistentWord n L (inputOf n z.toList) ∧
      labelOf n L z.toList = F (inputOf n z.toList) then
    (1 / 2) ^ n * (1 / 2) ^ (T - n - L - 1)
  else 0

theorem teacher_mem_unit (h : List Bool) :
    0 ≤ teacher n L P B h ∧ teacher n L P B h ≤ 1 :=
  ⟨(sigmoid_pos _).le, (sigmoid_lt_one _).le⟩

/-- On a good word the teacher mass is `(1-η)^{L+1}` times the `D_k` mass. -/
theorem wordDist_good (hn : 0 < n) {F : Word n → Bool} (hcons : Consistent n L P F) (T : ℕ)
    (hT : n + L + 1 ≤ T) (z : Word T) (hz : goodEvent n L F ∅ z.toList) :
    wordDist (teacher n L P B) T z =
      (1 - etaOf B) ^ (L + 1) * ((1 / 2) ^ n * (1 / 2) ^ (T - n - L - 1)) := by
  have hlen : n + L + 1 ≤ z.toList.length := by simp [hT]
  have hpre : z.toList.take (n + L + 1) = goodPrefix n L F (inputOf n z.toList) := by
    rw [take_eq_blocks _ hlen, goodPrefix, hz.1, hz.2.1]
  rw [wordDist, ← List.take_append_drop (n + L + 1) z.toList, condProb_append, List.nil_append,
    hpre, condProb_goodPrefix P B hn hcons, condProb_of_fair]
  · simp only [List.length_drop, List.Vector.toList_length]
    rw [show T - (n + L + 1) = T - n - L - 1 by omega]
    ring
  · intro g hg _
    rw [goodPrefix_length] at hg
    exact teacher_fair P B g (Or.inr (by omega))

/-- `TV(P_k, D_k) = 1 - (1-η)^{L+1}` (display after `thm:reduction`), for every length
`T ≥ n + L + 1`, under `eq:hard-consistency`. -/
theorem tv_teacher_ideal (hn : 0 < n) {F : Word n → Bool} (hcons : Consistent n L P F) (T : ℕ)
    (hT : n + L + 1 ≤ T) :
    tv (wordDist (teacher n L P B) T) (idealDist n L F T) = 1 - (1 - etaOf B) ^ (L + 1) := by
  set u := (1 - etaOf B) ^ (L + 1) with hu
  set c : ℝ := (1 / 2) ^ n * (1 / 2) ^ (T - n - L - 1) with hc
  set Pz := wordDist (teacher n L P B) T
  have hη0 := (etaOf_pos B).le
  have hη1 := etaOf_lt_one B
  have hu0 : 0 < u := pow_pos (by linarith) _
  have hu1 : u ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hc0 : 0 ≤ c := by positivity
  have hD : ∀ z, idealDist n L F T z = if goodEvent n L F ∅ z.toList then c else 0 := by
    intro z; simp [idealDist, goodEvent, hc]
  have hPnn : ∀ z, 0 ≤ Pz z := fun z => condProb_nonneg _ (teacher_mem_unit P B) _ _
  have hmass : ∑ z : Word T, (if goodEvent n L F ∅ z.toList then Pz z else 0) = u := by
    simpa using teacher_eventMass P B hn hcons T hT ∅
  have hsumD : ∑ z : Word T, (if goodEvent n L F ∅ z.toList then c else 0) = 1 := by
    have : ∑ z : Word T, (if goodEvent n L F ∅ z.toList then Pz z else 0) =
        u * ∑ z : Word T, (if goodEvent n L F ∅ z.toList then c else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs with hz
      · exact wordDist_good P B hn hcons T hT z hz
      · simp
    rw [hmass] at this
    field_simp at this
    linarith
  have hsumP : ∑ z : Word T, Pz z = 1 := sum_condProb _ _ _
  have habs : ∀ z, |Pz z - idealDist n L F T z| =
      (if goodEvent n L F ∅ z.toList then c else 0) -
        2 * (if goodEvent n L F ∅ z.toList then Pz z else 0) + Pz z := by
    intro z
    rw [hD]
    by_cases hz : goodEvent n L F ∅ z.toList
    · simp only [hz, ↓reduceIte]
      rw [show Pz z = u * c from wordDist_good P B hn hcons T hT z hz,
        abs_of_nonpos (by nlinarith)]
      ring
    · simp only [hz, ↓reduceIte, sub_zero, mul_zero, abs_of_nonneg (hPnn z)]
      ring
  rw [tv, Finset.sum_congr rfl (fun z _ => habs z), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hsumD, hmass, hsumP]
  ring

/-- Bernoulli: `1 - (1-η)^k ≤ kη` (for `η ≤ 2`). -/
theorem one_sub_pow_le {η : ℝ} (hη : η ≤ 2) (k : ℕ) :
    1 - (1 - η) ^ k ≤ k * η := by
  have := one_add_mul_le_pow (a := -η) (by linarith) k
  rw [← sub_eq_add_neg] at this
  linarith

/-- The display after `thm:reduction` for the parameters of `eq:hard-parameters`:
`TV(P_k, D_k) = 1 - (1-η)^{L+1} ≤ (L+1)η`. -/
theorem tv_hardTeacher_ideal (hn : 1 ≤ n) {F : Word n → Bool} (hcons : Consistent n L P F) :
    tv (wordDist (hardTeacher n L P) (hardT n L)) (idealDist n L F (hardT n L)) =
        1 - (1 - hardEta n) ^ (L + 1) ∧
      1 - (1 - hardEta n) ^ (L + 1) ≤ (L + 1) * hardEta n := by
  refine ⟨?_, ?_⟩
  · rw [← etaOf_hardB]
    exact tv_teacher_ideal P _ hn hcons _ (hardT_ge hn)
  · have h1 : hardEta n ≤ 1 := by rw [← etaOf_hardB]; exact (etaOf_lt_one _).le
    have := one_sub_pow_le (by linarith) (L + 1)
    push_cast at this
    exact this

end IdealTV

end LowLogitRank.Hardness
