import LowLogitRank.Spanner.Compression

/-!
# Feasibility on a fresh prefix (`lem:gls-feasibility`)

`LA : List Bool → ℝ` is the word-level oracle logit `𝓛_A` (any function on words works). At cut
`s`, the selected histories are `hsel s i`, `i : Fin d`, the future sets are `F s`, and the
extended future set is `F̃_s = F̂_s ∪ (Σ ∘ F̂_{s+1})`. The row of a history `h` at cut `s` is
`f ↦ LA (h ++ f)` on `F̃_s`. Cuts are numbered from `1` as in the paper; `y.getD (s-1) false` is
the paper's `y_s` and `y.take (s-1)` is `y_{1:s-1}`.
-/

namespace LowLogitRank.Spanner

open Finset

/-- The extended future set `F̃_s = F̂_s ∪ (Σ ∘ F̂_{s+1})`. -/
def ExtFut (F : ℕ → Set (List Bool)) (s : ℕ) : Set (List Bool) :=
  F s ∪ {f | ∃ a : Bool, ∃ g ∈ F (s + 1), f = a :: g}

/-- The row of the history `h` at cut `s`: `f ↦ LA (h ++ f)` for `f ∈ F̃_s`. -/
def rowAt (LA : List Bool → ℝ) (F : ℕ → Set (List Bool)) (s : ℕ) (h : List Bool) :
    ExtFut F s → ℝ := fun f => LA (h ++ f)

/-- The row of `h` at cut `s` is a combination of the selected rows with coefficients `c`. -/
def RowRep (LA : List Bool → ℝ) {d : ℕ} (hsel : ℕ → Fin d → List Bool)
    (F : ℕ → Set (List Bool)) (s : ℕ) (h : List Bool) (c : Fin d → ℝ) : Prop :=
  ∀ f ∈ ExtFut F s, LA (h ++ f) = ∑ i, c i * LA (hsel s i ++ f)

/-- The row of `h` at cut `s` has a representation by the selected rows with all coefficients in
`[-2, 2]`. -/
def Representable (LA : List Bool → ℝ) {d : ℕ} (hsel : ℕ → Fin d → List Bool)
    (F : ℕ → Set (List Bool)) (s : ℕ) (h : List Bool) : Prop :=
  ∃ c : Fin d → ℝ, (∀ i, |c i| ≤ 2) ∧ RowRep LA hsel F s h c

theorem representable_iff_mem_zonotope (LA : List Bool → ℝ) {d : ℕ}
    (hsel : ℕ → Fin d → List Bool) (F : ℕ → Set (List Bool)) (s : ℕ) (h : List Bool) :
    Representable LA hsel F s h ↔
      rowAt LA F s h ∈ zonotope 2 (fun i => rowAt LA F s (hsel s i)) := by
  constructor
  · rintro ⟨c, hc, hrep⟩
    refine ⟨c, hc, funext fun f => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowAt]
    exact (hrep f f.2).symm
  · rintro ⟨c, hc, hsum⟩
    refine ⟨c, hc, fun f hf => ?_⟩
    have := congrFun hsum ⟨f, hf⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rowAt] at this
    exact this.symm

/-- Feasibility of the reconstruction program `eq:our-gls-lp` at the prefix `y = y_{1:t}`, with
variables `c s : ℝ^d` (`1 ≤ s ≤ t`) and `Lh s` on `F̂_s` (`1 ≤ s ≤ t + 1`). -/
def LPFeasible (LA : List Bool → ℝ) {d : ℕ} [NeZero d] (hsel : ℕ → Fin d → List Bool)
    (F : ℕ → Set (List Bool)) (y : List Bool) (c : ℕ → Fin d → ℝ)
    (Lh : ℕ → List Bool → ℝ) : Prop :=
  (∀ s, 1 ≤ s → s ≤ y.length → ∀ f ∈ F s, Lh s f = ∑ i, c s i * LA (hsel s i ++ f)) ∧
  c 1 = Pi.single 0 1 ∧
  (∀ s, 1 ≤ s → s ≤ y.length → ∀ i, |c s i| ≤ 2) ∧
  (∀ s, 1 ≤ s → s ≤ y.length → ∀ f ∈ F (s + 1),
    Lh (s + 1) f = ∑ i, c s i * LA (hsel s i ++ (y.getD (s - 1) false :: f)))

theorem take_eq_take_pred_append (y : List Bool) {s : ℕ} (h1 : 1 ≤ s) (h2 : s ≤ y.length) :
    y.take s = y.take (s - 1) ++ [y.getD (s - 1) false] := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
  rfl

/-- `lem:gls-feasibility`, deterministic step. Suppose all selected histories at cut `1` are
empty, and for every `2 ≤ s ≤ t` the actual row of `y_{1:s-1}` is a combination of the selected
rows at cut `s` with coefficients in `[-2, 2]`. Then `eq:our-gls-lp` is feasible at `y`, with
`c_1 = e_1` and `L̂_s(f) = LA (y_{1:s-1} f)`. -/
theorem lpFeasible_of_reps (LA : List Bool → ℝ) {d : ℕ} [NeZero d]
    (hsel : ℕ → Fin d → List Bool) (F : ℕ → Set (List Bool)) (y : List Bool)
    (h1 : ∀ i, hsel 1 i = [])
    (hrep : ∀ s, 2 ≤ s → s ≤ y.length → Representable LA hsel F s (y.take (s - 1))) :
    ∃ c Lh, LPFeasible LA hsel F y c Lh := by
  classical
  let c : ℕ → Fin d → ℝ := fun s =>
    if hs : 2 ≤ s ∧ s ≤ y.length then (hrep s hs.1 hs.2).choose else Pi.single 0 1
  have hc1 : c 1 = Pi.single 0 1 := by simp [c]
  -- every cut `1 ≤ s ≤ t` has a bounded representation of its actual row
  have hall : ∀ s, 1 ≤ s → s ≤ y.length →
      (∀ i, |c s i| ≤ 2) ∧ RowRep LA hsel F s (y.take (s - 1)) (c s) := by
    intro s hs1 hst
    rcases Nat.lt_or_ge s 2 with hs | hs
    · obtain rfl : s = 1 := by omega
      rw [hc1]
      refine ⟨fun i => ?_, fun f _ => ?_⟩
      · rw [Pi.single_apply]; split_ifs <;> norm_num
      · simp [Pi.single_apply, h1]
    · have hdef : c s = (hrep s hs hst).choose := by simp [c, hs, hst]
      rw [hdef]
      exact (hrep s hs hst).choose_spec
  refine ⟨c, fun s f => LA (y.take (s - 1) ++ f), ?_, hc1, fun s hs1 hst => (hall s hs1 hst).1, ?_⟩
  · intro s hs1 hst f hf
    exact (hall s hs1 hst).2 f (Or.inl hf)
  · intro s hs1 hst f hf
    simp only [Nat.add_sub_cancel]
    rw [take_eq_take_pred_append y hs1 hst, List.append_assoc, List.singleton_append]
    exact (hall s hs1 hst).2 _ (Or.inr ⟨_, f, hf, rfl⟩)

/-! ### Prefix marginals and the probability bound -/

theorem bitProb_nonneg {p : NextBit} {h : List Bool} (hp : 0 ≤ p h ∧ p h ≤ 1) (b : Bool) :
    0 ≤ bitProb p h b := by
  cases b <;> simp [bitProb] <;> linarith [hp.1, hp.2]

theorem condProb_nonneg (p : NextBit) (t : ℕ)
    (hp : ∀ h : List Bool, h.length < t → 0 ≤ p h ∧ p h ≤ 1) :
    ∀ (f h : List Bool), h.length + f.length ≤ t → 0 ≤ condProb p h f := by
  intro f
  induction f with
  | nil => intro h _; simp
  | cons b f ih =>
    intro h hl
    simp only [List.length_cons] at hl
    rw [condProb_cons]
    exact mul_nonneg (bitProb_nonneg (hp h (by omega)) b) (ih _ (by simp; omega))

/-- The prefix law `P_{1:k}` on `{0,1}^k`. -/
def prefixLaw (p : NextBit) (k : ℕ) : Word k → ℝ := fun z => condProb p [] z.toList

theorem isProb_prefixLaw (p : NextBit) {t k : ℕ} (hk : k ≤ t)
    (hp : ∀ h : List Bool, h.length < t → 0 ≤ p h ∧ p h ≤ 1) : IsProb (prefixLaw p k) :=
  ⟨fun z => condProb_nonneg p t hp _ [] (by simp; omega), sum_condProb p k []⟩

/-- Marginalization: averaging a function of the first `k` symbols of `y ∼ P_{1:t}` is averaging
it under `P_{1:k}`. -/
theorem sum_condProb_take (p : NextBit) :
    ∀ (k t : ℕ) (h : List Bool) (G : List Bool → ℝ), k ≤ t →
      ∑ y : Word t, condProb p h y.toList * G (y.toList.take k) =
        ∑ z : Word k, condProb p h z.toList * G z.toList := by
  intro k
  induction k with
  | zero =>
    intro t h G _
    have hz : ∀ z : Word 0, z.toList = [] := fun z => List.length_eq_zero_iff.mp z.toList_length
    simp only [List.take_zero, hz, ← Finset.sum_mul]
    rw [sum_condProb]
    simp
  | succ k ih =>
    intro t h G hkt
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [sum_word_succ, sum_word_succ]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [List.Vector.toList_cons, condProb_cons, List.take_succ_cons, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    exact ih t (h ++ [b]) (fun z => G (b :: z)) (by omega)

theorem wprob_eq_sum_mul {α : Type*} [Fintype α] (μ : α → ℝ) (E : Set α) :
    wprob μ E = ∑ a, μ a * E.indicator (fun _ => (1 : ℝ)) a := by
  classical
  unfold wprob
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a ∈ E <;> simp [ha]

theorem wprob_prefix_take (p : NextBit) {k t : ℕ} (hkt : k ≤ t) (A : Set (List Bool)) :
    wprob (prefixLaw p t) {y | y.toList.take k ∈ A} = wprob (prefixLaw p k) {z | z.toList ∈ A} := by
  classical
  rw [wprob_eq_sum_mul, wprob_eq_sum_mul]
  have h := sum_condProb_take p k t [] (A.indicator fun _ => 1) hkt
  convert h using 2 with y _ z _
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq]; rfl
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq]; rfl

/-- `lem:gls-feasibility`. Let `p` be a next-bit model with conditionals in `[0,1]` before time
`t`, so that `P_{1:k}` is the prefix law. Suppose all selected histories at cut `1` are empty and,
for every `2 ≤ s ≤ t`, the selected rows at cut `s` are an `(η, 2)`-distributional spanner of the
law of the row of `y_{1:s-1} ∼ P_{1:s-1}`. Then a fresh prefix `y_{1:t} ∼ P_{1:t}` has a feasible
reconstruction program `eq:our-gls-lp` with probability at least `1 - t η`. -/
theorem gls_feasibility (LA : List Bool → ℝ) {d : ℕ} [NeZero d]
    (hsel : ℕ → Fin d → List Bool) (F : ℕ → Set (List Bool)) (p : NextBit) (t : ℕ)
    (hp : ∀ h : List Bool, h.length < t → 0 ≤ p h ∧ p h ≤ 1) {η : ℝ} (hη : 0 ≤ η)
    (h1 : ∀ i, hsel 1 i = [])
    (hspan : ∀ s, 2 ≤ s → s ≤ t →
      IsDistSpanner η 2 (prefixLaw p (s - 1)) (fun h => rowAt LA F s h.toList)
        (fun i => rowAt LA F s (hsel s i))) :
    1 - t * η ≤ wprob (prefixLaw p t) {y | ∃ c Lh, LPFeasible LA hsel F y.toList c Lh} := by
  classical
  have hPt := isProb_prefixLaw p le_rfl hp
  set B : ℕ → Set (Word t) := fun s =>
    {y | y.toList.take (s - 1) ∈ {l | ¬ Representable LA hsel F s l}}
  -- each cut fails with probability at most `η`
  have hB : ∀ s ∈ Finset.Icc 2 t, wprob (prefixLaw p t) (B s) ≤ η := by
    intro s hs
    obtain ⟨hs2, hst⟩ := Finset.mem_Icc.1 hs
    rw [wprob_prefix_take p (by omega : s - 1 ≤ t)]
    have hPs := isProb_prefixLaw p (by omega : s - 1 ≤ t) hp
    have hc : {z : Word (s - 1) | z.toList ∈ {l | ¬ Representable LA hsel F s l}} =
        {z : Word (s - 1) | Representable LA hsel F s z.toList}ᶜ := by ext; simp
    rw [hc, wprob_compl hPs]
    have hsp := hspan s hs2 hst
    unfold IsDistSpanner at hsp
    have : {z : Word (s - 1) | Representable LA hsel F s z.toList} =
        (fun h : Word (s - 1) => rowAt LA F s h.toList) ⁻¹'
          zonotope 2 (fun i => rowAt LA F s (hsel s i)) := by
      ext z; simp [representable_iff_mem_zonotope]
    rw [this]
    linarith
  -- off the union of the failure events the program is feasible
  have hsub : (⋃ s ∈ Finset.Icc 2 t, B s)ᶜ ⊆
      {y : Word t | ∃ c Lh, LPFeasible LA hsel F y.toList c Lh} := by
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy
    refine lpFeasible_of_reps LA hsel F y.toList h1 fun s hs2 hst => ?_
    rw [List.Vector.toList_length] at hst
    have := hy s (Finset.mem_Icc.2 ⟨hs2, hst⟩)
    simp only [B, Set.mem_ofPred_eq, not_not] at this
    exact this
  have hU := wprob_biUnion_le_card_mul hPt.nonneg (Finset.Icc 2 t) B hB
  have hcard : ((Finset.Icc 2 t).card : ℝ) * η ≤ t * η := by
    refine mul_le_mul_of_nonneg_right ?_ hη
    rw [Nat.card_Icc]; exact_mod_cast (by omega : t + 1 - 2 ≤ t)
  have := wprob_mono hPt.nonneg hsub
  rw [wprob_compl hPt] at this
  linarith

end LowLogitRank.Spanner
