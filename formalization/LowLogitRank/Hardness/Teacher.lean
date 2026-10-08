import LowLogitRank.Hardness.Program

/-!
# The hard teacher of `sec:hardness`: definition and block structure

A teacher output is `Z = (X, A, Y, W)` with block lengths `n, L, 1, T - n - L - 1`. Positions are
0-based: input bits are at positions `0, …, n - 1`, copy `j` (`0 ≤ j < L`, the paper's copy
`j + 1`) is at position `n + j` and reads the input coordinate `j mod n` (the paper's
`i_{j+1} = 1 + (j mod n)`, 1-based), the label is at position `n + L`, and the padding follows.

The teacher is defined for a general scale `B` (`teacherLogit`, `teacher`); the paper's choice
`eq:hard-parameters` is `B = n log 2` (`hardTeacher`). The logit is defined on every prefix,
including prefixes with inconsistent copies.
-/

namespace LowLogitRank.Hardness

open Finset Matrix

section Blocks

variable (n L : ℕ)

/-- The input word `X` of a string: its first `n` bits (missing bits read as `0`). -/
def inputOf (z : List Bool) : Word n := List.Vector.ofFn fun i => z.getD i false

/-- The copy word `A` of a string: its bits `n, …, n + L - 1`. -/
def copyOf (z : List Bool) : Word L := List.Vector.ofFn fun j => z.getD (n + j) false

/-- The label `Y` of a string: its bit `n + L`. -/
def labelOf (z : List Bool) : Bool := z.getD (n + L) false

/-- The public read schedule, 0-based: copy `j` reads input coordinate `j mod n`. -/
def sched (j : ℕ) : ℕ := j % n

/-- The consistent copy word `a(x) = (x_{i_1}, …, x_{i_L})`. -/
def consistentWord (x : Word n) : Word L :=
  List.Vector.ofFn fun j => x.toList.getD (sched n j) false

/-- The mismatch count `C(X, A) = ∑_{j} 1{A_j ≠ X_{i_j}}`. -/
def mismatchCount (x : Word n) (a : Word L) : ℕ :=
  ∑ j : Fin L, if a.get j = x.toList.getD (sched n j) false then 0 else 1

variable (P : Program) (B : ℝ)

/-- The teacher's centered logit with scale `B` (`eq:hard-mask`), on every prefix `h`: zero at
input and padding positions, `B(2X_{i_j} - 1)` at copy position `j`, and `B(2C(X,A) + R(A))` at
the label position `|h| = n + L`. -/
noncomputable def teacherLogit (h : List Bool) : ℝ :=
  if h.length < n then 0
  else if h.length < n + L then
    B * (2 * bitValue (h.getD (sched n (h.length - n)) false) - 1)
  else if h.length = n + L then
    B * (2 * (mismatchCount n L (inputOf n h) (copyOf n L h) : ℝ) +
      P.response (copyOf n L h).toList)
  else 0

/-- The teacher with scale `B`: `P(1 | h) = σ(2 ℓ(h))`. -/
noncomputable def teacher : NextBit := ofLogit (teacherLogit n L P B)

/-- `B = n log 2` of `eq:hard-parameters`. -/
noncomputable def hardB : ℝ := n * Real.log 2

/-- `η = (1 + 2^{2n})⁻¹` of `eq:hard-parameters`. -/
noncomputable def hardEta : ℝ := (1 + 2 ^ (2 * n))⁻¹

/-- `T = 2n(L + 1)` of `eq:hard-parameters`. -/
def hardT : ℕ := 2 * n * (L + 1)

/-- The teacher `P_k` of `eq:hard-parameters` and `eq:hard-mask`. -/
noncomputable def hardTeacher : NextBit := teacher n L P (hardB n)

/-- The copy error `η = σ(-2B) = (1 + e^{2B})⁻¹` for a general scale `B`. -/
noncomputable def etaOf (B : ℝ) : ℝ := (1 + Real.exp (2 * B))⁻¹

/-- `eq:hard-consistency`: the hidden program computes `F` on consistent words,
`R(a(x)) = 2F(x) - 1`. This stands for Barrington's theorem applied to `F_k`. -/
def Consistent (F : Word n → Bool) : Prop :=
  ∀ x : Word n, P.response (consistentWord n L x).toList = 2 * bitValue (F x) - 1

end Blocks

/-! ### List lemmas -/

theorem getD_snoc_of_ne {h : List Bool} {b : Bool} {i : ℕ} (hi : i ≠ h.length) :
    (h ++ [b]).getD i false = h.getD i false := by
  rcases Nat.lt_or_gt_of_ne hi with hi | hi
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_self (h : List Bool) (b : Bool) : (h ++ [b]).getD h.length false = b := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem getD_append_of_lt {h f : List Bool} {i : ℕ} (hi : i < h.length) :
    (h ++ f).getD i false = h.getD i false :=
  List.getD_append _ _ _ _ hi

theorem getD_ofFn {k : ℕ} (g : Fin k → Bool) {i : ℕ} (hi : i < k) :
    (List.ofFn g).getD i false = g ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

theorem getD_take (z : List Bool) {k i : ℕ} (hi : i < k) :
    (z.take k).getD i false = z.getD i false := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_drop (z : List Bool) (k i : ℕ) : (z.drop k).getD i false = z.getD (k + i) false := by
  simp [List.getD_eq_getElem?_getD]

theorem list_ext_getD {l₁ l₂ : List Bool} (h : l₁.length = l₂.length)
    (h' : ∀ i < l₁.length, l₁.getD i false = l₂.getD i false) : l₁ = l₂ := by
  apply List.ext_getElem h
  intro i h1 h2
  have := h' i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this


/-! ### Basic properties of the blocks -/

section BlockLemmas

variable {n L : ℕ}

theorem sched_lt (hn : 0 < n) (j : ℕ) : sched n j < n := Nat.mod_lt _ hn

theorem inputOf_getD (z : List Bool) {i : ℕ} (hi : i < n) :
    (inputOf n z).toList.getD i false = z.getD i false := by
  rw [inputOf, List.Vector.toList_ofFn, getD_ofFn _ hi]

theorem copyOf_get (z : List Bool) (j : Fin L) : (copyOf n L z).get j = z.getD (n + j) false := by
  simp [copyOf, List.Vector.get_ofFn]

theorem consistentWord_get (x : Word n) (j : Fin L) :
    (consistentWord n L x).get j = x.toList.getD (sched n j) false := by
  simp [consistentWord, List.Vector.get_ofFn]

/-- The input word of `x ++ f` is `x`. -/
theorem inputOf_append (x : Word n) (f : List Bool) : inputOf n (x.toList ++ f) = x := by
  apply List.Vector.ext
  intro i
  rw [inputOf, List.Vector.get_ofFn, getD_append_of_lt (by simp),
    List.getD_eq_getElem _ _ (by simp), List.Vector.get_eq_get_toList]
  rfl

theorem word_getD (v : Word n) (i : Fin n) : v.toList.getD i false = v.get i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.Vector.get_eq_get_toList]
  rfl

theorem inputOf_toList (x : Word n) : inputOf n x.toList = x := by
  simpa using inputOf_append x []

theorem inputOf_toList_of_length (z : List Bool) (hz : z.length = n) :
    (inputOf n z).toList = z := by
  apply list_ext_getD
  · simp [hz]
  intro i hi
  simp only [List.Vector.toList_length] at hi
  exact inputOf_getD z hi

theorem mismatchCount_le (x : Word n) (a : Word L) : mismatchCount n L x a ≤ L := by
  unfold mismatchCount
  calc (∑ j : Fin L, if a.get j = x.toList.getD (sched n j) false then 0 else 1)
      ≤ ∑ _j : Fin L, 1 := Finset.sum_le_sum fun j _ => by split_ifs <;> simp
    _ = L := by simp

/-- `C(x, a) = 0` exactly when `a` is the consistent word `a(x)`. -/
theorem mismatchCount_eq_zero_iff (x : Word n) (a : Word L) :
    mismatchCount n L x a = 0 ↔ a = consistentWord n L x := by
  unfold mismatchCount
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    apply List.Vector.ext
    intro j
    have := h j (Finset.mem_univ _)
    rw [consistentWord_get]
    by_contra hne
    simp only [hne, ↓reduceIte, one_ne_zero] at this
  · rintro rfl j -
    simp [consistentWord_get]

theorem mismatchCount_consistent (x : Word n) :
    mismatchCount n L x (consistentWord n L x) = 0 :=
  (mismatchCount_eq_zero_iff x _).mpr rfl

/-- The first `n + L + 1` bits of a long string are its blocks `X`, `A`, `Y`. -/
theorem take_eq_blocks (z : List Bool) (hz : n + L + 1 ≤ z.length) :
    z.take (n + L + 1) = (inputOf n z).toList ++ (copyOf n L z).toList ++ [labelOf n L z] := by
  apply list_ext_getD
  · simp; omega
  intro i hi
  simp only [List.length_take] at hi
  rw [getD_take _ (by omega)]
  by_cases h1 : i < n
  · rw [getD_append_of_lt (by simp; omega), getD_append_of_lt (by simp; omega),
      inputOf_getD _ h1]
  by_cases h2 : i < n + L
  · rw [getD_append_of_lt (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
      copyOf, List.Vector.toList_ofFn, List.Vector.toList_length, getD_ofFn _ (by omega)]
    congr 1
    simp only
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_append, List.Vector.toList_length, labelOf]
    have : i = n + L := by omega
    subst this
    simp

/-- For a string with at least `n + L` bits, the copy word is `(z.drop n).take L`. -/
theorem copyOf_toList (z : List Bool) (hz : n + L ≤ z.length) :
    (copyOf n L z).toList = (z.drop n).take L := by
  apply list_ext_getD
  · simp; omega
  intro j hj
  simp only [List.Vector.toList_length] at hj
  rw [getD_take _ hj, getD_drop, copyOf, List.Vector.toList_ofFn, getD_ofFn _ hj]

end BlockLemmas

end LowLogitRank.Hardness
