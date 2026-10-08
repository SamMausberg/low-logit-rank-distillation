import LowLogitRank.Hardness.Teacher

/-!
# The linear state of `lem:hard-teacher`

The column state is `s(h) = (1, X_1, …, X_n, C, v_1, …, v_5)`, indexed by
`Coord n = Unit ⊕ Fin n ⊕ Unit ⊕ Fin 5` (`n + 7` coordinates). Unfilled input coordinates are
zero, `C = 0` and `v = v₀` before the first copy. Writing an input bit uses the constant
coordinate, a copy updates `C ← C + b + (1 - 2b) X_{i_j}` and `v ← M_{j,b} v` (`eq:counter`), and
the label and padding positions keep the state.
-/

namespace LowLogitRank.Hardness

open Finset Matrix

/-- Coordinates of the state `s(h) = (1, X_1, …, X_n, C, v_1, …, v_5)`. -/
abbrev Coord (n : ℕ) := Unit ⊕ Fin n ⊕ Unit ⊕ Fin 5

theorem card_coord (n : ℕ) : Fintype.card (Coord n) = n + 7 := by
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

section State

variable (n L : ℕ) (P : Program) (B : ℝ)

/-- The number of copy positions filled by the prefix `h`. -/
def filled (h : List Bool) : ℕ := min (h.length - n) L

/-- The counter `C` of a prefix: the number of mismatches among its filled copy positions. -/
def counter (h : List Bool) : ℕ :=
  ∑ j ∈ range (filled n L h), if h.getD (n + j) false = h.getD (sched n j) false then 0 else 1

/-- The program state `v` of a prefix: `M_{j,a_j} ⋯ M_{1,a_1} v₀` over its filled copies. -/
def progState (h : List Bool) : Fin 5 → ℝ := P.prod ((h.drop n).take L) *ᵥ P.v0

/-- The state vector `s(h) = (1, X_1, …, X_n, C, v_1, …, v_5)`. -/
def state (h : List Bool) : Coord n → ℝ
  | .inl _ => 1
  | .inr (.inl i) => bitValue (h.getD i false)
  | .inr (.inr (.inl _)) => counter n L h
  | .inr (.inr (.inr k)) => progState n L P h k

/-- Reading the input coordinate `i` of a state (zero if `i ≥ n`). -/
def readInput (s : Coord n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then s (.inr (.inl ⟨i, hi⟩)) else 0

/-- The program part `(v_1, …, v_5)` of a state. -/
def progPart (s : Coord n → ℝ) : Fin 5 → ℝ := fun k => s (.inr (.inr (.inr k)))

/-- The update `s ↦ A_{t,b} s` at position `t` after the bit `b`. -/
def stepFun (t : ℕ) (b : Bool) (s : Coord n → ℝ) : Coord n → ℝ
  | .inl u => s (.inl u)
  | .inr (.inl i) => if i.val = t then bitValue b * s (.inl ()) else s (.inr (.inl i))
  | .inr (.inr (.inl u)) =>
      if n ≤ t ∧ t < n + L then
        s (.inr (.inr (.inl u))) + bitValue b * s (.inl ()) +
          (1 - 2 * bitValue b) * readInput n s (sched n (t - n))
      else s (.inr (.inr (.inl u)))
  | .inr (.inr (.inr k)) =>
      if n ≤ t ∧ t < n + L then (P.instr (t - n) b *ᵥ progPart n s) k
      else s (.inr (.inr (.inr k)))

/-- The linear update `A_{t,b}`. -/
def step (t : ℕ) (b : Bool) : (Coord n → ℝ) →ₗ[ℝ] (Coord n → ℝ) where
  toFun := stepFun n L P t b
  map_add' s₁ s₂ := by
    funext c
    rcases c with u | i | u | k <;>
      simp only [stepFun, readInput, progPart, Pi.add_apply, mulVec, dotProduct] <;>
      split_ifs <;> (try simp only [mul_add, Finset.sum_add_distrib]) <;> ring
  map_smul' a s := by
    funext c
    rcases c with u | i | u | k <;>
      simp only [stepFun, readInput, progPart, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
        RingHom.id_apply] <;>
      split_ifs <;> (try simp only [mul_left_comm _ a, ← Finset.mul_sum]) <;> ring

/-- The readout `w_t` of the logit at position `t`. -/
def readFun (t : ℕ) (s : Coord n → ℝ) : ℝ :=
  if t < n then 0
  else if t < n + L then B * (2 * readInput n s (sched n (t - n)) - s (.inl ()))
  else if t = n + L then B * (2 * s (.inr (.inr (.inl ()))) + P.sign ⬝ᵥ progPart n s)
  else 0

/-- The linear readout `w_t`. -/
def read (t : ℕ) : (Coord n → ℝ) →ₗ[ℝ] ℝ where
  toFun := readFun n L P B t
  map_add' s₁ s₂ := by
    simp only [readFun, readInput, progPart, Pi.add_apply, dotProduct]
    split_ifs <;> (try simp only [mul_add, Finset.sum_add_distrib]) <;> ring
  map_smul' a s := by
    simp only [readFun, readInput, progPart, Pi.smul_apply, smul_eq_mul, dotProduct,
      RingHom.id_apply]
    split_ifs <;> (try simp only [mul_left_comm _ a, ← Finset.mul_sum]) <;> ring

end State

/-! ### The state recursion `s(hb) = A_{t,b} s(h)` and the readout `ℓ(h) = w_tᵀ s(h)` -/

section Recursion

variable {n L : ℕ} (P : Program) (B : ℝ)

/-- The counter increment of `eq:counter` is the mismatch indicator: `b + (1 - 2b)x = 1{b ≠ x}`. -/
theorem mismatch_increment (x b : Bool) :
    bitValue b + (1 - 2 * bitValue b) * bitValue x = if b = x then 0 else 1 := by
  cases x <;> cases b <;> norm_num [bitValue]

/-- The linear update of `eq:counter` on a state whose constant coordinate is one. -/
theorem counter_update (C : ℝ) (x b : Bool) :
    C + bitValue b * 1 + (1 - 2 * bitValue b) * bitValue x = C + if b = x then 0 else 1 := by
  rw [← mismatch_increment]
  ring

theorem filled_snoc (h : List Bool) (b : Bool) :
    filled n L (h ++ [b]) =
      if n ≤ h.length ∧ h.length < n + L then filled n L h + 1 else filled n L h := by
  simp only [filled, List.length_append, List.length_singleton]
  split_ifs <;> omega

theorem counter_snoc (hn : 0 < n) (h : List Bool) (b : Bool) :
    counter n L (h ++ [b]) =
      if n ≤ h.length ∧ h.length < n + L then
        counter n L h + (if b = h.getD (sched n (h.length - n)) false then 0 else 1)
      else counter n L h := by
  have hterm : ∀ j ∈ range (filled n L h),
      (if (h ++ [b]).getD (n + j) false = (h ++ [b]).getD (sched n j) false then 0 else 1) =
        (if h.getD (n + j) false = h.getD (sched n j) false then 0 else 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : n + j < h.length := by simp only [filled] at hj; omega
    have h2 : sched n j < h.length := by have := sched_lt hn j; omega
    rw [getD_append_of_lt h1, getD_append_of_lt h2]
  unfold counter
  rw [filled_snoc]
  by_cases hc : n ≤ h.length ∧ h.length < n + L
  · rw [ite_eq_left hc, ite_eq_left hc, Finset.sum_range_succ, Finset.sum_congr rfl hterm]
    have hf : filled n L h = h.length - n := by simp only [filled]; omega
    have hs : sched n (h.length - n) < h.length := by
      have := sched_lt hn (h.length - n); omega
    rw [hf, show n + (h.length - n) = h.length by omega, getD_snoc_self,
      getD_append_of_lt hs]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact Finset.sum_congr rfl hterm

theorem progState_snoc (h : List Bool) (b : Bool) :
    progState n L P (h ++ [b]) =
      if n ≤ h.length ∧ h.length < n + L then P.instr (h.length - n) b *ᵥ progState n L P h
      else progState n L P h := by
  unfold progState
  split_ifs with hc
  · rw [List.drop_append_of_le_length hc.1, List.take_of_length_le (by simp; omega),
      List.take_of_length_le (by simp; omega), Program.prod_append_singleton, ← mulVec_mulVec,
      List.length_drop]
  · by_cases h1 : h.length < n
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by omega)]
    · rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by simp; omega)]

theorem readInput_state (h : List Bool) {i : ℕ} (hi : i < n) :
    readInput n (state n L P h) i = bitValue (h.getD i false) := by
  simp [readInput, hi, state]

theorem progPart_state (h : List Bool) : progPart n (state n L P h) = progState n L P h := rfl

/-- `s(hb) = A_{t,b} s(h)` with `t = |h|`. -/
theorem state_snoc (hn : 0 < n) (h : List Bool) (b : Bool) :
    state n L P (h ++ [b]) = step n L P h.length b (state n L P h) := by
  funext c
  change state n L P (h ++ [b]) c = stepFun n L P h.length b (state n L P h) c
  rcases c with u | i | u | k
  · rfl
  · simp only [state, stepFun]
    split_ifs with hi
    · rw [hi, getD_snoc_self, mul_one]
    · rw [getD_snoc_of_ne hi]
  · simp only [state, stepFun]
    rw [counter_snoc hn]
    by_cases hc : n ≤ h.length ∧ h.length < n + L
    · rw [ite_eq_left hc, ite_eq_left hc, readInput_state P h (sched_lt hn _), Nat.cast_add,
        counter_update, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
    · rw [ite_eq_right hc, ite_eq_right hc]
  · simp only [state, stepFun]
    rw [progState_snoc, progPart_state]
    split_ifs <;> rfl

theorem counter_eq_mismatchCount (hn : 0 < n) (z : List Bool) (hz : n + L ≤ z.length) :
    counter n L z = mismatchCount n L (inputOf n z) (copyOf n L z) := by
  have hf : filled n L z = L := by simp only [filled]; omega
  unfold counter mismatchCount
  rw [hf, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [copyOf_get, inputOf_getD _ (sched_lt hn _)]

theorem progState_eq (z : List Bool) (hz : n + L ≤ z.length) :
    progState n L P z = P.prod (copyOf n L z).toList *ᵥ P.v0 := by
  rw [progState, copyOf_toList z hz]

/-- `ℓ(h) = w_tᵀ s(h)` with `t = |h|`. -/
theorem teacherLogit_eq_read (hn : 0 < n) (h : List Bool) :
    teacherLogit n L P B h = read n L P B h.length (state n L P h) := by
  change teacherLogit n L P B h = readFun n L P B h.length (state n L P h)
  unfold teacherLogit readFun
  split_ifs with h1 h2 h3
  · rfl
  · rw [readInput_state P h (sched_lt hn _)]
    rfl
  · rw [progPart_state, progState_eq P h (by omega), Program.response]
    simp only [state]
    rw [counter_eq_mismatchCount hn h (by omega), dotProduct_comm]
  · rfl

/-- `lem:hard-teacher` (rank part): at every cut `t` and for every horizon `T`, the logit matrix
of the teacher has rank at most `n + 7`, for every scale `B`. -/
theorem teacherLogit_rank_le (hn : 0 < n) (T t : ℕ) :
    (logitCutMatrix (teacherLogit n L P B) T t).rank ≤ n + 7 := by
  have := rank_le_of_linearState (teacherLogit n L P B) (state n L P) (step n L P)
    (read n L P B) (state_snoc P hn) (teacherLogit_eq_read P B hn) T t
  rwa [card_coord] at this

end Recursion

end LowLogitRank.Hardness
