import LowLogitRank.Hardness.Class

/-!
# The multi-block teacher of `cor:allTV` (`sec:weak-error`)

The payload `X` has `m` bits; then come `r` blocks, block `j` consisting of `L` copies of `X` on
the public schedule followed by the label `Y_j`, then fair padding. Block `j` uses its own hidden
program `Ps j` (for `F(·, j)`). Positions are 0-based: block `j` starts at `m + j(L+1)`.

The rank proof uses the same state `(1, X, C, v)` as `lem:hard-teacher`, with the linear reset
`(1, X, C, v) ↦ (1, X, 0, v₀)` after each label (`reset`). The state machine treats every
position `≥ m` as part of a block, including the padding, where only the readout is zero.
-/

namespace LowLogitRank.Hardness

open Finset Matrix

/-! ### The reset map -/

section Reset

variable {m : ℕ}

/-- A state `(c, X, C, v)`. -/
def mkState (c : ℝ) (x : Fin m → ℝ) (C : ℝ) (v : Fin 5 → ℝ) : Coord m → ℝ
  | .inl _ => c
  | .inr (.inl i) => x i
  | .inr (.inr (.inl _)) => C
  | .inr (.inr (.inr k)) => v k

/-- The reset of `cor:allTV`, `(1, X, C, v) ↦ (1, X, 0, v₀)`, as a linear map (it writes `v₀`
through the constant coordinate). -/
def reset (v₀ : Fin 5 → ℝ) : (Coord m → ℝ) →ₗ[ℝ] (Coord m → ℝ) where
  toFun s := mkState (s (.inl ())) (fun i => s (.inr (.inl i))) 0 (fun k => v₀ k * s (.inl ()))
  map_add' s₁ s₂ := by
    funext c
    rcases c with u | i | u | k <;> simp [mkState]
    ring
  map_smul' a s := by
    funext c
    rcases c with u | i | u | k <;> simp [mkState]
    ring

/-- `cor:allTV`: the reset sends `(1, X, C, v)` to `(1, X, 0, v₀)`. -/
theorem reset_mkState (v₀ : Fin 5 → ℝ) (x : Fin m → ℝ) (C : ℝ) (v : Fin 5 → ℝ) :
    reset v₀ (mkState 1 x C v) = mkState 1 x 0 v₀ := by
  funext c; rcases c with u | i | u | k <;> simp [reset, mkState]

end Reset

/-! ### Block arithmetic -/

theorem succ_div_mod_of_lt {u K : ℕ} (hK : 0 < K) (h : u % K + 1 < K) :
    (u + 1) / K = u / K ∧ (u + 1) % K = u % K + 1 := by
  rw [Nat.div_mod_unique hK]
  have := Nat.mod_add_div u K
  constructor <;> omega

theorem succ_div_mod_of_eq {u K : ℕ} (hK : 0 < K) (h : u % K + 1 = K) :
    (u + 1) / K = u / K + 1 ∧ (u + 1) % K = 0 := by
  rw [Nat.div_mod_unique hK]
  have := Nat.mod_add_div u K
  constructor
  · rw [Nat.mul_add, Nat.mul_one]; omega
  · omega

/-! ### The multi-block teacher -/

section MultiBlock

variable (m L r : ℕ) (Ps : ℕ → Program) (B : ℝ)

/-- The block index of position `t ≥ m`. -/
def blockIdx (t : ℕ) : ℕ := (t - m) / (L + 1)

/-- The offset of position `t ≥ m` inside its block (`< L`: copy, `= L`: label). -/
def blockOff (t : ℕ) : ℕ := (t - m) % (L + 1)

/-- The copy word `A^{(j)}` of block `j`. -/
def blockCopy (j : ℕ) (h : List Bool) : Word L :=
  List.Vector.ofFn fun i => h.getD (m + j * (L + 1) + i) false

/-- The logits of the multi-block teacher of `cor:allTV`: zero at payload and padding positions,
`B(2X_{i_o} - 1)` at copy `o` of a block, and `B(2C_j + R_j(A^{(j)}))` at the label of block
`j < r`, where `C_j` counts the mismatches of block `j` and `R_j` is the readout of `Ps j`. -/
noncomputable def multiLogit (h : List Bool) : ℝ :=
  if h.length < m then 0
  else if blockIdx m L h.length < r then
    if blockOff m L h.length < L then
      B * (2 * bitValue (h.getD (sched m (blockOff m L h.length)) false) - 1)
    else
      B * (2 * (mismatchCount m L (inputOf m h) (blockCopy m L (blockIdx m L h.length) h) : ℝ) +
        (Ps (blockIdx m L h.length)).response (blockCopy m L (blockIdx m L h.length) h).toList)
  else 0

/-- The counter of the current block. -/
def multiCounter (h : List Bool) : ℕ :=
  ∑ i ∈ range (blockOff m L h.length),
    if h.getD (m + blockIdx m L h.length * (L + 1) + i) false = h.getD (sched m i) false then 0
    else 1

/-- The program state of the current block. -/
def multiProg (h : List Bool) : Fin 5 → ℝ :=
  (Ps (blockIdx m L h.length)).prod
    ((h.drop (m + blockIdx m L h.length * (L + 1))).take (blockOff m L h.length)) *ᵥ
      (Ps (blockIdx m L h.length)).v0

/-- The state `(1, X, C, v)` of the multi-block teacher. -/
def multiState (h : List Bool) : Coord m → ℝ :=
  mkState 1 (fun i => bitValue (h.getD i false)) (multiCounter m L h) (multiProg m L Ps h)

/-- The update at position `t`: write an input bit, update a copy as in `eq:counter`, or reset
after a label. -/
def multiStepFun (t : ℕ) (b : Bool) (s : Coord m → ℝ) : Coord m → ℝ
  | .inl u => s (.inl u)
  | .inr (.inl i) => if i.val = t then bitValue b * s (.inl ()) else s (.inr (.inl i))
  | .inr (.inr (.inl u)) =>
      if t < m then s (.inr (.inr (.inl u)))
      else if blockOff m L t < L then
        s (.inr (.inr (.inl u))) + bitValue b * s (.inl ()) +
          (1 - 2 * bitValue b) * readInput m s (sched m (blockOff m L t))
      else 0
  | .inr (.inr (.inr k)) =>
      if t < m then s (.inr (.inr (.inr k)))
      else if blockOff m L t < L then
        ((Ps (blockIdx m L t)).instr (blockOff m L t) b *ᵥ progPart m s) k
      else (Ps (blockIdx m L t + 1)).v0 k * s (.inl ())

/-- The linear update `A_{t,b}` of the multi-block teacher. -/
def multiStep (t : ℕ) (b : Bool) : (Coord m → ℝ) →ₗ[ℝ] (Coord m → ℝ) where
  toFun := multiStepFun m L Ps t b
  map_add' s₁ s₂ := by
    funext c
    rcases c with u | i | u | k <;>
      simp only [multiStepFun, readInput, progPart, Pi.add_apply, mulVec, dotProduct] <;>
      split_ifs <;> (try simp only [mul_add, Finset.sum_add_distrib]) <;> ring
  map_smul' a s := by
    funext c
    rcases c with u | i | u | k <;>
      simp only [multiStepFun, readInput, progPart, Pi.smul_apply, smul_eq_mul, mulVec,
        dotProduct, RingHom.id_apply] <;>
      split_ifs <;> (try simp only [mul_left_comm _ a, ← Finset.mul_sum]) <;> ring

/-- At a label position the update is the reset of `cor:allTV`, to the next block's `v₀`. -/
theorem multiStep_label (t : ℕ) (b : Bool) (ht : m ≤ t) (hl : ¬ blockOff m L t < L) :
    multiStep m L Ps t b = reset (Ps (blockIdx m L t + 1)).v0 := by
  have hm : ¬ t < m := by omega
  apply LinearMap.ext
  intro s
  funext c
  rcases c with u | i | u | k
  · rfl
  · change (if i.val = t then _ else _) = s (.inr (.inl i))
    rw [ite_eq_right (by omega)]
  · change (if t < m then _ else _) = 0
    rw [ite_eq_right hm, ite_eq_right hl]
  · change (if t < m then _ else _) = _
    rw [ite_eq_right hm, ite_eq_right hl]
    rfl

/-- The readout `w_t` of the multi-block teacher. -/
def multiReadFun (t : ℕ) (s : Coord m → ℝ) : ℝ :=
  if t < m then 0
  else if blockIdx m L t < r then
    if blockOff m L t < L then B * (2 * readInput m s (sched m (blockOff m L t)) - s (.inl ()))
    else B * (2 * s (.inr (.inr (.inl ()))) + (Ps (blockIdx m L t)).sign ⬝ᵥ progPart m s)
  else 0

/-- The linear readout. -/
def multiRead (t : ℕ) : (Coord m → ℝ) →ₗ[ℝ] ℝ where
  toFun := multiReadFun m L r Ps B t
  map_add' s₁ s₂ := by
    simp only [multiReadFun, readInput, progPart, Pi.add_apply, dotProduct]
    split_ifs <;> (try simp only [mul_add, Finset.sum_add_distrib]) <;> ring
  map_smul' a s := by
    simp only [multiReadFun, readInput, progPart, Pi.smul_apply, smul_eq_mul, dotProduct,
      RingHom.id_apply]
    split_ifs <;> (try simp only [mul_left_comm _ a, ← Finset.mul_sum]) <;> ring

end MultiBlock

/-! ### The state recursion of the multi-block teacher -/

section MultiRecursion

variable {m L r : ℕ} (Ps : ℕ → Program) (B : ℝ)

theorem blockOff_le (t : ℕ) : blockOff m L t ≤ L := by
  have := Nat.mod_lt (t - m) (show 0 < L + 1 by omega)
  unfold blockOff
  omega

theorem blockStart_add_off {t : ℕ} (ht : m ≤ t) :
    m + blockIdx m L t * (L + 1) + blockOff m L t = t := by
  unfold blockIdx blockOff
  have := Nat.div_add_mod' (t - m) (L + 1)
  omega

theorem blockOff_of_le {t : ℕ} (ht : t ≤ m) : blockOff m L t = 0 := by
  simp [blockOff, Nat.sub_eq_zero_of_le ht]

theorem block_snoc_input {t : ℕ} (ht : t < m) :
    blockIdx m L (t + 1) = blockIdx m L t ∧ blockOff m L (t + 1) = blockOff m L t := by
  unfold blockIdx blockOff
  rw [Nat.sub_eq_zero_of_le (show t + 1 ≤ m by omega), Nat.sub_eq_zero_of_le ht.le]
  simp

theorem block_snoc_copy {t : ℕ} (ht : m ≤ t) (ho : blockOff m L t < L) :
    blockIdx m L (t + 1) = blockIdx m L t ∧ blockOff m L (t + 1) = blockOff m L t + 1 := by
  unfold blockIdx blockOff at *
  rw [show t + 1 - m = (t - m) + 1 by omega]
  exact succ_div_mod_of_lt (Nat.succ_pos L) (by omega)

theorem block_snoc_label {t : ℕ} (ht : m ≤ t) (ho : ¬ blockOff m L t < L) :
    blockIdx m L (t + 1) = blockIdx m L t + 1 ∧ blockOff m L (t + 1) = 0 := by
  have := blockOff_le (m := m) (L := L) t
  unfold blockIdx blockOff at *
  rw [show t + 1 - m = (t - m) + 1 by omega]
  exact succ_div_mod_of_eq (Nat.succ_pos L) (by omega)

theorem multiCounter_snoc (hm : 0 < m) (h : List Bool) (b : Bool) :
    multiCounter m L (h ++ [b]) =
      if h.length < m then multiCounter m L h
      else if blockOff m L h.length < L then
        multiCounter m L h + (if b = h.getD (sched m (blockOff m L h.length)) false then 0 else 1)
      else 0 := by
  unfold multiCounter
  rw [List.length_append, List.length_singleton]
  by_cases h1 : h.length < m
  · rw [ite_eq_left h1, blockOff_of_le h1.le, blockOff_of_le (by omega)]
    simp
  rw [ite_eq_right h1]
  by_cases h2 : blockOff m L h.length < L
  · rw [ite_eq_left h2]
    obtain ⟨hi, ho⟩ := block_snoc_copy (L := L) (show m ≤ h.length by omega) h2
    have hst := blockStart_add_off (L := L) (show m ≤ h.length by omega)
    rw [hi, ho, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun i hi' => ?_
      rw [Finset.mem_range] at hi'
      have hs := sched_lt hm i
      rw [getD_append_of_lt (by omega), getD_append_of_lt (by omega)]
    · have hs := sched_lt hm (blockOff m L h.length)
      rw [show m + blockIdx m L h.length * (L + 1) + blockOff m L h.length = h.length by omega,
        getD_snoc_self, getD_append_of_lt (by omega)]
  · rw [ite_eq_right h2, (block_snoc_label (L := L) (show m ≤ h.length by omega) h2).2]
    simp

theorem prod_nil (P : Program) : P.prod [] = 1 := rfl

theorem multiProg_snoc (h : List Bool) (b : Bool) :
    multiProg m L Ps (h ++ [b]) =
      if h.length < m then multiProg m L Ps h
      else if blockOff m L h.length < L then
        (Ps (blockIdx m L h.length)).instr (blockOff m L h.length) b *ᵥ multiProg m L Ps h
      else (Ps (blockIdx m L h.length + 1)).v0 := by
  unfold multiProg
  rw [List.length_append, List.length_singleton]
  split_ifs with h1 h2
  · obtain ⟨hi, ho⟩ := block_snoc_input (L := L) h1
    rw [hi, ho, blockOff_of_le h1.le, List.take_zero, List.take_zero]
  · obtain ⟨hi, ho⟩ := block_snoc_copy (L := L) (show m ≤ h.length by omega) h2
    have hst := blockStart_add_off (L := L) (show m ≤ h.length by omega)
    rw [hi, ho, List.drop_append_of_le_length (by omega),
      List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega),
      Program.prod_append_singleton, ← mulVec_mulVec, List.length_drop,
      show h.length - (m + blockIdx m L h.length * (L + 1)) = blockOff m L h.length by omega]
  · rw [(block_snoc_label (L := L) (show m ≤ h.length by omega) h2).1,
      (block_snoc_label (L := L) (show m ≤ h.length by omega) h2).2, List.take_zero, prod_nil,
      one_mulVec]

@[simp] theorem multiState_one (h : List Bool) (u : Unit) :
    multiState m L Ps h (.inl u) = 1 := rfl

@[simp] theorem multiState_count (h : List Bool) (u : Unit) :
    multiState m L Ps h (.inr (.inr (.inl u))) = multiCounter m L h := rfl

@[simp] theorem multiState_prog (h : List Bool) (k : Fin 5) :
    multiState m L Ps h (.inr (.inr (.inr k))) = multiProg m L Ps h k := rfl

theorem progPart_multiState (h : List Bool) :
    progPart m (multiState m L Ps h) = multiProg m L Ps h := rfl

theorem readInput_multiState (h : List Bool) {i : ℕ} (hi : i < m) :
    readInput m (multiState m L Ps h) i = bitValue (h.getD i false) := by
  simp [readInput, hi, multiState, mkState]

/-- `s(hb) = A_{t,b} s(h)` for the multi-block teacher. -/
theorem multiState_snoc (hm : 0 < m) (h : List Bool) (b : Bool) :
    multiState m L Ps (h ++ [b]) = multiStep m L Ps h.length b (multiState m L Ps h) := by
  funext c
  change multiState m L Ps (h ++ [b]) c = multiStepFun m L Ps h.length b (multiState m L Ps h) c
  rcases c with u | i | u | k
  · rfl
  · simp only [multiState, mkState, multiStepFun]
    split_ifs with hi
    · rw [hi, getD_snoc_self, mul_one]
    · rw [getD_snoc_of_ne hi]
  · simp only [multiState_count, multiStepFun, multiState_one]
    rw [multiCounter_snoc hm]
    by_cases h1 : h.length < m
    · rw [ite_eq_left h1, ite_eq_left h1]
    rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : blockOff m L h.length < L
    · rw [ite_eq_left h2, ite_eq_left h2, readInput_multiState Ps h (sched_lt hm _), Nat.cast_add,
        counter_update, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
    · rw [ite_eq_right h2, ite_eq_right h2, Nat.cast_zero]
  · simp only [multiState_prog, multiStepFun, multiState_one, progPart_multiState]
    rw [multiProg_snoc]
    split_ifs with h1 h2
    · rfl
    · rfl
    · rw [mul_one]

theorem multiCounter_label (hm : 0 < m) (h : List Bool) (ho : ¬ blockOff m L h.length < L) :
    multiCounter m L h =
      mismatchCount m L (inputOf m h) (blockCopy m L (blockIdx m L h.length) h) := by
  have hL : blockOff m L h.length = L := le_antisymm (blockOff_le _) (by omega)
  unfold multiCounter mismatchCount
  rw [hL, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockCopy, List.Vector.get_ofFn, inputOf_getD _ (sched_lt hm _)]

theorem multiProg_label (h : List Bool) (ht : m ≤ h.length) (ho : ¬ blockOff m L h.length < L) :
    multiProg m L Ps h = (Ps (blockIdx m L h.length)).prod
      (blockCopy m L (blockIdx m L h.length) h).toList *ᵥ (Ps (blockIdx m L h.length)).v0 := by
  have hL : blockOff m L h.length = L := le_antisymm (blockOff_le _) (by omega)
  have hst := blockStart_add_off (L := L) ht
  unfold multiProg
  congr 2
  rw [hL]
  apply list_ext_getD
  · simp; omega
  intro i hi
  simp only [List.length_take, List.length_drop] at hi
  rw [getD_take _ (by omega), getD_drop, blockCopy, List.Vector.toList_ofFn,
    getD_ofFn _ (by omega)]

/-- `ℓ(h) = w_tᵀ s(h)` for the multi-block teacher. -/
theorem multiLogit_eq_read (hm : 0 < m) (h : List Bool) :
    multiLogit m L r Ps B h = multiRead m L r Ps B h.length (multiState m L Ps h) := by
  change multiLogit m L r Ps B h = multiReadFun m L r Ps B h.length (multiState m L Ps h)
  unfold multiLogit multiReadFun
  split_ifs with h1 h2 h3
  · rfl
  · rw [readInput_multiState Ps h (sched_lt hm _)]
    rfl
  · rw [Program.response, ← multiProg_label Ps h (by omega) h3,
      ← multiCounter_label hm h h3]
    rfl
  · rfl

/-- `cor:allTV`: the multi-block teacher has logit rank at most `m + 7` at every cut, for every
number of blocks `r`, every horizon `T`, and every scale `B`. -/
theorem multiLogit_rank_le (hm : 0 < m) (T t : ℕ) :
    (logitCutMatrix (multiLogit m L r Ps B) T t).rank ≤ m + 7 := by
  have := rank_le_of_linearState (multiLogit m L r Ps B) (multiState m L Ps)
    (multiStep m L Ps) (multiRead m L r Ps B) (multiState_snoc Ps hm)
    (multiLogit_eq_read Ps B hm) T t
  rwa [card_coord] at this

/-- `|ℓ(h)| ≤ B(2L + 1)` for the multi-block teacher. -/
theorem abs_multiLogit_le (hB : 0 ≤ B) (h : List Bool) :
    |multiLogit m L r Ps B h| ≤ B * (2 * L + 1) := by
  have hBL : 0 ≤ B * (2 * L + 1) := by positivity
  unfold multiLogit
  split_ifs with h1 h2 h3
  · simpa using hBL
  · rw [abs_mul, abs_of_nonneg hB]
    apply mul_le_mul_of_nonneg_left _ hB
    cases h.getD (sched m (blockOff m L h.length)) false <;> norm_num
  · rw [abs_mul, abs_of_nonneg hB]
    apply mul_le_mul_of_nonneg_left _ hB
    set a := blockCopy m L (blockIdx m L h.length) h
    have hC : (mismatchCount m L (inputOf m h) a : ℝ) ≤ L := by
      exact_mod_cast mismatchCount_le (inputOf m h) a
    have hC0 : (0 : ℝ) ≤ mismatchCount m L (inputOf m h) a := Nat.cast_nonneg _
    rcases (Ps (blockIdx m L h.length)).response_mem a.toList with hr | hr <;>
      rw [hr, abs_le] <;> constructor <;> linarith
  · simpa using hBL

/-- `cor:allTV`: the multi-block teacher is in `𝒞_{T,m+7}` whenever `B(2L + 1) ≤ T`. -/
theorem multiTeacher_inClass (hm : 0 < m) (hB : 0 ≤ B) (T : ℕ) (hT : B * (2 * L + 1) ≤ T) :
    InClass T (m + 7) (ofLogit (multiLogit m L r Ps B)) where
  fullSupport := ofLogit_fullSupport _ _
  logit_le h _ := by rw [logit_ofLogit]; exact (abs_multiLogit_le Ps B hB h).trans hT
  rank_le t _ := by
    rw [show logit (ofLogit (multiLogit m L r Ps B)) = multiLogit m L r Ps B from
      funext (logit_ofLogit _)]
    exact multiLogit_rank_le Ps B hm T t

/-- `cor:allTV` with its parameters `B = n log 2`, `T = 2nr(L + 1)`, for a payload of
`1 ≤ m ≤ n` bits and `r ≥ 1` blocks: `|ℓ| ≤ n log 2 (2L + 1) < T`, the blocks fit
(`m + r(L + 1) ≤ T`), and the teacher is in `𝒞_{T,m+7}`. -/
theorem multiTeacher_inClass_hard {n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hr : 1 ≤ r) :
    hardB n * (2 * L + 1) < 2 * n * r * (L + 1) ∧ m + r * (L + 1) ≤ 2 * n * r * (L + 1) ∧
      InClass (2 * n * r * (L + 1)) (m + 7) (ofLogit (multiLogit m L r Ps (hardB n))) := by
  have hn : 1 ≤ n := by omega
  have h1 : hardB n * (2 * L + 1) < 2 * n * r * (L + 1) := by
    have := hardB_mul_lt (L := L) hn
    unfold hardT at this
    have : ((2 * n * (L + 1) : ℕ) : ℝ) ≤ ((2 * n * r * (L + 1) : ℕ) : ℝ) := by
      have e : 2 * n * r * (L + 1) = 2 * n * (L + 1) * r := by ring
      exact_mod_cast (by rw [e]; exact Nat.le_mul_of_pos_right _ hr :
        2 * n * (L + 1) ≤ 2 * n * r * (L + 1))
    push_cast at *
    linarith
  have h2 : m + r * (L + 1) ≤ 2 * n * r * (L + 1) := by
    have hX : 1 ≤ r * (L + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e : 2 * n * r * (L + 1) = n * (r * (L + 1)) + n * (r * (L + 1)) := by ring
    have a1 : n ≤ n * (r * (L + 1)) := Nat.le_mul_of_pos_right _ hX
    have a2 : r * (L + 1) ≤ n * (r * (L + 1)) := Nat.le_mul_of_pos_left _ hn
    omega
  refine ⟨h1, h2, multiTeacher_inClass Ps _ hm (hardB_nonneg n) _ ?_⟩
  push_cast at h1 ⊢
  exact h1.le

end MultiRecursion

end LowLogitRank.Hardness
