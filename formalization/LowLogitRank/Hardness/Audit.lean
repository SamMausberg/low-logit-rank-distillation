import LowLogitRank.Hardness.Advantage

/-!
# The finite audit instance of `sec:audit`

`n = 2`, seven public copies (`L = 7`), `T = 128`, `d = 9`, `B = 8 log 2`, so the copy error is
`η = 1/65537`. The hidden functions are the two-bit AND and its complement. This also shows that
the hypothesis `eq:hard-consistency` (`Consistent`) is satisfiable by an explicit width-five
permutation program read along the public schedule `x₁, x₂, x₁, …`.

The program used here is a simple one, not Barrington's: instruction 0 (reading `x₁`) swaps the
states `0, 1` when `x₁ = 1`, instruction 1 (reading `x₂`) swaps `1, 2` when `x₂ = 1`, and the
other five instructions are identities. From the start state `0` the final state is `2` exactly
when `x₁ = x₂ = 1`. The rank table of `sec:audit` is not reproduced.

`Consistent` is also satisfiable for every `n` and `L`: every program is consistent with the
function it computes (`consistent_self`), and a dictator program computes `F(x) = x₁` for every
`L ≥ 1` (`dict_consistent`).
-/

namespace LowLogitRank.Hardness

open Finset

namespace Program

/-- The state index reached from `k` by the instructions `j, j+1, …` reading `a`. -/
def track (P : Program) : ℕ → List Bool → Fin 5 → Fin 5
  | _, [], k => k
  | j, b :: a, k => track P (j + 1) a ((P.perm j b).symm k)

theorem prodFrom_mulVec_single_eq (P : Program) (j : ℕ) (a : List Bool) (k : Fin 5) :
    Matrix.mulVec (P.prodFrom j a) (Pi.single k 1) = Pi.single (P.track j a k) 1 := by
  induction a generalizing j k with
  | nil => rw [prodFrom, Matrix.one_mulVec]; rfl
  | cons b a ih =>
    rw [prodFrom, ← Matrix.mulVec_mulVec, instr_mulVec_single, ih]
    rfl

theorem response_eq_sign_track (P : Program) (a : List Bool) :
    P.response a = P.sign (P.track 0 a P.start) := by
  rw [response, prod, v0, prodFrom_mulVec_single_eq, dotProduct_single, mul_one]

end Program

/-- The permutations of the audit program. -/
def auditPerm : ℕ → Bool → Equiv.Perm (Fin 5)
  | 0, true => Equiv.swap 0 1
  | 1, true => Equiv.swap 1 2
  | _, _ => 1

/-- The audit program for AND (`sign = +1` at state `2`) or its complement (`sign = -1` there). -/
def auditProgram (complement : Bool) : Program where
  perm := auditPerm
  start := 0
  sign := fun k => if (k = 2) = !complement then 1 else -1
  sign_mem := fun k => by split_ifs <;> simp

/-- The two-bit AND function, and its complement. -/
def auditF (complement : Bool) (x : Word 2) : Bool := (x.get 0 && x.get 1) != complement

theorem consistentWord_audit (x : Word 2) :
    (consistentWord 2 7 x).toList =
      [x.get 0, x.get 1, x.get 0, x.get 1, x.get 0, x.get 1, x.get 0] := by
  obtain ⟨l, hl⟩ := x
  match l, hl with
  | [a, b], _ => rfl

theorem auditProgram_track (complement : Bool) (x : Word 2) :
    (auditProgram complement).track 0 (consistentWord 2 7 x).toList 0 =
      if x.get 0 && x.get 1 then 2 else if x.get 0 then 1 else 0 := by
  rw [consistentWord_audit]
  generalize x.get 0 = a
  generalize x.get 1 = b
  cases a <;> cases b <;> cases complement <;> decide

/-- `eq:hard-consistency` holds for the audit programs. -/
theorem auditProgram_consistent (complement : Bool) :
    Consistent 2 7 (auditProgram complement) (auditF complement) := by
  intro x
  rw [Program.response_eq_sign_track]
  change (auditProgram complement).sign
    ((auditProgram complement).track 0 (consistentWord 2 7 x).toList 0) = _
  rw [auditProgram_track]
  simp only [auditProgram, auditF]
  cases x.get 0 <;> cases x.get 1 <;> cases complement <;> norm_num [bitValue]

/-- A trivial program (all instructions the identity, readout `+1`) satisfies
`eq:hard-consistency` for the constant function `1`, for every `n` and `L`: the hypothesis
`Consistent` is satisfiable in every dimension. -/
def constProgram : Program where
  perm := fun _ _ => 1
  start := 0
  sign := fun _ => 1
  sign_mem := fun _ => Or.inl rfl

theorem constProgram_consistent (n L : ℕ) : Consistent n L constProgram (fun _ => true) := by
  intro x
  rw [Program.response_eq_sign_track]
  simp [constProgram]
  norm_num

/-- Every program satisfies `eq:hard-consistency` for the function it computes on consistent
words, `F(x) = 1` exactly when `R(a(x)) = 1`. -/
theorem consistent_self (n L : ℕ) (P : Program) :
    Consistent n L P (fun x => decide (P.response (consistentWord n L x).toList = 1)) := by
  intro x
  rcases P.response_mem (consistentWord n L x).toList with h | h
  · simp [h, bitValue]; norm_num
  · simp [h, bitValue]; norm_num

/-- The permutations of the dictator program: instruction 0 (reading `x₁`) swaps the states
`0, 1` when `x₁ = 1`; all other instructions are identities. -/
def dictPerm : ℕ → Bool → Equiv.Perm (Fin 5)
  | 0, true => Equiv.swap 0 1
  | _, _ => 1

/-- The dictator program: start state `0`, readout `+1` exactly at state `1`. -/
def dictProgram : Program where
  perm := dictPerm
  start := 0
  sign := fun k => if k = 1 then 1 else -1
  sign_mem := fun k => by split_ifs <;> simp

/-- `eq:hard-consistency` holds for the dictator program and the function `F(x) = x₁` for every
`n` and every `L ≥ 1`; for `n ≥ 1` this `F` is not constant. -/
theorem dict_consistent (n L : ℕ) (hL : 1 ≤ L) :
    Consistent n L dictProgram (fun x => x.toList.getD 0 false) := by
  intro x
  rw [Program.response_eq_sign_track]
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hc : (consistentWord n (L' + 1) x).toList = x.toList.getD 0 false ::
      (List.ofFn fun j : Fin L' => x.toList.getD (sched n (j + 1)) false) := by
    simp [consistentWord, List.Vector.toList_ofFn, List.ofFn_succ, sched, Nat.zero_mod]
  have htrack : ∀ (j : ℕ) (a : List Bool) (k : Fin 5), 1 ≤ j →
      dictProgram.track j a k = k := by
    intro j a
    induction a generalizing j with
    | nil => intro k _; rfl
    | cons b a ih =>
      intro k hj
      simp only [Program.track]
      rw [ih (j + 1) _ (by omega)]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      cases b <;> simp [dictProgram, dictPerm] <;> rfl
  rw [hc]
  simp only [Program.track]
  rw [htrack 1 _ _ le_rfl]
  have h01 : (1 : Equiv.Perm (Fin 5)).symm 0 ≠ 1 := by decide
  cases x.toList.getD 0 false
  · simp only [dictProgram, dictPerm, ↓reduceIte, h01, bitValue_false, mul_zero, zero_sub]
  · simp only [dictProgram, dictPerm, Equiv.symm_swap, Equiv.swap_apply_left, ↓reduceIte,
      bitValue_true, mul_one]
    norm_num

/-- The audit scale `B = 8 log 2`. -/
noncomputable def auditB : ℝ := 8 * Real.log 2

/-- The audit copy error is exactly `1/65537`. -/
theorem etaOf_auditB : etaOf auditB = 1 / 65537 := by
  unfold etaOf auditB
  rw [show 2 * (8 * Real.log 2) = ((16 : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
    Real.exp_nat_mul, Real.exp_log two_pos]
  norm_num

/-- The audit teachers belong to `𝒞_{128,9}`. -/
theorem audit_inClass (complement : Bool) :
    InClass 128 9 (teacher 2 7 (auditProgram complement) auditB) := by
  apply teacher_inClass (n := 2) (L := 7) _ _ (by norm_num) (by unfold auditB; positivity)
  unfold auditB
  have := Real.log_two_lt_d9
  push_cast
  linarith

/-- The audit `TV` to the deterministic-copy distribution is `1 - (1 - 1/65537)^8`. -/
theorem audit_tv (complement : Bool) :
    tv (wordDist (teacher 2 7 (auditProgram complement) auditB) 128)
        (idealDist 2 7 (auditF complement) 128) = 1 - (1 - 1 / 65537) ^ 8 := by
  rw [tv_teacher_ideal _ _ (by norm_num) (auditProgram_consistent complement) 128 (by norm_num),
    etaOf_auditB]

/-- The largest per-query simulator discrepancy in the audit is `1/65537`: it bounds every
prefix and is attained at the first copy position. -/
theorem audit_simulator (complement : Bool) :
    (∀ h : List Bool, |simulator 2 7 (auditF complement) h -
        teacher 2 7 (auditProgram complement) auditB h| ≤ 1 / 65537) ∧
      |simulator 2 7 (auditF complement) [false, false] -
        teacher 2 7 (auditProgram complement) auditB [false, false]| = 1 / 65537 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← etaOf_auditB]
    exact simulator_close _ _ (by unfold auditB; positivity) (auditProgram_consistent complement) h
  · rw [← etaOf_auditB]
    have := teacher_copy (n := 2) (L := 7) (auditProgram complement) auditB [false, false]
      (by simp) (by simp)
    have hsim : simulator 2 7 (auditF complement) [false, false] =
        bitValue (([false, false] : List Bool).getD
          (sched 2 (([false, false] : List Bool).length - 2)) false) := by
      simp [simulator]
    rw [hsim]
    exact abs_bitValue_sub (etaOf_pos _).le this

end LowLogitRank.Hardness
