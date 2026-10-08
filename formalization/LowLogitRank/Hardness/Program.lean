import LowLogitRank.Hardness.Common

/-!
# Width-five permutation branching programs (`sec:hardness`)

Barrington's theorem is not formalized: a hidden program is data, and its correctness for the
pseudorandom function is the hypothesis `eq:hard-consistency` (`Consistent`, in `Teacher.lean`).
What is proved here is the structural fact used by the teacher: every instruction sequence,
consistent or not, keeps the state one-hot, so `R(a) ∈ {-1, 1}` for every `a`.
-/

namespace LowLogitRank.Hardness

open Matrix

/-- A width-five permutation branching program read along the public schedule. Instruction `j`
(0-based; the paper's instruction `j + 1`) applies the permutation matrix of `perm j b` after
reading the bit `b`. A program of length `L` uses only the instructions `j < L`. The start state
is the one-hot vector `v₀ = e_start`, and the readout is a sign vector `r ∈ {-1,1}^5`. -/
structure Program where
  perm : ℕ → Bool → Equiv.Perm (Fin 5)
  start : Fin 5
  sign : Fin 5 → ℝ
  sign_mem : ∀ k, sign k = 1 ∨ sign k = -1

namespace Program

variable (P : Program)

/-- The `5 × 5` permutation matrix `M_{j,b}`. -/
def instr (j : ℕ) (b : Bool) : Matrix (Fin 5) (Fin 5) ℝ := (P.perm j b).permMatrix ℝ

/-- The one-hot start vector `v₀`. -/
def v0 : Fin 5 → ℝ := Pi.single P.start 1

/-- `prodFrom j a = M_{j+|a|-1, a_{|a|}} ⋯ M_{j+1, a_2} M_{j, a_1}` (0-based instruction
indices). -/
def prodFrom : ℕ → List Bool → Matrix (Fin 5) (Fin 5) ℝ
  | _, [] => 1
  | j, b :: a => prodFrom (j + 1) a * P.instr j b

/-- The product `M_{|a|, a_{|a|}} ⋯ M_{1, a_1}` in the paper's 1-based notation. -/
def prod (a : List Bool) : Matrix (Fin 5) (Fin 5) ℝ := P.prodFrom 0 a

/-- The readout `R(a) = rᵀ M_{|a|,a_{|a|}} ⋯ M_{1,a_1} v₀`; the paper uses it for `|a| = L`. -/
def response (a : List Bool) : ℝ := P.sign ⬝ᵥ (P.prod a *ᵥ P.v0)

theorem prodFrom_append_singleton (j : ℕ) (a : List Bool) (b : Bool) :
    P.prodFrom j (a ++ [b]) = P.instr (j + a.length) b * P.prodFrom j a := by
  induction a generalizing j with
  | nil => simp [prodFrom]
  | cons c a ih =>
    simp only [List.cons_append, prodFrom, ih, List.length_cons, mul_assoc]
    congr 2
    omega

theorem prod_append_singleton (a : List Bool) (b : Bool) :
    P.prod (a ++ [b]) = P.instr a.length b * P.prod a := by
  simp [prod, prodFrom_append_singleton]

theorem instr_mulVec_single (j : ℕ) (b : Bool) (k : Fin 5) :
    P.instr j b *ᵥ Pi.single k 1 = Pi.single ((P.perm j b).symm k) 1 := by
  rw [instr, permMatrix_mulVec]
  ext i
  simp [Pi.single_apply, Equiv.eq_symm_apply]

/-- One-hot states are preserved by every instruction sequence. -/
theorem prodFrom_mulVec_single (j : ℕ) (a : List Bool) (k : Fin 5) :
    ∃ k' : Fin 5, P.prodFrom j a *ᵥ Pi.single k 1 = Pi.single k' 1 := by
  induction a generalizing j k with
  | nil => exact ⟨k, by rw [prodFrom, one_mulVec]⟩
  | cons b a ih =>
    obtain ⟨k', hk'⟩ := ih (j + 1) ((P.perm j b).symm k)
    exact ⟨k', by rw [prodFrom, ← mulVec_mulVec, instr_mulVec_single, hk']⟩

/-- Every instruction word `a`, consistent or not, leaves a one-hot state `e_k`, and
`R(a) = r_k`. -/
theorem exists_state (a : List Bool) :
    ∃ k : Fin 5, P.prod a *ᵥ P.v0 = Pi.single k 1 ∧ P.response a = P.sign k := by
  obtain ⟨k, hk⟩ := P.prodFrom_mulVec_single 0 a P.start
  refine ⟨k, hk, ?_⟩
  rw [response, prod, v0, hk, dotProduct_single, mul_one]

/-- (`sec:hardness`) `R(a) ∈ {-1, 1}` for every instruction word `a`. -/
theorem response_mem (a : List Bool) : P.response a = 1 ∨ P.response a = -1 := by
  obtain ⟨k, -, hk⟩ := P.exists_state a
  rw [hk]
  exact P.sign_mem k

/-- `R(a) ∈ {-1, 1}` for every `a ∈ {0,1}^L`. -/
theorem response_word_mem {L : ℕ} (a : Word L) :
    P.response a.toList = 1 ∨ P.response a.toList = -1 :=
  P.response_mem _

theorem abs_response (a : List Bool) : |P.response a| = 1 := by
  rcases P.response_mem a with h | h <;> simp [h]

end Program

end LowLogitRank.Hardness
