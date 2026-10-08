import LowLogitRank.Hardness.Class

/-!
# Simulation, the event mass, and `TV(P_k, D_k)` (`sec:hardness`)

* `simulator`: the per-prefix simulator of the paragraph "Simulation and the sampler test", and
  `simulator_close`: for `H = F` it is within `η` of the teacher at every prefix. The transcript
  bound `qη` is `tv_transcript_simulator_le` in `Transfer.lean`, from `lem:coupling`.
* `teacher_eventMass`: the mass identity `P_k(E_S) = (1-η)^{L+1} (1 - |S|/2^n)` in the proof of
  `thm:reduction`, computed from `wordDist` with the padding summed out.
* `tv_teacher_ideal`: `TV(P_k, D_k) = 1 - (1-η)^{L+1} ≤ (L+1)η`.
-/

namespace LowLogitRank.Hardness

open Finset

variable {n L : ℕ}

/-! ### The simulator -/

section Simulator

variable (n L) in
/-- The simulator with membership access to `H : {0,1}^n → {0,1}`: a fair bit at input and
padding positions, the prescribed copy `X_{i_j}` at copy positions (a point mass), `H(X)` at
consistent label prefixes (`C = 0`), and one at inconsistent label prefixes. It does not use
the hidden program. -/
noncomputable def simulator (H : Word n → Bool) : NextBit := fun h =>
  if h.length < n then 1 / 2
  else if h.length < n + L then bitValue (h.getD (sched n (h.length - n)) false)
  else if h.length = n + L then
    (if mismatchCount n L (inputOf n h) (copyOf n L h) = 0 then bitValue (H (inputOf n h)) else 1)
  else 1 / 2

/-- The simulator consults `H` only at the input `X` of a consistent label prefix: one membership
query per simulated reply, and none elsewhere. -/
theorem simulator_congr (H H' : Word n → Bool) (h : List Bool)
    (hH : h.length = n + L → mismatchCount n L (inputOf n h) (copyOf n L h) = 0 →
      H (inputOf n h) = H' (inputOf n h)) :
    simulator n L H h = simulator n L H' h := by
  unfold simulator
  split_ifs with h1 h2 h3 h4 <;> simp_all

theorem abs_bitValue_sub {p : NextBit} {h : List Bool} {x : Bool} {η : ℝ} (hη : 0 ≤ η)
    (hx : bitProb p h x = 1 - η) : |bitValue x - p h| = η := by
  cases x
  · simp only [bitProb, Bool.false_eq_true, ↓reduceIte] at hx
    rw [bitValue_false, show p h = η by linarith, zero_sub, abs_neg, abs_of_nonneg hη]
  · simp only [bitProb, ↓reduceIte] at hx
    rw [bitValue_true, hx, sub_sub_cancel, abs_of_nonneg hη]

variable (P : Program) (B : ℝ)

/-- "Simulation and the sampler test": for `H = F` under `eq:hard-consistency`, every simulated
response law differs from the teacher's by at most `η`, at every prefix (consistent or not). -/
theorem simulator_close (hB : 0 ≤ B) {F : Word n → Bool} (hcons : Consistent n L P F)
    (h : List Bool) : |simulator n L F h - teacher n L P B h| ≤ etaOf B := by
  have hη := (etaOf_pos B).le
  unfold simulator
  split_ifs with h1 h2 h3 h4
  · rw [teacher_fair P B h (Or.inl h1)]; simpa using hη
  · exact (abs_bitValue_sub hη (teacher_copy P B h (by omega) h2)).le
  · exact (abs_bitValue_sub hη (teacher_label_consistent P B hcons h h3 h4)).le
  · have := teacher_label_inconsistent P B hB h h3 (Nat.one_le_iff_ne_zero.mpr h4)
    have hlt : teacher n L P B h < 1 := sigmoid_lt_one _
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [teacher_fair P B h (Or.inr (by omega))]; simpa using hη

/-- The simulator bound for the parameters of `eq:hard-parameters`: within `η = (1 + 2^{2n})⁻¹`
of `P_k` at every prefix. -/
theorem simulator_close_hard {F : Word n → Bool} (hcons : Consistent n L P F) (h : List Bool) :
    |simulator n L F h - hardTeacher n L P h| ≤ hardEta n := by
  rw [← etaOf_hardB]
  exact simulator_close P _ (hardB_nonneg n) hcons h

end Simulator

end LowLogitRank.Hardness
