import LowLogitRank.Hardness.Advantage

/-!
# The two halves of the proof of `thm:reduction`

* Real case: the TV guarantee transfers the event mass to the student,
  `Q(E_S) ≥ P_k(E_S) - ε ≥ (1-η)^{L+1}(1 - q/2^n) - ε` (`student_event_ge`), and averaging over
  training transcripts that succeed with probability `≥ 1 - δ` gives the factor `1 - δ`
  (`average_ge`). The transfer from the real teacher to the simulator (`qη`) and the assembled
  real case are in `Transfer.lean` (`tv_transcript_simulator_le`, `reduction_real_case`); there
  the hypothesis `hSim` of `reduction_accounting` is proved.
* Random case: an adaptive membership-query algorithm, modeled as a decision tree, that outputs a
  pair `(x, y)` and accepts exactly when `x` was not queried and `y = H(x)`, accepts at most half of
  all functions `H` (`card_accept_le_half`), and the same holds after averaging over its coins.
-/

namespace LowLogitRank.Hardness

open Finset

/-! ### Real case -/

/-- An event changes probability by at most the total-variation distance. -/
theorem abs_event_sub_le_tv {α : Type*} [Fintype α] (P Q : α → ℝ) (hPQ : ∑ z, P z = ∑ z, Q z)
    (E : α → Prop) [DecidablePred E] :
    |(∑ z, if E z then P z else 0) - ∑ z, if E z then Q z else 0| ≤ tv P Q := by
  set a := ∑ z, if E z then P z - Q z else 0
  set b := ∑ z, if E z then 0 else P z - Q z
  have hsplit :
      ∀ z, P z - Q z = (if E z then P z - Q z else 0) + (if E z then 0 else P z - Q z) := by
    intro z; split_ifs <;> ring
  have hab : a + b = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_congr rfl fun z _ => hsplit z,
      Finset.sum_sub_distrib, hPQ, sub_self]
  have hlhs : (∑ z, if E z then P z else 0) - (∑ z, if E z then Q z else 0) = a := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by split_ifs <;> ring
  have ha : |a| ≤ ∑ z, if E z then |P z - Q z| else 0 :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => by split_ifs <;> simp)
  have hb : |b| ≤ ∑ z, if E z then 0 else |P z - Q z| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => by split_ifs <;> simp)
  have htot : (∑ z, if E z then |P z - Q z| else 0) + (∑ z, if E z then 0 else |P z - Q z|) =
      ∑ z, |P z - Q z| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun z _ => by split_ifs <;> ring
  rw [hlhs, tv]
  have : |b| = |a| := by rw [show b = -a by linarith, abs_neg]
  linarith

variable {n L : ℕ} (P : Program)

/-- Proof of `thm:reduction` (real case, one successful transcript): if the student `Q` is within
TV `ε` of `P_k` and the training queried a set `S` of at most `q` inputs, then
`Q(E_{k,S}) ≥ (1-η)^{L+1}(1 - q/2^n) - ε`. -/
theorem student_event_ge (hn : 1 ≤ n) {F : Word n → Bool} (hcons : Consistent n L P F)
    (Q : Word (hardT n L) → ℝ) (hQ : ∑ z, Q z = 1) {ε q : ℝ}
    (hTV : tv (wordDist (hardTeacher n L P) (hardT n L)) Q ≤ ε) (S : Finset (Word n))
    (hS : (S.card : ℝ) ≤ q) :
    (1 - hardEta n) ^ (L + 1) * (1 - q / 2 ^ n) - ε ≤
      ∑ z, if goodEvent n L F S z.toList then Q z else 0 := by
  have hP : ∑ z, wordDist (hardTeacher n L P) (hardT n L) z = 1 := sum_condProb _ _ _
  have h1 := abs_event_sub_le_tv _ Q (hP.trans hQ.symm) (fun z => goodEvent n L F S z.toList)
  rw [hardTeacher_eventMass P hn hcons S] at h1
  have hη0 := (hardEta_pos n).le
  have hη1 : hardEta n ≤ 1 := by rw [← etaOf_hardB]; exact (etaOf_lt_one _).le
  have hu : 0 ≤ (1 - hardEta n) ^ (L + 1) := pow_nonneg (by linarith) _
  have h2 : (1 - hardEta n) ^ (L + 1) * (1 - q / 2 ^ n) ≤
      (1 - hardEta n) ^ (L + 1) * (1 - S.card / 2 ^ n) := by
    apply mul_le_mul_of_nonneg_left _ hu
    have : (S.card : ℝ) / 2 ^ n ≤ q / 2 ^ n := div_le_div_of_nonneg_right hS (by positivity)
    linarith
  have h3 := (abs_le.mp h1).1
  linarith [(abs_le.mp (h1.trans hTV)).2]

/-- Averaging over transcripts (proof of `thm:reduction`): if a nonnegative acceptance
probability `X ω` is at least `a` on a set of transcripts of probability at least `1 - δ`, then
its mean is at least `(1 - δ) a` (for `δ ≤ 1`). -/
theorem average_ge {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hX : ∀ ω, 0 ≤ X ω) (G : Ω → Prop) [DecidablePred G] {a δ : ℝ} (hδ : δ ≤ 1)
    (hG : 1 - δ ≤ ∑ ω, if G ω then w ω else 0) (haG : ∀ ω, G ω → a ≤ X ω) :
    (1 - δ) * a ≤ ∑ ω, w ω * X ω := by
  have hmean : 0 ≤ ∑ ω, w ω * X ω := Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hX ω)
  rcases le_or_gt a 0 with ha | ha
  · nlinarith
  · calc (1 - δ) * a ≤ (∑ ω, if G ω then w ω else 0) * a :=
          mul_le_mul_of_nonneg_right hG ha.le
      _ = ∑ ω, if G ω then w ω * a else 0 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ω _ => by split_ifs <;> simp
      _ ≤ ∑ ω, w ω * X ω := Finset.sum_le_sum fun ω _ => by
          split_ifs with h
          · exact mul_le_mul_of_nonneg_left (haG ω h) (hw ω)
          · exact mul_nonneg (hw ω) (hX ω)

/-- The accounting of `thm:reduction`: a lower bound `(1-δ)[(1-η)^{L+1}(1 - q/2^n) - ε]` for the
acceptance with the real teacher, a transfer loss of at most `qη` to the simulated oracle
(`lem:coupling`), and acceptance at most `1/2` for a random function give `eq:hard-advantage`. -/
theorem reduction_accounting {n L : ℕ} {ε δ η q accReal accSim accRand : ℝ}
    (hReal : (1 - δ) * ((1 - η) ^ (L + 1) * (1 - q / 2 ^ n) - ε) ≤ accReal)
    (hSim : accReal - q * η ≤ accSim) (hRand : accRand ≤ 1 / 2) :
    hardAdvantage n L ε δ η q ≤ accSim - accRand := by
  unfold hardAdvantage
  linarith

/-! ### Random case: adaptive membership queries as decision trees -/

/-- An adaptive membership-query algorithm with fixed coins: it queries points of `α`, branches on
the answers, and ends with an output. -/
inductive QueryTree (α β : Type*) where
  | done : β → QueryTree α β
  | query : α → (Bool → QueryTree α β) → QueryTree α β

namespace QueryTree

variable {α β : Type*}

/-- The queried points and the output of a run against `H`. -/
def run (H : α → Bool) : QueryTree α β → List α × β
  | done b => ([], b)
  | query a k => (a :: (run H (k (H a))).1, (run H (k (H a))).2)

/-- A run depends only on the answers at the queried points. -/
theorem run_congr (t : QueryTree α β) (H H' : α → Bool)
    (h : ∀ a ∈ (run H t).1, H' a = H a) : run H' t = run H t := by
  induction t with
  | done b => rfl
  | query a k ih =>
    simp only [run, List.mem_cons] at h ⊢
    rw [h a (Or.inl rfl), ih (H a) fun a' ha' => h a' (Or.inr ha')]

variable [DecidableEq α]

/-- The output point and label if the output point was not queried during the run, else `none`
(also `none` for a rejection). -/
def freshOutput (H : α → Bool) (t : QueryTree α (Option (α × Bool))) : Option (α × Bool) :=
  match (run H t).2 with
  | some (x, y) => if x ∈ (run H t).1 then none else some (x, y)
  | none => none

/-- The final test of the distinguisher: the output `(x, y)` is accepted when `x` was not queried
during training and `y = H(x)`; outputs at queried points and rejections (`none`) are rejected. -/
def accepts (H : α → Bool) (t : QueryTree α (Option (α × Bool))) : Bool :=
  match freshOutput H t with
  | some (x, y) => y == H x
  | none => false

theorem accepts_iff (H : α → Bool) (t : QueryTree α (Option (α × Bool))) :
    accepts H t = true ↔ ∃ x y, (run H t).2 = some (x, y) ∧ x ∉ (run H t).1 ∧ y = H x := by
  unfold accepts freshOutput
  rcases h : (run H t).2 with _ | ⟨x, y⟩
  · simp
  · by_cases hx : x ∈ (run H t).1 <;> simp [hx]

/-- Flip the value of `H` at a fresh output point (identity otherwise). -/
def flip (t : QueryTree α (Option (α × Bool))) (H : α → Bool) : α → Bool :=
  match freshOutput H t with
  | some (x, _) => Function.update H x (!H x)
  | none => H

theorem freshOutput_spec {H : α → Bool} {t : QueryTree α (Option (α × Bool))} {x : α} {y : Bool}
    (h : freshOutput H t = some (x, y)) : (run H t).2 = some (x, y) ∧ x ∉ (run H t).1 := by
  unfold freshOutput at h
  rcases h' : (run H t).2 with _ | ⟨x', y'⟩
  · simp [h'] at h
  · simp only [h'] at h
    split_ifs at h with hx
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hx⟩

theorem flip_of_some {t : QueryTree α (Option (α × Bool))} {H : α → Bool} {x : α} {y : Bool}
    (h : freshOutput H t = some (x, y)) : flip t H = Function.update H x (!H x) := by
  unfold flip; rw [h]

theorem flip_of_none {t : QueryTree α (Option (α × Bool))} {H : α → Bool}
    (h : freshOutput H t = none) : flip t H = H := by
  unfold flip; rw [h]

theorem accepts_of_some {t : QueryTree α (Option (α × Bool))} {H : α → Bool} {x : α} {y : Bool}
    (h : freshOutput H t = some (x, y)) : accepts H t = (y == H x) := by
  unfold accepts; rw [h]

theorem accepts_of_none {t : QueryTree α (Option (α × Bool))} {H : α → Bool}
    (h : freshOutput H t = none) : accepts H t = false := by
  unfold accepts; rw [h]

theorem run_flip (t : QueryTree α (Option (α × Bool))) (H : α → Bool) :
    run (flip t H) t = run H t := by
  rcases h : freshOutput H t with _ | ⟨x, y⟩
  · rw [flip_of_none h]
  · rw [flip_of_some h]
    apply run_congr
    intro a ha
    rw [Function.update_of_ne]
    rintro rfl
    exact (freshOutput_spec h).2 ha

theorem freshOutput_flip (t : QueryTree α (Option (α × Bool))) (H : α → Bool) :
    freshOutput (flip t H) t = freshOutput H t := by
  unfold freshOutput
  rw [run_flip]

theorem flip_involutive (t : QueryTree α (Option (α × Bool))) :
    Function.Involutive (flip t) := by
  intro H
  rcases h : freshOutput H t with _ | ⟨x, y⟩
  · rw [flip_of_none h, flip_of_none h]
  · have h' : freshOutput (flip t H) t = some (x, y) := by rw [freshOutput_flip, h]
    rw [flip_of_some h', flip_of_some h]
    simp

theorem accepts_add_flip_le (t : QueryTree α (Option (α × Bool))) (H : α → Bool) :
    (if accepts H t then (1 : ℝ) else 0) + (if accepts (flip t H) t then 1 else 0) ≤ 1 := by
  rcases h : freshOutput H t with _ | ⟨x, y⟩
  · have h' : freshOutput (flip t H) t = none := by rw [freshOutput_flip, h]
    rw [accepts_of_none h, accepts_of_none h']
    simp
  · have h' : freshOutput (flip t H) t = some (x, y) := by rw [freshOutput_flip, h]
    rw [accepts_of_some h, accepts_of_some h', flip_of_some h]
    cases H x <;> cases y <;> simp

/-- Proof of `thm:reduction` (random case): for every adaptive membership-query algorithm with
fixed coins, at most half of all functions `H : α → {0,1}` pass the final test "the output point
was not queried and its label equals `H(x)`". -/
theorem card_accept_le_half [Fintype α] (t : QueryTree α (Option (α × Bool))) :
    (∑ H : α → Bool, if accepts H t then (1 : ℝ) else 0) ≤ Fintype.card (α → Bool) / 2 := by
  set e := (flip_involutive t).toPerm
  have hsum : (∑ H : α → Bool, if accepts H t then (1 : ℝ) else 0) =
      ∑ H : α → Bool, if accepts (flip t H) t then (1 : ℝ) else 0 :=
    (Equiv.sum_comp e (fun H => if accepts H t then (1 : ℝ) else 0)).symm
  have h2 : 2 * (∑ H : α → Bool, if accepts H t then (1 : ℝ) else 0) ≤
      ∑ _H : α → Bool, (1 : ℝ) := by
    calc 2 * (∑ H : α → Bool, if accepts H t then (1 : ℝ) else 0)
        = ∑ H : α → Bool, ((if accepts H t then (1 : ℝ) else 0) +
            (if accepts (flip t H) t then 1 else 0)) := by
          rw [Finset.sum_add_distrib, ← hsum]; ring
      _ ≤ ∑ _H : α → Bool, (1 : ℝ) := Finset.sum_le_sum fun H _ => accepts_add_flip_le t H
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h2
  linarith

/-- The random case with coins: if the algorithm draws coins `ω` with probabilities `w ω`
independently of `H`, its acceptance probability for a uniformly random function is at most
`1/2`. -/
theorem accept_prob_le_half [Fintype α] {Ω : Type*} [Fintype Ω]
    (t : Ω → QueryTree α (Option (α × Bool))) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) :
    ∑ ω, w ω * ((∑ H : α → Bool, if accepts H (t ω) then (1 : ℝ) else 0) /
      Fintype.card (α → Bool)) ≤ 1 / 2 := by
  have hc : (0 : ℝ) < Fintype.card (α → Bool) := by exact_mod_cast Fintype.card_pos
  calc ∑ ω, w ω * ((∑ H : α → Bool, if accepts H (t ω) then (1 : ℝ) else 0) /
        Fintype.card (α → Bool))
      ≤ ∑ ω, w ω * (1 / 2) := Finset.sum_le_sum fun ω _ => by
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        rw [div_le_iff₀ hc]
        linarith [card_accept_le_half (t ω)]
    _ = 1 / 2 := by rw [← Finset.sum_mul, hw1, one_mul]

/-! ### Several labels at a fresh payload (`cor:allTV`) -/

section MultiLabel

variable {ι : Type*}

/-- For queries at pairs `(x, j)`: the output payload and labels if no pair with that payload was
queried, else `none`. -/
def freshPayload (H : α × ι → Bool) (t : QueryTree (α × ι) (Option (α × (ι → Bool)))) :
    Option (α × (ι → Bool)) :=
  match (run H t).2 with
  | some (x, ys) => if (run H t).1.any (fun p => decide (p.1 = x)) then none else some (x, ys)
  | none => none

/-- The final test of `cor:allTV`: the output payload `x` was not recorded (no `(x, j)` was
queried) and all labels are correct, `ys j = H(x, j)` for every `j`. -/
def acceptsAll [Fintype ι] (H : α × ι → Bool)
    (t : QueryTree (α × ι) (Option (α × (ι → Bool)))) : Bool :=
  match freshPayload H t with
  | some (x, ys) => decide (∀ j, ys j = H (x, j))
  | none => false

/-- XOR the values of `H` at the fresh payload with the pattern `c`. -/
def flipBy (t : QueryTree (α × ι) (Option (α × (ι → Bool)))) (c : ι → Bool) (H : α × ι → Bool) :
    α × ι → Bool :=
  match freshPayload H t with
  | some (x, _) => fun p => if p.1 = x then xor (H p) (c p.2) else H p
  | none => H

variable {t : QueryTree (α × ι) (Option (α × (ι → Bool)))}

theorem freshPayload_spec {H : α × ι → Bool} {x : α} {ys : ι → Bool}
    (h : freshPayload H t = some (x, ys)) :
    (run H t).2 = some (x, ys) ∧ ∀ p ∈ (run H t).1, p.1 ≠ x := by
  unfold freshPayload at h
  rcases h' : (run H t).2 with _ | ⟨x', ys'⟩
  · simp [h'] at h
  · simp only [h'] at h
    split_ifs at h with hx
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, fun p hp hpx => hx ?_⟩
    simp only [List.any_eq_true, decide_eq_true_eq]
    exact ⟨p, hp, hpx⟩

theorem flipBy_of_some {c : ι → Bool} {H : α × ι → Bool} {x : α} {ys : ι → Bool}
    (h : freshPayload H t = some (x, ys)) :
    flipBy t c H = fun p => if p.1 = x then xor (H p) (c p.2) else H p := by
  unfold flipBy; rw [h]

theorem flipBy_of_none {c : ι → Bool} {H : α × ι → Bool} (h : freshPayload H t = none) :
    flipBy t c H = H := by
  unfold flipBy; rw [h]

theorem run_flipBy (c : ι → Bool) (H : α × ι → Bool) : run (flipBy t c H) t = run H t := by
  rcases h : freshPayload H t with _ | ⟨x, ys⟩
  · rw [flipBy_of_none h]
  · rw [flipBy_of_some h]
    apply run_congr
    intro p hp
    simp [(freshPayload_spec h).2 p hp]

theorem freshPayload_flipBy (c : ι → Bool) (H : α × ι → Bool) :
    freshPayload (flipBy t c H) t = freshPayload H t := by
  unfold freshPayload
  rw [run_flipBy]

theorem flipBy_involutive (c : ι → Bool) : Function.Involutive (flipBy t c) := by
  intro H
  rcases h : freshPayload H t with _ | ⟨x, ys⟩
  · rw [flipBy_of_none h, flipBy_of_none h]
  · have h' : freshPayload (flipBy t c H) t = some (x, ys) := by rw [freshPayload_flipBy, h]
    rw [flipBy_of_some h', flipBy_of_some h]
    funext p
    by_cases hp : p.1 = x <;> simp [hp]

variable [Fintype ι] [DecidableEq ι]

/-- For each `H`, at most one flip pattern `c` makes the test pass. -/
theorem sum_acceptsAll_flipBy_le (H : α × ι → Bool) :
    (∑ c : ι → Bool, if acceptsAll (flipBy t c H) t then (1 : ℝ) else 0) ≤ 1 := by
  rcases h : freshPayload H t with _ | ⟨x, ys⟩
  · have : ∀ c : ι → Bool, acceptsAll (flipBy t c H) t = false := fun c => by
      unfold acceptsAll; rw [freshPayload_flipBy, h]
    simp [this]
  · set c₀ : ι → Bool := fun j => xor (ys j) (H (x, j))
    have hc : ∀ c : ι → Bool, acceptsAll (flipBy t c H) t = true → c = c₀ := by
      intro c hacc
      unfold acceptsAll at hacc
      rw [freshPayload_flipBy, h, flipBy_of_some h] at hacc
      simp only [↓reduceIte, decide_eq_true_eq] at hacc
      funext j
      have := hacc j
      simp only [c₀, this]
      cases H (x, j) <;> cases c j <;> rfl
    calc (∑ c : ι → Bool, if acceptsAll (flipBy t c H) t then (1 : ℝ) else 0)
        ≤ ∑ c : ι → Bool, if c = c₀ then (1 : ℝ) else 0 :=
          Finset.sum_le_sum fun c _ => by
            by_cases hacc : acceptsAll (flipBy t c H) t = true
            · rw [ite_eq_left hacc, ite_eq_left (hc c hacc)]
            · rw [ite_eq_right hacc]
              split_ifs <;> norm_num
      _ = 1 := by simp

/-- Proof of `cor:allTV` (random case): if the final test checks the labels `H(x, j)` of all `r`
indices at a payload `x` that was not recorded during training, then at most a `2^{-r}` fraction
of all functions `H` pass, for every adaptive algorithm with fixed coins. -/
theorem card_acceptsAll_le [Fintype α] :
    (∑ H : α × ι → Bool, if acceptsAll H t then (1 : ℝ) else 0) * 2 ^ Fintype.card ι ≤
      Fintype.card (α × ι → Bool) := by
  have hperm : ∀ c : ι → Bool,
      (∑ H : α × ι → Bool, if acceptsAll H t then (1 : ℝ) else 0) =
        ∑ H : α × ι → Bool, if acceptsAll (flipBy t c H) t then (1 : ℝ) else 0 :=
    fun c => (Equiv.sum_comp (flipBy_involutive (t := t) c).toPerm
      (fun H => if acceptsAll H t then (1 : ℝ) else 0)).symm
  have hcard : (2 : ℝ) ^ Fintype.card ι = ∑ _c : ι → Bool, (1 : ℝ) := by
    simp [Fintype.card_bool]
  calc (∑ H : α × ι → Bool, if acceptsAll H t then (1 : ℝ) else 0) * 2 ^ Fintype.card ι
      = ∑ c : ι → Bool, ∑ H : α × ι → Bool,
          (if acceptsAll (flipBy t c H) t then (1 : ℝ) else 0) := by
        rw [hcard, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by rw [mul_one, hperm c]
    _ = ∑ H : α × ι → Bool, ∑ c : ι → Bool,
          (if acceptsAll (flipBy t c H) t then (1 : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ _H : α × ι → Bool, (1 : ℝ) :=
        Finset.sum_le_sum fun H _ => sum_acceptsAll_flipBy_le H
    _ = Fintype.card (α × ι → Bool) := by simp

/-- `cor:allTV` (random case) with coins drawn independently of `H`: the acceptance probability
for a uniformly random function is at most `2^{-r}`, `r = |ι|`. -/
theorem acceptsAll_prob_le [Fintype α] {Ω : Type*} [Fintype Ω]
    (t : Ω → QueryTree (α × ι) (Option (α × (ι → Bool)))) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) :
    ∑ ω, w ω * ((∑ H : α × ι → Bool, if acceptsAll H (t ω) then (1 : ℝ) else 0) /
      Fintype.card (α × ι → Bool)) ≤ (1 / 2) ^ Fintype.card ι := by
  have hc : (0 : ℝ) < Fintype.card (α × ι → Bool) := by exact_mod_cast Fintype.card_pos
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  calc ∑ ω, w ω * ((∑ H : α × ι → Bool, if acceptsAll H (t ω) then (1 : ℝ) else 0) /
        Fintype.card (α × ι → Bool))
      ≤ ∑ ω, w ω * (1 / 2) ^ Fintype.card ι := Finset.sum_le_sum fun ω _ => by
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        rw [div_le_iff₀ hc, one_div_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ h2]
        exact card_acceptsAll_le
    _ = (1 / 2) ^ Fintype.card ι := by rw [← Finset.sum_mul, hw1, one_mul]

end MultiLabel

end QueryTree

/-- The accounting of `cor:allTV`: real-teacher acceptance at least
`(1-δ)[(1-η)^{r(L+1)}(1 - q/2^m) - ε]`, a transfer loss of at most `qη`, and random-function
acceptance at most `2^{-r}` give the displayed advantage bound. -/
theorem weak_reduction_accounting {m L r : ℕ} {ε δ η q accReal accSim accRand : ℝ}
    (hReal : (1 - δ) * ((1 - η) ^ (r * (L + 1)) * (1 - q / 2 ^ m) - ε) ≤ accReal)
    (hSim : accReal - q * η ≤ accSim) (hRand : accRand ≤ (1 / 2) ^ r) :
    weakAdvantage m L r ε δ η q ≤ accSim - accRand := by
  unfold weakAdvantage
  linarith

end LowLogitRank.Hardness
