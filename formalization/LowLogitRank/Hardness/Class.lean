import LowLogitRank.Hardness.State

/-!
# `lem:hard-teacher`, the rank lower bound, and the label behavior

* `teacher_logitClass`, `hardTeacher_inClass`: the teacher belongs to `𝒞_{T,n+7}`.
* `hardTeacher_odds`, `hardTeacher_rational`: every logit is `Bm` with an integer `|m| ≤ 2L+1`,
  the odds are `2^{2nm}`, and the probabilities are ratios of integers below `2^{2n(2L+1)} + 1`.
* `teacher_rank_ge`: the remark after `lem:hard-teacher`, rank at least `n` at cut `n`.
* `teacher_copy`, `teacher_label_consistent`, `teacher_label_inconsistent`: the label behavior
  stated after `eq:hard-mask`.
-/

namespace LowLogitRank.Hardness

open Finset Matrix

variable {n L : ℕ} (P : Program) (B : ℝ)

/-! ### Elementary values of the logistic function -/

theorem sigmoid_zero : sigmoid 0 = 1 / 2 := by
  simp [sigmoid]
  norm_num

theorem sigmoid_neg_two_mul (B : ℝ) : sigmoid (-(2 * B)) = etaOf B := by
  simp [sigmoid, etaOf]

theorem sigmoid_two_mul (B : ℝ) : sigmoid (2 * B) = 1 - etaOf B := by
  rw [← sigmoid_neg_two_mul, ← one_sub_sigmoid]
  ring

theorem etaOf_pos (B : ℝ) : 0 < etaOf B := by
  unfold etaOf; positivity

theorem etaOf_lt_one (B : ℝ) : etaOf B < 1 := by
  rw [← sigmoid_neg_two_mul]; exact sigmoid_lt_one _

/-- For `B = n log 2`, the copy error is `η = (1 + 2^{2n})⁻¹`. -/
theorem etaOf_hardB (n : ℕ) : etaOf (hardB n) = hardEta n := by
  unfold etaOf hardB hardEta
  congr 2
  rw [show 2 * ((n : ℝ) * Real.log 2) = ((2 * n : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
    Real.exp_nat_mul, Real.exp_log two_pos]

theorem hardEta_pos (n : ℕ) : 0 < hardEta n := by
  unfold hardEta; positivity

/-- `η ≤ 2^{-2n}`. -/
theorem hardEta_le (n : ℕ) : hardEta n ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by
  unfold hardEta
  apply inv_anti₀ (by positivity)
  linarith

theorem hardB_nonneg (n : ℕ) : 0 ≤ hardB n := by
  unfold hardB; have := Real.log_pos one_lt_two; positivity

/-! ### Logit values -/

theorem logit_teacher : logit (teacher n L P B) = teacherLogit n L P B :=
  funext (logit_ofLogit _)

theorem teacher_apply (h : List Bool) : teacher n L P B h = sigmoid (2 * teacherLogit n L P B h) :=
  rfl

theorem teacherLogit_input (h : List Bool) (hh : h.length < n) : teacherLogit n L P B h = 0 := by
  simp [teacherLogit, hh]

theorem teacherLogit_copy (h : List Bool) (h1 : n ≤ h.length) (h2 : h.length < n + L) :
    teacherLogit n L P B h = B * (2 * bitValue (h.getD (sched n (h.length - n)) false) - 1) := by
  simp [teacherLogit, h2, show ¬ h.length < n by omega]

theorem teacherLogit_label (h : List Bool) (hh : h.length = n + L) :
    teacherLogit n L P B h = B * (2 * (mismatchCount n L (inputOf n h) (copyOf n L h) : ℝ) +
      P.response (copyOf n L h).toList) := by
  simp [teacherLogit, hh]

theorem teacherLogit_padding (h : List Bool) (hh : n + L < h.length) :
    teacherLogit n L P B h = 0 := by
  simp [teacherLogit, show ¬ h.length < n by omega, show ¬ h.length < n + L by omega,
    show h.length ≠ n + L by omega]

/-- Input and padding bits are fair. -/
theorem teacher_fair (h : List Bool) (hh : h.length < n ∨ n + L < h.length) :
    teacher n L P B h = 1 / 2 := by
  rcases hh with hh | hh
  · rw [teacher_apply, teacherLogit_input P B h hh, mul_zero, sigmoid_zero]
  · rw [teacher_apply, teacherLogit_padding P B h hh, mul_zero, sigmoid_zero]

/-- One mismatch makes the mask positive for either readout: `C ≥ 1` gives `2C + R(A) ≥ 1`. -/
theorem one_le_mask {C : ℕ} (hC : 1 ≤ C) (a : List Bool) :
    1 ≤ 2 * (C : ℝ) + P.response a := by
  have : (1 : ℝ) ≤ C := by exact_mod_cast hC
  rcases P.response_mem a with h | h <;> rw [h] <;> linarith

/-! ### The logit bound and `lem:hard-teacher` -/

/-- `|ℓ(h)| ≤ B(2L + 1)` on every prefix. -/
theorem abs_teacherLogit_le (hB : 0 ≤ B) (h : List Bool) :
    |teacherLogit n L P B h| ≤ B * (2 * L + 1) := by
  have hBL : 0 ≤ B * (2 * L + 1) := by positivity
  unfold teacherLogit
  split_ifs with h1 h2 h3
  · simpa using hBL
  · rw [abs_mul, abs_of_nonneg hB]
    apply mul_le_mul_of_nonneg_left _ hB
    cases h.getD (sched n (h.length - n)) false <;> norm_num
  · rw [abs_mul, abs_of_nonneg hB]
    apply mul_le_mul_of_nonneg_left _ hB
    have hC : (mismatchCount n L (inputOf n h) (copyOf n L h) : ℝ) ≤ L := by
      exact_mod_cast mismatchCount_le (inputOf n h) (copyOf n L h)
    have hC0 : (0 : ℝ) ≤ mismatchCount n L (inputOf n h) (copyOf n L h) := Nat.cast_nonneg _
    rcases P.response_mem (copyOf n L h).toList with hr | hr <;> rw [hr, abs_le] <;>
      constructor <;> linarith
  · simpa using hBL

/-- `lem:hard-teacher` for a general scale `B ≥ 0`: full support, `|ℓ| ≤ B(2L+1)`, and rank at
most `n + 7` at every cut. -/
theorem teacher_logitClass (hn : 0 < n) (hB : 0 ≤ B) (T : ℕ) :
    LogitClass T (B * (2 * L + 1)) (n + 7) (teacher n L P B) where
  fullSupport := ofLogit_fullSupport _ _
  logit_le h _ := by rw [logit_teacher]; exact abs_teacherLogit_le P B hB h
  rank_le t _ := by rw [logit_teacher]; exact teacherLogit_rank_le P B hn T t

/-- The teacher is in `𝒞_{T,n+7}` whenever `B(2L + 1) ≤ T`. -/
theorem teacher_inClass (hn : 0 < n) (hB : 0 ≤ B) (T : ℕ) (hT : B * (2 * L + 1) ≤ T) :
    InClass T (n + 7) (teacher n L P B) where
  fullSupport := ofLogit_fullSupport _ _
  logit_le h _ := by rw [logit_teacher]; exact (abs_teacherLogit_le P B hB h).trans hT
  rank_le t _ := by rw [logit_teacher]; exact teacherLogit_rank_le P B hn T t

/-- `n log 2 (2L + 1) < 2n(L + 1) = T`. -/
theorem hardB_mul_lt (hn : 1 ≤ n) : hardB n * (2 * L + 1) < hardT n L := by
  unfold hardB hardT
  have hlog : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  have h2L : (0 : ℝ) < 2 * L + 1 := by positivity
  have h1 : (n : ℝ) * Real.log 2 * (2 * L + 1) < n * 1 * (2 * L + 1) :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hlog (by positivity)) h2L
  linarith

/-- `lem:hard-teacher`: for `n ≥ 1`, `B = n log 2` and `T = 2n(L + 1)`, the teacher belongs to
`𝒞_{T,n+7}`. -/
theorem hardTeacher_inClass (hn : 1 ≤ n) : InClass (hardT n L) (n + 7) (hardTeacher n L P) :=
  teacher_inClass P _ hn (hardB_nonneg n) _ (hardB_mul_lt hn).le

/-- `lem:hard-teacher`: the strict logit bound `|ℓ_P(h)| ≤ n log 2 (2L+1) < T`. -/
theorem hardTeacher_abs_logit_lt (hn : 1 ≤ n) (h : List Bool) :
    |logit (hardTeacher n L P) h| ≤ hardB n * (2 * L + 1) ∧
      |logit (hardTeacher n L P) h| < hardT n L := by
  have := abs_teacherLogit_le (n := n) (L := L) P (hardB n) (hardB_nonneg n) h
  rw [hardTeacher, logit_teacher]
  exact ⟨this, this.trans_lt (hardB_mul_lt hn)⟩

/-- For the paper's range `n ≥ 32`, the parameters fall under `thm:hardness`:
`T ≥ 32` and `1 ≤ d = n + 7 ≤ T^2`. -/
theorem hardT_params (hn : 32 ≤ n) :
    32 ≤ hardT n L ∧ 1 ≤ n + 7 ∧ n + 7 ≤ hardT n L ^ 2 := by
  unfold hardT
  have h1 : 32 ≤ 2 * n * (L + 1) := by nlinarith
  refine ⟨h1, by omega, ?_⟩
  calc n + 7 ≤ 2 * n * (L + 1) := by nlinarith
    _ ≤ (2 * n * (L + 1)) ^ 2 := Nat.le_self_pow two_ne_zero _

/-! ### Rationality -/

/-- Every logit is `Bm` for an integer `|m| ≤ 2L + 1`. -/
theorem teacherLogit_eq_int_mul (h : List Bool) :
    ∃ m : ℤ, |m| ≤ 2 * L + 1 ∧ teacherLogit n L P B h = B * m := by
  unfold teacherLogit
  split_ifs with h1 h2 h3
  · exact ⟨0, by positivity, by simp⟩
  · cases h.getD (sched n (h.length - n)) false
    · exact ⟨-1, by simp, by simp⟩
    · exact ⟨1, by simp, by simp; norm_num⟩
  · have hC := mismatchCount_le (inputOf n h) (copyOf n L h)
    rcases P.response_mem (copyOf n L h).toList with hr | hr
    · refine ⟨2 * mismatchCount n L (inputOf n h) (copyOf n L h) + 1, ?_,
        by rw [hr]; push_cast; ring⟩
      rw [abs_le]; constructor <;> omega
    · refine ⟨2 * mismatchCount n L (inputOf n h) (copyOf n L h) - 1, ?_,
        by rw [hr]; push_cast; ring⟩
      rw [abs_le]; constructor <;> omega
  · exact ⟨0, by positivity, by simp⟩

/-- `lem:hard-teacher` (rationality): every logit of `P_k` is `Bm` with an integer
`|m| ≤ 2L + 1`, and the conditional odds are `p/(1-p) = 2^{2nm}`. -/
theorem hardTeacher_odds (h : List Bool) :
    ∃ m : ℤ, |m| ≤ 2 * L + 1 ∧ logit (hardTeacher n L P) h = hardB n * m ∧
      hardTeacher n L P h / (1 - hardTeacher n L P h) = (2 : ℝ) ^ (2 * n * m) := by
  obtain ⟨m, hm, hℓ⟩ := teacherLogit_eq_int_mul P (hardB n) (n := n) (L := L) h
  refine ⟨m, hm, by rw [hardTeacher, logit_teacher, hℓ], ?_⟩
  rw [hardTeacher, teacher_apply, sigmoid_div_one_sub, hℓ, ← Real.rpow_intCast,
    Real.rpow_def_of_pos two_pos, hardB]
  congr 1
  push_cast
  ring

/-- `lem:hard-teacher` (bit length): every conditional probability is `a / b` with integers
`0 < a < b ≤ 2^{2n(2L+1)} + 1`. -/
theorem hardTeacher_rational (h : List Bool) :
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ b ≤ 2 ^ (2 * n * (2 * L + 1)) + 1 ∧
      hardTeacher n L P h = a / b := by
  obtain ⟨m, hm, -, hodds⟩ := hardTeacher_odds P (n := n) (L := L) h
  set p := hardTeacher n L P h
  have hp1 : p < 1 := sigmoid_lt_one _
  have hp : p = 2 ^ (2 * n * m) / (1 + 2 ^ (2 * n * m)) := by
    rw [← hodds]
    have : 1 - p ≠ 0 := by linarith
    field_simp
    ring
  have hk : |(2 * n * m : ℤ)| ≤ 2 * n * (2 * L + 1) := by
    rw [abs_mul]
    have : |(2 * n : ℤ)| = 2 * n := abs_of_nonneg (by positivity)
    rw [this]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  obtain ⟨j, hj | hj⟩ := Int.eq_nat_or_neg (2 * n * m)
  · have hjle : j ≤ 2 * n * (2 * L + 1) := by
      rw [hj] at hk; simp only [Nat.abs_cast] at hk; exact_mod_cast hk
    refine ⟨2 ^ j, 2 ^ j + 1, by positivity, by omega,
      by have := Nat.pow_le_pow_right two_pos hjle; omega, ?_⟩
    rw [hp, hj, zpow_natCast]
    push_cast
    ring
  · have hjle : j ≤ 2 * n * (2 * L + 1) := by
      rw [hj] at hk; simp only [abs_neg, Nat.abs_cast] at hk; exact_mod_cast hk
    refine ⟨1, 2 ^ j + 1, one_pos, by have := Nat.one_le_two_pow (n := j); omega,
      by have := Nat.pow_le_pow_right two_pos hjle; omega, ?_⟩
    rw [hp, hj, _root_.zpow_neg, zpow_natCast]
    have : (0 : ℝ) < 2 ^ j := by positivity
    field_simp
    push_cast
    ring

/-- `lem:hard-teacher` (bit length, in terms of `T`): for `n ≥ 1` every conditional probability
is `a / b` with integers `0 < a < b < 2^{2T}`, i.e. numerators and denominators of at most `2T`
bits. -/
theorem hardTeacher_rational_bits (hn : 1 ≤ n) (h : List Bool) :
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ b < 2 ^ (2 * hardT n L) ∧ hardTeacher n L P h = a / b := by
  obtain ⟨a, b, ha, hab, hb, hp⟩ := hardTeacher_rational P (n := n) (L := L) h
  refine ⟨a, b, ha, hab, ?_, hp⟩
  have hk : 2 * n * (2 * L + 1) + 1 < 2 * hardT n L := by unfold hardT; nlinarith
  have h1 : 2 ^ (2 * n * (2 * L + 1)) + 1 ≤ 2 ^ (2 * n * (2 * L + 1) + 1) := by
    rw [pow_succ]; have := Nat.one_le_two_pow (n := 2 * n * (2 * L + 1)); omega
  have h2 := Nat.pow_lt_pow_right (a := 2) one_lt_two hk
  omega

/-! ### The rank lower bound -/

/-- The remark after `lem:hard-teacher`: at cut `n`, the columns of the futures `0^i`,
`0 ≤ i < n`, are `B(2X_{i+1} - 1)` (the logits at the copies of the first sweep). They are
linearly independent functions of `X ∈ {0,1}^n`, so the cut-`n` logit matrix has rank at least
`n`. Here `L ≥ n` provides the first sweep and `2n ≤ T` makes these futures legal. -/
theorem teacher_rank_ge (hL : n ≤ L) (hB : B ≠ 0) (T : ℕ) (hT : 2 * n ≤ T) :
    n ≤ (logitCutMatrix (logit (teacher n L P B)) T n).rank := by
  rw [logit_teacher]
  set M := logitCutMatrix (teacherLogit n L P B) T n
  let col : Fin n → ShortWord (T - n) := fun i => ⟨⟨i, by omega⟩, List.Vector.replicate i false⟩
  let v : Fin n → (Word n → ℝ) := fun i => M.col (col i)
  have hv : ∀ i x, v i x = B * (2 * bitValue (x.get i) - 1) := by
    intro i x
    change teacherLogit n L P B (x.toList ++ (List.Vector.replicate i false).toList) = _
    have hlen : (x.toList ++ (List.Vector.replicate (i : ℕ) false).toList).length = n + i := by
      simp
    rw [teacherLogit_copy P B _ (by omega) (by omega), hlen,
      show sched n (n + i - n) = i by simp [sched, Nat.mod_eq_of_lt i.isLt],
      getD_append_of_lt (by simp), List.getD_eq_getElem _ _ (by simp),
      List.Vector.get_eq_get_toList]
    rfl
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    let x0 : Word n := List.Vector.replicate n false
    let ek : Word n := List.Vector.ofFn fun i => decide (i = k)
    have h0 := congrFun hg x0
    have h1 := congrFun hg ek
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv, Pi.zero_apply] at h0 h1
    have hterm : ∀ i, g i * (B * (2 * bitValue (ek.get i) - 1)) -
        g i * (B * (2 * bitValue (x0.get i) - 1)) = if i = k then 2 * B * g k else 0 := by
      intro i
      by_cases hik : i = k
      · subst hik
        simp [ek, x0, List.Vector.get_ofFn, List.Vector.get_replicate]
        ring
      · simp [ek, x0, List.Vector.get_ofFn, List.Vector.get_replicate, hik]
    have key := congrArg₂ (· - ·) h1 h0
    simp only [sub_zero, ← Finset.sum_sub_distrib, hterm, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at key
    have h2B : (2 : ℝ) * B ≠ 0 := mul_ne_zero two_ne_zero hB
    simpa [h2B] using key
  rw [Matrix.rank_eq_finrank_span_cols]
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range M.col)) :=
      Submodule.finrank_mono (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨col i, rfl⟩))

/-- The remark after `lem:hard-teacher` for the parameters of `eq:hard-parameters`: with
`L ≥ n ≥ 1`, the logit matrix of `P_k` at cut `n` has rank at least `n`. -/
theorem hardTeacher_rank_ge (hn : 1 ≤ n) (hL : n ≤ L) :
    n ≤ (logitCutMatrix (logit (hardTeacher n L P)) (hardT n L) n).rank := by
  apply teacher_rank_ge P _ hL
  · unfold hardB
    have : (0 : ℝ) < n := by exact_mod_cast hn
    have := Real.log_pos one_lt_two
    positivity
  · unfold hardT
    nlinarith

/-! ### Label and copy behavior -/

/-- Each copy bit equals its scheduled input bit `X_{i_j}` with probability `1 - η`. -/
theorem teacher_copy (h : List Bool) (h1 : n ≤ h.length) (h2 : h.length < n + L) :
    bitProb (teacher n L P B) h (h.getD (sched n (h.length - n)) false) = 1 - etaOf B := by
  rw [bitProb, teacher_apply, teacherLogit_copy P B h h1 h2]
  cases h.getD (sched n (h.length - n)) false
  · simp only [Bool.false_eq_true, ↓reduceIte, bitValue_false]
    rw [show 2 * (B * (2 * 0 - 1)) = -(2 * B) by ring, sigmoid_neg_two_mul]
  · simp only [↓reduceIte, bitValue_true]
    rw [show 2 * (B * (2 * 1 - 1)) = 2 * B by ring, sigmoid_two_mul]

/-- Under `eq:hard-consistency`, at a label prefix with `C = 0` the label equals `F(X)` with
probability `1 - η`. -/
theorem teacher_label_consistent {F : Word n → Bool} (hcons : Consistent n L P F)
    (h : List Bool) (hh : h.length = n + L)
    (hC : mismatchCount n L (inputOf n h) (copyOf n L h) = 0) :
    bitProb (teacher n L P B) h (F (inputOf n h)) = 1 - etaOf B := by
  rw [mismatchCount_eq_zero_iff] at hC
  have hℓ := teacherLogit_label P B h hh
  rw [hC, mismatchCount_consistent, hcons] at hℓ
  rw [bitProb, teacher_apply, hℓ]
  cases F (inputOf n h)
  · simp only [Bool.false_eq_true, ↓reduceIte, bitValue_false]
    rw [show 2 * (B * (2 * ((0 : ℕ) : ℝ) + (2 * 0 - 1))) = -(2 * B) by push_cast; ring,
      sigmoid_neg_two_mul]
  · simp only [↓reduceIte, bitValue_true]
    rw [show 2 * (B * (2 * ((0 : ℕ) : ℝ) + (2 * 1 - 1))) = 2 * B by push_cast; ring,
      sigmoid_two_mul]

/-- At a label prefix with `C ≥ 1` the label is one with probability at least `1 - η`. -/
theorem teacher_label_inconsistent (hB : 0 ≤ B) (h : List Bool) (hh : h.length = n + L)
    (hC : 1 ≤ mismatchCount n L (inputOf n h) (copyOf n L h)) :
    1 - etaOf B ≤ teacher n L P B h := by
  rw [teacher_apply, teacherLogit_label P B h hh, ← sigmoid_two_mul]
  apply sigmoid_le_sigmoid
  have := one_le_mask P hC (copyOf n L h).toList
  nlinarith

end LowLogitRank.Hardness
