import LowLogitRank.Spanner.Prob

/-!
# Hoeffding's inequality for adapted indicators (`sec:gls-validation-arithmetic`)

A finite sequential process: at each round, after the past outcomes `h : List β`, the next outcome
has law `q h`, a probability vector on the finite type `β`. The joint probability of the outcomes
`f` after the past `h` is `seqProb q h f`. The indicator of round `k` is `1[ω_{1:k} ∈ I]`, a
function of the history through round `k`. If its conditional mean given every past of positive
probability is at least `1/2`, then `Pr{∑_{k ≤ K} I_k < K/3} ≤ e^{-K/18}`.

In the paper, a round is an epoch (its spanner samples and validation samples) and `I_k = 1` if
the epoch's spanners are invalid or all validation programs are feasible. The paper conditions on
the pre-validation past, which is finer; averaging over the epoch's spanner samples gives the
conditional mean bound used here.
-/

namespace LowLogitRank.Spanner

open Finset

variable {β : Type*}

/-- The probability of the outcomes `f` after the past `h`, by the sequential product rule. -/
def seqProb (q : List β → β → ℝ) : List β → List β → ℝ
  | _, [] => 1
  | h, b :: f => q h b * seqProb q (h ++ [b]) f

@[simp] theorem seqProb_nil (q : List β → β → ℝ) (h : List β) : seqProb q h [] = 1 := rfl

@[simp] theorem seqProb_cons (q : List β → β → ℝ) (h : List β) (b : β) (f : List β) :
    seqProb q h (b :: f) = q h b * seqProb q (h ++ [b]) f := rfl

theorem seqProb_append (q : List β → β → ℝ) (h f g : List β) :
    seqProb q h (f ++ g) = seqProb q h f * seqProb q (h ++ f) g := by
  induction f generalizing h with
  | nil => simp
  | cons b f ih => simp [ih, mul_assoc]

theorem seqProb_nonneg (q : List β → β → ℝ) (K : ℕ)
    (hq0 : ∀ h : List β, h.length < K → ∀ b, 0 ≤ q h b) :
    ∀ (f h : List β), h.length + f.length ≤ K → 0 ≤ seqProb q h f := by
  intro f
  induction f with
  | nil => intro h _; simp
  | cons b f ih =>
    intro h hl
    simp only [List.length_cons] at hl
    rw [seqProb_cons]
    exact mul_nonneg (hq0 h (by omega) b) (ih _ (by simp; omega))

/-- Sums over `β^{n+1}` split off the first outcome. -/
theorem sum_vector_succ [Fintype β] {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : List.Vector β (n + 1) → M) :
    ∑ v, F v = ∑ b : β, ∑ v : List.Vector β n, F (List.Vector.cons b v) := by
  let e : β × List.Vector β n ≃ List.Vector β (n + 1) :=
    { toFun := fun x => List.Vector.cons x.1 x.2
      invFun := fun v => (v.head, v.tail)
      left_inv := fun x => by simp
      right_inv := fun v => by simp }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  rfl

/-- The indicator `1[h ∈ I]` as a real number. -/
noncomputable def ind (I : Set (List β)) (h : List β) : ℝ := I.indicator (fun _ => (1 : ℝ)) h

theorem ind_eq_zero_or_one (I : Set (List β)) (h : List β) : ind I h = 0 ∨ ind I h = 1 := by
  classical
  unfold ind
  by_cases hh : h ∈ I
  · right; exact Set.indicator_of_mem hh _
  · left; exact Set.indicator_of_notMem hh _

variable [Fintype β]

/-- One round: if `I_k ∈ {0,1}` has conditional mean at least `1/2` and `a ≥ 0`, then
`E[e^{-a (I_k - 1/2)} | past] ≤ cosh (a/2)`. -/
theorem cond_moment_le (q : β → ℝ) (hq1 : ∑ b, q b = 1) (Y : β → ℝ)
    (hY : ∀ b, Y b = 0 ∨ Y b = 1) (hmean : 1 / 2 ≤ ∑ b, q b * Y b) {a : ℝ} (ha : 0 ≤ a) :
    ∑ b, q b * Real.exp (-a * (Y b - 1 / 2)) ≤ Real.cosh (a / 2) := by
  have hpt : ∀ b, Real.exp (-a * (Y b - 1 / 2)) =
      Real.exp (a / 2) - Y b * (Real.exp (a / 2) - Real.exp (-(a / 2))) := by
    intro b
    rcases hY b with h | h <;> rw [h] <;> ring_nf
  have hgap : 0 ≤ Real.exp (a / 2) - Real.exp (-(a / 2)) := by
    have : Real.exp (-(a / 2)) ≤ Real.exp (a / 2) := Real.exp_le_exp.mpr (by linarith)
    linarith
  simp_rw [hpt]
  have : ∑ b, q b * (Real.exp (a / 2) - Y b * (Real.exp (a / 2) - Real.exp (-(a / 2)))) =
      Real.exp (a / 2) * ∑ b, q b -
        (Real.exp (a / 2) - Real.exp (-(a / 2))) * ∑ b, q b * Y b := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [this, hq1, Real.cosh_eq]
  nlinarith

/-- Averaging over a first stage within a round: if, given every first-stage outcome `s`, the
second-stage conditional mean of `Y` is at least `1/2`, so is the mean over the whole round. This
passes from the paper's conditioning on the pre-validation past (`s` = the epoch's spanner
samples) to the conditioning on previous rounds used in `adapted_hoeffding`. -/
theorem mean_two_stage {σ τ : Type*} [Fintype σ] [Fintype τ] (q₁ : σ → ℝ) (q₂ : σ → τ → ℝ)
    (Y : σ × τ → ℝ) (h0 : ∀ s, 0 ≤ q₁ s) (h1 : ∑ s, q₁ s = 1)
    (hY : ∀ s, 1 / 2 ≤ ∑ v, q₂ s v * Y (s, v)) :
    1 / 2 ≤ ∑ p : σ × τ, q₁ p.1 * q₂ p.1 p.2 * Y p := by
  rw [Fintype.sum_prod_type]
  calc (1 / 2 : ℝ) = ∑ s, q₁ s * (1 / 2) := by rw [← Finset.sum_mul, h1, one_mul]
    _ ≤ ∑ s, q₁ s * ∑ v, q₂ s v * Y (s, v) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hY s) (h0 s)
    _ = _ := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring

/-- The exponential moment of the centered count of the next `n` rounds after the past `h`. -/
noncomputable def expMoment (q : List β → β → ℝ) (I : Set (List β)) (a : ℝ) (h : List β)
    (n : ℕ) : ℝ :=
  ∑ f : List.Vector β n, seqProb q h f.toList *
    Real.exp (-a * ∑ k ∈ range n, (ind I (h ++ f.toList.take (k + 1)) - 1 / 2))

theorem expMoment_succ (q : List β → β → ℝ) (I : Set (List β)) (a : ℝ) (h : List β) (n : ℕ) :
    expMoment q I a h (n + 1) = ∑ b, q h b * Real.exp (-a * (ind I (h ++ [b]) - 1 / 2)) *
      expMoment q I a (h ++ [b]) n := by
  unfold expMoment
  rw [sum_vector_succ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [List.Vector.toList_cons, seqProb_cons]
  rw [Finset.sum_range_succ']
  have hshift : ∀ k ∈ range n, ind I (h ++ (b :: f.toList).take (k + 1 + 1)) - 1 / 2 =
      ind I (h ++ [b] ++ f.toList.take (k + 1)) - 1 / 2 := by
    intro k _
    simp [List.take_succ_cons]
  rw [Finset.sum_congr rfl hshift]
  simp only [zero_add, List.take_succ_cons, List.take_zero]
  rw [mul_add, Real.exp_add]
  ring

/-- `sec:gls-validation-arithmetic`, exponential moment: under the adapted mean condition,
`P(h) · E[∏_k e^{-a(I_k - 1/2)} | h] ≤ P(h) · cosh(a/2)^n` for the next `n` rounds. -/
theorem expMoment_le (K : ℕ) (q : List β → β → ℝ) (I : Set (List β))
    (hq0 : ∀ h : List β, h.length < K → ∀ b, 0 ≤ q h b)
    (hq1 : ∀ h : List β, h.length < K → ∑ b, q h b = 1)
    (hI : ∀ h : List β, h.length < K → 0 < seqProb q [] h →
      1 / 2 ≤ ∑ b, q h b * ind I (h ++ [b]))
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ (n : ℕ) (h : List β), h.length + n ≤ K →
      seqProb q [] h * expMoment q I a h n ≤ seqProb q [] h * Real.cosh (a / 2) ^ n := by
  intro n
  induction n with
  | zero =>
    intro h _
    simp [expMoment]
  | succ n ih =>
    intro h hl
    have hP : 0 ≤ seqProb q [] h := seqProb_nonneg q K hq0 h [] (by simp; omega)
    have hchild : ∀ b, seqProb q [] (h ++ [b]) = seqProb q [] h * q h b := by
      intro b; rw [seqProb_append]; simp
    have hc : 0 ≤ Real.cosh (a / 2) ^ n := pow_nonneg (Real.cosh_pos _).le _
    rw [expMoment_succ, Finset.mul_sum]
    calc ∑ b, seqProb q [] h * (q h b * Real.exp (-a * (ind I (h ++ [b]) - 1 / 2)) *
          expMoment q I a (h ++ [b]) n)
        = ∑ b, Real.exp (-a * (ind I (h ++ [b]) - 1 / 2)) *
            (seqProb q [] (h ++ [b]) * expMoment q I a (h ++ [b]) n) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hchild]; ring
      _ ≤ ∑ b, Real.exp (-a * (ind I (h ++ [b]) - 1 / 2)) *
            (seqProb q [] (h ++ [b]) * Real.cosh (a / 2) ^ n) := by
          refine Finset.sum_le_sum fun b _ => ?_
          exact mul_le_mul_of_nonneg_left (ih _ (by simp; omega)) (Real.exp_pos _).le
      _ = seqProb q [] h * Real.cosh (a / 2) ^ n *
            ∑ b, q h b * Real.exp (-a * (ind I (h ++ [b]) - 1 / 2)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hchild]; ring
      _ ≤ seqProb q [] h * Real.cosh (a / 2) ^ (n + 1) := by
          rcases hP.eq_or_lt with h0 | hpos
          · rw [← h0]; simp
          · rw [pow_succ, ← mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hP hc)
            exact cond_moment_le (q h) (hq1 h (by omega)) (fun b => ind I (h ++ [b]))
              (fun b => ind_eq_zero_or_one I _) (hI h (by omega) hpos) ha

/-- `sec:gls-validation-arithmetic`, exponential moment from the root:
`E[∏_{k ≤ K} e^{-a (I_k - 1/2)}] ≤ cosh(a/2)^K ≤ e^{K a² / 8}` for `a ≥ 0`. -/
theorem expMoment_root_le (K : ℕ) (q : List β → β → ℝ) (I : Set (List β))
    (hq0 : ∀ h : List β, h.length < K → ∀ b, 0 ≤ q h b)
    (hq1 : ∀ h : List β, h.length < K → ∑ b, q h b = 1)
    (hI : ∀ h : List β, h.length < K → 0 < seqProb q [] h →
      1 / 2 ≤ ∑ b, q h b * ind I (h ++ [b]))
    {a : ℝ} (ha : 0 ≤ a) :
    expMoment q I a [] K ≤ Real.cosh (a / 2) ^ K ∧
      Real.cosh (a / 2) ^ K ≤ Real.exp (K * a ^ 2 / 8) := by
  constructor
  · have := expMoment_le K q I hq0 hq1 hI ha K [] (by simp)
    simpa using this
  · calc Real.cosh (a / 2) ^ K ≤ Real.exp ((a / 2) ^ 2 / 2) ^ K :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) K
      _ = Real.exp (K * a ^ 2 / 8) := by rw [← Real.exp_nat_mul]; ring_nf

/-- `sec:gls-validation-arithmetic`, adapted-indicator Hoeffding bound. For a finite sequential
process whose round-`k` indicator `I_k = 1[ω_{1:k} ∈ I]` has conditional mean at least `1/2`
given every past of positive probability,
`Pr{∑_{k=1}^K I_k < K/3} ≤ e^{-K/18}`. -/
theorem adapted_hoeffding (K : ℕ) (q : List β → β → ℝ) (I : Set (List β))
    (hq0 : ∀ h : List β, h.length < K → ∀ b, 0 ≤ q h b)
    (hq1 : ∀ h : List β, h.length < K → ∑ b, q h b = 1)
    (hI : ∀ h : List β, h.length < K → 0 < seqProb q [] h →
      1 / 2 ≤ ∑ b, q h b * ind I (h ++ [b])) :
    wprob (fun ω : List.Vector β K => seqProb q [] ω.toList)
        {ω | ∑ k ∈ range K, ind I (ω.toList.take (k + 1)) < (K : ℝ) / 3} ≤
      Real.exp (-((K : ℝ) / 18)) := by
  classical
  set a : ℝ := 2 / 3
  have hmom := expMoment_le K q I hq0 hq1 hI (a := a) (by norm_num) K [] (by simp)
  simp only [seqProb_nil, one_mul] at hmom
  have hP : ∀ ω : List.Vector β K, 0 ≤ seqProb q [] ω.toList := fun ω =>
    seqProb_nonneg q K hq0 _ [] (by simp)
  -- Markov's inequality for the exponential moment
  have hpt : ∀ ω : List.Vector β K,
      {ω : List.Vector β K | ∑ k ∈ range K, ind I (ω.toList.take (k + 1)) < (K : ℝ) / 3}.indicator
        (fun ω => seqProb q [] ω.toList) ω ≤
      Real.exp (-(a * K / 6)) * (seqProb q [] ω.toList *
        Real.exp (-a * ∑ k ∈ range K, (ind I ([] ++ ω.toList.take (k + 1)) - 1 / 2))) := by
    intro ω
    have hsum : ∑ k ∈ range K, (ind I ([] ++ ω.toList.take (k + 1)) - 1 / 2) =
        ∑ k ∈ range K, ind I (ω.toList.take (k + 1)) - K / 2 := by
      rw [Finset.sum_sub_distrib]; simp; ring
    rw [hsum]
    by_cases hω : ∑ k ∈ range K, ind I (ω.toList.take (k + 1)) < (K : ℝ) / 3
    · rw [Set.indicator_of_mem (show ω ∈ {ω : List.Vector β K |
        ∑ k ∈ range K, ind I (ω.toList.take (k + 1)) < (K : ℝ) / 3} from hω)]
      have h1 : 1 ≤ Real.exp (-(a * K / 6)) *
          Real.exp (-a * (∑ k ∈ range K, ind I (ω.toList.take (k + 1)) - K / 2)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        simp only [a]
        linarith
      nlinarith [hP ω]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω : List.Vector β K |
        ∑ k ∈ range K, ind I (ω.toList.take (k + 1)) < (K : ℝ) / 3} from hω)]
      have := hP ω
      positivity
  calc _ ≤ ∑ ω : List.Vector β K, Real.exp (-(a * K / 6)) * (seqProb q [] ω.toList *
        Real.exp (-a * ∑ k ∈ range K, (ind I ([] ++ ω.toList.take (k + 1)) - 1 / 2))) :=
        Finset.sum_le_sum fun ω _ => hpt ω
    _ = Real.exp (-(a * K / 6)) * expMoment q I a [] K := by
        rw [← Finset.mul_sum]; rfl
    _ ≤ Real.exp (-(a * K / 6)) * Real.cosh (a / 2) ^ K :=
        mul_le_mul_of_nonneg_left hmom (Real.exp_pos _).le
    _ ≤ Real.exp (-(a * K / 6)) * Real.exp ((a / 2) ^ 2 / 2) ^ K := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) K
    _ = Real.exp (-((K : ℝ) / 18)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        simp only [a]
        ring

end LowLogitRank.Spanner
