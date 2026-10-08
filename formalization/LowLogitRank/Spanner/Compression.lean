import LowLogitRank.Spanner.Prob

/-!
# Distributional spanners from sample compression (`lem:compression-spanner`)

The row law is finitely supported: a finite type `Ω` of outcomes with probability weights `D` and
a row map `x : Ω → V`. In the paper's use, the rows are the oracle rows of sampled histories, so
their law is the image of a law on a finite set of binary histories and is finitely supported.

`N` independent samples `ω : Fin N → Ω` carry the product weights `piW D`. For an index set `I`,
the covered set `C I (ω|_I)` may be any set determined by the samples indexed by `I`; the
zonotope `{∑_{i ∈ I} c_i x(ω_i) : |c_i| ≤ 2}` of the paper is one instance.
-/

namespace LowLogitRank.Spanner

open Finset

section Core

variable {Ω : Type*} [Fintype Ω]

/-- Restriction of a sample tuple to the coordinates in `S`. -/
def restr {ι : Type*} (S : Finset ι) (ω : ι → Ω) : S → Ω := fun i => ω i

/-- Compression for one fixed index set `S`: the samples outside `S` are independent of those in
`S`, so the probability that all of them fall in a set `A` determined by the samples in `S`, of
mass at most `q`, is at most `q ^ (card ι - #S)`. -/
theorem wprob_cover_le {ι : Type*} [Fintype ι] [DecidableEq ι] {D : Ω → ℝ} (hD : IsProb D)
    (S : Finset ι) (A : (S → Ω) → Set Ω) {q : ℝ} (hq : 0 ≤ q) :
    wprob (piW D) {ω : ι → Ω | (∀ j, j ∉ S → ω j ∈ A (restr S ω)) ∧
        wprob D (A (restr S ω)) ≤ q} ≤ q ^ (Fintype.card ι - S.card) := by
  classical
  set E := {ω : ι → Ω | (∀ j, j ∉ S → ω j ∈ A (restr S ω)) ∧ wprob D (A (restr S ω)) ≤ q}
  set e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Ω)
  have hrestr : ∀ a b, restr S (e.symm (a, b)) = a := by
    intro a b; funext i; simp [restr, e, Equiv.piEquivPiSubtypeProd, i.2]
  have hout : ∀ a b (j : ι) (hj : j ∉ S), e.symm (a, b) j = b ⟨j, hj⟩ := by
    intro a b j hj; simp [e, Equiv.piEquivPiSubtypeProd, hj]
  have hin : ∀ a b (i : {x // x ∈ S}), e.symm (a, b) i = a i := by
    intro a b i; simp [e, Equiv.piEquivPiSubtypeProd, i.2]
  have key : ∀ a b, E.indicator (piW D) (e.symm (a, b)) =
      if wprob D (A a) ≤ q then (∏ i, D (a i)) * ∏ j, (A a).indicator D (b j) else 0 := by
    intro a b
    have hsplit : piW D (e.symm (a, b)) =
        (∏ i : {x // x ∈ S}, D (a i)) * ∏ j : {x // x ∉ S}, D (b j) := by
      rw [piW, ← Fintype.prod_subtype_mul_prod_subtype (fun x => x ∈ S)]
      congr 1
      · convert Finset.prod_congr rfl fun i _ => congrArg D (hin a b i)
      · exact Finset.prod_congr rfl fun j _ => congrArg D (hout a b j j.2)
    by_cases hm : wprob D (A a) ≤ q
    · rw [ite_eq_left hm]
      by_cases hall : ∀ j : {x // x ∉ S}, b j ∈ A a
      · have hE : e.symm (a, b) ∈ E := by
          refine ⟨fun j hj => ?_, by rw [hrestr]; exact hm⟩
          rw [hrestr, hout a b j hj]; exact hall ⟨j, hj⟩
        rw [Set.indicator_of_mem hE, hsplit]
        congr 1
        exact Finset.prod_congr rfl fun j _ => (Set.indicator_of_mem (hall j) D).symm
      · push Not at hall
        obtain ⟨j, hj⟩ := hall
        have hE : e.symm (a, b) ∉ E := by
          intro h
          have := h.1 j j.2
          rw [hrestr, hout a b j j.2] at this
          exact hj this
        rw [Set.indicator_of_notMem hE, Finset.prod_eq_zero (Finset.mem_univ j)
          (Set.indicator_of_notMem hj D), mul_zero]
    · rw [ite_eq_right hm]
      have hE : e.symm (a, b) ∉ E := fun h => hm (by rw [← hrestr a b]; exact h.2)
      exact Set.indicator_of_notMem hE _
  have hcard : Fintype.card {x // x ∉ S} = Fintype.card ι - S.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have hpow : ∀ a, ∑ b : {x // x ∉ S} → Ω, ∏ j, (A a).indicator D (b j) =
      wprob D (A a) ^ (Fintype.card ι - S.card) := by
    intro a
    rw [← Fintype.prod_sum, Finset.prod_const, Finset.card_univ, hcard]
    rfl
  have hDS : ∑ a : {x // x ∈ S} → Ω, ∏ i, D (a i) = 1 := by
    rw [← Fintype.prod_sum, hD.sum_eq, Finset.prod_const_one]
  calc wprob (piW D) E = ∑ p, E.indicator (piW D) (e.symm p) := (e.symm.sum_comp _).symm
    _ = ∑ a, ∑ b, E.indicator (piW D) (e.symm (a, b)) := Fintype.sum_prod_type _
    _ = ∑ a, (if wprob D (A a) ≤ q then (∏ i, D (a i)) * wprob D (A a) ^
          (Fintype.card ι - S.card) else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [key]
        split_ifs
        · rw [← Finset.mul_sum, hpow]
        · simp
    _ ≤ ∑ a : {x // x ∈ S} → Ω, (∏ i, D (a i)) * q ^ (Fintype.card ι - S.card) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have hP : 0 ≤ ∏ i, D (a i) := Finset.prod_nonneg fun i _ => hD.nonneg _
        split_ifs with hm
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (wprob_nonneg hD.nonneg _) hm _) hP
        · exact mul_nonneg hP (pow_nonneg hq _)
    _ = q ^ (Fintype.card ι - S.card) := by rw [← Finset.sum_mul, hDS, one_mul]

/-- The number of index sets of each size: summing a function of `#I` over the subsets
`I ⊆ Fin N` with `#I ≤ m` gives `∑_{r ≤ m} binom(N, r) f(r)`. -/
theorem sum_subsets_card_le (N m : ℕ) (f : ℕ → ℝ) :
    ∑ I ∈ (univ : Finset (Finset (Fin N))).filter (fun I => I.card ≤ m), f I.card =
      ∑ r ∈ range (m + 1), (N.choose r : ℝ) * f r := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := range (m + 1)) (g := Finset.card)
    (fun I hI => by simp only [mem_filter] at hI; simp only [mem_range]; omega)]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hset : ((univ : Finset (Finset (Fin N))).filter (fun I => I.card ≤ m)).filter
      (fun I => I.card = r) = powersetCard r univ := by
    ext I
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
    simp only [mem_range] at hr
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by omega, h⟩
  rw [Finset.sum_congr rfl (fun I hI => by rw [(mem_filter.1 hI).2]), sum_const, hset,
    card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `lem:compression-spanner`, union bound over fixed index sets. For any family of covered sets
`C I (ω|_I)` determined by the samples indexed by `I`, the probability that some index set with
`#I ≤ m` covers every sample while its covered set has mass `< 1 - η` is at most
`∑_{r ≤ m} binom(N, r) (1 - η)^(N - r)`. The row law is finitely supported (see the module
docstring). -/
theorem compression_union_bound {V : Type*} {D : Ω → ℝ} (hD : IsProb D) (x : Ω → V)
    (N m : ℕ) (C : (I : Finset (Fin N)) → (I → Ω) → Set V) {η : ℝ} (hη : η < 1) :
    wprob (piW D) {ω : Fin N → Ω | ∃ I : Finset (Fin N), I.card ≤ m ∧
        (∀ i, x (ω i) ∈ C I (restr I ω)) ∧ wprob D (x ⁻¹' C I (restr I ω)) < 1 - η}
      ≤ ∑ r ∈ range (m + 1), (N.choose r : ℝ) * (1 - η) ^ (N - r) := by
  classical
  set s := (univ : Finset (Finset (Fin N))).filter (fun I => I.card ≤ m)
  set E : Finset (Fin N) → Set (Fin N → Ω) := fun I =>
    {ω | (∀ j, j ∉ I → ω j ∈ x ⁻¹' C I (restr I ω)) ∧ wprob D (x ⁻¹' C I (restr I ω)) ≤ 1 - η}
  have hsub : {ω : Fin N → Ω | ∃ I : Finset (Fin N), I.card ≤ m ∧
      (∀ i, x (ω i) ∈ C I (restr I ω)) ∧ wprob D (x ⁻¹' C I (restr I ω)) < 1 - η} ⊆
      ⋃ I ∈ s, E I := by
    rintro ω ⟨I, hI, hcov, hmass⟩
    simp only [Set.mem_iUnion]
    exact ⟨I, by simp [s, hI], fun j _ => hcov j, hmass.le⟩
  have hE : ∀ I ∈ s, wprob (piW D) (E I) ≤ (1 - η) ^ (N - I.card) := by
    intro I _
    have := wprob_cover_le hD I (fun a => x ⁻¹' C I a) (q := 1 - η) (by linarith)
    rwa [Fintype.card_fin] at this
  calc _ ≤ wprob (piW D) (⋃ I ∈ s, E I) := wprob_mono (piW_nonneg hD.nonneg) hsub
    _ ≤ ∑ I ∈ s, wprob (piW D) (E I) := wprob_biUnion_le (piW_nonneg hD.nonneg) s E
    _ ≤ ∑ I ∈ s, (1 - η) ^ (N - I.card) := Finset.sum_le_sum hE
    _ = _ := sum_subsets_card_le N m (fun r => (1 - η) ^ (N - r))

/-- `lem:compression-spanner`, counting step:
`∑_{r ≤ m} binom(N, r) (1 - η)^(N - r) ≤ (m + 1) N^m e^{-η (N - m)}` when `N ≥ 1`. -/
theorem sum_choose_le (N m : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∑ r ∈ range (m + 1), (N.choose r : ℝ) * (1 - η) ^ (N - r) ≤
      (m + 1) * (N : ℝ) ^ m * Real.exp (-η * (N - m)) := by
  have hterm : ∀ r ∈ range (m + 1),
      (N.choose r : ℝ) * (1 - η) ^ (N - r) ≤ (N : ℝ) ^ m * Real.exp (-η * (N - m)) := by
    intro r hr
    simp only [mem_range] at hr
    have hpos : 0 ≤ (N : ℝ) ^ m * Real.exp (-η * (N - m)) := by positivity
    rcases lt_or_ge N r with hNr | hrN
    · rw [Nat.choose_eq_zero_of_lt hNr, Nat.cast_zero, zero_mul]; exact hpos
    · have h1 : (N.choose r : ℝ) ≤ (N : ℝ) ^ m := by
        calc (N.choose r : ℝ) ≤ ((N ^ r : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_pow N r
          _ = (N : ℝ) ^ r := by push_cast; rfl
          _ ≤ (N : ℝ) ^ m := pow_le_pow_right₀ (by exact_mod_cast hN) (by omega)
      have h2 : (1 - η) ^ (N - r) ≤ Real.exp (-η * (N - m)) := by
        calc (1 - η) ^ (N - r) ≤ Real.exp (-η) ^ (N - r) :=
              pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg η) _
          _ = Real.exp (-η * ((N - r : ℕ) : ℝ)) := by
              rw [← Real.exp_nat_mul]; ring_nf
          _ ≤ Real.exp (-η * (N - m)) := by
              apply Real.exp_le_exp.mpr
              rw [Nat.cast_sub hrN]
              have : (r : ℝ) ≤ m := by exact_mod_cast (by omega : r ≤ m)
              nlinarith
      exact mul_le_mul h1 h2 (pow_nonneg (by linarith) _) (by positivity)
  calc _ ≤ ∑ r ∈ range (m + 1), (N : ℝ) ^ m * Real.exp (-η * (N - m)) := Finset.sum_le_sum hterm
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-- `lem:compression-spanner`, union bound with the final count: under `N ≥ 1` and `0 ≤ η < 1`,
the probability in `compression_union_bound` is at most `(m + 1) N^m e^{-η (N - m)}`. -/
theorem compression_union_bound_exp {V : Type*} {D : Ω → ℝ} (hD : IsProb D) (x : Ω → V)
    {N : ℕ} (hN : 1 ≤ N) (m : ℕ) (C : (I : Finset (Fin N)) → (I → Ω) → Set V) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    wprob (piW D) {ω : Fin N → Ω | ∃ I : Finset (Fin N), I.card ≤ m ∧
        (∀ i, x (ω i) ∈ C I (restr I ω)) ∧ wprob D (x ⁻¹' C I (restr I ω)) < 1 - η}
      ≤ (m + 1) * (N : ℝ) ^ m * Real.exp (-η * (N - m)) :=
  (compression_union_bound hD x N m C hη1).trans (sum_choose_le N m hN hη0 hη1.le)

end Core

/-! ### The sample size `N_s` -/

section SampleSize

/-- The sample size of `lem:compression-spanner`:
`N_s = ⌈(2/η)(m ⌈log₂(2m/η)⌉ + ⌈log₂((m+1)/δ_s)⌉)⌉`. -/
noncomputable def Ns (m : ℕ) (η δs : ℝ) : ℕ :=
  ⌈2 / η * ((m : ℝ) * (⌈Real.logb 2 (2 * m / η)⌉₊ : ℝ) +
    (⌈Real.logb 2 ((m + 1) / δs)⌉₊ : ℝ))⌉₊

/-- A base-two ceiling dominates the natural logarithm at arguments `≥ 1`. -/
theorem log_le_ceil_logb {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ ⌈Real.logb 2 y⌉₊ := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  calc Real.log y ≤ Real.log y / Real.log 2 := by
        rw [le_div_iff₀ h2]; nlinarith
    _ = Real.logb 2 y := rfl
    _ ≤ _ := Nat.le_ceil _

/-- `lem:compression-spanner`, sample size: for `m ≥ 1` and `η, δ_s ∈ (0,1)`,
`(m + 1) N_s^m e^{-η (N_s - m)} ≤ δ_s`. -/
theorem Ns_bound {m : ℕ} (hm : 1 ≤ m) {η δs : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hδ0 : 0 < δs)
    (hδ1 : δs < 1) :
    (m + 1) * (Ns m η δs : ℝ) ^ m * Real.exp (-η * (Ns m η δs - m)) ≤ δs := by
  set N : ℝ := (Ns m η δs : ℝ) with hNdef
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set u : ℝ := 2 * m / η with hu
  have hu1 : 1 < u := by rw [hu, lt_div_iff₀ hη0]; linarith
  have hv1 : 1 ≤ ((m : ℝ) + 1) / δs := by rw [le_div_iff₀ hδ0]; linarith
  have hA := log_le_ceil_logb hu1.le
  have hB := log_le_ceil_logb hv1
  have hN : 2 / η * ((m : ℝ) * (⌈Real.logb 2 u⌉₊ : ℝ) +
      (⌈Real.logb 2 ((m + 1) / δs)⌉₊ : ℝ)) ≤ N := Nat.le_ceil _
  have hLu : 0 < Real.log u := Real.log_pos hu1
  have hLv : 0 ≤ Real.log (((m : ℝ) + 1) / δs) := Real.log_nonneg hv1
  -- `η N / 2 ≥ m log u + log ((m+1)/δ_s)`
  have hsum : (m : ℝ) * Real.log u + Real.log (((m : ℝ) + 1) / δs) ≤ η * N / 2 := by
    have h1 : (m : ℝ) * Real.log u ≤ (m : ℝ) * (⌈Real.logb 2 u⌉₊ : ℝ) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    have h2 : η / 2 * (2 / η * ((m : ℝ) * (⌈Real.logb 2 u⌉₊ : ℝ) +
        (⌈Real.logb 2 ((m + 1) / δs)⌉₊ : ℝ))) ≤ η / 2 * N :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    have h3 : η / 2 * (2 / η * ((m : ℝ) * (⌈Real.logb 2 u⌉₊ : ℝ) +
        (⌈Real.logb 2 ((m + 1) / δs)⌉₊ : ℝ))) = (m : ℝ) * (⌈Real.logb 2 u⌉₊ : ℝ) +
        (⌈Real.logb 2 ((m + 1) / δs)⌉₊ : ℝ) := by field_simp
    linarith
  have hNpos : 0 < N := by
    have : 0 < η * N / 2 := lt_of_lt_of_le (by positivity) hsum
    nlinarith
  -- `log x ≤ x - 1` at `x = N / u = η N / (2 m)`
  have hlog : Real.log N - Real.log u ≤ N / u - 1 := by
    rw [← Real.log_div hNpos.ne' (by linarith)]
    exact Real.log_le_sub_one_of_pos (div_pos hNpos (by linarith))
  have hmx : (m : ℝ) * (N / u) = η * N / 2 := by
    rw [hu]; field_simp
  have hmlog : (m : ℝ) * Real.log N ≤ (m : ℝ) * Real.log u + η * N / 2 - m := by
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ m)
    nlinarith
  -- the logarithm of the bound is at most `log δ_s`
  have hexp : Real.log ((m : ℝ) + 1) + m * Real.log N - η * (N - m) ≤ Real.log δs := by
    have hdiv : Real.log (((m : ℝ) + 1) / δs) = Real.log ((m : ℝ) + 1) - Real.log δs :=
      Real.log_div (by positivity) hδ0.ne'
    nlinarith
  calc (m + 1) * N ^ m * Real.exp (-η * (N - m))
      = Real.exp (Real.log ((m : ℝ) + 1) + m * Real.log N - η * (N - m)) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log (by positivity), Real.exp_nat_mul,
          Real.exp_log hNpos, neg_mul, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (Real.log δs) := Real.exp_le_exp.mpr hexp
    _ = δs := Real.exp_log hδ0

theorem one_le_Ns {m : ℕ} (hm : 1 ≤ m) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (δs : ℝ) :
    1 ≤ Ns m η δs := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hu1 : 1 < 2 * (m : ℝ) / η := by rw [lt_div_iff₀ hη0]; linarith
  have hA : (1 : ℝ) ≤ ⌈Real.logb 2 (2 * m / η)⌉₊ := by
    have h1 := Real.logb_pos one_lt_two hu1
    have h2 : (0 : ℝ) < ⌈Real.logb 2 (2 * m / η)⌉₊ := lt_of_lt_of_le h1 (Nat.le_ceil _)
    exact Nat.one_le_cast.mpr (Nat.cast_pos.mp h2)
  have : (0 : ℝ) < 2 / η * ((m : ℝ) * (⌈Real.logb 2 (2 * m / η)⌉₊ : ℝ) +
      (⌈Real.logb 2 ((m + 1) / δs)⌉₊ : ℝ)) := by
    have : (0 : ℝ) < (m : ℝ) * (⌈Real.logb 2 (2 * m / η)⌉₊ : ℝ) := by nlinarith
    positivity
  exact Nat.one_le_iff_ne_zero.mpr fun h => by
    rw [Ns, Nat.ceil_eq_zero] at h; linarith

end SampleSize

/-! ### Barycentric and distributional spanners -/

section Spanners

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The set `{∑_i c_i v_i : |c_i| ≤ β}` of combinations of a finite family with coefficients in
`[-β, β]`. For an empty family it is `{0}`. -/
def zonotope {κ : Type*} [Fintype κ] (β : ℝ) (v : κ → V) : Set V :=
  {y | ∃ c : κ → ℝ, (∀ i, |c i| ≤ β) ∧ ∑ i, c i • v i = y}

theorem zonotope_of_isEmpty {κ : Type*} [Fintype κ] [IsEmpty κ] (β : ℝ) (v : κ → V) :
    zonotope β v = {0} := by
  ext y
  simp only [zonotope, Set.mem_ofPred_eq, Set.mem_singleton_iff, Finset.univ_eq_empty,
    Finset.sum_empty, IsEmpty.forall_iff, true_and]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨fun _ => 0, h.symm⟩⟩

theorem zonotope_mono {κ : Type*} [Fintype κ] {β β' : ℝ} (h : β ≤ β') (v : κ → V) :
    zonotope β v ⊆ zonotope β' v :=
  fun _ ⟨c, hc, hy⟩ => ⟨c, fun i => (hc i).trans h, hy⟩

/-- A `β`-barycentric spanner of a set `S`: every vector of `S` is a combination of the selected
vectors with all coefficients in `[-β, β]`. -/
def IsBarySpanner {κ : Type*} [Fintype κ] (β : ℝ) (S : Set V) (v : κ → V) : Prop :=
  S ⊆ zonotope β v

/-- An `(η, β)`-distributional spanner of the law of `x` under `D`: a fresh row `x(w)`, `w ∼ D`,
is a combination of the selected vectors with coefficients in `[-β, β]` with probability at
least `1 - η`. -/
def IsDistSpanner {Ω κ : Type*} [Fintype Ω] [Fintype κ] (η β : ℝ) (D : Ω → ℝ) (x : Ω → V)
    (v : κ → V) : Prop :=
  1 - η ≤ wprob D (x ⁻¹' zonotope β v)

/-- Reindexing a combination along an injective map into a finset of indices. -/
theorem zonotope_comp_subset {κ ι : Type*} [Fintype κ] [DecidableEq ι] {σ : κ → ι}
    (hσ : Function.Injective σ) (v : ι → V) {β : ℝ} (hβ : 0 ≤ β) :
    zonotope β (v ∘ σ) ⊆ zonotope β (fun i : (univ.image σ : Finset ι) => v i) := by
  rintro y ⟨c, hc, rfl⟩
  classical
  refine ⟨fun i => Function.extend σ c 0 i, fun i => ?_, ?_⟩
  · change |Function.extend σ c 0 (i : ι)| ≤ β
    by_cases h : ∃ k, σ k = (i : ι)
    · obtain ⟨k, hk⟩ := h
      rw [← hk, hσ.extend_apply]; exact hc k
    · rw [Function.extend_apply' _ _ _ h]; simpa using hβ
  · rw [Finset.sum_coe_sort (univ.image σ) (fun i => Function.extend σ c 0 i • v i),
      Finset.sum_image (fun a _ b _ h => hσ h)]
    exact Finset.sum_congr rfl fun k _ => by rw [hσ.extend_apply]; rfl

end Spanners

/-! ### Existence of a barycentric spanner among the sampled rows -/

section MaxVol

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Cramer's rule in determinant form: replacing the `k`-th vector by `∑_l c_l u_l` multiplies
the determinant by `c_k`. -/
theorem det_update_sum {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℝ W]
    (b : Module.Basis (Fin n) ℝ W)
    (u : Fin n → W) (c : Fin n → ℝ) (k : Fin n) :
    b.det (Function.update u k (∑ l, c l • u l)) = c k * b.det u := by
  rw [AlternatingMap.map_update_sum]
  simp only [AlternatingMap.map_update_smul, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · rw [Function.update_eq_self]
  · intro l _ hlk
    rw [AlternatingMap.map_update_self _ _ (Ne.symm hlk), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- `lem:compression-spanner`, selection step (maximum volume). Every finite family of vectors in a
finite-dimensional real space has a `1`-barycentric spanner consisting of at most `finrank V`
of its own members, which are linearly independent. If all vectors are zero, the selection is
empty (`r = 0`) and the zonotope is `{0}`. -/
theorem exists_bary_spanner [FiniteDimensional ℝ V] {ι : Type*} [Finite ι] (v : ι → V) :
    ∃ (r : ℕ) (σ : Fin r → ι), r ≤ Module.finrank ℝ V ∧ Function.Injective σ ∧
      LinearIndependent ℝ (v ∘ σ) ∧ ∀ j, v j ∈ zonotope 1 (v ∘ σ) := by
  classical
  set W := Submodule.span ℝ (Set.range v)
  set r := Module.finrank ℝ W
  let b : Module.Basis (Fin r) ℝ W := Module.finBasis ℝ W
  let w : ι → W := fun i => ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hw : Submodule.span ℝ (Set.range w) = ⊤ := by
    have h := Submodule.span_span_coe_preimage (R := ℝ) (s := Set.range v)
    convert h using 2
    ext x
    simp only [Set.mem_range, Set.mem_preimage, w]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi⟩
  -- an initial independent `r`-tuple of members
  obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' ℝ w
  have : Finite κ := Finite.of_injective a ha_inj
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    have bk := Module.Basis.mk ha_li (by rw [ha_span, hw])
    exact (Module.finrank_eq_card_basis bk).symm
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let σ₀ : Fin r → ι := a ∘ e
  have h0 : b.det (w ∘ σ₀) ≠ 0 := by
    have hli : LinearIndependent ℝ (w ∘ σ₀) := ha_li.comp e e.injective
    have hsp : Submodule.span ℝ (Set.range (w ∘ σ₀)) = ⊤ := by
      have : Set.range (w ∘ σ₀) = Set.range (w ∘ a) := by
        simp only [σ₀, ← Function.comp_assoc]; exact e.surjective.range_comp _
      rw [this, ha_span, hw]
    exact ((b.is_basis_iff_det).1 ⟨hli, hsp⟩).ne_zero
  -- a tuple of maximal volume
  have : Nonempty (Fin r → ι) := ⟨σ₀⟩
  obtain ⟨σ, hσ⟩ := Finite.exists_max (fun τ : Fin r → ι => |b.det (w ∘ τ)|)
  have hσ0 : b.det (w ∘ σ) ≠ 0 := by
    intro h
    have := hσ σ₀
    rw [h, abs_zero] at this
    exact h0 (abs_nonpos_iff.mp this)
  obtain ⟨hli, hsp⟩ := (b.is_basis_iff_det).2 (IsUnit.mk0 _ hσ0)
  refine ⟨r, σ, Submodule.finrank_le W, hli.injective.of_comp, ?_, ?_⟩
  · have : v ∘ σ = W.subtype ∘ (w ∘ σ) := rfl
    rw [this]
    exact hli.map' W.subtype (Submodule.ker_subtype W)
  · intro j
    have hj : w j ∈ Submodule.span ℝ (Set.range (w ∘ σ)) := hsp ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hj
    refine ⟨c, fun k => ?_, ?_⟩
    · have hdet : b.det (w ∘ Function.update σ k j) = c k * b.det (w ∘ σ) := by
        rw [Function.comp_update, ← hc]
        exact det_update_sum b (w ∘ σ) c k
      have hle := hσ (Function.update σ k j)
      rw [hdet, abs_mul] at hle
      have hpos : 0 < |b.det (w ∘ σ)| := abs_pos.mpr hσ0
      nlinarith
    · have := congrArg Subtype.val hc
      simpa [w] using this

end MaxVol

/-! ### Assembling `lem:compression-spanner` -/

section Assembly

variable {Ω V : Type*} [Fintype Ω] [AddCommGroup V] [Module ℝ V]

/-- `lem:compression-spanner`, failure bound for any selection rule. If a rule selects, from every
sample `ω`, at most `m` sampled rows forming a `2`-barycentric spanner of the sampled rows, then
the selected rows fail to be an `(η, 2)`-distributional spanner of the row law with probability at
most `(m + 1) N^m e^{-η (N - m)}`. The row law is finitely supported. -/
theorem selection_fail_le {D : Ω → ℝ} (hD : IsProb D) (x : Ω → V) {N m : ℕ} (hN : 1 ≤ N)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (sel : (Fin N → Ω) → Finset (Fin N))
    (hcard : ∀ ω, (sel ω).card ≤ m)
    (hbary : ∀ ω, IsBarySpanner 2 (Set.range fun i => x (ω i)) (fun i : sel ω => x (ω i))) :
    wprob (piW D) {ω | ¬ IsDistSpanner η 2 D x (fun i : sel ω => x (ω i))} ≤
      (m + 1) * (N : ℝ) ^ m * Real.exp (-η * (N - m)) := by
  refine le_trans ?_ ((compression_union_bound hD x N m
    (fun I a => zonotope 2 (fun i : I => x (a i))) hη1).trans (sum_choose_le N m hN hη0 hη1.le))
  refine wprob_mono (piW_nonneg hD.nonneg) fun ω hω => ?_
  simp only [IsDistSpanner, not_le, Set.mem_ofPred_eq] at hω
  exact ⟨sel ω, hcard ω, fun i => hbary ω ⟨i, rfl⟩, hω⟩

/-- `lem:compression-spanner`, success form of `selection_fail_le`. -/
theorem selection_success_ge {D : Ω → ℝ} (hD : IsProb D) (x : Ω → V) {N m : ℕ} (hN : 1 ≤ N)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (sel : (Fin N → Ω) → Finset (Fin N))
    (hcard : ∀ ω, (sel ω).card ≤ m)
    (hbary : ∀ ω, IsBarySpanner 2 (Set.range fun i => x (ω i)) (fun i : sel ω => x (ω i))) :
    1 - (m + 1) * (N : ℝ) ^ m * Real.exp (-η * (N - m)) ≤
      wprob (piW D) {ω | IsDistSpanner η 2 D x (fun i : sel ω => x (ω i))} := by
  have h := selection_fail_le hD x hN hη0 hη1 sel hcard hbary
  have hc := wprob_compl (isProb_piW (ι := Fin N) hD)
    {ω | IsDistSpanner η 2 D x (fun i : sel ω => x (ω i))}
  have : {ω | IsDistSpanner η 2 D x (fun i : sel ω => x (ω i))}ᶜ =
      {ω | ¬ IsDistSpanner η 2 D x (fun i : sel ω => x (ω i))} := rfl
  rw [this] at hc
  linarith

/-- `lem:compression-spanner` (statistical part). Rows in `ℝ^m`, `m ≥ 1`, `η, δ_s ∈ (0,1)`, and
`N_s` independent rows. For every selection rule choosing at most `m` actual sampled rows that
form a `2`-barycentric spanner of the sample, the selected rows are an `(η, 2)`-distributional
spanner of the row law with probability at least `1 - δ_s`. The row law is finitely supported;
the basis-exchange procedure and its bit cost are not formalized (see `exists_selection` for the
existence of a valid rule). -/
theorem compression_spanner {D : Ω → ℝ} (hD : IsProb D) {m : ℕ} (hm : 1 ≤ m)
    (x : Ω → (Fin m → ℝ)) {η δs : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hδ0 : 0 < δs) (hδ1 : δs < 1)
    (sel : (Fin (Ns m η δs) → Ω) → Finset (Fin (Ns m η δs)))
    (hcard : ∀ ω, (sel ω).card ≤ m)
    (hbary : ∀ ω, IsBarySpanner 2 (Set.range fun i => x (ω i)) (fun i : sel ω => x (ω i))) :
    1 - δs ≤ wprob (piW D) {ω | IsDistSpanner η 2 D x (fun i : sel ω => x (ω i))} := by
  have h := selection_success_ge hD x (one_le_Ns hm hη0 hη1 δs) hη0.le hη1 sel hcard hbary
  have hb := Ns_bound hm hη0 hη1 hδ0 hδ1
  linarith

omit [Fintype Ω] in
/-- A valid selection rule exists (maximum volume): for every sample, at most `finrank V` actual
sampled rows, linearly independent, forming a `1`-barycentric (hence `2`-barycentric) spanner of
the sampled rows. -/
theorem exists_selection [FiniteDimensional ℝ V] (x : Ω → V) (N : ℕ) :
    ∃ sel : (Fin N → Ω) → Finset (Fin N), ∀ ω, (sel ω).card ≤ Module.finrank ℝ V ∧
      LinearIndependent ℝ (fun i : sel ω => x (ω i)) ∧
      IsBarySpanner 1 (Set.range fun i => x (ω i)) (fun i : sel ω => x (ω i)) := by
  classical
  choose r σ hr hinj hli hcov using fun ω : Fin N → Ω => exists_bary_spanner (fun i => x (ω i))
  refine ⟨fun ω => univ.image (σ ω), fun ω => ⟨?_, ?_, ?_⟩⟩
  · exact (card_image_le.trans (by simp)).trans (hr ω)
  · let e : Fin (r ω) ≃ (univ.image (σ ω) : Finset (Fin N)) :=
      { toFun := fun k => ⟨σ ω k, mem_image_of_mem _ (mem_univ k)⟩
        invFun := fun i => (mem_image.1 i.2).choose
        left_inv := fun k =>
          hinj ω (mem_image.1 (mem_image_of_mem (σ ω) (mem_univ k))).choose_spec.2
        right_inv := fun i => Subtype.ext (mem_image.1 i.2).choose_spec.2 }
    exact (linearIndependent_equiv e).1 (hli ω)
  · rintro _ ⟨j, rfl⟩
    exact zonotope_comp_subset (hinj ω) (fun i => x (ω i)) zero_le_one (hcov ω j)

/-- `lem:compression-spanner`, combined form: there is a selection rule choosing at most `m`
linearly independent actual sampled rows that form a `1`-barycentric spanner of the sample, and
with probability at least `1 - δ_s` over `N_s` independent rows the selection is an
`(η, 2)`-distributional spanner of the (finitely supported) row law. -/
theorem compression_spanner_exists {D : Ω → ℝ} (hD : IsProb D) {m : ℕ} (hm : 1 ≤ m)
    (x : Ω → (Fin m → ℝ)) {η δs : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hδ0 : 0 < δs)
    (hδ1 : δs < 1) :
    ∃ sel : (Fin (Ns m η δs) → Ω) → Finset (Fin (Ns m η δs)),
      (∀ ω, (sel ω).card ≤ m ∧ LinearIndependent ℝ (fun i : sel ω => x (ω i)) ∧
        IsBarySpanner 1 (Set.range fun i => x (ω i)) (fun i : sel ω => x (ω i))) ∧
      1 - δs ≤ wprob (piW D) {ω | IsDistSpanner η 2 D x (fun i : sel ω => x (ω i))} := by
  obtain ⟨sel, hsel⟩ := exists_selection x (Ns m η δs)
  refine ⟨sel, fun ω => ?_, compression_spanner hD hm x hη0 hη1 hδ0 hδ1 sel
    (fun ω => ?_) (fun ω => ?_)⟩
  · obtain ⟨h1, h2, h3⟩ := hsel ω
    exact ⟨by simpa using h1, h2, h3⟩
  · simpa using (hsel ω).1
  · exact (hsel ω).2.2.trans (zonotope_mono one_le_two _)

end Assembly

end LowLogitRank.Spanner
