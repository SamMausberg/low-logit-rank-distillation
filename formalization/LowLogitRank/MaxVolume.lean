import LowLogitRank.Basic

/-!
# Maximum-volume bases and the canonical representation

The maximum-volume basis behind `eq:canonical` and `lem:bounded-factors`, the bounded
factorizations of `lem:bounded-factors` and `sec:sample-upper`, and the canonical recursive
representation of `sec:sample-upper` (also the bounded-coordinate step of `thm:alphabet`).

Volume is measured as `|det_b|` in a fixed basis `b` of the row space; the exchange identity
`vol_update_sum` is the property used in the paper.
-/

namespace LowLogitRank.MaxVolume

open Finset Module

section Volume

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The volume of a family `v` of `card ι` vectors, measured in a fixed basis `b`: `|det_b v|`. -/
noncomputable def vol (b : Basis ι ℝ V) (v : ι → V) : ℝ := |b.det v|

theorem alternating_update_sum {N : Type*} [AddCommGroup N] [Module ℝ N]
    (f : V [⋀^ι]→ₗ[ℝ] N) (v : ι → V) (c : ι → ℝ) (i : ι) :
    f (Function.update v i (∑ j, c j • v j)) = c i • f v := by
  rw [f.map_update_sum, Finset.sum_eq_single i]
  · rw [f.map_update_smul, Function.update_eq_self]
  · intro j _ hji
    rw [f.map_update_smul, f.map_eq_zero_of_eq _ (i := i) (j := j) ?_ (Ne.symm hji), smul_zero]
    simp [Function.update_of_ne hji]
  · simp

/-- The exchange identity behind `eq:canonical`: replacing the `i`-th vector of a family by the
combination `∑ j, c j • v j` multiplies the volume by `|c i|`. -/
theorem vol_update_sum (b : Basis ι ℝ V) (v : ι → V) (c : ι → ℝ) (i : ι) :
    vol b (Function.update v i (∑ j, c j • v j)) = |c i| * vol b v := by
  simp only [vol, alternating_update_sum, smul_eq_mul, abs_mul]

/-- The exchange argument of `eq:canonical`: if a family `v` has positive volume and replacing its
`i`-th vector by `∑ j, c j • v j` does not increase the volume, then `|c i| ≤ 1`. -/
theorem abs_coeff_le_one (b : Basis ι ℝ V) (v : ι → V) (hv : 0 < vol b v) (c : ι → ℝ) (i : ι)
    (hmax : vol b (Function.update v i (∑ j, c j • v j)) ≤ vol b v) : |c i| ≤ 1 := by
  rw [vol_update_sum] at hmax
  exact (mul_le_iff_le_one_left hv).mp hmax

end Volume

/-! ### Maximum-volume bases of the row space -/

variable {m n : Type*} [Finite m] [Fintype n]

/-- The row space of a matrix. -/
abbrev rowSpace (M : Matrix m n ℝ) : Submodule ℝ (n → ℝ) := Submodule.span ℝ (Set.range M)

/-- A row as an element of the row space. -/
def rowVec (M : Matrix m n ℝ) (x : m) : rowSpace M := ⟨M x, Submodule.subset_span ⟨x, rfl⟩⟩

theorem finrank_rowSpace (M : Matrix m n ℝ) : finrank ℝ (rowSpace M) = M.rank :=
  (M.rank_eq_finrank_span_row).symm

/-- Some `rank M` rows have positive volume, in any basis of the row space. -/
theorem exists_vol_pos (M : Matrix m n ℝ) (b : Basis (Fin M.rank) ℝ (rowSpace M)) :
    ∃ s : Fin M.rank → m, 0 < vol b (rowVec M ∘ s) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ (M : m → n → ℝ)
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = M.rank := by
    rw [Matrix.rank_eq_finrank_span_row, ← finrank_span_eq_card hli, hspan]; rfl
  let e : Fin M.rank ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent ℝ (rowVec M ∘ (a ∘ e)) :=
    LinearIndependent.of_comp (rowSpace M).subtype (hli.comp e e.injective)
  have htop := hli'.span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, finrank_rowSpace])
  exact abs_pos.mpr ((b.is_basis_iff_det).mp ⟨hli', htop⟩).ne_zero

/-- `eq:canonical`: let `b` be any basis of the row space and `s` any `rank M` actual rows of
maximum volume `|det_b|`. Then the rows `s` are a basis of the row space and every row has
coordinates in `[-1, 1]` in this basis. -/
theorem maxVolume_spec (M : Matrix m n ℝ) (b : Basis (Fin M.rank) ℝ (rowSpace M))
    (s : Fin M.rank → m)
    (hmax : ∀ s' : Fin M.rank → m, vol b (rowVec M ∘ s') ≤ vol b (rowVec M ∘ s)) :
    LinearIndependent ℝ (fun i => M (s i)) ∧
      Submodule.span ℝ (Set.range fun i => M (s i)) = rowSpace M ∧
      ∃ c : m → Fin M.rank → ℝ, (∀ x, M x = ∑ i, c x i • M (s i)) ∧ ∀ x i, |c x i| ≤ 1 := by
  classical
  obtain ⟨s0, hs0⟩ := exists_vol_pos M b
  have hpos : 0 < vol b (rowVec M ∘ s) := hs0.trans_le (hmax s0)
  obtain ⟨hlis, hsps⟩ := (b.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr (abs_pos.mp hpos))
  let bs : Basis (Fin M.rank) ℝ (rowSpace M) := Basis.mk hlis hsps.ge
  let c : m → Fin M.rank → ℝ := fun x => bs.repr (rowVec M x)
  have hrep : ∀ x, rowVec M x = ∑ i, c x i • (rowVec M ∘ s) i := fun x => by
    conv_lhs => rw [← bs.sum_repr (rowVec M x)]
    simp [bs, c, Basis.mk_apply]
  have hrep' : ∀ x, M x = ∑ i, c x i • M (s i) := fun x => by
    have := congrArg Subtype.val (hrep x)
    simpa [rowVec] using this
  refine ⟨hlis.map' (rowSpace M).subtype (rowSpace M).ker_subtype, ?_, c, hrep', fun x i => ?_⟩
  · apply le_antisymm
    · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨s i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, hrep' x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine abs_coeff_le_one b (rowVec M ∘ s) hpos (c x) i ?_
    rw [← hrep x, ← Function.comp_update]
    exact hmax _

/-- A family of `rank M` rows of maximum volume exists. -/
theorem exists_maxVolume (M : Matrix m n ℝ) (b : Basis (Fin M.rank) ℝ (rowSpace M)) :
    ∃ s : Fin M.rank → m, ∀ s', vol b (rowVec M ∘ s') ≤ vol b (rowVec M ∘ s) := by
  obtain ⟨s0, -⟩ := exists_vol_pos M b
  have : Nonempty (Fin M.rank → m) := ⟨s0⟩
  exact Finite.exists_max _

/-- `eq:canonical` (and the first step of the proof of `lem:bounded-factors`): every real matrix
with finite index types has `rank M` actual rows forming a basis of its row space in which every
row has coordinates in `[-1, 1]`. -/
theorem exists_maxVolume_basis (M : Matrix m n ℝ) :
    ∃ s : Fin M.rank → m, LinearIndependent ℝ (fun i => M (s i)) ∧
      Submodule.span ℝ (Set.range fun i => M (s i)) = Submodule.span ℝ (Set.range M) ∧
      ∃ c : m → Fin M.rank → ℝ, (∀ x, M x = ∑ i, c x i • M (s i)) ∧ ∀ x i, |c x i| ≤ 1 := by
  let b : Basis (Fin M.rank) ℝ (rowSpace M) :=
    Module.finBasisOfFinrankEq ℝ (rowSpace M) (finrank_rowSpace M)
  obtain ⟨s, hs⟩ := exists_maxVolume M b
  exact ⟨s, maxVolume_spec M b s hs⟩

/-! ### Zero padding -/

/-- Zero padding of a vector indexed by `Fin r` to `Fin d`. -/
def pad {β : Type*} [Zero β] {r : ℕ} (d : ℕ) (F : Fin r → β) : Fin d → β :=
  fun k => if hk : (k : ℕ) < r then F ⟨k, hk⟩ else 0

theorem pad_apply {β : Type*} {r : ℕ} (d : ℕ) (F : Fin r → Fin d → β) [Zero β] (k j : Fin d) :
    pad d F k j = pad d (fun i => F i j) k := by
  unfold pad; split_ifs <;> rfl

theorem pad_mul {r : ℕ} (d : ℕ) (F G : Fin r → ℝ) (k : Fin d) :
    pad d F k * pad d G k = pad d (fun i => F i * G i) k := by
  unfold pad; split_ifs <;> simp

theorem pad_sum_mul {r s : ℕ} (d : ℕ) (a : Fin s → ℝ) (F : Fin s → Fin r → ℝ) (k : Fin d) :
    pad d (fun j => ∑ i, a i * F i j) k = ∑ i, a i * pad d (F i) k := by
  unfold pad; split_ifs <;> simp

theorem abs_pad_le {r : ℕ} (d : ℕ) (F : Fin r → ℝ) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i, |F i| ≤ B)
    (k : Fin d) : |pad d F k| ≤ B := by
  unfold pad; split_ifs
  · exact hF _
  · simpa using hB

theorem sum_pad {r d : ℕ} (hrd : r ≤ d) (F : Fin r → ℝ) : ∑ k : Fin d, pad d F k = ∑ i, F i := by
  let G : ℕ → ℝ := fun k => if hk : k < r then F ⟨k, hk⟩ else 0
  have h1 : ∑ k : Fin d, pad d F k = ∑ k ∈ range d, G k := Fin.sum_univ_eq_sum_range G d
  have h2 : ∑ i : Fin r, F i = ∑ k ∈ range r, G k := by
    rw [← Fin.sum_univ_eq_sum_range G r]
    exact Finset.sum_congr rfl fun i _ => by simp [G]
  rw [h1, h2]
  refine (Finset.sum_subset (Finset.range_subset_range.mpr hrd) fun k _ hk => ?_).symm
  simp only [Finset.mem_range, not_lt] at hk
  simp [G, Nat.not_lt.mpr hk]

theorem sum_pad_mul {r d : ℕ} (hrd : r ≤ d) (F G : Fin r → ℝ) :
    ∑ k : Fin d, pad d F k * pad d G k = ∑ i, F i * G i := by
  simp only [pad_mul]; exact sum_pad hrd _

/-! ### Bounded factors -/

/-- The bounded factorization of `sec:sample-upper`: for a matrix of rank at most `d` with entries
in `[-Λ, Λ]`, the coordinate factor has norms at most `√d` and the basis-value factor has norms at
most `Λ √d`. -/
theorem coord_factors (M : Matrix m n ℝ) {d : ℕ} {Λ : ℝ} (hrank : M.rank ≤ d) (hΛ : 0 ≤ Λ)
    (hM : ∀ i j, |M i j| ≤ Λ) :
    ∃ (X : m → EuclideanSpace ℝ (Fin d)) (Y : n → EuclideanSpace ℝ (Fin d)),
      (∀ i j, M i j = inner ℝ (X i) (Y j)) ∧ (∀ i, ‖X i‖ ≤ √d) ∧ ∀ j, ‖Y j‖ ≤ Λ * √d := by
  obtain ⟨s, -, -, c, hrep, hc⟩ := exists_maxVolume_basis M
  refine ⟨fun i => WithLp.toLp 2 (pad d (c i)), fun j => WithLp.toLp 2 (pad d fun k => M (s k) j),
    ?_, ?_, ?_⟩
  · intro i j
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct]
    simp only [star_trivial]
    rw [sum_pad_mul hrank, hrep i]
    simp [Finset.sum_apply, mul_comm]
  · intro i
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    simp only [Real.norm_eq_abs, sq_abs]
    simp only [sq]
    rw [sum_pad_mul hrank]
    calc ∑ k, c i k * c i k ≤ ∑ _k : Fin M.rank, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by
            have := hc i k
            nlinarith [abs_mul_abs_self (c i k), abs_nonneg (c i k)]
      _ = M.rank := by simp
      _ ≤ d := by exact_mod_cast hrank
  · intro j
    rw [EuclideanSpace.norm_eq]
    calc √(∑ k, ‖pad d (fun k => M (s k) j) k‖ ^ 2) ≤ √(Λ ^ 2 * d) := by
          apply Real.sqrt_le_sqrt
          simp only [Real.norm_eq_abs, sq_abs]
          simp only [sq]
          rw [sum_pad_mul hrank]
          calc ∑ k, M (s k) j * M (s k) j ≤ ∑ _k : Fin M.rank, Λ * Λ :=
                Finset.sum_le_sum fun k _ => by
                  have := hM (s k) j
                  nlinarith [abs_mul_abs_self (M (s k) j), abs_nonneg (M (s k) j)]
            _ = Λ * Λ * M.rank := by simp [mul_comm]
            _ ≤ Λ * Λ * d := by gcongr
      _ = Λ * √d := by rw [Real.sqrt_mul (sq_nonneg Λ), Real.sqrt_sq hΛ]

/-- Rescaling the factors of `coord_factors` by `√Λ` and its reciprocal makes both norms at most
`√(dΛ)` (`sec:sample-upper`, with `Λ = T`). -/
theorem bounded_factors_of_pos (M : Matrix m n ℝ) {d : ℕ} {Λ : ℝ} (hrank : M.rank ≤ d)
    (hΛ : 0 < Λ) (hM : ∀ i j, |M i j| ≤ Λ) :
    ∃ (X : m → EuclideanSpace ℝ (Fin d)) (Y : n → EuclideanSpace ℝ (Fin d)),
      (∀ i j, M i j = inner ℝ (X i) (Y j)) ∧ (∀ i, ‖X i‖ ≤ √(d * Λ)) ∧
        ∀ j, ‖Y j‖ ≤ √(d * Λ) := by
  obtain ⟨X, Y, hXY, hX, hY⟩ := coord_factors M hrank hΛ.le hM
  have hs : 0 < √Λ := Real.sqrt_pos.mpr hΛ
  refine ⟨fun i => √Λ • X i, fun j => (√Λ)⁻¹ • Y j, ?_, ?_, ?_⟩
  · intro i j
    rw [inner_smul_left, inner_smul_right, hXY]
    simp [hs.ne']
  · intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, Real.sqrt_mul (Nat.cast_nonneg d), mul_comm]
    exact mul_le_mul_of_nonneg_right (hX i) hs.le
  · intro j
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, Real.sqrt_mul (Nat.cast_nonneg d)]
    calc (√Λ)⁻¹ * ‖Y j‖ ≤ (√Λ)⁻¹ * (Λ * √d) := by gcongr; exact hY j
      _ = √d * √Λ := by
          rw [show Λ * √d = √Λ * (√Λ * √d) by rw [← mul_assoc, Real.mul_self_sqrt hΛ.le],
            ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul, mul_comm]

/-- `lem:bounded-factors`: a real matrix of rank at most `d` with entries in `[-Λ, Λ]`, `Λ ≥ 1`,
has a factorization through `ℝ^d` whose history and future vectors have Euclidean norm at most
`√(dΛ)`. -/
theorem bounded_factors (M : Matrix m n ℝ) {d : ℕ} {Λ : ℝ} (hrank : M.rank ≤ d) (hΛ : 1 ≤ Λ)
    (hM : ∀ i j, |M i j| ≤ Λ) :
    ∃ (X : m → EuclideanSpace ℝ (Fin d)) (Y : n → EuclideanSpace ℝ (Fin d)),
      (∀ i j, M i j = inner ℝ (X i) (Y j)) ∧ (∀ i, ‖X i‖ ≤ √(d * Λ)) ∧
        ∀ j, ‖Y j‖ ≤ √(d * Λ) :=
  bounded_factors_of_pos M hrank (by linarith) hM

/-! ### The canonical recursive representation -/

/-- Coordinates in a linearly independent family are unique. -/
theorem coeffs_eq_of_linearIndependent {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    {v : ι → E} (hv : LinearIndependent ℝ v) {x y : ι → ℝ}
    (h : ∑ i, x i • v i = ∑ i, y i • v i) : x = y := by
  have h0 : ∑ i, (x - y) i • v i = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  funext i
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hv _ h0 i)

section Canonical

variable {α Y : Type*}

/-- The cut matrix at cut `t` of a family of logits `ℓ h y`: rows `h ∈ α^t`, columns
`(f, y) ∈ α^{<T-t} × Y`, entries `ℓ (h f) y`. With `α = Bool` and `Y = Unit` it is
`logitCutMatrix` up to relabelling columns (`cutMatrix_unit_rank`); with `Y = α` it is the cut
matrix of `sec:alphabet`. -/
def cutMatrix (ℓ : List α → Y → ℝ) (T t : ℕ) :
    Matrix (List.Vector α t) ((Σ j : Fin (T - t), List.Vector α j) × Y) ℝ :=
  fun h fy => ℓ (h.toList ++ fy.1.2.toList) fy.2

/-- Appending a letter to a word. -/
def vsnoc {t : ℕ} (h : List.Vector α t) (a : α) : List.Vector α (t + 1) :=
  ⟨h.toList ++ [a], by simp⟩

/-- The column of cut `t` obtained by prepending the letter `a` to the future of a column of cut
`t + 1`. -/
def consCol {T t : ℕ} (a : α) (fy : (Σ j : Fin (T - (t + 1)), List.Vector α j) × Y) :
    (Σ j : Fin (T - t), List.Vector α j) × Y :=
  (⟨⟨fy.1.1 + 1, by have := fy.1.1.isLt; omega⟩, a ::ᵥ fy.1.2⟩, fy.2)

/-- The child row: the row of `h a` at cut `t + 1` is the row of `h` at cut `t` restricted to
the columns whose future begins with `a`. -/
theorem cutMatrix_child (ℓ : List α → Y → ℝ) (T t : ℕ) (h : List.Vector α t) (a : α)
    (fy : (Σ j : Fin (T - (t + 1)), List.Vector α j) × Y) :
    cutMatrix ℓ T (t + 1) (vsnoc h a) fy = cutMatrix ℓ T t h (consCol a fy) := by
  simp [cutMatrix, vsnoc, consCol]

/-- `eq:canonical` and its recursive form (`sec:sample-upper`, and the bounded-coordinate step at
the start of the proof of `thm:alphabet`, where `Y = α`). If `|ℓ h y| ≤ Λ` for `|h| < T` and every
cut matrix `t < T` has rank at most `d`, there are states `c h ∈ [-1,1]^d`, transition matrices
`A t a` with entries in `[-1,1]` and readouts `w t y ∈ [-Λ,Λ]^d` with
`ℓ h y = ⟨c h, w |h| y⟩` for `|h| < T` and `c (h a) = c h · A |h| a` for `|h| + 1 < T`.
For `d ≥ 1` and `T ≥ 1` the initial state is `e_1`. -/
theorem exists_canonical [Fintype α] [Fintype Y] (ℓ : List α → Y → ℝ) (T d : ℕ) (Λ : ℝ)
    (hbound : ∀ h : List α, h.length < T → ∀ y, |ℓ h y| ≤ Λ)
    (hrank : ∀ t < T, (cutMatrix ℓ T t).rank ≤ d) :
    ∃ (c : List α → Fin d → ℝ) (A : ℕ → α → Matrix (Fin d) (Fin d) ℝ)
      (w : ℕ → Y → Fin d → ℝ),
      (∀ h i, |c h i| ≤ 1) ∧ (∀ t a i j, |A t a i j| ≤ 1) ∧ (∀ t < T, ∀ y i, |w t y i| ≤ Λ) ∧
      (∀ h : List α, h.length < T → ∀ y, ℓ h y = ∑ i, c h i * w h.length y i) ∧
      (∀ (h : List α) (a : α), h.length + 1 < T →
        c (h ++ [a]) = Matrix.vecMul (c h) (A h.length a)) ∧
      (∀ hd : 0 < d, 0 < T → c [] = Pi.single ⟨0, hd⟩ 1) := by
  classical
  have hΛ : 0 < T → ∀ y, 0 ≤ Λ := fun hT y => (abs_nonneg _).trans (hbound [] hT y)
  by_cases hzero : ∀ h : List α, h.length < T → ∀ y, ℓ h y = 0
  · let e : Fin d → ℝ := fun i => if (i : ℕ) = 0 then 1 else 0
    refine ⟨fun _ => e, fun _ _ => 1, fun _ _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h i; simp only [e]; split_ifs <;> simp
    · intro t a i j
      change |(1 : Matrix (Fin d) (Fin d) ℝ) i j| ≤ 1
      rw [Matrix.one_apply]; split_ifs <;> simp
    · intro t ht y i; simpa using hΛ (by omega) y
    · intro h hh y; simp [hzero h hh y]
    · intro h a _; simp [Matrix.vecMul_one]
    · intro hd _; funext i; simp [e, Pi.single_apply, Fin.ext_iff]
  push Not at hzero
  obtain ⟨f0, hf0, y0, hy0⟩ := hzero
  have H := fun t => exists_maxVolume_basis (cutMatrix ℓ T t)
  choose s hli _ cc hrep hcc using H
  let C : (t : ℕ) → List.Vector α t → Fin d → ℝ := fun t h => pad d (cc t h)
  let A : ℕ → α → Matrix (Fin d) (Fin d) ℝ :=
    fun t a => pad d (fun i => C (t + 1) (vsnoc (s t i) a))
  let w : ℕ → Y → Fin d → ℝ := fun t y => pad d (fun i => ℓ (s t i).toList y)
  let c : List α → Fin d → ℝ := fun h => C h.length ⟨h, rfl⟩
  have hcC : ∀ t (h : List.Vector α t), c h.toList = C t h := by
    rintro t ⟨l, hl⟩; subst hl; rfl
  have hC1 : ∀ t h i, |C t h i| ≤ 1 := fun t h i => abs_pad_le d _ zero_le_one (hcc t h) i
  -- the child coordinates
  have hchild : ∀ t, t + 1 < T → ∀ (h : List.Vector α t) (a : α),
      C (t + 1) (vsnoc h a) = Matrix.vecMul (C t h) (A t a) := by
    intro t ht h a
    have key : cc (t + 1) (vsnoc h a) =
        fun j => ∑ i, cc t h i * cc (t + 1) (vsnoc (s t i) a) j := by
      refine coeffs_eq_of_linearIndependent (hli (t + 1)) ?_
      rw [← hrep]
      funext fy
      rw [cutMatrix_child, hrep t h]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have : ∀ i, cutMatrix ℓ T t (s t i) (consCol a fy) =
          ∑ j, cc (t + 1) (vsnoc (s t i) a) j * cutMatrix ℓ T (t + 1) (s (t + 1) j) fy := by
        intro i
        rw [← cutMatrix_child, hrep (t + 1) (vsnoc (s t i) a)]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [this, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    funext j
    simp only [Matrix.vecMul, dotProduct, C, A]
    rw [key, pad_sum_mul]
    simp only [pad_apply]
    rw [sum_pad_mul (hrank t (by omega))]
  refine ⟨c, A, w, fun h i => hC1 _ _ i, ?_, ?_, ?_, ?_, ?_⟩
  · intro t a i j
    simp only [A, pad_apply]
    exact abs_pad_le d _ zero_le_one (fun k => hC1 _ _ j) i
  · intro t ht y i
    refine abs_pad_le d _ (hΛ (by omega) y) (fun k => hbound _ ?_ y) i
    simp [ht]
  · intro h hh y
    have h1 : ℓ h y = cutMatrix ℓ T h.length ⟨h, rfl⟩ (⟨⟨0, by omega⟩, List.Vector.nil⟩, y) := by
      simp [cutMatrix]
    rw [h1, congrFun (hrep h.length ⟨h, rfl⟩) _]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c, C, w]
    rw [sum_pad_mul (hrank _ hh)]
    simp [cutMatrix]
  · intro h a ha
    have := hchild h.length ha ⟨h, rfl⟩ a
    rw [← hcC] at this
    exact this
  · intro hd hT
    have hr0 : 0 < (cutMatrix ℓ T 0).rank := by
      by_contra hr
      have hr' : (cutMatrix ℓ T 0).rank = 0 := by omega
      have hrow := hrep 0 List.Vector.nil
      have h2 := congrFun hrow (⟨⟨f0.length, by omega⟩, ⟨f0, rfl⟩⟩, y0)
      have h3 : ∑ i, cc 0 List.Vector.nil i • cutMatrix ℓ T 0 (s 0 i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact absurd i.isLt (by omega)
      rw [h3] at h2
      exact hy0 (by simpa [cutMatrix] using h2)
    have hsingle : cc 0 List.Vector.nil = Pi.single ⟨0, hr0⟩ 1 := by
      refine coeffs_eq_of_linearIndependent (hli 0) ?_
      rw [← hrep, Finset.sum_eq_single ⟨0, hr0⟩]
      · simp [List.Vector.eq_nil (s 0 _)]
      · intro i _ hi; simp [hi]
      · simp
    change pad d (cc 0 ⟨[], rfl⟩) = _
    have hnil : (⟨[], rfl⟩ : List.Vector α 0) = List.Vector.nil := rfl
    rw [hnil, hsingle]
    funext k
    by_cases hk : (k : ℕ) = 0
    · have : k = ⟨0, hd⟩ := Fin.ext hk
      subst this
      simp [pad, hr0]
    · simp [pad, Fin.ext_iff, hk]

/-- The binary cut matrix of `Basic` has the same rank as `cutMatrix` with `Y = Unit`. -/
theorem cutMatrix_unit_rank (ℓ : List Bool → ℝ) (T t : ℕ) :
    (cutMatrix (fun h (_ : Unit) => ℓ h) T t).rank = (logitCutMatrix ℓ T t).rank := by
  have : cutMatrix (fun h (_ : Unit) => ℓ h) T t =
      (logitCutMatrix ℓ T t).submatrix (Equiv.refl _) (Equiv.prodPUnit _) := by
    ext h fy; rfl
  rw [this, Matrix.rank_submatrix]

end Canonical

/-- `eq:canonical` for binary strings (`sec:sample-upper`): states `c h ∈ [-1,1]^d`, transitions
`A t b` with entries in `[-1,1]`, readouts `w t ∈ [-Λ,Λ]^d`, `ℓ h = ⟨c h, w |h|⟩` for `|h| < T`,
`c (h b) = c h · A |h| b` for `|h| + 1 < T`, and `c [] = e_1` when `d, T ≥ 1`. -/
theorem exists_canonical_binary (ℓ : List Bool → ℝ) (T d : ℕ) (Λ : ℝ)
    (hbound : ∀ h : List Bool, h.length < T → |ℓ h| ≤ Λ)
    (hrank : ∀ t < T, (logitCutMatrix ℓ T t).rank ≤ d) :
    ∃ (c : List Bool → Fin d → ℝ) (A : ℕ → Bool → Matrix (Fin d) (Fin d) ℝ)
      (w : ℕ → Fin d → ℝ),
      (∀ h i, |c h i| ≤ 1) ∧ (∀ t b i j, |A t b i j| ≤ 1) ∧ (∀ t < T, ∀ i, |w t i| ≤ Λ) ∧
      (∀ h : List Bool, h.length < T → ℓ h = ∑ i, c h i * w h.length i) ∧
      (∀ (h : List Bool) (b : Bool), h.length + 1 < T →
        c (h ++ [b]) = Matrix.vecMul (c h) (A h.length b)) ∧
      (∀ hd : 0 < d, 0 < T → c [] = Pi.single ⟨0, hd⟩ 1) := by
  obtain ⟨c, A, w, h1, h2, h3, h4, h5, h6⟩ := exists_canonical (fun h (_ : Unit) => ℓ h) T d Λ
    (fun h hh _ => hbound h hh) (fun t ht => (cutMatrix_unit_rank ℓ T t).symm ▸ hrank t ht)
  exact ⟨c, A, fun t => w t (), h1, h2, fun t ht i => h3 t ht () i, fun h hh => h4 h hh (),
    h5, h6⟩

/-- `eq:canonical` for a member of the class: the recursive representation of the logits of any
`p` with `LogitClass T Λ d p`. -/
theorem exists_canonical_of_logitClass {T d : ℕ} {Λ : ℝ} {p : NextBit}
    (hp : LogitClass T Λ d p) :
    ∃ (c : List Bool → Fin d → ℝ) (A : ℕ → Bool → Matrix (Fin d) (Fin d) ℝ)
      (w : ℕ → Fin d → ℝ),
      (∀ h i, |c h i| ≤ 1) ∧ (∀ t b i j, |A t b i j| ≤ 1) ∧ (∀ t < T, ∀ i, |w t i| ≤ Λ) ∧
      (∀ h : List Bool, h.length < T → logit p h = ∑ i, c h i * w h.length i) ∧
      (∀ (h : List Bool) (b : Bool), h.length + 1 < T →
        c (h ++ [b]) = Matrix.vecMul (c h) (A h.length b)) ∧
      (∀ hd : 0 < d, 0 < T → c [] = Pi.single ⟨0, hd⟩ 1) :=
  exists_canonical_binary (logit p) T d Λ hp.logit_le hp.rank_le

/-- The bounded-coordinate step at the start of the proof of `thm:alphabet`: for an alphabet `α`,
token logits `ℓ h y` with `|ℓ h y| ≤ T` for `|h| < T`, and cut matrices (rows `h ∈ α^t`, columns
`(f, y) ∈ α^{<T-t} × α`) of rank at most `d`, there are states `c_t(h) ∈ [-1,1]^d`, matrices
`M_{t,b}` with entries in `[-1,1]` and readouts `w_{t,y}` with `‖w_{t,y}‖_∞ ≤ T` such that
`ℓ_y(h) = ⟨c_t(h), w_{t,y}⟩` and `c_{t+1}(hb) = c_t(h) M_{t,b}`. -/
theorem exists_canonical_alphabet {α : Type*} [Fintype α] (ℓ : List α → α → ℝ)
    (T d : ℕ) (hbound : ∀ h : List α, h.length < T → ∀ y, |ℓ h y| ≤ T)
    (hrank : ∀ t < T, (cutMatrix ℓ T t).rank ≤ d) :
    ∃ (c : List α → Fin d → ℝ) (M : ℕ → α → Matrix (Fin d) (Fin d) ℝ)
      (w : ℕ → α → Fin d → ℝ),
      (∀ h i, |c h i| ≤ 1) ∧ (∀ t b i j, |M t b i j| ≤ 1) ∧ (∀ t < T, ∀ y i, |w t y i| ≤ T) ∧
      (∀ h : List α, h.length < T → ∀ y, ℓ h y = ∑ i, c h i * w h.length y i) ∧
      (∀ (h : List α) (b : α), h.length + 1 < T →
        c (h ++ [b]) = Matrix.vecMul (c h) (M h.length b)) := by
  obtain ⟨c, M, w, h1, h2, h3, h4, h5, -⟩ := exists_canonical ℓ T d T hbound hrank
  exact ⟨c, M, w, h1, h2, h3, h4, h5⟩

end LowLogitRank.MaxVolume
