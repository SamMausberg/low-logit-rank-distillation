import LowLogitRank.Basic

/-!
# Rank bounds from polynomial feature expansions

This file contains the linear-algebra part of `lem:logit-lift` (`sec:fixed-rank`), `lem:lift`
(`sec:probability-route`) and the rank argument of `lem:hard-teacher` (`sec:hardness`).
-/

namespace LowLogitRank.PolyRank

open Finset MvPolynomial

/-! ### Feature factorizations and rank -/

section Factorization

variable {m n I : Type*} [Fintype n] [Fintype I]

/-- A matrix with entries `M i j = ∑_{a ∈ I} X i a Y j a` has rank at most `|I|`. -/
theorem rank_le_card_of_factor (M : Matrix m n ℝ) (X : m → I → ℝ) (Y : n → I → ℝ)
    (h : ∀ i j, M i j = ∑ a, X i a * Y j a) : M.rank ≤ Fintype.card I := by
  have hM : M = Matrix.of X * Matrix.of fun a j => Y j a := by
    ext i j
    simp [Matrix.mul_apply, h]
  rw [hM]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- A matrix of rank at most `d` factors through `d` real coordinates. -/
theorem exists_factor_of_rank_le (M : Matrix m n ℝ) {d : ℕ} (hM : M.rank ≤ d) :
    ∃ (X : m → Fin d → ℝ) (Y : n → Fin d → ℝ), ∀ i j, M i j = ∑ a, X i a * Y j a := by
  classical
  set V := LinearMap.range M.mulVecLin with hV
  set r := Module.finrank ℝ V with hr_def
  have hr : r ≤ d := hM
  let b : Module.Basis (Fin r) ℝ V := Module.finBasis ℝ V
  have hcol : ∀ j, M.col j ∈ V := fun j => by
    rw [hV, Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  let c : n → Fin r → ℝ := fun j => b.repr ⟨M.col j, hcol j⟩
  have hsum : ∀ i j, M i j = ∑ a : Fin r, (b a : m → ℝ) i * c j a := by
    intro i j
    have h1 := congrArg (fun v : V => (v : m → ℝ) i) (b.sum_repr ⟨M.col j, hcol j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h1
    rw [show M i j = M.col j i from rfl, ← h1]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨fun i a => if ha : (a : ℕ) < r then (b ⟨a, ha⟩ : m → ℝ) i else 0,
    fun j a => if ha : (a : ℕ) < r then c j ⟨a, ha⟩ else 0, fun i j => ?_⟩
  rw [hsum]
  let F : ℕ → ℝ := fun k => if hk : k < r then (b ⟨k, hk⟩ : m → ℝ) i * c j ⟨k, hk⟩ else 0
  have hF : ∀ a : Fin d, ((if ha : (a : ℕ) < r then (b ⟨a, ha⟩ : m → ℝ) i else 0) *
      if ha : (a : ℕ) < r then c j ⟨a, ha⟩ else 0) = F a := by
    intro a
    simp only [F]
    split_ifs <;> simp
  simp_rw [hF]
  rw [Fin.sum_univ_eq_sum_range F d]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hr) (fun k _ hk => by
    simp only [Finset.mem_range, not_lt] at hk
    simp [F, not_lt.mpr hk])]
  rw [← Fin.sum_univ_eq_sum_range F r]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [F]

/-- Rank at most `d` is the same as a factorization through `d` real coordinates. -/
theorem rank_le_iff_exists_factor (M : Matrix m n ℝ) (d : ℕ) :
    M.rank ≤ d ↔
      ∃ (X : m → Fin d → ℝ) (Y : n → Fin d → ℝ), ∀ i j, M i j = ∑ a, X i a * Y j a :=
  ⟨exists_factor_of_rank_le M, fun ⟨X, Y, h⟩ => by
    simpa using rank_le_card_of_factor M X Y h⟩

end Factorization

/-! ### Counting monomials -/

/-- The exponent vectors `α ∈ ℕ^d` with `∑ α_i ≤ K`, as finitely supported functions. -/
def monomials (d K : ℕ) : Finset (Fin d →₀ ℕ) :=
  (range (K + 1)).biUnion fun s => (univ : Finset (Fin d)).finsuppAntidiag s

theorem mem_monomials {d K : ℕ} {α : Fin d →₀ ℕ} : α ∈ monomials d K ↔ ∑ i, α i ≤ K := by
  simp [monomials]

/-- Stars and bars, used in `lem:logit-lift` and `lem:lift`: there are `binom(d + K, d)` exponent
vectors `α ∈ ℕ^d` with `∑ α_i ≤ K`. -/
theorem card_monomials (d K : ℕ) : (monomials d K).card = Nat.choose (d + K) d := by
  rw [monomials, card_biUnion]
  · simp_rw [card_finsuppAntidiag_nat_eq_multichoose, card_univ, Fintype.card_fin]
    rw [Nat.sum_range_multichoose, add_comm]
  · intro s _ s' _ hss'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro α hα hα'
    rw [mem_finsuppAntidiag] at hα hα'
    exact hss' (hα.1.symm.trans hα'.1)

/-- The same exponent vectors as plain functions `Fin d → ℕ`. -/
noncomputable def monomialsFun (d K : ℕ) : Finset (Fin d → ℕ) :=
  (monomials d K).map Finsupp.equivFunOnFinite.toEmbedding

theorem mem_monomialsFun {d K : ℕ} {α : Fin d → ℕ} : α ∈ monomialsFun d K ↔ ∑ i, α i ≤ K := by
  simp only [monomialsFun, mem_map_equiv, mem_monomials]
  simp

/-- Stars and bars for exponent vectors `α : Fin d → ℕ` with `∑ α_i ≤ K`. -/
theorem card_monomialsFun (d K : ℕ) : (monomialsFun d K).card = Nat.choose (d + K) d := by
  rw [monomialsFun, card_map, card_monomials]

/-! ### Polynomial features -/

section PolyFeatures

variable {m n : Type*} [Fintype n]

/-- If every column is a polynomial of total degree at most `K` in `d` row coordinates, the matrix
has rank at most `binom(d + K, d)`: expand every column in the monomials of degree `≤ K`. -/
theorem rank_le_of_eval_mvPolynomial {d K : ℕ} (M : Matrix m n ℝ) (x : m → Fin d → ℝ)
    (P : n → MvPolynomial (Fin d) ℝ) (hP : ∀ j, (P j).totalDegree ≤ K)
    (hM : ∀ i j, M i j = MvPolynomial.eval (x i) (P j)) :
    M.rank ≤ Nat.choose (d + K) d := by
  classical
  have hsupp : ∀ j, (P j).support ⊆ monomials d K := by
    intro j α hα
    rw [mem_monomials]
    have h1 := le_totalDegree hα
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    exact h1.trans (hP j)
  have key : ∀ i j, M i j = ∑ α : monomials d K,
      (∏ a, x i a ^ (α : Fin d →₀ ℕ) a) * (P j).coeff α := by
    intro i j
    rw [hM, MvPolynomial.eval_eq', Finset.sum_subset (hsupp j) (fun α _ hα => by
      rw [MvPolynomial.notMem_support_iff.mp hα, zero_mul])]
    rw [← Finset.sum_coe_sort (monomials d K)]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  have := rank_le_card_of_factor M _ _ key
  rwa [Fintype.card_coe, card_monomials] at this

/-- The linear form `y ↦ ∑ a, y a X_a` as a polynomial. -/
noncomputable def linForm {d : ℕ} (y : Fin d → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ a, C (y a) * X a

theorem eval_linForm {d : ℕ} (x y : Fin d → ℝ) :
    MvPolynomial.eval x (linForm y) = ∑ a, x a * y a := by
  simp [linForm, mul_comm]

theorem totalDegree_linForm_le {d : ℕ} (y : Fin d → ℝ) : (linForm y).totalDegree ≤ 1 := by
  refine totalDegree_finsetSum_le fun a _ => (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_X a).le

/-- Substituting a polynomial into a univariate polynomial multiplies degrees. -/
theorem totalDegree_aeval_le {σ : Type*} (p : MvPolynomial σ ℝ) (r : Polynomial ℝ) :
    (Polynomial.aeval p r).totalDegree ≤ r.natDegree * p.totalDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine totalDegree_finsetSum_le fun i hi => (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_pow _ _).trans ?_
  exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

theorem eval_aeval {σ : Type*} (x : σ → ℝ) (p : MvPolynomial σ ℝ) (r : Polynomial ℝ) :
    MvPolynomial.eval x (Polynomial.aeval p r) = r.eval (MvPolynomial.eval x p) := by
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval x) p r
  rw [Polynomial.coe_aeval_eq_eval] at h
  exact h.symm

/-- Matrix form of `lem:logit-lift`: if `M i j = ⟨x_i, y_j⟩` with `x_i, y_j ∈ ℝ^d` and `r` has
degree at most `k`, then the entrywise image `r(M)` has rank at most `binom(d + k, d)`. -/
theorem rank_map_polynomial_le {d k : ℕ} (M : Matrix m n ℝ) (x : m → Fin d → ℝ)
    (y : n → Fin d → ℝ) (hM : ∀ i j, M i j = ∑ a, x i a * y j a) (r : Polynomial ℝ)
    (hr : r.natDegree ≤ k) :
    (Matrix.of fun i j => r.eval (M i j)).rank ≤ Nat.choose (d + k) d := by
  refine rank_le_of_eval_mvPolynomial _ x (fun j => Polynomial.aeval (linForm (y j)) r)
    (fun j => ?_) (fun i j => ?_)
  · refine (totalDegree_aeval_le _ _).trans ?_
    calc r.natDegree * (linForm (y j)).totalDegree ≤ k * 1 :=
          Nat.mul_le_mul hr (totalDegree_linForm_le _)
      _ = k := mul_one k
  · rw [eval_aeval, eval_linForm, Matrix.of_apply, hM]

/-- `lem:logit-lift` for a matrix of rank at most `d` (no factorization given). -/
theorem rank_map_polynomial_le_of_rank_le {d k : ℕ} (M : Matrix m n ℝ) (hM : M.rank ≤ d)
    (r : Polynomial ℝ) (hr : r.natDegree ≤ k) :
    (Matrix.of fun i j => r.eval (M i j)).rank ≤ Nat.choose (d + k) d := by
  obtain ⟨x, y, hxy⟩ := exists_factor_of_rank_le M hM
  exact rank_map_polynomial_le M x y hxy r hr

end PolyFeatures

/-! ### `lem:logit-lift` for logit matrices -/

/-- `lem:logit-lift` at one cut: if the logit matrix of `ℓ` at cut `t` has rank at most `d` and `r`
has degree at most `k`, the logit matrix of `r ∘ ℓ` at cut `t` has rank at most
`binom(d + k, d)`. -/
theorem rank_logitCutMatrix_polynomial_le {ℓ : List Bool → ℝ} {T t d k : ℕ}
    (hℓ : (logitCutMatrix ℓ T t).rank ≤ d) (r : Polynomial ℝ) (hr : r.natDegree ≤ k) :
    (logitCutMatrix (fun h => r.eval (ℓ h)) T t).rank ≤ Nat.choose (d + k) d :=
  rank_map_polynomial_le_of_rank_le _ hℓ r hr

/-- `lem:logit-lift` at one cut, for the comparison model `P°` with `ℓ_{P°}(h) = r(ℓ_P(h))`,
i.e. `P°(1 | h) = σ(2 r(ℓ_P(h)))`. -/
theorem rank_logitCutMatrix_logitLift_le {p : NextBit} {T t d k : ℕ}
    (hp : (logitCutMatrix (logit p) T t).rank ≤ d) (r : Polynomial ℝ) (hr : r.natDegree ≤ k) :
    (logitCutMatrix (logit (ofLogit fun h => r.eval (logit p h))) T t).rank ≤
      Nat.choose (d + k) d := by
  have hl : logit (ofLogit fun h => r.eval (logit p h)) = fun h => r.eval (logit p h) :=
    funext (logit_ofLogit _)
  rw [hl]
  exact rank_logitCutMatrix_polynomial_le hp r hr

/-- `lem:logit-lift`: if `P` has logit bound `Λ` and logit rank at most `d` at every cut `t < T`,
`r` has degree at most `k` and `|r(u)| ≤ Λ'` for `|u| ≤ Λ`, then `P°` (logits `r(ℓ_P)`) is fully
supported, has logit bound `Λ'` and logit rank at most `binom(d + k, d)` at every cut `t < T`. -/
theorem logitLift_logitClass {p : NextBit} {T d k : ℕ} {Λ Λ' : ℝ} (hp : LogitClass T Λ d p)
    (r : Polynomial ℝ) (hr : r.natDegree ≤ k) (hbound : ∀ u, |u| ≤ Λ → |r.eval u| ≤ Λ') :
    LogitClass T Λ' (Nat.choose (d + k) d) (ofLogit fun h => r.eval (logit p h)) where
  fullSupport := ofLogit_fullSupport _ T
  logit_le h hh := by
    rw [logit_ofLogit]
    exact hbound _ (hp.logit_le h hh)
  rank_le t ht := rank_logitCutMatrix_logitLift_le (hp.rank_le t ht) r hr

/-- `lem:logit-lift` with the magnitude bound of the paper: if `|ψ(u)| ≤ M` and
`|r(u) - ψ(u)| ≤ ζ` for `|u| ≤ Λ`, the entries of the logit matrices of `P°` have magnitude at
most `M + ζ`. In the paper `Λ = T`, `ψ = ψ_τ` and `M = M_τ`. -/
theorem logitLift_logitClass_of_approx {p : NextBit} {T d k : ℕ} {Λ M ζ : ℝ}
    (hp : LogitClass T Λ d p) (r : Polynomial ℝ) (hr : r.natDegree ≤ k) (ψ : ℝ → ℝ)
    (hψ : ∀ u, |u| ≤ Λ → |ψ u| ≤ M) (happrox : ∀ u, |u| ≤ Λ → |r.eval u - ψ u| ≤ ζ) :
    LogitClass T (M + ζ) (Nat.choose (d + k) d) (ofLogit fun h => r.eval (logit p h)) := by
  refine logitLift_logitClass hp r hr fun u hu => ?_
  have h1 := happrox u hu
  have h2 := hψ u hu
  calc |r.eval u| = |(r.eval u - ψ u) + ψ u| := by rw [sub_add_cancel]
    _ ≤ |r.eval u - ψ u| + |ψ u| := abs_add_le _ _
    _ ≤ M + ζ := by linarith

/-- The bound `|ψ_τ(u)| ≤ M_τ` of `sec:fixed-rank`, for `0 < τ ≤ 1`. -/
theorem abs_softclip_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (u : ℝ) :
    |softclip τ u| ≤ softclipBound τ := by
  unfold softclip softclipBound
  have hw0 : 0 < Real.exp (2 * u) := Real.exp_pos _
  have hc : 0 < 2 - τ := by linarith
  have hnum : 0 < (2 - τ) * Real.exp (2 * u) + τ := by positivity
  have hden : 0 < τ * Real.exp (2 * u) + (2 - τ) := by positivity
  have hR := div_pos hnum hden
  have hup : ((2 - τ) * Real.exp (2 * u) + τ) / (τ * Real.exp (2 * u) + (2 - τ)) ≤
      (2 - τ) / τ := by
    rw [div_le_div_iff₀ hden hτ0]
    nlinarith
  have hlo : τ / (2 - τ) ≤
      ((2 - τ) * Real.exp (2 * u) + τ) / (τ * Real.exp (2 * u) + (2 - τ)) := by
    rw [div_le_div_iff₀ hc hden]
    nlinarith [mul_nonneg (sub_nonneg.mpr hτ1) hw0.le]
  have h1 := Real.log_le_log hR hup
  have h2 := Real.log_le_log (div_pos hτ0 hc) hlo
  rw [show τ / (2 - τ) = ((2 - τ) / τ)⁻¹ by rw [inv_div], Real.log_inv] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- `lem:logit-lift` as stated in the paper: for `P ∈ 𝒞_{T,d}`, `0 < τ ≤ 1` and a polynomial `r`
of degree at most `k` with `|r(u) - ψ_τ(u)| ≤ ζ` for `|u| ≤ T`, the comparison model `P°` with
logits `r(ℓ_P)` has logit rank at most `binom(d + k, d)` at every cut `t < T`, and its logits on
prefixes of length `< T` have magnitude at most `M_τ + ζ`. -/
theorem logitLift_inClass {p : NextBit} {T d k : ℕ} (hp : InClass T d p) {τ ζ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (r : Polynomial ℝ) (hr : r.natDegree ≤ k)
    (happrox : ∀ u : ℝ, |u| ≤ T → |r.eval u - softclip τ u| ≤ ζ) :
    LogitClass T (softclipBound τ + ζ) (Nat.choose (d + k) d)
      (ofLogit fun h => r.eval (logit p h)) :=
  logitLift_logitClass_of_approx hp r hr (softclip τ) (fun u _ => abs_softclip_le hτ0 hτ1 u)
    happrox

/-- The approximation hypothesis of `logitLift_inClass` is satisfiable for every `T`: `r = 0`
works with `ζ = M_τ`. (The paper takes `r` from `lem:softclip-poly`.) -/
theorem logitLift_inClass_hyp_satisfiable {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (T : ℕ) :
    ∃ r : Polynomial ℝ, r.natDegree ≤ 0 ∧
      ∀ u : ℝ, |u| ≤ T → |r.eval u - softclip τ u| ≤ softclipBound τ :=
  ⟨0, by simp, fun u _ => by simpa using abs_softclip_le hτ0 hτ1 u⟩

/-! ### `lem:lift` -/

/-- The polynomial form of `condProb`: along the suffix `f`, read after the part `u` already
generated, the factor for a bit `b` is `g(L u)` if `b = 1` and `1 - g(L u)` if `b = 0`. -/
noncomputable def seqPoly {d : ℕ} (L : List Bool → MvPolynomial (Fin d) ℝ) (g : Polynomial ℝ) :
    List Bool → List Bool → MvPolynomial (Fin d) ℝ
  | _, [] => 1
  | u, b :: f => (if b then Polynomial.aeval (L u) g else 1 - Polynomial.aeval (L u) g) *
      seqPoly L g (u ++ [b]) f

theorem totalDegree_seqPoly_le {d k : ℕ} (L : List Bool → MvPolynomial (Fin d) ℝ)
    (hL : ∀ u, (L u).totalDegree ≤ 1) (g : Polynomial ℝ) (hg : g.natDegree ≤ k)
    (u f : List Bool) : (seqPoly L g u f).totalDegree ≤ f.length * k := by
  induction f generalizing u with
  | nil => simp [seqPoly]
  | cons b f ih =>
    have hgL : (Polynomial.aeval (L u) g).totalDegree ≤ k :=
      (totalDegree_aeval_le _ _).trans (by simpa using Nat.mul_le_mul hg (hL u))
    have hfac : (if b then Polynomial.aeval (L u) g
        else 1 - Polynomial.aeval (L u) g).totalDegree ≤ k := by
      split
      · exact hgL
      · exact (totalDegree_sub _ _).trans (max_le (by simp) hgL)
    simp only [seqPoly, List.length_cons]
    calc _ ≤ _ := totalDegree_mul _ _
      _ ≤ k + f.length * k := Nat.add_le_add hfac (ih _)
      _ = (f.length + 1) * k := by ring

/-- If `ℓ(h u) = L(u)(x)` for every suffix `u` with `|u| < m`, then for `|u| + |f| ≤ m` the
conditional probability of `f` after `h u` under `q = g ∘ ℓ` is `seqPoly L g u f` evaluated at
`x`. -/
theorem condProb_eq_eval_seqPoly {d : ℕ} (ℓ : List Bool → ℝ) (g : Polynomial ℝ)
    (L : List Bool → MvPolynomial (Fin d) ℝ) (x : Fin d → ℝ) (h : List Bool) (mlen : ℕ)
    (hℓ : ∀ u : List Bool, u.length < mlen → ℓ (h ++ u) = MvPolynomial.eval x (L u))
    (u f : List Bool) (hle : u.length + f.length ≤ mlen) :
    condProb (fun h' => g.eval (ℓ h')) (h ++ u) f = MvPolynomial.eval x (seqPoly L g u f) := by
  induction f generalizing u with
  | nil => simp [seqPoly]
  | cons b f ih =>
    have hu : u.length < mlen := by simp at hle; omega
    have hb : bitProb (fun h' => g.eval (ℓ h')) (h ++ u) b = MvPolynomial.eval x
        (if b then Polynomial.aeval (L u) g else 1 - Polynomial.aeval (L u) g) := by
      cases b <;> simp [bitProb, eval_aeval, hℓ u hu]
    rw [condProb_cons, hb, List.append_assoc, ih (u ++ [b]) (by simp at hle ⊢; omega), seqPoly,
      map_mul]

/-- `lem:lift` at one cut: if the logit matrix of `ℓ` at cut `t` has rank at most `d` and `g` has
degree at most `k`, the probability matrix `G_t` of the model `q(h) = g(ℓ(h))` has rank at most
`binom(d + T k, d)`. No condition `0 < g < 1` is needed for the rank bound. -/
theorem rank_probCutMatrix_polynomial_le {ℓ : List Bool → ℝ} {T t d k : ℕ}
    (hℓ : (logitCutMatrix ℓ T t).rank ≤ d) (g : Polynomial ℝ) (hg : g.natDegree ≤ k) :
    (probCutMatrix (fun h => g.eval (ℓ h)) T t).rank ≤ Nat.choose (d + T * k) d := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_factor_of_rank_le _ hℓ
  let y' : List Bool → Fin d → ℝ := fun u =>
    if hu : u.length < T - t then y ⟨⟨u.length, hu⟩, ⟨u, rfl⟩⟩ else 0
  have hfac : ∀ (h : Word t) (u : List Bool), u.length < T - t →
      ℓ (h.toList ++ u) = MvPolynomial.eval (x h) (linForm (y' u)) := by
    intro h u hu
    rw [eval_linForm]
    have := hxy h ⟨⟨u.length, hu⟩, ⟨u, rfl⟩⟩
    simp only [y', hu, ↓reduceDIte]
    exact this
  refine rank_le_of_eval_mvPolynomial _ x
    (fun f => seqPoly (fun u => linForm (y' u)) g [] f.toList) (fun f => ?_) (fun h f => ?_)
  · refine (totalDegree_seqPoly_le _ (fun u => totalDegree_linForm_le _) g hg _ _).trans ?_
    rw [List.Vector.toList_length]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  · have := condProb_eq_eval_seqPoly ℓ g _ (x h) h.toList (T - t) (hfac h) [] f.toList (by simp)
    simpa [probCutMatrix] using this

/-- `lem:lift`: if the logit matrices of `ℓ` have rank at most `d` at every cut `t < T` and `g` has
degree at most `k`, the model `q(h) = g(ℓ(h))` has probability rank at most `binom(d + T k, d)`. -/
theorem probRank_polynomial_le {ℓ : List Bool → ℝ} {T d k : ℕ}
    (hℓ : ∀ t < T, (logitCutMatrix ℓ T t).rank ≤ d) (g : Polynomial ℝ) (hg : g.natDegree ≤ k) :
    probRank (fun h => g.eval (ℓ h)) T ≤ Nat.choose (d + T * k) d :=
  (probRank_le_iff _ _ _).mpr fun t _ => rank_probCutMatrix_polynomial_le (hℓ t ‹_›) g hg

/-- `lem:lift` for the surrogate `P̃(1 | h) = g(ℓ_P(h))` of `eq:surrogate`, with `P` in the class
`𝒞` (any logit bound `Λ`, rank `d`). -/
theorem probRank_lift_le {p : NextBit} {T d k : ℕ} {Λ : ℝ} (hp : LogitClass T Λ d p)
    (g : Polynomial ℝ) (hg : g.natDegree ≤ k) :
    probRank (fun h => g.eval (logit p h)) T ≤ Nat.choose (d + T * k) d :=
  probRank_polynomial_le hp.rank_le g hg

/-- Full support of the surrogate `P̃` of `eq:surrogate`: if `0 < g(u) < 1` for `|u| ≤ Λ` and the
logits of `P` on prefixes of length `< T` are bounded by `Λ`. -/
theorem lift_fullSupport {p : NextBit} {T d : ℕ} {Λ : ℝ} (hp : LogitClass T Λ d p)
    (g : Polynomial ℝ) (hg : ∀ u, |u| ≤ Λ → 0 < g.eval u ∧ g.eval u < 1) :
    FullSupport T fun h => g.eval (logit p h) :=
  fun h hh => hg _ (hp.logit_le h hh)

/-! ### Linear state recursions (`lem:hard-teacher`) -/

section LinearState

variable {ι : Type*}

/-- The state map along a suffix `b₁ ⋯ b_m` read from position `n`:
`A_{n+m-1, b_m} ∘ ⋯ ∘ A_{n, b₁}`. -/
def transfer (A : ℕ → Bool → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : ℕ → List Bool → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)
  | _, [] => LinearMap.id
  | n, b :: f => transfer A (n + 1) f ∘ₗ A n b

theorem state_append (s : List Bool → ι → ℝ) (A : ℕ → Bool → (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hs : ∀ h b, s (h ++ [b]) = A h.length b (s h)) (h f : List Bool) :
    s (h ++ f) = transfer A h.length f (s h) := by
  induction f generalizing h with
  | nil => simp [transfer]
  | cons b f ih =>
    rw [show h ++ b :: f = (h ++ [b]) ++ f by simp, ih, hs]
    simp [transfer]

/-- The rank argument of `lem:hard-teacher` (also used in `cor:allTV`): if the logits are read
linearly, `ℓ(h) = w_{|h|}ᵀ s(h)`, from a state that evolves linearly, `s(h b) = A_{|h|, b} s(h)`,
then every cut logit matrix has rank at most the state dimension. -/
theorem rank_logitCutMatrix_le_of_linearState [Fintype ι] (s : List Bool → ι → ℝ)
    (A : ℕ → Bool → (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (w : ℕ → ι → ℝ) (ℓ : List Bool → ℝ)
    (hs : ∀ h b, s (h ++ [b]) = A h.length b (s h))
    (hℓ : ∀ h, ℓ h = ∑ i, w h.length i * s h i) (T t : ℕ) :
    (logitCutMatrix ℓ T t).rank ≤ Fintype.card ι := by
  classical
  refine rank_le_card_of_factor _ (fun h => s h.toList)
    (fun f j => ∑ i, w (t + f.1) i *
      transfer A t f.2.toList (fun k => if j = k then 1 else 0) i) fun h f => ?_
  simp only [logitCutMatrix]
  rw [hℓ, state_append s A hs, LinearMap.pi_apply_eq_sum_univ (transfer A _ _)]
  simp only [List.length_append, List.Vector.toList_length, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- `rank_logitCutMatrix_le_of_linearState` with state space `ℝ^D`. -/
theorem rank_logitCutMatrix_le_of_linearState_fin {D : ℕ} (s : List Bool → Fin D → ℝ)
    (A : ℕ → Bool → (Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ)) (w : ℕ → Fin D → ℝ) (ℓ : List Bool → ℝ)
    (hs : ∀ h b, s (h ++ [b]) = A h.length b (s h))
    (hℓ : ∀ h, ℓ h = ∑ i, w h.length i * s h i) (T t : ℕ) :
    (logitCutMatrix ℓ T t).rank ≤ D := by
  simpa using rank_logitCutMatrix_le_of_linearState s A w ℓ hs hℓ T t

end LinearState

end LowLogitRank.PolyRank
