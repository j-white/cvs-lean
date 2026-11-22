import Mathlib
import Cvs.Upstream.CourantFischerAscending
import Cvs.Upstream.WhiteningInvariantEigenvalues

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Courant–Fischer for a symmetric operator, interlacing across a codimension, and the defect identity

For symmetric `T` with ascending eigenvalues `λ↑_k` (`CourantFischerAscending`'s matrix form, for operators, compressions and pencils
via Cvs.Upstream.WhiteningInvariantEigenvalues): min-max and max-min; `λ↑_i(T_{Bᗮ}) ≤ λ↑_{i+dim B}(T_S)`; `⟪Tv, v⟫ = λ↑_t‖v‖² − Σ_{j<t}(λ↑_t − λ↑_j)⟪u_j, v⟫²
+ Σ_{j>t}(λ↑_j − λ↑_t)⟪u_j, v⟫²`; weighted row sums or, for `T ≥ 0`, the trace bound a span over a Gram floor.
-/

noncomputable section

open Module
open scoped RealInnerProductSpace Matrix

namespace Cvs.Upstream.CourantFischerInterlacing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →ₗ[ℝ] E}

/-! ### Ascending eigenvalues and eigenvectors -/

/-- The eigenvalues of `T` in ascending order, `λ↑_0 ≤ λ↑_1 ≤ ⋯`. -/
def eigAsc (hT : T.IsSymmetric) (k : Fin (finrank ℝ E)) : ℝ := hT.eigenvalues rfl k.rev

/-- An orthonormal eigenvector of `T` at `λ↑_k`. -/
def vecAsc (hT : T.IsSymmetric) (k : Fin (finrank ℝ E)) : E := hT.eigenvectorBasis rfl k.rev

theorem eigAsc_monotone (hT : T.IsSymmetric) : Monotone (eigAsc hT) :=
  fun _ _ h => hT.eigenvalues_antitone rfl (Fin.rev_le_rev.2 h)

theorem apply_vecAsc (hT : T.IsSymmetric) (k : Fin (finrank ℝ E)) :
    T (vecAsc hT k) = eigAsc hT k • vecAsc hT k := by
  simp [vecAsc, eigAsc]

/-- **Parseval in the ascending eigenbasis**: `‖v‖² = Σ_k ⟪u_k, v⟫²`. -/
theorem norm_sq_eq_sum (hT : T.IsSymmetric) (v : E) :
    ‖v‖ ^ 2 = ∑ k, ⟪vecAsc hT k, v⟫ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_sq_inner_right v]
  exact (Fintype.sum_equiv Fin.revPerm _ _ fun k => rfl).symm

/-- **The form in the ascending eigenbasis**: `⟪Tv, v⟫ = Σ_k λ↑_k⟪u_k, v⟫²`. -/
theorem inner_eq_sum (hT : T.IsSymmetric) (v : E) :
    ⟪T v, v⟫ = ∑ k, eigAsc hT k * ⟪vecAsc hT k, v⟫ ^ 2 := by
  rw [← (hT.eigenvectorBasis rfl).sum_inner_mul_inner (T v) v]
  refine (Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_).symm
  have hb : T (hT.eigenvectorBasis rfl k.rev) = eigAsc hT k • hT.eigenvectorBasis rfl k.rev :=
    apply_vecAsc hT k
  have h : ⟪T v, hT.eigenvectorBasis rfl k.rev⟫ = eigAsc hT k * ⟪hT.eigenvectorBasis rfl k.rev, v⟫ := by
    rw [hT v, hb, real_inner_smul_right, real_inner_comm]
  rw [Fin.revPerm_apply, h, vecAsc]
  ring

/-! ### The spectral subspaces as kernels of coefficient maps -/

/-- The coefficients `v ↦ (⟪u_j, v⟫)_{j ∈ s}`. -/
def coeffs (hT : T.IsSymmetric) (s : Finset (Fin (finrank ℝ E))) : E →ₗ[ℝ] (s → ℝ) :=
  LinearMap.pi fun j => innerₗ E (vecAsc hT j)

theorem coeffs_apply (hT : T.IsSymmetric) (s : Finset (Fin (finrank ℝ E))) (v : E) (j : s) :
    coeffs hT s v j = ⟪vecAsc hT j, v⟫ := rfl

/-- The span of the eigenvectors at or below `λ↑_k`: no component above `k`. -/
def botSpace (hT : T.IsSymmetric) (k : Fin (finrank ℝ E)) : Submodule ℝ E :=
  LinearMap.ker (coeffs hT (Finset.Ioi k))

/-- The span of the eigenvectors at or above `λ↑_k`: no component below `k`. -/
def topSpace (hT : T.IsSymmetric) (k : Fin (finrank ℝ E)) : Submodule ℝ E :=
  LinearMap.ker (coeffs hT (Finset.Iio k))

theorem mem_botSpace {hT : T.IsSymmetric} {k : Fin (finrank ℝ E)} {v : E} :
    v ∈ botSpace hT k ↔ ∀ j, k < j → ⟪vecAsc hT j, v⟫ = 0 := by
  simp only [botSpace, LinearMap.mem_ker, funext_iff, coeffs_apply, Pi.zero_apply, Subtype.forall,
    Finset.mem_Ioi]

theorem mem_topSpace {hT : T.IsSymmetric} {k : Fin (finrank ℝ E)} {v : E} :
    v ∈ topSpace hT k ↔ ∀ j, j < k → ⟪vecAsc hT j, v⟫ = 0 := by
  simp only [topSpace, LinearMap.mem_ker, funext_iff, coeffs_apply, Pi.zero_apply, Subtype.forall,
    Finset.mem_Iio]

theorem finrank_ker_ge (hT : T.IsSymmetric) (s : Finset (Fin (finrank ℝ E))) :
    finrank ℝ E ≤ finrank ℝ (LinearMap.ker (coeffs hT s)) + s.card := by
  have h := LinearMap.finrank_range_add_finrank_ker (coeffs hT s)
  have hr : finrank ℝ (LinearMap.range (coeffs hT s)) ≤ s.card := by
    refine (Submodule.finrank_le _).trans ?_
    simp
  omega

theorem finrank_botSpace (hT : T.IsSymmetric) (k : Fin (finrank ℝ E)) :
    (k : ℕ) + 1 ≤ finrank ℝ (botSpace hT k) := by
  have h := finrank_ker_ge hT (Finset.Ioi k)
  rw [Fin.card_Ioi] at h
  have := k.2
  unfold botSpace
  omega

theorem finrank_topSpace (hT : T.IsSymmetric) (k : Fin (finrank ℝ E)) :
    finrank ℝ E ≤ finrank ℝ (topSpace hT k) + k := by
  have h := finrank_ker_ge hT (Finset.Iio k)
  rw [Fin.card_Iio] at h
  exact h

/-- On the eigenvectors at or below `λ↑_k`, `⟪Tv, v⟫ ≤ λ↑_k‖v‖²`. -/
theorem inner_le_of_mem_botSpace (hT : T.IsSymmetric) {k : Fin (finrank ℝ E)} {v : E}
    (hv : v ∈ botSpace hT k) : ⟪T v, v⟫ ≤ eigAsc hT k * ‖v‖ ^ 2 := by
  rw [inner_eq_sum hT, norm_sq_eq_sum hT, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt j k with h | h
  · exact mul_le_mul_of_nonneg_right (eigAsc_monotone hT h) (sq_nonneg _)
  · rw [mem_botSpace.1 hv j h]; simp

/-- On the eigenvectors at or above `λ↑_k`, `λ↑_k‖v‖² ≤ ⟪Tv, v⟫`. -/
theorem le_inner_of_mem_topSpace (hT : T.IsSymmetric) {k : Fin (finrank ℝ E)} {v : E}
    (hv : v ∈ topSpace hT k) : eigAsc hT k * ‖v‖ ^ 2 ≤ ⟪T v, v⟫ := by
  rw [inner_eq_sum hT, norm_sq_eq_sum hT, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge j k with h | h
  · rw [mem_topSpace.1 hv j h]; simp
  · exact mul_le_mul_of_nonneg_right (eigAsc_monotone hT h) (sq_nonneg _)

/-! ### Courant–Fischer -/

/-- Two subspaces whose dimensions add past `finrank E` meet in a nonzero vector. -/
theorem exists_ne_zero_mem_inf {U W : Submodule ℝ E}
    (h : finrank ℝ E < finrank ℝ U + finrank ℝ W) : ∃ v ∈ U ⊓ W, v ≠ 0 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
  have h2 := Submodule.finrank_le (U ⊔ W)
  have hne : U ⊓ W ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

/-- **Courant–Fischer, min-max (the counting lemma).** A subspace of dimension `≥ k + 1` with `⟪Tv, v⟫ ≤ μ‖v‖²` on it
gives `λ↑_k ≤ μ`: at least `k + 1` eigenvalues are `≤ μ`. -/
theorem eigAsc_le_of_forall_inner_le (hT : T.IsSymmetric) {S : Submodule ℝ E} {μ : ℝ}
    (k : Fin (finrank ℝ E)) (hS : (k : ℕ) + 1 ≤ finrank ℝ S)
    (h : ∀ v ∈ S, ⟪T v, v⟫ ≤ μ * ‖v‖ ^ 2) : eigAsc hT k ≤ μ := by
  have ht := finrank_topSpace hT k
  obtain ⟨v, ⟨hvS, hvT⟩, hv0⟩ := exists_ne_zero_mem_inf (U := S) (W := topSpace hT k) (by omega)
  have h1 := le_inner_of_mem_topSpace hT hvT
  have h2 := h v hvS
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith

/-- **Courant–Fischer, max-min.** A floor `μ‖v‖² ≤ ⟪Tv, v⟫` on a subspace of codimension `≤ k` gives `μ ≤ λ↑_k`. -/
theorem le_eigAsc_of_floor (hT : T.IsSymmetric) {V : Submodule ℝ E} {μ : ℝ}
    (k : Fin (finrank ℝ E)) (hV : finrank ℝ E ≤ finrank ℝ V + k)
    (h : ∀ v ∈ V, μ * ‖v‖ ^ 2 ≤ ⟪T v, v⟫) : μ ≤ eigAsc hT k := by
  have hb := finrank_botSpace hT k
  obtain ⟨v, ⟨hvV, hvB⟩, hv0⟩ := exists_ne_zero_mem_inf (U := V) (W := botSpace hT k) (by omega)
  have h1 := inner_le_of_mem_botSpace hT hvB
  have h2 := h v hvV
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith

/-- **Courant–Fischer, max-min, as a greatest element**: `λ↑_k` is the greatest `μ` with a floor on a subspace of
codimension `≤ k`, attained on the eigenvectors at or above `λ↑_k`. -/
theorem isGreatest_eigAsc (hT : T.IsSymmetric) (k : Fin (finrank ℝ E)) :
    IsGreatest {μ | ∃ V : Submodule ℝ E, finrank ℝ E ≤ finrank ℝ V + k ∧ ∀ v ∈ V, μ * ‖v‖ ^ 2 ≤ ⟪T v, v⟫}
      (eigAsc hT k) :=
  ⟨⟨topSpace hT k, finrank_topSpace hT k, fun _ hv => le_inner_of_mem_topSpace hT hv⟩,
    fun _ ⟨_, hV, h⟩ => le_eigAsc_of_floor hT k hV h⟩

/-! ### Compressions and interlacing -/

/-- The compression `P_S T|_S` of `T` to `S`. -/
def compr (T : E →ₗ[ℝ] E) (S : Submodule ℝ E) : S →ₗ[ℝ] S :=
  S.orthogonalProjectionOnto.toLinearMap ∘ₗ T ∘ₗ S.subtype

theorem inner_compr (T : E →ₗ[ℝ] E) (S : Submodule ℝ E) (u w : S) :
    ⟪compr T S u, w⟫ = ⟪T u, (w : E)⟫ := by
  simp only [compr, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    ContinuousLinearMap.coe_coe]
  rw [Submodule.coe_inner, ← Submodule.starProjection_apply,
    Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 w.2]

theorem isSymmetric_compr (hT : T.IsSymmetric) (S : Submodule ℝ E) : (compr T S).IsSymmetric :=
  fun u w => by
    have h2 := inner_compr T S w u
    rw [real_inner_comm] at h2
    rw [h2, inner_compr, hT]
    exact real_inner_comm _ _

/-- **Courant–Fischer for a compression**: if `U ∩ S` has dimension `≥ i + 1` and `⟪Tv, v⟫ ≤ μ‖v‖²` on `U`, then
`λ↑_i(T_S) ≤ μ`. -/
theorem eigAsc_compr_le (hT : T.IsSymmetric) (S U : Submodule ℝ E) {μ : ℝ} (i : Fin (finrank ℝ S))
    (hU : (i : ℕ) + 1 ≤ finrank ℝ (U ⊓ S : Submodule ℝ E))
    (h : ∀ v ∈ U, ⟪T v, v⟫ ≤ μ * ‖v‖ ^ 2) : eigAsc (isSymmetric_compr hT S) i ≤ μ := by
  refine eigAsc_le_of_forall_inner_le (isSymmetric_compr hT S) (S := (U ⊓ S).comap S.subtype) i ?_
    fun w hw => ?_
  · rw [(Submodule.comapSubtypeEquivOfLe (inf_le_right : U ⊓ S ≤ S)).finrank_eq]
    exact hU
  · rw [inner_compr, Submodule.coe_norm]
    exact h _ (Submodule.mem_inf.1 hw).1

/-- The bottom eigenvectors of `T_S`, as a subspace of `E` inside `S`. -/
def botIn (hT : T.IsSymmetric) (S : Submodule ℝ E) (k : Fin (finrank ℝ S)) : Submodule ℝ E :=
  (botSpace (isSymmetric_compr hT S) k).map S.subtype

theorem botIn_le (hT : T.IsSymmetric) (S : Submodule ℝ E) (k : Fin (finrank ℝ S)) : botIn hT S k ≤ S := by
  rintro _ ⟨w, -, rfl⟩
  exact w.2

theorem finrank_botIn (hT : T.IsSymmetric) (S : Submodule ℝ E) (k : Fin (finrank ℝ S)) :
    (k : ℕ) + 1 ≤ finrank ℝ (botIn hT S k) := by
  have := finrank_botSpace (isSymmetric_compr hT S) k
  rwa [botIn, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ S.subtype_injective _)]

theorem inner_le_of_mem_botIn (hT : T.IsSymmetric) (S : Submodule ℝ E) (k : Fin (finrank ℝ S)) {v : E}
    (hv : v ∈ botIn hT S k) : ⟪T v, v⟫ ≤ eigAsc (isSymmetric_compr hT S) k * ‖v‖ ^ 2 := by
  obtain ⟨w, hw, rfl⟩ := hv
  have := inner_le_of_mem_botSpace (isSymmetric_compr hT S) hw
  rwa [inner_compr, Submodule.coe_norm] at this

/-- **Interlacing across a codimension**: if `R ⊓ H` has codimension `≤ k` in `R`, then `λ↑_i(T_H) ≤ λ↑_{i+k}(T_R)`.
At `R ≤ H`, `k = 0` this is Cauchy interlacing `λ↑_i(T_H) ≤ λ↑_i(T_R)`. -/
theorem eigAsc_compr_le_eigAsc_compr (hT : T.IsSymmetric) {R H : Submodule ℝ E} {k : ℕ}
    (hcod : finrank ℝ R ≤ finrank ℝ (R ⊓ H : Submodule ℝ E) + k) (i : Fin (finrank ℝ H))
    (hik : (i : ℕ) + k < finrank ℝ R) :
    eigAsc (isSymmetric_compr hT H) i ≤ eigAsc (isSymmetric_compr hT R) ⟨i + k, hik⟩ := by
  set U := botIn hT R ⟨i + k, hik⟩
  refine eigAsc_compr_le hT H U i ?_ fun v hv => inner_le_of_mem_botIn hT R _ hv
  have hU : (i : ℕ) + k + 1 ≤ finrank ℝ U := finrank_botIn hT R ⟨i + k, hik⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (R ⊓ H)
  have h2 : finrank ℝ (U ⊔ (R ⊓ H) : Submodule ℝ E) ≤ finrank ℝ R :=
    Submodule.finrank_mono (sup_le (botIn_le hT R _) inf_le_left)
  have h3 : finrank ℝ (U ⊓ (R ⊓ H) : Submodule ℝ E) ≤ finrank ℝ (U ⊓ H : Submodule ℝ E) :=
    Submodule.finrank_mono (inf_le_inf_left _ inf_le_right)
  omega

/-- Every subspace loses at most `dim B` dimensions to `Bᗮ`: `dim A ≤ dim(A ⊓ Bᗮ) + dim B`. -/
theorem finrank_le_finrank_inf_orthogonal_add (A B : Submodule ℝ E) :
    finrank ℝ A ≤ finrank ℝ (A ⊓ Bᗮ : Submodule ℝ E) + finrank ℝ B := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A Bᗮ
  have h2 := Submodule.finrank_le (A ⊔ Bᗮ)
  have h3 := Submodule.finrank_add_finrank_orthogonal B
  omega

/-- **Interlacing against an orthogonal complement**: for any `S, B`, `λ↑_i(T_{Bᗮ}) ≤ λ↑_{i+dim B}(T_S)`. -/
theorem eigAsc_compr_orthogonal_le (hT : T.IsSymmetric) (S B : Submodule ℝ E) (i : Fin (finrank ℝ Bᗮ))
    (hik : (i : ℕ) + finrank ℝ B < finrank ℝ S) :
    eigAsc (isSymmetric_compr hT Bᗮ) i ≤ eigAsc (isSymmetric_compr hT S) ⟨i + finrank ℝ B, hik⟩ :=
  eigAsc_compr_le_eigAsc_compr hT (finrank_le_finrank_inf_orthogonal_add S B) i hik

/-! ### Operator eigenvalues are pencil eigenvalues -/

/-- **Operator and pencil eigenvalues agree**: if `φ : (n → ℝ) ≃ E` carries `aᵀAa` to `⟪Tv, v⟫` and `aᵀGa` to
`‖v‖²`, then `λ↑_k(T)` is the `k`-th ascending eigenvalue of `PᵀAP` for every `P` with `PᵀGP = 1` (Cvs.Upstream.CourantFischerAscending, Cvs.Upstream.WhiteningInvariantEigenvalues). -/
theorem eigAsc_eq_eigAsc_gram {n : Type*} [Fintype n] [DecidableEq n] (hT : T.IsSymmetric)
    {A G P : Matrix n n ℝ} (hGP : P.transpose * G * P = 1) (hAP : (P.transpose * A * P).IsHermitian)
    (φ : (n → ℝ) ≃ₗ[ℝ] E) (hA : ∀ a, ⟪T (φ a), φ a⟫ = a ⬝ᵥ (A *ᵥ a))
    (hG : ∀ a, ‖φ a‖ ^ 2 = a ⬝ᵥ (G *ᵥ a)) (k : Fin (finrank ℝ E)) :
    eigAsc hT k = Cvs.Upstream.CourantFischerAscending.eigAsc hAP
      (Fin.cast (φ.finrank_eq.symm.trans (Module.finrank_fintype_fun_eq_card (R := ℝ))) k) := by
  have hcard : finrank ℝ E = Fintype.card n :=
    φ.finrank_eq.symm.trans (Module.finrank_fintype_fun_eq_card (R := ℝ))
  apply le_antisymm
  · obtain ⟨⟨V, hV, hfl⟩, -⟩ := isGreatest_eigAsc hT k
    have hfin : finrank ℝ (V.comap φ.toLinearMap) = finrank ℝ V := by
      rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    exact Cvs.Upstream.CourantFischerAscending.le_eigAsc_of_floor_gram hGP hAP (V := V.comap φ.toLinearMap) (r := k) (by omega)
      (fun a ha => by rw [← hG, ← hA]; exact hfl _ ha) (by omega)
  · obtain ⟨⟨V, hV, hfl⟩, -⟩ := Cvs.Upstream.WhiteningInvariantEigenvalues.isGreatest_eigAsc_gram hGP hAP (Fin.cast hcard k)
    have hk : ((Fin.cast hcard k : Fin (Fintype.card n)) : ℕ) = k := rfl
    have hfin : finrank ℝ (V.map φ.toLinearMap) = finrank ℝ V := LinearEquiv.finrank_map_eq φ V
    refine le_eigAsc_of_floor hT k (V := V.map φ.toLinearMap) (by omega) fun v hv => ?_
    obtain ⟨a, ha, rfl⟩ := hv
    rw [LinearEquiv.coe_coe, hG, hA]
    exact hfl a ha

/-! ### The angle floor -/

/-! ### The defect identity -/

/-- The defect of `v` below `λ↑_t`, `Σ_{j<t}(λ↑_t − λ↑_j)⟪u_j, v⟫²`. -/
def botDefect (hT : T.IsSymmetric) (t : Fin (finrank ℝ E)) (v : E) : ℝ :=
  ∑ j ∈ Finset.Iio t, (eigAsc hT t - eigAsc hT j) * ⟪vecAsc hT j, v⟫ ^ 2

/-- The surplus of `v` above `λ↑_t`, `Σ_{j>t}(λ↑_j − λ↑_t)⟪u_j, v⟫²`. -/
def topSurplus (hT : T.IsSymmetric) (t : Fin (finrank ℝ E)) (v : E) : ℝ :=
  ∑ j ∈ Finset.Ioi t, (eigAsc hT j - eigAsc hT t) * ⟪vecAsc hT j, v⟫ ^ 2

/-- **The defect identity**: `⟪Tv, v⟫ = λ↑_t‖v‖² − botDefect + topSurplus`. -/
theorem inner_eq_defect (hT : T.IsSymmetric) (t : Fin (finrank ℝ E)) (v : E) :
    ⟪T v, v⟫ = eigAsc hT t * ‖v‖ ^ 2 - botDefect hT t v + topSurplus hT t v := by
  have hb : botDefect hT t v
      = ∑ j, if j < t then (eigAsc hT t - eigAsc hT j) * ⟪vecAsc hT j, v⟫ ^ 2 else 0 := by
    rw [botDefect, ← Finset.sum_filter]; congr 1; ext j; simp
  have ht : topSurplus hT t v
      = ∑ j, if t < j then (eigAsc hT j - eigAsc hT t) * ⟪vecAsc hT j, v⟫ ^ 2 else 0 := by
    rw [topSurplus, ← Finset.sum_filter]; congr 1; ext j; simp
  rw [inner_eq_sum hT, norm_sq_eq_sum hT, hb, ht, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy j t with h | rfl | h
  · rw [if_pos h, if_neg (not_lt.2 h.le)]; ring
  · simp
  · rw [if_neg (not_lt.2 h.le), if_pos h]; ring

theorem topSurplus_nonneg (hT : T.IsSymmetric) (t : Fin (finrank ℝ E)) (v : E) : 0 ≤ topSurplus hT t v :=
  Finset.sum_nonneg fun _ hj =>
    mul_nonneg (sub_nonneg.2 (eigAsc_monotone hT (Finset.mem_Ioi.1 hj).le)) (sq_nonneg _)

/-- **The floor is the defect bound up to the surplus**: `b‖v‖² ≤ ⟪Tv, v⟫` iff
`botDefect ≤ (λ↑_t − b)‖v‖² + topSurplus`. -/
theorem le_inner_iff_botDefect (hT : T.IsSymmetric) (t : Fin (finrank ℝ E)) (v : E) (b : ℝ) :
    b * ‖v‖ ^ 2 ≤ ⟪T v, v⟫ ↔ botDefect hT t v ≤ (eigAsc hT t - b) * ‖v‖ ^ 2 + topSurplus hT t v := by
  rw [inner_eq_defect hT t v]
  constructor <;> intro h <;> linarith

theorem botDefect_eq_zero (hT : T.IsSymmetric) {t : Fin (finrank ℝ E)} (ht : (t : ℕ) = 0) (v : E) :
    botDefect hT t v = 0 :=
  Finset.sum_eq_zero fun j hj => by
    have := Fin.lt_def.1 (Finset.mem_Iio.1 hj); omega

/-! ### The Rayleigh quotient on a span: weighted row sums, traces and a Gram floor -/

section Span

variable {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E] in
/-- The form on a span in coordinates: `⟪T(Σ a_i e_i), Σ a_i e_i⟫ = Σ_{i,j} a_i a_j⟪Te_i, e_j⟫`. -/
theorem inner_sum_smul_sum (hT : T.IsSymmetric) (e : ι → E) (a : ι → ℝ) :
    ⟪T (∑ i, a i • e i), ∑ i, a i • e i⟫ = ∑ i, ∑ j, a i * a j * ⟪T (e i), e j⟫ := by
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hT (e j) (e i), real_inner_comm (T (e i))]
  ring

omit [FiniteDimensional ℝ E] in
/-- The form on a span is the quadratic form of the matrix `(⟪Te_i, e_j⟫)`. -/
theorem inner_sum_smul_eq_dotProduct (hT : T.IsSymmetric) (e : ι → E) (a : ι → ℝ) :
    ⟪T (∑ i, a i • e i), ∑ i, a i • e i⟫ = a ⬝ᵥ (Matrix.of (fun i j => ⟪T (e i), e j⟫) *ᵥ a) := by
  rw [inner_sum_smul_sum hT]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [FiniteDimensional ℝ E] in
/-- **The Schur test on a span**: with weights `w > 0` and `Σ_j |⟪Te_i, e_j⟫|·w_j/w_i ≤ m` for every `i`,
`⟪Tv, v⟫ ≤ m·Σ_i a_i²` at `v = Σ_i a_i e_i`. At `w ≡ 1` these are the row sums. -/
theorem inner_le_weightedRowSum (hT : T.IsSymmetric) (e : ι → E) {w : ι → ℝ} (hw : ∀ i, 0 < w i) {m : ℝ}
    (hm : ∀ i, ∑ j, |⟪T (e i), e j⟫| * (w j / w i) ≤ m) (a : ι → ℝ) :
    ⟪T (∑ i, a i • e i), ∑ i, a i • e i⟫ ≤ m * ∑ i, a i ^ 2 := by
  rw [inner_sum_smul_sum hT]
  have hsym : ∀ i j, |⟪T (e i), e j⟫| = |⟪T (e j), e i⟫| := fun i j => by
    rw [hT, real_inner_comm]
  have key : ∀ i j, a i * a j * ⟪T (e i), e j⟫
      ≤ (a i ^ 2 * (|⟪T (e i), e j⟫| * (w j / w i)) + a j ^ 2 * (|⟪T (e j), e i⟫| * (w i / w j))) / 2 := by
    intro i j
    rw [← hsym i j]
    have hr : 0 < w j / w i := div_pos (hw j) (hw i)
    have hr' : w i / w j = (w j / w i)⁻¹ := (inv_div _ _).symm
    rw [hr']
    set r := w j / w i
    have h1 : a i * a j * ⟪T (e i), e j⟫ ≤ |a i| * |a j| * |⟪T (e i), e j⟫| := by
      rw [← abs_mul, ← abs_mul]; exact le_abs_self _
    have e1 : (|a i| * r - |a j|) ^ 2 * r⁻¹ = |a i| ^ 2 * r - 2 * (|a i| * |a j|) + |a j| ^ 2 * r⁻¹ := by
      field_simp; ring
    have h2 : |a i| * |a j| ≤ (a i ^ 2 * r + a j ^ 2 * r⁻¹) / 2 := by
      rw [← sq_abs (a i), ← sq_abs (a j)]
      nlinarith [mul_nonneg (sq_nonneg (|a i| * r - |a j|)) (inv_nonneg.2 hr.le)]
    have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg ⟪T (e i), e j⟫)
    nlinarith
  calc ∑ i, ∑ j, a i * a j * ⟪T (e i), e j⟫
      ≤ ∑ i, ∑ j, (a i ^ 2 * (|⟪T (e i), e j⟫| * (w j / w i))
          + a j ^ 2 * (|⟪T (e j), e i⟫| * (w i / w j))) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = ∑ i, a i ^ 2 * ∑ j, |⟪T (e i), e j⟫| * (w j / w i) := by
        simp only [add_div, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm (f := fun i j => a j ^ 2 * (|⟪T (e j), e i⟫| * (w i / w j)) / 2)]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, a i ^ 2 * m := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hm i) (sq_nonneg _)
    _ = m * ∑ i, a i ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

omit [FiniteDimensional ℝ E] in
/-- **Cauchy–Schwarz for a nonnegative symmetric operator**: `⟪Tu, w⟫² ≤ ⟪Tu, u⟫⟪Tw, w⟫`. -/
theorem inner_sq_le_of_nonneg (hT : T.IsSymmetric) (hpos : ∀ v, 0 ≤ ⟪T v, v⟫) (u w : E) :
    ⟪T u, w⟫ ^ 2 ≤ ⟪T u, u⟫ * ⟪T w, w⟫ := by
  have hwu : ⟪T w, u⟫ = ⟪T u, w⟫ := by rw [hT, real_inner_comm]
  have hq : ∀ s r : ℝ, ⟪T (s • u + r • w), s • u + r • w⟫
      = s ^ 2 * ⟪T u, u⟫ + 2 * s * r * ⟪T u, w⟫ + r ^ 2 * ⟪T w, w⟫ := by
    intro s r
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hwu]
    ring
  set A := ⟪T u, u⟫
  set B := ⟪T u, w⟫
  set C := ⟪T w, w⟫
  have hC : 0 ≤ C := hpos w
  rcases eq_or_lt_of_le hC with hC0 | hC0
  · by_contra hlt
    have hB : B ≠ 0 := by
      intro hB; rw [hB] at hlt; rw [← hC0] at hlt; simp at hlt
    have h := hpos ((1 : ℝ) • u + (-(A + 1) / (2 * B)) • w)
    rw [hq, ← hC0] at h
    have e : (1 : ℝ) ^ 2 * A + 2 * 1 * (-(A + 1) / (2 * B)) * B + (-(A + 1) / (2 * B)) ^ 2 * 0 = -1 := by
      field_simp; ring
    rw [e] at h
    linarith
  · have h := hpos (C • u + (-B) • w)
    rw [hq] at h
    nlinarith

omit [FiniteDimensional ℝ E] in
/-- **The trace bound on a span**: if `⟪Tv, v⟫ ≥ 0` everywhere, `⟪Tv, v⟫ ≤ (Σ_i ⟪Te_i, e_i⟫)·Σ_i a_i²` at
`v = Σ_i a_i e_i`. -/
theorem inner_le_trace (hT : T.IsSymmetric) (hpos : ∀ v, 0 ≤ ⟪T v, v⟫) (e : ι → E) (a : ι → ℝ) :
    ⟪T (∑ i, a i • e i), ∑ i, a i • e i⟫ ≤ (∑ i, ⟪T (e i), e i⟫) * ∑ i, a i ^ 2 := by
  rw [inner_sum_smul_sum hT]
  set s : ι → ℝ := fun i => Real.sqrt ⟪T (e i), e i⟫
  have hs : ∀ i, s i ^ 2 = ⟪T (e i), e i⟫ := fun i => Real.sq_sqrt (hpos _)
  have hij : ∀ i j, a i * a j * ⟪T (e i), e j⟫ ≤ (|a i| * s i) * (|a j| * s j) := by
    intro i j
    have h1 : |⟪T (e i), e j⟫| ≤ s i * s j := by
      rw [← Real.sqrt_mul (hpos _)]; exact Real.abs_le_sqrt (inner_sq_le_of_nonneg hT hpos _ _)
    calc a i * a j * ⟪T (e i), e j⟫ ≤ |a i * a j * ⟪T (e i), e j⟫| := le_abs_self _
      _ = |a i| * |a j| * |⟪T (e i), e j⟫| := by rw [abs_mul, abs_mul]
      _ ≤ |a i| * |a j| * (s i * s j) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  calc ∑ i, ∑ j, a i * a j * ⟪T (e i), e j⟫ ≤ ∑ i, ∑ j, (|a i| * s i) * (|a j| * s j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
    _ = (∑ i, |a i| * s i) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ ≤ (∑ i, |a i| ^ 2) * ∑ i, s i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, ⟪T (e i), e i⟫) * ∑ i, a i ^ 2 := by simp only [sq_abs, hs]; ring

omit [FiniteDimensional ℝ E] in
/-- **The Rayleigh bound on a span over a Gram floor**: `⟪T(Σ a_i e_i), Σ a_i e_i⟫ ≤ m·Σa_i²` with `0 ≤ m` and
`g·Σa_i² ≤ ‖Σ a_i e_i‖²` give `g·⟪Tv, v⟫ ≤ m‖v‖²` on `span e`. -/
theorem mul_inner_le_of_gram (e : ι → E) {m g : ℝ}
    (hq : ∀ a : ι → ℝ, ⟪T (∑ i, a i • e i), ∑ i, a i • e i⟫ ≤ m * ∑ i, a i ^ 2) (hm0 : 0 ≤ m) (hg0 : 0 ≤ g)
    (hg : ∀ a : ι → ℝ, g * ∑ i, a i ^ 2 ≤ ‖∑ i, a i • e i‖ ^ 2) :
    ∀ v ∈ Submodule.span ℝ (Set.range e), g * ⟪T v, v⟫ ≤ m * ‖v‖ ^ 2 := by
  intro v hv
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  have h1 := mul_le_mul_of_nonneg_left (hq a) hg0
  have h2 := mul_le_mul_of_nonneg_left (hg a) hm0
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- **A Gram floor `g > 0` makes the family independent**, so `span e` has dimension `#ι`. -/
theorem finrank_span_eq_card_of_gram (e : ι → E) {g : ℝ} (hg0 : 0 < g)
    (hg : ∀ a : ι → ℝ, g * ∑ i, a i ^ 2 ≤ ‖∑ i, a i • e i‖ ^ 2) :
    finrank ℝ (Submodule.span ℝ (Set.range e)) = Fintype.card ι := by
  refine finrank_span_eq_card (Fintype.linearIndependent_iff.2 fun a ha i => ?_)
  have h := hg a
  rw [ha, norm_zero] at h
  have hs : ∑ j, a j ^ 2 = 0 := le_antisymm (by nlinarith) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  exact pow_eq_zero_iff two_ne_zero |>.1 ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 hs i
    (Finset.mem_univ _))

/-- **`k + 1` eigenvalues below a span bound**: `⟪T(Σ a_i e_i), Σ a_i e_i⟫ ≤ m·Σa_i²`, `0 ≤ m` and a Gram floor
`g > 0` give `g·λ↑_k ≤ m` for `k < dim span e`. -/
theorem mul_eigAsc_le_of_span (hT : T.IsSymmetric) (e : ι → E) {m g : ℝ}
    (hq : ∀ a : ι → ℝ, ⟪T (∑ i, a i • e i), ∑ i, a i • e i⟫ ≤ m * ∑ i, a i ^ 2) (hm0 : 0 ≤ m) (hg0 : 0 < g)
    (hg : ∀ a : ι → ℝ, g * ∑ i, a i ^ 2 ≤ ‖∑ i, a i • e i‖ ^ 2) (k : Fin (finrank ℝ E))
    (hk : (k : ℕ) + 1 ≤ finrank ℝ (Submodule.span ℝ (Set.range e))) :
    g * eigAsc hT k ≤ m := by
  have h := eigAsc_le_of_forall_inner_le hT (μ := m / g) k hk fun v hv => by
    have := mul_inner_le_of_gram e hq hm0 hg0.le hg v hv
    rw [div_mul_eq_mul_div, le_div_iff₀ hg0]
    linarith
  rw [le_div_iff₀ hg0] at h
  linarith

/-- **`k + 1` eigenvalues below the weighted row sums**: for weights `w > 0`, `Σ_j |⟪Te_i, e_j⟫|·w_j/w_i ≤ m` and a
Gram floor `g > 0`, `g·λ↑_k ≤ m` for `k < dim span e`. -/
theorem mul_eigAsc_le_of_gram (hT : T.IsSymmetric) (e : ι → E) {w : ι → ℝ} (hw : ∀ i, 0 < w i) {m g : ℝ}
    (hm : ∀ i, ∑ j, |⟪T (e i), e j⟫| * (w j / w i) ≤ m) (hg0 : 0 < g)
    (hg : ∀ a : ι → ℝ, g * ∑ i, a i ^ 2 ≤ ‖∑ i, a i • e i‖ ^ 2) (k : Fin (finrank ℝ E))
    (hk : (k : ℕ) + 1 ≤ finrank ℝ (Submodule.span ℝ (Set.range e))) :
    g * eigAsc hT k ≤ m := by
  have hι : 0 < Fintype.card ι := by
    have : finrank ℝ (Submodule.span ℝ (Set.range e)) ≤ Fintype.card ι := finrank_range_le_card (R := ℝ) e
    omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.1 hι
  have hm0 : 0 ≤ m := (Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (div_pos (hw j) (hw i)).le).trans (hm i)
  exact mul_eigAsc_le_of_span hT e (inner_le_weightedRowSum hT e hw hm) hm0 hg0 hg k hk

/-- **`k + 1` eigenvalues below the trace**: if `⟪Tv, v⟫ ≥ 0` everywhere, a Gram floor `g > 0` gives
`g·λ↑_k ≤ Σ_i ⟪Te_i, e_i⟫` for `k < dim span e`. -/
theorem mul_eigAsc_le_trace (hT : T.IsSymmetric) (hpos : ∀ v, 0 ≤ ⟪T v, v⟫) (e : ι → E) {g : ℝ}
    (hg0 : 0 < g) (hg : ∀ a : ι → ℝ, g * ∑ i, a i ^ 2 ≤ ‖∑ i, a i • e i‖ ^ 2) (k : Fin (finrank ℝ E))
    (hk : (k : ℕ) + 1 ≤ finrank ℝ (Submodule.span ℝ (Set.range e))) :
    g * eigAsc hT k ≤ ∑ i, ⟪T (e i), e i⟫ :=
  mul_eigAsc_le_of_span hT e (inner_le_trace hT hpos e) (Finset.sum_nonneg fun _ _ => hpos _) hg0 hg k hk

end Span

end Cvs.Upstream.CourantFischerInterlacing
