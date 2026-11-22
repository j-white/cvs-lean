import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.SpineClassNotOdd
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenNormGramPosDef
import Cvs.L2a.EvenRungBlockOneLowEigen
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.CoreSchurForm
import Cvs.Route.EvenGramRungFloors
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.RungTierWindowForm
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.CourantFischerAscending
import Cvs.Upstream.CourantFischerInterlacing
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tier below the whitened even rung matrix, its row sums and its trace

At `80 ≤ 2πx`, `λ↑_k(Q|R₁) = λ↑_k(SᵀTS)` (`T = evenGram x`, `S` `EvenNormGramPosDef`'s whitening of `evenNormGram x`), so
`λ↑_i(Q|span v ∩ Kᗮ) ≤ λ↑_{i+k}(SᵀTS)`; on rungs `J` with `g·cᵀc ≤ cᵀN_J c` (`g = λ_min(N_J) > 0`), weighted row sums
`≤ m` give `g·λ↑_i ≤ m`, and `EvenGramRungFloors`'s `EvenGramNonneg` gives `g·λ↑_i ≤ Σ_{j∈J} Q(rung_j)`, for `i + k < #J`.
-/

noncomputable section

open Module
open scoped RealInnerProductSpace Matrix

namespace Cvs.Route.WhitenedEvenRungTier
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom Bx rung)
open Cvs.L2a.EvenSectorReflectionBound (R1 evenGram)
open Cvs.L2a.EvenRungBlockOneLowEigen (evenNormGram)
open Cvs.Upstream.CourantFischerInterlacing (eigAsc compr isSymmetric_compr inner_compr)
open Cvs.Route.RungTierWindowForm (emb opOn isSymmetric_opOn inC range_emb)

/-! ### The even rungs and `R₁` -/

/-- **The even rungs are independent** at `80 ≤ 2πx` (`SpineClassNotOdd`'s injectivity of the even spine). -/
theorem linearIndependent_rung {x : ℕ} (hx : 80 ≤ 2 * Real.pi * x) : LinearIndependent ℝ (rung x) := by
  have e : rung x = (Cvs.Approximant.D0FloorEvenRungShare.evenPartL (Real.log_natCast_nonneg x)).comp (Cvs.Approximant.SpineSubspace.spineMap x)
      ∘ Pi.basisFun ℝ (Cvs.Approximant.SpineSubspace.SF x) := by
    funext j; rw [Function.comp_apply, Pi.basisFun_apply]; rfl
  rw [e]
  exact (Pi.basisFun ℝ _).linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr (Cvs.Approximant.SpineClassNotOdd.evenSpine_injective hx))

/-- **`dim R₁ = #SF x`** at `80 ≤ 2πx`. -/
theorem finrank_R1 {x : ℕ} (hx : 80 ≤ 2 * Real.pi * x) : finrank ℝ (R1 x) = Fintype.card (Cvs.Approximant.SpineSubspace.SF x) :=
  finrank_span_eq_card (linearIndependent_rung hx)

/-- **RH gives `EvenGramNonneg`** (`CoreSchurForm`'s `Q ≥ 0` on the even rung classes), at every `x ≥ 2`. -/
theorem evenGramNonneg_of_rh (hRH : RiemannHypothesis) {x : ℕ} (hx : 2 ≤ x) : Cvs.Route.EvenGramRungFloors.EvenGramNonneg x :=
  fun a => by rw [Cvs.Route.EvenGramRungFloors.evenGram_quad_eq_Qx]; exact Cvs.Route.CoreSchurForm.nonneg_of_rh hRH x hx _

/-! ### Coordinates of the even rungs -/

variable {x d : ℕ} {v : Fin d → Dom x}

/-- Coordinates of the even rungs in `span v ⊇ R₁`. -/
def rungC (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (j : Cvs.Approximant.SpineSubspace.SF x) : EuclideanSpace ℝ (Fin d) :=
  Classical.choose (show rung x j ∈ LinearMap.range (emb v) by
    rw [range_emb]; exact hRF (Submodule.subset_span ⟨j, rfl⟩))

theorem emb_rungC (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (j : Cvs.Approximant.SpineSubspace.SF x) :
    emb v (rungC hRF j) = rung x j :=
  Classical.choose_spec (show rung x j ∈ LinearMap.range (emb v) by
    rw [range_emb]; exact hRF (Submodule.subset_span ⟨j, rfl⟩))

/-- The even rungs as vectors of `inC v R₁`. -/
def rungV (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (j : Cvs.Approximant.SpineSubspace.SF x) : inC v (R1 x) :=
  ⟨rungC hRF j, by
    show emb v (rungC hRF j) ∈ R1 x
    rw [emb_rungC]; exact Submodule.subset_span ⟨j, rfl⟩⟩

/-- `⟪T_{R₁} rung_i, rung_j⟫ = evenGram x i j`. -/
theorem inner_rungV (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (i j : Cvs.Approximant.SpineSubspace.SF x) :
    ⟪compr (opOn x v) (inC v (R1 x)) (rungV hRF i), rungV hRF j⟫ = evenGram x i j := by
  rw [inner_compr]
  change ⟪opOn x v (rungC hRF i), rungC hRF j⟫ = _
  rw [opOn, Cvs.Route.RungTierWindowForm.inner_formOp, LinearMap.compl₁₂_apply, emb_rungC, emb_rungC]
  rfl

/-- `⟪rung_i, rung_j⟫ = evenNormGram x i j` in coordinates. -/
theorem inner_rungV_rungV (hv : Orthonormal ℝ v) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v))
    (i j : Cvs.Approximant.SpineSubspace.SF x) : ⟪(rungV hRF i : EuclideanSpace ℝ (Fin d)), rungV hRF j⟫ = evenNormGram x i j := by
  change ⟪rungC hRF i, rungC hRF j⟫ = _
  rw [← Cvs.Route.RungTierWindowForm.inner_emb hv, emb_rungC, emb_rungC]
  rfl

/-- The coefficient map `a ↦ Σ_j a_j rung_j` into `inC v R₁`. -/
def coordMap (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) : (Cvs.Approximant.SpineSubspace.SF x → ℝ) →ₗ[ℝ] inC v (R1 x) :=
  Fintype.linearCombination ℝ (rungV hRF)

theorem coordMap_apply (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    coordMap hRF a = ∑ j, a j • rungV hRF j :=
  Fintype.linearCombination_apply ℝ (rungV hRF) a

theorem emb_coordMap (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    emb v (coordMap hRF a : EuclideanSpace ℝ (Fin d)) = ∑ j, a j • rung x j := by
  rw [coordMap_apply, Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, map_smul]
  change a j • emb v (rungC hRF j) = _
  rw [emb_rungC]

/-- **`⟪T_{R₁} e_a, e_a⟫ = aᵀ(evenGram x)a`**. -/
theorem inner_coordMap (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ⟪compr (opOn x v) (inC v (R1 x)) (coordMap hRF a), coordMap hRF a⟫ = a ⬝ᵥ (evenGram x *ᵥ a) := by
  have hM : Matrix.of (fun i j => ⟪compr (opOn x v) (inC v (R1 x)) (rungV hRF i), rungV hRF j⟫) = evenGram x := by
    ext i j; rw [Matrix.of_apply, inner_rungV]
  rw [coordMap_apply, Cvs.Upstream.CourantFischerInterlacing.inner_sum_smul_eq_dotProduct (isSymmetric_compr (isSymmetric_opOn v) _), hM]

/-- **`‖e_a‖² = aᵀ(evenNormGram x)a`**. -/
theorem norm_coordMap (hv : Orthonormal ℝ v) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v))
    (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ‖coordMap hRF a‖ ^ 2 = a ⬝ᵥ (evenNormGram x *ᵥ a) := by
  have hM : Matrix.of (fun i j => ⟪(LinearMap.id : inC v (R1 x) →ₗ[ℝ] inC v (R1 x)) (rungV hRF i), rungV hRF j⟫)
      = evenNormGram x := by
    ext i j; rw [Matrix.of_apply, LinearMap.id_apply, Submodule.coe_inner, inner_rungV_rungV hv]
  have h := Cvs.Upstream.CourantFischerInterlacing.inner_sum_smul_eq_dotProduct LinearMap.IsSymmetric.id (rungV hRF) a
  rw [hM, LinearMap.id_apply] at h
  rw [← real_inner_self_eq_norm_sq, coordMap_apply, h]

theorem coordMap_surjective (hv : Orthonormal ℝ v) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) :
    Function.Surjective (coordMap hRF) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (show emb v y ∈ R1 x from hy)
  exact ⟨a, Subtype.ext (Cvs.Route.RungTierWindowForm.emb_injective hv ((emb_coordMap hRF a).trans ha))⟩

theorem coordMap_injective (hx : 80 ≤ 2 * Real.pi * x) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) :
    Function.Injective (coordMap hRF) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have h : ∑ j, a j • rung x j = 0 := by rw [← emb_coordMap hRF a, ha]; simp
  exact funext (Fintype.linearIndependent_iffₛ.1 (linearIndependent_rung hx) a 0 (by rw [h]; simp))

/-- The coefficient isomorphism `(SF x → ℝ) ≃ inC v R₁` at `80 ≤ 2πx`. -/
def coordEquiv (hx : 80 ≤ 2 * Real.pi * x) (hv : Orthonormal ℝ v) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) :
    (Cvs.Approximant.SpineSubspace.SF x → ℝ) ≃ₗ[ℝ] inC v (R1 x) :=
  LinearEquiv.ofBijective (coordMap hRF) ⟨coordMap_injective hx hRF, coordMap_surjective hv hRF⟩

theorem finrank_inC_R1 (hx : 80 ≤ 2 * Real.pi * x) (hv : Orthonormal ℝ v)
    (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) : finrank ℝ (inC v (R1 x)) = Fintype.card (Cvs.Approximant.SpineSubspace.SF x) :=
  (Cvs.Route.RungTierWindowForm.finrank_inC hv hRF).trans (finrank_R1 hx)

/-! ### `Q|R₁` is the whitened even rung matrix -/

/-- **`λ↑_k(Q|R₁)` is the `k`-th ascending eigenvalue of `Sᵀ(evenGram x)S`**, `S = (evenNormGram x)^{−1/2}`, at
`80 ≤ 2πx` (Cvs.L2a.EvenNormGramPosDef). -/
theorem eigAsc_R1_eq_whitened (hx : 80 ≤ 2 * Real.pi * x) (hv : Orthonormal ℝ v)
    (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (k : Fin (finrank ℝ (inC v (R1 x)))) :
    eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v (R1 x))) k
      = Cvs.Upstream.CourantFischerAscending.eigAsc (Cvs.L2a.EvenNormGramPosDef.whitened_isHermitian x) (Fin.cast (finrank_inC_R1 hx hv hRF) k) :=
  Cvs.Upstream.CourantFischerInterlacing.eigAsc_eq_eigAsc_gram _ (Cvs.L2a.EvenNormGramPosDef.whiten_spec hx) _ (coordEquiv hx hv hRF)
    (fun a => inner_coordMap hRF a) (fun a => norm_coordMap hv hRF a) k

/-- **The tier below the whitened even rung matrix**: for any `K`, `k = dim(span v ∩ K)` and `i + k < #SF x`,
`λ↑_i(Q|span v ∩ Kᗮ) ≤ λ↑_{i+k}(Sᵀ(evenGram x)S)` at `80 ≤ 2πx`. -/
theorem eigAsc_tier_le_whitened (hx : 80 ≤ 2 * Real.pi * x) (hv : Orthonormal ℝ v)
    (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (K : Submodule ℝ (Dom x)) (i : Fin (finrank ℝ (inC v K)ᗮ))
    (h : (i : ℕ) + finrank ℝ (inC v K) < Fintype.card (Cvs.Approximant.SpineSubspace.SF x)) :
    eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) i
      ≤ Cvs.Upstream.CourantFischerAscending.eigAsc (Cvs.L2a.EvenNormGramPosDef.whitened_isHermitian x) ⟨i + finrank ℝ (inC v K), h⟩ := by
  have hik : (i : ℕ) + finrank ℝ (inC v K) < finrank ℝ (inC v (R1 x)) := by
    rw [finrank_inC_R1 hx hv hRF]; exact h
  have h1 := Cvs.Route.RungTierWindowForm.eigAsc_tier_le v K i hik
  rw [eigAsc_R1_eq_whitened hx hv hRF] at h1
  exact h1

/-! ### Sets of rungs: the Gram floor -/

/-- The Gram matrix `N_J` of the even rungs of `J`. -/
abbrev gramJ (x : ℕ) (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) : Matrix J J ℝ :=
  (evenNormGram x).submatrix Subtype.val Subtype.val

theorem quad_gramJ (x : ℕ) (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) (c : J → ℝ) :
    c ⬝ᵥ (gramJ x J *ᵥ c) = ‖∑ j, c j • rung x j‖ ^ 2 := by
  have hM : Matrix.of (fun i j : J => ⟪(LinearMap.id : Dom x →ₗ[ℝ] Dom x) (rung x i), rung x j⟫) = gramJ x J := by
    ext i j; rw [Matrix.of_apply, LinearMap.id_apply]; rfl
  have h := Cvs.Upstream.CourantFischerInterlacing.inner_sum_smul_eq_dotProduct LinearMap.IsSymmetric.id (fun j : J => rung x j) c
  rw [hM, LinearMap.id_apply] at h
  rw [← h]
  exact real_inner_self_eq_norm_sq _

theorem norm_sum_rungV (hv : Orthonormal ℝ v) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v))
    (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) (c : J → ℝ) :
    ‖∑ j, c j • rungV hRF j‖ = ‖∑ j, c j • rung x j‖ := by
  have h0 : ‖∑ j, c j • rungV hRF j‖
      = ‖((∑ j, c j • rungV hRF j : inC v (R1 x)) : EuclideanSpace ℝ (Fin d))‖ := rfl
  rw [h0, Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  rw [← Cvs.Route.RungTierWindowForm.norm_emb hv, map_sum]
  simp only [map_smul]
  change ‖∑ j, c j • emb v (rungC hRF j)‖ = _
  simp only [emb_rungC]

theorem gram_floor_coords (hv : Orthonormal ℝ v) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v))
    (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) {g : ℝ} (hg : ∀ c : J → ℝ, g * (c ⬝ᵥ c) ≤ c ⬝ᵥ (gramJ x J *ᵥ c)) (c : J → ℝ) :
    g * ∑ j, c j ^ 2 ≤ ‖∑ j, c j • rungV hRF j‖ ^ 2 := by
  rw [norm_sum_rungV hv, ← quad_gramJ]
  have := hg c
  simpa [dotProduct, sq] using this

/-- **The least Gram eigenvalue is a positive Gram floor**: at `80 ≤ 2πx`, for nonempty `J`, `g = λ_min(N_J) > 0`
and `g·cᵀc ≤ cᵀN_J c`. -/
theorem gramFloor_eigAsc (hx : 80 ≤ 2 * Real.pi * x) (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) (hJ : J.Nonempty) :
    0 < Cvs.Upstream.CourantFischerAscending.eigAsc ((Cvs.L2a.EvenNormGramPosDef.evenNormGram_isHermitian x).submatrix (Subtype.val : J → Cvs.Approximant.SpineSubspace.SF x))
        ⟨0, by rw [Fintype.card_coe]; exact hJ.card_pos⟩ ∧
      ∀ c : J → ℝ, Cvs.Upstream.CourantFischerAscending.eigAsc ((Cvs.L2a.EvenNormGramPosDef.evenNormGram_isHermitian x).submatrix (Subtype.val : J → Cvs.Approximant.SpineSubspace.SF x))
        ⟨0, by rw [Fintype.card_coe]; exact hJ.card_pos⟩ * (c ⬝ᵥ c) ≤ c ⬝ᵥ (gramJ x J *ᵥ c) := by
  set hH := (Cvs.L2a.EvenNormGramPosDef.evenNormGram_isHermitian x).submatrix (Subtype.val : J → Cvs.Approximant.SpineSubspace.SF x)
  have hli : LinearIndependent ℝ (fun j : J => rung x j) := (linearIndependent_rung hx).comp _ Subtype.val_injective
  have hposq : ∀ c : J → ℝ, c ≠ 0 → 0 < c ⬝ᵥ (gramJ x J *ᵥ c) := by
    intro c hc
    rw [quad_gramJ]
    have : ∑ j, c j • rung x j ≠ 0 := fun h0 => hc (funext fun j => Fintype.linearIndependent_iff.1 hli c h0 j)
    positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨S, hS, hfl⟩, -⟩ := Cvs.Upstream.CourantFischerAscending.isLeast_eigAsc hH ⟨0, by rw [Fintype.card_coe]; exact hJ.card_pos⟩
    have hne : S ≠ ⊥ := fun h => by rw [h, finrank_bot] at hS; simp at hS
    obtain ⟨c, hcS, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := hfl c hcS
    have h2 := hposq c hc0
    have h3 : 0 ≤ c ⬝ᵥ c := dotProduct_self_star_nonneg c
    by_contra hneg
    push Not at hneg
    nlinarith
  · obtain ⟨⟨V, hV, hfl⟩, -⟩ := Cvs.Upstream.CourantFischerAscending.isGreatest_eigAsc hH ⟨0, by rw [Fintype.card_coe]; exact hJ.card_pos⟩
    have htop : V = ⊤ := Submodule.eq_top_of_finrank_eq
      (le_antisymm (Submodule.finrank_le V) (by rw [Module.finrank_fintype_fun_eq_card]; simpa using hV))
    intro c
    exact hfl c (htop ▸ Submodule.mem_top)

/-! ### Sets of rungs: row sums and the trace -/

/-- **The even rung matrix bounds `Q|R₁` by weighted row sums**: for `w > 0`, `Σ_{j∈J}|T_ij|·w_j/w_i ≤ m` on `J`
and `g·cᵀc ≤ cᵀN_J c`, `g > 0`, give `g·λ↑_k(Q|R₁) ≤ m` for `k < #J`. -/
theorem mul_eigAsc_R1_le (hv : Orthonormal ℝ v) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v))
    (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) {w : Cvs.Approximant.SpineSubspace.SF x → ℝ} (hw : ∀ j, 0 < w j) {m g : ℝ}
    (hm : ∀ i ∈ J, ∑ j ∈ J, |evenGram x i j| * (w j / w i) ≤ m)
    (hg0 : 0 < g) (hg : ∀ c : J → ℝ, g * (c ⬝ᵥ c) ≤ c ⬝ᵥ (gramJ x J *ᵥ c))
    (k : Fin (finrank ℝ (inC v (R1 x)))) (hk : (k : ℕ) + 1 ≤ J.card) :
    g * eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v (R1 x))) k ≤ m := by
  have hg' := gram_floor_coords hv hRF J hg
  refine Cvs.Upstream.CourantFischerInterlacing.mul_eigAsc_le_of_gram (isSymmetric_compr (isSymmetric_opOn v) (inC v (R1 x)))
    (fun j : J => rungV hRF j) (w := fun j : J => w j) (fun j => hw j) (fun i => ?_) hg0 hg' k ?_
  · simp only [inner_rungV]
    rw [Finset.sum_coe_sort J (fun j => |evenGram x i j| * (w j / w i))]
    exact hm i i.2
  · rw [Cvs.Upstream.CourantFischerInterlacing.finrank_span_eq_card_of_gram _ hg0 hg', Fintype.card_coe]
    exact hk

/-- **The even rung matrix bounds `Q|R₁` by its trace on `J`** when `T ⪰ 0`: `EvenGramNonneg x` and
`g·cᵀc ≤ cᵀN_J c`, `g > 0`, give `g·λ↑_k(Q|R₁) ≤ Σ_{j∈J} T_jj` for `k < #J`. -/
theorem mul_eigAsc_R1_le_trace (hv : Orthonormal ℝ v) (hRF : R1 x ≤ Submodule.span ℝ (Set.range v))
    (hT : Cvs.Route.EvenGramRungFloors.EvenGramNonneg x) (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) {g : ℝ} (hg0 : 0 < g)
    (hg : ∀ c : J → ℝ, g * (c ⬝ᵥ c) ≤ c ⬝ᵥ (gramJ x J *ᵥ c))
    (k : Fin (finrank ℝ (inC v (R1 x)))) (hk : (k : ℕ) + 1 ≤ J.card) :
    g * eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v (R1 x))) k ≤ ∑ j ∈ J, evenGram x j j := by
  have hg' := gram_floor_coords hv hRF J hg
  have hpos : ∀ u : inC v (R1 x), 0 ≤ ⟪compr (opOn x v) (inC v (R1 x)) u, u⟫ := fun u => by
    obtain ⟨a, rfl⟩ := coordMap_surjective hv hRF u
    rw [inner_coordMap]; exact hT a
  have h := Cvs.Upstream.CourantFischerInterlacing.mul_eigAsc_le_trace (isSymmetric_compr (isSymmetric_opOn v) (inC v (R1 x))) hpos
    (fun j : J => rungV hRF j) hg0 hg' k (by
      rw [Cvs.Upstream.CourantFischerInterlacing.finrank_span_eq_card_of_gram _ hg0 hg', Fintype.card_coe]; exact hk)
  simp only [inner_rungV] at h
  rwa [Finset.sum_coe_sort J (fun j => evenGram x j j)] at h

/-- **The tier below weighted row sums**: for any `K`, `w > 0`, `Σ_{j∈J}|T_ij|·w_j/w_i ≤ m` and a Gram floor
`g > 0` on `J`, `g·λ↑_i(Q|span v ∩ Kᗮ) ≤ m` whenever `i + dim(span v ∩ K) < #J`. -/
theorem mul_eigAsc_tier_le (hv : Orthonormal ℝ v) (K : Submodule ℝ (Dom x))
    (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) {w : Cvs.Approximant.SpineSubspace.SF x → ℝ}
    (hw : ∀ j, 0 < w j) {m g : ℝ} (hm : ∀ i ∈ J, ∑ j ∈ J, |evenGram x i j| * (w j / w i) ≤ m) (hg0 : 0 < g)
    (hg : ∀ c : J → ℝ, g * (c ⬝ᵥ c) ≤ c ⬝ᵥ (gramJ x J *ᵥ c))
    (i : Fin (finrank ℝ (inC v K)ᗮ)) (hiJ : (i : ℕ) + finrank ℝ (inC v K) + 1 ≤ J.card) :
    g * eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) i ≤ m := by
  have hg' := gram_floor_coords hv hRF J hg
  have hJ : J.card ≤ finrank ℝ (inC v (R1 x)) := by
    have := Cvs.Upstream.CourantFischerInterlacing.finrank_span_eq_card_of_gram (fun j : J => rungV hRF j) hg0 hg'
    rw [Fintype.card_coe] at this
    rw [← this]
    exact Submodule.finrank_le _
  have hik : (i : ℕ) + finrank ℝ (inC v K) < finrank ℝ (inC v (R1 x)) := by omega
  have h1 := Cvs.Route.RungTierWindowForm.eigAsc_tier_le v K i hik
  have h2 := mul_eigAsc_R1_le hv hRF J hw hm hg0 hg ⟨_, hik⟩ (by simpa using hiJ)
  nlinarith

/-- **The tier below the trace**: for any `K`, `EvenGramNonneg x` and a Gram floor `g > 0` on `J` give
`g·λ↑_i(Q|span v ∩ Kᗮ) ≤ Σ_{j∈J} Q(rung_j)` whenever `i + dim(span v ∩ K) < #J`. -/
theorem mul_eigAsc_tier_le_trace (hv : Orthonormal ℝ v) (K : Submodule ℝ (Dom x))
    (hRF : R1 x ≤ Submodule.span ℝ (Set.range v)) (hT : Cvs.Route.EvenGramRungFloors.EvenGramNonneg x) (J : Finset (Cvs.Approximant.SpineSubspace.SF x))
    {g : ℝ} (hg0 : 0 < g) (hg : ∀ c : J → ℝ, g * (c ⬝ᵥ c) ≤ c ⬝ᵥ (gramJ x J *ᵥ c))
    (i : Fin (finrank ℝ (inC v K)ᗮ)) (hiJ : (i : ℕ) + finrank ℝ (inC v K) + 1 ≤ J.card) :
    g * eigAsc (isSymmetric_compr (isSymmetric_opOn v) (inC v K)ᗮ) i ≤ ∑ j ∈ J, Cvs.Route.WindowPositivityBulkCoupling.Qx x (rung x j) := by
  have hg' := gram_floor_coords hv hRF J hg
  have hJ : J.card ≤ finrank ℝ (inC v (R1 x)) := by
    have := Cvs.Upstream.CourantFischerInterlacing.finrank_span_eq_card_of_gram (fun j : J => rungV hRF j) hg0 hg'
    rw [Fintype.card_coe] at this
    rw [← this]
    exact Submodule.finrank_le _
  have hik : (i : ℕ) + finrank ℝ (inC v K) < finrank ℝ (inC v (R1 x)) := by omega
  have h1 := Cvs.Route.RungTierWindowForm.eigAsc_tier_le v K i hik
  have h2 := mul_eigAsc_R1_le_trace hv hRF hT J hg0 hg ⟨_, hik⟩ (by simpa using hiJ)
  have hd : ∀ j, evenGram x j j = Cvs.Route.WindowPositivityBulkCoupling.Qx x (rung x j) := fun j => by
    rw [Cvs.L2a.EvenSectorReflectionBound.evenGram_apply]; exact Cvs.WeilForm.SymmetricBilinearForm.QWbil_self _ _ _ _
  simp only [hd] at h2
  nlinarith

/-- **The weighted row-sum bound is satisfiable**: `m = Σ_{i,j∈J}|T_ij|·w_j/w_i` bounds every weighted row over `J`. -/
theorem rowSum_le_total (x : ℕ) (J : Finset (Cvs.Approximant.SpineSubspace.SF x)) {w : Cvs.Approximant.SpineSubspace.SF x → ℝ} (hw : ∀ j, 0 < w j) :
    ∀ i ∈ J, ∑ j ∈ J, |evenGram x i j| * (w j / w i)
      ≤ ∑ i' ∈ J, ∑ j ∈ J, |evenGram x i' j| * (w j / w i') := fun _ hi =>
  Finset.single_le_sum (f := fun i' => ∑ j ∈ J, |evenGram x i' j| * (w j / w i'))
    (fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (div_pos (hw _) (hw _)).le) hi

end Cvs.Route.WhitenedEvenRungTier
