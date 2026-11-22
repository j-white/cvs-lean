import Mathlib
import Cvs.Approximant.ConnesVectorFirstRung
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Approximant.XiKrylovHermiteSpan
import Cvs.Finite.SymmetricModeSet
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ScalingLaplacianCauchyLaw
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.Route.EvenBulkFloorSandwich
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.L1FloorFromBulkD0

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung flag and the bulk on Connes' even hyperplane

`e = gramSchmidtNormed (rungVec x N)` in the order of `SF x` has `e₁ = v̂`, Connes' vector; its layers `j ≤ m`
span the rungs `j ≤ m`, the layers `j ≥ 2` span `R₁(N) ⊓ v̂ᗮ`, and the whole flag spans `R₁(N)`.
Every even `y` is `∑ⱼ ⟪eⱼ, y⟫ eⱼ + P_{R₁(N)ᗮ} y`; on `v̂ᗮ` the `j = 1` term vanishes, and for positive `gⱼ, b`
the graded weight `∑_{j≥2} gⱼ⟪eⱼ,y⟫² + b‖P y‖²` dominates `gmin ‖y‖²` and, with its dual, bounds `⟪u, y⟫²`.
-/

noncomputable section

open Real Submodule Matrix Filter InnerProductSpace
open scoped InnerProductSpace

namespace Cvs.Route.RungFlagConnesHyperplane
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Route.GroundRouteJointGap (evenSub)
open Cvs.Route.L1FloorFromBulkD0 (D0idx)
open Cvs.Approximant.ConnesVectorFirstRung (vhat)

/-! ### The index split `SF x = {1} ∪ D₀` -/

/-- In `SF x`, `j ≠ 1` iff `2 ≤ j`. -/
theorem ne_one_iff {x : ℕ} (j1 : Cvs.Approximant.SpineSubspace.SF x) (hj1 : (j1 : ℕ) = 1) (j : Cvs.Approximant.SpineSubspace.SF x) :
    j ≠ j1 ↔ 2 ≤ (j : ℕ) := by
  have h1 : 1 ≤ (j : ℕ) := (Finset.mem_filter.1 j.2).2
  rw [Ne, Subtype.ext_iff, hj1]
  omega

/-- A sum over `SF x` is its `j = 1` term plus the sum over `D₀` (`j ≥ 2`). -/
theorem sum_SF_eq {M : Type*} [AddCommMonoid M] {x : ℕ} (j1 : Cvs.Approximant.SpineSubspace.SF x) (hj1 : (j1 : ℕ) = 1)
    (f : Cvs.Approximant.SpineSubspace.SF x → M) : ∑ j, f j = f j1 + ∑ j : D0idx x, f j.1 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f j1]
  congr 1
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight (ne_one_iff j1 hj1)) _ _ fun _ => rfl

/-- `1` is the least element of `SF x`. -/
theorem isMin_one {x : ℕ} (j1 : Cvs.Approximant.SpineSubspace.SF x) (hj1 : (j1 : ℕ) = 1) : IsMin j1 := by
  intro j _
  show (j1 : ℕ) ≤ j
  rw [hj1]
  exact (Finset.mem_filter.1 j.2).2

/-! ### The rung flag -/

/-- The rung flag: Gram–Schmidt of the even rung vectors in the order of `SF x`, normalised. -/
def rungFlag (x N : ℕ) : Cvs.Approximant.SpineSubspace.SF x → evenSub N := gramSchmidtNormed ℝ (Cvs.Route.EvenBulkFloorSandwich.rungVec x N)

/-- The first flag vector is the normalised rung-1 vector. -/
theorem rungFlag_one_eq {x N : ℕ} (j1 : Cvs.Approximant.SpineSubspace.SF x) (hj1 : (j1 : ℕ) = 1) :
    rungFlag x N j1 = ‖Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1‖⁻¹ • Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1 := by
  have hg : gramSchmidt ℝ (Cvs.Route.EvenBulkFloorSandwich.rungVec x N) j1 = Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1 := by
    rw [gramSchmidt_def, Finset.Iio_eq_empty.2 (isMin_one j1 hj1), Finset.sum_empty, sub_zero]
  unfold rungFlag gramSchmidtNormed
  rw [hg]
  rfl

/-- **The first flag vector is Connes' vector** whenever its coefficient vector is nonzero. -/
theorem rungFlag_one_eq_vhat {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j1 : Cvs.Approximant.SpineSubspace.SF x)
    (hj1 : (j1 : ℕ) = 1) (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    rungFlag x N j1 = vhat x N := by
  rw [rungFlag_one_eq j1 hj1, Cvs.Approximant.ConnesVectorFirstRung.evenVec_connesVec_eq hx N j1 hj1 hs]

/-- The first flag vector lies on the line of Connes' vector. -/
theorem rungFlag_one_mem {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) (j1 : Cvs.Approximant.SpineSubspace.SF x)
    (hj1 : (j1 : ℕ) = 1) : rungFlag x N j1 ∈ ℝ ∙ vhat x N := by
  by_cases hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N = 0
  · have h0 : Cvs.Route.EvenBulkFloorSandwich.rungVec x N j1 = 0 := by
      rw [← norm_eq_zero, Cvs.Approximant.ConnesVectorFirstRung.norm_rungVec_one hx N j1 hj1, hs, Real.sqrt_zero, mul_zero]
    rw [rungFlag_one_eq j1 hj1, h0, smul_zero]
    exact zero_mem _
  · rw [rungFlag_one_eq_vhat hx N j1 hj1 hs]
    exact mem_span_singleton_self _

/-- Distinct flag vectors are orthogonal. -/
theorem inner_rungFlag_eq_zero (x N : ℕ) {i j : Cvs.Approximant.SpineSubspace.SF x} (hij : i ≠ j) :
    ⟪rungFlag x N i, rungFlag x N j⟫_ℝ = 0 := by
  unfold rungFlag gramSchmidtNormed
  rw [real_inner_smul_left (F := evenSub N), real_inner_smul_right (F := evenSub N), gramSchmidt_orthogonal ℝ _ hij, mul_zero, mul_zero]

/-- **Every flag vector `j ≥ 2` is orthogonal to Connes' vector.** -/
theorem inner_rungFlag_vhat {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (j : D0idx x) :
    ⟪rungFlag x N j.1, vhat x N⟫_ℝ = 0 := by
  have h1 : 1 ∈ Cvs.Approximant.SpineSubspace.SF x := Finset.mem_filter.2
    ⟨Finset.mem_range.2 (by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx), le_rfl⟩
  rw [← rungFlag_one_eq_vhat hx N ⟨1, h1⟩ rfl hs]
  exact inner_rungFlag_eq_zero x N ((ne_one_iff ⟨1, h1⟩ rfl j.1).2 j.2)

/-- The nonzero flag vectors are orthonormal. -/
theorem rungFlag_orthonormal (x N : ℕ) :
    Orthonormal ℝ fun i : {i | rungFlag x N i ≠ 0} => rungFlag x N i :=
  gramSchmidtNormed_orthonormal' _

/-- Each flag vector is zero or a unit vector. -/
theorem rungFlag_eq_zero_or_norm (x N : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) :
    rungFlag x N j = 0 ∨ ‖rungFlag x N j‖ = 1 := by
  by_cases h : rungFlag x N j = 0
  · exact Or.inl h
  · exact Or.inr (gramSchmidtNormed_unit_length' h)

/-- **The flag spans the rung span** `R₁(N)`. -/
theorem span_rungFlag (x N : ℕ) : span ℝ (Set.range (rungFlag x N)) = Cvs.Route.EvenBulkFloorSandwich.R1N x N := by
  unfold rungFlag Cvs.Route.EvenBulkFloorSandwich.R1N
  rw [span_gramSchmidtNormed_range, span_gramSchmidt]

/-- **The flag is nested**: the layers `j ≤ m` span the rungs `j ≤ m`, for every `m`. -/
theorem span_rungFlag_le (x N m : ℕ) :
    span ℝ (rungFlag x N '' {j | (j : ℕ) ≤ m}) = span ℝ (Cvs.Route.EvenBulkFloorSandwich.rungVec x N '' {j | (j : ℕ) ≤ m}) := by
  unfold rungFlag
  rw [span_gramSchmidtNormed]
  apply le_antisymm
  · refine span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    refine span_mono (Set.image_mono fun i hi => ?_) (gramSchmidt_mem_span ℝ _ le_rfl)
    exact (show (i : ℕ) ≤ j from Set.mem_Iic.1 hi).trans hj
  · refine span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    refine span_mono (Set.image_mono fun i hi => ?_) (mem_span_gramSchmidt ℝ _ le_rfl)
    exact (show (i : ℕ) ≤ j from Set.mem_Iic.1 hi).trans hj

/-- Each flag vector lies in `R₁(N)`. -/
theorem rungFlag_mem_R1N (x N : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : rungFlag x N j ∈ Cvs.Route.EvenBulkFloorSandwich.R1N x N := by
  rw [← span_rungFlag]; exact subset_span (Set.mem_range_self j)

/-! ### The projections onto `R₁(N)` and its complement -/

/-- `⟪eₖ, ∑ⱼ ⟪eⱼ,y⟫eⱼ⟫ = ⟪eₖ, y⟫`. -/
theorem inner_rungFlag_sum (x N : ℕ) (k : Cvs.Approximant.SpineSubspace.SF x) (y : evenSub N) :
    ⟪rungFlag x N k, ∑ j, ⟪rungFlag x N j, y⟫_ℝ • rungFlag x N j⟫_ℝ = ⟪rungFlag x N k, y⟫_ℝ := by
  rw [inner_sum, Finset.sum_eq_single k]
  · rw [real_inner_smul_right (F := evenSub N)]
    rcases rungFlag_eq_zero_or_norm x N k with h | h
    · rw [h, inner_zero_left, inner_zero_left, mul_zero]
    · rw [real_inner_self_eq_norm_sq, h, one_pow, mul_one]
  · intro j _ hj
    rw [real_inner_smul_right (F := evenSub N), inner_rungFlag_eq_zero x N (Ne.symm hj), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

-- `OrthonormalBasis.orthogonalProjection_eq_sum` needs a basis; the flag can have zero vectors
-- (dependent rungs), so the expansion is proved against the full flag directly.
/-- **The projection onto `R₁(N)` is the flag expansion.** -/
theorem starProjection_R1N (x N : ℕ) (y : evenSub N) :
    (Cvs.Route.EvenBulkFloorSandwich.R1N x N).starProjection y = ∑ j, ⟪rungFlag x N j, y⟫_ℝ • rungFlag x N j := by
  refine eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (rungFlag_mem_R1N x N j)) fun w hw => ?_
  rw [← span_rungFlag] at hw
  refine Submodule.span_induction (p := fun w _ => ⟪y - ∑ j, ⟪rungFlag x N j, y⟫_ℝ • rungFlag x N j, w⟫_ℝ = 0)
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨k, rfl⟩
    rw [real_inner_comm, inner_sub_right, inner_rungFlag_sum, sub_self]
  · exact inner_zero_right _
  · intro u v _ _ hu hv; rw [inner_add_right, hu, hv, add_zero]
  · intro c u _ hu; rw [real_inner_smul_right (F := evenSub N), hu, mul_zero]

/-- **The flag/bulk expansion**: `y = ∑ⱼ ⟪eⱼ, y⟫ eⱼ + P_{R₁(N)ᗮ} y`. -/
theorem expand (x N : ℕ) (y : evenSub N) :
    y = ∑ j, ⟪rungFlag x N j, y⟫_ℝ • rungFlag x N j + (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection y := by
  rw [starProjection_orthogonal_val, starProjection_R1N, add_sub_cancel]

/-- `R₁(N)ᗮ ≤ v̂ᗮ` when Connes' coefficient vector is nonzero. -/
theorem R1N_orthogonal_le_perp {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ ≤ (ℝ ∙ vhat x N)ᗮ :=
  orthogonal_le ((span_singleton_le_iff_mem _ _).2 (Cvs.Approximant.ConnesVectorFirstRung.evenVec_connesVec_mem_R1N hx N hs))

/-- **Connes' hyperplane splits** as `(R₁(N) ⊓ v̂ᗮ) ⊔ R₁(N)ᗮ`, the two parts orthogonal. -/
theorem perp_eq_sup {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    (ℝ ∙ vhat x N)ᗮ = (Cvs.Route.EvenBulkFloorSandwich.R1N x N ⊓ (ℝ ∙ vhat x N)ᗮ) ⊔ (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ ∧
      (Cvs.Route.EvenBulkFloorSandwich.R1N x N ⊓ (ℝ ∙ vhat x N)ᗮ) ⟂ (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ := by
  refine ⟨?_, (isOrtho_orthogonal_right _).mono_left inf_le_left⟩
  have h := sup_orthogonal_inf_of_hasOrthogonalProjection (R1N_orthogonal_le_perp hx N hs)
  rw [orthogonal_orthogonal] at h
  rw [sup_comm]
  exact h.symm

/-- **The expansion on Connes' hyperplane**: for `y ⊥ v̂`, `y = ∑_{j≥2} ⟪eⱼ, y⟫ eⱼ + P_{R₁(N)ᗮ} y`. -/
theorem expand_perp {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {y : evenSub N}
    (hy : ⟪y, vhat x N⟫_ℝ = 0) :
    y = ∑ j : D0idx x, ⟪rungFlag x N j.1, y⟫_ℝ • rungFlag x N j.1
      + (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection y := by
  have h1 : 1 ∈ Cvs.Approximant.SpineSubspace.SF x := Finset.mem_filter.2
    ⟨Finset.mem_range.2 (by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx), le_rfl⟩
  conv_lhs => rw [expand x N y]
  rw [sum_SF_eq ⟨1, h1⟩ rfl, rungFlag_one_eq_vhat hx N ⟨1, h1⟩ rfl hs, real_inner_comm, hy, zero_smul,
    zero_add]

/-- **Parseval on Connes' hyperplane**: `‖y‖² = ∑_{j≥2} ⟪eⱼ, y⟫² + ‖P_{R₁(N)ᗮ} y‖²` for `y ⊥ v̂`. -/
theorem norm_sq_perp {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {y : evenSub N}
    (hy : ⟪y, vhat x N⟫_ℝ = 0) :
    ‖y‖ ^ 2 = ∑ j : D0idx x, ⟪rungFlag x N j.1, y⟫_ℝ ^ 2 + ‖(Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection y‖ ^ 2 := by
  set K := Cvs.Route.EvenBulkFloorSandwich.R1N x N
  have hP : ‖K.starProjection y‖ ^ 2 = ∑ j : D0idx x, ⟪rungFlag x N j.1, y⟫_ℝ ^ 2 := by
    have h1 : 1 ∈ Cvs.Approximant.SpineSubspace.SF x := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx), le_rfl⟩
    rw [← real_inner_self_eq_norm_sq, starProjection_R1N, sum_inner]
    simp only [real_inner_smul_left (F := evenSub N), inner_rungFlag_sum]
    rw [sum_SF_eq ⟨1, h1⟩ rfl, rungFlag_one_eq_vhat hx N ⟨1, h1⟩ rfl hs, real_inner_comm, hy,
      zero_mul, zero_add]
    exact Finset.sum_congr rfl fun j _ => (sq _).symm
  have hsum := K.starProjection_add_starProjection_orthogonal y
  have horth : ⟪K.starProjection y, Kᗮ.starProjection y⟫_ℝ = 0 :=
    K.inner_right_of_mem_orthogonal (K.starProjection_apply_mem y) (Kᗮ.starProjection_apply_mem y)
  rw [← hP]
  conv_lhs => rw [← hsum]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_add_left, inner_add_right, inner_add_right, horth,
    real_inner_comm (K.starProjection y) (Kᗮ.starProjection y), horth]
  ring

/-! ### Weights -/

/-- The graded weight: `∑_{j≥2} gⱼ ⟪eⱼ, y⟫² + b ‖P_{R₁(N)ᗮ} y‖²`. -/
def gradedWeight (x N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) (y : evenSub N) : ℝ :=
  ∑ j : D0idx x, g j.1 * ⟪rungFlag x N j.1, y⟫_ℝ ^ 2 + b * ‖(Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection y‖ ^ 2

/-- The dual graded weight: `∑_{j≥2} ⟪eⱼ, u⟫²/gⱼ + ‖P_{R₁(N)ᗮ} u‖²/b`. -/
def gradedDual (x N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) (u : evenSub N) : ℝ :=
  ∑ j : D0idx x, ⟪rungFlag x N j.1, u⟫_ℝ ^ 2 / g j.1 + ‖(Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection u‖ ^ 2 / b

/-- The graded residual of Connes' vector: the dual weight of `T v̂`, `T` the even form at truncation `N`. -/
def gradedResid {x : ℕ} (hx1 : (1 : ℝ) < x) (N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) : ℝ :=
  gradedDual x N g b (Cvs.Route.EvenBulkFloorSandwich.formN hx1 N (vhat x N))

/-- The least weight: `min(b, min_{j≥2} gⱼ)`. -/
def gmin (x : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) : ℝ :=
  (Finset.univ : Finset (D0idx x)).fold min b fun j => g j.1

/-- `gmin ≤ b`. -/
theorem gmin_le_b (x : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) : gmin x g b ≤ b := by
  unfold gmin; exact ((Finset.le_fold_min _).1 le_rfl).1

/-- `gmin ≤ gⱼ` for every `j ≥ 2`. -/
theorem gmin_le (x : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) (j : D0idx x) : gmin x g b ≤ g j.1 := by
  unfold gmin; exact ((Finset.le_fold_min _).1 le_rfl).2 j (Finset.mem_univ _)

/-- `gmin > 0` when every weight is positive. -/
theorem gmin_pos {x : ℕ} {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b : ℝ} (hg : ∀ j : D0idx x, 0 < g j.1) (hb : 0 < b) :
    0 < gmin x g b := by
  unfold gmin; exact (Finset.lt_fold_min _).2 ⟨hb, fun j _ => hg j⟩

/-- **The graded weight dominates `gmin ‖y‖²` on Connes' hyperplane.** -/
theorem gmin_mul_norm_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ)
    {y : evenSub N} (hy : ⟪y, vhat x N⟫_ℝ = 0) :
    gmin x g b * ‖y‖ ^ 2 ≤ gradedWeight x N g b y := by
  rw [norm_sq_perp hx N hs hy, mul_add, Finset.mul_sum, gradedWeight]
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_) ?_
  · exact mul_le_mul_of_nonneg_right (gmin_le x g b j) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (gmin_le_b x g b) (sq_nonneg _)

/-- **Weighted Cauchy–Schwarz on Connes' hyperplane**: `⟪u, y⟫² ≤ gradedDual(u) · gradedWeight(y)`. -/
theorem sq_inner_le_gradedDual_mul {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b : ℝ}
    (hg : ∀ j : D0idx x, 0 < g j.1) (hb : 0 < b) (u : evenSub N) {y : evenSub N}
    (hy : ⟪y, vhat x N⟫_ℝ = 0) :
    ⟪u, y⟫_ℝ ^ 2 ≤ gradedDual x N g b u * gradedWeight x N g b y := by
  set K := Cvs.Route.EvenBulkFloorSandwich.R1N x N
  set c : D0idx x → ℝ := fun j => ⟪rungFlag x N j.1, y⟫_ℝ
  set a : D0idx x → ℝ := fun j => ⟪rungFlag x N j.1, u⟫_ℝ
  have hexp : ⟪u, y⟫_ℝ = ∑ j, a j * c j + ⟪Kᗮ.starProjection u, Kᗮ.starProjection y⟫_ℝ := by
    conv_lhs => rw [expand_perp hx N hs hy]
    rw [inner_add_right, inner_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_right (F := evenSub N), real_inner_comm (rungFlag x N j.1) u]
      exact mul_comm _ _
    · rw [inner_starProjection_left_eq_right,
        starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ y)]
  -- Cauchy–Schwarz over `Option (D0idx x)`, the extra index carrying the bulk.
  let F : Option (D0idx x) → ℝ := fun o => o.elim (‖Kᗮ.starProjection u‖ / √b) fun j => |a j| / √(g j.1)
  let G : Option (D0idx x) → ℝ := fun o => o.elim (√b * ‖Kᗮ.starProjection y‖) fun j => √(g j.1) * |c j|
  have hFG : ∀ o, F o * G o = o.elim (‖Kᗮ.starProjection u‖ * ‖Kᗮ.starProjection y‖) fun j => |a j| * |c j| := by
    rintro (_ | j)
    · simp only [F, G, Option.elim]
      have : √b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
      field_simp
    · simp only [F, G, Option.elim]
      have : √(g j.1) ≠ 0 := (Real.sqrt_pos.2 (hg j)).ne'
      field_simp
  have hF2 : ∀ o, F o ^ 2 = o.elim (‖Kᗮ.starProjection u‖ ^ 2 / b) fun j => a j ^ 2 / g j.1 := by
    rintro (_ | j)
    · simp only [F, Option.elim]; rw [div_pow, Real.sq_sqrt hb.le]
    · simp only [F, Option.elim]; rw [div_pow, sq_abs, Real.sq_sqrt (hg j).le]
  have hG2 : ∀ o, G o ^ 2 = o.elim (b * ‖Kᗮ.starProjection y‖ ^ 2) fun j => g j.1 * c j ^ 2 := by
    rintro (_ | j)
    · simp only [G, Option.elim]; rw [mul_pow, Real.sq_sqrt hb.le]
    · simp only [G, Option.elim]; rw [mul_pow, sq_abs, Real.sq_sqrt (hg j).le]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F G
  simp only [Fintype.sum_option, hFG, hF2, hG2, Option.elim] at hCS
  have hdual : gradedDual x N g b u = ∑ j, a j ^ 2 / g j.1 + ‖Kᗮ.starProjection u‖ ^ 2 / b := rfl
  have hwt : gradedWeight x N g b y = ∑ j, g j.1 * c j ^ 2 + b * ‖Kᗮ.starProjection y‖ ^ 2 := rfl
  rw [hdual, hwt]
  have habs : |⟪u, y⟫_ℝ| ≤ ‖Kᗮ.starProjection u‖ * ‖Kᗮ.starProjection y‖ + ∑ j, |a j| * |c j| := by
    rw [hexp, add_comm]
    refine (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    exact Finset.sum_congr rfl fun j _ => abs_mul _ _
  have hnn : 0 ≤ ‖Kᗮ.starProjection u‖ * ‖Kᗮ.starProjection y‖ + ∑ j, |a j| * |c j| :=
    add_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by positivity)
  calc ⟪u, y⟫_ℝ ^ 2 = |⟪u, y⟫_ℝ| ^ 2 := (sq_abs _).symm
    _ ≤ (‖Kᗮ.starProjection u‖ * ‖Kᗮ.starProjection y‖ + ∑ j, |a j| * |c j|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ (‖Kᗮ.starProjection u‖ ^ 2 / b + ∑ j, a j ^ 2 / g j.1)
        * (b * ‖Kᗮ.starProjection y‖ ^ 2 + ∑ j, g j.1 * c j ^ 2) := hCS
    _ = _ := by ring

/-! ### The hypotheses of a graded angle bound on `v̂ᗮ` -/

/-- **The two graded hypotheses on `Cvs.Route.EigenvectorCoordinateCompression.perp v̂`**: `gmin ‖y‖² ≤ w(y)` and `⟪T v̂, y⟫² ≤ gradedResid · w(y)`. -/
theorem graded_hyps {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b : ℝ}
    (hg : ∀ j : D0idx x, 0 < g j.1) (hb : 0 < b) (y : Cvs.Route.EigenvectorCoordinateCompression.perp (vhat x N)) :
    gmin x g b * ‖(y : evenSub N)‖ ^ 2 ≤ gradedWeight x N g b y ∧
      ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (vhat x N), (y : evenSub N)⟫_ℝ ^ 2
        ≤ gradedResid (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b * gradedWeight x N g b y := by
  have hy : ⟪(y : evenSub N), vhat x N⟫_ℝ = 0 := mem_orthogonal_singleton_iff_inner_left.1 y.2
  exact ⟨gmin_mul_norm_sq_le hx N hs g b hy, sq_inner_le_gradedDual_mul hx N hs hg hb _ hy⟩

/-- **The layers `j ≥ 2` span `R₁(N) ⊓ v̂ᗮ`** when Connes' coefficient vector is nonzero. -/
theorem span_rungFlag_D0 {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    span ℝ (Set.range fun j : D0idx x => rungFlag x N j.1) = Cvs.Route.EvenBulkFloorSandwich.R1N x N ⊓ (ℝ ∙ vhat x N)ᗮ := by
  have h1 : 1 ∈ Cvs.Approximant.SpineSubspace.SF x := Finset.mem_filter.2
    ⟨Finset.mem_range.2 (by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx), le_rfl⟩
  apply le_antisymm
  · refine span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨rungFlag_mem_R1N x N j.1, ?_⟩
    exact mem_orthogonal_singleton_iff_inner_left.2 (inner_rungFlag_vhat hx N hs j)
  · rintro y ⟨hyR, hyp⟩
    have hy : ⟪y, vhat x N⟫_ℝ = 0 := mem_orthogonal_singleton_iff_inner_left.1 hyp
    have he : y = ∑ j : D0idx x, ⟪rungFlag x N j.1, y⟫_ℝ • rungFlag x N j.1 := by
      have h := expand_perp hx N hs hy
      rwa [starProjection_orthogonal_apply_eq_zero hyR, add_zero] at h
    rw [he]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- **The dual weight ignores `v̂`**: `gradedDual (u + t • v̂) = gradedDual u`. -/
theorem gradedDual_add_smul_vhat {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b t : ℝ)
    (u : evenSub N) : gradedDual x N g b (u + t • vhat x N) = gradedDual x N g b u := by
  have hP : (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection (vhat x N) = 0 :=
    starProjection_orthogonal_apply_eq_zero (Cvs.Approximant.ConnesVectorFirstRung.evenVec_connesVec_mem_R1N hx N hs)
  unfold gradedDual
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_add_right, real_inner_smul_right (F := evenSub N), inner_rungFlag_vhat hx N hs j, mul_zero,
      add_zero]
  · rw [map_add, map_smul, hP, smul_zero, add_zero]

/-- **The graded residual is the dual weight of the residual** `T v̂ − ⟪T v̂, v̂⟫ v̂`. -/
theorem gradedResid_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) :
    gradedResid (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b
      = gradedDual x N g b (Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (vhat x N)
          - ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (vhat x N), vhat x N⟫_ℝ • vhat x N) := by
  rw [sub_eq_add_neg, ← neg_smul, gradedDual_add_smul_vhat hx N hs]
  rfl

/-- **Each layer of a bounded dual weight**: `gradedDual u ≤ R` gives `⟪eⱼ,u⟫² ≤ R gⱼ` and
`‖P_{R₁(N)ᗮ} u‖² ≤ R b`. -/
theorem layer_le_of_gradedDual_le {x N : ℕ} {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b R : ℝ}
    (hg : ∀ j : D0idx x, 0 < g j.1) (hb : 0 < b) {u : evenSub N} (hR : gradedDual x N g b u ≤ R) :
    (∀ j : D0idx x, ⟪rungFlag x N j.1, u⟫_ℝ ^ 2 ≤ R * g j.1) ∧
      ‖(Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection u‖ ^ 2 ≤ R * b := by
  have hnn : ∀ j ∈ (Finset.univ : Finset (D0idx x)), 0 ≤ ⟪rungFlag x N j.1, u⟫_ℝ ^ 2 / g j.1 :=
    fun j _ => div_nonneg (sq_nonneg _) (hg j).le
  have hS := Finset.sum_nonneg hnn
  have hB : 0 ≤ ‖(Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection u‖ ^ 2 / b := div_nonneg (sq_nonneg _) hb.le
  unfold gradedDual at hR
  refine ⟨fun j => ?_, ?_⟩
  · have h := (Finset.single_le_sum hnn (Finset.mem_univ j)).trans (by linarith : _ ≤ R)
    rwa [div_le_iff₀ (hg j)] at h
  · rw [← div_le_iff₀ hb]; linarith

/-! ### Disc, corners and bulk -/

/-- The layers `2 ≤ j ≤ j* + 1`, `j* = Cvs.Approximant.XiKrylovHermiteSpan.jstar x`: rung `j` has top index `4j`, at most the top
index `4j* + 4` of `Cvs.Approximant.XiKrylovHermiteSpan.evenH0 (j* + 1)`. -/
def discIdx (x : ℕ) : Finset (D0idx x) := Finset.univ.filter fun j => (j.1 : ℕ) ≤ Cvs.Approximant.XiKrylovHermiteSpan.jstar x + 1

/-- The layers `j* + 1 < j < x`. -/
def cornerIdx (x : ℕ) : Finset (D0idx x) := Finset.univ.filter fun j => ¬ (j.1 : ℕ) ≤ Cvs.Approximant.XiKrylovHermiteSpan.jstar x + 1

/-- **The graded weight is disc + corners + bulk.** -/
theorem gradedWeight_eq_regions (x N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) (y : evenSub N) :
    gradedWeight x N g b y
      = ∑ j ∈ discIdx x, g j.1 * ⟪rungFlag x N j.1, y⟫_ℝ ^ 2
        + ∑ j ∈ cornerIdx x, g j.1 * ⟪rungFlag x N j.1, y⟫_ℝ ^ 2
        + b * ‖(Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection y‖ ^ 2 := by
  rw [gradedWeight, discIdx, cornerIdx, Finset.sum_filter_add_sum_filter_not]

/-- **The graded residual is disc + corners + bulk.** -/
theorem gradedDual_eq_regions (x N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) (u : evenSub N) :
    gradedDual x N g b u
      = ∑ j ∈ discIdx x, ⟪rungFlag x N j.1, u⟫_ℝ ^ 2 / g j.1
        + ∑ j ∈ cornerIdx x, ⟪rungFlag x N j.1, u⟫_ℝ ^ 2 / g j.1
        + ‖(Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ.starProjection u‖ ^ 2 / b := by
  rw [gradedDual, discIdx, cornerIdx, Finset.sum_filter_add_sum_filter_not]

/-! ### The two weight families -/

/-- The prolate endpoint weight of layer `j`: `h_{4j}(1)²/c`, `c = 2πx`. -/
def endpointWeight (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : ℝ :=
  Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) (2 * (j : ℕ)) 1 ^ 2 / (2 * π * x)

/-- The endpoint weights are positive. -/
theorem endpointWeight_pos (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : 0 < endpointWeight x j := by
  have hjx : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_le _).trans_lt hjx
  have hr := Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (Cvs.Prolate.ScalingLaplacianCauchyLaw.rungSpace_level hjx)
  exact div_pos (pow_pos (abs_pos.2 hr) 2 |>.trans_eq (sq_abs _)) (by positivity)

/-- The L2a weight of layer `j`: `π(1 − λ_{4j})/(8c(1 + 2c/(π λ₀)))`, `c = 2πx`. -/
def l2aWeight (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : ℝ :=
  π / (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * Cvs.Prolate.EvenRungsByIndex.lamR (2 * π * x) 0)))
    * (1 - Cvs.Prolate.EvenRungsByIndex.lamR (2 * π * x) (2 * (j : ℕ)))

/-- The L2a weights are positive. -/
theorem l2aWeight_pos (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : 0 < l2aWeight x j := by
  have hjx : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hj1 : 1 ≤ (j : ℕ) := (Finset.mem_filter.1 j.2).2
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_le _).trans_lt hjx
  have hc : 0 < 2 * π * (x : ℝ) := by positivity
  have h0 := Cvs.Prolate.EvenRungsByIndex.lamR_zero_pos hc
  have hlt := Cvs.Prolate.EvenRungsByIndex.lamR_lt_one hc (Cvs.Prolate.ScalingLaplacianCauchyLaw.rungSpace_level hjx) (by omega)
  unfold l2aWeight
  have : 0 < 1 - Cvs.Prolate.EvenRungsByIndex.lamR (2 * π * x) (2 * (j : ℕ)) := by linarith
  positivity

end Cvs.Route.RungFlagConnesHyperplane
