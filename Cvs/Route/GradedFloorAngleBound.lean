import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesVectorFirstRung
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Route.AngleBoundFromFloor
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.Route.EvenBulkFloorSandwich
import Cvs.Route.GroundConnesAngle
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.RungFlagConnesHyperplane
import Cvs.Route.TameCouplingBulkFloor
import Cvs.Upstream.EigenvectorAngleGradedFloor
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The graded floor on Connes' even hyperplane gives the angle bound

`GradedFloorPerp`: on `v̂ᗮ` the even window form minus `q = ⟪T v̂, v̂⟫` dominates `κ` times the graded weight
`∑_{j≥2} gⱼ⟪eⱼ,·⟫² + b‖P_{R₁(N)ᗮ}·‖²`. It gives `1 − (ground⬝connesVec)² ≤ R/(κ² gmin + R)`, `R` the dual weight
of `T v̂`, with no positivity of the form; at fixed `κ₀, b` and endpoint weights, frequently with `R ≤ (2/(√x log x))κ₀² gmin`,
it gives RH. Some `κ > 0` exists at one scale iff the floor on `v̂ᗮ` exceeds `q`; both sides are unchanged by `T ↦ T + c`.
-/

noncomputable section

open Real Filter Matrix
open scoped InnerProductSpace

namespace Cvs.Route.GradedFloorAngleBound
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Route.GroundRouteJointGap (evenSub Meven)
open Cvs.Route.L1FloorFromBulkD0 (D0idx)
open Cvs.Approximant.ConnesVectorFirstRung (vhat norm_vhat)
open Cvs.Route.RungFlagConnesHyperplane (gradedWeight gradedDual gradedResid gmin)
open Cvs.Route.EigenvectorCoordinateCompression (perp schurVec)

/-! ### The graded floor of an operator on the even sector -/

section Op

variable {x N : ℕ}

/-- **The graded floor of `T`**: `κ w(y) ≤ ⟪T y, y⟫ − ⟪T v̂, v̂⟫‖y‖²` for every even `y ⊥ v̂`, `w` the graded weight. -/
def GradedFloor (x N : ℕ) (T : evenSub N →ₗ[ℝ] evenSub N) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b κ : ℝ) : Prop :=
  ∀ y : evenSub N, ⟪y, vhat x N⟫_ℝ = 0 →
    κ * gradedWeight x N g b y ≤ ⟪T y, y⟫_ℝ - ⟪T (vhat x N), vhat x N⟫_ℝ * ‖y‖ ^ 2

/-- The graded residual of `T`: the dual graded weight of `T v̂`. -/
def gradedResidOf (x N : ℕ) (T : evenSub N →ₗ[ℝ] evenSub N) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) : ℝ :=
  gradedDual x N g b (T (vhat x N))

/-- The dual graded weight is nonnegative for positive weights. -/
theorem gradedDual_nonneg {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b : ℝ} (hg : ∀ j : D0idx x, 0 < g j.1) (hb : 0 < b)
    (u : evenSub N) : 0 ≤ gradedDual x N g b u :=
  add_nonneg (Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hg j).le)
    (div_nonneg (sq_nonneg _) hb.le)

/-- **The graded floor is shift invariant**: `T` and `T + c` have the same graded floors. -/
theorem gradedFloor_add_smul_id (T : evenSub N →ₗ[ℝ] evenSub N) (c : ℝ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b κ : ℝ) :
    GradedFloor x N (T + c • LinearMap.id) g b κ ↔ GradedFloor x N T g b κ := by
  have hv := norm_vhat x N
  have e : ∀ y : evenSub N,
      ⟪(T + c • LinearMap.id : evenSub N →ₗ[ℝ] evenSub N) y, y⟫_ℝ
          - ⟪(T + c • LinearMap.id : evenSub N →ₗ[ℝ] evenSub N) (vhat x N), vhat x N⟫_ℝ * ‖y‖ ^ 2
        = ⟪T y, y⟫_ℝ - ⟪T (vhat x N), vhat x N⟫_ℝ * ‖y‖ ^ 2 := by
    intro y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_add_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
    ring
  unfold GradedFloor
  simp only [e]

/-- **The graded residual is shift invariant** when Connes' coefficient vector is nonzero. -/
theorem gradedResidOf_add_smul_id (hx : 80 ≤ 2 * π * x)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (T : evenSub N →ₗ[ℝ] evenSub N) (c : ℝ)
    (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) :
    gradedResidOf x N (T + c • LinearMap.id) g b = gradedResidOf x N T g b := by
  unfold gradedResidOf
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  exact Cvs.Route.RungFlagConnesHyperplane.gradedDual_add_smul_vhat hx N hs g b c _

/-- **The graded angle bound on the even sector**: a graded floor of `T` on `v̂ᗮ` and a unit eigenvector `θ` of
`T` at `l ≤ q = ⟪T v̂, v̂⟫` give `‖(C − q)⁻¹ r‖² ≤ R/(κ² gmin)` and `1 − ⟪v̂, θ⟫² ≤ R/(κ² gmin + R)`. -/
theorem one_sub_inner_sq_le_of_gradedFloor (hx : 80 ≤ 2 * π * x)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {T : evenSub N →ₗ[ℝ] evenSub N}
    {θ : evenSub N} {l κ b : ℝ} {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} (hθ1 : ‖θ‖ = 1) (hθ : T θ = l • θ)
    (hlq : l ≤ ⟪T (vhat x N), vhat x N⟫_ℝ) (hκ : 0 < κ) (hb : 0 < b) (hg : ∀ j : D0idx x, 0 < g j.1)
    (h : GradedFloor x N T g b κ) :
    ‖schurVec T (vhat x N) ⟪T (vhat x N), vhat x N⟫_ℝ‖ ^ 2
        ≤ gradedResidOf x N T g b / (κ ^ 2 * gmin x g b) ∧
      1 - ⟪vhat x N, θ⟫_ℝ ^ 2 ≤ gradedResidOf x N T g b / (κ ^ 2 * gmin x g b + gradedResidOf x N T g b) := by
  have hy : ∀ y : perp (vhat x N), ⟪(y : evenSub N), vhat x N⟫_ℝ = 0 := fun y =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 y.2
  refine Cvs.Upstream.EigenvectorAngleGradedFloor.one_sub_inner_sq_le_of_graded_rayleigh (fun y : perp (vhat x N) => gradedWeight x N g b y)
    (norm_vhat x N) hθ1 hθ hκ (Cvs.Route.RungFlagConnesHyperplane.gmin_pos hg hb) (gradedDual_nonneg hg hb _) hlq ?_ ?_ ?_
  · intro y
    have a := h y (hy y)
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact a
  · intro y
    exact Cvs.Route.RungFlagConnesHyperplane.sq_inner_le_gradedDual_mul hx N hs hg hb _ (hy y)
  · intro y
    exact Cvs.Route.RungFlagConnesHyperplane.gmin_mul_norm_sq_le hx N hs g b (hy y)

/-- **The graded floor as a pencil bound**: `GradedFloor x N T g b κ` iff `κ ≤ (⟪T y, y⟫ − q‖y‖²)/w(y)` for every
nonzero even `y ⊥ v̂`, `w` the graded weight. -/
theorem gradedFloor_iff_le_ratio (hx : 80 ≤ 2 * π * x)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (T : evenSub N →ₗ[ℝ] evenSub N)
    {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b κ : ℝ} (hg : ∀ j : D0idx x, 0 < g j.1) (hb : 0 < b) :
    GradedFloor x N T g b κ ↔ ∀ y : evenSub N, ⟪y, vhat x N⟫_ℝ = 0 → y ≠ 0 →
      κ ≤ (⟪T y, y⟫_ℝ - ⟪T (vhat x N), vhat x N⟫_ℝ * ‖y‖ ^ 2) / gradedWeight x N g b y := by
  have hw : ∀ y : evenSub N, ⟪y, vhat x N⟫_ℝ = 0 → y ≠ 0 → 0 < gradedWeight x N g b y := fun y hy hy0 =>
    (mul_pos (Cvs.Route.RungFlagConnesHyperplane.gmin_pos hg hb) (pow_pos (norm_pos_iff.2 hy0) 2)).trans_le
      (Cvs.Route.RungFlagConnesHyperplane.gmin_mul_norm_sq_le hx N hs g b hy)
  constructor
  · intro h y hy hy0
    rw [le_div_iff₀ (hw y hy hy0)]
    exact h y hy
  · intro h y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · simp [gradedWeight]
    · have := h y hy hy0
      rwa [le_div_iff₀ (hw y hy hy0)] at this

/-- **At one scale a positive graded constant exists iff the floor on `v̂ᗮ` is above `q`**: some `κ > 0` has
`GradedFloor x N T g b κ` iff some `μ > ⟪T v̂, v̂⟫` has `μ‖y‖² ≤ ⟪T y, y⟫` for every even `y ⊥ v̂`. -/
theorem exists_gradedFloor_iff (hx : 80 ≤ 2 * π * x)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (T : evenSub N →ₗ[ℝ] evenSub N)
    {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b : ℝ} (hg : ∀ j : D0idx x, 0 < g j.1) (hb : 0 < b) :
    (∃ κ, 0 < κ ∧ GradedFloor x N T g b κ) ↔
      ∃ μ, ⟪T (vhat x N), vhat x N⟫_ℝ < μ ∧ ∀ y : evenSub N, ⟪y, vhat x N⟫_ℝ = 0 → μ * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ := by
  set q := ⟪T (vhat x N), vhat x N⟫_ℝ
  constructor
  · rintro ⟨κ, hκ, h⟩
    refine ⟨q + κ * gmin x g b, by linarith [mul_pos hκ (Cvs.Route.RungFlagConnesHyperplane.gmin_pos hg hb)], fun y hy => ?_⟩
    have a := h y hy
    have c := mul_le_mul_of_nonneg_left (Cvs.Route.RungFlagConnesHyperplane.gmin_mul_norm_sq_le hx N hs g b hy) hκ.le
    nlinarith
  · rintro ⟨μ, hμ, h⟩
    set G := b + ∑ j : D0idx x, g j.1
    have hS : 0 ≤ ∑ j : D0idx x, g j.1 := Finset.sum_nonneg fun j _ => (hg j).le
    have hG : 0 < G := by positivity
    have hgG : ∀ j : D0idx x, g j.1 ≤ G := fun j =>
      (Finset.single_le_sum (fun i _ => (hg i).le) (Finset.mem_univ j)).trans (le_add_of_nonneg_left hb.le)
    have hwG : ∀ y : evenSub N, ⟪y, vhat x N⟫_ℝ = 0 → gradedWeight x N g b y ≤ G * ‖y‖ ^ 2 := by
      intro y hy
      rw [Cvs.Route.RungFlagConnesHyperplane.norm_sq_perp hx N hs hy, mul_add, Finset.mul_sum, gradedWeight]
      refine add_le_add (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hgG j) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hS) (sq_nonneg _))
    refine ⟨(μ - q) / G, div_pos (by linarith) hG, fun y hy => ?_⟩
    have a := h y hy
    have c := mul_le_mul_of_nonneg_left (hwG y hy) (div_pos (sub_pos.2 hμ) hG).le
    rw [← mul_assoc, div_mul_cancel₀ _ hG.ne'] at c
    linarith

end Op

/-! ### The window form at truncation `N` -/

section Window

variable {x : ℕ}

/-- **Connes' Rayleigh value** `q = ⟪T v̂, v̂⟫` at truncation `N`. -/
def qN (hx1 : (1 : ℝ) < x) (N : ℕ) : ℝ := ⟪Cvs.Route.EvenBulkFloorSandwich.formN hx1 N (vhat x N), vhat x N⟫_ℝ

/-- `q = connesVec ⬝ M connesVec`. -/
theorem qN_eq (hx1 : (1 : ℝ) < x) (N : ℕ) :
    qN hx1 N = Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
      ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) :=
  Cvs.Route.EigenvectorCoordinateCompression.inner_Meven_evenVec _ _ _ _

/-- **The RH-content node**: the graded floor of the even window form on Connes' even hyperplane, i.e.
`κ(∑_{j≥2} gⱼ⟪eⱼ,y⟫² + b‖P_{R₁(N)ᗮ}y‖²) ≤ ⟪T y, y⟫ − q‖y‖²` for every even `y ⊥ v̂`. -/
def GradedFloorPerp (hx1 : (1 : ℝ) < x) (N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b κ : ℝ) : Prop :=
  GradedFloor x N (Cvs.Route.EvenBulkFloorSandwich.formN hx1 N) g b κ

/-- `GradedFloorPerp` unfolded. -/
theorem gradedFloorPerp_iff (hx1 : (1 : ℝ) < x) (N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b κ : ℝ) :
    GradedFloorPerp hx1 N g b κ ↔ ∀ y : evenSub N, ⟪y, vhat x N⟫_ℝ = 0 →
      κ * gradedWeight x N g b y ≤ ⟪Cvs.Route.EvenBulkFloorSandwich.formN hx1 N y, y⟫_ℝ - qN hx1 N * ‖y‖ ^ 2 :=
  Iff.rfl

/-- `Cvs.Route.RungFlagConnesHyperplane.gradedResid` is the graded residual of the window form. -/
theorem gradedResid_eq_gradedResidOf (hx1 : (1 : ℝ) < x) (N : ℕ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) :
    gradedResid hx1 N g b = gradedResidOf x N (Cvs.Route.EvenBulkFloorSandwich.formN hx1 N) g b := rfl

/-- **The node is shift invariant**: `GradedFloorPerp` holds for the window form iff it holds for the form plus `c`. -/
theorem gradedFloorPerp_shift (hx1 : (1 : ℝ) < x) (N : ℕ) (c : ℝ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b κ : ℝ) :
    GradedFloor x N (Cvs.Route.EvenBulkFloorSandwich.formN hx1 N + c • LinearMap.id) g b κ ↔ GradedFloorPerp hx1 N g b κ :=
  gradedFloor_add_smul_id _ c g b κ

/-- **The graded residual is shift invariant**: the form plus `c` has the graded residual of the form. -/
theorem gradedResid_shift (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) (c : ℝ) (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b : ℝ) :
    gradedResidOf x N (Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N + c • LinearMap.id) g b
      = gradedResid (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b :=
  gradedResidOf_add_smul_id hx hs _ c g b

/-- The ground state is below Connes' Rayleigh value. -/
theorem groundLam_le_qN (hx1 : (1 : ℝ) < x) (N : ℕ) :
    Cvs.Limit.SpineWithoutSimplicity.groundLam x (Nat.clog 2 x) (Real.log x) (Real.log_pos hx1) N ≤ qN hx1 N := by
  have h := (Cvs.Limit.SpineWithoutSimplicity.ground_spec x (Nat.clog 2 x) (Real.log_pos hx1) N).2.2.1
    (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) (Cvs.Approximant.ConnesVectorRealScale.connesVec_even (fun _ => N) x)
  rw [Cvs.Approximant.ConnesVectorRealScale.connesVec_dotProduct_self, mul_one] at h
  rw [qN_eq]
  exact h

/-- **The graded floor gives the angle bound with no positivity**: `GradedFloorPerp` at `κ, b, gⱼ > 0` gives
`SinSqClose` at `R/(κ² gmin + R)` against Connes' vector, `R = gradedResid`, and `‖(C − q)⁻¹ r‖² ≤ R/(κ² gmin)`. -/
theorem sinSqClose_of_gradedFloorPerp (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b κ : ℝ}
    (hκ : 0 < κ) (hb : 0 < b) (hg : ∀ j : D0idx x, 0 < g j.1)
    (h : GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b κ) :
    ‖schurVec (Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N) (vhat x N) (qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N)‖ ^ 2
        ≤ gradedResid (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b / (κ ^ 2 * gmin x g b) ∧
      Cvs.Route.GroundConnesAngle.SinSqClose x (Nat.clog 2 x) (Real.log x) N
        (gradedResid (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b
          / (κ ^ 2 * gmin x g b + gradedResid (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b))
        (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hL := Real.log_pos hx1
  obtain ⟨hge, hg1, -, -, -⟩ := Cvs.Limit.SpineWithoutSimplicity.ground_spec x (Nat.clog 2 x) hL N
  have hθ := Cvs.Route.EigenvectorCoordinateCompression.Meven_ground x (Nat.clog 2 x) hL N
  have H := one_sub_inner_sq_le_of_gradedFloor hx hs (T := Cvs.Route.EvenBulkFloorSandwich.formN hx1 N)
    (Cvs.Route.EigenvectorCoordinateCompression.norm_evenVec hge hg1) hθ (groundLam_le_qN hx1 N) hκ hb hg h
  refine ⟨H.1, hL, ?_⟩
  have e : ⟪vhat x N, Cvs.Route.EigenvectorCoordinateCompression.evenVec hge⟫_ℝ
      = Cvs.Limit.SpineWithoutSimplicity.ground x (Nat.clog 2 x) (Real.log x) hL N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x := by
    rw [Cvs.Route.EigenvectorCoordinateCompression.inner_evenVec, dotProduct_comm]
  rw [← e]
  exact H.2

private theorem div_add_le_of_le_mul {R a ε : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (h : R ≤ ε * a) :
    R / (a + R) ≤ ε := by
  rw [div_le_iff₀ (by linarith)]
  have hε : 0 ≤ ε := by
    by_contra hc
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hc) ha
    linarith
  nlinarith

end Window

/-! ### RH from the graded floor at infinitely many scales -/

/-- **RH from a uniform graded floor**: a truncation eventually at least `⌈x^{1/4}⌉` and, for infinitely many `n`,
`GradedFloorPerp` at fixed `κ₀, b > 0` with the endpoint weights and `R ≤ (2/(√n log n)) κ₀² gmin` give RH. -/
theorem riemannHypothesis_of_frequently_gradedFloorPerp (N : ℝ → ℕ)
    (hN : ∀ᶠ x : ℝ in atTop, Cvs.Route.JointGapAtConnesVectors.connesThreshold x ≤ N x) {κ₀ b : ℝ} (hκ : 0 < κ₀) (hb : 0 < b)
    (h : ∃ᶠ n : ℕ in atTop, ∃ hn : (1 : ℝ) < n,
      GradedFloorPerp hn (N n) (Cvs.Route.RungFlagConnesHyperplane.endpointWeight n) b κ₀ ∧
      gradedResid hn (N n) (Cvs.Route.RungFlagConnesHyperplane.endpointWeight n) b
        ≤ 2 / (√(n : ℝ) * Real.log n) * (κ₀ ^ 2 * gmin n (Cvs.Route.RungFlagConnesHyperplane.endpointWeight n) b)) :
    RiemannHypothesis := by
  refine Cvs.Route.GroundConnesAngle.riemannHypothesis_of_frequently_sinSq_connes_two_div (fun x => ⌊x⌋₊)
    (fun x => Nat.clog 2 ⌊x⌋₊) ⟨N, hN, ?_⟩
  refine tendsto_natCast_atTop_atTop.frequently ?_
  refine (h.and_eventually (Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_nat_connesCoef_mass_ne_zero.and Cvs.Route.TameCouplingBulkFloor.eventually_scale)).mono ?_
  rintro n ⟨⟨hn, hG, hR⟩, hs, hx⟩
  have hg : ∀ j : D0idx n, 0 < Cvs.Route.RungFlagConnesHyperplane.endpointWeight n j.1 := fun j => Cvs.Route.RungFlagConnesHyperplane.endpointWeight_pos n j.1
  simp only [Nat.floor_natCast]
  refine Cvs.Route.AngleBoundFromFloor.sinSqClose_mono (sinSqClose_of_gradedFloorPerp hx (N n) (hs (N n)) hκ hb hg hG).2 ?_
  exact div_add_le_of_le_mul (gradedDual_nonneg hg hb _) (mul_pos (pow_pos hκ 2) (Cvs.Route.RungFlagConnesHyperplane.gmin_pos hg hb)) hR

end Cvs.Route.GradedFloorAngleBound
