import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesResidualFixedScale
import Cvs.Approximant.ConnesVectorFirstRung
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.ParitySectorDefect
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.QSideConnesRelative
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ScalingLaplacianCauchyLaw
import Cvs.Route.AngleBoundFromFloor
import Cvs.Route.CoreSchurForm
import Cvs.Route.EigenvectorCoordinateCompression
import Cvs.Route.EvenBulkFloorSandwich
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.GradedFloorAngleBound
import Cvs.Route.GroundConnesAngle
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.ProlateFloorNearPositivity
import Cvs.Route.RungFlagConnesHyperplane
import Cvs.Route.RungTierWindowForm
import Cvs.Route.TameCouplingBulkFloor
import Cvs.Route.Visibility.VisibilityUnconditional
import Cvs.StepA.StepACountDischarged
import Cvs.Upstream.EigenvectorAngleGradedFloor
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# What the graded floor on Connes' hyperplane contains and what gives it

`GradedFloorPerp` gives the floor `q + κ gmin` on `v̂ᗮ` (FloorPerp), the floor `q + κ b` on `R₁(N)ᗮ` and, at all large
`N`, `EvenBulkFloor x b′` and `TierAngleW x R₁ b′`; with `(K − 1)q ≤ κ gmin` it gives `ConnesFloor` at `K`, under RH at
`K = √x log x` once `κ gmin ≥ ε h₈(1)²/c`. A floor `μ ≥ 0` on Connes' hyperplane at all large `N` gives `EvenBulkFloor x 0`,
and RH for infinitely many `x`. A Schur coupling with rung and bulk floors gives the graded floor.
-/

noncomputable section

open Real Filter Matrix Topology
open scoped InnerProductSpace

namespace Cvs.Route.GradedFloorConsequences
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Route.GroundRouteJointGap (evenSub Meven)
open Cvs.Route.L1FloorFromBulkD0 (D0idx)
open Cvs.Approximant.ConnesVectorFirstRung (vhat norm_vhat)
open Cvs.Route.RungFlagConnesHyperplane (gradedWeight gradedDual gradedResid gmin rungFlag)
open Cvs.Route.GradedFloorAngleBound (GradedFloorPerp qN)

variable {x : ℕ}

private theorem inner_sub_smul_self {N : ℕ} (T : evenSub N →ₗ[ℝ] evenSub N) (q : ℝ) (u : evenSub N) :
    ⟪T u - q • u, u⟫_ℝ = ⟪T u, u⟫_ℝ - q * ‖u‖ ^ 2 := by
  rw [inner_sub_left, real_inner_smul_left (F := evenSub N), real_inner_self_eq_norm_sq]

/-! ### The floors contained in the graded floor -/

/-- **The hyperplane floor**: `GradedFloorPerp` with `κ ≥ 0` gives `(q + κ gmin)‖y‖² ≤ ⟪T y, y⟫` on `v̂ᗮ`. -/
theorem floor_of_gradedFloorPerp (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b κ : ℝ} (hκ : 0 ≤ κ)
    (h : GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b κ) {y : evenSub N} (hy : ⟪y, vhat x N⟫_ℝ = 0) :
    (qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N + κ * gmin x g b) * ‖y‖ ^ 2
      ≤ ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N y, y⟫_ℝ := by
  have a := h y hy
  have c := mul_le_mul_of_nonneg_left (Cvs.Route.RungFlagConnesHyperplane.gmin_mul_norm_sq_le hx N hs g b hy) hκ
  have hq : qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N
      = ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (vhat x N), vhat x N⟫_ℝ := rfl
  rw [hq]
  nlinarith

/-- **FloorPerp from the graded floor**: the even floor `μ = q + κ gmin > q` on `connesVecᗮ` in matrix form, and
`‖(C − q)⁻¹ r‖² ≤ R/(κ² gmin)`, the two hypotheses of `Cvs.Route.EigenvectorCoordinateCompression.sinSqClose_of_floorPerp` at `ε = R/(κ² gmin + R)`. -/
theorem floorPerp_of_gradedFloorPerp (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b κ : ℝ} (hκ : 0 < κ)
    (hb : 0 < b) (hg : ∀ j : D0idx x, 0 < g j.1) (h : GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b κ) :
    (∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ f = 0 →
      (qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N + κ * gmin x g b) * (f ⬝ᵥ f)
        ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ f)) ∧
    Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ
        Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) < qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N + κ * gmin x g b ∧
    ‖Cvs.Route.EigenvectorCoordinateCompression.schurVec (Meven x (Nat.clog 2 x) (Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx)) N)
        (Cvs.Route.EigenvectorCoordinateCompression.evenVec (Cvs.Approximant.ConnesVectorRealScale.connesVec_even (fun _ => N) x))
        (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ
          Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x))‖ ^ 2
      ≤ gradedResid (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b / (κ ^ 2 * gmin x g b) := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hgm := Cvs.Route.RungFlagConnesHyperplane.gmin_pos hg hb
  refine ⟨fun f hfe hf0 => ?_, ?_, ?_⟩
  · have hy : ⟪Cvs.Route.EigenvectorCoordinateCompression.evenVec hfe, vhat x N⟫_ℝ = 0 := by
      rw [Cvs.Route.EigenvectorCoordinateCompression.inner_evenVec, dotProduct_comm]; exact hf0
    have H := floor_of_gradedFloorPerp hx N hs hκ.le h hy
    rw [← real_inner_self_eq_norm_sq, Cvs.Route.EigenvectorCoordinateCompression.inner_evenVec] at H
    rw [← Cvs.Route.EigenvectorCoordinateCompression.inner_Meven_evenVec x (Nat.clog 2 x) (Real.log_pos hx1) hfe]
    exact H
  · rw [← Cvs.Route.GradedFloorAngleBound.qN_eq hx1 N]
    linarith [mul_pos hκ hgm]
  · rw [← Cvs.Route.GradedFloorAngleBound.qN_eq hx1 N]
    exact (Cvs.Route.GradedFloorAngleBound.sinSqClose_of_gradedFloorPerp hx N hs hκ hb hg h).1

/-- **The bulk floor**: `GradedFloorPerp` gives `(q + κ b)‖f‖² ≤ ⟪T f, f⟫` on `R₁(N)ᗮ`. -/
theorem bulkFloor_of_gradedFloorPerp (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b κ : ℝ}
    (h : GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b κ) {f : evenSub N} (hf : f ∈ (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ) :
    (qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N + κ * b) * ‖f‖ ^ 2 ≤ ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N f, f⟫_ℝ := by
  have hy : ⟪f, vhat x N⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Cvs.Route.RungFlagConnesHyperplane.R1N_orthogonal_le_perp hx N hs hf)
  have hw : gradedWeight x N g b f = b * ‖f‖ ^ 2 := by
    unfold gradedWeight
    rw [Submodule.starProjection_eq_self_iff.mpr hf]
    have : ∀ j : D0idx x, ⟪rungFlag x N j.1, f⟫_ℝ = 0 := fun j =>
      Submodule.inner_right_of_mem_orthogonal (Cvs.Route.RungFlagConnesHyperplane.rungFlag_mem_R1N x N j.1) hf
    simp only [this, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Finset.sum_const_zero, zero_add]
  have a := h f hy
  rw [hw] at a
  have hq : qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N
      = ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (vhat x N), vhat x N⟫_ℝ := rfl
  rw [hq]
  nlinarith

/-- **The even bulk floor from the graded floor at all large truncations**: `GradedFloorPerp` at `(b_N, κ_N)` with
`b′ ≤ q_N + κ_N b_N` for all large `N` gives `EvenBulkFloor x b′` and `TierAngleW x R₁ b′`. -/
theorem evenBulkFloor_of_eventually_gradedFloorPerp (hx : 80 ≤ 2 * π * x) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ}
    {b κ : ℕ → ℝ} {b' : ℝ}
    (h : ∀ᶠ N in atTop, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0 ∧
      GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g (b N) (κ N) ∧
      b' ≤ qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N + κ N * b N) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b' ∧ Cvs.Route.RungTierWindowForm.TierAngleW x (Cvs.L2a.EvenSectorReflectionBound.R1 x) b' := by
  have hF : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b' := by
    refine (Cvs.Route.EvenBulkFloorSandwich.evenBulkFloor_iff_eventually (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) b').mpr (h.mono ?_)
    rintro N ⟨hs, hG, hb'⟩ f hf
    exact (mul_le_mul_of_nonneg_right hb' (sq_nonneg _)).trans (bulkFloor_of_gradedFloorPerp hx N hs hG hf)
  exact ⟨hF, (Cvs.Route.RungTierWindowForm.tierAngleW_R1_iff x b').mpr hF⟩

/-- **RH from the graded floor at all large truncations**: if for infinitely many `x`, at all large `N`, `GradedFloorPerp`
holds with `0 ≤ q_N + κ_N b_N`, then RH. -/
theorem riemannHypothesis_of_frequently_eventually_gradedFloorPerp (g : ∀ x : ℕ, Cvs.Approximant.SpineSubspace.SF x → ℝ)
    (b κ : ℕ → ℕ → ℝ)
    (h : ∃ᶠ x : ℕ in atTop, ∃ hx : 80 ≤ 2 * π * x, ∀ᶠ N in atTop,
      GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (g x) (b x N) (κ x N) ∧
      0 ≤ qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N + κ x N * b x N) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨x, ⟨hx, hev⟩, hs, hnF⟩ :=
    (h.and_eventually (Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_nat_connesCoef_mass_ne_zero.and (Cvs.Route.Visibility.VisibilityUnconditional.hV hRH))).exists
  exact hnF (evenBulkFloor_of_eventually_gradedFloorPerp hx (hev.mono fun N hN => ⟨hs N, hN⟩)).1

/-! ### Hyperplane floors with normal in the rung span -/

/-- **A hyperplane floor with normal in `R₁(N)` is a bulk floor**: if at all large `N` some `k ∈ R₁(N)` has
`b′‖y‖² ≤ ⟪T y, y⟫` on `kᗮ`, then `EvenBulkFloor x b′`. -/
theorem evenBulkFloor_of_hyperplaneFloor (hx1 : (1 : ℝ) < x) {b' : ℝ}
    (h : ∀ᶠ N in atTop, ∃ k ∈ Cvs.Route.EvenBulkFloorSandwich.R1N x N, ∀ y : evenSub N, ⟪y, k⟫_ℝ = 0 →
      b' * ‖y‖ ^ 2 ≤ ⟪Cvs.Route.EvenBulkFloorSandwich.formN hx1 N y, y⟫_ℝ) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b' := by
  refine (Cvs.Route.EvenBulkFloorSandwich.evenBulkFloor_iff_eventually hx1 b').mpr (h.mono ?_)
  rintro N ⟨k, hk, hfl⟩ f hf
  exact hfl f (Submodule.inner_left_of_mem_orthogonal hk hf)

/-- **A nonnegative floor on Connes' even hyperplane at all large `N` is `EvenBulkFloor x 0`**: in the matrix form of
`Cvs.Route.AngleBoundFromFloor.ConnesFloor` with normal `connesVec` and `μ ≥ 0`. -/
theorem evenBulkFloor_zero_of_connesHyperplaneFloor (hx : 80 ≤ 2 * π * x)
    (h : ∀ᶠ N in atTop, Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0 ∧ ∃ μ : ℝ, 0 ≤ μ ∧
      ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ f = 0 →
        μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX (Real.log x) N *ᵥ f)) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x 0 := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hx0 : 0 < x := by exact_mod_cast zero_lt_one.trans hx1
  refine evenBulkFloor_of_hyperplaneFloor hx1 (h.mono ?_)
  rintro N ⟨hs, μ, hμ, hfl⟩
  refine ⟨vhat x N, Cvs.Approximant.ConnesVectorFirstRung.evenVec_connesVec_mem_R1N hx N hs, fun y hy => ?_⟩
  have hy' : Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ WithLp.ofLp (y : EuclideanSpace ℝ (Idx N)) = 0 := by
    rw [real_inner_comm, Cvs.Route.GroundRouteJointGap.inner_evenSub] at hy; exact hy
  have H := hfl _ y.2 hy'
  rw [Cvs.Route.EigenvectorCoordinateCompression.MX_log_natCast hx0 N] at H
  have hff : 0 ≤ WithLp.ofLp (y : EuclideanSpace ℝ (Idx N)) ⬝ᵥ WithLp.ofLp (y : EuclideanSpace ℝ (Idx N)) := by
    rw [← Cvs.Route.GroundRouteJointGap.norm_sq_evenSub]; positivity
  rw [zero_mul, Cvs.Route.GroundRouteJointGap.inner_evenSub, Cvs.Route.GroundRouteJointGap.ofLp_Meven, dotProduct_comm]
  exact (mul_nonneg hμ hff).trans H

/-- **A nonnegative floor on Connes' even hyperplane at all large `N`, for infinitely many `x`, gives RH.** -/
theorem riemannHypothesis_of_frequently_connesHyperplaneFloor
    (h : ∃ᶠ x : ℕ in atTop, ∀ᶠ N in atTop, ∃ μ : ℝ, 0 ≤ μ ∧
      ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ f = 0 →
        μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.ParitySectorDefect.MX (Real.log x) N *ᵥ f)) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨x, hx, ⟨hs, hsc⟩, hnF⟩ := (h.and_eventually ((Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_nat_connesCoef_mass_ne_zero.and
    Cvs.Route.TameCouplingBulkFloor.eventually_scale).and (Cvs.Route.Visibility.VisibilityUnconditional.hV hRH))).exists
  exact hnF (evenBulkFloor_zero_of_connesHyperplaneFloor hsc (hx.mono fun N hN => ⟨hs N, hN⟩))

/-! ### A Schur coupling gives the graded floor -/

/-- **The Schur route to the graded floor**: on `D = R₁(N) ⊓ v̂ᗮ`, `B = R₁(N)ᗮ` with `A(u) = ⟪T u, u⟫ − q‖u‖²`, a
coupling `η A(y) ≤ A(y + w)` (`0 ≤ η < 1`), a bulk floor `s‖w‖² ≤ A(w)` and a rung floor `∑_{j≥2} gⱼ⟪eⱼ,y⟫² ≤ A(y)` on
`D` give `GradedFloorPerp` at `κ = η/2`, `b = s/2`. -/
theorem gradedFloorPerp_of_schur (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {η s : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hB : ∀ w ∈ (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ, s * ‖w‖ ^ 2
      ≤ ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N w, w⟫_ℝ - qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N * ‖w‖ ^ 2)
    (hcoup : ∀ y ∈ Cvs.Route.EvenBulkFloorSandwich.R1N x N ⊓ (ℝ ∙ vhat x N)ᗮ, ∀ w ∈ (Cvs.Route.EvenBulkFloorSandwich.R1N x N)ᗮ,
      η * (⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N y, y⟫_ℝ - qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N * ‖y‖ ^ 2)
        ≤ ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N (y + w), y + w⟫_ℝ
          - qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N * ‖y + w‖ ^ 2)
    (hW : ∀ y ∈ Cvs.Route.EvenBulkFloorSandwich.R1N x N ⊓ (ℝ ∙ vhat x N)ᗮ, ∑ j : D0idx x, g j.1 * ⟪rungFlag x N j.1, y⟫_ℝ ^ 2
      ≤ ⟪Cvs.Route.EvenBulkFloorSandwich.formN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N y, y⟫_ℝ - qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N * ‖y‖ ^ 2) :
    GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g (s / 2) (η / 2) := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  set T := Cvs.Route.EvenBulkFloorSandwich.formN hx1 N
  set q := qN hx1 N
  set K := Cvs.Route.EvenBulkFloorSandwich.R1N x N
  intro y hy
  change η / 2 * gradedWeight x N g (s / 2) y ≤ ⟪T y, y⟫_ℝ - q * ‖y‖ ^ 2
  set yD := K.starProjection y
  set yB := Kᗮ.starProjection y
  have hsplit : yD + yB = y := K.starProjection_add_starProjection_orthogonal y
  have hyB : yB ∈ Kᗮ := Kᗮ.starProjection_apply_mem y
  have hvK : vhat x N ∈ K := Cvs.Approximant.ConnesVectorFirstRung.evenVec_connesVec_mem_R1N hx N hs
  have hyD : yD ∈ K ⊓ (ℝ ∙ vhat x N)ᗮ := by
    refine ⟨K.starProjection_apply_mem y, Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_⟩
    rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hvK]
    exact hy
  have H := Cvs.Upstream.EigenvectorAngleGradedFloor.schur_graded_floor (Cvs.Route.EvenBulkFloorSandwich.isSymmetric_formN hx1 N) (l := q)
    (K ⊓ (ℝ ∙ vhat x N)ᗮ) Kᗮ (fun u => ∑ j : D0idx x, g j.1 * ⟪rungFlag x N j.1, u⟫_ℝ ^ 2) hη0 hη1
    (fun w hw => by rw [inner_sub_smul_self]; exact hB w hw)
    (fun y hy w hw => by rw [inner_sub_smul_self, inner_sub_smul_self]; exact hcoup y hy w hw)
    (fun y hy => by rw [inner_sub_smul_self]; exact hW y hy) hyD hyB
  rw [hsplit, inner_sub_smul_self] at H
  have he : ∀ j : D0idx x, ⟪rungFlag x N j.1, y⟫_ℝ = ⟪rungFlag x N j.1, yD⟫_ℝ := by
    intro j
    rw [← hsplit, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal (Cvs.Route.RungFlagConnesHyperplane.rungFlag_mem_R1N x N j.1) hyB, add_zero]
  have hw : gradedWeight x N g (s / 2) y
      = ∑ j : D0idx x, g j.1 * ⟪rungFlag x N j.1, yD⟫_ℝ ^ 2 + s / 2 * ‖yB‖ ^ 2 := by
    unfold gradedWeight
    simp only [he]
    rfl
  rw [hw]
  linarith

/-! ### Connes' floor -/

/-- **ConnesFloor from the graded floor**: `GradedFloorPerp` with `(K − 1)q ≤ κ gmin` gives `Cvs.Route.AngleBoundFromFloor.ConnesFloor` at `K`
with normal `connesVec` and `μ = q + κ gmin`. -/
theorem connesFloor_of_gradedFloorPerp (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) {g : Cvs.Approximant.SpineSubspace.SF x → ℝ} {b κ K : ℝ} (hκ : 0 < κ)
    (hb : 0 < b) (hg : ∀ j : D0idx x, 0 < g j.1) (h : GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b κ)
    (hK : (K - 1) * qN (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N ≤ κ * gmin x g b) :
    Cvs.Route.AngleBoundFromFloor.ConnesFloor (Real.log x) N K (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hx0 : 0 < x := by exact_mod_cast zero_lt_one.trans hx1
  obtain ⟨hfl, hlt, -⟩ := floorPerp_of_gradedFloorPerp hx N hs hκ hb hg h
  refine ⟨qN hx1 N + κ * gmin x g b, Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x, ?_, ?_, ?_⟩
  · rw [Cvs.Route.EigenvectorCoordinateCompression.MX_log_natCast hx0 N]; exact hfl
  · rw [Cvs.Route.EigenvectorCoordinateCompression.MX_log_natCast hx0 N, ← Cvs.Route.GradedFloorAngleBound.qN_eq hx1 N]; linarith
  · rw [Cvs.Route.EigenvectorCoordinateCompression.MX_log_natCast hx0 N]; exact hlt

/-- **Under RH the graded floor gives ConnesFloor at `K = √x log x`**: for `ε > 0`, at all large `x` and all large
`N`, `GradedFloorPerp` with `ε h₈(1)²/(2πx) ≤ κ gmin` gives `Cvs.Route.AngleBoundFromFloor.ConnesFloor (log x) N (√x log x) connesVec`. -/
theorem eventually_connesFloor_of_RH (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ hx : 80 ≤ 2 * π * x, ∀ᶠ N in atTop, ∀ (g : Cvs.Approximant.SpineSubspace.SF x → ℝ) (b κ : ℝ),
      0 < κ → 0 < b → (∀ j : D0idx x, 0 < g j.1) → GradedFloorPerp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N g b κ →
      ε * Cvs.Prolate.EvenRungsByIndex.rung (2 * π * x) 4 1 ^ 2 / (2 * π * x) ≤ κ * gmin x g b →
      Cvs.Route.AngleBoundFromFloor.ConnesFloor (Real.log x) N (√(x : ℝ) * Real.log x) (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) := by
  have hc0W : ∀ᶠ x : ℕ in atTop, Cvs.L2a.WindowChainInputsProlate.c0W ≤ 2 * π * x :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 2 * π)).eventually_ge_atTop _
  filter_upwards [hc0W, Cvs.Route.ProlateFloorNearPositivity.eventually_qside_le hε, Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_nat_connesCoef_mass_ne_zero,
    Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_coefficientMass_pos, eventually_ge_atTop 3] with x hc hq hs hm hx3 hx
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hx0 : 0 < x := by omega
  have hL := Real.log_pos hx1
  set e := Cvs.Route.JointGapConnesFromL1.connesEven hx with hed
  have he2 : 0 < ‖e‖ ^ 2 := by rw [hed, Cvs.Route.JointGapConnesFromL1.norm_connesEven_sq hx]; positivity
  have he : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg _) fun h0 => by rw [← h0] at he2; simp at he2
  have hQ0 := Cvs.Route.CoreSchurForm.nonneg_of_rh hRH x (by omega)
  have hQe : Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) e ≤ Cvs.L2a.QSideConnesRelative.connesLrel x := by
    have h1 := Cvs.Route.JointGapConnesFromL1.Q_evenPart_le (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (s := 0)
      (fun φ => by rw [neg_zero, zero_mul]; exact hQ0 φ) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)
    rw [zero_mul, add_zero] at h1
    exact h1.trans (Cvs.L2a.QSideConnesRelative.Q_connesClass_le_rel x hc)
  set K := √(x : ℝ) * Real.log x with hK
  have hK0 : 0 < K := mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hx0)) hL
  set c := 2 * π * (x : ℝ) with hcdef
  have hc0 : 0 < c := by positivity
  have hr : 0 < ε * Cvs.Prolate.EvenRungsByIndex.rung c 4 1 ^ 2 / c := by
    have hne : Cvs.Prolate.EvenRungsByIndex.rung c (2 * 2) 1 ≠ 0 := Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (Cvs.Prolate.ScalingLaplacianCauchyLaw.rungSpace_level (by omega))
    have : 0 < Cvs.Prolate.EvenRungsByIndex.rung c 4 1 ^ 2 := pow_pos (abs_pos.2 hne) 2 |>.trans_eq (sq_abs _)
    positivity
  have hq' : K * (Cvs.L2a.QSideConnesRelative.connesLrel x / ‖e‖ ^ 2) ≤ ε / 2 * Cvs.Prolate.EvenRungsByIndex.rung c 4 1 ^ 2 / c := hq hc
  have hlim : K * (Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) e / ‖e‖ ^ 2)
      < ε * Cvs.Prolate.EvenRungsByIndex.rung c 4 1 ^ 2 / c := by
    have h1 : K * (Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) e / ‖e‖ ^ 2)
        ≤ K * (Cvs.L2a.QSideConnesRelative.connesLrel x / ‖e‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hQe he2.le) hK0.le
    have h2 : ε / 2 * Cvs.Prolate.EvenRungsByIndex.rung c 4 1 ^ 2 / c = ε * Cvs.Prolate.EvenRungsByIndex.rung c 4 1 ^ 2 / c / 2 := by ring
    linarith
  filter_upwards [((Cvs.Route.JointGapConnesFromL1.tendsto_rayleigh hx he).const_mul K).eventually (gt_mem_nhds hlim)]
    with N hN g b κ hκ hb hg hG hgm
  refine connesFloor_of_gradedFloorPerp hx N (hs N) hκ hb hg hG ?_
  rw [Cvs.Route.GradedFloorAngleBound.qN_eq hx1 N]
  have hq0 : 0 ≤ Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ
      (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) := by
    have hv0 : Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ≠ 0 := by
      intro h0
      have h1 := Cvs.Approximant.ConnesVectorRealScale.connesVec_dotProduct_self (fun _ => N) x
      rw [h0, zero_dotProduct] at h1
      exact zero_ne_one h1
    have hp := (Cvs.StepA.StepACountDischarged.posDef_of_RH hRH hL N).dotProduct_mulVec_pos hv0
    simp only [star_trivial] at hp
    rw [Cvs.Route.EigenvectorCoordinateCompression.MX_log_natCast hx0 N] at hp
    exact hp.le
  nlinarith

/-! ### The joint gap is an energy certificate -/

/-- **The joint gap with `q ≥ 0` is near-positivity**: `Cvs.Route.GroundRouteJointGap.JointGap` at `K > 1` against `v` with `v⬝Mv ≥ 0` has a
floor `μ` on an even hyperplane with `−μ/(K − 1) ≤ λ₁`. -/
theorem nearPos_of_jointGap {P R N : ℕ} {L K : ℝ} {v : Idx N → ℝ} (hK : 1 < K)
    (h : Cvs.Route.GroundRouteJointGap.JointGap P R L N K v) (hq : 0 ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v)) :
    ∃ (hL : 0 < L) (μ : ℝ) (kt : Idx N → ℝ),
      (∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
        μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f)) ∧
      -μ / (K - 1) ≤ Cvs.Limit.SpineWithoutSimplicity.groundLam P R L hL N := by
  obtain ⟨hL, μ, kt, -, hfl, hj⟩ := h
  exact ⟨hL, μ, kt, hfl, Cvs.Upstream.EigenvectorAngleGradedFloor.neg_div_le_of_jointGap hK hj hq⟩

end Cvs.Route.GradedFloorConsequences
