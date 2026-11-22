import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Route.GroundRouteJointGap
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
# The joint gap from a floor and near-positivity

The joint gap from a lower bound on the whole even form in place of `Cvs.Route.JointGapFromResidual`'s residual: if
`M ≥ −s` on even vectors and a hyperplane floor `μ` has `K q + (K − 1)s ≤ μ`, the joint gap holds
for the unit even trial of Rayleigh value `q`.
-/

noncomputable section

open Matrix

namespace Cvs.Route.JointGapFloorNearPositivity
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Limit.SpineWithoutSimplicity (ground groundLam ground_spec)

/-- **A lower bound on the even form bounds the ground level.** -/
theorem neg_le_groundLam {P R N : ℕ} {L s : ℝ} (hL : 0 < L)
    (hneg : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) →
      -s * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f)) :
    -s ≤ groundLam P R L hL N := by
  obtain ⟨hge, hg1, -, hgeig, -⟩ := ground_spec P R hL N
  have h := hneg _ hge
  rw [hgeig, dotProduct_smul, hg1, smul_eq_mul, mul_one, mul_one] at h
  exact h

/-- **The joint gap from a hyperplane floor and near-positivity of the even form**: with
`M ≥ −s` on even vectors, a floor `μ` on an even hyperplane with `q < μ` and `K q + (K − 1)s ≤ μ`
gives `Cvs.Route.GroundRouteJointGap.JointGap` at `K`, for the unit even trial `v` of Rayleigh value `q`. -/
theorem jointGap_of_floor_nearPos {P R N : ℕ} {L K μ s : ℝ} (hL : 0 < L)
    (kt v : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hneg : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) →
      -s * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hK : 1 ≤ K)
    (hqμ : v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) < μ)
    (hμ : K * (v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v)) + (K - 1) * s ≤ μ) :
    Cvs.Route.GroundRouteJointGap.JointGap P R L N K v := by
  obtain ⟨-, -, hgmin, -, -⟩ := ground_spec P R hL N
  have hlamq : groundLam P R L hL N ≤ v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) := by
    have h := hgmin v hve
    simpa only [hv1, mul_one] using h
  have hlam := neg_le_groundLam (P := P) (R := R) (N := N) hL hneg
  refine ⟨hL, μ, kt, hlamq.trans_lt hqμ, hfloor, ?_⟩
  nlinarith [mul_nonneg (sub_nonneg.mpr hK) (show 0 ≤ groundLam P R L hL N + s by linarith)]

end Cvs.Route.JointGapFloorNearPositivity
