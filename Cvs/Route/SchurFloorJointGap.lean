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
# A codimension-one Schur floor gives the joint gap with a bottom loss

A Schur bound on a hyperplane gives a floor there; a Rayleigh ceiling `C`, bottom bound `−ε`, and
`K C + (K−1)ε ≤ μ` give the joint gap without requiring the full form to be nonnegative.
-/

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace Cvs.Route.SchurFloorJointGap
open Cvs.ZeroCounting

open Cvs.Route.GroundRouteJointGap (evenSub Meven JointGap)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.Limit.SpineWithoutSimplicity (groundLam ground_spec)

/-- A ceiling and a lower bound give the joint Rayleigh inequality with the loss `(K−1)ε`. -/
theorem joint_inequality_of_ceiling_lower {K q C l₁ ε μ : ℝ} (hK : 1 ≤ K)
    (hq : q ≤ C) (hl : -ε ≤ l₁) (hbudget : K * C + (K - 1) * ε ≤ μ) :
    K * (q - l₁) ≤ μ - l₁ := by
  have hq' := mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ K)
  have hl' := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ K - 1)
  nlinarith

section abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end abstract

/-- An even hyperplane floor, Rayleigh ceiling and bottom loss give `JointGap`. -/
theorem jointGap_of_floor_lower_bound {P R N : ℕ} {L K C ε μ : ℝ} (hL : 0 < L)
    (hK : 1 ≤ K) (v kt : Idx N → ℝ) (hve : ∀ i, v (negI N i) = v i)
    (hv1 : v ⬝ᵥ v = 1)
    (hfloor : ∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f))
    (hceil : v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) ≤ C)
    (hlower : -ε ≤ groundLam P R L hL N) (hCμ : C < μ)
    (hbudget : K * C + (K - 1) * ε ≤ μ) : JointGap P R L N K v := by
  obtain ⟨-, -, hmin, -, -⟩ := ground_spec P R hL N
  have hlC : groundLam P R L hL N ≤ C := by
    have h := hmin v hve
    rw [hv1, mul_one] at h
    exact h.trans hceil
  refine ⟨hL, μ, kt, lt_of_le_of_lt hlC hCμ, hfloor, ?_⟩
  exact joint_inequality_of_ceiling_lower hK hceil hlower hbudget

end Cvs.Route.SchurFloorJointGap
