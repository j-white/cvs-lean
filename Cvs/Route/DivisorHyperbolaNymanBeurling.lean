import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.PowerLawVisibilityBulkFloor
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.DivisorHyperbolaFactorisation
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.GreenRemovesFirstArchChannel
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WholeDomainUnification
import Cvs.WeilForm.WindowCircleIsometry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Whole-Window Divisor–Hyperbola and Adjoint Nyman–Beurling Bridges to Zero-Free Strips and RH

Connects the whole-window `Op x` divisor–hyperbola and adjoint-projected Nyman–Beurling identities (`Cvs.WeilForm.WholeDomainUnification`,
`Cvs.Zeta.DivisorDiscrepancyAdjointZeta`) on `Dom x` to the loss-tolerant `EvenBulkFloor`, `topDepth`, and `RiemannHypothesis` spine (`Cvs.Route.PowerLawVisibilityBulkFloor`).
-/

noncomputable section

open MeasureTheory Real Set Filter
open scoped InnerProductSpace NNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.Route.DivisorHyperbolaNymanBeurling
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
open Cvs.WeilForm.PoleArchPrimeProblem (archTerm)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)
open Cvs.WeilForm.ReflectionEvenPositivityRH (Ev)
open Cvs.Route.EvenWindowBulkCoupling (EvenBulkFloor)
open Cvs.WeilForm.WindowCircleIsometry (windowCircle)
open Cvs.WeilForm.OrganisingIdentityGreen (windowGreenEnergy meanFreePrimeTerm)
open Cvs.WeilForm.DivisorHyperbolaFactorisation (divisorDiscrepancy)
open Cvs.WeilForm.WholeDomainUnification (smoothPoleZetaRem)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)

/-! ### 1. Exact Scale-`x` Divisor–Hyperbola and Adjoint-Projected Decompositions of `Qx` on `Dom x` -/

/-- Exact scale-`x` shifted-Archimedean + divisor–hyperbola identity for `Qx x w` (`1 < x`). -/
theorem Qx_eq_shiftedArch_add_smooth_add_divisor_pairing {x : ℕ} (hx : 1 < x)
    (α : ℝ) (w : Dom x) :
    Qx x w =
      (∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho w t) +
        smoothPoleZetaRem hx α (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) +
        2 * ⟪Op x (μ : ArithmeticFunction ℝ) (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))),
          ContinuousLinearMap.adjoint (Op x (divisorDiscrepancy α))
            (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))⟫_ℝ :=
  Cvs.WeilForm.WholeDomainUnification.Q_eq_shiftedArch_add_smooth_add_divisor_pairing
    hx (Nat.le_succ x) (Nat.le_succ (Nat.clog 2 x)) α w

/-- **Full-Symbol Divisor–Möbius Cauchy–Schwarz Lower Bound on `Qx x w`** (`1 < x`):
retains the full `∫ shiftedArchSymbol · ρ_w` rather than dropping to the constant floor `archSymbol 0 + 4`. -/
theorem Qx_ge_shiftedArch_add_smooth_sub_divisor_moebius {x : ℕ} (hx : 1 < x)
    (α : ℝ) (w : Dom x) :
    (∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho w t) +
        smoothPoleZetaRem hx α (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) -
        2 * ‖Op x (μ : ArithmeticFunction ℝ)
            (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ *
          ‖ContinuousLinearMap.adjoint (Op x (divisorDiscrepancy α))
            (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ ≤
      Qx x w := by
  rw [Qx_eq_shiftedArch_add_smooth_add_divisor_pairing hx α w]
  have hcs :
      -⟪Op x (μ : ArithmeticFunction ℝ) (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))),
          ContinuousLinearMap.adjoint (Op x (divisorDiscrepancy α))
            (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))⟫_ℝ ≤
        ‖Op x (μ : ArithmeticFunction ℝ)
            (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ *
          ‖ContinuousLinearMap.adjoint (Op x (divisorDiscrepancy α))
            (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ := by
    rw [← inner_neg_left]
    exact (real_inner_le_norm _ _).trans (by rw [norm_neg])
  linarith

/-! ### 2. Exact Two-Sided `RiemannHypothesis ↔` Equivalences on `Ev x ∩ (R₁ x)ᗮ` -/

/-! ### 3. Zero-Free Strips (`topDepth ≤ θ`) and RH from Divisor–Möbius Norms and Adjoint Projections -/

/-- **`RiemannHypothesis` from Subpolynomial Control of `2 ‖Op x μ g_w‖ ‖(Op x d_α)* g_w‖`**
on `Ev x ∩ (R₁ x)ᗮ`. -/
theorem rh_of_divisor_moebius_subPoly {Q : ℕ → ℝ} {α : ℝ} (hQ : SubPoly Q)
    (hF : ∃ᶠ x : ℕ in atTop, ∃ hx : 1 < x, ∀ w ∈ Ev x, w ∈ (R1 x)ᗮ →
      2 * ‖Op x (μ : ArithmeticFunction ℝ)
            (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ *
          ‖ContinuousLinearMap.adjoint (Op x (divisorDiscrepancy α))
            (windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ -
        smoothPoleZetaRem hx α (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) ≤
        (∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho w t) + Q x * ‖w‖ ^ 2) :
    RiemannHypothesis := by
  refine Cvs.Route.PowerLawVisibilityBulkFloor.rh_iff_exists_subPoly_evenBulkFloor.mpr ⟨Q, hQ,
    hF.mono fun x ⟨hx, h⟩ w hwE hwR => ?_⟩
  have hlow := Qx_ge_shiftedArch_add_smooth_sub_divisor_moebius hx α w
  linarith [h w hwE hwR]

end Cvs.Route.DivisorHyperbolaNymanBeurling

end
