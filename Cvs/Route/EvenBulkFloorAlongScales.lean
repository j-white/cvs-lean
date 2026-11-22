import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.DivisorHyperbolaNymanBeurling
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.PowerLawVisibilityBulkFloor
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.WeilForm.DivisorHyperbolaFactorisation
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.GreenRemovesFirstArchChannel
import Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget
import Cvs.WeilForm.OrganisingIdentityGreen
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.PrimeOperatorPathLawDeficit
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WholeDomainUnification
import Cvs.WeilForm.WindowCircleIsometry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even bulk floor along an infinite set of scales

For an infinite `S ⊆ ℕ`, a floor holding at every large `x ∈ S` holds frequently, so every frequently-quantified
`RiemannHypothesis` criterion of `Cvs.Route.PowerLawVisibilityBulkFloor` and `Cvs.Route.DivisorHyperbolaNymanBeurling` may be proved along `S`. For each infinite `S` and each
nonnegative subpolynomial loss, the floor along `S` is equivalent to `RiemannHypothesis`, and off it the floor
fails at every large `x ∈ S` for each loss exponent below `topDepth`.
-/

noncomputable section

open Real Filter Set
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.Route.EvenBulkFloorAlongScales
open Cvs.ZeroCounting

/-! ### 1. Along an infinite set -/

/-- A property holding at every large element of an infinite `S ⊆ ℕ` holds frequently. -/
theorem frequently_of_eventually_mem {S : Set ℕ} (hS : S.Infinite) {P : ℕ → Prop}
    (h : ∀ᶠ x : ℕ in atTop, x ∈ S → P x) : ∃ᶠ x : ℕ in atTop, P x :=
  ((Nat.frequently_atTop_iff_infinite.mpr hS).and_eventually h).mono fun _ hx => hx.2 hx.1

/-- A subpolynomial-loss criterion along an infinite `S` gives the same criterion frequently. -/
theorem exists_subPoly_frequently_of_along {S : Set ℕ} (hS : S.Infinite) {P : (ℕ → ℝ) → ℕ → Prop}
    (h : ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, x ∈ S → P Q x) :
    ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∃ᶠ x : ℕ in atTop, P Q x :=
  let ⟨Q, hQ, hS'⟩ := h
  ⟨Q, hQ, frequently_of_eventually_mem hS hS'⟩

/-- The even bulk floor at loss `Q x` at every large `x ∈ S`. -/
def FloorAlong (S : Set ℕ) (Q : ℕ → ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, x ∈ S → Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-Q x)

/-! ### 2. The reduction along `S` and its converse -/

/-- **A subpolynomial-loss floor along an infinite `S` gives `RiemannHypothesis`.** -/
theorem rh_of_floorAlong {S : Set ℕ} (hS : S.Infinite) {Q : ℕ → ℝ} (hQ : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q)
    (h : FloorAlong S Q) : RiemannHypothesis :=
  Cvs.Route.PowerLawVisibilityBulkFloor.rh_iff_exists_subPoly_evenBulkFloor.mpr ⟨Q, hQ, frequently_of_eventually_mem hS h⟩

/-- **Floors at loss `x^ε` for every `ε > 0` along an infinite `S` give `RiemannHypothesis`.** -/
theorem rh_of_rpow_floorAlong {S : Set ℕ} (hS : S.Infinite)
    (h : ∀ ε : ℝ, 0 < ε → FloorAlong S fun x => (x : ℝ) ^ ε) : RiemannHypothesis :=
  Cvs.Route.PowerLawVisibilityBulkFloor.rh_iff_subpoly_evenBulkFloor.mpr fun ε hε => frequently_of_eventually_mem hS (h ε hε)

/-- Under `RiemannHypothesis` the floor holds along every `S` at every eventually nonnegative loss. -/
theorem floorAlong_of_rh (hRH : RiemannHypothesis) (S : Set ℕ) {Q : ℕ → ℝ}
    (hQ0 : ∀ᶠ x : ℕ in atTop, 0 ≤ Q x) : FloorAlong S Q := by
  filter_upwards [eventually_ge_atTop 2, hQ0] with x hx2 hQx _
  exact Cvs.Route.PowerLawVisibilityBulkFloor.evenBulkFloor_mono (by linarith) (Cvs.Route.EvenWindowBulkCoupling.even_floor_coupling_zero_of_rh hRH hx2).2.1

/-- **For each infinite `S` and nonnegative subpolynomial `Q`, the floor along `S` is `RiemannHypothesis`.** -/
theorem rh_iff_floorAlong {S : Set ℕ} (hS : S.Infinite) {Q : ℕ → ℝ} (hQ : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q)
    (hQ0 : ∀ᶠ x : ℕ in atTop, 0 ≤ Q x) : RiemannHypothesis ↔ FloorAlong S Q :=
  ⟨fun hRH => floorAlong_of_rh hRH S hQ0, rh_of_floorAlong hS hQ⟩

/-- **For each infinite `S`: `RiemannHypothesis ↔` the floor at loss `x^ε` along `S` for every `ε > 0`.** -/
theorem rh_iff_rpow_floorAlong {S : Set ℕ} (hS : S.Infinite) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → FloorAlong S fun x => (x : ℝ) ^ ε :=
  ⟨fun hRH ε _ => floorAlong_of_rh hRH S
    (Eventually.of_forall fun x => Real.rpow_nonneg (Nat.cast_nonneg x) ε), rh_of_rpow_floorAlong hS⟩

/-- **The choice of infinite `S` does not change the floor statement**: both sides are `RiemannHypothesis`. -/
theorem floorAlong_iff_floorAlong {S S' : Set ℕ} (hS : S.Infinite) (hS' : S'.Infinite) {Q : ℕ → ℝ}
    (hQ : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q) (hQ0 : ∀ᶠ x : ℕ in atTop, 0 ≤ Q x) :
    FloorAlong S Q ↔ FloorAlong S' Q :=
  (rh_iff_floorAlong hS hQ hQ0).symm.trans (rh_iff_floorAlong hS' hQ hQ0)

/-! ### 3. Off `RiemannHypothesis`, along every `S` -/

/-- **Off `RiemannHypothesis`, along every `S`**: for `κ < topDepth` the floor at loss `C · x^κ` fails at every
large `x ∈ S`. -/
theorem eventually_not_floor_of_mem (hRH : ¬ RiemannHypothesis) (S : Set ℕ) {κ : ℝ}
    (hκ : κ < Cvs.StepA.Edge.CaseInfinityJointRates.topDepth) (C : ℝ) :
    ∀ᶠ x : ℕ in atTop, x ∈ S → ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-C * (x : ℝ) ^ κ) :=
  (Cvs.Route.PowerLawVisibilityBulkFloor.hV_lt_topDepth hRH hκ C).mono fun _ hx _ => hx

/-- Off `RiemannHypothesis`, no infinite `S` carries the floor at loss `C · x^κ` for `κ < topDepth`. -/
theorem not_floorAlong_rpow_of_not_rh (hRH : ¬ RiemannHypothesis) {S : Set ℕ} (hS : S.Infinite) {κ : ℝ}
    (hκ : κ < Cvs.StepA.Edge.CaseInfinityJointRates.topDepth) (C : ℝ) :
    ¬ FloorAlong S fun x => C * (x : ℝ) ^ κ := by
  intro h
  have hf := frequently_of_eventually_mem hS
    ((h.and (eventually_not_floor_of_mem hRH S hκ C)).mono fun x hx hxS => (hx.2 hxS) (by
      simpa [neg_mul] using hx.1 hxS))
  exact hf (Eventually.of_forall fun _ hx => hx)

/-- **Zero-free strip from a power-loss floor along an infinite `S`**: loss `C · x^θ` (`θ ≥ 0`) gives
`1/2 − θ ≤ Re ρ ≤ 1/2 + θ`. -/
theorem zeroFreeStrip_of_rpow_floorAlong {S : Set ℕ} (hS : S.Infinite) {θ C : ℝ} (hθ : 0 ≤ θ)
    (h : FloorAlong S fun x => C * (x : ℝ) ^ θ) (ρ : nonTrivialZeroSet) :
    1 / 2 - θ ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ 1 / 2 + θ :=
  Cvs.Route.PowerLawVisibilityBulkFloor.zeroFreeStrip_of_frequently_evenBulkFloor_neg_rpow (C := C) hθ
    (frequently_of_eventually_mem hS (h.mono fun _ hx hxS => by simpa [neg_mul] using hx hxS)) ρ

/-! ### 4. Prime-side criteria along `S` -/

/-- **Mean-free prime side along an infinite `S`**: `RiemannHypothesis ↔`
`meanFreePrimeTerm ≤ archTerm + Q(x)‖w‖²` on `Ev x ∩ (R₁ x)ᗮ` at every large `x ∈ S`, `Q` subpolynomial. -/
theorem rh_iff_meanFreePrime_along {S : Set ℕ} (hS : S.Infinite) :
    RiemannHypothesis ↔
      ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, x ∈ S → ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
        Cvs.WeilForm.OrganisingIdentityGreen.meanFreePrimeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
          ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) + Q x * ‖w‖ ^ 2 := by
  constructor
  · intro hRH
    refine ⟨fun _ => 4, Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 4, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with x hx _ w hwE hwR
    exact Cvs.Route.PowerLawVisibilityBulkFloor.meanFreePrime_le_arch_add_four_of_rh hRH hx hwE hwR
  · exact fun h => Cvs.Route.PowerLawVisibilityBulkFloor.rh_iff_meanFreePrime_le_arch_add_subPoly.mpr (exists_subPoly_frequently_of_along hS h)

/-- **Path-Law SOS criterion along an infinite `S`** (`Cvs.Route.PowerLawVisibilityBulkFloor.rh_of_pathLaw_schur_subPoly` along `S`). -/
theorem rh_of_pathLaw_along {S : Set ℕ} (hS : S.Infinite) {Q : ℕ → ℝ} (hQ : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q)
    (hF : ∀ᶠ x : ℕ in atTop, x ∈ S → ∃ hx : 1 < x, ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
      (Cvs.PrimeOperator.atomBudget x x (Nat.clog 2 x) - Q x) * ‖w‖ ^ 2
        ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm x x (Nat.clog 2 x)
              (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm x x (Nat.clog 2 x)
              (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))) :
    RiemannHypothesis :=
  Cvs.Route.PowerLawVisibilityBulkFloor.rh_of_pathLaw_schur_subPoly hQ (frequently_of_eventually_mem hS hF)

/-- **Divisor–Möbius criterion along an infinite `S`** (`Cvs.Route.DivisorHyperbolaNymanBeurling.rh_of_divisor_moebius_subPoly` along `S`). -/
theorem rh_of_divisor_moebius_along {S : Set ℕ} (hS : S.Infinite) {Q : ℕ → ℝ} {α : ℝ}
    (hQ : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q)
    (hF : ∀ᶠ x : ℕ in atTop, x ∈ S → ∃ hx : 1 < x, ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
      2 * ‖Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition.Op x (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
            (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ *
          ‖ContinuousLinearMap.adjoint (Cvs.WeilForm.MaskedShift.DirichletConvolutionComposition.Op x (Cvs.WeilForm.DivisorHyperbolaFactorisation.divisorDiscrepancy α))
            (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))‖ -
        Cvs.WeilForm.WholeDomainUnification.smoothPoleZetaRem hx α (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) ≤
        (∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t * Cvs.WeilForm.EvenBulkVisibility.rho w t) + Q x * ‖w‖ ^ 2) :
    RiemannHypothesis :=
  Cvs.Route.DivisorHyperbolaNymanBeurling.rh_of_divisor_moebius_subPoly hQ (frequently_of_eventually_mem hS hF)

end Cvs.Route.EvenBulkFloorAlongScales
