import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.AveragedColumnEnergy
import Cvs.Prolate.Hardy.CarrierBoundBothColumns
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.HardyCarrierBound
import Cvs.Prolate.Hardy.HardyColumnLimsupBound
import Cvs.Prolate.Hardy.HardyExtensionHighpass
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.MixedTermColumnLimits
import Cvs.Prolate.Hardy.TraceLimitHighpassOperator
import Cvs.Route.Visibility.VisibilityLandauTransition

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hardy extension operator realises the exterior-column limits at the turning-point level

`J_c = hardyJ c` is one explicit witness for every `ε`: eventually `HighpassOp`, `S_J ≤ S_∞(1/√3) + ε` and
`|O_J| ≤ ε`, given `HardyModule`; this gives `HighpassColumnLimsup` at `S_∞(1/√3)` and `S_∞(3/5)`, then hV.
-/

noncomputable section

open Real Filter

namespace Cvs.Prolate.Hardy.HardyExtensionTurningLevel
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (hardyJ)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (extS extO)
open Cvs.Prolate.Hardy.AveragedColumnEnergy (avgEnergy)

/-- **One witness for every `ε`**: `J_c` is eventually highpass with `S_J ≤ S_∞(1/√3) + ε` and `|O_J| ≤ ε`. -/
theorem hardyJ_columns (hH : Cvs.Prolate.Hardy.HardyExtensionHighpass.HardyModule) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, Cvs.Prolate.Hardy.TraceLimitHighpassOperator.HighpassOp (2 * π * x) (hardyJ (2 * π * x)) ∧
      extS (2 * π * x) (hardyJ (2 * π * x)) ≤ avgEnergy (1 / √3) + ε ∧
      |extO (2 * π * x) (hardyJ (2 * π * x))| ≤ ε := by
  have hO := Cvs.Prolate.Hardy.MixedTermColumnLimits.eventually_abs_extO_le Cvs.Prolate.Hardy.MixedTermColumnLimits.closedBall_subset_ball (fun _ hz => Cvs.Prolate.Hardy.MixedTermColumnLimits.ellipse_box hz)
    Cvs.Prolate.Hardy.MixedTermColumnLimits.ellipse_sum_lt_one (fun x : ℕ => hardyJ (2 * π * x)) Cvs.Prolate.Hardy.HardyCarrierBound.eventually_carrierBound ε hε
  filter_upwards [eventually_ge_atTop 1, Cvs.Prolate.Hardy.HardyColumnLimsupBound.extS_hardyJ_le_nat hε, hO] with x hx hS hOx
  have : (1 : ℝ) ≤ x := by exact_mod_cast hx
  exact ⟨Cvs.Prolate.Hardy.HardyExtensionHighpass.hardyJ_highpassOp hH (by positivity), hS, hOx⟩

/-- **The exterior-column limits at the turning-point level** `S_∞(1/√3)`, from `HardyModule`. -/
theorem highpassColumnLimsup_turn (hH : Cvs.Prolate.Hardy.HardyExtensionHighpass.HardyModule) :
    Cvs.Prolate.Hardy.TraceLimitHighpassOperator.HighpassColumnLimsup (avgEnergy (1 / √3)) := by
  intro ε hε
  filter_upwards [hardyJ_columns hH hε] with x ⟨hJ, hS, hO⟩
  exact ⟨_, hJ, hS, (le_abs_self _).trans hO⟩

/-- **The workflow target** `HighpassColumnLimsup (S_∞(3/5))`, from `HardyModule`. -/
theorem highpassColumnLimsup_three_fifths (hH : Cvs.Prolate.Hardy.HardyExtensionHighpass.HardyModule) :
    Cvs.Prolate.Hardy.TraceLimitHighpassOperator.HighpassColumnLimsup (avgEnergy (3 / 5)) :=
  Cvs.Prolate.Hardy.TraceLimitHighpassOperator.highpassColumnLimsup_mono (by
    rw [Cvs.Prolate.Hardy.AveragedColumnEnergy.avgEnergy_turn, Cvs.Prolate.Hardy.AveragedColumnEnergy.avgEnergy_three_fifths]
    linarith [Cvs.Route.Visibility.VisibilityLandauTransition.thetaSharp_le_thetaCons]) (highpassColumnLimsup_turn hH)

end Cvs.Prolate.Hardy.HardyExtensionTurningLevel

end
