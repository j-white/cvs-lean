import Mathlib
import Cvs.Prolate.Hardy.AveragedColumnEnergy
import Cvs.Prolate.Hardy.HardyExtensionHighpass
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.HardyExtensionTurningLevel
import Cvs.Prolate.Hardy.TraceLimitHighpassOperator
import Cvs.Upstream.HardyBoundedMultiplier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hardy module, `CEBound (57/60)` from Landau's transition law, and hV

`Cvs.Upstream.HardyBoundedMultiplier.hardyModule` discharges `Cvs.Prolate.Hardy.HardyExtensionHighpass.HardyModule` in `Cvs.Prolate.Hardy.HardyExtensionHighpass.hardyJ_highpassOp` and in the `Cvs.Prolate.Hardy.HardyExtensionTurningLevel` results.
-/

noncomputable section

open Real Filter

namespace Cvs.Route.Visibility.VisibilityHardyModule
open Cvs.ZeroCounting

/-- **`H²` of the upper half-plane is a module over `H^∞`.** -/
theorem hardyModule : Cvs.Prolate.Hardy.HardyExtensionHighpass.HardyModule :=
  Cvs.Upstream.HardyBoundedMultiplier.hardyModule

/-- **`J_c` is a highpass extension operator** for every `c > 0`. -/
theorem hardyJ_highpassOp {c : ℝ} (hc : 0 < c) : Cvs.Prolate.Hardy.TraceLimitHighpassOperator.HighpassOp c (Cvs.Prolate.Hardy.HardyExtensionOperator.hardyJ c) :=
  Cvs.Prolate.Hardy.HardyExtensionHighpass.hardyJ_highpassOp hardyModule hc

/-- **The exterior-column limits** `HighpassColumnLimsup (S_∞(3/5))`. -/
theorem highpassColumnLimsup_three_fifths : Cvs.Prolate.Hardy.TraceLimitHighpassOperator.HighpassColumnLimsup (Cvs.Prolate.Hardy.AveragedColumnEnergy.avgEnergy (3 / 5)) :=
  Cvs.Prolate.Hardy.HardyExtensionTurningLevel.highpassColumnLimsup_three_fifths hardyModule

end Cvs.Route.Visibility.VisibilityHardyModule

end
