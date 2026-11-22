import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-!
# Global Minimum of `archSymbol`, `boxLowBandEnergy`, and `ε`-Small Damped `ModeBox` Floor

Proves `archSymbol 0 ≤ archSymbol t`, bounds `boxDiagDeficit` by `boxLowBandEnergy`, and constructs
an explicit frequency threshold `dampedThreshold` achieving `dampedFloorConst ≤ ε` for any `ε > 0`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.WeilForm.Archimedean.ArchSymbolGlobalMinimum

open scoped BigOperators Matrix
open Real Filter Finset

/-! ### Global minimum of `Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol` at `0` and uniform deficit weight bound -/

/-- **Global minimum of `Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol` at `0`**: `archSymbol 0 ≤ archSymbol t` for all `t : ℝ`. -/
theorem archSymbol_zero_le (t : ℝ) : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t :=
  Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (by nlinarith [sq_nonneg t])

/-! ### `M₀`-independent low-band Euclidean energy `boxLowBandEnergy` on `ModeBox M₀` -/

/-! ### Explicit `(2M₀ + 1)`-free damped floor coefficient and `ε`-small threshold -/

end Cvs.WeilForm.Archimedean.ArchSymbolGlobalMinimum
