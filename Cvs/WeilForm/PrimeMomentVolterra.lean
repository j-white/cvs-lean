import Mathlib
import Cvs.WeilForm.PrimePowerIndexed

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A coupled Volterra transform of the signed prime moments

The actual finite prime moment retains its endpoint and curvature in one ramp transform.
-/

noncomputable section

open Real Set Filter MeasureTheory Finset Matrix
open scoped Topology

namespace Cvs.WeilForm.PrimeMomentVolterra

/-- The first cosine frequency of the window. -/
def omega (L : ℝ) : ℝ := 2*π/L

/-- The actual truncated prime ramp. -/
def primeRamp (P R : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
    (ArithmeticFunction.vonMangoldt n*(n : ℝ)^(-(1/2) : ℝ))*max (t-Real.log n) 0

/-- The second primitive of the continuous arithmetic mean. -/
def meanRamp (t : ℝ) : ℝ := 4*Real.exp (t/2)-2*t-4

open Cvs.Zeta.Explicit.Weil

end Cvs.WeilForm.PrimeMomentVolterra
