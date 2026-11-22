import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The variation of a dilated mode's amplitude product

The derivative of the amplitude product `A(mt)/(2(m′t)^{n+1})` of Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeProduct is bounded on `[p, q]` with `mp ≥ ξ₀` by
the amplitude bound times `2m(mp/√((mp)² − 1))(mp/((mp)² − 1)) + (n + 1)/p`: the rung's relative rate through the
correction bound of Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow at the dilated point, times the chain factor `m`, plus the profile's own decay. With an earlier result's
partition argument this is the datum `V` of the dilated-mode pairings.
-/

namespace Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeVariation

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-- The amplitude bound of Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeProduct: `√(E(ξ₀)fac(ξ₀)/a(mp))/(2(m′p)^{n+1})`. -/
noncomputable def ampBoundM (c χ : ℝ) (ψ u : ℝ → ℝ) (ξ₀ p : ℝ) (m m' n : ℕ) : ℝ :=
  √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ ((m : ℝ) * p)) / (2 * ((m' : ℝ) * p) ^ (n + 1))

end Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeVariation
