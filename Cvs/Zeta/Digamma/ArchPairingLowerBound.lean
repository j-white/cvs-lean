import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real

namespace Cvs.Zeta.Digamma.ArchPairingLowerBound

/-!
# The venue's archimedean pairing, bounded below

The venue defines `CompletedGammaTest.archimedeanPairing` and proves it is literally `∫
frequencyDensity · Re logDeriv Γ_ℝ(1/2 + iu)`.
-/

/-- The uniform archimedean constant, `−(log π)/2 + ψ(1/4)/2`. -/
noncomputable def archConst : ℝ :=
  -(Real.log π) / 2 + (Complex.digamma (((1 / 4 : ℝ)) : ℂ)).re / 2

end Cvs.Zeta.Digamma.ArchPairingLowerBound
