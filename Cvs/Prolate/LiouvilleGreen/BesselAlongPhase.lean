import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Upstream.BesselJZeroEquation
import Cvs.Upstream.BesselJZeroIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `J₀` along a phase

For a differentiable phase `ζ`, `(J₀∘ζ)′ = J₀′(ζ)ζ′` and `(J₀′∘ζ)′ = J₀″(ζ)ζ′`, and by Bessel's equation (Cvs.Upstream.BesselJZeroEquation)
`ζJ₀″(ζ) = −J₀′(ζ) − ζJ₀(ζ)`: the derivatives of the uniform approximant `A·J₀(ζ)` involve only `J₀(ζ)` and `J₀′(ζ)`,
the first step of Olver's residual identity.
-/

namespace Cvs.Prolate.LiouvilleGreen.BesselAlongPhase

open Real Cvs.Upstream.BesselJZeroIntegral Cvs.Upstream.BesselJZeroEquation

theorem hasDerivAt_besselJ0_comp {ζ : ℝ → ℝ} {ζ' s : ℝ} (hζ : HasDerivAt ζ ζ' s) :
    HasDerivAt (fun s => besselJ0 (ζ s)) (besselJ0' (ζ s) * ζ') s :=
  (hasDerivAt_besselJ0 (ζ s)).comp s hζ

theorem hasDerivAt_besselJ0'_comp {ζ : ℝ → ℝ} {ζ' s : ℝ} (hζ : HasDerivAt ζ ζ' s) :
    HasDerivAt (fun s => besselJ0' (ζ s)) (besselJ0'' (ζ s) * ζ') s :=
  (hasDerivAt_besselJ0' (ζ s)).comp s hζ

/-- `ζJ₀″(ζ) = −J₀′(ζ) − ζJ₀(ζ)`. -/
theorem mul_besselJ0''_eq (z : ℝ) : z * besselJ0'' z = -besselJ0' z - z * besselJ0 z := by
  have := bessel_ode z
  linarith

end Cvs.Prolate.LiouvilleGreen.BesselAlongPhase
