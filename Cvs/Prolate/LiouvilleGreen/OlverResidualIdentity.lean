import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.BesselAlongPhase
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
# Olver's residual identity

For `g = A·J₀(ζ)` with `g′ = A′J₀(ζ) + Aζ′J₀′(ζ)`: if the phase obeys `Pζ′² = Q` and the amplitude obeys Olver's
cancellation `(PA′)ζ′ + (PAζ′)′ = PAζ′²/ζ` (satisfied by `A = (ζ²/(PQ))^{1/4}`), then
`(Pg′)′ + Qg = (PA′)′·J₀(ζ)`: the uniform approximant solves `(Pψ′)′ + Qψ = 0` up to the explicit residual
`(PA′)′J₀(ζ)`, which a comparison argument turns into the approximation error.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverResidualIdentity

open Real Cvs.Upstream.BesselJZeroIntegral Cvs.Upstream.BesselJZeroEquation Cvs.Prolate.LiouvilleGreen.BesselAlongPhase

/-- **Olver's residual identity.** -/
theorem hasDerivAt_olver {P Q A A' ζ ζ' U V : ℝ → ℝ} {w V' s : ℝ}
    (hζ : HasDerivAt ζ (ζ' s) s) (hζ0 : ζ s ≠ 0)
    (hU : HasDerivAt U w s) (hUeq : U = fun s => P s * A' s)
    (hV : HasDerivAt V V' s) (hVeq : V = fun s => P s * A s * ζ' s)
    (hphase : P s * ζ' s ^ 2 = Q s)
    (holver : U s * ζ' s + V' = V s * ζ' s / ζ s) :
    HasDerivAt (fun s => P s * (A' s * besselJ0 (ζ s) + A s * ζ' s * besselJ0' (ζ s)))
      (w * besselJ0 (ζ s) - Q s * (A s * besselJ0 (ζ s))) s := by
  -- `P g′ = U·J₀(ζ) + V·J₀′(ζ)`
  have hfun : (fun s => P s * (A' s * besselJ0 (ζ s) + A s * ζ' s * besselJ0' (ζ s)))
      = fun s => U s * besselJ0 (ζ s) + V s * besselJ0' (ζ s) := by
    funext x; rw [hUeq, hVeq]; ring
  rw [hfun]
  have h := ((hU.mul (hasDerivAt_besselJ0_comp hζ)).add (hV.mul (hasDerivAt_besselJ0'_comp hζ)))
  refine h.congr_deriv ?_
  -- eliminate `J₀″(ζ)` and use the two conditions
  have hB := mul_besselJ0''_eq (ζ s)
  have hJ'' : besselJ0'' (ζ s) = (-besselJ0' (ζ s) - ζ s * besselJ0 (ζ s)) / ζ s := by
    field_simp; linarith
  rw [hJ'']
  have hVs : V s = P s * A s * ζ' s := by rw [hVeq]
  have hV2 : V s * ζ' s = A s * Q s := by rw [hVs, ← hphase]; ring
  have e : w * besselJ0 (ζ s) + U s * (besselJ0' (ζ s) * ζ' s)
      + (V' * besselJ0' (ζ s) + V s * ((-besselJ0' (ζ s) - ζ s * besselJ0 (ζ s)) / ζ s * ζ' s))
      = w * besselJ0 (ζ s) + besselJ0' (ζ s) * (U s * ζ' s + V' - V s * ζ' s / ζ s) - V s * ζ' s * besselJ0 (ζ s) := by
    field_simp; ring
  rw [e, holver, hV2]; ring

end Cvs.Prolate.LiouvilleGreen.OlverResidualIdentity
