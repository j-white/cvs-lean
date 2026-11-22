import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.ProjIcc
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge
import Cvs.Prolate.LiouvilleGreen.LayerFrequencySecondDerivative
import Cvs.Prolate.LiouvilleGreen.LayerProlateSystem
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat
import Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
import Cvs.Prolate.LiouvilleGreen.OlverRungError

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Olver's residual in closed form

With `L = a′/(af) = P̃′/(P̃f) + f′/f²`: `R′ = (1 − ζL)/P̃` and `P̃A′ = (1 − ζL)/(2√R)`, so the residual is
`w = (P̃A′)′ = −(fL + ζL′)/(2√R) − (1 − ζL)R′/(4R√R)` with
`L′ = P̃″/(P̃f) − P̃′(P̃′f + P̃f′)/(P̃f)² + f″/f² − 2f′²/f³`, `P̃″ = 3s/(2c²)`: explicit in `s`, `f`, `f′`, `f″`, `ζ`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverResidualClosedForm

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero Cvs.Prolate.LiouvilleGreen.OlverRungError Cvs.Prolate.LiouvilleGreen.LayerFrequencySecondDerivative

/-- `P̃′ = 1 + 3s²/(4c²)`. -/
noncomputable def pS' (c s : ℝ) : ℝ := 1 + 3 * s ^ 2 / (4 * c ^ 2)

/-- `L = P̃′/(P̃f) + f′/f²`. -/
noncomputable def logRate (c χ s : ℝ) : ℝ := pS' c s / (pS c s * freqS c χ s) + freqS' c χ s / freqS c χ s ^ 2

/-- `L′`. -/
noncomputable def logRate' (c χ s : ℝ) : ℝ :=
  3 * s / (2 * c ^ 2) / (pS c s * freqS c χ s)
    - pS' c s * (pS' c s * freqS c χ s + pS c s * freqS' c χ s) / (pS c s * freqS c χ s) ^ 2
    + freqS'' c χ s / freqS c χ s ^ 2 - 2 * freqS' c χ s ^ 2 / freqS c χ s ^ 3

/-- **Olver's residual** `w = (P̃A′)′`. -/
noncomputable def olverResid (c χ s : ℝ) : ℝ :=
  -(freqS c χ s * logRate c χ s + olverZeta c χ s * logRate' c χ s) / (2 * √(ampRatio c χ s))
    - (1 - olverZeta c χ s * logRate c χ s) * ampRatio' c χ s / (4 * ampRatio c χ s * √(ampRatio c χ s))

theorem hasDerivAt_pS' {c : ℝ} (hc : 0 < c) (s : ℝ) : HasDerivAt (pS' c) (3 * s / (2 * c ^ 2)) s := by
  have := ((hasDerivAt_pow 2 s).const_mul 3 |>.div_const (4 * c ^ 2)).const_add 1
  refine this.congr_deriv ?_
  field_simp; ring

theorem hasDerivAt_logRate {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hs : 0 < s) :
    HasDerivAt (logRate c χ) (logRate' c χ s) s := by
  have hf := freqS_pos (s := s) hc hχc
  have hp := pS_pos hc hs
  have hF := hasDerivAt_freqS hc hχc s
  have hPf := (hasDerivAt_pS hc s).mul hF
  have h1 := (hasDerivAt_pS' hc s).div hPf (mul_pos hp hf).ne'
  have h2 := (hasDerivAt_freqS' hc hχc s).div (hF.pow 2) (pow_pos hf 2).ne'
  refine (h1.add h2).congr_deriv ?_
  unfold logRate' pS'
  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  rw [show s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s) = freqS' c χ s from rfl]
  field_simp
  ring

/-- **`R′ = (1 − ζL)/P̃`.** -/
theorem ampRatio'_eq {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hs : 0 < s) :
    ampRatio' c χ s = (1 - olverZeta c χ s * logRate c χ s) / pS c s := by
  have hf := freqS_pos (s := s) hc hχc
  have hp := pS_pos hc hs
  unfold ampRatio' logRate pS'
  rw [show s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s) = freqS' c χ s from rfl]
  field_simp

/-- **`P̃A′ = (1 − ζL)/(2√R)`.** -/
theorem pS_mul_olverAmp' {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hs : 0 < s) :
    pS c s * olverAmp' c χ s = (1 - olverZeta c χ s * logRate c χ s) / (2 * √(ampRatio c χ s)) := by
  have hp := pS_pos hc hs
  unfold olverAmp' olverAmp
  rw [ampRatio'_eq hc hχc hs]
  field_simp

/-- **The residual `w = (P̃A′)′` in closed form.** -/
theorem hasDerivAt_pS_mul_olverAmp' {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    HasDerivAt (fun y => pS c y * olverAmp' c χ y) (olverResid c χ s) s := by
  have hR := ampRatio_pos hc hχ0 hχc hs
  have hN := (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_olverZeta (χ := χ) hc s).mul (hasDerivAt_logRate hc hχc hs))
  have hD := ((hasDerivAt_ampRatio hc hχc hs).sqrt hR.ne').const_mul 2
  have hq := hN.div hD (by positivity)
  have hev : (fun y => pS c y * olverAmp' c χ y) =ᶠ[𝓝 s]
      fun y => (1 - olverZeta c χ y * logRate c χ y) / (2 * √(ampRatio c χ y)) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy using pS_mul_olverAmp' hc hχc hy
  refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
  have hsq : 0 < √(ampRatio c χ s) := Real.sqrt_pos.mpr hR
  have hsq2 : √(ampRatio c χ s) ^ 2 = ampRatio c χ s := Real.sq_sqrt hR.le
  unfold olverResid
  simp only [Pi.sub_apply, Pi.mul_apply]
  field_simp
  rw [hsq2]
  ring

end Cvs.Prolate.LiouvilleGreen.OlverResidualClosedForm
