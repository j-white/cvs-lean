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
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
import Cvs.Prolate.LiouvilleGreen.OlverResidualClosedForm
import Cvs.Prolate.LiouvilleGreen.OlverRungError

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Olver's rung error from a bound on the truncated `c = 1` residual integral

The explicit residual `w = (P̃A′)′` (Cvs.Prolate.LiouvilleGreen.OlverResidualClosedForm) is continuous for `s > 0` and rescales as `w(s) = ŵ(s/c)/c`, `ŵ` the
residual at `c = 1`, `χ̂ = χ/c²`. So if `∫_{t₀}^{t₁} |ŵ|/(P̂f̂) ≤ K` for every `t₀ ∈ (0, t₁)`, `t₁ = s₁/c`, a rung
with `ψ(ξ(s)) → c₀` and `|u(ξ(s))| ≤ Cs²` at the edge obeys `|ψ(ξ(s₁)) − c₀A(s₁)J₀(ζ(s₁))| ≤ |c₀|K/c`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverTruncatedResidual

open Real Set Filter Topology MeasureTheory Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Upstream.BesselJZeroIntegral Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.OlverApproximantSystem Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero Cvs.Prolate.LiouvilleGreen.ApproximantErrorContinuous Cvs.Prolate.LiouvilleGreen.OlverRungError Cvs.Prolate.LiouvilleGreen.LayerFrequencySecondDerivative Cvs.Prolate.LiouvilleGreen.OlverResidualClosedForm

/-- **The residual is continuous** for `s > 0`. -/
theorem continuousAt_olverResid {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    ContinuousAt (olverResid c χ) s := by
  have hf := freqS_pos (s := s) hc hχc
  have hp := pS_pos hc hs
  have hR := ampRatio_pos hc hχ0 hχc hs
  have cf : ContinuousAt (freqS c χ) s := (hasDerivAt_freqS hc hχc s).continuousAt
  have cf' : ContinuousAt (freqS' c χ) s := (hasDerivAt_freqS' hc hχc s).continuousAt
  have cp : ContinuousAt (pS c) s := (hasDerivAt_pS hc s).continuousAt
  have cz : ContinuousAt (olverZeta c χ) s := (hasDerivAt_olverZeta hc s).continuousAt
  have cR : ContinuousAt (ampRatio c χ) s := (hasDerivAt_ampRatio hc hχc hs).continuousAt
  have cL : ContinuousAt (logRate c χ) s := (hasDerivAt_logRate hc hχc hs).continuousAt
  have cp' : ContinuousAt (pS' c) s := (hasDerivAt_pS' hc s).continuousAt
  have cf'' : ContinuousAt (freqS'' c χ) s := by
    unfold freqS''
    have hξ1 : 0 < xiOf c s + 1 := by linarith [one_le_xiOf c s]
    have cx : ContinuousAt (xiOf c) s := (hasDerivAt_xiOf c s hc.ne').continuousAt
    have crx : ContinuousAt (fun y => radXi c χ (xiOf c y)) s :=
      ((hasDerivAt_radXi (c := c) (χ := χ) hξ1.ne').continuousAt).comp cx
    refine ContinuousAt.sub (ContinuousAt.div (crx.add ((continuousAt_id.pow 2 |>.div_const _).mul
      (continuousAt_const.div ((cx.add continuousAt_const).pow 3) (pow_pos hξ1 3).ne'))) (continuousAt_const.mul cf)
      (mul_pos (mul_pos two_pos (pow_pos hc 4)) hf).ne') (ContinuousAt.div ((continuousAt_id.mul crx).mul cf') (continuousAt_const.mul (cf.pow 2))
      (mul_pos (mul_pos two_pos (pow_pos hc 4)) (pow_pos hf 2)).ne')
  have cL' : ContinuousAt (logRate' c χ) s := by
    unfold logRate'
    have hpf : pS c s * freqS c χ s ≠ 0 := (mul_pos hp hf).ne'
    refine ((((continuousAt_const.mul continuousAt_id).div_const _).div (cp.mul cf) hpf).sub
      ((cp'.mul ((cp'.mul cf).add (cp.mul cf'))).div ((cp.mul cf).pow 2) (pow_ne_zero 2 hpf))).add
      (cf''.div (cf.pow 2) (pow_pos hf 2).ne') |>.sub ((continuousAt_const.mul (cf'.pow 2)).div (cf.pow 3) (pow_pos hf 3).ne')
  have cR' : ContinuousAt (ampRatio' c χ) s := by
    have e : ∀ᶠ y in nhds s, ampRatio' c χ y = (1 - olverZeta c χ y * logRate c χ y) / pS c y := by
      filter_upwards [Ioi_mem_nhds hs] with y hy using ampRatio'_eq hc hχc hy
    refine ContinuousAt.congr ?_ (Filter.EventuallyEq.symm e)
    exact (continuousAt_const.sub (cz.mul cL)).div cp hp.ne'
  have csq : ContinuousAt (fun y => √(ampRatio c χ y)) s := cR.sqrt
  have hsq : 0 < √(ampRatio c χ s) := Real.sqrt_pos.mpr hR
  unfold olverResid
  exact ((cf.mul cL).add (cz.mul cL')).neg.div (continuousAt_const.mul csq) (mul_pos two_pos hsq).ne' |>.sub
    (((continuousAt_const.sub (cz.mul cL)).mul cR').div ((continuousAt_const.mul cR).mul csq) (mul_pos (mul_pos (by norm_num) hR) hsq).ne')

end Cvs.Prolate.LiouvilleGreen.OlverTruncatedResidual
