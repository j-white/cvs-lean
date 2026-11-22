import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate system in the layer variable

With `ξ = ξ(s)` and `φ = ψ∘ξ`, the prolate system `ψ′ = u/p`, `u′ = −qψ` becomes `φ′ = (u∘ξ)/P̃`,
`(u∘ξ)′ = −Q̃φ` with `P̃ = s(ξ + 1)/2 = pc²/s` and `Q̃ = qs/c²`. Then `P̃Q̃ = pq = a²`, and Olver's phase condition
`P̃ζ′² = Q̃` holds for `ζ′ = f_s`, so `olverZeta` is the Olver phase of the layer system and `P̃f_s = a`.
-/

namespace Cvs.Prolate.LiouvilleGreen.LayerProlateSystem

open Real Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate

/-- The layer system's `P̃ = s(ξ(s) + 1)/2`. -/
noncomputable def pS (c s : ℝ) : ℝ := s * (xiOf c s + 1) / 2

/-- The layer system's `Q̃ = q(ξ(s))·s/c²`. -/
noncomputable def qS (c χ s : ℝ) : ℝ := qP c χ (xiOf c s) * s / c ^ 2

theorem one_lt_xiOf {c s : ℝ} (hc : 0 < c) (hs : 0 < s) : 1 < xiOf c s := by
  unfold xiOf
  have : 0 < s ^ 2 / (2 * c ^ 2) := by positivity
  linarith

theorem pS_pos {c s : ℝ} (hc : 0 < c) (hs : 0 < s) : 0 < pS c s := by
  have := one_lt_xiOf hc hs
  unfold pS; nlinarith

/-- `p(ξ(s)) = P̃·s/c²`. -/
theorem pP_xiOf {c s : ℝ} (hc : c ≠ 0) : pP (xiOf c s) = pS c s * s / c ^ 2 := by
  unfold pP pS xiOf; field_simp; ring

/-- **The flux equation in `s`.** -/
theorem hasDerivAt_layer_psi {ψ u : ℝ → ℝ} {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hψ : HasDerivAt ψ (u (xiOf c s) / pP (xiOf c s)) (xiOf c s)) :
    HasDerivAt (fun t => ψ (xiOf c t)) (u (xiOf c s) / pS c s) s := by
  refine (hψ.comp s (hasDerivAt_xiOf c s hc.ne')).congr_deriv ?_
  have := pS_pos hc hs
  rw [pP_xiOf hc.ne']
  field_simp

/-- **The force equation in `s`.** -/
theorem hasDerivAt_layer_u {ψ u : ℝ → ℝ} {c χ s : ℝ} (hc : 0 < c)
    (hu : HasDerivAt u (-(qP c χ (xiOf c s) * ψ (xiOf c s))) (xiOf c s)) :
    HasDerivAt (fun t => u (xiOf c t)) (-(qS c χ s * ψ (xiOf c s))) s := by
  refine (hu.comp s (hasDerivAt_xiOf c s hc.ne')).congr_deriv ?_
  unfold qS; ring

/-- **`P̃Q̃ = a²`** on the layer. -/
theorem aP_xiOf_sq {c χ s : ℝ} (hc : 0 < c) (hs : 0 < s) (hχc : χ < c ^ 2) :
    aP c χ (xiOf c s) ^ 2 = pS c s * qS c χ s := by
  rw [aP_sq (one_lt_xiOf hc hs) (by positivity) hχc, pP_xiOf hc.ne']
  unfold qS; ring

/-- **Olver's phase condition in `s`**: `P̃f_s² = Q̃`. -/
theorem pS_mul_freqS_sq {c χ s : ℝ} (hc : 0 < c) (hs : 0 < s) (hχc : χ < c ^ 2) :
    pS c s * freqS c χ s ^ 2 = qS c χ s := by
  have hξ := one_lt_xiOf hc hs
  have hq : 0 < qP c χ (xiOf c s) := qP_pos hξ (by positivity) hχc
  have hξ1 : 0 < xiOf c s + 1 := by linarith
  unfold freqS
  rw [div_pow, Real.sq_sqrt (div_nonneg (by positivity) hξ1.le)]
  unfold pS qS
  field_simp

/-- **`P̃f_s = a`** on the layer. -/
theorem pS_mul_freqS {c χ s : ℝ} (hc : 0 < c) (hs : 0 < s) (hχc : χ < c ^ 2) :
    pS c s * freqS c χ s = aP c χ (xiOf c s) := by
  have hp := pS_pos hc hs
  have hf : 0 ≤ freqS c χ s := div_nonneg (Real.sqrt_nonneg _) hc.le
  have ha : 0 ≤ aP c χ (xiOf c s) := Real.sqrt_nonneg _
  rw [← Real.sqrt_sq (mul_nonneg hp.le hf), ← Real.sqrt_sq ha, aP_xiOf_sq hc hs hχc,
    ← pS_mul_freqS_sq hc hs hχc]
  congr 1; ring

end Cvs.Prolate.LiouvilleGreen.LayerProlateSystem
