import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.Bounds
import Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset
import Cvs.Prolate.Envelope.ProlateWeightToEdge
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Two prolates at one bandwidth: the Wronskian integral

If `ψ_a, ψ_b` solve the radial equation at the same `c` with `χ_a`, `χ_b`, both regular at `1` (`u(1) = 0`), then
`(χ_a − χ_b)∫₁ᵗ ψ_aψ_b = u_a(t)ψ_b(t) − ψ_a(t)u_b(t)`; with the flux–value envelope,
`|χ_a − χ_b| |∫₁ᵗ ψ_aψ_b| ≤ 2G√(ew(t)/(t² − 1))`.
-/

namespace Cvs.Prolate.ProlateWronskianIntegral

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Envelope.ProlateWeightToEdge

variable {c χa χb t : ℝ} {ψa ua ψb ub : ℝ → ℝ}

/-- **The Wronskian integral**: `(χ_a − χ_b)∫₁ᵗ ψ_aψ_b = u_a(t)ψ_b(t) − ψ_a(t)u_b(t)`. -/
theorem wronskian_integral (ht : 1 ≤ t)
    (hψa : ∀ ξ ∈ Ioo 1 t, HasDerivAt ψa (ua ξ / pP ξ) ξ) (hua : ∀ ξ ∈ Ioo 1 t, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioo 1 t, HasDerivAt ψb (ub ξ / pP ξ) ξ) (hub : ∀ ξ ∈ Ioo 1 t, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hca : ContinuousOn ψa (Icc 1 t)) (hcua : ContinuousOn ua (Icc 1 t))
    (hcb : ContinuousOn ψb (Icc 1 t)) (hcub : ContinuousOn ub (Icc 1 t)) (hua1 : ua 1 = 0) (hub1 : ub 1 = 0) :
    (χa - χb) * ∫ ξ in (1 : ℝ)..t, ψa ξ * ψb ξ = ua t * ψb t - ψa t * ub t := by
  have hderiv : ∀ ξ ∈ Ioo 1 t, HasDerivAt (fun ξ => ua ξ * ψb ξ - ψa ξ * ub ξ)
      ((χa - χb) * (ψa ξ * ψb ξ)) ξ := by
    intro ξ hξ
    have hp : pP ξ ≠ 0 := (pP_pos hξ.1).ne'
    refine ((hua ξ hξ).mul (hψb ξ hξ)).sub ((hψa ξ hξ).mul (hub ξ hξ)) |>.congr_deriv ?_
    unfold qP; field_simp; ring
  have hcont : ContinuousOn (fun ξ => ua ξ * ψb ξ - ψa ξ * ub ξ) (Icc 1 t) :=
    (hcua.mul hcb).sub (hca.mul hcub)
  have hint : IntervalIntegrable (fun ξ => (χa - χb) * (ψa ξ * ψb ξ)) MeasureTheory.volume 1 t :=
    (continuousOn_const.mul (hca.mul hcb)).intervalIntegrable_of_Icc ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  rw [intervalIntegral.integral_const_mul] at h
  rw [h, hua1, hub1]; ring

/-- **The Wronskian integral, bounded**: `|χ_a − χ_b| |∫₁ᵗ ψ_aψ_b| ≤ 2G√(ew(t)/(t² − 1))` for `t > 1`. -/
theorem abs_wronskian_integral_le {G : ℝ} (hc : 0 < c) (hχa0 : 0 ≤ χa) (hχb0 : 0 ≤ χb) (hχa : χa < c ^ 2)
    (hχb : χb < c ^ 2) (ht : 1 < t)
    (hψa : ∀ ξ ∈ Ioo 1 t, HasDerivAt ψa (ua ξ / pP ξ) ξ) (hua : ∀ ξ ∈ Ioo 1 t, HasDerivAt ua (-(qP c χa ξ * ψa ξ)) ξ)
    (hψb : ∀ ξ ∈ Ioo 1 t, HasDerivAt ψb (ub ξ / pP ξ) ξ) (hub : ∀ ξ ∈ Ioo 1 t, HasDerivAt ub (-(qP c χb ξ * ψb ξ)) ξ)
    (hca : ContinuousOn ψa (Icc 1 t)) (hcua : ContinuousOn ua (Icc 1 t))
    (hcb : ContinuousOn ψb (Icc 1 t)) (hcub : ContinuousOn ub (Icc 1 t)) (hua1 : ua 1 = 0) (hub1 : ub 1 = 0)
    (hGa : energy (aP c χa) ψa ua t ≤ G) (hGb : energy (aP c χb) ψb ub t ≤ G) :
    |χa - χb| * |∫ ξ in (1 : ℝ)..t, ψa ξ * ψb ξ| ≤ 2 * (G * √(ew t / (t ^ 2 - 1))) := by
  rw [← abs_mul, wronskian_integral ht.le hψa hua hψb hub hca hcua hcb hcub hua1 hub1]
  have e1 := Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset.flux_val_le (ψa := ψa) (ψb := ψb) hc hχa0 hχa hχb ht ht hGa hGb
  have e2 := Cvs.Prolate.Envelope.EdgeEnvelopeSigmaFreeOffset.flux_val_le (ψa := ψb) (ψb := ψa) hc hχb0 hχb hχa ht ht hGb hGa
  calc |ua t * ψb t - ψa t * ub t| ≤ |ua t * ψb t| + |ψa t * ub t| := abs_sub _ _
    _ = |ua t * ψb t| + |ub t * ψa t| := by rw [mul_comm (ψa t)]
    _ ≤ 2 * (G * √(ew t / (t ^ 2 - 1))) := by linarith

end Cvs.Prolate.ProlateWronskianIntegral
