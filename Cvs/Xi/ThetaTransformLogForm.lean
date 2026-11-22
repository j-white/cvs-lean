import Mathlib
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.ThetaSumEvenKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The transform on the half line, as an integral from one

Doubling the variable and then reading it as a logarithm carries the half line onto `[1, ∞)`, where
the theta sum is the even kernel's departure from its limit. The transform of the theta sum is
therefore an integral of that kernel against a power and a cosine of the logarithm.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.Xi.ThetaTransformLogForm

open Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumEvenKernel

/-- **The theta sum at a halved logarithm**, in terms of the even kernel. -/
theorem two_mul_thetaSum_log_half {x : ℝ} (hx : 0 < x) :
    2 * thetaSum (Real.log x / 2)
      = Real.exp (Real.log x / 4) * (HurwitzZeta.evenKernel 0 x - 1) := by
  have h := two_mul_thetaSum_eq (Real.log x / 2)
  rw [show 2 * (Real.log x / 2) = Real.log x by ring, Real.exp_log hx] at h
  rw [h]
  congr 2
  ring

/-- **Doubling the variable.** -/
theorem integral_scale (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), thetaSum u * cos (t * u)
      = (1 / 2) * ∫ v in Ioi (0 : ℝ), thetaSum (v / 2) * cos (t * (v / 2)) := by
  have h := integral_comp_mul_left_Ioi
    (fun v : ℝ => thetaSum (v / 2) * cos (t * (v / 2))) 0 (b := 2) two_pos
  rw [mul_zero, smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) = 2⁻¹ from by norm_num, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  norm_num

/-- **Reading the variable as a logarithm.** -/
theorem integral_log_form (t : ℝ) :
    ∫ v in Ioi (0 : ℝ), thetaSum (v / 2) * cos (t * (v / 2))
      = ∫ x in Ioi (1 : ℝ),
          x⁻¹ * (thetaSum (Real.log x / 2) * cos (t * (Real.log x / 2))) := by
  have h := integral_comp_log_Ioi
    (fun v : ℝ => thetaSum (v / 2) * cos (t * (v / 2))) (a := 1) one_pos
  rw [Real.log_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [smul_eq_mul]

/-- **The transform of the theta sum, as an integral from one.** -/
theorem integral_thetaSum_cos_eq (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), thetaSum u * cos (t * u)
      = (1 / 4) * ∫ x in Ioi (1 : ℝ),
          (x⁻¹ * Real.exp (Real.log x / 4)) * (HurwitzZeta.evenKernel 0 x - 1)
            * cos (t / 2 * Real.log x) := by
  rw [integral_scale t, integral_log_form t]
  rw [show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hk := two_mul_thetaSum_log_half hx0
  have hts : thetaSum (Real.log x / 2)
      = Real.exp (Real.log x / 4) * (HurwitzZeta.evenKernel 0 x - 1) / 2 := by
    linarith
  rw [hts, show t * (Real.log x / 2) = t / 2 * Real.log x by ring]
  ring

end Cvs.Xi.ThetaTransformLogForm
