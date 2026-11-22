import Mathlib
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.PhiThetaDifferentialOperator
import Cvs.Zeta.ZetaRealSegment

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The theta sum is the even kernel

On the imaginary axis the theta terms are real, so the sum over the positive integers is half the
even kernel's departure from its limit. Rescaling the variable by `e^{2u}` and the value by `e^{u/2}`
turns that into the sum this development uses.
-/

noncomputable section

open Real Complex Filter Topology

namespace Cvs.Xi.ThetaSumEvenKernel

open Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums

/-- **The exponent folds to a real one**, because `I * I = -1`. -/
theorem term_eq (n : ℕ) (t : ℝ) :
    Complex.exp ((Real.pi : ℂ) * I * (((n : ℂ) + 1)) ^ 2 * (I * (t : ℂ)))
      = ((Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * t)) : ℝ) : ℂ) := by
  have hz : (Real.pi : ℂ) * I * (((n : ℂ) + 1)) ^ 2 * (I * (t : ℂ))
      = ((-(Real.pi * ((n : ℝ) + 1) ^ 2 * t) : ℝ) : ℂ) := by
    have h : (Real.pi : ℂ) * I * (((n : ℂ) + 1)) ^ 2 * (I * (t : ℂ))
        = (Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (t : ℂ) * (I * I) := by ring
    rw [h, Complex.I_mul_I]
    push_cast
    ring
  rw [hz]
  exact (Complex.ofReal_exp _).symm

/-- **The even kernel's departure from one is twice the sum over the positive integers.** -/
theorem hasSum_kernel {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * t)))
      ((HurwitzZeta.evenKernel 0 t - 1) / 2) := by
  have him : 0 < (I * (t : ℂ)).im := by simpa using ht
  have h := hasSum_nat_jacobiTheta him
  rw [← Cvs.Zeta.evenKernel_zero_eq_jacobiTheta t] at h
  simp_rw [term_eq] at h
  rw [show ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1
      = ((HurwitzZeta.evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring] at h
  rw [show (((HurwitzZeta.evenKernel 0 t - 1 : ℝ) : ℂ)) / 2
      = (((HurwitzZeta.evenKernel 0 t - 1) / 2 : ℝ) : ℂ) by push_cast; ring] at h
  exact_mod_cast h

theorem thetaTerm_succ (n : ℕ) (u : ℝ) :
    thetaTerm (n + 1) u
      = Real.exp (u / 2) * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))) := by
  unfold thetaTerm
  push_cast
  ring

/-- **The theta sum, in terms of the even kernel.** -/
theorem two_mul_thetaSum_eq (u : ℝ) :
    2 * thetaSum u
      = Real.exp (u / 2) * (HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) - 1) := by
  have ht : (0 : ℝ) < Real.exp (2 * u) := Real.exp_pos _
  have h := hasSum_kernel ht
  have hfun : (fun n : ℕ => thetaTerm (n + 1) u)
      = fun n : ℕ => Real.exp (u / 2)
        * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))) :=
    funext fun n => thetaTerm_succ n u
  have hts : thetaSum u
      = Real.exp (u / 2) * ((HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) - 1) / 2) := by
    unfold thetaSum
    rw [hfun, tsum_mul_left, h.tsum_eq]
  rw [hts]
  ring

end Cvs.Xi.ThetaSumEvenKernel
