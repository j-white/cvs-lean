import Mathlib
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Xi.PhiCosineTransform
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.XiCosineTransformPhi

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The value at the origin

At the origin the cosine is one, so the transform of `Φ` is the plain integral of `Φ`. The kernel
identity carries integrability across from the theta sums, and `Φ` is positive on the half line, so
the integral is positive and `Ξ` is positive at the origin.
-/

noncomputable section

open Real Set MeasureTheory Complex

namespace Cvs.Xi.XiValueAtOrigin

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiKernelIdentitySums

/-- **`Φ` is integrable on the half line**, because the theta sums that compose it are. -/
theorem integrableOn_riemannPhi : IntegrableOn riemannPhi (Ioi (0 : ℝ)) := by
  have h2 := (Cvs.Xi.PhiCosineTransform.integrableOn_thetaSum2_cos 0).const_mul (1 / 2 : ℝ)
  have h1 := (Cvs.Xi.PhiCosineTransform.integrableOn_thetaSum_cos 0).const_mul (1 / 8 : ℝ)
  refine MeasureTheory.IntegrableOn.congr_fun (h2.sub h1) (fun u _ => ?_) measurableSet_Ioi
  have h := eight_mul_riemannPhi_eq u
  simp only [Pi.sub_apply, zero_mul, Real.cos_zero, mul_one]
  linarith

/-- The support of `Φ` meets the half line in the whole half line. -/
theorem support_inter_Ioi : Function.support riemannPhi ∩ Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext u
  simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
  exact ⟨fun h => h.2, fun h => ⟨ne_of_gt (riemannPhi_pos h.le), h⟩⟩

/-- **The integral of `Φ` over the half line is positive.** -/
theorem integral_riemannPhi_pos : 0 < ∫ u in Ioi (0 : ℝ), riemannPhi u := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] riemannPhi := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (riemannPhi_pos (le_of_lt hu)).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn integrableOn_riemannPhi, support_inter_Ioi]
  simp [Real.volume_Ioi]

/-- **At the origin the transform is four times the integral of `Φ`.** -/
theorem Xi_zero_eq :
    Cvs.Limit.ZeroFreeApproximantsRH.Xi 0
      = ((4 * ∫ u in Ioi (0 : ℝ), riemannPhi u : ℝ) : ℂ) := by
  have h := Cvs.Xi.XiCosineTransformPhi.Xi_eq_four_mul_integral_riemannPhi 0
  simp only [Complex.ofReal_zero, zero_mul, Real.cos_zero, mul_one] at h
  exact h

/-- **`Ξ` is positive at the origin.** -/
theorem Xi_zero_re_pos : 0 < (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0).re := by
  rw [Xi_zero_eq, Complex.ofReal_re]
  have := integral_riemannPhi_pos
  linarith

end Cvs.Xi.XiValueAtOrigin
