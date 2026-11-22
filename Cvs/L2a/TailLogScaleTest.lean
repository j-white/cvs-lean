import Mathlib
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The log-scale test function of a tail on `[1, ∞)`

For `F` vanishing on `(−∞, 1]` and `f(s) = F(eˢ) e^{s/2}`: `∫ f² = ∫_{θ>1} F²`, `∫ f e^{s/2} = ∫_{θ>1} F`,
`∫ f e^{−s/2} = ∫_{θ>1} F/θ`, and `(f ⋆ f)(±log k) = √k ∫_{θ>1} F(θ) F(kθ)`; its spectral density is `((∫F y_t)² + (∫F ỹ_t)²)/(2π)`
with `MellinKernelSturmLiouville`'s Mellin kernels.
-/

namespace Cvs.L2a.TailLogScaleTest

open Real Set MeasureTheory
open scoped FourierTransform

/-- The log-scale function `f(s) = F(eˢ) e^{s/2}`. -/
noncomputable def logScale (F : ℝ → ℝ) (s : ℝ) : ℝ := F (exp s) * exp (s / 2)

/-- **The substitution `θ = eˢ`** for integrands vanishing at `θ ≤ 1`. -/
theorem integral_exp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (hg : ∀ θ ≤ 1, g θ = 0) :
    ∫ s, exp s • g (exp s) = ∫ θ in Ioi 1, g θ := by
  have h0 : ∫ s, exp s • g (exp s) = ∫ s in Ioi 0, exp s • g (exp s) := by
    symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    simp only [mem_Ioi, not_lt] at hs
    rw [hg _ (exp_le_one_iff.mpr hs), smul_zero]
  rw [h0, integral_comp_exp_Ioi g 0, exp_zero]

theorem exp_half_sq (s : ℝ) : exp (s / 2) * exp (s / 2) = exp s := by
  rw [← exp_add]; ring_nf

/-- `∫ f² = ∫_{θ>1} F²`. -/
theorem integral_sq (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) :
    ∫ s, logScale F s ^ 2 = ∫ θ in Ioi 1, F θ ^ 2 := by
  have e : (fun s => logScale F s ^ 2) = fun s => exp s • (fun θ => F θ ^ 2) (exp s) := by
    funext s; unfold logScale; rw [smul_eq_mul, ← exp_half_sq]; ring
  rw [e]; exact integral_exp_smul (fun θ => F θ ^ 2) (fun θ h => by simp [hF θ h])

/-- `∫ f e^{s/2} = ∫_{θ>1} F`. -/
theorem integral_mul_exp (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) :
    ∫ s, logScale F s * exp (s / 2) = ∫ θ in Ioi 1, F θ := by
  have e : (fun s => logScale F s * exp (s / 2)) = fun s => exp s • F (exp s) := by
    funext s; unfold logScale; rw [smul_eq_mul, ← exp_half_sq]; ring
  rw [e, integral_exp_smul _ hF]

/-- `∫ f e^{−s/2} = ∫_{θ>1} F/θ`. -/
theorem integral_mul_exp_neg (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) :
    ∫ s, logScale F s * exp (-(s / 2)) = ∫ θ in Ioi 1, F θ / θ := by
  have e : (fun s => logScale F s * exp (-(s / 2))) = fun s => exp s • (fun θ => F θ / θ) (exp s) := by
    funext s; unfold logScale
    rw [smul_eq_mul, mul_assoc, ← exp_add, show s / 2 + -(s / 2) = 0 by ring, exp_zero]
    field_simp
  rw [e]; exact integral_exp_smul (fun θ => F θ / θ) (fun θ h => by simp [hF θ h])

/-- `(f ⋆ f)(log k) = √k ∫_{θ>1} F(θ) F(kθ)`. -/
theorem selfConvolution_log (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) {k : ℝ} (hk : 0 < k) :
    Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) (log k) = √k * ∫ θ in Ioi 1, F θ * F (k * θ) := by
  unfold Cvs.Zeta.Explicit.Weil.selfConvolution
  have e : (fun x => logScale F x * logScale F (x + log k))
      = fun x => exp x • (fun θ => √k * (F θ * F (k * θ))) (exp x) := by
    funext x; unfold logScale
    rw [smul_eq_mul, exp_add, exp_log hk, mul_comm (exp x) k]
    have h1 : exp ((x + log k) / 2) = exp (x / 2) * √k := by
      rw [show (x + log k) / 2 = x / 2 + log k / 2 by ring, exp_add, sqrt_eq_rpow, rpow_def_of_pos hk]
      ring_nf
    rw [h1, ← exp_half_sq x]; ring
  rw [e, ← integral_const_mul]
  exact integral_exp_smul (fun θ => √k * (F θ * F (k * θ))) (fun θ h => by simp [hF θ h])

/-- `(f ⋆ f)(−log k) = (f ⋆ f)(log k)`. -/
theorem selfConvolution_neg_log (F : ℝ → ℝ) (k : ℝ) :
    Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) (-log k)
      = Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F) (log k) := by
  unfold Cvs.Zeta.Explicit.Weil.selfConvolution
  rw [← integral_add_right_eq_self _ (log k)]
  congr 1; funext x
  rw [show x + log k + -log k = x by ring, mul_comm]

/-- **The Fourier transform is the Mellin transform** on the critical line. -/
theorem fourier_eq (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) (t : ℝ)
    (h1 : IntegrableOn (fun θ => F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ) (Ioi 1))
    (h2 : IntegrableOn (fun θ => F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ) (Ioi 1)) :
    𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (logScale F)) (t / (2 * π))
      = ((∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ : ℝ) : ℂ)
        - Complex.I * ((∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set G : ℝ → ℂ := fun θ => ((F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ : ℝ) : ℂ)
    - Complex.I * ((F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ : ℝ) : ℂ) with hG
  have e : (fun v : ℝ => Complex.exp (↑(-2 * π * v * (t / (2 * π))) * Complex.I)
      • Cvs.WeilForm.SelfConvolutionTransform.cf (logScale F) v) = fun v => exp v • G (exp v) := by
    funext v
    unfold Cvs.WeilForm.SelfConvolutionTransform.cf logScale
    simp only [hG, Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky, Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys, log_exp, smul_eq_mul, Complex.real_smul]
    have hsq : √(exp v) = exp (v / 2) := by
      rw [sqrt_eq_iff_mul_self_eq (exp_pos _).le (exp_pos _).le, exp_half_sq]
    rw [hsq]
    have hpv : (0 : ℝ) < exp (v / 2) := exp_pos _
    have ev : exp v = exp (v / 2) * exp (v / 2) := (exp_half_sq v).symm
    have harg : (↑(-2 * π * v * (t / (2 * π))) : ℂ) * Complex.I = ↑(-(t * v)) * Complex.I := by
      congr 1; push_cast; field_simp
    rw [harg, show (↑(-(t * v)) : ℂ) * Complex.I = ((-(t * v) : ℝ) : ℂ) * Complex.I from rfl,
      Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_neg, sin_neg]
    rw [ev]; push_cast
    field_simp
    ring_nf
  rw [e, integral_exp_smul G (fun θ h => by simp [hG, hF θ h])]
  rw [hG, integral_sub, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  · exact h1.ofReal
  · exact (h2.ofReal).const_mul _

/-- **The spectral density of a tail**: `((∫ F y_t)² + (∫ F ỹ_t)²)/(2π)`. -/
theorem specDensity_eq (F : ℝ → ℝ) (hF : ∀ θ ≤ 1, F θ = 0) (t : ℝ)
    (h1 : IntegrableOn (fun θ => F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ) (Ioi 1))
    (h2 : IntegrableOn (fun θ => F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ) (Ioi 1)) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale F) t
      = ((∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ) ^ 2
          + (∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ) ^ 2) / (2 * π) := by
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  rw [fourier_eq F hF t h1 h2]
  congr 1
  set a := ∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ
  set b := ∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

end Cvs.L2a.TailLogScaleTest
