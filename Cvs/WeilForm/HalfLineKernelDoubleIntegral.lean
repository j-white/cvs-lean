import Mathlib
import Cvs.WeilForm.WeilFormReflection
import Cvs.Zeta.WeilPositivityStatement

/-!
# The half-line self-convolution integral is the kernel double integral

    `2 ∫_{v>0} e^{−b v} g(v) dv = ∫ s, f s · ∫ u, f u · e^{−b|s−u|} du`   (`g = f ⋆ f̃`)

for continuous, compactly supported `f`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.Zeta.Explicit.Weil
open scoped Pointwise

namespace Cvs.WeilForm.HalfLineKernelDoubleIntegral

variable {f : ℝ → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) {b : ℝ}

/-- The joint integrand `(s,t) ↦ f s · f (s+t) · e^{−b|t|}` is continuous with compact support. -/
theorem joint_integrable (hf : Continuous f) (hcf : HasCompactSupport f) (b : ℝ) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f (p.1 + p.2) * Real.exp (-(b * |p.2|))) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((hf.comp continuous_fst).mul (hf.comp (continuous_fst.add continuous_snd))).mul
      (by fun_prop)
  · -- support lies in (supp f) × (supp f − supp f), a compact set
    apply HasCompactSupport.intro (K := tsupport f ×ˢ (tsupport f + -tsupport f))
    · exact (hcf.isCompact.prod (hcf.isCompact.add hcf.isCompact.neg))
    · rintro ⟨s, t⟩ hst
      simp only [mem_prod, not_and_or] at hst
      have hsupp : ∀ x, f x ≠ 0 → x ∈ tsupport f := fun x hx => subset_tsupport f hx
      by_cases h1 : f s = 0
      · simp [h1]
      by_cases h2 : f (s + t) = 0
      · simp [h2]
      exfalso
      rcases hst with h | h
      · exact h (hsupp s h1)
      · exact h (Set.mem_add.mpr ⟨s + t, hsupp _ h2, -s,
          Set.mem_neg.mpr (by simpa using hsupp s h1), by ring⟩)

/-- **The kernel double integral is the half-line self-convolution integral**, given the joint
integrability of `(s,t) ↦ f s · f (s+t) · e^{−b|t|}`. -/
theorem kernel_eq_half_line_of_joint {f : ℝ → ℝ} {b : ℝ}
    (hjoint : Integrable (fun p : ℝ × ℝ => f p.1 * f (p.1 + p.2) * Real.exp (-(b * |p.2|)))) :
    (∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      = 2 * ∫ v in Ioi (0:ℝ), Real.exp (-(b * v)) * selfConvolution f v := by
  -- pull `f s` in and translate `u = s + t`
  have step1 : (∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      = ∫ s, ∫ t, f s * f (s + t) * Real.exp (-(b * |t|)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    rw [← integral_const_mul (f s) (fun u => f u * Real.exp (-(b * |s - u|)))]
    rw [← integral_add_left_eq_self (fun u => f s * (f u * Real.exp (-(b * |s - u|)))) s]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [show s - (s + t) = -t by ring, abs_neg]
    ring
  -- Fubini
  have hswap : (∫ s, ∫ t, f s * f (s + t) * Real.exp (-(b * |t|)))
      = ∫ t, ∫ s, f s * f (s + t) * Real.exp (-(b * |t|)) :=
    integral_integral_swap hjoint
  have step2 : (∫ s, ∫ t, f s * f (s + t) * Real.exp (-(b * |t|)))
      = ∫ t, Real.exp (-(b * |t|)) * selfConvolution f t := by
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    unfold selfConvolution
    rw [integral_mul_const (Real.exp (-(b * |t|))) (fun s => f s * f (s + t))]
    ring
  -- the integrand is even in `t`
  have heven : (∫ t, Real.exp (-(b * |t|)) * selfConvolution f t)
      = 2 * ∫ t in Ioi (0:ℝ), Real.exp (-(b * t)) * selfConvolution f t := by
    have hint : Integrable (fun t => Real.exp (-(b * |t|)) * selfConvolution f t) := by
      have := hjoint.integral_prod_right
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only []
      unfold selfConvolution
      rw [integral_mul_const (Real.exp (-(b * |t|))) (fun s => f s * f (s + t)), mul_comm]
    have hev : ∀ t, Real.exp (-(b * |(-t)|)) * selfConvolution f (-t)
        = Real.exp (-(b * |t|)) * selfConvolution f t := by
      intro t; rw [abs_neg, Cvs.WeilForm.WeilFormReflection.selfConvolution_neg]
    rw [← integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hint]
    have hIic : (∫ t in (Ioi (0:ℝ))ᶜ, Real.exp (-(b * |t|)) * selfConvolution f t)
        = ∫ t in Ioi (0:ℝ), Real.exp (-(b * t)) * selfConvolution f t := by
      rw [show (Ioi (0:ℝ))ᶜ = Iic 0 from by simp]
      have hmp : MeasurePreserving (fun t : ℝ => -t) (volume.restrict (Iic 0))
          (volume.restrict (Ici 0)) := by
        have he : (Iic (0:ℝ)) = (fun t => -t) ⁻¹' (Ici 0) := by ext t; simp
        rw [he]
        exact (Measure.measurePreserving_neg volume).restrict_preimage measurableSet_Ici
      have hemb : MeasurableEmbedding (fun t : ℝ => -t) := (MeasurableEquiv.neg ℝ).measurableEmbedding
      have h := hmp.integral_comp hemb
        (fun t => Real.exp (-(b * |(-t)|)) * selfConvolution f (-t))
      simp only [neg_neg] at h
      rw [h, integral_Ici_eq_integral_Ioi]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [hev t, abs_of_pos ht]
    have hIoi : (∫ t in Ioi (0:ℝ), Real.exp (-(b * |t|)) * selfConvolution f t)
        = ∫ t in Ioi (0:ℝ), Real.exp (-(b * t)) * selfConvolution f t := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [abs_of_pos ht]
    rw [hIoi, hIic]; ring
  rw [step1, step2, heven]

/-- **The kernel double integral is the half-line self-convolution integral.** -/
theorem kernel_eq_half_line (hf : Continuous f) (hcf : HasCompactSupport f) (b : ℝ) (hb : 0 < b) :
    (∫ s, f s * ∫ u, f u * Real.exp (-(b * |s - u|)))
      = 2 * ∫ v in Ioi (0:ℝ), Real.exp (-(b * v)) * selfConvolution f v :=
  kernel_eq_half_line_of_joint (joint_integrable hf hcf b)

end Cvs.WeilForm.HalfLineKernelDoubleIntegral
