import Mathlib
import Cvs.Upstream.JensenProbabilityDensity
import Cvs.WeilForm.Mollify.MollifiedL2
import Cvs.WeilForm.Mollify.MollifiedSliceL2
import Cvs.WeilForm.Mollify.MollifyL2Contraction
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy

/-!
# Mollification moves a function by at most its translation modulus

    ∫ ((f⋆ρ)(s) − f s)² ds  ≤  ε      whenever  ∫ (f (s−t) − f s)² ds ≤ ε  on `supp ρ`

Jensen against the density puts the whole displacement inside a translation of `f`, which is
the one thing that is known to be small.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Function
open scoped ENNReal

namespace Cvs.WeilForm.Mollify.MollifyTranslationModulus

variable {f ρ : ℝ → ℝ}

/-- The displacement kernel is measurable on the product. -/
theorem measurable_kernel_sub (hfm : Measurable f) (hρm : Measurable ρ) :
    Measurable (uncurry fun s t : ℝ => ENNReal.ofReal ((f (s - t) - f s) ^ 2 * ρ t)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  exact (((hfm.comp (measurable_fst.sub measurable_snd)).sub
    (hfm.comp measurable_fst)).pow_const 2).mul (hρm.comp measurable_snd)

/-- **The mollification error is the density's average of the translation errors.** -/
theorem lintegral_conv_sub_le (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1) :
    (∫⁻ s : ℝ, ENNReal.ofReal ((Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s - f s) ^ 2))
      ≤ ∫⁻ t : ℝ, ENNReal.ofReal (ρ t * ∫ s : ℝ, (f (s - t) - f s) ^ 2) := by
  have hsqrt := Cvs.Upstream.JensenProbabilityDensity.memLp_sqrt hρnn hρi
  -- the mollification error as one integral in the displacement
  have hdiff : ∀ s : ℝ, Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s - f s
      = ∫ t : ℝ, (f (s - t) - f s) * ρ t := by
    intro s
    rw [Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv]
    have hfs : (∫ t : ℝ, f s * ρ t) = f s := by
      rw [integral_const_mul, hρ1, mul_one]
    calc (∫ t : ℝ, f (s - t) * ρ t) - f s
        = (∫ t : ℝ, f (s - t) * ρ t) - ∫ t : ℝ, f s * ρ t := by rw [hfs]
      _ = ∫ t : ℝ, (f (s - t) * ρ t - f s * ρ t) :=
          (integral_sub (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.integrable_slice hf hρc hρs s)
            (hρi.const_mul (f s))).symm
      _ = ∫ t : ℝ, (f (s - t) - f s) * ρ t :=
          integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  -- Jensen, in each fibre
  have hjensen : ∀ s : ℝ, ENNReal.ofReal ((Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s - f s) ^ 2)
      ≤ ∫⁻ t : ℝ, ENNReal.ofReal ((f (s - t) - f s) ^ 2 * ρ t) := by
    intro s
    have hk : MemLp (fun t : ℝ => (f (s - t) - f s) * Real.sqrt (ρ t)) 2
        (volume : Measure ℝ) := by
      have h1 := Cvs.WeilForm.Mollify.MollifiedSliceL2.memLp_slice hf hρc hρs hρnn s
      have h2 := hsqrt.const_mul (f s)
      refine (h1.sub h2).ae_eq (Filter.Eventually.of_forall fun t => ?_)
      simp only [Pi.sub_apply]
      ring
    have hj := Cvs.Upstream.JensenProbabilityDensity.sq_integral_weighted_le hρnn hρi hρ1 hk
    have hslice : Integrable (fun t : ℝ => (f (s - t) - f s) ^ 2 * ρ t)
        (volume : Measure ℝ) := by
      have h1 := Cvs.WeilForm.Mollify.MollifyL2Contraction.integrable_slice_sq hf hρc hρs hρnn s
      have h2 := (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.integrable_slice hf hρc hρs s).const_mul (-(2 * f s))
      have h3 := hρi.const_mul (f s ^ 2)
      refine ((h1.add h2).add h3).congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [Pi.add_apply]
      ring
    rw [hdiff s, ← ofReal_integral_eq_lintegral_ofReal hslice
      (Filter.Eventually.of_forall fun t => mul_nonneg (sq_nonneg _) (hρnn t))]
    exact ENNReal.ofReal_le_ofReal hj
  refine le_trans (lintegral_mono hjensen) ?_
  rw [lintegral_lintegral_swap (measurable_kernel_sub hfm hρm).aemeasurable]
  refine lintegral_mono fun t => ?_
  have hmem : MemLp (fun s : ℝ => f (s - t) - f s) 2 (volume : Measure ℝ) := by
    have hrefl : MemLp (fun s : ℝ => f (s - t)) 2 (volume : Measure ℝ) := by
      have h0 := hf.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) (-t))
      refine h0.ae_eq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply]
      congr 1
    exact hrefl.sub hf
  have hfac : ∀ s : ℝ, ENNReal.ofReal ((f (s - t) - f s) ^ 2 * ρ t)
      = ENNReal.ofReal (ρ t) * ENNReal.ofReal ((f (s - t) - f s) ^ 2) := by
    intro s
    rw [← ENNReal.ofReal_mul (hρnn t)]
    congr 1
    ring
  simp only [hfac]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
      (Filter.Eventually.of_forall fun s => sq_nonneg _),
    ← ENNReal.ofReal_mul (hρnn t)]

/-- **The mollification error is at most the translation modulus over the kernel's support.** -/
theorem integral_conv_sub_le {δ ε : ℝ} (hε : 0 ≤ ε)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1)
    (hsupp : ∀ t : ℝ, ρ t ≠ 0 → |t| ≤ δ)
    (hsmall : ∀ t : ℝ, |t| ≤ δ → (∫ s : ℝ, (f (s - t) - f s) ^ 2) ≤ ε) :
    (∫ s : ℝ, (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s - f s) ^ 2) ≤ ε := by
  have hcm := Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv hf hfm hρc hρs hρm hρi hρnn hρ1
  have hL : Integrable (fun s : ℝ => (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s - f s) ^ 2)
      (volume : Measure ℝ) := (hcm.sub hf).integrable_sq
  have hchain := lintegral_conv_sub_le hf hfm hρc hρs hρm hρi hρnn hρ1
  have hstep : (∫⁻ t : ℝ, ENNReal.ofReal (ρ t * ∫ s : ℝ, (f (s - t) - f s) ^ 2))
      ≤ ∫⁻ t : ℝ, ENNReal.ofReal (ρ t * ε) := by
    refine lintegral_mono fun t => ?_
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases ht : ρ t = 0
    · rw [ht]; simp
    · exact mul_le_mul_of_nonneg_left (hsmall t (hsupp t ht)) (hρnn t)
  have hval : (∫⁻ t : ℝ, ENNReal.ofReal (ρ t * ε)) = ENNReal.ofReal ε := by
    have hfac : ∀ t : ℝ, ENNReal.ofReal (ρ t * ε)
        = ENNReal.ofReal ε * ENNReal.ofReal (ρ t) := by
      intro t
      rw [← ENNReal.ofReal_mul hε]
      congr 1
      ring
    simp only [hfac]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hρi (Filter.Eventually.of_forall hρnn), hρ1]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal hL
    (Filter.Eventually.of_forall fun s => sq_nonneg _)] at hchain
  have hfin := le_trans hchain (le_trans hstep (le_of_eq hval))
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hfin

end Cvs.WeilForm.Mollify.MollifyTranslationModulus
