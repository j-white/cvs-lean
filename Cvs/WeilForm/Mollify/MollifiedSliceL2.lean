import Mathlib

/-!
# The mollified slice is square integrable

    `h ∈ L²`, `ρ ≥ 0` continuous of compact support  ⟹  `t ↦ h(s−t)·√(ρ t)` is `L²`

the hypothesis `Cvs.Upstream.JensenProbabilityDensity` needs at each point, so that Jensen applies along the convolution.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real

namespace Cvs.WeilForm.Mollify.MollifiedSliceL2

variable {h ρ : ℝ → ℝ}

/-- The reflected translate of an `L²` function is `L²`. -/
theorem memLp_reflect_translate (hh : MemLp h 2 (volume : Measure ℝ)) (s : ℝ) :
    MemLp (fun t : ℝ => h (s - t)) 2 (volume : Measure ℝ) := by
  have h1 : MemLp (fun t : ℝ => h (-t)) 2 (volume : Measure ℝ) :=
    hh.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  have h2 := h1.comp_measurePreserving
    (measurePreserving_add_right (volume : Measure ℝ) (-s))
  refine h2.ae_eq (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  congr 1
  ring

/-- **The slice is square integrable.** -/
theorem memLp_slice (hh : MemLp h 2 (volume : Measure ℝ)) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρnn : ∀ t, 0 ≤ ρ t) (s : ℝ) :
    MemLp (fun t : ℝ => h (s - t) * Real.sqrt (ρ t)) 2 (volume : Measure ℝ) := by
  obtain ⟨C, hC⟩ := hρc.bounded_above_of_compact_support hρs
  have hrefl := memLp_reflect_translate hh s
  have hmeas : AEStronglyMeasurable (fun t : ℝ => h (s - t) * Real.sqrt (ρ t))
      (volume : Measure ℝ) :=
    hrefl.aestronglyMeasurable.mul
      (Real.continuous_sqrt.comp hρc).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine (hrefl.integrable_sq.const_mul C).mono'
    ((hmeas.norm.pow 2)) (Filter.Eventually.of_forall fun t => ?_)
  have hρC : ρ t ≤ C := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC t)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [norm_mul, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hρnn t), sq_abs]
  calc h (s - t) ^ 2 * ρ t ≤ h (s - t) ^ 2 * C :=
        mul_le_mul_of_nonneg_left hρC (sq_nonneg _)
    _ = C * h (s - t) ^ 2 := by ring

end Cvs.WeilForm.Mollify.MollifiedSliceL2
