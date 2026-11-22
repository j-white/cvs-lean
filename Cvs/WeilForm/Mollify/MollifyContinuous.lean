import Mathlib
import Cvs.Upstream.CauchySchwarzLine
import Cvs.Upstream.L2TranslationContinuity
import Cvs.WeilForm.Mollify.MollifiedSliceL2
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy

/-!
# The mollification is continuous

    f ∈ L²,  ρ continuous with compact support  ⟹  f⋆ρ is continuous

the regularity a mollification exists to buy: the displacement passes onto `ρ`, whose
translation modulus is controlled because `ρ` is continuous and compactly supported.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.WeilForm.Mollify.MollifyContinuous

variable {f ρ : ℝ → ℝ}

/-- **The convolution is symmetric in its two arguments.** -/
theorem conv_comm (s : ℝ) (f ρ : ℝ → ℝ) :
    Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s = ∫ u : ℝ, f u * ρ (s - u) := by
  rw [Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv]
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.subLeft s))
      (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.measurePreserving_sub_left (volume : Measure ℝ) s
  have h := hmp.integral_comp' (fun u : ℝ => f u * ρ (s - u))
  refine Eq.trans ?_ h
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show f (s - t) * ρ t = f (s - t) * ρ (s - (s - t))
  rw [sub_sub_cancel]

/-- **The mollification is continuous.** -/
theorem continuous_conv (hf : MemLp f 2 (volume : Measure ℝ))
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) :
    Continuous (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ) := by
  have hρL : MemLp ρ 2 (volume : Measure ℝ) := hρc.memLp_of_hasCompactSupport hρs
  set Ef : ℝ := Real.sqrt (∫ x : ℝ, f x ^ 2) with hEf
  have hEfnn : 0 ≤ Ef := Real.sqrt_nonneg _
  -- the difference of two values, as one integral against `f`
  have hsplit : ∀ s s' : ℝ, Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s
      - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s' = ∫ u : ℝ, f u * (ρ (s - u) - ρ (s' - u)) := by
    intro s s'
    have h1 : Integrable (fun u : ℝ => f u * ρ (s - u)) (volume : Measure ℝ) :=
      hf.integrable_mul (Cvs.WeilForm.Mollify.MollifiedSliceL2.memLp_reflect_translate hρL s)
    have h2 : Integrable (fun u : ℝ => f u * ρ (s' - u)) (volume : Measure ℝ) :=
      hf.integrable_mul (Cvs.WeilForm.Mollify.MollifiedSliceL2.memLp_reflect_translate hρL s')
    rw [conv_comm s f ρ, conv_comm s' f ρ, ← integral_sub h1 h2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  -- the modulus is the kernel's, at the displacement
  have hmod : ∀ s s' : ℝ, (∫ u : ℝ, (ρ (s - u) - ρ (s' - u)) ^ 2)
      = ∫ v : ℝ, (ρ v - ρ (v + (s' - s))) ^ 2 := by
    intro s s'
    have hmp : MeasurePreserving (⇑(MeasurableEquiv.subLeft s))
        (volume : Measure ℝ) (volume : Measure ℝ) :=
      Measure.measurePreserving_sub_left (volume : Measure ℝ) s
    have h := hmp.integral_comp' (fun v : ℝ => (ρ v - ρ (v + (s' - s))) ^ 2)
    refine Eq.trans ?_ h
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show (ρ (s - u) - ρ (s' - u)) ^ 2 = (ρ (s - u) - ρ (s - u + (s' - s))) ^ 2
    rw [show s - u + (s' - s) = s' - u by ring]
  rw [Metric.continuous_iff]
  intro b ε hε
  set ε' : ℝ := (ε / (Ef + 1)) ^ 2 with hε'
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have htr := Cvs.Upstream.L2TranslationContinuity.tendsto_integral_sub_translate_sq_of_compactSupport
    hρc hρs
  rw [Metric.tendsto_nhds] at htr
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp (htr ε' hε'pos)
  refine ⟨η, hηpos, fun a hab => ?_⟩
  have hd : dist (a - b) 0 < η := by
    rw [Real.dist_eq, sub_zero]
    rw [Real.dist_eq] at hab
    exact hab
  have hmodle : (∫ v : ℝ, (ρ v - ρ (v + (a - b))) ^ 2) ≤ ε' := by
    have h := hη hd
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) h)
  have hdiff : MemLp (fun u : ℝ => ρ (b - u) - ρ (a - u)) 2 (volume : Measure ℝ) :=
    (Cvs.WeilForm.Mollify.MollifiedSliceL2.memLp_reflect_translate hρL b).sub
      (Cvs.WeilForm.Mollify.MollifiedSliceL2.memLp_reflect_translate hρL a)
  have hcs := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le hf hdiff
  rw [← hsplit b a] at hcs
  have hmodeq : (∫ u : ℝ, (ρ (b - u) - ρ (a - u)) ^ 2)
      = ∫ v : ℝ, (ρ v - ρ (v + (a - b))) ^ 2 := hmod b a
  rw [hmodeq] at hcs
  have hsq : Real.sqrt (∫ v : ℝ, (ρ v - ρ (v + (a - b))) ^ 2) ≤ ε / (Ef + 1) := by
    have := Real.sqrt_le_sqrt hmodle
    rwa [hε', Real.sqrt_sq (by positivity)] at this
  rw [Real.dist_eq]
  have habs : |Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ a - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ b|
      = |Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ b - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ a| := abs_sub_comm _ _
  rw [habs]
  have hfin : |Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ b - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ a|
      ≤ Ef * (ε / (Ef + 1)) := by
    refine le_trans hcs ?_
    rw [← hEf]
    exact mul_le_mul_of_nonneg_left hsq hEfnn
  have hlt : Ef * (ε / (Ef + 1)) < ε := by
    rw [mul_div_assoc'] at *
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hEfnn, hε]
  linarith

end Cvs.WeilForm.Mollify.MollifyContinuous
