import Mathlib
import Cvs.Upstream.L2DilationContinuity
import Cvs.WeilForm.Mollify.ComposedApproximant
import Cvs.WeilForm.Mollify.MollifierKernel
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy
import Cvs.WeilForm.Mollify.MollifySmooth
import Cvs.WeilForm.WindowConstraintSet
import Cvs.WeilForm.WindowSetNonempty

/-!
# Almost-everywhere symmetry is enough

    η symmetric a.e.  ⟹  the dilate and its translate are too, and the mollification is
    symmetric POINTWISE

the mollification integrating away the null set on which the symmetry fails.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Upstream.L2DilationContinuity

namespace Cvs.WeilForm.Mollify.AeSymmetryEnough

variable {L : ℝ} {η : ℝ → ℝ}

/-- Scaling is quasi measure preserving. -/
theorem qmp_div {a : ℝ} (ha : 0 < a) :
    QuasiMeasurePreserving (fun x : ℝ => x / a)
      (volume : Measure ℝ) (volume : Measure ℝ) := by
  refine ⟨(measurable_id.div_const a).aemeasurable, ?_⟩
  have hfun : (fun x : ℝ => x / a) = fun x : ℝ => a⁻¹ * x := by
    funext x; rw [div_eq_inv_mul]
  rw [hfun, Real.map_volume_mul_left (inv_ne_zero ha.ne')]
  exact Measure.smul_absolutelyContinuous

/-- **A dilate of an a.e. symmetric function is a.e. symmetric.** -/
theorem dilate_even_ae {a : ℝ} (ha : 0 < a)
    (hη : (fun x : ℝ => η (L - x)) =ᵐ[(volume : Measure ℝ)] η) :
    (fun x : ℝ => dilate a η (a * L - x)) =ᵐ[(volume : Measure ℝ)] dilate a η := by
  have hshift := (qmp_div ha).ae hη
  filter_upwards [hshift] with x hx
  simp only [dilate]
  have harg : (a * L - x) / a = L - x / a := by field_simp
  rw [harg, hx]

/-- **The dilate-and-translate is a.e. symmetric about the window's centre.** -/
theorem shifted_even_ae (hL : 0 < L)
    (hη : (fun x : ℝ => η (L - x)) =ᵐ[(volume : Measure ℝ)] η) (n : ℕ) :
    (fun x : ℝ => Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n (L - x))
      =ᵐ[(volume : Measure ℝ)] Cvs.WeilForm.Mollify.ComposedApproximant.shifted L η n := by
  set a : ℝ := Cvs.WeilForm.Mollify.ComposedApproximant.dila n with ha
  set c : ℝ := Cvs.WeilForm.Mollify.ComposedApproximant.shift L n with hc
  have hapos : 0 < a := Cvs.WeilForm.Mollify.ComposedApproximant.dila_pos n
  have hfit : a * L + 2 * c = L := Cvs.WeilForm.Mollify.ComposedApproximant.fit L n
  have hdil := dilate_even_ae (L := L) hapos hη
  -- translate the almost-everywhere statement
  have htr := ((measurePreserving_add_right (volume : Measure ℝ)
    (-c)).quasiMeasurePreserving).ae hdil
  filter_upwards [htr] with x hx
  simp only [Cvs.WeilForm.Mollify.ComposedApproximant.shifted]
  have hlhs : L - x + -c = a * L - (x + -c) := by linarith
  rw [hlhs]
  exact hx

/-- **Mollification by an even kernel turns a.e. symmetry into pointwise symmetry.** -/
theorem conv_even_of_ae {S ρ : ℝ → ℝ}
    (hS : (fun x : ℝ => S (L - x)) =ᵐ[(volume : Measure ℝ)] S)
    (hρ : ∀ t : ℝ, ρ (-t) = ρ t) (x : ℝ) :
    Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv S ρ (L - x) = Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv S ρ x := by
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.neg ℝ))
      (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have h := hmp.integral_comp' (fun u : ℝ => S (x - u) * ρ u)
  rw [Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv, Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv]
  refine Eq.trans ?_ h
  -- the symmetry holds for almost every displacement
  have hae := ((measurePreserving_add_right (volume : Measure ℝ) x).quasiMeasurePreserving).ae hS
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  show S (L - x - t) * ρ t = S (x - -t) * ρ (-t)
  rw [hρ t, show L - x - t = L - (t + x) by ring, ht, show x - -t = t + x by ring]

/-- **So the composed approximant is symmetric, from an a.e. symmetric target.** -/
theorem pre_even_of_ae (hL : 0 < L)
    (hη : (fun x : ℝ => η (L - x)) =ᵐ[(volume : Measure ℝ)] η) (n : ℕ) (x : ℝ) :
    Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n (L - x) = Cvs.WeilForm.Mollify.ComposedApproximant.pre hL η n x :=
  conv_even_of_ae (shifted_even_ae hL hη n) (Cvs.WeilForm.Mollify.MollifySmooth.kernel_neg _) x

/-- **A windowed symmetric function is symmetric off the two endpoints.** -/
theorem indicator_even_ae (hL : L ≠ 0) {f : ℝ → ℝ} (hf : ∀ x : ℝ, f (L - x) = f x) :
    (fun x : ℝ => Set.indicator (Set.Ioc (0:ℝ) L) f (L - x))
      =ᵐ[(volume : Measure ℝ)] Set.indicator (Set.Ioc (0:ℝ) L) f := by
  have hnull : (volume : Measure ℝ) ({(0:ℝ)} ∪ {L}) = 0 := by
    refine measure_union_null ?_ ?_ <;> exact Real.volume_singleton
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
  intro x hx
  by_contra hmem
  refine hx ?_
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hmem
  obtain ⟨hx0, hxL⟩ := hmem
  simp only
  by_cases hin : x ∈ Set.Ioc (0:ℝ) L
  · have hin' : L - x ∈ Set.Ioc (0:ℝ) L := by
      simp only [Set.mem_Ioc] at hin ⊢
      refine ⟨?_, by linarith [hin.1]⟩
      rcases lt_or_eq_of_le hin.2 with h | h
      · linarith
      · exact absurd h hxL
    rw [Set.indicator_of_mem hin', Set.indicator_of_mem hin]
    exact hf x
  · have hout : L - x ∉ Set.Ioc (0:ℝ) L := by
      simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hin ⊢
      rcases hin with h | h
      · have hlt : x < 0 := lt_of_le_of_ne h hx0
        exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    rw [Set.indicator_of_notMem hout, Set.indicator_of_notMem hin]

/-- **The constant mode is symmetric, off the endpoints.** -/
theorem flat_even_ae (hL : 0 < L) :
    (fun x : ℝ => Cvs.WeilForm.WindowSetNonempty.flat L (L - x))
      =ᵐ[(volume : Measure ℝ)] Cvs.WeilForm.WindowSetNonempty.flat L := by
  rw [Cvs.WeilForm.WindowSetNonempty.flat]
  exact indicator_even_ae hL.ne' (fun x => rfl)

/-- **The even sector's constraint set has a member.** -/
theorem exists_even_member (hL : 0 < L) :
    ∃ η ∈ Cvs.WeilForm.WindowConstraintSet.windowSet L,
      (fun x : ℝ => η (L - x)) =ᵐ[(volume : Measure ℝ)] η := by
  refine ⟨fun x => (Real.sqrt L)⁻¹ * Cvs.WeilForm.WindowSetNonempty.flat L x,
    Cvs.WeilForm.WindowSetNonempty.flat_normalised_mem hL, ?_⟩
  filter_upwards [flat_even_ae hL] with x hx
  rw [hx]

end Cvs.WeilForm.Mollify.AeSymmetryEnough
