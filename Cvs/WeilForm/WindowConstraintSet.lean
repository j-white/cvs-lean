import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.SublevelUniformTightness
import Cvs.WeilForm.TransformClassesTotallyBounded
import Cvs.WeilForm.TransformFamiliesIsometric
import Cvs.WeilForm.UnitWindowTransformBounded
import Cvs.WeilForm.UnitWindowTransformEquicontinuous
import Cvs.WeilForm.WindowTransformIsometry
import Cvs.WeilForm.WindowTransformsEquicontinuous

/-!
# The window's constraint set, and its transforms' total boundedness

    D L = { f ∈ L² : supp f ⊆ (0, L],  ∫ f² = 1,  the Lévy integral converges }

whose members' transforms are equibounded, equicontinuous and — on a sublevel set of the
form — uniformly tight, so their classes are totally bounded.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil
open scoped FourierTransform

namespace Cvs.WeilForm.WindowConstraintSet

/-- **The constraint set.** -/
def windowSet (L : ℝ) : Set (ℝ → ℝ) :=
  {f | MemLp f 2 (volume : Measure ℝ) ∧ (∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0)
    ∧ (∫ x : ℝ, f x ^ 2) = 1
    ∧ IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Set.Ioi 0) (volume : Measure ℝ)}

theorem integrable_of_mem {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : f ∈ windowSet L) :
    Integrable f (volume : Measure ℝ) :=
  Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hf.1 hf.2.1

/-- **The transforms of a form-bounded family are totally bounded.** -/
theorem totallyBounded_transforms {L B : ℝ} (hL : 0 ≤ L) (P R : ℕ) {F : ℕ → ℝ → ℝ}
    (hFD : ∀ n, F n ∈ windowSet L)
    (hFB : ∀ n, Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F n) ≤ B) :
    TotallyBounded (Set.range fun n : ℕ =>
      (Cvs.WeilForm.TransformFamiliesIsometric.memLp_fourier (hFD n).1 (integrable_of_mem hL (hFD n))).toLp
        (𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (F n)))) := by
  have hint : ∀ n, Integrable (F n) (volume : Measure ℝ) := fun n =>
    integrable_of_mem hL (hFD n)
  have hcfint : ∀ n, Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf (F n)) (volume : Measure ℝ) :=
    fun n => (hint n).ofReal
  refine Cvs.WeilForm.TransformClassesTotallyBounded.totallyBounded_toLp (M := Real.sqrt L) ?_ ?_ ?_ ?_ ?_ ?_ _
  · intro n
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) (hcfint n)
  · intro n ξ
    exact Cvs.WeilForm.UnitWindowTransformBounded.norm_fourier_le hL (hFD n).1 (hFD n).2.1 (hFD n).2.2.1 ξ
  · refine Cvs.WeilForm.WindowTransformsEquicontinuous.equicontinuous_fourier (M := Real.sqrt (L ^ 3 / 3))
      hcfint (fun n => Cvs.WeilForm.UnitWindowTransformEquicontinuous.integrable_moment hL (hFD n).1 (hFD n).2.1)
      (fun n => Cvs.WeilForm.UnitWindowTransformEquicontinuous.moment_le hL (hFD n).1 (hFD n).2.1 (hFD n).2.2.1)
      (Real.sqrt_nonneg _)
  · intro n
    exact Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq (hFD n).1 (hint n)
  · intro i j
    have hsub : MemLp (F i - F j) 2 (volume : Measure ℝ) := (hFD i).1.sub (hFD j).1
    have hsubint : Integrable (F i - F j) (volume : Measure ℝ) := (hint i).sub (hint j)
    have hFs := Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hsub hsubint
    refine hFs.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only
    rw [Cvs.WeilForm.WindowTransformIsometry.fourier_sub (hint i) (hint j) ξ]
  · intro ε hε
    obtain ⟨T, hTpos, hT⟩ := Cvs.WeilForm.SublevelUniformTightness.exists_tight (L := L) (B := B) hL P R hε
    exact ⟨T, hTpos, fun n => hT (F n) (hFD n).1 (hFD n).2.1 (hFD n).2.2.1
      (hFD n).2.2.2 (hFB n)⟩

end Cvs.WeilForm.WindowConstraintSet
