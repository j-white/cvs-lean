import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.RectWinding

/-
The argument principle on a rectangle.

`Cvs.Zeta.RectWinding` supplies the one piece that could not come from the circle;
this assembles it.  Mathlib's Cauchy–Goursat kills the holomorphic part, the
winding integral supplies the pole, and the pointwise decomposition
`Cvs.Zeta.logDeriv_split` is contour-agnostic and carries over unchanged from the
circle case.

This is what rung 6's contour shift needs: `N(T)` counts zeros in a *strip*, not
a disc.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex Set
open scoped Interval

/-- The closed rectangle Mathlib's Cauchy–Goursat is stated on. -/
noncomputable abbrev closedRect (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

theorem bottom_mem {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + z.im * I) ∈ closedRect z w := by
  exact ⟨by simpa using hx, by simp⟩

theorem top_mem {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + w.im * I) ∈ closedRect z w := by
  exact ⟨by simpa using hx, by simp⟩

theorem right_mem {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((w.re : ℂ) + y * I) ∈ closedRect z w := by
  exact ⟨by simp, by simpa using hy⟩

theorem left_mem {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((z.re : ℂ) + y * I) ∈ closedRect z w := by
  exact ⟨by simp, by simpa using hy⟩

/-- Integrability along the four sides — the actual hypothesis the boundary
integral needs.  Continuity on the closed rectangle implies it, but the pole term
`m/(u−ρ)` satisfies it *without* being continuous there, since `ρ` is interior. -/
def SidesIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + z.im * I)) MeasureTheory.volume z.re w.re
  ∧ IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + w.im * I)) MeasureTheory.volume z.re w.re
  ∧ IntervalIntegrable (fun y : ℝ => f ((w.re : ℂ) + y * I)) MeasureTheory.volume z.im w.im
  ∧ IntervalIntegrable (fun y : ℝ => f ((z.re : ℂ) + y * I)) MeasureTheory.volume z.im w.im

theorem rect_sides_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (closedRect z w)) : SidesIntegrable f z w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_
  · exact hf.comp (by fun_prop) (fun x hx => bottom_mem hx)
  · exact hf.comp (by fun_prop) (fun x hx => top_mem hx)
  · exact hf.comp (by fun_prop) (fun y hy => right_mem hy)
  · exact hf.comp (by fun_prop) (fun y hy => left_mem hy)

/-- **Cauchy–Goursat, in this notation.** -/
theorem rectBoundaryIntegral_eq_zero {f : ℂ → ℂ} {z w : ℂ}
    (hc : ContinuousOn f (closedRect z w))
    (hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im),
      DifferentiableAt ℂ f x) :
    rectBoundaryIntegral f z w = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w ∅ Set.countable_empty hc (fun x hx => hd x hx.1)
  simpa [rectBoundaryIntegral, smul_eq_mul] using h

theorem rectBoundaryIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : SidesIntegrable f z w) (hg : SidesIntegrable g z w) :
    rectBoundaryIntegral (fun u => f u + g u) z w
      = rectBoundaryIntegral f z w + rectBoundaryIntegral g z w := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain ⟨g1, g2, g3, g4⟩ := hg
  simp only [rectBoundaryIntegral]
  rw [intervalIntegral.integral_add f1 g1, intervalIntegral.integral_add f2 g2,
    intervalIntegral.integral_add f3 g3, intervalIntegral.integral_add f4 g4]
  ring

theorem rectBoundaryIntegral_congr_sides {f g : ℂ → ℂ} {z w : ℂ}
    (hb : ∀ x ∈ uIcc z.re w.re, f ((x : ℂ) + z.im * I) = g ((x : ℂ) + z.im * I))
    (ht : ∀ x ∈ uIcc z.re w.re, f ((x : ℂ) + w.im * I) = g ((x : ℂ) + w.im * I))
    (hr : ∀ y ∈ uIcc z.im w.im, f ((w.re : ℂ) + y * I) = g ((w.re : ℂ) + y * I))
    (hl : ∀ y ∈ uIcc z.im w.im, f ((z.re : ℂ) + y * I) = g ((z.re : ℂ) + y * I)) :
    rectBoundaryIntegral f z w = rectBoundaryIntegral g z w := by
  simp only [rectBoundaryIntegral]
  rw [intervalIntegral.integral_congr hb, intervalIntegral.integral_congr ht,
    intervalIntegral.integral_congr hr, intervalIntegral.integral_congr hl]

theorem rectBoundaryIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectBoundaryIntegral (fun u => c * f u) z w = c * rectBoundaryIntegral f z w := by
  simp only [rectBoundaryIntegral, intervalIntegral.integral_const_mul]
  ring

end Cvs.Zeta
