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
import Cvs.Zeta.RectArgument
import Cvs.Zeta.RectWinding

/-
Cauchy's integral formula on a rectangle, and the weighted argument principle.

Mathlib has the Cauchy formula for circles only.  On a rectangle it follows from
the same two-line split as everywhere else in this development: `dslope` absorbs
the singularity and integrates to zero by Cauchy–Goursat, leaving `φ(ρ)` times
the winding integral of `Cvs.Zeta.RectWinding`.

The weighted form is what produces the *zero sum* of the explicit formula: with a
test function `φ` in the integrand, each zero inside the contour contributes
`φ(ρ)` rather than `1`.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex Set
open scoped Interval

/-- `dslope` splits off the pole: `φ(u)/(u−ρ) = dslope φ ρ u + φ(ρ)·(u−ρ)⁻¹`. -/
theorem div_sub_eq_dslope_add {φ : ℂ → ℂ} {ρ u : ℂ} (hu : u ≠ ρ) :
    φ u / (u - ρ) = dslope φ ρ u + φ ρ * (u - ρ)⁻¹ := by
  rw [dslope_of_ne _ hu, slope_def_field]
  field_simp [sub_ne_zero.mpr hu]
  ring

/-- `dslope φ ρ` is holomorphic wherever `φ` is — the removable singularity. -/
theorem differentiableOn_dslope_at {φ : ℂ → ℂ} {U : Set ℂ} {ρ : ℂ}
    (hUo : IsOpen U) (hρ : ρ ∈ U) (hφ : DifferentiableOn ℂ φ U) :
    DifferentiableOn ℂ (dslope φ ρ) U :=
  (differentiableOn_dslope (hUo.mem_nhds hρ)).mpr hφ

/-- **Cauchy's integral formula on a rectangle.** Mathlib has this for circles only. -/
theorem rectBoundaryIntegral_div_sub_eq {φ : ℂ → ℂ} {z w ρ : ℂ} {U : Set ℂ}
    (hre1 : z.re < ρ.re) (hre2 : ρ.re < w.re)
    (him1 : z.im < ρ.im) (him2 : ρ.im < w.im)
    (hUo : IsOpen U) (hU : closedRect z w ⊆ U)
    (hφ : DifferentiableOn ℂ φ U) :
    rectBoundaryIntegral (fun u => φ u / (u - ρ)) z w
      = 2 * (Real.pi : ℂ) * I * φ ρ := by
  have hρre : ρ.re ∈ uIcc z.re w.re := Set.mem_uIcc.mpr (Or.inl ⟨hre1.le, hre2.le⟩)
  have hρim : ρ.im ∈ uIcc z.im w.im := Set.mem_uIcc.mpr (Or.inl ⟨him1.le, him2.le⟩)
  have hρU : ρ ∈ U := hU ⟨hρre, hρim⟩
  -- the boundary misses `ρ`
  have hbne : ∀ x : ℝ, ((x : ℂ) + z.im * I) ≠ ρ := by
    intro x hcon
    have h : (ρ : ℂ).im = z.im := by rw [← hcon]; simp
    rw [h] at him1; exact lt_irrefl _ him1
  have htne : ∀ x : ℝ, ((x : ℂ) + w.im * I) ≠ ρ := by
    intro x hcon
    have h : (ρ : ℂ).im = w.im := by rw [← hcon]; simp
    rw [h] at him2; exact lt_irrefl _ him2
  have hrne : ∀ y : ℝ, ((w.re : ℂ) + y * I) ≠ ρ := by
    intro y hcon
    have h : (ρ : ℂ).re = w.re := by rw [← hcon]; simp
    rw [h] at hre2; exact lt_irrefl _ hre2
  have hlne : ∀ y : ℝ, ((z.re : ℂ) + y * I) ≠ ρ := by
    intro y hcon
    have h : (ρ : ℂ).re = z.re := by rw [← hcon]; simp
    rw [h] at hre1; exact lt_irrefl _ hre1
  have hds : DifferentiableOn ℂ (dslope φ ρ) U :=
    differentiableOn_dslope_at hUo hρU hφ
  have hcong := rectBoundaryIntegral_congr_sides (z := z) (w := w)
    (f := fun u => φ u / (u - ρ))
    (g := fun u => dslope φ ρ u + φ ρ * (u - ρ)⁻¹)
    (fun x _ => div_sub_eq_dslope_add (hbne x))
    (fun x _ => div_sub_eq_dslope_add (htne x))
    (fun y _ => div_sub_eq_dslope_add (hrne y))
    (fun y _ => div_sub_eq_dslope_add (hlne y))
  have hzero : rectBoundaryIntegral (dslope φ ρ) z w = 0 :=
    rectBoundaryIntegral_eq_zero ((hds.mono hU).continuousOn)
      (fun x hx => (hds.differentiableAt (hUo.mem_nhds (hU ⟨
        Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩))))
  have hpolec : SidesIntegrable (fun u : ℂ => φ ρ * (u - ρ)⁻¹) z w := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) ?_)
    · exact fun x _ => sub_ne_zero.mpr (hbne x)
    · exact fun x _ => sub_ne_zero.mpr (htne x)
    · exact fun y _ => sub_ne_zero.mpr (hrne y)
    · exact fun y _ => sub_ne_zero.mpr (hlne y)
  rw [hcong, rectBoundaryIntegral_add (rect_sides_integrable ((hds.mono hU).continuousOn))
      hpolec, hzero, rectBoundaryIntegral_const_mul,
    rectBoundaryIntegral_inv_eq hre1 hre2 him1 him2]
  ring

end Cvs.Zeta
