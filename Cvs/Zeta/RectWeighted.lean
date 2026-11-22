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
import Cvs.Zeta.ArgumentPrinciple
import Cvs.Zeta.RectArgument
import Cvs.Zeta.RectCauchy
import Cvs.Zeta.RectWinding

/-
The explicit formula's zero side, at finite height.

`∮_∂R (f'/f)·φ = 2πi·Σ_{n∈F} φ(bₙ)`: with a test function in the integrand, each
zero inside the rectangle contributes `φ(ρ)` rather than `1`.  That sum **is**
the zero side of Guinand–Weil.

What is *not* here is the limit.  Taking the rectangle to infinity — right edge
at `Re s = 1+δ` where the Dirichlet series converges, left edge at `Re s = −δ`
via the functional equation, horizontal edges to `±∞` — needs growth estimates on
`ξ'/ξ` in the strip.  Those are the genuinely hard part of the explicit formula
and none of them are here.  At finite height no estimate is needed, which is
exactly why this much is reachable.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex Set
open scoped Interval

theorem SidesIntegrable.add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : SidesIntegrable f z w) (hg : SidesIntegrable g z w) :
    SidesIntegrable (fun u => f u + g u) z w :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

theorem SidesIntegrable.zero {z w : ℂ} : SidesIntegrable (fun _ : ℂ => (0 : ℂ)) z w :=
  ⟨intervalIntegrable_const, intervalIntegrable_const,
   intervalIntegrable_const, intervalIntegrable_const⟩

theorem sidesIntegrable_finset_sum {ι : Type*} {s : Finset ι} {F : ι → ℂ → ℂ} {z w : ℂ}
    (h : ∀ i ∈ s, SidesIntegrable (F i) z w) :
    SidesIntegrable (fun u => ∑ i ∈ s, F i u) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SidesIntegrable.zero
  | insert j t hj ih =>
      have ht : ∀ i ∈ t, SidesIntegrable (F i) z w :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      simp only [Finset.sum_insert hj]
      exact (h j (Finset.mem_insert_self j t)).add (ih ht)

theorem rectBoundaryIntegral_finset_sum {ι : Type*} {s : Finset ι} {F : ι → ℂ → ℂ}
    {z w : ℂ} (h : ∀ i ∈ s, SidesIntegrable (F i) z w) :
    rectBoundaryIntegral (fun u => ∑ i ∈ s, F i u) z w
      = ∑ i ∈ s, rectBoundaryIntegral (F i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectBoundaryIntegral]
  | insert j t hj ih =>
      have ht : ∀ i ∈ t, SidesIntegrable (F i) z w :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      simp only [Finset.sum_insert hj]
      rw [rectBoundaryIntegral_add (h j (Finset.mem_insert_self j t))
        (sidesIntegrable_finset_sum ht), ih ht]

/-- A point strictly inside the rectangle is missed by all four sides. -/
theorem sides_ne_of_interior {z w ρ : ℂ}
    (h : z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im) :
    (∀ x : ℝ, ((x : ℂ) + z.im * I) ≠ ρ) ∧ (∀ x : ℝ, ((x : ℂ) + w.im * I) ≠ ρ)
    ∧ (∀ y : ℝ, ((w.re : ℂ) + y * I) ≠ ρ) ∧ (∀ y : ℝ, ((z.re : ℂ) + y * I) ≠ ρ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun x hc => ?_, fun x hc => ?_, fun y hc => ?_, fun y hc => ?_⟩
  · have : (ρ : ℂ).im = z.im := by rw [← hc]; simp
    rw [this] at h3; exact lt_irrefl _ h3
  · have : (ρ : ℂ).im = w.im := by rw [← hc]; simp
    rw [this] at h4; exact lt_irrefl _ h4
  · have : (ρ : ℂ).re = w.re := by rw [← hc]; simp
    rw [this] at h2; exact lt_irrefl _ h2
  · have : (ρ : ℂ).re = z.re := by rw [← hc]; simp
    rw [this] at h1; exact lt_irrefl _ h1

set_option maxHeartbeats 1000000 in
/-- **The weighted argument principle on a rectangle.** With a test function `φ` in the integrand,
each zero inside contributes `φ(ρ)` rather than `1`. -/
theorem rect_argument_principle_weighted {ι : Type*} {f g φ : ℂ → ℂ} {z w : ℂ}
    {F : Finset ι} {b : ι → ℂ} {U : Set ℂ}
    (hin : ∀ n ∈ F, z.re < (b n).re ∧ (b n).re < w.re ∧ z.im < (b n).im ∧ (b n).im < w.im)
    (hUo : IsOpen U) (hU : closedRect z w ⊆ U)
    (hfg : ∀ u, f u = (∏ n ∈ F, (u - b n)) * g u)
    (hgd : DifferentiableOn ℂ g U) (hgne : ∀ u ∈ U, g u ≠ 0)
    (hφ : DifferentiableOn ℂ φ U) :
    rectBoundaryIntegral (fun u => deriv f u / f u * φ u) z w
      = 2 * (Real.pi : ℂ) * I * ∑ n ∈ F, φ (b n) := by
  classical
  -- the split, pointwise off the zeros
  have hsplit : ∀ u ∈ closedRect z w, (∀ n ∈ F, u ≠ b n) →
      deriv f u / f u * φ u
        = (∑ n ∈ F, φ u / (u - b n)) + deriv g u / g u * φ u := by
    intro u hu hne
    have hP : (∏ n ∈ F, (u - b n)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun n hn => sub_ne_zero.mpr (hne n hn))
    have hdP : DifferentiableAt ℂ (fun v : ℂ => ∏ n ∈ F, (v - b n)) u :=
      DifferentiableAt.fun_finsetProd (fun n _ => differentiableAt_id.sub_const (b n))
    have hfun : f = (fun v : ℂ => ∏ n ∈ F, (v - b n)) * g := funext hfg
    have hm := logDeriv_mul (f := fun v : ℂ => ∏ n ∈ F, (v - b n)) (g := g) u
      hP (hgne u (hU hu)) hdP (hgd.differentiableAt (hUo.mem_nhds (hU hu)))
    have hl : deriv f u / f u = (∑ n ∈ F, 1 / (u - b n)) + deriv g u / g u := by
      rw [show deriv f u / f u = logDeriv f u from rfl, hfun, hm,
        logDeriv_prod_linear F b hne]
      rfl
    rw [hl, add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun n _ => by ring)
  -- boundary side conditions
  have hbd : ∀ n ∈ F, _ := fun n hn => sides_ne_of_interior (hin n hn)
  have hcong := rectBoundaryIntegral_congr_sides (z := z) (w := w)
    (f := fun u => deriv f u / f u * φ u)
    (g := fun u => (∑ n ∈ F, φ u / (u - b n)) + deriv g u / g u * φ u)
    (fun x hx => hsplit _ (bottom_mem hx) (fun n hn => (hbd n hn).1 x))
    (fun x hx => hsplit _ (top_mem hx) (fun n hn => (hbd n hn).2.1 x))
    (fun y hy => hsplit _ (right_mem hy) (fun n hn => (hbd n hn).2.2.1 y))
    (fun y hy => hsplit _ (left_mem hy) (fun n hn => (hbd n hn).2.2.2 y))
  -- the holomorphic remainder
  have hquot : DifferentiableOn ℂ (fun u => deriv g u / g u * φ u) U :=
    ((hgd.deriv hUo).div hgd hgne).mul hφ
  have hzero : rectBoundaryIntegral (fun u => deriv g u / g u * φ u) z w = 0 :=
    rectBoundaryIntegral_eq_zero ((hquot.mono hU).continuousOn)
      (fun x hx => hquot.differentiableAt (hUo.mem_nhds (hU
        ⟨Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩)))
  -- each pole term
  have hpolesi : ∀ n ∈ F, SidesIntegrable (fun u : ℂ => φ u / (u - b n)) z w := by
    intro n hn
    obtain ⟨e1, e2, e3, e4⟩ := hbd n hn
    have hc := (hφ.mono hU).continuousOn
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hd : ContinuousOn (fun x : ℝ => ((x : ℂ) + z.im * I) - b n) (Set.uIcc z.re w.re) :=
        Continuous.continuousOn (by fun_prop)
      have hnum : ContinuousOn (fun x : ℝ => φ (((x : ℂ) + z.im * I))) (Set.uIcc z.re w.re) :=
        hc.comp (f := fun x : ℝ => ((x : ℂ) + z.im * I)) (Continuous.continuousOn (by fun_prop))
          (fun x hx => bottom_mem hx)
      exact (hnum.div hd (fun x _ => sub_ne_zero.mpr (e1 x))).intervalIntegrable
    · have hd : ContinuousOn (fun x : ℝ => ((x : ℂ) + w.im * I) - b n) (Set.uIcc z.re w.re) :=
        Continuous.continuousOn (by fun_prop)
      have hnum : ContinuousOn (fun x : ℝ => φ (((x : ℂ) + w.im * I))) (Set.uIcc z.re w.re) :=
        hc.comp (f := fun x : ℝ => ((x : ℂ) + w.im * I)) (Continuous.continuousOn (by fun_prop))
          (fun x hx => top_mem hx)
      exact (hnum.div hd (fun x _ => sub_ne_zero.mpr (e2 x))).intervalIntegrable
    · have hd : ContinuousOn (fun y : ℝ => ((w.re : ℂ) + y * I) - b n) (Set.uIcc z.im w.im) :=
        Continuous.continuousOn (by fun_prop)
      have hnum : ContinuousOn (fun y : ℝ => φ (((w.re : ℂ) + y * I))) (Set.uIcc z.im w.im) :=
        hc.comp (f := fun y : ℝ => ((w.re : ℂ) + y * I)) (Continuous.continuousOn (by fun_prop))
          (fun y hy => right_mem hy)
      exact (hnum.div hd (fun y _ => sub_ne_zero.mpr (e3 y))).intervalIntegrable
    · have hd : ContinuousOn (fun y : ℝ => ((z.re : ℂ) + y * I) - b n) (Set.uIcc z.im w.im) :=
        Continuous.continuousOn (by fun_prop)
      have hnum : ContinuousOn (fun y : ℝ => φ (((z.re : ℂ) + y * I))) (Set.uIcc z.im w.im) :=
        hc.comp (f := fun y : ℝ => ((z.re : ℂ) + y * I)) (Continuous.continuousOn (by fun_prop))
          (fun y hy => left_mem hy)
      exact (hnum.div hd (fun y _ => sub_ne_zero.mpr (e4 y))).intervalIntegrable
  rw [hcong, rectBoundaryIntegral_add (sidesIntegrable_finset_sum hpolesi)
      (rect_sides_integrable ((hquot.mono hU).continuousOn)), hzero, add_zero,
    rectBoundaryIntegral_finset_sum hpolesi]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hin n hn
  exact rectBoundaryIntegral_div_sub_eq h1 h2 h3 h4 hUo hU hφ

end Cvs.Zeta
