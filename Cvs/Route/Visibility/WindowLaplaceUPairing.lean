import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExteriorTransformHolomorphy
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.OneZeroParitySectors
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window Laplace transform and the `U` pairing

For `u` in the form domain at `L = log x`, `F_u(w) = ∫_{−L/2}^{L/2} u(t + L/2) e^{wt} dt` is the two-sided Laplace
transform of the centred window profile. The `ue` pairing is its symmetrised real part:
`⟪u, ue_z⟫ = Re (F_u(w) + F_u(−w))/2` with `w = Im z + i Re z`, so at a zero `w = ½ − ρ̄`.
-/

noncomputable section

open Real MeasureTheory Set Metric
open scoped InnerProductSpace
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.StepA.OneZeroParitySectors (ue)

namespace Cvs.Route.Visibility.WindowLaplaceUPairing
open Cvs.ZeroCounting

/-- The profile `s ↦ u(s)` of a form-domain class, as an `L²(ℝ)` function. -/
def prof {x : ℕ} (u : Dom x) : ℝ → ℝ :=
  ⇑(((u : Dom x) : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))

/-- The window Laplace transform `F_u(w) = ∫_{−L/2}^{L/2} u(t + L/2) e^{wt} dt`, `L = log x`. -/
def winLaplace {x : ℕ} (u : Dom x) (w : ℂ) : ℂ :=
  ∫ t in -(Real.log x / 2)..Real.log x / 2, ((prof u (t + Real.log x / 2) : ℝ) : ℂ) * Complex.exp (w * t)

/-- The shifted profile is interval integrable on every interval. -/
theorem intervalIntegrable_prof {x : ℕ} (u : Dom x) (a b : ℝ) :
    IntervalIntegrable (fun t => prof u (t + Real.log x / 2)) volume a b := by
  have hl : LocallyIntegrable (prof u) volume := (Lp.memLp _).locallyIntegrable (by norm_num)
  have hc := isCompact_uIcc (a := a + Real.log x / 2) (b := b + Real.log x / 2)
  have h := ((hl.integrableOn_isCompact hc).intervalIntegrable).comp_add_right
    (Real.log x / 2)
  simpa using h

/-- The real part of `u(t + L/2) e^{wt}` is `u(t + L/2) e^{(Re w) t} cos((Im w) t)`. -/
theorem re_integrand {x : ℕ} (u : Dom x) (w : ℂ) (t : ℝ) :
    (((prof u (t + Real.log x / 2) : ℝ) : ℂ) * Complex.exp (w * t)).re
      = prof u (t + Real.log x / 2) * (Real.exp (w.re * t) * Real.cos (w.im * t)) := by
  rw [Complex.re_ofReal_mul, Complex.exp_re]
  simp

/-- `Re F_u(w) = ∫_{−L/2}^{L/2} u(t + L/2) e^{(Re w)t} cos((Im w)t) dt`. -/
theorem re_winLaplace {x : ℕ} (u : Dom x) (w : ℂ) :
    (winLaplace u w).re = ∫ t in -(Real.log x / 2)..Real.log x / 2,
      prof u (t + Real.log x / 2) * (Real.exp (w.re * t) * Real.cos (w.im * t)) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((prof u (t + Real.log x / 2) : ℝ) : ℂ) * Complex.exp (w * t))
      volume (-(Real.log x / 2)) (Real.log x / 2) := by
    have h1 : IntervalIntegrable (fun t : ℝ => ((prof u (t + Real.log x / 2) : ℝ) : ℂ)) volume
        (-(Real.log x / 2)) (Real.log x / 2) :=
      ⟨(intervalIntegrable_prof u _ _).1.ofReal, (intervalIntegrable_prof u _ _).2.ofReal⟩
    exact h1.mul_continuousOn (by fun_prop)
  have h := Complex.reCLM.intervalIntegral_comp_comm hi
  simp only [Complex.reCLM_apply] at h
  rw [winLaplace, ← h]
  exact intervalIntegral.integral_congr fun t _ => re_integrand u w t

/-- The two-sided Laplace transform `w ↦ ∫_{−h}^{h} φ(t) e^{wt} dt` of an integrable `φ` is entire. -/
theorem differentiable_laplace {φ : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h)
    (hφ : IntervalIntegrable φ volume (-h) h) :
    Differentiable ℂ fun w : ℂ => ∫ t in -h..h, ((φ t : ℝ) : ℂ) * Complex.exp (w * t) := by
  intro w₀
  have hφc : IntervalIntegrable (fun t => ((φ t : ℝ) : ℂ)) volume (-h) h := ⟨hφ.1.ofReal, hφ.2.ofReal⟩
  set K := h * Real.exp ((‖w₀‖ + 1) * h)
  have hb : IntervalIntegrable (fun t => |φ t| * K) volume (-h) h := hφ.abs.mul_const K
  have hI : uIoc (-h) h = Ioc (-h) h := uIoc_of_le (by linarith)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun w t => ((φ t : ℝ) : ℂ) * Complex.exp (w * t))
    (F' := fun w t => ((φ t : ℝ) : ℂ) * ((t : ℂ) * Complex.exp (w * t)))
    (x₀ := w₀) (s := ball w₀ 1) (bound := fun t => |φ t| * K) (ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun w => by
      rw [hI]; exact (hφc.mul_continuousOn
        (by fun_prop : ContinuousOn (fun t : ℝ => Complex.exp (w * t)) _)).1.aestronglyMeasurable)
    (hφc.mul_continuousOn (by fun_prop))
    (by rw [hI]; exact (hφc.mul_continuousOn
      (by fun_prop : ContinuousOn (fun t : ℝ => (t : ℂ) * Complex.exp (w₀ * t)) _)).1.aestronglyMeasurable)
    ?_ hb ?_
  · exact key.2.differentiableAt
  · refine Filter.Eventually.of_forall fun t ht w hw => ?_
    have ht' : |t| ≤ h := by
      rw [hI] at ht
      exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    have hw' : ‖w‖ ≤ ‖w₀‖ + 1 := by
      have := mem_ball_iff_norm.1 hw
      linarith [norm_le_insert' w w₀]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs,
      Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine mul_le_mul ht' (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hh
    calc (w * t).re ≤ ‖w * t‖ := Complex.re_le_norm _
      _ = ‖w‖ * |t| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (‖w₀‖ + 1) * h := mul_le_mul hw' ht' (abs_nonneg _) (by positivity)
  · refine Filter.Eventually.of_forall fun t _ w _ => ?_
    have := ((hasDerivAt_id w).mul_const (t : ℂ)).cexp
    simpa [mul_comm, mul_assoc, mul_left_comm] using this.const_mul ((φ t : ℝ) : ℂ)

/-- The window transform `F_u` is entire. -/
theorem differentiable_winLaplace {x : ℕ} (u : Dom x) : Differentiable ℂ (winLaplace u) := by
  have h := differentiable_laplace (φ := fun t => prof u (t + Real.log x / 2)) (h := Real.log x / 2)
    (by have := Real.log_natCast_nonneg x; linarith) (intervalIntegrable_prof u _ _)
  exact h

/-- **Sub-mean value on discs**: `|F_u(c)|² ≤ (πr²)⁻¹∫_{D(c,r)} |F_u|²`. -/
theorem norm_sq_winLaplace_le_ball {x : ℕ} (u : Dom x) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ‖winLaplace u c‖ ^ 2 ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in ball c r, ‖winLaplace u z‖ ^ 2 :=
  Cvs.Route.Visibility.ExteriorTransformHolomorphy.norm_sq_le_ball hr (differentiable_winLaplace u).diffContOnCl

/-- **The `U` pairing is the symmetrised window transform**: `⟪u, ue_z⟫ = Re (F_u(w) + F_u(−w))/2`,
`w = Im z + i Re z`. -/
theorem inner_ueVec_eq_re {x : ℕ} (hx0 : (0 : ℝ) < x) (u : Dom x) (z : ℂ) :
    ⟪u, ueVec hx0 z⟫_ℝ
      = ((winLaplace u (z.im + z.re * Complex.I) + winLaplace u (-(z.im + z.re * Complex.I))) / 2).re := by
  rw [Cvs.Route.Visibility.VisibilityClosingStep.inner_ueVec hx0 z u (f := prof u) (Filter.EventuallyEq.refl _ _)]
  have hd : ∀ v : ℂ, (v / 2).re = v.re / 2 := fun v => by simp
  rw [hd, Complex.add_re, re_winLaplace, re_winLaplace]
  have hI : ∀ w : ℂ, IntervalIntegrable
      (fun t => prof u (t + Real.log x / 2) * (Real.exp (w.re * t) * Real.cos (w.im * t))) volume
      (-(Real.log x / 2)) (Real.log x / 2) :=
    fun w => (intervalIntegrable_prof u _ _).mul_continuousOn (by fun_prop)
  rw [← intervalIntegral.integral_add (hI _) (hI _), ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [ue, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im]
  rw [Real.cosh_eq]
  have hc : Real.cos (-(z.re * t)) = Real.cos (z.re * t) := Real.cos_neg _
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero, neg_mul] at hc ⊢
  rw [hc]
  ring

end Cvs.Route.Visibility.WindowLaplaceUPairing

end
