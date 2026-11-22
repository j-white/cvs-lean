import Mathlib
import Cvs.L2a.PlaneCorrelationL2
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.Upstream.FourierLaplace
import Cvs.Upstream.FourierLaplacePlancherel
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Plancherel for the window transform on a vertical line

On the line `Re w = σ` the window transform of Cvs.Route.Visibility.WindowLaplaceUPairing is the Fourier–Laplace transform of the weighted profile
`1_{(−L/2, L/2]}(t)·u(t + L/2)·e^{σt}`, which lies in `L¹ ∩ L²`. Plancherel (Cvs.Upstream.FourierLaplacePlancherel) gives
`∫ ‖F_u(σ + ig)‖² dg = 2π ∫ ‖weighted profile‖² ≤ 2π·x^{|σ|}·‖u‖²`, since `e^{2σt} ≤ e^{|σ|L} = x^{|σ|}` on the
window.
-/

noncomputable section

open Real MeasureTheory Set Complex
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.Visibility.WindowLaplaceUPairing (prof winLaplace)

namespace Cvs.Route.Visibility.WindowTransformPlancherel
open Cvs.ZeroCounting

/-- The weighted window profile `1_{(−L/2, L/2]}(t)·u(t + L/2)·e^{σt}`, `L = log x`. -/
def winProf {x : ℕ} (u : Dom x) (σ : ℝ) : ℝ → ℂ :=
  indicator (Ioc (-(Real.log x / 2)) (Real.log x / 2))
    fun t => ((prof u (t + Real.log x / 2) * Real.exp (σ * t) : ℝ) : ℂ)

/-- **The window transform on a vertical line is a Fourier–Laplace transform**:
`F_u(σ + ig) = fourierLaplace (winProf u σ) g`. -/
theorem winLaplace_eq_fourierLaplace {x : ℕ} (u : Dom x) (σ g : ℝ) :
    winLaplace u (σ + g * I) = FourierLaplace.fourierLaplace (winProf u σ) g := by
  have hh : -(Real.log x / 2) ≤ Real.log x / 2 := by
    have := Real.log_natCast_nonneg x; linarith
  rw [winLaplace, intervalIntegral.integral_of_le hh, FourierLaplace.fourierLaplace]
  have hi : ∀ t : ℝ, winProf u σ t * Complex.exp (I * (g : ℂ) * t)
      = indicator (Ioc (-(Real.log x / 2)) (Real.log x / 2)) (fun t : ℝ =>
          ((prof u (t + Real.log x / 2) * Real.exp (σ * t) : ℝ) : ℂ) * Complex.exp (I * (g : ℂ) * t)) t :=
    fun t => by unfold winProf; by_cases ht : t ∈ Ioc (-(Real.log x / 2)) (Real.log x / 2) <;> simp [ht]
  simp_rw [hi]
  rw [integral_indicator measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The shifted profile `t ↦ u(t + L/2)` is in `L²(ℝ)`. -/
theorem memLp_prof_shift {x : ℕ} (u : Dom x) :
    MemLp (fun t => prof u (t + Real.log x / 2)) 2 volume :=
  (Lp.memLp _).comp_measurePreserving (measurePreserving_add_right volume (Real.log x / 2))

/-- `‖winProf u σ t‖ ≤ e^{|σ|L/2}·|u(t + L/2)|`. -/
theorem norm_winProf_le {x : ℕ} (u : Dom x) (σ t : ℝ) :
    ‖winProf u σ t‖ ≤ Real.exp (|σ| * (Real.log x / 2)) * |prof u (t + Real.log x / 2)| := by
  unfold winProf
  by_cases ht : t ∈ Ioc (-(Real.log x / 2)) (Real.log x / 2)
  · rw [indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (abs_nonneg _)
    have h1 : |t| ≤ Real.log x / 2 := abs_le.2 ⟨ht.1.le, ht.2⟩
    calc σ * t ≤ |σ * t| := le_abs_self _
      _ = |σ| * |t| := abs_mul _ _
      _ ≤ |σ| * (Real.log x / 2) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  · rw [indicator_of_notMem ht, norm_zero]; positivity

/-- The weighted window profile is integrable. -/
theorem integrable_winProf {x : ℕ} (u : Dom x) (σ : ℝ) : Integrable (winProf u σ) volume := by
  unfold winProf
  rw [integrable_indicator_iff measurableSet_Ioc]
  have h := ((Cvs.Route.Visibility.WindowLaplaceUPairing.intervalIntegrable_prof u (-(Real.log x / 2)) (Real.log x / 2)).mul_continuousOn
    (by fun_prop : ContinuousOn (fun t : ℝ => Real.exp (σ * t)) _))
  have hh : -(Real.log x / 2) ≤ Real.log x / 2 := by
    have := Real.log_natCast_nonneg x; linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh] at h
  exact h.ofReal

/-- The weighted window profile is in `L²(ℝ)`. -/
theorem memLp_winProf {x : ℕ} (u : Dom x) (σ : ℝ) : MemLp (winProf u σ) 2 volume := by
  refine ((memLp_prof_shift u).const_mul (Real.exp (|σ| * (Real.log x / 2)))).of_le
    (integrable_winProf u σ).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact norm_winProf_le u σ t

/-- `e^{2·|σ|·L/2} = x^{|σ|}`. -/
theorem exp_sq_eq_rpow {x : ℕ} (hx : 0 < x) (σ : ℝ) :
    Real.exp (|σ| * (Real.log x / 2)) ^ 2 = (x : ℝ) ^ |σ| := by
  rw [← Real.exp_nat_mul, Real.rpow_def_of_pos (by exact_mod_cast hx)]
  congr 1
  push_cast
  ring

/-- **Plancherel for the window transform**: on `Re w = σ`, `g ↦ ‖F_u(σ + ig)‖²` is integrable with
`∫ ‖F_u(σ + ig)‖² dg ≤ 2π·x^{|σ|}·‖u‖²`. -/
theorem integral_norm_sq_winLaplace_le {x : ℕ} (hx : 0 < x) (u : Dom x) (σ : ℝ) :
    Integrable (fun g : ℝ => ‖winLaplace u (σ + g * I)‖ ^ 2)
      ∧ ∫ g : ℝ, ‖winLaplace u (σ + g * I)‖ ^ 2 ≤ 2 * π * (x : ℝ) ^ |σ| * ‖u‖ ^ 2 := by
  simp_rw [winLaplace_eq_fourierLaplace]
  refine ⟨Cvs.Upstream.FourierLaplacePlancherel.integrable_norm_fourierLaplace_sq (integrable_winProf u σ) (memLp_winProf u σ), ?_⟩
  rw [Cvs.Upstream.FourierLaplacePlancherel.integral_norm_fourierLaplace_sq (integrable_winProf u σ) (memLp_winProf u σ),
    show 2 * π * (x : ℝ) ^ |σ| * ‖u‖ ^ 2 = 2 * π * ((x : ℝ) ^ |σ| * ‖u‖ ^ 2) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 2 * π)
  set K := Real.exp (|σ| * (Real.log x / 2))
  have hp := (memLp_two_iff_integrable_sq (memLp_prof_shift u).aestronglyMeasurable).1 (memLp_prof_shift u)
  have h1 : ∫ t, ‖winProf u σ t‖ ^ 2 ≤ ∫ t, K ^ 2 * prof u (t + Real.log x / 2) ^ 2 := by
    refine integral_mono ((memLp_two_iff_integrable_sq_norm (memLp_winProf u σ).aestronglyMeasurable).1 (memLp_winProf u σ))
      (hp.const_mul _) fun t => ?_
    have h := norm_winProf_le u σ t
    calc ‖winProf u σ t‖ ^ 2 ≤ (K * |prof u (t + Real.log x / 2)|) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = K ^ 2 * prof u (t + Real.log x / 2) ^ 2 := by rw [mul_pow, sq_abs]
  have h2 : ∫ t, prof u (t + Real.log x / 2) ^ 2 = ‖u‖ ^ 2 := by
    rw [integral_add_right_eq_self (fun t => prof u t ^ 2) (Real.log x / 2)]
    exact (Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral u.1.1).symm
  rw [integral_const_mul, h2, exp_sq_eq_rpow hx] at h1
  exact h1

end Cvs.Route.Visibility.WindowTransformPlancherel

end
