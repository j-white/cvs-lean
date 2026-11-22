import Mathlib
import Cvs.Route.Visibility.CEBoundFromTrace

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# HV from the trace comparison, the trace limit and Landau's transition theorem

The limiting trace constants `Θ = log((7 + 4√3)/3)/π²` and `Θ₀ = log(16/3)/π²` satisfy `Θ ≤ Θ₀ < 9/50`, so
`limsup T_c ≤ Θ₀` gives the trace limit; with (B), the top ceiling, `PosQ0At 1`, KRD, `EdgeLawSum` and Carlson,
`CEBound (57/60)` and hV follow through `an earlier result.hV_ceBound`.
-/

noncomputable section

open Real Filter

namespace Cvs.Route.Visibility.VisibilityLandauTransition
open Cvs.ZeroCounting

open Cvs.Route.Visibility.CEBoundFromTrace (TraceComparison TraceBound TraceLimit TopCeiling LandauTransition)

/-- The reflected-wave trace constant `Θ = log((7 + 4√3)/3)/π² = (4 atanh(1/√3) − 2 atanh(1/2))/π²`. -/
def thetaSharp : ℝ := Real.log ((7 + 4 * √3) / 3) / π ^ 2

/-- The fixed-ellipse trace constant `Θ₀ = log(16/3)/π²`. -/
def thetaCons : ℝ := Real.log (16 / 3) / π ^ 2

/-- `limsup T_c ≤ τ` with well-posedness: for every `ε > 0`, eventually `T_c ≤ τ + ε`. -/
def TraceLimsup (τ : ℝ) : Prop := ∀ ε > 0, TraceBound (τ + ε)

/-- `Θ ≤ Θ₀`. -/
theorem thetaSharp_le_thetaCons : thetaSharp ≤ thetaCons := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h3' : 4 * √3 ≤ 9 := by nlinarith [Real.sqrt_nonneg 3]
  unfold thetaSharp thetaCons
  gcongr
  linarith

/-- `Θ₀ < 9/50`. -/
theorem thetaCons_lt : thetaCons < 9 / 50 := by
  have hπ := Real.pi_gt_d2
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 77 / 100 by norm_num)
  have hexp : (16 : ℝ) / 3 < Real.exp (177 / 100) := by
    have e : Real.exp (177 / 100) = Real.exp 1 * Real.exp (77 / 100) := by rw [← Real.exp_add]; norm_num
    rw [e]
    nlinarith [Real.exp_pos (77 / 100)]
  have hlog : Real.log (16 / 3) < 177 / 100 := (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp
  unfold thetaCons
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- The trace limit from `limsup T_c ≤ τ` with `τ < 9/50`. -/
theorem traceLimit_of_limsup {τ : ℝ} (hτ : τ < 9 / 50) (h : TraceLimsup τ) : TraceLimit := by
  have := h (9 / 50 - τ) (by linarith)
  rwa [add_sub_cancel] at this

/-- The trace limit from `limsup T_c ≤ Θ₀`. -/
theorem traceLimit_of_thetaCons (h : TraceLimsup thetaCons) : TraceLimit :=
  traceLimit_of_limsup thetaCons_lt h

end Cvs.Route.Visibility.VisibilityLandauTransition

end
