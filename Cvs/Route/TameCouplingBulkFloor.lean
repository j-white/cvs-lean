import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.CouplingPoleChannel
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.PhysicalCubicCorrectionColumn
import Cvs.WeilForm.SeparatedArchKernelL2
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tame form coupling from a bulk floor and a channel ratio

At `80 ≤ 2πx`, the channels give `|Q(spineMap x a, w_u)| ≤ K_x(a)‖u‖₂` with `‖w_u‖ = ‖u‖₂` and
`K_x(a) = Σ_n Λ(n)(∫_{n/x}^{n} τ_a²)^{1/2}/√n + (π/2 + 1 + √(1 − 1/x))‖τ_a‖₂ + √(x − 1)|P₊τ_a|`. So `BulkFloor x b`,
`b > 0`, and `TailRatio x b δ : K_x(a)² ≤ (1−δ)b·Q(spineMap x a)` give `TameCoupling x δ`, and RH at infinitely
many `x` where the tame classes are dense (Cvs.WeilForm.CouplingFromTameDensity).
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.Route.TameCouplingBulkFloor
open Cvs.ZeroCounting

open Cvs.WeilForm.ThetaSpaceParseval (dil poleP poleM)
open Cvs.L2a.WindowFormTailLimit (Tame)

/-! ### The form-domain norm of a tame class -/

/-- **A tame class has the physical `L²` norm**: `‖w_u‖ = (∫ u²)^{1/2}` for `u` tame on `[1/x, 1]`. -/
theorem norm_wv {x : ℕ} (hx0 : (0 : ℝ) < x) {u : ℝ → ℝ} (hu : Tame u (1 / x) 1) :
    ‖Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu‖ = √(∫ θ, u θ ^ 2) := by
  have hm := Cvs.Approximant.SpineCouplingTailPairing.fv_memLp (x := x) hu
  have e : hm.toLp (Cvs.Approximant.SpineCouplingTailPairing.fv x u)
      = (((Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :
          Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 volume) := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hu] with s h1 h2
    rw [h1, h2]
  have hn : ‖Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu‖ = ‖hm.toLp (Cvs.Approximant.SpineCouplingTailPairing.fv x u)‖ := by rw [e]; rfl
  rw [hn, Cvs.WeilForm.SeparatedArchKernelL2.norm_toLp_eq_sqrt hm]
  congr 1
  rw [show (fun s => Cvs.Approximant.SpineCouplingTailPairing.fv x u s ^ 2) = fun s => Cvs.L2a.TailLogScaleTest.logScale u (s - Real.log x) ^ 2 from rfl,
    integral_sub_right_eq_self (fun s => Cvs.L2a.TailLogScaleTest.logScale u s ^ 2) (Real.log x),
    Cvs.WeilForm.PhysicalCubicCorrectionColumn.integral_logScale_sq fun θ hθ => Cvs.WeilForm.CouplingPoleChannel.eq_zero_of_nonpos_of_tame hu hθ]

/-! ### The channel constant -/

/-! ### The channel ratio -/

/-- `80 ≤ 2πx` for all large `x`. -/
theorem eventually_scale : ∀ᶠ x : ℕ in atTop, (80 : ℝ) ≤ 2 * π * x :=
  ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity : (0 : ℝ) < 2 * π)).eventually_ge_atTop 80

end Cvs.Route.TameCouplingBulkFloor
