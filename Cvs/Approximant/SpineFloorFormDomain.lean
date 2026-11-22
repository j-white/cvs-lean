import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `D₀` spine floor on the form domain at `L = log x`

`‖spineMap x a‖²` is the window energy `∫ window(1/x)(G_a)²`, so `FullSpanReciprocalContraction`'s full-span `D₀` floor reads
`b_D(x)‖spineMap x a‖² ≤ Q(spineMap x a)` for every coefficient vector `a` vanishing on `j < 2`.
-/

noncomputable section

open MeasureTheory Real Set

namespace Cvs.Approximant.SpineFloorFormDomain

open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Approximant.DeepIndexSpineSpan (spineG)
open Cvs.L2a.WindowChainInputsProlate (c0W)

/-- **The spine class has the window energy as squared norm**: `‖spineMap x a‖² = ∫ window(1/x)(G_a)²`. -/
theorem norm_spineMap_sq (x : ℕ) (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ‖Cvs.Approximant.SpineSubspace.spineMap x a‖ ^ 2
      = ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2 := by
  have hx0 : (0 : ℝ) < x := by
    have : (0 : ℝ) < 2 * π * x := by linarith
    nlinarith [Real.pi_pos]
  set W := Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) with hW
  have ha : 0 < 2 * π / (2 * π * x) := by positivity
  have hn : ∀ v : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      ‖v‖ = ‖((v : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))‖ := fun v => rfl
  have hc : ‖((Cvs.Approximant.SpineSubspace.spineMap x a : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) : Lp ℝ 2 (volume : Measure ℝ))‖ ^ 2
      = ∫ s, Cvs.Approximant.SpineSubspace.kG x a s ^ 2 := by
    rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
    exact integral_congr_ae ((Cvs.Approximant.SpineSubspace.coe_spineMap_ae x hx a).mono fun s hs => by simp only []; rw [hs])
  rw [hn, hc]
  have hk : ∀ s, Cvs.Approximant.SpineSubspace.kG x a s = Cvs.L2a.TailLogScaleTest.logScale W (s - Real.log x) := fun s => rfl
  simp_rw [hk]
  rw [integral_sub_right_eq_self (fun s => Cvs.L2a.TailLogScaleTest.logScale W s ^ 2) (Real.log x)]
  have h1 : ∫ s, Cvs.L2a.TailLogScaleTest.logScale W s ^ 2 = ∫ θ in Ioi (0 : ℝ), W θ ^ 2 := by
    have h := Cvs.WeilForm.ThetaFormWindowIdentification.selfConvolution_logScale_log W (k := 1) one_pos
    simp only [Cvs.Zeta.Explicit.Weil.selfConvolution, Real.log_one, add_zero, Real.sqrt_one,
      one_mul] at h
    simpa [sq] using h
  have h2 : ∫ θ in Ioi (0 : ℝ), W θ ^ 2 = ∫ θ, W θ ^ 2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun θ hθ => ?_
    have hn : θ ∉ Icc (2 * π / (2 * π * x)) 1 := fun h => hθ (ha.trans_le h.1)
    rw [hW, Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hn]; ring
  rw [h1, h2]

end Cvs.Approximant.SpineFloorFormDomain
