import Mathlib
import Cvs.L2a.WindowFormTailLimit
import Cvs.StepA.OffLineHyperbolicMellin
import Cvs.WeilForm.ThetaSpaceParseval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The inside function is a tame test, and the inside energy is its Weil form

Tame tests on `[a, 1]` are closed under differences and under a.e. change within the bounded measurable functions.
The inside function `I_a` of an earlier result is the odd window `W_a − R_{1/x}W_a` off `ℕ/x`, so it is tame and `2o_a = w_{I_a}`:
`Q(2o_a) = weilθ(I_a, I_a) = Σ_ρ m_ρ Re(M[I_a](1 − ρ) M[I_a](ρ)) = −2 weilθ(τ̃_a, I_a)`, `τ̃_a` the regularised tail.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace Cvs.WeilForm.InsideFunctionTame

open Cvs.WeilForm.ThetaSpaceParseval (weilθ mellinR)
open Cvs.L2a.WindowFormTailLimit (Tame regProfile)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.AngularProlateTailPositive (psi)

/-! ### Tame test algebra -/

/-- The Mellin transform is additive on windowed tests: `M[v − w] = M[v] − M[w]`. -/
theorem mellinR_sub {v w : ℝ → ℝ} {a : ℝ} (hv : Cvs.StepA.OffLineHyperbolicMellin.Win v a) (hw : Cvs.StepA.OffLineHyperbolicMellin.Win w a) (s : ℂ) :
    mellinR (fun θ => v θ - w θ) s = mellinR v s - mellinR w s := by
  have h1 := Cvs.StepA.OffLineHyperbolicMellin.integrableOn_mul hv (Cvs.StepA.OffLineHyperbolicMellin.continuousOn_cpow hv.pos (s - 1))
  have h2 := Cvs.StepA.OffLineHyperbolicMellin.integrableOn_mul hw (Cvs.StepA.OffLineHyperbolicMellin.continuousOn_cpow hw.pos (s - 1))
  unfold mellinR mellin
  simp only [smul_eq_mul]
  rw [← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ _ => ?_
  simp only [Complex.ofReal_sub]
  ring

/-- **Tame tests on `[a, 1]` are closed under differences.** -/
theorem tame_sub {v w : ℝ → ℝ} {a : ℝ} (hv : Tame v a 1) (hw : Tame w a 1) :
    Tame (fun θ => v θ - w θ) a 1 where
  pos := hv.pos
  supp θ hθ := by rw [hv.supp θ hθ, hw.supp θ hθ, sub_zero]
  meas := hv.meas.sub hw.meas
  bdd := by
    obtain ⟨M, hM⟩ := hv.bdd
    obtain ⟨N, hN⟩ := hw.bdd
    exact ⟨M + N, fun θ => (abs_sub _ _).trans (add_le_add (hM θ) (hN θ))⟩
  dec := by
    obtain ⟨C, hC⟩ := hv.dec
    obtain ⟨D, hD⟩ := hw.dec
    refine ⟨C + D, fun s h1 h2 h3 => ?_⟩
    rw [mellinR_sub (Cvs.StepA.OffLineHyperbolicMellin.win_of_tame hv) (Cvs.StepA.OffLineHyperbolicMellin.win_of_tame hw) s, add_div]
    exact (norm_sub_le _ _).trans (add_le_add (hC s h1 h2 h3) (hD s h1 h2 h3))

/-! ### The odd window and the inside function -/

/-! ### The inside energy as a Weil pairing -/

/-- `80 ≤ 2πx` forces `2 ≤ x`. -/
theorem two_le_of_scale {x : ℕ} (hx : 80 ≤ 2 * π * x) : 2 ≤ x := by
  by_contra h
  have : (x : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 (not_le.1 h)
  nlinarith [Real.pi_lt_four]

end Cvs.WeilForm.InsideFunctionTame
