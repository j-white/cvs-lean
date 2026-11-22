import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.SpineProfileWindowNormPos
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFormDeepSpan
import Cvs.L2a.WindowFullSpanProlate
import Cvs.Prolate.EvenRungsByIndex
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.EWindowReciprocalContraction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Full-span window floors from reciprocal contraction

The actual even spine profiles have window energy at most half their angular
energy. The full-span window budget is therefore one in both the D₀ and Rᴅ floors.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.L2a.FullSpanReciprocalContraction
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (lamR)
open Cvs.Approximant.DeepIndexSpineSpan (spineG)
open Cvs.L2a.WindowChainInputsProlate (c0W)

/-- Reciprocal contraction gives the full-span floor with window budget one. -/
theorem L2a_window_full_of (x : ℕ) (hx : c0W ≤ 2 * π * x) {S : Finset ℕ}
    (hS : ∀ j ∈ S, j < x) {k : ℕ} (hk : 1 ≤ k) (hSk : ∀ j ∈ S, k ≤ j) (a : S → ℝ) :
    π / (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) (2 * k))
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) := by
  have hc80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  obtain ⟨_, _, _, _, _, heven, _⟩ := Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hc80 hS a
  have hwindow := Cvs.Xi.EWindowReciprocalContraction.integral_window_sq_le_half
    (a := 2 * π / (2 * π * x)) (by positivity)
    (Cvs.L2a.SpineProfileWindowNormPos.continuousOn_spineG (2 * π * x) a) heven
  have h := Cvs.L2a.WindowFullSpanProlate.L2a_window_full_budget_of (H := 1) x hx hS hk hSk a
    (by norm_num) hwindow
  simpa only [mul_one] using h

/-- The full Rᴅ span has the positive `1 − λ₄` window floor at budget one. -/
theorem L2a_window_full_RD (x : ℕ) (hx : c0W ≤ 2 * π * x)
    (a : ((Finset.range x).filter (1 ≤ ·)) → ℝ) :
    π / (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 2)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) :=
  L2a_window_full_of x hx (fun _ hj => Finset.mem_range.1 (Finset.mem_filter.1 hj).1)
    (k := 1) le_rfl (fun _ hj => (Finset.mem_filter.1 hj).2) a

/-- Both budget-one full-span floor coefficients are strictly positive past the window threshold. -/
theorem full_factors_pos (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    0 < π / (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 4) ∧
      0 < π / (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 2) := by
  have hc80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hc2π : 2 * π ≤ 2 * π * (x : ℝ) := by linarith [Real.pi_lt_four]
  have hH := Cvs.L2a.WindowFormDeepSpan.Hx_pos hc2π
  obtain ⟨hD0, hRD⟩ := Cvs.L2a.WindowFullSpanProlate.full_factors_pos x hx
  have hcancel (d : ℝ) :
      Cvs.L2a.WindowFormDeepSpan.Hx (2 * π * x) *
          (π / (8 * (2 * π * x) * Cvs.L2a.WindowFormDeepSpan.Hx (2 * π * x)
            * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0))) * d)
        = π / (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0))) * d := by
    rw [show 8 * (2 * π * x) * Cvs.L2a.WindowFormDeepSpan.Hx (2 * π * x)
        * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0))
      = Cvs.L2a.WindowFormDeepSpan.Hx (2 * π * x) *
          (8 * (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0))) by ring]
    rw [← mul_assoc, ← mul_div_assoc, mul_div_mul_left _ _ hH.ne']
  constructor
  · rw [← hcancel (1 - lamR (2 * π * x) 4)]
    exact mul_pos hH hD0
  · rw [← hcancel (1 - lamR (2 * π * x) 2)]
    exact mul_pos hH hRD

end Cvs.L2a.FullSpanReciprocalContraction
