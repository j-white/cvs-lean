import Mathlib
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FirstAliasEdgeScale
import Cvs.Prolate.Mellin.HigherAliasRayTransforms
import Cvs.Prolate.Mellin.ProlateAliasSumLaw
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RungProfileOutsideCircle
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trapezoid error of one rung profile on the far lines

The alias series of Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries splits into the first alias (Cvs.Prolate.Mellin.FirstAliasEdgeScale) and the rest (Cvs.Prolate.Mellin.HigherAliasRayTransforms): for `|σ| ≤ 1`, `g ≥ 8πx`,
`y₀ ∈ (0, 1]`, `g|T_{S_{H_{4j}}}(σ + ig)| ≤ 4e⁶|h_{4j}(1)|(|μ_{4j}| + 2/(g − c)) + gΩ_{4j}/(g − c)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev IsLevelIdx)

namespace Cvs.Prolate.Mellin.TrapezoidErrorFarLines
open Cvs.ZeroCounting

/-- The alias constant of the profile `H_k` at `c = 2πx` and `y₀`. -/
def omegaK (x k : ℕ) (y₀ : ℝ) : ℝ :=
  Cvs.Prolate.Mellin.HigherAliasRayTransforms.omega (2 * π * x) (√(|rung (2 * π * x) k 1| * (Real.exp 1 * (Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk (2 * π * x) k
      + |rung (2 * π * x) k 1|))))
    (√((2 * π * x) ^ 2 * |rung (2 * π * x) k 1| * (Real.exp 1 * ((2 * π * x) * Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk (2 * π * x) k
      + (2 * π * x) ^ 2 * |rung (2 * π * x) k 1|)))) y₀

theorem lev_lt {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) : lev (2 * π * x) (2 * j) < (2 * π * x) ^ 2 := by
  have h1 := Cvs.L2a.FullSpanIndexFloor.full_index x hx hj
  have hsl := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (by linarith : 1 < 2 * π * (x : ℝ))
  linarith [h1.2]

/-- **The trapezoid error of one profile**. -/
theorem g_norm_rayT_trapErr_le {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {σ : ℝ} (hσ : |σ| ≤ 1) {g : ℝ}
    (hg : 8 * π * x ≤ g) {y₀ : ℝ} (hy₀ : 0 < y₀) (hy₁ : y₀ ≤ 1) :
    g * ‖rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk (2 * π * x) (2 * j))) (σ + g * I)‖
      ≤ 4 * Real.exp 6 * |rung (2 * π * x) (2 * j) 1| * (|muR (2 * π * x) (2 * j)| + 2 / (g - 2 * π * x))
        + g * (omegaK x (2 * j) y₀ / (g - 2 * π * x)) := by
  set c := 2 * π * (x : ℝ) with hcd
  obtain ⟨h1, hμ, hχ'⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  have hχ := lev_lt hx hj
  have hc0 : 0 < c := by linarith
  have hgc : c < g := by nlinarith [Real.pi_pos]
  have hg0 : 0 < g := hc0.trans hgc
  set w : ℂ := σ + g * I with hwd
  have hwim : w.im = g := by simp [hwd]
  have hw0 : 0 < w.im := by rw [hwim]; exact hg0
  have hS := Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries.hasSum_aliasTerm hx hj hw0
  set a := Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries.aliasTerm x j w with had
  -- the first alias
  have hfirst : ‖a 0‖ ≤ 4 * Real.exp 6 * |rung c (2 * j) 1| * (|muR c (2 * j)| + 2 / (g - c)) / g := by
    rw [had, Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries.aliasTerm_eq_rayT hx hj hw0 0, le_div_iff₀ hg0, mul_comm]
    have := Cvs.Prolate.Mellin.FirstAliasEdgeScale.g_norm_rayT_first_le hx hj hσ hg
    have e : (fun ζ => ∫ t in (-1 : ℝ)..1, Hk (2 * π * x) (2 * j) (t * ζ)
        * Complex.cos (2 * π * x * (((0 : ℕ) : ℂ) + 1) * t))
        = fun ζ => ∫ t in (-1 : ℝ)..1, Hk (2 * π * x) (2 * j) (t * ζ) * Complex.cos ((2 * π * x : ℝ) * t) := by
      funext ζ; refine intervalIntegral.integral_congr fun t _ => ?_
      refine congrArg (fun u => Hk (2 * π * x) (2 * j) (t * ζ) * Complex.cos u) ?_
      push_cast; ring
    rw [e]; exact this
  -- the rest
  have hrest : ∀ N : ℕ, ∑ m ∈ Finset.range N, ‖a (m + 1)‖ ≤ omegaK x (2 * j) y₀ / (g - c) := fun N => by
    have := Cvs.Prolate.Mellin.HigherAliasRayTransforms.sum_norm_rayT_tail_le hc0 h1 hχ hχ' hμ (w := w) (by rw [hwim]; exact hgc) hy₀ hy₁ N
    rw [hwim] at this
    refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_) this
    rw [had, Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries.aliasTerm_eq_rayT hx hj hw0 (m + 1)]
    unfold Cvs.Prolate.Mellin.HigherAliasRayTransforms.tailF
    refine congrArg (fun F => ‖rayT F w‖) (funext fun ζ => intervalIntegral.integral_congr fun t _ => ?_)
    refine congrArg (fun u => Hk (2 * π * x) (2 * j) (t * ζ) * Complex.cos u) ?_
    push_cast; ring
  have hbound : ∀ N : ℕ, ∑ m ∈ Finset.range N, ‖a m‖
      ≤ 4 * Real.exp 6 * |rung c (2 * j) 1| * (|muR c (2 * j)| + 2 / (g - c)) / g
        + omegaK x (2 * j) y₀ / (g - c) := fun N => by
    rcases N with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty]
      have h0 : 0 ≤ omegaK x (2 * j) y₀ := by
        unfold omegaK
        exact Cvs.Prolate.Mellin.HigherAliasRayTransforms.omega_nonneg hc0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hy₀ hy₁
      have : 0 ≤ 4 * Real.exp 6 * |rung c (2 * j) 1| * (|muR c (2 * j)| + 2 / (g - c)) / g := by
        have : 0 < g - c := by linarith
        positivity
      have : 0 ≤ omegaK x (2 * j) y₀ / (g - c) := div_nonneg h0 (by linarith)
      linarith
    · rw [Finset.sum_range_succ']
      linarith [hrest N, hfirst]
  have hnorm := Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries.norm_le_of_hasSum hS hbound
  calc g * ‖rayT (Cvs.Prolate.Mellin.ProlateAliasSumLaw.trapErr x (Hk c (2 * j))) w‖
      ≤ g * (4 * Real.exp 6 * |rung c (2 * j) 1| * (|muR c (2 * j)| + 2 / (g - c)) / g
        + omegaK x (2 * j) y₀ / (g - c)) := mul_le_mul_of_nonneg_left hnorm hg0.le
    _ = _ := by field_simp

end Cvs.Prolate.Mellin.TrapezoidErrorFarLines

end
