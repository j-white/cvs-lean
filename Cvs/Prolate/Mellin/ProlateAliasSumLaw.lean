import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.CentreValueAliasSum
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RightEdgeAliasLaw
import Cvs.Prolate.Mellin.RightEdgeIntegralPart
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The alias sum law rung by rung

For any `F`, `S_F(ζ) = (1/x)Σ_{n ≤ x} F((n/x)ζ) − ∫_0^1 F(tζ)dt − (F(ζ) − F(0))/(2x)` is the trapezoid error of
`t ↦ F(tζ)` on `[0, 1]`; it is linear in `F`, and the alias sum of rung `j` is `S_{H_{4j}} − α_jS_{H₀}`. So the
law `g‖T_{S_{H_k}}(σ + ig)‖ ≤ C(x)|h_k(1)|/√x` for each single prolate profile `H_k` gives `AliasSumLaw`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex
open Cvs.Prolate.RungProfileEntireExtension (GC)
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.EvenRungsByIndex (rung)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)

namespace Cvs.Prolate.Mellin.ProlateAliasSumLaw
open Cvs.ZeroCounting

/-- The trapezoid error `S_F(ζ) = (1/x)Σ_{n ≤ x} F((n/x)ζ) − ∫_0^1 F(tζ)dt − (F(ζ) − F(0))/(2x)`. -/
def trapErr (x : ℕ) (F : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  1 / x * ∑ n ∈ Finset.Icc 1 x, F (n / x * ζ) - (∫ t in (0 : ℝ)..1, F (t * ζ)) - (F ζ - F 0) / (2 * x)

/-- The alias sum of rung `j` is the trapezoid error of its profile. -/
theorem aliasSum_eq_trapErr (x j : ℕ) : Cvs.Prolate.Mellin.CentreValueAliasSum.aliasSum x j = trapErr x (GC x j) := by
  funext ζ
  unfold Cvs.Prolate.Mellin.CentreValueAliasSum.aliasSum Cvs.Prolate.Mellin.RightEdgeAliasLaw.aliasQ Cvs.Prolate.Mellin.RayTransformEdgeSum.edgeSum Cvs.Prolate.Mellin.RightEdgeIntegralPart.intG trapErr
  ring

/-- `t ↦ F(tζ)` is interval integrable for continuous `F`. -/
theorem intervalIntegrable_comp {F : ℂ → ℂ} (hF : Continuous F) (ζ : ℂ) :
    IntervalIntegrable (fun t : ℝ => F (t * ζ)) volume 0 1 :=
  (hF.comp (by fun_prop)).intervalIntegrable _ _

/-- **The trapezoid error is linear**: `S_{F₁ − aF₂} = S_{F₁} − aS_{F₂}` for continuous `F₁`, `F₂`. -/
theorem trapErr_sub_smul (x : ℕ) {F₁ F₂ : ℂ → ℂ} (h₁ : Continuous F₁) (h₂ : Continuous F₂) (a : ℂ) (ζ : ℂ) :
    trapErr x (fun z => F₁ z - a * F₂ z) ζ = trapErr x F₁ ζ - a * trapErr x F₂ ζ := by
  unfold trapErr
  rw [intervalIntegral.integral_sub (intervalIntegrable_comp h₁ ζ)
    ((intervalIntegrable_comp h₂ ζ).const_mul a), intervalIntegral.integral_const_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The trapezoid error of a continuous function is continuous. -/
theorem continuous_trapErr (x : ℕ) {F : ℂ → ℂ} (hF : Continuous F) : Continuous (trapErr x F) := by
  unfold trapErr
  have hI : Continuous fun ζ : ℂ => ∫ t in (0 : ℝ)..1, F (t * ζ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (ζ : ℂ) (t : ℝ) => F (t * ζ)) (hF.comp (by fun_prop)) 0 1
  have hS : Continuous fun ζ : ℂ => ∑ n ∈ Finset.Icc 1 x, F (n / x * ζ) :=
    continuous_finsetSum _ fun n _ => hF.comp (by fun_prop)
  exact ((continuous_const.mul hS).sub hI).sub ((hF.sub continuous_const).div_const _)

/-- **The ray transform is linear**: `T_{F₁ − aF₂} = T_{F₁} − aT_{F₂}` on `Im w > 0` for continuous `F₁`, `F₂`. -/
theorem rayT_sub_smul {F₁ F₂ : ℂ → ℂ} (h₁ : Continuous F₁) (h₂ : Continuous F₂) (a : ℂ) {w : ℂ}
    (hw : 0 < w.im) : rayT (fun z => F₁ z - a * F₂ z) w = rayT F₁ w - a * rayT F₂ w := by
  unfold rayT
  rw [← integral_const_mul, ← integral_sub (Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand h₁ hw)
    ((Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand h₂ hw).const_mul a)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

/-- **The alias sum splits rung by rung**: `S_{G_j} = S_{H_{4j}} − α_jS_{H₀}`. -/
theorem aliasSum_eq_sub {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) :
    Cvs.Prolate.Mellin.CentreValueAliasSum.aliasSum x j = fun ζ => trapErr x (Hk (2 * π * x) (2 * j)) ζ
      - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * trapErr x (Hk (2 * π * x) 0) ζ := by
  obtain ⟨hA1, -, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  obtain ⟨hA0, -, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data (j := 0) hx (by omega)
  simp only [mul_zero] at hA0
  rw [aliasSum_eq_trapErr, Cvs.Prolate.Mellin.RungUnitCircleLaw.GC_eq]
  funext ζ
  exact trapErr_sub_smul x (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA1).continuous
    (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA0).continuous _ ζ

/-- **The alias law for a single prolate profile**: some subpolynomial `C` has, at all large `x`, for every
`j < x`, `|σ| ≤ 1` and `g ≥ 8πx`, `g‖T_{S_{H_{4j}}}(σ + ig)‖ ≤ C(x)|h_{4j}(1)|/√x`. -/
def ProlateAliasLaw : Prop :=
  ∃ C : ℕ → ℝ, SubPoly C ∧ ∀ᶠ x : ℕ in atTop, ∀ j : ℕ, j < x → ∀ σ : ℝ, |σ| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
    g * ‖rayT (trapErr x (Hk (2 * π * x) (2 * j))) (σ + g * I)‖
      ≤ C x * |rung (2 * π * x) (2 * j) 1| / √(x : ℝ)

/-- **The single-profile law gives the alias sum law**. -/
theorem aliasSumLaw_of_prolateAliasLaw (h : ProlateAliasLaw) : Cvs.Prolate.Mellin.CentreValueAliasSum.AliasSumLaw := by
  obtain ⟨C, hC, hL⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hL, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hLx hx j σ hσ g hg
  have hj : (j : ℕ) < x := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.zero_le _) hj
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx0
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hwi : 0 < ((σ : ℂ) + g * I).im := by simp [hg0]
  obtain ⟨hA1, -, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  obtain ⟨hA0, -, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data (j := 0) hx hx0
  simp only [mul_zero] at hA0
  have c1 := continuous_trapErr x (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA1).continuous
  have c0 := continuous_trapErr x (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA0).continuous
  have L1 := hLx j hj σ hσ g hg
  have L0 := hLx 0 hx0 σ hσ g hg
  simp only [mul_zero] at L0
  set α := Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j
  set T1 := rayT (trapErr x (Hk (2 * π * x) (2 * j))) (σ + g * I)
  set T0 := rayT (trapErr x (Hk (2 * π * x) 0)) (σ + g * I)
  have e : rayT (Cvs.Prolate.Mellin.CentreValueAliasSum.aliasSum x j) (σ + g * I) = T1 - (α : ℂ) * T0 := by
    rw [aliasSum_eq_sub hx hj]
    exact rayT_sub_smul c1 c0 _ hwi
  rw [e]
  calc g * ‖T1 - (α : ℂ) * T0‖ ≤ g * ‖T1‖ + |α| * (g * ‖T0‖) := by
        rw [mul_left_comm, ← mul_add]
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hg0.le
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ C x * |rung (2 * π * x) (2 * j) 1| / √(x : ℝ)
          + |α| * (C x * |rung (2 * π * x) 0 1| / √(x : ℝ)) := by gcongr
    _ = C x * Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE x j / √(x : ℝ) := by unfold Cvs.Prolate.Mellin.RungWindowLawRightEdge.edgeE; ring

/-- **The single-profile law gives the right-edge law**. -/
theorem edgeLawSum_of_prolateAliasLaw (h : ProlateAliasLaw) : Cvs.Prolate.Mellin.RungWindowLawRightEdge.EdgeLawSum :=
  Cvs.Prolate.Mellin.CentreValueAliasSum.edgeLawSum_iff_aliasSumLaw.2 (aliasSumLaw_of_prolateAliasLaw h)

end Cvs.Prolate.Mellin.ProlateAliasSumLaw

end
