import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Cvs.Upstream.ForcedOscillatorEnergy
import Cvs.Upstream.SqrtGrowthLaw

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The error of an approximant with the integrand continuous on the interval

The integrated growth law of Cvs.Upstream.SqrtGrowthLaw and the error bound of an earlier result hold with the forcing continuous on `[x₀, x₁]` only:
extend it by `IccExtend`, which is continuous and agrees with it on the interval. This admits the layer amplitude,
whose `a = P̃f_s` vanishes at the edge `s = 0`.
-/

namespace Cvs.Prolate.LiouvilleGreen.ApproximantErrorContinuous

open Real Set MeasureTheory intervalIntegral Cvs.Upstream.ForcedOscillatorEnergy Cvs.Upstream.SqrtGrowthLaw

/-- **`√Z` grows by at most `∫f`**, with `f` continuous on `[x₀, x₁]`. -/
theorem sqrt_le_add_integral_on {Z Z' f : ℝ → ℝ} {x₀ x₁ : ℝ} (hx : x₀ ≤ x₁) (hZ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ Z x)
    (hZ : ∀ x ∈ Icc x₀ x₁, HasDerivAt Z (Z' x) x) (hf0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ f x)
    (hfc : ContinuousOn f (Icc x₀ x₁)) (hle : ∀ x ∈ Icc x₀ x₁, Z' x ≤ 2 * √(Z x) * f x) :
    √(Z x₁) ≤ √(Z x₀) + ∫ x in x₀..x₁, f x := by
  set g : ℝ → ℝ := IccExtend hx (fun y : Icc x₀ x₁ => f y) with hg
  have hgf : ∀ x ∈ Icc x₀ x₁, g x = f x := fun x hx' => by rw [hg, IccExtend_of_mem _ _ hx']
  have hgc : Continuous g := continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_restrict.mp hfc)
  have h := sqrt_le_add_integral hx hZ0 hZ (fun x hx' => (hgf x hx').symm ▸ hf0 x hx') hgc
    (fun x hx' => (hgf x hx').symm ▸ hle x hx')
  have hint : ∫ x in x₀..x₁, g x = ∫ x in x₀..x₁, f x :=
    intervalIntegral.integral_congr fun x hx' => hgf x (by rwa [uIcc_of_le hx] at hx')
  rwa [hint] at h

/-- **The error of an approximant from its residual**, with the integrand continuous on the interval only. -/
theorem abs_error_le_on {ψ uψ g gp r a a' P Q : ℝ → ℝ} {c₀ x₀ x₁ : ℝ} (hx : x₀ ≤ x₁)
    (hψ : ∀ x ∈ Icc x₀ x₁, HasDerivAt ψ (uψ x / P x) x) (huψ : ∀ x ∈ Icc x₀ x₁, HasDerivAt uψ (-(Q x * ψ x)) x)
    (hg : ∀ x ∈ Icc x₀ x₁, HasDerivAt g (gp x / P x) x) (hgp : ∀ x ∈ Icc x₀ x₁, HasDerivAt gp (r x - Q x * g x) x)
    (ha : ∀ x ∈ Icc x₀ x₁, HasDerivAt a (a' x) x) (ha0 : ∀ x ∈ Icc x₀ x₁, 0 < a x)
    (ha' : ∀ x ∈ Icc x₀ x₁, 0 ≤ a' x) (hP0 : ∀ x ∈ Icc x₀ x₁, P x ≠ 0)
    (haPQ : ∀ x ∈ Icc x₀ x₁, a x ^ 2 = P x * Q x)
    (hfc : ContinuousOn (fun x => |c₀ * r x| / a x) (Icc x₀ x₁)) :
    |ψ x₁ - c₀ * g x₁|
      ≤ √((ψ x₀ - c₀ * g x₀) ^ 2 + (uψ x₀ - c₀ * gp x₀) ^ 2 / a x₀ ^ 2) + ∫ x in x₀..x₁, |c₀ * r x| / a x := by
  set e : ℝ → ℝ := fun x => ψ x - c₀ * g x
  set u : ℝ → ℝ := fun x => uψ x - c₀ * gp x
  set Z : ℝ → ℝ := fun x => e x ^ 2 + u x ^ 2 / a x ^ 2 with hZd
  have he : ∀ x ∈ Icc x₀ x₁, HasDerivAt e (u x / P x) x := fun x hx' => by
    have := (hψ x hx').sub ((hg x hx').const_mul c₀)
    refine this.congr_deriv ?_
    simp only [u]; field_simp [hP0 x hx']
  have hu : ∀ x ∈ Icc x₀ x₁, HasDerivAt u (-(Q x * e x) + (-(c₀ * r x))) x := fun x hx' => by
    have := (huψ x hx').sub ((hgp x hx').const_mul c₀)
    refine this.congr_deriv ?_
    simp only [e]; ring
  have hZ : ∀ x ∈ Icc x₀ x₁, HasDerivAt Z
      (2 * u x * (-(c₀ * r x)) / a x ^ 2 - 2 * u x ^ 2 * a' x / a x ^ 3) x := fun x hx' =>
    hasDerivAt_normEnergy (F := fun x => -(c₀ * r x)) (he x hx') (hu x hx') (ha x hx') (ha0 x hx').ne'
      (hP0 x hx') rfl rfl (haPQ x hx')
  have hZ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ Z x := fun x hx' => by simp only [hZd]; positivity
  have hle : ∀ x ∈ Icc x₀ x₁, 2 * u x * (-(c₀ * r x)) / a x ^ 2 - 2 * u x ^ 2 * a' x / a x ^ 3
      ≤ 2 * √(Z x) * (|c₀ * r x| / a x) := fun x hx' => by
    have hbase := normEnergy_deriv_le (u := u x) (F := -(c₀ * r x)) (Z := Z x) (ha0 x hx') (ha' x hx')
      (by simp only [hZd]; nlinarith [sq_nonneg (e x)])
    rw [abs_neg] at hbase
    calc _ ≤ 2 * √(Z x) * |c₀ * r x| / a x := hbase
      _ = 2 * √(Z x) * (|c₀ * r x| / a x) := by ring
  have hmain := sqrt_le_add_integral_on hx hZ0 hZ (fun x hx' => div_nonneg (abs_nonneg _) (ha0 x hx').le) hfc hle
  have he1 : |e x₁| ≤ √(Z x₁) := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    simp only [hZd]
    have : 0 ≤ u x₁ ^ 2 / a x₁ ^ 2 := by positivity
    linarith
  exact he1.trans hmain

end Cvs.Prolate.LiouvilleGreen.ApproximantErrorContinuous
