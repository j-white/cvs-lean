import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Cvs.Upstream.ForcedOscillatorLiouvilleEnergy
import Cvs.Upstream.SqrtGrowthLawLinear

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The error of a forced oscillator through the corrected Liouville energy

For `e′ = u/P`, `u′ = −Qe + F`, `a² = PQ`, `a > 0` and `k = a′/Q` with `|k| < 2` on `[x₀, x₁]`, Cvs.Upstream.ForcedOscillatorLiouvilleEnergy and Cvs.Upstream.SqrtGrowthLawLinear give
`|e(x₁)| ≤ e^{B(x₁)}(√((1 + |k(x₀)|/2)E(x₀)) + ∫γe^{−B})/√(d(x₁)a(x₁))`, with `E = ae² + u²/a`, `d = 1 − |k|/2`,
`β = |k′|/(4d)`, `γ = |F|(|k| + 2)/(2√(da))`, `B = ∫β`: the error follows the envelope `1/√a`.
-/

namespace Cvs.Upstream.ForcedOscillatorError

open Real Set MeasureTheory intervalIntegral Cvs.Upstream.ForcedOscillatorLiouvilleEnergy Cvs.Upstream.SqrtGrowthLawLinear

/-- **Cvs.Upstream.SqrtGrowthLawLinear with `β`, `γ` continuous on the interval only.** -/
theorem sqrt_le_exp_mul_on {Z Z' β γ : ℝ → ℝ} {x₀ x₁ : ℝ} (hx : x₀ ≤ x₁) (hZ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ Z x)
    (hZ : ∀ x ∈ Icc x₀ x₁, HasDerivAt Z (Z' x) x) (hβ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ β x)
    (hγ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ γ x) (hβc : ContinuousOn β (Icc x₀ x₁)) (hγc : ContinuousOn γ (Icc x₀ x₁))
    (hle : ∀ x ∈ Icc x₀ x₁, Z' x ≤ 2 * β x * Z x + 2 * γ x * √(Z x)) :
    √(Z x₁) ≤ exp (∫ t in x₀..x₁, β t)
      * (√(Z x₀) + ∫ x in x₀..x₁, γ x * exp (-∫ t in x₀..x, β t)) := by
  set β' : ℝ → ℝ := IccExtend hx (fun y : Icc x₀ x₁ => β y) with hβ'd
  set γ' : ℝ → ℝ := IccExtend hx (fun y : Icc x₀ x₁ => γ y) with hγ'd
  have hβe : ∀ x ∈ Icc x₀ x₁, β' x = β x := fun x hx' => by rw [hβ'd, IccExtend_of_mem _ _ hx']
  have hγe : ∀ x ∈ Icc x₀ x₁, γ' x = γ x := fun x hx' => by rw [hγ'd, IccExtend_of_mem _ _ hx']
  have hβ'c : Continuous β' := continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_restrict.mp hβc)
  have hγ'c : Continuous γ' := continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_restrict.mp hγc)
  have h := sqrt_le_exp_mul hx hZ0 hZ (fun x hx' => (hβe x hx').symm ▸ hβ0 x hx')
    (fun x hx' => (hγe x hx').symm ▸ hγ0 x hx') hβ'c hγ'c
    (fun x hx' => by rw [hβe x hx', hγe x hx']; exact hle x hx')
  have hBi : ∀ x ∈ Icc x₀ x₁, ∫ t in x₀..x, β' t = ∫ t in x₀..x, β t := fun x hx' =>
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hx'.1] at ht; exact hβe t ⟨ht.1, ht.2.trans hx'.2⟩
  have hGi : ∫ x in x₀..x₁, γ' x * exp (-∫ t in x₀..x, β' t) = ∫ x in x₀..x₁, γ x * exp (-∫ t in x₀..x, β t) :=
    intervalIntegral.integral_congr fun x hx' => by
      rw [uIcc_of_le hx] at hx'; rw [hγe x hx', hBi x hx']
  rwa [hBi x₁ ⟨hx, le_rfl⟩, hGi] at h

/-- **The error through the corrected Liouville energy.** -/
theorem abs_le_liouville {e u a a' k k' P Q F : ℝ → ℝ} {x₀ x₁ : ℝ} (hx : x₀ ≤ x₁)
    (he : ∀ x ∈ Icc x₀ x₁, HasDerivAt e (u x / P x) x)
    (hu : ∀ x ∈ Icc x₀ x₁, HasDerivAt u (-(Q x * e x) + F x) x)
    (ha : ∀ x ∈ Icc x₀ x₁, HasDerivAt a (a' x) x) (hk : ∀ x ∈ Icc x₀ x₁, HasDerivAt k (k' x) x)
    (ha0 : ∀ x ∈ Icc x₀ x₁, 0 < a x) (hP0 : ∀ x ∈ Icc x₀ x₁, P x ≠ 0)
    (haPQ : ∀ x ∈ Icc x₀ x₁, a x ^ 2 = P x * Q x) (hkx : ∀ x ∈ Icc x₀ x₁, k x = a' x / Q x)
    (hk2 : ∀ x ∈ Icc x₀ x₁, |k x| < 2)
    (hβc : ContinuousOn (fun x => |k' x| / (4 * (1 - |k x| / 2))) (Icc x₀ x₁))
    (hγc : ContinuousOn (fun x => |F x| * (|k x| + 2) / (2 * √((1 - |k x| / 2) * a x))) (Icc x₀ x₁)) :
    |e x₁| ≤ exp (∫ t in x₀..x₁, |k' t| / (4 * (1 - |k t| / 2)))
      * (√((1 + |k x₀| / 2) * (a x₀ * e x₀ ^ 2 + u x₀ ^ 2 / a x₀))
        + ∫ x in x₀..x₁, |F x| * (|k x| + 2) / (2 * √((1 - |k x| / 2) * a x))
          * exp (-∫ t in x₀..x, |k' t| / (4 * (1 - |k t| / 2))))
      / √((1 - |k x₁| / 2) * a x₁) := by
  set Et : ℝ → ℝ := fun x => a x * e x ^ 2 + u x ^ 2 / a x + k x * e x * u x with hEtd
  have hd : ∀ x ∈ Icc x₀ x₁, 0 < 1 - |k x| / 2 := fun x hx' => by linarith [hk2 x hx']
  have hEt0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ Et x := fun x hx' => by
    have h1 := mul_energy_le (e := e x) (u := u x) (k := k x) (ha0 x hx')
    have h2 : 0 ≤ a x * e x ^ 2 + u x ^ 2 / a x := by have := ha0 x hx'; positivity
    have h3 := hd x hx'
    simp only [hEtd]; nlinarith
  have hEt : ∀ x ∈ Icc x₀ x₁, HasDerivAt Et (2 * u x * F x / a x + k' x * e x * u x + k x * e x * F x) x :=
    fun x hx' => hasDerivAt_liouvilleEnergy (he x hx') (hu x hx') (ha x hx') (hk x hx') (ha0 x hx').ne'
      (hP0 x hx') rfl rfl (haPQ x hx') (hkx x hx')
  have hmain := sqrt_le_exp_mul_on hx hEt0 hEt
    (fun x hx' => div_nonneg (abs_nonneg _) (by have := hd x hx'; positivity))
    (fun x hx' => div_nonneg (mul_nonneg (abs_nonneg _) (by positivity)) (by positivity)) hβc hγc
    (fun x hx' => by
      have h := liouville_deriv_le (e := e x) (u := u x) (k' := k' x) (F := F x) (ha0 x hx') (hk2 x hx')
      have hd' := hd x hx'
      have ha' := ha0 x hx'
      have hs : √((a x * e x ^ 2 + u x ^ 2 / a x + k x * e x * u x) / ((1 - |k x| / 2) * a x))
          = √(Et x) / √((1 - |k x| / 2) * a x) := by
        rw [Real.sqrt_div' _ (by positivity)]
      rw [hs] at h
      have hsq : 0 < √((1 - |k x| / 2) * a x) := Real.sqrt_pos.mpr (by positivity)
      calc 2 * u x * F x / a x + k' x * e x * u x + k x * e x * F x
          ≤ |k' x| / (2 * (1 - |k x| / 2)) * Et x + |F x| * (|k x| + 2) * (√(Et x) / √((1 - |k x| / 2) * a x)) := h
        _ = 2 * (|k' x| / (4 * (1 - |k x| / 2))) * Et x
            + 2 * (|F x| * (|k x| + 2) / (2 * √((1 - |k x| / 2) * a x))) * √(Et x) := by
            field_simp; ring)
  -- initial energy and the final extraction of `|e|`
  have hx₀ : x₀ ∈ Icc x₀ x₁ := ⟨le_rfl, hx⟩
  have hx₁ : x₁ ∈ Icc x₀ x₁ := ⟨hx, le_rfl⟩
  have hinit : √(Et x₀) ≤ √((1 + |k x₀| / 2) * (a x₀ * e x₀ ^ 2 + u x₀ ^ 2 / a x₀)) := by
    apply Real.sqrt_le_sqrt
    have ha' := ha0 x₀ hx₀
    have hsq : 2 * |e x₀ * u x₀| ≤ a x₀ * e x₀ ^ 2 + u x₀ ^ 2 / a x₀ := by
      have h0 : 0 ≤ (a x₀ * |e x₀| - |u x₀|) ^ 2 / a x₀ := by positivity
      have e1 : (a x₀ * |e x₀| - |u x₀|) ^ 2 / a x₀ = a x₀ * e x₀ ^ 2 + u x₀ ^ 2 / a x₀ - 2 * |e x₀ * u x₀| := by
        rw [abs_mul]; field_simp
        rw [show (a x₀ * |e x₀| - |u x₀|) ^ 2 = a x₀ ^ 2 * |e x₀| ^ 2 + |u x₀| ^ 2 - a x₀ * |e x₀| * |u x₀| * 2
          by ring, sq_abs, sq_abs]
      linarith
    have hku : k x₀ * e x₀ * u x₀ ≤ |k x₀| * |e x₀ * u x₀| := by
      rw [← abs_mul, show k x₀ * e x₀ * u x₀ = k x₀ * (e x₀ * u x₀) by ring]; exact le_abs_self _
    have : |k x₀| * |e x₀ * u x₀| ≤ |k x₀| / 2 * (a x₀ * e x₀ ^ 2 + u x₀ ^ 2 / a x₀) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_nonneg (k x₀)]
    simp only [hEtd]; nlinarith
  have hfin : |e x₁| ≤ √(Et x₁) / √((1 - |k x₁| / 2) * a x₁) := by
    have ha' := ha0 x₁ hx₁
    have hd' := hd x₁ hx₁
    rw [← Real.sqrt_div' _ (by positivity)]
    apply Real.abs_le_sqrt
    rw [le_div_iff₀ (by positivity)]
    have h1 := mul_energy_le (e := e x₁) (u := u x₁) (k := k x₁) ha'
    have h2 : 0 ≤ u x₁ ^ 2 / a x₁ := by positivity
    have h3 : e x₁ ^ 2 * ((1 - |k x₁| / 2) * a x₁) ≤ (1 - |k x₁| / 2) * (a x₁ * e x₁ ^ 2 + u x₁ ^ 2 / a x₁) := by
      nlinarith
    simp only [hEtd]; linarith
  refine hfin.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  refine hmain.trans (mul_le_mul_of_nonneg_left (add_le_add hinit le_rfl) (exp_pos _).le)

end Cvs.Upstream.ForcedOscillatorError
