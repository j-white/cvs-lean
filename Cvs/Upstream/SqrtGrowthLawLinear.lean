import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A square-root growth law with a linear term

If `Z ≥ 0` has `Z′ ≤ 2βZ + 2γ√Z` on `[x₀, x₁]` with `β, γ ≥ 0` continuous, then with `B(x) = ∫_{x₀}^x β`,
`√Z(x₁) ≤ e^{B(x₁)}(√Z(x₀) + ∫_{x₀}^{x₁} γe^{−B})`: `√(Z + ε)e^{−B} − ∫γe^{−B}` is antitone, and `ε → 0`. This
integrates the corrected Liouville energy of Cvs.Upstream.ForcedOscillatorLiouvilleEnergy.
-/

namespace Cvs.Upstream.SqrtGrowthLawLinear

open Real Set MeasureTheory intervalIntegral

/-- **Square-root growth with a linear term.** -/
theorem sqrt_le_exp_mul {Z Z' β γ : ℝ → ℝ} {x₀ x₁ : ℝ} (hx : x₀ ≤ x₁) (hZ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ Z x)
    (hZ : ∀ x ∈ Icc x₀ x₁, HasDerivAt Z (Z' x) x) (hβ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ β x)
    (hγ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ γ x) (hβc : Continuous β) (hγc : Continuous γ)
    (hle : ∀ x ∈ Icc x₀ x₁, Z' x ≤ 2 * β x * Z x + 2 * γ x * √(Z x)) :
    √(Z x₁) ≤ exp (∫ t in x₀..x₁, β t)
      * (√(Z x₀) + ∫ x in x₀..x₁, γ x * exp (-∫ t in x₀..x, β t)) := by
  set B : ℝ → ℝ := fun x => ∫ t in x₀..x, β t with hBd
  have hB : ∀ x, HasDerivAt B (β x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hβc.intervalIntegrable _ _) (hβc.stronglyMeasurableAtFilter _ _)
      hβc.continuousAt
  have hBc : Continuous B := continuous_iff_continuousAt.2 fun x => (hB x).continuousAt
  set g : ℝ → ℝ := fun x => γ x * exp (-B x) with hgd
  have hgc : Continuous g := hγc.mul (hBc.neg.rexp)
  set G : ℝ → ℝ := fun x => ∫ t in x₀..x, g t with hGd
  have hG : ∀ x, HasDerivAt G (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _) (hgc.stronglyMeasurableAtFilter _ _)
      hgc.continuousAt
  have hB0 : B x₀ = 0 := by simp [hBd]
  have hG0 : G x₀ = 0 := by simp [hGd]
  -- for each `ε > 0`, `√(Z + ε)e^{−B} − G` is antitone
  have key : ∀ ε > 0, √(Z x₁ + ε) * exp (-B x₁) ≤ √(Z x₀ + ε) + G x₁ := by
    intro ε hε
    set φ : ℝ → ℝ := fun x => √(Z x + ε) * exp (-B x) - G x with hφ
    have hderiv : ∀ x ∈ Icc x₀ x₁, HasDerivAt φ
        ((Z' x / (2 * √(Z x + ε))) * exp (-B x) + √(Z x + ε) * (exp (-B x) * -β x) - g x) x := fun x hx' => by
      have hpos : 0 < Z x + ε := by linarith [hZ0 x hx']
      have h1 := ((hZ x hx').add_const ε).sqrt hpos.ne'
      have h2 : HasDerivAt (fun y => exp (-B y)) (exp (-B x) * -β x) x :=
        HasDerivAt.exp (HasDerivAt.neg (hB x))
      exact (HasDerivAt.mul h1 h2).sub (hG x)
    have hanti : AntitoneOn φ (Icc x₀ x₁) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc x₀ x₁)
      · exact fun x hx' => (hderiv x hx').continuousAt.continuousWithinAt
      · exact fun x hx' => (hderiv x (interior_subset hx')).differentiableAt.differentiableWithinAt
      · intro x hx'
        have hx'' := interior_subset hx'
        rw [(hderiv x hx'').deriv]
        have hZx := hZ0 x hx''
        have hS : 0 < √(Z x + ε) := Real.sqrt_pos.mpr (by linarith)
        have hsZ : √(Z x) ≤ √(Z x + ε) := Real.sqrt_le_sqrt (by linarith)
        have hE : 0 < exp (-B x) := exp_pos _
        have hb := hβ0 x hx''
        have hc := hγ0 x hx''
        -- `Z′/(2√(Z+ε)) ≤ β√(Z+ε) + γ`
        have hq : Z' x / (2 * √(Z x + ε)) ≤ β x * √(Z x + ε) + γ x := by
          rw [div_le_iff₀ (by positivity)]
          have hsq : √(Z x + ε) ^ 2 = Z x + ε := Real.sq_sqrt (by linarith)
          have h1 : 2 * β x * Z x ≤ β x * √(Z x + ε) * (2 * √(Z x + ε)) := by nlinarith
          have h2 : 2 * γ x * √(Z x) ≤ γ x * (2 * √(Z x + ε)) := by nlinarith
          linarith [hle x hx'']
        have : (Z' x / (2 * √(Z x + ε))) * exp (-B x) ≤ (β x * √(Z x + ε) + γ x) * exp (-B x) :=
          mul_le_mul_of_nonneg_right hq hE.le
        simp only [hgd]
        nlinarith
    have := hanti ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
    simp only [hφ, hB0, hG0, neg_zero, exp_zero, mul_one, sub_zero] at this
    linarith
  -- let `ε → 0`
  have hEB : 0 < exp (B x₁) := exp_pos _
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hδ' : 0 < δ / exp (B x₁) := div_pos hδ hEB
  have h := key ((δ / exp (B x₁)) ^ 2) (by positivity)
  have h1 : √(Z x₁) ≤ √(Z x₁ + (δ / exp (B x₁)) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h2 : √(Z x₀ + (δ / exp (B x₁)) ^ 2) ≤ √(Z x₀) + δ / exp (B x₁) := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt (hZ0 x₀ ⟨le_rfl, hx⟩), Real.sqrt_nonneg (Z x₀)]
  have h3 : √(Z x₁ + (δ / exp (B x₁)) ^ 2) ≤ exp (B x₁) * (√(Z x₀ + (δ / exp (B x₁)) ^ 2) + G x₁) := by
    have e : exp (-B x₁) = (exp (B x₁))⁻¹ := by rw [exp_neg]
    rw [e] at h
    rw [← div_le_iff₀' hEB]
    simpa [div_eq_mul_inv, mul_comm] using h
  have h4 : exp (B x₁) * (√(Z x₀ + (δ / exp (B x₁)) ^ 2) + G x₁)
      ≤ exp (B x₁) * (√(Z x₀) + G x₁) + δ := by
    have := mul_le_mul_of_nonneg_left (add_le_add_right h2 (G x₁)) hEB.le
    have e : exp (B x₁) * (√(Z x₀) + δ / exp (B x₁) + G x₁) = exp (B x₁) * (√(Z x₀) + G x₁) + δ := by
      field_simp; ring
    linarith
  simp only [hBd, hGd, hgd] at h1 h3 h4 ⊢
  linarith

end Cvs.Upstream.SqrtGrowthLawLinear
