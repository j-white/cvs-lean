import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
# Integrating a square-root growth law

If `Z ≥ 0` has `Z′ ≤ 2√Z·f` on `[x₀, x₁]` with `f ≥ 0` continuous, then `√Z(x₁) ≤ √Z(x₀) + ∫_{x₀}^{x₁} f`: through
`√(Z + ε) − ∫f`, whose derivative is nonpositive, and `ε → 0`. With Cvs.Upstream.ForcedOscillatorEnergy (`f = |F|/a`) and `Z = 0` at the edge this is
the error bound `|ψ − ψ(1)A J₀(ζ)| ≤ ∫ |F|/a` of Olver's approximant.
-/

namespace Cvs.Upstream.SqrtGrowthLaw

open Real Set MeasureTheory intervalIntegral

/-- **The square-root growth law, integrated.** -/
theorem sqrt_le_add_integral {Z Z' f : ℝ → ℝ} {x₀ x₁ : ℝ} (hx : x₀ ≤ x₁) (hZ0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ Z x)
    (hZ : ∀ x ∈ Icc x₀ x₁, HasDerivAt Z (Z' x) x) (hf0 : ∀ x ∈ Icc x₀ x₁, 0 ≤ f x) (hfc : Continuous f)
    (hle : ∀ x ∈ Icc x₀ x₁, Z' x ≤ 2 * √(Z x) * f x) :
    √(Z x₁) ≤ √(Z x₀) + ∫ x in x₀..x₁, f x := by
  -- for each `ε > 0`, `√(Z + ε) − ∫_{x₀}^x f` is antitone
  have key : ∀ ε > 0, √(Z x₁ + ε) ≤ √(Z x₀ + ε) + ∫ x in x₀..x₁, f x := by
    intro ε hε
    set φ : ℝ → ℝ := fun x => √(Z x + ε) - ∫ t in x₀..x, f t with hφ
    have hderiv : ∀ x ∈ Icc x₀ x₁, HasDerivAt φ (Z' x / (2 * √(Z x + ε)) - f x) x := fun x hx' => by
      have hpos : 0 < Z x + ε := by linarith [hZ0 x hx']
      have h1 := ((hZ x hx').add_const ε).sqrt hpos.ne'
      have h2 : HasDerivAt (fun x => ∫ t in x₀..x, f t) (f x) x :=
        intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
          (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt
      exact h1.sub h2
    have hanti : AntitoneOn φ (Icc x₀ x₁) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc x₀ x₁)
      · exact fun x hx' => (hderiv x hx').continuousAt.continuousWithinAt
      · exact fun x hx' => (hderiv x (interior_subset hx')).differentiableAt.differentiableWithinAt
      · intro x hx'
        have hx'' := interior_subset hx'
        rw [(hderiv x hx'').deriv]
        have hpos : 0 < √(Z x + ε) := Real.sqrt_pos.mpr (by linarith [hZ0 x hx''])
        have hs : √(Z x) ≤ √(Z x + ε) := Real.sqrt_le_sqrt (by linarith)
        rw [sub_nonpos, div_le_iff₀ (by positivity)]
        calc Z' x ≤ 2 * √(Z x) * f x := hle x hx''
          _ ≤ 2 * √(Z x + ε) * f x := by
              apply mul_le_mul_of_nonneg_right _ (hf0 x hx''); linarith
          _ = f x * (2 * √(Z x + ε)) := by ring
    have := hanti ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
    simp only [hφ, intervalIntegral.integral_same, sub_zero] at this
    linarith
  -- let `ε → 0` through `√(Z₀ + ε) ≤ √Z₀ + √ε`
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have h := key (δ ^ 2) (by positivity)
  have h1 : √(Z x₁) ≤ √(Z x₁ + δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have h2 : √(Z x₀ + δ ^ 2) ≤ √(Z x₀) + δ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt (hZ0 x₀ ⟨le_rfl, hx⟩), Real.sqrt_nonneg (Z x₀)]
  linarith

end Cvs.Upstream.SqrtGrowthLaw
