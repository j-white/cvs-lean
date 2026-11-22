import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation
import Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The amplitude of a stationary edge pair in the layer variable

In `s` the amplitude of the pairing is `B(s) = A(ξ(s))·s/(2c²(m′ξ(s))^{n+1})` with `A = √(E/a)` the Prüfer amplitude.
Since `ξ² − 1 ≥ s²/c²` and `q ≥ c² − χ`, `a(ξ(s)) ≥ σs` with `σ = √(c² − χ)/c`, so with the energy window of Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge,
`|B(s)| ≤ √(E(ξ₀)fac(ξ₀)s/(σ·c))/(2c²m′^{n+1})`: the datum `A` of an earlier result, growing only like `√s` although `A(ξ)`
itself blows up like `(ξ − 1)^{−1/4}` at the edge.
-/

namespace Cvs.Prolate.LiouvilleGreen.LayerEdgePairAmplitude

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable

/-- **`a` in the layer variable**: `a(ξ(s)) ≥ s·√(c² − χ)/c` for `s ≥ 0`. -/
theorem aP_xiOf_ge {c χ s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) (hχc : χ < c ^ 2) :
    s * √(c ^ 2 - χ) / c ≤ aP c χ (xiOf c s) := by
  unfold aP
  have hε : 0 ≤ s ^ 2 / (2 * c ^ 2) := by positivity
  have hξ : xiOf c s = 1 + s ^ 2 / (2 * c ^ 2) := rfl
  have hl : 0 ≤ s * √(c ^ 2 - χ) / c := by positivity
  rw [← Real.sqrt_sq hl]
  apply Real.sqrt_le_sqrt
  rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]
  unfold pP qP
  rw [hξ]
  have hc2 : 0 < c ^ 2 := by positivity
  have h1 : s ^ 2 / c ^ 2 ≤ (1 + s ^ 2 / (2 * c ^ 2)) ^ 2 - 1 := by
    have : (1 + s ^ 2 / (2 * c ^ 2)) ^ 2 - 1 = s ^ 2 / c ^ 2 + (s ^ 2 / (2 * c ^ 2)) ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg (s ^ 2 / (2 * c ^ 2))]
  have h2 : c ^ 2 - χ ≤ c ^ 2 * (1 + s ^ 2 / (2 * c ^ 2)) ^ 2 - χ := by
    have : (1 : ℝ) ≤ (1 + s ^ 2 / (2 * c ^ 2)) ^ 2 := by nlinarith
    nlinarith
  calc s ^ 2 * (c ^ 2 - χ) / c ^ 2 = s ^ 2 / c ^ 2 * (c ^ 2 - χ) := by ring
    _ ≤ ((1 + s ^ 2 / (2 * c ^ 2)) ^ 2 - 1) * (c ^ 2 * (1 + s ^ 2 / (2 * c ^ 2)) ^ 2 - χ) :=
        mul_le_mul h1 h2 (by linarith) (by nlinarith [sq_nonneg (s ^ 2 / (2 * c ^ 2))])

/-- **The amplitude of a stationary edge pair in `s`**: for `0 < s` with `ξ₀ ≤ ξ(s) ≤ ξ₁`,
`A(ξ(s))·s/(2c²(m′ξ(s))^{n+1}) ≤ √(E(ξ₀)fac(ξ₀)·s·c/√(c² − χ))/(2c²m′^{n+1})`. -/
theorem ampS_le {c χ ξ₀ ξ₁ s : ℝ} {ψ u : ℝ → ℝ} {m' n : ℕ} (h1 : 1 < ξ₀) (hs : 0 < s)
    (hξ₀ : ξ₀ ≤ xiOf c s) (hξ₁ : xiOf c s ≤ ξ₁) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hm' : 1 ≤ m')
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    ampl (aP c χ) ψ u (xiOf c s) * s / (2 * c ^ 2 * ((m' : ℝ) * xiOf c s) ^ (n + 1))
      ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ * s * c / √(c ^ 2 - χ)) / (2 * c ^ 2 * (m' : ℝ) ^ (n + 1)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hσ : 0 < √(c ^ 2 - χ) := Real.sqrt_pos.mpr (by linarith)
  have hξ1 : 1 < xiOf c s := lt_of_lt_of_le h1 hξ₀
  have ha : 0 < aP c χ (xiOf c s) := aP_pos hξ1 hc2 hχc
  have hage := aP_xiOf_ge hc hs.le hχc
  obtain ⟨-, hup⟩ := prolate_ampl_sq_bounds (ψ := ψ) (u := u) h1 hξ₀ hξ₁ hc hχ hχc hψ hu hW
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ₀ := by
    have ha0 := aP_pos h1 hc2 hχc
    unfold energy; positivity
  have hw0 : 0 < wP c χ ξ₀ := wP_pos h1 hc2 hχc
  have hfac : 0 ≤ fac c χ ξ₀ := by
    unfold fac
    have : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
    positivity
  have hA0 : 0 ≤ ampl (aP c χ) ψ u (xiOf c s) := Real.sqrt_nonneg _
  -- `A(ξ(s))·s ≤ √(E fac s c/√(c² − χ))`
  have hAs : ampl (aP c χ) ψ u (xiOf c s) * s ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ * s * c / √(c ^ 2 - χ)) := by
    apply Real.le_sqrt_of_sq_le
    have hsa : s / aP c χ (xiOf c s) ≤ c / √(c ^ 2 - χ) := by
      rw [div_le_div_iff₀ ha hσ]
      have := hage
      rw [div_le_iff₀ hc] at this
      linarith
    calc (ampl (aP c χ) ψ u (xiOf c s) * s) ^ 2 = ampl (aP c χ) ψ u (xiOf c s) ^ 2 * s ^ 2 := by ring
      _ ≤ energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ (xiOf c s) * s ^ 2 :=
          mul_le_mul_of_nonneg_right hup (sq_nonneg _)
      _ = energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ * s * (s / aP c χ (xiOf c s)) := by ring
      _ ≤ energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ * s * (c / √(c ^ 2 - χ)) :=
          mul_le_mul_of_nonneg_left hsa (by positivity)
      _ = energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ * s * c / √(c ^ 2 - χ) := by ring
  have hm0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hpow : (m' : ℝ) ^ (n + 1) ≤ ((m' : ℝ) * xiOf c s) ^ (n + 1) :=
    pow_le_pow_left₀ hm0.le (le_mul_of_one_le_right hm0.le hξ1.le) _
  calc ampl (aP c χ) ψ u (xiOf c s) * s / (2 * c ^ 2 * ((m' : ℝ) * xiOf c s) ^ (n + 1))
      ≤ ampl (aP c χ) ψ u (xiOf c s) * s / (2 * c ^ 2 * (m' : ℝ) ^ (n + 1)) :=
        div_le_div_of_nonneg_left (mul_nonneg hA0 hs.le) (by positivity)
          (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ * s * c / √(c ^ 2 - χ)) / (2 * c ^ 2 * (m' : ℝ) ^ (n + 1)) :=
        div_le_div_of_nonneg_right hAs (by positivity)

end Cvs.Prolate.LiouvilleGreen.LayerEdgePairAmplitude
