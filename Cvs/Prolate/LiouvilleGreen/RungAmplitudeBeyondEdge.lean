import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The amplitude of a prolate rung beyond the edge

The energy of a prolate rung on `[ξ₀, ξ]` stays within the factor `fac(ξ₀)` of its value at `ξ₀` (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval, Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower), so
the Prüfer amplitude `A = √(E/a)` satisfies `E(ξ₀)/(fac(ξ₀) a(ξ)) ≤ A(ξ)² ≤ E(ξ₀) fac(ξ₀)/a(ξ)` with
`a(ξ) = √((ξ² − 1)(c²ξ² − χ))`: the amplitude datum of every profile pairing, decaying like `1/(ξ√c)` from one energy
value at the edge of the far region.
-/

namespace Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation

/-- **The amplitude window of a prolate rung**: `E(ξ₀)/(fac a(ξ)) ≤ A(ξ)² ≤ E(ξ₀) fac/a(ξ)` on `[ξ₀, ξ₁]`. -/
theorem prolate_ampl_sq_bounds {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ ξ : ℝ} (h1 : 1 < ξ₀) (hξ : ξ₀ ≤ ξ)
    (hξ₁ : ξ ≤ ξ₁) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₀ / fac c χ ξ₀ / aP c χ ξ ≤ ampl (aP c χ) ψ u ξ ^ 2
      ∧ ampl (aP c χ) ψ u ξ ^ 2 ≤ energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ ξ := by
  have hξ1 : 1 < ξ := lt_of_lt_of_le h1 hξ
  have hc2 : 0 < c ^ 2 := by positivity
  have ha : 0 < aP c χ ξ := aP_pos hξ1 hc2 hχc
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ := by
    unfold energy; positivity
  have hsub : Icc ξ₀ ξ ⊆ Icc ξ₀ ξ₁ := Icc_subset_Icc le_rfl hξ₁
  have hup := prolate_energy_le (c := c) (χ := χ) h1 hξ hc2 hχ hχc (fun t ht => hψ t (hsub ht))
    (fun t ht => hu t (hsub ht)) hW
  have hlo := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower.prolate_energy_ge (c := c) (χ := χ) h1 hξ hc2 hχ hχc
    (fun t ht => hψ t (hsub ht)) (fun t ht => hu t (hsub ht)) hW
  have hA : ampl (aP c χ) ψ u ξ ^ 2 = energy (aP c χ) ψ u ξ / aP c χ ξ := by
    unfold ampl; exact Real.sq_sqrt (div_nonneg hE0 ha.le)
  have hw0 : 0 < wP c χ ξ₀ := wP_pos h1 hc2 hχc
  have hfac : 0 < fac c χ ξ₀ := by
    unfold fac
    have : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
    positivity
  -- `fac⁻¹ = (1 − w/2)/(1 + w/2) · exp(−w/(2 − w))`
  have hfac_inv : (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2) * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀)))
      = 1 / fac c χ ξ₀ := by
    unfold fac
    rw [Real.exp_neg]
    have : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
    have : 0 < 1 + wP c χ ξ₀ / 2 := by linarith
    field_simp
  rw [hA]
  constructor
  · rw [div_le_div_iff_of_pos_right ha]
    calc energy (aP c χ) ψ u ξ₀ / fac c χ ξ₀ = energy (aP c χ) ψ u ξ₀ * (1 / fac c χ ξ₀) := by ring
      _ = energy (aP c χ) ψ u ξ₀ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2)
          * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀))) := by rw [← hfac_inv]; ring
      _ ≤ energy (aP c χ) ψ u ξ := hlo
  · rw [div_le_div_iff_of_pos_right ha]
    calc energy (aP c χ) ψ u ξ ≤ energy (aP c χ) ψ u ξ₀ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
          * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := hup
      _ = energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ := by unfold fac; ring

end Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge
