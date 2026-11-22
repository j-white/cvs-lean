import Mathlib
import Cvs.L2a.WeightedArcsineDiagonal
import Cvs.Prolate.ExteriorMassEdgeLayer
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.RadialCutResolvent
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The arch channel of a radial cut past the energy point

For a radial solution with `0 ≤ χ < c²`, `c ≥ 1`, `w(ξ₀) < 2`, a cut `M ≥ ξ₀ > 1`, `G = G(ξ₀)fac(ξ₀)`,
`C = G/√(c² − χ)`, `S = arcsin(1/M)`, `s_M = √(M² − 1)` and `K₀ = |log(c/π)| + |a(0)| + 57/(2c)`:
`|archSpec(1_{(M,∞)}ψ) − ∫_M^∞ ψ² a(ν)|` is at most an explicit `bulkErr` in `C, G, c, χ, M, S` and `ℓ(S)`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology
open Cvs.Prolate.RadialCutResolvent (uu)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP qP aP wP)

namespace Cvs.L2a.RadialCutPastEnergyPoint
open Cvs.ZeroCounting

section Radial

variable {ψ v v' : ℝ → ℝ} {c χ : ℝ}
    (hψ : ∀ r ∈ Ici (1 : ℝ), HasDerivAt ψ (v r) r)
    (hv : ∀ r ∈ Ici (1 : ℝ), HasDerivAt v (v' r) r)
    (hode : ∀ r ∈ Ici (1 : ℝ), (r ^ 2 - 1) * v' r + 2 * r * v r + (c ^ 2 * r ^ 2 - χ) * ψ r = 0)

include hψ hv hode in
/-- **The energy envelope past `ξ₀`**: `ψ² ≤ C/(w√(w²−1))`, `u² ≤ Gcw√(w²−1)`, `|ψ||u| ≤ G/2`. -/
theorem energy_env (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) {ξ₀ w : ℝ} (h1 : 1 < ξ₀) (hW : wP c χ ξ₀ < 2)
    (hw : ξ₀ ≤ w) :
    |ψ w| ^ 2 ≤ Cvs.Prolate.ExteriorMassEdgeLayer.enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / √(c ^ 2 - χ)
        / (w * √(w ^ 2 - 1)) ∧
      |uu v w| ^ 2 ≤ Cvs.Prolate.ExteriorMassEdgeLayer.enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ * c * w * √(w ^ 2 - 1) ∧
      |ψ w| * |uu v w| ≤ Cvs.Prolate.ExteriorMassEdgeLayer.enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ / 2 := by
  have hw1 : 1 < w := lt_of_lt_of_le h1 hw
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.aP_pos hw1 hc2 hχ
  set G := Cvs.Prolate.ExteriorMassEdgeLayer.enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀ with hG
  have hE := (Cvs.Prolate.ExteriorMassEdgeLayer.enG_bounds hψ hv hode hc hχ0 hχ h1 hw hW).2
  have hEd : aP c χ w * ψ w ^ 2 + (pP w * v w) ^ 2 / aP c χ w ≤ G := hE
  have hu : uu v w = pP w * v w := rfl
  have h1' : aP c χ w * ψ w ^ 2 ≤ G := by have : 0 ≤ (pP w * v w) ^ 2 / aP c χ w := by positivity
                                          linarith
  have h2' : (pP w * v w) ^ 2 / aP c χ w ≤ G := by have : 0 ≤ aP c χ w * ψ w ^ 2 := by positivity
                                                   linarith
  have hlo := Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.inv_a_le hw1 hc hχ0 hχ
  have hhi := Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.inv_a_ge hw1 hc hχ0 hχ
  have hp : 0 < w ^ 2 - 1 := by nlinarith
  have hs := sqrt_pos.mpr hp
  have hd := sqrt_pos.mpr (sub_pos.mpr hχ)
  have hw0 : 0 < w := by linarith
  have halo : √(c ^ 2 - χ) * (w * √(w ^ 2 - 1)) ≤ aP c χ w := by
    rw [one_div_le_one_div (by positivity) (by positivity)] at hlo; exact hlo
  have hahi : aP c χ w ≤ c * (w * √(w ^ 2 - 1)) := by
    rw [one_div_le_one_div (by positivity) ha] at hhi; exact hhi
  refine ⟨?_, ?_, ?_⟩
  · rw [sq_abs, div_div, le_div_iff₀ (by positivity)]
    calc ψ w ^ 2 * (√(c ^ 2 - χ) * (w * √(w ^ 2 - 1))) ≤ ψ w ^ 2 * aP c χ w := by gcongr
      _ = aP c χ w * ψ w ^ 2 := by ring
      _ ≤ G := h1'
  · rw [sq_abs, hu]
    rw [div_le_iff₀ ha] at h2'
    calc (pP w * v w) ^ 2 ≤ G * aP c χ w := h2'
      _ ≤ G * (c * (w * √(w ^ 2 - 1))) := by
          have hG0 : 0 ≤ G := le_trans (by positivity) h1'
          gcongr
      _ = G * c * w * √(w ^ 2 - 1) := by ring
  · rw [hu]
    have hsq : 2 * (|ψ w| * |pP w * v w|) ≤ aP c χ w * ψ w ^ 2 + (pP w * v w) ^ 2 / aP c χ w := by
      have h := sq_nonneg (√(aP c χ w) * |ψ w| - |pP w * v w| / √(aP c χ w))
      have hsa := sqrt_pos.mpr ha
      have hsq2 := sq_sqrt ha.le
      rw [sub_sq, mul_pow, div_pow, hsq2, sq_abs, sq_abs] at h
      have : 2 * (√(aP c χ w) * |ψ w|) * (|pP w * v w| / √(aP c χ w)) = 2 * (|ψ w| * |pP w * v w|) := by
        field_simp
      linarith
    linarith

/-- The symbol increment at the local frequency, `α(w) = a(ν(w)) − a(0)`. -/
def alf (c w : ℝ) : ℝ := Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (Cvs.L2a.WeightedArcsineDiagonal.nuLoc c w) - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0

omit hψ hv hode in
/-- `α ≤ K₀ + lw` with `K₀ = |log(c/π)| + |a(0)| + 57/(2c)`. -/
theorem alf_le {w : ℝ} (hc : 1 ≤ c) (hw : 1 < w) :
    alf c w ≤ |Real.log (c / π)| + |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 57 / (2 * c) + Cvs.L2a.WeightedArcsineDiagonal.lw w := by
  have h1 := Cvs.L2a.WeightedArcsineDiagonal.abs_archSymbol_nuLoc_le hc hw
  unfold alf
  have := (abs_le.mp h1).2
  have := le_abs_self (Real.log (c / π))
  have := neg_abs_le (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
  linarith

omit hψ hv hode in
theorem rr_eq (w : ℝ) : Cvs.L2a.WeightedArcsineDiagonal.rr w = 1 / (w * √(w ^ 2 - 1)) := rfl

/-- The energy constant `G = G(ξ₀)·fac(ξ₀)`. -/
def Gen (c χ : ℝ) (ψ v : ℝ → ℝ) (ξ₀ : ℝ) : ℝ :=
  Cvs.Prolate.ExteriorMassEdgeLayer.enG c χ ψ v ξ₀ * Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c χ ξ₀

end Radial

end Cvs.L2a.RadialCutPastEnergyPoint
