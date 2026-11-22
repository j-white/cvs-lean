import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prolate's leakage tail decays like `arcsin(1/Y)`, relative to its whole

With `Fac = (1 + W/2)/(1 − W/2) e^{W/(2−W)}`, `W = w ξ₀`, the energy stays in `[G₀/Fac, G₀ Fac]`, so
Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw on `[ξ₀, Z]` and on `[Y, Z]` gives, whenever `L = Δ₀/(2c Fac) − Fac/(2q(ξ₀)) > 0`,
`∫_Y^Z ψ² ≤ (Fac/L)(arcsin(1/Y)/(2√(c²−χ)) + 1/(2q(Y))) ∫_{ξ₀}^Z ψ²`: the amplitude cancels.
-/

namespace Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- The two-sided energy factor at `ξ₀`. -/
noncomputable def fac (c χ ξ₀ : ℝ) : ℝ :=
  (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2) * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀))

/-- **The tail ratio.** -/
theorem prolate_tail_ratio {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ Y Z : ℝ} (h1 : 1 < ξ₀) (hY : ξ₀ ≤ Y)
    (hZ : Y ≤ Z) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ Z, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ Z, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2)
    (hL : 0 < (arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
      - fac c χ ξ₀ / (2 * qP c χ ξ₀)) :
    ∫ t in Y..Z, ψ t ^ 2 ≤ fac c χ ξ₀ / ((arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
        - fac c χ ξ₀ / (2 * qP c χ ξ₀))
      * (arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) + 1 / (2 * qP c χ Y)) * ∫ t in ξ₀..Z, ψ t ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hle : ξ₀ ≤ Z := hY.trans hZ
  set F := fac c χ ξ₀ with hF
  set G₀ := energy (aP c χ) ψ u ξ₀
  have hW0 := wP_pos h1 hc2 hχc
  have hd1 : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
  have hFpos : 0 < F := by
    simp only [hF, fac]; exact mul_pos (div_pos (by linarith) hd1) (exp_pos _)
  -- the energy stays in [G₀/F, G₀ F]
  have hup : ∀ t ∈ Icc ξ₀ Z, energy (aP c χ) ψ u t ≤ G₀ * F := fun t ht => by
    have := prolate_energy_le h1 ht.1 hc2 hχ hχc (fun s hs => hψ s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hu s ⟨hs.1, hs.2.trans ht.2⟩) hW
    simp only [hF, fac]; linarith [this, show G₀ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
      * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) = G₀ * ((1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
      * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀))) by ring]
  have hlo : ∀ t ∈ Icc ξ₀ Z, G₀ / F ≤ energy (aP c χ) ψ u t := fun t ht => by
    have := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower.prolate_energy_ge h1 ht.1 hc2 hχ hχc
      (fun s hs => hψ s ⟨hs.1, hs.2.trans ht.2⟩) (fun s hs => hu s ⟨hs.1, hs.2.trans ht.2⟩) hW
    refine le_trans (le_of_eq ?_) this
    simp only [hF, fac, exp_neg, G₀]
    field_simp
  have hG0 : 0 ≤ G₀ := le_trans (by positivity)
    (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos h1 hc2 hχc))
  -- lower bound on the whole
  have lower := (Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.prolate_mass_bounds h1 hle hc hχ hχc hψ hu hlo hup
    (div_nonneg hG0 hFpos.le)).1
  -- upper bound on the tail
  have hY1 : 1 < Y := lt_of_lt_of_le h1 hY
  have sub : ∀ t ∈ Icc Y Z, t ∈ Icc ξ₀ Z := fun t ht => ⟨hY.trans ht.1, ht.2⟩
  have upper := (Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.prolate_mass_bounds hY1 hZ hc hχ hχc
    (fun t ht => hψ t (sub t ht)) (fun t ht => hu t (sub t ht))
    (fun t ht => hlo t (sub t ht)) (fun t ht => hup t (sub t ht)) (div_nonneg hG0 hFpos.le)).2
  have hΔY : arccos (1 / Z) - arccos (1 / Y) ≤ arcsin (1 / Y) := by
    have h0 : arccos (1 / Z) ≤ π / 2 := arccos_le_pi_div_two.mpr (by
      have : 0 < Z := by linarith
      positivity)
    rw [arccos_eq_pi_div_two_sub_arcsin (1 / Y)]
    linarith
  have hsq := Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.sub_pos' hχc
  have hs : 0 < √(c ^ 2 - χ) := sqrt_pos.mpr hsq
  have hqY := qP_pos hY1 hc2 hχc
  set R := arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) + 1 / (2 * qP c χ Y)
  have hupR : ∫ t in Y..Z, ψ t ^ 2 ≤ G₀ * F * R := by
    refine upper.trans ?_
    simp only [R]
    have : G₀ * F * (arccos (1 / Z) - arccos (1 / Y)) / (2 * √(c ^ 2 - χ))
        ≤ G₀ * F * arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΔY (by positivity)) (by positivity)
    have e : G₀ * F / (2 * qP c χ Y) = G₀ * F * (1 / (2 * qP c χ Y)) := by ring
    have e2 : G₀ * F * arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) =
        G₀ * F * (arcsin (1 / Y) / (2 * √(c ^ 2 - χ))) := by ring
    rw [mul_add]; linarith
  -- G₀ L ≤ ∫_{ξ₀}^Z ψ²
  set L := (arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * F) - F / (2 * qP c χ ξ₀)
  have hlowL : G₀ * L ≤ ∫ t in ξ₀..Z, ψ t ^ 2 := by
    refine le_trans (le_of_eq ?_) lower
    simp only [L]; field_simp
  have hR : 0 ≤ R := by
    have := arcsin_nonneg.mpr (show (0:ℝ) ≤ 1 / Y by positivity)
    positivity
  -- combine: ∫_Y^Z ≤ G₀ F R ≤ (F/L) R ∫_{ξ₀}^Z
  have hG0L : G₀ ≤ (∫ t in ξ₀..Z, ψ t ^ 2) / L := by rw [le_div_iff₀ hL]; linarith
  calc ∫ t in Y..Z, ψ t ^ 2 ≤ G₀ * F * R := hupR
    _ ≤ (∫ t in ξ₀..Z, ψ t ^ 2) / L * F * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        exact mul_le_mul_of_nonneg_right hG0L hFpos.le
    _ = F / L * R * ∫ t in ξ₀..Z, ψ t ^ 2 := by ring

end Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
