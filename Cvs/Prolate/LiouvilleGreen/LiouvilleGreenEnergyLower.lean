import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Liouville–Green energy is also bounded below

Reflecting `s ↦ −s` maps the system `ψ' = u/p`, `u' = −qψ` to one of the same form with the same energy,
so Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth run backwards gives `G t₀ ≤ G t₁ (1 + |w t₁|/2)/(1 − W/2) exp(∫|w'|/(2 − W))`. For the prolate
this pins every solution's energy within `(1 ± W/2)^{±1} e^{±W/(2−W)}` of its value at `ξ₀`, `W = w ξ₀`.
-/

namespace Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

variable {ψ u p q a w w' : ℝ → ℝ}

/-- **The energy's growth bound, backwards.** -/
theorem energy_le_exp_rev {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' (Icc t₀ t₁)) {W : ℝ} (hW : ∀ t ∈ Icc t₀ t₁, |w t| ≤ W) (hW2 : W < 2) :
    energy a ψ u t₀ ≤ energy a ψ u t₁ * (1 + |w t₁| / 2) / (1 - W / 2)
      * exp (∫ t in t₀..t₁, |w' t| / (2 - W)) := by
  have hmem : ∀ s ∈ Icc (-t₁) (-t₀), -s ∈ Icc t₀ t₁ := fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hn : ∀ s : ℝ, HasDerivAt (fun r : ℝ => -r) (-1) s := fun s => hasDerivAt_neg' s
  have key := Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth.energy_le_exp (ψ := fun s => ψ (-s)) (u := fun s => -u (-s))
    (p := fun s => p (-s)) (q := fun s => q (-s)) (a := fun s => a (-s)) (w := fun s => -w (-s))
    (w' := fun s => w' (-s)) (t₀ := -t₁) (t₁ := -t₀) (by linarith)
    (fun s hs => ha _ (hmem s hs)) (fun s hs => hp _ (hmem s hs)) (fun s hs => hapq _ (hmem s hs))
    (fun s hs => by
      have := (hψ _ (hmem s hs)).comp s (hn s)
      refine this.congr_deriv ?_; simp; ring)
    (fun s hs => by
      have := ((hu _ (hmem s hs)).comp s (hn s)).neg
      refine this.congr_deriv ?_; simp)
    (fun s hs => by
      have := (haw _ (hmem s hs)).comp s (hn s)
      refine this.congr_deriv ?_; simp)
    (fun s hs => by
      have := ((hw _ (hmem s hs)).comp s (hn s)).neg
      refine this.congr_deriv ?_; simp)
    (hw'.comp continuousOn_neg (fun s hs => hmem s hs))
    (fun s hs => by simpa [abs_neg] using hW _ (hmem s hs)) hW2
  have hE : ∀ t, energy (fun s => a (-s)) (fun s => ψ (-s)) (fun s => -u (-s)) (-t) = energy a ψ u t := by
    intro t; simp [energy]
  rw [hE, hE, abs_neg] at key
  have hI : ∫ s in -t₁..-t₀, |w' (-s)| / (2 - W) = ∫ t in t₀..t₁, |w' t| / (2 - W) := by
    have := intervalIntegral.integral_comp_neg (a := -t₁) (b := -t₀) (fun t => |w' t| / (2 - W))
    simpa using this
  rw [hI] at key
  simpa only [neg_neg] using key

/-- **The prolate energy, bounded below.** Under `prolate_energy_le`'s hypotheses,
`G ξ₀ (1 − W/2)/(1 + W/2) exp(−W/(2 − W)) ≤ G ξ₁`, `W = w ξ₀`. -/
theorem prolate_energy_ge {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c ^ 2) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₀ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2)
      * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀))) ≤ energy (aP c χ) ψ u ξ₁ := by
  have gt1 : ∀ t ∈ Icc ξ₀ ξ₁, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
  have hw'c : ContinuousOn (wP' c χ) (Icc ξ₀ ξ₁) := fun t ht =>
    (continuousAt_wP' (gt1 t ht) hc hχc).continuousWithinAt
  have hwc : ContinuousOn (wP c χ) (Icc ξ₀ ξ₁) := fun t ht =>
    (hasDerivAt_wP (gt1 t ht) hc hχc).continuousAt.continuousWithinAt
  have hanti : AntitoneOn (wP c χ) (Icc ξ₀ ξ₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ξ₀ ξ₁) hwc
    · rw [interior_Icc]; exact fun t ht =>
        (hasDerivAt_wP (gt1 t (Ioo_subset_Icc_self ht)) hc hχc).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      rw [(hasDerivAt_wP (gt1 t (Ioo_subset_Icc_self ht)) hc hχc).deriv]
      exact wP'_nonpos (gt1 t (Ioo_subset_Icc_self ht)) hc hχ hχc
  have hmem0 : ξ₀ ∈ Icc ξ₀ ξ₁ := left_mem_Icc.mpr hle
  have hmem1 : ξ₁ ∈ Icc ξ₀ ξ₁ := right_mem_Icc.mpr hle
  have hWb : ∀ t ∈ Icc ξ₀ ξ₁, |wP c χ t| ≤ wP c χ ξ₀ := fun t ht => by
    rw [abs_of_pos (wP_pos (gt1 t ht) hc hχc)]; exact hanti hmem0 ht ht.1
  have hE := energy_le_exp_rev hle (fun t ht => aP_pos (gt1 t ht) hc hχc)
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => aP_sq (gt1 t ht) hc hχc) hψ hu
    (fun t ht => hasDerivAt_aP (gt1 t ht) hc hχc) (fun t ht => hasDerivAt_wP (gt1 t ht) hc hχc)
    hw'c hWb hW
  have hI : uIcc ξ₀ ξ₁ = Icc ξ₀ ξ₁ := uIcc_of_le hle
  have hint : ∫ t in ξ₀..ξ₁, |wP' c χ t| / (2 - wP c χ ξ₀)
      = (wP c χ ξ₀ - wP c χ ξ₁) / (2 - wP c χ ξ₀) := by
    rw [intervalIntegral.integral_div]
    congr 1
    have hcongr : ∫ t in ξ₀..ξ₁, |wP' c χ t| = ∫ t in ξ₀..ξ₁, -wP' c χ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [hI] at ht
      exact abs_of_nonpos (wP'_nonpos (gt1 t ht) hc hχ hχc)
    rw [hcongr, intervalIntegral.integral_neg,
      integral_eq_sub_of_hasDerivAt (fun t ht => hasDerivAt_wP (gt1 t (hI ▸ ht)) hc hχc)
        (hw'c.intervalIntegrable_of_Icc hle)]
    ring
  rw [hint] at hE
  have hW0 := wP_pos h1 hc hχc
  have hW1 := wP_pos (gt1 ξ₁ hmem1) hc hχc
  have hw1le : wP c χ ξ₁ ≤ wP c χ ξ₀ := hanti hmem0 hmem1 hle
  rw [abs_of_pos hW1] at hE
  have hd : 0 < 2 - wP c χ ξ₀ := by linarith
  have hd1 : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
  have hG1 : 0 ≤ energy (aP c χ) ψ u ξ₁ :=
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (aP_pos (gt1 ξ₁ hmem1) hc hχc))
  -- G₀ ≤ G₁ (1 + W/2)/(1 − W/2) e^{W/(2−W)}
  have hexp : exp ((wP c χ ξ₀ - wP c χ ξ₁) / (2 - wP c χ ξ₀))
      ≤ exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) :=
    exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hd.le)
  have hfac : (1 + wP c χ ξ₁ / 2) ≤ (1 + wP c χ ξ₀ / 2) := by linarith
  have hG0 : energy (aP c χ) ψ u ξ₀ ≤ energy (aP c χ) ψ u ξ₁ * (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
      * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := by
    refine hE.trans ?_
    apply mul_le_mul _ hexp (exp_pos _).le
    · apply div_nonneg (mul_nonneg hG1 (by linarith)) hd1.le
    · apply div_le_div_of_nonneg_right _ hd1.le
      exact mul_le_mul_of_nonneg_left hfac hG1
  -- rearrange
  have hA : 0 < (1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2) * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀)) := by
    apply mul_pos (div_pos (by linarith) hd1) (exp_pos _)
  have : energy (aP c χ) ψ u ξ₀ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2)
      * exp (-(wP c χ ξ₀ / (2 - wP c χ ξ₀)))
      = energy (aP c χ) ψ u ξ₀ / ((1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
        * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀))) := by
    rw [exp_neg]; field_simp
  rw [this, div_le_iff₀ hA]
  calc energy (aP c χ) ψ u ξ₀ ≤ _ := hG0
    _ = energy (aP c χ) ψ u ξ₁ * ((1 + wP c χ ξ₀ / 2) / (1 - wP c χ ξ₀ / 2)
        * exp (wP c χ ξ₀ / (2 - wP c χ ξ₀))) := by ring

end Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyLower
