import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Upstream.GronwallVariableRate

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Liouville–Green energy grows at most by `exp(∫|w'|/(2 − W))`

Under `LiouvilleGreenEnergyExact`'s system on `[t₀, t₁]` with `|w| ≤ W < 2` and `w'` continuous,
`G t₁ ≤ G t₀ (1 + |w t₀|/2)/(1 − W/2) · exp(∫_{t₀}^{t₁} |w'|/(2 − W))`: the WKB amplitude bound
with an explicit error, uniform up to any point where the variation of `w` stays finite.
-/

namespace Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact

variable {ψ u p q a w w' : ℝ → ℝ}

/-- **The energy's growth bound.** -/
theorem energy_le_exp {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' (Icc t₀ t₁)) {W : ℝ} (hW : ∀ t ∈ Icc t₀ t₁, |w t| ≤ W) (hW2 : W < 2) :
    energy a ψ u t₁ ≤ energy a ψ u t₀ * (1 + |w t₀| / 2) / (1 - W / 2)
      * exp (∫ t in t₀..t₁, |w' t| / (2 - W)) := by
  have hd : 0 < 1 - W / 2 := by linarith
  have hd2 : 0 < 2 - W := by linarith
  -- continuity of the pieces on the interval
  have cont : ∀ f : ℝ → ℝ, (∀ t ∈ Icc t₀ t₁, DifferentiableAt ℝ f t) → ContinuousOn f (Icc t₀ t₁) :=
    fun f hf t ht => (hf t ht).continuousAt.continuousWithinAt
  have hψc := cont ψ fun t ht => (hψ t ht).differentiableAt
  have huc := cont u fun t ht => (hu t ht).differentiableAt
  have hac := cont a fun t ht => (haw t ht).differentiableAt
  have hGc : ContinuousOn (energy a ψ u) (Icc t₀ t₁) := by
    unfold energy
    exact (hac.mul (hψc.pow 2)).add ((huc.pow 2).div hac fun t ht => (ha t ht).ne')
  have hG0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ energy a ψ u t := fun t ht =>
    le_trans (by positivity) (two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht))
  set C := energy a ψ u t₀ * (1 + |w t₀| / 2) / (1 - W / 2)
  have hk : ContinuousOn (fun t => |w' t| / (2 - W)) (Icc t₀ t₁) :=
    (hw'.abs).div_const _
  have hbound : ∀ t ∈ Icc t₀ t₁, energy a ψ u t
      ≤ C + ∫ s in t₀..t, |w' s| / (2 - W) * energy a ψ u s := by
    intro t ht
    have hsub : uIcc t₀ t ⊆ Icc t₀ t₁ := by
      rw [uIcc_of_le ht.1]; exact Icc_subset_Icc_right ht.2
    have hI1 : IntervalIntegrable (fun s => w' s * (ψ s * u s)) MeasureTheory.volume t₀ t :=
      (ContinuousOn.intervalIntegrable ((hw'.mul (hψc.mul huc)).mono hsub))
    have hI2 : IntervalIntegrable (fun s => |w' s| * energy a ψ u s / 2) MeasureTheory.volume t₀ t :=
      (ContinuousOn.intervalIntegrable (((hw'.abs).mul hGc).div_const 2 |>.mono hsub))
    have hE := energy_le ht.1 (fun s hs => ha s (hsub hs)) (fun s hs => hp s (hsub hs))
      (fun s hs => hapq s (hsub hs)) (fun s hs => hψ s (hsub hs)) (fun s hs => hu s (hsub hs))
      (fun s hs => haw s (hsub hs)) (fun s hs => hw s (hsub hs)) hI1 hI2
    have hwt : |w t| * energy a ψ u t / 2 ≤ W * energy a ψ u t / 2 := by
      have := mul_le_mul_of_nonneg_right (hW t ht) (hG0 t ht); linarith
    have hint_eq : ∫ s in t₀..t, |w' s| / (2 - W) * energy a ψ u s
        = (∫ s in t₀..t, |w' s| * energy a ψ u s / 2) / (1 - W / 2) := by
      rw [← intervalIntegral.integral_div]
      congr 1; funext s; field_simp
    rw [hint_eq]
    have hG0t := hG0 t ht
    have hmain : (1 - W / 2) * energy a ψ u t ≤ energy a ψ u t₀ * (1 + |w t₀| / 2)
        + ∫ s in t₀..t, |w' s| * energy a ψ u s / 2 := by linarith
    have : energy a ψ u t ≤ (energy a ψ u t₀ * (1 + |w t₀| / 2)
        + ∫ s in t₀..t, |w' s| * energy a ψ u s / 2) / (1 - W / 2) := by
      rw [le_div_iff₀ hd]; linarith
    calc energy a ψ u t ≤ _ := this
      _ = C + (∫ s in t₀..t, |w' s| * energy a ψ u s / 2) / (1 - W / 2) := by
        simp only [C]; ring
  exact Cvs.Upstream.GronwallVariableRate.le_mul_exp_integral hle hGc hk
    (fun t _ => div_nonneg (abs_nonneg _) hd2.le) hbound

end Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyGrowth
