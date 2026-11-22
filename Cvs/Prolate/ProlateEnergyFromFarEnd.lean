import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The energy from the far end, two-sided, with no exponential

For `ψ' = u/p`, `u' = −qψ`, `a' = wq` with the rate `w` decreasing in `[0, 2)`, the two quantities
`(G + wψu)(1 − w/2)` and `(G + wψu)/(1 − w/2)` are monotone in opposite directions, because `(G + wψu)' = w'ψu`
and `2|ψu| ≤ G`. Hence on `[t₀, t₁]`: `G(t₁)(1 − w(t₀)/2)/(1 + w(t₀)/2) ≤ G(t₀) ≤ G(t₁)(1 − w(t₁)²/4)/(1 − w(t₀)/2)²`.
For the prolate rate `w = (pq)'/(2qa)` this holds from any `ξ₀ > 1` with `w(ξ₀) < 2`.
-/

namespace Cvs.Prolate.ProlateEnergyFromFarEnd

open Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

variable {ψ u p q a w w' : ℝ → ℝ}

/-- **The energy from the far end**: for a decreasing rate `0 ≤ w < 2` on `[t₀, t₁]`,
`G(t₁)(1 − w(t₀)/2)/(1 + w(t₀)/2) ≤ G(t₀)` and `G(t₀) ≤ G(t₁)(1 − (w(t₁)/2)²)/(1 − w(t₀)/2)²`. -/
theorem energy_bounds_of_far {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Icc t₀ t₁, w' t ≤ 0) (hw0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ w t)
    (hw2 : ∀ t ∈ Icc t₀ t₁, w t < 2) :
    energy a ψ u t₁ * (1 - w t₀ / 2) / (1 + w t₀ / 2) ≤ energy a ψ u t₀ ∧
    energy a ψ u t₀ ≤ energy a ψ u t₁ * (1 - (w t₁ / 2) ^ 2) / (1 - w t₀ / 2) ^ 2 := by
  set F : ℝ → ℝ := fun s => energy a ψ u s + w s * (ψ s * u s) with hFdef
  have hF : ∀ t ∈ Icc t₀ t₁, HasDerivAt F (w' t * (ψ t * u t)) t := fun t ht =>
    hasDerivAt_energy_add (ha t ht) (hp t ht) (hapq t ht) (hψ t ht) (hu t ht) (haw t ht) (hw t ht)
  have hg : ∀ t ∈ Icc t₀ t₁, HasDerivAt (fun s => 1 - w s / 2) (-(w' t / 2)) t := fun t ht =>
    ((hw t ht).div_const 2).const_sub 1
  have hpos : ∀ t ∈ Icc t₀ t₁, 0 < 1 - w t / 2 := fun t ht => by linarith [hw2 t ht]
  have hPE : ∀ t ∈ Icc t₀ t₁, 2 * |ψ t * u t| ≤ energy a ψ u t := fun t ht =>
    two_mul_abs_le_energy (ha t ht)
  -- `(G + wψu)(1 − w/2)` does not decrease
  have h1 : MonotoneOn (fun s => F s * (1 - w s / 2)) (Icc t₀ t₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ t₁)
    · exact fun t ht => ((hF t ht).fun_mul (hg t ht)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun t ht => ((hF t (Ioo_subset_Icc_self ht)).mul
        (hg t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      have ht' := Ioo_subset_Icc_self ht
      rw [((hF t ht').fun_mul (hg t ht')).deriv]
      have e : w' t * (ψ t * u t) * (1 - w t / 2) + F t * -(w' t / 2)
          = w' t * (ψ t * u t * (1 - w t) - energy a ψ u t / 2) := by simp only [hFdef]; ring
      rw [e]
      have h := hPE t ht'
      have habs : ψ t * u t * (1 - w t) ≤ |ψ t * u t| := by
        calc ψ t * u t * (1 - w t) ≤ |ψ t * u t * (1 - w t)| := le_abs_self _
          _ = |ψ t * u t| * |1 - w t| := abs_mul _ _
          _ ≤ |ψ t * u t| * 1 := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              rw [abs_le]; constructor <;> linarith [hw0 t ht', hw2 t ht']
          _ = |ψ t * u t| := mul_one _
      have hbr : ψ t * u t * (1 - w t) - energy a ψ u t / 2 ≤ 0 := by linarith
      nlinarith [mul_nonneg (neg_nonneg.mpr (hw' t ht')) (neg_nonneg.mpr hbr)]
  -- `(G + wψu)/(1 − w/2)` does not increase
  have h2 : AntitoneOn (fun s => F s / (1 - w s / 2)) (Icc t₀ t₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
    · exact fun t ht => ((hF t ht).fun_div (hg t ht) (hpos t ht).ne').continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun t ht => ((hF t (Ioo_subset_Icc_self ht)).fun_div (hg t (Ioo_subset_Icc_self ht))
        (hpos t (Ioo_subset_Icc_self ht)).ne').differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      have ht' := Ioo_subset_Icc_self ht
      rw [((hF t ht').fun_div (hg t ht') (hpos t ht').ne').deriv]
      have e : (w' t * (ψ t * u t) * (1 - w t / 2) - F t * -(w' t / 2)) / (1 - w t / 2) ^ 2
          = w' t * (ψ t * u t + energy a ψ u t / 2) / (1 - w t / 2) ^ 2 := by simp only [hFdef]; ring
      rw [e]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      have h := hPE t ht'
      have h' := neg_abs_le (ψ t * u t)
      have hbr : 0 ≤ ψ t * u t + energy a ψ u t / 2 := by linarith
      nlinarith [mul_nonneg (neg_nonneg.mpr (hw' t ht')) hbr]
  have hm0 : t₀ ∈ Icc t₀ t₁ := left_mem_Icc.mpr hle
  have hm1 : t₁ ∈ Icc t₀ t₁ := right_mem_Icc.mpr hle
  have m1 := h1 hm0 hm1 hle
  have m2 := h2 hm0 hm1 hle
  simp only at m1 m2
  have hp0 := hpos t₀ hm0
  have hp1 := hpos t₁ hm1
  rw [div_le_div_iff₀ hp1 hp0] at m2
  -- `G(1 − w/2) ≤ G + wψu ≤ G(1 + w/2)`
  have box : ∀ t ∈ Icc t₀ t₁, energy a ψ u t * (1 - w t / 2) ≤ F t ∧ F t ≤ energy a ψ u t * (1 + w t / 2) := by
    intro t ht
    have h := hPE t ht
    have l1 := neg_abs_le (ψ t * u t)
    have l2 := le_abs_self (ψ t * u t)
    have hw := hw0 t ht
    simp only [hFdef]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left (show -(energy a ψ u t / 2) ≤ ψ t * u t by linarith) hw]
    · nlinarith [mul_le_mul_of_nonneg_left (show ψ t * u t ≤ energy a ψ u t / 2 by linarith) hw]
  obtain ⟨b0l, b0u⟩ := box t₀ hm0
  obtain ⟨b1l, b1u⟩ := box t₁ hm1
  constructor
  · rw [div_le_iff₀ (by linarith [hw0 t₀ hm0])]
    -- `G₁(1 − W₀/2)(1 − W₁/2) ≤ F₁(1 − W₀/2) ≤ F₀(1 − W₁/2)`, so `G₁(1 − W₀/2) ≤ F₀ ≤ G₀(1 + W₀/2)`
    have s1 : energy a ψ u t₁ * (1 - w t₁ / 2) * (1 - w t₀ / 2) ≤ F t₁ * (1 - w t₀ / 2) :=
      mul_le_mul_of_nonneg_right b1l hp0.le
    have s2 : energy a ψ u t₁ * (1 - w t₀ / 2) ≤ F t₀ := by
      apply le_of_mul_le_mul_right _ hp1
      nlinarith [s1, m2]
    linarith
  · rw [le_div_iff₀ (pow_pos hp0 2)]
    -- `G₀(1 − W₀/2)² ≤ F₀(1 − W₀/2) ≤ F₁(1 − W₁/2) ≤ G₁(1 + W₁/2)(1 − W₁/2)`
    have s1 : energy a ψ u t₀ * (1 - w t₀ / 2) ^ 2 ≤ F t₀ * (1 - w t₀ / 2) := by
      rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right b0l hp0.le
    have s2 : F t₁ * (1 - w t₁ / 2) ≤ energy a ψ u t₁ * (1 + w t₁ / 2) * (1 - w t₁ / 2) :=
      mul_le_mul_of_nonneg_right b1u hp1.le
    nlinarith [s1, m1, s2]

/-- **The prolate energy from the far end**: on `[ξ₀, ξ₁]`, `1 < ξ₀`, `0 ≤ χ < c²`, with `W = w(ξ₀) < 2`,
`G(ξ₁)(1 − W/2)/(1 + W/2) ≤ G(ξ₀)` and `G(ξ₀) ≤ G(ξ₁)(1 − (w(ξ₁)/2)²)/(1 − W/2)²`. -/
theorem prolate_energy_bounds_of_far {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c ^ 2) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₁ * (1 - wP c χ ξ₀ / 2) / (1 + wP c χ ξ₀ / 2) ≤ energy (aP c χ) ψ u ξ₀ ∧
    energy (aP c χ) ψ u ξ₀
      ≤ energy (aP c χ) ψ u ξ₁ * (1 - (wP c χ ξ₁ / 2) ^ 2) / (1 - wP c χ ξ₀ / 2) ^ 2 := by
  have gt1 : ∀ t ∈ Icc ξ₀ ξ₁, 1 < t := fun t ht => lt_of_lt_of_le h1 ht.1
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
  exact energy_bounds_of_far hle (fun t ht => aP_pos (gt1 t ht) hc hχc)
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => aP_sq (gt1 t ht) hc hχc) hψ hu
    (fun t ht => hasDerivAt_aP (gt1 t ht) hc hχc) (fun t ht => hasDerivAt_wP (gt1 t ht) hc hχc)
    (fun t ht => wP'_nonpos (gt1 t ht) hc hχ hχc) (fun t ht => (wP_pos (gt1 t ht) hc hχc).le)
    (fun t ht => lt_of_le_of_lt (hanti hmem0 ht ht.1) hW)

end Cvs.Prolate.ProlateEnergyFromFarEnd
