import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.Envelope.EdgeValueSoninBound
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
# The corrected energy is antitone, and the box constant `11/10`

For `ψ' = u/p`, `u' = −qψ`, `a² = pq`, `a' = wq` with `w` decreasing in `[0, 2)`, `(E + wψu)/(1 − w/2)` is antitone,
so `E(t₁) ≤ (E(t₀) + w(t₀)ψ(t₀)u(t₀))/(1 − w(t₀)/2)`; this is the prolate form with `w = wP`. For `c ≥ 80`, `χ ≥ 0`,
`D = c² − χ ≥ 5c` and `ξ₀ = 1 + 1/(2D)`: `W = wP(ξ₀) ≤ 1.0195` and `[(1 + d₀)a(ξ₀) − W(ξ₀ − 1)q(ξ₀)]/(1 − W/2) ≤ 11/10`.
-/

namespace Cvs.Prolate.CorrectedEnergyAntitone

open Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

variable {ψ u p q a w w' : ℝ → ℝ}

/-- **The corrected energy is antitone**: for `w` decreasing below `2`, `(E + wψu)/(1 − w/2)` does not increase. -/
theorem corrected_antitoneOn {t₀ t₁ : ℝ}
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Icc t₀ t₁, w' t ≤ 0) (hw2 : ∀ t ∈ Icc t₀ t₁, w t < 2) :
    AntitoneOn (fun s => (energy a ψ u s + w s * (ψ s * u s)) / (1 - w s / 2)) (Icc t₀ t₁) := by
  set F : ℝ → ℝ := fun s => energy a ψ u s + w s * (ψ s * u s) with hFdef
  have hF : ∀ t ∈ Icc t₀ t₁, HasDerivAt F (w' t * (ψ t * u t)) t := fun t ht =>
    hasDerivAt_energy_add (ha t ht) (hp t ht) (hapq t ht) (hψ t ht) (hu t ht) (haw t ht) (hw t ht)
  have hg : ∀ t ∈ Icc t₀ t₁, HasDerivAt (fun s => 1 - w s / 2) (-(w' t / 2)) t := fun t ht =>
    ((hw t ht).div_const 2).const_sub 1
  have hpos : ∀ t ∈ Icc t₀ t₁, 0 < 1 - w t / 2 := fun t ht => by linarith [hw2 t ht]
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
    have h := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht')
    have h' := neg_abs_le (ψ t * u t)
    have hbr : 0 ≤ ψ t * u t + energy a ψ u t / 2 := by linarith
    nlinarith [mul_nonneg (neg_nonneg.mpr (hw' t ht')) hbr]

/-- **The energy under the corrected energy**: on `[t₀, t₁]` with `w` decreasing in `[0, 2)`,
`E(t₁) ≤ (E(t₀) + w(t₀)ψ(t₀)u(t₀))/(1 − w(t₀)/2)`. -/
theorem energy_le_corrected {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Icc t₀ t₁, w' t ≤ 0) (hw0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ w t)
    (hw2 : ∀ t ∈ Icc t₀ t₁, w t < 2) :
    energy a ψ u t₁ ≤ (energy a ψ u t₀ + w t₀ * (ψ t₀ * u t₀)) / (1 - w t₀ / 2) := by
  have hm0 : t₀ ∈ Icc t₀ t₁ := left_mem_Icc.mpr hle
  have hm1 : t₁ ∈ Icc t₀ t₁ := right_mem_Icc.mpr hle
  have m := corrected_antitoneOn ha hp hapq hψ hu haw hw hw' hw2 hm0 hm1 hle
  simp only at m
  refine le_trans ?_ m
  have hp1 : 0 < 1 - w t₁ / 2 := by linarith [hw2 t₁ hm1]
  rw [le_div_iff₀ hp1]
  -- `E(1 − w/2) ≤ E + wψu` from `2|ψu| ≤ E` and `w ≥ 0`
  have h := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t₁ hm1)
  have l1 := neg_abs_le (ψ t₁ * u t₁)
  nlinarith [mul_le_mul_of_nonneg_left
    (show -(energy a ψ u t₁ / 2) ≤ ψ t₁ * u t₁ by linarith) (hw0 t₁ hm1)]

/-- **The prolate energy under the corrected energy**: on `[ξ₀, ξ₁]`, `1 < ξ₀`, `0 ≤ χ < c²`, `wP(ξ₀) < 2`,
`E(ξ₁) ≤ (E(ξ₀) + wP(ξ₀)ψ(ξ₀)u(ξ₀))/(1 − wP(ξ₀)/2)`. -/
theorem prolate_energy_le_corrected {c χ : ℝ} {ψ u : ℝ → ℝ} {ξ₀ ξ₁ : ℝ} (h1 : 1 < ξ₀) (hle : ξ₀ ≤ ξ₁)
    (hc : 0 < c ^ 2) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    energy (aP c χ) ψ u ξ₁
      ≤ (energy (aP c χ) ψ u ξ₀ + wP c χ ξ₀ * (ψ ξ₀ * u ξ₀)) / (1 - wP c χ ξ₀ / 2) := by
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
  exact energy_le_corrected hle (fun t ht => aP_pos (gt1 t ht) hc hχc)
    (fun t ht => (pP_pos (gt1 t ht)).ne') (fun t ht => aP_sq (gt1 t ht) hc hχc) hψ hu
    (fun t ht => hasDerivAt_aP (gt1 t ht) hc hχc) (fun t ht => hasDerivAt_wP (gt1 t ht) hc hχc)
    (fun t ht => wP'_nonpos (gt1 t ht) hc hχ hχc) (fun t ht => (wP_pos (gt1 t ht) hc hχc).le)
    (fun t ht => lt_of_le_of_lt (hanti hmem0 ht ht.1) hW)

/-- **The box inequality in scaled variables**: for `0 < ε ≤ 1/800`, `0 ≤ e ≤ 1/25`, `s = 1 + ε/2`, `y = es`,
`a² = s(1 + y)` and `W(1 + y)a = (1 + ε)(1 + 2y)`: `W ≤ 1.0195` and
`[(1 + e(1 + ε))a − W(1 + y)/2]/(1 − W/2) ≤ 11/10`. -/
theorem box_scaled {ε e s y a W : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 800) (he0 : 0 ≤ e) (he : e ≤ 1 / 25)
    (hs : s = 1 + ε / 2) (hy : y = e * s) (ha : 0 < a) (ha2 : a ^ 2 = s * (1 + y))
    (hW : W * ((1 + y) * a) = (1 + ε) * (1 + 2 * y)) :
    W ≤ 1.0195 ∧ ((1 + e * (1 + ε)) * a - W * ((1 + y) / 2)) / (1 - W / 2) ≤ 11 / 10 := by
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hs2 : s ≤ 1.000625 := by rw [hs]; norm_num; linarith
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyY : y ≤ 0.040025 := by
    rw [hy]; nlinarith [mul_le_mul he hs2 (by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 25)]
  have hya : 0 < (1 + y) * a := by positivity
  -- `W ≤ 1.0195`
  have hW1 : W ≤ 1.0195 := by
    have k1 : (1 + ε) ^ 2 ≤ 1.001876 * s := by
      rw [hs]; nlinarith [mul_le_mul_of_nonneg_left hε hε0.le]
    have k2 : 1.001876 * (1 + 2 * y) ^ 2 ≤ 1.0195 ^ 2 * (1 + y) ^ 3 := by
      have hYy : 0 ≤ 0.040025 - y := by linarith
      nlinarith [mul_nonneg (mul_nonneg hy0 hYy) hy0, mul_nonneg hy0 hYy]
    have k3 : ((1 + ε) * (1 + 2 * y)) ^ 2 ≤ (1.0195 * ((1 + y) * a)) ^ 2 := by
      have e1 : (1.0195 * ((1 + y) * a)) ^ 2 = 1.0195 ^ 2 * (1 + y) ^ 2 * (s * (1 + y)) := by
        rw [← ha2]; ring
      rw [e1]
      have h12 : 0 ≤ (1 + 2 * y) ^ 2 := sq_nonneg _
      calc ((1 + ε) * (1 + 2 * y)) ^ 2 = (1 + ε) ^ 2 * (1 + 2 * y) ^ 2 := by ring
        _ ≤ 1.001876 * s * (1 + 2 * y) ^ 2 := mul_le_mul_of_nonneg_right k1 h12
        _ = s * (1.001876 * (1 + 2 * y) ^ 2) := by ring
        _ ≤ s * (1.0195 ^ 2 * (1 + y) ^ 3) := mul_le_mul_of_nonneg_left k2 (by linarith)
        _ = 1.0195 ^ 2 * (1 + y) ^ 2 * (s * (1 + y)) := by ring
    have k4 : (1 + ε) * (1 + 2 * y) ≤ 1.0195 * ((1 + y) * a) :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp k3
    rw [← hW] at k4
    exact le_of_mul_le_mul_right k4 hya
  refine ⟨hW1, ?_⟩
  have hden : 0 < 1 - W / 2 := by linarith
  rw [div_le_iff₀ hden]
  -- `a ≥ 1 + y/2 − y²/8`
  have hL : 1 + y / 2 - y ^ 2 / 8 ≤ a := by
    have hL0 : 0 ≤ 1 + y / 2 - y ^ 2 / 8 := by nlinarith
    apply (pow_le_pow_iff_left₀ hL0 ha.le two_ne_zero).mp
    rw [ha2]
    nlinarith [mul_nonneg (mul_nonneg hy0 hy0) hy0, mul_nonneg (mul_nonneg hy0 hy0) (sub_nonneg.mpr hs1)]
  -- `e(1 + ε) ≤ 1.000625 y`
  have hey : e * (1 + ε) ≤ 1.000625 * y := by
    have h2 : 1 + ε ≤ s * s := by rw [hs]; nlinarith
    calc e * (1 + ε) ≤ e * (s * s) := mul_le_mul_of_nonneg_left h2 he0
      _ = y * s := by rw [hy]; ring
      _ ≤ y * 1.000625 := mul_le_mul_of_nonneg_left hs2 hy0
      _ = 1.000625 * y := by ring
  -- reduce to a polynomial inequality in `y` after multiplying by `(1 + y)a`
  have key : ((1 + e * (1 + ε)) * a - W * ((1 + y) / 2) - 11 / 10 * (1 - W / 2)) * ((1 + y) * a)
      = (1 + e * (1 + ε)) * s * (1 + y) ^ 2 + (1 + ε) * (1 + 2 * y) * (1 / 20 - y / 2)
        - 11 / 10 * (1 + y) * a := by
    linear_combination (1 + e * (1 + ε)) * (1 + y) * ha2 + (11 / 20 - (1 + y) / 2) * hW
  have q1 : (1 + e * (1 + ε)) * s * (1 + y) ^ 2 ≤ (1 + 1.000625 * y) * 1.000625 * (1 + y) ^ 2 := by
    have h1y : 0 ≤ (1 + y) ^ 2 := sq_nonneg _
    have := mul_le_mul (by linarith : 1 + e * (1 + ε) ≤ 1 + 1.000625 * y) hs2 (by linarith)
      (by positivity)
    exact mul_le_mul_of_nonneg_right this h1y
  have q2 : (1 + ε) * (1 + 2 * y) * (1 / 20 - y / 2) ≤ 1.00125 * (1 + 2 * y) * (1 / 20 - y / 2) := by
    have h0 : 0 ≤ (1 + 2 * y) * (1 / 20 - y / 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have q3 : 11 / 10 * (1 + y) * (1 + y / 2 - y ^ 2 / 8) ≤ 11 / 10 * (1 + y) * a :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have q4 : (1 + 1.000625 * y) * 1.000625 * (1 + y) ^ 2 + 1.00125 * (1 + 2 * y) * (1 / 20 - y / 2)
      ≤ 11 / 10 * (1 + y) * (1 + y / 2 - y ^ 2 / 8) := by
    have hYy : 0 ≤ 0.040025 - y := by linarith
    nlinarith [mul_nonneg (mul_nonneg hy0 hYy) hy0, mul_nonneg hy0 hYy,
      mul_nonneg (mul_nonneg (mul_nonneg hy0 hYy) hy0) hy0]
  have hneg : ((1 + e * (1 + ε)) * a - W * ((1 + y) / 2) - 11 / 10 * (1 - W / 2)) * ((1 + y) * a)
      ≤ 0 := by rw [key]; linarith
  have := nonpos_of_mul_nonpos_left hneg hya
  linarith

/-- **The box constant**: for `c ≥ 80`, `χ ≥ 0`, `D = c² − χ ≥ 5c` and `ξ₀ = 1 + 1/(2D)`, `W = wP(ξ₀) ≤ 1.0195` and
`[(1 + d₀)aP(ξ₀) − W(ξ₀ − 1)qP(ξ₀)]/(1 − W/2) ≤ 11/10` with `d₀ = 2c²ξ₀(ξ₀ − 1)/D`. -/
theorem eeb_constant {c χ ξ₀ : ℝ} (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hD : 5 * c ≤ c ^ 2 - χ)
    (hξ₀ : ξ₀ = 1 + 1 / (2 * (c ^ 2 - χ))) :
    wP c χ ξ₀ ≤ 1.0195 ∧
    ((1 + 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ)) * aP c χ ξ₀ - wP c χ ξ₀ * (ξ₀ - 1) * qP c χ ξ₀)
      / (1 - wP c χ ξ₀ / 2) ≤ 11 / 10 := by
  obtain ⟨D, rfl⟩ : ∃ D, χ = c ^ 2 - D := ⟨c ^ 2 - χ, by ring⟩
  have eD : c ^ 2 - (c ^ 2 - D) = D := by ring
  rw [eD] at hD hξ₀ ⊢
  have hD400 : 400 ≤ D := by linarith
  have hD0 : 0 < D := by linarith
  set ε := 1 / (2 * D) with hεdef
  set e := c ^ 2 / D ^ 2 with hedef
  set s := 1 + ε / 2 with hsdef
  set y := e * s with hydef
  have hε0 : 0 < ε := by positivity
  have hε : ε ≤ 1 / 800 := by
    rw [hεdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have he0 : 0 ≤ e := by positivity
  have he : e ≤ 1 / 25 := by
    rw [hedef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hD hD (by positivity) (by positivity)]
  have h1 : 1 < ξ₀ := by rw [hξ₀]; linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hχc : c ^ 2 - D < c ^ 2 := by linarith
  have hεD : ε * D = 1 / 2 := by rw [hεdef]; field_simp
  have heD : e * D ^ 2 = c ^ 2 := by rw [hedef]; field_simp
  have hp : pP ξ₀ = 2 * ε * s := by rw [pP, hξ₀, hsdef]; ring
  have hq : qP c (c ^ 2 - D) ξ₀ = D * (1 + y) := by
    rw [qP, hξ₀, hydef, hsdef]
    have : c ^ 2 * ε = e * D / 2 := by rw [← heD]; linear_combination e * D * hεD
    linear_combination (2 + ε) * this
  have hd : dP c (c ^ 2 - D) ξ₀ = 2 * ξ₀ * D * (1 + 2 * y) := by
    have hpq : pP ξ₀ = ξ₀ ^ 2 - 1 := rfl
    have : 2 * c ^ 2 * ξ₀ ^ 2 - c ^ 2 - (c ^ 2 - D) = D + 2 * c ^ 2 * pP ξ₀ := by rw [hpq]; ring
    rw [dP, this, hp, hydef]
    have h2 : c ^ 2 * ε = e * D / 2 := by rw [← heD]; linear_combination e * D * hεD
    linear_combination 2 * ξ₀ * (4 * s) * h2
  have ha := aP_pos h1 hc2 hχc
  have ha2 : aP c (c ^ 2 - D) ξ₀ ^ 2 = s * (1 + y) := by
    rw [aP_sq h1 hc2 hχc, hp, hq]
    linear_combination 2 * s * (1 + y) * hεD
  have hW : wP c (c ^ 2 - D) ξ₀ * ((1 + y) * aP c (c ^ 2 - D) ξ₀) = (1 + ε) * (1 + 2 * y) := by
    have hne : aP c (c ^ 2 - D) ξ₀ ≠ 0 := ha.ne'
    have hy1 : 1 + y ≠ 0 := by positivity
    rw [wP, hd, hq]
    field_simp
    rw [hξ₀]; ring
  have hd0 : 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / D = e * (1 + ε) := by
    rw [hξ₀, hedef, hεdef]; field_simp; ring
  have hxq : wP c (c ^ 2 - D) ξ₀ * (ξ₀ - 1) * qP c (c ^ 2 - D) ξ₀
      = wP c (c ^ 2 - D) ξ₀ * ((1 + y) / 2) := by
    rw [hq, show ξ₀ - 1 = ε by rw [hξ₀]; ring]
    linear_combination wP c (c ^ 2 - D) ξ₀ * (1 + y) * hεD
  rw [hd0, hxq]
  exact box_scaled hε0 hε he0 he rfl rfl ha ha2 hW

end Cvs.Prolate.CorrectedEnergyAntitone
