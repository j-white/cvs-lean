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
# The corrected-energy pair for increasing `w`, and the prolate angular instance

For `ψ' = u/p`, `u' = −qψ`, `a² = pq`, `a' = wq` with `w` increasing in `[0, 2)`, `(E + wψu)/(1 + w/2)` is antitone
and `(E + wψu)/(1 − w/2)` is monotone, so `R(w t₁)E` bounds `E` both ways across `[t₀, t₁]`, `R(w) = (2 − w)/(2 + w)`.
In the angular zone `c²s² < χ` of the prolate equation `w′ ≥ 0` by an exact sum of squares, and for `χ = c²a²`
`w(s) = s(2(a² − s²) + 1 − a²)/(c(a² − s²)^{3/2}√(1 − s²))`.
-/

namespace Cvs.Prolate.CorrectedEnergyPairAngular

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

section pair

variable {ψ u p q a w w' : ℝ → ℝ} {t₀ t₁ : ℝ}

/-- **The plus-corrected energy is antitone**: for `w ≥ 0` increasing, `(E + wψu)/(1 + w/2)` does not increase. -/
theorem corrected_add_antitoneOn
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Icc t₀ t₁, 0 ≤ w' t) (hw0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ w t) :
    AntitoneOn (fun s => (energy a ψ u s + w s * (ψ s * u s)) / (1 + w s / 2)) (Icc t₀ t₁) := by
  set F : ℝ → ℝ := fun s => energy a ψ u s + w s * (ψ s * u s) with hFdef
  have hF : ∀ t ∈ Icc t₀ t₁, HasDerivAt F (w' t * (ψ t * u t)) t := fun t ht =>
    hasDerivAt_energy_add (ha t ht) (hp t ht) (hapq t ht) (hψ t ht) (hu t ht) (haw t ht) (hw t ht)
  have hg : ∀ t ∈ Icc t₀ t₁, HasDerivAt (fun s => 1 + w s / 2) (w' t / 2) t := fun t ht =>
    ((hw t ht).div_const 2).const_add 1
  have hpos : ∀ t ∈ Icc t₀ t₁, 0 < 1 + w t / 2 := fun t ht => by linarith [hw0 t ht]
  apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
  · exact fun t ht => ((hF t ht).fun_div (hg t ht) (hpos t ht).ne').continuousAt.continuousWithinAt
  · rw [interior_Icc]
    exact fun t ht => ((hF t (Ioo_subset_Icc_self ht)).fun_div (hg t (Ioo_subset_Icc_self ht))
      (hpos t (Ioo_subset_Icc_self ht)).ne').differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro t ht
    have ht' := Ioo_subset_Icc_self ht
    rw [((hF t ht').fun_div (hg t ht') (hpos t ht').ne').deriv]
    have e : (w' t * (ψ t * u t) * (1 + w t / 2) - F t * (w' t / 2)) / (1 + w t / 2) ^ 2
        = w' t * (ψ t * u t - energy a ψ u t / 2) / (1 + w t / 2) ^ 2 := by simp only [hFdef]; ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have h := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht')
    have h' := le_abs_self (ψ t * u t)
    have hbr : ψ t * u t - energy a ψ u t / 2 ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (hw' t ht') hbr

/-- **The minus-corrected energy is monotone**: for `w < 2` increasing, `(E + wψu)/(1 − w/2)` does not decrease. -/
theorem corrected_sub_monotoneOn
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Icc t₀ t₁, 0 ≤ w' t) (hw2 : ∀ t ∈ Icc t₀ t₁, w t < 2) :
    MonotoneOn (fun s => (energy a ψ u s + w s * (ψ s * u s)) / (1 - w s / 2)) (Icc t₀ t₁) := by
  set F : ℝ → ℝ := fun s => energy a ψ u s + w s * (ψ s * u s) with hFdef
  have hF : ∀ t ∈ Icc t₀ t₁, HasDerivAt F (w' t * (ψ t * u t)) t := fun t ht =>
    hasDerivAt_energy_add (ha t ht) (hp t ht) (hapq t ht) (hψ t ht) (hu t ht) (haw t ht) (hw t ht)
  have hg : ∀ t ∈ Icc t₀ t₁, HasDerivAt (fun s => 1 - w s / 2) (-(w' t / 2)) t := fun t ht =>
    ((hw t ht).div_const 2).const_sub 1
  have hpos : ∀ t ∈ Icc t₀ t₁, 0 < 1 - w t / 2 := fun t ht => by linarith [hw2 t ht]
  apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ t₁)
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
    apply div_nonneg _ (sq_nonneg _)
    have h := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t ht')
    have h' := neg_abs_le (ψ t * u t)
    have hbr : 0 ≤ ψ t * u t + energy a ψ u t / 2 := by linarith
    exact mul_nonneg (hw' t ht') hbr

end pair

/-- The transport ratio `R(w) = (2 − w)/(2 + w) = (1 − w/2)/(1 + w/2)`. -/
noncomputable def Rcorr (w : ℝ) : ℝ := (2 - w) / (2 + w)

theorem Rcorr_pos {w : ℝ} (hw0 : -2 < w) (hw2 : w < 2) : 0 < Rcorr w := by
  unfold Rcorr; apply div_pos <;> linarith

theorem Rcorr_anti {w w' : ℝ} (hw : -2 < w) (hww' : w ≤ w') : Rcorr w' ≤ Rcorr w := by
  unfold Rcorr
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **The energy transport**: for `w` increasing in `[0, 2)` on `[t₀, t₁]`,
`R(w t₁)E(t₁) ≤ E(t₀)` and `R(w t₁)E(t₀) ≤ E(t₁)`. -/
theorem energy_transport {ψ u p q a w w' : ℝ → ℝ} {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hw : ∀ t ∈ Icc t₀ t₁, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Icc t₀ t₁, 0 ≤ w' t) (hw0 : ∀ t ∈ Icc t₀ t₁, 0 ≤ w t)
    (hw2 : ∀ t ∈ Icc t₀ t₁, w t < 2) :
    Rcorr (w t₁) * energy a ψ u t₁ ≤ energy a ψ u t₀ ∧ Rcorr (w t₁) * energy a ψ u t₀ ≤ energy a ψ u t₁ := by
  have hm0 : t₀ ∈ Icc t₀ t₁ := left_mem_Icc.mpr hle
  have hm1 : t₁ ∈ Icc t₀ t₁ := right_mem_Icc.mpr hle
  have mA := corrected_add_antitoneOn ha hp hapq hψ hu haw hw hw' hw0 hm0 hm1 hle
  have mM := corrected_sub_monotoneOn ha hp hapq hψ hu haw hw hw' hw2 hm0 hm1 hle
  simp only at mA mM
  have e0 := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t₀ hm0)
  have e1 := two_mul_abs_le_energy (ψ := ψ) (u := u) (ha t₁ hm1)
  have a0 := abs_le.mp (show |ψ t₀ * u t₀| ≤ energy a ψ u t₀ / 2 by linarith)
  have a1 := abs_le.mp (show |ψ t₁ * u t₁| ≤ energy a ψ u t₁ / 2 by linarith)
  have w00 := hw0 t₀ hm0
  have w10 := hw0 t₁ hm1
  have w02 := hw2 t₀ hm0
  have w12 := hw2 t₁ hm1
  have hP0 : 0 < 1 + w t₀ / 2 := by linarith
  have hP1 : 0 < 1 + w t₁ / 2 := by linarith
  have hM0 : 0 < 1 - w t₀ / 2 := by linarith
  have hM1 : 0 < 1 - w t₁ / 2 := by linarith
  have hR : Rcorr (w t₁) = (1 - w t₁ / 2) / (1 + w t₁ / 2) := by
    unfold Rcorr; field_simp
  rw [hR]
  constructor
  · -- `R E₁ ≤ F₊ t₁ ≤ F₊ t₀ ≤ E₀`
    have l1 : (1 - w t₁ / 2) / (1 + w t₁ / 2) * energy a ψ u t₁
        ≤ (energy a ψ u t₁ + w t₁ * (ψ t₁ * u t₁)) / (1 + w t₁ / 2) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hP1.le
      nlinarith [mul_le_mul_of_nonneg_left a1.1 w10]
    have l0 : (energy a ψ u t₀ + w t₀ * (ψ t₀ * u t₀)) / (1 + w t₀ / 2) ≤ energy a ψ u t₀ := by
      rw [div_le_iff₀ hP0]
      nlinarith [mul_le_mul_of_nonneg_left a0.2 w00]
    linarith
  · -- `E₀ ≤ F₋ t₀ ≤ F₋ t₁ ≤ E₁/R`
    have l0 : energy a ψ u t₀ ≤ (energy a ψ u t₀ + w t₀ * (ψ t₀ * u t₀)) / (1 - w t₀ / 2) := by
      rw [le_div_iff₀ hM0]
      nlinarith [mul_le_mul_of_nonneg_left a0.1 w00]
    have l1 : (energy a ψ u t₁ + w t₁ * (ψ t₁ * u t₁)) / (1 - w t₁ / 2)
        ≤ energy a ψ u t₁ * (1 + w t₁ / 2) / (1 - w t₁ / 2) := by
      apply div_le_div_of_nonneg_right _ hM1.le
      nlinarith [mul_le_mul_of_nonneg_left a1.2 w10]
    have h := le_trans l0 (le_trans mM l1)
    rw [le_div_iff₀ hM1] at h
    rw [div_mul_eq_mul_div, div_le_iff₀ hP1]
    linarith

section angular

variable {c χ s : ℝ}

theorem aP_sq_of_neg (hp : pP s < 0) (hq : qP c χ s < 0) : aP c χ s ^ 2 = pP s * qP c χ s :=
  sq_sqrt (mul_pos_of_neg_of_neg hp hq).le

theorem aP_pos_of_neg (hp : pP s < 0) (hq : qP c χ s < 0) : 0 < aP c χ s :=
  sqrt_pos.mpr (mul_pos_of_neg_of_neg hp hq)

/-- `a' = w q` in the angular zone `p < 0`, `q < 0`. -/
theorem hasDerivAt_aP_of_neg (hp : pP s < 0) (hq : qP c χ s < 0) :
    HasDerivAt (aP c χ) (wP c χ s * qP c χ s) s := by
  have hf : HasDerivAt (fun x => pP x * qP c χ x) (dP c χ s) s := by
    have h := ((hasDerivAt_pow 2 s).sub_const 1).mul
      (((hasDerivAt_pow 2 s).const_mul (c ^ 2)).sub_const χ)
    refine h.congr_deriv ?_
    simp only [dP, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
  have hs := hf.sqrt (mul_pos_of_neg_of_neg hp hq).ne'
  refine hs.congr_deriv ?_
  have ha := aP_pos_of_neg hp hq
  have hq' := hq.ne
  unfold wP
  rw [show √(pP s * qP c χ s) = aP c χ s from rfl]
  field_simp

/-- `w'` is the derivative of `w` in the angular zone. -/
theorem hasDerivAt_wP_of_neg (hp : pP s < 0) (hq : qP c χ s < 0) :
    HasDerivAt (wP c χ) (wP' c χ s) s := by
  have hd : HasDerivAt (dP c χ) (2 * (6 * c ^ 2 * s ^ 2 - c ^ 2 - χ)) s := by
    have h := (((hasDerivAt_pow 3 s).const_mul (4 * c ^ 2)).sub
      ((hasDerivAt_id s).const_mul (2 * (c ^ 2 + χ))))
    have e : dP c χ = fun x => 4 * c ^ 2 * x ^ 3 - 2 * (c ^ 2 + χ) * id x := by
      funext x; unfold dP; simp; ring
    rw [e]; refine h.congr_deriv ?_; simp; ring
  have hqd : HasDerivAt (qP c χ) (2 * c ^ 2 * s) s := by
    have h := ((hasDerivAt_pow 2 s).const_mul (c ^ 2)).sub_const χ
    have e : qP c χ = fun x => c ^ 2 * x ^ 2 - χ := rfl
    rw [e]; refine h.congr_deriv ?_; ring
  have hden := ((hqd.const_mul 2).fun_mul (hasDerivAt_aP_of_neg hp hq))
  have hne : 2 * qP c χ s * aP c χ s ≠ 0 := by
    have := aP_pos_of_neg hp hq
    have := hq.ne
    positivity
  have h := hd.fun_div hden hne
  have e : wP c χ = fun x => dP c χ x / (2 * qP c χ x * aP c χ x) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold wP'
  ring

/-- **`w` increases in the angular zone**: `w' ≥ 0`, from
`P = 3c⁴X(1 − X)² + c²(χ − c²X)(1 − X)² + (χ − c²X)² ≥ 0`, `X = s²`. -/
theorem wP'_nonneg_of_neg (hp : pP s < 0) (hq : qP c χ s < 0) : 0 ≤ wP' c χ s := by
  have ha := aP_pos_of_neg hp hq
  have ha2 := aP_sq_of_neg hp hq
  have hqne := hq.ne
  have hd : 0 ≤ χ - c ^ 2 * s ^ 2 := by unfold qP at hq; linarith
  have hP : 0 ≤ c ^ 4 * (2 * (s ^ 2) ^ 3 - 3 * (s ^ 2) ^ 2 + 2 * s ^ 2)
      + c ^ 2 * χ * ((s ^ 2) ^ 2 - 4 * s ^ 2 + 1) + χ ^ 2 := by
    have e : c ^ 4 * (2 * (s ^ 2) ^ 3 - 3 * (s ^ 2) ^ 2 + 2 * s ^ 2)
        + c ^ 2 * χ * ((s ^ 2) ^ 2 - 4 * s ^ 2 + 1) + χ ^ 2
        = 3 * c ^ 4 * s ^ 2 * (1 - s ^ 2) ^ 2 + c ^ 2 * (χ - c ^ 2 * s ^ 2) * (1 - s ^ 2) ^ 2
          + (χ - c ^ 2 * s ^ 2) ^ 2 := by ring
    rw [e]
    have h1 : 0 ≤ 3 * c ^ 4 * s ^ 2 * (1 - s ^ 2) ^ 2 := by positivity
    have h2 : 0 ≤ c ^ 2 * (χ - c ^ 2 * s ^ 2) * (1 - s ^ 2) ^ 2 := by positivity
    have h3 := sq_nonneg (χ - c ^ 2 * s ^ 2)
    linarith
  unfold wP' wP
  apply div_nonneg _ (sq_nonneg _)
  have key : (2 * (6 * c ^ 2 * s ^ 2 - c ^ 2 - χ) * (2 * qP c χ s * aP c χ s)
      - dP c χ s * (2 * (2 * c ^ 2 * s * aP c χ s
        + qP c χ s * (dP c χ s / (2 * qP c χ s * aP c χ s) * qP c χ s)))) * aP c χ s
      = qP c χ s * (-4 * (c ^ 4 * (2 * (s ^ 2) ^ 3 - 3 * (s ^ 2) ^ 2 + 2 * s ^ 2)
        + c ^ 2 * χ * ((s ^ 2) ^ 2 - 4 * s ^ 2 + 1) + χ ^ 2)) := by
    field_simp
    rw [ha2]
    unfold pP qP dP
    ring
  have hrhs : 0 ≤ qP c χ s * (-4 * (c ^ 4 * (2 * (s ^ 2) ^ 3 - 3 * (s ^ 2) ^ 2 + 2 * s ^ 2)
        + c ^ 2 * χ * ((s ^ 2) ^ 2 - 4 * s ^ 2 + 1) + χ ^ 2)) := by nlinarith
  by_contra hcon
  push Not at hcon
  have := mul_neg_of_neg_of_pos hcon ha
  linarith

/-- `w ≥ 0` in the angular zone for `s ≥ 0`. -/
theorem wP_nonneg_of_neg (hs : 0 ≤ s) (hp : pP s < 0) (hq : qP c χ s < 0) : 0 ≤ wP c χ s := by
  have ha := aP_pos_of_neg hp hq
  have hdP : dP c χ s ≤ 0 := by
    unfold pP at hp; unfold qP at hq; unfold dP
    have h1 : 2 * c ^ 2 * s ^ 2 - c ^ 2 - χ ≤ 0 := by nlinarith [sq_nonneg c]
    nlinarith
  have hden : 2 * qP c χ s * aP c χ s < 0 := by
    have := mul_neg_of_neg_of_pos hq ha; linarith
  exact div_nonneg_of_nonpos hdP hden.le

end angular

/-- **The prolate angular transport**: on `[t₀, t₁] ⊂ [0, √χ/c)`, `0 < c`, `χ < c²`, `w(t₁) < 2`,
`R(w t₁)E(t₁) ≤ E(t₀)` and `R(w t₁)E(t₀) ≤ E(t₁)` for every solution. -/
theorem angular_transport {ψ u : ℝ → ℝ} {c χ t₀ t₁ : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2)
    (ht₀ : 0 ≤ t₀) (hle : t₀ ≤ t₁) (ht₁ : c ^ 2 * t₁ ^ 2 < χ)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hw2 : wP c χ t₁ < 2) :
    Rcorr (wP c χ t₁) * energy (aP c χ) ψ u t₁ ≤ energy (aP c χ) ψ u t₀ ∧
      Rcorr (wP c χ t₁) * energy (aP c χ) ψ u t₀ ≤ energy (aP c χ) ψ u t₁ := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hq : ∀ t ∈ Icc t₀ t₁, qP c χ t < 0 := fun t ht => by
    have h0 : 0 ≤ t := ht₀.trans ht.1
    have h1 : t ^ 2 ≤ t₁ ^ 2 := pow_le_pow_left₀ h0 ht.2 2
    unfold qP; nlinarith
  have hp : ∀ t ∈ Icc t₀ t₁, pP t < 0 := fun t ht => by
    have h0 : 0 ≤ t := ht₀.trans ht.1
    have h1 : t ^ 2 ≤ t₁ ^ 2 := pow_le_pow_left₀ h0 ht.2 2
    have h2 : c ^ 2 * t ^ 2 < c ^ 2 * 1 := by nlinarith
    have h3 : t ^ 2 < 1 := lt_of_mul_lt_mul_left h2 hc2.le
    unfold pP; linarith
  have hwc : ContinuousOn (wP c χ) (Icc t₀ t₁) := fun t ht =>
    (hasDerivAt_wP_of_neg (hp t ht) (hq t ht)).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (wP c χ) (Icc t₀ t₁) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t₀ t₁) hwc
    · rw [interior_Icc]; exact fun t ht =>
        (hasDerivAt_wP_of_neg (hp t (Ioo_subset_Icc_self ht))
          (hq t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      have ht' := Ioo_subset_Icc_self ht
      rw [(hasDerivAt_wP_of_neg (hp t ht') (hq t ht')).deriv]
      exact wP'_nonneg_of_neg (hp t ht') (hq t ht')
  have hm1 : t₁ ∈ Icc t₀ t₁ := right_mem_Icc.mpr hle
  exact energy_transport hle (fun t ht => aP_pos_of_neg (hp t ht) (hq t ht))
    (fun t ht => (hp t ht).ne) (fun t ht => aP_sq_of_neg (hp t ht) (hq t ht)) hψ hu
    (fun t ht => hasDerivAt_aP_of_neg (hp t ht) (hq t ht))
    (fun t ht => hasDerivAt_wP_of_neg (hp t ht) (hq t ht))
    (fun t ht => wP'_nonneg_of_neg (hp t ht) (hq t ht))
    (fun t ht => wP_nonneg_of_neg (ht₀.trans ht.1) (hp t ht) (hq t ht))
    (fun t ht => lt_of_le_of_lt (hmono ht hm1 ht.2) hw2)

/-- **The angular rate in closed form**: for `χ = c²a²`, `0 ≤ s < a < 1`,
`w(s) = s(2(a² − s²) + (1 − a²))/(c(a² − s²)√(a² − s²)√(1 − s²))`. -/
theorem wP_eq_angular {c χ a s : ℝ} (hc : 0 < c) (ha1 : a < 1) (hχ : χ = c ^ 2 * a ^ 2)
    (hs0 : 0 ≤ s) (hsa : s < a) :
    wP c χ s = s * (2 * (a ^ 2 - s ^ 2) + (1 - a ^ 2))
      / (c * (a ^ 2 - s ^ 2) * √(a ^ 2 - s ^ 2) * √(1 - s ^ 2)) := by
  have hA : 0 < a ^ 2 - s ^ 2 := by nlinarith
  have hB : 0 < 1 - s ^ 2 := by nlinarith
  have haP : aP c χ s = c * √(a ^ 2 - s ^ 2) * √(1 - s ^ 2) := by
    unfold aP pP qP
    rw [hχ]
    have e : (s ^ 2 - 1) * (c ^ 2 * s ^ 2 - c ^ 2 * a ^ 2) = c ^ 2 * (a ^ 2 - s ^ 2) * (1 - s ^ 2) := by
      ring
    rw [e, sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_sq hc.le]
  have hqP : qP c χ s = -(c ^ 2 * (a ^ 2 - s ^ 2)) := by unfold qP; rw [hχ]; ring
  have hdP : dP c χ s = -(2 * s * c ^ 2 * (2 * (a ^ 2 - s ^ 2) + (1 - a ^ 2))) := by
    unfold dP; rw [hχ]; ring
  have hsA := sqrt_pos.mpr hA
  have hsB := sqrt_pos.mpr hB
  unfold wP
  rw [haP, hqP, hdP]
  field_simp

end Cvs.Prolate.CorrectedEnergyPairAngular
