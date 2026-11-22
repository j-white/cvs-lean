import Mathlib
import Cvs.Prolate.Mellin.ForcingComplexLogTelescope
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningErrorsSummed
import Cvs.Prolate.Mellin.PastTurningRootSizes
import Cvs.Prolate.Mellin.PastTurningStepErrors
import Cvs.Prolate.Mellin.PastTurningStepForcing

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frozen forcing summed along a line past the turning point

On the region of Cvs.Prolate.Mellin.PastTurningContraction with `c ≥ 6000/ε²`: `|rρ²| ≤ 1 − √ε/4`, so `Re p, Re q ≥ √ε/4`; `|β| ≤ 330/(εc)`,
`|e/(pq)| ≤ 387200c²/(ε²|m|⁴)` and the shift term is at most `16/(√ε|m|²)`. Along `s_k = s₀ + 2k`,
`|Σ_{k<K} β_k − ½(log p_K − log p₀) + ½(log(1 + r_K) − log(1 + r₀))| ≤ E2U(ε, c) = 254100/(ε²c) + 6/(√ε c)`.
-/

noncomputable section

open Complex Finset

namespace Cvs.Prolate.Mellin.PastTurningForcingSum

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (rhoStar zeta)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)
open Cvs.Prolate.Mellin.NearRegionBetaStep (betaf)
open Cvs.Prolate.Mellin.FrozenForcingIdentities (rr pp qq one_sub_betaf_mul one_add_Af_sq shift_identity rr_sub)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)

variable {ε c χ : ℝ} {s : ℂ}

theorem Up.norm_s1_ge (h : Up ε c χ s) : ‖s + 3 / 2‖ / 2 ≤ ‖s + 1‖ := by
  have := norm_sub_norm_le (s + 3 / 2) (1 / 2 : ℂ)
  rw [show s + 3 / 2 - 1 / 2 = s + 1 by ring] at this
  have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge h
  norm_num at this; linarith [h.c_ge]

/-- `|r(s)| ≤ 1 + 1/(2c)` and the bound `|r(s)ζ|... ` used for `p` and `q`. -/
theorem Up.norm_rr_le (h : Up ε c χ s) : ‖rr s‖ ≤ 1 + Real.sqrt ε / 128 := by
  have hc := h.c_pos
  have hε := h.hε
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hrr : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hs1 : 2 * c ≤ ‖s + 1‖ := by have := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_add_ge h 1; push_cast at this; exact this
  have hrat : ‖rr s‖ ≤ 1 + 1 / (2 * c) := by
    have hpos : 0 < ‖s + 1‖ := by linarith
    unfold rr
    rw [norm_div, div_le_iff₀ hpos]
    have := norm_add_le (s + 1) 1
    rw [show s + 1 + 1 = s + 2 by ring, norm_one] at this
    have : 1 ≤ 1 / (2 * c) * ‖s + 1‖ := by rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]; linarith
    nlinarith
  have hc2 : 1 / (2 * c) ≤ r / 128 := by
    have hcε := h.hc
    rw [div_le_iff₀ (by positivity)] at hcε
    have hcr4 : 64 ≤ c * r ^ 4 := by rw [show r ^ 4 = ε ^ 2 by rw [← hrr]; ring]; linarith
    have hr3 : r ^ 3 ≤ 1 := pow_le_one₀ hr0.le hr1
    have hr4 : r ^ 4 ≤ r := by nlinarith
    have hcr : 64 ≤ c * r := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-- `|r(s)|·|ζ(t)|² ≤ 1 − √ε/4` for `t` on the region. -/
theorem Up.norm_rr_zeta_sq_le (h : Up ε c χ s) {t : ℂ} (ht : Up ε c χ t) :
    ‖rr s‖ * ‖zeta c χ t‖ ^ 2 ≤ 1 - Real.sqrt ε / 4 := by
  have hε := h.hε
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hrr : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hq := ht.normSq_zeta_le
  rw [Complex.normSq_eq_norm_sq] at hq
  have hs2 : 7 / 10 * r ≤ Real.sqrt (ε / 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
  have hq₀ : 1 / (1 + 2 * Real.sqrt (ε / 2)) ≤ 1 / (1 + 7 / 5 * r) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hR := Up.norm_rr_le h
  calc ‖rr s‖ * ‖zeta c χ t‖ ^ 2 ≤ (1 + r / 128) * (1 / (1 + 7 / 5 * r)) := by
        gcongr; exact hq.trans hq₀
    _ ≤ 1 - r / 4 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith

theorem Up.re_one_add_ge (h : Up ε c χ s) {t : ℂ} (ht : Up ε c χ t) {ρ : ℂ} (hρ : ‖ρ‖ ≤ ‖zeta c χ t‖) :
    Real.sqrt ε / 4 ≤ (1 + rr s * ρ ^ 2).re := by
  have h1 := Up.norm_rr_zeta_sq_le h ht
  have h2 : ‖rr s * ρ ^ 2‖ ≤ 1 - Real.sqrt ε / 4 := by
    rw [norm_mul, norm_pow]
    calc ‖rr s‖ * ‖ρ‖ ^ 2 ≤ ‖rr s‖ * ‖zeta c χ t‖ ^ 2 := by gcongr
      _ ≤ _ := h1
  have h3 : -(rr s * ρ ^ 2).re ≤ ‖rr s * ρ ^ 2‖ := by
    have := Complex.abs_re_le_norm (rr s * ρ ^ 2); linarith [neg_abs_le (rr s * ρ ^ 2).re]
  simp only [add_re, one_re]
  linarith

/-- **`Re p ≥ √ε/4`.** -/
theorem Up.re_pp_ge (h : Up ε c χ s) : Real.sqrt ε / 4 ≤ (pp c χ s).re :=
  Up.re_one_add_ge h h (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_rho_le h)

/-- **`Re q ≥ √ε/4`.** -/
theorem Up.re_qq_ge (h : Up ε c χ s) : Real.sqrt ε / 4 ≤ (qq c χ s).re :=
  Up.re_one_add_ge h (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_two h)
    (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_rho_le (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_two h))

theorem Up.re_one_add_rr (h : Up ε c χ s) : 0 < (1 + rr s).re := by
  have hs1 := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne h 1
  push_cast at hs1
  have e : rr s = 1 + 1 / (s + 1) := by unfold rr; field_simp; ring
  rw [e]
  have : 0 ≤ (1 / (s + 1)).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp; linarith [h.hre]
  simp only [add_re, one_re]; linarith

/-- `|β| ≤ 2640c²/(ε|m|³)`. -/
theorem Up.norm_betaf_le (h : Up ε c χ s) : ‖betaf c χ s‖ ≤ 2640 * c ^ 2 / (ε * ‖s + 3 / 2‖ ^ 3) := by
  have hε := h.hε
  have hr0 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hrr : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith [h.c_pos]
  unfold betaf
  rw [div_eq_mul_inv, norm_mul]
  calc ‖Bf c χ s‖ * ‖(1 + Af c χ s)⁻¹‖
      ≤ 660 * c ^ 2 / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 3) * (4 / Real.sqrt ε) :=
        mul_le_mul (Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_Bf_le h) (Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_inv_one_add_Af_le h)
          (norm_nonneg _) (by positivity)
    _ = 2640 * c ^ 2 / (Real.sqrt ε ^ 2 * ‖s + 3 / 2‖ ^ 3) := by field_simp; ring
    _ = 2640 * c ^ 2 / (ε * ‖s + 3 / 2‖ ^ 3) := by rw [hrr]

/-- `|e/(pq)| ≤ 387200c²/(ε²|m|⁴)` with `e = r(ρ' − ρ)²`. -/
theorem Up.norm_e_le (h : Up ε c χ s) :
    ‖rr s * (rhoStar c χ (s + 2) - rhoStar c χ s) ^ 2 / (pp c χ s * qq c χ s)‖
      ≤ 387200 * c ^ 2 / (ε ^ 2 * ‖s + 3 / 2‖ ^ 4) := by
  have hε := h.hε
  have hc := h.c_pos
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hrr : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have hp : r / 4 ≤ ‖pp c χ s‖ := (Up.re_pp_ge h).trans (Complex.re_le_norm _)
  have hq : r / 4 ≤ ‖qq c χ s‖ := (Up.re_qq_ge h).trans (Complex.re_le_norm _)
  have hR : ‖rr s‖ ≤ 2 := (Up.norm_rr_le h).trans (by linarith)
  have hd := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_rho_step_le h
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  have hden : r / 4 * (r / 4) ≤ ‖pp c χ s‖ * ‖qq c χ s‖ := mul_le_mul hp hq (by positivity) (by positivity)
  calc ‖rr s‖ * ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ^ 2 / (‖pp c χ s‖ * ‖qq c χ s‖)
      ≤ 2 * (110 * c / (r * ‖s + 3 / 2‖ ^ 2)) ^ 2 / (r / 4 * (r / 4)) := by gcongr
    _ = 387200 * c ^ 2 / ((r ^ 2) ^ 2 * ‖s + 3 / 2‖ ^ 4) := by field_simp; ring
    _ = 387200 * c ^ 2 / (ε ^ 2 * ‖s + 3 / 2‖ ^ 4) := by rw [hrr]

/-- The shift remainder `D = (r(s) − r(s+2))(ρ'² − 1)`: `|D/(p'(1 + r))| ≤ 16/(√ε|m|²)`. -/
theorem Up.norm_D_le (h : Up ε c χ s) :
    ‖(rr s - rr (s + 2)) * (rhoStar c χ (s + 2) ^ 2 - 1) / (pp c χ (s + 2) * (1 + rr s))‖
      ≤ 16 / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
  have h' := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_two h
  have hε := h.hε
  have hc := h.c_pos
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have hs1 : s + 1 ≠ 0 := by have := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne h 1; push_cast at this; exact this
  have hs3 : s + 3 ≠ 0 := by have := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne h 3; push_cast at this; exact this
  rw [rr_sub hs1 hs3]
  have hn1 := Up.norm_s1_ge h
  have hn3 : ‖s + 3 / 2‖ ≤ ‖s + 3‖ := by
    have := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_le_add h (a := 3) (by norm_num); push_cast at this; exact this
  have hρ' : ‖rhoStar c χ (s + 2)‖ ≤ 1 := by
    refine (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_rho_le h').trans ?_
    have := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_zeta_le h'
    have ht : 1 ≤ ‖Cvs.Prolate.Mellin.FrozenRootErrorIdentity.tau c χ (s + 2)‖ := by
      have := Cvs.Prolate.Mellin.PastTurningRootSizes.im_le_norm (Cvs.Prolate.Mellin.FrozenRootErrorIdentity.tau c χ (s + 2))
      linarith [h'.im_tau_ge, h'.hε]
    exact this.trans (by rw [div_le_one (by linarith)]; exact ht)
  have hnum : ‖rhoStar c χ (s + 2) ^ 2 - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_one]; nlinarith [norm_nonneg (rhoStar c χ (s + 2))]
  have hp' : r / 4 ≤ ‖pp c χ (s + 2)‖ := (Up.re_pp_ge h').trans (Complex.re_le_norm _)
  have hr' : 2 ≤ ‖1 + rr s‖ := by
    have hre := Up.re_one_add_rr h
    have e : rr s = 1 + 1 / (s + 1) := by unfold rr; field_simp; ring
    have : 2 ≤ (1 + rr s).re := by
      rw [e]
      have : 0 ≤ (1 / (s + 1)).re := by
        rw [one_div, Complex.inv_re]
        apply div_nonneg _ (Complex.normSq_nonneg _)
        simp; linarith [h.hre]
      simp only [add_re, one_re]; linarith
    exact this.trans (Complex.re_le_norm _)
  rw [norm_div, norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_ofNat]
  have hden : r / 4 * 2 ≤ ‖pp c χ (s + 2)‖ * ‖1 + rr s‖ := mul_le_mul hp' hr' (by norm_num) (by positivity)
  have hss : ‖s + 3 / 2‖ / 2 * ‖s + 3 / 2‖ ≤ ‖s + 1‖ * ‖s + 3‖ := mul_le_mul hn1 hn3 (by positivity) (by positivity)
  calc 2 / (‖s + 1‖ * ‖s + 3‖) * ‖rhoStar c χ (s + 2) ^ 2 - 1‖ / (‖pp c χ (s + 2)‖ * ‖1 + rr s‖)
      ≤ 2 / (‖s + 3 / 2‖ / 2 * ‖s + 3 / 2‖) * 2 / (r / 4 * 2) := by gcongr
    _ = 16 / (r * ‖s + 3 / 2‖ ^ 2) := by field_simp; ring

/-- `Σ_{k<K} 1/|m_k|⁴ ≤ 1/(8c³)`. -/
theorem sum_inv_four_le {s₀ : ℂ} (h : Up ε c χ s₀) (K : ℕ) :
    ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 4 ≤ 1 / (8 * c ^ 3) := by
  have hc := h.c_pos
  calc ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 4
      ≤ ∑ k ∈ range K, 1 / (2 * c) ^ 2 * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2) := by
        refine sum_le_sum fun k _ => ?_
        have hm := Cvs.Prolate.Mellin.PastTurningErrorsSummed.Up.two_c_le_norm_m h k
        have hp := Cvs.Prolate.Mellin.PastTurningErrorsSummed.Up.norm_m_pos h k
        rw [div_mul_div_comm, one_mul, show ‖s₀ + 2 * (k : ℂ) + 3 / 2‖ ^ 4
          = ‖s₀ + 2 * (k : ℂ) + 3 / 2‖ ^ 2 * ‖s₀ + 2 * (k : ℂ) + 3 / 2‖ ^ 2 by ring]
        exact one_div_le_one_div_of_le (by positivity) (by gcongr)
    _ = 1 / (2 * c) ^ 2 * ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2 := by rw [mul_sum]
    _ ≤ 1 / (2 * c) ^ 2 * (1 / (2 * c)) := by gcongr; exact Cvs.Prolate.Mellin.PastTurningErrorsSummed.Up.sum_inv_sq_le h K
    _ = 1 / (8 * c ^ 3) := by field_simp; ring

/-- The forcing budget past the turning point. -/
def E2U (ε c : ℝ) : ℝ := 254100 / (ε ^ 2 * c) + 6 / (Real.sqrt ε * c)

/-- Pointwise shift bound at `s₀ + 2k`. -/
theorem sum_betaf_shift {s₀ : ℂ} (h : Up ε c χ s₀) (hrc : 6000 ≤ Real.sqrt ε * c) (k : ℕ) :
    ‖Complex.log (qq c χ (s₀ + 2 * k)) - Complex.log (pp c χ (s₀ + 2 * ((k + 1 : ℕ) : ℂ)))
        - Complex.log (1 + rr (s₀ + 2 * k)) + Complex.log (1 + rr (s₀ + 2 * ((k + 1 : ℕ) : ℂ)))‖
      ≤ 24 / Real.sqrt ε * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2) := by
  have hc := h.c_pos
  have hε := h.hε
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hk := Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k
  have hk' := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_two hk
  set s := s₀ + 2 * (k : ℂ)
  have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge hk
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have hm3 : (2 * c) ^ 3 ≤ ‖s + 3 / 2‖ ^ 3 := pow_le_pow_left₀ (by positivity) hm 3
  have hm4 : (2 * c) ^ 4 ≤ ‖s + 3 / 2‖ ^ 4 := pow_le_pow_left₀ (by positivity) hm 4
  have hm2 : (2 * c) ^ 2 ≤ ‖s + 3 / 2‖ ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
  have hs2 : s₀ + 2 * ((k + 1 : ℕ) : ℂ) = s + 2 := by simp only [s]; push_cast; ring
  rw [hs2]
  have hD := Up.norm_D_le hk
  have hD' : ‖(rr s - rr (s + 2)) * (rhoStar c χ (s + 2) ^ 2 - 1) / (pp c χ (s + 2) * (1 + rr s))‖ ≤ 1 / 2 := by
    refine hD.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hm2 (show (0 : ℝ) ≤ r by positivity)]
  have hs1 : s + 1 ≠ 0 := by have := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne hk 1; push_cast at this; exact this
  have hs3 : s + 3 ≠ 0 := by have := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne hk 3; push_cast at this; exact this
  have hsmall : ‖rr s - rr (s + 2)‖ ≤ 8 / ‖s + 3 / 2‖ ^ 2 := by
    rw [rr_sub hs1 hs3, norm_div, norm_mul, Complex.norm_ofNat]
    have hn1 := Up.norm_s1_ge hk
    have hn3 : ‖s + 3 / 2‖ ≤ ‖s + 3‖ := by
      have := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_le_add hk (a := 3) (by norm_num); push_cast at this; exact this
    calc 2 / (‖s + 1‖ * ‖s + 3‖) ≤ 2 / (‖s + 3 / 2‖ / 2 * ‖s + 3 / 2‖) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul hn1 hn3 (by positivity) (norm_nonneg _))
      _ = 4 / ‖s + 3 / 2‖ ^ 2 := by field_simp; norm_num
      _ ≤ 8 / ‖s + 3 / 2‖ ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hp' : r / 4 ≤ ‖pp c χ (s + 2)‖ := (Up.re_pp_ge hk').trans (Complex.re_le_norm _)
  have hρ' : ‖rhoStar c χ (s + 2)‖ ≤ 1 := by
    refine (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_rho_le hk').trans ?_
    have := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_zeta_le hk'
    have ht : 1 ≤ ‖Cvs.Prolate.Mellin.FrozenRootErrorIdentity.tau c χ (s + 2)‖ := by
      have := Cvs.Prolate.Mellin.PastTurningRootSizes.im_le_norm (Cvs.Prolate.Mellin.FrozenRootErrorIdentity.tau c χ (s + 2))
      linarith [hk'.im_tau_ge, hk'.hε]
    exact this.trans (by rw [div_le_one (by linarith)]; exact ht)
  have hq1 : ‖qq c χ s / pp c χ (s + 2) - 1‖ ≤ 1 / 2 := by
    have hp0 : pp c χ (s + 2) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hp'; linarith
    have hqp : qq c χ s - pp c χ (s + 2) = (rr s - rr (s + 2)) * rhoStar c χ (s + 2) ^ 2 := by
      unfold qq pp; ring
    have e : qq c χ s / pp c χ (s + 2) - 1 = (rr s - rr (s + 2)) * rhoStar c χ (s + 2) ^ 2 / pp c χ (s + 2) := by
      rw [div_sub_one hp0, hqp]
    rw [e, norm_div, norm_mul, norm_pow]
    have : ‖rhoStar c χ (s + 2)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (rhoStar c χ (s + 2))]
    calc ‖rr s - rr (s + 2)‖ * ‖rhoStar c χ (s + 2)‖ ^ 2 / ‖pp c χ (s + 2)‖
        ≤ 8 / ‖s + 3 / 2‖ ^ 2 * 1 / (r / 4) :=
          div_le_div₀ (by positivity) (mul_le_mul hsmall this (by positivity) (by positivity))
            (by positivity) hp'
      _ ≤ 1 / 2 := by
          rw [mul_one, div_div, div_le_iff₀ (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hm2 (show (0 : ℝ) ≤ r by positivity)]
  have hr2 : ‖(1 + rr (s + 2)) / (1 + rr s) - 1‖ ≤ 1 / 2 := by
    have hre := Up.re_one_add_rr hk
    have h1r : 1 + rr s ≠ 0 := fun h0 => by rw [h0] at hre; simp at hre
    have hn : 1 ≤ ‖1 + rr s‖ := by
      have e : rr s = 1 + 1 / (s + 1) := by unfold rr; field_simp; ring
      have : 1 ≤ (1 + rr s).re := by
        rw [e]
        have : 0 ≤ (1 / (s + 1)).re := by
          rw [one_div, Complex.inv_re]
          apply div_nonneg _ (Complex.normSq_nonneg _)
          simp; linarith [hk.hre]
        simp only [add_re, one_re]; linarith
      exact this.trans (Complex.re_le_norm _)
    rw [show (1 + rr (s + 2)) / (1 + rr s) - 1 = -(rr s - rr (s + 2)) / (1 + rr s) by field_simp; ring,
      norm_div, norm_neg]
    calc ‖rr s - rr (s + 2)‖ / ‖1 + rr s‖ ≤ 8 / ‖s + 3 / 2‖ ^ 2 / 1 :=
        div_le_div₀ (by positivity) hsmall zero_lt_one hn
      _ ≤ 1 / 2 := by
          rw [div_one, div_le_iff₀ (by positivity)]; nlinarith
  have hr4 : 0 < Real.sqrt ε / 4 := by positivity
  have hqre : 0 < (qq c χ s).re := lt_of_lt_of_le hr4 (Up.re_qq_ge hk)
  have hpre : 0 < (pp c χ (s + 2)).re := lt_of_lt_of_le hr4 (Up.re_pp_ge hk')
  have hsh := Cvs.Prolate.Mellin.ForcingComplexLogTelescope.shift_c (shift_identity c χ s) hqre
    hpre (Up.re_one_add_rr hk) (Up.re_one_add_rr hk') hq1 hr2 hD'
  refine hsh.trans ?_
  calc 3 / 2 * ‖(rr s - rr (s + 2)) * (rhoStar c χ (s + 2) ^ 2 - 1) / (pp c χ (s + 2) * (1 + rr s))‖
      ≤ 3 / 2 * (16 / (r * ‖s + 3 / 2‖ ^ 2)) := mul_le_mul_of_nonneg_left hD (by norm_num)
    _ = 24 / r * (1 / ‖s + 3 / 2‖ ^ 2) := by field_simp; ring

/-- Pointwise step and shift bounds at `s₀ + 2k`. -/
theorem sum_betaf_pt {s₀ : ℂ} (h : Up ε c χ s₀) (hεc : 6000 ≤ ε * c) (hrc : 6000 ≤ Real.sqrt ε * c) (k : ℕ) :
    ‖betaf c χ (s₀ + 2 * k) - 1 / 2 * (Complex.log (qq c χ (s₀ + 2 * k)) - Complex.log (pp c χ (s₀ + 2 * k)))‖
      ≤ (2640 * c ^ 2 / ε) ^ 2 * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 6)
        + 3 / 4 * (387200 * c ^ 2 / ε ^ 2) * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 4)
    ∧ ‖Complex.log (qq c χ (s₀ + 2 * k)) - Complex.log (pp c χ (s₀ + 2 * ((k + 1 : ℕ) : ℂ)))
        - Complex.log (1 + rr (s₀ + 2 * k)) + Complex.log (1 + rr (s₀ + 2 * ((k + 1 : ℕ) : ℂ)))‖
      ≤ 24 / Real.sqrt ε * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2) := by
  have hc := h.c_pos
  have hε := h.hε
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hk := Cvs.Prolate.Mellin.PastTurningStepErrors.Up.line h k
  have hk' := Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_two hk
  set s := s₀ + 2 * (k : ℂ)
  have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge hk
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have hm3 : (2 * c) ^ 3 ≤ ‖s + 3 / 2‖ ^ 3 := pow_le_pow_left₀ (by positivity) hm 3
  have hm4 : (2 * c) ^ 4 ≤ ‖s + 3 / 2‖ ^ 4 := pow_le_pow_left₀ (by positivity) hm 4
  have hm2 : (2 * c) ^ 2 ≤ ‖s + 3 / 2‖ ^ 2 := pow_le_pow_left₀ (by positivity) hm 2
  have hA0 := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_one_add_Af_ge hk
  have hAne : 1 + Af c χ s ≠ 0 := fun h0 => by rw [h0, norm_zero] at hA0; linarith
  have hβ := Up.norm_betaf_le hk
  have hβ' : ‖betaf c χ s‖ ≤ 1 / 2 := by
    refine hβ.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hm3 (show (0 : ℝ) ≤ ε by positivity)]
  have he := Up.norm_e_le hk
  have he' : ‖rr s * (rhoStar c χ (s + 2) - rhoStar c χ s) ^ 2 / (pp c χ s * qq c χ s)‖ ≤ 1 / 2 := by
    refine he.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : 6000 ^ 2 ≤ (ε * c) ^ 2 := pow_le_pow_left₀ (by norm_num) hεc 2
    nlinarith [mul_le_mul_of_nonneg_left hm4 (show (0 : ℝ) ≤ ε ^ 2 by positivity)]
  have hstep := Cvs.Prolate.Mellin.ForcingComplexLogTelescope.step_c (one_sub_betaf_mul hAne) (one_add_Af_sq c χ s) hAne
    (by linarith [Up.re_pp_ge hk]) (by linarith [Up.re_qq_ge hk]) hβ' he'
  refine ⟨hstep.trans ?_, ?_⟩
  · have b1 : ‖betaf c χ s‖ ^ 2 ≤ (2640 * c ^ 2 / ε) ^ 2 * (1 / ‖s + 3 / 2‖ ^ 6) := by
      calc ‖betaf c χ s‖ ^ 2 ≤ (2640 * c ^ 2 / (ε * ‖s + 3 / 2‖ ^ 3)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hβ 2
        _ = _ := by field_simp
    have b2 : 3 / 4 * ‖rr s * (rhoStar c χ (s + 2) - rhoStar c χ s) ^ 2 / (pp c χ s * qq c χ s)‖
        ≤ 3 / 4 * (387200 * c ^ 2 / ε ^ 2) * (1 / ‖s + 3 / 2‖ ^ 4) := by
      rw [mul_assoc]; gcongr; refine he.trans (le_of_eq ?_); field_simp
    linarith
  · exact sum_betaf_shift h hrc k

/-- **The frozen forcing summed along a line past the turning point.** -/
theorem sum_betaf {s₀ : ℂ} (h : Up ε c χ s₀) (hcb : 6000 / ε ^ 2 ≤ c) (K : ℕ) :
    ‖∑ k ∈ range K, betaf c χ (s₀ + 2 * k)
        - 1 / 2 * (Complex.log (pp c χ (s₀ + 2 * K)) - Complex.log (pp c χ (s₀ + 2 * (0 : ℕ))))
        + 1 / 2 * (Complex.log (1 + rr (s₀ + 2 * K)) - Complex.log (1 + rr (s₀ + 2 * (0 : ℕ))))‖
      ≤ E2U ε c := by
  have hc := h.c_pos
  have hε := h.hε
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hcbig : 6000 / ε ≤ c := by
    have : 6000 / ε ≤ 6000 / ε ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith [h.hε1]
    linarith
  have hεc : 6000 ≤ ε * c := by rw [div_le_iff₀ hε] at hcbig; linarith
  have hrc : 6000 ≤ r * c := by
    have : ε ≤ r := by
      have := Real.sqrt_le_sqrt h.hε1; rw [Real.sqrt_one] at this
      calc ε = r * r := (Real.mul_self_sqrt hε.le).symm
        _ ≤ r * 1 := by gcongr
        _ = r := by ring
    nlinarith
  -- pointwise data at `s_k`
  have pt : ∀ k : ℕ,
      ‖betaf c χ (s₀ + 2 * k) - 1 / 2 * (Complex.log (qq c χ (s₀ + 2 * k)) - Complex.log (pp c χ (s₀ + 2 * k)))‖
        ≤ (2640 * c ^ 2 / ε) ^ 2 * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 6)
          + 3 / 4 * (387200 * c ^ 2 / ε ^ 2) * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 4)
      ∧ ‖Complex.log (qq c χ (s₀ + 2 * k)) - Complex.log (pp c χ (s₀ + 2 * ((k + 1 : ℕ) : ℂ)))
          - Complex.log (1 + rr (s₀ + 2 * k)) + Complex.log (1 + rr (s₀ + 2 * ((k + 1 : ℕ) : ℂ)))‖
        ≤ 24 / r * (1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2) :=
    fun k => sum_betaf_pt h hεc hrc k
  have hsum := Cvs.Prolate.Mellin.ForcingComplexLogTelescope.sum_c_le (β := fun k : ℕ => betaf c χ (s₀ + 2 * k))
    (ℓp := fun k : ℕ => Complex.log (pp c χ (s₀ + 2 * k)))
    (ℓq := fun k : ℕ => Complex.log (qq c χ (s₀ + 2 * k)))
    (ℓr := fun k : ℕ => Complex.log (1 + rr (s₀ + 2 * k))) K (fun k _ => (pt k).1) (fun k _ => (pt k).2)
  refine hsum.trans ?_
  have s6 := Cvs.Prolate.Mellin.PastTurningErrorsSummed.Up.sum_inv_six_le h K
  have s4 := sum_inv_four_le h K
  have s2 := Cvs.Prolate.Mellin.PastTurningErrorsSummed.Up.sum_inv_sq_le h K
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
  unfold E2U
  calc (2640 * c ^ 2 / ε) ^ 2 * ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 6
        + 3 / 4 * (387200 * c ^ 2 / ε ^ 2) * ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 4
        + 1 / 2 * (24 / r * ∑ k ∈ range K, 1 / ‖s₀ + 2 * k + 3 / 2‖ ^ 2)
      ≤ (2640 * c ^ 2 / ε) ^ 2 * (1 / (32 * c ^ 5)) + 3 / 4 * (387200 * c ^ 2 / ε ^ 2) * (1 / (8 * c ^ 3))
        + 1 / 2 * (24 / r * (1 / (2 * c))) := by gcongr
    _ = 254100 / (ε ^ 2 * c) + 6 / (r * c) := by field_simp; ring

end Cvs.Prolate.Mellin.PastTurningForcingSum
