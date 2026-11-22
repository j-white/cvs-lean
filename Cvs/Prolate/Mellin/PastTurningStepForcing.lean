import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootClosedBounds
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootFirstDifference
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningRootSizes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The step coefficient and forcing past the turning point

On the region of Cvs.Prolate.Mellin.PastTurningContraction, with `m = s + 3/2`: `|ω(s+2)/(s+4) − ω(s)/(s+2)| ≤ 3/(2|m|²)`,
`|ζ(s+2) − ζ(s)| ≤ 108c/(√ε|m|²)`, `|ρ*(s+2) − ρ*(s)| ≤ 110c/(√ε|m|²)`, `|B| ≤ 660c²/(√ε|m|³)`,
`|A| ≤ 1 − √ε/4`, `|(1 + A)⁻¹| ≤ 4/√ε` and `|A(s+2) − A(s)| ≤ 1340c²/(√ε|m|³)`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.PastTurningStepForcing

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (csqrt csqrt_sq omega omega_sq tau zeta rhoStar)
open Cvs.Prolate.Mellin.FrozenRootClosedBounds (norm_omega_sub_le)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)
open Cvs.Prolate.Mellin.PastTurningRootSizes

variable {ε c χ : ℝ} {s : ℂ}

theorem Up.norm_m_ge (h : Up ε c χ s) : 2 * c ≤ ‖s + 3 / 2‖ := by
  have := Up.norm_add_ge h (3 / 2); push_cast at this; exact this

theorem Up.norm_m_le_add (h : Up ε c χ s) {a : ℝ} (ha : 3 / 2 ≤ a) : ‖s + 3 / 2‖ ≤ ‖s + a‖ := by
  have := norm_add_mono (s := s) (by linarith [h.hre]) (a := 3 / 2) (b := a) (by norm_num) ha
  push_cast at this; exact this

/-- `|ζ| ≤ 3c/|m|`. -/
theorem Up.norm_zeta_le_m (h : Up ε c χ s) : ‖zeta c χ s‖ ≤ 3 * c / ‖s + 3 / 2‖ := by
  have hc := h.c_pos
  have hm := Up.norm_m_ge h
  have ht := Up.norm_tau_ge h
  have hz := Up.norm_zeta_le h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have htpos : 0 < ‖tau c χ s‖ := lt_of_lt_of_le (by positivity) ht
  refine hz.trans ?_
  rw [div_le_div_iff₀ htpos hmpos]
  rw [div_le_iff₀ (by positivity)] at ht
  linarith

/-- The shifted bound `|ζ(s+2)| ≤ 3c/|m|`. -/
theorem Up.norm_zeta_two_le_m (h : Up ε c χ s) : ‖zeta c χ (s + 2)‖ ≤ 3 * c / ‖s + 3 / 2‖ := by
  have h' := Up.add_two h
  have hz := Up.norm_zeta_le_m h'
  have hmm : ‖s + 3 / 2‖ ≤ ‖s + 2 + 3 / 2‖ := by
    have := Up.norm_m_le_add h (a := 7 / 2) (by norm_num)
    rw [show s + 2 + 3 / 2 = s + (7 / 2 : ℝ) by push_cast; ring]; exact this
  have hm := Up.norm_m_ge h
  refine hz.trans ?_
  exact div_le_div_of_nonneg_left (by linarith [h.c_pos]) (by linarith [h.c_pos]) hmm

/-- **The `κ`-step**: `|ω(s+2)/(s+4) − ω(s)/(s+2)| ≤ 3/(2|m|²)`. -/
theorem Up.norm_kappa_step_le (h : Up ε c χ s) :
    ‖omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)‖ ≤ 3 / (2 * ‖s + 3 / 2‖ ^ 2) := by
  have h' := Up.add_two h
  have hm := Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith [h.c_pos]
  have hs2 := Up.norm_m_le_add h (a := 2) (by norm_num)
  have hs4 := Up.norm_m_le_add h (a := 4) (by norm_num)
  push_cast at hs2 hs4
  have hs2ne : s + 2 ≠ 0 := by intro h0; rw [h0, norm_zero] at hs2; linarith
  have hs4ne : s + 4 ≠ 0 := by intro h0; rw [h0, norm_zero] at hs4; linarith
  set δ := omega s - (s + 3 / 2)
  set δ' := omega (s + 2) - (s + 2 + 3 / 2)
  have hδ : ‖δ‖ ≤ 1 / (4 * ‖s + 3 / 2‖) := norm_omega_sub_le h.m_ne
  have hm' : ‖s + 3 / 2‖ ≤ ‖s + 2 + 3 / 2‖ := by
    have := Up.norm_m_le_add h (a := 7 / 2) (by norm_num)
    rw [show s + 2 + 3 / 2 = s + (7 / 2 : ℝ) by push_cast; ring]; exact this
  have hδ' : ‖δ'‖ ≤ 1 / (4 * ‖s + 3 / 2‖) :=
    (norm_omega_sub_le h'.m_ne).trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  have e : omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)
      = 1 / ((s + 2) * (s + 4)) + δ' / (s + 4) - δ / (s + 2) := by
    rw [show s + 2 + 2 = s + 4 by ring]
    simp only [δ, δ']
    field_simp
    ring
  rw [e]
  have t1 : ‖1 / ((s + 2) * (s + 4))‖ ≤ 1 / ‖s + 3 / 2‖ ^ 2 := by
    rw [norm_div, norm_one, norm_mul, sq]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul hs2 hs4 hmpos.le (by linarith))
  have t2 : ‖δ' / (s + 4)‖ ≤ 1 / (4 * ‖s + 3 / 2‖ ^ 2) := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    calc ‖δ'‖ ≤ 1 / (4 * ‖s + 3 / 2‖) := hδ'
      _ = 1 / (4 * ‖s + 3 / 2‖ ^ 2) * ‖s + 3 / 2‖ := by field_simp
      _ ≤ 1 / (4 * ‖s + 3 / 2‖ ^ 2) * ‖s + 4‖ := by gcongr
  have t3 : ‖δ / (s + 2)‖ ≤ 1 / (4 * ‖s + 3 / 2‖ ^ 2) := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    calc ‖δ‖ ≤ 1 / (4 * ‖s + 3 / 2‖) := hδ
      _ = 1 / (4 * ‖s + 3 / 2‖ ^ 2) * ‖s + 3 / 2‖ := by field_simp
      _ ≤ 1 / (4 * ‖s + 3 / 2‖ ^ 2) * ‖s + 2‖ := by gcongr
  calc ‖1 / ((s + 2) * (s + 4)) + δ' / (s + 4) - δ / (s + 2)‖
      ≤ ‖1 / ((s + 2) * (s + 4))‖ + ‖δ' / (s + 4)‖ + ‖δ / (s + 2)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 / ‖s + 3 / 2‖ ^ 2 + 1 / (4 * ‖s + 3 / 2‖ ^ 2) + 1 / (4 * ‖s + 3 / 2‖ ^ 2) := by linarith
    _ = 3 / (2 * ‖s + 3 / 2‖ ^ 2) := by field_simp; ring

/-- **The `ζ`-step**: `|ζ(s+2) − ζ(s)| ≤ 108c/(√ε|m|²)`. -/
theorem Up.norm_zeta_step_le_m (h : Up ε c χ s) :
    ‖zeta c χ (s + 2) - zeta c χ s‖ ≤ 108 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
  have hc := h.c_pos
  have hε := h.hε
  have hm := Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hstep := Up.norm_zeta_step_le h
  have htau := Up.norm_tau_step_le h
  have hz := Up.norm_zeta_le_m h
  have hz' := Up.norm_zeta_two_le_m h
  have hw := Up.norm_w_ge h
  have ht := Up.norm_tau_ge h
  have hwlow : Real.sqrt ε * ‖s + 3 / 2‖ / (9 * c) ≤ ‖csqrt (tau c χ s ^ 2 + 1)‖ := by
    refine le_trans ?_ hw
    have : Real.sqrt ε * (‖s + 3 / 2‖ / (3 * c)) / 3 ≤ Real.sqrt ε * ‖tau c χ s‖ / 3 := by gcongr
    calc Real.sqrt ε * ‖s + 3 / 2‖ / (9 * c) = Real.sqrt ε * (‖s + 3 / 2‖ / (3 * c)) / 3 := by
          field_simp; ring
      _ ≤ _ := this
  have hwpos : 0 < Real.sqrt ε * ‖s + 3 / 2‖ / (9 * c) := by positivity
  refine hstep.trans ?_
  calc ‖tau c χ (s + 2) - tau c χ s‖ * (‖zeta c χ s‖ + ‖zeta c χ (s + 2)‖) / ‖csqrt (tau c χ s ^ 2 + 1)‖
      ≤ 2 / c * (3 * c / ‖s + 3 / 2‖ + 3 * c / ‖s + 3 / 2‖)
          / (Real.sqrt ε * ‖s + 3 / 2‖ / (9 * c)) := by
        apply div_le_div₀ (by positivity) _ hwpos hwlow
        exact mul_le_mul htau (by linarith) (by positivity) (by positivity)
    _ = 108 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by field_simp; ring

/-- **The `ρ*`-step**: `|ρ*(s+2) − ρ*(s)| ≤ 110c/(√ε|m|²)`. -/
theorem Up.norm_rho_step_le (h : Up ε c χ s) :
    ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ≤ 110 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
  have hc := h.c_pos
  have hε := h.hε
  have hm := Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hse1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hk := Up.norm_kappa_step_le h
  have hκ := Up.norm_kappa_le h
  have hz' := Up.norm_zeta_two_le_m h
  have hzs := Up.norm_zeta_step_le_m h
  have e : rhoStar c χ (s + 2) - rhoStar c χ s
      = (omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)) * zeta c χ (s + 2)
        + omega s / (s + 2) * (zeta c χ (s + 2) - zeta c χ s) := by
    unfold rhoStar; rw [show s + 2 + 2 = s + 4 by ring]; ring
  rw [e]
  have b1 : ‖(omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)) * zeta c χ (s + 2)‖
      ≤ 3 / (2 * ‖s + 3 / 2‖ ^ 2) * (3 * c / ‖s + 3 / 2‖) := by
    rw [norm_mul]; exact mul_le_mul hk hz' (norm_nonneg _) (by positivity)
  have b2 : ‖omega s / (s + 2) * (zeta c χ (s + 2) - zeta c χ s)‖
      ≤ 108 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
    rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hκ).trans hzs
  have b3 : 3 / (2 * ‖s + 3 / 2‖ ^ 2) * (3 * c / ‖s + 3 / 2‖) ≤ 2 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
    rw [show 3 / (2 * ‖s + 3 / 2‖ ^ 2) * (3 * c / ‖s + 3 / 2‖) = 9 * c / (2 * ‖s + 3 / 2‖ ^ 2 * ‖s + 3 / 2‖) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h9 : 9 * Real.sqrt ε ≤ 4 * ‖s + 3 / 2‖ := by nlinarith [h.c_ge]
    have h9' := mul_le_mul_of_nonneg_left h9 (show 0 ≤ c * ‖s + 3 / 2‖ ^ 2 by positivity)
    nlinarith [h9']
  calc ‖(omega (s + 2) / (s + 2 + 2) - omega s / (s + 2)) * zeta c χ (s + 2)
        + omega s / (s + 2) * (zeta c χ (s + 2) - zeta c χ s)‖
      ≤ _ := norm_add_le _ _
    _ ≤ 2 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) + 108 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by linarith
    _ = 110 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by ring

/-- `|(s + a + 1)/(s + a)| ≤ 2` for real `a`. -/
theorem Up.norm_ratio_le (h : Up ε c χ s) (a : ℝ) : ‖(s + a + 1) / (s + a)‖ ≤ 2 := by
  have h2 := Up.norm_add_ge h a
  have hpos : 0 < ‖s + a‖ := by linarith [h.c_pos]
  rw [norm_div, div_le_iff₀ hpos]
  have h1 := norm_add_le (s + a) 1
  rw [norm_one] at h1
  nlinarith [h.c_ge]

/-- **The forcing**: `|B| ≤ 660c²/(√ε|m|³)`. -/
theorem Up.norm_Bf_le (h : Up ε c χ s) : ‖Bf c χ s‖ ≤ 660 * c ^ 2 / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 3) := by
  have hc := h.c_pos
  have hm := Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have hr : ‖(s + 2) / (s + 1)‖ ≤ 2 := by
    have := Up.norm_ratio_le h 1; push_cast at this; rwa [show s + 1 + 1 = s + 2 by ring] at this
  have hρ : ‖rhoStar c χ s‖ ≤ 3 * c / ‖s + 3 / 2‖ := (Up.norm_rho_le h).trans (Up.norm_zeta_le_m h)
  have hd := Up.norm_rho_step_le h
  have e : Bf c χ s = (s + 2) / (s + 1) * rhoStar c χ s * (rhoStar c χ (s + 2) - rhoStar c χ s) := by
    unfold Bf; ring
  rw [e, norm_mul, norm_mul]
  calc ‖(s + 2) / (s + 1)‖ * ‖rhoStar c χ s‖ * ‖rhoStar c χ (s + 2) - rhoStar c χ s‖
      ≤ 2 * (3 * c / ‖s + 3 / 2‖) * (110 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2)) := by
        gcongr
    _ = 660 * c ^ 2 / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 3) := by field_simp; ring

/-- **Contraction**: `|A| ≤ 1 − √ε/4`. -/
theorem Up.norm_Af_le (h : Up ε c χ s) : ‖Af c χ s‖ ≤ 1 - Real.sqrt ε / 4 := by
  have h' := Up.add_two h
  have hc := h.c_pos
  have hε := h.hε
  have hε1 := h.hε1
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hrr : r ^ 2 = ε := Real.sq_sqrt hε.le
  -- `|ζ|², |ζ'|² ≤ q₀ = 1/(1 + 2√(ε/2))`
  have hq := h.normSq_zeta_le
  have hq' := h'.normSq_zeta_le
  rw [Complex.normSq_eq_norm_sq] at hq hq'
  have hs2 : 7 / 10 * r ≤ Real.sqrt (ε / 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
  set q₀ := 1 / (1 + 2 * Real.sqrt (ε / 2))
  have hq₀ : q₀ ≤ 1 / (1 + 7 / 5 * r) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hzz : ‖zeta c χ s‖ * ‖zeta c χ (s + 2)‖ ≤ 1 / (1 + 7 / 5 * r) := by
    nlinarith [sq_nonneg (‖zeta c χ s‖ - ‖zeta c χ (s + 2)‖)]
  -- the ratio `|(s+2)/(s+1)| ≤ 1 + 1/(2c)`
  have hs1 : 2 * c ≤ ‖s + 1‖ := by have := Up.norm_add_ge h 1; push_cast at this; exact this
  have hrat : ‖(s + 2) / (s + 1)‖ ≤ 1 + 1 / (2 * c) := by
    have hpos : 0 < ‖s + 1‖ := by linarith
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
  have e : Af c χ s = (s + 2) / (s + 1) * (omega s / (s + 2) * zeta c χ s)
      * (omega (s + 2) / (s + 2 + 2) * zeta c χ (s + 2)) := by
    unfold Af rhoStar; ring
  rw [e, norm_mul, norm_mul, norm_mul, norm_mul]
  have hk := Up.norm_kappa_le h
  have hk' := Up.norm_kappa_le h'
  have hz0 := norm_nonneg (zeta c χ s)
  have hz1 := norm_nonneg (zeta c χ (s + 2))
  calc ‖(s + 2) / (s + 1)‖ * (‖omega s / (s + 2)‖ * ‖zeta c χ s‖)
        * (‖omega (s + 2) / (s + 2 + 2)‖ * ‖zeta c χ (s + 2)‖)
      ≤ (1 + r / 128) * (1 * ‖zeta c χ s‖) * (1 * ‖zeta c χ (s + 2)‖) := by
        gcongr; linarith
    _ = (1 + r / 128) * (‖zeta c χ s‖ * ‖zeta c χ (s + 2)‖) := by ring
    _ ≤ (1 + r / 128) * (1 / (1 + 7 / 5 * r)) := by gcongr
    _ ≤ 1 - r / 4 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith

theorem Up.norm_one_add_Af_ge (h : Up ε c χ s) : Real.sqrt ε / 4 ≤ ‖1 + Af c χ s‖ := by
  have hA := Up.norm_Af_le h
  have := norm_sub_norm_le (1 : ℂ) (-Af c χ s)
  rw [norm_neg, norm_one, sub_neg_eq_add] at this
  linarith

/-- `|(1 + A)⁻¹| ≤ 4/√ε`. -/
theorem Up.norm_inv_one_add_Af_le (h : Up ε c χ s) : ‖(1 + Af c χ s)⁻¹‖ ≤ 4 / Real.sqrt ε := by
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have hg := Up.norm_one_add_Af_ge h
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ (by linarith) hse]
  linarith

/-- **The `A`-step**: `|A(s+2) − A(s)| ≤ 1340c²/(√ε|m|³)`. -/
theorem Up.norm_Af_step_le (h : Up ε c χ s) :
    ‖Af c χ (s + 2) - Af c χ s‖ ≤ 1340 * c ^ 2 / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 3) := by
  have h' := Up.add_two h
  have hc := h.c_pos
  have hm := Up.norm_m_ge h
  have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
  have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr h.hε
  have hse1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hs1 : s + 1 ≠ 0 := by have := Up.add_ne h 1; push_cast at this; exact this
  have hs3 : s + 3 ≠ 0 := by have := Up.add_ne h 3; push_cast at this; exact this
  rw [Cvs.Prolate.Mellin.FrozenRootFirstDifference.Af_step_eq hs1 hs3]
  have hmm : ‖s + 3 / 2‖ ≤ ‖s + 2 + 3 / 2‖ := by
    have := Up.norm_m_le_add h (a := 7 / 2) (by norm_num)
    rw [show s + 2 + 3 / 2 = s + (7 / 2 : ℝ) by push_cast; ring]; exact this
  have hρ' : ‖rhoStar c χ (s + 2)‖ ≤ 3 * c / ‖s + 3 / 2‖ :=
    (Up.norm_rho_le h').trans (Up.norm_zeta_two_le_m h)
  have hρ : ‖rhoStar c χ s‖ ≤ 3 * c / ‖s + 3 / 2‖ := (Up.norm_rho_le h).trans (Up.norm_zeta_le_m h)
  have hd1 := Up.norm_rho_step_le h
  have hd2 : ‖rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)‖ ≤ 110 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
    refine (Up.norm_rho_step_le h').trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hdd : ‖rhoStar c χ (s + 2 + 2) - rhoStar c χ s‖ ≤ 220 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
    have := norm_add_le (rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2)) (rhoStar c χ (s + 2) - rhoStar c χ s)
    rw [show rhoStar c χ (s + 2 + 2) - rhoStar c χ (s + 2) + (rhoStar c χ (s + 2) - rhoStar c χ s)
      = rhoStar c χ (s + 2 + 2) - rhoStar c χ s by ring] at this
    have e2 : 220 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2)
        = 110 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) + 110 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by ring
    linarith
  have hr43 : ‖(s + 4) / (s + 3)‖ ≤ 2 := by
    have := Up.norm_ratio_le h 3; push_cast at this; rwa [show s + 3 + 1 = s + 4 by ring] at this
  have hs1n : 2 * c ≤ ‖s + 1‖ := by have := Up.norm_add_ge h 1; push_cast at this; exact this
  have hs3n : ‖s + 3 / 2‖ ≤ ‖s + 3‖ := by
    have := Up.norm_m_le_add h (a := 3) (by norm_num); push_cast at this; exact this
  have hlast : ‖2 * rhoStar c χ s / ((s + 1) * (s + 3))‖ ≤ 3 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
    have hden : 2 * c * ‖s + 3 / 2‖ ≤ ‖s + 1‖ * ‖s + 3‖ := mul_le_mul hs1n hs3n (by positivity) (by positivity)
    calc 2 * ‖rhoStar c χ s‖ / (‖s + 1‖ * ‖s + 3‖)
        ≤ 2 * (3 * c / ‖s + 3 / 2‖) / (2 * c * ‖s + 3 / 2‖) := by gcongr
      _ = 3 / ‖s + 3 / 2‖ ^ 2 := by field_simp
      _ ≤ 3 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h.c_ge, sq_nonneg ‖s + 3 / 2‖]
  rw [norm_mul]
  calc ‖rhoStar c χ (s + 2)‖
        * ‖(s + 4) / (s + 3) * (rhoStar c χ (s + 2 + 2) - rhoStar c χ s) - 2 * rhoStar c χ s / ((s + 1) * (s + 3))‖
      ≤ 3 * c / ‖s + 3 / 2‖ * (2 * (220 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2))
          + 3 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2)) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
        gcongr
    _ ≤ 1340 * c ^ 2 / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 3) := by
        rw [show 3 * c / ‖s + 3 / 2‖ * (2 * (220 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2))
          + 3 * c / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 2)) = 1329 * c ^ 2 / (Real.sqrt ε * ‖s + 3 / 2‖ ^ 3) by
          field_simp; ring]
        gcongr; norm_num

end Cvs.Prolate.Mellin.PastTurningStepForcing
