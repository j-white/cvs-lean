import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.ForcingUnifiedSizes
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootLogErrorSum
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.FrozenRootStep
import Cvs.Prolate.Mellin.NearRegionBetaStep
import Cvs.Prolate.Mellin.PropagationFactorSizes
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frozen forcing summed along a line

For `c ≥ 10⁵/ε²`, along `s_k = s₀ + 2k`:
`|Σ_{k<K} Re β(s_k) − ½(log‖p(s_K)‖ − log‖p(s₀)‖) + ½(log‖1 + r(s_K)‖ − log‖1 + r(s₀)‖)| ≤ E₂(ε, c)` with
`E₂ = ((10848/ε)² + 1.5·10¹⁰/ε³)/c + (468/√ε)(1 + log(1 + c/2))/(2c)`.
-/

noncomputable section

open Finset

namespace Cvs.Prolate.Mellin.FrozenForcingLineSum

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.ForcingSmallBound Cvs.Prolate.Mellin.NearRegionBetaStep Cvs.Prolate.Mellin.FrozenForcingIdentities Cvs.Prolate.Mellin.ForcingUnifiedSizes

/-- The forcing budget `E₂`. -/
def E2 (ε c : ℝ) : ℝ :=
  ((10848 / ε) ^ 2 + 15000000000 / ε ^ 3) / c + 468 / Real.sqrt ε * ((1 + Real.log (1 + c / 2)) / (2 * c))

variable {ε c χ : ℝ} {s : ℂ}

theorem Hyp.c_big (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) (hc5 : 100000 / ε ^ 2 ≤ c) : 100000 / ε ≤ c := by
  have hε := h.hε
  have : 100000 / ε ≤ 100000 / ε ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity); nlinarith
  linarith

/-- **The step terms.** -/
theorem Hyp.step_terms (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) (hc5 : 100000 / ε ^ 2 ≤ c) :
    pp c χ s ≠ 0 ∧ qq c χ s ≠ 0 ∧ ‖betaf c χ s‖ ≤ 1 / 2
      ∧ ‖rr s * (rhoStar c χ (s + 2) - rhoStar c χ s) ^ 2 / (pp c χ s * qq c χ s)‖ ≤ 1 / 2
      ∧ ‖betaf c χ s‖ ^ 2 + 3 / 4 * ‖rr s * (rhoStar c χ (s + 2) - rhoStar c χ s) ^ 2 / (pp c χ s * qq c χ s)‖
        ≤ ((10848 / ε) ^ 2 + 15000000000 / ε ^ 3) / (s.re + 2 * c) ^ 2 := by
  have hε := h.hε
  have hc := h.c_pos
  have hcb := Hyp.c_big h hε4 hc5
  have hx := h.hre
  set y := s.re + 2 * c
  have hy : 2 * c ≤ y := by simp only [y]; linarith
  have hy0 : 0 < y := by linarith
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hse : ε ≤ Real.sqrt ε := by
    have := Real.sqrt_le_sqrt (show ε ^ 2 ≤ ε by nlinarith); rwa [Real.sqrt_sq hε.le] at this
  -- β
  have hβ' := Hyp.norm_betaf_le' h hε4
  have hβ : ‖betaf c χ s‖ ≤ 1 / 2 := by
    refine hβ'.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have : 10848 ≤ ε * c / 2 := by
      have := (div_le_iff₀ hε).mp hcb; nlinarith
    nlinarith
  -- p
  have hp := Hyp.norm_pp_ge h hε4 hβ
  have hp0 : pp c χ s ≠ 0 := fun h0 => by rw [h0, norm_zero] at hp; linarith
  have hpu : ‖pp c χ s‖ ≤ 10 := by
    unfold pp
    have := norm_add_le (1 : ℂ) (rr s * rhoStar c χ s ^ 2)
    rw [norm_one, norm_mul, norm_pow] at this
    have h1 := Hyp.norm_rr_le h
    have h2 := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h
    have : ‖rhoStar c χ s‖ ^ 2 ≤ (9 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [norm_nonneg (rr s)]
  -- e
  set e := rr s * (rhoStar c χ (s + 2) - rhoStar c χ s) ^ 2
  have hd := Hyp.norm_drho_le h hε4
  have he : ‖e‖ ≤ 800000 / (3 * ε * y ^ 2) := by
    simp only [e]; rw [norm_mul, norm_pow]
    have h1 := Hyp.norm_rr_le h
    have h2 : ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ^ 2 ≤ (400 / (Real.sqrt ε * y)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hd 2
    have h3 : (400 / (Real.sqrt ε * y)) ^ 2 = 160000 / (ε * y ^ 2) := by
      rw [div_pow, mul_pow, hsq]; norm_num
    calc ‖rr s‖ * ‖rhoStar c χ (s + 2) - rhoStar c χ s‖ ^ 2 ≤ 5 / 3 * (160000 / (ε * y ^ 2)) := by
          rw [← h3]; gcongr
      _ = 800000 / (3 * ε * y ^ 2) := by field_simp; ring
  have hy2 : 4 * c ^ 2 ≤ y ^ 2 := by nlinarith
  have hc2 : 10000000000 / ε ^ 4 ≤ c ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hc5 2
    calc 10000000000 / ε ^ 4 = (100000 / ε ^ 2) ^ 2 := by field_simp; ring
      _ ≤ c ^ 2 := this
  have he2 : ‖e‖ ≤ ε / 288 := by
    refine he.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 40000000000 ≤ ε ^ 4 * y ^ 2 := by
      have := (div_le_iff₀ (by positivity)).mp hc2; nlinarith
    nlinarith [pow_pos hε 3]
  -- q
  have hA := Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_one_add_Af_ge' h hε4
  have hA2 : ε / 144 ≤ ‖(1 + Af c χ s) ^ 2‖ := by
    rw [norm_pow]
    have := pow_le_pow_left₀ (by positivity) hA 2
    rw [div_pow, hsq] at this; linarith
  have hid := one_add_Af_sq c χ s
  have hq : ε / 2880 ≤ ‖qq c χ s‖ := by
    have e1 : pp c χ s * qq c χ s = (1 + Af c χ s) ^ 2 + e := by rw [hid]; simp only [e]; ring
    have h1 : ‖(1 + Af c χ s) ^ 2‖ - ‖e‖ ≤ ‖pp c χ s‖ * ‖qq c χ s‖ := by
      rw [← norm_mul, e1]
      have := norm_sub_norm_le ((1 + Af c χ s) ^ 2) (-e)
      rw [norm_neg, sub_neg_eq_add] at this; linarith
    have : ε / 288 ≤ ‖pp c χ s‖ * ‖qq c χ s‖ := by linarith
    by_contra hcon; push_neg at hcon
    have : ‖pp c χ s‖ * ‖qq c χ s‖ < 10 * (ε / 2880) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hpu (norm_nonneg _)) (by linarith)
    linarith
  have hq0 : qq c χ s ≠ 0 := fun h0 => by rw [h0, norm_zero] at hq; linarith
  -- e/(pq)
  have hw : ‖e / (pp c χ s * qq c χ s)‖ ≤ 18432000000 / (ε ^ 3 * y ^ 2) := by
    rw [norm_div, norm_mul (pp c χ s)]
    have hpq : Real.sqrt ε / 24 * (ε / 2880) ≤ ‖pp c χ s‖ * ‖qq c χ s‖ :=
      mul_le_mul hp hq (by positivity) (norm_nonneg _)
    have hpq' : ε ^ 2 / 69120 ≤ ‖pp c χ s‖ * ‖qq c χ s‖ := by
      refine le_trans ?_ hpq
      rw [div_mul_div_comm, div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
    rw [div_le_div_iff₀ (mul_pos (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hq0)) (by positivity)]
    calc ‖e‖ * (ε ^ 3 * y ^ 2) ≤ 800000 / (3 * ε * y ^ 2) * (ε ^ 3 * y ^ 2) := by gcongr
      _ = 800000 / 3 * ε ^ 2 := by field_simp
      _ ≤ 18432000000 * (ε ^ 2 / 69120) := by nlinarith [sq_nonneg ε]
      _ ≤ 18432000000 * (‖pp c χ s‖ * ‖qq c χ s‖) := by gcongr
  have hw2 : ‖e / (pp c χ s * qq c χ s)‖ ≤ 1 / 2 := by
    refine hw.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 40000000000 ≤ ε ^ 4 * y ^ 2 := by
      have := (div_le_iff₀ (by positivity)).mp hc2; nlinarith
    nlinarith [pow_pos hε 3]
  refine ⟨hp0, hq0, hβ, hw2, ?_⟩
  have hβ2 : ‖betaf c χ s‖ ^ 2 ≤ (10848 / ε) ^ 2 / y ^ 2 := by
    calc ‖betaf c χ s‖ ^ 2 ≤ (10848 / (ε * y)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hβ' 2
      _ = (10848 / ε) ^ 2 / y ^ 2 := by field_simp
  calc ‖betaf c χ s‖ ^ 2 + 3 / 4 * ‖e / (pp c χ s * qq c χ s)‖
      ≤ (10848 / ε) ^ 2 / y ^ 2 + 3 / 4 * (18432000000 / (ε ^ 3 * y ^ 2)) := by gcongr
    _ ≤ (10848 / ε) ^ 2 / y ^ 2 + 15000000000 / ε ^ 3 / y ^ 2 := by
        have : 3 / 4 * (18432000000 / (ε ^ 3 * y ^ 2)) ≤ 15000000000 / ε ^ 3 / y ^ 2 := by
          rw [div_div, show 3 / 4 * (18432000000 / (ε ^ 3 * y ^ 2)) = 13824000000 / (ε ^ 3 * y ^ 2) by ring]
          exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
        linarith
    _ = _ := by ring

/-- **The shift term.** -/
theorem Hyp.shift_term (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) (hc5 : 100000 / ε ^ 2 ≤ c) :
    ‖(rr s - rr (s + 2)) * (rhoStar c χ (s + 2) ^ 2 - 1) / (pp c χ (s + 2) * (1 + rr s))‖ ≤ 1 / 2
      ∧ 3 / 2 * ‖(rr s - rr (s + 2)) * (rhoStar c χ (s + 2) ^ 2 - 1) / (pp c χ (s + 2) * (1 + rr s))‖
        ≤ 936 / Real.sqrt ε / ((s.re + 2) * (s.re + 2 + c)) := by
  have hε := h.hε
  have hc := h.c_pos
  have hcb := Hyp.c_big h hε4 hc5
  have hx := h.hre
  have h' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two h
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hse : ε ≤ Real.sqrt ε := by
    have := Real.sqrt_le_sqrt (show ε ^ 2 ≤ ε by nlinarith); rwa [Real.sqrt_sq hε.le] at this
  have hs1 := Hyp.s1_ne h
  have hs3 : s + 3 ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this; linarith
  have n1 : s.re + 1 ≤ ‖s + 1‖ := by have := Complex.re_le_norm (s + 1); simpa using this
  have n3 : s.re + 3 ≤ ‖s + 3‖ := by have := Complex.re_le_norm (s + 3); simpa using this
  -- `‖D‖ ≤ 52/((x+2)(x+2+c))`
  have hρ1 := Hyp.norm_rho_sq_sub_one_le h
  have hρ2 : ‖rhoStar c χ (s + 2) ^ 2 - 1‖ ≤ 97 / 16 := by
    have := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h'
    have h2 := norm_sub_le (rhoStar c χ (s + 2) ^ 2) 1
    rw [norm_pow, norm_one] at h2
    have : ‖rhoStar c χ (s + 2)‖ ^ 2 ≤ (9 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    linarith
  have hr : ‖rr s - rr (s + 2)‖ = 2 / (‖s + 1‖ * ‖s + 3‖) := by
    rw [rr_sub hs1 hs3, norm_div, norm_mul]; norm_num
  have hD : ‖(rr s - rr (s + 2)) * (rhoStar c χ (s + 2) ^ 2 - 1)‖ ≤ 52 / ((s.re + 2) * (s.re + 2 + c)) := by
    rw [norm_mul, hr]
    have hp13 : 0 < ‖s + 1‖ * ‖s + 3‖ := by nlinarith
    by_cases hxc : s.re + 2 ≤ c
    · calc 2 / (‖s + 1‖ * ‖s + 3‖) * ‖rhoStar c χ (s + 2) ^ 2 - 1‖
          ≤ 2 / (‖s + 1‖ * ‖s + 3‖) * (13 * (‖s + 3‖ + 1) / (4 * c)) := by gcongr
        _ ≤ 26 / (c * (s.re + 2)) := by
            rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
            have k1 : s.re + 2 ≤ 2 * ‖s + 1‖ := by linarith
            have k2 : ‖s + 3‖ + 1 ≤ 2 * ‖s + 3‖ := by linarith
            have k3 : (‖s + 3‖ + 1) * (s.re + 2) ≤ 2 * ‖s + 3‖ * (2 * ‖s + 1‖) :=
              mul_le_mul k2 k1 (by linarith) (by positivity)
            nlinarith [mul_le_mul_of_nonneg_left k3 (show 0 ≤ 26 * c by positivity)]
        _ ≤ 52 / ((s.re + 2) * (s.re + 2 + c)) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    · push_neg at hxc
      calc 2 / (‖s + 1‖ * ‖s + 3‖) * ‖rhoStar c χ (s + 2) ^ 2 - 1‖ ≤ 2 / (‖s + 1‖ * ‖s + 3‖) * (97 / 16) := by
            gcongr
        _ ≤ 2 / ((s.re + 1) * (s.re + 3)) * (97 / 16) := by
            gcongr
        _ ≤ 52 / ((s.re + 2) * (s.re + 2 + c)) := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [mul_pos (show 0 < s.re + 2 by linarith) (show 0 < s.re + 2 by linarith)]
  -- the denominator
  have hβ' := (Hyp.step_terms h' hε4 hc5).2.2.1
  have hp := Hyp.norm_pp_ge h' hε4 hβ'
  have hr2 := Hyp.norm_one_add_rr_ge h
  have hden : Real.sqrt ε / 12 ≤ ‖pp c χ (s + 2) * (1 + rr s)‖ := by
    rw [norm_mul]; nlinarith
  have hval : ‖(rr s - rr (s + 2)) * (rhoStar c χ (s + 2) ^ 2 - 1) / (pp c χ (s + 2) * (1 + rr s))‖
      ≤ 624 / Real.sqrt ε / ((s.re + 2) * (s.re + 2 + c)) := by
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
    calc _ ≤ 52 / ((s.re + 2) * (s.re + 2 + c)) := hD
      _ = 624 / Real.sqrt ε / ((s.re + 2) * (s.re + 2 + c)) * (Real.sqrt ε / 12) := by field_simp; ring
      _ ≤ _ := by gcongr
  refine ⟨hval.trans ?_, ?_⟩
  · rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 2 * c ≤ (s.re + 2) * (s.re + 2 + c) := by nlinarith
    have : 1248 ≤ Real.sqrt ε * c := by
      have := (div_le_iff₀ hε).mp hcb; nlinarith
    nlinarith
  · calc 3 / 2 * _ ≤ 3 / 2 * (624 / Real.sqrt ε / ((s.re + 2) * (s.re + 2 + c))) := by gcongr
      _ = _ := by ring

/-- **The forcing summed along a line.** -/
theorem Hyp.sum_re_betaf (h : Hyp ε c χ s) (hε4 : ε ≤ 1 / 4) (hc5 : 100000 / ε ^ 2 ≤ c) (K : ℕ) :
    |∑ k ∈ range K, (betaf c χ (s + 2 * k)).re
        - 1 / 2 * (Real.log ‖pp c χ (s + 2 * K)‖ - Real.log ‖pp c χ (s + 2 * (0 : ℕ))‖)
        + 1 / 2 * (Real.log ‖1 + rr (s + 2 * K)‖ - Real.log ‖1 + rr (s + 2 * (0 : ℕ))‖)| ≤ E2 ε c := by
  have hε := h.hε
  have hc := h.c_pos
  have hx := h.hre
  have hsk : ∀ k : ℕ, s + 2 * ((k + 1 : ℕ) : ℂ) = s + 2 * (k : ℂ) + 2 := fun k => by push_cast; ring
  have main := sum_re_le (β := fun k => betaf c χ (s + 2 * k)) (p := fun k => pp c χ (s + 2 * k))
    (q := fun k => qq c χ (s + 2 * k)) (r := fun k => rr (s + 2 * k))
    (e1 := fun k => ((10848 / ε) ^ 2 + 15000000000 / ε ^ 3) / (s.re + 2 * k + 2 * c) ^ 2)
    (e2 := fun k => 936 / Real.sqrt ε / ((s.re + 2 * k + 2) * (s.re + 2 * k + 2 + c))) K
    (fun k _ => by
      have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line h k
      obtain ⟨hp0, hq0, hβ, hw, hb⟩ := Hyp.step_terms hl hε4 hc5
      have hA := Cvs.Prolate.Mellin.PropagationFactorSizes.Hyp.norm_one_add_Af_ge' hl hε4
      have hAne : 1 + Af c χ (s + 2 * (k : ℂ)) ≠ 0 := fun h0 => by
        rw [h0, norm_zero] at hA; have := Real.sqrt_pos.mpr hε; linarith
      have hst := step_re (one_sub_betaf_mul hAne) (one_add_Af_sq c χ _) hAne hp0 hq0 hβ hw
      refine hst.trans (hb.trans (le_of_eq ?_))
      simp)
    (fun k _ => by
      have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line h k
      have hl' := Cvs.Prolate.Mellin.FrozenRootStep.Hyp.add_two hl
      obtain ⟨_, hq0, _, _, _⟩ := Hyp.step_terms hl hε4 hc5
      obtain ⟨hp0', _, _, _, _⟩ := Hyp.step_terms hl' hε4 hc5
      obtain ⟨hD1, hD2⟩ := Hyp.shift_term hl hε4 hc5
      have hr := Hyp.norm_one_add_rr_ge hl
      have hr' := Hyp.norm_one_add_rr_ge hl'
      have hrne : 1 + rr (s + 2 * (k : ℂ)) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hr; linarith
      have hrne' : 1 + rr (s + 2 * (k : ℂ) + 2) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hr'; linarith
      have hsh := step_shift (shift_identity c χ _) hq0 hp0' hrne hrne' hD1
      simp only [hsk]
      refine hsh.trans (hD2.trans (le_of_eq ?_))
      simp)
  refine main.trans ?_
  unfold E2
  have hsum1 : ∑ k ∈ range K, 1 / (s.re + 2 * c + 2 * k) ^ 2 ≤ 1 / c :=
    (Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum.sum_inv_sq_le (X := s.re + 2 * c) (by linarith [h.c_ge]) K).trans
      (one_div_le_one_div_of_le hc (by linarith [h.c_ge]))
  have hsum2 := Cvs.Prolate.Mellin.FrozenRootLogErrorSum.sum_inv_mul_le (c := c) (x₀ := s.re + 2) hc (by linarith) K
  have e1 : ∑ k ∈ range K, ((10848 / ε) ^ 2 + 15000000000 / ε ^ 3) / (s.re + 2 * k + 2 * c) ^ 2
      = ((10848 / ε) ^ 2 + 15000000000 / ε ^ 3) * ∑ k ∈ range K, 1 / (s.re + 2 * c + 2 * k) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring_nf
  have e2 : ∑ k ∈ range K, 1 / 2 * (936 / Real.sqrt ε / ((s.re + 2 * k + 2) * (s.re + 2 * k + 2 + c)))
      = 468 / Real.sqrt ε * ∑ k ∈ range K, 1 / ((s.re + 2 + 2 * k) * (s.re + 2 + 2 * k + c)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring_nf
  rw [Finset.sum_add_distrib, e1, e2]
  have h0 : 0 ≤ (10848 / ε) ^ 2 + 15000000000 / ε ^ 3 := by positivity
  calc _ ≤ ((10848 / ε) ^ 2 + 15000000000 / ε ^ 3) * (1 / c)
        + 468 / Real.sqrt ε * ((1 + Real.log (1 + c / 2)) / (2 * c)) :=
        add_le_add (mul_le_mul_of_nonneg_left hsum1 h0) (mul_le_mul_of_nonneg_left hsum2 (by positivity))
    _ = _ := by ring

end Cvs.Prolate.Mellin.FrozenForcingLineSum
