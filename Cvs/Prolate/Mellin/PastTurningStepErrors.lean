import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.PastTurningContraction
import Cvs.Prolate.Mellin.PastTurningRootSizes
import Cvs.Prolate.Mellin.PastTurningStepForcing
import Cvs.Prolate.Mellin.RungThreeTermRecurrence
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.TrueRatioMatchesFrozen

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The step errors past the turning point

On a line `s_k = s₀ + 2k` starting in the region of Cvs.Prolate.Mellin.PastTurningContraction, `y_k = ρ*(s_k)(s_k + 2)/c → 1` and `v_k → 0`. For
`c ≥ 6000/ε²` the ground law ratio has `P_k ≠ 0` and `|v_k| ≤ 660/(εc)` at every `k`, by contraction from infinity,
and then `|v_k| ≤ 5280c²/(ε|s_k + 3/2|³)` by `FarRegionStepDecay`'s unrolled contraction.
-/

noncomputable section

open Complex Filter Topology

namespace Cvs.Prolate.Mellin.PastTurningStepErrors

open Cvs.Prolate.Mellin.RungThreeTermRecurrence (mel)
open Cvs.Prolate.Mellin.LawRatioRecurrence (mg lawRatio)
open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (rhoStar)
open Cvs.Prolate.Mellin.ForcingSmallBound (Af Bf)
open Cvs.Prolate.Mellin.TrueRatioDownwardStep (Pk vk sk_succ Pk_rec down_step eventually_Pk_ne)
open Cvs.Prolate.Mellin.PastTurningContraction (Up)
open Cvs.Prolate.Mellin.PastTurningRootSizes
open Cvs.Prolate.Mellin.PastTurningStepForcing

variable {ε c χ : ℝ} {s₀ : ℂ}

/-- The region is stable along the line. -/
theorem Up.line (h : Up ε c χ s₀) (k : ℕ) : Up ε c χ (s₀ + 2 * k) where
  hε := h.hε
  hε1 := h.hε1
  hc := h.hc
  hχ0 := h.hχ0
  hχ1 := h.hχ1
  hre := by simp; linarith [h.hre, (k.cast_nonneg : (0 : ℝ) ≤ k)]
  him := by simpa using h.him

theorem Up.rho_ne {s : ℂ} (h : Up ε c χ s) : rhoStar c χ s ≠ 0 := by
  unfold rhoStar
  exact div_ne_zero (mul_ne_zero h.omega_ne (Cvs.Prolate.Mellin.FrozenRootErrorIdentity.zeta_ne_zero c χ s))
    (by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne h 2)

/-- **`y_k → 1`** past the turning point. -/
theorem tendsto_y (h : Up ε c χ s₀) :
    Tendsto (fun k : ℕ => rhoStar c χ (s₀ + 2 * k) * (s₀ + 2 * k + 2) / c) atTop (𝓝 1) := by
  have hc := h.c_pos
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set x : ℕ → ℝ := fun k => s₀.re + 2 * k
  have hx : ∀ k : ℕ, (s₀ + 2 * (k : ℂ)).re = x k := fun k => by simp [x]
  have hbound : ∀ k : ℕ, ‖rhoStar c χ (s₀ + 2 * k) * (s₀ + 2 * k + 2) / c - 1‖
      ≤ (4 * χ + 16 * c ^ 2) / ((x k + 1) * (x k + 2)) := by
    intro k
    have hk' := Up.line h k
    set s := s₀ + 2 * (k : ℂ)
    have hxk : 1 / 2 ≤ x k := by rw [← hx]; exact hk'.hre
    have hroot := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.rhoStar_root (χ := χ) hc.ne' hk'.m_ne
      (by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne hk' 2) hk'.omega_ne
    have hid := Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.y_identity hc.ne' (by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne hk' 2) hroot
    set y := rhoStar c χ s * (s + 2) / c
    have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge hk'
    have hρ : ‖rhoStar c χ s‖ ≤ 3 * c / ‖s + 3 / 2‖ :=
      (Cvs.Prolate.Mellin.PastTurningRootSizes.Up.norm_rho_le hk').trans (Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_zeta_le_m hk')
    have hs2n : ‖s + 2‖ ≤ ‖s + 3 / 2‖ + 1 / 2 := by
      have := norm_add_le (s + 3 / 2) (1 / 2 : ℂ)
      rw [show s + 3 / 2 + 1 / 2 = s + 2 by ring] at this; simpa using this
    have hy : ‖y‖ ≤ 4 := by
      simp only [y]
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, div_le_iff₀ hc]
      have hmpos : 0 < ‖s + 3 / 2‖ := by linarith
      calc ‖rhoStar c χ s‖ * ‖s + 2‖ ≤ 3 * c / ‖s + 3 / 2‖ * (‖s + 3 / 2‖ + 1 / 2) :=
            mul_le_mul hρ hs2n (norm_nonneg _) (by positivity)
        _ ≤ 4 * c := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hmpos]
            nlinarith [mul_le_mul_of_nonneg_left (show (3 / 2 : ℝ) ≤ ‖s + 3 / 2‖ by linarith [hk'.c_ge]) hc.le]
    have hden : (x k + 1) * (x k + 2) ≤ ‖(s + 1) * (s + 2)‖ := by
      rw [norm_mul]
      have a1 := Complex.re_le_norm (s + 1); have a2 := Complex.re_le_norm (s + 2)
      have r1 : (s + 1).re = x k + 1 := by simp [s, x]
      have r2 : (s + 2).re = x k + 2 := by simp [s, x]
      rw [r1] at a1; rw [r2] at a2
      exact mul_le_mul a1 a2 (by linarith) (norm_nonneg _)
    have hden0 : 0 < (x k + 1) * (x k + 2) := by positivity
    have hne : (s + 1) * (s + 2) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hden; linarith
    have e : y - 1 = (y * χ - c ^ 2 * y ^ 2) / ((s + 1) * (s + 2)) := by
      rw [eq_div_iff hne]; exact hid
    rw [e, norm_div]
    have hχ0 : 0 ≤ χ := by linarith [hk'.hχ0, hk'.c_ge]
    have hnum : ‖y * χ - c ^ 2 * y ^ 2‖ ≤ 4 * χ + 16 * c ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      have k1 := mul_le_mul_of_nonneg_right hy hχ0
      have k2 : ‖y‖ ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
      have k3 := mul_le_mul_of_nonneg_left k2 (sq_nonneg c)
      nlinarith
    exact div_le_div₀ (by positivity) hnum hden0 hden
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  have hx2 : Tendsto (fun k : ℕ => (x k + 1) * (x k + 2)) atTop atTop := by
    have : Tendsto x atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    exact (tendsto_atTop_add_const_right _ 1 this).atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ 2 this)
  exact hx2.const_div_atTop _

/-- **`v_k → 0`** past the turning point. -/
theorem tendsto_vk (h : Up ε c χ s₀) : Tendsto (vk c χ s₀) atTop (𝓝 0) := by
  have hc := h.c_pos
  have h1 := Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c (s₀ := s₀) (by linarith [h.hre])
  have h2 : Tendsto (fun k : ℕ => (s₀ + 2 * k + 2) * mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2)) atTop
      (𝓝 (Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ)) := by
    have := (Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c (s₀ := s₀) (by linarith [h.hre])).comp
      (tendsto_add_atTop_nat 1)
    refine this.congr fun k => ?_
    simp only [Function.comp]; push_cast; ring_nf
  have hy := tendsto_y h
  have hne : (Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ) ≠ 0 := by
    exact_mod_cast Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
  have hlim : Tendsto (fun k : ℕ => rhoStar c χ (s₀ + 2 * k) * (s₀ + 2 * k + 2) / c
      * ((s₀ + 2 * k) * mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k))
      / ((s₀ + 2 * k + 2) * mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2)) - 1) atTop (𝓝 0) := by
    have := ((hy.mul h1).div h2 hne).sub_const 1
    simpa [hne] using this
  refine hlim.congr' ?_
  have hev : ∀ᶠ k : ℕ in atTop, mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k) ≠ 0 ∧
      mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2) ≠ 0 := by
    have e1 := h1.eventually_ne hne
    have e2 := h2.eventually_ne hne
    filter_upwards [e1, e2] with k k1 k2
    exact ⟨fun h0 => k1 (by rw [h0, mul_zero]), fun h0 => k2 (by rw [h0, mul_zero])⟩
  filter_upwards [hev] with k ⟨hM0, hM2⟩
  have hre : 0 < (s₀ + 2 * (k : ℂ)).re := by simp; linarith [h.hre, (k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hs0 : s₀ + 2 * (k : ℂ) ≠ 0 := fun h0 => by rw [h0] at hre; simp at hre
  have hs2 : s₀ + 2 * (k : ℂ) + 2 ≠ 0 := by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne (Up.line h k) 2
  have hg := Cvs.Prolate.Mellin.LawRatioRecurrence.mg_ne_zero hc hre
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hP : lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2) / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)
      = c / (s₀ + 2 * k) * (mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2) / mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)) :=
    Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.lawRatio_step hc hre hM0
  have hP0 : lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k) ≠ 0 := by
    unfold lawRatio; exact div_ne_zero hM0 hg
  have hP2 : lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hP
    exact (mul_ne_zero (div_ne_zero hc' hs0) (div_ne_zero hM2 hM0)) hP.symm
  unfold vk Pk
  rw [sk_succ]
  have e : rhoStar c χ (s₀ + 2 * k) * lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)
      / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2)
      = rhoStar c χ (s₀ + 2 * k) / (lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2)
          / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)) := by
    field_simp
  rw [e, hP]
  field_simp

/-- **One downward step on the line** past the turning point. -/
theorem line_step (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (k : ℕ)
    (hP1 : Pk c s₀ (k + 1) ≠ 0) (hP2 : Pk c s₀ (k + 2) ≠ 0) (hv : 1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1) ≠ 0) :
    rhoStar c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k) * Pk c s₀ k
      = Pk c s₀ (k + 1) * (1 + Af c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k)
          * (-vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1) / (1 + vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ (k + 1)))
          + Bf c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k)) := by
  have hk := Up.line h k
  have hk1 := Up.line h (k + 1)
  have hc := h.c_pos
  rw [sk_succ] at hk1
  have hrec := Pk_rec hc (by linarith [h.hre]) k
  have hroot := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.rhoStar_root (χ := Cvs.Prolate.EvenRungsByIndex.lev c 0) hc.ne' hk.m_ne
    (by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne hk 2) hk.omega_ne
  have hρ0 := Up.rho_ne hk
  have hρ1 := Up.rho_ne hk1
  have hv' : rhoStar c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (s₀ + 2 * k + 2) * Pk c s₀ (k + 1) / Pk c s₀ (k + 2) ≠ 0 := by
    intro h0; apply hv; unfold vk; rw [sk_succ, show k + 1 + 1 = k + 2 by ring, h0]; ring
  have := down_step (by simpa using Cvs.Prolate.Mellin.PastTurningRootSizes.Up.add_ne hk 1) hρ0 hρ1 hP1 hP2 hv' hrec hroot
  unfold vk Af Bf
  rw [sk_succ, show k + 1 + 1 = k + 2 by ring]
  exact this

/-- The uniform step-error level `V = 660/(εc)`. -/
def VU (ε c : ℝ) : ℝ := 660 / (ε * c)

/-- `|B| ≤ (√ε/8)·V` on the line. -/
theorem Up.norm_Bf_le_V {s : ℂ} (h : Up ε c χ s) : ‖Bf c χ s‖ ≤ Real.sqrt ε / 8 * VU ε c := by
  have hc := h.c_pos
  have hε := h.hε
  have hB := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_Bf_le h
  have hm := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_m_ge h
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hrr : r ^ 2 = ε := Real.sq_sqrt hε.le
  refine hB.trans ?_
  have h3 : (2 * c) ^ 3 ≤ ‖s + 3 / 2‖ ^ 3 := pow_le_pow_left₀ (by positivity) hm 3
  unfold VU
  rw [← hrr]
  calc 660 * c ^ 2 / (r * ‖s + 3 / 2‖ ^ 3) ≤ 660 * c ^ 2 / (r * (2 * c) ^ 3) := by gcongr
    _ = r / 8 * (660 / (r ^ 2 * c)) := by field_simp; ring

/-- `V ≤ √ε/8 ≤ 1/8` for `c ≥ 6000/ε²`. -/
theorem VU_le {ε c : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hcb : 6000 / ε ^ 2 ≤ c) : VU ε c ≤ Real.sqrt ε / 8 := by
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hrr : r ^ 2 = ε := Real.sq_sqrt hε.le
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hcb
  rw [div_le_iff₀ (by positivity)] at hcb
  unfold VU
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  rw [← hrr] at hcb ⊢
  have : r ^ 3 ≤ r ^ 2 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
  nlinarith [pow_pos hr0 4]

/-- **The bootstrap past the turning point**: `P_k ≠ 0` and `|v_k| ≤ V` at every `k`. -/
theorem bootstrap (h : Up ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀) (hcb : 6000 / ε ^ 2 ≤ c) :
    ∀ k, Pk c s₀ k ≠ 0 ∧ ‖vk c (Cvs.Prolate.EvenRungsByIndex.lev c 0) s₀ k‖ ≤ VU ε c := by
  set χ := Cvs.Prolate.EvenRungsByIndex.lev c 0
  have hc := h.c_pos
  have hε := h.hε
  have hV := VU_le hε h.hε1 hcb
  set r := Real.sqrt ε
  have hr0 : 0 < r := Real.sqrt_pos.mpr hε
  have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr h.hε1
  have hV0 : 0 < VU ε c := by unfold VU; positivity
  obtain ⟨K, hK⟩ : ∃ K, ∀ j, K ≤ j → Pk c s₀ j ≠ 0 ∧ ‖vk c χ s₀ j‖ ≤ VU ε c := by
    have e1 := eventually_Pk_ne hc (s₀ := s₀) (by linarith [h.hre])
    have e2 : ∀ᶠ k : ℕ in atTop, ‖vk c χ s₀ k‖ ≤ VU ε c := by
      have := (tendsto_vk h).norm
      rw [norm_zero] at this
      exact this.eventually (ge_mem_nhds hV0)
    exact (e1.and e2).exists_forall_of_atTop
  have step : ∀ k, (Pk c s₀ (k + 1) ≠ 0 ∧ ‖vk c χ s₀ (k + 1)‖ ≤ VU ε c) →
      (Pk c s₀ (k + 2) ≠ 0 ∧ ‖vk c χ s₀ (k + 2)‖ ≤ VU ε c) → Pk c s₀ k ≠ 0 ∧ ‖vk c χ s₀ k‖ ≤ VU ε c := by
    intro k ⟨hP1, hv1⟩ ⟨hP2, _⟩
    have hk := Up.line h k
    have hA := Cvs.Prolate.Mellin.PastTurningStepForcing.Up.norm_Af_le hk
    have hB := Up.norm_Bf_le_V hk
    have hv1ne : 1 + vk c χ s₀ (k + 1) ≠ 0 := by
      intro h0
      have : ‖vk c χ s₀ (k + 1)‖ = 1 := by
        rw [show vk c χ s₀ (k + 1) = -1 by linear_combination h0]; simp
      linarith
    have hstep := line_step h k hP1 hP2 hv1ne
    set w := Af c χ (s₀ + 2 * k) * (-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))) + Bf c χ (s₀ + 2 * k)
    have h1 : 1 - r / 8 ≤ ‖1 + vk c χ s₀ (k + 1)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-vk c χ s₀ (k + 1))
      rw [norm_neg, sub_neg_eq_add, norm_one] at this; linarith
    have hw : ‖w‖ ≤ VU ε c := by
      have h2 : ‖-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))‖ ≤ VU ε c / (1 - r / 8) := by
        rw [norm_div, norm_neg]; exact div_le_div₀ hV0.le hv1 (by linarith) h1
      calc ‖w‖ ≤ ‖Af c χ (s₀ + 2 * k)‖ * ‖-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))‖
            + ‖Bf c χ (s₀ + 2 * k)‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul]
        _ ≤ (1 - r / 4) * (VU ε c / (1 - r / 8)) + r / 8 * VU ε c := by
            have hA' : 0 ≤ 1 - r / 4 := by linarith
            exact add_le_add (mul_le_mul hA h2 (norm_nonneg _) hA') hB
        _ ≤ VU ε c := by
            have hq : (1 - r / 4) * (VU ε c / (1 - r / 8)) ≤ (1 - r / 8) * VU ε c := by
              rw [mul_div_assoc', div_le_iff₀ (by linarith)]
              nlinarith [sq_nonneg r]
            linarith
    have ew : 1 + Af c χ (s₀ + 2 * k) * (-vk c χ s₀ (k + 1) / (1 + vk c χ s₀ (k + 1))) + Bf c χ (s₀ + 2 * k)
        = 1 + w := by simp only [w]; ring
    rw [ew] at hstep
    have h1w : 1 + w ≠ 0 := by
      intro h0
      have : ‖w‖ = 1 := by rw [show w = -1 by linear_combination h0]; simp
      linarith
    have hP0 : Pk c s₀ k ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hstep
      exact mul_ne_zero hP1 h1w hstep.symm
    refine ⟨hP0, ?_⟩
    have hρ := Up.rho_ne hk
    have : vk c χ s₀ k = w := by
      unfold vk
      rw [hstep]; field_simp; ring
    rw [this]; exact hw
  have main : ∀ m k, K ≤ k + m → Pk c s₀ k ≠ 0 ∧ ‖vk c χ s₀ k‖ ≤ VU ε c := by
    intro m
    induction m with
    | zero => intro k hk; exact hK k (by simpa using hk)
    | succ m ih =>
      intro k hkm
      by_cases hkK : K ≤ k
      · exact hK k hkK
      · exact step k (ih (k + 1) (by omega)) (ih (k + 2) (by omega))
  intro k
  exact main K k (by omega)

end Cvs.Prolate.Mellin.PastTurningStepErrors
