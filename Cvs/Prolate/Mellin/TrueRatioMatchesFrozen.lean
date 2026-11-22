import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.EndpointAsymptotics
import Cvs.Prolate.Mellin.FarRegionDamping
import Cvs.Prolate.Mellin.FrozenRootDecayOffLine
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.RungThreeTermRecurrence
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.UniformRootBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The true step ratio agrees with the frozen root at infinity

Along `s_k = s₀ + 2k`: `s_k·mel h₀ s_k → h₀(1) ≠ 0` for the ground rung `h₀`; the frozen root has
`y = ρ*(s)(s+2)/c → 1` because the step quadratic reads `y − 1 = (yχ − c²y²)/((s+1)(s+2))`; and
`P(s+2)/P(s) = (c/s)·M(s+2)/M(s)`. Hence `v_k = ρ*(s_k)P(s_k)/P(s_{k+1}) − 1 → 0`.
-/

noncomputable section

open Complex Set Filter Topology

namespace Cvs.Prolate.Mellin.TrueRatioMatchesFrozen

open Cvs.Prolate.Mellin.RungThreeTermRecurrence (mel)
open Cvs.Prolate.Mellin.LawRatioRecurrence (mg lawRatio)
open Cvs.Prolate.Mellin.FrozenRootErrorIdentity (omega tau zeta rhoStar)
open Cvs.Prolate.Mellin.UniformRootBounds (Hyp)

/-- **The quadratic in `y = ρ(s+2)/c`**: if `(s+2)ρ² + qρ − (s+1) = 0` with `q = ((s+1)(s+2) − χ)/c`, then
`(y − 1)(s+1)(s+2) = yχ − c²y²`. -/
theorem y_identity {c χ : ℝ} (hc : c ≠ 0) {s ρ : ℂ} (hs2 : s + 2 ≠ 0)
    (h : (s + 2) * ρ ^ 2 + ((s + 1) * (s + 2) - χ) / c * ρ - (s + 1) = 0) :
    (ρ * (s + 2) / c - 1) * ((s + 1) * (s + 2)) = ρ * (s + 2) / c * χ - c ^ 2 * (ρ * (s + 2) / c) ^ 2 := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have e1 : (c : ℂ) ^ 2 * (ρ * (s + 2) / c) ^ 2 = (ρ * (s + 2)) ^ 2 := by field_simp
  rw [e1]
  linear_combination (s + 2) * h

/-- The ground rung's endpoint bound. -/
theorem exists_bound_rung₁ (c : ℝ) : ∃ B₁, ∀ w ∈ Icc (0 : ℝ) 1, |Cvs.Prolate.EvenRungsByIndex.rung₁ c 0 w| ≤ B₁ := by
  have hk := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  obtain ⟨-, hd₁, -, -, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec hk
  have hc : ContinuousOn (Cvs.Prolate.EvenRungsByIndex.rung₁ c 0) (Icc 0 1) := fun w hw =>
    (hd₁ w (by rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl hw)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨B, fun w hw => by have := hB w hw; rwa [Real.norm_eq_abs] at this⟩

/-- **`s_k·mel h₀ s_k → h₀(1)`** along `s_k = s₀ + 2k`, `Re s₀ > 0`. -/
theorem tendsto_mul_mel (c : ℝ) {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    Tendsto (fun k : ℕ => (s₀ + 2 * k) * mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)) atTop
      (𝓝 (Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ)) := by
  have hk := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  obtain ⟨hd, hd₁, -, -, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec hk
  have hsub : Icc (0 : ℝ) 1 ⊆ uIcc (-1) 1 := by
    rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl
  have hc₁ : ContinuousOn (Cvs.Prolate.EvenRungsByIndex.rung₁ c 0) (Icc 0 1) := fun w hw => (hd₁ w (hsub hw)).continuousAt.continuousWithinAt
  obtain ⟨B₁, hB⟩ := exists_bound_rung₁ c
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ k : ℕ, ‖(s₀ + 2 * k) * mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k) - Cvs.Prolate.EvenRungsByIndex.rung c 0 1‖
      ≤ B₁ / (s₀.re + 2 * k + 1) := by
    intro k
    have hre : (s₀ + 2 * (k : ℂ)).re = s₀.re + 2 * k := by simp
    have := Cvs.Prolate.Mellin.EndpointAsymptotics.norm_mul_mel_sub_le (fun w hw => hd w (hsub hw)) hc₁ hB
      (s := s₀ + 2 * k) (by rw [hre]; positivity)
    rwa [hre] at this
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  have : Tendsto (fun k : ℕ => s₀.re + 2 * (k : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop_add_const_right
    exact tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  exact this.const_div_atTop B₁ |>.congr fun k => rfl

variable {ε c χ : ℝ} {s₀ : ℂ}

/-- **`ρ*(s_k)(s_k+2)/c → 1`** along a line in the region. -/
theorem tendsto_y (h : Hyp ε c χ s₀) :
    Tendsto (fun k : ℕ => rhoStar c χ (s₀ + 2 * k) * (s₀ + 2 * k + 2) / c) atTop (𝓝 1) := by
  have hc := h.c_pos
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set x : ℕ → ℝ := fun k => s₀.re + 2 * k
  have hx : ∀ k : ℕ, (s₀ + 2 * (k : ℂ)).re = x k := fun k => by simp [x]
  -- eventually far: x k ≥ 2c
  have hev : ∀ᶠ k : ℕ in atTop, 2 * c ≤ x k := by
    have : Tendsto x atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    exact this.eventually_ge_atTop _
  have hbound : ∀ᶠ k : ℕ in atTop, ‖rhoStar c χ (s₀ + 2 * k) * (s₀ + 2 * k + 2) / c - 1‖
      ≤ (8 * χ + 64 * c ^ 2) / ((x k + 1) * (x k + 2)) := by
    filter_upwards [hev] with k hk
    have hk' := Cvs.Prolate.Mellin.StepAmplification.hyp_line h k
    have hfar : 2 * c ≤ (s₀ + 2 * (k : ℂ)).re := by rw [hx]; exact hk
    have hρ := Cvs.Prolate.Mellin.FrozenRootDecayOffLine.Hyp.norm_rho_le_far hk' (Cvs.Prolate.Mellin.FarRegionDamping.Hyp.far_omega hk' hfar)
    rw [hx] at hρ
    set s := s₀ + 2 * (k : ℂ)
    have hroot := Cvs.Prolate.Mellin.FrozenRootErrorIdentity.rhoStar_root (χ := χ) hc.ne' hk'.m_ne hk'.s2_ne hk'.omega_ne
    have hid := y_identity hc.ne' hk'.s2_ne hroot
    set y := rhoStar c χ s * (s + 2) / c
    have hx0 : 0 < x k := by linarith
    have hs2n : ‖s + 2‖ ≤ x k + 2 + 2 * c := by
      have hn := Complex.norm_le_abs_re_add_abs_im (s + 2)
      have him := hk'.him; have hε := hk'.hε
      have hr : (s + 2).re = x k + 2 := by simp [s, x]
      have hi : (s + 2).im = s.im := by simp
      rw [hr, hi, abs_of_pos (by linarith)] at hn
      have : |s.im| ≤ 2 * c := by nlinarith
      linarith
    have hy : ‖y‖ ≤ 8 := by
      simp only [y]
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, div_le_iff₀ hc]
      calc ‖rhoStar c χ s‖ * ‖s + 2‖ ≤ 4 * c / (x k + 3 / 2) * (x k + 2 + 2 * c) :=
            mul_le_mul hρ hs2n (norm_nonneg _) (by positivity)
        _ ≤ 8 * c := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
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
    have hnum : ‖y * χ - c ^ 2 * y ^ 2‖ ≤ 8 * χ + 64 * c ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      have k1 := mul_le_mul_of_nonneg_right hy hχ0
      have k2 : ‖y‖ ^ 2 ≤ 8 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
      have k3 := mul_le_mul_of_nonneg_left k2 (sq_nonneg c)
      nlinarith
    exact div_le_div₀ (by positivity) hnum hden0 hden
  refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) hbound ?_
  have hx2 : Tendsto (fun k : ℕ => (x k + 1) * (x k + 2)) atTop atTop := by
    have : Tendsto x atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    exact (tendsto_atTop_add_const_right _ 1 this).atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ 2 this)
  exact hx2.const_div_atTop _

/-- The law ratio step: `P(s+2)/P(s) = (c/s) M(s+2)/M(s)`. -/
theorem lawRatio_step {f : ℝ → ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) (hM : mel f s ≠ 0) :
    lawRatio c f (s + 2) / lawRatio c f s = c / s * (mel f (s + 2) / mel f s) := by
  have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
  have hg := Cvs.Prolate.Mellin.LawRatioRecurrence.mg_ne_zero hc hs
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold lawRatio
  rw [Cvs.Prolate.Mellin.LawRatioRecurrence.mg_add_two hc hs0]
  field_simp

/-- **`v_k → 0`**: `ρ*(s_k) P(s_k)/P(s_{k+1}) − 1 → 0` for `P = lawRatio c h₀`, `h₀` the ground rung. -/
theorem tendsto_v (h : Hyp ε c χ s₀) :
    Tendsto (fun k : ℕ => rhoStar c χ (s₀ + 2 * k) * lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)
      / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2) - 1) atTop (𝓝 0) := by
  have hc := h.c_pos
  have h1 := tendsto_mul_mel c (s₀ := s₀) (by linarith [h.hre])
  have h2 : Tendsto (fun k : ℕ => (s₀ + 2 * k + 2) * mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2)) atTop
      (𝓝 (Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ)) := by
    have := (tendsto_mul_mel c (s₀ := s₀) (by linarith [h.hre])).comp (tendsto_add_atTop_nat 1)
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
  have hs2 : s₀ + 2 * (k : ℂ) + 2 ≠ 0 := (Cvs.Prolate.Mellin.StepAmplification.hyp_line h k).s2_ne
  have hg := Cvs.Prolate.Mellin.LawRatioRecurrence.mg_ne_zero hc hre
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hP : lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2) / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)
      = c / (s₀ + 2 * k) * (mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2) / mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)) :=
    lawRatio_step hc hre hM0
  have hP0 : lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k) ≠ 0 := by
    unfold lawRatio; exact div_ne_zero hM0 hg
  have hP2 : lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hP
    exact (mul_ne_zero (div_ne_zero hc' hs0) (div_ne_zero hM2 hM0)) hP.symm
  have e : rhoStar c χ (s₀ + 2 * k) * lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)
      / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2)
      = rhoStar c χ (s₀ + 2 * k) / (lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k + 2)
          / lawRatio c (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * k)) := by
    field_simp
  rw [e, hP]
  field_simp

end Cvs.Prolate.Mellin.TrueRatioMatchesFrozen
