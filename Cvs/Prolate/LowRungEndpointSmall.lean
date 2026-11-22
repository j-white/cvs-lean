import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.RungSpanProfilePowers
import Cvs.L2a.RungSpanTailHighMass

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The angular endpoint of a low rung is exponentially small: `h(1)² ≤ 100c⁴e^{−c/16}`

Agmon's estimate on the forbidden region `[3/4, 1]` of an even angular eigenfunction with `χ ≤ (2/5)c²`: with
`F = (1 − s²)h'h e^{cs/2}`, `F(1) = 0` and `F' ≥ (c²/16)h²e^{cs/2}` there, so `∫_{3/4}^1 h²e^{cs/2} ≤ 64c²e^{3c/8}`;
averaging `h(1)² ≤ 2h(t)² + 32c⁶δ²` over `t ∈ [1 − δ, 1]`, `δ = e^{−c/16}/c`, gives the bound.
-/

noncomputable section

open Real Set MeasureTheory
open Cvs.L2a.AngularProlateTailPositive (psi)

namespace Cvs.Prolate.LowRungEndpointSmall

set_option maxHeartbeats 1600000 in
/-- **Agmon at the angular endpoint**: an even normalised angular eigenfunction with `0 ≤ χ ≤ (2/5)c²`, `μ ≥ 1/c`,
`c ≥ 100`, has `h(1)² ≤ 100c⁴e^{−c/16}`. -/
theorem endpoint_sq_le {g g₁ g₂ : ℝ → ℝ} {c χ μ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2)
    (hμc : 1 / c ≤ μ) :
    g 1 ^ 2 ≤ 100 * c ^ 4 * exp (-(c / 16)) := by
  have hc0 : 0 < c := by linarith
  have hμ0 : 0 < μ := lt_of_lt_of_le (by positivity) hμc
  have hU : ∀ s ∈ Icc (0 : ℝ) 1, s ∈ uIcc (-1 : ℝ) 1 := fun s hs => by
    rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith [hs.1], hs.2⟩
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  obtain ⟨hI, -, -, hd1, -, h2, -⟩ := Cvs.L2a.RungSpanProfilePowers.rung_data hg hg₁ hg₂c hang heven hnorm hμ
    (by linarith) hχ0 (by nlinarith) hμc
  -- `|g| ≤ 2c` on `[−1, 1]`
  have hinv : 1 / μ ≤ c := by
    rw [div_le_iff₀ hμ0]; have := mul_le_mul_of_nonneg_left hμc hc0.le
    rw [mul_one_div_cancel hc0.ne'] at this; linarith
  have hsup : ∀ s ∈ Icc (-1 : ℝ) 1, |g s| ≤ 2 * c := fun s hs => by
    have h := Cvs.L2a.RungSpanTailHighMass.abs_psi_le_L1 (c := c) (ξ := s) hgc
    rw [hμ s hs, abs_mul, abs_of_pos hμ0, one_mul] at h
    have hI0 : 0 ≤ ∫ s in (-1 : ℝ)..1, |g s| := intervalIntegral.integral_nonneg (by norm_num) fun _ _ => abs_nonneg _
    have : |g s| ≤ (∫ s in (-1 : ℝ)..1, |g s|) / μ := by rw [le_div_iff₀ hμ0]; linarith
    calc |g s| ≤ (∫ s in (-1 : ℝ)..1, |g s|) / μ := this
      _ = (∫ s in (-1 : ℝ)..1, |g s|) * (1 / μ) := by ring
      _ ≤ 2 * c := mul_le_mul hI hinv (by positivity) (by norm_num)
  -- `|g'| ≤ 4c³` on `[0, 1]`
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, |g₁ s| ≤ 4 * c ^ 3 := fun s hs => by
    have hsub : uIcc s 1 ⊆ uIcc (-1 : ℝ) 1 := by
      rw [uIcc_of_le hs.2, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by linarith [hs.1]) le_rfl
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hg₁ t (hsub ht))
      ((hg₂c.mono hsub).intervalIntegrable)
    have hint : |∫ t in s..1, g₂ t| ≤ ∫ t in (-1 : ℝ)..1, |g₂ t| := by
      calc |∫ t in s..1, g₂ t| ≤ ∫ t in s..1, |g₂ t| := intervalIntegral.abs_integral_le_integral_abs hs.2
        _ ≤ ∫ t in (-1 : ℝ)..1, |g₂ t| := by
          apply intervalIntegral.integral_mono_interval (by linarith [hs.1]) hs.2 le_rfl
            (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          exact (hg₂c.abs).intervalIntegrable
    have : g₁ s = g₁ 1 - ∫ t in s..1, g₂ t := by linarith
    rw [this]
    calc |g₁ 1 - ∫ t in s..1, g₂ t| ≤ |g₁ 1| + |∫ t in s..1, g₂ t| := abs_sub _ _
      _ ≤ c ^ 3 + 3 * c ^ 3 := add_le_add hd1 (hint.trans h2)
      _ = 4 * c ^ 3 := by ring
  -- the Agmon identity on `[3/4, 1]`
  set W : ℝ → ℝ := fun s => exp (c * s / 2) with hW
  have hWd : ∀ s, HasDerivAt W (W s * (c / 2)) s := fun s => by
    have hlin : HasDerivAt (fun s : ℝ => c * s / 2) (c / 2) s := by
      simpa using ((hasDerivAt_id s).const_mul c).div_const 2
    exact hlin.exp
  set F : ℝ → ℝ := fun s => (1 - s ^ 2) * g₁ s * g s * W s with hF
  set F' : ℝ → ℝ := fun s => ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) * g s * W s
      + (1 - s ^ 2) * g₁ s * (g₁ s * W s + g s * (W s * (c / 2))) with hF'
  have hFd : ∀ s ∈ uIcc (3 / 4 : ℝ) 1, HasDerivAt F (F' s) s := fun s hs => by
    rw [uIcc_of_le (by norm_num)] at hs
    have hs' := hU s ⟨by linarith [hs.1], hs.2⟩
    have hp : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
      simpa using ((hasDerivAt_pow 2 s).const_sub 1)
    have := ((hp.mul (hg₁ s hs')).mul (hg s hs')).mul (hWd s)
    refine this.congr_deriv ?_
    simp only [hF', Pi.mul_apply]; ring
  have hW0 : ∀ s, 0 < W s := fun s => exp_pos _
  have hsub34 : uIcc (3 / 4 : ℝ) 1 ⊆ uIcc (-1 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num), uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl
  have hWc : Continuous W := by simp only [hW]; fun_prop
  have hF'c : ContinuousOn F' (uIcc (3 / 4 : ℝ) 1) := by
    simp only [hF']
    have h1 := hgc.mono hsub34
    have h2' := hg₁c.mono hsub34
    have h3 := hg₂c.mono hsub34
    have hcs : ContinuousOn (fun s : ℝ => s) (uIcc (3 / 4 : ℝ) 1) := continuousOn_id
    exact ((((continuousOn_const.sub (hcs.pow 2)).mul h3).sub ((continuousOn_const.mul hcs).mul h2')).mul h1 |>.mul
      hWc.continuousOn).add (((continuousOn_const.sub (hcs.pow 2)).mul h2').mul
        ((h2'.mul hWc.continuousOn).add (h1.mul (hWc.continuousOn.mul continuousOn_const))))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hFd hF'c.intervalIntegrable
  have hF1 : F 1 = 0 := by simp [hF]
  -- `F' ≥ (c²/16)g²W` on `[3/4, 1]`
  have hlow : ∀ s ∈ Icc (3 / 4 : ℝ) 1, c ^ 2 / 16 * (g s ^ 2 * W s) ≤ F' s := fun s hs => by
    have hs' := hU s ⟨by linarith [hs.1], hs.2⟩
    have hq := hang s hs'
    have hpe : (1 - s ^ 2) * g₂ s - 2 * s * g₁ s = (c ^ 2 * s ^ 2 - χ) * g s := by linarith
    simp only [hF']
    rw [hpe]
    have hs2 : 9 / 16 ≤ s ^ 2 := by nlinarith [hs.1]
    have hp0 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.2, hs.1]
    have hp7 : 1 - s ^ 2 ≤ 7 / 16 := by linarith
    have key : c ^ 2 / 16 * g s ^ 2 ≤ (c ^ 2 * s ^ 2 - χ) * g s ^ 2 + (1 - s ^ 2) * g₁ s ^ 2
        + (1 - s ^ 2) * (c / 2) * g s * g₁ s := by
      have hsq : 0 ≤ (1 - s ^ 2) * (g₁ s + c / 4 * g s) ^ 2 := mul_nonneg hp0 (sq_nonneg _)
      have hcoef : c ^ 2 / 16 + (1 - s ^ 2) * c ^ 2 / 16 ≤ c ^ 2 * s ^ 2 - χ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg (g s))]
    have hWs := hW0 s
    nlinarith [mul_le_mul_of_nonneg_right key hWs.le]
  have hgWi : IntervalIntegrable (fun s => g s ^ 2 * W s) volume (3 / 4) 1 :=
    ((hgc.mono hsub34).pow 2 |>.mul hWc.continuousOn).intervalIntegrable
  have hAg : c ^ 2 / 16 * ∫ s in (3 / 4 : ℝ)..1, g s ^ 2 * W s ≤ -F (3 / 4) := by
    rw [← intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_mono_on (by norm_num) (hgWi.const_mul _) hF'c.intervalIntegrable hlow
    rw [hFTC, hF1] at this; linarith
  have hFa : -F (3 / 4) ≤ 4 * c ^ 4 * W (3 / 4) := by
    have h1 := hd (3 / 4) ⟨by norm_num, by norm_num⟩
    have h2'' := hsup (3 / 4) ⟨by norm_num, by norm_num⟩
    have : |F (3 / 4)| ≤ 4 * c ^ 4 * W (3 / 4) := by
      simp only [hF, abs_mul, abs_of_pos (hW0 _)]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 - (3 / 4) ^ 2)]
      have := mul_le_mul h1 h2'' (abs_nonneg _) (by positivity)
      have hWa := hW0 (3 / 4)
      nlinarith [abs_nonneg (g₁ (3 / 4)), abs_nonneg (g (3 / 4)), mul_le_mul_of_nonneg_right this hWa.le,
        mul_nonneg (mul_nonneg (abs_nonneg (g₁ (3 / 4))) (abs_nonneg (g (3 / 4)))) hWa.le]
    linarith [neg_abs_le (F (3 / 4)), le_abs_self (F (3 / 4))]
  have hAgm : ∫ s in (3 / 4 : ℝ)..1, g s ^ 2 * W s ≤ 64 * c ^ 2 * W (3 / 4) := by
    have h := hAg.trans hFa
    rw [← le_div_iff₀' (by positivity)] at h
    calc _ ≤ 4 * c ^ 4 * W (3 / 4) / (c ^ 2 / 16) := h
      _ = 64 * c ^ 2 * W (3 / 4) := by field_simp; ring
  -- averaging near the endpoint
  set A := exp (-(c / 16)) with hA
  have hA0 : 0 < A := exp_pos _
  have hA1 : A ≤ 1 := by rw [hA]; exact exp_le_one_iff.mpr (by linarith)
  set δ := A / c with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by
    rw [hδ, div_le_iff₀ hc0]; nlinarith
  set b := 1 - δ with hb
  set B := exp (c * δ / 2) with hB
  have hB2 : B ≤ 2 := by
    have : c * δ / 2 ≤ 1 / 2 := by
      rw [hδ, mul_div_cancel₀ _ hc0.ne']; linarith
    calc B ≤ exp (1 / 2) := exp_le_exp.mpr this
      _ ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h2 : exp (1 / 2) ^ 2 = exp 1 := by rw [← exp_nat_mul]; norm_num
        nlinarith [exp_pos (1 / 2 : ℝ)]
  have hB1 : 1 ≤ B := one_le_exp (by positivity)
  have hb34 : 3 / 4 ≤ b := by linarith
  have hbI : uIcc b 1 ⊆ uIcc (3 / 4 : ℝ) 1 := by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by norm_num)]; exact Icc_subset_Icc hb34 le_rfl
  -- pointwise: `g(1)² ≤ 2g(t)² + 32c⁶δ²` on `[b, 1]`
  have hpt : ∀ t ∈ Icc b 1, g 1 ^ 2 ≤ 2 * g t ^ 2 + 32 * c ^ 6 * δ ^ 2 := fun t ht => by
    have hsub : uIcc t 1 ⊆ uIcc (-1 : ℝ) 1 := by
      rw [uIcc_of_le ht.2, uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by linarith [ht.1]) le_rfl
    have hFTC' := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hg s (hsub hs))
      ((hg₁c.mono hsub).intervalIntegrable)
    have hbd : |∫ s in t..1, g₁ s| ≤ 4 * c ^ 3 * δ := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := 1) (C := 4 * c ^ 3) (f := g₁)
        (fun s hs => by
          rw [uIoc_of_le ht.2] at hs
          rw [Real.norm_eq_abs]; exact hd s ⟨by linarith [hs.1, ht.1], hs.2⟩)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)] at h
      calc _ ≤ 4 * c ^ 3 * (1 - t) := h
        _ ≤ 4 * c ^ 3 * δ := mul_le_mul_of_nonneg_left (by linarith [ht.1]) (by positivity)
    have e : g 1 = g t + ∫ s in t..1, g₁ s := by linarith
    rw [e]
    have := abs_le.mp hbd
    nlinarith [sq_nonneg (g t - ∫ s in t..1, g₁ s)]
  have hWb : ∀ t ∈ Icc b 1, W b ≤ W t := fun t ht => exp_le_exp.mpr (by nlinarith [ht.1])
  have hWt1 : ∀ t ∈ Icc b 1, W t ≤ W 1 := fun t ht => exp_le_exp.mpr (by nlinarith [ht.2])
  have hWbi : IntervalIntegrable W volume b 1 := hWc.intervalIntegrable _ _
  have hgWb : IntervalIntegrable (fun s => g s ^ 2 * W s) volume b 1 := hgWi.mono_set hbI
  have hint : g 1 ^ 2 * (δ * W b) ≤ 2 * (64 * c ^ 2 * W (3 / 4)) + 32 * c ^ 6 * δ ^ 2 * (δ * W 1) := by
    have hlhs : δ * W b ≤ ∫ s in b..1, W s := by
      have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hWbi hWb
      rw [intervalIntegral.integral_const, smul_eq_mul, show 1 - b = δ by rw [hb]; ring] at this
      exact this
    have hrhs1 : ∫ s in b..1, W s ≤ δ * W 1 := by
      have := intervalIntegral.integral_mono_on (by linarith) hWbi intervalIntegrable_const hWt1
      rw [intervalIntegral.integral_const, smul_eq_mul, show 1 - b = δ by rw [hb]; ring] at this
      exact this
    have hmono : ∫ s in b..1, g 1 ^ 2 * W s ≤ ∫ s in b..1, (2 * g s ^ 2 + 32 * c ^ 6 * δ ^ 2) * W s :=
      intervalIntegral.integral_mono_on (by linarith) (hWbi.const_mul _)
        ((((hgc.mono (hbI.trans hsub34)).pow 2).const_smul (2 : ℝ) |>.add continuousOn_const |>.mul
          hWc.continuousOn).intervalIntegrable)
        fun t ht => mul_le_mul_of_nonneg_right (hpt t ht) (hW0 t).le
    have hsplit : ∫ s in b..1, (2 * g s ^ 2 + 32 * c ^ 6 * δ ^ 2) * W s
        = 2 * (∫ s in b..1, g s ^ 2 * W s) + 32 * c ^ 6 * δ ^ 2 * ∫ s in b..1, W s := by
      have e : ∫ s in b..1, (2 * g s ^ 2 + 32 * c ^ 6 * δ ^ 2) * W s
          = ∫ s in b..1, (2 * (g s ^ 2 * W s) + 32 * c ^ 6 * δ ^ 2 * W s) :=
        intervalIntegral.integral_congr fun s _ => by ring
      rw [e, intervalIntegral.integral_add (hgWb.const_mul _) (hWbi.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hsub2 : ∫ s in b..1, g s ^ 2 * W s ≤ ∫ s in (3 / 4 : ℝ)..1, g s ^ 2 * W s := by
      apply intervalIntegral.integral_mono_interval hb34 (by linarith) le_rfl
        (Filter.Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (hW0 s).le) hgWi
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [hsplit] at hmono
    have hc6 : 0 ≤ 32 * c ^ 6 * δ ^ 2 := by positivity
    calc g 1 ^ 2 * (δ * W b) ≤ g 1 ^ 2 * ∫ s in b..1, W s := mul_le_mul_of_nonneg_left hlhs (sq_nonneg _)
      _ ≤ 2 * (∫ s in b..1, g s ^ 2 * W s) + 32 * c ^ 6 * δ ^ 2 * ∫ s in b..1, W s := hmono
      _ ≤ 2 * (64 * c ^ 2 * W (3 / 4)) + 32 * c ^ 6 * δ ^ 2 * (δ * W 1) :=
          add_le_add (mul_le_mul_of_nonneg_left (hsub2.trans hAgm) (by norm_num : (0 : ℝ) ≤ 2))
            (mul_le_mul_of_nonneg_left hrhs1 hc6)
  -- the exponents
  have eW1 : W 1 = exp (c / 2) := by simp [hW]
  have eWb : W b = exp (c / 2) / B := by
    simp only [hW, hB, hb]; rw [← exp_sub]; congr 1; ring
  have eWa : W (3 / 4) = exp (c / 2) * A ^ 2 := by
    simp only [hW, hA]; rw [← exp_nat_mul, ← exp_add]; congr 1; push_cast; ring
  rw [eW1, eWb, eWa] at hint
  have hE := exp_pos (c / 2)
  -- divide out `e^{c/2}`
  have hint' : g 1 ^ 2 * δ ≤ B * (128 * c ^ 2 * A ^ 2 + 32 * c ^ 6 * δ ^ 3) := by
    have h := hint
    have e1 : g 1 ^ 2 * (δ * (exp (c / 2) / B)) = g 1 ^ 2 * δ / B * exp (c / 2) := by field_simp
    have e2 : 2 * (64 * c ^ 2 * (exp (c / 2) * A ^ 2)) + 32 * c ^ 6 * δ ^ 2 * (δ * exp (c / 2))
        = (128 * c ^ 2 * A ^ 2 + 32 * c ^ 6 * δ ^ 3) * exp (c / 2) := by ring
    rw [e1, e2] at h
    have h' := le_of_mul_le_mul_right h hE
    have h'' := (div_le_iff₀ (by linarith : (0 : ℝ) < B)).mp h'
    linarith [mul_comm (128 * c ^ 2 * A ^ 2 + 32 * c ^ 6 * δ ^ 3) B]
  -- substitute `δ = A/c`
  have hfinal : g 1 ^ 2 ≤ B * (128 * c ^ 3 * A + 32 * c ^ 4 * A ^ 2) := by
    rw [hδ] at hint'
    have e : B * (128 * c ^ 2 * A ^ 2 + 32 * c ^ 6 * (A / c) ^ 3) = (A / c) * (B * (128 * c ^ 3 * A + 32 * c ^ 4 * A ^ 2)) := by
      field_simp
    rw [e] at hint'
    exact le_of_mul_le_mul_left (by rw [mul_comm] at hint'; linarith) (by positivity : 0 < A / c)
  calc g 1 ^ 2 ≤ B * (128 * c ^ 3 * A + 32 * c ^ 4 * A ^ 2) := hfinal
    _ ≤ 2 * (128 * c ^ 3 * A + 32 * c ^ 4 * A) := by
        apply mul_le_mul hB2 (by nlinarith [mul_le_mul_of_nonneg_left hA1 hA0.le, pow_pos hc0 4]) (by positivity)
          (by norm_num)
    _ ≤ 100 * c ^ 4 * A := by
        have h36 : 256 * c ^ 3 ≤ 36 * c ^ 4 := by nlinarith [pow_pos hc0 3]
        nlinarith [mul_le_mul_of_nonneg_right h36 hA0.le]

end Cvs.Prolate.LowRungEndpointSmall
