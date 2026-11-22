import Mathlib
import Cvs.L2a.ChebyshevRampBound
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.RampIntegrals
import Cvs.L2a.RampOnePieceBounds
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two-piece bounds on `‖xw′/p‖²` and `‖w′/p‖²`

`w′² = π² sin²(2π(x − 3/2))` rises on `[3/2, 7/4]` and falls on `[7/4, 2]`. Chebyshev on the first piece and
`g ≤ g(7/4)` on the second give `∫ w′²g ≤ π²((1/2)∫_{3/2}^{7/4} g + g(7/4)/8)` for `g` nonincreasing, so
`‖xw′/p‖² ≤ π²(1937/10890 + (1/8) log(15/11))`, `‖w′/p‖² ≤ π²(1277/10890 − (1/8) log(15/11))`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.FarIntegrationByParts Cvs.L2a.FarFarBound Cvs.L2a.RampIntegrals Cvs.L2a.ChebyshevRampBound Cvs.L2a.RampOnePieceBounds

namespace Cvs.L2a.RampTwoPieceBounds

/-! ### `w′²` on the two pieces -/

/-- `w′²` is nondecreasing on `[3/2, 7/4]`. -/
theorem wF₁_sq_monotoneOn : MonotoneOn (fun x => wF₁ x ^ 2) (Icc (3 / 2) (7 / 4)) := by
  intro s hs t ht hst
  simp only
  rw [(wF_eq_on_Icc ⟨hs.1, by linarith [hs.2]⟩).1, (wF_eq_on_Icc ⟨ht.1, by linarith [ht.2]⟩).1]
  have h0 : 0 ≤ Real.sin (2 * π * s - 3 * π) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [pi_pos, hs.1]) (by nlinarith [pi_pos, hs.2])
  have h1 : Real.sin (2 * π * s - 3 * π) ≤ Real.sin (2 * π * t - 3 * π) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [pi_pos, hs.1]) (by nlinarith [pi_pos, ht.2])
      (by nlinarith [pi_pos])
  have := pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg π]

/-- `∫ w′²` over `[a, b] ⊆ [3/2, 2]` in terms of `u = 2πx − 3π`. -/
theorem integral_wF₁_sq_sub {a b : ℝ} (ha : 3 / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    ∫ x in a..b, wF₁ x ^ 2 = π ^ 2 * ((2 * π)⁻¹ * ∫ u in (2 * π * a - 3 * π)..(2 * π * b - 3 * π),
      Real.sin u ^ 2) := by
  rw [intervalIntegral.integral_congr (g := fun x => π ^ 2 * Real.sin (2 * π * x - 3 * π) ^ 2)
    (fun x hx => by
      rw [uIcc_of_le hab] at hx
      rw [(wF_eq_on_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩).1]; ring)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_sub (fun x => Real.sin x ^ 2) (by positivity : (2 * π) ≠ 0) (3 * π),
    smul_eq_mul]

/-- `∫_{3/2}^{7/4} w′² = π²/8`. -/
theorem integral_wF₁_sq_left : ∫ x in (3 / 2 : ℝ)..(7 / 4), wF₁ x ^ 2 = π ^ 2 / 8 := by
  rw [integral_wF₁_sq_sub le_rfl (by norm_num) (by norm_num), show 2 * π * (3 / 2) - 3 * π = 0 by ring,
    show 2 * π * (7 / 4) - 3 * π = π / 2 by ring, integral_sin_sq]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two]
  field_simp
  ring

/-- `∫_{7/4}^2 w′² = π²/8`. -/
theorem integral_wF₁_sq_right : ∫ x in (7 / 4 : ℝ)..2, wF₁ x ^ 2 = π ^ 2 / 8 := by
  rw [integral_wF₁_sq_sub (by norm_num) (by norm_num) le_rfl, show 2 * π * (7 / 4) - 3 * π = π / 2 by ring,
    show 2 * π * 2 - 3 * π = π by ring, integral_sin_sq]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two, Real.cos_pi_div_two]
  field_simp
  ring

/-! ### The two-piece bound -/

/-- **The two-piece bound**: for `g` nonincreasing and continuous on `[3/2, 2]`,
`∫_{3/2}^2 w′²g ≤ π²((1/2)∫_{3/2}^{7/4} g + g(7/4)/8)`. -/
theorem integral_wF₁_sq_mul_le {g : ℝ → ℝ} (hg : AntitoneOn g (Icc (3 / 2) 2))
    (hgc : ContinuousOn g (Icc (3 / 2) 2)) :
    ∫ x in (3 / 2 : ℝ)..2, wF₁ x ^ 2 * g x
      ≤ π ^ 2 * (1 / 2 * (∫ x in (3 / 2 : ℝ)..(7 / 4), g x) + 1 / 8 * g (7 / 4)) := by
  have hsub : Icc (3 / 2 : ℝ) (7 / 4) ⊆ Icc (3 / 2) 2 := Icc_subset_Icc le_rfl (by norm_num)
  have hsub' : Icc (7 / 4 : ℝ) 2 ⊆ Icc (3 / 2) 2 := Icc_subset_Icc (by norm_num) le_rfl
  have hc : ContinuousOn (fun x => wF₁ x ^ 2 * g x) (Icc (3 / 2) 2) :=
    (continuous_wF.2.pow 2).continuousOn.mul hgc
  have hi1 : IntervalIntegrable (fun x => wF₁ x ^ 2 * g x) volume (3 / 2) (7 / 4) :=
    ((uIcc_of_le (by norm_num : (3 / 2 : ℝ) ≤ 7 / 4)).symm ▸ hc.mono hsub).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => wF₁ x ^ 2 * g x) volume (7 / 4) 2 :=
    ((uIcc_of_le (by norm_num : (7 / 4 : ℝ) ≤ 2)).symm ▸ hc.mono hsub').intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have h1 := integral_mul_le_of_monotoneOn_antitoneOn (by norm_num) wF₁_sq_monotoneOn (hg.mono hsub)
    ((continuous_wF.2.pow 2).continuousOn) (hgc.mono hsub)
  rw [integral_wF₁_sq_left] at h1
  have h2 : ∫ x in (7 / 4 : ℝ)..2, wF₁ x ^ 2 * g x ≤ ∫ x in (7 / 4 : ℝ)..2, wF₁ x ^ 2 * g (7 / 4) :=
    intervalIntegral.integral_mono_on (by norm_num) hi2
      ((continuous_wF.2.pow 2).intervalIntegrable _ _ |>.mul_const _) fun x hx =>
        mul_le_mul_of_nonneg_left (hg ⟨by norm_num, by norm_num⟩ (hsub' hx) hx.1) (sq_nonneg _)
  rw [intervalIntegral.integral_mul_const, integral_wF₁_sq_right] at h2
  nlinarith

/-- `‖f‖² = ∫_{3/2}^2 w′²g` when `f² = w′²g` on `[3/2, ∞)`. -/
theorem nN_sq_eq_wF₁ {f g : ℝ → ℝ} (hfg : ∀ x, 3 / 2 ≤ x → f x ^ 2 = wF₁ x ^ 2 * g x) :
    nN f ^ 2 = ∫ x in (3 / 2 : ℝ)..2, wF₁ x ^ 2 * g x := by
  rw [nN_sq, setIntegral_Ioi_eq_interval fun x hx => by
    rw [hfg x (by linarith), (wF_of_two_le hx.le).2]; ring]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (by norm_num)] at hx
  exact hfg x hx.1

/-- **The two-piece bound with a primitive**: if `f² = w′²g` on `[3/2, ∞)`, `g` is nonincreasing and continuous on
`[3/2, 2]`, and `G′ = g` on `(1, ∞)`, then `‖f‖² ≤ π²((G(7/4) − G(3/2))/2 + g(7/4)/8)`. -/
theorem nN_sq_le_of_primitive₁ {f g G : ℝ → ℝ} (hfg : ∀ x, 3 / 2 ≤ x → f x ^ 2 = wF₁ x ^ 2 * g x)
    (hg : AntitoneOn g (Icc (3 / 2) 2)) (hgc : ContinuousOn g (Icc (3 / 2) 2))
    (hG : ∀ x, 1 < x → HasDerivAt G (g x) x) :
    nN f ^ 2 ≤ π ^ 2 * (1 / 2 * (G (7 / 4) - G (3 / 2)) + 1 / 8 * g (7 / 4)) := by
  have hI : uIcc (3 / 2 : ℝ) (7 / 4) = Icc (3 / 2) (7 / 4) := uIcc_of_le (by norm_num)
  have hmid : ∫ x in (3 / 2 : ℝ)..(7 / 4), g x = G (7 / 4) - G (3 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hG x (by rw [hI] at hx; linarith [hx.1]))
      ((hI ▸ hgc.mono (Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable)
  rw [nN_sq_eq_wF₁ hfg, ← hmid]
  exact integral_wF₁_sq_mul_le hg hgc

/-- `log(3/11) − log(1/5) = log(15/11)`. -/
theorem log_fifteen_elevenths : Real.log ((7 / 4 - 1) / (7 / 4 + 1)) - Real.log ((3 / 2 - 1) / (3 / 2 + 1))
    = Real.log (15 / 11) := by
  rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num

/-! ### The two closed forms -/

/-- **`ν₅`**: `‖xw′/p‖² ≤ π²(1937/10890 + (1/8) log(15/11))`. -/
theorem nN_xP₅_sq_le : nN xP₅ ^ 2 ≤ π ^ 2 * (1937 / 10890 + 1 / 8 * Real.log (15 / 11)) := by
  refine (nN_sq_le_of_primitive₁ (g := fun x => x ^ 2 / pP x ^ 2) (fun x _ => ?_) sq_div_pP_sq_antitoneOn
    (continuousOn_div_pP_pow (by fun_prop) 2) fun x hx => hasDerivAt_primSq hx).trans (le_of_eq ?_)
  · unfold xP₅; ring
  · have h := log_fifteen_elevenths
    unfold primSq pP
    norm_num at h ⊢
    linear_combination 1 / 8 * h

/-- **`ν₆`**: `‖w′/p‖² ≤ π²(1277/10890 − (1/8) log(15/11))`. -/
theorem nN_xP₆_sq_le : nN xP₆ ^ 2 ≤ π ^ 2 * (1277 / 10890 - 1 / 8 * Real.log (15 / 11)) := by
  refine (nN_sq_le_of_primitive₁ (g := fun x => 1 / pP x ^ 2) (fun x _ => ?_) (inv_pP_pow_antitoneOn 2)
    (continuousOn_div_pP_pow (by fun_prop) 2) fun x hx => hasDerivAt_primC_xP₄ hx).trans (le_of_eq ?_)
  · unfold xP₆; ring
  · have h := log_fifteen_elevenths
    unfold primC pP
    norm_num at h ⊢
    linear_combination -1 / 8 * h

/-- An admissible `ν₅`: `‖xw′/p‖ ≤ π (1937/10890 + (1/8) log(15/11))^{1/2}`. -/
theorem nN_xP₅_le : nN xP₅ ≤ π * √(1937 / 10890 + 1 / 8 * Real.log (15 / 11)) := by
  rw [← Real.sqrt_sq pi_pos.le, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le nN_xP₅_sq_le

/-- An admissible `ν₆`: `‖w′/p‖ ≤ π (1277/10890 − (1/8) log(15/11))^{1/2}`. -/
theorem nN_xP₆_le : nN xP₆ ≤ π * √(1277 / 10890 - 1 / 8 * Real.log (15 / 11)) := by
  rw [← Real.sqrt_sq pi_pos.le, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le nN_xP₆_sq_le

end Cvs.L2a.RampTwoPieceBounds

end
