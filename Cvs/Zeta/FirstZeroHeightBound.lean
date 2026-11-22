import Mathlib
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStrip
import Cvs.Zeta.ZeroFreeHeightFive

/-!
# The ceiling of the constant method, and reaching it

`ZeroFreeHeightFive` proved `|Im ρ| > 5` from `‖Λ₀‖ ≤ 2.1·e^{−π}/π ≈ 0.0289`.
-/

noncomputable section

open Complex Cvs.Zeta

namespace Cvs.Zeta.FirstZeroHeightBound
open Cvs.ZeroFree

/-- The constant is below `1/31.25`, which is what `t = 5.5` needs. -/
theorem const_lt_sharp : 2.1 * (Real.exp (-Real.pi) / Real.pi) < 1 / 31.25 := by
  have h21 := Cvs.ZeroFree.exp_pi_gt_21
  have hepos : (0:ℝ) < Real.exp Real.pi := Real.exp_pos _
  have hE : (0:ℝ) < Real.exp (-Real.pi) := Real.exp_pos _
  have hinv : Real.exp (-Real.pi) < 1 / 21 := by
    rw [Real.exp_neg, inv_lt_comm₀ hepos (by norm_num)]
    linarith
  have h314 : (3.14:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have hkey : 65.625 * Real.exp (-Real.pi) < Real.pi := by nlinarith
  rw [mul_div_assoc', div_lt_iff₀ hpipos]
  linarith

/-- **What a zero forces on the constant.**  `ξ s = 0` makes `s(s−1)Λ₀(s)` have modulus
one, and `‖s‖‖s−1‖ ≤ 1 + t²` on the strip, so the bound cannot beat `1/(1+t²)`. -/
theorem one_le_one_add_sq_mul_const {s : ℂ} (h : riemannXi s = 0) :
    (1:ℝ) ≤ (1 + s.im ^ 2) * (2.1 * (Real.exp (-Real.pi) / Real.pi)) := by
  obtain ⟨h0, h1⟩ := riemannXi_zero_mem_strip h
  have hL := Cvs.ZeroFree.norm_completedRiemannZeta₀_le_sharp (s := s) (by linarith) (by linarith)
  have hns : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hns1 : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]
    ring
  have hA : ‖s‖ ^ 2 ≤ 1 + s.im ^ 2 := by rw [hns]; nlinarith
  have hB : ‖s - 1‖ ^ 2 ≤ 1 + s.im ^ 2 := by rw [hns1]; nlinarith
  have hprod : ‖s‖ * ‖s - 1‖ ≤ 1 + s.im ^ 2 := by
    have hsq : (‖s‖ * ‖s - 1‖) ^ 2 ≤ (1 + s.im ^ 2) ^ 2 := by
      have := mul_le_mul hA hB (by positivity) (by positivity)
      nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
    nlinarith [norm_nonneg s, norm_nonneg (s - 1), sq_nonneg s.im,
      mul_nonneg (norm_nonneg s) (norm_nonneg (s - 1))]
  have hxi : riemannXi s - 1 / 2 = s * (s - 1) * completedRiemannZeta₀ s / 2 := by
    rw [riemannXi]; ring
  have hhalf : ‖riemannXi s - 1 / 2‖ = 1 / 2 := by
    rw [h, zero_sub, norm_neg, show ‖(1/2:ℂ)‖ = 1/2 by norm_num]
  have hbd : (1:ℝ) / 2
      ≤ (1 + s.im ^ 2) * (2.1 * (Real.exp (-Real.pi) / Real.pi)) / 2 := by
    rw [← hhalf, hxi, norm_div, norm_mul, norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
    have hstep : ‖s‖ * ‖s - 1‖ * ‖completedRiemannZeta₀ s‖
        ≤ (1 + s.im ^ 2) * (2.1 * (Real.exp (-Real.pi) / Real.pi)) :=
      mul_le_mul hprod hL (norm_nonneg _) (by positivity)
    linarith
  linarith

/-- **The zero-free height, at this constant.**  Every zero of `ξ` has `|Im ρ| > 5.5`. -/
theorem abs_im_gt_of_riemannXi_eq_zero {s : ℂ} (h : riemannXi s = 0) : 5.5 < |s.im| := by
  have h1' := one_le_one_add_sq_mul_const h
  have hsq : (0:ℝ) ≤ s.im ^ 2 := sq_nonneg _
  have hlt : (1 + s.im ^ 2) * (2.1 * (Real.exp (-Real.pi) / Real.pi))
      < (1 + s.im ^ 2) * (1 / 31.25) := by
    refine mul_lt_mul_of_pos_left const_lt_sharp ?_
    linarith
  have ht2 : (30.25:ℝ) < s.im ^ 2 := by nlinarith
  nlinarith [sq_abs s.im, abs_nonneg s.im]

end Cvs.Zeta.FirstZeroHeightBound
