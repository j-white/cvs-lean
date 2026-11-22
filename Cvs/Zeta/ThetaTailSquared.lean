import Mathlib
import Cvs.Zeta.KernelPrefactorBound
import Cvs.Zeta.ThetaDecay
import Cvs.Zeta.ZeroFreeHeightFive
import Cvs.Zeta.ZetaRealSegment

/-!
# The theta tail with the square kept

Mathlib's `norm_jacobiTheta_sub_one_le` bounds `‖cexp(πIm²τ)‖` by `e^{−πt·m}`, using
`m² ≥ m`.  Keeping the square costs one geometric comparison and takes the prefactor from
`2.0904` to `2.0002`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex Cvs.Zeta

namespace Cvs.Zeta.ThetaTailSquared
open Cvs.ZeroFree

/-- The exact modulus of a theta term on the imaginary axis. -/
theorem norm_theta_term (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖Complex.exp ((Real.pi : ℂ) * I * (((m : ℂ) + 1)) ^ 2 * (I * (t : ℂ)))‖
      = Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * t)) := by
  have hz : (Real.pi : ℂ) * I * (((m : ℂ) + 1)) ^ 2 * (I * (t : ℂ))
      = ((-(Real.pi * ((m : ℝ) + 1) ^ 2 * t) : ℝ) : ℂ) := by
    have : (Real.pi : ℂ) * I * (((m : ℂ) + 1)) ^ 2 * (I * (t : ℂ))
        = (Real.pi : ℂ) * ((m : ℂ) + 1) ^ 2 * (t : ℂ) * (I * I) := by ring
    rw [this, Complex.I_mul_I]
    push_cast
    ring
  rw [hz, Complex.norm_exp, Complex.ofReal_re]

/-- Past the first term the square beats a geometric ratio `e^{−2πt}`. -/
theorem theta_term_le_geom (m : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-(Real.pi * ((m : ℝ) + 2) ^ 2 * t))
      ≤ Real.exp (-(2 * Real.pi * t)) ^ (m + 2) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have htp : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hcast : (((m + 2 : ℕ)) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hsq : 2 * ((m : ℝ) + 2) ≤ ((m : ℝ) + 2) ^ 2 := by nlinarith
  have hpt : (0:ℝ) < Real.pi * t := mul_pos hpi htp
  nlinarith [hsq, hpt]

/-- Summability of the squared-exponent tail, by comparison with the linear one. -/
theorem summable_theta_terms {t : ℝ} (ht : 1 ≤ t) :
    Summable fun n : ℕ => Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * t)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have htp : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hr : Real.exp (-(Real.pi * t)) < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_; nlinarith
  have hgeom : Summable fun n : ℕ => Real.exp (-(Real.pi * t)) ^ (n + 1) := by
    simpa [pow_succ'] using
      (summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left (Real.exp (-(Real.pi * t)))
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hgeom
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hm : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hpt : (0:ℝ) < Real.pi * t := mul_pos hpi htp
  nlinarith [hsq, hpt]

/-- **The tail, with the square kept.**  The first term, plus a geometric remainder at
ratio `e^{−2πt}`. -/
theorem theta_tail_le {t : ℝ} (ht : 1 ≤ t) :
    ∑' n : ℕ, Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * t))
      ≤ Real.exp (-(Real.pi * t))
        + Real.exp (-(2 * Real.pi * t)) ^ 2 / (1 - Real.exp (-(2 * Real.pi * t))) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have htp : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hr : Real.exp (-(2 * Real.pi * t)) < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_; nlinarith
  have hr0 : (0:ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hsum := summable_theta_terms ht
  rw [hsum.tsum_eq_zero_add]
  have hzero : Real.exp (-(Real.pi * (((0 : ℕ) : ℝ) + 1) ^ 2 * t))
      = Real.exp (-(Real.pi * t)) := by norm_num
  rw [hzero]
  refine add_le_add le_rfl ?_
  have hshift : ∀ n : ℕ, Real.exp (-(Real.pi * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * t))
      = Real.exp (-(Real.pi * ((n : ℝ) + 2) ^ 2 * t)) := by
    intro n; congr 2; push_cast; ring
  simp only [hshift]
  have hgeom : Summable fun n : ℕ => Real.exp (-(2 * Real.pi * t)) ^ (n + 2) := by
    have hg := (summable_geometric_of_lt_one hr0 hr).mul_left
      (Real.exp (-(2 * Real.pi * t)) ^ 2)
    refine hg.congr fun n => ?_
    rw [pow_add]; ring
  have hcmp : Summable fun n : ℕ => Real.exp (-(Real.pi * ((n : ℝ) + 2) ^ 2 * t)) :=
    Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le)
      (fun n => theta_term_le_geom n ht) hgeom
  refine (hcmp.tsum_le_tsum (fun n => theta_term_le_geom n ht) hgeom).trans (le_of_eq ?_)
  have hsplit : ∑' n : ℕ, Real.exp (-(2 * Real.pi * t)) ^ (n + 2)
      = Real.exp (-(2 * Real.pi * t)) ^ 2 * ∑' n : ℕ, Real.exp (-(2 * Real.pi * t)) ^ n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by rw [pow_add]; ring
  rw [hsplit, tsum_geometric_of_lt_one hr0 hr]
  ring

/-- **The kernel bound with the square kept**: prefactor `2.0002`. -/
theorem abs_evenKernel_sub_one_le_sq {t : ℝ} (ht : 1 ≤ t) :
    |HurwitzZeta.evenKernel 0 t - 1| ≤ 2.0002 * Real.exp (-(Real.pi * t)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have htp : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have him : (0 : ℝ) < (I * (t : ℂ)).im := by simpa using htp
  have hnorm : ‖jacobiTheta (I * (t : ℂ)) - 1‖ = |HurwitzZeta.evenKernel 0 t - 1| := by
    rw [← evenKernel_zero_eq_jacobiTheta t]
    rw [show ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1
        = ((HurwitzZeta.evenKernel 0 t - 1 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.norm_real _
  rw [← hnorm, sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat him)]
  rw [norm_mul, Complex.norm_two]
  have hnormterm : ∀ n : ℕ,
      ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + 1) ^ 2 * (I * (t:ℂ)))‖
        = Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * t)) := fun n => norm_theta_term n htp
  have hsum := summable_theta_terms ht
  have hsn : Summable fun n : ℕ =>
      ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + 1) ^ 2 * (I * (t:ℂ)))‖ :=
    hsum.congr fun n => (hnormterm n).symm
  have hle : ‖∑' n : ℕ, cexp ((Real.pi : ℂ) * I * ((n : ℂ) + 1) ^ 2 * (I * (t:ℂ)))‖
      ≤ ∑' n : ℕ, Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * t)) := by
    refine (norm_tsum_le_tsum_norm hsn).trans (le_of_eq ?_)
    exact tsum_congr hnormterm
  refine (mul_le_mul_of_nonneg_left (hle.trans (theta_tail_le ht)) (by norm_num)).trans ?_
  -- the remainder, in the single variable `E = e^{-pi t}`
  set E : ℝ := Real.exp (-(Real.pi * t)) with hEdef
  have hEpos : (0:ℝ) < E := Real.exp_pos _
  have hF : E ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [hEdef, sq, ← Real.exp_add]; congr 1; ring
  have hE := Cvs.Zeta.KernelPrefactorBound.exp_pi_gt_2314
  have hepos : (0:ℝ) < Real.exp Real.pi := Real.exp_pos _
  have hEsmall : E ≤ Real.exp (-Real.pi) := by
    rw [hEdef]; refine Real.exp_le_exp.mpr ?_; nlinarith [Real.pi_pos]
  have hEle : E < 1 / 23.14 := by
    have hinv : Real.exp (-Real.pi) < 1 / 23.14 := by
      rw [Real.exp_neg, inv_lt_comm₀ hepos (by norm_num)]
      linarith
    linarith
  have hden : (0:ℝ) < 1 - Real.exp (-(2 * Real.pi * t)) := by
    rw [← hF]; nlinarith [hEpos, hEle]
  have hrem : Real.exp (-(2 * Real.pi * t)) ^ 2 / (1 - Real.exp (-(2 * Real.pi * t)))
      ≤ 0.0001 * E := by
    rw [div_le_iff₀ hden, ← hF]
    nlinarith [hEpos, hEle, sq_nonneg E, pow_pos hEpos 3]
  linarith

theorem abs_cosKernel_sub_one_le_sq {t : ℝ} (ht : 1 ≤ t) :
    |HurwitzZeta.cosKernel 0 t - 1| ≤ 2.0002 * Real.exp (-(Real.pi * t)) := by
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  exact abs_evenKernel_sub_one_le_sq ht

/-- **`‖Λ₀‖ ≤ 2.0002·e^{−π}/π`** on `−1 ≤ Re s ≤ 2`. -/
theorem norm_completedRiemannZeta₀_le_sq {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ ≤ 2.0002 * (Real.exp (-Real.pi) / Real.pi) := by
  rw [completedRiemannZeta₀_eq_Lambda0, Lambda0_zeta_eq_tails, norm_div]
  have hre : (s / 2).re = s.re / 2 := by simp
  have he1 : (s / 2 - 1).re ≤ 0 := by
    rw [Complex.sub_re, hre]; simp; linarith
  have he2 : ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1).re ≤ 0 := by
    rw [Complex.sub_re, Complex.sub_re, hre]; simp; linarith
  have hA := Cvs.ZeroFree.norm_kernel_tail_le_pi he1 2.0002 (by norm_num)
    (HurwitzZeta.evenKernel 0) (fun t ht => abs_evenKernel_sub_one_le_sq ht)
  have hB := Cvs.ZeroFree.norm_kernel_tail_le_pi he2 2.0002 (by norm_num)
    (HurwitzZeta.cosKernel 0) (fun t ht => abs_cosKernel_sub_one_le_sq ht)
  have hsum := le_trans (norm_add_le
      (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ (s / 2 - 1)
        • (((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1))
      (∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ ((((1:ℝ)/2 : ℝ) : ℂ) - s / 2 - 1)
        • (((HurwitzZeta.cosKernel 0 t : ℝ) : ℂ) - 1))) (add_le_add hA hB)
  rw [show ‖(2:ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

theorem const_lt_sq : 2.0002 * (Real.exp (-Real.pi) / Real.pi) < 1 / 36.3 := by
  have hE := Cvs.Zeta.KernelPrefactorBound.exp_pi_gt_2314
  have hepos : (0:ℝ) < Real.exp Real.pi := Real.exp_pos _
  have hinv : Real.exp (-Real.pi) < 1 / 23.14 := by
    rw [Real.exp_neg, inv_lt_comm₀ hepos (by norm_num)]
    linarith
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have h314 : (3.141592:ℝ) < Real.pi := Real.pi_gt_d6
  have hE0 : (0:ℝ) < Real.exp (-Real.pi) := Real.exp_pos _
  have hkey : 72.6073 * Real.exp (-Real.pi) < Real.pi := by nlinarith
  rw [mul_div_assoc', div_lt_iff₀ hpipos]
  linarith

end Cvs.Zeta.ThetaTailSquared
