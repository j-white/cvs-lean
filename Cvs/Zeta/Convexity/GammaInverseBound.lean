import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Convexity.CompletedZetaStripBound

/-!
# `ζ` is bounded on the critical strip, so the growth hypothesis is discharged

`CompletedZetaStripBound` reduced the last obstruction to an upper bound on `1/‖Γ_ℝ‖`.
-/

open Complex MeasureTheory Set

namespace Cvs.ZetaGrowth

/-- **`‖Γ(s)‖ ≤ Γ(Re s)`** on the right half plane: the integral representation, with the
triangle inequality, and `‖x^{s-1}‖ = x^{σ-1}` for real `x > 0`. -/
theorem norm_Gamma_le {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp [Complex.norm_exp]

/-- **`‖sin z‖ ≤ e^{|Im z|}`.** -/
theorem norm_sin_le (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  have hb1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have hb2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  have hstep : ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one]
    simp only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
  rw [h1, h2] at hstep
  linarith

/-- **`‖1/Γ(z)‖ ≤ Γ(1 - Re z)·e^{π|Im z|}/π`** off the real axis. -/
theorem norm_inv_Gamma_le {z : ℂ} (hz : z.re < 1) (him : z.im ≠ 0) :
    ‖(Complex.Gamma z)⁻¹‖ ≤ Real.Gamma (1 - z.re) * Real.exp (Real.pi * |z.im|) / Real.pi := by
  have hnm : ∀ m : ℕ, z ≠ -m := by
    intro m hc
    apply him
    rw [hc]; simp
  have hΓz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hnm
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hsin : Complex.sin (Real.pi * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hc
    apply him
    have : (Real.pi : ℂ) * z = k * Real.pi := hc
    have him2 : ((Real.pi : ℂ) * z).im = 0 := by rw [this]; simp
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at him2
    exact (mul_eq_zero.mp him2).resolve_left (ne_of_gt Real.pi_pos)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hmul : Complex.Gamma z
      * (Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / Real.pi) = 1 := by
    rw [← mul_div_assoc, ← mul_assoc, hrefl]
    field_simp
  have hkey : (Complex.Gamma z)⁻¹
      = Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / Real.pi :=
    inv_eq_of_mul_eq_one_right hmul
  rw [hkey, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hre : (1 - z).re = 1 - z.re := by simp
  have hG : ‖Complex.Gamma (1 - z)‖ ≤ Real.Gamma (1 - z.re) := by
    have := norm_Gamma_le (s := 1 - z) (by rw [hre]; linarith)
    rwa [hre] at this
  have hS : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
    refine le_trans (norm_sin_le _) (Real.exp_le_exp.mpr ?_)
    have hh : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
    rw [hh, abs_mul, abs_of_pos Real.pi_pos]
  have hnum : ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin ((Real.pi : ℂ) * z)‖
      ≤ Real.Gamma (1 - z.re) * Real.exp (Real.pi * |z.im|) :=
    mul_le_mul hG hS (norm_nonneg _) (le_trans (norm_nonneg _) hG)
  exact div_le_div_of_nonneg_right hnum Real.pi_pos.le

/-- **`Γ` is bounded on `[a,b] ⊂ (0,∞)` by the sum of its endpoint values.**  The same split at
`t = 1` as `CompletedZetaStripBound.rpow_le_edges`, now inside the `Γ` integral.  This is what makes the strip
bound uniform in `σ` as well as in the height. -/
theorem Gamma_le_edges {a b x : ℝ} (ha : 0 < a) (h1 : a ≤ x) (h2 : x ≤ b) :
    Real.Gamma x ≤ Real.Gamma a + Real.Gamma b := by
  have hx : 0 < x := lt_of_lt_of_le ha h1
  have hb : 0 < b := lt_of_lt_of_le hx h2
  have hIa := Real.GammaIntegral_convergent ha
  have hIb := Real.GammaIntegral_convergent hb
  rw [Real.Gamma_eq_integral hx, Real.Gamma_eq_integral ha, Real.Gamma_eq_integral hb,
    ← MeasureTheory.integral_add hIa hIb]
  refine setIntegral_mono_on (Real.GammaIntegral_convergent hx) (hIa.add hIb)
    measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  have hle := Cvs.ZetaGrowth.rpow_le_edges ht0 h1 h2
  have hexp : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  nlinarith

/-- **The reciprocal of `Γ_ℝ` on a vertical line**, with an exponential bound in the height.
`Γ_ℝ(s) = π^{-s/2}·Γ(s/2)`, and `‖π^{-s/2}‖ = π^{-σ/2}` because `π > 0`. -/
theorem norm_inv_Gammaℝ_le {s : ℂ} (hs : s.re < 2) (him : s.im ≠ 0) :
    ‖(Gammaℝ s)⁻¹‖
      ≤ Real.pi ^ (s.re / 2) * (Real.Gamma (1 - s.re / 2)
          * Real.exp (Real.pi * |s.im| / 2) / Real.pi) := by
  have hre : (s / 2).re = s.re / 2 := by simp
  have hima : (s / 2).im = s.im / 2 := by simp
  have hz : (s / 2).re < 1 := by rw [hre]; linarith
  have hz2 : (s / 2).im ≠ 0 := by rw [hima]; exact div_ne_zero him (by norm_num)
  have hg := norm_inv_Gamma_le hz hz2
  rw [hre, hima] at hg
  have hpow : ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ = Real.pi ^ (s.re / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre2 : (-s / 2).re = -(s.re / 2) := by simp; ring
    rw [hre2, Real.rpow_neg Real.pi_pos.le, inv_inv]
  have habs : |s.im / 2| = |s.im| / 2 := by
    rw [abs_div]; simp
  rw [Gammaℝ_def, mul_inv, norm_mul, hpow]
  rw [habs] at hg
  have hmul : Real.pi * (|s.im| / 2) = Real.pi * |s.im| / 2 := by ring
  rw [hmul] at hg
  exact mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg Real.pi_pos.le _)

/-- **`ζ` is bounded on the critical strip by `C·e^{π|t|/2}`, unconditionally.** `ζ = (Λ₀ - 1/s -
1/(1-s))·Γ_ℝ⁻¹`. -/
theorem norm_zeta_strip_le {s : ℂ} (h1 : -1/2 ≤ s.re) (h2 : s.re ≤ 3/2) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖
      ≤ (Cvs.ZetaGrowth.zetaStripConst / 2 + 2)
        * (Real.pi ^ (3/4 : ℝ)
          * ((Real.Gamma (1/4) + Real.Gamma (5/4))
            * Real.exp (Real.pi * |s.im| / 2) / Real.pi)) := by
  have himne : s.im ≠ 0 := by
    intro hc; rw [hc] at him; simp at him; linarith
  have hs0 : s ≠ 0 := by
    intro hc; apply himne; rw [hc]; simp
  have hsim : (1 : ℝ) ≤ ‖s‖ := le_trans him (Complex.abs_im_le_norm s)
  have hsim' : (1 : ℝ) ≤ ‖1 - s‖ := by
    have hh : |(1 - s).im| = |s.im| := by simp
    exact le_trans him (hh ▸ Complex.abs_im_le_norm (1 - s))
  have heq : riemannZeta s
      = (completedRiemannZeta₀ s - 1/s - 1/(1-s)) * (Gammaℝ s)⁻¹ := by
    rw [riemannZeta_eq_completedRiemannZeta₀ hs0, Gammaℝ_def, div_eq_mul_inv]
  rw [heq, norm_mul]
  have hbr : ‖completedRiemannZeta₀ s - 1/s - 1/(1-s)‖
      ≤ Cvs.ZetaGrowth.zetaStripConst / 2 + 2 := by
    have hΛ := Cvs.ZetaGrowth.norm_completedRiemannZeta₀_le h1 h2
    have hA : ‖(1 : ℂ)/s‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]; exact hsim
    have hB : ‖(1 : ℂ)/(1-s)‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]; exact hsim'
    calc ‖completedRiemannZeta₀ s - 1/s - 1/(1-s)‖
        ≤ ‖completedRiemannZeta₀ s - 1/s‖ + ‖(1 : ℂ)/(1-s)‖ := norm_sub_le _ _
      _ ≤ (‖completedRiemannZeta₀ s‖ + ‖(1 : ℂ)/s‖) + ‖(1 : ℂ)/(1-s)‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ (Cvs.ZetaGrowth.zetaStripConst / 2 + 1) + 1 := by gcongr
      _ = Cvs.ZetaGrowth.zetaStripConst / 2 + 2 := by ring
  have hGam : ‖(Gammaℝ s)⁻¹‖
      ≤ Real.pi ^ (3/4 : ℝ)
        * ((Real.Gamma (1/4) + Real.Gamma (5/4))
          * Real.exp (Real.pi * |s.im| / 2) / Real.pi) := by
    refine le_trans (norm_inv_Gammaℝ_le (by linarith) himne) ?_
    have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hp : Real.pi ^ (s.re / 2) ≤ Real.pi ^ (3/4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpi1 (by linarith)
    have hG : Real.Gamma (1 - s.re / 2) ≤ Real.Gamma (1/4) + Real.Gamma (5/4) :=
      Gamma_le_edges (by norm_num) (by linarith) (by linarith)
    have hGnn : (0 : ℝ) ≤ Real.Gamma (1 - s.re / 2) :=
      le_of_lt (Real.Gamma_pos_of_pos (by linarith))
    gcongr
  exact mul_le_mul hbr hGam (norm_nonneg _) (le_trans (norm_nonneg _) hbr)

end Cvs.ZetaGrowth
