import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.GammaReflect
import Cvs.Zeta.MellinStrip

/-!
# An a-priori interior bound for `ζ` on a vertical strip

Phragmén–Lindelöf converts edge bounds into strip bounds, but only for functions already known
to grow no faster than `exp (B · exp (c |Im s|))` inside the strip.
-/

open MeasureTheory Set Complex Real

namespace Cvs.Zeta

/-- The entire part of the completed zeta function is bounded on every vertical strip, uniformly
in `Im s`. -/
theorem exists_norm_completedRiemannZeta₀_le_strip (a b : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖completedRiemannZeta₀ s‖ ≤ K := by
  set P := HurwitzZeta.hurwitzEvenFEPair 0 with hP
  set Ma : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (a / 2 - 1) * ‖P.f_modif x‖ with hMa
  set Mb : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (b / 2 - 1) * ‖P.f_modif x‖ with hMb
  refine ⟨(Ma + Mb) / 2, ?_, ?_⟩
  · have hna : 0 ≤ Ma := by
      rw [hMa]
      refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx
      positivity
    have hnb : 0 ≤ Mb := by
      rw [hMb]
      refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx
      positivity
    linarith
  · intro s ha hb
    have heq : completedRiemannZeta₀ s = P.Λ₀ (s / 2) / 2 := rfl
    have hre : (s / 2).re = s.re / 2 := by simp
    have h := norm_Λ₀_le_strip (a := a / 2) (b := b / 2) (s := s / 2) P
      (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [heq, norm_div, Complex.norm_ofNat]
    rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
    exact h

/-- **`ζ` grows at most exponentially on a vertical strip inside `(0,2)`.** This is the a-priori
interior bound that the Phragmén–Lindelöf principle requires and that Mathlib does not
otherwise supply. -/
theorem exists_norm_riemannZeta_le_exp {a b : ℝ} (hb : b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * Real.exp (π * |s.im| / 2) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_completedRiemannZeta₀_le_strip a b
  set G : ℝ := max (Real.Gamma (1 - b / 2)) (Real.Gamma (1 - a / 2)) with hG
  have hG0 : 0 ≤ G := le_max_of_le_left (Real.Gamma_nonneg_of_nonneg (by linarith))
  have hpi1 : (1 : ℝ) ≤ π := by linarith [Real.two_le_pi]
  refine ⟨(K + 2) * π ^ (b / 2) * G / π, by positivity, ?_⟩
  intro s ha' hb' him
  have hab : a ≤ b := le_trans ha' hb'
  have him0 : s.im ≠ 0 := by intro h; rw [h] at him; simp at him; linarith
  have hs0 : s ≠ 0 := fun h => him0 (by rw [h]; simp)
  have hsre : (s / 2).re = s.re / 2 := by simp
  have hsim : (s / 2).im = s.im / 2 := by simp
  -- the three factors
  have hnorm_s : (1 : ℝ) ≤ ‖s‖ := le_trans him (Complex.abs_im_le_norm s)
  have hnorm_1s : (1 : ℝ) ≤ ‖1 - s‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm (1 - s))
    simpa [abs_neg] using him
  have hN : ‖completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)‖ ≤ K + 2 := by
    have h1 : ‖(1 : ℂ) / s‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]; exact hnorm_s
    have h2 : ‖(1 : ℂ) / (1 - s)‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (by linarith)]; exact hnorm_1s
    have h3 := hK s ha' hb'
    calc ‖completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)‖
        ≤ ‖completedRiemannZeta₀ s - 1 / s‖ + ‖(1 : ℂ) / (1 - s)‖ := norm_sub_le _ _
      _ ≤ (‖completedRiemannZeta₀ s‖ + ‖(1 : ℂ) / s‖) + ‖(1 : ℂ) / (1 - s)‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ K + 2 := by linarith
  have hA : ‖(((π : ℂ)) ^ (-s / 2))⁻¹‖ ≤ π ^ (b / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-s / 2).re = -(s.re / 2) := by rw [neg_div]; simp
    rw [hre, Real.rpow_neg Real.pi_pos.le, inv_inv]
    exact Real.rpow_le_rpow_of_exponent_le hpi1 (by linarith)
  have hB : ‖(Complex.Gamma (s / 2))⁻¹‖ ≤ G * Real.exp (π * |s.im| / 2) / π := by
    refine (norm_inv_Gamma_le (by rw [hsim]; simpa using him0) (by rw [hsre]; linarith)).trans ?_
    rw [hsim, hsre]
    have hgle : Real.Gamma (1 - s.re / 2) ≤ G := by
      refine Real.convexOn_Gamma.le_max_of_mem_Icc (x := 1 - b / 2) (y := 1 - a / 2)
        (by simp; linarith) (by simp; linarith) ⟨by linarith, by linarith⟩
    have habs : |s.im / 2| = |s.im| / 2 := by rw [abs_div]; norm_num
    rw [habs]
    have : π * (|s.im| / 2) = π * |s.im| / 2 := by ring
    rw [this]
    gcongr
  -- assemble
  rw [riemannZeta_eq_completedRiemannZeta₀ hs0]
  have hsplit : (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s))
        / ((π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))
      = (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s))
        * (((π : ℂ)) ^ (-s / 2))⁻¹ * (Complex.Gamma (s / 2))⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc]
  rw [hsplit, norm_mul, norm_mul]
  have hA0 : (0 : ℝ) ≤ ‖(((π : ℂ)) ^ (-s / 2))⁻¹‖ := norm_nonneg _
  have hB0 : (0 : ℝ) ≤ ‖(Complex.Gamma (s / 2))⁻¹‖ := norm_nonneg _
  calc ‖completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)‖ * ‖(((π : ℂ)) ^ (-s / 2))⁻¹‖
        * ‖(Complex.Gamma (s / 2))⁻¹‖
      ≤ (K + 2) * π ^ (b / 2) * (G * Real.exp (π * |s.im| / 2) / π) := by
        gcongr
    _ = (K + 2) * π ^ (b / 2) * G / π * Real.exp (π * |s.im| / 2) := by
        field_simp

end Cvs.Zeta
