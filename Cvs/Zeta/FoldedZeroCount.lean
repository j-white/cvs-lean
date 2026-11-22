import Mathlib
import Cvs.Zeta.FiniteRectangleFold
import Cvs.Zeta.RectWinding
import Cvs.Zeta.RectangleQuarterReduction
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiJointHeight
import Cvs.Zeta.XiStrip

/-!
# The folded count with everything discharged, and the horizontal bounded

`Cvs.Zeta.RectangleQuarterReduction` proved `π·N(T') = Re V − Im H` unconditionally, and halved `Im H` onto `Re ∈ [½,2]`
*given* interval integrability.
-/

noncomputable section

open Complex Cvs.Zeta

namespace Cvs.Zeta.FoldedZeroCount
open Cvs.ZeroCounting

/-- `ξ` has no zero on the horizontal `Im = T'`, given that `ζ` has none on the segment.
Inside the strip that is the hypothesis; outside it, every zero of `ξ` has `0 < Re < 1`. -/
theorem riemannXi_ne_zero_horiz {T' : ℝ} (hT' : T' ≠ 0)
    (hζ : ∀ x ∈ Set.uIcc (-1 : ℝ) 2, riemannZeta ((x : ℂ) + (T' : ℂ) * I) ≠ 0) (x : ℝ) :
    riemannXi ((x : ℂ) + (T' : ℂ) * I) ≠ 0 := by
  intro h0
  obtain ⟨hr1, hr2⟩ := riemannXi_zero_mem_strip h0
  have hre : (((x : ℂ) + (T' : ℂ) * I)).re = x := by simp
  rw [hre] at hr1 hr2
  have hmem : x ∈ Set.uIcc (-1 : ℝ) 2 := by
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
    exact ⟨by linarith, by linarith⟩
  have hs1 : ((x : ℂ) + (T' : ℂ) * I) ≠ 1 := by
    intro hc
    have : (((x : ℂ) + (T' : ℂ) * I)).im = T' := by simp
    rw [hc] at this
    simp at this
    exact hT' this.symm
  exact hζ x hmem ((riemannXi_eq_zero_iff_riemannZeta (by rw [hre]; exact hr1) hs1).mp h0)

/-- `ξ'/ξ` is continuous along a horizontal free of zeros of `ξ`. -/
theorem continuous_logDeriv_horiz {T' : ℝ}
    (h : ∀ x : ℝ, riemannXi ((x : ℂ) + (T' : ℂ) * I) ≠ 0) :
    Continuous fun x : ℝ => logDeriv riemannXi ((x : ℂ) + (T' : ℂ) * I) := by
  have hderiv : Continuous (deriv riemannXi) :=
    continuous_iff_continuousAt.mpr fun z =>
      ((analyticOnNhd_riemannXi.deriv) z (Set.mem_univ z)).continuousAt
  have hpath : Continuous fun x : ℝ => ((x : ℂ) + (T' : ℂ) * I) := by fun_prop
  simp only [logDeriv_apply]
  exact (hderiv.comp hpath).div ((differentiable_riemannXi.continuous).comp hpath) h

/-- The folding of `Cvs.Zeta.RectangleQuarterReduction`, stated over an arbitrary admissible height rather than one minted
inside the proof, so a caller can supply a height carrying extra properties. -/
theorem folded_of_rect {T' : ℝ} {S : Finset ℂ} {m : ℂ → ℕ}
    (h5 : 2 * (Real.pi : ℂ) * I * (∑ ρ ∈ S, (m ρ : ℂ))
      = rectBoundaryIntegral (fun u => logDeriv riemannXi u)
          (-1 - (T' : ℂ) * I) (2 + (T' : ℂ) * I)) :
    Real.pi * (∑ ρ ∈ S, (m ρ : ℝ))
      = (∫ y in (-T')..T', logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)).re
        - (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T' : ℂ) * I)).im := by
  set H : ℂ := ∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T' : ℂ) * I) with hH
  set V : ℂ := ∫ y in (-T')..T', logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I) with hV
  rw [rectBoundaryIntegral] at h5
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.one_re, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.neg_re, Complex.neg_im] at h5
  norm_num at h5
  have hbot : (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + -((T' : ℂ) * I))) = -H := by
    rw [hH, ← Cvs.Zeta.RectangleQuarterReduction.bottom_eq_neg_top T']
    exact intervalIntegral.integral_congr (fun x _ => by ring_nf)
  have hleft : (∫ y in (-T')..T', logDeriv riemannXi ((-1 : ℂ) + (y : ℂ) * I)) = -V :=
    Cvs.ZeroCounting.integral_vline_left_eq_neg_finite T'
  have hHre : H.re = 0 := Cvs.Zeta.RectangleQuarterReduction.re_top_eq_zero T'
  have hVim : V.im = 0 := Cvs.Zeta.RectangleQuarterReduction.im_vertical_eq_zero T'
  have hHeq : H = (H.im : ℂ) * I := by
    apply Complex.ext <;> simp [hHre]
  have hVeq : V = (V.re : ℂ) := by
    apply Complex.ext <;> simp [hVim]
  rw [hbot, hleft] at h5
  have hkey : (2 * I) * ((Real.pi : ℂ) * ∑ ρ ∈ S, ((m ρ : ℕ) : ℂ))
      = (2 * I) * (((V.re : ℝ) : ℂ) - ((H.im : ℝ) : ℂ)) := by
    linear_combination h5 - 2 * hHeq + 2 * I * hVeq
  have h2I : (2 * I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  have hre := congrArg Complex.re (mul_left_cancel₀ h2I hkey)
  simpa [Complex.re_sum] using hre

/-- **Riemann–von Mangoldt with the main term isolated.** |π·N(T') − Re ∫_{-T'}^{T'} ξ'/ξ(2+iy)
dy| ≤ C·(1 + log T)² for an admissible height `T' ∈ [T, T+1]`, with `N(T')` the zero count of
`ξ` below `T'` with multiplicity. -/
theorem exists_zero_count_main_term :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 20 ≤ T →
      ∃ (T' : ℝ) (S : Finset ℂ) (m : ℂ → ℕ),
        T ≤ T' ∧ T' ≤ T + 1 ∧
        (∀ u : ℂ, u ∈ S ↔ (riemannXi u = 0 ∧ |u.im| < T')) ∧
        (∀ u : ℂ, (m u : ℤ) = MeromorphicOn.divisor riemannXi Set.univ u) ∧
        |Real.pi * (∑ ρ ∈ S, (m ρ : ℝ))
            - (∫ y in (-T')..T', logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)).re|
          ≤ C * (1 + Real.log |T|) ^ 2 := by
  obtain ⟨K, hK0, hJ⟩ := exists_joint_height 6 (by norm_num) (by norm_num) 13 (by norm_num)
    (by norm_num) (φ := fun _ => (1 : ℂ)) (differentiable_const 1)
  refine ⟨3 * K, by positivity, fun T hT => ?_⟩
  obtain ⟨T', S, m, h1, h2, hS1, hS2, hS3, hm, hζline, hbound, hrect⟩ := hJ T (by norm_num; linarith)
  have hT'0 : T' ≠ 0 := by intro hc; rw [hc] at h1; linarith
  -- the horizontal is zero-free, so the integrand is continuous, hence integrable
  have hxi := riemannXi_ne_zero_horiz hT'0 hζline
  have hcont := continuous_logDeriv_horiz hxi
  -- fold
  have hfold := folded_of_rect (T' := T') (S := S) (m := m) (by
    simpa only [mul_one] using hrect.symm)
  -- halve, and bound the half
  have hhalf := Cvs.Zeta.RectangleQuarterReduction.im_top_eq_two_im_half T'
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hnorm : ‖∫ x in (1/2 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T' : ℂ) * I)‖
      ≤ (K * (1 + Real.log |T|) ^ 2) * |(2 : ℝ) - 1/2| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
    refine hbound ((x : ℂ) + (T' : ℂ) * I) ?_ (by simp) ?_
    · have : ((x : ℂ) + (T' : ℂ) * I) - (2 + (T' : ℂ) * I) = ((x - 2 : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> [linarith [hx.1]; linarith [hx.2]]
    · exact hζline x (by
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)]
        exact ⟨by linarith [hx.1], hx.2⟩)
  refine ⟨T', S, m, h1, h2, fun u => ⟨fun hu => ⟨hS1 u hu, ?_⟩, fun hu => hS3 u hu.1 hu.2⟩, hm, ?_⟩
  · obtain ⟨-, -, hl, hr⟩ := hS2 u hu
    exact abs_lt.mpr ⟨hl, hr⟩
  · rw [hfold]
    have him : |(∫ x in (1/2 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T' : ℂ) * I)).im|
        ≤ K * (1 + Real.log |T|) ^ 2 * (3/2) := by
      refine le_trans (Complex.abs_im_le_norm _) ?_
      calc _ ≤ (K * (1 + Real.log |T|) ^ 2) * |(2 : ℝ) - 1/2| := hnorm
        _ = K * (1 + Real.log |T|) ^ 2 * (3/2) := by norm_num
    rw [show (∫ y in (-T')..T', logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)).re
          - (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T' : ℂ) * I)).im
          - (∫ y in (-T')..T', logDeriv riemannXi ((2 : ℂ) + (y : ℂ) * I)).re
        = - (∫ x in (-1 : ℝ)..2, logDeriv riemannXi ((x : ℂ) + (T' : ℂ) * I)).im from by ring,
      abs_neg, hhalf, abs_mul]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [him]

end Cvs.Zeta.FoldedZeroCount
