import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.RectArgument
import Cvs.Zeta.RectWinding
import Cvs.Zeta.XiZetaBridge

/-!
# Moving the archimedean channel from `Re = 2` to the critical line
-/

noncomputable section

open Complex MeasureTheory Cvs.Zeta Set

namespace Cvs.ZeroCounting

/-- The open right half-plane. -/
def RHP : Set ℂ := {s : ℂ | 0 < s.re}

theorem isOpen_RHP : IsOpen RHP := isOpen_lt continuous_const Complex.continuous_re

/-- `Γ_ℝ` is analytic on `Re > 0`: differentiable there, and the half-plane is open. -/
theorem analyticOnNhd_gammaR : AnalyticOnNhd ℂ Gammaℝ RHP := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_RHP
  exact (differentiableAt_gammaR (Gammaℝ_ne_zero_of_re_pos hs)).differentiableWithinAt

/-- `Γ_ℝ'/Γ_ℝ` is differentiable on `Re > 0`. -/
theorem differentiableAt_logDeriv_gammaR {s : ℂ} (hs : s ∈ RHP) :
    DifferentiableAt ℂ (logDeriv Gammaℝ) s := by
  have hd : DifferentiableAt ℂ (deriv Gammaℝ) s :=
    ((analyticOnNhd_gammaR.deriv) s hs).differentiableAt
  have hg : DifferentiableAt ℂ Gammaℝ s := (analyticOnNhd_gammaR s hs).differentiableAt
  simp only [logDeriv]
  exact hd.div hg (Gammaℝ_ne_zero_of_re_pos hs)

/-- `Γ_ℝ'/Γ_ℝ` is continuous on `Re > 0`. -/
theorem continuousOn_logDeriv_gammaR : ContinuousOn (logDeriv Gammaℝ) RHP :=
  fun s hs => (differentiableAt_logDeriv_gammaR hs).continuousAt.continuousWithinAt

/-- The rectangle `[½,2] × [0,T]` sits in the right half-plane. -/
theorem closedRect_subset_RHP {T : ℝ} (hT : 0 ≤ T) :
    closedRect ((1/2 : ℂ)) ((2 : ℂ) + (T : ℂ) * I) ⊆ RHP := by
  rintro s ⟨hre, -⟩
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat] at hre
  norm_num at hre
  show (0:ℝ) < s.re
  linarith [hre.1]

/-- **Cauchy–Goursat for the archimedean channel** on `[½,2] × [0,T]`. -/
theorem rect_gammaR_eq_zero {T : ℝ} (hT : 0 ≤ T) :
    rectBoundaryIntegral (logDeriv Gammaℝ) ((1/2 : ℂ)) ((2 : ℂ) + (T : ℂ) * I) = 0 := by
  refine rectBoundaryIntegral_eq_zero
    (continuousOn_logDeriv_gammaR.mono (closedRect_subset_RHP hT)) (fun s hs => ?_)
  refine differentiableAt_logDeriv_gammaR ?_
  obtain ⟨hre, -⟩ := hs
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat] at hre
  norm_num at hre
  show (0:ℝ) < s.re
  linarith [hre.1]

/-- **The shift.**  Taking the *imaginary* part of `∮ = 0` converts the two vertical
`Re`-integrals into the two horizontal `Im`-integrals, because the verticals carry a factor
`i` and `Im(i·z) = Re z`.  The `x`-axis term is `T`-independent. -/
theorem re_vertical_shift {T : ℝ} (hT : 0 ≤ T) :
    (∫ y in (0 : ℝ)..T, logDeriv Gammaℝ ((2 : ℂ) + (y : ℂ) * I)).re
        - (∫ y in (0 : ℝ)..T, logDeriv Gammaℝ (((1/2 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = (∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ) + (T : ℂ) * I)).im
        - (∫ x in (1/2 : ℝ)..2, logDeriv Gammaℝ ((x : ℂ))).im := by
  have h := rect_gammaR_eq_zero hT
  rw [rectBoundaryIntegral] at h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.div_re, Complex.div_im,
    Complex.one_re, Complex.one_im, Complex.normSq_ofNat] at h
  norm_num at h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.zero_im] at him
  simp only [zero_mul, one_mul, zero_add] at him
  push_cast at him ⊢
  linarith [him]

end Cvs.ZeroCounting
