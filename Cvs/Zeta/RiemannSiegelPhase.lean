import Mathlib
import Cvs.Zeta.ExplicitFormula.ArchimedeanIntegrand
import Cvs.Zeta.GammaRLogDeriv
import Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound

/-!
# The two archimedean scores are one function, and it is the Riemann–Siegel phase

The repository carries `archScore` twice, defined differently and used in different arcs:
-/

open Complex

namespace Cvs.ArchScore

theorem log_pi_re : (Complex.log ((Real.pi : ℝ) : ℂ)).re = Real.log Real.pi := by
  rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem digamma_arg_eq (u : ℝ) :
    ((1 : ℂ) / 2 + I * u) / 2 = (1 / 4 : ℂ) + (u : ℂ) / 2 * I := by
  ring

/-- **The two archimedean scores are one function.**  `ArchimedeanIntegrand` defines it as the real part of
`logDeriv Γ_ℝ` on the critical line; `Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound` defines it as `-½log π + ½Re ψ(¼ + iu/2)`.  They
agree, by `Cvs.Zeta.logDeriv_gammaR`. -/
theorem archScore_eq (u : ℝ) : Cvs.Detection.archScore u = Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore u := by
  rw [Cvs.Detection.archScore, Cvs.Zeta.logDeriv_gammaR (Cvs.Detection.half_add_I_ne_neg_nat u),
    digamma_arg_eq, Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore]
  simp only [Complex.add_re, Complex.div_re, Complex.neg_re, Complex.neg_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat, log_pi_re]
  ring

end Cvs.ArchScore
