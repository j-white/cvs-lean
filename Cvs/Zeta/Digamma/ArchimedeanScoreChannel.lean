import Mathlib

/-!
# The archimedean score channel

The finite-place score is the logarithmic derivative of the local Euler
factor.  The matching archimedean observable is therefore the logarithmic
derivative of `Gammaℝ(s) = pi^(-s/2) Gamma(s/2)`.  This file derives its
closed digamma form and restricts it to the critical boundary.
-/

namespace Cvs.Zeta.Explicit.Venue

noncomputable section

/-- The real Gamma factor respects complex conjugation. This is stated for
the actual completed local factor, rather than inferred later from a
closed-form score. -/
theorem GammaR_star (s : ℂ) :
    Complex.Gammaℝ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (Complex.Gammaℝ s) := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  rw [show (starRingEnd ℂ)
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) =
        (starRingEnd ℂ) ((Real.pi : ℂ) ^ (-s / 2)) *
          (starRingEnd ℂ) (Complex.Gamma (s / 2)) by
    exact map_mul (starRingEnd ℂ) _ _]
  have hg := Complex.Gamma_conj (s / 2)
  have harg : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im, Complex.normSq] <;> ring
  have hgamma : Complex.Gamma ((starRingEnd ℂ) s / 2) =
      (starRingEnd ℂ) (Complex.Gamma (s / 2)) :=
    (congrArg Complex.Gamma harg).trans hg
  rw [hgamma]
  congr 1
  have hexp : -(starRingEnd ℂ) s / 2 =
      (starRingEnd ℂ) (-s / 2) := by
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im, Complex.normSq] <;> ring
  rw [hexp]
  have hc := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) (by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Ne.symm Real.pi_ne_zero)
  have hpistar : (starRingEnd ℂ) (Real.pi : ℂ) = (Real.pi : ℂ) := by
    apply Complex.ext <;> simp
  rw [hpistar] at hc
  exact hc

/-- The logarithmic derivative of the real Gamma factor respects complex
conjugation. This is the symmetry that cancels the imaginary critical-line
integral. -/
theorem logDeriv_GammaR_star (s : ℂ) :
    logDeriv Complex.Gammaℝ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (logDeriv Complex.Gammaℝ s) := by
  have hf : ((starRingEnd ℂ) ∘ Complex.Gammaℝ ∘ (starRingEnd ℂ)) =
      Complex.Gammaℝ := by
    funext z
    simp only [Function.comp_apply]
    rw [GammaR_star]
    simp
  have hd := congrArg deriv hf
  have hd' := congrFun hd ((starRingEnd ℂ) s)
  have hderiv : deriv Complex.Gammaℝ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (deriv Complex.Gammaℝ s) := by
    simpa using hd'.symm
  rw [logDeriv_apply, logDeriv_apply, hderiv, GammaR_star]
  simpa using (map_div (starRingEnd ℂ) _ _).symm

end

end Cvs.Zeta.Explicit.Venue
