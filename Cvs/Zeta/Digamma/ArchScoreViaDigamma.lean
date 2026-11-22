import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Complex Real

namespace Cvs.Digamma

/-!
# The archimedean score, in Mathlib's digamma

The venue writes its archimedean score as `Re (logDeriv Γ_ℝ (1/2 + iu))`
(`Cvs.Zeta.Explicit.Venue.archimedeanPairing_eq_logDerGammaR`), and Mathlib has `Complex.digamma =
logDeriv Gamma`.
-/

/-- **The bridge.** -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Real.log π) / 2 + Complex.digamma (s / 2) / 2 := by
  have hπ : ((π : ℂ)) ≠ 0 := by simp
  have hhalf : 0 < (s / 2).re := by
    simp only [Complex.div_re]
    norm_num
    positivity
  have hnm : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hcon
    rw [hcon] at hhalf
    simp at hhalf
    linarith [hhalf]
  have hG : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hhalf
  have hcp : ((π : ℂ)) ^ (-s / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, hπ]
  have hnegdiv : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s :=
    (differentiableAt_id.neg).div_const 2
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => ((π : ℂ)) ^ (-z / 2)) s :=
    hnegdiv.const_cpow (Or.inl hπ)
  -- the Gamma factor, through `HasDerivAt` rather than `logDeriv_comp`
  have hhalfD : HasDerivAt (fun z : ℂ => z / 2) (1 / 2 : ℂ) s :=
    (hasDerivAt_id s).div_const 2
  have hGD : HasDerivAt Complex.Gamma (deriv Complex.Gamma (s / 2)) (s / 2) :=
    (Complex.differentiableAt_Gamma _ hnm).hasDerivAt
  have hcompD : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := hGD.comp s hhalfD
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    hcompD.differentiableAt
  have hfun : Complex.Gammaℝ = fun z : ℂ => ((π : ℂ)) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z
    exact Complex.Gammaℝ_def z
  have hderiv1 : deriv (fun z : ℂ => -z / 2) s = -(1 / 2) := by
    have hD : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s :=
      ((hasDerivAt_id s).neg).div_const 2
    rw [hD.deriv]
    ring
  have hpow : logDeriv (fun z : ℂ => ((π : ℂ)) ^ (-z / 2)) s = -(Real.log π) / 2 := by
    rw [logDeriv_apply, Complex.deriv_const_cpow hnegdiv, hderiv1,
      Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have hgam : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s
      = Complex.digamma (s / 2) / 2 := by
    rw [logDeriv_apply, hcompD.deriv, Complex.digamma_def, logDeriv_apply]
    ring
  rw [hfun, ← hpow, ← hgam]
  exact logDeriv_mul (f := fun z : ℂ => ((π : ℂ)) ^ (-z / 2))
    (g := fun z : ℂ => Complex.Gamma (z / 2)) s hcp hG hd1 hd2

/-- **The venue's score, evaluated.** At the critical boundary `s = 1/2 + iu`, where
`Cvs.Zeta.Explicit.Venue.archimedeanPairing_eq_logDerGammaR` reads the archimedean weight, the
score is an explicit real expression in Mathlib's digamma. -/
theorem re_logDeriv_Gammaℝ_boundary (u : ℝ) :
    (logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (u : ℂ) * Complex.I)).re
      = -(Real.log π) / 2
        + (Complex.digamma ((1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I)).re / 2 := by
  have hre : (0 : ℝ) < ((1 / 2 : ℂ) + (u : ℂ) * Complex.I).re := by
    simp
  rw [logDeriv_Gammaℝ hre]
  have harg : ((1 / 2 : ℂ) + (u : ℂ) * Complex.I) / 2
      = (1 / 4 : ℂ) + (u : ℂ) / 2 * Complex.I := by ring
  rw [harg]
  simp [Complex.add_re]

/-!
## The shift, in real form

Any estimate of `Re digamma` on a vertical line begins by shifting right, since Mathlib
carries no asymptotics near the imaginary axis.
-/

end Cvs.Digamma
