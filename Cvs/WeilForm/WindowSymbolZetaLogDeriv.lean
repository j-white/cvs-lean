import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window symbol is the log-derivative of `ζ / P_x` on the critical line

Away from the zeros, `archSymbol t = −2 Re (ζ'/ζ)(½ + it)`, and the effective symbol
`effSymbol P R t` is `−2 Re` of the log-derivative of `ζ` divided by the Euler product truncated
at the prime powers `p^r`, `p ≤ P`, `r ≤ R`.
-/

namespace Cvs.WeilForm.WindowSymbolZetaLogDeriv

open Real
open Complex (I)

/-! ### Conjugation and the functional equation -/

theorem completedZeta_eq_mul {s : ℂ} (hs : s ≠ 0) (hG : Complex.Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero hs, div_mul_cancel₀ _ hG]

/-! ### The archimedean factor -/

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => ((π : ℝ) : ℂ) ^ (-s / 2)) s :=
    ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s := by
    refine (Complex.differentiableAt_Gamma (s / 2) fun m => ?_).comp s (differentiableAt_id.div_const 2)
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact h1.mul h2

/-- **`logDeriv Gammaℝ = −½ log π + ½ ψ(s/2)`** on the right half-plane. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Real.log π : ℂ) / 2 + Complex.digamma (s / 2) / 2 := by
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : ((π : ℝ) : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hd1 : DifferentiableAt ℂ (fun s : ℂ => ((π : ℝ) : ℂ) ^ (-s / 2)) s :=
    ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hπ)
  have hd2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s := by
    refine (Complex.differentiableAt_Gamma (s / 2) fun m => ?_).comp s (differentiableAt_id.div_const 2)
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hG : Complex.Gammaℝ = fun s : ℂ => ((π : ℝ) : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
    funext fun s => Complex.Gammaℝ_def s
  rw [hG, logDeriv_fun_mul s hpow hΓ hd1 hd2]
  congr 1
  · have hlin : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2) s := by
      have := (hasDerivAt_id s).neg.div_const 2
      simpa using this
    have h := hlin.const_cpow (c := ((π : ℝ) : ℂ)) (Or.inl hπ)
    rw [logDeriv_apply, h.deriv, Complex.ofReal_log Real.pi_pos.le]
    field_simp
  · have := logDeriv_comp (f := Complex.Gamma) (g := fun s : ℂ => s / 2) (x := s)
      (Complex.differentiableAt_Gamma (s / 2) fun m h => by
        have := congrArg Complex.re h; simp at this; linarith)
      (differentiableAt_id.div_const 2)
    rw [Function.comp_def] at this
    rw [this, ← Complex.digamma_def]
    have hlin2 : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) s := by
      have := (hasDerivAt_id s).div_const 2
      simpa using this
    rw [hlin2.deriv]; ring

/-! ### The truncated Euler product -/

end Cvs.WeilForm.WindowSymbolZetaLogDeriv
