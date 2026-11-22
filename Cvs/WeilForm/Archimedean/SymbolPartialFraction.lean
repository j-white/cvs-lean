import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.Zeta.Digamma

/-!
# The symbol's partial fraction

    Re ψ(N+¼+it/2) − Re ψ(¼+it/2) = ∑_{n<N} 2bₙ/(t² + bₙ²),     bₙ = 2n + ½

Shifting the digamma argument along its poles contributes a rational function of `t`, so the
archimedean symbol splits into a rational part and a tail read at the shifted argument.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Complex

namespace Cvs.WeilForm.Archimedean.SymbolPartialFraction

open Cvs.WeilForm.Archimedean.OffWindowDefect (bIdx)

/-- **Each shifted pole contributes one rational term.** -/
theorem re_inv_eq (t : ℝ) (k : ℕ) :
    (Cvs.Zeta.digammaArg t k)⁻¹.re = 2 * bIdx k / (t ^ 2 + (bIdx k) ^ 2) := by
  rw [Cvs.Zeta.re_inv_digammaArg]
  unfold bIdx
  have h1 : (0:ℝ) < (1 / 4 + (k:ℝ)) ^ 2 + (t / 2) ^ 2 := by positivity
  have h2 : (0:ℝ) < t ^ 2 + (2 * (k:ℝ) + 1 / 2) ^ 2 := by positivity
  field_simp
  ring

/-- **The partial fraction.**  The difference of digamma real parts across `N` poles is rational
in `t`. -/
theorem re_digamma_shift (t : ℝ) (N : ℕ) :
    (Complex.digamma (Cvs.Zeta.digammaArg t N)).re
        - (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re
      = ∑ n ∈ Finset.range N, 2 * bIdx n / (t ^ 2 + (bIdx n) ^ 2) := by
  have hrec := Cvs.Zeta.digamma_add_nat (Cvs.Zeta.digammaArg t 0) (Cvs.Zeta.digammaArg_re_pos t) N
  rw [← Cvs.Zeta.digammaArg_eq_add t N] at hrec
  rw [hrec, Complex.add_re, Complex.re_sum]
  simp only [add_sub_cancel_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Cvs.Zeta.digammaArg_eq_add t k, re_inv_eq]

/-- **The symbol splits into a rational part and a shifted tail.**  `Cvs.WeilForm.Archimedean.TruncatedSymbolConstant`'s constant is the
rational part's value at the shifted argument. -/
theorem archSymbol_split (t : ℝ) (N : ℕ) :
    Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t
      = (Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst N
          - ∑ n ∈ Finset.range N, 2 * bIdx n / (t ^ 2 + (bIdx n) ^ 2))
        + ((Complex.digamma (Cvs.Zeta.digammaArg t N)).re
           - (Complex.digamma (Cvs.Zeta.digammaArg 0 N)).re) := by
  have hshift := re_digamma_shift t N
  have hconst := Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst_eq_shifted N
  unfold Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol
  rw [hconst]
  linarith [hshift]

end Cvs.WeilForm.Archimedean.SymbolPartialFraction
