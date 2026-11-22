import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTermsSum
import Cvs.WeilForm.EvenDiagonalProper
import Cvs.WeilForm.ShiftSumModeDiagonal
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaLimitDischarged

/-!
# The diagonal minimum is attained only at the zero mode

    archSymbol 0 < archSymbol t   for t ≠ 0,   and   ∑ⱼ wⱼ cos(ωₙ uⱼ) ≤ ∑ⱼ wⱼ

so with nonnegative prime weights the diagonal `D` is strictly smallest at `n = 0`.  The
symbol's strictness comes from the deficit's closed form, which is a positive quotient.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

namespace Cvs.WeilForm.DiagonalMinimumZeroMode

/-- **Each deficit term is strictly positive** away from `t = 0` — read off the closed form. -/
theorem digammaDeficit_pos {t : ℝ} (ht : t ≠ 0) (k : ℕ) : 0 < Cvs.Zeta.digammaDeficit t k := by
  rw [Cvs.Zeta.digammaDeficit_eq]
  have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0:ℝ) < 1 / 4 + (k : ℝ) := by linarith
  have hnum : 0 < (t / 2) ^ 2 := by positivity
  have hden : 0 < (1 / 4 + (k : ℝ)) * ((1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2) := by positivity
  exact div_pos hnum hden

/-- **The symbol is strictly smallest at zero frequency.** -/
theorem archSymbol_zero_lt {t : ℝ} (ht : t ≠ 0) : archSymbol 0 < archSymbol t := by
  have hsum := Cvs.WeilForm.Archimedean.LevyTermsSum.hasSum_digammaDeficit t
  have hpos : 0 < (Complex.digamma (Cvs.Zeta.digammaArg t 0)).re
      - (Complex.digamma (Cvs.Zeta.digammaArg 0 0)).re := by
    refine lt_of_lt_of_le (digammaDeficit_pos ht 0) ?_
    have hle := sum_le_hasSum {0} (fun k _ => (digammaDeficit_pos ht k).le) hsum
    simpa using hle
  unfold archSymbol
  linarith

/-- **The diagonal is strictly smallest at the zero mode.**  The symbol is, and the prime
side is largest there because every displacement contributes `cos 0 = 1`. -/
theorem diag_lt_of_ne_zero {ι : Type*} {L : ℝ} (hL : 0 < L) (s : Finset ι) (w u : ι → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) {n : ℕ} (hn : n ≠ 0) :
    Cvs.WeilForm.EvenDiagonalProper.diagVal L s w u 0 < Cvs.WeilForm.EvenDiagonalProper.diagVal L s w u n := by
  have hfreq0 : Cvs.WeilForm.EvenDiagonalProper.freqN L 0 = 0 := by
    unfold Cvs.WeilForm.EvenDiagonalProper.freqN; simp
  have hfreqn : Cvs.WeilForm.EvenDiagonalProper.freqN L n ≠ 0 := by
    unfold Cvs.WeilForm.EvenDiagonalProper.freqN
    have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  have harch : archSymbol (Cvs.WeilForm.EvenDiagonalProper.freqN L 0)
      < archSymbol (Cvs.WeilForm.EvenDiagonalProper.freqN L n) := by
    rw [hfreq0]
    exact archSymbol_zero_lt hfreqn
  have hprime : Cvs.WeilForm.ShiftSumModeDiagonal.shiftDiag L s w u n
      ≤ Cvs.WeilForm.ShiftSumModeDiagonal.shiftDiag L s w u 0 := by
    unfold Cvs.WeilForm.ShiftSumModeDiagonal.shiftDiag
    refine Finset.sum_le_sum fun j hj => ?_
    have hc : Real.cos (2 * π * (n : ℕ) / L * u j) ≤ 1 := Real.cos_le_one _
    have hc0 : Real.cos (2 * π * ((0:ℕ) : ℝ) / L * u j) = 1 := by
      simp
    rw [hc0]
    nlinarith [hw j hj, hc]
  unfold Cvs.WeilForm.EvenDiagonalProper.diagVal
  linarith

end Cvs.WeilForm.DiagonalMinimumZeroMode
