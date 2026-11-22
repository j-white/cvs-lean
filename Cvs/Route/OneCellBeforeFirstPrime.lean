import Mathlib
import Cvs.Route.OneCellLaplaceTransform
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The one-cell function is nonnegative before the first prime
For `0 < L ≤ log 2` no prime power enters, `G = 16(cosh(L/2) − 1) + A₀L + 2·ladder L`, and `G ≥ 0`: by concavity of
`1 − e^{−bL}` on `(0, 1/20]`, and on 62 intervals of `[1/20, 0.6932]` by exact rational bounds (seven Taylor terms of
`exp`, sixteen ladder terms, `A₀ ≥ −5.3721834231`).  The window form is nonnegative on every box shorter than `log 2`.
-/

noncomputable section

open Real Finset

namespace Cvs.Route.OneCellBeforeFirstPrime

open Cvs.Route.OneCellLaplaceTransform (G ladder primeSide)
open Cvs.Finite.WindowMatrixSymbolKernel (bk bk_pos)

theorem primeSide_eq_zero {L : ℝ} (hL : L ≤ Real.log 2) : primeSide L = 0 := by
  unfold primeSide
  have hz : (fun n : ℕ => ArithmeticFunction.vonMangoldt n / Real.sqrt n * max (L - Real.log n) 0) = 0 := by
    funext n
    rcases n with _ | _ | n
    · simp
    · simp
    · have h2 : Real.log 2 ≤ Real.log ((n + 2 : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) (by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      have : max (L - Real.log ((n + 2 : ℕ) : ℝ)) 0 = 0 := max_eq_right (by linarith)
      simp only [Pi.zero_apply, this, mul_zero]
  rw [show (fun n : ℕ => ArithmeticFunction.vonMangoldt n / Real.sqrt n * max (L - Real.log n) 0) = _ from hz]
  exact tsum_zero

theorem G_eq {L : ℝ} (hL : L ≤ Real.log 2) :
    G L = 16 * (Real.cosh (L / 2) - 1) + Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 * L + 2 * ladder L := by
  unfold G; rw [primeSide_eq_zero hL]; ring

end Cvs.Route.OneCellBeforeFirstPrime
