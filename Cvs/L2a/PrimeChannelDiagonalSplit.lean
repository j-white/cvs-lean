import Mathlib
import Cvs.L2a.AdmixtureNegligibleModes
import Cvs.L2a.RampCutSumsUniform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The prime channel splits into the log-weighted mode diagonal and the pair off-diagonal

With `P = R = ⌊X⌋`: `primeSide(F_X) = 2Σ_{M<⌊X⌋} (log(M+1)/(M+1))∫_{M+1}^X Φ² + 2Σ_{a≠n} log n ∫_1^{X/max(a,n)}
Φ(aθ)Φ(nθ)` for `Φ` continuous on `[1, X]`; for `Φ = psi c g` the off-diagonal tends to
`Prime_∞/2 − Σ_M log M · T(M)/M`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.L2a.PrimeChannelDiagonalSplit
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.PositionTruncatedTail (posTail pairI)
open Cvs.L2a.AdmixtureNegligibleModes (modeSum)

/-- The log weight `log(M+1)/(M+1)` of mode `M + 1`. -/
def wLog (M : ℕ) : ℝ := Real.log ((M : ℝ) + 1) / ((M : ℝ) + 1)

theorem wLog_nonneg (M : ℕ) : 0 ≤ wLog M :=
  div_nonneg (Real.log_nonneg (by linarith [M.cast_nonneg (α := ℝ)])) (by positivity)

/-- The prime diagonal `Σ_{M≥1} log M · T(M)/M`. -/
def primeDiag (Φ : ℝ → ℝ) : ℝ := modeSum wLog Φ

/-- `Σ_M wLog_M/(M+1) = Σ log(M+1)/(M+1)² < ∞`. -/
theorem summable_wLog_div : Summable fun M : ℕ => wLog M / ((M : ℝ) + 1) := by
  have h := (summable_nat_add_iff 1).mpr Cvs.L2a.RampCutSumsUniform.summable_one_add_log_sq
  refine h.of_nonneg_of_le (fun M => div_nonneg (wLog_nonneg M) (by positivity)) fun M => ?_
  push_cast
  have hM : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [M.cast_nonneg (α := ℝ)]
  have hl : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg hM
  have hle : Real.log ((M : ℝ) + 1) ≤ (1 + Real.log ((M : ℝ) + 1)) ^ 2 := by nlinarith
  rw [wLog, div_div, ← sq]
  exact div_le_div_of_nonneg_right hle (by positivity)

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

end Cvs.L2a.PrimeChannelDiagonalSplit
