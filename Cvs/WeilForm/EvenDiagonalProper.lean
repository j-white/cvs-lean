import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.ShiftSumModeDiagonal
import Cvs.Zeta.Digamma.ArchPairingLowerBound

/-!
# The full diagonal is bounded below and proper

    Dₙ = archSymbol(ωₙ) − ∑ⱼ wⱼ cos(ωₙ uⱼ)

The prime part is bounded by the total weight, uniformly in `n`, so the growth of the symbol
survives it: `D` is bounded below and only finitely many modes sit under any level.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

namespace Cvs.WeilForm.EvenDiagonalProper

variable {ι : Type*}

/-- The frequency of the `n`-th cosine mode. -/
def freqN (L : ℝ) (n : ℕ) : ℝ := 2 * π * n / L

/-- **Only finitely many cosine modes sit below any level** — `an earlier result`'s argument, at `ℕ`. -/
theorem finite_below_nat {L : ℝ} (hL : 0 < L) (M : ℝ) :
    {n : ℕ | archSymbol (freqN L n) < M}.Finite := by
  obtain ⟨T₀, hT₀2, hT₀⟩ := Cvs.WeilForm.Archimedean.ArchimedeanCoercive.exists_threshold M
  have hpi := Real.pi_pos
  refine Set.Finite.subset (Set.finite_Icc 0 ⌈T₀ * L / (2 * π)⌉₊) ?_
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn
  have hlt : |freqN L n| < T₀ := by
    by_contra hc
    exact absurd hn (not_lt.mpr (hT₀ _ (not_lt.mp hc)))
  have hfe : |freqN L n| = 2 * π * (n : ℝ) / L := by
    unfold freqN
    rw [abs_div, abs_of_pos hL, abs_of_nonneg (by positivity)]
  rw [hfe, div_lt_iff₀ hL] at hlt
  have hbound : (n : ℝ) ≤ T₀ * L / (2 * π) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * π)]
    nlinarith [hlt]
  refine Set.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
  have hcast : (n : ℝ) ≤ (⌈T₀ * L / (2 * π)⌉₊ : ℝ) := le_trans hbound (Nat.le_ceil _)
  exact_mod_cast hcast

/-- The full diagonal: the symbol, less what the shift sum contributes. -/
def diagVal (L : ℝ) (s : Finset ι) (w u : ι → ℝ) (n : ℕ) : ℝ :=
  archSymbol (freqN L n) - Cvs.WeilForm.ShiftSumModeDiagonal.shiftDiag L s w u n

/-- **The diagonal is bounded below**, by the symbol's floor less the total weight. -/
theorem diag_ge (L : ℝ) (s : Finset ι) (w u : ι → ℝ) (n : ℕ) :
    2 * Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst - ∑ j ∈ s, |w j| ≤ diagVal L s w u n := by
  have h1 := Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archConst_le_archSymbol (freqN L n)
  have h2 := Cvs.WeilForm.ShiftSumModeDiagonal.abs_shiftDiag_le L s w u n
  have h3 : Cvs.WeilForm.ShiftSumModeDiagonal.shiftDiag L s w u n ≤ ∑ j ∈ s, |w j| :=
    le_trans (le_abs_self _) h2
  unfold diagVal
  linarith

/-- **The diagonal is proper**: the bounded prime part cannot undo the symbol's growth. -/
theorem diag_finite_below {L : ℝ} (hL : 0 < L) (s : Finset ι) (w u : ι → ℝ) (M : ℝ) :
    {n : ℕ | diagVal L s w u n < M}.Finite := by
  refine Set.Finite.subset (finite_below_nat hL (M + ∑ j ∈ s, |w j|)) ?_
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  have h2 := Cvs.WeilForm.ShiftSumModeDiagonal.abs_shiftDiag_le L s w u n
  have h3 : Cvs.WeilForm.ShiftSumModeDiagonal.shiftDiag L s w u n ≤ ∑ j ∈ s, |w j| :=
    le_trans (le_abs_self _) h2
  unfold diagVal at hn
  linarith

end Cvs.WeilForm.EvenDiagonalProper
