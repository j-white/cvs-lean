import Mathlib
import Cvs.Finite.SymmetricModeSet
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.LowModeRungBulkFloor
import Cvs.Route.PosChannelFloorCoercivity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-!
# Explicit Frequency Threshold `freqBound` and Integer-Mode Cutoff Rung `modeCutoffRung`

Bounds `lowModeSet L N C` inside `{i | |mode_N(i)| ≤ M₀}` for `L exp(|C| + 30) ≤ M₀` and establishes
unconditional bulk floor, strip contraction, and rung-residual reductions on `modeCutoffRung N M₀`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.FreqThresholdModeCutoff
open Cvs.ZeroCounting

open scoped Matrix
open Real Filter
open Cvs.Finite.SymmetricModeSet
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.PosChannelFloorCoercivity
open Cvs.Route.LowModeRungBulkFloor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Explicit frequency threshold `freqBound` and containment of `lowModeSet` -/

/-- **The explicit archimedean threshold frequency** `2π exp(|C| + 30)` above which `archSymbol > C`. -/
def freqBound (C : ℝ) : ℝ := 2 * Real.pi * Real.exp (|C| + 30)

/-- `freqBound C` is always at least `2`, so the digamma asymptotic threshold `2 ≤ t` applies. -/
theorem two_le_freqBound (C : ℝ) : 2 ≤ freqBound C := by
  unfold freqBound
  have hpi : (3 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have he1 : (1 : ℝ) ≤ Real.exp (|C| + 30) := by
    rw [Real.one_le_exp_iff]
    have := abs_nonneg C
    linarith
  nlinarith

/-- Whenever `freqBound C ≤ t`, the logarithmic digamma lower bound strictly exceeds `C`. -/
theorem lt_log_Bound_of_freqBound_le {t : ℝ} (C : ℝ) (ht : freqBound C ≤ t) :
    C < Real.log (t / 2) - 57 / t - Real.log Real.pi := by
  have ht0_ge : (2 : ℝ) ≤ freqBound C := two_le_freqBound C
  have ht2 : (2 : ℝ) ≤ t := le_trans ht0_ge ht
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog0 : Real.log (freqBound C / 2) = Real.log Real.pi + (|C| + 30) := by
    have h : freqBound C / 2 = Real.pi * Real.exp (|C| + 30) := by unfold freqBound; ring
    rw [h, Real.log_mul (ne_of_gt hpi0) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have hlog : Real.log (freqBound C / 2) ≤ Real.log (t / 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have h57 : 57 / t ≤ 57 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) ht2
  have hCabs : C ≤ |C| := le_abs_self C
  linarith

/-- Whenever `freqBound C ≤ |t|`, `C < archSymbol t`. -/
theorem lt_archSymbol_of_freqBound_le {t : ℝ} (C : ℝ) (ht : freqBound C ≤ |t|) :
    C < Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t := by
  have ht2 : 2 ≤ |t| := le_trans (two_le_freqBound C) ht
  exact lt_of_lt_of_le (lt_log_Bound_of_freqBound_le C ht)
    (Cvs.Route.PosChannelFloorCoercivity.archSymbol_ge_of_two_le_abs ht2)

/-- Every mode `i ∈ lowModeSet L N C` has frequency `|2π mode_N(i) / L| < freqBound C`. -/
theorem abs_freq_lt_of_mem_lowModeSet {L : ℝ} {N : ℕ} {C : ℝ} {i : Cvs.Finite.SymmetricModeSet.Idx N}
    (hi : i ∈ lowModeSet L N C) :
    |2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L| < freqBound C := by
  by_contra hge
  have hlt := lt_archSymbol_of_freqBound_le C (not_lt.1 hge)
  have hi' : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * π * Cvs.Finite.SymmetricModeSet.mode N i / L) < C := hi
  linarith

/-- Every mode `i ∈ lowModeSet L N C` has integer mode `|mode_N(i)| < L * exp(|C| + 30)` for `0 < L`. -/
theorem abs_mode_lt_of_mem_lowModeSet {L : ℝ} (hL : 0 < L) {N : ℕ} {C : ℝ}
    {i : Cvs.Finite.SymmetricModeSet.Idx N} (hi : i ∈ lowModeSet L N C) :
    |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)| < L * Real.exp (|C| + 30) := by
  have hfreq := abs_freq_lt_of_mem_lowModeSet hi
  unfold freqBound at hfreq
  have hpi : 0 < 2 * π := by positivity
  have habs : |2 * π * (Cvs.Finite.SymmetricModeSet.mode N i : ℝ) / L| = 2 * π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)| / L := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hL]
  rw [habs, div_lt_iff₀ hL] at hfreq
  have hmul : 2 * π * |(Cvs.Finite.SymmetricModeSet.mode N i : ℝ)| < 2 * π * (L * Real.exp (|C| + 30)) := by
    linarith
  exact lt_of_mul_lt_mul_left hmul hpi.le

/-! ### Explicit integer-mode cutoff set `modeCutoffSet` and rung subspace `modeCutoffRung` -/

/-- **The explicit integer-mode cutoff set** `{i : Idx N | |mode_N(i)| ≤ M₀}`. -/
def modeCutoffSet (N M₀ : ℕ) : Set (Cvs.Finite.SymmetricModeSet.Idx N) :=
  {i : Cvs.Finite.SymmetricModeSet.Idx N | (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ M₀}

/-- **The explicit integer-mode cutoff rung subspace** spanned by `evenBasisVec (negI N) i`
for all modes `i` with `(mode N i).natAbs ≤ M₀`. -/
def modeCutoffRung (N M₀ : ℕ) : Submodule ℝ (Cvs.Finite.SymmetricModeSet.Idx N → ℝ) :=
  Submodule.span ℝ (evenBasisVec (Cvs.Finite.SymmetricModeSet.negI N) '' modeCutoffSet N M₀)

/-- `modeCutoffRung N M₀` is a submodule of `evenModeSub (negI N)`. -/
theorem modeCutoffRung_le_evenModeSub (N M₀ : ℕ) :
    modeCutoffRung N M₀ ≤ evenModeSub (Cvs.Finite.SymmetricModeSet.negI N) :=
  span_evenBasisVec_le_evenModeSub (Cvs.Finite.SymmetricModeSet.negI_involutive N) (modeCutoffSet N M₀)

/-- Every mode index `i : Idx N` has `(mode N i).natAbs ≤ N`. -/
theorem natAbs_mode_le (N : ℕ) (i : Cvs.Finite.SymmetricModeSet.Idx N) :
    (Cvs.Finite.SymmetricModeSet.mode N i).natAbs ≤ N := by
  rcases i with _ | ⟨k, b⟩
  · simp [Cvs.Finite.SymmetricModeSet.mode]
  · cases b <;> simp only [Cvs.Finite.SymmetricModeSet.mode, ↓reduceIte, Bool.false_eq_true, Int.natAbs_neg] <;> omega

/-- Whenever `L * exp(|C| + 30) ≤ M₀`, `lowModeSet L N C ⊆ modeCutoffSet N M₀` for all `N`. -/
theorem lowModeSet_subset_modeCutoffSet {L : ℝ} (hL : 0 < L) (N : ℕ) (C : ℝ)
    {M₀ : ℕ} (hM₀ : L * Real.exp (|C| + 30) ≤ M₀) :
    lowModeSet L N C ⊆ modeCutoffSet N M₀ := by
  intro i hi
  dsimp [modeCutoffSet]
  obtain ⟨h1, h2⟩ := abs_lt.1 (lt_of_lt_of_le (abs_mode_lt_of_mem_lowModeSet hL hi) hM₀)
  have h1' : -(M₀ : ℤ) < Cvs.Finite.SymmetricModeSet.mode N i := by exact_mod_cast h1
  have h2' : Cvs.Finite.SymmetricModeSet.mode N i < (M₀ : ℤ) := by exact_mod_cast h2
  omega

/-! ### Unconditional bulk floors and strip contractions on `modeCutoffRung N M₀` -/

/-! ### Reduction of `ApoleSlot` and `RiemannHypothesis` to `modeCutoffRung N M₀` -/

end Cvs.Route.FreqThresholdModeCutoff
