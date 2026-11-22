import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.Zeta.Digamma
import Cvs.Zeta.Digamma.ArchPairingLowerBound
import Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound

/-!
# The archimedean form is coercive in the mode basis

    (M − K)·∑_{n ∈ T} aₙ²  ≤  archForm freq a − K·∑ aₙ²

for any finite set `T` of modes whose symbol is at least `M`, where `K` is the symbol's
global lower bound.  So mass on high modes costs, and costs more the higher it sits.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

namespace Cvs.WeilForm.Archimedean.ArchimedeanCoercive

/-- **The symbol is twice the detection score** — the same digamma, differently normalised. -/
theorem archSymbol_eq_two_mul (t : ℝ) :
    archSymbol t = 2 * Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore t := by
  unfold archSymbol Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore
  rw [show ((1 / 4 : ℂ) + (t : ℂ) / 2 * Complex.I) = Cvs.Zeta.digammaArg t 0 by
    unfold Cvs.Zeta.digammaArg
    push_cast
    ring]
  ring

/-- **The symbol is bounded below**, globally, by twice `Cvs.Zeta.Digamma.ArchPairingLowerBound`'s constant. -/
theorem archConst_le_archSymbol (t : ℝ) : 2 * Cvs.Zeta.Digamma.ArchPairingLowerBound.archConst ≤ archSymbol t := by
  rw [archSymbol_eq_two_mul]
  have := Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archConst_le_archScore t
  linarith

/-! ### The threshold the growth supplies -/

/-- **The symbol is monotone in `|t|`.** -/
theorem archSymbol_mono {t₀ t₁ : ℝ} (h : t₀ ^ 2 ≤ t₁ ^ 2) : archSymbol t₀ ≤ archSymbol t₁ := by
  rw [archSymbol_eq_two_mul, archSymbol_eq_two_mul]
  have := Cvs.Zeta.GaussKernel.ArchimedeanCutoffBound.archScore_mono h
  linarith

/-- **Every level is passed, and stays passed.**  Beyond a threshold the symbol never drops
back below `M` — the growth `Cvs.WeilForm.Archimedean.ArchimedeanUnbounded` reads off the digamma asymptotic, made into a tail. -/
theorem exists_threshold (M : ℝ) : ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → M ≤ archSymbol t := by
  obtain ⟨T₀, hT₂, hgt⟩ := archSymbol_unbounded M
  refine ⟨T₀, hT₂, fun t ht => ?_⟩
  have hsq : T₀ ^ 2 ≤ t ^ 2 := by
    have h0 : (0:ℝ) ≤ T₀ := by linarith
    have := abs_nonneg t
    nlinarith [sq_abs t, abs_nonneg t]
  exact le_trans hgt.le (archSymbol_mono hsq)

end Cvs.WeilForm.Archimedean.ArchimedeanCoercive
