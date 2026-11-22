import Mathlib
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.PoleFreeEntryBounds
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The archimedean channel is at least its floor above `T`, less its low mass

If `ℓ ≤ archSymbol t` whenever `T ≤ |t|`, then for a nonnegative spectral density `ρ`,
`∫ archSymbol · ρ ≥ ℓ ∫ ρ − (ℓ − archSymbol 0) ∫_{|t|<T} ρ`. Two floors: `log(T/2) − 57/T − log π`,
and at `T = 2πx` the `K`-term floor `archSymbol 0 + Σ_{k<K} (1/(k+¼) − (k+¼)/(πx)²) + log(πx/(K+¼))`.
-/

namespace Cvs.L2a.ArchChannelFloorAbove

open MeasureTheory Real
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)

/-- The symbol's floor above frequency `T`. -/
noncomputable def floorAt (T : ℝ) : ℝ := log (T / 2) - 57 / T - log π

/-- **Above `T`, the symbol is at least its floor**: `2 ≤ T ≤ |t|` gives `ℓ_T ≤ archSymbol t`. -/
theorem floorAt_le_archSymbol {T t : ℝ} (hT : 2 ≤ T) (ht : T ≤ |t|) :
    floorAt T ≤ archSymbol t := by
  have hsq : T ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]; exact pow_le_pow_left₀ (by linarith) ht 2
  exact (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol_ge hT).trans (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono hsq)

/-- **The archimedean channel against a spectral density.** If `ℓ ≤ archSymbol t` for `T ≤ |t|`,
`ρ ≥ 0` is integrable and `archSymbol · ρ` is integrable, then
`ℓ ∫ ρ − (ℓ − archSymbol 0) ∫_{|t|<T} ρ ≤ ∫ archSymbol · ρ`. -/
theorem floor_mul_integral_le (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ ρ t) (hi : Integrable ρ)
    (hA : Integrable (fun t => archSymbol t * ρ t)) {T ℓ : ℝ}
    (hℓ : ∀ t : ℝ, T ≤ |t| → ℓ ≤ archSymbol t) :
    ℓ * (∫ t, ρ t) - (ℓ - archSymbol 0) * (∫ t in {t : ℝ | |t| < T}, ρ t)
      ≤ ∫ t, archSymbol t * ρ t := by
  set S : Set ℝ := {t : ℝ | |t| < T} with hS
  have hSm : MeasurableSet S := (isOpen_lt continuous_abs continuous_const).measurableSet
  have hind : Integrable (S.indicator ρ) := hi.indicator hSm
  have hlow : ∀ t, ℓ * ρ t - (ℓ - archSymbol 0) * S.indicator ρ t ≤ archSymbol t * ρ t := by
    intro t
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht]
      have := Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.archSymbol_min_at_zero t
      nlinarith [hρ t]
    · rw [Set.indicator_of_notMem ht]
      have ht' : T ≤ |t| := by simpa [hS] using ht
      have := hℓ t ht'
      nlinarith [hρ t]
  have hint : ∫ t, (ℓ * ρ t - (ℓ - archSymbol 0) * S.indicator ρ t)
      = ℓ * (∫ t, ρ t) - (ℓ - archSymbol 0) * (∫ t in S, ρ t) := by
    rw [integral_sub (hi.const_mul ℓ) (hind.const_mul _), integral_const_mul, integral_const_mul,
      integral_indicator hSm]
  rw [← hint]
  exact integral_mono ((hi.const_mul ℓ).sub (hind.const_mul _)) hA hlow

/-- The `K`-term floor of the symbol above `2πx`. -/
noncomputable def floorK (x : ℝ) (K : ℕ) : ℝ :=
  archSymbol 0 + ∑ k ∈ Finset.range K, (1 / (1 / 4 + (k : ℝ)) - (1 / 4 + (k : ℝ)) / (π * x) ^ 2)
    + log (π * x / (K + 1 / 4))

/-- **The floor is `log x` less a constant**: `floorK x K = log x + c_K − s_K/(πx)²`, with
`c_K = archSymbol 0 + Σ_{k<K} 1/(k+¼) + log(π/(K+¼))` and `s_K = Σ_{k<K} (k+¼)`. -/
theorem floorK_eq {x : ℝ} (hx : 0 < x) (K : ℕ) :
    floorK x K = log x
      + (archSymbol 0 + ∑ k ∈ Finset.range K, 1 / (1 / 4 + (k : ℝ)) + log (π / (K + 1 / 4)))
      - (∑ k ∈ Finset.range K, (1 / 4 + (k : ℝ))) / (π * x) ^ 2 := by
  unfold floorK
  have hK : (0 : ℝ) < K + 1 / 4 := by positivity
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, mul_div_assoc, log_mul pi_pos.ne' (by positivity),
    log_div pi_pos.ne' hK.ne', log_div hx.ne' hK.ne']
  ring

/-- **The `K`-term floor above `2πx`**: for `0 < x`, `1 ≤ K` and `2πx ≤ |t|`,
`floorK x K ≤ archSymbol t`. -/
theorem floorK_le_archSymbol {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K) {t : ℝ}
    (ht : 2 * π * x ≤ |t|) : floorK x K ≤ archSymbol t := by
  have hy : 0 < π * x := mul_pos pi_pos hx
  have h := Cvs.WeilForm.Archimedean.PoleFreeEntryBounds.archSymbol_ge_K hy hK
  have hsq : (2 * (π * x)) ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact h.trans (Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono hsq)

/-- **Part 1's archimedean floor at `2πx`**: with `ρ` the tail's spectral density,
`floorK x K ∫ ρ − (floorK x K − archSymbol 0) ∫_{|t|<2πx} ρ ≤ ∫ archSymbol · ρ`. -/
theorem floorK_mul_integral_le (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ ρ t) (hi : Integrable ρ)
    (hA : Integrable (fun t => archSymbol t * ρ t)) {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K) :
    floorK x K * (∫ t, ρ t)
        - (floorK x K - archSymbol 0) * (∫ t in {t : ℝ | |t| < 2 * π * x}, ρ t)
      ≤ ∫ t, archSymbol t * ρ t :=
  floor_mul_integral_le ρ hρ hi hA fun _ ht => floorK_le_archSymbol hx hK ht

end Cvs.L2a.ArchChannelFloorAbove
