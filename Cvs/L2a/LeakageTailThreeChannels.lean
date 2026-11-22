import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The global form on the leakage tail, bounded below by its three channels

With `ρ` the tail's spectral density and `N = ∫ ρ`, the global Weil form is `∫ archSymbol · ρ + pole − P`.
If the mass below `2πx` is at most `ε N`, the prime channel at most `p N` and the pole at least `−q N`, then
the form is at least `(ℓ − (ℓ − archSymbol 0) ε − p − q) N` with `ℓ = floorK x K`.
-/

namespace Cvs.L2a.LeakageTailThreeChannels

open MeasureTheory Real
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

/-- **The tail form's lower bound.** For `ρ ≥ 0` with `ρ` and `archSymbol · ρ` integrable, `0 < x`,
`1 ≤ K`, `archSymbol 0 ≤ floorK x K`, low mass `≤ ε N`, `P ≤ p N` and `−q N ≤ pole`,
`(floorK x K − (floorK x K − archSymbol 0) ε − p − q) N ≤ ∫ archSymbol · ρ + pole − P`. -/
theorem tail_form_ge (ρ : ℝ → ℝ) (hρ : ∀ t, 0 ≤ ρ t) (hi : Integrable ρ)
    (hA : Integrable (fun t => archSymbol t * ρ t)) {x : ℝ} (hx : 0 < x) {K : ℕ} (hK : 1 ≤ K)
    (hfl : archSymbol 0 ≤ floorK x K) {ε p q pole P : ℝ}
    (hlow : (∫ t in {t : ℝ | |t| < 2 * π * x}, ρ t) ≤ ε * ∫ t, ρ t)
    (hP : P ≤ p * ∫ t, ρ t) (hpole : -(q * ∫ t, ρ t) ≤ pole) :
    (floorK x K - (floorK x K - archSymbol 0) * ε - p - q) * (∫ t, ρ t)
      ≤ (∫ t, archSymbol t * ρ t) + pole - P := by
  have hA' := Cvs.L2a.ArchChannelFloorAbove.floorK_mul_integral_le ρ hρ hi hA hx hK
  have hd : 0 ≤ floorK x K - archSymbol 0 := sub_nonneg.mpr hfl
  have hmul := mul_le_mul_of_nonneg_left hlow hd
  nlinarith [hA', hmul]

end Cvs.L2a.LeakageTailThreeChannels
