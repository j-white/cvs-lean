import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The one-prime window: at `x = 3` the prime side is the prime `2` alone

A representative vanishing off `(0, L]` has self-convolution zero at every lag `|u| ≥ L`. At `x = 3` this removes the
lags `log 4`, `log 3` and `log 9`, so the window form is `pole + arch − 2 (log 2/√2) (f ⋆ f)(log 2)`: the prime `2`
couples the first `log(3/2)` of the window to its last. `OnePrimeWindowPos` is window positivity there.
-/

noncomputable section

open Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.OnePrimeWindow


/-- A function vanishing off `(0, L]` has self-convolution zero at every lag `u` with `L ≤ |u|`. -/
theorem selfConvolution_eq_zero_of_le_abs {f : ℝ → ℝ} {L u : ℝ} (hf : ∀ s ∉ Set.Ioc (0 : ℝ) L, f s = 0)
    (hu : L ≤ |u|) : selfConvolution f u = 0 := by
  have hz : ∀ s, f s * f (s + u) = 0 := by
    intro s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) L
    · by_cases hsu : s + u ∈ Set.Ioc (0 : ℝ) L
      · exfalso
        obtain ⟨h1, h2⟩ := hs
        obtain ⟨h3, h4⟩ := hsu
        rcases abs_cases u with ⟨ha, _⟩ | ⟨ha, _⟩
        · rw [ha] at hu; linarith
        · rw [ha] at hu; linarith
      · rw [hf _ hsu, mul_zero]
    · rw [hf _ hs, zero_mul]
  unfold selfConvolution
  simp [hz]

end Cvs.WeilForm.OnePrimeWindow
