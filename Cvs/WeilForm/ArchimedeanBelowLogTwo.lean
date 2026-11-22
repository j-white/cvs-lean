import Mathlib
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.LevyKernelIncrement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form is archimedean below `log 2`

The cut kernel vanishes at and beyond the window's edge, and every prime lag is at least `log 2`,
so on a window no longer than `log 2` the prime channel contributes nothing and the pair value is
its pole, archimedean and Lévy channels alone; the witness family's first window is exactly
`log 2`, so its form is prime-free.
-/

noncomputable section

open Real

namespace Cvs.WeilForm.ArchimedeanBelowLogTwo

open Cvs.Finite.CosineModeOverlap Cvs.Finite.LevyKernelIncrement

/-- **The kernel vanishes at the window's edge**, in both branches. -/
theorem K_at_edge {L : ℝ} (hL : L ≠ 0) (m n : ℤ) : K L m n L = 0 := by
  unfold K
  have hsin : ∀ k : ℤ, Real.sin (2 * π * k * L / L) = 0 := by
    intro k
    have : 2 * π * k * L / L = (2 * k : ℤ) * π := by
      field_simp
      push_cast
      ring
    rw [this]
    exact Real.sin_int_mul_pi _
  split_ifs with h
  · rw [div_self hL]; ring
  · rw [hsin m, hsin n]; ring

/-- **The cut kernel vanishes at and beyond the edge.** -/
theorem Kc_eq_zero_of_le {L v : ℝ} (hL : L ≠ 0) (m n : ℤ) (hv : L ≤ v) : Kc L m n v = 0 := by
  unfold Kc
  split_ifs with h
  · have : v = L := le_antisymm h hv
    rw [this]
    exact K_at_edge hL m n
  · rfl

/-- **Every prime lag is at least `log 2`.** -/
theorem log_two_le_prime_lag {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    Real.log 2 ≤ (r : ℝ) * Real.log p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) h2
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

end Cvs.WeilForm.ArchimedeanBelowLogTwo
