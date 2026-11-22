import Mathlib
import Cvs.Zeta.Digamma

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The archimedean weight is a filter bank

The weight paired against the kernel's spectral density is
-/

namespace Cvs.Transform

open Complex

/-- A high-pass filter of cutoff `c`: blocks `u ≪ c`, passes `u ≫ c`. -/
noncomputable def highpass (c u : ℝ) : ℝ := u ^ 2 / (c ^ 2 + u ^ 2)

/-- The `k`-th cutoff, `2(¼+k) = 2k + ½` — the height of the `k`-th pole of
`Γ(s/2)` on the `u` line. -/
noncomputable def cutoff (k : ℕ) : ℝ := 2 * (1 / 4 + (k : ℝ))

theorem cutoff_pos (k : ℕ) : 0 < cutoff k := by
  have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  unfold cutoff; linarith

theorem highpass_nonneg (c u : ℝ) : 0 ≤ highpass c u := by
  unfold highpass; positivity

/-- It never reaches full transmission. -/
theorem highpass_lt_one {c : ℝ} (hc : c ≠ 0) (u : ℝ) : highpass c u < 1 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hd : 0 < c ^ 2 + u ^ 2 := by positivity
  rw [highpass, div_lt_one hd]
  linarith [sq_nonneg u]

/-- **Each term of the archimedean weight is a high-pass filter**, of gain
`1/aₖ` and cutoff `2aₖ`. -/
theorem deficit_eq_highpass (t : ℝ) (k : ℕ) :
    Cvs.Zeta.digammaDeficit t k = (1 / (1 / 4 + (k : ℝ))) * highpass (cutoff k) t := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have ha : (0 : ℝ) < 1 / 4 + (k : ℝ) := by linarith
  have hd1 : (0 : ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2 := by positivity
  have hd2 : (0 : ℝ) < cutoff k ^ 2 + t ^ 2 := by
    have := cutoff_pos k; positivity
  rw [Cvs.Zeta.digammaDeficit_eq, highpass, cutoff]
  field_simp

end Cvs.Transform
