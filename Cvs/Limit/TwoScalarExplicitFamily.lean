import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Limit.MomentLimitsBoundedUnique
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisSpineChosenConstants
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Limit.TwoScalarsRiemannHypothesis
import Cvs.Limit.ZeroFreeApproximantsRH

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# An explicit family for the two-scalar route

Taking the window at `x = n + 2` and the normalisation point `1 + I` settles the positivity of the
window lengths and the two conditions on the point, and asking the mode count to dominate the
squared window length settles both the mode count's positivity and the ratio bound, with
constant one.
-/

set_option maxHeartbeats 3200000

noncomputable section

namespace Cvs.Limit.TwoScalarExplicitFamily
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet Cvs.Limit.SpineWithoutSimplicity

/-- The window length at scale `n`: the CvS window at `x = n + 2`. -/
def wlen (n : ℕ) : ℝ := Real.log ((n : ℝ) + 2)

/-- **The window lengths are positive.** -/
theorem wlen_pos (n : ℕ) : 0 < wlen n := by
  refine Real.log_pos ?_
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The normalisation point. -/
def pt : ℂ := 1 + Complex.I

/-- **The normalisation point is not the origin.** -/
theorem pt_ne_zero : pt ≠ 0 := by
  intro h
  have him : pt.im = 0 := by rw [h]; simp
  simp [pt] at him

/-- **The normalisation point has a purely imaginary square.** -/
theorem pt_sq_re : (pt ^ 2).re = 0 := by
  simp [pt, pow_two, Complex.mul_re]

variable {N : ℕ → ℕ}

/-- **A mode count dominating the squared window length is positive.** -/
theorem modes_pos (hNL : ∀ n, wlen n ^ 2 ≤ (N n : ℝ)) (n : ℕ) : 0 < N n := by
  rcases Nat.eq_zero_or_pos (N n) with h | h
  · exfalso
    have hle := hNL n
    rw [h] at hle
    simp only [Nat.cast_zero] at hle
    nlinarith [wlen_pos n]
  · exact h

/-- **The squared window length over the mode count is at most one.** -/
theorem sq_div_modes_le (hNL : ∀ n, wlen n ^ 2 ≤ (N n : ℝ)) (n : ℕ) :
    wlen n ^ 2 / (N n : ℝ) ≤ 1 := by
  have hN : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast modes_pos hNL n
  rw [div_le_one hN]
  exact hNL n

/-- **The Riemann Hypothesis from the two scalars, on an explicit family.** -/
theorem riemannHypothesis_of_scalars_sees_explicit (P R : ℕ → ℕ)
    (hNL : ∀ n, wlen n ^ 2 ≤ (N n : ℝ)) {K : ℝ}
    (hS : ∀ n, ((Cvs.Limit.MomentLimitsBoundedUnique.gpoly wlen_pos P R N n).roots.map fun r => ‖r‖⁻¹).sum ≤ K)
    (hx0 : ∀ n, ground (P n) (R n) (wlen n) (wlen_pos n) (N n) none ≠ 0)
    (hSees : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ f : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun k z => Cvs.Limit.OffAxisSpineChosenConstants.cnorm (P (φ k)) (R (φ k)) (wlen_pos (φ k)) (N (φ k)) pt
          * Cvs.Finite.RecentredTransform.cgtransform (P (φ k)) (R (φ k)) (wlen_pos (φ k)) (N (φ k)) z)
        f Filter.atTop Cvs.Limit.OffAxesLimit.offAxes →
      ∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes, Cvs.Limit.ZeroFreeApproximantsRH.Xi z = 0 → f z = 0) :
    RiemannHypothesis :=
  Cvs.Limit.TwoScalarsRiemannHypothesis.riemannHypothesis_of_scalars_sees wlen_pos P R N pt_ne_zero pt_sq_re
    (modes_pos hNL) hS hx0 (sq_div_modes_le hNL) hSees

end Cvs.Limit.TwoScalarExplicitFamily
