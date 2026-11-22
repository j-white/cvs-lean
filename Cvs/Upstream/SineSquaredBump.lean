import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.LeftRight
import Cvs.Upstream.SineSquaredRamp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The bump on `[L, R]`: a ramp up at `L` times a ramp down at `R`

`bump L R h = ramp L h · ramp (−R) h (−·)` is `0` outside `(L, R)`, `1` on `[L + h, R − h]`, `C¹` with the product-rule
derivative `bump'`, `0 ≤ bump ≤ 1`, and when the ramps do not overlap (`L + h ≤ R − h`) the majorant of Cvs.Upstream.SineSquaredRamp
survives: `bump'² ≤ (π/h)² bump`. It is the plateau weight of Cvs.L2a.PlateauSummedDiagonal and the outer weight of the `V`-norms of Cvs.L2a.WeightedDerivativeMajorant.
-/

namespace Cvs.Upstream.SineSquaredBump

open Real Set Cvs.Upstream.SineSquaredRamp

/-- The bump on `[L, R]` with ramps of length `h`. -/
noncomputable def bump (L R h θ : ℝ) : ℝ := ramp L h θ * ramp (-R) h (-θ)

/-- Its derivative. -/
noncomputable def bump' (L R h θ : ℝ) : ℝ := ramp' L h θ * ramp (-R) h (-θ) - ramp L h θ * ramp' (-R) h (-θ)

theorem bump_nonneg (L R h θ : ℝ) : 0 ≤ bump L R h θ := mul_nonneg (ramp_nonneg _ _ _) (ramp_nonneg _ _ _)

theorem bump_le_one (L R h θ : ℝ) : bump L R h θ ≤ 1 :=
  mul_le_one₀ (ramp_le_one _ _ _) (ramp_nonneg _ _ _) (ramp_le_one _ _ _)

theorem bump_of_le {L R h θ : ℝ} (hθ : θ ≤ L) : bump L R h θ = 0 := by
  unfold bump; rw [ramp_of_le hθ, zero_mul]

theorem bump_of_ge {L R h θ : ℝ} (hθ : R ≤ θ) : bump L R h θ = 0 := by
  unfold bump; rw [ramp_of_le (by linarith : -θ ≤ -R), mul_zero]

theorem bump_eq_one {L R h θ : ℝ} (hh : 0 < h) (h1 : L + h ≤ θ) (h2 : θ ≤ R - h) : bump L R h θ = 1 := by
  unfold bump; rw [ramp_of_ge hh h1, ramp_of_ge hh (by linarith : -R + h ≤ -θ), one_mul]

theorem continuous_ramp {a h : ℝ} (hh : 0 < h) : Continuous (ramp a h) :=
  continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_ramp hh θ).continuousAt

/-- **The bump is `C¹`.** -/
theorem hasDerivAt_bump {L R h : ℝ} (hh : 0 < h) (θ : ℝ) : HasDerivAt (bump L R h) (bump' L R h θ) θ := by
  have h1 := hasDerivAt_ramp (a := L) hh θ
  have h2 : HasDerivAt (fun θ => ramp (-R) h (-θ)) (ramp' (-R) h (-θ) * (-1)) θ :=
    (hasDerivAt_ramp (a := -R) hh (-θ)).comp θ (hasDerivAt_neg θ)
  refine (h1.fun_mul h2).congr_deriv ?_
  unfold bump'; ring

theorem continuous_bump' {L R h : ℝ} (hh : 0 < h) : Continuous (bump' L R h) := by
  unfold bump'
  exact ((continuous_ramp' hh).mul ((continuous_ramp hh).comp continuous_neg)).sub
    ((continuous_ramp hh).mul ((continuous_ramp' hh).comp continuous_neg))

/-- **The majorant of the bump**: `bump'² ≤ (π/h)² bump` when the ramps do not overlap. -/
theorem bump'_sq_le {L R h : ℝ} (hh : 0 < h) (hLR : L + h ≤ R - h) (θ : ℝ) :
    bump' L R h θ ^ 2 ≤ (Real.pi / h) ^ 2 * bump L R h θ := by
  unfold bump bump'
  rcases le_or_gt θ (L + h) with hθ | hθ
  · -- on the up-ramp side the down-ramp is flat
    have e1 : ramp (-R) h (-θ) = 1 := ramp_of_ge hh (by linarith)
    have e2 : ramp' (-R) h (-θ) = 0 := ramp'_of_ge hh (by linarith)
    rw [e1, e2, mul_one, mul_zero, sub_zero, mul_one]
    exact ramp'_sq_le hh θ
  · have e1 : ramp L h θ = 1 := ramp_of_ge hh hθ.le
    have e2 : ramp' L h θ = 0 := ramp'_of_ge hh hθ.le
    rw [e1, e2, zero_mul, one_mul, zero_sub, neg_sq, one_mul]
    exact ramp'_sq_le hh (-θ)

end Cvs.Upstream.SineSquaredBump
