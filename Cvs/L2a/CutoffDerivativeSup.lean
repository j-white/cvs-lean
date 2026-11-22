import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.LeftRight
import Cvs.L2a.HierarchyFactorSuprema
import Cvs.L2a.HierarchyModePairNode
import Cvs.Upstream.SineSquaredBump
import Cvs.Upstream.SineSquaredRamp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The derivative sup of the cutoffs, and the factors at the far end

`|ramp'| ≤ π/(2h)` and `|bump'| ≤ π/h` (Cvs.Upstream.SineSquaredRamp, Cvs.Upstream.SineSquaredBump): the constants `S'` of the node weights of the cutoff route.
At the far end `θ = b` the factors of a pair `(1, k)` obey `|g₁(b)| ≤ (b² − 1)/(c²b²(t − 1)(tb² − t − 1))` and
`|g₂(b)| ≤ (tb² − 1)/(…)` (Cvs.L2a.HierarchyFactorSuprema at `X₀ = b²`), of order `1/(c²t²b²)` and `1/(c²tb²)`: the constants `κ_iᴿ` of the
boundary term at `b` (Cvs.L2a.TreeBoundFirstPairBoundary, Cvs.L2a.BoundaryConstantMassSum).
-/

namespace Cvs.L2a.CutoffDerivativeSup

open Real Set Cvs.L2a.HierarchyModePairNode Cvs.Upstream.SineSquaredRamp Cvs.Upstream.SineSquaredBump Cvs.L2a.HierarchyFactorSuprema

theorem abs_ramp'_le {a h : ℝ} (hh : 0 < h) (θ : ℝ) : |ramp' a h θ| ≤ Real.pi / (2 * h) := by
  unfold ramp'
  split_ifs
  · simp; positivity
  · rw [abs_mul, abs_of_pos (by positivity : 0 < Real.pi / (2 * h))]
    exact mul_le_of_le_one_right (by positivity) (abs_sin_le_one _)
  · simp; positivity

theorem abs_bump'_le {L R h : ℝ} (hh : 0 < h) (θ : ℝ) : |bump' L R h θ| ≤ Real.pi / h := by
  unfold bump'
  have h1 : |ramp' L h θ * ramp (-R) h (-θ)| ≤ Real.pi / (2 * h) := by
    rw [abs_mul]
    calc |ramp' L h θ| * |ramp (-R) h (-θ)| ≤ Real.pi / (2 * h) * 1 := by
          apply mul_le_mul (abs_ramp'_le hh θ) _ (abs_nonneg _) (by positivity)
          rw [abs_of_nonneg (ramp_nonneg _ _ _)]; exact ramp_le_one _ _ _
      _ = Real.pi / (2 * h) := mul_one _
  have h2 : |ramp L h θ * ramp' (-R) h (-θ)| ≤ Real.pi / (2 * h) := by
    rw [abs_mul]
    calc |ramp L h θ| * |ramp' (-R) h (-θ)| ≤ 1 * (Real.pi / (2 * h)) := by
          apply mul_le_mul _ (abs_ramp'_le hh _) (abs_nonneg _) zero_le_one
          rw [abs_of_nonneg (ramp_nonneg _ _ _)]; exact ramp_le_one _ _ _
      _ = Real.pi / (2 * h) := one_mul _
  calc |ramp' L h θ * ramp (-R) h (-θ) - ramp L h θ * ramp' (-R) h (-θ)|
      ≤ |ramp' L h θ * ramp (-R) h (-θ)| + |ramp L h θ * ramp' (-R) h (-θ)| := abs_sub _ _
    _ ≤ Real.pi / (2 * h) + Real.pi / (2 * h) := add_le_add h1 h2
    _ = Real.pi / h := by field_simp; ring

/-- **The factors of `(1, k)` at the far end `b ≥ 2`.** -/
theorem factors_first_at {c t b : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hb : 2 ≤ b) :
    |g₁ c 1 t b| ≤ (1 * b ^ 2 - 1) / (c ^ 2 * b ^ 2 * (t - 1) * (1 * t * b ^ 2 - t - 1)) ∧
    |g₂ c 1 t b| ≤ (t * b ^ 2 - 1) / (c ^ 2 * b ^ 2 * (t - 1) * (1 * t * b ^ 2 - t - 1)) := by
  have hb2 : (4 : ℝ) ≤ b ^ 2 := by nlinarith
  have hts : (1 : ℝ) < t := by linarith
  have h1 : (1 : ℝ) < 1 * b ^ 2 := by linarith
  have h2 : 1 < t * b ^ 2 := by nlinarith
  have hD : t + 1 < 1 * t * b ^ 2 := by nlinarith
  have hQ1 : 0 ≤ 1 * t * b ^ 2 * (1 * b ^ 2 - 2) + t + 1 := by
    have : 0 ≤ 1 * t * b ^ 2 * (1 * b ^ 2 - 2) := by
      apply mul_nonneg (by positivity : (0:ℝ) ≤ 1 * t * b ^ 2); linarith
    linarith
  have hQ2 : 0 ≤ 1 * t * b ^ 2 * (t * b ^ 2 - 2) + t + 1 := by
    have : 0 ≤ 1 * t * b ^ 2 * (t * b ^ 2 - 2) := by
      apply mul_nonneg (by positivity : (0:ℝ) ≤ 1 * t * b ^ 2); linarith
    linarith
  exact ⟨abs_g₁_le_of hc one_pos hts (by positivity) h1 hD hQ1 le_rfl,
    abs_g₂_le_of hc one_pos hts (by positivity) h2 hD hQ2 le_rfl⟩

end Cvs.L2a.CutoffDerivativeSup
