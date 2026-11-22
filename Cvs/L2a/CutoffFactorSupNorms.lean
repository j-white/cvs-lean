import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.L2a.HierarchyFactorSuprema
import Cvs.L2a.HierarchyModePairNode

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sup norms of the path-weight factors on the intervals of the cutoff route

The bounds of Cvs.L2a.HierarchyFactorSuprema at `θ₀ = 19/20` for the mode pairs `≥ 2` (`s ≥ 4`, `t ≥ s + 5`) and at `θ₀ = 4/3` for the
pairs `(1, k)` (`t ≥ 4`), with their sign conditions discharged: the constants `κ₁, κ₂, κ₁', κ₂'` of the trees
(Cvs.L2a.TreeBoundModePair, Cvs.L2a.TreeBoundFirstPairBoundary) as explicit rational expressions in `c, s, t`.
-/

namespace Cvs.L2a.CutoffFactorSupNorms

open Real Set Cvs.L2a.HierarchyModePairNode Cvs.L2a.HierarchyFactorSuprema

/-- The sup of `|g₁|` on `θ ≥ 19/20` for a mode pair `≥ 2`. -/
noncomputable def κ₁m (c s t : ℝ) : ℝ := (s * (361 / 400) - 1) / (c ^ 2 * (361 / 400) * (t - s) * (s * t * (361 / 400) - t - s))
noncomputable def κ₂m (c s t : ℝ) : ℝ := (t * (361 / 400) - 1) / (c ^ 2 * (361 / 400) * (t - s) * (s * t * (361 / 400) - t - s))
noncomputable def κ₁'m (c s t : ℝ) : ℝ :=
  2 * (s ^ 2 * t + (t + s) / ((19 / 20 : ℝ) ^ 2) ^ 2) / (c ^ 2 * (t - s) * (19 / 20) ^ 3 * (s * t - (t + s) / (19 / 20) ^ 2) ^ 2)
noncomputable def κ₂'m (c s t : ℝ) : ℝ :=
  2 * (s * t ^ 2 + (t + s) / ((19 / 20 : ℝ) ^ 2) ^ 2) / (c ^ 2 * (t - s) * (19 / 20) ^ 3 * (s * t - (t + s) / (19 / 20) ^ 2) ^ 2)

theorem modes_conditions {s t : ℝ} (hs : 4 ≤ s) (hst : s + 5 ≤ t) :
    1 < s * (361 / 400) ∧ 1 < t * (361 / 400) ∧ t + s < s * t * (361 / 400) ∧
    0 ≤ s * t * (361 / 400) * (s * (361 / 400) - 2) + t + s ∧
    0 ≤ s * t * (361 / 400) * (t * (361 / 400) - 2) + t + s := by
  have ht : 9 ≤ t := by linarith
  refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s - 4) (by linarith : (0:ℝ) ≤ t - 9)]
  · have : 0 ≤ s * t * (361 / 400) * (s * (361 / 400) - 2) := by
      apply mul_nonneg (by positivity : (0:ℝ) ≤ s * t * (361 / 400)); linarith
    linarith
  · have : 0 ≤ s * t * (361 / 400) * (t * (361 / 400) - 2) := by
      apply mul_nonneg (by positivity : (0:ℝ) ≤ s * t * (361 / 400)); linarith
    linarith

/-- **The four sup norms for a mode pair `≥ 2` on `θ ≥ 19/20`.** -/
theorem factors_modes {c s t θ : ℝ} (hc : 0 < c) (hs : 4 ≤ s) (hst : s + 5 ≤ t) (hθ : 19 / 20 ≤ θ) :
    |g₁ c s t θ| ≤ κ₁m c s t ∧ |g₂ c s t θ| ≤ κ₂m c s t ∧ |g₁' c s t θ| ≤ κ₁'m c s t ∧ |g₂' c s t θ| ≤ κ₂'m c s t := by
  obtain ⟨h1, h2, hD, hQ1, hQ2⟩ := modes_conditions hs hst
  have hs0 : 0 < s := by linarith
  have hts : s < t := by linarith
  have hX : (361 / 400 : ℝ) ≤ θ ^ 2 := by nlinarith
  have hD' : t + s < s * t * (19 / 20 : ℝ) ^ 2 := by norm_num; linarith
  refine ⟨abs_g₁_le_of hc hs0 hts (by norm_num) h1 hD hQ1 hX,
    abs_g₂_le_of hc hs0 hts (by norm_num) h2 hD hQ2 hX, ?_, ?_⟩
  · exact abs_g₁'_le_of hc hs0 hts (by norm_num) hD' hθ
  · exact abs_g₂'_le_of hc hs0 hts (by norm_num) hD' hθ

/-- The sup of the factors on `θ ≥ 4/3` for a pair `(1, k)`. -/
noncomputable def κ₁f (c t : ℝ) : ℝ := (1 * (16 / 9) - 1) / (c ^ 2 * (16 / 9) * (t - 1) * (1 * t * (16 / 9) - t - 1))
noncomputable def κ₂f (c t : ℝ) : ℝ := (t * (16 / 9) - 1) / (c ^ 2 * (16 / 9) * (t - 1) * (1 * t * (16 / 9) - t - 1))
noncomputable def κ₁'f (c t : ℝ) : ℝ :=
  2 * (1 ^ 2 * t + (t + 1) / ((4 / 3 : ℝ) ^ 2) ^ 2) / (c ^ 2 * (t - 1) * (4 / 3) ^ 3 * (1 * t - (t + 1) / (4 / 3) ^ 2) ^ 2)
noncomputable def κ₂'f (c t : ℝ) : ℝ :=
  2 * (1 * t ^ 2 + (t + 1) / ((4 / 3 : ℝ) ^ 2) ^ 2) / (c ^ 2 * (t - 1) * (4 / 3) ^ 3 * (1 * t - (t + 1) / (4 / 3) ^ 2) ^ 2)

theorem first_conditions {t : ℝ} (ht : 4 ≤ t) :
    (1 : ℝ) < 1 * (16 / 9) ∧ 1 < t * (16 / 9) ∧ t + 1 < 1 * t * (16 / 9) ∧
    0 ≤ 1 * t * (16 / 9) * (1 * (16 / 9) - 2) + t + 1 ∧
    0 ≤ 1 * t * (16 / 9) * (t * (16 / 9) - 2) + t + 1 := by
  refine ⟨by norm_num, by linarith, by linarith, by linarith, ?_⟩
  have : 0 ≤ 1 * t * (16 / 9) * (t * (16 / 9) - 2) := by
    apply mul_nonneg (by positivity : (0:ℝ) ≤ 1 * t * (16 / 9)); linarith
  linarith

/-- **The four sup norms for a pair `(1, k)` on `θ ≥ 4/3`.** -/
theorem factors_first {c t θ : ℝ} (hc : 0 < c) (ht : 4 ≤ t) (hθ : 4 / 3 ≤ θ) :
    |g₁ c 1 t θ| ≤ κ₁f c t ∧ |g₂ c 1 t θ| ≤ κ₂f c t ∧ |g₁' c 1 t θ| ≤ κ₁'f c t ∧ |g₂' c 1 t θ| ≤ κ₂'f c t := by
  obtain ⟨h1, h2, hD, hQ1, hQ2⟩ := first_conditions ht
  have hts : (1 : ℝ) < t := by linarith
  have hX : (16 / 9 : ℝ) ≤ θ ^ 2 := by nlinarith
  have hD' : t + 1 < 1 * t * (4 / 3 : ℝ) ^ 2 := by norm_num; linarith
  refine ⟨abs_g₁_le_of hc one_pos hts (by norm_num) h1 hD hQ1 hX,
    abs_g₂_le_of hc one_pos hts (by norm_num) h2 hD hQ2 hX, ?_, ?_⟩
  · exact abs_g₁'_le_of hc one_pos hts (by norm_num) hD' hθ
  · exact abs_g₂'_le_of hc one_pos hts (by norm_num) hD' hθ

end Cvs.L2a.CutoffFactorSupNorms
