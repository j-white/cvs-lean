import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A small admixture moves an L² mass by at most `(1 ± ε)²`

If `∫B² ≤ ε² ∫A²` on an interval, `0 < ε ≤ 1`, then `(1−ε)² ∫A² ≤ ∫(A − B)² ≤ (1+ε)² ∫A²` (pointwise Young).
Applied to `ĝ = μ[h₄ − κh₀]` outside the window, `ProlateLeakageArcsinDecay`'s tail ratio for `h₄` passes to `ĝ` with the
factor `((1+ε)/(1−ε))²`.
-/

namespace Cvs.Upstream.SmallAdmixtureMassBounds

open intervalIntegral Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-- **Admixture bounds.** -/
theorem admixture_bounds {A B : ℝ → ℝ} {s t ε : ℝ} (hst : s ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : ContinuousOn A (Icc s t)) (hB : ContinuousOn B (Icc s t))
    (hsmall : ∫ r in s..t, B r ^ 2 ≤ ε ^ 2 * ∫ r in s..t, A r ^ 2) :
    (1 - ε) ^ 2 * (∫ r in s..t, A r ^ 2) ≤ ∫ r in s..t, (A r - B r) ^ 2 ∧
      ∫ r in s..t, (A r - B r) ^ 2 ≤ (1 + ε) ^ 2 * ∫ r in s..t, A r ^ 2 := by
  have iA : IntervalIntegrable (fun r => A r ^ 2) MeasureTheory.volume s t :=
    (hA.pow 2).intervalIntegrable_of_Icc hst
  have iB : IntervalIntegrable (fun r => B r ^ 2) MeasureTheory.volume s t :=
    (hB.pow 2).intervalIntegrable_of_Icc hst
  have iAB : IntervalIntegrable (fun r => (A r - B r) ^ 2) MeasureTheory.volume s t :=
    ((hA.sub hB).pow 2).intervalIntegrable_of_Icc hst
  have hA0 : 0 ≤ ∫ r in s..t, A r ^ 2 := integral_nonneg hst fun r _ => sq_nonneg _
  constructor
  · have hpt : ∀ r ∈ Icc s t, (1 - ε) * A r ^ 2 - (1 / ε - 1) * B r ^ 2 ≤ (A r - B r) ^ 2 := by
      intro r _
      have key : 2 * (A r * B r) ≤ ε * A r ^ 2 + B r ^ 2 / ε := by
        have : 0 ≤ (ε * A r - B r) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
        have e : (ε * A r - B r) ^ 2 / ε = ε * A r ^ 2 - 2 * (A r * B r) + B r ^ 2 / ε := by
          field_simp; ring
        linarith
      have e2 : (1 / ε - 1) * B r ^ 2 = B r ^ 2 / ε - B r ^ 2 := by field_simp
      nlinarith
    have hmono := integral_mono_on hst ((iA.const_mul (1 - ε)).sub (iB.const_mul (1 / ε - 1))) iAB hpt
    rw [intervalIntegral.integral_sub (iA.const_mul _) (iB.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    have hc : 0 ≤ 1 / ε - 1 := by rw [sub_nonneg, le_div_iff₀ hε]; linarith
    have := mul_le_mul_of_nonneg_left hsmall hc
    have e : (1 / ε - 1) * (ε ^ 2 * ∫ r in s..t, A r ^ 2) = (ε - ε ^ 2) * ∫ r in s..t, A r ^ 2 := by
      field_simp
    have e3 : (1 - ε) ^ 2 * (∫ r in s..t, A r ^ 2)
        = (1 - ε) * (∫ r in s..t, A r ^ 2) - (ε - ε ^ 2) * ∫ r in s..t, A r ^ 2 := by ring
    linarith
  · have hpt : ∀ r ∈ Icc s t, (A r - B r) ^ 2 ≤ (1 + ε) * A r ^ 2 + (1 + 1 / ε) * B r ^ 2 := by
      intro r _
      have key : -(2 * (A r * B r)) ≤ ε * A r ^ 2 + B r ^ 2 / ε := by
        have : 0 ≤ (ε * A r + B r) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
        have e : (ε * A r + B r) ^ 2 / ε = ε * A r ^ 2 + 2 * (A r * B r) + B r ^ 2 / ε := by
          field_simp; ring
        linarith
      have e2 : (1 + 1 / ε) * B r ^ 2 = B r ^ 2 + B r ^ 2 / ε := by field_simp
      nlinarith
    have hmono := integral_mono_on hst iAB ((iA.const_mul (1 + ε)).add (iB.const_mul (1 + 1 / ε))) hpt
    rw [intervalIntegral.integral_add (iA.const_mul _) (iB.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    have hc : 0 ≤ 1 + 1 / ε := by positivity
    have := mul_le_mul_of_nonneg_left hsmall hc
    have e : (1 + 1 / ε) * (ε ^ 2 * ∫ r in s..t, A r ^ 2) = (ε + ε ^ 2) * ∫ r in s..t, A r ^ 2 := by
      field_simp; ring
    have e3 : (1 + ε) ^ 2 * (∫ r in s..t, A r ^ 2)
        = (1 + ε) * (∫ r in s..t, A r ^ 2) + (ε + ε ^ 2) * ∫ r in s..t, A r ^ 2 := by ring
    linarith

/-- **The tail ratio for `ĝ = h₄ − κh₀`.** With `ProlateLeakageArcsinDecay`'s hypotheses for `ψ = h₄` and the admixture
`κφ` at most `ε < 1` in L² relative to `ψ` on `[Y, Z]` and on `[ξ₀, Z]`, the tail ratio holds for
`ψ − κφ` with the extra factor `((1+ε)/(1−ε))²`. -/
theorem ghat_tail_ratio {c χ κ ε : ℝ} {ψ u φ : ℝ → ℝ} {ξ₀ Y Z : ℝ} (h1 : 1 < ξ₀) (hY : ξ₀ ≤ Y)
    (hZ : Y ≤ Z) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : ∀ t ∈ Icc ξ₀ Z, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ Z, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2)
    (hL : 0 < (arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
      - fac c χ ξ₀ / (2 * qP c χ ξ₀))
    (hφ : ContinuousOn φ (Icc ξ₀ Z)) (hε : 0 < ε) (hε1 : ε < 1)
    (hmixY : ∫ t in Y..Z, (κ * φ t) ^ 2 ≤ ε ^ 2 * ∫ t in Y..Z, ψ t ^ 2)
    (hmix0 : ∫ t in ξ₀..Z, (κ * φ t) ^ 2 ≤ ε ^ 2 * ∫ t in ξ₀..Z, ψ t ^ 2) :
    ∫ t in Y..Z, (ψ t - κ * φ t) ^ 2 ≤ ((1 + ε) / (1 - ε)) ^ 2
      * (fac c χ ξ₀ / ((arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
        - fac c χ ξ₀ / (2 * qP c χ ξ₀))
      * (arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) + 1 / (2 * qP c χ Y)))
      * ∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2 := by
  have hle : ξ₀ ≤ Z := hY.trans hZ
  have hψc : ContinuousOn ψ (Icc ξ₀ Z) := fun t ht => (hψ t ht).continuousAt.continuousWithinAt
  have hsub : Icc Y Z ⊆ Icc ξ₀ Z := Icc_subset_Icc_left hY
  have hκφ : ContinuousOn (fun t => κ * φ t) (Icc ξ₀ Z) := continuousOn_const.mul hφ
  have upY := (admixture_bounds hZ hε hε1.le (hψc.mono hsub) (hκφ.mono hsub) hmixY).2
  have lo0 := (admixture_bounds hle hε hε1.le hψc hκφ hmix0).1
  have tr := prolate_tail_ratio h1 hY hZ hc hχ hχc hψ hu hW hL
  set R := fac c χ ξ₀ / ((arccos (1 / Z) - arccos (1 / ξ₀)) / (2 * c * fac c χ ξ₀)
        - fac c χ ξ₀ / (2 * qP c χ ξ₀)) * (arcsin (1 / Y) / (2 * √(c ^ 2 - χ)) + 1 / (2 * qP c χ Y))
  have hR : 0 ≤ R := by
    have hY1 : 1 < Y := lt_of_lt_of_le h1 hY
    have hc2 : 0 < c ^ 2 := by positivity
    have := qP_pos hY1 hc2 hχc
    have := Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.sub_pos' hχc
    have := arcsin_nonneg.mpr (show (0:ℝ) ≤ 1 / Y by positivity)
    have hF : 0 < fac c χ ξ₀ := by
      have hW0 := wP_pos h1 hc2 hχc
      unfold fac; exact mul_pos (div_pos (by linarith) (by linarith)) (exp_pos _)
    positivity
  have h1e : 0 < 1 - ε := by linarith
  have hI0 : ∫ t in ξ₀..Z, ψ t ^ 2 ≤ (∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2) / (1 - ε) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ∫ t in Y..Z, (ψ t - κ * φ t) ^ 2 ≤ (1 + ε) ^ 2 * ∫ t in Y..Z, ψ t ^ 2 := upY
    _ ≤ (1 + ε) ^ 2 * (R * ∫ t in ξ₀..Z, ψ t ^ 2) := mul_le_mul_of_nonneg_left tr (by positivity)
    _ ≤ (1 + ε) ^ 2 * (R * ((∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2) / (1 - ε) ^ 2)) := by
        gcongr
    _ = ((1 + ε) / (1 - ε)) ^ 2 * R * ∫ t in ξ₀..Z, (ψ t - κ * φ t) ^ 2 := by
        field_simp

end Cvs.Upstream.SmallAdmixtureMassBounds
