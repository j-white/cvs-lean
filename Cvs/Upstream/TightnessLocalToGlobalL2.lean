import Mathlib

/-!
# Tightness upgrades local convergence to the whole line

    small on `[−T, T]` and uniformly small tails  ⟹  small on `ℝ`

with the constant `5`: the middle contributes once and each tail twice, through
`‖a − b‖² ≤ 2‖a‖² + 2‖b‖²`.  This is the step `Cvs.WeilForm.HighFrequencyMassBound`'s tightness exists to feed.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real

namespace Cvs.Upstream.TightnessLocalToGlobalL2

/-- **The tail of a difference costs twice each tail.** -/
theorem norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have hna : (0:ℝ) ≤ ‖a‖ := norm_nonneg a
  have hnb : (0:ℝ) ≤ ‖b‖ := norm_nonneg b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a - b)]

/-- **The upgrade.**  A bound on the middle and on both tails bounds the whole line. -/
theorem integral_sq_le_of_tails {gn g : ℝ → ℂ} {T ε : ℝ} (hT : 0 ≤ T)
    (hdiff : Integrable fun t => ‖gn t - g t‖ ^ 2)
    (hgn : Integrable fun t => ‖gn t‖ ^ 2)
    (hg : Integrable fun t => ‖g t‖ ^ 2)
    (hmid : (∫ t in Icc (-T) T, ‖gn t - g t‖ ^ 2) ≤ ε)
    (htn : (∫ t in (Icc (-T) T)ᶜ, ‖gn t‖ ^ 2) ≤ ε)
    (htg : (∫ t in (Icc (-T) T)ᶜ, ‖g t‖ ^ 2) ≤ ε) :
    (∫ t : ℝ, ‖gn t - g t‖ ^ 2) ≤ 5 * ε := by
  have hsplit : (∫ t in Icc (-T) T, ‖gn t - g t‖ ^ 2)
      + ∫ t in (Icc (-T) T)ᶜ, ‖gn t - g t‖ ^ 2
      = ∫ t : ℝ, ‖gn t - g t‖ ^ 2 :=
    integral_add_compl measurableSet_Icc hdiff
  have htail : (∫ t in (Icc (-T) T)ᶜ, ‖gn t - g t‖ ^ 2)
      ≤ ∫ t in (Icc (-T) T)ᶜ, (2 * ‖gn t‖ ^ 2 + 2 * ‖g t‖ ^ 2) := by
    refine setIntegral_mono_on hdiff.integrableOn
      ((hgn.const_mul 2).add (hg.const_mul 2)).integrableOn
      measurableSet_Icc.compl fun t _ => norm_sub_sq_le (gn t) (g t)
  have hsum : (∫ t in (Icc (-T) T)ᶜ, (2 * ‖gn t‖ ^ 2 + 2 * ‖g t‖ ^ 2))
      = 2 * (∫ t in (Icc (-T) T)ᶜ, ‖gn t‖ ^ 2)
        + 2 * ∫ t in (Icc (-T) T)ᶜ, ‖g t‖ ^ 2 := by
    rw [integral_add (hgn.const_mul 2).integrableOn (hg.const_mul 2).integrableOn,
      integral_const_mul, integral_const_mul]
  rw [hsum] at htail
  linarith

end Cvs.Upstream.TightnessLocalToGlobalL2
