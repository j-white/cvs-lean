import Mathlib

/-!
# A sup bound on an interval is an `L²` bound on it

    (∀ t ∈ [−T, T], ‖f t − g t‖ ≤ δ)  ⟹  ∫_{[−T,T]} ‖f − g‖² ≤ δ²·2T

so a finite sup-norm net on the interval is a finite `L²` net there, which is what turns
`Cvs.Upstream.BoundedEquicontinuousCompactClosure`'s compactness into total boundedness without extracting any subsequence.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real

namespace Cvs.Upstream.SupBoundIntervalL2

/-- **Sup to `L²` on a bounded interval.** -/
theorem setIntegral_sq_le_of_sup {f g : ℝ → ℂ} {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (hint : IntegrableOn (fun t => ‖f t - g t‖ ^ 2) (Icc (-T) T))
    (hsup : ∀ t ∈ Icc (-T) T, ‖f t - g t‖ ≤ δ) :
    (∫ t in Icc (-T) T, ‖f t - g t‖ ^ 2) ≤ δ ^ 2 * (2 * T) := by
  have hbd : (∫ t in Icc (-T) T, ‖f t - g t‖ ^ 2)
      ≤ ∫ _t in Icc (-T) T, δ ^ 2 := by
    refine setIntegral_mono_on hint ?_ measurableSet_Icc fun t ht => ?_
    · exact integrableOn_const (measure_Icc_lt_top).ne
    · have h := hsup t ht
      nlinarith [norm_nonneg (f t - g t), hδ]
  have hconst : (∫ _t in Icc (-T) T, δ ^ 2) = δ ^ 2 * (2 * T) := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
    have : T - -T = 2 * T := by ring
    rw [this]
    ring
  linarith [hbd, hconst.le, hconst.ge]

end Cvs.Upstream.SupBoundIntervalL2
