import Mathlib
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WeilFormReflection
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-!
# The prime side vanishes on the window of length `log 2`

    `selfConvolution (rep φ) (±L) = 0`,   so at `x = 2` the prime-power side of the form is `0`.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PrimeSideVanishesLogTwo

/-- **The self-convolution vanishes at the window length**: the representative and its shift by
`L` have supports meeting only at a point. -/
theorem selfConvolution_rep_at_L {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) L = 0 := by
  unfold selfConvolution
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Ioc (0:ℝ) L
  · have : s + L ∉ Ioc (0:ℝ) L := fun h => by linarith [hs.1, h.2]
    simp [Cvs.WeilForm.WindowRepresentative.rep_supp φ _ this]
  · simp [Cvs.WeilForm.WindowRepresentative.rep_supp φ _ hs]

theorem selfConvolution_rep_at_neg_L {L : ℝ} (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) (-L) = 0 := by
  rw [Cvs.WeilForm.WeilFormReflection.selfConvolution_neg, selfConvolution_rep_at_L]

/-- The prime powers up to `2` with exponent up to `1`: just `2¹`. -/
theorem primes_le_two : (Finset.range 3).filter Nat.Prime = {2} := by decide

/-- **At `x = 2` the prime side is zero.** -/
theorem primeSide_eq_zero (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) :
    primePowerSideTruncated 2 1 (selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ)) = 0 := by
  unfold primePowerSideTruncated
  rw [primes_le_two, Finset.sum_singleton, show Finset.Icc 1 1 = {1} from rfl, Finset.sum_singleton]
  have h1 := selfConvolution_rep_at_L φ
  have h2 := selfConvolution_rep_at_neg_L φ
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at h1 h2 ⊢
  rw [h1, h2]; ring

end Cvs.WeilForm.PrimeSideVanishesLogTwo
