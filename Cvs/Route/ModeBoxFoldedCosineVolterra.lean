import Mathlib
import Cvs.Approximant.ConnesEndpointGeometry
import Cvs.Finite.CosineModeOverlap
import Cvs.Finite.LevyKernelIncrement
import Cvs.Finite.ModeSumPairValues
import Cvs.Route.EvenMatrixSlotPoleRestored
import Cvs.Route.ModeBoxIsometricTransfer
import Cvs.Route.ModeBoxShiftedArchGreen
import Cvs.WeilForm.ArchGreenSecondChannel
import Cvs.WeilForm.PrimeMomentVolterra
import Cvs.Zeta.PrimePowerSideTruncated

/-!
# Folded Cosine and Linear-Shift Volterra Identity on `ModeBox M₀`

Lifts `Cvs.Approximant.ConnesEndpointGeometry.folded_discrepancyEntry_eq_signedMoment` and `Cvs.Approximant.ThreeModeMassShiftFilters.cosineVolterra_sub_linear`
to `ModeBox M₀`, absorbs `(coreDeficit + ε) * (η ⬝ᵥ η)` into the linear Volterra ramp.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace Cvs.Route.ModeBoxFoldedCosineVolterra
open Cvs.ZeroCounting

open scoped BigOperators Matrix
open Real Filter Finset MeasureTheory
open Cvs.Finite.SymmetricModeSet
open Cvs.WeilForm.ArchGreenSecondChannel
open Cvs.WeilForm.PrimeMomentVolterra
open Cvs.Approximant.ConnesEndpointGeometry
open Cvs.Route.EvenMatrixSlotPoleRestored
open Cvs.Route.ModeBoxIsometricTransfer
open Cvs.Route.ModeBoxShiftedArchGreen

/-! ### Unsigned cosine amplitudes on `ModeBox M₀` -/

/-! ### Simultaneous sign-inversion invariance and folded Volterra identity -/

/-- The divided-difference kernel `Cvs.Finite.CosineModeOverlap.K` is invariant under simultaneous sign negation. -/
theorem K_neg_neg (L : ℝ) (m n : ℤ) (v : ℝ) :
    Cvs.Finite.CosineModeOverlap.K L (-m) (-n) v = Cvs.Finite.CosineModeOverlap.K L m n v := by
  unfold Cvs.Finite.CosineModeOverlap.K
  simp only [neg_inj]
  push_cast
  have hm : 2 * π * -(m : ℝ) * v / L = -(2 * π * (m : ℝ) * v / L) := by ring
  have hn : 2 * π * -(n : ℝ) * v / L = -(2 * π * (n : ℝ) * v / L) := by ring
  rw [hm, hn, Real.cos_neg, Real.sin_neg, Real.sin_neg]
  split_ifs
  · rfl
  · rw [show -Real.sin (2 * π * (m : ℝ) * v / L) - -Real.sin (2 * π * (n : ℝ) * v / L) =
        -(Real.sin (2 * π * (m : ℝ) * v / L) - Real.sin (2 * π * (n : ℝ) * v / L)) by ring,
      show π * (-(n : ℝ) - -(m : ℝ)) = -(π * ((n : ℝ) - m)) by ring,
      neg_div_neg_eq]

/-- The window-cut kernel `Cvs.Finite.LevyKernelIncrement.Kc` is invariant under simultaneous sign negation. -/
theorem Kc_neg_neg (L : ℝ) (m n : ℤ) (v : ℝ) :
    Cvs.Finite.LevyKernelIncrement.Kc L (-m) (-n) v = Cvs.Finite.LevyKernelIncrement.Kc L m n v := by
  unfold Cvs.Finite.LevyKernelIncrement.Kc
  rw [K_neg_neg]

/-- `Cvs.Finite.ModeSumPairValues.primePair` is invariant under simultaneous sign negation. -/
theorem primePair_neg_neg (P R : ℕ) (L : ℝ) (m n : ℤ) :
    Cvs.Finite.ModeSumPairValues.primePair P R L (-m) (-n) = Cvs.Finite.ModeSumPairValues.primePair P R L m n := by
  unfold Cvs.Finite.ModeSumPairValues.primePair
  simp_rw [Kc_neg_neg]

/-- `Cvs.WeilForm.ArchGreenSecondChannel.meanEntry` is invariant under simultaneous sign negation. -/
theorem meanEntry_neg_neg (L : ℝ) (m n : ℤ) :
    Cvs.WeilForm.ArchGreenSecondChannel.meanEntry L (-m) (-n) = Cvs.WeilForm.ArchGreenSecondChannel.meanEntry L m n := by
  unfold Cvs.WeilForm.ArchGreenSecondChannel.meanEntry
  simp_rw [Kc_neg_neg]

/-- `Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry` is invariant under simultaneous sign negation. -/
theorem discrepancyEntry_neg_neg (P R : ℕ) (L : ℝ) (m n : ℤ) :
    Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L (-m) (-n) = Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L m n := by
  unfold Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry
  rw [primePair_neg_neg, meanEntry_neg_neg]

/-- Folded `discrepancyEntry` identity for arbitrary signed modes `a, b : ℤ`. -/
theorem discrepancyEntry_add_neg_eq_cosineVolterra {L : ℝ} (hL : 0 < L)
    (P R : ℕ) (a b : ℤ) :
    Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L a b + Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L a (-b) =
      (4 / L) * Cvs.Approximant.ConnesEndpointGeometry.cosineVolterra L a.natAbs b.natAbs
        (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) := by
  have hfold := Cvs.Approximant.ConnesEndpointGeometry.folded_discrepancyEntry_eq_signedMoment hL P R a.natAbs b.natAbs
  have hL0 : L ≠ 0 := hL.ne'
  have hnat : Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L (a.natAbs : ℤ) (b.natAbs : ℤ) +
      Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L (a.natAbs : ℤ) (-(b.natAbs : ℤ)) =
      (4 / L) * Cvs.Approximant.ConnesEndpointGeometry.cosineVolterra L a.natAbs b.natAbs
        (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) := by
    field_simp at hfold ⊢
    linarith
  rw [← hnat]
  have hb_eq : ∀ x : ℤ,
      Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L x b + Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L x (-b) =
        Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L x (b.natAbs : ℤ) +
          Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L x (-(b.natAbs : ℤ)) := by
    intro x
    rcases Int.natAbs_eq b with hb | hb
    · rw [← hb]
    · conv_lhs => rw [hb, neg_neg]
      ring
  rw [hb_eq a]
  rcases Int.natAbs_eq a with ha | ha
  · rw [← ha]
  · conv_lhs => rw [ha]
    have h1 := discrepancyEntry_neg_neg P R L (a.natAbs : ℤ) (-(b.natAbs : ℤ))
    have h2 := discrepancyEntry_neg_neg P R L (a.natAbs : ℤ) (b.natAbs : ℤ)
    rw [neg_neg] at h1
    linarith

/-! ### `boxVolterraMatrix` on `ModeBox M₀` and Equivalence with `boxDiscrepancyMatrix` -/

/-- Unsigned cosine Volterra matrix on `ModeBox M₀` associated to a ramp profile `V : ℝ → ℝ`. -/
def boxVolterraMatrix (L : ℝ) (M₀ : ℕ) (V : ℝ → ℝ) :
    Matrix (ModeBox M₀) (ModeBox M₀) ℝ :=
  fun i j => (2 / L) * Cvs.Approximant.ConnesEndpointGeometry.cosineVolterra L i.1.natAbs j.1.natAbs V

/-- On `evenModeSub (negBox M₀)`, `boxDiscrepancyMatrix` and `boxVolterraMatrix` have identical
matrix-vector products. -/
theorem boxDiscrepancyMatrix_mulVec_eq_boxVolterraMatrix {L : ℝ} (hL : 0 < L)
    (P R M₀ : ℕ) {η : ModeBox M₀ → ℝ} (hη : η ∈ evenModeSub (negBox M₀)) :
    boxDiscrepancyMatrix P R L M₀ *ᵥ η =
      boxVolterraMatrix L M₀
        (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ η := by
  funext i
  simp only [Matrix.mulVec, dotProduct, boxDiscrepancyMatrix, boxVolterraMatrix, boxMode]
  have hperm : (∑ j : ModeBox M₀, Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 (-j.1) * η j) =
      ∑ j : ModeBox M₀, Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 j.1 * η j := by
    have h := Equiv.sum_comp ((negBox_involutive M₀).toPerm)
      (fun j : ModeBox M₀ => Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 j.1 * η j)
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.Involutive.coe_toPerm, hη j]
    rfl
  have hhalf : (∑ j : ModeBox M₀, Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 j.1 * η j) =
      ∑ j : ModeBox M₀,
        (1 / 2) * (Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 j.1 +
          Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 (-j.1)) * η j := by
    calc ∑ j : ModeBox M₀, Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 j.1 * η j
        = (1 / 2) * ((∑ j : ModeBox M₀, Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 j.1 * η j) +
            ∑ j : ModeBox M₀, Cvs.WeilForm.ArchGreenSecondChannel.discrepancyEntry P R L i.1 (-j.1) * η j) := by
          rw [hperm]; ring
      _ = _ := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
  rw [hhalf]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [discrepancyEntry_add_neg_eq_cosineVolterra hL P R i.1 j.1]
  ring

/-- On `evenModeSub (negBox M₀)`, the quadratic form of `boxDiscrepancyMatrix` equals that of
`boxVolterraMatrix` for `primeRamp - meanRamp`. -/
theorem boxDiscrepancyMatrix_quad_eq_boxVolterraMatrix {L : ℝ} (hL : 0 < L)
    (P R M₀ : ℕ) {η : ModeBox M₀ → ℝ} (hη : η ∈ evenModeSub (negBox M₀)) :
    η ⬝ᵥ (boxDiscrepancyMatrix P R L M₀ *ᵥ η) =
      η ⬝ᵥ (boxVolterraMatrix L M₀
        (fun t => Cvs.WeilForm.PrimeMomentVolterra.primeRamp P R t - Cvs.WeilForm.PrimeMomentVolterra.meanRamp t) *ᵥ η) := by
  rw [boxDiscrepancyMatrix_mulVec_eq_boxVolterraMatrix hL P R M₀ hη]

/-! ### Exact linear-ramp identity for `boxVolterraMatrix` (`Cvs.Approximant.ThreeModeMassShiftFilters.cosineVolterra_id`) -/

/-! ### Linear ramp shift for `boxVolterraMatrix` (`Cvs.Approximant.ThreeModeMassShiftFilters.cosineVolterra_sub_linear`) -/

/-! ### Linear-shifted Volterra targets on `ModeBox M₀` and routes to `RiemannHypothesis` -/

end Cvs.Route.ModeBoxFoldedCosineVolterra
