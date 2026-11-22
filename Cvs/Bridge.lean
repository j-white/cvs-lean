import Mathlib
import Cvs.StepA.StepAAlongEveryBandwidth
import Cvs.StepA.ConnesStepAModeCount
import Cvs.WeilForm.WindowWeilCriterion
import Cvs.WeilForm.MatrixPSDCriterion

/-!
# The bridge: what a proof of the Riemann Hypothesis gives Connes' programme

Every theorem here takes `hRH : RiemannHypothesis`, Mathlib's statement
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`), as an ordinary hypothesis. Any proof of that
statement, whatever its route and size, instantiates the whole file; nothing here depends on how
it was proved.

What it delivers, in the order of Connes §6:

* §6.4, Weil positivity: the truncated Weil form `QW_λ` is nonnegative on its form domain at
  every scale, and every finite truncation matrix is positive semidefinite.
* §6.6, Step A at finite resolution: along every fixed bandwidth `Ω`, at all large integer
  scales `x`, the bottom of the `⌈Ω log x / 2π⌉`-mode truncation is simple with an even
  eigenvector (`ConnesStepAN`), the odd sector lies strictly above it, and no zero has escaped
  to the imaginary axis.
* §6.1, Theorem 6.1 at finite resolution: for each of those truncations, the transform of the
  even bottom eigenvector has no zero off the two axes.
* The criterion runs both ways: RH is equivalent to step (a) along every fixed bandwidth together
  with `DepthToZero`, so the consequences above are not only implied by RH but characterise it.

The continuous Step A (`ConnesStepA` at every scale) and Step B are not obtained here: RH gives
the finite-resolution forms above, and the passage to the full form at the knee resolution
remains open.
-/

noncomputable section

open Real Filter

namespace Cvs.Bridge

open Cvs.StepA.StepAAlongBandwidth (StepAAlong)
open Cvs.Finite.SymmetricModeSet (Idx mode negI)

/-- The scale data used along a bandwidth: `L = log x`, `P = ⌈x⌉`, `R = ⌈log₂ x⌉`. -/
abbrev scaleP (x : ℕ) : ℕ := ⌈Real.exp (Real.log x)⌉₊
abbrev scaleR (x : ℕ) : ℕ := ⌈Real.log x / Real.log 2⌉₊

section AssumeRH

variable (hRH : RiemannHypothesis)
include hRH

/-- **§6.4 under RH**: the truncated Weil form is nonnegative on its form domain at every scale
`L`, for any prime cutoff `P ≥ e^L` and prime-power cutoff `R` with `L ≤ R log 2`. -/
theorem weil_nonneg {L : ℝ} (hL : 0 < L) {P R : ℕ} (hP : Real.exp L ≤ P)
    (hR : L ≤ R * Real.log 2) (φ : Cvs.WeilForm.FormDomain.formDomain hL.le) :
    0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL.le P R φ :=
  Cvs.WeilForm.PositivityOfRH.Q_nonneg_of_RH hRH hL hP hR φ

/-- **§6.4 under RH, finite form**: every `N`-mode truncation of the Weil form at the canonical
cutoffs is positive semidefinite. -/
theorem truncation_posSemidef {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (Cvs.Finite.TruncationQuadraticForm.M ⌈Real.exp L⌉₊ ⌈L / Real.log 2⌉₊ L (mode N)).PosSemidef :=
  Cvs.WeilForm.MatrixPSDCriterion.rh_iff_posSemidef.mp hRH L hL N

/-- **Step (a) along every bandwidth under RH**: for every `Ω > 0`, the odd sector of the
`⌈Ω log x / 2π⌉`-mode truncation lies strictly above the even bottom at all large `x`. -/
theorem stepAAlong (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ x₀ : ℕ, StepAAlong (Cvs.StepA.FixedBandwidthSetup.band Ω) x₀ :=
  (Cvs.Finite.OddDisplacementPencil.riemannHypothesis_iff_forall_stepAAlong_and_depthToZero.mp hRH).1 Ω hΩ

/-- **§6.6 Step A at finite resolution under RH**: along every fixed bandwidth `Ω > 0`, at all
large integer scales `x`, the bottom of the truncated Weil matrix is simple with an even
eigenvector. -/
theorem connesStepAN_along (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → 0 < Real.log x →
      Cvs.StepA.ConnesStepAModeCount.ConnesStepAN (scaleP x) (scaleR x) (Real.log x)
        (Cvs.StepA.FixedBandwidthSetup.band Ω (Real.log x)) := by
  obtain ⟨x₀, h⟩ := stepAAlong hRH Ω hΩ
  refine ⟨x₀, fun x hx hlx => ?_⟩
  have hA := h x hx hlx
  exact (Cvs.StepA.ConnesStepAModeCount.connesStepAN_iff _ _ hlx _).mpr
    ⟨hA, Cvs.StepA.OddAboveDisplacement.evenSimple_of_notOddEig
      (Cvs.StepA.OddAboveDisplacement.notOddEig_of_oddAbove hA)⟩

/-- **Theorem 6.1 at finite resolution under RH**: along every fixed bandwidth, at all large
scales, the transform of the even bottom eigenvector has no zero off the two axes, and none on
the imaginary axis either. -/
theorem realZeros_along (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → ∀ hlx : 0 < Real.log x,
      (∀ z ∈ Cvs.Limit.OffAxesLimit.offAxes,
        Cvs.Finite.EvenMinimisers.etransform (scaleP x) (scaleR x) hlx
          (Cvs.StepA.FixedBandwidthSetup.band Ω (Real.log x)) z ≠ 0) ∧
      Cvs.Finite.SecularCoefficientLimits.NoNonposRoot (Real.log x) (Cvs.StepA.FixedBandwidthSetup.band Ω (Real.log x))
        (Cvs.Limit.SpineWithoutSimplicity.ground (scaleP x) (scaleR x) (Real.log x) hlx
          (Cvs.StepA.FixedBandwidthSetup.band Ω (Real.log x))) := by
  obtain ⟨x₀, h⟩ := stepAAlong hRH Ω hΩ
  refine ⟨x₀, fun x hx hlx => ⟨?_, ?_⟩⟩
  · exact Cvs.Finite.EvenMinimisers.etransform_ne_zero hlx
      (Cvs.StepA.OddAboveDisplacement.evenSimple_of_notOddEig
        (Cvs.StepA.OddAboveDisplacement.notOddEig_of_oddAbove (h x hx hlx)))
  · exact Cvs.StepA.OddAboveDisplacement.noNonposRoot_of_oddAbove (h x hx hlx)

/-- **Under RH, every band off the critical line holds finitely many zeros** (it is empty). -/
theorem depthToZero : Cvs.StepA.DepthToZero.DepthToZero :=
  Cvs.StepA.DepthToZero.depthToZero_of_RH hRH

end AssumeRH

/-- **The bridge is an equivalence**: RH holds exactly when step (a) holds along every fixed
bandwidth at all large scales and every band off the line holds finitely many zeros. -/
theorem riemannHypothesis_iff :
    RiemannHypothesis ↔
      (∀ Ω : ℝ, 0 < Ω → ∃ x₀ : ℕ, StepAAlong (Cvs.StepA.FixedBandwidthSetup.band Ω) x₀) ∧
        Cvs.StepA.DepthToZero.DepthToZero :=
  Cvs.Finite.OddDisplacementPencil.riemannHypothesis_iff_forall_stepAAlong_and_depthToZero

/-- **RH is Weil positivity of the truncated forms** at every integer scale `x ≥ x₀`. -/
theorem riemannHypothesis_iff_weil (x₀ : ℕ) (hx₀ : 2 ≤ x₀) :
    RiemannHypothesis ↔ ∀ x : ℕ, x₀ ≤ x →
      ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
        0 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q _ x (Nat.clog 2 x) φ :=
  Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos x₀ hx₀

end Cvs.Bridge
