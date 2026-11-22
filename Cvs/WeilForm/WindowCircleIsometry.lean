import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.PartOneWeilForm
import Cvs.Prolate.GevreyTailCircle
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.Upstream.CompactSupportWeightIntegrable
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.CentredHodgeIndexWindow
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MaskedShift.AtomIdentitySmoothTest
import Cvs.WeilForm.MaskedShift.AtomPairingWeilTest
import Cvs.WeilForm.MaskedShift.ChainTestFunctionL2
import Cvs.WeilForm.MaskedShift.MaskedLiftSquareIntegrable
import Cvs.WeilForm.MaskedShift.MaskedLiftToLine
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimeOperatorBudgetGap
import Cvs.WeilForm.MaskedShift.PrimePowerRotationNumber
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget
import Cvs.WeilForm.MaskedShift.PrimeSideAtomForm
import Cvs.WeilForm.NestedWindowsMonotoneBottom
import Cvs.WeilForm.NilpotentResolventEulerSquares
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.PoleTermCauchySchwarz
import Cvs.WeilForm.PrimeOperatorPathLawDeficit
import Cvs.WeilForm.ProductIntegrability
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SpectralDensityIntegrable
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowFormTranslationInvariant
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# General Window-to-Circle Isometry, Downward Closure, and High-Band Floor

Formalizes the `L²` window-to-circle isometry `windowCircle`, the form-domain Path-Law bound
`primeTerm ≤ atomBudget · ‖φ‖²`, downward scale closure (`Q_embedD_eq`), and the high-band floor.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Cvs.Zeta.Explicit.Weil
open scoped InnerProductSpace NNReal

namespace Cvs.WeilForm.WindowCircleIsometry
open Cvs.ZeroCounting

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator

/-! ### 1. General Window-to-Circle Isometry (`windowCircle`) and Form-Domain Path-Law Bound -/

/-- `Cvs.Operator.rep : 𝕋 → ℝ` is measure-preserving from Haar measure on `𝕋` to Lebesgue measure
restricted to `[0, 1)`. -/
theorem measurePreserving_rep :
    MeasurePreserving Cvs.Operator.rep (volume : Measure Cvs.Operator.T1)
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  refine ⟨Cvs.Operator.measurable_rep, ?_⟩
  have hmp : MeasurePreserving (β := Cvs.Operator.T1) ((↑) : ℝ → Cvs.Operator.T1)
      (volume.restrict (Ico (0 : ℝ) 1)) volume := by
    rw [Cvs.PrimeOperator.restrict_Ico_eq_Ioc]
    exact Cvs.PrimeOperator.measurePreserving_mk'
  rw [← hmp.map_eq, Measure.map_map Cvs.Operator.measurable_rep hmp.measurable]
  have hae : (Cvs.Operator.rep ∘ ((↑) : ℝ → Cvs.Operator.T1))
      =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] id := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ico]
    exact Filter.Eventually.of_forall fun y hy => Cvs.Operator.rep_coe y hy.1 hy.2
  rw [Measure.map_congr hae, Measure.map_id]

/-- Reading any `g ∈ L²(ℝ)` on `𝕋` via `rep` produces a function in `L²(𝕋)`. -/
theorem memLp_circleVal_of_memLp {g : ℝ → ℝ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    MemLp (Cvs.PrimeOperator.circleVal g) 2 (volume : Measure Cvs.Operator.T1) :=
  (hg.restrict (Ico (0 : ℝ) 1)).comp_measurePreserving measurePreserving_rep

/-- The `L²(𝕋)` class attached to any `g ∈ L²(ℝ)`. -/
def circleOfLp {g : ℝ → ℝ} (hg : MemLp g 2 (volume : Measure ℝ)) : Cvs.Operator.L2 :=
  (memLp_circleVal_of_memLp hg).toLp _

/-- Lifting `circleOfLp hg` back to `ℝ` recovers `g` almost everywhere whenever `g` is supported
in `(0, 1]`. -/
theorem lift_circleOfLp {g : ℝ → ℝ} (hg : MemLp g 2 (volume : Measure ℝ))
    (hsupp : ∀ y : ℝ, y ∉ Ioc (0 : ℝ) 1 → g y = 0) :
    Cvs.PrimeOperator.lift (circleOfLp hg) =ᵐ[volume] g := by
  have h1 : ∀ᵐ z : Cvs.Operator.T1 ∂(volume : Measure Cvs.Operator.T1),
      (circleOfLp hg : Cvs.Operator.T1 → ℝ) z = Cvs.PrimeOperator.circleVal g z :=
    MemLp.coeFn_toLp _
  have h2 : ∀ᵐ y : ℝ ∂((volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)),
      (circleOfLp hg : Cvs.Operator.T1 → ℝ) (y : Cvs.Operator.T1)
        = Cvs.PrimeOperator.circleVal g (y : Cvs.Operator.T1) :=
    Cvs.PrimeOperator.measurePreserving_mk'.quasiMeasurePreserving.ae h1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc] at h2
  have h3 : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), y ≠ 0 := Measure.ae_ne volume 0
  have h4 : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), y ≠ 1 := Measure.ae_ne volume 1
  filter_upwards [h2, h3, h4] with y hy hy0 hy1
  by_cases hmem : y ∈ Ico (0 : ℝ) 1
  · obtain ⟨hy0', hy1'⟩ := hmem
    have hIoc : y ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hy0' (Ne.symm hy0), hy1'.le⟩
    rw [Cvs.PrimeOperator.lift_of_mem _ hy0' hy1', hy hIoc,
      Cvs.PrimeOperator.circleVal, Cvs.Operator.rep_coe y hy0' hy1']
  · rw [Cvs.PrimeOperator.lift_of_notMem _ hmem,
      hsupp y fun hIoc => hmem ⟨hIoc.1.le, lt_of_le_of_ne hIoc.2 hy1⟩]

/-- The unit-interval rescaled representative `y ↦ √(log c) · rep φ (y log c)` of a window class
`φ ∈ window (log c)`. -/
def unitWindow (c : ℕ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) (y : ℝ) : ℝ :=
  √(Real.log c) * Cvs.WeilForm.WindowRepresentative.rep φ (y * Real.log c)

/-- For `1 < c`, `unitWindow c φ` vanishes outside `(0, 1]`. -/
theorem unitWindow_supp {c : ℕ} (hc : 1 < c) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    ∀ y ∉ Ioc (0 : ℝ) 1, unitWindow c φ y = 0 := by
  intro y hy
  have hL : 0 < Real.log c := Cvs.PrimeOperator.log_pos_of_one_lt hc
  unfold unitWindow
  rw [Cvs.WeilForm.WindowRepresentative.rep_supp φ (y * Real.log c), mul_zero]
  rintro ⟨h0, h1⟩
  exact hy ⟨pos_of_mul_pos_left h0 hL.le, (mul_le_iff_le_one_left hL).mp h1⟩

/-- For `1 < c`, `unitWindow c φ` belongs to `L²(ℝ)`. -/
theorem memLp_unitWindow {c : ℕ} (hc : 1 < c) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    MemLp (unitWindow c φ) 2 (volume : Measure ℝ) := by
  have hL : 0 < Real.log c := Cvs.PrimeOperator.log_pos_of_one_lt hc
  have hint : Integrable (unitWindow c φ) volume :=
    ((Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).comp_mul_right' hL.ne').const_mul √(Real.log c)
  refine (memLp_two_iff_integrable_sq hint.aestronglyMeasurable).mpr ?_
  have hsq : (fun y => unitWindow c φ y ^ 2)
      = fun y => Real.log c * (Cvs.WeilForm.WindowRepresentative.rep φ (y * Real.log c)) ^ 2 := by
    funext y
    unfold unitWindow
    rw [mul_pow, Real.sq_sqrt hL.le]
  rw [hsq]
  exact ((Cvs.WeilForm.WindowRepresentative.integrable_sq_rep φ).comp_mul_right' hL.ne').const_mul (Real.log c)

/-- Rescaling `unitWindow c φ` back to `(0, log c]` via `smoothTest c` recovers `Cvs.WeilForm.WindowRepresentative.rep φ`. -/
theorem smoothTest_unitWindow {c : ℕ} (hc : 1 < c) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    Cvs.PrimeOperator.smoothTest c (unitWindow c φ) = Cvs.WeilForm.WindowRepresentative.rep φ := by
  have hL : 0 < Real.log c := Cvs.PrimeOperator.log_pos_of_one_lt hc
  have hsqrt : √(Real.log c) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  funext s
  unfold Cvs.PrimeOperator.smoothTest unitWindow
  rw [div_mul_cancel₀ s hL.ne', mul_div_cancel_left₀ _ hsqrt]

/-- The canonical circle class in `L²(𝕋)` attached to any `φ ∈ window (log c)`. -/
def windowCircle {c : ℕ} (hc : 1 < c) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) : Cvs.Operator.L2 :=
  circleOfLp (memLp_unitWindow hc φ)

/-- Lifting `windowCircle hc φ` from `𝕋` to `ℝ` recovers `unitWindow c φ` almost everywhere. -/
theorem lift_windowCircle {c : ℕ} (hc : 1 < c) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    Cvs.PrimeOperator.lift (windowCircle hc φ) =ᵐ[volume] unitWindow c φ :=
  lift_circleOfLp (memLp_unitWindow hc φ) (unitWindow_supp hc φ)

/-- **Window-to-Circle Self-Convolution Identity**: for every `φ ∈ window (log c)`, the
self-convolution of `Cvs.WeilForm.WindowRepresentative.rep φ` equals `testFn c (windowCircle hc φ)`. -/
theorem selfConvolution_rep_eq_testFn {c : ℕ} (hc : 1 < c) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    selfConvolution (Cvs.WeilForm.WindowRepresentative.rep φ) = Cvs.PrimeOperator.testFn c (windowCircle hc φ) := by
  rw [← smoothTest_unitWindow hc φ]
  funext t
  rw [show Cvs.PrimeOperator.smoothTest c (unitWindow c φ)
      = fun y => unitWindow c φ (y / Real.log c) / √(Real.log c) from rfl,
    Cvs.PrimeOperator.selfConvolution_rescale (Cvs.PrimeOperator.log_pos_of_one_lt hc)
      (unitWindow c φ) t,
    ← Cvs.PrimeOperator.selfConvolution_congr_ae (lift_windowCircle hc φ)]
  rfl

/-- **Window-to-Circle Norm Isometry**: `‖windowCircle hc φ‖² = ‖φ‖²`. -/
theorem norm_sq_windowCircle {c : ℕ} (hc : 1 < c) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    ‖windowCircle hc φ‖ ^ 2 = ‖φ‖ ^ 2 := by
  rw [← Cvs.WeilForm.NilpotentResolventEulerSquares.testFn_zero c (windowCircle hc φ),
    ← selfConvolution_rep_eq_testFn hc φ,
    (Cvs.WeilForm.WindowRepresentative.weilQW_rep 0 0 φ).2]

/-- For every `φ ∈ window (log c)`, `primeTerm P R (rep φ)` equals the quadratic form of
`primeOperator c P R` on `windowCircle hc φ`. -/
theorem primeTerm_rep_eq_inner_primeOperator {c : ℕ} (hc : 1 < c) (P R : ℕ)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep φ)
      = ⟪Cvs.PrimeOperator.primeOperator c P R (windowCircle hc φ), windowCircle hc φ⟫_ℝ := by
  unfold Cvs.WeilForm.PoleArchPrimeProblem.primeTerm
  rw [selfConvolution_rep_eq_testFn hc φ, Cvs.PrimeOperator.primePowerSide_eq_atomForm hc _ P R]
  show (∑ p ∈ Cvs.PrimeOperator.primeRange P, ∑ r ∈ Finset.Icc 1 R,
      ⟪atom c (p ^ r) (windowCircle hc φ), windowCircle hc φ⟫_ℝ) = _
  rw [← Cvs.PrimeOperator.inner_primeOperator]

/-- **General Window Path-Law Sum-of-Squares Identity**: for every `φ ∈ window (log c)`,
`primeTerm P R (rep φ)` equals `atomBudget c P R · ‖φ‖²` minus the nonnegative Path-Law sum of
squares. -/
theorem primeTerm_rep_eq_atomBudget_sub_schur {c : ℕ} (hc : 1 < c) (P R : ℕ)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep φ)
      = Cvs.PrimeOperator.atomBudget c P R * ‖φ‖ ^ 2
        - (Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm c P R (windowCircle hc φ)
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm c P R (windowCircle hc φ)) := by
  rw [primeTerm_rep_eq_inner_primeOperator hc P R φ,
    Cvs.WeilForm.PrimeOperatorPathLawDeficit.inner_primeOperator_eq_atomBudget_sub_schur hc P R,
    norm_sq_windowCircle hc φ]

/-- **General Window Path-Law Companion Sum-of-Squares Identity**: for every `φ ∈ window (log c)`,
`primeTerm P R (rep φ)` equals the companion sum of squares minus `atomBudget c P R · ‖φ‖²`. -/
theorem primeTerm_rep_eq_schurPlus_sub_atomBudget {c : ℕ} (hc : 1 < c) (P R : ℕ)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep φ)
      = (Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurPlusForm c P R (windowCircle hc φ)
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm c P R (windowCircle hc φ))
        - Cvs.PrimeOperator.atomBudget c P R * ‖φ‖ ^ 2 := by
  rw [primeTerm_rep_eq_inner_primeOperator hc P R φ,
    Cvs.WeilForm.PrimeOperatorPathLawDeficit.inner_primeOperator_eq_schurPlus_sub_atomBudget hc P R,
    norm_sq_windowCircle hc φ]

/-- **General Window Path-Law Upper Bound**: `primeTerm P R (rep φ) ≤ atomBudget c P R · ‖φ‖²`. -/
theorem primeTerm_rep_le_atomBudget {c : ℕ} (hc : 1 < c) (P R : ℕ)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep φ) ≤ Cvs.PrimeOperator.atomBudget c P R * ‖φ‖ ^ 2 := by
  rw [primeTerm_rep_eq_atomBudget_sub_schur hc P R φ]
  linarith [Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm_nonneg c P R (windowCircle hc φ),
    Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm_nonneg hc P R (windowCircle hc φ)]

/-- **General Window Path-Law Lower Bound**: `−atomBudget c P R · ‖φ‖² ≤ primeTerm P R (rep φ)`. -/
theorem neg_atomBudget_le_primeTerm_rep {c : ℕ} (hc : 1 < c) (P R : ℕ)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    -(Cvs.PrimeOperator.atomBudget c P R * ‖φ‖ ^ 2) ≤ Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep φ) := by
  rw [primeTerm_rep_eq_schurPlus_sub_atomBudget hc P R φ]
  linarith [Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurPlusForm_nonneg c P R (windowCircle hc φ),
    Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm_nonneg hc P R (windowCircle hc φ)]

/-- **Two-Sided General Window Path-Law Bound**: `|primeTerm P R (rep φ)| ≤ atomBudget c P R · ‖φ‖²`. -/
theorem abs_primeTerm_rep_le_atomBudget {c : ℕ} (hc : 1 < c) (P R : ℕ)
    (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log c)) :
    |Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep φ)| ≤ Cvs.PrimeOperator.atomBudget c P R * ‖φ‖ ^ 2 :=
  abs_le.mpr ⟨neg_atomBudget_le_primeTerm_rep hc P R φ, primeTerm_rep_le_atomBudget hc P R φ⟩

/-! ### 2. Downward Scale Closure (`Q_embedD_eq`, `floor_of_le`, `windowPos_of_le`) -/

/-- **Form Invariance under Centered Embedding**: embedding `formDomain hL` into `formDomain hL'`
for `L ≤ L'` preserves `Cvs.WeilForm.InfimumAttainedSphere.Q` whenever `(P, R)` is complete at scale `L`. -/
theorem Q_embedD_eq {L L' : ℝ} {P R P' R' : ℕ} (hL : 0 ≤ L) (hL' : 0 ≤ L') (hLL : L ≤ L')
    (hPP : P ≤ P') (hRR : R ≤ R') (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL' P' R' (Cvs.WeilForm.NestedWindowsMonotoneBottom.embedD hL hL' hLL φ) = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ :=
  Cvs.WeilForm.NestedWindowsMonotoneBottom.weilQW_embed hL hLL hPP hRR hP hR φ

/-! ### 3. Form-Domain Plancherel, Upgraded Tail Bound, and Layer 1(4) High-Band Floor -/

/-- **Form-Domain Spectral Representation of `archTerm`**: on `formDomain hL`, `archTerm` equals
`∫ archSymbol · specDensity`. -/
theorem archTerm_rep_eq_integral_archSymbol {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      = ∫ t : ℝ, Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) t := by
  have hf2 := Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hf1 := Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hfsq := Cvs.WeilForm.WindowRepresentative.integrable_sq_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hfsh := Cvs.WeilForm.WindowRepresentative.integrable_cross_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hflevy := Cvs.WeilForm.FormDomain.hdom_of_mem φ
  have hfspec := Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hf2 hf1 hflevy
  have hfρ := Cvs.WeilForm.ProductIntegrability.integrable_specDensity (Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf2 hf1)
  exact Cvs.L2a.PartOneWeilForm.arch_eq hf2 hf1 hfsq hfsh hflevy hfspec hfρ

/-- **Form-Domain Plancherel Identity**: the spectral density of `rep φ` integrates to `‖φ‖²`. -/
theorem integral_specDensity_rep_eq_norm_sq {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    (∫ t : ℝ, Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) t) = ‖φ‖ ^ 2 := by
  rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity_eq_selfConvolution (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _) (Cvs.WeilForm.WindowRepresentative.memLp_rep _),
    (Cvs.WeilForm.WindowRepresentative.weilQW_rep 0 0 (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)).2]
  rfl

/-- **Form-Domain High-Band Archimedean Lower Bound**: if `ℓ ≤ archSymbol t` for `T ≤ |t|`, then
`archTerm(rep φ) ≥ ℓ · ‖φ‖² − (ℓ − archSymbol 0) · ∫_{|t| < T} specDensity(rep φ)`. -/
theorem archTerm_rep_ge_floor_sub_lowBand {L T ℓ : ℝ} (hL : 0 ≤ L)
    (hℓ : ∀ t : ℝ, T ≤ |t| → ℓ ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    ℓ * ‖φ‖ ^ 2
        - (ℓ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
          * (∫ t in {t : ℝ | |t| < T}, Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) t)
      ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  set f := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hf2 := Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hf1 := Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hflevy := Cvs.WeilForm.FormDomain.hdom_of_mem φ
  have hfspec := Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch hf2 hf1 hflevy
  have hfρ := Cvs.WeilForm.ProductIntegrability.integrable_specDensity (Cvs.WeilForm.SpectralDensityIntegrable.integrable_fourier_sq hf2 hf1)
  have hfA : Integrable (fun t => Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) volume := by
    refine (hfspec.add (hfρ.const_mul (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]; ring
  rw [archTerm_rep_eq_integral_archSymbol hL φ, ← integral_specDensity_rep_eq_norm_sq hL φ]
  exact Cvs.L2a.ArchChannelFloorAbove.floor_mul_integral_le (Cvs.WeilForm.SelfConvolutionCosine.specDensity f) (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f) hfρ hfA hℓ

/-- **Form-Domain Pole Term Lower Bound**: `−4 sinh(L/2) · ‖φ‖² ≤ poleTerm(rep φ)`. -/
theorem neg_sinh_le_poleTerm_rep {L : ℝ} (hL : 0 ≤ L) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    -4 * Real.sinh (L / 2) * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.PoleArchPrimeProblem.poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  set f := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  set g : ℝ → ℝ := fun x => f (x + L / 2)
  have hf2 := Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hfsupp := Cvs.WeilForm.WindowRepresentative.rep_supp (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hgsupp : ∀ x, x ∉ Icc (-(L / 2)) (L / 2) → g x = 0 :=
    Cvs.WeilForm.CentredWindowTranslate.support_translate hfsupp
  have hgmem : MemLp g 2 volume := Cvs.WeilForm.CentredWindowTranslate.memLp_translate _ hf2
  have hfint : Integrable f volume := Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hf2 hfsupp
  have hgint : Integrable g volume := hfint.comp_add_right (L / 2)
  have hgsq : Integrable (fun s : ℝ => g s ^ 2) volume := hgmem.integrable_sq
  have hgA : Integrable (fun s : ℝ => g s * Real.exp (s / 2)) volume :=
    Cvs.Upstream.CompactSupportWeightIntegrable.integrable_mul_weight hgint hgsupp
      (Real.continuous_exp.comp (continuous_id.div_const 2))
  have hgM : Integrable (fun s : ℝ => g s * Real.exp (-(s / 2))) volume :=
    Cvs.Upstream.CompactSupportWeightIntegrable.integrable_mul_weight hgint hgsupp
      (Real.continuous_exp.comp (continuous_id.div_const 2).neg)
  have hpole := Cvs.WeilForm.PoleTermCauchySchwarz.neg_le_poleTerm hL hgsupp hgsq hgA hgM
  have hrec : Real.exp (-(L / 2 / 2)) * Real.exp (L / 2 / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpole_eq : 2 * (∫ x : ℝ, g x * Real.exp (x / 2)) * (∫ x : ℝ, g x * Real.exp (-(x / 2)))
      = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm f := by
    unfold g Cvs.WeilForm.PoleArchPrimeProblem.poleTerm Cvs.WeilForm.PoleArchPrimeProblem.Mplus Cvs.WeilForm.PoleArchPrimeProblem.Mminus
    rw [Cvs.WeilForm.WindowFormTranslationInvariant.integral_translate_exp f (L / 2), Cvs.WeilForm.WindowFormTranslationInvariant.integral_translate_exp' f (L / 2)]
    linear_combination
      2 * (∫ x, f x * Real.exp (x / 2)) * (∫ x, f x * Real.exp (-(x / 2))) * hrec
  rw [hpole_eq, Cvs.WeilForm.CentredWindowTranslate.selfConvolution_translate f (L / 2) 0,
    (Cvs.WeilForm.WindowRepresentative.weilQW_rep 0 0 (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)).2, ← Submodule.coe_norm] at hpole
  linarith

/-- General truncation split of `Cvs.WeilForm.InfimumAttainedSphere.Q` into `poleTerm + archTerm - primeTerm`. -/
theorem Q_eq_split_general (x P R : ℕ) (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R φ
      = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - Cvs.WeilForm.PoleArchPrimeProblem.primeTerm P R (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) := by
  show Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)) = _
  rw [(Cvs.WeilForm.WindowRepresentative.weilQW_rep P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))).1, Cvs.WeilForm.PoleArchPrimeProblem.weilForm_split]

/-- **General Form-Domain Path-Law Sum-of-Squares Decomposition of `Cvs.WeilForm.InfimumAttainedSphere.Q`**: holds for every
class `φ ∈ formDomain` without continuity or tameness hypotheses. -/
theorem Q_eq_pathLaw_schur {x : ℕ} (hx : 1 < x) (P R : ℕ)
    (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R φ
      = Cvs.WeilForm.PoleArchPrimeProblem.poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - Cvs.PrimeOperator.atomBudget x P R * ‖φ‖ ^ 2
        + (Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm x P R (windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm x P R (windowCircle hx (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))) := by
  rw [Q_eq_split_general x P R φ,
    primeTerm_rep_eq_atomBudget_sub_schur hx P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)),
    ← Submodule.coe_norm]
  ring

/-- **Layer 1(4) High-Band Coercivity Floor**: if `ℓ ≤ archSymbol t` for `|t| ≥ T` and the low-band
spectral mass in `(-T, T)` is at most `η · ‖φ‖²`, then
`Q(φ) ≥ (ℓ − (ℓ − archSymbol 0) η − atomBudget x P R) ‖φ‖² + poleTerm(rep φ)`. -/
theorem Q_ge_highBand_floor {x : ℕ} (hx : 1 < x) (P R : ℕ) {T ℓ η : ℝ}
    (hℓ0 : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ ℓ) (hℓ : ∀ t : ℝ, T ≤ |t| → ℓ ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t)
    (φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x))
    (hlow : (∫ t in {t : ℝ | |t| < T},
        Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) t)
      ≤ η * ‖φ‖ ^ 2) :
    (ℓ - (ℓ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * η - Cvs.PrimeOperator.atomBudget x P R) * ‖φ‖ ^ 2
        + Cvs.WeilForm.PoleArchPrimeProblem.poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R φ := by
  have hQ := Q_eq_split_general x P R φ
  have harch := archTerm_rep_ge_floor_sub_lowBand (Real.log_natCast_nonneg x) hℓ φ
  have hprime := primeTerm_rep_le_atomBudget hx P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))
  rw [← Submodule.coe_norm] at hprime
  have hmul : (ℓ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0)
        * (∫ t in {t : ℝ | |t| < T},
            Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) t)
      ≤ (ℓ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * (η * ‖φ‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr hℓ0)
  linarith

/-- On the codimension-1 subspace `ker Uc`, the pole term is a pure nonnegative square
`2 Vc(φ)² ≥ 0`. -/
theorem poleTerm_rep_nonneg_of_Uc_eq_zero {L : ℝ} (hL : 0 ≤ L) {φ : Cvs.WeilForm.FormDomain.formDomain hL}
    (hU : Cvs.WeilForm.CentredHodgeIndexWindow.Uc hL φ = 0) :
    0 ≤ Cvs.WeilForm.PoleArchPrimeProblem.poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)) := by
  rw [Cvs.WeilForm.CentredHodgeIndexWindow.poleTerm_rep_centered hL φ, hU]
  have : 0 ≤ 2 * Cvs.WeilForm.CentredHodgeIndexWindow.Vc hL φ ^ 2 := by positivity
  linarith

/-- **Codimension-1 High-Band Coercivity Floor on `ker Uc`**: when `Uc φ = 0`, `poleTerm(rep φ) ≥ 0`
so `(ℓ − (ℓ − archSymbol 0) η − atomBudget x P R) ‖φ‖² ≤ Q P R φ`. -/
theorem Q_ge_highBand_floor_of_Uc_eq_zero {x : ℕ} (hx : 1 < x) (P R : ℕ) {T ℓ η : ℝ}
    (hℓ0 : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ ℓ) (hℓ : ∀ t : ℝ, T ≤ |t| → ℓ ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t)
    {φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)}
    (hU : Cvs.WeilForm.CentredHodgeIndexWindow.Uc (Real.log_natCast_nonneg x) φ = 0)
    (hlow : (∫ t in {t : ℝ | |t| < T},
        Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) t)
      ≤ η * ‖φ‖ ^ 2) :
    (ℓ - (ℓ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * η - Cvs.PrimeOperator.atomBudget x P R) * ‖φ‖ ^ 2
      ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R φ := by
  have h1 := Q_ge_highBand_floor hx P R hℓ0 hℓ φ hlow
  have hpole := poleTerm_rep_nonneg_of_Uc_eq_zero (Real.log_natCast_nonneg x) hU
  linarith

/-- **Reflection-Even High-Band Coercivity Floor**: on `Ev x`, `Uc φ = 0` so
`(ℓ − (ℓ − archSymbol 0) η − atomBudget x x ⌈log₂ x⌉) ‖φ‖² ≤ Qx x φ`. -/
theorem Qx_even_ge_highBand_floor {x : ℕ} (hx : 1 < x) {T ℓ η : ℝ}
    (hℓ0 : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 ≤ ℓ) (hℓ : ∀ t : ℝ, T ≤ |t| → ℓ ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol t)
    {φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)} (hEv : φ ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x)
    (hlow : (∫ t in {t : ℝ | |t| < T},
        Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) t)
      ≤ η * ‖φ‖ ^ 2) :
    (ℓ - (ℓ - Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0) * η
        - Cvs.PrimeOperator.atomBudget x x (Nat.clog 2 x)) * ‖φ‖ ^ 2
      ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x φ :=
  Q_ge_highBand_floor_of_Uc_eq_zero hx x (Nat.clog 2 x) hℓ0 hℓ
    (Cvs.WeilForm.CentredHodgeIndexWindow.Uc_eq_zero_of_mem_evenSub (Real.log_natCast_nonneg x) hEv) hlow

end Cvs.WeilForm.WindowCircleIsometry
