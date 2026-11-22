import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.AbelScaleSymbol
import Cvs.WeilForm.AdmissibleMultiplierMinorants
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.BandFreedomCosine
import Cvs.WeilForm.EvenBulkVisibility
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.GreenRemovesFirstArchChannel
import Cvs.WeilForm.OrganisingIdentityGreen
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.PolePrimeCosineMultipliers
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.StepQuadratureResidual
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Green Tail Cancellation, `shiftedAbelScaleSymbol`, and Two-Band Spectral Coercivity

Bounds `greenTailSymbol = greenMultiplier - greenSymbol`, proves it integrates to `0` against `rho φ`
on `formDomain hL`, and establishes `shiftedAbelScaleSymbol` and two-band spectral coercivity for `Qx`.
-/

noncomputable section

open Real Set Filter MeasureTheory Cvs.Zeta.Explicit.Weil
open scoped BigOperators InnerProductSpace NNReal ENNReal

namespace Cvs.WeilForm.GreenTailCancellation
open Cvs.ZeroCounting

/-! ### 1. `greenTailSymbol`, Lagrange Bound, and Global Floor on `archSymbol + greenSymbol` -/

/-- Tail difference `greenMultiplier t − greenSymbol L t` corresponding to `∫_{|v|>L} e^{-|v|/2} cos(t v) dv`. -/
def greenTailSymbol (L t : ℝ) : ℝ :=
  Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier t - Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t

/-! ### 2. Spectral Identities on `formDomain hL` and `shiftedAbelScaleSymbol` -/

/-- Truncated Green measure `exp(-|v| / 2) dv` on `(a, b]`. -/
def greenMeasure (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc a b)).withDensity fun v => ENNReal.ofReal (Real.exp (-|v| / 2))

instance (a b : ℝ) : IsFiniteMeasure (greenMeasure a b) :=
  isFiniteMeasure_withDensity_ofReal
    (((by fun_prop : Continuous fun v : ℝ => Real.exp (-|v| / 2)).integrableOn_Icc
      (a := a) (b := b)).mono_set Ioc_subset_Icc_self).2

/-- Integration against `greenMeasure a b`. -/
theorem integral_greenMeasure (a b : ℝ) (h : ℝ → ℝ) :
    ∫ v, h v ∂greenMeasure a b = ∫ v in Ioc a b, Real.exp (-|v| / 2) * h v := by
  have hm : Measurable fun v : ℝ => (Real.exp (-|v| / 2)).toNNReal :=
    (by fun_prop : Continuous fun v : ℝ => Real.exp (-|v| / 2)).measurable.real_toNNReal
  rw [greenMeasure, show (fun v : ℝ => ENNReal.ofReal (Real.exp (-|v| / 2)))
      = fun v => (((Real.exp (-|v| / 2)).toNNReal : ℝ≥0) : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]

/-- Cosine transform of `greenMeasure a b` for `a ≤ b`. -/
theorem integral_cos_greenMeasure {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    ∫ v, Real.cos (t * v) ∂greenMeasure a b
      = ∫ v in a..b, Real.exp (-|v| / 2) * Real.cos (t * v) := by
  rw [integral_greenMeasure, intervalIntegral.integral_of_le hab]

/-- `greenSymbol L` is the cosine transform of `greenMeasure (-L) L` for `0 ≤ L`. -/
theorem greenSymbol_eq_integral_greenMeasure {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t = ∫ v, Real.cos (t * v) ∂greenMeasure (-L) L := by
  have hc : ∀ a b : ℝ,
      IntervalIntegrable (fun v => Real.exp (-|v| / 2) * Real.cos (t * v)) volume a b :=
    fun a b => (by fun_prop : Continuous _).intervalIntegrable a b
  rw [integral_cos_greenMeasure (by linarith) t,
    ← intervalIntegral.integral_add_adjacent_intervals (hc (-L) 0) (hc 0 L)]
  have hpos : (∫ v in (0 : ℝ)..L, Real.exp (-|v| / 2) * Real.cos (t * v))
      = (1 / 2) * Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t := by
    rw [Cvs.WeilForm.StepQuadratureResidual.greenSymbol_eq_intervalIntegral L t, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le hL] at hv
    rw [abs_of_nonneg hv.1, neg_div]
    ring
  have hneg : (∫ v in (-L)..(0 : ℝ), Real.exp (-|v| / 2) * Real.cos (t * v))
      = (1 / 2) * Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t := by
    have heq : (∫ v in (-L)..(0 : ℝ), Real.exp (-|v| / 2) * Real.cos (t * v))
        = (1 / 2) * ∫ v in (-L)..(0 : ℝ), 2 * Real.exp (v / 2) * Real.cos (t * v) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le (by linarith : -L ≤ 0)] at hv
      rw [abs_of_nonpos hv.2, neg_neg]
      ring
    rw [heq, Cvs.WeilForm.AbelScaleSymbol.integral_two_mul_exp_half_cos]
    unfold Cvs.WeilForm.AbelScaleSymbol.meanCosAntideriv Cvs.WeilForm.AbelScaleSymbol.greenSymbol
    rw [show -L / 2 = -(L / 2) by ring, show t * -L = -(L * t) by ring,
      Real.cos_neg, Real.sin_neg]
    simp only [zero_div, Real.exp_zero, mul_zero, Real.cos_zero, Real.sin_zero]
    ring
  rw [hneg, hpos]
  ring

/-- `greenSymbol L * rho φ` is integrable on `formDomain hL`. -/
theorem integrable_greenSymbol_mul_rho {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  have h := Cvs.WeilForm.BandFreedomCosine.integrable_cosTransform_mul_crossSpec
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (greenMeasure (-L) L)
  refine h.congr (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [← greenSymbol_eq_integral_greenMeasure hL t, Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self]

/-- **Truncated Green Spectral Identity on `formDomain hL`**:
`windowGreenEnergy (rep φ) = ∫ t, greenSymbol L t * rho φ t`. -/
theorem windowGreenEnergy_rep_eq_integral_greenSymbol {L : ℝ} {hL : 0 ≤ L}
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.OrganisingIdentityGreen.windowGreenEnergy (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      = ∫ t, Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  set f := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hf1 : Integrable f := Cvs.WeilForm.TruncatedFormPolarised.integrable_rep _
  have hf2 : MemLp f 2 volume := Cvs.WeilForm.WindowRepresentative.memLp_rep _
  have hfs : ∀ x ∉ Icc 0 L, f x = 0 := Cvs.WeilForm.AdmissibleMultiplierMinorants.rep_eq_zero hL φ
  have hhab : L - 0 ≤ L := by linarith
  have hz : ∀ v ∉ Ioc (-L) L, Real.exp (-|v| / 2) * Cvs.WeilForm.TruncatedFormPolarised.polar f f v = 0 := fun v hv => by
    refine mul_eq_zero_of_right _ (Cvs.WeilForm.BandFreedomCosine.polar_eq_zero_of_support hfs hfs (hhab.trans ?_))
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hv
    rcases hv with h | h
    · exact (by linarith : L ≤ -v).trans (neg_le_abs v)
    · exact h.le.trans (le_abs_self v)
  have hpolar : ∀ v, Cvs.WeilForm.TruncatedFormPolarised.polar f f v = 2 * selfConvolution f v := fun v => by
    unfold Cvs.WeilForm.TruncatedFormPolarised.polar; rw [← Cvs.WeilForm.TruncatedFormPolarised.selfConvolution_eq_crossConv]; ring
  calc Cvs.WeilForm.OrganisingIdentityGreen.windowGreenEnergy f
      = (∫ v, Cvs.WeilForm.TruncatedFormPolarised.polar f f v ∂greenMeasure (-L) L) / 2 := by
        unfold Cvs.WeilForm.OrganisingIdentityGreen.windowGreenEnergy
        rw [integral_greenMeasure, setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← integral_div]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [hpolar v]
        ring
    _ = ∫ t, (∫ v, Real.cos (t * v) ∂greenMeasure (-L) L) * Cvs.L2a.FullTailPolarisation.crossSpec f f t :=
        (Cvs.WeilForm.BandFreedomCosine.integral_cosTransform_mul_crossSpec hf1 hf2 hf1 hf2 _).symm
    _ = ∫ t, Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        dsimp only
        rw [← greenSymbol_eq_integral_greenMeasure hL t, Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self]

/-- `greenSymbol L` and `greenMultiplier` have the exact same spectral integral on `formDomain hL`. -/
theorem integral_greenSymbol_mul_rho_eq_greenMultiplier {L : ℝ} {hL : 0 ≤ L}
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    (∫ t, Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = ∫ t, Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  rw [← windowGreenEnergy_rep_eq_integral_greenSymbol φ, Cvs.WeilForm.OrganisingIdentityGreen.windowGreenEnergy_rep_eq_spectral φ]

/-- `greenTailSymbol L * rho φ` is integrable on `formDomain hL`. -/
theorem integrable_greenTailSymbol_mul_rho {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => greenTailSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  refine ((Cvs.WeilForm.OrganisingIdentityGreen.integrable_greenMultiplier_mul_rho φ).sub (integrable_greenSymbol_mul_rho φ)).congr
    (Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, greenTailSymbol]
  ring

/-- **Band-Freedom of `greenTailSymbol` on `formDomain hL`**:
`∫ t, greenTailSymbol L t * rho φ t = 0`. -/
theorem integral_greenTailSymbol_mul_rho_eq_zero {L : ℝ} {hL : 0 ≤ L}
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    ∫ t, greenTailSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t = 0 := by
  have hsplit : (fun t => greenTailSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t)
      = fun t => Cvs.WeilForm.GreenRemovesFirstArchChannel.greenMultiplier t * Cvs.WeilForm.EvenBulkVisibility.rho φ t
          - Cvs.WeilForm.AbelScaleSymbol.greenSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
    funext t; unfold greenTailSymbol; ring
  rw [hsplit, integral_sub (Cvs.WeilForm.OrganisingIdentityGreen.integrable_greenMultiplier_mul_rho φ)
    (integrable_greenSymbol_mul_rho φ),
    integral_greenSymbol_mul_rho_eq_greenMultiplier φ, sub_self]

/-- `poleSymbol L * rho φ` is integrable on `formDomain hL`. -/
theorem integrable_poleSymbol_mul_rho {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Integrable fun t => Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  simpa only [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self] using Cvs.WeilForm.PolePrimeCosineMultipliers.integrable_poleSymbol_mul_crossSpec L
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))

/-- Spectral identity for `poleTerm` on `formDomain hL`:
`poleTerm (rep φ) = ∫ t, poleSymbol L t * rho φ t`. -/
theorem poleTerm_rep_eq_integral_poleSymbol {L : ℝ} {hL : 0 ≤ L} (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.PoleArchPrimeProblem.poleTerm (Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
      = ∫ t, Cvs.WeilForm.PolePrimeCosineMultipliers.poleSymbol L t * Cvs.WeilForm.EvenBulkVisibility.rho φ t := by
  set f := Cvs.WeilForm.WindowRepresentative.rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  have hp : Cvs.WeilForm.PoleArchPrimeProblem.poleTerm f = Cvs.WeilForm.TruncatedFormPolarised.poleF f * Cvs.WeilForm.TruncatedFormPolarised.poleG f + Cvs.WeilForm.TruncatedFormPolarised.poleF f * Cvs.WeilForm.TruncatedFormPolarised.poleG f := by
    unfold Cvs.WeilForm.PoleArchPrimeProblem.poleTerm Cvs.WeilForm.PoleArchPrimeProblem.Mplus Cvs.WeilForm.PoleArchPrimeProblem.Mminus Cvs.WeilForm.TruncatedFormPolarised.poleF Cvs.WeilForm.TruncatedFormPolarised.poleG
    ring
  rw [hp, Cvs.WeilForm.PolePrimeCosineMultipliers.pole_eq_integral_crossSpec
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.WindowRepresentative.memLp_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))
    (Cvs.WeilForm.AdmissibleMultiplierMinorants.rep_eq_zero hL φ) (Cvs.WeilForm.AdmissibleMultiplierMinorants.rep_eq_zero hL φ) (by linarith : L - 0 ≤ L)]
  exact integral_congr_ae (Eventually.of_forall fun t => by
    dsimp only; rw [Cvs.WeilForm.ThetaFormWindowIdentification.crossSpec_self])

/-- **Shifted Abel Scale Multiplier `shiftedAbelScaleSymbol x`**: replaces `archSymbol + greenSymbol`
in `abelScaleSymbol x` by the full-line `shiftedArchSymbol = archSymbol + greenMultiplier`. -/
def shiftedAbelScaleSymbol (x : ℕ) (t : ℝ) : ℝ :=
  Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol t - Cvs.WeilForm.StepQuadratureResidual.meanFreeOscSymbol (x - 1) t

/-- Pointwise identity `shiftedAbelScaleSymbol x t − abelScaleSymbol x t = greenTailSymbol (log x) t`. -/
theorem shiftedAbelScaleSymbol_sub_abelScaleSymbol_eq {x : ℕ} (hx : 1 ≤ x) (t : ℝ) :
    shiftedAbelScaleSymbol x t - Cvs.WeilForm.AbelScaleSymbol.abelScaleSymbol x t
      = greenTailSymbol (Real.log x) t := by
  unfold shiftedAbelScaleSymbol Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol greenTailSymbol
  rw [Cvs.WeilForm.StepQuadratureResidual.abelScaleSymbol_eq_arch_add_green_sub_osc hx t]
  ring

/-- `shiftedAbelScaleSymbol x * rho w` is integrable on `Dom x` (`1 ≤ x`). -/
theorem integrable_shiftedAbelScaleSymbol_mul_rho {x : ℕ} (hx : 1 ≤ x) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Integrable fun t => shiftedAbelScaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  refine ((Cvs.WeilForm.AbelScaleSymbol.integrable_abelScaleSymbol_mul_rho hx w).add
    (integrable_greenTailSymbol_mul_rho w)).congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, ← shiftedAbelScaleSymbol_sub_abelScaleSymbol_eq hx t]
  ring

/-- **Exact Spectral Identity for `shiftedAbelScaleSymbol`** (`1 ≤ x`): on `Dom x`,
`Qx x w = ∫ t, shiftedAbelScaleSymbol x t * rho w t`. -/
theorem Qx_eq_integral_shiftedAbelScaleSymbol {x : ℕ} (hx : 1 ≤ x) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.Route.WindowPositivityBulkCoupling.Qx x w = ∫ t, shiftedAbelScaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
  have hsplit : (fun t => shiftedAbelScaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t)
      = fun t => Cvs.WeilForm.AbelScaleSymbol.abelScaleSymbol x t * Cvs.WeilForm.EvenBulkVisibility.rho w t
          + greenTailSymbol (Real.log x) t * Cvs.WeilForm.EvenBulkVisibility.rho w t := by
    funext t
    rw [← shiftedAbelScaleSymbol_sub_abelScaleSymbol_eq hx t]
    ring
  rw [hsplit, integral_add (Cvs.WeilForm.AbelScaleSymbol.integrable_abelScaleSymbol_mul_rho hx w)
    (integrable_greenTailSymbol_mul_rho w),
    integral_greenTailSymbol_mul_rho_eq_zero w, add_zero,
    ← Cvs.WeilForm.AbelScaleSymbol.Qx_eq_integral_abelScaleSymbol hx w]

/-- **Universal Origin-Neighborhood Coercivity of `shiftedAbelScaleSymbol`**:
`(archSymbol 0 + 4) − totalMeanFreeSlope (x - 1) * |t| ≤ shiftedAbelScaleSymbol x t`. -/
theorem shiftedAbelScaleSymbol_ge_origin_sub_slope (x : ℕ) (t : ℝ) :
    (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 + 4) - Cvs.WeilForm.StepQuadratureResidual.totalMeanFreeSlope (x - 1) * |t|
      ≤ shiftedAbelScaleSymbol x t := by
  unfold shiftedAbelScaleSymbol
  have h1 := Cvs.WeilForm.GreenRemovesFirstArchChannel.shiftedArchSymbol_ge t
  have h2 : Cvs.WeilForm.StepQuadratureResidual.meanFreeOscSymbol (x - 1) t ≤ Cvs.WeilForm.StepQuadratureResidual.totalMeanFreeSlope (x - 1) * |t| :=
    (abs_le.mp (Cvs.WeilForm.StepQuadratureResidual.abs_meanFreeOscSymbol_le_lip (x - 1) t)).2
  linarith

/-! ### 3. Two-Band Spectral Coercivity (`Qx_ge_twoBand_of_symbol`) -/

end Cvs.WeilForm.GreenTailCancellation
