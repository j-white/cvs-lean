import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandCouplingDischarged
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.BandRungData
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandSumThreshold
import Cvs.L2a.BulkECouplingBound
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.FullSpanInstance
import Cvs.L2a.FullSpanProlateFamily
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.JointMainTerm
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TopCutCouplingBound
import Cvs.Prolate.Envelope.AngularEdgeEnvelope
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a-FULL on `Finset.range x` of the prolate family at `c = 2πx ≥ c₀^F`, from the scale alone
At a band rung `j`, `TopCutCouplingBound`'s top bound with `F_j = K_A|ψ_j(1)|` (Cvs.Prolate.Envelope.AngularEdgeEnvelope) gives `T = Ttop ≤ 10⁶F_jc^{−3/4}`, and
`BulkECouplingBound`'s resolvent bulk bound gives `|bulkE| ≤ (700F_j/c)√P`; Cvs.L2a.BandInputsFromCutMultipliers turns the two into `BandInputs x a 1`, and
`FullSpanInstance`'s instance at `K_r = 1` gives `κ_F ≥ 1/38`, `b̄ ≥ 1`, `b̄·N(M) ≤ W(M)` and `b̄·N_∞ ≤ W_∞`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.Upstream.CosineTransformDilation Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption Cvs.L2a.CleanBandDilation Cvs.L2a.DilationCornerSplit Cvs.L2a.CornerSplitSqrtFloor

namespace Cvs.L2a.FullSpanFromScale

open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev muR rung_spec psi_rung)
open Cvs.L2a.BandECouplingCollar (bandSetG gX chiX BandInputs)
open Cvs.L2a.BandInputsFromCutMultipliers (TopInput BulkInput fJ)

/-- **The span data at `c = 2πx ≥ 80`**: every rung is a smooth even solution of the angular equation at
`χ_i = lev c (2i)`, the levels are distinct and lie in `[0, c²)`, and each rung has mass on `(1, M)` for `M ≥ 3`. -/
theorem span_data {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    (∀ i : Finset.range x, 0 ≤ chiX x i) ∧ (∀ i : Finset.range x, chiX x i < (2 * π * x) ^ 2)
      ∧ Function.Injective (chiX x)
      ∧ ∀ M : ℕ, 3 ≤ M → ∀ i : Finset.range x, 0 < ∫ t in (1 : ℝ)..M, psi (2 * π * x) (gX x i) t ^ 2 := by
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hspec := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)
  refine ⟨Cvs.Prolate.RungFamilyRangePartners.lev_main_nonneg hx, fun i => ?_,
    Cvs.Prolate.RungFamilyRangePartners.lev_main_injective hx, fun M hM i => ?_⟩
  · have := Cvs.Prolate.RungFamilyRangePartners.sigmaLow_le_main hx i
    have := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (c := 2 * π * x) (by linarith)
    unfold chiX; linarith
  · have h3 := Cvs.Prolate.RungFamilyRangePartners.mass_main hx i
    have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    have hint : IntegrableOn (fun t => psi (2 * π * x) (gX x i) t ^ 2) (Ioi 1) :=
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hspec i).1 (hspec i).2.1 (hspec i).2.2.1 (hspec i).2.2.2.1
        hc0).integrable_sq
    refine lt_of_lt_of_le h3 (intervalIntegral.integral_mono_interval le_rfl (by norm_num) hM3
      (ae_of_all _ fun _ => sq_nonneg _) ?_)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      (hint.mono_set Ioc_subset_Ioi_self)

/-- **The top input** past `c₀^F`: at every `M ≥ 3` and band rung `j`, `|topE| ≤ Ttop·√P` (Cvs.L2a.TopCutCouplingBound) with
`Ttop ≤ 10⁶F_jc^{−3/4}` at `F_j = K_A|ψ_j(1)|`. -/
theorem topInput_closed {x : ℕ} (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) (a : Finset.range x → ℝ) :
    TopInput x a := by
  intro M hM j hj
  obtain ⟨hcE, hc80⟩ := Cvs.L2a.BandInputsFromCutMultipliers.scale_ge hx
  have hc6 : (10 : ℝ) ^ 6 ≤ 2 * π * x := le_trans (by norm_num) (Cvs.L2a.FullSpanProlateFamily.c80_le_exp.trans hcE)
  obtain ⟨hχ0, hχc, hχi, hmass⟩ := span_data hc80
  have hspec := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)
  obtain ⟨-, -, hband, hlam, henv, hG⟩ := Cvs.L2a.BandRungData.band_rung_data x hc80 j hj
  have hJ : (Fintype.card (Finset.range x) : ℝ) ≤ 2 * π * x / 4 + 1 := by
    simp only [Fintype.card_coe, Finset.card_range]
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    nlinarith [Real.pi_gt_three]
  have htop := Cvs.L2a.TopCutCouplingBound.topE_le (ι := Finset.range x) a
    (g₁ := fun i => rung₁ (2 * π * x) (2 * (i : ℕ))) (g₂ := fun i => rung₂ (2 * π * x) (2 * (i : ℕ)))
    (gj₁ := rung₁ (2 * π * x) (2 * (j : ℕ))) (gj₂ := rung₂ (2 * π * x) (2 * (j : ℕ)))
    (χj := chiX x j) (μj := muR (2 * π * x) (2 * (j : ℕ))) (F := fJ x j)
    (fun i => (hspec i).1) (fun i => (hspec i).2.1) (fun i => (hspec i).2.2.1) (fun i => (hspec i).2.2.2.1)
    hc6 hχ0 hχc hχi hJ (hmass M hM) (hspec j).1 (hspec j).2.1 (hspec j).2.2.1 (hspec j).2.2.2.1
    (hspec j).2.2.2.2.1 (hχ0 j) (hχc j) hband.le
    (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)) hlam henv hM
  refine ⟨Cvs.L2a.TopCutCouplingBound.Ttop (2 * π * x) (gX x j) (fJ x j), ?_, htop⟩
  have h := Cvs.L2a.TopCutCouplingBound.Ttop_le_band hc6 Cvs.Prolate.Envelope.AngularEdgeEnvelope.one_le_KA hG
  simpa only [fJ, mul_assoc] using h

/-- **The bulk input** past `c₀^F`: at every `M ≥ 3` and band rung `j`, `|bulkE| ≤ (700F_j/c)√P` (Cvs.L2a.BulkECouplingBound) with
`F_j = K_A|ψ_j(1)|`. -/
theorem bulkInput_closed {x : ℕ} (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) (a : Finset.range x → ℝ) :
    BulkInput x a := by
  intro M hM j hj
  obtain ⟨-, hc80⟩ := Cvs.L2a.BandInputsFromCutMultipliers.scale_ge hx
  obtain ⟨hχ0, hχc, hχi, -⟩ := span_data hc80
  have hspec := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)
  obtain ⟨-, -, -, -, henv, -⟩ := Cvs.L2a.BandRungData.band_rung_data x hc80 j hj
  have hgj : ContinuousOn (gX x j) (Icc (-1) 1) := fun s hs =>
    ((hspec j).1 s (by rwa [uIcc_of_le (by norm_num)])).continuousAt.continuousWithinAt
  exact Cvs.L2a.BulkECouplingBound.bulkE_le (ι := Finset.range x) a
    (g₁ := fun i => rung₁ (2 * π * x) (2 * (i : ℕ))) (g₂ := fun i => rung₂ (2 * π * x) (2 * (i : ℕ)))
    (fun i => (hspec i).1) (fun i => (hspec i).2.1) (fun i => (hspec i).2.2.1) (fun i => (hspec i).2.2.2.1)
    hc80 hχ0 hχc hχi hgj (hspec j).2.2.2.2.1 henv hM

/-- **`BandInputs x a 1`** past `c₀^F`, for every coefficient vector `a`. -/
theorem bandInputs_closed (x : ℕ) (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x) (a : Finset.range x → ℝ) :
    BandInputs x a 1 :=
  Cvs.L2a.BandInputsFromCutMultipliers.bandInputs_of_cuts hx (topInput_closed hx a) (bulkInput_closed hx a)

/-- **`BandInputs x a K_r`** past `c₀^F` for every `K_r ≥ 1`. -/
theorem bandInputs_closed_of_le (x : ℕ) (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x)
    (a : Finset.range x → ℝ) {Kr : ℝ} (hKr : 1 ≤ Kr) : BandInputs x a Kr :=
  Cvs.L2a.BandInputsFromCutMultipliers.bandInputs_mono hKr (bandInputs_closed x hx a)

/-- **L2a-FULL on `Finset.range x` of the prolate family**: at `c = 2πx ≥ c₀^F`, for every `a`, `κ_F ≥ 1/38`,
`b̄ ≥ 1`, `b̄·N(M) ≤ W(M)` for all `M ≥ 3` and `b̄·N_∞ ≤ W_∞`, with `ω = ω(1, c)` inside the E-coupling. -/
theorem L2a_full_span_closed (x : ℕ) (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x)
    (a : Finset.range x → ℝ) :
    let c := 2 * π * x
    let Φ := fun ξ => ∑ j, a j * psi c (rung c (2 * (j : ℕ))) ξ
    let κF := Cvs.L2a.FullSpanInstance.kappaFfullG (10 ^ 16) c x (7 * c ^ (-(1 / 8 : ℝ)))
      (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      (Cvs.L2a.BandCouplingDischarged.thetaBar
        (Cvs.L2a.BandSumThreshold.kapBarG c 10
          (Cvs.L2a.BandECouplingCollar.eMain c 10 * (1 + Cvs.L2a.BandECouplingCollar.omegaE 1 c) ^ 2))
        (Cvs.Prolate.PlungeMassTrace.plungeBound c))
      (Cvs.L2a.SpanPlungeBound.epsTauFlat 10) Cvs.L2a.JointMainTerm.RbarJ
    1 / 38 ≤ κF
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
      ∧ (∀ M : ℕ, 3 ≤ M →
          Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
              * ∫ y in Ioi 1, posTail Φ M y ^ 2
            ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
                (Cvs.L2a.TailLogScaleTest.logScale (posTail Φ M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
          * ∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail Φ y ^ 2
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf Φ :=
  Cvs.L2a.FullSpanInstance.L2a_full_span_instance x hx a zero_le_one (by norm_num) (bandInputs_closed x hx a)

end Cvs.L2a.FullSpanFromScale
