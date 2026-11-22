import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandCouplingDischarged
import Cvs.L2a.BandSumThreshold
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorBandCoupling
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullSpanConditional
import Cvs.L2a.FullSpanFrameFloor
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.FullSpanLowConstant
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.KappaUniformInX
import Cvs.L2a.LocalResidualDecay
import Cvs.L2a.LowConstantUniform
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RampCutSumsUniform
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.Mellin.FarPartLevelBound
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a-FULL on the full span `Finset.range x` of the prolate family at `c = 2πx`
The rungs `rung c (2j)`, `j < x`, carry L2a-FULL's structural hypotheses at `σ̲ = 4c/log c`; the partners
`rung c (2j + 1)` give `D̄ = plungeBound c`; Cvs.L2a.FullSpanThreshold gives `κ = κ⋆(κ₀)` at any floor `κ₀ ≤ 1/38`. A band rung
coupling with `κ̄·(log c − 2.64) ≤ K` gives an explicit `θ̄ ≤ T`; at `c₀^F` the margin holds for `K = 7/4`, at
`c₀(1/500)` for `K = 5/2`. Cauchy–Schwarz with the E-coupling gives `K = (√1.60947 + 2√E)²`. Landau's pivot is named.
-/

noncomputable section

open Real Set MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.EvenRungsByIndex

namespace Cvs.L2a.FullSpanProlateFamily

open Cvs.Prolate.EvenLevelIndexLemma (sigmaLow)
open Cvs.L2a.BandCouplingDischarged (thetaBar kapBar fBar RungCoupling ECoupling)
open Cvs.L2a.FullSpanThreshold (kapStarAt kapStarF B0At c0At c0F)

/-- The band of the span at `c = 2πx`: the indices `j < x` with `c² − lev c (2j) < 5c`. -/
def bandX (x : ℕ) : Finset (Finset.range x) :=
  Cvs.L2a.FullSpanFrameFloor.bandSet (2 * π * x) fun j : Finset.range x => lev (2 * π * x) (2 * (j : ℕ))

/-- The span profile `Φ = Σ_j a_j ψ(g_j)` at `c = 2πx`. -/
def phiX (x : ℕ) (a : Finset.range x → ℝ) (ξ : ℝ) : ℝ :=
  ∑ j, a j * psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ

/-- The span has exactly `x` rungs. -/
theorem card_range (x : ℕ) : Fintype.card (Finset.range x) = x := by
  rw [Fintype.card_coe, Finset.card_range]

/-- `x ≤ 2πx/4 + 1`. -/
theorem x_le (x : ℕ) : ((x : ℕ) : ℝ) ≤ 2 * π * x / 4 + 1 := by
  have := Cvs.Prolate.RungFamilyRangePartners.card_range_le x
  rwa [card_range] at this

/-! ### The threshold `c₀(κ₀)` is antitone in the floor -/

/-- `Ē_full ≥ 0`. -/
theorem EbarFull_nonneg : 0 ≤ Cvs.L2a.FullSpanLowConstant.EbarFull := by
  unfold Cvs.L2a.FullSpanLowConstant.EbarFull; positivity

/-- `κ⋆(κ₁) ≤ κ⋆(κ₀)` for `0 < κ₀ ≤ κ₁`. -/
theorem kapStarAt_anti {κ₀ κ₁ : ℝ} (h0 : 0 < κ₀) (h : κ₀ ≤ κ₁) : kapStarAt κ₁ ≤ kapStarAt κ₀ :=
  max_le_max le_rfl (div_le_div_of_nonneg_left (by have := EbarFull_nonneg; linarith) h0 h)

/-- `B₀(κ₁) ≤ B₀(κ₀)` for `0 < κ₀ ≤ κ₁`. -/
theorem B0At_anti {κ₀ κ₁ : ℝ} (h0 : 0 < κ₀) (h : κ₀ ≤ κ₁) : B0At κ₁ ≤ B0At κ₀ := by
  have h1 : √(1 / (16 * κ₁)) ≤ √(1 / (16 * κ₀)) :=
    Real.sqrt_le_sqrt (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hL := add_nonneg Cvs.L2a.RampCutSumsUniform.LambdaBar0_nonneg Cvs.L2a.KappaUniformInX.kappaBar_nonneg
  have h2 : 63 / 40 * (Cvs.L2a.RampCutSumsUniform.LambdaBar0 + Cvs.L2a.KappaUniformInX.kappaBar) / κ₁
      ≤ 63 / 40 * (Cvs.L2a.RampCutSumsUniform.LambdaBar0 + Cvs.L2a.KappaUniformInX.kappaBar) / κ₀ :=
    div_le_div_of_nonneg_left (by positivity) h0 h
  have h3 := mul_le_mul_of_nonneg_left h1
    (by positivity : (0 : ℝ) ≤ 4 * √(24 * Cvs.Prolate.Mellin.FarPartLevelBound.Cbar 80 Cvs.L2a.LowConstantUniform.rBarF ^ 2 / π))
  unfold B0At
  linarith

/-- `c₀(κ₁) ≤ c₀(κ₀)` for `0 < κ₀ ≤ κ₁`. -/
theorem c0At_anti {κ₀ κ₁ : ℝ} (h0 : 0 < κ₀) (h : κ₀ ≤ κ₁) : c0At κ₁ ≤ c0At κ₀ := by
  unfold c0At
  refine max_le_max (max_le_max le_rfl (div_le_div_of_nonneg_left (by norm_num) h0 h)) ?_
  have hk := kapStarAt_anti h0 h
  have hk2 : (2 : ℝ) ≤ kapStarAt κ₁ := le_max_left _ _
  have hsq : kapStarAt κ₁ ^ 2 ≤ kapStarAt κ₀ ^ 2 := pow_le_pow_left₀ (by linarith) hk 2
  have he : exp (4 * B0At κ₁ + 4) ≤ exp (4 * B0At κ₀ + 4) := Real.exp_le_exp.2 (by linarith [B0At_anti h0 h])
  have := mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 16)) he (Real.exp_pos _).le
    (by positivity)
  exact this

/-- `c₀^F ≤ c₀(κ₀)` for `0 < κ₀ ≤ 1/38`. -/
theorem c0F_le_c0At {κ₀ : ℝ} (h0 : 0 < κ₀) (h : κ₀ ≤ 1 / 38) : c0F ≤ c0At κ₀ :=
  Cvs.L2a.FullSpanThreshold.c0F_eq ▸ c0At_anti h0 h

/-- `c₀(κ₀) ≤ c` forces `10¹⁶ ≤ c`. -/
theorem c16_le_c0At {κ₀ c : ℝ} (hc : c0At κ₀ ≤ c) : (10 : ℝ) ^ 16 ≤ c :=
  le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc

/-! ### L2a-FULL on the span at a floor `κ₀` -/

/-- **L2a-FULL on `Finset.range x` at floor `κ₀`**: for `κ₀ > 0`, `c₀(κ₀) ≤ 2πx`, Landau's lower pivot at `2x − 1`,
a rung coupling `κ̄ ≥ 0` on the band, `resLoc ≤ ρ` and `ρ + rSig(σ̲(c₁)) + θ̄ + κ₀ + (7/500)√κ₀ ≤ 153/1000`: the
four conclusions of L2a-FULL with `κ = κ⋆(κ₀)`, and `κ_full ≥ κ₀`, `T ≥ 2`, `b̄ ≥ 1`. -/
theorem L2a_full_span_at (x : ℕ) {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (hx : c0At κ₀ ≤ 2 * π * x)
    (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1)) (a : Finset.range x → ℝ)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc (2 * π * x) x M ≤ ρ)
    {κb : ℝ} (hκb : 0 ≤ κb)
    (hRC : RungCoupling (2 * π * x) (fun j : Finset.range x => rung (2 * π * x) (2 * (j : ℕ))) a (bandX x)
      Cvs.L2a.FarIntegrationByParts.wF κb)
    {c₁ : ℝ} (hc₁ : 10 ^ 16 ≤ c₁) (hc : c₁ ≤ 2 * π * x)
    (hm : ρ + Cvs.L2a.FullSpanConditional.rSig (sigmaLow c₁)
      + thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)) + κ₀ + 7 / 500 * √κ₀ ≤ 153 / 1000) :
    κ₀ ≤ Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
            (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
              (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
                (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
            * (∫ y in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
              (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
          * (∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail (phiX x a) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (phiX x a)
      ∧ 2 ≤ Cvs.L2a.FullTailDeepSpan.TL (2 * π * x) (kapStarAt κ₀)
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
              (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))) := by
  classical
  set c : ℝ := 2 * π * x with hcdef
  set θ := thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound c) with hθ
  have hc16 : (10 : ℝ) ^ 16 ≤ c := c16_le_c0At hx
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hc1 : (1 : ℝ) ≤ c := le_trans (by norm_num) hc16
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc16
  have hspec := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)
  have hspec' := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j)
  have hJx : ((x : ℕ) : ℝ) ≤ c / 4 + 1 := x_le x
  have hJ : (Fintype.card (Finset.range x) : ℝ) ≤ c / 4 + 1 := by rw [card_range]; exact hJx
  have hρ' : ∀ M : ℕ, 3 ≤ M →
      Cvs.L2a.FrameFloorIntegerM.resLoc c (Fintype.card (Finset.range x)) M ≤ ρ := by
    rw [card_range]; exact hρ
  -- the strip term at `σ̲(c)` against `rSig(σ̲(c₁))`
  have hσ0 := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (c := c) (by linarith)
  have hrS : Cvs.L2a.MiddlePartQStep.rStrip c (sigmaLow c) ≤ Cvs.L2a.FullSpanConditional.rSig (sigmaLow c₁) :=
    (Cvs.L2a.FullSpanConditional.rStrip_le_rSig hc0 hσ0 (Cvs.L2a.FullSpanIndexFloor.sigmaLow_le_five hc80)).trans
      (Cvs.L2a.FullSpanIndexFloor.rSig_sigmaLow_anti (Cvs.L2a.FullSpanIndexFloor.exp_one_le_c16.trans hc₁) hc)
  have hfl := Cvs.L2a.FullSpanThreshold.kappaFfull_ge_floor (J := (x : ℝ)) (ρ := ρ) (σ₀ := sigmaLow c) (θ := θ)
    hc16 (Nat.cast_nonneg _) hJx hκ₀.le (by linarith)
  obtain ⟨hT, hb1⟩ := Cvs.L2a.FullSpanThreshold.bBarFull_ge_one_at (J := (x : ℝ)) hκ₀ hx (Nat.cast_nonneg _) hJx hfl
  have hκ1 : (1 : ℝ) ≤ kapStarAt κ₀ := le_trans (by norm_num) (le_max_left _ _)
  have hs : 0 < √κ₀ := Real.sqrt_pos.2 hκ₀
  -- the paired plunge deficit on the band
  have hD := Cvs.L2a.BandCouplingDischarged.sum_one_sub_le_plunge_paired (ι := Finset.range x) (bandX x) hc1
    (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (h := fun j : Finset.range x => rung c (2 * (j : ℕ) + 1))
    (h₁ := fun j => rung₁ c (2 * (j : ℕ) + 1)) (h₂ := fun j => rung₂ c (2 * (j : ℕ) + 1))
    (χ := fun j => lev c (2 * (j : ℕ))) (χ' := fun j => lev c (2 * (j : ℕ) + 1))
    (μ := fun j => muR c (2 * (j : ℕ))) (μ' := fun j => muR c (2 * (j : ℕ) + 1))
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    (fun j => (hspec' j).1) (fun j => (hspec' j).2.1) (fun j => (hspec' j).2.2.1)
    (fun j => (hspec' j).2.2.2.1)
    ((Cvs.Prolate.RungFamilyRangePartners.lev_main_injective hc80).injOn)
    ((Cvs.Prolate.RungFamilyRangePartners.lev_partner_injective hL).injOn)
    (fun i _ j _ => Cvs.Prolate.RungFamilyRangePartners.lev_main_ne_partner hc80 hL i j)
    (fun j _ => (hspec j).2.2.2.2.1) (fun j _ => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j _ => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j _ => (hspec' j).2.2.2.2.1) (fun j _ => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j))
    (fun j _ => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j))
    (fun j _ => Cvs.Prolate.RungFamilyRangePartners.lev_le_partner hL j)
    (fun j _ => Cvs.Prolate.RungFamilyRangePartners.half_le_lam_partner hc80 hL j)
  -- (BC) on the band
  have hBC := Cvs.L2a.BandCouplingDischarged.bandCoupling_band (ι := Finset.range x) a
    (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := fun j => lev c (2 * (j : ℕ)))
    (μ := fun j => muR c (2 * (j : ℕ)))
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    hc0 (Cvs.Prolate.RungFamilyRangePartners.lev_main_injective hc80) (fun j => (hspec j).2.2.2.2.1)
    (fun j => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (Cvs.Prolate.RungFamilyRangePartners.even_ncard_main hc80) (Cvs.Prolate.RungFamilyRangePartners.mass_main hc80) hL
    (fun j _ => Cvs.Prolate.RungFamilyRangePartners.ncard_main_le hc80 j) hκb hRC hD
  have H := Cvs.L2a.FullSpanIndexFloor.L2a_fulltail_full_span_sigmaLow (ι := Finset.range x) a
    (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := fun j => lev c (2 * (j : ℕ)))
    (μ := fun j => muR c (2 * (j : ℕ))) (κ := kapStarAt κ₀)
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    hc₁ hc (Cvs.Prolate.RungFamilyRangePartners.lev_main_nonneg hc80) (Cvs.Prolate.RungFamilyRangePartners.sigmaLow_le_main hc80)
    (Cvs.Prolate.RungFamilyRangePartners.lev_main_injective hc80) (fun j => (hspec j).2.2.2.2.1)
    (fun j => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (Cvs.Prolate.RungFamilyRangePartners.even_ncard_main hc80) hJ (Cvs.Prolate.RungFamilyRangePartners.mass_main hc80) hρ' hBC
    (by nlinarith) hκ1 hT
  rw [card_range] at H
  obtain ⟨-, -, h2, h3⟩ := H
  exact ⟨hfl, h2, h3, hT, hb1⟩

/-- **The rung coupling on the band from the E-coupling**: on `bandX x` the levels satisfy `0 ≤ χ < c²` and
`c² − χ ≤ 5c`, so `BandCouplingDischarged`'s arm turns an E-coupling `ē ≥ 0` into the rung coupling `κ̄ = (√f̄ + 2√ē)²`. -/
theorem rungCoupling_of_E {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Finset.range x → ℝ)
    {e : ℝ} (he : 0 ≤ e)
    (hE : ECoupling (2 * π * x) (fun j : Finset.range x => rung (2 * π * x) (2 * (j : ℕ))) a (bandX x) e) :
    RungCoupling (2 * π * x) (fun j : Finset.range x => rung (2 * π * x) (2 * (j : ℕ))) a (bandX x)
      Cvs.L2a.FarIntegrationByParts.wF (kapBar (2 * π * x) e) := by
  classical
  have hspec := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hx j)
  have hσ := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (c := 2 * π * x) (by linarith)
  exact Cvs.L2a.BandCouplingDischarged.rungCoupling_of_eCoupling (ι := Finset.range x) a (bandX x)
    (g₁ := fun j => rung₁ (2 * π * x) (2 * (j : ℕ))) (g₂ := fun j => rung₂ (2 * π * x) (2 * (j : ℕ)))
    (χ := fun j => lev (2 * π * x) (2 * (j : ℕ)))
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    hx (fun j _ => Cvs.Prolate.RungFamilyRangePartners.lev_main_nonneg hx j)
    (fun j _ => by have := Cvs.Prolate.RungFamilyRangePartners.sigmaLow_le_main hx j; linarith)
    (fun j hj => by
      unfold bandX Cvs.L2a.FullSpanFrameFloor.bandSet at hj
      exact (Finset.mem_filter.1 hj).2.le)
    he hE

/-! ### `θ̄` as an elementary bound in `L = log c` -/

/-- **`θ̄ ≤ T` from a normalised coupling**: for `κ ≥ 0`, `L ≥ 1360`, `κ·(L − 2.64) ≤ K`,
`D ≤ (L/2 + 1.85)/π²` and `(3 − 2√2)·K·0.502336 ≤ T²π²`, `θ̄(κ, D) ≤ T`. -/
theorem thetaBar_le_of_K {κ D L K T : ℝ} (hκ0 : 0 ≤ κ) (hT : 0 ≤ T) (hL : 1360 ≤ L)
    (hκs : κ * (L - 264 / 100) ≤ K) (hD : D ≤ (L / 2 + 185 / 100) / π ^ 2)
    (hnum : (3 - 2 * √2) * K * (502336 / 1000000) ≤ T ^ 2 * π ^ 2) :
    thetaBar κ D ≤ T := by
  set s := L - 264 / 100 with hsd
  have hs0 : 0 < s := by linarith
  have hK0 : 0 ≤ K := le_trans (mul_nonneg hκ0 hs0.le) hκs
  have hq0 := Cvs.L2a.BandCouplingDischarged.two_q_nonneg
  have hq : 2 * ((3 - 2 * √2) / 2) = 3 - 2 * √2 := by ring
  have hπ0 : 0 < π ^ 2 := by positivity
  have hD0 : D * π ^ 2 ≤ L / 2 + 185 / 100 := by rwa [le_div_iff₀ hπ0] at hD
  have hLs : L / 2 + 185 / 100 ≤ 502336 / 1000000 * s := by rw [hsd]; linarith
  rw [hq] at hq0
  have key : 2 * ((3 - 2 * √2) / 2) * (κ * D) * (s * π ^ 2) ≤ T ^ 2 * (s * π ^ 2) := by
    have e1 : 2 * ((3 - 2 * √2) / 2) * (κ * D) * (s * π ^ 2)
        = (3 - 2 * √2) * (κ * s) * (D * π ^ 2) := by rw [hq]; ring
    rw [e1]
    rcases le_or_gt (D * π ^ 2) 0 with hDn | hDn
    · have : 0 ≤ (3 - 2 * √2) * (κ * s) := mul_nonneg hq0 (mul_nonneg hκ0 hs0.le)
      have := mul_nonpos_of_nonneg_of_nonpos this hDn
      have : 0 ≤ T ^ 2 * (s * π ^ 2) := by positivity
      linarith
    · calc (3 - 2 * √2) * (κ * s) * (D * π ^ 2)
          ≤ (3 - 2 * √2) * K * (L / 2 + 185 / 100) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hκs hq0) hD0 hDn.le (mul_nonneg hq0 hK0)
        _ ≤ (3 - 2 * √2) * K * (502336 / 1000000 * s) :=
            mul_le_mul_of_nonneg_left hLs (mul_nonneg hq0 hK0)
        _ = (3 - 2 * √2) * K * (502336 / 1000000) * s := by ring
        _ ≤ T ^ 2 * π ^ 2 * s := mul_le_mul_of_nonneg_right hnum hs0.le
        _ = T ^ 2 * (s * π ^ 2) := by ring
  have hfin : 2 * ((3 - 2 * √2) / 2) * (κ * D) ≤ T ^ 2 :=
    le_of_mul_le_mul_right key (by positivity)
  unfold thetaBar
  exact Real.sqrt_le_iff.2 ⟨hT, hfin⟩

/-- **The Cauchy–Schwarz arm, normalised**: `f·s ≤ F` and `e·s ≤ E` give `(√f + 2√e)²·s ≤ (√F + 2√E)²`. -/
theorem arm_mul_le {f e s F E : ℝ} (hf : 0 ≤ f) (he : 0 ≤ e) (hs : 0 ≤ s) (hfs : f * s ≤ F)
    (hes : e * s ≤ E) : (√f + 2 * √e) ^ 2 * s ≤ (√F + 2 * √E) ^ 2 := by
  have hss := Real.sq_sqrt hs
  have ha : √f * √s ≤ √F := by rw [← Real.sqrt_mul hf]; exact Real.sqrt_le_sqrt hfs
  have hb : √e * √s ≤ √E := by rw [← Real.sqrt_mul he]; exact Real.sqrt_le_sqrt hes
  have hx : 0 ≤ (√f + 2 * √e) * √s := by positivity
  have hy : (√f + 2 * √e) * √s ≤ √F + 2 * √E := by nlinarith
  calc (√f + 2 * √e) ^ 2 * s = ((√f + 2 * √e) * √s) ^ 2 := by rw [mul_pow, hss]
    _ ≤ (√F + 2 * √E) ^ 2 := pow_le_pow_left₀ hx hy 2

/-- **`f̄·(log c − 2.64) ≤ 1.60947`** for `c ≥ 10²⁰`, `log c ≥ 1360`: `δ_c(3/2) ≤ 10⁻⁹`, `2k(2, 5) ≤ 2.64`. -/
theorem fBar_mul_le {c : ℝ} (hc : 10 ^ 20 ≤ c) (hL : 1360 ≤ Real.log c) :
    fBar c * (Real.log c - 264 / 100) ≤ 160947 / 100000 := by
  have hc0 : 0 < c := by linarith
  have hδ := Cvs.L2a.BandSumThreshold.deltaC_three_halves_le (c := c) (by linarith)
  have hδ0 := Cvs.L2a.BandCouplingDischarged.deltaC_three_halves_nonneg (c := c) (by linarith)
  have hk : Cvs.Prolate.BandMassLaw.twoK c 2 5 ≤ 264 / 100 :=
    (Cvs.Prolate.BandMassLaw.twoK_mono hc0 two_pos (by norm_num : (5 : ℝ) ≤ 10)).trans
      (Cvs.L2a.BandSumThreshold.twoK_two_ten_le (by linarith))
  have hl : Real.log c ≤ Real.log (1 + c) := Real.log_le_log hc0 (by linarith)
  have hs : 0 < Real.log c - 264 / 100 := by linarith
  have hden : Real.log c - 264 / 100 ≤ Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 5 := by linarith
  have h5 := Real.log_five_lt_d9
  have h5' : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hnum : Real.log 5 * (1 + Cvs.Prolate.BandMassLaw.deltaC c (3 / 2)) ≤ 160947 / 100000 := by
    norm_num at h5 ⊢; nlinarith
  have hn0 : 0 ≤ Real.log 5 * (1 + Cvs.Prolate.BandMassLaw.deltaC c (3 / 2)) := by positivity
  unfold fBar
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  calc Real.log 5 * (1 + Cvs.Prolate.BandMassLaw.deltaC c (3 / 2)) * (Real.log c - 264 / 100)
      ≤ 160947 / 100000 * (Real.log c - 264 / 100) := mul_le_mul_of_nonneg_right hnum hs.le
    _ ≤ 160947 / 100000 * (Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 5) :=
        mul_le_mul_of_nonneg_left hden (by norm_num)

/-- **`κ̄(c, ē)·(log c − 2.64) ≤ (√1.60947 + 2√E)²`** for `c ≥ 10²⁰`, `log c ≥ 1360`, `ē·(log c − 2.64) ≤ E`. -/
theorem kapBar_mul_le {c e E : ℝ} (hc : 10 ^ 20 ≤ c) (hL : 1360 ≤ Real.log c) (he : 0 ≤ e)
    (hes : e * (Real.log c - 264 / 100) ≤ E) :
    kapBar c e * (Real.log c - 264 / 100) ≤ (√(160947 / 100000) + 2 * √E) ^ 2 :=
  arm_mul_le (Cvs.L2a.BandCouplingDischarged.fBar_nonneg (by linarith)) he (by linarith) (fBar_mul_le hc hL) hes

/-- `10⁸⁰ ≤ e^{1360}`. -/
theorem c80_le_exp : (10 : ℝ) ^ 80 ≤ Real.exp 1360 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have e : Real.exp 1360 = Real.exp 1 ^ 1360 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc (10 : ℝ) ^ 80 ≤ 16 ^ 80 := pow_le_pow_left₀ (by norm_num) (by norm_num) 80
    _ = 2 ^ 320 := by rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
    _ ≤ 2 ^ 1360 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ ≤ Real.exp 1 ^ 1360 := pow_le_pow_left₀ (by norm_num) h2 _

/-- Past `c₀(κ₀)`, `κ₀ ≤ 1/38`: `c ≥ 10⁸⁰` and `log c ≥ 1360`. -/
theorem c_facts {κ₀ c : ℝ} (h0 : 0 < κ₀) (h : κ₀ ≤ 1 / 38) (hc : c0At κ₀ ≤ c) :
    (10 : ℝ) ^ 80 ≤ c ∧ 1360 ≤ Real.log c := by
  have h1 := (Cvs.L2a.FullSpanThreshold.c0F_bounds.1.trans (c0F_le_c0At h0 h)).trans hc
  refine ⟨c80_le_exp.trans h1, ?_⟩
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h1)]
  exact h1

/-! ### L2a-FULL from a normalised rung coupling -/

/-- **L2a-FULL on `Finset.range x` from a rung coupling with `κ̄·(log c − 2.64) ≤ K`**: for `0 < κ₀ ≤ 1/38`,
`c₀(κ₀) ≤ c = 2πx`, Landau's pivot at `2x − 1`, `resLoc ≤ ρ`, `(3 − 2√2)K·0.502336 ≤ T²π²` and
`ρ + rSig(σ̲(c)) + T + κ₀ + (7/500)√κ₀ ≤ 153/1000`: the conclusions of `L2a_full_span_at`. -/
theorem L2a_full_span_of_K (x : ℕ) {κ₀ K T : ℝ} (hκ₀ : 0 < κ₀) (hκ₀38 : κ₀ ≤ 1 / 38)
    (hx : c0At κ₀ ≤ 2 * π * x)
    (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1)) (a : Finset.range x → ℝ)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc (2 * π * x) x M ≤ ρ)
    {κb : ℝ} (hκb : 0 ≤ κb)
    (hRC : RungCoupling (2 * π * x) (fun j : Finset.range x => rung (2 * π * x) (2 * (j : ℕ))) a (bandX x)
      Cvs.L2a.FarIntegrationByParts.wF κb)
    (hκs : κb * (Real.log (2 * π * x) - 264 / 100) ≤ K) (hT : 0 ≤ T)
    (hnum : (3 - 2 * √2) * K * (502336 / 1000000) ≤ T ^ 2 * π ^ 2)
    (hm : ρ + Cvs.L2a.FullSpanConditional.rSig (sigmaLow (2 * π * x)) + T + κ₀ + 7 / 500 * √κ₀ ≤ 153 / 1000) :
    κ₀ ≤ Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
            (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
              (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
                (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
            * (∫ y in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
              (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
          * (∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail (phiX x a) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (phiX x a)
      ∧ 2 ≤ Cvs.L2a.FullTailDeepSpan.TL (2 * π * x) (kapStarAt κ₀)
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
              (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))) := by
  obtain ⟨hc80, hlog⟩ := c_facts hκ₀ hκ₀38 hx
  have hθ := thetaBar_le_of_K hκb hT hlog hκs
    (Cvs.L2a.BandSumThreshold.plungeBound_le_log (le_trans (by norm_num) hc80)) hnum
  exact L2a_full_span_at x hκ₀ hx hL a hρ hκb hRC (c16_le_c0At hx) le_rfl (by linarith)

/-- **L2a-FULL on `Finset.range x` from the E-coupling**: `L2a_full_span_of_K` at the Cauchy–Schwarz coupling
`κ̄ = (√f̄ + 2√ē)²` with `ē·(log c − 2.64) ≤ E`, i.e. at `K = (√1.60947 + 2√E)²`. -/
theorem L2a_full_span_of_E (x : ℕ) {κ₀ E T : ℝ} (hκ₀ : 0 < κ₀) (hκ₀38 : κ₀ ≤ 1 / 38) (hx : c0At κ₀ ≤ 2 * π * x)
    (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1)) (a : Finset.range x → ℝ)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc (2 * π * x) x M ≤ ρ)
    {e : ℝ} (he : 0 ≤ e)
    (hE : ECoupling (2 * π * x) (fun j : Finset.range x => rung (2 * π * x) (2 * (j : ℕ))) a (bandX x) e)
    (hes : e * (Real.log (2 * π * x) - 264 / 100) ≤ E) (hT : 0 ≤ T)
    (hnum : (3 - 2 * √2) * (√(160947 / 100000) + 2 * √E) ^ 2 * (502336 / 1000000) ≤ T ^ 2 * π ^ 2)
    (hm : ρ + Cvs.L2a.FullSpanConditional.rSig (sigmaLow (2 * π * x)) + T + κ₀ + 7 / 500 * √κ₀ ≤ 153 / 1000) :
    κ₀ ≤ Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
            (thetaBar (kapBar (2 * π * x) e) (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
              (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
                (thetaBar (kapBar (2 * π * x) e) (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
            * (∫ y in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
              (thetaBar (kapBar (2 * π * x) e) (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
          * (∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail (phiX x a) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (phiX x a)
      ∧ 2 ≤ Cvs.L2a.FullTailDeepSpan.TL (2 * π * x) (kapStarAt κ₀)
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt κ₀) x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x ρ (sigmaLow (2 * π * x))
              (thetaBar (kapBar (2 * π * x) e) (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))) := by
  obtain ⟨hc80, hlog⟩ := c_facts hκ₀ hκ₀38 hx
  exact L2a_full_span_of_K x hκ₀ hκ₀38 hx hL a hρ (Cvs.L2a.BandCouplingDischarged.kapBar_nonneg _ e)
    (rungCoupling_of_E (le_trans (by norm_num) (c16_le_c0At hx)) a he hE)
    (kapBar_mul_le (le_trans (by norm_num) hc80) hlog he hes) hT (by linarith) hm

/-! ### The instances at `c₀^F` and at `c₀(1/500)` -/

/-- `3 − 2√2 ≤ 0.171573`. -/
theorem three_sub_le : 3 - 2 * √2 ≤ (171573 / 1000000 : ℝ) := by
  have hr2 : (14142135 / 10000000 : ℝ) ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  linarith

/-- `π² ≥ 3.141592²`. -/
theorem pi_sq_ge : (3141592 / 1000000 : ℝ) ^ 2 ≤ π ^ 2 :=
  pow_le_pow_left₀ (by norm_num) (by have := Real.pi_gt_d6; norm_num at this ⊢; linarith) 2

/-- The numeric side at `K = 7/4`, `T = 0.1237`. -/
theorem hnum_c0F : (3 - 2 * √2) * (7 / 4) * (502336 / 1000000) ≤ (1237 / 10000 : ℝ) ^ 2 * π ^ 2 := by
  have h := three_sub_le
  have hπ := pi_sq_ge
  nlinarith

/-- The numeric side at `K = 5/2`, `T = 0.1478`. -/
theorem hnum_wide : (3 - 2 * √2) * (5 / 2) * (502336 / 1000000) ≤ (1478 / 10000 : ℝ) ^ 2 * π ^ 2 := by
  have h := three_sub_le
  have hπ := pi_sq_ge
  nlinarith

/-- **The margin at `T = 0.1237`, `κ₀ = 1/38`**: for `c ≥ 10⁸⁰` and `ρ ≤ 7c^{−1/8}`, the sum is `≤ 0.15229`. -/
theorem margin_c0F {c ρ : ℝ} (hc : 10 ^ 80 ≤ c) (hρ : ρ ≤ 7 * c ^ (-(1 / 8 : ℝ))) :
    ρ + Cvs.L2a.FullSpanConditional.rSig (sigmaLow c) + 1237 / 10000 + 1 / 38 + 7 / 500 * √(1 / 38)
      ≤ 153 / 1000 := by
  have h1 := Cvs.L2a.BandSumThreshold.rho_le hc
  have h2 := Cvs.L2a.BandSumThreshold.rSig_sigmaLow_le hc
  have h3 : √(1 / 38 : ℝ) ≤ 162222 / 1000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  norm_num at h1 h2 h3 ⊢
  linarith

/-- **The margin at `T = 0.1478`, `κ₀ = 1/500`**: for `c ≥ 10⁸⁰` and `ρ ≤ 7c^{−1/8}`, the sum is `≤ 0.15043`. -/
theorem margin_wide {c ρ : ℝ} (hc : 10 ^ 80 ≤ c) (hρ : ρ ≤ 7 * c ^ (-(1 / 8 : ℝ))) :
    ρ + Cvs.L2a.FullSpanConditional.rSig (sigmaLow c) + 1478 / 10000 + 1 / 500 + 7 / 500 * √(1 / 500)
      ≤ 153 / 1000 := by
  have h1 := Cvs.L2a.BandSumThreshold.rho_le hc
  have h2 := Cvs.L2a.BandSumThreshold.rSig_sigmaLow_le hc
  have h3 : √(1 / 500 : ℝ) ≤ 44722 / 1000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  norm_num at h1 h2 h3 ⊢
  linarith

/-- The residual level `ρ(c) = 7c^{−1/8}`. -/
def rhoX (x : ℕ) : ℝ := 7 * (2 * π * x) ^ (-(1 / 8 : ℝ))

/-- **`resLoc ≤ 7c^{−1/8}` on the span** (Cvs.L2a.LocalResidualDecay): `J = x ≤ c/4 + 1` at `c = 2πx ≥ 10¹⁶`. -/
theorem resLoc_le_rhoX {x : ℕ} (hx : 10 ^ 16 ≤ 2 * π * x) :
    ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc (2 * π * x) x M ≤ rhoX x := fun _ hM =>
  Cvs.L2a.LocalResidualDecay.resLoc_le_decay hx (Nat.cast_nonneg _) (x_le x) hM

/-- **L2a-FULL on `Finset.range x` of the prolate family at `c = 2πx ≥ c₀^F`**: for Landau's pivot at `2x − 1` and
a rung coupling `κ̄ ≥ 0` on the band with `κ̄·(log c − 2.64) ≤ 7/4`: `κ_full ≥ 1/38` at `ρ = 7c^{−1/8}`, the two
L2a-FULL inequalities with `κ = κ⋆_F`, `T ≥ 2` and `b̄ ≥ 1`. -/
theorem L2a_full_span_c0F (x : ℕ) (hx : c0F ≤ 2 * π * x)
    (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1)) (a : Finset.range x → ℝ)
    {κb : ℝ} (hκb : 0 ≤ κb)
    (hRC : RungCoupling (2 * π * x) (fun j : Finset.range x => rung (2 * π * x) (2 * (j : ℕ))) a (bandX x)
      Cvs.L2a.FarIntegrationByParts.wF κb)
    (hκs : κb * (Real.log (2 * π * x) - 264 / 100) ≤ 7 / 4) :
    1 / 38 ≤ Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x (rhoX x) (sigmaLow (2 * π * x))
            (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) kapStarF x
              (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x (rhoX x) (sigmaLow (2 * π * x))
                (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
            * (∫ y in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) kapStarF x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x (rhoX x) (sigmaLow (2 * π * x))
              (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
          * (∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail (phiX x a) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (phiX x a)
      ∧ 2 ≤ Cvs.L2a.FullTailDeepSpan.TL (2 * π * x) kapStarF
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) kapStarF x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x (rhoX x) (sigmaLow (2 * π * x))
              (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))) := by
  have hx' : c0At (1 / 38) ≤ 2 * π * x := Cvs.L2a.FullSpanThreshold.c0F_eq ▸ hx
  obtain ⟨hc80, -⟩ := c_facts (by norm_num) le_rfl hx'
  rw [Cvs.L2a.FullSpanThreshold.kapStarF_eq]
  exact L2a_full_span_of_K x (by norm_num) le_rfl hx' hL a (resLoc_le_rhoX (c16_le_c0At hx')) hκb hRC hκs
    (by norm_num) hnum_c0F (margin_c0F hc80 le_rfl)

/-- **L2a-FULL on `Finset.range x` at `c = 2πx ≥ c₀(1/500)`** with the wider coupling `κ̄·(log c − 2.64) ≤ 5/2`:
`κ_full ≥ 1/500` at `ρ = 7c^{−1/8}`, the two L2a-FULL inequalities with `κ = κ⋆(1/500)`, `T ≥ 2` and `b̄ ≥ 1`. -/
theorem L2a_full_span_wide (x : ℕ) (hx : c0At (1 / 500) ≤ 2 * π * x)
    (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1)) (a : Finset.range x → ℝ)
    {κb : ℝ} (hκb : 0 ≤ κb)
    (hRC : RungCoupling (2 * π * x) (fun j : Finset.range x => rung (2 * π * x) (2 * (j : ℕ))) a (bandX x)
      Cvs.L2a.FarIntegrationByParts.wF κb)
    (hκs : κb * (Real.log (2 * π * x) - 264 / 100) ≤ 5 / 2) :
    1 / 500 ≤ Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x (rhoX x) (sigmaLow (2 * π * x))
            (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt (1 / 500)) x
              (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x (rhoX x) (sigmaLow (2 * π * x))
                (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
            * (∫ y in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail (phiX x a) M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt (1 / 500)) x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x (rhoX x) (sigmaLow (2 * π * x))
              (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x))))
          * (∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail (phiX x a) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (phiX x a)
      ∧ 2 ≤ Cvs.L2a.FullTailDeepSpan.TL (2 * π * x) (kapStarAt (1 / 500))
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull (2 * π * x) (kapStarAt (1 / 500)) x
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) (2 * π * x) x (rhoX x) (sigmaLow (2 * π * x))
              (thetaBar κb (Cvs.Prolate.PlungeMassTrace.plungeBound (2 * π * x)))) := by
  obtain ⟨hc80, -⟩ := c_facts (by norm_num) (by norm_num) hx
  exact L2a_full_span_of_K x (by norm_num) (by norm_num) hx hL a (resLoc_le_rhoX (c16_le_c0At hx)) hκb hRC hκs
    (by norm_num) hnum_wide (margin_wide hc80 le_rfl)

end Cvs.L2a.FullSpanProlateFamily
