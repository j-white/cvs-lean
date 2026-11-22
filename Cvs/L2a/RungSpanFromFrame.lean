import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.FarMassPlateau
import Cvs.L2a.FirstSecondPairNoGram
import Cvs.L2a.MassBeyondFrame
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanCrossPlateau
import Cvs.L2a.RungSpanFirstSecondPair
import Cvs.L2a.RungSpanFromPlateau
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanFrameFromRungs
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailEdgeFarSplit
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailOfModes
import Cvs.L2a.TrivialGainsCrossConstants
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a on the span with the mass beyond `b` from the rung-level frame bound

Cvs.L2a.RungSpanCrossPlateau with its hypothesis on the mass beyond `b` (`ε₃`) supplied by Cvs.L2a.MassBeyondFrame and Cvs.L2a.SpanFrameFromRungs: `ε₃ = (1 + S/(1 − e))/(1 − δ)`
with `δ` the span's mode-1 angle on `[1, b]`, `e` the rungs' tail Schur row and `S = Σᵢ ∫_b^{Mb}ψᵢ²/∫₁ᵇψᵢ²`.
-/

namespace Cvs.L2a.RungSpanFromFrame

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.TailNormModeMassesNonres Cvs.L2a.ResonantPartBeyondEdge Cvs.L2a.RungSpanTailFractions Cvs.L2a.RungSpanFirstSecondPair Cvs.L2a.FirstSecondPairFarMass Cvs.L2a.FirstSecondPairNoGram Cvs.L2a.RungSpanClosedForm Cvs.L2a.PoissonFarMassHarmonicGain Cvs.L2a.TailFractionsPairRatio Cvs.L2a.FarMassPlateau Cvs.L2a.TailEdgeFarSplit Cvs.L2a.RungSpanFromPlateau
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)
open Cvs.L2a.RungSpanCrossPlateau Cvs.L2a.MassBeyondFrame Cvs.L2a.SpanFrameFromRungs

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **L2a on the span with the mass beyond `b` from the rung-level frame bound.** -/
theorem L2a_span_of_frame {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β ρ ρ₁ ε₃ : ℝ} {M k₀ : ℕ} (N P R Kf : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ) (εs : ℕ → ℝ) (C Cef : ℕ → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hc8 : 8 ≤ c) (hs : 0 < s) (hsmax : max s (5 / (6 * s)) ≤ 1)
    (hh : 0 < h) (hh' : h ≤ 1 / 5)
    (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20) (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 4 ≤ b)
    (hbM : 3 * M / 2 ≤ b)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b)
    (hD : 0 < D) (hgap : ∀ i j, i ≠ j → D ≤ |χ i - χ j|)
    (hξ₀ : 1 < ξ₀) (hξ₀b : ξ₀ ≤ b) (hw' : wbar c ξ₀ < 2) (hden : 0 < massCoeff c b ξ₀)
    (hκ : 0 < (1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b))
    (hx : 0 < x') (hKf : 1 ≤ Kf) (hfl : archSymbol 0 ≤ floorK x' Kf)
    (hB : ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ B
      ∧ |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ B)
    (hβ : B ^ 2 ≤ β * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) (hβ0 : 0 ≤ β)
    (hMb : (M : ℝ) ≤ b)
    (Gr τr : ι → ℝ) {δa ea Sa : ℝ} (hδa0 : 0 ≤ δa) (hδa1 : δa < 1)
    (hangle : |∫ θ in (1 : ℝ)..b, (∑ i, a i * psi c (g i) θ)
        * ∑ m ∈ Finset.Icc 2 M, ∑ i, a i * psi c (g i) (m * θ)|
      ≤ δa * √((∫ θ in (1 : ℝ)..b, (∑ i, a i * psi c (g i) θ) ^ 2)
          * ∫ θ in (1 : ℝ)..b, (∑ m ∈ Finset.Icc 2 M, ∑ i, a i * psi c (g i) (m * θ)) ^ 2))
    (hGdef : ∀ i, Gr i = ∫ θ in (1 : ℝ)..b, psi c (g i) θ ^ 2) (hGr : ∀ i, 0 < Gr i) (hτ0 : ∀ i, 0 ≤ τr i)
    (hpair : ∀ i j, i ≠ j → |∫ θ in (1 : ℝ)..b, psi c (g i) θ * psi c (g j) θ| ≤ √(τr i * τr j))
    (hea0 : 0 ≤ ea) (hea1 : ea < 1)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, √(τr i * τr j) / √(Gr i * Gr j) ≤ ea)
    (hSa : ∑ i, (∫ ξ in b..(M * b), psi c (g i) ξ ^ 2) / Gr i ≤ Sa)
    (hε₃ : ε₃ = (1 + Sa / (1 - ea)) / (1 - δa))
    (hε0 : ∀ j, 0 ≤ εs j) (hε1 : ∀ j, εs j < 1)
    (hfar : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      (1 - εs j) * ∑ m ∈ Finset.Icc 1 M, farMode (fun ξ => ∑ i, a i * psi c (g i) ξ) b j m
        ≤ ∫ θ in Ioi 1, farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2)
    (hCef0 : ∀ j, 0 ≤ Cef j) (hCef : ∀ j, Cef j < 1 / 4)
    (hcorrC : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      |∫ θ in Ioi 1, edgeF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ * farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ|
        ≤ Cef j * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hC : ∀ j, 0 ≤ C j) (hT : 0 < ∫ θ in (1 : ℝ)..b, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hcrossC : ∀ j ∈ Finset.Icc 1 M, 2 ≤ j → j < k₀ →
      |∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ (Finset.Icc 1 M).erase m,
          ∫ θ in (j : ℝ)..b, (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) * (fun ξ => ∑ i, a i * psi c (g i) ξ) (m' * θ)|
        ≤ C j * ∫ θ in (j : ℝ)..b, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (h2 : 2 ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b))
    (hρ₁ : 0 ≤ ρ₁)
    (hrest1 : 2 * |pairPiece (fun ξ => ∑ i, a i * psi c (g i) ξ) b|
        + |rest1 (fun ξ => ∑ i, a i * psi c (g i) ξ) M b|
      ≤ ρ₁ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hrest : nonresRestTotal (fun ξ => ∑ i, a i * psi c (g i) ξ) M b
          ((Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b))
      ≤ ρ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hpole : -(q * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ / θ)) :
    (floorK x' Kf
        - (floorK x' Kf - archSymbol 0)
          * (4 * x' * β / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
            - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
                + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)))
        - ((∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
              2 * Λ k * tauG (gainP k₀ (fun j => 2 * Cef j / (1 - 2 * Cef j)) (fun _ => 1) εs (Cvs.L2a.TrivialGainsCrossConstants.deltaSeq (∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) ^ 2) (∫ θ in (1 : ℝ)..b, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2) C)) ε₃ M k / k)
            + (2 * Λ 2 * √((1 + ρ₁) * tauG (gainP k₀ (fun j => 2 * Cef j / (1 - 2 * Cef j)) (fun _ => 1) εs (Cvs.L2a.TrivialGainsCrossConstants.deltaSeq (∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) ^ 2) (∫ θ in (1 : ℝ)..b, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2) C)) ε₃ M 2 / 2) + ρ)) - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hM1 : 1 ≤ M := by omega
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMb' : b ≤ M * b := by nlinarith
  have hcont : ∀ i, ContinuousOn (psi c (g i)) (Icc 1 (M * b)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1.continuousOn
  have hframe := frame_of_rungs a (fun i => psi c (g i)) Gr τr hM1 hb1 hcont hδa0 hδa1 hangle hGdef hGr hτ0
    hpair hea0 hea1 hrow hSa
  have hcΦ : ContinuousOn (fun ξ => ∑ i, a i * psi c (g i) ξ) (Icc 1 (M * b)) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hcont i)
  rw [← hε₃] at hframe
  have hbeyond := beyond_le_frame hb1 hMb' hcΦ hframe
  have hSa0 : 0 ≤ Sa := le_trans (Finset.sum_nonneg fun i _ => div_nonneg
    (intervalIntegral.integral_nonneg hMb' fun ξ _ => sq_nonneg _) (hGr i).le) hSa
  have hε₃0 : 0 ≤ ε₃ := by
    rw [hε₃]
    have h1 : 0 < 1 - ea := by linarith
    have h2 : 0 < 1 - δa := by linarith
    positivity
  exact L2a_span_of_cross_plateau N P R Kf g g₁ g₂ χ a εs C Cef hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw' hden hκ hx hKf hfl hB hβ hβ0 hMb hε₃0 hbeyond hε0 hε1 hfar hCef0 hCef hcorrC hC hT hcrossC h2 hρ₁ hrest1 hrest hpole

end Cvs.L2a.RungSpanFromFrame
