import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarMassPlateau
import Cvs.L2a.FirstSecondPairNoGram
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungPairingsAveragedTail
import Cvs.L2a.RungSpanExplicitCutoff
import Cvs.L2a.RungSpanFirstSecondPair
import Cvs.L2a.RungSpanFromLowMass
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanPoleMellinFromRungs
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailEdgeFarSplit
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailOfModes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.Archimedean.ArchFloorThreshold
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
# L2a on the rung span with the pole and Mellin terms from the rungs' own values

Cvs.L2a.RungSpanExplicitCutoff with the span's pole and Mellin bounds supplied by Cvs.L2a.SpanPoleMellinFromRungs from rung values `Pᵢ, Qᵢ, Bᵢ` and the span floor
`κ = den` (Cvs.L2a.RungHilbertLossMass): `q = 2√(Σ P²/m)√(Σ Q²/m)/κ` and `β = Σ B²/m`, `mᵢ = ∫₁ᵇψᵢ²`, so the low mass and the pole enter
as single-rung sums weighted by the rungs' masses.
-/

namespace Cvs.L2a.RungSpanFromRungValues

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.TailNormModeMassesNonres Cvs.L2a.ResonantPartBeyondEdge Cvs.L2a.RungSpanTailFractions Cvs.L2a.RungSpanFirstSecondPair Cvs.L2a.FirstSecondPairFarMass Cvs.L2a.FirstSecondPairNoGram Cvs.L2a.RungSpanClosedForm Cvs.L2a.PoissonFarMassHarmonicGain Cvs.L2a.TailFractionsPairRatio Cvs.L2a.FarMassPlateau Cvs.L2a.TailEdgeFarSplit Cvs.L2a.RungSpanFromPlateau
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)
open Cvs.L2a.RungSpanCrossPlateau Cvs.L2a.MassBeyondFrame Cvs.L2a.SpanFrameFromRungs

open Cvs.L2a.RungSpanFromFrame Cvs.L2a.RungPairingsAveragedTail
open Cvs.L2a.RungSpanFromAveragedTail Cvs.L2a.EdgeFarAnglePlateau Cvs.WeilForm.Archimedean.ArchFloorThreshold
open Cvs.L2a.RungSpanExplicitCutoff Cvs.L2a.SpanPoleMellinFromRungs

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 400000 in
/-- **L2a on the rung span from the rungs' pole and Mellin values.** -/
theorem L2a_of_rung_values {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' ρ ρ₁ ε₃ : ℝ} {δef εb σ₁ Cb ηl c₂ : ℝ} {M k₀ : ℕ} (N P R Kf : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ) (εs : ℕ → ℝ) (C : ℕ → ℝ)
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
    (hx : 0 < x') (hKf : 1 ≤ Kf)
    (hMb : (M : ℝ) ≤ b)
    (Gr : ι → ℝ) {δa ea Sa : ℝ} (hδa0 : 0 ≤ δa) (hδa1 : δa < 1)
    (hangle : |∫ θ in (1 : ℝ)..b, (∑ i, a i * psi c (g i) θ)
        * ∑ m ∈ Finset.Icc 2 M, ∑ i, a i * psi c (g i) (m * θ)|
      ≤ δa * √((∫ θ in (1 : ℝ)..b, (∑ i, a i * psi c (g i) θ) ^ 2)
          * ∫ θ in (1 : ℝ)..b, (∑ m ∈ Finset.Icc 2 M, ∑ i, a i * psi c (g i) (m * θ)) ^ 2))
    (hGdef : ∀ i, Gr i = ∫ θ in (1 : ℝ)..b, psi c (g i) θ ^ 2) (hGr : ∀ i, 0 < Gr i)
    (hea0 : 0 ≤ ea) (hea1 : ea < 1)
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, √(avgTail c (χ i) (g i) b * avgTail c (χ j) (g j) b) / √(Gr i * Gr j) ≤ ea)
    (hSa : ∑ i, (∫ ξ in b..(M * b), psi c (g i) ξ ^ 2) / Gr i ≤ Sa)
    (hε₃ : ε₃ = (1 + Sa / (1 - ea)) / (1 - δa))
    (hε0 : ∀ j, 0 ≤ εs j) (hε1 : ∀ j, εs j < 1)
    (hfar : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      (1 - εs j) * ∑ m ∈ Finset.Icc 1 M, farMode (fun ξ => ∑ i, a i * psi c (g i) ξ) b j m
        ≤ ∫ θ in Ioi 1, farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2)
    (hδef0 : 0 ≤ δef) (hδef : δef < 1 / 3)
    (hangEF : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      |∫ θ in Ioi 1, edgeF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ * farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ|
        ≤ δef * √((∫ θ in Ioi 1, edgeF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2) * ∫ θ in Ioi 1, farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2))
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
    (Pv Qv Bm : ι → ℝ)
    (hP : ∀ i, |∫ θ in Ioi 1, tailF (psi c (g i)) M b θ| ≤ Pv i)
    (hQ : ∀ i, |∫ θ in Ioi 1, tailF (psi c (g i)) M b θ / θ| ≤ Qv i)
    (hBm : ∀ i, ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, tailF (psi c (g i)) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ Bm i
      ∧ |∫ θ in Ioi 1, tailF (psi c (g i)) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ Bm i)
    (hεb : ∀ j, εs j ≤ εb) (hεb1 : εb < 1)
    (hσ₁ : 0 ≤ σ₁) (hS₁ : ∑ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) ^ 2
      ≤ σ₁ * ∫ θ in (1 : ℝ)..b, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hCb0 : 0 ≤ Cb) (hCb : ∀ j, 2 ≤ j → j < k₀ → C j ≤ Cb)
    (hηl : 4 * x' * massSum Bm Gr / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)) ≤ ηl) (hηl1 : ηl < 1)
    (hcut : exp (max (l2aNeed δef εb σ₁ Cb ε₃ ρ₁ ρ (2 * √(massSum Pv Gr) * √(massSum Qv Gr) / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b))) c₂ ηl M k₀) (archSymbol 0) - cFloor Kf + 1) ≤ x')
    (hsF : sFloor Kf ≤ (π * x') ^ 2) :
    c₂ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM1 : 1 ≤ M := by omega
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hNeq := integral_tailF_sq_eq (ψ := fun i => psi c (g i)) (a := a) (χ := χ) hM1 hb1 hcψ
  have hfloor := span_floor_prolate_explicit N g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax
    hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw' hden
  rw [← hNeq] at hfloor
  have hmass : ∑ i, a i ^ 2 * Gr i = ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hGdef i]
  have hfl' : ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)) * ∑ i, a i ^ 2 * Gr i
      ≤ ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2 := by rw [hmass]; exact hfloor
  have hpole := pole_of_rungs (fun i => psi c (g i)) a Gr Pv Qv M hb1 hcψ hGr hκ hfl' hP hQ
  have hB := mellin_of_rungs (fun i => psi c (g i)) a Gr Bm M (T := 2 * π * x') hb1 hcψ hGr hBm
  have hβ : (√(∑ i, a i ^ 2 * Gr i) * √(massSum Bm Gr)) ^ 2
      ≤ massSum Bm Gr * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 := by
    rw [mellin_sq_eq a Gr Bm hGr, hmass]
  have hβ0 := massSum_nonneg Bm hGr
  exact L2a_pos N P R Kf g g₁ g₂ χ a εs C hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw' hden hκ hx hKf hB hβ hβ0 hMb Gr hδa0 hδa1 hangle hGdef hGr hea0 hea1 hrow hSa hε₃ hε0 hε1 hfar hδef0 hδef hangEF hC hT hcrossC h2 hρ₁ hrest1 hrest hpole hεb hεb1 hσ₁ hS₁ hCb0 hCb hηl hηl1 hcut hsF

end Cvs.L2a.RungSpanFromRungValues
