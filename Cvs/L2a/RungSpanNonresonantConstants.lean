import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.PrimePairingResonantSplit
import Cvs.L2a.ResonantChannelModeMasses
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanResonantForm
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailNormModeMassesNonres
import Cvs.L2a.TailOfModes
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
# L2a on the rung span from the two non-resonant constants

The resonant channel is at most `2 log M` times the mode masses (Cvs.L2a.ResonantChannelModeMasses), and the tail norm is the mode masses plus
the non-resonant pairs at `k = 1` (Cvs.L2a.TailNormModeMassesNonres): so if the non-resonant pairs at `k = 1` are at least `−δ` times the
mode masses and those of the prime powers `k ≤ b` at most `ν` times them, the prime constant of the span
statement is `(2 log M + ν)/(1 − δ)`, uniform in `b`, and the full-tail L2a on the span rests on `δ` and `ν`.
-/

namespace Cvs.L2a.RungSpanNonresonantConstants

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant
open Cvs.L2a.RungSpanResonantForm Cvs.L2a.TailNormModeMassesNonres Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span from the two non-resonant constants**: with `nonresPart(1) ≥ −δ Σ_n modeMass(n)`
and `Σ_{k ≤ b} 2Λ(k) nonresPart(k) ≤ ν Σ_n modeMass(n)`, the prime constant is `(2 log M + ν)/(1 − δ)`. -/
theorem L2a_span_nonres {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β δ₁ ν : ℝ} {M : ℕ} (N P R Kf : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
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
    (hξ₀ : 1 < ξ₀) (hξ₀b : ξ₀ ≤ b) (hw : wbar c ξ₀ < 2) (hden : 0 < massCoeff c b ξ₀)
    (hκ : 0 < (1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b))
    (hx : 0 < x') (hKf : 1 ≤ Kf) (hfl : archSymbol 0 ≤ floorK x' Kf)
    (hB : ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ B
      ∧ |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ B)
    (hβ : B ^ 2 ≤ β * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) (hβ0 : 0 ≤ β)
    (hδ₁ : 0 ≤ δ₁) (hδ₁' : δ₁ < 1) (hν : 0 ≤ ν)
    (hnr1 : -(δ₁ * ∑ n ∈ Finset.Icc 1 M, modeMass (fun ξ => ∑ i, a i * psi c (g i) ξ) b n)
      ≤ nonresPart (fun ξ => ∑ i, a i * psi c (g i) ξ) M b 1)
    (hnr : ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
          2 * Λ k * nonresPart (fun ξ => ∑ i, a i * psi c (g i) ξ) M b k
      ≤ ν * ∑ n ∈ Finset.Icc 1 M, modeMass (fun ξ => ∑ i, a i * psi c (g i) ξ) b n)
    (hpole : -(q * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ / θ)) :
    (floorK x' Kf
        - (floorK x' Kf - archSymbol 0)
          * (4 * x' * β / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
            - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
                + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)))
        - (2 * Real.log M + ν) / (1 - δ₁) - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hconts : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcψ i)
  have hb1 : (1 : ℝ) ≤ b := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦ
  set S := ∑ n ∈ Finset.Icc 1 M, modeMass Φ b n with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => intervalIntegral.integral_nonneg hb1 (fun θ _ => sq_nonneg _)
  -- the norm against the mode masses (Cvs.L2a.TailNormModeMassesNonres)
  have hNeq := norm_eq_modeMasses_add_nonres Φ M hb1 hconts.continuousOn
  have hNS : (1 - δ₁) * S ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by rw [hNeq]; linarith
  -- the log-weighted mode masses against `2 log M` times the mode masses
  have hlog : ∑ n ∈ Finset.Icc 1 M, 2 * Real.log n * modeMass Φ b n ≤ 2 * Real.log M * S := by
    rw [hSdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast hn.2
    have hm : 0 ≤ modeMass Φ b n := intervalIntegral.integral_nonneg hb1 (fun θ _ => sq_nonneg _)
    have : Real.log n ≤ Real.log M := Real.log_le_log (by linarith) hnM
    nlinarith
  have hp : (∑ n ∈ Finset.Icc 1 M, 2 * Real.log n * modeMass Φ b n)
      + (∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
          2 * Λ k * nonresPart Φ M b k)
      ≤ (2 * Real.log M + ν) / (1 - δ₁) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    have h1δ : 0 < 1 - δ₁ := by linarith
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
    calc (∑ n ∈ Finset.Icc 1 M, 2 * Real.log n * modeMass Φ b n)
          + (∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
              2 * Λ k * nonresPart Φ M b k)
        ≤ (2 * Real.log M + ν) * S := by linarith
      _ = (2 * Real.log M + ν) / (1 - δ₁) * ((1 - δ₁) * S) := by field_simp
      _ ≤ (2 * Real.log M + ν) / (1 - δ₁) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 :=
          mul_le_mul_of_nonneg_left hNS (by positivity)
  exact L2a_span_resonant N P R Kf g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax hh hh'
    hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden hκ hx hKf hfl hB hβ hβ0 hp hpole

end Cvs.L2a.RungSpanNonresonantConstants
