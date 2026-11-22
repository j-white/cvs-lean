import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.PrimePairingResonantSplit
import Cvs.L2a.ResonantPartBeyondEdge
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanResonantForm
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.SpanTailPrimeResonant
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailOfModes
import Cvs.L2a.TailPrimeSideByNorm
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional
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
# L2a on the rung span from the tail fractions beyond the edge

The resonant part at `k` is `(1/k)` times the mode masses of the sub-tail on `[k, b]` (Cvs.L2a.ResonantPartBeyondEdge). With
`τ_k` the fraction of the tail norm those masses occupy, `Σ_{k ≤ b} 2Λ(k) resPart(k) ≤ (Σ_{k ≤ b} 2Λ(k) τ_k/k) ∫F²`,
and the span statement of Cvs.L2a.RungSpanResonantForm holds with the prime constant `Σ_{k ≤ b} 2Λ(k) τ_k/k + ν`, `ν` the non-resonant
constant against the tail norm: the full-tail L2a on the span rests on the profile `τ_k` and on `ν`.
-/

namespace Cvs.L2a.RungSpanTailFractions

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.ResonantPartBeyondEdge
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The mode masses of the sub-tail of `⌊M/k⌋` modes on `[k, b]`. -/
noncomputable def modesBeyond (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) : ℝ :=
  ∑ m' ∈ (Finset.Icc 1 M).filter (fun m' => k * m' ≤ M), ∫ ξ in (k : ℝ)..b, Φ (m' * ξ) ^ 2

/-- **The resonant channel against the tail norm from the tail fractions**: with
`modesBeyond(k) ≤ τ k · ∫F²` for the prime powers `k ≤ b`, `Σ_k 2Λ(k) resPart(k) ≤ (Σ_k 2Λ(k) τ k / k) ∫F²`. -/
theorem resonant_le_of_fractions (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (S : Finset ℕ) (τ : ℕ → ℝ)
    (hS : ∀ k ∈ S, 1 ≤ k) (hN : 0 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2)
    (hτ : ∀ k ∈ S, modesBeyond Φ M b k ≤ τ k * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) :
    ∑ k ∈ S, 2 * Λ k * resPart Φ M b k
      ≤ (∑ k ∈ S, 2 * Λ k * τ k / k) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hS k hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hΛ : 0 ≤ Λ k := vonMangoldt_nonneg
  rw [resPart_eq_modes_beyond Φ M (hS k hk)]
  have := hτ k hk
  unfold modesBeyond at this
  calc 2 * Λ k * (1 / (k : ℝ) * ∑ m' ∈ (Finset.Icc 1 M).filter (fun m' => k * m' ≤ M),
          ∫ ξ in (k : ℝ)..b, Φ (m' * ξ) ^ 2)
      ≤ 2 * Λ k * (1 / (k : ℝ) * (τ k * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 * Λ k * τ k / k * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
        field_simp

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span from the tail fractions beyond the edge and the non-resonant constant**:
the prime constant is `Σ_{k ≤ b} 2Λ(k) τ_k/k + ν`. -/
theorem L2a_span_of_fractions {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β ν : ℝ} {M : ℕ} (N P R Kf : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ) (τ : ℕ → ℝ)
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
    (hτ : ∀ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
      modesBeyond (fun ξ => ∑ i, a i * psi c (g i) ξ) M b k
        ≤ τ k * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hν : ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
          2 * Λ k * nonresPart (fun ξ => ∑ i, a i * psi c (g i) ξ) M b k
      ≤ ν * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hpole : -(q * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ / θ)) :
    (floorK x' Kf
        - (floorK x' Kf - archSymbol 0)
          * (4 * x' * β / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
            - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
                + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)))
        - ((∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
              2 * Λ k * τ k / k) + ν) - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hconts : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcψ i)
  have hb1 : (1 : ℝ) ≤ b := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦ
  have hNn : 0 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hS : ∀ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b), 1 ≤ k :=
    fun k hk => Cvs.L2a.TailPrimeSideByNorm.one_le_of_mem_primePowIndex (Finset.mem_filter.mp hk).1
  have hres := resonant_le_of_fractions Φ M _ τ hS hNn hτ
  -- the prime side in resonant form (Cvs.L2a.SpanTailPrimeResonant) against the two hypotheses
  have hp : Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution
        (logScale (tailF Φ M b)))
      ≤ ((∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
            2 * Λ k * τ k / k) + ν) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    rw [Cvs.L2a.SpanTailPrimeResonant.primeSide_eq Φ M (by linarith) hconts.continuousOn P R]
    have hsplit : ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
          2 * Λ k * (resPart Φ M b k + nonresPart Φ M b k)
        = (∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
              2 * Λ k * resPart Φ M b k)
          + ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
              2 * Λ k * nonresPart Φ M b k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hsplit, add_mul]
    exact add_le_add hres hν
  exact L2a_span_of_prime N P R Kf g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax hh hh'
    hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden hκ hx hKf hfl hB hβ hβ0 hp hpole

end Cvs.L2a.RungSpanTailFractions
