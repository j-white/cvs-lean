import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.PrimePairingResonantSplit
import Cvs.L2a.ResonantChannelModeMasses
import Cvs.L2a.RungChiHierarchy
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanFromLowMass
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.SpanTailPrimeResonant
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesAdmissible
import Cvs.L2a.TailOfModes
import Cvs.L2a.TailPrimeSideByNorm
import Cvs.L2a.TailPrimeSideMultiplicative
import Cvs.L2a.TailWeilFormFromBounds
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
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
# L2a on the rung span with the prime side in resonant form

The assembly of Cvs.L2a.RungSpanFromLowMass with the prime side entering through any bound `p` on it, and its instance with the
resonant form of Cvs.L2a.SpanTailPrimeResonant: `p` is then the log-weighted mode masses plus the non-resonant pairs of the prime powers
`k ≤ b`, over the tail's norm, so the constant no longer carries the pairwise `Σ 2Λ(k)/√k` that grows with `b`.
-/

namespace Cvs.L2a.RungSpanResonantForm

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span, given the low mass, the pole and any bound `p` on the prime side.** -/
theorem L2a_span_of_prime {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β p : ℝ} {M : ℕ} (N P R Kf : ℕ)
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
    (hp : Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R (Cvs.Zeta.Explicit.Weil.selfConvolution
        (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)))
      ≤ p * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hpole : -(q * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ / θ)) :
    (floorK x' Kf
        - (floorK x' Kf - archSymbol 0)
          * (4 * x' * β / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
            - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
                + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)))
        - p - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  set ψs : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hψs
  set F := tailF ψs M b with hFdef
  set Nn := ∫ θ in Ioi 1, F θ ^ 2 with hNn
  set κ := (1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
    - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
        + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b) with hκdef
  set S := ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 with hSdef
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM1 : 1 ≤ M := by omega
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  -- the combination is `C¹`
  have hC1s : ContDiff ℝ 1 ψs := by
    rw [hψs]
    exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_psi (hg i) (hg₁ i) (hg₂c i) (hang i))
  have hconts : Continuous ψs := hC1s.continuous
  -- the tail vanishes at `θ ≤ 1` and is admissible
  have hF0 : ∀ θ ≤ 1, F θ = 0 := tailF_zero ψs M b
  obtain ⟨h2, h1, hsq, hsh, hlevy⟩ := Cvs.L2a.TailModesAdmissible.admissible (M := M) (Ξ := M * b) hb1 le_rfl
    hC1s.contDiffOn
  have hsum_cont : Continuous fun θ => ∑ m ∈ Finset.Icc 1 M, ψs (m * θ) :=
    continuous_finsetSum _ fun m _ => hconts.comp (continuous_const.mul continuous_id)
  have hFi : IntegrableOn F (Ioi 1) := by
    have hint : IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 M, ψs (m * θ)) (Ioc 1 b) :=
      (hsum_cont.continuousOn.integrableOn_Icc (a := 1) (b := b)).mono_set Ioc_subset_Icc_self
    exact ((integrable_indicator_iff measurableSet_Ioc).mpr hint).integrableOn
  have hFm : AEStronglyMeasurable F volume :=
    Cvs.L2a.TailPrimeSideByNorm.tailF_aestronglyMeasurable hconts.continuousOn
  have hF2 : IntegrableOn (fun θ => F θ ^ 2) (Ioi 1) := by
    have hind : (fun θ => F θ ^ 2)
        = Set.indicator (Ioc 1 b) (fun θ => (∑ m ∈ Finset.Icc 1 M, ψs (m * θ)) ^ 2) := by
      funext θ; rw [hFdef]; unfold tailF; by_cases hθ : θ ∈ Ioc 1 b <;> simp [hθ]
    rw [hind]
    have hint : IntegrableOn (fun θ => (∑ m ∈ Finset.Icc 1 M, ψs (m * θ)) ^ 2) (Ioc 1 b) :=
      ((hsum_cont.pow 2).continuousOn.integrableOn_Icc (a := 1) (b := b)).mono_set Ioc_subset_Icc_self
    exact ((integrable_indicator_iff measurableSet_Ioc).mpr hint).integrableOn
  -- the norm is the span tail square, and the floor
  have hNeq : Nn = ∫ θ in (1 : ℝ)..b, (Gk a χ (fun i => psi c (g i)) 0 θ
      + ∑ m ∈ Finset.Icc 2 M, Gk a χ (fun i => psi c (g i)) 0 (m * θ)) ^ 2 :=
    integral_tailF_sq_eq (χ := χ) hM1 hb1 hcψ
  have hfloor := span_floor_prolate_explicit N g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax
    hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden
  rw [← hNeq] at hfloor
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hMpos i).le
  have hN : 0 < Nn := by
    have : 0 < κ * S := by
      rcases hS0.lt_or_eq with hSpos | hSz
      · exact mul_pos hκ hSpos
      · exfalso
        -- `S = 0` forces every `a i = 0`, against `N₀ > 0`
        have : ∀ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2 = 0 := fun i =>
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hMpos j).le).mp hSz.symm i
            (Finset.mem_univ i)
        have ha : ∀ i, a i = 0 := fun i => by
          have := this i
          rcases mul_eq_zero.mp this with h0 | h0
          · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
          · exact absurd h0 (hMpos i).ne'
        have : ∑ i, a i ^ 2 * massB c (χ i) (g i) b = 0 := Finset.sum_eq_zero fun i _ => by rw [ha i]; ring
        linarith
    linarith
  -- the prime side by the hypothesis
  have hPr : ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
      2 * Real.log p * (∫ θ in Ioi 1, F θ * F ((p : ℝ) ^ r * θ)) ≤ p * ∫ θ in Ioi 1, F θ ^ 2 := by
    have := hp
    rwa [Cvs.L2a.TailPrimeSideMultiplicative.primeSide_eq F hF0 P R] at this
  -- the terminal inequality (Cvs.L2a.TailWeilFormFromBounds)
  have hW := Cvs.L2a.TailWeilFormFromBounds.weilForm_tail_ge P R hF0 hFi h2 h1 hsq hsh hlevy hx hKf hfl (B := B) (p := p)
    (q := q) hN hB hPr hpole
  -- the low mass against the floor
  have hfl0 : 0 ≤ floorK x' Kf - archSymbol 0 := by linarith
  have hε' : 4 * x' * B ^ 2 / Nn ≤ 4 * x' * β / κ := by
    rw [div_le_div_iff₀ hN hκ]
    have h1' : B ^ 2 * κ ≤ β * S * κ := mul_le_mul_of_nonneg_right hβ hκ.le
    have h2' : β * (κ * S) ≤ β * Nn := mul_le_mul_of_nonneg_left hfloor hβ0
    nlinarith [hx]
  have hcoef : (floorK x' Kf - (floorK x' Kf - archSymbol 0) * (4 * x' * β / κ) - p - q)
      ≤ floorK x' Kf - (floorK x' Kf - archSymbol 0) * (4 * x' * B ^ 2 / Nn) - p - q := by
    have := mul_le_mul_of_nonneg_left hε' hfl0
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef hN.le).trans hW

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span with the prime side in resonant form**: the constant carries
`p ≥ (Σ_{n ≤ M} 2 log n ∫_1^b Φ(nθ)² dθ + Σ_{k ≤ b} 2Λ(k) nonresPart(k)) / ∫F²`, uniform in `b`. -/
theorem L2a_span_resonant {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β p : ℝ} {M : ℕ} (N P R Kf : ℕ)
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
    (hp : (∑ n ∈ Finset.Icc 1 M, 2 * Real.log n * modeMass (fun ξ => ∑ i, a i * psi c (g i) ξ) b n)
        + (∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
            2 * Λ k * nonresPart (fun ξ => ∑ i, a i * psi c (g i) ξ) M b k)
      ≤ p * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hpole : -(q * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ / θ)) :
    (floorK x' Kf
        - (floorK x' Kf - archSymbol 0)
          * (4 * x' * β / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
            - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
                + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)))
        - p - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hconts : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcψ i)
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hp' := (primeSide_le (fun ξ => ∑ i, a i * psi c (g i) ξ) M hb1 hconts.continuousOn P R).trans hp
  exact L2a_span_of_prime N P R Kf g g₁ g₂ χ a hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax hh hh'
    hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden hκ hx hKf hfl hB hβ hβ0 hp' hpole

end Cvs.L2a.RungSpanResonantForm
