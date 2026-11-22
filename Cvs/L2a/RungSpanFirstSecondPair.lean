import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.PrimePairingResonantSplit
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanTailFractions
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailOfModes
import Cvs.L2a.TailPrimeSideByNorm
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
# L2a on the rung span from the `(1, 2)` pair against the tail norm

The non-resonant part at `k ≥ 2` is the `(1, 1)` pair `∫_1^{b/k} Φ(θ)Φ(kθ) dθ` plus the other mode pairs, and the
non-resonant channel over the prime powers is `2Λ(2)` times the `(1, 2)` pair plus everything else. With the tail
fractions `τ_k` (Cvs.L2a.RungSpanTailFractions), the `(1, 2)` pair at most `θ₂ ∫F²` and the rest at most `ρ ∫F²`, L2a on the span holds
with the prime constant `Σ_{k ≤ b} 2Λ(k) τ_k/k + 2Λ(2) θ₂ + ρ`.
-/

namespace Cvs.L2a.RungSpanFirstSecondPair

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.ResonantPartBeyondEdge Cvs.L2a.RungSpanTailFractions
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The `(1, 1)` mode pair at `k`: `∫_1^{b/k} Φ(θ) Φ(kθ) dθ`. -/
noncomputable def pair11 (Φ : ℝ → ℝ) (b : ℝ) (k : ℕ) : ℝ :=
  ∫ θ in (1 : ℝ)..b / k, Φ θ * Φ (k * θ)

/-- The non-resonant part at `k` without its `(1, 1)` pair. -/
noncomputable def nonresRest (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (nonresPairs M k).erase (1, 1), ∫ θ in (1 : ℝ)..b / k, Φ (p.1 * θ) * Φ (p.2 * (k * θ))

/-- Everything in the non-resonant channel over `S` but the `(1, 2)` pair. -/
noncomputable def nonresRestTotal (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (S : Finset ℕ) : ℝ :=
  (∑ k ∈ S, 2 * Λ k * nonresRest Φ M b k) + ∑ k ∈ S.erase 2, 2 * Λ k * pair11 Φ b k

/-- The `(1, 1)` pair is non-resonant at every `k ≥ 2`. -/
theorem one_one_mem_nonresPairs {M k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k) : (1, 1) ∈ nonresPairs M k := by
  simp only [nonresPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

/-- **The non-resonant part at `k ≥ 2` is the `(1, 1)` pair plus the rest.** -/
theorem nonresPart_eq_pair11_add_rest (Φ : ℝ → ℝ) {M : ℕ} (b : ℝ) {k : ℕ} (hM : 1 ≤ M) (hk : 2 ≤ k) :
    nonresPart Φ M b k = pair11 Φ b k + nonresRest Φ M b k := by
  unfold nonresPart nonresRest pair11
  rw [← Finset.add_sum_erase _ _ (one_one_mem_nonresPairs hM hk)]
  simp only [Nat.cast_one, one_mul]

/-- **The non-resonant channel over `S ∋ 2` is `2Λ(2)` times the `(1, 2)` pair plus the rest.** -/
theorem primeNonres_split (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (S : Finset ℕ) (h2 : 2 ∈ S) (hM : 1 ≤ M)
    (hS : ∀ k ∈ S, 1 ≤ k) :
    ∑ k ∈ S, 2 * Λ k * nonresPart Φ M b k = 2 * Λ 2 * pair11 Φ b 2 + nonresRestTotal Φ M b S := by
  -- `k = 1` is not in `S` when every `k ∈ S` is a prime power, but here only `k ≥ 1` is assumed:
  -- the split needs `k ≥ 2`, so we separate `k = 1` if present
  unfold nonresRestTotal
  have hsplit : ∀ k ∈ S, 2 * Λ k * nonresPart Φ M b k
      = 2 * Λ k * pair11 Φ b k + 2 * Λ k * nonresRest Φ M b k := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · have hk1 : k = 1 := by have := hS k hk; omega
      subst hk1
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    · rw [nonresPart_eq_pair11_add_rest Φ b hM hge]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.add_sum_erase _ _ h2]
  ring

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span from the tail fractions and the `(1, 2)` pair against the tail norm**: with
`∫_1^{b/2} Φ(θ)Φ(2θ) dθ ≤ θ₂ ∫F²` and the other non-resonant pairs at most `ρ ∫F²`, the prime constant is
`Σ_{k ≤ b} 2Λ(k) τ_k/k + 2Λ(2) θ₂ + ρ`. -/
theorem L2a_span_of_P2 {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β θ₂ ρ : ℝ} {M : ℕ} (N P R Kf : ℕ)
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
    (h2 : 2 ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b))
    (hP2 : pair11 (fun ξ => ∑ i, a i * psi c (g i) ξ) b 2
      ≤ θ₂ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
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
              2 * Λ k * τ k / k) + (2 * Λ 2 * θ₂ + ρ)) - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hconts : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcψ i)
  have hb1 : (1 : ℝ) ≤ b := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦ
  have hM1 : 1 ≤ M := by omega
  have hS : ∀ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b), 1 ≤ k :=
    fun k hk => Cvs.L2a.TailPrimeSideByNorm.one_le_of_mem_primePowIndex (Finset.mem_filter.mp hk).1
  have hNn : 0 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hν : ∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
        2 * Λ k * nonresPart Φ M b k
      ≤ (2 * Λ 2 * θ₂ + ρ) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    rw [primeNonres_split Φ M b _ h2 hM1 hS]
    have hΛ : 0 ≤ 2 * Λ 2 := by have := vonMangoldt_nonneg (n := 2); linarith
    calc 2 * Λ 2 * pair11 Φ b 2 + nonresRestTotal Φ M b _
        ≤ 2 * Λ 2 * (θ₂ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) + ρ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hP2 hΛ) hrest
      _ = (2 * Λ 2 * θ₂ + ρ) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by ring
  exact L2a_span_of_fractions N P R Kf g g₁ g₂ χ a τ hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax hh hh'
    hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden hκ hx hKf hfl hB hβ hβ0 hτ hν hpole

end Cvs.L2a.RungSpanFirstSecondPair
