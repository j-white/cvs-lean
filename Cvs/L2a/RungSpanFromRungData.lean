import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanFromPerRungBounds
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesPoleMellinValues
import Cvs.L2a.TailOfModes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.FirstModeMellinEdge
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.ModeMellinDyadicPiece
import Cvs.Prolate.SlepianCommutingRelation
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
# L2a on the prolate rung span, from the rung data alone

The per-rung Mellin bounds (Cvs.L2a.TailModesPoleMellinValues `mellin_le`) and pole integrals (Cvs.L2a.TailModesPoleMellinValues `pole_plus_le`, `pole_minus_le`, with
`|u| ≤ ξ√(cG)` from the energy, Cvs.Prolate.Mellin.ModeMellinDyadicPiece) discharge the hypotheses of Cvs.L2a.RungSpanFromPerRungBounds: for prolate rungs with energies `G_j`,
Sonin's edge bound, `χ_j ≤ c² − 2(2πx′)² − 1/2` and gaps `≥ D`, on a dyadic tail `b = 2^{J+1}`, `W(f)` is at least
an explicit multiple of `∫F²` with `β = Σ mellinBound_j²/m_j` and `q` from the pole constants.
-/

namespace Cvs.L2a.RungSpanFromRungData

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanFromLowMass Cvs.L2a.RungSpanFromPerRungBounds
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The per-rung pole constants of Cvs.L2a.TailModesPoleMellinValues at `U = √(cG)`. -/
noncomputable def poleP (c χ G : ℝ) : ℝ :=
  π ^ 2 / 6 * (2 * √(c * G) / (c ^ 2 - χ) + 2 * c ^ 2 * √(c * G) / (c ^ 2 - χ) ^ 2)
noncomputable def poleP' (c χ G : ℝ) : ℝ :=
  π ^ 2 / 6 * (2 * √(c * G) / (c ^ 2 - χ) + 3 * c ^ 2 * √(c * G) / (2 * (c ^ 2 - χ) ^ 2))

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span, from the rung data alone.** -/
theorem L2a_span_prolate {c c₀ h h₂ hη s ε δ μ₁ μ₂ D ξ₀ x' η : ℝ} {M : ℕ} (N P R Kf J : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ G : ι → ℝ) (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hc8 : 8 ≤ c) (hs : 0 < s) (hsmax : max s (5 / (6 * s)) ≤ 1)
    (hh : 0 < h) (hh' : h ≤ 1 / 5)
    (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20) (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hJ : 1 ≤ J)
    (hbM : 3 * M / 2 ≤ (2 : ℝ) ^ (J + 1))
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..(2 : ℝ) ^ (J + 1), psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) (2 ^ (J + 1)))
    (hD : 0 < D) (hgap : ∀ i j, i ≠ j → D ≤ |χ i - χ j|)
    (hξ₀ : 1 < ξ₀) (hξ₀b : ξ₀ ≤ 2 ^ (J + 1)) (hw : wbar c ξ₀ < 2) (hden : 0 < massCoeff c (2 ^ (J + 1)) ξ₀)
    (hκ : 0 < (1 - max s (5 / (6 * s))) * (1 - θH c D (2 ^ (J + 1)) ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη (2 ^ (J + 1)) ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 (2 ^ (J + 1)) (Qpsi c g g₁ g₂ χ (2 ^ (J + 1)) / c) (Qu c g g₁ g₂ χ (2 ^ (J + 1)) / c ^ 3) M N)
          * (1 + τtail c (2 ^ (J + 1))))
    (hx : 0 < x') (hKf : 1 ≤ Kf) (hfl : archSymbol 0 ≤ floorK x' Kf)
    (hG : ∀ j, ∀ ξ ∈ Ioc (1 : ℝ) (M * 2 ^ (J + 1)), energy (aP c (χ j)) (psi c (g j)) (rungU c (g j)) ξ ≤ G j)
    (hG0 : ∀ j, 0 ≤ G j)
    (hedge : ∀ j, ∀ ξ ∈ Icc (1 : ℝ) 2, |psi c (g j) ξ| ≤ |psi c (g j) 1|)
    (hT : ∀ j, 2 * (2 * π * x') ^ 2 + 1 / 2 ≤ c ^ 2 - χ j) (hηpos : 0 < η)
    (hηθ : ∀ j, 1 + η ≤ √(1 + √(c ^ 2 - χ j) / c)) :
    (floorK x' Kf
        - (floorK x' Kf - archSymbol 0)
          * (4 * x' * (∑ j, Cvs.L2a.TailModesPoleMellinValues.mellinBound c (χ j) (G j) η (2 * π * x') (psi c (g j) 1) ^ 2
              / ∫ ξ in (1 : ℝ)..(2 : ℝ) ^ (J + 1), psi c (g j) ξ ^ 2)
            / ((1 - max s (5 / (6 * s))) * (1 - θH c D (2 ^ (J + 1)) ξ₀)
              - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη (2 ^ (J + 1)) ε δ μ₁ μ₂ c₀ M N / c
                  + Λpair s 1 (2 ^ (J + 1)) (Qpsi c g g₁ g₂ χ (2 ^ (J + 1)) / c)
                      (Qu c g g₁ g₂ χ (2 ^ (J + 1)) / c ^ 3) M N) * (1 + τtail c (2 ^ (J + 1)))))
        - (∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R, 2 * Λ k / √(k : ℝ))
        - 2 * √(∑ j, poleP c (χ j) (G j) ^ 2 / ∫ ξ in (1 : ℝ)..(2 : ℝ) ^ (J + 1), psi c (g j) ξ ^ 2)
            * √(∑ j, poleP' c (χ j) (G j) ^ 2 / ∫ ξ in (1 : ℝ)..(2 : ℝ) ^ (J + 1), psi c (g j) ξ ^ 2)
            / ((1 - max s (5 / (6 * s))) * (1 - θH c D (2 ^ (J + 1)) ξ₀)
              - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη (2 ^ (J + 1)) ε δ μ₁ μ₂ c₀ M N / c
                  + Λpair s 1 (2 ^ (J + 1)) (Qpsi c g g₁ g₂ χ (2 ^ (J + 1)) / c)
                      (Qu c g g₁ g₂ χ (2 ^ (J + 1)) / c ^ 3) M N) * (1 + τtail c (2 ^ (J + 1)))))
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M (2 ^ (J + 1)) θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
          (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M (2 ^ (J + 1)))) := by
  have hc0 : 0 < c := by linarith
  have hb4 : (4 : ℝ) ≤ 2 ^ (J + 1) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hb1 : (1 : ℝ) ≤ 2 ^ (J + 1) := by linarith
  have hM1 : 1 ≤ M := by omega
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hΞ : (M : ℝ) * 2 ^ (J + 1) ≤ M * 2 ^ (J + 1) := le_rfl
  have hsys := fun j => rung_system (hg j) (hg₁ j) (hg₂c j) (hang j)
  have hu1 : ∀ j, rungU c (g j) 1 = 0 := fun j => by unfold rungU pP; norm_num
  -- the per-rung `u` bound from the energy (Cvs.Prolate.Mellin.ModeMellinDyadicPiece)
  have hub : ∀ j, ∀ ξ ∈ Icc (1 : ℝ) (M * 2 ^ (J + 1)), |rungU c (g j) ξ| ≤ ξ * √(c * G j) := fun j ξ hξ => by
    rcases eq_or_lt_of_le hξ.1 with h | h
    · rw [← h, hu1, abs_zero]; positivity
    · exact Cvs.Prolate.Mellin.ModeMellinDyadicPiece.abs_u_le hc0 (hχ0 j) (hχc j) h (hG j ξ ⟨h, hξ.2⟩)
  -- the per-rung Mellin bounds (Cvs.L2a.TailModesPoleMellinValues)
  have hBj : ∀ j, ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, tailF (psi c (g j)) M (2 ^ (J + 1)) θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ|
          ≤ Cvs.L2a.TailModesPoleMellinValues.mellinBound c (χ j) (G j) η (2 * π * x') (psi c (g j) 1)
      ∧ |∫ θ in Ioi 1, tailF (psi c (g j)) M (2 ^ (J + 1)) θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ|
          ≤ Cvs.L2a.TailModesPoleMellinValues.mellinBound c (χ j) (G j) η (2 * π * x') (psi c (g j) 1) := fun j t ht => by
    obtain ⟨hψj, huj, hcj, -⟩ := hsys j
    have ht' : |t| ≤ 2 * π * x' := ht.le
    constructor
    · exact Cvs.L2a.TailModesPoleMellinValues.mellin_le (y := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky) (v := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ku)
        J hc0 (hχ0 j) (hχc j) (hT j) ht' (hG0 j) hηpos (hηθ j) (fun ξ hξ => hψj ξ hξ.1) (fun ξ _ => huj ξ)
        (hG j) hcj.continuousOn hM1 (hedge j)
        (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_ky hτ) (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_ku hτ)
        (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_ky_le hτ) (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_ku_le hτ)
    · exact Cvs.L2a.TailModesPoleMellinValues.mellin_le (y := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys) (v := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kus)
        J hc0 (hχ0 j) (hχc j) (hT j) ht' (hG0 j) hηpos (hηθ j) (fun ξ hξ => hψj ξ hξ.1) (fun ξ _ => huj ξ)
        (hG j) hcj.continuousOn hM1 (hedge j)
        (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_kys hτ) (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_kus hτ)
        (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_kys_le hτ) (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_kus_le hτ)
  -- the per-rung pole integrals (Cvs.L2a.TailModesPoleMellinValues)
  have hPj : ∀ j, |∫ θ in Ioi 1, tailF (psi c (g j)) M (2 ^ (J + 1)) θ| ≤ poleP c (χ j) (G j) := fun j => by
    obtain ⟨-, huj, hcj, -⟩ := hsys j
    exact Cvs.L2a.TailModesPoleMellinValues.pole_plus_le (ψ := psi c (g j)) (M := M) hc0 (hχ0 j) (hχc j) hb1 hΞ
      (sqrt_nonneg _) (fun ξ _ => huj ξ) (hub j) hcj.continuousOn
  have hPj' : ∀ j, |∫ θ in Ioi 1, tailF (psi c (g j)) M (2 ^ (J + 1)) θ / θ| ≤ poleP' c (χ j) (G j) := fun j => by
    obtain ⟨-, huj, hcj, -⟩ := hsys j
    exact Cvs.L2a.TailModesPoleMellinValues.pole_minus_le (ψ := psi c (g j)) (M := M) hc0 (hχ0 j) (hχc j) hb1 hΞ
      (sqrt_nonneg _) (fun ξ _ => huj ξ) (hub j) hcj.continuousOn
  exact L2a_span_of_per_rung (b := 2 ^ (J + 1)) N P R Kf g g₁ g₂ χ a
    (fun j => Cvs.L2a.TailModesPoleMellinValues.mellinBound c (χ j) (G j) η (2 * π * x') (psi c (g j) 1))
    (fun j => poleP c (χ j) (G j)) (fun j => poleP' c (χ j) (G j)) hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs
    hsmax hh hh' hh₂ hh₂' hη0 hη' hb4 hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden hκ hx hKf hfl hBj
    hPj hPj'

end Cvs.L2a.RungSpanFromRungData
