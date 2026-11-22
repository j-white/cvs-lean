import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.ExactRootWeightedPairTotal
import Cvs.L2a.ModeTailPrimeSideExactRoot
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesAdmissible
import Cvs.L2a.TailModesPoleMellinValues
import Cvs.L2a.TailModesTerminalInequality
import Cvs.L2a.TailOfModes
import Cvs.L2a.TailPrimeSideMultiplicative
import Cvs.L2a.TailWeilFormFromBounds
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.FirstModeMellinEdge
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.Prolate.Mellin.ModeMellinDyadicPiece
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
# L2a's terminal inequality for the tail of `M` modes, for every `χ < c²`

Cvs.L2a.TailModesTerminalInequality with `ModeTailPrimeSideExactRoot`'s prime bound: for `ℓ ≤ (c² − χ)/c²`, `(3/5)√c ℓ ≥ 1`,
`(floorK − (floorK − a₀)·4x'B²/N − p/N − q/N) N ≤ W(f)`, `p` the bound of Cvs.L2a.ModeTailPrimeSideExactRoot, `B`, `q` as in Cvs.L2a.TailModesTerminalInequality.
-/

namespace Cvs.L2a.ModeTailTerminalExactRoot

open Real Set MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)
open ArithmeticFunction

/-- The prime bound of Cvs.L2a.ModeTailPrimeSideExactRoot. -/
noncomputable def primeBound (c χ G K ℓ : ℝ) : ℝ :=
  2 * (G * (Cvs.L2a.ExactRootWeightedPairTotal.C1 c χ K ℓ * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
      + 3 * Cvs.L2a.ExactRootWeightedPairTotal.C3 c χ ℓ * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
      + Cvs.L2a.ExactRootWeightedPairTotal.Hc c χ K ℓ * (log (3 / 5 * (√c * ℓ)) * (1 + log (3 / 5 * (√c * ℓ))) ^ 2))
    + G / (3 / 4 * c) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
    + 8 * G * (2 / √3) / c ^ 2 * (36 * (π ^ 2 / 6 + 6)))

set_option maxHeartbeats 1000000 in
/-- **L2a's terminal inequality for the tail of `M` modes, for every `χ < c²`.** -/
theorem weilForm_tailF_ge {c χ G K Ξ η x' ℓ : ℝ} {ψ u : ℝ → ℝ} (P R N M J Kf : ℕ)
    (hc : 1 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hℓ0 : 0 < ℓ) (hℓ : ℓ ≤ (c ^ 2 - χ) / c ^ 2)
    (hsℓ : 1 ≤ 3 / 5 * (√c * ℓ))
    (hψ : ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Icc 1 Ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ) (hu1 : u 1 = 0)
    (hC1 : ContDiffOn ℝ 1 ψ (Icc 1 Ξ))
    (hG : ∀ ξ ∈ Ioc 1 Ξ, energy (aP c χ) ψ u ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hedge : ∀ ξ ∈ Icc 1 Ξ, |ψ ξ| ≤ |ψ 1|) (hedge1 : ψ 1 ^ 2 ≤ K * G)
    (hM : 1 ≤ M) (hΞ : (M : ℝ) * 2 ^ (J + 1) ≤ Ξ)
    (hidx : Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N) (hrb : (N : ℝ) + 2 ≤ 2 ^ (J + 1))
    (hx : 0 < x') (hKf : 1 ≤ Kf) (hfl : archSymbol 0 ≤ floorK x' Kf)
    (hT : 2 * (2 * π * x') ^ 2 + 1 / 2 ≤ c ^ 2 - χ) (hη : 0 < η) (hηθ : 1 + η ≤ √(1 + √(c ^ 2 - χ) / c))
    (hN : 0 < ∫ θ in Ioi 1, tailF ψ M (2 ^ (J + 1)) θ ^ 2) :
    (floorK x' Kf - (floorK x' Kf - archSymbol 0)
        * (4 * x' * Cvs.L2a.TailModesPoleMellinValues.mellinBound c χ G η (2 * π * x') (ψ 1) ^ 2
          / ∫ θ in Ioi 1, tailF ψ M (2 ^ (J + 1)) θ ^ 2)
        - primeBound c χ G K ℓ / (∫ θ in Ioi 1, tailF ψ M (2 ^ (J + 1)) θ ^ 2)
        - Cvs.L2a.TailModesTerminalInequality.poleBound c χ G / (∫ θ in Ioi 1, tailF ψ M (2 ^ (J + 1)) θ ^ 2))
      * (∫ θ in Ioi 1, tailF ψ M (2 ^ (J + 1)) θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF ψ M (2 ^ (J + 1)))) := by
  set b : ℝ := 2 ^ (J + 1) with hbdef
  set F := tailF ψ M b with hFdef
  set Nn := ∫ θ in Ioi 1, F θ ^ 2 with hNn
  have hc0 : 0 < c := by linarith
  have hb1 : (1 : ℝ) ≤ b := one_le_pow₀ (by norm_num)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : b ≤ Ξ := le_trans (by nlinarith) hΞ
  have hcont : ContinuousOn ψ (Icc 1 Ξ) := hC1.continuousOn
  have hIocIcc : ∀ ξ ∈ Ioc (1 : ℝ) Ξ, ξ ∈ Icc 1 Ξ := fun ξ h => ⟨h.1.le, h.2⟩
  -- the flux envelope, `|u(ξ)| ≤ ξ√(cG)`, `u(1) = 0`
  have hub : ∀ ξ ∈ Icc 1 Ξ, |u ξ| ≤ ξ * √(c * G) := fun ξ hξ => by
    rcases eq_or_lt_of_le hξ.1 with h | h
    · rw [← h, hu1, abs_zero]; positivity
    · exact Cvs.Prolate.Mellin.ModeMellinDyadicPiece.abs_u_le hc0 hχ0 hχ h (hG ξ ⟨h, hξ.2⟩)
  -- admissibility
  obtain ⟨h2, h1, hsq, hsh, hlevy⟩ := Cvs.L2a.TailModesAdmissible.admissible (M := M) hb1 (le_trans (by nlinarith) hΞ) hC1
  have hFi : IntegrableOn F (Ioi 1) := by
    have hint : IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 M, ψ (m * θ)) (Ioc 1 b) := by
      apply ContinuousOn.integrableOn_Icc (a := 1) (b := b) _ |>.mono_set Ioc_subset_Icc_self
      apply continuousOn_finsetSum; intro m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      exact hcont.comp (continuousOn_const.mul continuousOn_id) (fun θ hθ =>
        ⟨by nlinarith [hθ.1], le_trans (by nlinarith [hθ.2]) hΞ⟩)
    have := (integrable_indicator_iff measurableSet_Ioc).mpr hint
    exact this.integrableOn
  -- the Mellin bound below 2πx'
  have hsubM : ∀ ξ ∈ Ioc (1 : ℝ) ((M : ℝ) * 2 ^ (J + 1)), ξ ∈ Ioc 1 Ξ := fun ξ h => ⟨h.1, h.2.trans hΞ⟩
  have hedge2 : ∀ ξ ∈ Icc (1 : ℝ) 2, |ψ ξ| ≤ |ψ 1| := fun ξ h =>
    hedge ξ ⟨h.1, h.2.trans (by
      have : (2 : ℝ) ≤ b := by rw [hbdef, pow_succ]; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := J)]
      linarith)⟩
  have hB : ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ Cvs.L2a.TailModesPoleMellinValues.mellinBound c χ G η (2 * π * x') (ψ 1)
      ∧ |∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ Cvs.L2a.TailModesPoleMellinValues.mellinBound c χ G η (2 * π * x') (ψ 1) := by
    intro t ht
    have ht' : |t| ≤ 2 * π * x' := ht.le
    have hc' := hcont.mono (Icc_subset_Icc le_rfl hΞ)
    constructor
    · exact Cvs.L2a.TailModesPoleMellinValues.mellin_le (y := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky) (v := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ku)
        J hc0 hχ0 hχ hT ht' hG0 hη hηθ (fun ξ h => hψ ξ (hsubM ξ h)) (fun ξ h => hu ξ (hIocIcc ξ (hsubM ξ h)))
        (fun ξ h => hG ξ (hsubM ξ h)) hc' hM hedge2
        (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_ky hτ) (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_ku hτ)
        (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_ky_le hτ) (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_ku_le hτ)
    · exact Cvs.L2a.TailModesPoleMellinValues.mellin_le (y := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys) (v := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kus)
        J hc0 hχ0 hχ hT ht' hG0 hη hηθ (fun ξ h => hψ ξ (hsubM ξ h)) (fun ξ h => hu ξ (hIocIcc ξ (hsubM ξ h)))
        (fun ξ h => hG ξ (hsubM ξ h)) hc' hM hedge2
        (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_kys hτ) (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_kus hτ)
        (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_kys_le hτ) (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_kus_le hτ)
  -- the prime bound
  have hPr0 := Cvs.L2a.ModeTailPrimeSideExactRoot.primeSide_tail_le (ψ := ψ) (u := u) (K := K) P R N M hc hχ0 hχ hℓ0 hℓ hsℓ hidx hrb hΞ
    hψ (fun ξ h => hu ξ (hIocIcc ξ h)) hG hG0 hK hcont hedge hedge1
  rw [Cvs.L2a.TailPrimeSideMultiplicative.primeSide_eq F (tailF_zero ψ M b)] at hPr0
  have hPr : ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
      2 * Real.log p * (∫ θ in Ioi 1, F θ * F ((p : ℝ) ^ r * θ)) ≤ primeBound c χ G K ℓ / Nn * Nn := by
    rw [div_mul_cancel₀ _ hN.ne']; exact hPr0
  -- the pole
  have hU : 0 ≤ √(c * G) := sqrt_nonneg _
  have hAp := Cvs.L2a.TailModesPoleMellinValues.pole_plus_le (ψ := ψ) (M := M) hc0 hχ0 hχ hb1 (le_trans (by nlinarith) hΞ) hU hu hub hcont
  have hAm := Cvs.L2a.TailModesPoleMellinValues.pole_minus_le (ψ := ψ) (M := M) hc0 hχ0 hχ hb1 (le_trans (by nlinarith) hΞ) hU hu hub hcont
  have hpole : -(Cvs.L2a.TailModesTerminalInequality.poleBound c χ G / Nn * Nn) ≤ 2 * (∫ θ in Ioi 1, F θ) * (∫ θ in Ioi 1, F θ / θ) := by
    rw [div_mul_cancel₀ _ hN.ne']
    unfold Cvs.L2a.TailModesTerminalInequality.poleBound
    have hprod : |∫ θ in Ioi 1, F θ| * |∫ θ in Ioi 1, F θ / θ|
        ≤ (π ^ 2 / 6 * (2 * √(c * G) / (c ^ 2 - χ) + 2 * c ^ 2 * √(c * G) / (c ^ 2 - χ) ^ 2))
          * (π ^ 2 / 6 * (2 * √(c * G) / (c ^ 2 - χ) + 3 * c ^ 2 * √(c * G) / (2 * (c ^ 2 - χ) ^ 2))) :=
      mul_le_mul hAp hAm (abs_nonneg _) (le_trans (abs_nonneg _) hAp)
    have h3 : -(|∫ θ in Ioi 1, F θ| * |∫ θ in Ioi 1, F θ / θ|)
        ≤ (∫ θ in Ioi 1, F θ) * ∫ θ in Ioi 1, F θ / θ := by
      have := neg_abs_le ((∫ θ in Ioi 1, F θ) * ∫ θ in Ioi 1, F θ / θ)
      rwa [abs_mul] at this
    linarith
  have key := Cvs.L2a.TailWeilFormFromBounds.weilForm_tail_ge (F := F) P R (tailF_zero ψ M b) hFi h2 h1 hsq hsh hlevy
    hx hKf hfl hN hB hPr hpole
  linarith [key]

end Cvs.L2a.ModeTailTerminalExactRoot
