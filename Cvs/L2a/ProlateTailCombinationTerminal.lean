import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.StationaryPairsWeightedTotal
import Cvs.L2a.TailCombinationPrimeBilinear
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailModesAdmissible
import Cvs.L2a.TailModesPoleMellinValues
import Cvs.L2a.TailModesTerminalInequality
import Cvs.L2a.TailOfModes
import Cvs.L2a.TailPrimeSideMultiplicative
import Cvs.L2a.TailWeilFormFromBounds
import Cvs.L2a.TwoTailCrossPrimeSide
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
# L2a's terminal inequality for a combination of prolate tails

For prolates `ψ_j` (`j ∈ J`, each with its own `χ_j ≤ χ_m`, `χ_j ≤ c√c`, `|χ_i − χ_j| ≤ (3/4)c√c`, a common energy
bound `G`, Sonin's edge bound and `ψ_j(1)² ≤ KG`) and `F` the tail of `M` modes of `Σ_j a_j ψ_j`, `N = ∫F²`:
`(floorK − (floorK − a₀)·4x'B²/N − p/N − q/N) N ≤ W(f)`, where `B = Σ_j |a_j| B_j` sums the Mellin bounds of Cvs.L2a.TailModesPoleMellinValues,
`p = (Σ_j |a_j|)²` times `TwoTailCrossPrimeSide`'s cross bound at `χ_m`, and `q = (Σ_j |a_j|)²` times `TailModesTerminalInequality`'s pole bound at `χ_m`.
-/

namespace Cvs.L2a.ProlateTailCombinationTerminal

open Real Set MeasureTheory ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type*}

/-- The tail of a combination is the combination of the tails. -/
theorem tailF_sum (J : Finset ι) (a : ι → ℝ) (ψ : ι → ℝ → ℝ) (M : ℕ) (b θ : ℝ) :
    tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M b θ = ∑ j ∈ J, a j * tailF (ψ j) M b θ := by
  unfold tailF
  by_cases h : θ ∈ Ioc 1 b
  · simp only [indicator_of_mem h, Finset.mul_sum]
    rw [Finset.sum_comm]
  · simp [indicator_of_notMem h]

/-- **A weighted integral of the tail of a combination** is the combination of the weighted integrals. -/
theorem integral_tailF_sum_mul (J : Finset ι) (a : ι → ℝ) (ψ : ι → ℝ → ℝ) (g : ℝ → ℝ) (M : ℕ) {b : ℝ}
    (hb : 1 ≤ b) (hcont : ∀ j ∈ J, ∀ m ∈ Finset.Icc 1 M, ContinuousOn (fun θ => ψ j (m * θ) * g θ) (Icc 1 b)) :
    ∫ θ in Ioi 1, tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M b θ * g θ
      = ∑ j ∈ J, a j * ∫ θ in Ioi 1, tailF (ψ j) M b θ * g θ := by
  have hsum : ∀ m ∈ Finset.Icc 1 M,
      ContinuousOn (fun θ => (∑ j ∈ J, a j * ψ j (m * θ)) * g θ) (Icc 1 b) := fun m hm => by
    have e : (fun θ => (∑ j ∈ J, a j * ψ j (m * θ)) * g θ) = fun θ => ∑ j ∈ J, a j * (ψ j (m * θ) * g θ) := by
      funext θ; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    rw [e]
    exact continuousOn_finsetSum _ fun j hj => continuousOn_const.mul (hcont j hj m hm)
  rw [integral_tailF_mul _ g M hb hsum]
  have e1 : ∀ m ∈ Finset.Icc 1 M, ∫ θ in (1 : ℝ)..b, (∑ j ∈ J, a j * ψ j (m * θ)) * g θ
      = ∑ j ∈ J, a j * ∫ θ in (1 : ℝ)..b, ψ j (m * θ) * g θ := fun m hm => by
    have e : (fun θ => (∑ j ∈ J, a j * ψ j (m * θ)) * g θ) = fun θ => ∑ j ∈ J, a j * (ψ j (m * θ) * g θ) := by
      funext θ; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
    rw [e, intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro j _; rw [intervalIntegral.integral_const_mul]
    · intro j hj; exact ((hcont j hj m hm).intervalIntegrable_of_Icc hb).const_mul _
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  rw [integral_tailF_mul _ g M hb (hcont j hj), Finset.mul_sum]

/-- The cross prime bound of Cvs.L2a.TwoTailCrossPrimeSide. -/
noncomputable def crossBound (c χ G K : ℝ) : ℝ :=
  2 * (G * ((4 * Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / √c + 32 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √c / c ^ 2
      + 32 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ / (3 * c)) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
    + 96 * Cvs.L2a.StationaryPairsWeightedTotal.κw c χ * √(√c) / c ^ 2 * ∑' n : ℕ, Λ n / ((n : ℝ) * √n)
    + (Cvs.L2a.StationaryPairsWeightedTotal.Aw c χ K / c + 2 * Cvs.L2a.StationaryPairsWeightedTotal.Qw c χ / √c)
      * (log √c * (1 + log √c) ^ 2))
  + G / (√3 / 2 * √(c ^ 2 - χ)) * (π ^ 2 / 6) * ∑' n : ℕ, Λ n / (n : ℝ) ^ 2
  + 8 * G * √(2 * c / (√3 * √(c ^ 2 - χ))) / c ^ 2 * (36 * (π ^ 2 / 6 + 6)))

set_option maxHeartbeats 4000000 in
/-- **L2a's terminal inequality for the tail of a combination of prolates.** -/
theorem weilForm_tailF_sum_ge (J : Finset ι) (a χ : ι → ℝ) (ψ u : ι → ℝ → ℝ) {c χm G K Ξ η x' : ℝ}
    (P R N M Jd Kf : ℕ)
    (hc : 1 ≤ c) (hχ0 : ∀ j ∈ J, 0 ≤ χ j) (hχm : ∀ j ∈ J, χ j ≤ χm) (hχmc : χm < c ^ 2)
    (hχs : ∀ j ∈ J, χ j ≤ c * √c) (hΔ : ∀ i ∈ J, ∀ j ∈ J, |χ i - χ j| ≤ 3 / 4 * c * √c)
    (hψ : ∀ j ∈ J, ∀ ξ ∈ Ioc 1 Ξ, HasDerivAt (ψ j) (u j ξ / pP ξ) ξ)
    (hu : ∀ j ∈ J, ∀ ξ ∈ Icc 1 Ξ, HasDerivAt (u j) (-(qP c (χ j) ξ * ψ j ξ)) ξ) (hu1 : ∀ j ∈ J, u j 1 = 0)
    (hC1 : ∀ j ∈ J, ContDiffOn ℝ 1 (ψ j) (Icc 1 Ξ))
    (hG : ∀ j ∈ J, ∀ ξ ∈ Ioc 1 Ξ, energy (aP c (χ j)) (ψ j) (u j) ξ ≤ G) (hG0 : 0 ≤ G) (hK : 0 ≤ K)
    (hedge : ∀ j ∈ J, ∀ ξ ∈ Icc 1 Ξ, |ψ j ξ| ≤ |ψ j 1|) (hedge1 : ∀ j ∈ J, ψ j 1 ^ 2 ≤ K * G)
    (hM : 1 ≤ M) (hΞ : (M : ℝ) * 2 ^ (Jd + 1) ≤ Ξ)
    (hidx : Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R ⊆ Finset.Icc 2 N) (hrb : (N : ℝ) + 2 ≤ 2 ^ (Jd + 1))
    (hx : 0 < x') (hKf : 1 ≤ Kf) (hfl : archSymbol 0 ≤ floorK x' Kf)
    (hT : 2 * (2 * π * x') ^ 2 + 1 / 2 ≤ c ^ 2 - χm) (hη : 0 < η) (hηθ : 1 + η ≤ √(1 + √(c ^ 2 - χm) / c))
    (hN : 0 < ∫ θ in Ioi 1, tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M (2 ^ (Jd + 1)) θ ^ 2) :
    (floorK x' Kf - (floorK x' Kf - archSymbol 0)
        * (4 * x' * (∑ j ∈ J, |a j| * Cvs.L2a.TailModesPoleMellinValues.mellinBound c (χ j) G η (2 * π * x') (ψ j 1)) ^ 2
          / ∫ θ in Ioi 1, tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M (2 ^ (Jd + 1)) θ ^ 2)
        - (∑ j ∈ J, |a j|) ^ 2 * crossBound c χm G K
          / (∫ θ in Ioi 1, tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M (2 ^ (Jd + 1)) θ ^ 2)
        - (∑ j ∈ J, |a j|) ^ 2 * Cvs.L2a.TailModesTerminalInequality.poleBound c χm G
          / (∫ θ in Ioi 1, tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M (2 ^ (Jd + 1)) θ ^ 2))
      * (∫ θ in Ioi 1, tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M (2 ^ (Jd + 1)) θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ j ∈ J, a j * ψ j ξ) M (2 ^ (Jd + 1)))) := by
  set b : ℝ := 2 ^ (Jd + 1) with hbdef
  set ψs : ℝ → ℝ := fun ξ => ∑ j ∈ J, a j * ψ j ξ with hψs
  set F := tailF ψs M b with hFdef
  set Nn := ∫ θ in Ioi 1, F θ ^ 2 with hNn
  set S := ∑ j ∈ J, |a j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hc0 : 0 < c := by linarith
  have hb1 : (1 : ℝ) ≤ b := one_le_pow₀ (by norm_num)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hbΞ : b ≤ Ξ := le_trans (by nlinarith) hΞ
  have hMbΞ : (M : ℝ) * b ≤ Ξ := hΞ
  have hχ : ∀ j ∈ J, χ j < c ^ 2 := fun j hj => lt_of_le_of_lt (hχm j hj) hχmc
  have hcont : ∀ j ∈ J, ContinuousOn (ψ j) (Icc 1 Ξ) := fun j hj => (hC1 j hj).continuousOn
  have hIocIcc : ∀ ξ ∈ Ioc (1 : ℝ) Ξ, ξ ∈ Icc 1 Ξ := fun ξ h => ⟨h.1.le, h.2⟩
  have hC1s : ContDiffOn ℝ 1 ψs (Icc 1 Ξ) :=
    ContDiffOn.sum fun j hj => contDiffOn_const.mul (hC1 j hj)
  have hconts : ContinuousOn ψs (Icc 1 Ξ) := hC1s.continuousOn
  -- continuity of each mode against a weight continuous on `[1, b]`
  have hmode : ∀ j ∈ J, ∀ g : ℝ → ℝ, ContinuousOn g (Icc 1 b) → ∀ m ∈ Finset.Icc 1 M,
      ContinuousOn (fun θ => ψ j (m * θ) * g θ) (Icc 1 b) := fun j hj g hg m hm => by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    exact ((hcont j hj).comp (continuousOn_const.mul continuousOn_id) (fun (θ : ℝ) (hθ : θ ∈ Icc 1 b) =>
      ⟨one_le_mul_of_one_le_of_one_le hm1 hθ.1,
        (mul_le_mul hmM hθ.2 (show (0:ℝ) ≤ θ by linarith [hθ.1]) (Nat.cast_nonneg M)).trans hMbΞ⟩)).mul hg
  -- admissibility
  obtain ⟨h2, h1, hsq, hsh, hlevy⟩ := Cvs.L2a.TailModesAdmissible.admissible (M := M) hb1 hMbΞ hC1s
  have hFi : IntegrableOn F (Ioi 1) := by
    have hint : IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 M, ψs (m * θ)) (Ioc 1 b) := by
      apply ContinuousOn.integrableOn_Icc (a := 1) (b := b) _ |>.mono_set Ioc_subset_Icc_self
      apply continuousOn_finsetSum; intro m hm
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hmM : (m : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hm).2
      exact hconts.comp (continuousOn_const.mul continuousOn_id) (fun (θ : ℝ) (hθ : θ ∈ Icc 1 b) =>
        ⟨by nlinarith [hθ.1], le_trans (by nlinarith [hθ.2]) hΞ⟩)
    have := (integrable_indicator_iff measurableSet_Ioc).mpr hint
    exact this.integrableOn
  -- the Mellin bound below `2πx'`
  have hsubM : ∀ ξ ∈ Ioc (1 : ℝ) ((M : ℝ) * 2 ^ (Jd + 1)), ξ ∈ Ioc 1 Ξ := fun ξ h => ⟨h.1, h.2.trans hΞ⟩
  have h2b : (2 : ℝ) ≤ b := by
    rw [hbdef, pow_succ]; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := Jd)]
  have hedge2 : ∀ j ∈ J, ∀ ξ ∈ Icc (1 : ℝ) 2, |ψ j ξ| ≤ |ψ j 1| := fun j hj ξ h =>
    hedge j hj ξ ⟨h.1, h.2.trans (h2b.trans hbΞ)⟩
  have hTj : ∀ j ∈ J, 2 * (2 * π * x') ^ 2 + 1 / 2 ≤ c ^ 2 - χ j := fun j hj => by linarith [hχm j hj]
  have hηj : ∀ j ∈ J, 1 + η ≤ √(1 + √(c ^ 2 - χ j) / c) := fun j hj => by
    refine hηθ.trans (sqrt_le_sqrt ?_)
    have : √(c ^ 2 - χm) ≤ √(c ^ 2 - χ j) := sqrt_le_sqrt (by linarith [hχm j hj])
    have := div_le_div_of_nonneg_right this hc0.le
    linarith
  have hkyc : ∀ t : ℝ, ContinuousOn (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t) (Icc 1 b) := fun t τ hτ =>
    (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_ky (by linarith [hτ.1] : (0 : ℝ) < τ)).continuousAt.continuousWithinAt
  have hkysc : ∀ t : ℝ, ContinuousOn (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t) (Icc 1 b) := fun t τ hτ =>
    (Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_kys (by linarith [hτ.1] : (0 : ℝ) < τ)).continuousAt.continuousWithinAt
  have hB : ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ|
          ≤ ∑ j ∈ J, |a j| * Cvs.L2a.TailModesPoleMellinValues.mellinBound c (χ j) G η (2 * π * x') (ψ j 1)
      ∧ |∫ θ in Ioi 1, F θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ|
          ≤ ∑ j ∈ J, |a j| * Cvs.L2a.TailModesPoleMellinValues.mellinBound c (χ j) G η (2 * π * x') (ψ j 1) := by
    intro t ht
    have ht' : |t| ≤ 2 * π * x' := ht.le
    constructor
    · rw [hFdef, integral_tailF_sum_mul J a ψ _ M hb1 fun j hj => hmode j hj _ (hkyc t)]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact Cvs.L2a.TailModesPoleMellinValues.mellin_le (y := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky) (v := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ku)
        Jd hc0 (hχ0 j hj) (hχ j hj) (hTj j hj) ht' hG0 hη (hηj j hj)
        (fun ξ h => hψ j hj ξ (hsubM ξ h)) (fun ξ h => hu j hj ξ (hIocIcc ξ (hsubM ξ h)))
        (fun ξ h => hG j hj ξ (hsubM ξ h)) ((hcont j hj).mono (Icc_subset_Icc le_rfl hΞ)) hM (hedge2 j hj)
        (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_ky hτ) (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_ku hτ)
        (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_ky_le hτ) (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_ku_le hτ)
    · rw [hFdef, integral_tailF_sum_mul J a ψ _ M hb1 fun j hj => hmode j hj _ (hkysc t)]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact Cvs.L2a.TailModesPoleMellinValues.mellin_le (y := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys) (v := Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kus)
        Jd hc0 (hχ0 j hj) (hχ j hj) (hTj j hj) ht' hG0 hη (hηj j hj)
        (fun ξ h => hψ j hj ξ (hsubM ξ h)) (fun ξ h => hu j hj ξ (hIocIcc ξ (hsubM ξ h)))
        (fun ξ h => hG j hj ξ (hsubM ξ h)) ((hcont j hj).mono (Icc_subset_Icc le_rfl hΞ)) hM (hedge2 j hj)
        (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_kys hτ) (fun τ hτ => Cvs.Prolate.Mellin.MellinKernelSturmLiouville.hasDerivAt_kus hτ)
        (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_kys_le hτ) (fun τ hτ => Cvs.Prolate.Mellin.FirstModeMellinEdge.abs_kus_le hτ)
  -- the prime bound
  have hcontMb : ∀ j ∈ J, ContinuousOn (ψ j) (Icc 1 (M * b)) := fun j hj =>
    (hcont j hj).mono (Icc_subset_Icc le_rfl hMbΞ)
  have hNb : (N : ℝ) ≤ b := by linarith
  have hPr0 := Cvs.L2a.TailCombinationPrimeBilinear.primeSide_sum_le J a ψ P R N M hidx hNb hcontMb
  have hX : ∀ i ∈ J, ∀ j ∈ J, ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
      2 * Λ k * |∫ θ in Ioi 1, tailF (ψ i) M b θ * tailF (ψ j) M b (k * θ)| ≤ crossBound c χm G K :=
    fun i hi j hj => Cvs.L2a.TwoTailCrossPrimeSide.crossSide_le (ψa := ψ i) (ua := u i) (ψb := ψ j) (ub := u j) P R N M
      hc (hχ0 i hi) (hχm i hi) (hχ0 j hj) (hχm j hj) hχmc (hχs j hj) (hΔ i hi j hj) hidx hrb hMbΞ
      (hψ i hi) (fun ξ h => hu i hi ξ (hIocIcc ξ h)) (hψ j hj) (fun ξ h => hu j hj ξ (hIocIcc ξ h))
      (hG i hi) (hG j hj) hG0 hK (hcont i hi) (hcont j hj) (hedge i hi) (hedge1 i hi)
  have hPr1 : Cvs.Zeta.Explicit.Weil.primePowerSideTruncated P R
      (Cvs.Zeta.Explicit.Weil.selfConvolution (logScale F)) ≤ S ^ 2 * crossBound c χm G K := by
    refine hPr0.trans ?_
    calc ∑ i ∈ J, ∑ j ∈ J, |a i| * |a j| * ∑ k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R,
            2 * Λ k * |∫ θ in Ioi 1, tailF (ψ i) M b θ * tailF (ψ j) M b (k * θ)|
        ≤ ∑ i ∈ J, ∑ j ∈ J, |a i| * |a j| * crossBound c χm G K :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_left (hX i hi j hj) (by positivity)
      _ = S ^ 2 * crossBound c χm G K := by
          rw [hS, sq, Finset.sum_mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
  rw [Cvs.L2a.TailPrimeSideMultiplicative.primeSide_eq F (tailF_zero ψs M b)] at hPr1
  have hPr : ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R,
      2 * Real.log p * (∫ θ in Ioi 1, F θ * F ((p : ℝ) ^ r * θ)) ≤ S ^ 2 * crossBound c χm G K / Nn * Nn := by
    rw [div_mul_cancel₀ _ hN.ne']; exact hPr1
  -- the pole
  have hU : 0 ≤ √(c * G) := sqrt_nonneg _
  have hdm : 0 < c ^ 2 - χm := by linarith
  set Ap := π ^ 2 / 6 * (2 * √(c * G) / (c ^ 2 - χm) + 2 * c ^ 2 * √(c * G) / (c ^ 2 - χm) ^ 2) with hAp
  set Am := π ^ 2 / 6 * (2 * √(c * G) / (c ^ 2 - χm) + 3 * c ^ 2 * √(c * G) / (2 * (c ^ 2 - χm) ^ 2)) with hAm
  have hub : ∀ j ∈ J, ∀ ξ ∈ Icc 1 Ξ, |u j ξ| ≤ ξ * √(c * G) := fun j hj ξ hξ => by
    rcases eq_or_lt_of_le hξ.1 with h | h
    · rw [← h, hu1 j hj, abs_zero]; positivity
    · exact Cvs.Prolate.Mellin.ModeMellinDyadicPiece.abs_u_le hc0 (hχ0 j hj) (hχ j hj) h (hG j hj ξ ⟨h, hξ.2⟩)
  have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 1 b) := continuousOn_const
  have hinv : ContinuousOn (fun θ : ℝ => 1 / θ) (Icc 1 b) :=
    continuousOn_const.div continuousOn_id (fun θ hθ => by linarith [hθ.1])
  have hPp : |∫ θ in Ioi 1, F θ| ≤ S * Ap := by
    have e : ∫ θ in Ioi 1, F θ = ∑ j ∈ J, a j * ∫ θ in Ioi 1, tailF (ψ j) M b θ := by
      have := integral_tailF_sum_mul J a ψ (fun _ => (1 : ℝ)) M hb1 fun j hj => hmode j hj _ hone
      simpa only [mul_one] using this
    rw [e, hS, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h := Cvs.L2a.TailModesPoleMellinValues.pole_plus_le (ψ := ψ j) (M := M) hc0 (hχ0 j hj) (hχ j hj) hb1 hMbΞ hU
      (hu j hj) (hub j hj) (hcont j hj)
    refine h.trans ?_
    have hdj : c ^ 2 - χm ≤ c ^ 2 - χ j := by linarith [hχm j hj]
    rw [hAp]; gcongr
  have hPm : |∫ θ in Ioi 1, F θ / θ| ≤ S * Am := by
    have e : ∫ θ in Ioi 1, F θ / θ = ∑ j ∈ J, a j * ∫ θ in Ioi 1, tailF (ψ j) M b θ / θ := by
      have := integral_tailF_sum_mul J a ψ (fun θ => 1 / θ) M hb1 fun j hj => hmode j hj _ hinv
      simp only [mul_one_div] at this
      exact this
    rw [e, hS, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h := Cvs.L2a.TailModesPoleMellinValues.pole_minus_le (ψ := ψ j) (M := M) hc0 (hχ0 j hj) (hχ j hj) hb1 hMbΞ hU
      (hu j hj) (hub j hj) (hcont j hj)
    refine h.trans ?_
    have hdj : c ^ 2 - χm ≤ c ^ 2 - χ j := by linarith [hχm j hj]
    rw [hAm]; gcongr
  have hpole : -(S ^ 2 * Cvs.L2a.TailModesTerminalInequality.poleBound c χm G / Nn * Nn)
      ≤ 2 * (∫ θ in Ioi 1, F θ) * (∫ θ in Ioi 1, F θ / θ) := by
    rw [div_mul_cancel₀ _ hN.ne']
    have hpb : Cvs.L2a.TailModesTerminalInequality.poleBound c χm G = 2 * Ap * Am := by
      unfold Cvs.L2a.TailModesTerminalInequality.poleBound; rw [hAp, hAm]
    have hprod : |∫ θ in Ioi 1, F θ| * |∫ θ in Ioi 1, F θ / θ| ≤ S * Ap * (S * Am) :=
      mul_le_mul hPp hPm (abs_nonneg _) (le_trans (abs_nonneg _) hPp)
    have h3 : -(|∫ θ in Ioi 1, F θ| * |∫ θ in Ioi 1, F θ / θ|)
        ≤ (∫ θ in Ioi 1, F θ) * ∫ θ in Ioi 1, F θ / θ := by
      have := neg_abs_le ((∫ θ in Ioi 1, F θ) * ∫ θ in Ioi 1, F θ / θ)
      rwa [abs_mul] at this
    rw [hpb]
    nlinarith
  have key := Cvs.L2a.TailWeilFormFromBounds.weilForm_tail_ge (F := F) P R (tailF_zero ψs M b) hFi h2 h1 hsq hsh hlevy
    hx hKf hfl hN hB hPr hpole
  linarith [key]

end Cvs.L2a.ProlateTailCombinationTerminal
