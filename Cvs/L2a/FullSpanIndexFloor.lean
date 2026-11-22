import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorBandCoupling
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullSpanConditional
import Cvs.L2a.FullSpanFrameFloor
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RegularSolutionEdge
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The index floor `σ̲(c) = 4c/log c` on every level of index `2j < 2x`, and L2a-FULL at that floor

At `c = 2πx ≥ 80` the level of index `2j` exists for `j < x` and lies below `c² − 4c/log c`. The strip term at
`4c/log c` obeys the closed-form threshold `c0Prime m = 25(129/m)⁸`, and L2a-FULL holds with (I) at `4c/log c`.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology

namespace Cvs.L2a.FullSpanIndexFloor

open Cvs.Prolate.EvenLevelIndexLemma (sigmaLow sigmaLow_pos_le le_ncard_sigmaLow)
open Cvs.L2a.FullSpanConditional (rSig rSig_anti rSig_le_of_small L2a_fulltail_full_sigma)

/-! ### The index on every level of index `2j < 2x` -/

/-- **The full index**: at `c = 2πx ≥ 80` and `j < x`, the level of index `2j` exists and
`4c/log c ≤ c² − lev c (2j)`. -/
theorem full_index (x : ℕ) (hx : 80 ≤ 2 * π * x) {j : ℕ} (hj : j < x) :
    (∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx (2 * π * x) (2 * j) χ) ∧
      sigmaLow (2 * π * x) ≤ (2 * π * x) ^ 2 - Cvs.Prolate.EvenRungsByIndex.lev (2 * π * x) (2 * j) := by
  have h1 := le_ncard_sigmaLow hx
  have hk : 2 * j < (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC (2 * π * x)) ∩
      Iio ((2 * π * x) ^ 2 - sigmaLow (2 * π * x))).ncard := by omega
  obtain ⟨χ, hlt, hidx⟩ := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_of_lt_ncard hk
  refine ⟨⟨χ, hidx⟩, ?_⟩
  rw [Cvs.Prolate.EvenRungsByIndex.lev_eq hidx]
  linarith

/-! ### `σ̲(c) = 4c/log c` -/

/-- `√c ≤ 4c/log c` for `c > 1`. -/
theorem sqrt_le_sigmaLow {c : ℝ} (hc : 1 < c) : √c ≤ sigmaLow c := by
  have hL : 0 < Real.log c := Real.log_pos hc
  have hr : 0 < √c := Real.sqrt_pos.2 (by linarith)
  have hl : Real.log c = 2 * Real.log √c := by
    rw [← Real.log_rpow hr, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (by linarith)]
  have h1 := Real.log_le_sub_one_of_pos hr
  have hsq : √c * √c = c := Real.mul_self_sqrt (by linarith)
  unfold sigmaLow
  rw [le_div_iff₀ hL]
  nlinarith

/-- `0 < 4c/log c` for `c > 1`. -/
theorem sigmaLow_pos {c : ℝ} (hc : 1 < c) : 0 < sigmaLow c :=
  (Real.sqrt_pos.2 (by linarith)).trans_le (sqrt_le_sigmaLow hc)

/-- `4c/log c ≤ 5c` for `c ≥ 80`. -/
theorem sigmaLow_le_five {c : ℝ} (hc : 80 ≤ c) : sigmaLow c ≤ 5 * c := by
  linarith [(sigmaLow_pos_le hc).2]

/-- `4c/log c` is monotone on `[e, ∞)`. -/
theorem sigmaLow_mono {c c' : ℝ} (hc : Real.exp 1 ≤ c) (hcc : c ≤ c') : sigmaLow c ≤ sigmaLow c' := by
  have hc0 : 0 < c := (Real.exp_pos 1).trans_le hc
  have hc'0 : 0 < c' := hc0.trans_le hcc
  have hL1 : 1 ≤ Real.log c := by rwa [Real.le_log_iff_exp_le hc0]
  have hL' : 0 < Real.log c' := by
    have := Real.log_le_log hc0 hcc
    linarith
  have hsplit : Real.log c' = Real.log c + Real.log (c' / c) := by
    rw [← Real.log_mul hc0.ne' (by positivity)]; congr 1; field_simp
  have hl := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < c' / c)
  have hcl : c * Real.log (c' / c) ≤ c' - c := by
    have := mul_le_mul_of_nonneg_left hl hc0.le
    rwa [mul_sub, mul_div_cancel₀ _ hc0.ne', mul_one] at this
  unfold sigmaLow
  rw [div_le_div_iff₀ (by linarith) hL', hsplit]
  nlinarith [mul_nonneg (sub_nonneg.2 hcc) (sub_nonneg.2 hL1)]

/-- `e ≤ 10¹⁶`. -/
theorem exp_one_le_c16 : Real.exp 1 ≤ 10 ^ 16 := by
  linarith [Real.exp_one_lt_d9]

/-- **The strip term at `4c/log c` is antitone in `c`**: `rSig σ̲(c) ≤ rSig σ̲(c₁)` for `e ≤ c₁ ≤ c`. -/
theorem rSig_sigmaLow_anti {c₁ c : ℝ} (hc₁ : Real.exp 1 ≤ c₁) (hc : c₁ ≤ c) :
    rSig (sigmaLow c) ≤ rSig (sigmaLow c₁) :=
  rSig_anti (sigmaLow_pos (lt_of_lt_of_le (by linarith [Real.add_one_lt_exp (one_ne_zero)]) hc₁))
    (sigmaLow_mono hc₁ hc)

/-! ### L2a-FULL with (I) at `4c/log c` -/

section main

variable {ι : Type} [Fintype ι]

/-- **L2a-FULL at the index floor `σ̲(c) = 4c/log c`**: (I) `4c/log c ≤ c² − χᵢ`, residual `ρ`, (BC) at `θ`, and
`θ + ρ + rSig(4c₁/log c₁) < 153/1000` give the conclusions of `L2a_fulltail_full_sigma` at every `c ≥ c₁ ≥ 10¹⁶`. -/
theorem L2a_fulltail_full_span_sigmaLow {μ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {κ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    {c₁ : ℝ} (hc₁ : 10 ^ 16 ≤ c₁) (hc : c₁ ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hI : ∀ i, sigmaLow c ≤ c ^ 2 - χ i)
    (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, Cvs.L2a.AngularProlateTailPositive.psi c (g i) t ^ 2)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc c (Fintype.card ι) M ≤ ρ)
    {θ : ℝ} (hBC : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorBandCoupling.BandCoupling c g μ a
      (Cvs.L2a.FullSpanFrameFloor.bandSet c χ) Cvs.L2a.FarIntegrationByParts.wF M θ)
    (hm : θ + ρ + rSig (sigmaLow c₁) < 153 / 1000)
    (hκ1 : 1 ≤ κ) (hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c κ) :
    (√(153 / 1000 - ρ - rSig (sigmaLow c₁) - θ + Cvs.L2a.SpanPlungeBound.epsTauFlat 5 ^ 2)
          - Cvs.L2a.SpanPlungeBound.epsTauFlat 5) ^ 2
        ≤ Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ (sigmaLow c) θ
      ∧ 0 < Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ (sigmaLow c) θ
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullSpanWiring.bBarFull c κ (Fintype.card ι)
              (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ (sigmaLow c) θ)
            * (∫ y in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail
                (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail
                (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull c κ (Fintype.card ι)
            (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ (sigmaLow c) θ)
          * (∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail
              (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * Cvs.L2a.AngularProlateTailPositive.psi c (g i) ξ) := by
  have hc16 : (10 : ℝ) ^ 16 ≤ c := hc₁.trans hc
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc16
  have hc₁e : Real.exp 1 ≤ c₁ := exp_one_le_c16.trans hc₁
  have hmin : min (sigmaLow c) (5 * c) = sigmaLow c := min_eq_left (sigmaLow_le_five hc80)
  have hr := rSig_sigmaLow_anti hc₁e hc
  obtain ⟨h0, h1, h2, h3⟩ := L2a_fulltail_full_sigma a hg hg₁ hg₂c hang hc16 hχ0
    (sigmaLow_pos (by linarith)) hI hχi heven hg0 hμ hidx hJ hmass hρ hBC (by rw [hmin]; linarith) hκ1 hT
  refine ⟨le_trans ?_ h0, h1, h2, h3⟩
  rw [hmin]
  exact Cvs.L2a.FullSpanFrameFloor.floorFn_mono (by linarith) (by linarith)

end main

end Cvs.L2a.FullSpanIndexFloor
