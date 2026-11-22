import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandCouplingDischarged
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandSumThreshold
import Cvs.L2a.CoreArmIdentity
import Cvs.L2a.CornerSplitSqrtFloor
import Cvs.L2a.CutKernelRemainder
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarFarConstantClosedForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorBandCoupling
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullSpanConditional
import Cvs.L2a.FullSpanFrameFloor
import Cvs.L2a.FullSpanIndexFloor
import Cvs.L2a.FullSpanLowConstant
import Cvs.L2a.FullSpanProlateFamily
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.JointMainTerm
import Cvs.L2a.LocalisedBottomCorners
import Cvs.L2a.LocalisedConstants
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TopCornerSum
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.ForbiddenZoneClosedForm
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.LandauLowerPivot
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Upstream.CosineTransformHalfLine
import Cvs.Upstream.QuinticSmoothStep
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L2a-FULL on `Finset.range x` of the prolate family at `c = 2πx ≥ c₀^F`, band edge `10`
`FullSpanFrameFloor`'s JA with the deep rungs at `s·c ≤ c² − χ` (`ε_τ(s)`) and the main term at any `R ≥ r1main + botMain`; `BandCouplingDischarged`'s
arm at edge `s` (`f̄(c, s)`). At `s = 10`, `R = RbarJ`, `σ̲ = 4c/log c`, `ρ = 7c^{−1/8}`, Landau's pivot (Cvs.Prolate.LandauLowerPivot),
the paired deficit `D̄ = plungeBound c` and `BandECouplingCollar`'s E-coupling `ē_main(c, 10)(1 + ω)²`, `BandSumThreshold`'s margin gives
`κ_F ≥ 1/38` and Cvs.L2a.FullSpanThreshold gives `b̄ ≥ 1` at `κ = κ⋆_F`. THEOREM E's inputs on the band enter as `BandInputs x a K_r`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.Upstream.CosineTransformDilation Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption Cvs.L2a.CleanBandDilation Cvs.L2a.DilationCornerSplit Cvs.L2a.CornerSplitSqrtFloor

namespace Cvs.L2a.FullSpanInstance

open Cvs.L2a.FrameFloorIntegerM (resLoc cEtaClosed_nonneg gammaD_le gammaE1_le)
open Cvs.L2a.FrameFloorBandCoupling (BandCoupling)

/-! ### `ε_τ(10)` -/

/-- **`ε_τ(10) ≤ 10⁻⁵`**: the window term at `Z = 10π/4` is `≤ 1.21·10⁻⁵`, the large-`S` term at `Z = 5π` is
`≤ 10⁻¹⁰`, and `1 + √(20/(11π)) ≥ 1.76`. -/
theorem epsTauFlat_ten_le : Cvs.L2a.SpanPlungeBound.epsTauFlat 10 ≤ 1 / 100000 := by
  have hk := Cvs.L2a.SpanPlungeBound.one_add_sqrt_ge
  have hπl := Real.pi_gt_d4
  have hπu := Real.pi_lt_d4
  have he1 := Real.exp_one_gt_d9
  have he0 : (0 : ℝ) < 2.7182818283 := by norm_num
  set r := √((π * 10 / 4) ^ 2 + 9 / 4) with hrdef
  have hr1 : (7995 / 1000 : ℝ) ≤ r := by
    rw [hrdef, Real.le_sqrt' (by norm_num)]; nlinarith
  have hr2 : r ≤ 7997 / 1000 := by
    rw [hrdef, Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_pos]
  have hL : (2.7182818283 : ℝ) ^ 12 * (1 + 99 / 100 + (99 / 100) ^ 2 / 2)
      ≤ Real.exp (12 + 99 / 100) := by
    rw [Real.exp_add, show Real.exp 12 = Real.exp 1 ^ 12 by rw [← Real.exp_nat_mul]; norm_num]
    exact mul_le_mul (pow_le_pow_left₀ he0.le he1.le 12)
      (Real.quadratic_le_exp_of_nonneg (by norm_num)) (by norm_num) (by positivity)
  have hX0 : Real.exp (3 - 2 * r)
      ≤ 1 / ((2.7182818283 : ℝ) ^ 12 * (1 + 99 / 100 + (99 / 100) ^ 2 / 2)) := by
    calc Real.exp (3 - 2 * r) ≤ Real.exp (-(12 + 99 / 100)) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / Real.exp (12 + 99 / 100) := by rw [Real.exp_neg, one_div]
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) hL
  have hX : Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC (π * 10 / 4)))
      ≤ 1 / ((2.7182818283 : ℝ) ^ 12 * (1 + 99 / 100 + (99 / 100) ^ 2 / 2))
        * (7997 / 1000 + 1 / 2) / 2 := by
    rw [Cvs.Prolate.ForbiddenZoneClosedForm.exp_neg_two_PhiC, ← hrdef]
    gcongr
  have hY0 := Cvs.Prolate.ForbiddenZoneClosedForm.exp_neg_two_PhiC_le (Z := π * max 10 20 / 4) (by positivity)
  rw [show max (10 : ℝ) 20 = 20 by norm_num] at hY0
  have hE : Real.exp 3 * Real.exp (-(2 * (π * 20 / 4))) ≤ 1 / (2.7182818283 : ℝ) ^ 28 := by
    rw [← Real.exp_add]
    calc Real.exp (3 + -(2 * (π * 20 / 4))) ≤ Real.exp (-28) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / Real.exp 1 ^ 28 := by
          rw [Real.exp_neg, ← Real.exp_nat_mul, one_div]; norm_num
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ he0.le he1.le 28)
  have hY : Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC (π * 20 / 4)))
      ≤ (5 * 31416 / 10000 + 2) / 2 / (2.7182818283 : ℝ) ^ 28 := by
    refine hY0.trans ?_
    calc Real.exp 3 / 2 * (π * 20 / 4 + 2) * Real.exp (-(2 * (π * 20 / 4)))
        = (π * 20 / 4 + 2) / 2 * (Real.exp 3 * Real.exp (-(2 * (π * 20 / 4)))) := by ring
      _ ≤ (5 * 31416 / 10000 + 2) / 2 * (1 / (2.7182818283 : ℝ) ^ 28) := by
          apply mul_le_mul (by linarith) hE (by positivity) (by positivity)
      _ = _ := by ring
  have hC := Cvs.L2a.SpanPlungeBound.Cbig_le
  have hC0 := Cvs.L2a.SpanPlungeBound.Cbig_pos
  unfold Cvs.L2a.SpanPlungeBound.epsTauFlat Cvs.L2a.SpanPlungeBound.plungeFlat
  rw [show max (10 : ℝ) 20 = 20 by norm_num, div_le_iff₀ (by positivity)]
  apply max_le
  · have : 8 / 7 * Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC (π * 10 / 4)))
        ≤ 8 / 7 * (1 / ((2.7182818283 : ℝ) ^ 12 * (1 + 99 / 100 + (99 / 100) ^ 2 / 2))
          * (7997 / 1000 + 1 / 2) / 2) := by gcongr
    have h2 : 8 / 7 * (1 / ((2.7182818283 : ℝ) ^ 12 * (1 + 99 / 100 + (99 / 100) ^ 2 / 2))
          * (7997 / 1000 + 1 / 2) / 2) ≤ 1 / 100000 * (176 / 100) := by norm_num
    nlinarith
  · have : Cvs.L2a.SpanPlungeBound.Cbig * Real.exp (-(2 * Cvs.Prolate.ForbiddenZoneGrowth.PhiC (π * 20 / 4)))
        ≤ 71 / 10 * ((5 * 31416 / 10000 + 2) / 2 / (2.7182818283 : ℝ) ^ 28) :=
      mul_le_mul hC hY (Real.exp_pos _).le (by norm_num)
    have h2 : 71 / 10 * ((5 * 31416 / 10000 + 2) / 2 / (2.7182818283 : ℝ) ^ 28)
        ≤ 1 / 100000 * (176 / 100) := by norm_num
    nlinarith

/-! ### JA with the deep rungs at edge `s` and the main term at `R` -/

section consts

/-- **The JA margin at `(ε, R)`**: `A = ½ − 3ε − √(C_η(c₀)/c) − (R + ρ + γ_D + γ_E₁ + r₁ + r_S(c, σ₀)) − θ`. -/
def aJAfullG (c₀ c J ρ σ₀ θ ε R : ℝ) : ℝ :=
  1 / 2 - 3 * ε - √(Cvs.L2a.FarFarConstantClosedForm.cEtaClosed c₀ / c)
    - (R + ρ + (Cvs.L2a.CutKernelRemainder.γD c J + Cvs.L2a.CutKernelRemainder.γE1 c J)
      + Cvs.L2a.MiddlePartQStep.rOne c + Cvs.L2a.MiddlePartQStep.rStrip c σ₀) - θ

/-- **The floor constant at `(ε, R)`**: `κ = (√(A + ε²) − ε)²`. -/
def kappaFfullG (c₀ c J ρ σ₀ θ ε R : ℝ) : ℝ :=
  (√(aJAfullG c₀ c J ρ σ₀ θ ε R + ε ^ 2) - ε) ^ 2

/-- At `ε = ε_τ(5)`, `R = R̄` the constants are `FullSpanFrameFloor`'s. -/
theorem kappaFfullG_five (c₀ c J ρ σ₀ θ : ℝ) :
    kappaFfullG c₀ c J ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat 5) Cvs.L2a.LocalisedConstants.Rbar
      = Cvs.L2a.FullSpanFrameFloor.kappaFfull c₀ c J ρ σ₀ θ := rfl

/-- **`A ≥ ½ − 3ε − R − 1.3·10⁻⁵ − ρ − r_S(c, σ₀) − θ`** for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1`. -/
theorem aJAfullG_ge {c J ρ σ₀ θ ε R : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    1 / 2 - 3 * ε - R - 13 / 10 ^ 6 - ρ - Cvs.L2a.MiddlePartQStep.rStrip c σ₀ - θ
      ≤ aJAfullG (10 ^ 16) c J ρ σ₀ θ ε R := by
  have hJc : J ≤ c := by linarith
  have h2 := Cvs.L2a.LocalisedConstants.eta_le_c0 hc
  have h3 := Cvs.L2a.LocalisedConstants.rOne_le_c0 hc
  have h6 := gammaD_le hc hJ0 hJc
  have h7 := gammaE1_le hc hJc
  unfold aJAfullG
  norm_num at h2 h3 h6 h7 ⊢
  linarith

/-- `A > 0` gives `κ > 0` at any `ε ≥ 0`. -/
theorem kappaFfullG_pos {c₀ c J ρ σ₀ θ ε R : ℝ} (hε : 0 ≤ ε) (hA : 0 < aJAfullG c₀ c J ρ σ₀ θ ε R) :
    0 < kappaFfullG c₀ c J ρ σ₀ θ ε R := by
  unfold kappaFfullG
  have hlt : ε < √(aJAfullG c₀ c J ρ σ₀ θ ε R + ε ^ 2) := by
    rw [Real.lt_sqrt hε]; linarith
  exact pow_pos (by linarith) 2

end consts

section floor

open Cvs.L2a.FarIntegrationByParts

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}

/-- **JA at one integer `M`, edge `s`**: `FullSpanFrameFloor`'s `JA_floor_full` with `5c` replaced by `s·c` (`s ≥ 5`, `ε = ε_τ(s)`)
off `S` and `R̄` replaced by any `R ≥ r1main + botMain`. -/
theorem JA_floor_G (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 4096 ≤ c) {c₀ : ℝ} (hc₀ : 1 ≤ c₀) (hcc : c₀ ≤ c)
    (hχ0 : ∀ i, 0 ≤ χ i) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hshell : Cvs.L2a.LocalisedBottomCorners.ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) χ g a)
    (S : Finset ι) {sb : ℝ} (hsb : 5 ≤ sb) (hdeep : ∀ i ∉ S, sb * c ≤ c ^ 2 - χ i)
    {R : ℝ} (hR : ∀ κ : ℝ, κ ≤ 1 → ∀ M : ℕ, 3 ≤ M →
      Cvs.L2a.LocalisedConstants.r1main κ M + Cvs.L2a.LocalisedConstants.botMain κ M ≤ R)
    {M : ℕ} (hM3 : 3 ≤ M) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2)
    {ρ : ℝ} (hρ : resLoc c (Fintype.card ι) M ≤ ρ) {θ : ℝ} (hBC : BandCoupling c g μ a S wF M θ)
    (hA : 0 ≤ aJAfullG c₀ c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R) :
    kappaFfullG c₀ c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R
        * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hc80 : 80 ≤ c := by linarith
  have hχc : ∀ i, χ i ≤ c ^ 2 := fun i => by linarith [hσ i]
  have hsign := Cvs.Prolate.EdgeCentreSign.hsign_of_even_index hc0 hχ0 hg hg₁ hg₂c hang heven hg0 hμ hidx
  have hτ : ∀ i ∉ S, 1 - Cvs.L2a.SpanPlungeBound.epsTauFlat sb ≤ μ i * √(c / (2 * π)) := fun i hi =>
    Cvs.L2a.SpanPlungeBound.tau_flat (hg i) (hg₁ i) (hg₂c i) (hang i) hc80 (hχ0 i) hsb (hdeep i hi) (heven i)
      (hg0 i) (hμ i) (hsign i)
  have hηb := Cvs.L2a.FarFarConstantClosedForm.farFar_le_closed_of_le a hg hg₁ hg₂c hang hc₀ hcc hχi hχ0 hχc
  have hη : ∫ y in Ioi 1, ‖(wF y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ √(Cvs.L2a.FarFarConstantClosedForm.cEtaClosed c₀ / c) ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
    rwa [Real.sq_sqrt (div_nonneg (cEtaClosed_nonneg c₀) hc0.le)]
  have hcor := Cvs.L2a.FullSpanFrameFloor.corners_ge_loc_full a hg hg₁ hg₂c hang hc hχ0 hσ₀ hσ hχi hM3 hmass hshell
  have hκ : Cvs.L2a.LocalisedBottomCorners.kapI c (Fintype.card ι) ≤ 1 :=
    (Cvs.L2a.LocalisedConstants.kappaI_mem (by linarith) (Nat.cast_nonneg _) hJ).2
  have hmain := hR _ hκ M hM3
  have hP0 : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hsum : -(R + ρ
        + (Cvs.L2a.CutKernelRemainder.γD c (Fintype.card ι) + Cvs.L2a.CutKernelRemainder.γE1 c (Fintype.card ι))
        + Cvs.L2a.MiddlePartQStep.rOne c + Cvs.L2a.MiddlePartQStep.rStrip c σ₀)
        * (∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2)
      ≤ DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2)
        + DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2)
        + DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2) := by
    refine le_trans ?_ hcor
    refine mul_le_mul_of_nonneg_right ?_ hP0
    linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hwX : ∀ x, (M : ℝ) < x → wF x = 1 := fun x hx => by
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM3
    exact (wF_of_two_le (by linarith)).1
  exact Cvs.L2a.FrameFloorBandCoupling.FF_of_corners_split_S a hg hg₁ hg₂c hang hc0 hχi heven hμ S
    (Cvs.L2a.SpanPlungeBound.epsTauFlat_nonneg sb) hτ continuous_wF.1.measurable
    (fun x => (Cvs.L2a.FarFarBound.wF_bounds x).1) (fun x => (Cvs.L2a.FarFarBound.wF_bounds x).2.1) hM1 hwX
    (Real.sqrt_nonneg _) hη hsum hBC hA

/-- **THEOREM JA at edge `s`**: for `c ≥ 10¹⁶`, `0 < σ₀ ≤ c² − χᵢ`, `s·c ≤ c² − χᵢ` off `S`, (BC) on `S` at `θ`,
`resLoc ≤ ρ`, `R ≥ r1main + botMain` and `A > 0`: `κ > 0` and `κ·Σ aᵢ²∫₁^M ψᵢ² ≤ N(M)` at every `M ≥ 3`. -/
theorem JA_integer_floor_G (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 16 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i)
    (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hmass3 : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2)
    (S : Finset ι) {sb : ℝ} (hsb : 5 ≤ sb) (hdeep : ∀ i ∉ S, sb * c ≤ c ^ 2 - χ i)
    {R : ℝ} (hR : ∀ κ : ℝ, κ ≤ 1 → ∀ M : ℕ, 3 ≤ M →
      Cvs.L2a.LocalisedConstants.r1main κ M + Cvs.L2a.LocalisedConstants.botMain κ M ≤ R)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → resLoc c (Fintype.card ι) M ≤ ρ)
    {θ : ℝ} (hBC : ∀ M : ℕ, 3 ≤ M → BandCoupling c g μ a S wF M θ)
    (hA : 0 < aJAfullG (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R) :
    0 < kappaFfullG (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R
      ∧ ∀ M : ℕ, 3 ≤ M → (∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) →
        kappaFfullG (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R
            * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
          ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2 := by
  have hc4 : (4096 : ℝ) ≤ c := le_trans (by norm_num) hc
  have hshell := Cvs.L2a.FullSpanFrameFloor.shellM2_strip a hg hg₁ hg₂c hang hc4 hχ0 hσ₀ hσ hχi hmass3
  refine ⟨kappaFfullG_pos (Cvs.L2a.SpanPlungeBound.epsTauFlat_nonneg sb) hA, fun M hM3 hmass => ?_⟩
  exact JA_floor_G a hg hg₁ hg₂c hang hc4 (by norm_num) hc hχ0 hσ₀ hσ hχi heven hg0 hμ hidx hJ hshell S hsb
    hdeep hR hM3 hmass (hρ M hM3) (hBC M hM3) hA.le

end floor

/-! ### The full-tail L2a at edge `s` -/

section wiring

variable {ι : Type} [Fintype ι]

/-- **L2a-FULL at edge `s`**: under `JA_integer_floor_G`'s hypotheses, `κ ≥ 1` and `T ≥ 2`, the floor
`κ_F = kappaFfullG 10¹⁶ c J ρ σ₀ θ ε_τ(s) R` is positive and gives `b̄·N(M) ≤ W(M)` and `b̄·N_∞ ≤ W_∞`. -/
theorem L2a_fulltail_G {μ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 16 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i)
    (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2)
    (S : Finset ι) {sb : ℝ} (hsb : 5 ≤ sb) (hdeep : ∀ i ∉ S, sb * c ≤ c ^ 2 - χ i)
    {R : ℝ} (hR : ∀ κ : ℝ, κ ≤ 1 → ∀ M : ℕ, 3 ≤ M →
      Cvs.L2a.LocalisedConstants.r1main κ M + Cvs.L2a.LocalisedConstants.botMain κ M ≤ R)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → resLoc c (Fintype.card ι) M ≤ ρ)
    {θ : ℝ} (hBC : ∀ M : ℕ, 3 ≤ M → BandCoupling c g μ a S Cvs.L2a.FarIntegrationByParts.wF M θ)
    (hA : 0 < aJAfullG (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R)
    (hκ1 : 1 ≤ κ) (hT : 2 ≤ Cvs.L2a.FullTailDeepSpan.TL c κ) :
    0 < kappaFfullG (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullSpanWiring.bBarFull c κ (Fintype.card ι)
              (kappaFfullG (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R)
            * (∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull c κ (Fintype.card ι)
            (kappaFfullG (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat sb) R)
          * (∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) := by
  have hc4 : (10 : ℝ) ^ 4 ≤ c := le_trans (by norm_num) hc
  have hχc : ∀ i, χ i < c ^ 2 := fun i => by linarith [hσ i]
  obtain ⟨hκ, hFF⟩ := JA_integer_floor_G a hg hg₁ hg₂c hang hc hχ0 hσ₀ hσ hχi heven hg0 hμ hidx hJ hmass S
    hsb hdeep hR hρ hBC hA
  have hM : ∀ M : ℕ, 3 ≤ M → ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2 := fun M hM3 i =>
    (hmass i).trans_le (Cvs.L2a.FullTailDeepSpan.mass_mono (hg i) (by exact_mod_cast hM3))
  have hFF' : ∀ n : ℕ, 3 ≤ n → _ := fun n hn => hFF n hn (hM n hn)
  refine ⟨hκ, fun M hM3 => ?_, ?_⟩
  · exact Cvs.L2a.FullSpanWiring.L2a_at_M_full a hg hg₁ hg₂c hang hc4 hχ0 hχc hχi hJ hκ1 hT hκ hM3 (hM M hM3)
      (hFF' M hM3)
  · exact Cvs.L2a.FullSpanWiring.L2a_fulltail_of_floor_full a hg hg₁ hg₂c hang hc4 hχ0 hχc hχi hJ hκ1 hT hκ
      hmass hFF'

end wiring

/-! ### The arm at band edge `s` -/

section arm

local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))

open Cvs.L2a.BandSumThreshold (fBarG kapBarG)

/-- `f̄(c, s) ≥ 0` when its denominator is positive and `c ≥ 80`. -/
theorem fBarG_nonneg {c s : ℝ} (hc : 80 ≤ c) (hd : 0 < Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 s) :
    0 ≤ fBarG c s := by
  have h1 := Cvs.L2a.BandCouplingDischarged.deltaC_three_halves_nonneg hc
  have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  unfold fBarG
  positivity

/-- **The arm on a rung at edge `s`**: for `0 ≤ χ < c²`, `c² − χ ≤ s·c`, `c ≥ 80` and `log(1 + c) > 2k(2, s)`,
`∫_{3/2}^∞ ψ² ≤ f̄(c, s)·∫_1^∞ ψ²` (`BandMassLaw`'s far fraction at `r₀ = 2`, `ξ = 3/2`). -/
theorem far_le_fBarG {g g₁ g₂ : ℝ → ℝ} {c χ s : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hband : c ^ 2 - χ ≤ s * c)
    (hD : 0 < Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 s) :
    ∫ t in Ioi (3 / 2), psi c g t ^ 2 ≤ fBarG c s * ∫ t in Ioi 1, psi c g t ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hξ : 1 + 2 / c ≤ 3 / 2 := by
    have : 2 / c ≤ 1 / 2 := by rw [div_le_iff₀ hc0]; linarith
    linarith
  have h := Cvs.Prolate.BandMassLaw.rung_band_far_fraction (ξ := 3 / 2) (r₀ := 2) hg hg₁ hg₂c hang hc0 hχ hχc
    (by norm_num) (Cvs.Prolate.BandMassLaw.wBar_lt_two hc0 (by norm_num)) hξ
  have hl : Cvs.Prolate.BandMassLaw.ellF (3 / 2) = Real.log 5 := by
    unfold Cvs.Prolate.BandMassLaw.ellF; norm_num
  have hlog : Real.log (1 + 2 * c / 2) = Real.log (1 + c) := by congr 1; ring
  rw [hl, hlog] at h
  have hs : (c ^ 2 - χ) / c ≤ s := by rw [div_le_iff₀ hc0]; linarith
  have hmono := Cvs.Prolate.BandMassLaw.twoK_mono (c := c) (r₀ := 2) hc0 (by norm_num) hs
  have hF : 0 ≤ ∫ t in Ioi (3 / 2), psi c g t ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have h2 : (∫ t in Ioi (3 / 2), psi c g t ^ 2) * (Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 s)
      ≤ (∫ t in Ioi (3 / 2), psi c g t ^ 2)
        * (Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 ((c ^ 2 - χ) / c)) :=
    mul_le_mul_of_nonneg_left (by linarith) hF
  unfold fBarG
  rw [div_mul_eq_mul_div, le_div_iff₀ hD]
  linarith

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- **E plus arm at edge `s`**: on rungs with `0 ≤ χⱼ < c²`, `c² − χⱼ ≤ s·c`, `c ≥ 80`, `log(1 + c) > 2k(2, s)`, the
E-coupling `ē` gives the combined coupling with `w_F` and `κ̄ = (√f̄(c, s) + 2√ē)²`. -/
theorem rungCoupling_of_eCouplingG (a : ι → ℝ) (S : Finset ι)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) {sb : ℝ} (hD : 0 < Real.log (1 + c) - Cvs.Prolate.BandMassLaw.twoK c 2 sb)
    (hχ0 : ∀ i ∈ S, 0 ≤ χ i) (hχc : ∀ i ∈ S, χ i < c ^ 2)
    (hband : ∀ i ∈ S, c ^ 2 - χ i ≤ sb * c) {e : ℝ} (he : 0 ≤ e)
    (hE : Cvs.L2a.BandCouplingDischarged.ECoupling c g a S e) :
    Cvs.L2a.BandCouplingDischarged.RungCoupling c g a S Cvs.L2a.FarIntegrationByParts.wF (kapBarG c sb e) := by
  intro M hM j hj
  have hc0 : 0 < c := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦdef
  have hψ : ∀ i, MemLp (psi c (g i)) 2 μ₁ := fun i =>
    Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc0
  have hΦ : MemLp Φ 2 μ₁ := memLp_finsetSum Finset.univ fun i _ => (hψ i).const_mul (a i)
  have hX : (1 : ℝ) ≤ (M : ℝ) := by
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hE0 := Cvs.L2a.FrameFloorBandCoupling.memLp_frame (w := fun _ => (0 : ℝ)) hX hΦ measurable_const
    (fun _ => le_rfl) (fun _ => zero_le_one)
  have hEL : MemLp (dilSum Φ M) 2 μ₁ := by
    refine MemLp.ae_eq (ae_of_all _ fun x => ?_) (hE0.const_mul (1 / 2 : ℝ))
    simp only [zero_mul, sub_zero]
    ring
  have hwm : Measurable Cvs.L2a.FarIntegrationByParts.wF := Cvs.L2a.FarIntegrationByParts.continuous_wF.1.measurable
  have hw0 : ∀ x, 0 ≤ Cvs.L2a.FarIntegrationByParts.wF x := fun x => (Cvs.L2a.FarFarBound.wF_bounds x).1
  have hw1 : ∀ x, Cvs.L2a.FarIntegrationByParts.wF x ≤ 1 := fun x => (Cvs.L2a.FarFarBound.wF_bounds x).2.1
  have hwΦ : MemLp (fun x => Cvs.L2a.FarIntegrationByParts.wF x * Φ x) 2 μ₁ :=
    hΦ.of_le (hwm.aestronglyMeasurable.mul hΦ.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hw1 x))
  have hI1 : Integrable (fun x => psi c (g j) x * dilSum Φ M x) μ₁ := (hψ j).integrable_mul hEL
  have hI2 : Integrable (fun x => psi c (g j) x * (Cvs.L2a.FarIntegrationByParts.wF x * Φ x)) μ₁ :=
    (hψ j).integrable_mul hwΦ
  have hsplit : ∫ x in Ioi 1, psi c (g j) x * (2 * dilSum Φ M x - Cvs.L2a.FarIntegrationByParts.wF x * Φ x)
      = 2 * Cvs.L2a.BandRungOutgoingWave.eCoup c (g j) a g M
        - ∫ x in Ioi 1, psi c (g j) x * (Cvs.L2a.FarIntegrationByParts.wF x * Φ x) := by
    have e1 : (fun x => psi c (g j) x * (2 * dilSum Φ M x - Cvs.L2a.FarIntegrationByParts.wF x * Φ x))
        = fun x => 2 * (psi c (g j) x * dilSum Φ M x)
          - psi c (g j) x * (Cvs.L2a.FarIntegrationByParts.wF x * Φ x) := funext fun x => by ring
    rw [e1, integral_sub (hI1.const_mul 2) hI2, integral_const_mul]
    rfl
  have harm := Cvs.L2a.BandCouplingDischarged.sq_integral_mul_weight_le (hψ j) hΦ hwm hw0 hw1
    (fun x hx => Cvs.L2a.FarFarBound.wF_eq_zero_of_le hx)
  have hfar := far_le_fBarG (hg j) (hg₁ j) (hg₂c j) (hang j) hc (hχ0 j hj) (hχc j hj) (hband j hj) hD
  have hP : 0 ≤ ∫ x in Ioi 1, Φ x ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hMj : 0 ≤ ∫ ξ in Ioi 1, psi c (g j) ξ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hy : (∫ x in Ioi 1, psi c (g j) x * (Cvs.L2a.FarIntegrationByParts.wF x * Φ x)) ^ 2
      ≤ fBarG c sb * (∫ ξ in Ioi 1, psi c (g j) ξ ^ 2) * ∫ x in Ioi 1, Φ x ^ 2 :=
    harm.trans (mul_le_mul_of_nonneg_right hfar hP)
  have hx := hE M hM j hj
  show (∫ x in Ioi 1, psi c (g j) x * (2 * dilSum Φ M x - Cvs.L2a.FarIntegrationByParts.wF x * Φ x)) ^ 2 ≤ _
  rw [hsplit]
  exact Cvs.L2a.BandCouplingDischarged.sq_two_mul_sub_le he (fBarG_nonneg hc hD) hMj hP hx hy

end arm

/-! ### The margin at `c ≥ c₀^F` -/

/-- **The floor `1/38`**: for `c ≥ c₀^F`, `0 ≤ J ≤ c/4 + 1`, `ρ = 7c^{−1/8}`, `r_S(c, σ₀) ≤ rSig(σ̲(c))` and
`θ + 7c^{−1/8} + rSig(σ̲(c)) ≤ 0.2074 − 0.027`: `A(ε_τ(10), RbarJ) > 0` and `κ ≥ 1/38`. -/
theorem floor_ge_of_margin {c J σ₀ θ : ℝ} (hc : Cvs.L2a.FullSpanThreshold.c0F ≤ c) (hJ0 : 0 ≤ J)
    (hJ : J ≤ c / 4 + 1)
    (hrS : Cvs.L2a.MiddlePartQStep.rStrip c σ₀
      ≤ Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c))
    (hm : θ + 7 * c ^ (-(1 / 8 : ℝ)) + Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      ≤ 2074 / 10000 - 27 / 1000) :
    0 < aJAfullG (10 ^ 16) c J (7 * c ^ (-(1 / 8 : ℝ))) σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat 10)
        Cvs.L2a.JointMainTerm.RbarJ
      ∧ 1 / 38 ≤ kappaFfullG (10 ^ 16) c J (7 * c ^ (-(1 / 8 : ℝ))) σ₀ θ
        (Cvs.L2a.SpanPlungeBound.epsTauFlat 10) Cvs.L2a.JointMainTerm.RbarJ := by
  have hc80 := Cvs.L2a.FullSpanProlateFamily.c80_le_exp.trans (Cvs.L2a.FullSpanThreshold.c0F_bounds.1.trans hc)
  have hc16 : (10 : ℝ) ^ 16 ≤ c := le_trans (by norm_num) hc80
  have hA := aJAfullG_ge (ρ := 7 * c ^ (-(1 / 8 : ℝ))) (σ₀ := σ₀) (θ := θ)
    (ε := Cvs.L2a.SpanPlungeBound.epsTauFlat 10) (R := Cvs.L2a.JointMainTerm.RbarJ) hc16 hJ0 hJ
  have hε := epsTauFlat_ten_le
  have hε0 := Cvs.L2a.SpanPlungeBound.epsTauFlat_nonneg 10
  have hs : √(1 / 38 : ℝ) ≤ 1 / 6 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 := Real.sqrt_nonneg (1 / 38 : ℝ)
  have hRJ : Cvs.L2a.JointMainTerm.RbarJ = 2925 / 10000 := rfl
  have hA' : 1 / 38 + 2 * Cvs.L2a.SpanPlungeBound.epsTauFlat 10 * √(1 / 38)
      ≤ aJAfullG (10 ^ 16) c J (7 * c ^ (-(1 / 8 : ℝ))) σ₀ θ (Cvs.L2a.SpanPlungeBound.epsTauFlat 10)
        Cvs.L2a.JointMainTerm.RbarJ := by
    have : 2 * Cvs.L2a.SpanPlungeBound.epsTauFlat 10 * √(1 / 38) ≤ 2 * (1 / 100000) * (1 / 6) := by
      have := mul_le_mul hε hs hs0 (by norm_num)
      nlinarith
    linarith
  refine ⟨lt_of_lt_of_le (by positivity) hA', ?_⟩
  exact Cvs.L2a.FullSpanThreshold.floor_of_margin (by norm_num) hA'

/-! ### The instance on `Finset.range x` -/

open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ lev muR rung_spec rung_ne_zero psi_rung)

/-- **L2a-FULL on `Finset.range x` of the prolate family at `c = 2πx ≥ c₀^F`**: with THEOREM E's band inputs
`BandInputs x a K_r` (`0 ≤ K_r ≤ 10⁴⁵`), `κ_F ≥ 1/38`, `b̄ ≥ 1` at `κ = κ⋆_F`, `b̄·N(M) ≤ W(M)` for all `M ≥ 3`
and `b̄·N_∞ ≤ W_∞`; `κ_F` is the edge-10 floor at `ρ = 7c^{−1/8}`, `σ̲`, `θ̄(κ̄(c, 10, ē), D̄)`, `ε_τ(10)`, RbarJ. -/
theorem L2a_full_span_instance (x : ℕ) (hx : Cvs.L2a.FullSpanThreshold.c0F ≤ 2 * π * x)
    (a : Finset.range x → ℝ) {Kr : ℝ} (hKr0 : 0 ≤ Kr) (hKr : Kr ≤ 10 ^ 45)
    (hin : Cvs.L2a.BandECouplingCollar.BandInputs x a Kr) :
    let c := 2 * π * x
    let Φ := fun ξ => ∑ j, a j * psi c (rung c (2 * (j : ℕ))) ξ
    let κF := kappaFfullG (10 ^ 16) c x (7 * c ^ (-(1 / 8 : ℝ))) (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      (Cvs.L2a.BandCouplingDischarged.thetaBar
        (Cvs.L2a.BandSumThreshold.kapBarG c 10
          (Cvs.L2a.BandECouplingCollar.eMain c 10 * (1 + Cvs.L2a.BandECouplingCollar.omegaE Kr c) ^ 2))
        (Cvs.Prolate.PlungeMassTrace.plungeBound c))
      (Cvs.L2a.SpanPlungeBound.epsTauFlat 10) Cvs.L2a.JointMainTerm.RbarJ
    1 / 38 ≤ κF
      ∧ 1 ≤ Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
      ∧ (∀ M : ℕ, 3 ≤ M →
          Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
              * ∫ y in Ioi 1, posTail Φ M y ^ 2
            ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
                (Cvs.L2a.TailLogScaleTest.logScale (posTail Φ M)))
      ∧ Cvs.L2a.FullSpanWiring.bBarFull c Cvs.L2a.FullSpanThreshold.kapStarF x κF
          * ∫ y in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail Φ y ^ 2
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf Φ := by
  classical
  intro c Φ κF
  set ω := Cvs.L2a.BandECouplingCollar.omegaE Kr c with hωdef
  set e := Cvs.L2a.BandECouplingCollar.eMain c 10 * (1 + ω) ^ 2 with hedef
  set θ := Cvs.L2a.BandCouplingDischarged.thetaBar (Cvs.L2a.BandSumThreshold.kapBarG c 10 e)
    (Cvs.Prolate.PlungeMassTrace.plungeBound c) with hθdef
  set S := Cvs.L2a.BandECouplingCollar.bandSetG c 10 (fun j : Finset.range x => lev c (2 * (j : ℕ))) with hSdef
  -- the scale
  have hc80' := Cvs.L2a.FullSpanProlateFamily.c80_le_exp.trans (Cvs.L2a.FullSpanThreshold.c0F_bounds.1.trans hx)
  have hc16 : (10 : ℝ) ^ 16 ≤ c := le_trans (by norm_num) hc80'
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hc1 : (1 : ℝ) ≤ c := le_trans (by norm_num) hc16
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc16
  have hL := Cvs.Prolate.LandauLowerPivot.landau_lower_pivot x hc80
  have hspec := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)
  have hspec' := fun j => rung_spec (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j)
  have hJx : ((x : ℕ) : ℝ) ≤ c / 4 + 1 := Cvs.L2a.FullSpanProlateFamily.x_le x
  have hJ : (Fintype.card (Finset.range x) : ℝ) ≤ c / 4 + 1 := by
    rw [Cvs.L2a.FullSpanProlateFamily.card_range]; exact hJx
  have hρ : ∀ M : ℕ, 3 ≤ M →
      resLoc c (Fintype.card (Finset.range x)) M ≤ 7 * c ^ (-(1 / 8 : ℝ)) := by
    rw [Cvs.L2a.FullSpanProlateFamily.card_range]; exact Cvs.L2a.FullSpanProlateFamily.resLoc_le_rhoX hc16
  have hσ0 := Cvs.L2a.FullSpanIndexFloor.sigmaLow_pos (c := c) (by linarith)
  have hσ := Cvs.Prolate.RungFamilyRangePartners.sigmaLow_le_main hc80
  have hχ0 := Cvs.Prolate.RungFamilyRangePartners.lev_main_nonneg hc80
  have hχc : ∀ j : Finset.range x, lev c (2 * (j : ℕ)) < c ^ 2 := fun j => by linarith [hσ j]
  have hχi := Cvs.Prolate.RungFamilyRangePartners.lev_main_injective hc80
  -- the E-coupling and the rung coupling on the band at edge `10`
  have hω0 : 0 ≤ ω := Cvs.L2a.BandECouplingCollar.omegaE_nonneg hKr0 hc0.le
  have hω1 : ω ≤ 1 / 1000 := Cvs.L2a.BandECouplingCollar.omegaE_le hKr hx
  have he : 0 ≤ e := mul_nonneg (Cvs.L2a.BandECouplingCollar.eMain_nonneg hc80) (sq_nonneg _)
  have hE : Cvs.L2a.BandCouplingDischarged.ECoupling c (fun j : Finset.range x => rung c (2 * (j : ℕ))) a S e :=
    Cvs.L2a.BandECouplingCollar.eCoupling_band x hc80 a hKr0 hin
  have hband : ∀ j ∈ S, c ^ 2 - lev c (2 * (j : ℕ)) ≤ 10 * c := fun j hj => by
    rw [hSdef] at hj
    unfold Cvs.L2a.BandECouplingCollar.bandSetG at hj
    exact (Finset.mem_filter.1 hj).2.le
  have hdeep : ∀ j ∉ S, 10 * c ≤ c ^ 2 - lev c (2 * (j : ℕ)) := fun j hj => by
    by_contra hlt
    exact hj (by rw [hSdef]; unfold Cvs.L2a.BandECouplingCollar.bandSetG; simpa using lt_of_not_ge hlt)
  have hRC := rungCoupling_of_eCouplingG (ι := Finset.range x) a S
    (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := fun j => lev c (2 * (j : ℕ)))
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    hc80 (Cvs.L2a.BandECouplingCollar.eMain_den_pos hc80) (fun j _ => hχ0 j) (fun j _ => hχc j) hband he hE
  -- the paired deficit on the band
  have hD := Cvs.L2a.BandCouplingDischarged.sum_one_sub_le_plunge_paired (ι := Finset.range x) S hc1
    (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (h := fun j : Finset.range x => rung c (2 * (j : ℕ) + 1))
    (h₁ := fun j => rung₁ c (2 * (j : ℕ) + 1)) (h₂ := fun j => rung₂ c (2 * (j : ℕ) + 1))
    (χ := fun j => lev c (2 * (j : ℕ))) (χ' := fun j => lev c (2 * (j : ℕ) + 1))
    (μ := fun j => muR c (2 * (j : ℕ))) (μ' := fun j => muR c (2 * (j : ℕ) + 1))
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    (fun j => (hspec' j).1) (fun j => (hspec' j).2.1) (fun j => (hspec' j).2.2.1)
    (fun j => (hspec' j).2.2.2.1)
    hχi.injOn ((Cvs.Prolate.RungFamilyRangePartners.lev_partner_injective hL).injOn)
    (fun i _ j _ => Cvs.Prolate.RungFamilyRangePartners.lev_main_ne_partner hc80 hL i j)
    (fun j _ => (hspec j).2.2.2.2.1) (fun j _ => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j _ => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j _ => (hspec' j).2.2.2.2.1) (fun j _ => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j))
    (fun j _ => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_partner hL j))
    (fun j _ => Cvs.Prolate.RungFamilyRangePartners.lev_le_partner hL j)
    (fun j _ => Cvs.Prolate.RungFamilyRangePartners.half_le_lam_partner hc80 hL j)
  -- (BC) on the band
  have hBC : ∀ M : ℕ, 3 ≤ M → BandCoupling c (fun j : Finset.range x => rung c (2 * (j : ℕ)))
      (fun j => muR c (2 * (j : ℕ))) a S Cvs.L2a.FarIntegrationByParts.wF M θ := fun M hM =>
    Cvs.L2a.BandCouplingDischarged.bandCoupling_routeT (ι := Finset.range x) a S
      (g := fun j : Finset.range x => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
      (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := fun j => lev c (2 * (j : ℕ)))
      (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
      hc0 hχi (fun j => (hspec j).2.2.2.2.1)
      (fun j => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
      (fun j _ => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
      (fun j _ => Cvs.L2a.BandCouplingDischarged.mass_Ioi_pos
        (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hspec j).1 (hspec j).2.1 (hspec j).2.2.1 (hspec j).2.2.2.1
          hc0).integrable_sq (Cvs.Prolate.RungFamilyRangePartners.mass_main hc80 j))
      (fun j _ => (mul_pos (Cvs.Prolate.SlepianEvenOrdering.mu_pos_of_even_index hc0 (hspec j).1 (hspec j).2.1
        (hspec j).2.2.1 (hspec j).2.2.2.1 (hspec j).2.2.2.2.1
        (rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
        (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)) (Cvs.Prolate.RungFamilyRangePartners.even_ncard_main hc80 j))
        (Real.sqrt_pos.2 (by positivity))).le)
      (fun j _ => Cvs.Prolate.LandauHalfEvenSpectrum.half_le_lam_of_lower hc0 hL (hspec j).1 (hspec j).2.1 (hspec j).2.2.1
        (hspec j).2.2.2.1 (hspec j).2.2.2.2.1 (rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
        (psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j)) (Cvs.Prolate.RungFamilyRangePartners.ncard_main_le hc80 j))
      Cvs.L2a.FarIntegrationByParts.wF M (by unfold Cvs.L2a.BandSumThreshold.kapBarG; positivity) (hRC M hM) hD
  -- the margin
  have hrS : Cvs.L2a.MiddlePartQStep.rStrip c (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c)
      ≤ Cvs.L2a.FullSpanConditional.rSig (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c) :=
    Cvs.L2a.FullSpanConditional.rStrip_le_rSig hc0 hσ0 (Cvs.L2a.FullSpanIndexFloor.sigmaLow_le_five hc80)
  have hm := Cvs.L2a.BandSumThreshold.hm_full hx hω0 hω1
  obtain ⟨hA, h38⟩ := floor_ge_of_margin (J := (x : ℝ)) (σ₀ := Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c) (θ := θ) hx
    (Nat.cast_nonneg _) hJx hrS hm
  obtain ⟨hT, hb1⟩ := Cvs.L2a.FullSpanThreshold.bBarFull_ge_one hx (Nat.cast_nonneg _) hJx h38
  have hκ1 : (1 : ℝ) ≤ Cvs.L2a.FullSpanThreshold.kapStarF := le_trans (by norm_num) (le_max_left _ _)
  have hA' : 0 < aJAfullG (10 ^ 16) c (Fintype.card (Finset.range x)) (7 * c ^ (-(1 / 8 : ℝ)))
      (Cvs.Prolate.EvenLevelIndexLemma.sigmaLow c) θ (Cvs.L2a.SpanPlungeBound.epsTauFlat 10) Cvs.L2a.JointMainTerm.RbarJ := by
    rw [Cvs.L2a.FullSpanProlateFamily.card_range]; exact hA
  have H := L2a_fulltail_G (ι := Finset.range x) a (g := fun j : Finset.range x => rung c (2 * (j : ℕ)))
    (g₁ := fun j => rung₁ c (2 * (j : ℕ))) (g₂ := fun j => rung₂ c (2 * (j : ℕ)))
    (χ := fun j => lev c (2 * (j : ℕ))) (μ := fun j => muR c (2 * (j : ℕ)))
    (κ := Cvs.L2a.FullSpanThreshold.kapStarF)
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1)
    hc16 hχ0 hσ0 hσ hχi (fun j => (hspec j).2.2.2.2.1)
    (fun j => rung_ne_zero (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (fun j => psi_rung (Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 j))
    (Cvs.Prolate.RungFamilyRangePartners.even_ncard_main hc80) hJ (Cvs.Prolate.RungFamilyRangePartners.mass_main hc80) S
    (by norm_num : (5 : ℝ) ≤ 10) hdeep (fun κ hκ M hM => Cvs.L2a.JointMainTerm.main_le_RbarJ hκ hM) hρ hBC hA'
    hκ1 hT
  rw [Cvs.L2a.FullSpanProlateFamily.card_range] at H
  obtain ⟨-, h2, h3⟩ := H
  exact ⟨h38, hb1, h2, h3⟩

end Cvs.L2a.FullSpanInstance
