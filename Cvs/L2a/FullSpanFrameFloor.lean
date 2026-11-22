import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CleanBandDilation
import Cvs.L2a.CornerKernelUniform
import Cvs.L2a.CornerSplitSqrtFloor
import Cvs.L2a.CutKernelRemainder
import Cvs.L2a.CutKernels
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarFarConstantClosedForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorBandCoupling
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.LocalisedBottomCorners
import Cvs.L2a.LocalisedConstants
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SecondModeShells
import Cvs.L2a.SpanPlungeBound
import Cvs.L2a.TopCornerSum
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Upstream.CosineTransformHalfLine
import Cvs.Upstream.QuinticSmoothStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# JA on the full span: the strip at any `σ₀ > 0` and the band through band coupling

`FrameFloorIntegerM`'s JA with `σᵢ² ≥ 5c` split in two: every rung has `σ₀ ≤ c² − χᵢ` for one `σ₀ > 0` (the strip costs
`r_S(c, σ₀)`), and `1 − ε_τ(5) ≤ τᵢ` is asked only off a set `S` of rungs with `5c ≤ c² − χᵢ` outside it, the rungs of
`S` entering through (BC) at `θ`. `A_full = A − (r_S(c, σ₀) − r_S(c, 5c)) − θ` and `κ_full = (√(A_full + ε²) − ε)²`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.Upstream.CosineTransformHalfLine Cvs.L2a.MirrorFloor Cvs.L2a.ReflectionFloor Cvs.Upstream.CosineTransformDilation Cvs.L2a.MirrorSplitDefect Cvs.L2a.CoreArmIdentity Cvs.L2a.FrameFloorJumpAbsorption Cvs.L2a.CleanBandDilation Cvs.L2a.DilationCornerSplit Cvs.L2a.CornerSplitSqrtFloor

namespace Cvs.L2a.FullSpanFrameFloor

open Cvs.L2a.FrameFloorIntegerM (resLoc aJA kappaF cEtaClosed_nonneg gammaD_le gammaE1_le)
open Cvs.L2a.FrameFloorBandCoupling (BandCoupling)

/-! ### The strip constant as a function of `σ₀` -/

section strip

open Cvs.L2a.MiddlePartQStep

/-- **`r_S(c, ·)` is antitone**: `0 < σ ≤ σ'` gives `r_S(c, σ') ≤ r_S(c, σ)`. -/
theorem rStrip_anti {c σ σ' : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσσ : σ ≤ σ') : rStrip c σ' ≤ rStrip c σ := by
  have hσ' : 0 < σ' := lt_of_lt_of_le hσ hσσ
  have hinv : 1 / σ' ≤ 1 / σ := one_div_le_one_div_of_le hσ hσσ
  have hp : ∀ e : ℝ, 0 ≤ e → (1 / σ') ^ e ≤ (1 / σ) ^ e := fun e he =>
    Real.rpow_le_rpow (by positivity) hinv he
  have h1 := hp (1 / 4) (by norm_num)
  have h3 := hp (3 / 4) (by norm_num)
  have h7 := hp (7 / 4) (by norm_num)
  unfold rStrip LamStrip
  have hB : ∀ e : ℝ, 0 ≤ (3 / 2 * c ^ 2) ^ e := fun e => Real.rpow_nonneg (by positivity) e
  have hG : ∀ x : ℝ, 0 < x → 0 ≤ Real.Gamma x := fun x hx => (Real.Gamma_pos_of_pos hx).le
  have hk : 0 ≤ √(2 * c / π) * (16 * π ^ 2 / 9) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hk
  have g14 := hG (1 / 4) (by norm_num)
  have g34 := hG (3 / 4) (by norm_num)
  have g74 := hG (7 / 4) (by norm_num)
  have b74 := hB (-(7 / 4))
  have b54 := hB (-(5 / 4))
  have b94 := hB (-(9 / 4))
  gcongr

/-- `(1/s)^e = (5/s)^e·(1/5)^e` for `s > 0`. -/
theorem one_div_rpow_eq {s : ℝ} (hs : 0 < s) (e : ℝ) : (1 / s) ^ e = (5 / s) ^ e * (1 / 5) ^ e := by
  rw [← Real.mul_rpow (by positivity) (by norm_num)]
  congr 1
  field_simp

/-- **The strip coefficients at `s ≤ 5`**: `K₁(s) = (5/s)^{1/4}K₁(5)`, `K₂(s) ≤ (5/s)^{7/4}K₂(5)`,
`K₃(s) ≤ (5/s)^{7/4}K₃(5)`. -/
theorem KS_le_scaled {s : ℝ} (hs : 0 < s) (hs5 : s ≤ 5) :
    KS₁ s = (5 / s) ^ (1 / 4 : ℝ) * KS₁ 5 ∧ KS₂ s ≤ (5 / s) ^ (7 / 4 : ℝ) * KS₂ 5
      ∧ KS₃ s ≤ (5 / s) ^ (7 / 4 : ℝ) * KS₃ 5 := by
  have hl : 1 ≤ 5 / s := by rw [le_div_iff₀ hs]; linarith
  have hm : (5 / s) ^ (3 / 4 : ℝ) ≤ (5 / s) ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hl (by norm_num)
  have h5 : ∀ e : ℝ, (1 / (5 : ℝ)) ^ e = (5 / (5 : ℝ)) ^ e * (1 / 5) ^ e := fun e => by norm_num
  have hG : ∀ x : ℝ, 0 < x → 0 ≤ Real.Gamma x := fun x hx => (Real.Gamma_pos_of_pos hx).le
  have g34 := hG (3 / 4) (by norm_num)
  have g74 := hG (7 / 4) (by norm_num)
  have hq : ∀ e : ℝ, 0 ≤ (1 / (5 : ℝ)) ^ e := fun e => Real.rpow_nonneg (by norm_num) e
  have q34 := hq (3 / 4)
  have q74 := hq (7 / 4)
  have hb : ∀ e : ℝ, 0 ≤ (3 / 2 : ℝ) ^ e := fun e => Real.rpow_nonneg (by norm_num) e
  have b54 := hb (-(5 / 4))
  have b94 := hb (-(9 / 4))
  have k0 : 0 ≤ √(2 / π) * (16 * π ^ 2 / 9) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold KS₁; rw [one_div_rpow_eq hs]; ring
  · unfold KS₂
    rw [one_div_rpow_eq hs]
    have hA : 0 ≤ 10 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ)) * ((1 / 5) ^ (3 / 4 : ℝ)
        * Real.Gamma (3 / 4)) + 8 * √(Real.Gamma (9 / 2)) * (3 / 2 : ℝ) ^ (-(9 / 4 : ℝ))
        * ((1 / 5) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)) := by positivity
    have := mul_le_mul_of_nonneg_right hm (mul_nonneg k0 hA)
    nlinarith
  · unfold KS₃
    rw [one_div_rpow_eq hs, one_div_rpow_eq hs]
    have hA : 0 ≤ √(2 / π) * (16 * π ^ 2 / 9) * (2 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
        * ((1 / 5) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4))) := by positivity
    have := mul_le_mul_of_nonneg_right hm hA
    nlinarith

end strip

/-! ### The three parts at an integer `M` with the strip at `σ₀` -/

section corners

open Cvs.L2a.FarIntegrationByParts Cvs.L2a.CutKernels

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- **The three parts at `S*`, strip at `σ₀`**: `FrameFloorIntegerM`'s `corners_ge_loc` with `σᵢ² ≥ 5c` replaced by
`0 < σ₀ ≤ c² − χᵢ`; the strip enters as `r_S(c, σ₀)`. -/
theorem corners_ge_loc_full (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 4096 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i)
    (hχi : Function.Injective χ)
    {M : ℕ} (hM3 : 3 ≤ M) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2)
    (hshell : Cvs.L2a.LocalisedBottomCorners.ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) χ g a) :
    -(Cvs.L2a.LocalisedConstants.r1main (Cvs.L2a.LocalisedBottomCorners.kapI c (Fintype.card ι)) M
        + Cvs.L2a.LocalisedConstants.botMain (Cvs.L2a.LocalisedBottomCorners.kapI c (Fintype.card ι)) M
        + resLoc c (Fintype.card ι) M
        + (Cvs.L2a.CutKernelRemainder.γD c (Fintype.card ι) + Cvs.L2a.CutKernelRemainder.γE1 c (Fintype.card ι))
        + Cvs.L2a.MiddlePartQStep.rOne c + Cvs.L2a.MiddlePartQStep.rStrip c σ₀)
        * ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2
      ≤ DbotG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2)
        + DmidG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2)
        + DtopG Cvs.Upstream.QuinticSmoothStep.S c (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M (1 / 2) := by
  have hc0 : 0 < c := by linarith
  have hc80 : 80 ≤ c := by linarith
  have hχc : ∀ i, χ i < c ^ 2 := fun i => by linarith [hσ i]
  have hδ := Cvs.L2a.TopCornerSum.deltaS_pos hc0
  have hδ8 := Cvs.L2a.TopCornerSum.deltaS_le hc
  have hs := Cvs.L2a.TopCornerSum.sS_pos hc0
  have hs1 := Cvs.L2a.TopCornerSum.sS_le hc
  have hB := Cvs.L2a.LocalisedBottomCorners.Dbot_local a (Xb := 550) hg hg₁ hg₂c hang hc80 hχ0 hχc hχi hmass hM3
    (by norm_num) hδ (by linarith) hδ (by linarith) hs hs1 hshell
  have hT := Cvs.L2a.TopCornerSum.Dtop_flat_rho a (J := (Fintype.card ι : ℝ)) 68 hg hg₁ hg₂c hang hc80 hχ0 hχc hχi hM3 hmass
    le_rfl hδ (by linarith) hδ (by linarith) hs hs1 (Cvs.L2a.TopCornerSum.uS_zero hc) (Cvs.L2a.TopCornerSum.uS_K hc) (Cvs.L2a.TopCornerSum.uS_mono hc0)
  have hC := Cvs.L2a.CornerKernelUniform.calCa_le a hg hg₁ hg₂c hang hc80 hχ0 hχc hχi hM3 hmass
    (J := (Fintype.card ι : ℝ)) le_rfl
  have hmid := Cvs.L2a.MiddlePartQStep.corners_add_mid_ge_closed a hg hg₁ hg₂c hang hc0 hχi hχ0
    hσ₀ hσ hM3 (δ := 1 / 2) (by norm_num) (by norm_num)
  have hloc := Cvs.L2a.FrameFloorIntegerM.loc_le c (Fintype.card ι) M
  have hP0 : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  set P := ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 with hP
  set J : ℝ := (Fintype.card ι : ℝ) with hJ
  have hbsum : |∑ m ∈ Finset.Icc 2 (M - 1), ∫ t in Ioi 1,
        ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t|
      ≤ ∑ m ∈ Finset.Icc 2 (M - 1), |∫ t in Ioi 1,
        ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t| :=
    Finset.abs_sum_le_sum_abs _ _
  have hbneg := le_abs_self (∑ m ∈ Finset.Icc 2 (M - 1), ∫ t in Ioi 1,
    ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t)
  have htsum : |∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m| ≤ ∑ m ∈ Finset.Icc 2 (M - 1), |cTop c χ g a M m| :=
    Finset.abs_sum_le_sum_abs _ _
  have htneg := neg_abs_le (∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m)
  have hCa := neg_abs_le (calCa c χ g a M)
  have hrho : Cvs.L2a.FrameFloorIntegerM.rhoTL c J
      = Cvs.L2a.TopCornerSum.rhoT c J (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) (Cvs.L2a.TopCornerSum.uS c) (Cvs.L2a.TopCornerSum.KS c) 68 := rfl
  have hlocP := mul_le_mul_of_nonneg_right hloc hP0
  rw [hrho] at hlocP
  have e1 : -(Cvs.L2a.LocalisedBottomCorners.calB c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) 550 M J * P)
      ≤ -2 * ∑ m ∈ Finset.Icc 2 (M - 1), ∫ t in Ioi 1,
        ubar (fun ξ => ∑ i, a i * psi c (g i) ξ) wF M t * frakB c χ g a m t := by linarith
  have e2 : -((Cvs.L2a.TopCornerSum.r1T c J 68 M
      + Cvs.L2a.TopCornerSum.rhoT c J (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) (Cvs.L2a.TopCornerSum.uS c) (Cvs.L2a.TopCornerSum.KS c) 68) * P)
      ≤ ∑ m ∈ Finset.Icc 2 (M - 1), cTop c χ g a M m := by linarith
  have e3 : -((Cvs.L2a.CutKernelRemainder.γD c J + Cvs.L2a.CutKernelRemainder.γE1 c J) * P) ≤ calCa c χ g a M := by linarith
  linarith

/-- **The `m = 2` shells from the strip**: `c ≥ 4096`, `0 < σ₀ ≤ c² − χᵢ` and `∫₁³ ψᵢ² > 0` give
`ShellM2 c δ* δ* s* χ g a`. -/
theorem shellM2_strip (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 4096 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ : ∀ i, σ₀ ≤ c ^ 2 - χ i)
    (hχi : Function.Injective χ) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2) :
    Cvs.L2a.LocalisedBottomCorners.ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.sS c) χ g a :=
  Cvs.L2a.SecondModeShells.shellM2_S a hg hg₁ hg₂c hang hc hχ0 (fun i => by linarith [hσ i]) hχi hmass

end corners

/-! ### The full margin and the full floor constant -/

section consts

/-- **The full JA margin** `A_full = ½ − 3ε_τ(5) − √(C_η(c₀)/c) − (R̄ + ρ + γ_D + γ_E₁ + r₁ + r_S(c, σ₀)) − θ`. -/
def aJAfull (c₀ c J ρ σ₀ θ : ℝ) : ℝ :=
  1 / 2 - 3 * Cvs.L2a.SpanPlungeBound.epsTauFlat 5 - √(Cvs.L2a.FarFarConstantClosedForm.cEtaClosed c₀ / c)
    - (Cvs.L2a.LocalisedConstants.Rbar + ρ + (Cvs.L2a.CutKernelRemainder.γD c J + Cvs.L2a.CutKernelRemainder.γE1 c J)
      + Cvs.L2a.MiddlePartQStep.rOne c + Cvs.L2a.MiddlePartQStep.rStrip c σ₀) - θ

/-- **The full floor constant** `κ_full = (√(A_full + ε²) − ε)²`, `ε = ε_τ(5)`. -/
def kappaFfull (c₀ c J ρ σ₀ θ : ℝ) : ℝ :=
  (√(aJAfull c₀ c J ρ σ₀ θ + Cvs.L2a.SpanPlungeBound.epsTauFlat 5 ^ 2) - Cvs.L2a.SpanPlungeBound.epsTauFlat 5) ^ 2

/-- **`A_full ≥ 153/1000 − ρ − r_S(c, σ₀) − θ`** for `c ≥ 10¹⁶`, `0 ≤ J ≤ c/4 + 1`. -/
theorem aJAfull_ge {c J ρ σ₀ θ : ℝ} (hc : 10 ^ 16 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    153 / 1000 - ρ - Cvs.L2a.MiddlePartQStep.rStrip c σ₀ - θ ≤ aJAfull (10 ^ 16) c J ρ σ₀ θ := by
  have hJc : J ≤ c := by linarith
  have h1 := Cvs.L2a.SpanPlungeBound.epsTauFlat_five_le
  have h2 := Cvs.L2a.LocalisedConstants.eta_le_c0 hc
  have h3 := Cvs.L2a.LocalisedConstants.rOne_le_c0 hc
  have h5 := Cvs.L2a.LocalisedConstants.Rbar_le
  have h6 := gammaD_le hc hJ0 hJc
  have h7 := gammaE1_le hc hJc
  unfold aJAfull
  norm_num at h2 h3 h6 h7 ⊢
  linarith

/-- `t ↦ (√(t + ε²) − ε)²` is monotone on `t ≥ 0`. -/
theorem floorFn_mono {ε t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    (√(t + ε ^ 2) - ε) ^ 2 ≤ (√(t' + ε ^ 2) - ε) ^ 2 := by
  have h0 : ε ≤ √(t + ε ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
  have h1 : √(t + ε ^ 2) ≤ √(t' + ε ^ 2) := Real.sqrt_le_sqrt (by linarith)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- **`κ_full ≥ (√(A₀ + ε²) − ε)²`** for any `0 ≤ A₀ ≤ A_full`. -/
theorem kappaFfull_ge {c₀ c J ρ σ₀ θ A₀ : ℝ} (hA₀ : 0 ≤ A₀) (hA : A₀ ≤ aJAfull c₀ c J ρ σ₀ θ) :
    (√(A₀ + Cvs.L2a.SpanPlungeBound.epsTauFlat 5 ^ 2) - Cvs.L2a.SpanPlungeBound.epsTauFlat 5) ^ 2
      ≤ kappaFfull c₀ c J ρ σ₀ θ :=
  floorFn_mono hA₀ hA

/-- `A_full > 0` gives `κ_full > 0`. -/
theorem kappaFfull_pos {c₀ c J ρ σ₀ θ : ℝ} (hA : 0 < aJAfull c₀ c J ρ σ₀ θ) : 0 < kappaFfull c₀ c J ρ σ₀ θ := by
  unfold kappaFfull
  have hε := Cvs.L2a.SpanPlungeBound.epsTauFlat_nonneg 5
  have hlt : Cvs.L2a.SpanPlungeBound.epsTauFlat 5
      < √(aJAfull c₀ c J ρ σ₀ θ + Cvs.L2a.SpanPlungeBound.epsTauFlat 5 ^ 2) := by
    rw [Real.lt_sqrt hε]; linarith
  exact pow_pos (by linarith) 2

end consts

/-! ### The band -/

section band

variable {ι : Type} [Fintype ι]

/-- **The band** `𝓑 = {i : c² − χᵢ < 5c}`. -/
def bandSet (c : ℝ) (χ : ι → ℝ) : Finset ι := by
  classical exact Finset.univ.filter fun i => c ^ 2 - χ i < 5 * c

/-- Off the band, `5c ≤ c² − χᵢ`. -/
theorem deep_of_notMem_bandSet {c : ℝ} {χ : ι → ℝ} {i : ι} (h : i ∉ bandSet c χ) : 5 * c ≤ c ^ 2 - χ i := by
  classical
  by_contra hlt
  exact h (by unfold bandSet; simpa using lt_of_not_ge hlt)

end band

/-! ### JA on the full span -/

section floor

open Cvs.L2a.FarIntegrationByParts

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ μ : ι → ℝ}

/-- **JA at one integer `M`, full span**: `0 < σ₀ ≤ c² − χᵢ` for all `i`, `5c ≤ c² − χᵢ` off `S`, (BC) on `S` at `θ`,
the `m = 2` shells, `resLoc(c, M) ≤ ρ` and `A_full ≥ 0` give `κ_full·Σ aᵢ²∫₁^M ψᵢ² ≤ N(M)`. -/
theorem JA_floor_full (a : ι → ℝ)
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
    (S : Finset ι) (hdeep : ∀ i ∉ S, 5 * c ≤ c ^ 2 - χ i)
    {M : ℕ} (hM3 : 3 ≤ M) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2)
    {ρ : ℝ} (hρ : resLoc c (Fintype.card ι) M ≤ ρ) {θ : ℝ} (hBC : BandCoupling c g μ a S wF M θ)
    (hA : 0 ≤ aJAfull c₀ c (Fintype.card ι) ρ σ₀ θ) :
    kappaFfull c₀ c (Fintype.card ι) ρ σ₀ θ * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
      ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hc80 : 80 ≤ c := by linarith
  have hχc : ∀ i, χ i ≤ c ^ 2 := fun i => by linarith [hσ i]
  have hsign := Cvs.Prolate.EdgeCentreSign.hsign_of_even_index hc0 hχ0 hg hg₁ hg₂c hang heven hg0 hμ hidx
  have hτ : ∀ i ∉ S, 1 - Cvs.L2a.SpanPlungeBound.epsTauFlat 5 ≤ μ i * √(c / (2 * π)) := fun i hi =>
    Cvs.L2a.SpanPlungeBound.tau_flat (hg i) (hg₁ i) (hg₂c i) (hang i) hc80 (hχ0 i) le_rfl (hdeep i hi) (heven i)
      (hg0 i) (hμ i) (hsign i)
  have hηb := Cvs.L2a.FarFarConstantClosedForm.farFar_le_closed_of_le a hg hg₁ hg₂c hang hc₀ hcc hχi hχ0 hχc
  have hη : ∫ y in Ioi 1, ‖(wF y : ℂ) * calK c ((Ioi 1).indicator fun x =>
        ((wF x * ∑ i, a i * psi c (g i) x : ℝ) : ℂ)) y‖ ^ 2
      ≤ √(Cvs.L2a.FarFarConstantClosedForm.cEtaClosed c₀ / c) ^ 2 * ∫ ξ in Ioi 1, (∑ i, a i * psi c (g i) ξ) ^ 2 := by
    rwa [Real.sq_sqrt (div_nonneg (cEtaClosed_nonneg c₀) hc0.le)]
  have hcor := corners_ge_loc_full a hg hg₁ hg₂c hang hc hχ0 hσ₀ hσ hχi hM3 hmass hshell
  have hκ : Cvs.L2a.LocalisedBottomCorners.kapI c (Fintype.card ι) ≤ 1 :=
    (Cvs.L2a.LocalisedConstants.kappaI_mem (by linarith) (Nat.cast_nonneg _) hJ).2
  have hmain := Cvs.L2a.LocalisedConstants.main_le_Rbar hκ hM3
  have hP0 : 0 ≤ ∫ x in Ioi 1, (∑ i, a i * psi c (g i) x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hsum : -(Cvs.L2a.LocalisedConstants.Rbar + ρ
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
    (Cvs.L2a.SpanPlungeBound.epsTauFlat_nonneg 5) hτ continuous_wF.1.measurable
    (fun x => (Cvs.L2a.FarFarBound.wF_bounds x).1) (fun x => (Cvs.L2a.FarFarBound.wF_bounds x).2.1) hM1 hwX
    (Real.sqrt_nonneg _) hη hsum hBC hA

/-- **THEOREM JA, full span**: for `c ≥ 10¹⁶`, `0 < σ₀ ≤ c² − χᵢ`, `5c ≤ c² − χᵢ` off `S`, (BC) on `S` at `θ` at every
integer `M ≥ 3`, `∫₁³ ψᵢ² > 0`, `resLoc(c, M) ≤ ρ` and `A_full > 0`: `κ_full > 0` and `κ_full·Σ aᵢ²∫₁^M ψᵢ² ≤ N(M)`. -/
theorem JA_integer_floor_full (a : ι → ℝ)
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
    (S : Finset ι) (hdeep : ∀ i ∉ S, 5 * c ≤ c ^ 2 - χ i)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → resLoc c (Fintype.card ι) M ≤ ρ)
    {θ : ℝ} (hBC : ∀ M : ℕ, 3 ≤ M → BandCoupling c g μ a S wF M θ)
    (hA : 0 < aJAfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ) :
    0 < kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ
      ∧ ∀ M : ℕ, 3 ≤ M → (∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2) →
        kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
          ≤ ∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2 := by
  have hc4 : (4096 : ℝ) ≤ c := le_trans (by norm_num) hc
  have hshell := shellM2_strip a hg hg₁ hg₂c hang hc4 hχ0 hσ₀ hσ hχi hmass3
  refine ⟨kappaFfull_pos hA, fun M hM3 hmass => ?_⟩
  exact JA_floor_full a hg hg₁ hg₂c hang hc4 (by norm_num) hc hχ0 hσ₀ hσ hχi heven hg0 hμ hidx hJ hshell S hdeep
    hM3 hmass (hρ M hM3) (hBC M hM3) hA.le

end floor

end Cvs.L2a.FullSpanFrameFloor
