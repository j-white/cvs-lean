import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutPointCountForm
import Cvs.L2a.CutRemainderDensity
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.FirstStepRemainderCount
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.KappaUniformInX
import Cvs.L2a.LocalisedBottomCorners
import Cvs.L2a.LowConstantUniform
import Cvs.L2a.PerLevelFarLeak
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RampCutSumsUniform
import Cvs.L2a.RungSpanLowMass
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TopCornerSum
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full-tail L2a on the deep span

With `T = c/(κ(1 + log c))`, `η = Ē/(κκ_F)`, `k₁ = 2`, `ε(k) = A/k` and the `X`-free NS constant, a frame floor
`κ_F` at every integer `n ≥ 3` gives `b̄·N(M) ≤ W(M)` at every integer `M ≥ 3` and `b̄·N_∞ ≤ W_∞` through
`FullTailFloorLimit`'s limit, with `b̄ = archSymbol T − 114/T − (archSymbol T − archSymbol 0)Ē/(κκ_F) − (log 2 + 4√(A/2))
− (63/40)(Λ̄₀ + κ̄)/κ_F − 49(c/4 + 1)/(2c²κ_F)`; `FrameFloorIntegerM`'s JA supplies `κ_F` for `c ≥ 10¹⁶`.
-/

noncomputable section

namespace Cvs.L2a.FullTailDeepSpan

open MeasureTheory Real Set Filter Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.CutWeightResidual Cvs.L2a.SpectralMassLevelLeak Cvs.L2a.CutPointCountForm Cvs.L2a.FirstStepRemainderCount Cvs.L2a.CutEstimateFrameFloor Cvs.L2a.PerLevelFarLeak Cvs.L2a.FullTailConvergence Cvs.L2a.RungSpanLowMass Cvs.L2a.LowConstantUniform Cvs.L2a.RampCutSumsUniform Cvs.L2a.KappaUniformInX
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- The frequency cut `T = c/(κ(1 + log c))`. -/
def TL (c κ : ℝ) : ℝ := c / (κ * (1 + Real.log c))

/-- The level radius `r = (T² + 1/16)/c²` of Cvs.L2a.PerLevelFarLeak. -/
def rL (c κ : ℝ) : ℝ := (TL c κ ^ 2 + 1 / 16) / c ^ 2

/-- **The L2a bracket** `b̄ = archSymbol T − 114/T − (archSymbol T − archSymbol 0)Ē/(κκ_F) − (log 2 + 4√(A/2))
− (63/40)(Λ̄₀ + κ̄)/κ_F − 49(c/4 + 1)/(2c²κ_F)`, `A = ALoc J c r T κ_F`. -/
def bBar (c κ J κF : ℝ) : ℝ :=
  archSymbol (TL c κ) - 114 / TL c κ - (archSymbol (TL c κ) - archSymbol 0) * (Ebar / (κ * κF))
    - (Real.log 2 + 4 * √(ALoc J c (rL c κ) (TL c κ) κF / 2))
    - 63 / 40 * (LambdaBar0 + kappaBar) / κF - 49 * (c / 4 + 1) / (2 * c ^ 2 * κF)

/-! ### The low and level constants at `K0 = κ(1 + log c)` -/

/-- `0 < κ(1 + log c)` and `rLow c (κ(1 + log c)) < 1` for `c ≥ 80`, `κ ≥ 1`. -/
theorem K0_pos_rLow_lt {c κ : ℝ} (hc : 80 ≤ c) (hκ1 : 1 ≤ κ) :
    0 < κ * (1 + Real.log c) ∧ rLow c (κ * (1 + Real.log c)) < 1 := by
  have hL : 0 < Real.log c := Real.log_pos (by linarith)
  obtain ⟨-, hrρ, hρb⟩ := rLow_le hc hκ1
  exact ⟨by positivity, (hrρ.trans hρb).trans_lt rBar_mem.2⟩

/-- `T² + 1/16 ≤ r c²` and `r < 1` for `r = rL c κ`, `c ≥ 80`, `κ ≥ 1`. -/
theorem rL_mem {c κ : ℝ} (hc : 80 ≤ c) (hκ1 : 1 ≤ κ) :
    TL c κ ^ 2 + 1 / 16 ≤ rL c κ * c ^ 2 ∧ rL c κ < 1 := by
  have hc0 : 0 < c := by linarith
  obtain ⟨hK0, hr⟩ := K0_pos_rLow_lt hc hκ1
  refine ⟨le_of_eq (by unfold rL; field_simp), ?_⟩
  have e : rL c κ = 1 / (κ * (1 + Real.log c)) ^ 2 + 1 / (16 * c ^ 2) := by
    unfold rL TL; field_simp
  have h4 : 1 / (16 * c ^ 2) ≤ 1 / (4 * c ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg c])
  rw [e]
  unfold rLow at hr
  linarith

/-- `η_P/κ_F ≤ Ē/(κκ_F)` at `K0 = κ(1 + log c)`. -/
theorem etaP_div_le {c κ J κF : ℝ} (hc : 80 ≤ c) (hκ1 : 1 ≤ κ) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1)
    (hκ : 0 < κF) : etaP c (κ * (1 + Real.log c)) J / κF ≤ Ebar / (κ * κF) := by
  rw [← div_div]
  exact div_le_div_of_nonneg_right (etaP_le_Ebar hc hκ1 hJ0 hJ) hκ.le

/-- The NS constant at level `X`, `(6J/c)(Λ°(X) + κ(X))/κ_F`, is at most `(63/40)(Λ̄₀ + κ̄)/κ_F`. -/
theorem ns_count_le {c J κF : ℝ} (hc : 80 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) (hκ : 0 < κF) (X : ℝ) :
    6 * J / c * (lamCount nsRamp (5 / 4) X + kapCount nsRamp nsRamp' (5 / 4) X) / κF
      ≤ 63 / 40 * (LambdaBar0 + kappaBar) / κF := by
  have hc0 : 0 < c := by linarith
  have h1 : 6 * J / c * (lamCount nsRamp (5 / 4) X + kapCount nsRamp nsRamp' (5 / 4) X)
      ≤ 6 * J / c * (LambdaBar0 + kappaBar) :=
    mul_le_mul_of_nonneg_left (add_le_add (lamCount_nsRamp_le X) (kapCount_nsRamp_le X)) (by positivity)
  exact (div_le_div_of_nonneg_right h1 hκ.le).trans (ns_const_le hc hJ hκ)

/-- `∫₁^X ψ² ≥ ∫₁^3 ψ²` for `X ≥ 3`. -/
theorem mass_mono {g g₁ : ℝ → ℝ} {c : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) {X : ℝ}
    (hX : 3 ≤ X) : ∫ t in (1 : ℝ)..3, psi c g t ^ 2 ≤ ∫ t in (1 : ℝ)..X, psi c g t ^ 2 := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hcont : Continuous fun t => psi c g t ^ 2 := ((contDiff_psi hgc c).continuous).pow 2
  have e := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable (1 : ℝ) 3) (hcont.intervalIntegrable 3 X)
  have : 0 ≤ ∫ t in (3 : ℝ)..X, psi c g t ^ 2 := intervalIntegral.integral_nonneg hX fun _ _ => sq_nonneg _
  linarith

variable {ι : Type} [Fintype ι]

/-! ### L2a at every integer `M` and on the full tail, from a floor at every integer -/

/-- **L2a at an integer `M ≥ 3`**: `LowConstantUniform`'s bracket at `X = M` is at least `b̄`, so a floor `κ_F` at `M` gives
`b̄·N(M) ≤ W(M)`. -/
theorem L2a_at_M {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχinj : Function.Injective χ)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hκ1 : 1 ≤ κ) (hT : 2 ≤ TL c κ) (hκ : 0 < κF)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M θ ^ 2) :
    bBar c κ (Fintype.card ι) κF * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M)) := by
  have hX : (2 : ℝ) ≤ M := by exact_mod_cast (show 2 ≤ M by omega)
  have h := L2a_span_fulltail_ff_unif a hg hg₁ hg₂c hang hX hc hχ0 hσ hχinj hM hJ hκ1 hT hκ hFF
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _)) h
  have hns := ns_count_le hc (Nat.cast_nonneg _) hJ hκ (M : ℝ)
  unfold bBar rL TL
  linarith

/-- **L2a on the full tail from an integer floor**: a floor `κ_F` at every integer `n ≥ 3` gives
`b̄·∫₁^∞ fullTail(Φ)² ≤ W_∞(Φ)`, via Cvs.L2a.FullTailFloorLimit with `RungSpanLowMass`'s `hlow`, `PerLevelFarLeak`'s `hε` (`k₁ = 2`) and `KappaUniformInX`'s `hNS`. -/
theorem L2a_fulltail_of_floor {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχinj : Function.Injective χ)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hκ1 : 1 ≤ κ) (hT : 2 ≤ TL c κ) (hκ : 0 < κF)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2)
    (hFF : ∀ n : ℕ, 3 ≤ n → κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..n, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n θ ^ 2) :
    bBar c κ (Fintype.card ι) κF * (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)
      ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) := by
  set J : ℝ := (Fintype.card ι : ℝ) with hJd
  set A := ALoc J c (rL c κ) (TL c κ) κF with hA
  set C := 6 * J / c * (LambdaBar0 + kappaBar) / κF with hC
  have hχc : ∀ i, χ i < c ^ 2 := fun i => by have := hσ i; nlinarith
  obtain ⟨hK0, hr⟩ := K0_pos_rLow_lt hc hκ1
  obtain ⟨hTr, hr'⟩ := rL_mem hc hκ1
  have hη := etaP_div_le hc hκ1 (Nat.cast_nonneg _) hJ hκ
  have hns := ns_const_le hc hJ hκ
  refine Cvs.L2a.FullTailFloorLimit.L2a_fulltail_limit a (fun _ => nsRamp) (fun _ k => A / k) (fun _ => TL c κ)
    (fun _ => Ebar / (κ * κF)) (fun _ => 2) (fun _ => 3 / 2) (fun _ => 0) (fun _ => C) (fun _ => κF)
    hg hg₁ hg₂c hang hc hχ0 hσ hJ ?_
  refine (eventually_atTop.2 ⟨3, fun n hn => ?_⟩).frequently
  have hX : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hX3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..n, psi c (g i) ξ ^ 2 := fun i =>
    (hmass i).trans_le (mass_mono (hg i) hX3)
  have hF := hFF n hn
  have hN0 : 0 ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hlow := hlow_of_FF a hg hg₁ hg₂c hang hX hc hχ0 hσ hχinj hM hK0 hr hκ hF
  have hε := hloc_span_green a hg hg₁ hg₂c hang hX hc hχ0 hχc hM hκ hF (by linarith) hTr hr'
  have hNS := NS_unif_nsRamp a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hκ hF
  have hI := integral_min_sqrt_le (A := A) hX
  refine ⟨hX, hM, hκ, hF, hT, ?_, by norm_num, hX, measurable_const.div measurable_id, hε, ?_, by norm_num,
    fun θ hθ => nsRamp_nonneg hθ, fun θ hθ => nsRamp_le_log hθ, fun θ hθ => nsRamp_of_ge hθ, zero_le_one,
    hNS, ?_⟩
  · exact hlow.trans (mul_le_mul_of_nonneg_right hη hN0)
  · exact Cvs.L2a.CutRemainderDensity.continuousOn_nsRamp.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1])
  · show bBar c κ J κF ≤ _
    unfold bBar
    linarith

/-! ### The deep-span L2a with JA's floor -/

/-- **The full-tail L2a on the deep span**: under `FrameFloorIntegerM`'s JA hypotheses (`c ≥ 10¹⁶`, `σᵢ² ≥ 5c`, the `m = 2`
shells, `resLoc ≤ ρ ≤ 13/100`), `κ ≥ 1`, `T ≥ 2` and `∫₁³ ψᵢ² > 0`: `κ_F > 0`, `b̄·N(M) ≤ W(M)` at every
integer `M ≥ 3`, and `b̄·∫₁^∞ fullTail(Φ)² ≤ W_∞(Φ)`, with `κ_F = kappaF 10¹⁶ c J ρ`. -/
theorem L2a_fulltail_span {μ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ ρ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 16 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s) (hg0 : ∀ i, ∃ s ∈ Icc (-1 : ℝ) 1, g i s ≠ 0)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hshell : Cvs.L2a.LocalisedBottomCorners.ShellM2 c (Cvs.L2a.TopCornerSum.deltaS c) (Cvs.L2a.TopCornerSum.deltaS c)
      (Cvs.L2a.TopCornerSum.sS c) χ g a)
    (hρ : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc c (Fintype.card ι) M ≤ ρ) (hρ1 : ρ ≤ 13 / 100)
    (hκ1 : 1 ≤ κ) (hT : 2 ≤ TL c κ) (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2) :
    0 < Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) c (Fintype.card ι) ρ
      ∧ (∀ M : ℕ, 3 ≤ M →
        bBar c κ (Fintype.card ι) (Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) c (Fintype.card ι) ρ)
            * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M θ ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M)))
      ∧ bBar c κ (Fintype.card ι) (Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) c (Fintype.card ι) ρ)
          * (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) := by
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc
  obtain ⟨hκ, hFF⟩ := Cvs.L2a.FrameFloorIntegerM.JA_integer_floor a hg hg₁ hg₂c hang hc hχ0 hσ hχi heven hg0 hμ
    hidx hJ hshell hρ hρ1
  have hM : ∀ M : ℕ, 3 ≤ M → ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2 := fun M hM3 i =>
    (hmass i).trans_le (mass_mono (hg i) (by exact_mod_cast hM3))
  have hFF' : ∀ n : ℕ, 3 ≤ n → _ := fun n hn => hFF n hn (hM n hn)
  refine ⟨hκ, fun M hM3 => ?_, ?_⟩
  · exact L2a_at_M a hg hg₁ hg₂c hang hc80 hχ0 hσ hχi hJ hκ1 hT hκ hM3 (hM M hM3) (hFF' M hM3)
  · exact L2a_fulltail_of_floor a hg hg₁ hg₂c hang hc80 hχ0 hσ hχi hJ hκ1 hT hκ hmass hFF'

end Cvs.L2a.FullTailDeepSpan
