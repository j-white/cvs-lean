import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutRemainderDensity
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.EllipticTilt
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.FrameFloorBandCoupling
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullSpanFrameFloor
import Cvs.L2a.FullSpanLowConstant
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.FullTailTiltedPole
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.KappaUniformInX
import Cvs.L2a.PerLevelFarLeak
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RampCutSumsUniform
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
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
# The full-tail L2a wiring on the full span

Cvs.L2a.LowConstantUniform, Cvs.L2a.FullTailFloorLimit and Cvs.L2a.FullTailDeepSpan with `5c ≤ c² − χᵢ` replaced by `χᵢ < c²`: the pole from Cvs.L2a.FullTailTiltedPole (`tiltK(23/24, c)² ≤ 49`
for `c ≥ 10⁴`), `hlow` from Cvs.L2a.FullSpanLowConstant (`Ē` replaced by `EbarFull`), `hε` from Cvs.L2a.PerLevelFarLeak, `hNS` from Cvs.L2a.KappaUniformInX, and the frame
floor `kappaFfull` from `FullSpanFrameFloor`'s JA with the band charged by the coupling hypothesis.
-/

noncomputable section

namespace Cvs.L2a.FullSpanWiring

open MeasureTheory Real Set Filter Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.CutWeightResidual Cvs.L2a.SpectralMassLevelLeak Cvs.L2a.CutPointCountForm Cvs.L2a.FirstStepRemainderCount Cvs.L2a.CutEstimateFrameFloor Cvs.L2a.PerLevelFarLeak Cvs.L2a.FullTailConvergence Cvs.L2a.RampCutSumsUniform Cvs.L2a.KappaUniformInX
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)
open Cvs.L2a.FullTailDeepSpan (TL rL rL_mem mass_mono)
open Cvs.L2a.EllipticTilt (tiltK tiltK_turn_le_seven)
open Cvs.L2a.FullSpanLowConstant (EbarFull)

/-- **The full-span L2a bracket**: `FullTailDeepSpan`'s `b̄` with `Ē` replaced by `EbarFull`. -/
def bBarFull (c κ J κF : ℝ) : ℝ :=
  archSymbol (TL c κ) - 114 / TL c κ - (archSymbol (TL c κ) - archSymbol 0) * (EbarFull / (κ * κF))
    - (Real.log 2 + 4 * √(ALoc J c (rL c κ) (TL c κ) κF / 2))
    - 63 / 40 * (LambdaBar0 + kappaBar) / κF - 49 * (c / 4 + 1) / (2 * c ^ 2 * κF)

/-- The pole coefficient: `tiltK(23/24, c)² ≤ 49` for `c ≥ 10⁴`. -/
theorem tiltK_sq_le {c : ℝ} (hc : 10 ^ 4 ≤ c) : tiltK (23 / 24) c ^ 2 ≤ 49 := by
  have h7 := tiltK_turn_le_seven hc
  have h0 : 0 ≤ tiltK (23 / 24) c := by unfold tiltK; positivity
  nlinarith

/-- `tiltK(23/24, c)²(c/4 + 1)/(2c²κ_F) ≤ 49(c/4 + 1)/(2c²κ_F)` for `c ≥ 10⁴`, `κ_F > 0`. -/
theorem pole_term_le {c κF : ℝ} (hc : 10 ^ 4 ≤ c) (hκ : 0 < κF) :
    tiltK (23 / 24) c ^ 2 * (c / 4 + 1) / (2 * c ^ 2 * κF) ≤ 49 * (c / 4 + 1) / (2 * c ^ 2 * κF) := by
  have hc0 : 0 < c := by linarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (tiltK_sq_le hc) (by linarith))
    (by positivity)

variable {ι : Type} [Fintype ι]

/-! ### Cvs.L2a.LowConstantUniform′: the bracket at one level `X`, with `χᵢ < c²` -/

/-- **The full-tail L2a under the frame floor, `χᵢ < c²`**: `FullTailTiltedPole`'s pole, `FullSpanLowConstant`'s `hlow` (`η = EbarFull/(κκ_F)`),
`PerLevelFarLeak`'s `hε` (`k₁ = 2`) and `KappaUniformInX`'s `X`-free `hNS`, at `T = c/(κ(1 + log c))`. -/
theorem L2a_span_fulltail_ff_full {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X κ κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hκ1 : 1 ≤ κ) (hT : 2 ≤ TL c κ) (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    (archSymbol (TL c κ) - 114 / TL c κ - (archSymbol (TL c κ) - archSymbol 0) * (EbarFull / (κ * κF))
        - (Real.log 2 + 4 * √(ALoc (Fintype.card ι) c (rL c κ) (TL c κ) κF / 2))
        - 6 * (Fintype.card ι : ℝ) / c * (LambdaBar0 + kappaBar) / κF
        - tiltK (23 / 24) c ^ 2 * (c / 4 + 1) / (2 * c ^ 2 * κF))
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) := by
  set A := ALoc (Fintype.card ι) c (rL c κ) (TL c κ) κF with hA
  obtain ⟨hTr, hr'⟩ := rL_mem hc hκ1
  have hχ1 : ∀ i, χ i ≤ c ^ 2 + c / 2 := fun i => by linarith [hχc i]
  have hlow : ∫ t in {t : ℝ | |t| < TL c κ},
        specDensity (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) t
      ≤ EbarFull / (κ * κF) * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
    Cvs.L2a.FullSpanLowConstant.hlow_of_FF_full_unif a hg hg₁ hg₂c hang hX hc hχ0 hχc hχinj hM hJ hκ1 hκ hFF
  have hε := hloc_span_green a hg hg₁ hg₂c hang hX hc hχ0 hχc hM hκ hFF (by linarith) hTr hr'
  have hNS := NS_unif_nsRamp a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hκ hFF
  have hεm : Measurable (fun k : ℝ => A / k) := measurable_const.div measurable_id
  have hω : ContinuousOn nsRamp (Icc 1 X) :=
    Cvs.L2a.CutRemainderDensity.continuousOn_nsRamp.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1])
  have h := Cvs.L2a.FullTailTiltedPole.L2a_span_fulltail a nsRamp (fun k => A / k) hg hg₁ hg₂c hang hX hc hχ0 hχ1
    hM hJ hκ hFF hT hlow (by norm_num : (1 : ℝ) ≤ 2) hX hεm hε hω (t2 := 3 / 2) (by norm_num)
    (fun θ hθ => nsRamp_nonneg hθ) (fun θ hθ => nsRamp_le_log hθ) (fun θ hθ => nsRamp_of_ge hθ)
    (εc := 0) (by norm_num) hNS
  have hI := integral_min_sqrt_le (A := A) hX
  have hN0 : 0 ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hN0) h
  linarith

/-! ### Cvs.L2a.FullTailDeepSpan′: L2a at every integer `M` -/

/-- **L2a at an integer `M ≥ 3`, `χᵢ < c²`**: for `c ≥ 10⁴` a floor `κ_F` at `M` gives `bBarFull·N(M) ≤ W(M)`. -/
theorem L2a_at_M_full {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 4 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχinj : Function.Injective χ)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hκ1 : 1 ≤ κ) (hT : 2 ≤ TL c κ) (hκ : 0 < κF)
    {M : ℕ} (hM3 : 3 ≤ M) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..M, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M θ ^ 2) :
    bBarFull c κ (Fintype.card ι) κF * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M)) := by
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc
  have hX : (2 : ℝ) ≤ M := by exact_mod_cast (show 2 ≤ M by omega)
  have h := L2a_span_fulltail_ff_full a hg hg₁ hg₂c hang hX hc80 hχ0 hχc hχinj hM hJ hκ1 hT hκ hFF
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _)) h
  have hns := ns_const_le hc80 hJ hκ
  have hpole := pole_term_le hc hκ
  unfold bBarFull
  linarith

/-! ### Cvs.L2a.FullTailFloorLimit′: the limit with the R2 pole -/

/-- **L2a on the full tail, `χᵢ ≤ c² + c/2`**: `FullTailTiltedPole`'s inputs at integer `X = n`, holding frequently with bracket
`≥ b`, give `b N_∞ ≤ W_∞`; the pole coefficient is `tiltK(23/24, c)²`. -/
theorem L2a_fulltail_limit_full {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (ω ε : ℕ → ℝ → ℝ) (T η k₁ t2 εc C κF : ℕ → ℝ) {b : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ1 : ∀ i, χ i ≤ c ^ 2 + c / 2)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hn : ∃ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ∧ (∀ i, 0 < ∫ ξ in (1 : ℝ)..n, psi c (g i) ξ ^ 2) ∧ 0 < κF n ∧
      κF n * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..n, psi c (g i) ξ ^ 2)
        ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n θ ^ 2 ∧
      2 ≤ T n ∧
      ∫ t in {t : ℝ | |t| < T n}, specDensity (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n)) t
        ≤ η n * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n θ ^ 2 ∧
      1 ≤ k₁ n ∧ k₁ n ≤ n ∧ Measurable (ε n) ∧
      (∀ k ∈ Icc (k₁ n) n, specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n
          - posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k) (k * T n)
        ≤ ε n k * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n θ ^ 2) ∧
      ContinuousOn (ω n) (Icc 1 n) ∧ t2 n ≤ 2 ∧ (∀ θ, 1 ≤ θ → 0 ≤ ω n θ) ∧
      (∀ θ, 1 ≤ θ → ω n θ ≤ Real.log θ) ∧ (∀ θ, t2 n ≤ θ → ω n θ = Real.log θ) ∧ εc n ≤ 1 ∧
      cutNS (ω n) (fun ξ => ∑ i, a i * psi c (g i) ξ) n
        ≤ εc n * (-(cutW (ω n) (fun ξ => ∑ i, a i * psi c (g i) ξ) n))
          + C n * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n θ ^ 2 ∧
      b ≤ archSymbol (T n) - 114 / T n - (archSymbol (T n) - archSymbol 0) * η n
        - (Real.log (k₁ n) + ∫ k in (k₁ n)..n, min 1 (2 * √(ε n k)) / k) - C n
        - tiltK (23 / 24) c ^ 2 * (c / 4 + 1) / (2 * c ^ 2 * κF n)) :
    b * (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)
      ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) := by
  have hc0 : 0 < c := by linarith
  refine Cvs.L2a.FullTailFloorLimit.le_Winf_of_bracket a hg hg₁ hg₂c hc0 (fun _ => b) ?_
  refine tendsto_natCast_atTop_atTop.frequently (hn.mono fun n hn' => ?_)
  obtain ⟨hn2, hM, hκ, hFF, hT, hlow, hk₁, hk₁n, hεm, hε, hω, ht2, hω0, hωle, hωeq, hεc, hNS, hb⟩ := hn'
  refine ⟨le_rfl, ?_⟩
  have hL := Cvs.L2a.FullTailTiltedPole.L2a_span_fulltail a (ω n) (ε n) hg hg₁ hg₂c hang hn2 hc hχ0 hχ1 hM hJ hκ
    hFF hT hlow hk₁ hk₁n hεm hε hω ht2 hω0 hωle hωeq hεc hNS
  exact (mul_le_mul_of_nonneg_right hb
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)).trans hL

/-- **L2a on the full tail from an integer floor, `χᵢ < c²`**: for `c ≥ 10⁴` a floor `κ_F` at every integer
`n ≥ 3` gives `bBarFull·∫₁^∞ fullTail(Φ)² ≤ W_∞(Φ)`. -/
theorem L2a_fulltail_of_floor_full {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 10 ^ 4 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχinj : Function.Injective χ)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hκ1 : 1 ≤ κ) (hT : 2 ≤ TL c κ) (hκ : 0 < κF)
    (hmass : ∀ i, 0 < ∫ t in (1 : ℝ)..3, psi c (g i) t ^ 2)
    (hFF : ∀ n : ℕ, 3 ≤ n → κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..n, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) n θ ^ 2) :
    bBarFull c κ (Fintype.card ι) κF * (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)
      ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) := by
  have hc80 : (80 : ℝ) ≤ c := le_trans (by norm_num) hc
  set J : ℝ := (Fintype.card ι : ℝ) with hJd
  set A := ALoc J c (rL c κ) (TL c κ) κF with hA
  set C := 6 * J / c * (LambdaBar0 + kappaBar) / κF with hC
  have hχ1 : ∀ i, χ i ≤ c ^ 2 + c / 2 := fun i => by linarith [hχc i]
  obtain ⟨hTr, hr'⟩ := rL_mem hc80 hκ1
  have hns := ns_const_le hc80 hJ hκ
  have hpole := pole_term_le hc hκ
  refine L2a_fulltail_limit_full a (fun _ => nsRamp) (fun _ k => A / k) (fun _ => TL c κ)
    (fun _ => EbarFull / (κ * κF)) (fun _ => 2) (fun _ => 3 / 2) (fun _ => 0) (fun _ => C) (fun _ => κF)
    hg hg₁ hg₂c hang hc80 hχ0 hχ1 hJ ?_
  refine (eventually_atTop.2 ⟨3, fun n hn => ?_⟩).frequently
  have hX : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hX3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..n, psi c (g i) ξ ^ 2 := fun i =>
    (hmass i).trans_le (mass_mono (hg i) hX3)
  have hF := hFF n hn
  have hlow := Cvs.L2a.FullSpanLowConstant.hlow_of_FF_full_unif a hg hg₁ hg₂c hang hX hc80 hχ0 hχc hχinj hM hJ hκ1
    hκ hF
  have hε := hloc_span_green a hg hg₁ hg₂c hang hX hc80 hχ0 hχc hM hκ hF (by linarith) hTr hr'
  have hNS := NS_unif_nsRamp a hg hg₁ hg₂c hang hc80 hχ0 hχc hX hM hκ hF
  have hI := integral_min_sqrt_le (A := A) hX
  refine ⟨hX, hM, hκ, hF, hT, hlow, by norm_num, hX, measurable_const.div measurable_id, hε, ?_, by norm_num,
    fun θ hθ => nsRamp_nonneg hθ, fun θ hθ => nsRamp_le_log hθ, fun θ hθ => nsRamp_of_ge hθ, zero_le_one,
    hNS, ?_⟩
  · exact Cvs.L2a.CutRemainderDensity.continuousOn_nsRamp.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1])
  · show bBarFull c κ J κF ≤ _
    unfold bBarFull
    linarith

/-! ### The full-span L2a with `FullSpanFrameFloor`'s floor -/

/-- **The full-tail L2a on the full span**: under `FullSpanFrameFloor`'s JA hypotheses (`c ≥ 10¹⁶`, `σ₀ ≤ c² − χᵢ` with
`σ₀ > 0`, the deep rungs off `S`, the coupling `(BC)` on `S`, `A_full > 0`), `κ ≥ 1` and `T ≥ 2`: `κ_F > 0`,
`bBarFull·N(M) ≤ W(M)` at every integer `M ≥ 3` and `bBarFull·N_∞ ≤ W_∞`, `κ_F = kappaFfull 10¹⁶ c J ρ σ₀ θ`. -/
theorem L2a_fulltail_full {μ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ : ℝ}
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
    (S : Finset ι) (hdeep : ∀ i ∉ S, 5 * c ≤ c ^ 2 - χ i)
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc c (Fintype.card ι) M ≤ ρ)
    {θ : ℝ} (hBC : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorBandCoupling.BandCoupling c g μ a S Cvs.L2a.FarIntegrationByParts.wF M θ)
    (hA : 0 < Cvs.L2a.FullSpanFrameFloor.aJAfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ)
    (hκ1 : 1 ≤ κ) (hT : 2 ≤ TL c κ) :
    0 < Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ
      ∧ (∀ M : ℕ, 3 ≤ M →
        bBarFull c κ (Fintype.card ι) (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ)
            * (∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M)))
      ∧ bBarFull c κ (Fintype.card ι) (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ)
          * (∫ y in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) := by
  have hc4 : (10 : ℝ) ^ 4 ≤ c := le_trans (by norm_num) hc
  have hχc : ∀ i, χ i < c ^ 2 := fun i => by linarith [hσ i]
  obtain ⟨hκ, hFF⟩ := Cvs.L2a.FullSpanFrameFloor.JA_integer_floor_full a hg hg₁ hg₂c hang hc hχ0 hσ₀ hσ hχi heven
    hg0 hμ hidx hJ hmass S hdeep hρ hBC hA
  have hM : ∀ M : ℕ, 3 ≤ M → ∀ i, 0 < ∫ t in (1 : ℝ)..M, psi c (g i) t ^ 2 := fun M hM3 i =>
    (hmass i).trans_le (mass_mono (hg i) (by exact_mod_cast hM3))
  have hFF' : ∀ n : ℕ, 3 ≤ n → _ := fun n hn => hFF n hn (hM n hn)
  refine ⟨hκ, fun M hM3 => ?_, ?_⟩
  · exact L2a_at_M_full a hg hg₁ hg₂c hang hc4 hχ0 hχc hχi hJ hκ1 hT hκ hM3 (hM M hM3) (hFF' M hM3)
  · exact L2a_fulltail_of_floor_full a hg hg₁ hg₂c hang hc4 hχ0 hχc hχi hJ hκ1 hT hκ hmass hFF'

/-- **The full-tail L2a on the band `𝓑 = {c² − χᵢ < 5c}`**: `L2a_fulltail_full` at `S = 𝓑`, with `(BC)` on the
band. -/
theorem L2a_fulltail_band {μ : ι → ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {κ : ℝ}
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
    {ρ : ℝ} (hρ : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorIntegerM.resLoc c (Fintype.card ι) M ≤ ρ)
    {θ : ℝ} (hBC : ∀ M : ℕ, 3 ≤ M → Cvs.L2a.FrameFloorBandCoupling.BandCoupling c g μ a
      (Cvs.L2a.FullSpanFrameFloor.bandSet c χ) Cvs.L2a.FarIntegrationByParts.wF M θ)
    (hA : 0 < Cvs.L2a.FullSpanFrameFloor.aJAfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ)
    (hκ1 : 1 ≤ κ) (hT : 2 ≤ TL c κ) :
    0 < Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ
      ∧ (∀ M : ℕ, 3 ≤ M →
        bBarFull c κ (Fintype.card ι) (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ)
            * (∫ y in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M y ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) M)))
      ∧ bBarFull c κ (Fintype.card ι) (Cvs.L2a.FullSpanFrameFloor.kappaFfull (10 ^ 16) c (Fintype.card ι) ρ σ₀ θ)
          * (∫ y in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) y ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
  L2a_fulltail_full a hg hg₁ hg₂c hang hc hχ0 hσ₀ hσ hχi heven hg0 hμ hidx hJ hmass
    (Cvs.L2a.FullSpanFrameFloor.bandSet c χ) (fun _ hi => Cvs.L2a.FullSpanFrameFloor.deep_of_notMem_bandSet hi) hρ hBC hA
    hκ1 hT

end Cvs.L2a.FullSpanWiring
