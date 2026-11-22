import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.FullTailArchChannel
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PositionTailFullTail
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
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
# The frame floor and L2a pass to the full tail

A frequent floor `κ P(X) ≤ N_X` gives `κ P_∞ ≤ N_∞`; `κ P_∞ ≤ N_∞` for all coefficients gives `(κ − δ) P(X) ≤ N_X`
for large `X`, uniformly (Gram entries). Cvs.L2a.PositionTailFullTail at integers `X = n` with bracket `≥ b` gives `b N_∞ ≤ W_∞`.
-/

namespace Cvs.L2a.FullTailFloorLimit

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.FullTailConvergence Cvs.L2a.TailLogScaleTest Cvs.L2a.CutWeightResidual Cvs.L2a.SpectralMassLevelLeak
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)

/-- `ψ_c g` is square integrable on `(1, ∞)`. -/
theorem integrableOn_psi_sq {g g₁ g₂ : ℝ → ℝ} {c : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) : IntegrableOn (fun ξ => psi c g ξ ^ 2) (Ioi 1) := by
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hcont : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  refine Integrable.mono' ((integrableOn_one_div_sq one_pos).const_mul (B ^ 2))
    (hcont.pow 2).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ξ hξ => ?_))
  have hξ1 : (1 : ℝ) < ξ := hξ
  have h := Cvs.L2a.FullTailArchChannel.abs_psi_le_BG hg hg₁ hg₂c hc hξ1.le
  rw [Real.norm_eq_abs, abs_pow]
  calc |psi c g ξ| ^ 2 ≤ (B / ξ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = B ^ 2 * (1 / ξ ^ 2) := by ring

/-- The span profile is the cosine transform of the span of the angular profiles. -/
theorem span_eq {ι : Type*} [Fintype ι] {g g₁ : ι → ℝ → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s) (c : ℝ) :
    (fun ξ => ∑ i, a i * psi c (g i) ξ) = psi c (fun t => ∑ i, a i * g i t) := by
  funext ξ
  exact (psi_sum Finset.univ a g (fun i _ => ContinuousOn.intervalIntegrable fun s hs =>
    (hg i s hs).continuousAt.continuousWithinAt) c ξ).symm

/-- The span of the angular profiles has the span of their derivatives as derivative. -/
theorem hasDerivAt_span {ι : Type*} [Fintype ι] {g g₁ : ι → ℝ → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s) :
    ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun t => ∑ i, a i * g i t) (∑ i, a i * g₁ i s) s := fun s hs =>
  HasDerivAt.fun_sum fun i _ => (hg i s hs).const_mul (a i)

/-- The span of continuous second derivatives is continuous. -/
theorem continuousOn_span {ι : Type*} [Fintype ι] {g₂ : ι → ℝ → ℝ} (a : ι → ℝ)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) :
    ContinuousOn (fun t => ∑ i, a i * g₂ i t) (uIcc (-1) 1) :=
  continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hg₂c i)

/-- **The span energies converge**: `N_X(a) → N_∞(a)`. -/
theorem tendsto_N_span {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) (hc : 0 < c) :
    Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) atTop
      (𝓝 (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)) := by
  rw [span_eq a hg c]
  exact tendsto_N (hasDerivAt_span a hg) (hasDerivAt_span a hg₁) (continuousOn_span a hg₂c) hc

/-- **The integer-`X` frame floor passes to the limit**: `κ P(X) ≤ N_X` frequently gives `κ P_∞ ≤ N_∞`. -/
theorem floor_limit {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) (hc : 0 < c) {κ : ℝ}
    (hFF : ∃ᶠ X in atTop, κ * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    κ * ∑ i, a i ^ 2 * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2 := by
  have hP : Tendsto (fun X : ℝ => ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)) atTop
      (𝓝 (∑ i, a i ^ 2 * (∫ ξ in Ioi 1, psi c (g i) ξ ^ 2))) :=
    tendsto_finsetSum _ fun i _ => (intervalIntegral_tendsto_integral_Ioi 1
      (integrableOn_psi_sq (hg i) (hg₁ i) (hg₂c i) hc) tendsto_id).const_mul _
  have hlim := (tendsto_N_span a hg hg₁ hg₂c hc).sub (hP.const_mul κ)
  have h0 := ge_of_tendsto_of_frequently hlim (hFF.mono fun X hX => sub_nonneg.mpr hX)
  linarith

/-- **A frequent bracket passes to `W_∞`**: `b ≤ B(X)` and `B(X) N_X ≤ W_X` frequently give `b N_∞ ≤ W_∞`. -/
theorem le_Winf_of_bracket {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) (hc : 0 < c) {b : ℝ} (B : ℝ → ℝ)
    (hB : ∃ᶠ X in atTop, b ≤ B X ∧ B X * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊ (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X))) :
    b * (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)
      ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) := by
  have hfr : ∃ᶠ X in atTop, b * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) :=
    hB.mono fun X hX => (mul_le_mul_of_nonneg_right hX.1
      (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)).trans hX.2
  rw [span_eq a hg c] at hfr ⊢
  exact Cvs.L2a.FullTailWeilFormLimit.le_Winf_of_frequently (hasDerivAt_span a hg) (hasDerivAt_span a hg₁)
    (continuousOn_span a hg₂c) hc hfr

/-- **L2a on the full tail**: `PositionTailFullTail`'s inputs at integer `X = n`, holding frequently with bracket `≥ b`, give
`b N_∞ ≤ W_∞`. -/
theorem L2a_fulltail_limit {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (ω ε : ℕ → ℝ → ℝ) (T η k₁ t2 εc C κF : ℕ → ℝ) {b : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
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
        - 49 * (c / 4 + 1) / (2 * c ^ 2 * κF n)) :
    b * (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)
      ≤ Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ) := by
  have hc0 : 0 < c := by linarith
  refine le_Winf_of_bracket a hg hg₁ hg₂c hc0 (fun _ => b) ?_
  refine tendsto_natCast_atTop_atTop.frequently (hn.mono fun n hn' => ?_)
  obtain ⟨hn2, hM, hκ, hFF, hT, hlow, hk₁, hk₁n, hεm, hε, hω, ht2, hω0, hωle, hωeq, hεc, hNS, hb⟩ := hn'
  refine ⟨le_rfl, ?_⟩
  have hL := Cvs.L2a.PositionTailFullTail.L2a_span_fulltail a (ω n) (ε n) hg hg₁ hg₂c hang hn2 hc hχ0 hσ hM hJ hκ
    hFF hT hlow hk₁ hk₁n hεm hε hω ht2 hω0 hωle hωeq hεc hNS
  exact (mul_le_mul_of_nonneg_right hb
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)).trans hL

end Cvs.L2a.FullTailFloorLimit
