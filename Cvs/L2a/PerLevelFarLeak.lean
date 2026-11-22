import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.FarPartDirichletSplit
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTailFullTail
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanFromLowMass
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.FarPartLevelBound
import Cvs.Prolate.Mellin.GreenBoundaryBound
import Cvs.Prolate.Mellin.GreenBulkBound
import Cvs.Prolate.ProlateWindowMassIdentity
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The per-level far leak on the rung span (THEOREM LOC)

Cvs.Prolate.Mellin.FarPartLevelBound with `ProlateWindowMassIdentity`'s `E ≤ 6c∫₁^X ψ²` and the frame floor gives `PositionTailFullTail`'s `hε` with `ε(k) = A/k`,
`A = 6J·C̄²T/(πc²κ_F)`; since `∫₂^X min(1, 2√(A/k))/k ≤ 4√(A/2)`, the loc term is `log 2 + 4√(A/2)`.
-/

namespace Cvs.L2a.PerLevelFarLeak

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.SpectralMassLevelLeak Cvs.L2a.FarPartDirichletSplit Cvs.Prolate.Mellin.FarPartLevelBound
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)
open scoped FourierTransform

/-- The far-leak constant `A = 6J·C̄²·T/(πc²κ_F)`. -/
noncomputable def ALoc (J c r T κF : ℝ) : ℝ := 6 * J * Cbar c r ^ 2 * T / (π * c ^ 2 * κF)

/-- **Per-rung far mass**: for a rung with `0 ≤ χ < c²`, `c ≥ 80`, `2 ≤ k ≤ X`, `T² + 1/16 ≤ r c²`, `r < 1`,
`specMass (posTail ψ X − posTail ψ k)(kT) ≤ 6C̄²T·m/(πc²k)`, `m = ∫₁^X ψ²`. -/
theorem specMass_far_rung_le {g g₁ g₂ : ℝ → ℝ} {c χ r T k X : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hk : 2 ≤ k) (hkX : k ≤ X) (hT : 0 ≤ T)
    (hTr : T ^ 2 + 1 / 16 ≤ r * c ^ 2) (hr : r < 1) :
    specMass (posTail (psi c g) X - posTail (psi c g) k) (k * T)
      ≤ 6 * Cbar c r ^ 2 * T * (∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2) / (π * c ^ 2 * k) := by
  obtain ⟨hψ, hu, hψc, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hX : 2 ≤ X := le_trans hk hkX
  have hE := Cvs.Prolate.ProlateWindowMassIdentity.far_energy_le_rung hg hg₁ hg₂c hang hc hχ0 hχ hX
  set m := ∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2 with hm
  have hm0 : 0 ≤ m := intervalIntegral.integral_nonneg (by linarith) fun ξ _ => sq_nonneg _
  have hlev : ∀ t, |t| < k * T →
      ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (logScale (posTail (psi c g) X - posTail (psi c g) k))) (t / (2 * π))‖
        ≤ Cbar c r * √(6 * c * m / c ^ 3) / k := fun t ht =>
    mellin_level_le hc0 hχ0 hχ.le hk hkX hTr hr ht.le hψc.continuousOn
      (fun ξ hξ => hψ ξ (by linarith [hξ.1])) (fun ξ _ => hu ξ)
      (fun ξ hξ => hE ξ ⟨by linarith [hξ.1], hξ.2⟩)
  have hCb : 0 ≤ Cbar c r := by unfold Cbar; positivity
  have h := specMass_le_sup_fourier (posTail (psi c g) X - posTail (psi c g) k) (K := k * T)
    (B := Cbar c r * √(6 * c * m / c ^ 3) / k) (by positivity)
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hlev t ht) 2)
  refine h.trans (le_of_eq ?_)
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- **`hε` of Cvs.L2a.PositionTailFullTail on the rung span**: with the frame floor `κ_F`, for every `k ∈ [2, X]`,
`specMass (posTail Φ X − posTail Φ k)(kT) ≤ (A/k)·N`, `A = ALoc J c r T κ_F`, `J` the number of rungs. -/
theorem hloc_span_green {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {X T r κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i, χ i < c ^ 2)
    (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hT : 0 ≤ T) (hTr : T ^ 2 + 1 / 16 ≤ r * c ^ 2) (hr : r < 1) :
    ∀ k ∈ Icc (2 : ℝ) X,
      specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X - posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k)
          (k * T)
        ≤ ALoc (Fintype.card ι) c r T κF / k
          * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 := by
  intro k hk
  have hk0 : 0 < k := by linarith [hk.1]
  have hc0 : 0 < c := by linarith
  set N := ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 with hN
  set m : ι → ℝ := fun i => ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 with hm
  set G : ι → ℝ → ℝ := fun i => posTail (psi c (g i)) X - posTail (psi c (g i)) k with hG
  have e : posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X - posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k
      = fun θ => ∑ i, a i * G i θ := by
    funext θ
    simp only [Pi.sub_apply, hG]
    rw [Cvs.L2a.PositionTailSpanAdapters.posTail_sum, Cvs.L2a.PositionTailSpanAdapters.posTail_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hΦ : ∀ i, ContDiff ℝ 1 (psi c (g i)) := fun i =>
    Cvs.L2a.RungSpanFromLowMass.contDiff_psi (hg i) (hg₁ i) (hg₂c i) (hang i)
  have hadX := fun i => Cvs.L2a.PositionTailAdmissible.admissible_posTail (by linarith : (1 : ℝ) ≤ X) (hΦ i).contDiffOn
  have hadk := fun i => Cvs.L2a.PositionTailAdmissible.admissible_posTail (X := k) (by linarith [hk.1])
    (hΦ i).contDiffOn
  have h2 : ∀ i, MemLp (logScale (G i)) 2 volume := fun i => by
    simp only [hG]; rw [logScale_sub]; exact (hadX i).1.sub (hadk i).1
  have h1 : ∀ i, Integrable (logScale (G i)) volume := fun i => by
    simp only [hG]; rw [logScale_sub]; exact (hadX i).2.1.sub (hadk i).2.1
  have hspan := specMass_span_le a m G hM h2 h1 (k * T)
  rw [e]
  have hrung : ∀ i, specMass (G i) (k * T) / m i ≤ 6 * Cbar c r ^ 2 * T / (π * c ^ 2 * k) := fun i => by
    have h := specMass_far_rung_le (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχ i) hk.1 hk.2 hT hTr hr
    rw [div_le_iff₀ (hM i)]
    calc specMass (G i) (k * T) ≤ 6 * Cbar c r ^ 2 * T * m i / (π * c ^ 2 * k) := h
      _ = 6 * Cbar c r ^ 2 * T / (π * c ^ 2 * k) * m i := by ring
  have hsum : ∑ i, specMass (G i) (k * T) / m i ≤ Fintype.card ι * (6 * Cbar c r ^ 2 * T / (π * c ^ 2 * k)) := by
    calc ∑ i, specMass (G i) (k * T) / m i ≤ ∑ _i : ι, 6 * Cbar c r ^ 2 * T / (π * c ^ 2 * k) :=
          Finset.sum_le_sum fun i _ => hrung i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hS0 : 0 ≤ ∑ i, a i ^ 2 * m i := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have hSN : ∑ i, a i ^ 2 * m i ≤ N / κF := by rw [le_div_iff₀ hκ]; linarith
  have hQ0 : 0 ≤ Fintype.card ι * (6 * Cbar c r ^ 2 * T / (π * c ^ 2 * k)) := by positivity
  calc specMass (fun θ => ∑ i, a i * G i θ) (k * T)
      ≤ (∑ i, a i ^ 2 * m i) * ∑ i, specMass (G i) (k * T) / m i := hspan
    _ ≤ (N / κF) * (Fintype.card ι * (6 * Cbar c r ^ 2 * T / (π * c ^ 2 * k))) :=
        mul_le_mul hSN hsum (Finset.sum_nonneg fun i _ => div_nonneg (specMass_nonneg _ _) (hM i).le)
          (by have : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
              positivity)
    _ = ALoc (Fintype.card ι) c r T κF / k * N := by unfold ALoc; field_simp

/-- `(−2/√k)′ = 1/(k√k)` for `k > 0`. -/
theorem hasDerivAt_neg_inv_sqrt {k : ℝ} (hk : 0 < k) :
    HasDerivAt (fun x => -2 * (√x)⁻¹) (1 / (k * √k)) k := by
  have hs : 0 < √k := Real.sqrt_pos.mpr hk
  have h := ((Real.hasDerivAt_sqrt hk.ne').inv hs.ne').const_mul (-2 : ℝ)
  refine h.congr_deriv ?_
  have hss : √k * √k = k := Real.mul_self_sqrt hk.le
  field_simp
  nlinarith [hss]

/-- **The level integral**: `∫₂^X min(1, 2√(A/k))/k dk ≤ 4√(A/2)`, uniformly in `X ≥ 2`. -/
theorem integral_min_sqrt_le {A X : ℝ} (hX : 2 ≤ X) :
    ∫ k in (2 : ℝ)..X, min 1 (2 * √(A / k)) / k ≤ 4 * √(A / 2) := by
  have hpos : ∀ x ∈ uIcc (2 : ℝ) X, 0 < x := fun x hx => by rw [uIcc_of_le hX] at hx; linarith [hx.1]
  have hc1 : ContinuousOn (fun k : ℝ => min 1 (2 * √(A / k)) / k) (Icc 2 X) := by
    have hne : ∀ x ∈ Icc (2 : ℝ) X, x ≠ 0 := fun x hx => (show (0 : ℝ) < x by linarith [hx.1]).ne'
    fun_prop (disch := assumption)
  have hc2 : ContinuousOn (fun k : ℝ => 2 * √A * (1 / (k * √k))) (uIcc 2 X) := by
    have hne : ∀ x ∈ uIcc (2 : ℝ) X, x * √x ≠ 0 := fun x hx =>
      (mul_pos (hpos x hx) (Real.sqrt_pos.mpr (hpos x hx))).ne'
    fun_prop (disch := assumption)
  have hle : ∫ k in (2 : ℝ)..X, min 1 (2 * √(A / k)) / k ≤ ∫ k in (2 : ℝ)..X, 2 * √A * (1 / (k * √k)) := by
    refine intervalIntegral.integral_mono_on hX (hc1.intervalIntegrable_of_Icc hX)
      (hc2.intervalIntegrable) fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
    calc min 1 (2 * √(A / x)) / x ≤ 2 * √(A / x) / x := div_le_div_of_nonneg_right (min_le_right _ _) hx0.le
      _ = 2 * √A * (1 / (x * √x)) := by rw [Real.sqrt_div' A hx0.le]; field_simp
  have hint : ∫ k in (2 : ℝ)..X, 2 * √A * (1 / (k * √k)) = 2 * √A * (2 * (√2)⁻¹ - 2 * (√X)⁻¹) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_neg_inv_sqrt (hpos x hx))
        ((ContinuousOn.div continuousOn_const (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
          fun x hx => (mul_pos (hpos x hx) (Real.sqrt_pos.mpr (hpos x hx))).ne').intervalIntegrable)]
    ring
  have hX0 : 0 < X := by linarith
  have h4 : 2 * √A * (2 * (√2)⁻¹ - 2 * (√X)⁻¹) ≤ 4 * √(A / 2) := by
    have h1 : 0 ≤ (√X)⁻¹ := by positivity
    have h2 : 4 * √(A / 2) = 2 * √A * (2 * (√2)⁻¹) := by rw [Real.sqrt_div' A (by norm_num)]; ring
    rw [h2]
    have : 0 ≤ 2 * √A := by positivity
    nlinarith
  linarith

/-- **Cvs.L2a.PositionTailFullTail with `hε` discharged**: the loc term of the full-tail L2a is `log 2 + 4√(A/2)`, `A = ALoc J c r T κ_F`. -/
theorem L2a_span_fulltail_loc {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (ω : ℝ → ℝ) {X T η r t2 εc C κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hT : 2 ≤ T) (hTr : T ^ 2 + 1 / 16 ≤ r * c ^ 2) (hr : r < 1)
    (hlow : ∫ t in {t : ℝ | |t| < T}, specDensity (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) t
      ≤ η * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hω : ContinuousOn ω (Icc 1 X)) (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωle : ∀ θ, 1 ≤ θ → ω θ ≤ Real.log θ) (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ) (hεc : εc ≤ 1)
    (hNS : Cvs.L2a.CutWeightResidual.cutNS ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X
      ≤ εc * (-(Cvs.L2a.CutWeightResidual.cutW ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X))
        + C * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    (archSymbol T - 114 / T - (archSymbol T - archSymbol 0) * η
        - (Real.log 2 + 4 * √(ALoc (Fintype.card ι) c r T κF / 2)) - C - 49 * (c / 4 + 1) / (2 * c ^ 2 * κF))
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) := by
  set A := ALoc (Fintype.card ι) c r T κF with hA
  have hc0 : 0 < c := by linarith
  have hχ : ∀ i, χ i < c ^ 2 := fun i => by nlinarith [hσ i]
  have hε := hloc_span_green a hg hg₁ hg₂c hang hX hc hχ0 hχ hM hκ hFF (by linarith) hTr hr
  have hεm : Measurable (fun k : ℝ => A / k) := measurable_const.div measurable_id
  have h := Cvs.L2a.PositionTailFullTail.L2a_span_fulltail a ω (fun k => A / k) hg hg₁ hg₂c hang hX hc hχ0 hσ hM hJ hκ
    hFF hT hlow (by norm_num : (1 : ℝ) ≤ 2) hX hεm hε hω ht2' hω0 hωle hωeq hεc hNS
  have hI := integral_min_sqrt_le (A := A) hX
  have hN0 : 0 ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hN0) h
  linarith

end Cvs.L2a.PerLevelFarLeak
