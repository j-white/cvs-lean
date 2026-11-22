import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.EllipticTilt
import Cvs.L2a.LogPositionCut
import Cvs.L2a.LogPositionIdentity
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpanPoleMellinFromRungs
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TiltFrameFreePole
import Cvs.Prolate.Envelope.TurningPointEnergyEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimePowerIndexed
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
# The tilted pole and full-tail L2a with no σ cut

For `c ≥ 80`, `0 ≤ χ ≤ c² + c/2` and `X ≥ 2`: `|∫_{(1,∞)} posTail ψ X θ (1 − 1/θ)| ≤ tiltK(23/24, c)√(∫₁^X ψ²)/c`.
With it `RungSpanPole`'s pole and `PositionTailFullTail`'s full-tail L2a hold for `0 ≤ χᵢ ≤ c² + c/2`, the constant `49` becoming
`tiltK(23/24, c)²`.
-/

namespace Cvs.L2a.FullTailTiltedPole

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.RungTiltedPole Cvs.Prolate.Envelope.TurningPointEnergyEnvelope Cvs.L2a.EllipticTilt

/-- **The tilted pole for `0 ≤ χ ≤ c² + c/2`**: for `c ≥ 80`, `X ≥ 2` and a system `ψ' = u/p`, `u' = −qψ`,
`|∫_{(1,∞)} posTail ψ X θ (1 − 1/θ)| ≤ tiltK (23/24) c · √(∫₁^X ψ²)/c`. -/
theorem tilt_le {c χ X : ℝ} {ψ u : ℝ → ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ c ^ 2 + c / 2)
    (hX : 2 ≤ X) (hψ : ∀ ξ, 1 < ξ → HasDerivAt ψ (u ξ / pP ξ) ξ) (hu : ∀ ξ, HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hψc : Continuous ψ) :
    |∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail ψ X θ * (1 - 1 / θ)|
      ≤ tiltK (23 / 24) c * √(∫ ξ in (1 : ℝ)..X, ψ ξ ^ 2) / c := by
  have hc0 : 0 < c := by linarith
  exact tilt_le_env hc hχ0 hX (by norm_num) (by norm_num) (fun ξ hξ => ell_of_le hc0 hχ1 hξ)
    (fun ξ hξ => cube_of_le hc hχ1 hξ) hψ hu hψc
    (far_energy_le_turn hc hχ0 hχ1 hX (fun t ht => hψ t (by linarith [ht.1])) (fun t _ => hu t)
      hψc.continuousOn)
    (energy_envelope_turn hc hχ0 hχ1 hX hψ hu hψc.continuousOn)

open Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity in
/-- **The per-rung tilted pole**: `tilt_le` for a rung `ψ = psi c g`, `c ≥ 80`, `0 ≤ χ ≤ c² + c/2`, `X ≥ 2`. -/
theorem tilt_le_rung {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ} (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {X : ℝ} (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ c ^ 2 + c / 2) (hX : 2 ≤ X) :
    |∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail (psi c g) X θ * (1 - 1 / θ)|
      ≤ tiltK (23 / 24) c * √(∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2) / c := by
  obtain ⟨hψ, hu, hψc, -⟩ := rung_system hg hg₁ hg₂c hang
  exact tilt_le hc hχ0 hχ1 hX hψ hu hψc

open Cvs.L2a.PositionTruncatedTail in
/-- **The pole from per-function tilt bounds**: for continuous `ψᵢ` with positive masses `mᵢ = ∫₁^X ψᵢ²`, tilts
`|∫_{(1,∞)} posTail ψᵢ X θ(1 − 1/θ)| ≤ K√mᵢ/c` and the frame floor `κF Σ aᵢ²mᵢ ≤ ∫F²` (`F = posTail Φ X`,
`Φ = Σ aᵢψᵢ`): `−(K²·#ι/(2c²κF))∫F² ≤ 2(∫F)(∫F/θ)`. -/
theorem pole_of_tilt {ι : Type} [Fintype ι] (a : ι → ℝ) {ψ : ι → ℝ → ℝ} {X κF K c : ℝ}
    (hc : 0 < c) (hψc : ∀ i, Continuous (ψ i)) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, ψ i ξ ^ 2) (hκ : 0 < κF)
    (hT : ∀ i, |∫ θ in Ioi 1, posTail (ψ i) X θ * (1 - 1 / θ)| ≤ K * √(∫ ξ in (1 : ℝ)..X, ψ i ξ ^ 2) / c)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, ψ i ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * ψ i ξ) X θ ^ 2) :
    -((K ^ 2 * Fintype.card ι / (2 * c ^ 2 * κF))
        * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * ψ i ξ) X θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * ψ i ξ) X θ)
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * ψ i ξ) X θ / θ) := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * ψ i ξ with hΦ
  set F := posTail Φ X with hF
  set N := ∫ θ in Ioi 1, F θ ^ 2 with hN
  set m : ι → ℝ := fun i => ∫ ξ in (1 : ℝ)..X, ψ i ξ ^ 2 with hm
  have hψo : ∀ i, ContinuousOn (ψ i) (Icc 1 X) := fun i => (hψc i).continuousOn
  have hΦc : ContinuousOn Φ (Icc 1 X) := by
    rw [hΦ]; exact (continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)).continuousOn
  have hw : ContinuousOn (fun θ : ℝ => 1 - 1 / θ) (Icc 1 X) :=
    continuousOn_const.sub (continuousOn_const.div continuousOn_id fun θ hθ =>
      (lt_of_lt_of_le one_pos hθ.1).ne')
  have hinv : ContinuousOn (fun θ : ℝ => θ⁻¹) (Icc 1 X) :=
    continuousOn_inv₀.mono fun θ hθ => (lt_of_lt_of_le one_pos hθ.1).ne'
  have hI1 : IntegrableOn (fun θ => F θ * 1) (Ioi 1) := integrableOn_posTail_mul Φ hΦc continuousOn_const
  have hI2 : IntegrableOn (fun θ => F θ * θ⁻¹) (Ioi 1) := integrableOn_posTail_mul Φ hΦc hinv
  have hdiff : (∫ θ in Ioi 1, F θ) - (∫ θ in Ioi 1, F θ / θ) = ∫ θ in Ioi 1, F θ * (1 - 1 / θ) := by
    have e1 : (∫ θ in Ioi 1, F θ) = ∫ θ in Ioi 1, F θ * 1 := by simp
    have e2 : (∫ θ in Ioi 1, F θ / θ) = ∫ θ in Ioi 1, F θ * θ⁻¹ := by simp [div_eq_mul_inv]
    rw [e1, e2, ← integral_sub hI1 hI2]
    congr 1; funext θ; ring
  set T : ι → ℝ := fun i => ∫ θ in Ioi 1, posTail (ψ i) X θ * (1 - 1 / θ) with hTdef
  have hsplit : (∫ θ in Ioi 1, F θ * (1 - 1 / θ)) = ∑ i, a i * T i := by
    have hpt : (fun θ => F θ * (1 - 1 / θ))
        = fun θ => ∑ i, a i * (posTail (ψ i) X θ * (1 - 1 / θ)) := by
      funext θ
      rw [hF, hΦ, Cvs.L2a.PositionTailSpanAdapters.posTail_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hpt, integral_finsetSum _ fun i _ =>
      (integrableOn_posTail_mul (ψ i) (hψo i) hw).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hcs := Cvs.L2a.SpanPoleMellinFromRungs.abs_sum_le_mass a T (fun i => K * √(m i) / c) m hM hT
  have hms : Cvs.L2a.SpanPoleMellinFromRungs.massSum (fun i => K * √(m i) / c) m
      = (Fintype.card ι : ℝ) * (K ^ 2 / c ^ 2) := by
    unfold Cvs.L2a.SpanPoleMellinFromRungs.massSum
    have hterm : ∀ i, (K * √(m i) / c) ^ 2 / m i = K ^ 2 / c ^ 2 := fun i => by
      have hmi : 0 < m i := hM i
      rw [div_pow, mul_pow, sq_sqrt hmi.le]
      field_simp
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hms] at hcs
  set S := ∑ i, a i ^ 2 * m i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have hK0 : 0 ≤ (Fintype.card ι : ℝ) * (K ^ 2 / c ^ 2) := by positivity
  have hsq : (∑ i, a i * T i) ^ 2 ≤ S * ((Fintype.card ι : ℝ) * (K ^ 2 / c ^ 2)) := by
    calc (∑ i, a i * T i) ^ 2 = |∑ i, a i * T i| ^ 2 := (sq_abs _).symm
      _ ≤ (√S * √((Fintype.card ι : ℝ) * (K ^ 2 / c ^ 2))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = S * ((Fintype.card ι : ℝ) * (K ^ 2 / c ^ 2)) := by
          rw [mul_pow, sq_sqrt hS0, sq_sqrt hK0]
  have hSN : S ≤ N / κF := by rw [le_div_iff₀ hκ]; linarith
  have hbound : (∑ i, a i * T i) ^ 2 ≤ N / κF * ((Fintype.card ι : ℝ) * (K ^ 2 / c ^ 2)) :=
    hsq.trans (mul_le_mul_of_nonneg_right hSN hK0)
  have hkey := Cvs.L2a.TiltFrameFreePole.neg_sq_sub_le (∫ θ in Ioi 1, F θ) (∫ θ in Ioi 1, F θ / θ)
  rw [hdiff, hsplit] at hkey
  have heq : K ^ 2 * Fintype.card ι / (2 * c ^ 2 * κF) * N
      = N / κF * ((Fintype.card ι : ℝ) * (K ^ 2 / c ^ 2)) / 2 := by
    field_simp
  rw [heq]
  linarith

open Cvs.L2a.PositionTruncatedTail Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity in
/-- **The pole on the rung span with no σ cut**: for `c ≥ 80`, `0 ≤ χᵢ ≤ c² + c/2`, `≤ c/4 + 1` rungs and the
frame floor, `−(tiltK(23/24, c)²(c/4 + 1)/(2c²κF))∫F² ≤ 2(∫F)(∫F/θ)`, `F = posTail Φ X`. -/
theorem pole_span {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    {X κF : ℝ} (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ1 : ∀ i, χ i ≤ c ^ 2 + c / 2)
    (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    -((tiltK (23 / 24) c ^ 2 * (c / 4 + 1) / (2 * c ^ 2 * κF))
        * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ)
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ / θ) := by
  have hc0 : 0 < c := by linarith
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have h := pole_of_tilt a hc0 hψc hM hκ
    (fun i => tilt_le_rung (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχ1 i) hX) hFF
  have hN : 0 ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hcmp : tiltK (23 / 24) c ^ 2 * Fintype.card ι / (2 * c ^ 2 * κF)
      ≤ tiltK (23 / 24) c ^ 2 * (c / 4 + 1) / (2 * c ^ 2 * κF) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (sq_nonneg _)) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hcmp hN]

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.LogPositionIdentity Cvs.L2a.CutWeightResidual Cvs.L2a.SpectralMassLevelLeak Cvs.Prolate.Gram.RungGramFloorAtInfinity in
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol) in
open Cvs.WeilForm.SelfConvolutionCosine (specDensity) in
/-- **L2a on the full tail of the rung span with no σ cut**: Cvs.L2a.PositionTailFullTail for `c ≥ 80` and `0 ≤ χᵢ ≤ c² + c/2`, the pole
term `tiltK(23/24, c)²(c/4 + 1)/(2c²κF)` from `pole_span`. -/
theorem L2a_span_fulltail {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    (ω ε : ℝ → ℝ) {X T η k₁ t2 εc C κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ1 : ∀ i, χ i ≤ c ^ 2 + c / 2)
    (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hT : 2 ≤ T)
    (hlow : ∫ t in {t : ℝ | |t| < T}, specDensity (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) t
      ≤ η * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hk₁ : 1 ≤ k₁) (hk₁X : k₁ ≤ X) (hεm : Measurable ε)
    (hε : ∀ k ∈ Icc k₁ X,
      specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X - posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k)
          (k * T)
        ≤ ε k * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
    (hω : ContinuousOn ω (Icc 1 X)) (ht2' : t2 ≤ 2) (hω0 : ∀ θ, 1 ≤ θ → 0 ≤ ω θ)
    (hωle : ∀ θ, 1 ≤ θ → ω θ ≤ Real.log θ) (hωeq : ∀ θ, t2 ≤ θ → ω θ = Real.log θ) (hεc : εc ≤ 1)
    (hNS : cutNS ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X
      ≤ εc * (-(cutW ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X))
        + C * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    (archSymbol T - 114 / T - (archSymbol T - archSymbol 0) * η
        - (Real.log k₁ + ∫ k in k₁..X, min 1 (2 * √(ε k)) / k) - C
        - tiltK (23 / 24) c ^ 2 * (c / 4 + 1) / (2 * c ^ 2 * κF))
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hΦ := Cvs.L2a.PositionTailSpanAdapters.contDiffOn_span a hg hg₁ hg₂c hang X
  have hPR : ∀ k : ℕ, IsPrimePow k → (k : ℝ) ≤ X → k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex ⌊X⌋₊ ⌊X⌋₊ :=
    fun k hk hkX => Cvs.L2a.PositionTailSpanAdapters.mem_primePowIndex_floor hk hkX
  have hloc := hloc_of_levels (fun ξ => ∑ i, a i * psi c (g i) ξ) ε hX1 hΦ hT hk₁ hk₁X hεm hε
  have hpole := pole_span a hg hg₁ hg₂c hang hX hc hχ0 hχ1 hM hJ hκ hFF
  exact Cvs.L2a.LogPositionCut.L2a_logPos_cut _ ω ⌊X⌋₊ ⌊X⌋₊ hX1 hΦ hPR hT hlow hloc hω ht2' hω0 hωle hωeq hεc
    hNS hpole

end Cvs.L2a.FullTailTiltedPole
