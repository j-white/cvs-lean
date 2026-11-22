import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutEstimateFrameFloor
import Cvs.L2a.CutPointCountForm
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.EdgeCountSSums
import Cvs.L2a.FarPartDirichletSplit
import Cvs.L2a.FirstStepRemainderCount
import Cvs.L2a.PerLevelFarLeak
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanFromLowMass
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeBesselCount
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.EdgeGreenIdentity
import Cvs.Prolate.Mellin.EdgeRemainderClosedForm
import Cvs.Prolate.Mellin.FarPartLevelBound
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
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
# THEOREM LOW′: the low mass of the rung span below `c/K0`

`posTail Φ X = (posTail Φ X − posTail Φ 2) + Φ·1_(1,2]`: Cvs.L2a.PerLevelFarLeak at level 2 bounds the far part by `P·Far/(πK0)`, and the
edge identity (Cvs.Prolate.Mellin.EdgeGreenIdentity), Lemma E (Cvs.Prolate.Mellin.EdgeRemainderClosedForm) and the S-sums (Cvs.L2a.EdgeCountSSums) bound the edge part by `P(√Wb + √ℛ)²/(πK0)`, so
`low ≤ η_P P` with `η_P = (√Far + √Wb + √ℛ)²/(πK0)`; under the frame floor this is `PositionTailFullTail`'s `hlow` with `η = η_P/κ_F`.
-/

namespace Cvs.L2a.RungSpanLowMass

open MeasureTheory Real Set Cvs.L2a.TailLogScaleTest Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.SpectralMassLevelLeak Cvs.L2a.CutPointCountForm Cvs.L2a.FirstStepRemainderCount Cvs.L2a.CutEstimateFrameFloor Cvs.Prolate.Mellin.FarPartLevelBound Cvs.L2a.PerLevelFarLeak Cvs.Prolate.Mellin.EdgeGreenIdentity Cvs.Prolate.Mellin.EdgeRemainderClosedForm Cvs.L2a.EdgeCountSSums
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)
open scoped FourierTransform

/-- `r = 1/K0² + 1/(4c²)`: `(t² + ¼)/c² < r` for `|t| < c/K0`. -/
noncomputable def rLow (c K0 : ℝ) : ℝ := 1 / K0 ^ 2 + 1 / (4 * c ^ 2)

/-- The far constant `(3/2)(J/c)C̄(c, r_f)²`, `r_f = 1/(4K0²) + 1/(16c²)`. -/
noncomputable def Far (c K0 J : ℝ) : ℝ := 3 / 2 * (J / c) * Cbar c (1 / (4 * K0 ^ 2) + 1 / (16 * c ^ 2)) ^ 2

/-- The edge boundary constant `(J/c)ω₂²`. -/
noncomputable def Wb (c K0 J : ℝ) : ℝ := J / c * omega2Sq c (rLow c K0)

/-- `η_P = (√Far + √Wb + √ℛ)²/(πK0)`. -/
noncomputable def etaP (c K0 J : ℝ) : ℝ :=
  (√(Far c K0 J) + √(Wb c K0 J) + √(Rcal c (rLow c K0) J)) ^ 2 / (π * K0)

/-- `rLow c K0 · c² = (c/K0)² + ¼`. -/
theorem rLow_mul_sq {c K0 : ℝ} (hc : c ≠ 0) (hK0 : K0 ≠ 0) : rLow c K0 * c ^ 2 = (c / K0) ^ 2 + 1 / 4 := by
  unfold rLow; field_simp

/-- **The edge rung bound**: `specMass (posTail ψ 2)(c/K0) ≤ (c/K0)/π · m(ω₂/c + √LE)²`, `m = ∫₁^X ψ²`,
`LE` Lemma E's bound at `r = rLow c K0` and `s = (c² − χ)/c`. -/
theorem specMass_edge_rung_le {g g₁ g₂ : ℝ → ℝ} {c χ X K0 : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hσ : 5 * c ≤ c ^ 2 - χ) (hX : 2 ≤ X) (hK0 : 0 < K0) (hr : rLow c K0 < 1) :
    specMass (posTail (psi c g) 2) (c / K0)
      ≤ c / K0 / π * ((∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2)
        * (√(omega2Sq c (rLow c K0)) / c + √(lemmaEBound c (rLow c K0) ((c ^ 2 - χ) / c))) ^ 2) := by
  obtain ⟨-, -, hψc, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  have hc0 : 0 < c := by linarith
  have hχ : χ < c ^ 2 := by nlinarith
  have hm0 : 0 ≤ ∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun ξ _ => sq_nonneg _
  have hrc := rLow_mul_sq hc0.ne' hK0.ne'
  have hψ2 : ContinuousOn (psi c g) (Icc 1 2) := hψc.continuousOn
  have hlev : ∀ t, |t| < c / K0 →
      ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (logScale (posTail (psi c g) 2))) (t / (2 * π))‖ ^ 2
        ≤ (√(∫ ξ in (1 : ℝ)..X, psi c g ξ ^ 2)
          * (√(omega2Sq c (rLow c K0)) / c + √(lemmaEBound c (rLow c K0) ((c ^ 2 - χ) / c)))) ^ 2 := by
    intro t ht
    have hw : t ^ 2 + 1 / 4 ≤ rLow c K0 * c ^ 2 := by
      rw [hrc]
      have : t ^ 2 ≤ (c / K0) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) ht.le 2
      linarith
    have e1 := fourier_eq (posTail (psi c g) 2) (fun θ hθ => posTail_zero _ _ hθ) t
      (integrableOn_posTail_mul _ hψ2 (Cvs.L2a.FarPartDirichletSplit.continuousOn_ky t 2))
      (integrableOn_posTail_mul _ hψ2 (Cvs.L2a.FarPartDirichletSplit.continuousOn_kys t 2))
    have e2 := Cvs.L2a.FarPartDirichletSplit.mellin_posTail_eq (psi c g) (by norm_num : (1 : ℝ) ≤ 2) hψ2 t
    have hd1 : Cvs.L2a.FarPartDirichletSplit.dch 1 t = 1 := by
      simp [Cvs.L2a.FarPartDirichletSplit.dch]
    have hI2 : Cvs.L2a.FarPartDirichletSplit.mellinI (psi c g) 2 2 t = 0 := by
      simp [Cvs.L2a.FarPartDirichletSplit.mellinI]
    have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
    rw [hfl, show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)] at e2
    simp only [Nat.cast_one, Nat.cast_ofNat, hd1, hI2, one_mul, mul_zero, add_zero] at e2
    rw [e1, e2]
    have hN := norm_mellinI_one_two_le hg hg₁ hg₂c hang hc hχ0 hχ hX hr.le hw
    have hE := integral_norm_rhoEdge_sq_le (t := t) (by linarith) hχ0 hσ hr hw
    refine pow_le_pow_left₀ (norm_nonneg _) (hN.trans ?_) 2
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.sqrt_le_sqrt hE)) (Real.sqrt_nonneg _)
  refine (Cvs.L2a.FarPartDirichletSplit.specMass_le_sup_fourier _ (by positivity) hlev).trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hm0]

/-- `ℓ²` Minkowski against a constant: `Σᵢ(u + √vᵢ)² ≤ (√J·u + √(Σᵢ vᵢ))²`, `J = #ι`. -/
theorem sum_add_sqrt_sq_le {ι : Type*} [Fintype ι] {u : ℝ} (v : ι → ℝ) (hu : 0 ≤ u) (hv : ∀ i, 0 ≤ v i) :
    ∑ i, (u + √(v i)) ^ 2 ≤ (√(Fintype.card ι : ℝ) * u + √(∑ i, v i)) ^ 2 := by
  have hS : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ => hv i
  have hsq : ∑ i, √(v i) ^ 2 = ∑ i, v i := Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hv i)
  have hCS : (∑ i, √(v i)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, v i := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => √(v i))
    rw [hsq, Finset.card_univ] at this
    exact this
  have hsum : ∑ i, √(v i) ≤ √(Fintype.card ι : ℝ) * √(∑ i, v i) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hCS)
  have expand : ∑ i, (u + √(v i)) ^ 2 = (Fintype.card ι : ℝ) * u ^ 2 + 2 * u * ∑ i, √(v i) + ∑ i, v i := by
    rw [← hsq, Finset.mul_sum]
    simp only [add_sq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hJ : √(Fintype.card ι : ℝ) ^ 2 = Fintype.card ι := Real.sq_sqrt (Nat.cast_nonneg _)
  have hS2 : √(∑ i, v i) ^ 2 = ∑ i, v i := Real.sq_sqrt hS
  rw [expand]
  have h2 : 2 * u * ∑ i, √(v i) ≤ 2 * u * (√(Fintype.card ι : ℝ) * √(∑ i, v i)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  nlinarith [hJ, hS2]

variable {ι : Type} [Fintype ι]

/-- **The edge part on the span**: `specMass (posTail Φ 2)(c/K0) ≤ P·(√Wb + √ℛ)²/(πK0)`, `P = Σ aᵢ²∫₁^X ψᵢ²`. -/
theorem specMass_edge_span_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X K0 : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hK0 : 0 < K0)
    (hr : rLow c K0 < 1) :
    specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2) (c / K0)
      ≤ (∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
        * ((√(Wb c K0 (Fintype.card ι)) + √(Rcal c (rLow c K0) (Fintype.card ι))) ^ 2 / (π * K0)) := by
  have hc0 : 0 < c := by linarith
  have hχ : ∀ i, χ i < c ^ 2 := fun i => by nlinarith [hσ i]
  have hr0 : 0 ≤ rLow c K0 := by unfold rLow; positivity
  have hrc := rLow_mul_sq hc0.ne' hK0.ne'
  have e : posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2 = fun θ => ∑ i, a i * posTail (psi c (g i)) 2 θ := by
    funext θ; exact Cvs.L2a.PositionTailSpanAdapters.posTail_sum _ _ _ _ _
  have hΦ : ∀ i, ContDiff ℝ 1 (psi c (g i)) := fun i =>
    Cvs.L2a.RungSpanFromLowMass.contDiff_psi (hg i) (hg₁ i) (hg₂c i) (hang i)
  have had := fun i => Cvs.L2a.PositionTailAdmissible.admissible_posTail (X := 2) (by norm_num) (hΦ i).contDiffOn
  have hspan := Cvs.L2a.FarPartDirichletSplit.specMass_span_le a (fun i => ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
    (fun i => posTail (psi c (g i)) 2) hM (fun i => (had i).1) (fun i => (had i).2.1) (c / K0)
  rw [e]
  have hLE0 : ∀ i, 0 ≤ lemmaEBound c (rLow c K0) ((c ^ 2 - χ i) / c) := fun i => by
    have h := integral_norm_rhoEdge_sq_le (t := 0) (by linarith) (hχ0 i) (hσ i) hr
      (by rw [hrc]; nlinarith [sq_nonneg (c / K0)])
    exact le_trans (intervalIntegral.integral_nonneg (by norm_num) fun ξ _ => sq_nonneg _) h
  have hu0 : 0 ≤ √(omega2Sq c (rLow c K0)) / c := by positivity
  have hrung : ∀ i, specMass (posTail (psi c (g i)) 2) (c / K0) / (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ c / K0 / π * (√(omega2Sq c (rLow c K0)) / c + √(lemmaEBound c (rLow c K0) ((c ^ 2 - χ i) / c))) ^ 2 :=
    fun i => by
    have h := specMass_edge_rung_le (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hσ i) hX hK0 hr
    rw [div_le_iff₀ (hM i)]
    exact h.trans (le_of_eq (by ring))
  have hS0 : 0 ≤ ∑ i, lemmaEBound c (rLow c K0) ((c ^ 2 - χ i) / c) := Finset.sum_nonneg fun i _ => hLE0 i
  have hsum : ∑ i, specMass (posTail (psi c (g i)) 2) (c / K0) / (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ c / K0 / π * (√(Fintype.card ι : ℝ) * (√(omega2Sq c (rLow c K0)) / c)
        + √(∑ i, lemmaEBound c (rLow c K0) ((c ^ 2 - χ i) / c))) ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => hrung i).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_add_sqrt_sq_le _ hu0 hLE0) (by positivity)
  have hR := Cvs.L2a.EdgeCountSSums.mul_sum_lemmaEBound_le_Rcal hg hg₁ hg₂c hang hc hχ0 hσ hχinj
    (fun i => Cvs.Prolate.EdgeBesselCount.psi_one_ne_zero_of_mass_pos (hg i) (hg₁ i) (hg₂c i) (hang i) (hχ i)
      (by linarith) (hM i)) hr0 hr
  have hω0 : 0 ≤ omega2Sq c (rLow c K0) := by unfold omega2Sq; positivity
  have hW : √(Wb c K0 (Fintype.card ι))
      = √c * (√(Fintype.card ι : ℝ) * (√(omega2Sq c (rLow c K0)) / c)) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ √c * (√(Fintype.card ι : ℝ) * (√(omega2Sq c (rLow c K0)) / c)))]
    congr 1
    unfold Wb
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hc0.le, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hω0]
    field_simp
  have hcS : √c * √(∑ i, lemmaEBound c (rLow c K0) ((c ^ 2 - χ i) / c))
      ≤ √(Rcal c (rLow c K0) (Fintype.card ι)) := by
    rw [← Real.sqrt_mul hc0.le, Finset.mul_sum]
    exact Real.sqrt_le_sqrt (by rw [← Finset.mul_sum]; exact hR)
  have hfin : c / K0 / π * (√(Fintype.card ι : ℝ) * (√(omega2Sq c (rLow c K0)) / c)
        + √(∑ i, lemmaEBound c (rLow c K0) ((c ^ 2 - χ i) / c))) ^ 2
      ≤ (√(Wb c K0 (Fintype.card ι)) + √(Rcal c (rLow c K0) (Fintype.card ι))) ^ 2 / (π * K0) := by
    set x := √(Fintype.card ι : ℝ) * (√(omega2Sq c (rLow c K0)) / c)
    set y := √(∑ i, lemmaEBound c (rLow c K0) ((c ^ 2 - χ i) / c))
    have e2 : c / K0 / π * (x + y) ^ 2 = (√c * x + √c * y) ^ 2 / (π * K0) := by
      rw [show (√c * x + √c * y) ^ 2 = √c ^ 2 * (x + y) ^ 2 by ring, Real.sq_sqrt hc0.le]
      field_simp
    rw [e2, hW]
    have hx : 0 ≤ √c * x := by positivity
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (add_nonneg hx (by positivity))
      (add_le_add le_rfl hcS) 2) (by positivity)
  have hP0 : 0 ≤ ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  exact hspan.trans (mul_le_mul_of_nonneg_left (hsum.trans hfin) hP0)

/-- **The far part on the span**: Cvs.L2a.PerLevelFarLeak at level `k = 2`, `T = c/(2K0)`, `r_f = 1/(4K0²) + 1/(16c²)`, summed over
the rungs: `specMass (posTail Φ X − posTail Φ 2)(c/K0) ≤ P·Far/(πK0)`. -/
theorem specMass_far_span_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X K0 : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i, χ i < c ^ 2)
    (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hK0 : 0 < K0)
    (hrf : 1 / (4 * K0 ^ 2) + 1 / (16 * c ^ 2) < 1) :
    specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X - posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2)
        (c / K0)
      ≤ (∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) * (Far c K0 (Fintype.card ι) / (π * K0)) := by
  have hc0 : 0 < c := by linarith
  set rf := 1 / (4 * K0 ^ 2) + 1 / (16 * c ^ 2) with hrfd
  set G : ι → ℝ → ℝ := fun i => posTail (psi c (g i)) X - posTail (psi c (g i)) 2 with hG
  have e : posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X - posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2
      = fun θ => ∑ i, a i * G i θ := by
    funext θ
    simp only [Pi.sub_apply, hG]
    rw [Cvs.L2a.PositionTailSpanAdapters.posTail_sum, Cvs.L2a.PositionTailSpanAdapters.posTail_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hΦ : ∀ i, ContDiff ℝ 1 (psi c (g i)) := fun i =>
    Cvs.L2a.RungSpanFromLowMass.contDiff_psi (hg i) (hg₁ i) (hg₂c i) (hang i)
  have hadX := fun i => Cvs.L2a.PositionTailAdmissible.admissible_posTail (by linarith : (1 : ℝ) ≤ X) (hΦ i).contDiffOn
  have had2 := fun i => Cvs.L2a.PositionTailAdmissible.admissible_posTail (X := 2) (by norm_num) (hΦ i).contDiffOn
  have h2 : ∀ i, MemLp (logScale (G i)) 2 volume := fun i => by
    simp only [hG]; rw [logScale_sub]; exact (hadX i).1.sub (had2 i).1
  have h1 : ∀ i, Integrable (logScale (G i)) volume := fun i => by
    simp only [hG]; rw [logScale_sub]; exact (hadX i).2.1.sub (had2 i).2.1
  have hspan := Cvs.L2a.FarPartDirichletSplit.specMass_span_le a (fun i => ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) G hM h2
    h1 (c / K0)
  rw [e]
  have hTr : (c / (2 * K0)) ^ 2 + 1 / 16 ≤ rf * c ^ 2 := le_of_eq (by rw [hrfd]; field_simp; ring)
  have hk : 2 * (c / (2 * K0)) = c / K0 := by field_simp
  have hrung : ∀ i, specMass (G i) (c / K0) / (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ 3 / 2 * Cbar c rf ^ 2 / (π * c * K0) := fun i => by
    have h := specMass_far_rung_le (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχ i) (le_refl 2) hX
      (by positivity) hTr hrf
    rw [hk] at h
    rw [div_le_iff₀ (hM i)]
    refine h.trans (le_of_eq ?_)
    field_simp
    ring
  have hsum : ∑ i, specMass (G i) (c / K0) / (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ Fintype.card ι * (3 / 2 * Cbar c rf ^ 2 / (π * c * K0)) := by
    calc _ ≤ ∑ _i : ι, 3 / 2 * Cbar c rf ^ 2 / (π * c * K0) := Finset.sum_le_sum fun i _ => hrung i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP0 : 0 ≤ ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  refine hspan.trans ((mul_le_mul_of_nonneg_left hsum hP0).trans (le_of_eq ?_))
  unfold Far
  rw [← hrfd]
  field_simp

/-- **THEOREM LOW′**: `specMass (posTail Φ X)(c/K0) ≤ η_P·P`, `η_P = etaP c K0 J`, `P = Σ aᵢ²∫₁^X ψᵢ²`. -/
theorem low_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X K0 : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hK0 : 0 < K0)
    (hr : rLow c K0 < 1) :
    specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X) (c / K0)
      ≤ etaP c K0 (Fintype.card ι) * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hχ : ∀ i, χ i < c ^ 2 := fun i => by nlinarith [hσ i]
  have hΦ := Cvs.L2a.PositionTailSpanAdapters.contDiffOn_span a hg hg₁ hg₂c hang
  have hadX := Cvs.L2a.PositionTailAdmissible.admissible_posTail (by linarith : (1 : ℝ) ≤ X) (hΦ X)
  have had2 := Cvs.L2a.PositionTailAdmissible.admissible_posTail (by norm_num : (1 : ℝ) ≤ 2) (hΦ 2)
  have hsplit := sqrt_specMass_add_le
    (G := posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X - posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2)
    (H := posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) 2)
    (by rw [logScale_sub]; exact hadX.1.sub had2.1) (by rw [logScale_sub]; exact hadX.2.1.sub had2.2.1)
    had2.1 had2.2.1 (c / K0)
  rw [sub_add_cancel] at hsplit
  have hrf : 1 / (4 * K0 ^ 2) + 1 / (16 * c ^ 2) < 1 := by
    have : 1 / (4 * K0 ^ 2) + 1 / (16 * c ^ 2) = rLow c K0 / 4 := by unfold rLow; field_simp; ring
    rw [this]
    have : 0 ≤ rLow c K0 := by unfold rLow; positivity
    linarith
  have hF := specMass_far_span_le a hg hg₁ hg₂c hang hX hc hχ0 hχ hM hK0 hrf
  have hE := specMass_edge_span_le a hg hg₁ hg₂c hang hX hc hχ0 hσ hχinj hM hK0 hr
  set P := ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 with hPd
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have hπK : 0 < π * K0 := by positivity
  set s := √(π * K0) with hsd
  have hs0 : 0 < s := Real.sqrt_pos.mpr hπK
  have hs2 : s ^ 2 = π * K0 := Real.sq_sqrt hπK.le
  have h1 := (Real.sqrt_le_sqrt hF).trans (le_of_eq (by
    rw [Real.sqrt_mul hP0, Real.sqrt_div' _ hπK.le]))
  have h2 := (Real.sqrt_le_sqrt hE).trans (le_of_eq (by
    rw [Real.sqrt_mul hP0, Real.sqrt_div' _ hπK.le, Real.sqrt_sq (by positivity)]))
  have hsum := hsplit.trans (add_le_add h1 h2)
  have hm0 := specMass_nonneg (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X) (c / K0)
  calc specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X) (c / K0)
      = √(specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X) (c / K0)) ^ 2 := (Real.sq_sqrt hm0).symm
    _ ≤ (√P * (√(Far c K0 (Fintype.card ι)) / s)
          + √P * ((√(Wb c K0 (Fintype.card ι)) + √(Rcal c (rLow c K0) (Fintype.card ι))) / s)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsum 2
    _ = √P ^ 2 * (√(Far c K0 (Fintype.card ι)) + √(Wb c K0 (Fintype.card ι))
          + √(Rcal c (rLow c K0) (Fintype.card ι))) ^ 2 / s ^ 2 := by
        field_simp
        ring
    _ = etaP c K0 (Fintype.card ι) * P := by
        rw [Real.sq_sqrt hP0, hs2]
        unfold etaP
        ring

/-- **`hlow` under the frame floor**: `κ_F P ≤ N` turns LOW′ into `PositionTailFullTail`'s `hlow` with `η = η_P/κ_F`. -/
theorem hlow_of_FF {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X K0 κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2) (hK0 : 0 < K0)
    (hr : rLow c K0 < 1) (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    ∫ t in {t : ℝ | |t| < c / K0}, specDensity (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) t
      ≤ etaP c K0 (Fintype.card ι) / κF * ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 := by
  have h := low_le a hg hg₁ hg₂c hang hX hc hχ0 hσ hχinj hM hK0 hr
  set N := ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2 with hN
  set P := ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2 with hPd
  have hP : P ≤ N / κF := by rw [le_div_iff₀ hκ, mul_comm]; exact hFF
  have he : 0 ≤ etaP c K0 (Fintype.card ι) := by unfold etaP; positivity
  calc _ = specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X) (c / K0) := rfl
    _ ≤ etaP c K0 (Fintype.card ι) * P := h
    _ ≤ etaP c K0 (Fintype.card ι) * (N / κF) := mul_le_mul_of_nonneg_left hP he
    _ = etaP c K0 (Fintype.card ι) / κF * N := by ring

/-- **The full-tail L2a under the frame floor**: `PerLevelFarLeak`'s loc form with `T = c/K0`, `hlow` from LOW′
(`η = η_P/κ_F`) and `hNS` from Cvs.L2a.CutEstimateFrameFloor (`ω = nsRamp`, `t₁ = 5/4`, `κ_P = κ_F`). -/
theorem L2a_span_fulltail_ff {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {X K0 κF : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hX : 2 ≤ X) (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i)
    (hχinj : Function.Injective χ) (hM : ∀ i, 0 < ∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1) (hr : rLow c K0 < 1) (hT : 2 ≤ c / K0) (hκ : 0 < κF)
    (hFF : κF * ∑ i, a i ^ 2 * (∫ ξ in (1 : ℝ)..X, psi c (g i) ξ ^ 2)
      ≤ ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2) :
    (archSymbol (c / K0) - 114 / (c / K0) - (archSymbol (c / K0) - archSymbol 0) * (etaP c K0 (Fintype.card ι) / κF)
        - (Real.log 2 + 4 * √(ALoc (Fintype.card ι) c (((c / K0) ^ 2 + 1 / 16) / c ^ 2) (c / K0) κF / 2))
        - 6 * (Fintype.card ι : ℝ) / c * (lamCount nsRamp (5 / 4) X + kapCount nsRamp nsRamp' (5 / 4) X) / κF
        - 49 * (c / 4 + 1) / (2 * c ^ 2 * κF))
        * (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊X⌋₊ ⌊X⌋₊
          (logScale (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) X)) := by
  have hc0 : 0 < c := by linarith
  have hK0 : 0 < K0 := by
    by_contra h
    push Not at h
    have : c / K0 ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc0.le h
    linarith
  have hχc : ∀ i, χ i < c ^ 2 := fun i => by nlinarith [hσ i]
  have hlow := hlow_of_FF a hg hg₁ hg₂c hang hX hc hχ0 hσ hχinj hM hK0 hr hκ hFF
  have hωd : ∀ θ ∈ Icc (1 : ℝ) X, HasDerivAt nsRamp (nsRamp' θ) θ := fun θ hθ =>
    hasDerivAt_nsRamp (by linarith [hθ.1])
  have hω₁ : ContinuousOn nsRamp' (Icc 1 X) :=
    continuousOn_nsRamp'.mono fun θ hθ => mem_Ioi.mpr (by linarith [hθ.1])
  have hω : ContinuousOn nsRamp (Icc 1 X) := fun θ hθ => (hωd θ hθ).continuousAt.continuousWithinAt
  have hNS := NS_of_floor a hg hg₁ hg₂c hang hc hχ0 hχc hX hM (t₁ := 5 / 4) (by norm_num)
    (fun θ hθ => nsRamp_of_le hθ.2) hωd hω₁ hκ hFF
  have hTr : (c / K0) ^ 2 + 1 / 16 ≤ ((c / K0) ^ 2 + 1 / 16) / c ^ 2 * c ^ 2 :=
    le_of_eq (by field_simp)
  have hr' : ((c / K0) ^ 2 + 1 / 16) / c ^ 2 < 1 := by
    have e : ((c / K0) ^ 2 + 1 / 16) / c ^ 2 = 1 / K0 ^ 2 + 1 / (16 * c ^ 2) := by field_simp
    have h4 : 1 / (16 * c ^ 2) ≤ 1 / (4 * c ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg c])
    rw [e]
    unfold rLow at hr
    linarith
  exact L2a_span_fulltail_loc a nsRamp hg hg₁ hg₂c hang hX hc hχ0 hσ hM hJ hκ hFF hT hTr hr' hlow hω
    (t2 := 3 / 2) (by norm_num) (fun θ hθ => nsRamp_nonneg hθ) (fun θ hθ => nsRamp_le_log hθ)
    (fun θ hθ => nsRamp_of_ge hθ) (εc := 0) (by norm_num) hNS

end Cvs.L2a.RungSpanLowMass
