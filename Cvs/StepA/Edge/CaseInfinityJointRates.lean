import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.Route.Visibility.SpinePairingExteriorTransform
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.StepA.Edge.CorrectedPairingUSums
import Cvs.StepA.Edge.DeepJointShare
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FiniteTopIffFiniteBand
import Cvs.StepA.Edge.FiniteTopTieTerm
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.StepA.LowEigenvalueCountZeros
import Cvs.StepA.RestEnvelopeSmall
import Cvs.StepA.TopQuadruple
import Cvs.Upstream.ProjectionInterpolantSplit
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Xi.WindowTransformExterior
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge
import Cvs.Zeta.ZeroTailInverseSquare

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Case ∞ of hV: the joint rates from the transplant, the exterior data and the Bessel rate

With `Θ' = sup_ρ |δ_ρ|`, `δ_D = Θ'/2` and deep sets `D_x = deepSet δ_D H(x)` below a cutoff `H(x) ≍ x^{ε₂}`, the
joint residue's `U` sum off `D_x` is at most `3(T₂ + Bess(2K_p² + 4θ²‖V‖²) + 6‖V‖²A₃)` (caseinf-attack §6). The
named statements `SEPData`, `M1Prime`, `DbarTransplant`, `FreeInterp` and `LemmaC` give each piece a power rate,
and for a deep enough off-line `σ` they give `DeepJointShare`'s joint hypothesis on `NoTop` (caseinf-W Theorem 9 (A)).
-/

noncomputable section

open Real MeasureTheory Filter Set
open scoped InnerProductSpace ComplexConjugate
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.StepA.Edge.FiniteTopCorrectedClosing (USpan bPerp)
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.WindowCoshTransformDuality (coshT wR Transplant PointInterp)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet mem_deepSet)
open Cvs.StepA.Edge.TransplantAngleHighZeros (rect sbox ExtData)
open Cvs.StepA.Edge.DeepJointShare (Vσ wJoint angle)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.CaseInfinityJointRates
open Cvs.ZeroCounting

/-! ### The top depth -/

/-- `Θ' = sup_ρ |δ_ρ|`, the largest distance of a nontrivial zero from the critical line. -/
def topDepth : ℝ := ⨆ ρ : nonTrivialZeroSet, |Cvs.GaussKernel.del ρ|

/-- `|δ_ρ|` is bounded above by `½`. -/
theorem bddAbove_abs_del : BddAbove (Set.range fun ρ : nonTrivialZeroSet => |Cvs.GaussKernel.del ρ|) :=
  ⟨1 / 2, by rintro _ ⟨ρ, rfl⟩; exact Cvs.GaussKernel.del_bdd ρ⟩

/-- `|δ_ρ| ≤ Θ'`. -/
theorem abs_del_le_topDepth (ρ : nonTrivialZeroSet) : |Cvs.GaussKernel.del ρ| ≤ topDepth :=
  le_ciSup bddAbove_abs_del ρ

/-- Without RH some zero has `δ_σ ≠ 0`. -/
theorem exists_del_ne_zero (h : ¬ RiemannHypothesis) : ∃ σ : nonTrivialZeroSet, Cvs.GaussKernel.del σ ≠ 0 := by
  obtain ⟨ρ, hρ⟩ := Cvs.StepA.TopQuadruple.exists_offLine_of_not_RH h
  exact ⟨ρ, Cvs.GaussKernel.del_ne_zero_iff.2 hρ⟩

/-- Without RH, `Θ' > 0`. -/
theorem topDepth_pos (h : ¬ RiemannHypothesis) : 0 < topDepth := by
  obtain ⟨σ, hσ⟩ := exists_del_ne_zero h
  exact (abs_pos.2 hσ).trans_le (abs_del_le_topDepth σ)

/-- Without RH, `Θ' ≤ ½`. -/
theorem topDepth_le_half (h : ¬ RiemannHypothesis) : topDepth ≤ 1 / 2 := by
  obtain ⟨σ, -⟩ := exists_del_ne_zero h
  have : Nonempty nonTrivialZeroSet := ⟨σ⟩
  exact ciSup_le Cvs.GaussKernel.del_bdd

/-- Without RH, every `η > 0` has a zero with `|δ_σ| > Θ' − η`. -/
theorem exists_abs_del_gt (h : ¬ RiemannHypothesis) {η : ℝ} (hη : 0 < η) :
    ∃ σ : nonTrivialZeroSet, topDepth - η < |Cvs.GaussKernel.del σ| := by
  obtain ⟨σ, -⟩ := exists_del_ne_zero h
  have : Nonempty nonTrivialZeroSet := ⟨σ⟩
  have hlt : topDepth - η < topDepth := by linarith
  exact exists_lt_of_lt_ciSup hlt

/-! ### The joint residue at one `x` -/

set_option synthInstance.maxHeartbeats 400000

/-- `m_ρ⟪u, U_ρ⟫²` is summable for `u` in the deep span. -/
theorem summable_inner_sq_of_mem_USpan {x : ℕ} (hx0 : (0 : ℝ) < x) {D : Finset nonTrivialZeroSet} {u : Dom x}
    (hu : u ∈ USpan hx0 D) :
    Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪u, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, -, rfl⟩ := hy
    simp_rw [Cvs.StepA.Edge.CorrectedPairingUSums.inner_ueVec_ueVec]
    exact Cvs.StepA.Edge.DeepSetZeroSums.summable_mul_ueUe_sq r (Real.log_natCast_nonneg x)
  | zero => simp
  | add y z _ _ hy hz =>
    refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (mult_nonneg ρ) (sq_nonneg _)) (fun ρ => ?_)
      ((hy.add hz).mul_left 2)
    rw [inner_add_left (𝕜 := ℝ) y z]
    have hm := mult_nonneg ρ
    nlinarith [mul_nonneg hm (sq_nonneg (⟪y, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ
      - ⟪z, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ))]
  | smul c y _ hy =>
    refine (hy.mul_left (c ^ 2)).congr fun ρ => ?_
    rw [real_inner_smul_left]
    ring

set_option maxHeartbeats 1000000 in
/-- **The joint residue's `U` sum off `D`** (caseinf-attack §6): with `θ_x(D) ≤ θ ≤ ½`, an `R₁` Bessel bound `Bess`,
`‖P_{R₁}V_σ‖ ≤ K_p`, and `Σ_{ρ ∉ D} m_ρ‖P_{U_D}U_ρ‖² ≤ A₃` summable, the family `m_ρ⟪w, U_ρ⟫²` is summable and its
part off `D` is at most `3(Σ_{ρ ∉ D} m_ρ⟪V_σ, U_ρ⟫² + Bess(2K_p² + 4θ²‖V_σ‖²) + 6‖V_σ‖²A₃)`. -/
theorem tsum_compl_wJoint_le {x : ℕ} (hx0 : (0 : ℝ) < x) (D : Finset nonTrivialZeroSet) (σ : nonTrivialZeroSet)
    {Bess Kp A₃ θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : angle hx0 D ≤ θ) (hθ2 : θ ≤ 1 / 2)
    (hB : ∀ r ∈ R1 x, (Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ ∑' ρ : nonTrivialZeroSet, mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 ≤ Bess * ‖r‖ ^ 2)
    (hBess : 0 ≤ Bess) (hK : ‖(R1 x).starProjection (Vσ hx0 σ)‖ ≤ Kp)
    (hA : (Summable fun ρ : ↥((D : Set nonTrivialZeroSet)ᶜ) =>
        mult ρ * ‖(USpan hx0 D).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2)
      ∧ ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ),
          mult ρ * ‖(USpan hx0 D).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2 ≤ A₃) :
    (Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪wJoint hx0 D σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ),
          mult ρ * ⟪wJoint hx0 D σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ 3 * (∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ),
                mult ρ * ⟪Vσ hx0 σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
            + Bess * (2 * Kp ^ 2 + 4 * θ ^ 2 * ‖Vσ hx0 σ‖ ^ 2) + 6 * ‖Vσ hx0 σ‖ ^ 2 * A₃) := by
  set V := Vσ hx0 σ
  set U : nonTrivialZeroSet → Dom x := fun ρ => ueVec hx0 (Cvs.ZeroCounting.zPoint ρ) with hUdef
  obtain ⟨r, hr, u, hu, hsplit⟩ := Cvs.Upstream.ProjectionInterpolantSplit.exists_split (R1 x) (USpan hx0 D) V
  have hw : wJoint hx0 D σ = V - (r + u) := by
    show V - (R1 x ⊔ USpan hx0 D).starProjection V = _
    rw [hsplit]
  have hinner : ∀ ρ, ⟪wJoint hx0 D σ, U ρ⟫_ℝ = ⟪V, U ρ⟫_ℝ - ⟪r, U ρ⟫_ℝ - ⟪u, U ρ⟫_ℝ := fun ρ => by
    rw [hw]
    have h1 : ⟪V - (r + u), U ρ⟫_ℝ = ⟪V, U ρ⟫_ℝ - ⟪r + u, U ρ⟫_ℝ := inner_sub_left (𝕜 := ℝ) V (r + u) (U ρ)
    have h2 : ⟪r + u, U ρ⟫_ℝ = ⟪r, U ρ⟫_ℝ + ⟪u, U ρ⟫_ℝ := inner_add_left (𝕜 := ℝ) r u (U ρ)
    rw [h1, h2]; ring
  have hθa : ∀ a ∈ R1 x, ‖(USpan hx0 D).starProjection a‖ ≤ θ * ‖a‖ := fun a ha =>
    (Cvs.StepA.Edge.DeepJointShare.norm_starProjection_le_angle hx0 D ha).trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg _))
  have hcoer := Cvs.Upstream.ProjectionInterpolantSplit.split_coercive (R1 x) (USpan hx0 D) hr hu hsplit hθ0 hθa
  have hleft := Cvs.Upstream.ProjectionInterpolantSplit.norm_split_left_le (R1 x) (USpan hx0 D) hr hu hsplit hθ0 hθa
  have hKp : 0 ≤ Kp := (norm_nonneg _).trans hK
  have hhalf : 1 / 2 * (‖r‖ ^ 2 + ‖u‖ ^ 2) ≤ (1 - θ) * (‖r‖ ^ 2 + ‖u‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hu2 : ‖u‖ ^ 2 ≤ 2 * ‖V‖ ^ 2 := by nlinarith [sq_nonneg ‖r‖]
  have hr2 : ‖r‖ ^ 2 ≤ 2 * ‖V‖ ^ 2 := by nlinarith [sq_nonneg ‖u‖]
  have hrK : ‖r‖ ^ 2 ≤ 2 * Kp ^ 2 + 4 * θ ^ 2 * ‖V‖ ^ 2 := by
    have h1 : ‖r‖ ≤ Kp + θ * ‖u‖ := hleft.trans (by linarith)
    have h2 : ‖r‖ ^ 2 ≤ (Kp + θ * ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (Kp - θ * ‖u‖), mul_le_mul_of_nonneg_left hu2 (sq_nonneg θ)]
  have hVr : ‖V - r‖ ^ 2 ≤ 6 * ‖V‖ ^ 2 := by
    have h1 : ‖V - r‖ ≤ ‖V‖ + ‖r‖ := norm_sub_le V r
    have h2 : ‖V - r‖ ^ 2 ≤ (‖V‖ + ‖r‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖V‖ - ‖r‖), hr2, h2]
  have hL := Real.log_natCast_nonneg x
  have hsa : Summable fun ρ => mult ρ * ⟪V, U ρ⟫_ℝ ^ 2 := by
    show Summable fun ρ : nonTrivialZeroSet => mult ρ
      * ⟪Cvs.Route.Visibility.ZeroPairingVector.pairVec hx0 (Cvs.ZeroCounting.zPoint σ), ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
    simp_rw [Cvs.StepA.Edge.FiniteTopTieTerm.inner_pairVec_ueVec]
    exact Cvs.StepA.Edge.DeepSetZeroSums.summable_mul_pairUe_sq σ hL
  have hsb : Summable fun ρ => mult ρ * ⟪r, U ρ⟫_ℝ ^ 2 := (hB r hr).1
  have hsc : Summable fun ρ => mult ρ * ⟪u, U ρ⟫_ℝ ^ 2 := summable_inner_sq_of_mem_USpan hx0 hu
  have hall := Cvs.Upstream.ProjectionInterpolantSplit.tsum_mul_sub_sub_sq_le (fun ρ => mult_nonneg ρ) hsa hsb hsc
  refine ⟨hall.1.congr fun ρ => ?_, ?_⟩
  · show _ = mult ρ * ⟪wJoint hx0 D σ, U ρ⟫_ℝ ^ 2
    rw [hinner]
  set S : Set nonTrivialZeroSet := ((D : Set nonTrivialZeroSet)ᶜ)
  have hsub := Cvs.Upstream.ProjectionInterpolantSplit.tsum_mul_sub_sub_sq_le (ι := ↥S) (m := fun ρ => mult ρ) (fun ρ => mult_nonneg _)
    (hsa.subtype _) (hsb.subtype _) (hsc.subtype _)
  have e : ∀ ρ : ↥S, mult ρ * ⟪wJoint hx0 D σ, U ρ⟫_ℝ ^ 2
      = mult ρ * (⟪V, U ρ⟫_ℝ - ⟪r, U ρ⟫_ℝ - ⟪u, U ρ⟫_ℝ) ^ 2 := fun ρ => by rw [hinner]
  rw [tsum_congr e]
  refine hsub.2.trans ?_
  have hb : ∑' ρ : ↥S, mult ρ * ⟪r, U ρ⟫_ℝ ^ 2 ≤ Bess * (2 * Kp ^ 2 + 4 * θ ^ 2 * ‖V‖ ^ 2) :=
    (Summable.tsum_subtype_le (fun ρ => mult ρ * ⟪r, U ρ⟫_ℝ ^ 2) S
      (fun ρ => mul_nonneg (mult_nonneg ρ) (sq_nonneg _)) hsb).trans
      ((hB r hr).2.trans (mul_le_mul_of_nonneg_left hrK hBess))
  have hc : ∑' ρ : ↥S, mult ρ * ⟪u, U ρ⟫_ℝ ^ 2 ≤ 6 * ‖V‖ ^ 2 * A₃ := by
    have hpt : ∀ ρ : ↥S, mult ρ * ⟪u, U ρ⟫_ℝ ^ 2
        ≤ ‖V - r‖ ^ 2 * (mult ρ * ‖(USpan hx0 D).starProjection (U ρ)‖ ^ 2) := fun ρ => by
      have h1 := Cvs.Upstream.ProjectionInterpolantSplit.abs_inner_split_le (R1 x) (USpan hx0 D) hu hsplit (U ρ)
      have h2 : ⟪u, U ρ⟫_ℝ ^ 2 ≤ (‖V - r‖ * ‖(USpan hx0 D).starProjection (U ρ)‖) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have hm := mult_nonneg (ρ : nonTrivialZeroSet)
      nlinarith [mul_le_mul_of_nonneg_left h2 hm]
    refine (Summable.tsum_le_tsum hpt (hsc.subtype _) (hA.1.mul_left _)).trans ?_
    rw [tsum_mul_left]
    have hA0 : 0 ≤ ∑' ρ : ↥S, mult ρ * ‖(USpan hx0 D).starProjection (U ρ)‖ ^ 2 :=
      tsum_nonneg fun ρ => mul_nonneg (mult_nonneg _) (sq_nonneg _)
    have := mul_le_mul hVr hA.2 hA0 (by positivity)
    linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **The projections off `D` onto the deep span** (caseinf-attack §6.3): with `Transplant` constant `K` on
`rect (δ_D/4) Y` and the deep zeros above `H` summing to `≤ A_c`, `Σ_{ρ ∉ D} m_ρ‖P_{U_D}U_ρ‖²` is summable and at most
`L x^{δ_D}(1 + (2Y)²)Σ m/(1 + γ²) + 16K²x^{δ_D}Σ m/γ² + A_c`, `D = deepSet δ_D H`. -/
theorem tsum_compl_proj_le {x : ℕ} (hx0 : (0 : ℝ) < x) (hx1 : (1 : ℝ) ≤ x) {δD H Y K Kp Ac : ℝ} (hδD : 0 < δD)
    (hY : 0 < Y) (hT : Transplant x (wR '' (deepSet δD H : Set nonTrivialZeroSet)) (rect (δD / 4) Y)
      (rect (δD / 4) Y) K Kp)
    (hC : (Summable fun ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ H < |(ρ : ℂ).im|} =>
        mult ρ * ‖(USpan hx0 (deepSet δD H)).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2)
      ∧ ∑' ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ H < |(ρ : ℂ).im|},
          mult ρ * ‖(USpan hx0 (deepSet δD H)).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2 ≤ Ac) :
    (Summable fun ρ : ↥((deepSet δD H : Set nonTrivialZeroSet)ᶜ) =>
        mult ρ * ‖(USpan hx0 (deepSet δD H)).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2)
      ∧ ∑' ρ : ↥((deepSet δD H : Set nonTrivialZeroSet)ᶜ),
          mult ρ * ‖(USpan hx0 (deepSet δD H)).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2
        ≤ Real.log x * (x : ℝ) ^ δD * (1 + (2 * Y) ^ 2) * Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum
          + 16 * K ^ 2 * (x : ℝ) ^ δD * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum + Ac := by
  set D := deepSet δD H
  set P : nonTrivialZeroSet → ℝ := fun ρ =>
    ‖(USpan hx0 D).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2 with hP
  set L := Real.log x with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg x
  set c := L * (x : ℝ) ^ δD
  have hc : 0 ≤ c := mul_nonneg hL (Real.rpow_nonneg hx0.le _)
  set Sc : Set nonTrivialZeroSet := {ρ | δD ≤ |Cvs.GaussKernel.del ρ| ∧ H < |(ρ : ℂ).im|}
  set fa : nonTrivialZeroSet → ℝ := fun ρ => if |(ρ : ℂ).im| ≤ 2 * Y then mult ρ * c else 0
  set fb : nonTrivialZeroSet → ℝ := fun ρ => 16 * K ^ 2 * (x : ℝ) ^ δD * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2))
  set fc : nonTrivialZeroSet → ℝ := Sc.indicator fun ρ => mult ρ * P ρ
  obtain ⟨hsa, hta⟩ := Cvs.StepA.Edge.DeepSetZeroSums.tsum_mul_ite_le_le (2 * Y) hc
  have hsb : Summable fb := Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq.mul_left _
  have hsc : Summable fc := summable_subtype_iff_indicator.1 hC.1
  have hfa0 : ∀ ρ, 0 ≤ fa ρ := fun ρ => by
    simp only [fa]; split_ifs
    · exact mul_nonneg (mult_nonneg ρ) hc
    · exact le_rfl
  have hfb0 : ∀ ρ, 0 ≤ fb ρ := fun ρ => mul_nonneg (by positivity) (mul_nonneg (mult_nonneg ρ) (by positivity))
  have hfc0 : ∀ ρ, 0 ≤ fc ρ := fun ρ => Set.indicator_nonneg (fun ρ _ => mul_nonneg (mult_nonneg ρ) (sq_nonneg _)) ρ
  have hpt : ∀ ρ : ↥((D : Set nonTrivialZeroSet)ᶜ), mult ρ * P ρ ≤ fa ρ + fb ρ + fc ρ := by
    rintro ⟨ρ, hρ⟩
    have hnot : ¬ (|(ρ : ℂ).im| ≤ H ∧ δD ≤ |Cvs.GaussKernel.del ρ|) := fun h => hρ (mem_deepSet.2 h)
    have hm := mult_nonneg ρ
    show mult ρ * P ρ ≤ fa ρ + fb ρ + fc ρ
    by_cases hd : δD ≤ |Cvs.GaussKernel.del ρ|
    · have hS : ρ ∈ Sc := ⟨hd, lt_of_not_ge fun h => hnot ⟨h, hd⟩⟩
      have : fc ρ = mult ρ * P ρ := Set.indicator_of_mem hS _
      linarith [hfa0 ρ, hfb0 ρ]
    · have hd' : |Cvs.GaussKernel.del ρ| ≤ δD := (not_le.1 hd).le
      have hxδ : (x : ℝ) ^ |Cvs.GaussKernel.del ρ| ≤ (x : ℝ) ^ δD := Real.rpow_le_rpow_of_exponent_le hx1 hd'
      by_cases hγ : |(ρ : ℂ).im| ≤ 2 * Y
      · have h1 : P ρ ≤ c := by
          have hPU : P ρ ≤ ‖ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)‖ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) ((USpan hx0 D).norm_starProjection_apply_le _) 2
          refine hPU.trans ((Cvs.StepA.Edge.DeepSetZeroSums.norm_sq_ueVec_le hx0 ρ).trans ?_)
          have : Real.exp (|Cvs.GaussKernel.del ρ| * L) = (x : ℝ) ^ |Cvs.GaussKernel.del ρ| := by
            rw [Real.rpow_def_of_pos hx0, mul_comm]
          rw [this]
          exact mul_le_mul_of_nonneg_left hxδ hL
        have : fa ρ = mult ρ * c := if_pos hγ
        nlinarith [hfb0 ρ, hfc0 ρ, mul_le_mul_of_nonneg_left h1 hm]
      · have h4 := Cvs.StepA.Edge.TransplantAngleHighZeros.norm_proj_ueVec_le hx0 (by linarith : (0 : ℝ) ≤ δD / 4) hT ρ hY (not_le.1 hγ).le
        have hγ0 : 0 < |(ρ : ℂ).im| := by linarith [(not_le.1 hγ)]
        have h5 : P ρ ≤ 16 * K ^ 2 * (x : ℝ) ^ δD * (1 / ((ρ : ℂ).im) ^ 2) := by
          have hsq : P ρ ≤ (K * (4 * (x : ℝ) ^ (|Cvs.GaussKernel.del ρ| / 2) / |(ρ : ℂ).im|)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h4 2
          have e : (K * (4 * (x : ℝ) ^ (|Cvs.GaussKernel.del ρ| / 2) / |(ρ : ℂ).im|)) ^ 2
              = 16 * K ^ 2 * (x : ℝ) ^ |Cvs.GaussKernel.del ρ| * (1 / ((ρ : ℂ).im) ^ 2) := by
            have hxx : ((x : ℝ) ^ (|Cvs.GaussKernel.del ρ| / 2)) ^ 2 = (x : ℝ) ^ |Cvs.GaussKernel.del ρ| := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
            rw [mul_pow, div_pow, mul_pow, hxx, sq_abs]
            field_simp
            norm_num
          rw [e] at hsq
          refine hsq.trans ?_
          have hiv : 0 ≤ 1 / ((ρ : ℂ).im) ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hxδ (by positivity : (0 : ℝ) ≤ 16 * K ^ 2)
          nlinarith [mul_le_mul_of_nonneg_right this hiv]
        have : fb ρ = 16 * K ^ 2 * (x : ℝ) ^ δD * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2)) := rfl
        have hfa := hfa0 ρ
        have hfc := hfc0 ρ
        nlinarith [mul_le_mul_of_nonneg_left h5 hm]
  have hsum : Summable fun ρ => fa ρ + fb ρ + fc ρ := (hsa.add hsb).add hsc
  have hs1 : Summable fun ρ : ↥((D : Set nonTrivialZeroSet)ᶜ) => mult ρ * P ρ :=
    Summable.of_nonneg_of_le (fun ρ => mul_nonneg (mult_nonneg _) (sq_nonneg _)) hpt (hsum.subtype _)
  refine ⟨hs1, ?_⟩
  calc ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ), mult ρ * P ρ
      ≤ ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ), (fa ρ + fb ρ + fc ρ) :=
        Summable.tsum_le_tsum hpt hs1 (hsum.subtype _)
    _ ≤ ∑' ρ, (fa ρ + fb ρ + fc ρ) :=
        Summable.tsum_subtype_le _ _ (fun ρ => add_nonneg (add_nonneg (hfa0 ρ) (hfb0 ρ)) (hfc0 ρ)) hsum
    _ = ∑' ρ, fa ρ + ∑' ρ, fb ρ + ∑' ρ, fc ρ := by
        rw [Summable.tsum_add (hsa.add hsb) hsc, Summable.tsum_add hsa hsb]
    _ ≤ _ := by
        have e2 : ∑' ρ, fb ρ = 16 * K ^ 2 * (x : ℝ) ^ δD * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := by
          simp only [fb]; rw [tsum_mul_left]; rfl
        have e3 : ∑' ρ, fc ρ = ∑' ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ H < |(ρ : ℂ).im|},
            mult ρ * ‖(USpan hx0 (deepSet δD H)).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2 :=
          (tsum_subtype Sc fun ρ => mult ρ * P ρ).symm
        rw [e2, e3]
        have : c * (1 + (2 * Y) ^ 2) * Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum
            = Real.log x * (x : ℝ) ^ δD * (1 + (2 * Y) ^ 2) * Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum := rfl
        linarith [hC.2]

/-! ### The named inputs -/

/-- A cutoff at exponent `ε₂`: `x^{ε₂} ≤ H(x) ≤ 2x^{ε₂}` at all large `x`. -/
def Cutoff (ε₂ : ℝ) (H : ℕ → ℝ) : Prop :=
  ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ ε₂ ≤ H x ∧ H x ≤ 2 * (x : ℝ) ^ ε₂

/-- **Route SEP's exterior data with saving `m`** (caseinf-W Proposition 5.1, (SEP-X)): `ExtData x (Q(x)x^{−m})` at
all large `x`, `Q` subpolynomial. -/
def SEPData (m : ℝ) : Prop :=
  ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ExtData x (Q x * (x : ℝ) ^ (-m))

/-- **(M1′) with saving `m`**: for some `ε > 0`, every `r ∈ R₁` has a summable `U` sum at most
`Q(x)x^{Θ' + m − ε}‖r‖²` at all large `x`, `Q` subpolynomial. -/
def M1Prime (m : ℝ) : Prop :=
  ∃ ε > 0, ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, ∀ r ∈ R1 x,
    (Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ ∑' ρ : nonTrivialZeroSet, mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ Q x * (x : ℝ) ^ (topDepth + m - ε) * ‖r‖ ^ 2

/-- **(M1′) from a Bessel bound at depth `Θ'`**: a summable `R₁` Bessel bound `Q(x)x^{Θ'}‖r‖²` (caseinf-W
Proposition 8.1's conclusion) gives `M1Prime m` for every `m > 0`. -/
theorem m1Prime_of_bessel {Q : ℕ → ℝ} (hQ : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q)
    (h : ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, ∀ r ∈ R1 x,
      (Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
        ∧ ∑' ρ : nonTrivialZeroSet, mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
          ≤ Q x * (x : ℝ) ^ topDepth * ‖r‖ ^ 2) {m : ℝ} (hm : 0 < m) : M1Prime m :=
  ⟨m, hm, Q, hQ, by
    filter_upwards [h] with x hx hx0 r hr
    obtain ⟨h1, h2⟩ := hx hx0 r hr
    exact ⟨h1, by rwa [show topDepth + m - m = topDepth by ring]⟩⟩

/-- **The ∂̄-transplant on the deep sets** (caseinf-attack Theorem 4 (a), (d), (e), Lemma 3, Corollary 5): some
`α > 0` such that for `0 < δ_D < ½`, `0 < ε₂`, `αε₂ < δ_D/8` and a cutoff `H` at `ε₂`, `Transplant` holds for
`deepSet δ_D H(x)` on `rect (δ_D/4) (4H(x) + 1)` with constants `Cx^{αε₂}`, `C` at all large `x`. -/
def DbarTransplant : Prop :=
  ∃ α > 0, ∀ δD : ℝ, 0 < δD → δD < 1 / 2 → ∀ ε₂ : ℝ, 0 < ε₂ → α * ε₂ < δD / 8 → ∀ H : ℕ → ℝ, Cutoff ε₂ H →
    ∃ C > 0, ∀ᶠ x : ℕ in atTop, Transplant x (wR '' (deepSet δD (H x) : Set nonTrivialZeroSet))
      (rect (δD / 4) (4 * H x + 1)) (rect (δD / 4) (4 * H x + 1)) (C * (x : ℝ) ^ (α * ε₂)) C

/-- **Point interpolation on the deep sets** (caseinf-W Theorem F (ii), (iii), (v)): some `α > 0` such that under the
same conditions every `σ` with `|δ_σ| ≥ δ_D` has `β > 0` with `PointInterp` at `w_σ` and bound
`32|δ_σ|x^{−|δ_σ|}/((1 − |δ_σ|/|w_σ|)²β²)` at all large `x`. -/
def FreeInterp : Prop :=
  ∃ α > 0, ∀ δD : ℝ, 0 < δD → δD < 1 / 2 → ∀ ε₂ : ℝ, 0 < ε₂ → α * ε₂ < δD / 8 → ∀ H : ℕ → ℝ, Cutoff ε₂ H →
    ∀ σ : nonTrivialZeroSet, δD ≤ |Cvs.GaussKernel.del σ| → ∃ β > 0, ∀ᶠ x : ℕ in atTop,
      PointInterp x (wR '' (deepSet δD (H x) : Set nonTrivialZeroSet)) (wR σ)
        (32 * |Cvs.GaussKernel.del σ| * (x : ℝ) ^ (-|Cvs.GaussKernel.del σ|)
          / ((1 - |Cvs.GaussKernel.del σ| / ‖wR σ‖) ^ 2 * β ^ 2))

/-- **Lemma C** (caseinf-W Lemma P and Theorem C): some `α > 0` such that each `0 < δ_D < ½` has `κ > 0`, and each
`0 < ε₂`, `αε₂ < δ_D/8` a cutoff `H` at `ε₂` with `Σ m_ρ‖P_{U_D}U_ρ‖² ≤ Q(x)x^{Θ' − κε₂}` (summable) over the zeros
with `|δ_ρ| ≥ δ_D`, `|γ_ρ| > H(x)`, `D = deepSet δ_D H(x)`, `Q` subpolynomial. -/
def LemmaC : Prop :=
  ∃ α > 0, ∀ δD : ℝ, 0 < δD → δD < 1 / 2 → ∃ κ > 0, ∀ ε₂ : ℝ, 0 < ε₂ → α * ε₂ < δD / 8 →
    ∃ H : ℕ → ℝ, Cutoff ε₂ H ∧ ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      (Summable fun ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ H x < |(ρ : ℂ).im|} =>
        mult ρ * ‖(USpan hx0 (deepSet δD (H x))).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2)
      ∧ ∑' ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ H x < |(ρ : ℂ).im|},
          mult ρ * ‖(USpan hx0 (deepSet δD (H x))).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2
        ≤ Q x * (x : ℝ) ^ (topDepth - κ * ε₂)

/-! ### The free share, the angle and the pairing rate -/

/-- `ExtData` is monotone in its constant. -/
theorem extData_mono {x : ℕ} {E E' : ℝ} (h : ExtData x E) (hE : E ≤ E') : ExtData x E' := fun a => by
  obtain ⟨hg, F, h1, h2, h3, h4⟩ := h a
  have hR := sq_nonneg (Cvs.Route.Visibility.ExteriorFactorMTwo.rNorm x a)
  exact ⟨hg.trans (mul_le_mul_of_nonneg_right hE hR), F, h1, h2, h3,
    fun s hs => (h4 s hs).trans (mul_le_mul_of_nonneg_right hE hR)⟩

/-- `|δ_σ| < |w_σ|` for an off-line zero. -/
theorem abs_del_lt_norm_wR (σ : nonTrivialZeroSet) : |Cvs.GaussKernel.del σ| < ‖wR σ‖ := by
  have him : (wR σ).im ≠ 0 := by
    have h := Cvs.StepA.Edge.WindowCoshTransformDuality.abs_wR_im σ
    intro h0; rw [h0, abs_zero] at h
    exact Cvs.StepA.LowEigenvalueCountZeros.im_ne_zero σ (abs_eq_zero.1 h.symm)
  rw [← Cvs.StepA.Edge.WindowCoshTransformDuality.wR_re σ]
  exact (le_abs_self _).trans_lt (Complex.abs_re_lt_norm.2 him)

/-- **The free share from point interpolation** (caseinf-W Theorem F (iv)): `PointInterp` with the bound
`32δx^{−δ}/((1 − g)²β²)` at all large `x` gives `FreeShare σ D ((1 − g)²β²/8)`, `δ = |δ_σ| ≠ 0`, `g = δ/|w_σ|`. -/
theorem freeShare_of_pointInterp {σ : nonTrivialZeroSet} (hσ : Cvs.GaussKernel.del σ ≠ 0)
    {D : ℕ → Finset nonTrivialZeroSet} {β : ℝ} (hβ : 0 < β)
    (h : ∀ᶠ x : ℕ in atTop, PointInterp x (wR '' (D x : Set nonTrivialZeroSet)) (wR σ)
      (32 * |Cvs.GaussKernel.del σ| * (x : ℝ) ^ (-|Cvs.GaussKernel.del σ|)
        / ((1 - |Cvs.GaussKernel.del σ| / ‖wR σ‖) ^ 2 * β ^ 2))) :
    Cvs.StepA.Edge.DeepJointShare.FreeShare σ D ((1 - |Cvs.GaussKernel.del σ| / ‖wR σ‖) ^ 2 * β ^ 2 / 8) := by
  set δ := |Cvs.GaussKernel.del σ|
  set g := δ / ‖wR σ‖
  have hδ : 0 < δ := abs_pos.2 hσ
  have hw := abs_del_lt_norm_wR σ
  have hg1 : g < 1 := (div_lt_one (hδ.trans hw)).2 hw
  have hc : 0 < (1 - g) ^ 2 * β ^ 2 := by
    have : 0 < 1 - g := by linarith
    positivity
  filter_upwards [h] with x hx hx0
  have h1 := Cvs.StepA.Edge.WindowCoshTransformDuality.one_le_mul_norm_bPerp_sq hx0 σ hx
  have h2 := Cvs.StepA.Edge.WindowCoshTransformDuality.norm_sq_Vσ_le hx0 hσ
  have hxδ : 0 < (x : ℝ) ^ δ := Real.rpow_pos_of_pos hx0 _
  have hinv : (x : ℝ) ^ (-δ) = ((x : ℝ) ^ δ)⁻¹ := Real.rpow_neg hx0.le δ
  set b := ‖bPerp hx0 (D x) σ‖ ^ 2
  have hB : 32 * δ * (x : ℝ) ^ (-δ) / ((1 - g) ^ 2 * β ^ 2) * b
      = 32 * δ * b / ((1 - g) ^ 2 * β ^ 2 * (x : ℝ) ^ δ) := by
    rw [hinv]; field_simp
  rw [hB, le_div_iff₀ (by positivity), one_mul] at h1
  have h3 : (1 - g) ^ 2 * β ^ 2 / 8 * ‖Vσ hx0 σ‖ ^ 2 ≤ (1 - g) ^ 2 * β ^ 2 / 8 * ((x : ℝ) ^ δ / (4 * δ)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  refine h3.trans ?_
  rw [show (1 - g) ^ 2 * β ^ 2 / 8 * ((x : ℝ) ^ δ / (4 * δ)) = (1 - g) ^ 2 * β ^ 2 * (x : ℝ) ^ δ / (32 * δ) by
    field_simp; ring, div_le_iff₀ (by positivity)]
  linarith

/-- `80 ≤ 2πx`, `x ≥ 1` and `4H(x) + 1 < x`, `H(x) ≥ 1` at all large `x`, for a cutoff at `0 < ε₂ < 1`. -/
theorem eventually_cutoff_facts {ε₂ : ℝ} (h0 : 0 < ε₂) (h1 : ε₂ < 1) {H : ℕ → ℝ} (hH : Cutoff ε₂ H) :
    ∀ᶠ x : ℕ in atTop, (80 : ℝ) ≤ 2 * π * x ∧ (1 : ℝ) ≤ x ∧ 4 * H x + 1 < x ∧ 1 ≤ H x := by
  have hlim : Tendsto (fun x : ℕ => (x : ℝ) ^ (ε₂ - 1)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - ε₂)).comp tendsto_natCast_atTop_atTop |>.congr
      fun x => by simp only [Function.comp, neg_sub]
  filter_upwards [Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale, hH, hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    eventually_ge_atTop 2] with x hs hc hl hx2
  have hx : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hx0 : (0 : ℝ) < x := by linarith
  have hpow : (x : ℝ) ^ ε₂ = (x : ℝ) ^ (ε₂ - 1) * x := by
    rw [← Real.rpow_add_one hx0.ne']; ring_nf
  have hge1 : (1 : ℝ) ≤ (x : ℝ) ^ ε₂ := Real.one_le_rpow (by linarith) h0.le
  refine ⟨hs, by linarith, ?_, hge1.trans hc.1⟩
  have : (x : ℝ) ^ ε₂ < x / 16 := by
    rw [hpow]; nlinarith
  nlinarith [hc.2]

/-- **The angle at one `x`**: with the transplant on `rect (δ_D/4) (4H + 1)`, `4H + 1 < x`, constants `A = Cx^{αε₂}`
and `C`, and `ExtData x (Q x^{−m})`, `Q ≥ 0`: `θ_x(D) ≤ 2A√(Q x^{−m})` and `(2A√(Q x^{−m}))² = 4C²Q x^{2αε₂ − m}`. -/
theorem angle_le_at {x : ℕ} (hs : (80 : ℝ) ≤ 2 * π * x) (hx0 : (0 : ℝ) < x) (hx1 : (1 : ℝ) ≤ x)
    {m α C ε₂ δD Hx Qp : ℝ} (hα : 0 ≤ α) (hε₂ : 0 ≤ ε₂) (hC : 0 < C) (hδD : 0 < δD) (hY : 4 * Hx + 1 < x)
    (hTx : Transplant x (wR '' (deepSet δD Hx : Set nonTrivialZeroSet)) (rect (δD / 4) (4 * Hx + 1))
      (rect (δD / 4) (4 * Hx + 1)) (C * (x : ℝ) ^ (α * ε₂)) C)
    (hQp : 0 ≤ Qp) (hE : ExtData x (Qp * (x : ℝ) ^ (-m))) :
    angle hx0 (deepSet δD Hx) ≤ 2 * (C * (x : ℝ) ^ (α * ε₂)) * √(Qp * (x : ℝ) ^ (-m))
      ∧ (2 * (C * (x : ℝ) ^ (α * ε₂)) * √(Qp * (x : ℝ) ^ (-m))) ^ 2
        = 4 * C ^ 2 * Qp * (x : ℝ) ^ (0 - (m - 2 * α * ε₂)) := by
  have hD : ∀ ρ ∈ deepSet δD Hx, |(ρ : ℂ).im| < x := fun ρ hρ => by
    have := (mem_deepSet.1 hρ).1
    have h1 : Hx < x := by linarith [show 0 ≤ Hx from (abs_nonneg _).trans this]
    linarith
  have hang := Cvs.StepA.Edge.TransplantAngleHighZeros.angle_le_of_extData hs hx0 (by linarith : 0 < δD / 4) hY.le hTx (by positivity) hC.le hD hE
  set A := C * (x : ℝ) ^ (α * ε₂)
  have hA1 : C ≤ A := le_mul_of_one_le_right hC.le (Real.one_le_rpow hx1 (by positivity))
  have hE0 : 0 ≤ Qp * (x : ℝ) ^ (-m) := mul_nonneg hQp (Real.rpow_nonneg hx0.le _)
  refine ⟨hang.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)), ?_⟩
  have hA2 : A ^ 2 = C ^ 2 * (x : ℝ) ^ (2 * α * ε₂) := by
    simp only [A]
    rw [mul_pow, ← Real.rpow_natCast ((x : ℝ) ^ (α * ε₂)), ← Real.rpow_mul hx0.le]
    congr 2; push_cast; ring
  have hxx : (x : ℝ) ^ (2 * α * ε₂) * (x : ℝ) ^ (-m) = (x : ℝ) ^ (0 - (m - 2 * α * ε₂)) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  rw [mul_pow, mul_pow, Real.sq_sqrt hE0, hA2, ← hxx]; ring

/-- **The angle bound** (caseinf-W Proposition 5.1 with caseinf-attack Theorem 4): route SEP's data with saving `m`
and a transplant with constants `Cx^{αε₂}`, `C`, `2αε₂ < m`, give `AngleBound D η` for every `η > 0`. -/
theorem angleBound_of {m α C ε₂ δD : ℝ} (hα : 0 ≤ α) (hC : 0 < C) (h0 : 0 < ε₂) (h1 : ε₂ < 1)
    (hm : 2 * α * ε₂ < m) (hδD : 0 < δD) {H : ℕ → ℝ} (hH : Cutoff ε₂ H) (hX : SEPData m)
    (hT : ∀ᶠ x : ℕ in atTop, Transplant x (wR '' (deepSet δD (H x) : Set nonTrivialZeroSet))
      (rect (δD / 4) (4 * H x + 1)) (rect (δD / 4) (4 * H x + 1)) (C * (x : ℝ) ^ (α * ε₂)) C)
    {η : ℝ} (hη : 0 < η) : Cvs.StepA.Edge.DeepJointShare.AngleBound (fun x => deepSet δD (H x)) η := by
  obtain ⟨Q, hQ, hXe⟩ := hX
  have hQ' : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x => 4 * C ^ 2 * max (Q x) 0 :=
    (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).mul (Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ) (Eventually.of_forall fun _ => by positivity)
      (Eventually.of_forall fun _ => le_max_right _ _)
  filter_upwards [hXe, hT, eventually_cutoff_facts h0 h1 hH,
    Cvs.Route.Visibility.ExtPairingRatesSubpoly.eventually_mul_rpow_le hQ' (by linarith : 0 < m - 2 * α * ε₂) 0 hη] with x hXx hTx hf hfin hx0
  obtain ⟨hs, hx1, hY, -⟩ := hf
  have hE : ExtData x (max (Q x) 0 * (x : ℝ) ^ (-m)) :=
    extData_mono hXx (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _))
  obtain ⟨hθ, heq⟩ := angle_le_at hs hx0 hx1 hα h0.le hC hδD hY hTx (le_max_right _ _) hE
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hθ 2
  calc angle hx0 (deepSet δD (H x)) ^ 2 ≤ _ := hsq
    _ = _ := heq
    _ ≤ η * (x : ℝ) ^ (0 : ℝ) := hfin
    _ = η := by rw [Real.rpow_zero, mul_one]

/-- **The pairing rate** (caseinf-attack Corollary 5′ on route SEP): route SEP's data with saving `m > 0` give
`ExtPairingRate {σ} |δ_σ| K` with `K = x^{|δ_σ|/2}(1 + 1/(1 − 2|δ_σ|))√(Q⁺x^{−m})`. -/
theorem extPairingRate_of {m : ℝ} (hm : 0 < m) (hX : SEPData m) (σ : nonTrivialZeroSet) :
    ∃ K : ℕ → ℝ, Cvs.Route.Visibility.ShareBesselFromExtPairing.ExtPairingRate {σ} |Cvs.GaussKernel.del σ| K
      ∧ ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∀ x : ℕ, 0 < x → K x ^ 2 = Q x * (x : ℝ) ^ (|Cvs.GaussKernel.del σ| - m) := by
  obtain ⟨Q, hQ, hXe⟩ := hX
  set δ := |Cvs.GaussKernel.del σ|
  set κ := 1 + 1 / (1 - 2 * δ)
  set K : ℕ → ℝ := fun x => (x : ℝ) ^ (δ / 2) * κ * √(max (Q x) 0 * (x : ℝ) ^ (-m))
  have hδ := Cvs.StepA.Edge.TransplantAngleHighZeros.abs_del_lt_half σ
  have hκ : 0 ≤ κ := by have : 0 < 1 - 2 * δ := by linarith
                        positivity
  have hK0 : ∀ x, 0 ≤ K x := fun x => mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hκ)
    (Real.sqrt_nonneg _)
  have hQ' : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x => κ ^ 2 * max (Q x) 0 :=
    (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).mul (Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ) (Eventually.of_forall fun _ => by positivity)
      (Eventually.of_forall fun _ => le_max_right _ _)
  have hK2 : ∀ x : ℕ, 0 < x → K x ^ 2 = κ ^ 2 * max (Q x) 0 * (x : ℝ) ^ (δ - m) := fun x hx => by
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
    simp only [K]
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx0.le _)),
      ← Real.rpow_natCast ((x : ℝ) ^ (δ / 2)), ← Real.rpow_mul hx0.le]
    have e : (x : ℝ) ^ (δ / 2 * ((2 : ℕ) : ℝ)) * (x : ℝ) ^ (-m) = (x : ℝ) ^ (δ - m) := by
      rw [← Real.rpow_add hx0]; congr 1; push_cast; ring
    rw [← e]; ring
  refine ⟨K, ⟨hK0, ?_, fun ε hε => ?_⟩, _, hQ', hK2⟩
  · have hlim := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop |(σ : ℂ).im|
    filter_upwards [hXe, hlim, eventually_gt_atTop 0] with x hXx hγ hxpos
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hxpos
    intro ρ hρ a
    rw [Finset.mem_singleton] at hρ
    subst hρ
    have hE : ExtData x (max (Q x) 0 * (x : ℝ) ^ (-m)) :=
      extData_mono hXx (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _))
    exact Cvs.StepA.Edge.TransplantAngleHighZeros.norm_extComb_le_of_extData hx0 hE hγ a
  · filter_upwards [Cvs.Route.Visibility.ExtPairingRatesSubpoly.eventually_mul_rpow_le hQ' hm δ hε, eventually_gt_atTop 0] with x h hx
    rw [hK2 x hx]; exact h

/-! ### The shallow rate -/

/-- `x^a x^b = x^{a+b}` for `x > 0`. -/
theorem rpow_mul_rpow' {x : ℕ} (hx0 : (0 : ℝ) < x) (a b : ℝ) :
    (x : ℝ) ^ a * (x : ℝ) ^ b = (x : ℝ) ^ (a + b) := (Real.rpow_add hx0 a b).symm

set_option maxHeartbeats 4000000 in
/-- **The off-`D` sum at one `x`, explicitly** (caseinf-attack §6): with transplant constants `Cx^{αε₂}`, `C`,
`ExtData x (Qx^{−m})`, `R₁` Bessel bound `Q₁x^{Θ'+m−ε₁}`, deep tail `Q_c x^{Θ'−κε₂}` and `4C²Qx^{2αε₂−m} ≤ ¼`, the
joint residue's `U` sum off `deepSet δ_D H` is summable and at most `3(t₁ + ⋯ + t₇)`, `t_i = q_i(x)x^{e_i}`. -/
theorem tsum_compl_wJoint_le_explicit {x : ℕ} (hs : (80 : ℝ) ≤ 2 * π * x) (hx0 : (0 : ℝ) < x) (hx1 : (1 : ℝ) ≤ x)
    {σ : nonTrivialZeroSet} (hσ : Cvs.GaussKernel.del σ ≠ 0)
    {m α C ε₂ δD κ ε₁ Hx Qp Q1p Qcp : ℝ} (hα : 0 ≤ α) (hε₂ : 0 ≤ ε₂) (hC : 0 < C) (hδD : 0 < δD)
    (hY : 4 * Hx + 1 < x) (hH1 : 1 ≤ Hx) (hHlo : (x : ℝ) ^ ε₂ ≤ Hx) (hHhi : Hx ≤ 2 * (x : ℝ) ^ ε₂)
    (hγ : |(σ : ℂ).im| < x) (hR : 2 * |(σ : ℂ).im| + 1 ≤ Hx) (hH9 : 9 + Real.exp 1 ≤ 2 * Hx)
    (hQp : 0 ≤ Qp) (hE : ExtData x (Qp * (x : ℝ) ^ (-m)))
    (hTx : Transplant x (wR '' (deepSet δD Hx : Set nonTrivialZeroSet)) (rect (δD / 4) (4 * Hx + 1))
      (rect (δD / 4) (4 * Hx + 1)) (C * (x : ℝ) ^ (α * ε₂)) C)
    (hθb : 4 * C ^ 2 * Qp * (x : ℝ) ^ (0 - (m - 2 * α * ε₂)) ≤ 1 / 4)
    (hQ1p : 0 ≤ Q1p)
    (hB : ∀ r ∈ R1 x, (Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ ∑' ρ : nonTrivialZeroSet, mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ Q1p * (x : ℝ) ^ (topDepth + m - ε₁) * ‖r‖ ^ 2)
    (hQcp : 0 ≤ Qcp)
    (hCx : (Summable fun ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ Hx < |(ρ : ℂ).im|} =>
        mult ρ * ‖(USpan hx0 (deepSet δD Hx)).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2)
      ∧ ∑' ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ Hx < |(ρ : ℂ).im|},
          mult ρ * ‖(USpan hx0 (deepSet δD Hx)).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2
        ≤ Qcp * (x : ℝ) ^ (topDepth - κ * ε₂)) :
    (Summable fun ρ : nonTrivialZeroSet =>
        mult ρ * ⟪wJoint hx0 (deepSet δD Hx) σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ ∑' ρ : ↥((deepSet δD Hx : Set nonTrivialZeroSet)ᶜ),
          mult ρ * ⟪wJoint hx0 (deepSet δD Hx) σ, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ 3 * (((Real.log x) ^ 2 * Cvs.StepA.Edge.DeepSetZeroSums.nearWeight σ + 16 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum)
              * (x : ℝ) ^ (|Cvs.GaussKernel.del σ| + δD)
            + 256 * (Real.log 8 + ε₂ * Real.log x) * (x : ℝ) ^ (|Cvs.GaussKernel.del σ| + topDepth - ε₂)
            + 2 * (1 + 1 / (1 - 2 * |Cvs.GaussKernel.del σ|)) ^ 2 * Q1p * Qp
              * (x : ℝ) ^ (topDepth + |Cvs.GaussKernel.del σ| - ε₁)
            + 4 * C ^ 2 * Q1p * Qp / |Cvs.GaussKernel.del σ|
              * (x : ℝ) ^ (topDepth - ε₁ + 2 * α * ε₂ + |Cvs.GaussKernel.del σ|)
            + 6 * 325 * Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum / (4 * |Cvs.GaussKernel.del σ|) * Real.log x
              * (x : ℝ) ^ (|Cvs.GaussKernel.del σ| + δD + 2 * ε₂)
            + 24 * C ^ 2 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum / |Cvs.GaussKernel.del σ|
              * (x : ℝ) ^ (|Cvs.GaussKernel.del σ| + δD + 2 * α * ε₂)
            + 6 / (4 * |Cvs.GaussKernel.del σ|) * Qcp
              * (x : ℝ) ^ (|Cvs.GaussKernel.del σ| + topDepth - κ * ε₂)) := by
  set δ := |Cvs.GaussKernel.del σ| with hδdef
  have hδ : 0 < δ := abs_pos.2 hσ
  have hδh := Cvs.StepA.Edge.TransplantAngleHighZeros.abs_del_lt_half σ
  set D := deepSet δD Hx
  set V := Vσ hx0 σ
  set L := Real.log x with hLdef
  have hL : 0 ≤ L := Real.log_natCast_nonneg x
  set Θ := topDepth
  set κσ := 1 + 1 / (1 - 2 * δ)
  have hκσ : 0 ≤ κσ := by
    have : 0 < 1 - 2 * δ := by linarith
    positivity
  have hxp : ∀ e : ℝ, 0 ≤ (x : ℝ) ^ e := fun e => Real.rpow_nonneg hx0.le e
  -- the angle
  obtain ⟨hθ, hθeq⟩ := angle_le_at hs hx0 hx1 hα hε₂ hC hδD hY hTx hQp hE
  set θb := 2 * (C * (x : ℝ) ^ (α * ε₂)) * √(Qp * (x : ℝ) ^ (-m))
  have hθb0 : 0 ≤ θb := by positivity
  have hθb2 : θb ≤ 1 / 2 := by
    have : θb ^ 2 ≤ (1 / 2) ^ 2 := by rw [hθeq]; linarith
    exact (pow_le_pow_iff_left₀ hθb0 (by norm_num) two_ne_zero).1 this
  -- the pairing
  set Kσ := (x : ℝ) ^ (δ / 2) * κσ * √(Qp * (x : ℝ) ^ (-m))
  have hKσ0 : 0 ≤ Kσ := by positivity
  have hKp : ‖(R1 x).starProjection V‖ ≤ Kσ :=
    (Cvs.Route.Visibility.ShareBesselFromExtPairing.norm_proj_le_of_extComb hs hx0 hKσ0 fun a => Cvs.StepA.Edge.TransplantAngleHighZeros.norm_extComb_le_of_extData hx0 hE hγ a).2
  have hKσ2 : Kσ ^ 2 = κσ ^ 2 * Qp * (x : ℝ) ^ (δ - m) := by
    simp only [Kσ]
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hQp (hxp _)), ← Real.rpow_natCast ((x : ℝ) ^ (δ / 2)),
      ← Real.rpow_mul hx0.le]
    have e : (x : ℝ) ^ (δ / 2 * ((2 : ℕ) : ℝ)) * (x : ℝ) ^ (-m) = (x : ℝ) ^ (δ - m) := by
      rw [rpow_mul_rpow' hx0]; congr 1; push_cast; ring
    rw [← e]; ring
  -- the projections
  set K := C * (x : ℝ) ^ (α * ε₂)
  have hA := tsum_compl_proj_le hx0 hx1 hδD (by linarith : (0 : ℝ) < 4 * Hx + 1) hTx hCx
  set A₃ := Real.log x * (x : ℝ) ^ δD * (1 + (2 * (4 * Hx + 1)) ^ 2) * Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum
    + 16 * K ^ 2 * (x : ℝ) ^ δD * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum + Qcp * (x : ℝ) ^ (Θ - κ * ε₂)
  -- the main bound
  set Bess := Q1p * (x : ℝ) ^ (Θ + m - ε₁)
  have hBess : 0 ≤ Bess := mul_nonneg hQ1p (hxp _)
  have hmain := tsum_compl_wJoint_le hx0 D σ hθb0 hθ hθb2 hB hBess hKp hA
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  -- the pairing part
  have hT2 : ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ), mult ρ * ⟪V, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ ((Real.log x) ^ 2 * Cvs.StepA.Edge.DeepSetZeroSums.nearWeight σ + 16 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum) * (x : ℝ) ^ (δ + δD)
        + 256 * (Real.log 8 + ε₂ * Real.log x) * (x : ℝ) ^ (δ + Θ - ε₂) := by
    have h := Cvs.StepA.Edge.DeepSetZeroSums.tsum_compl_pairUe_le σ (δD := δD) hL (fun ρ => abs_del_le_topDepth ρ) hR hH9
    have e0 : ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ), mult ρ * ⟪V, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        = ∑' ρ : ↥((D : Set nonTrivialZeroSet)ᶜ),
          mult (ρ : nonTrivialZeroSet) * Cvs.StepA.Edge.FiniteTopTieTerm.pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2 :=
      tsum_congr fun ρ => by rw [Cvs.StepA.Edge.FiniteTopTieTerm.inner_pairVec_ueVec]
    rw [e0]
    refine h.trans ?_
    have hex : ∀ e : ℝ, Real.exp (e * L) = (x : ℝ) ^ e := fun e => by rw [Real.rpow_def_of_pos hx0, mul_comm]
    rw [hex, hex]
    have hn0 : 0 ≤ Cvs.StepA.Edge.DeepSetZeroSums.nearWeight σ := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg ρ) (by split_ifs <;> norm_num)
    have hz0 : 0 ≤ Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg ρ) (by positivity)
    have htail : Cvs.Zeta.ZeroTailInverseSquare.tailBound Hx ≤ 16 * (Real.log 8 + ε₂ * L) * (x : ℝ) ^ (-ε₂) := by
      unfold Cvs.Zeta.ZeroTailInverseSquare.tailBound
      have hxe : 0 < (x : ℝ) ^ ε₂ := Real.rpow_pos_of_pos hx0 _
      have hlog : Real.log (4 * Hx) ≤ Real.log 8 + ε₂ * L := by
        rw [← Real.log_rpow hx0, ← Real.log_mul (by norm_num) hxe.ne']
        exact Real.log_le_log (by linarith) (by linarith)
      have hlog0 : 0 ≤ Real.log (4 * Hx) := Real.log_nonneg (by linarith)
      rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv]
      exact div_le_div₀ (by nlinarith) (by linarith) hxe hHlo
    have h2 : 16 * (x : ℝ) ^ (δ + Θ) * Cvs.Zeta.ZeroTailInverseSquare.tailBound Hx
        ≤ 256 * (Real.log 8 + ε₂ * Real.log x) * (x : ℝ) ^ (δ + Θ - ε₂) := by
      have := mul_le_mul_of_nonneg_left htail (by positivity : (0 : ℝ) ≤ 16 * (x : ℝ) ^ (δ + Θ))
      refine this.trans (le_of_eq ?_)
      rw [show δ + Θ - ε₂ = (δ + Θ) + -ε₂ by ring, ← rpow_mul_rpow' hx0 (δ + Θ) (-ε₂)]
      ring
    linarith
  -- the Bessel parts
  have hVu : ‖V‖ ^ 2 ≤ (x : ℝ) ^ δ / (4 * δ) := Cvs.StepA.Edge.WindowCoshTransformDuality.norm_sq_Vσ_le hx0 hσ
  have hV0 : 0 ≤ ‖V‖ ^ 2 := sq_nonneg _
  have ht3 : Bess * (2 * Kσ ^ 2) = 2 * κσ ^ 2 * Q1p * Qp * (x : ℝ) ^ (Θ + δ - ε₁) := by
    simp only [Bess]; rw [hKσ2]
    rw [show Θ + δ - ε₁ = (Θ + m - ε₁) + (δ - m) by ring, ← rpow_mul_rpow' hx0]; ring
  have ht4 : Bess * (4 * θb ^ 2 * ‖V‖ ^ 2)
      ≤ 4 * C ^ 2 * Q1p * Qp / δ * (x : ℝ) ^ (Θ - ε₁ + 2 * α * ε₂ + δ) := by
    have h1 : Bess * (4 * θb ^ 2 * ‖V‖ ^ 2) ≤ Bess * (4 * θb ^ 2 * ((x : ℝ) ^ δ / (4 * δ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVu (by positivity)) hBess
    refine h1.trans (le_of_eq ?_)
    simp only [Bess]; rw [hθeq]
    rw [show Θ - ε₁ + 2 * α * ε₂ + δ = (Θ + m - ε₁) + (0 - (m - 2 * α * ε₂)) + δ by ring,
      ← rpow_mul_rpow' hx0, ← rpow_mul_rpow' hx0]
    field_simp
  -- the projection parts
  have hxe1 : 1 ≤ (x : ℝ) ^ ε₂ := Real.one_le_rpow hx1 hε₂
  have hY2 : 1 + (2 * (4 * Hx + 1)) ^ 2 ≤ 325 * (x : ℝ) ^ (2 * ε₂) := by
    have h1 : 2 * (4 * Hx + 1) ≤ 18 * (x : ℝ) ^ ε₂ := by linarith
    have h2 : (2 * (4 * Hx + 1)) ^ 2 ≤ (18 * (x : ℝ) ^ ε₂) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : ((x : ℝ) ^ ε₂) ^ 2 = (x : ℝ) ^ (2 * ε₂) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have h4 : 1 ≤ (x : ℝ) ^ (2 * ε₂) := Real.one_le_rpow hx1 (by linarith)
    nlinarith
  have hZ0 : 0 ≤ Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg ρ) (by positivity)
  have hZ'0 : 0 ≤ Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg ρ) (by positivity)
  have hK2 : K ^ 2 = C ^ 2 * (x : ℝ) ^ (2 * α * ε₂) := by
    simp only [K]
    rw [mul_pow, ← Real.rpow_natCast ((x : ℝ) ^ (α * ε₂)), ← Real.rpow_mul hx0.le]
    congr 2; push_cast; ring
  have hA3 : 6 * ‖V‖ ^ 2 * A₃
      ≤ 6 * 325 * Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum / (4 * δ) * Real.log x * (x : ℝ) ^ (δ + δD + 2 * ε₂)
        + 24 * C ^ 2 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum / δ * (x : ℝ) ^ (δ + δD + 2 * α * ε₂)
        + 6 / (4 * δ) * Qcp * (x : ℝ) ^ (δ + Θ - κ * ε₂) := by
    have hA0 : 0 ≤ A₃ := by positivity
    have h1 : 6 * ‖V‖ ^ 2 * A₃ ≤ 6 * ((x : ℝ) ^ δ / (4 * δ)) * A₃ :=
      mul_le_mul_of_nonneg_right (by linarith) hA0
    refine h1.trans ?_
    have hA3b : A₃ ≤ Real.log x * (x : ℝ) ^ δD * (325 * (x : ℝ) ^ (2 * ε₂)) * Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum
        + 16 * K ^ 2 * (x : ℝ) ^ δD * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum + Qcp * (x : ℝ) ^ (Θ - κ * ε₂) := by
      simp only [A₃]
      have := mul_le_mul_of_nonneg_left hY2 (mul_nonneg hL (hxp δD))
      nlinarith [mul_le_mul_of_nonneg_right this hZ'0]
    have h2 := mul_le_mul_of_nonneg_left hA3b (by positivity : (0 : ℝ) ≤ 6 * ((x : ℝ) ^ δ / (4 * δ)))
    refine h2.trans (le_of_eq ?_)
    rw [hK2]
    rw [show δ + δD + 2 * ε₂ = δ + (δD + 2 * ε₂) by ring, show δ + δD + 2 * α * ε₂ = δ + (δD + 2 * α * ε₂) by ring,
      show δ + Θ - κ * ε₂ = δ + (Θ - κ * ε₂) by ring, ← rpow_mul_rpow' hx0 δ, ← rpow_mul_rpow' hx0 δ,
      ← rpow_mul_rpow' hx0 δ, ← rpow_mul_rpow' hx0 δD, ← rpow_mul_rpow' hx0 δD]
    field_simp
    ring
  have e : Bess * (2 * Kσ ^ 2 + 4 * θb ^ 2 * ‖V‖ ^ 2) = Bess * (2 * Kσ ^ 2) + Bess * (4 * θb ^ 2 * ‖V‖ ^ 2) := by
    ring
  rw [e, ht3]
  have := add_le_add (add_le_add hT2 ht4) hA3
  linarith

/-- A subpolynomial factor times `x^e` is eventually below `εx^b` for `e < b`. -/
theorem eventually_mul_rpow_le_of_lt {q : ℕ → ℝ} (hq : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly q) {e b ε : ℝ} (h : e < b) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, q x * (x : ℝ) ^ e ≤ ε * (x : ℝ) ^ b := by
  filter_upwards [Cvs.Route.Visibility.ExtPairingRatesSubpoly.eventually_mul_rpow_le hq (sub_pos.2 h) b hε] with x hx
  rwa [sub_sub_cancel] at hx

/-- A nonnegative constant multiple of an eventually nonnegative subpolynomial function is subpolynomial. -/
theorem subPoly_const_mul {q : ℕ → ℝ} (hq : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly q) (hq0 : ∀ᶠ x : ℕ in atTop, 0 ≤ q x) {c : ℝ}
    (hc : 0 ≤ c) : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x => c * q x :=
  (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const c).mul hq (Eventually.of_forall fun _ => hc) hq0

set_option maxHeartbeats 4000000 in
/-- **The shallow rate** (caseinf-attack §6 with caseinf-W Theorem C and Proposition 8.1): under the exponent
conditions `δ_D + 2ε₂ < δ`, `δ_D + 2αε₂ < δ`, `Θ' − ε₂ < δ`, `Θ' − ε₁ + 2αε₂ < δ`, `Θ' − κε₂ < δ`, `2αε₂ < m`
(`δ = |δ_σ|`), route SEP's data, the `R₁` Bessel rate, the transplant and the deep tail give `ShallowRate σ D`. -/
theorem shallowRate_of {σ : nonTrivialZeroSet} (hσ : Cvs.GaussKernel.del σ ≠ 0) {m α C ε₂ δD κ ε₁ : ℝ}
    (hα : 0 ≤ α) (hC : 0 < C) (h0 : 0 < ε₂) (h1 : ε₂ < 1) (hm : 2 * α * ε₂ < m) (hδD : 0 < δD)
    (c1 : δD + 2 * ε₂ < |Cvs.GaussKernel.del σ|) (c2 : δD + 2 * α * ε₂ < |Cvs.GaussKernel.del σ|)
    (c3 : topDepth - ε₂ < |Cvs.GaussKernel.del σ|) (c4 : topDepth - ε₁ + 2 * α * ε₂ < |Cvs.GaussKernel.del σ|)
    (c5 : topDepth - κ * ε₂ < |Cvs.GaussKernel.del σ|)
    {H : ℕ → ℝ} (hH : Cutoff ε₂ H) (hX : SEPData m)
    (hM : ∃ Q₁ : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q₁ ∧ ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x, ∀ r ∈ R1 x,
      (Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
        ∧ ∑' ρ : nonTrivialZeroSet, mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
          ≤ Q₁ x * (x : ℝ) ^ (topDepth + m - ε₁) * ‖r‖ ^ 2)
    (hT : ∀ᶠ x : ℕ in atTop, Transplant x (wR '' (deepSet δD (H x) : Set nonTrivialZeroSet))
      (rect (δD / 4) (4 * H x + 1)) (rect (δD / 4) (4 * H x + 1)) (C * (x : ℝ) ^ (α * ε₂)) C)
    (hLC : ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ hx0 : (0 : ℝ) < x,
      (Summable fun ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ H x < |(ρ : ℂ).im|} =>
        mult ρ * ‖(USpan hx0 (deepSet δD (H x))).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2)
      ∧ ∑' ρ : {ρ : nonTrivialZeroSet // δD ≤ |Cvs.GaussKernel.del ρ| ∧ H x < |(ρ : ℂ).im|},
          mult ρ * ‖(USpan hx0 (deepSet δD (H x))).starProjection (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))‖ ^ 2
        ≤ Q x * (x : ℝ) ^ (topDepth - κ * ε₂)) :
    Cvs.StepA.Edge.DeepJointShare.ShallowRate σ (fun x => deepSet δD (H x)) := by
  intro ε hε
  obtain ⟨Q, hQ, hXe⟩ := hX
  obtain ⟨Q₁, hQ₁, hMe⟩ := hM
  obtain ⟨Qc, hQc, hCe⟩ := hLC
  set δ := |Cvs.GaussKernel.del σ| with hδdef
  have hδ : 0 < δ := abs_pos.2 hσ
  have hre : (Cvs.ZeroCounting.zPoint σ).re ≠ 0 := by rw [Cvs.ZeroCounting.zPoint_re]; exact Cvs.StepA.LowEigenvalueCountZeros.im_ne_zero σ
  have him : (Cvs.ZeroCounting.zPoint σ).im ≠ 0 := by rw [Cvs.ZeroCounting.zPoint_im]; exact neg_ne_zero.2 hσ
  have habs : |(Cvs.ZeroCounting.zPoint σ).im| = δ := by rw [Cvs.ZeroCounting.zPoint_im, abs_neg]; rfl
  obtain ⟨βV, hβV, hVlo⟩ := Cvs.StepA.Edge.DeepJointShare.exists_norm_sq_pairVec_ge hre him
  set ε' := ε * βV ^ 2 / 21
  have hε' : 0 < ε' := by positivity
  have hαε : 0 ≤ α * ε₂ := mul_nonneg hα h0.le
  set Θ := topDepth
  set κσ := 1 + 1 / (1 - 2 * δ)
  -- the subpolynomial factors
  have hlog0 : ∀ᶠ x : ℕ in atTop, 0 ≤ Real.log x := Eventually.of_forall fun x => Real.log_natCast_nonneg x
  have hQp := Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ
  have hQ1p := Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ₁
  have hQcp := Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQc
  have hmax0 : ∀ q : ℕ → ℝ, ∀ᶠ x : ℕ in atTop, 0 ≤ max (q x) 0 := fun q =>
    Eventually.of_forall fun _ => le_max_right _ _
  have hn0 : 0 ≤ Cvs.StepA.Edge.DeepSetZeroSums.nearWeight σ := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg ρ) (by split_ifs <;> norm_num)
  have hZ0 : 0 ≤ Cvs.StepA.Edge.DeepSetZeroSums.invSqSum := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg ρ) (by positivity)
  have hZ'0 : 0 ≤ Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum := tsum_nonneg fun ρ => mul_nonneg (mult_nonneg ρ) (by positivity)
  have hlog2 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => Real.log x ^ 2 :=
    (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log.mul Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log hlog0 hlog0).mono (Eventually.of_forall fun x => le_of_eq (by ring))
  have q1 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => Real.log x ^ 2 * Cvs.StepA.Edge.DeepSetZeroSums.nearWeight σ + 16 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum :=
    (hlog2.mul (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _) (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ => hn0)).add (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _)
  have q2 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => 256 * (Real.log 8 + ε₂ * Real.log x) :=
    subPoly_const_mul ((Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _).add (subPoly_const_mul Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log hlog0 h0.le))
      (Eventually.of_forall fun x => by
        have := Real.log_natCast_nonneg x
        have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
        positivity) (by norm_num)
  have hκσ : 0 ≤ κσ := by
    have := Cvs.StepA.Edge.TransplantAngleHighZeros.abs_del_lt_half σ
    have : 0 < 1 - 2 * δ := by linarith
    positivity
  have hQQ : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x => max (Q₁ x) 0 * max (Q x) 0 := hQ1p.mul hQp (hmax0 Q₁) (hmax0 Q)
  have q3 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x => 2 * κσ ^ 2 * max (Q₁ x) 0 * max (Q x) 0 :=
    (subPoly_const_mul hQQ (Eventually.of_forall fun _ => mul_nonneg (le_max_right _ _) (le_max_right _ _))
      (by positivity : (0 : ℝ) ≤ 2 * κσ ^ 2)).mono (Eventually.of_forall fun x => le_of_eq (by ring))
  have q4 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x => 4 * C ^ 2 * max (Q₁ x) 0 * max (Q x) 0 / δ :=
    (subPoly_const_mul hQQ (Eventually.of_forall fun _ => mul_nonneg (le_max_right _ _) (le_max_right _ _))
      (by positivity : (0 : ℝ) ≤ 4 * C ^ 2 / δ)).mono (Eventually.of_forall fun x => le_of_eq (by ring))
  have q5 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x : ℕ => 6 * 325 * Cvs.StepA.Edge.DeepSetZeroSums.invOneSqSum / (4 * δ) * Real.log x :=
    subPoly_const_mul Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_log hlog0 (by positivity)
  have q6 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun _ : ℕ => 24 * C ^ 2 * Cvs.StepA.Edge.DeepSetZeroSums.invSqSum / δ := Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const _
  have q7 : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x => 6 / (4 * δ) * max (Qc x) 0 := subPoly_const_mul hQcp (hmax0 Qc) (by positivity)
  have hθq : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly fun x => 4 * C ^ 2 * max (Q x) 0 := subPoly_const_mul hQp (hmax0 Q) (by positivity)
  -- large `H`
  have hHbig : ∀ᶠ x : ℕ in atTop, max (2 * |(σ : ℂ).im| + 1) ((9 + Real.exp 1) / 2) ≤ (x : ℝ) ^ ε₂ :=
    (Cvs.Route.Visibility.ExtPairingRatesSubpoly.tendsto_natCast_rpow h0).eventually_ge_atTop _
  have hγx : ∀ᶠ x : ℕ in atTop, |(σ : ℂ).im| < x :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
  filter_upwards [eventually_cutoff_facts h0 h1 hH, hH, hHbig, hγx, hXe, hMe, hT, hCe, hVlo,
    Cvs.Route.Visibility.ExtPairingRatesSubpoly.eventually_mul_rpow_le hθq (by linarith : 0 < m - 2 * α * ε₂) 0 (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_mul_rpow_le_of_lt q1 (by linarith : δ + δD < 2 * δ) hε',
    eventually_mul_rpow_le_of_lt q2 (by linarith : δ + Θ - ε₂ < 2 * δ) hε',
    eventually_mul_rpow_le_of_lt q3 (by linarith : Θ + δ - ε₁ < 2 * δ) hε',
    eventually_mul_rpow_le_of_lt q4 (by linarith : Θ - ε₁ + 2 * α * ε₂ + δ < 2 * δ) hε',
    eventually_mul_rpow_le_of_lt q5 (by linarith : δ + δD + 2 * ε₂ < 2 * δ) hε',
    eventually_mul_rpow_le_of_lt q6 (by linarith : δ + δD + 2 * α * ε₂ < 2 * δ) hε',
    eventually_mul_rpow_le_of_lt q7 (by linarith : δ + Θ - κ * ε₂ < 2 * δ) hε']
    with x hf hc hbig hγ hXx hMx hTx hCx hVx hθx t1 t2 t3 t4 t5 t6 t7 hx0
  obtain ⟨hs, hx1, hY, hH1⟩ := hf
  have hE : ExtData x (max (Q x) 0 * (x : ℝ) ^ (-m)) :=
    extData_mono hXx (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _))
  have hB : ∀ r ∈ R1 x, (Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ ∑' ρ : nonTrivialZeroSet, mult ρ * ⟪r, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ max (Q₁ x) 0 * (x : ℝ) ^ (Θ + m - ε₁) * ‖r‖ ^ 2 := fun r hr => by
    obtain ⟨h1', h2'⟩ := hMx hx0 r hr
    refine ⟨h1', h2'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hx0.le _)) (sq_nonneg _))⟩
  obtain ⟨hCs, hCb⟩ := hCx hx0
  have hCx' := And.intro hCs (hCb.trans (mul_le_mul_of_nonneg_right (le_max_left (Qc x) 0)
    (Real.rpow_nonneg hx0.le (Θ - κ * ε₂))))
  have hθb : 4 * C ^ 2 * max (Q x) 0 * (x : ℝ) ^ (0 - (m - 2 * α * ε₂)) ≤ 1 / 4 := by
    rw [Real.rpow_zero, mul_one] at hθx; exact hθx
  have hR : 2 * |(σ : ℂ).im| + 1 ≤ H x := ((le_max_left _ _).trans hbig).trans hc.1
  have hH9 : 9 + Real.exp 1 ≤ 2 * H x := by
    have := ((le_max_right _ _).trans hbig).trans hc.1; linarith
  obtain ⟨hsum, hbound⟩ := tsum_compl_wJoint_le_explicit hs hx0 hx1 hσ hα h0.le hC hδD hY hH1 hc.1 hc.2 hγ hR hH9
    (le_max_right _ _) hE hTx hθb (le_max_right _ _) hB (le_max_right _ _) hCx'
  refine ⟨hsum, hbound.trans ?_⟩
  have hV := hVx hx0
  rw [habs] at hV
  have hV4 : (βV * (x : ℝ) ^ δ) ^ 2 ≤ ‖Vσ hx0 σ‖ ^ 4 := by
    have := pow_le_pow_left₀ (by positivity) hV 2
    rw [← pow_mul] at this; exact this
  have hx2 : ((x : ℝ) ^ δ) ^ 2 = (x : ℝ) ^ (2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hsumt := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add t1 t2) t3) t4) t5) t6) t7
  have e : (βV * (x : ℝ) ^ δ) ^ 2 = βV ^ 2 * (x : ℝ) ^ (2 * δ) := by rw [mul_pow, hx2]
  rw [e] at hV4
  have hfin : 3 * (7 * (ε' * (x : ℝ) ^ (2 * δ))) = ε * (βV ^ 2 * (x : ℝ) ^ (2 * δ)) := by
    simp only [ε']; ring
  nlinarith [mul_le_mul_of_nonneg_left hV4 hε.le]

/-! ### Case ∞ -/

set_option maxHeartbeats 1000000 in
/-- **Case ∞ of hV** (caseinf-W Theorem 9 (A)): route SEP's exterior data and (M1′) with a saving `m > 0`, the
∂̄-transplant, point interpolation and Lemma C give `DeepJointShare`'s joint hypothesis on `NoTop`. -/
theorem jointRates_of_caseInf {m : ℝ} (hm : 0 < m) (hX : SEPData m) (hM : M1Prime m) (hT : DbarTransplant)
    (hF : FreeInterp) (hC : LemmaC) :
    Cvs.StepA.Edge.FiniteTopIffFiniteBand.NoTop → ∃ σ : nonTrivialZeroSet, Cvs.GaussKernel.del σ ≠ 0 ∧
      ∃ (D : ℕ → Finset nonTrivialZeroSet) (r η : ℝ) (K : ℕ → ℝ), η < r ∧ Cvs.StepA.Edge.DeepJointShare.FreeShare σ D r
        ∧ Cvs.Route.Visibility.ShareBesselFromExtPairing.ExtPairingRate {σ} |Cvs.GaussKernel.del σ| K ∧ Cvs.StepA.Edge.DeepJointShare.AngleBound D η ∧ Cvs.StepA.Edge.DeepJointShare.ShallowRate σ D := by
  intro hN
  have hRH := hN.1
  set Θ := topDepth
  have hΘ0 := topDepth_pos hRH
  have hΘh := topDepth_le_half hRH
  set δD := Θ / 2
  have hδD0 : 0 < δD := by positivity
  have hδDh : δD < 1 / 2 := by simp only [δD]; linarith
  obtain ⟨ε₁, hε₁, Q₁, hQ₁, hMe⟩ := hM
  obtain ⟨αT, hαT, hT'⟩ := hT
  obtain ⟨αF, hαF, hF'⟩ := hF
  obtain ⟨αC, hαC, hC'⟩ := hC
  obtain ⟨κ, hκ, hCδ⟩ := hC' δD hδD0 hδDh
  set α := max αT (max αF αC)
  have hα : 0 < α := lt_max_of_lt_left hαT
  have hαT' : αT ≤ α := le_max_left _ _
  have hαF' : αF ≤ α := (le_max_left _ _).trans (le_max_right _ _)
  have hαC' : αC ≤ α := (le_max_right _ _).trans (le_max_right _ _)
  set ε₂ := min (min (δD / (16 * α)) (ε₁ / (8 * α))) (min (min (m / (4 * α)) (Θ / 16)) (1 / 2))
  have hε₂0 : 0 < ε₂ := by positivity
  have he1 : ε₂ ≤ δD / (16 * α) := (min_le_left _ _).trans (min_le_left _ _)
  have he2 : ε₂ ≤ ε₁ / (8 * α) := (min_le_left _ _).trans (min_le_right _ _)
  have he3 : ε₂ ≤ m / (4 * α) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have he4 : ε₂ ≤ Θ / 16 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have he5 : ε₂ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hαe1 : α * ε₂ ≤ δD / 16 :=
    (mul_le_mul_of_nonneg_left he1 hα.le).trans_eq (by field_simp)
  have hαe2 : α * ε₂ ≤ ε₁ / 8 :=
    (mul_le_mul_of_nonneg_left he2 hα.le).trans_eq (by field_simp)
  have hαe3 : α * ε₂ ≤ m / 4 :=
    (mul_le_mul_of_nonneg_left he3 hα.le).trans_eq (by field_simp)
  have hTε : αT * ε₂ ≤ α * ε₂ := mul_le_mul_of_nonneg_right hαT' hε₂0.le
  have hFε : αF * ε₂ ≤ α * ε₂ := mul_le_mul_of_nonneg_right hαF' hε₂0.le
  have hCε : αC * ε₂ ≤ α * ε₂ := mul_le_mul_of_nonneg_right hαC' hε₂0.le
  obtain ⟨H, hH, Qc, hQc, hCe⟩ := hCδ ε₂ hε₂0 (by linarith)
  obtain ⟨C, hC0, hTe⟩ := hT' δD hδD0 hδDh ε₂ hε₂0 (by linarith) H hH
  set η₀ := min (min (ε₂ / 2) (ε₁ / 4)) (min (κ * ε₂ / 2) (Θ / 4))
  have hη₀ : 0 < η₀ := by positivity
  obtain ⟨σ, hσgt⟩ := exists_abs_del_gt hRH hη₀
  have hη1 : η₀ ≤ ε₂ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η₀ ≤ ε₁ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η₀ ≤ κ * ε₂ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη4 : η₀ ≤ Θ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  set δ := |Cvs.GaussKernel.del σ|
  have hδ0 : 0 < δ := by linarith
  have hσ : Cvs.GaussKernel.del σ ≠ 0 := abs_pos.1 hδ0
  have hδD : δD ≤ δ := by simp only [δD]; linarith
  obtain ⟨β, hβ, hPI⟩ := hF' δD hδD0 hδDh ε₂ hε₂0 (by linarith) H hH σ hδD
  set g := δ / ‖wR σ‖
  have hg : g < 1 := (div_lt_one ((hδ0.trans (abs_del_lt_norm_wR σ)))).2 (abs_del_lt_norm_wR σ)
  set r := (1 - g) ^ 2 * β ^ 2 / 8
  have hr : 0 < r := by
    have : 0 < 1 - g := by linarith
    positivity
  obtain ⟨K, hK, -⟩ := extPairingRate_of hm hX σ
  have hm' : 2 * αT * ε₂ < m := by linarith
  refine ⟨σ, hσ, fun x => deepSet δD (H x), r, r / 2, K, by linarith, freeShare_of_pointInterp hσ hβ hPI, hK,
    angleBound_of hαT.le hC0 hε₂0 (by linarith) hm' hδD0 hH hX hTe (by linarith), ?_⟩
  exact shallowRate_of hσ hαT.le hC0 hε₂0 (by linarith) hm' hδD0 (by simp only [δD]; linarith)
    (by simp only [δD]; linarith) (by linarith) (by linarith) (by nlinarith) hH hX ⟨Q₁, hQ₁, hMe⟩ hTe ⟨Qc, hQc, hCe⟩

end Cvs.StepA.Edge.CaseInfinityJointRates

end
