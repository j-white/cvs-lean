import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFormTailLimit
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The spine regularization parameter has a quadratic concentration defect

The centre of a pole-free spine retains the squared concentration defects under angular Bessel.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Approximant.SpineRegularisationDefect
open Cvs.ZeroCounting

open Cvs.Prolate.EvenRungsByIndex (rung rung₁ rung₂ muR lamR rung_spec psi_rung)
open Cvs.Approximant.DeepIndexSpineSpan (alpha spineG)

/-- Ordered nonnegative contractions retain the square of the concentration defect in their ratio. -/
theorem one_sub_div_sq_le_defect_sq {τ τ₀ : ℝ} (hτ : 0 ≤ τ) (hτ₀ : 0 < τ₀)
    (hle : τ ≤ τ₀) (h1 : τ₀ ≤ 1) :
    (1 - τ / τ₀) ^ 2 ≤ (1 - τ ^ 2) ^ 2 := by
  have hdiv : τ / τ₀ ≤ 1 := (div_le_one hτ₀).2 hle
  have hge : τ ≤ τ / τ₀ := by
    rw [le_div_iff₀ hτ₀]
    exact mul_le_of_le_one_right hτ h1
  have ht1 : τ ≤ 1 := hle.trans h1
  have hsq : τ ^ 2 ≤ τ := by nlinarith
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- Weighted Bessel and a squared-defect weight give a squared-defect centre bound. -/
theorem sq_sum_le_defect_sq_of_bessel {ι : Type*} (S : Finset ι) (b v w lam : ι → ℝ)
    {K m : ℝ} (hm : 0 < m) (hw : ∀ i ∈ S, w i ^ 2 ≤ (1 - lam i) ^ 2)
    (hmin : ∀ i ∈ S, m ≤ lam i) (hB : ∑ i ∈ S, lam i * v i ^ 2 ≤ K) :
    (∑ i ∈ S, b i * v i * w i) ^ 2
      ≤ (∑ i ∈ S, b i ^ 2 * (1 - lam i) ^ 2) * (K / m) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => b i * w i) v
  have he : ∑ i ∈ S, b i * v i * w i = ∑ i ∈ S, b i * w i * v i :=
    Finset.sum_congr rfl fun i _ => by ring
  have h1 : ∑ i ∈ S, (b i * w i) ^ 2 ≤ ∑ i ∈ S, b i ^ 2 * (1 - lam i) ^ 2 :=
    Finset.sum_le_sum fun i hi => by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (hw i hi) (sq_nonneg _)
  have h2 : ∑ i ∈ S, v i ^ 2 ≤ K / m := by
    rw [le_div_iff₀ hm]
    calc
      (∑ i ∈ S, v i ^ 2) * m = ∑ i ∈ S, m * v i ^ 2 := by
        rw [Finset.sum_mul]
        simp [mul_comm]
      _ ≤ ∑ i ∈ S, lam i * v i ^ 2 :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hmin i hi) (sq_nonneg _)
      _ ≤ K := hB
  rw [he]
  exact hCS.trans (mul_le_mul h1 h2
    (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- The scaled centre of an actual spine is bounded by the weighted squared concentration defects. -/
theorem scaled_spine_center_sq_le {c lmin : ℝ} (hc : 0 < c) {S : Finset ℕ}
    (hS : ∀ j ∈ S, ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c (2 * j) χ)
    (hlmin : 0 < lmin) (hlam : ∀ j ∈ S, lmin ≤ lamR c (2 * j)) (a : S → ℝ) :
    (2 * π / c) ^ 2 * spineG c a 0 ^ 2
      ≤ 4 * π / (c * lmin) * ∑ j, a j ^ 2 * (1 - lamR c (2 * (j : ℕ))) ^ 2 := by
  classical
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hspec := fun j : S => rung_spec (hS j j.2)
  have hs0 := rung_spec h0
  have hμ0 := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h0 (show Even 0 from ⟨0, rfl⟩)
  let k := √(c / (2 * π))
  have hk : 0 < k := Real.sqrt_pos.mpr (by positivity)
  have hcentre : spineG c a 0
      = ∑ j, a j * rung c (2 * (j : ℕ)) 0 * (1 - muR c (2 * (j : ℕ)) / muR c 0) := by
    unfold spineG
    apply Finset.sum_congr rfl
    intro j _
    have hi0 : (∫ s in (-1 : ℝ)..1, rung c 0 s) = muR c 0 * rung c 0 0 :=
      Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (psi_rung h0)
    have hij := Cvs.Prolate.AngularBesselInequality.integral_eq_mu_mul (psi_rung (hS j j.2))
    have hg0 : rung c 0 0 ≠ 0 := by
      intro h
      have := Cvs.Prolate.EvenRungsByIndex.integral_rung_zero_ne hc
      rw [hi0, h, mul_zero] at this
      exact this rfl
    unfold alpha
    rw [hij, hi0]
    field_simp
  have hχ : Function.Injective (fun j : S => Cvs.Prolate.EvenRungsByIndex.lev c (2 * (j : ℕ))) := by
    intro i j hij
    dsimp only at hij
    have hi := (Cvs.Prolate.EvenRungsByIndex.lev_spec (hS i i.2)).2
    have hj := (Cvs.Prolate.EvenRungsByIndex.lev_spec (hS j j.2)).2
    rw [hij] at hi
    apply Subtype.ext
    omega
  have hB := Cvs.Prolate.AngularBesselInequality.sum_lam_mul_sq_le (Finset.univ : Finset S) hc
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.2.1)
    hχ.injOn (fun j _ => (hspec j).2.2.2.2.2)
    (fun j _ => psi_rung (hS j j.2))
  have hw : ∀ j : S, (1 - muR c (2 * (j : ℕ)) / muR c 0) ^ 2
      ≤ (1 - lamR c (2 * (j : ℕ))) ^ 2 := by
    intro j
    obtain ⟨ht, hle, h1⟩ := Cvs.Prolate.SlepianEvenOrdering.tau_le_tau_zero hc hs0.1 hs0.2.1 hs0.2.2.1 hs0.2.2.2.1
      hs0.2.2.2.2.1 (Cvs.Prolate.EvenRungsByIndex.rung_ne_zero h0)
      (hspec j).1 (hspec j).2.1 (hspec j).2.2.1 (hspec j).2.2.2.1
      (hspec j).2.2.2.2.1 (Cvs.Prolate.EvenRungsByIndex.rung_ne_zero (hS j j.2))
      (psi_rung h0) (psi_rung (hS j j.2)) (Cvs.Prolate.EvenRungsByIndex.lev_spec h0).2
      (by rw [(Cvs.Prolate.EvenRungsByIndex.lev_spec (hS j j.2)).2]; exact ⟨j, by omega⟩)
    have h := one_sub_div_sq_le_defect_sq ht.le (mul_pos hμ0 hk) hle h1
    rw [mul_div_mul_right _ _ hk.ne'] at h
    exact h
  have hsq := sq_sum_le_defect_sq_of_bessel (Finset.univ : Finset S) a
    (fun j => rung c (2 * (j : ℕ)) 0)
    (fun j => 1 - muR c (2 * (j : ℕ)) / muR c 0)
    (fun j => lamR c (2 * (j : ℕ))) hlmin (fun j _ => hw j)
    (fun j _ => hlam j j.2) hB
  rw [← hcentre] at hsq
  have hscale := mul_le_mul_of_nonneg_left hsq (sq_nonneg (2 * π / c))
  calc
    (2 * π / c) ^ 2 * spineG c a 0 ^ 2
        ≤ (2 * π / c) ^ 2 * ((∑ j, a j ^ 2 * (1 - lamR c (2 * (j : ℕ))) ^ 2)
          * (c / π / lmin)) := hscale
    _ = 4 * π / (c * lmin) * ∑ j, a j ^ 2 * (1 - lamR c (2 * (j : ℕ))) ^ 2 := by
      field_simp
      ring

/-- Connes' singleton spine has a regularization parameter bounded by its squared concentration defect. -/
theorem connes_polar_parameter_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    (2 * π / (2 * π * x)) ^ 2
        * spineG (2 * π * x) (S := {1}) (fun _ => 1) 0 ^ 2
      ≤ 8 * π / (2 * π * x) * (1 - lamR (2 * π * x) 2) ^ 2 := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx
  have h := scaled_spine_center_sq_le (by linarith : 0 < 2 * π * (x : ℝ))
    (S := {1}) (fun j hj => Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨j, Finset.mem_range.mpr (hx1 j hj)⟩)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun j hj => Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (hx1 j hj)) (fun _ => 1)
  simp only [one_pow, one_mul] at h
  rw [Finset.sum_coe_sort ({1} : Finset ℕ)
    (fun j : ℕ => (1 - lamR (2 * π * x) (2 * j)) ^ 2)] at h
  simpa only [Finset.sum_singleton, mul_one,
    show 4 * π / (2 * π * (x : ℝ) * (1 / 2)) = 8 * π / (2 * π * x) by ring] using h

/-- The Fourier profile changed by Connes' regularization carries the squared concentration defect. -/
theorem connes_fourier_regularization_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (ξ : ℝ) :
    let c := 2 * π * (x : ℝ)
    let G := spineG c (S := {1}) (fun _ => 1)
    (Cvs.L2a.AngularProlateTailPositive.psi c (Cvs.L2a.WindowFormTailLimit.regProfile c G) ξ - Cvs.L2a.AngularProlateTailPositive.psi c G ξ) ^ 2
      ≤ 8 * π / c * (1 - lamR c 2) ^ 2 * Cvs.L2a.BetaProfilePoissonTail.Psi ξ ^ 2 := by
  dsimp only
  let c := 2 * π * (x : ℝ)
  let G := spineG c (S := {1}) (fun _ => 1)
  have hc : 2 * π ≤ c := by
    dsimp only [c]
    nlinarith [Real.pi_pos, Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx]
  have hGc : ContinuousOn G (uIcc (-1 : ℝ) 1) := by
    rw [uIcc_of_le (by norm_num)]
    exact Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG c (S := {1}) (fun _ => 1)
  have hβc : ContinuousOn (Cvs.L2a.FullTailBilinearChannels.betaA c) (uIcc (-1 : ℝ) 1) := by
    unfold Cvs.L2a.FullTailBilinearChannels.betaA
    exact (continuous_const.mul (Cvs.L2a.BetaProfilePoissonTail.contDiff_beta.continuous.comp
      (continuous_id.div_const _))).continuousOn
  change (Cvs.L2a.AngularProlateTailPositive.psi c (Cvs.L2a.WindowFormTailLimit.regProfile c G) ξ - Cvs.L2a.AngularProlateTailPositive.psi c G ξ) ^ 2 ≤ _
  have he : Cvs.L2a.AngularProlateTailPositive.psi c (Cvs.L2a.WindowFormTailLimit.regProfile c G)
      = fun η => Cvs.L2a.AngularProlateTailPositive.psi c G η - (2 * π / c * G 0) * Cvs.L2a.BetaProfilePoissonTail.Psi η := by
    change Cvs.L2a.AngularProlateTailPositive.psi c (fun s => G s + -(2 * π / c * G 0) * Cvs.L2a.FullTailBilinearChannels.betaA c s) = _
    rw [Cvs.L2a.FullTailPolarisation.psi_add_smul hGc hβc, Cvs.L2a.FullTailBilinearChannels.psi_betaA hc]
    funext η
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_right (connes_polar_parameter_sq_le hx)
    (sq_nonneg (Cvs.L2a.BetaProfilePoissonTail.Psi ξ))
  calc
    (Cvs.L2a.AngularProlateTailPositive.psi c G ξ - (2 * π / c * G 0) * Cvs.L2a.BetaProfilePoissonTail.Psi ξ - Cvs.L2a.AngularProlateTailPositive.psi c G ξ) ^ 2
        = (2 * π / c) ^ 2 * G 0 ^ 2 * Cvs.L2a.BetaProfilePoissonTail.Psi ξ ^ 2 := by ring
    _ ≤ 8 * π / c * (1 - lamR c 2) ^ 2 * Cvs.L2a.BetaProfilePoissonTail.Psi ξ ^ 2 := by
      simpa only [c, G] using h

end Cvs.Approximant.SpineRegularisationDefect
