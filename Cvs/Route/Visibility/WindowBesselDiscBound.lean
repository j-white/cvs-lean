import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.MOnePrimeTopDepth
import Cvs.Route.Visibility.SummableBesselDisc
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window Bessel disc bound with `A = 176/π`, and (M1′) at `Θ' = ½` from the energy rate

`⟪u, U_ρ⟫² ≤ (|F_u(w_ρ)|² + |F_u(−w_ρ)|²)/2` with `w_ρ = ½ − ρ̄` (Cvs.Route.Visibility.WindowLaplaceUPairing). Each square is at most the disc mean of
`|F_u|²` on `D(±w_ρ, r₀)`, `F_u` being entire, and `SummableBesselDisc`'s overlap count and Tonelli bound each disc sum by
`88·2(δ + r₀)·M`. So `WinBesselDisc (176/π)` holds for every `δ ≤ ½`, and `WinLogReg ν` with `ν < 1` gives
`M1Prime 1` at `Θ' = ½`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Metric
open scoped InnerProductSpace ENNReal
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.Visibility.WindowLaplaceUPairing (winLaplace)
open Cvs.Route.Visibility.SummableBesselDisc (strip overlap_le sum_lintegral_le symm_equiv_real_prod)
open Cvs.StepA.Edge.CaseInfinityJointRates (M1Prime topDepth)

namespace Cvs.Route.Visibility.WindowBesselDiscBound
open Cvs.ZeroCounting

/-- **The disc sum for a continuous function**: centres with `|Re c_ρ − ½| ≤ δ` and `Im c_ρ = s·Im ρ`, `s = ±1`,
`0 < r₀ < ½`, and `∫|f(σ + ig)|² log(|g| + 7/2) dg ≤ M` (integrable) on `|σ − ½| ≤ δ + r₀` give
`Σ_ρ m_ρ ∫_{D(c_ρ, r₀)} |f|² ≤ 88·2(δ + r₀)·M` over every finite set of zeros. -/
theorem sum_ball_le {f : ℂ → ℂ} (hf : Continuous f) {δ r₀ s M : ℝ} (hδ : 0 ≤ δ)
    (hr₀ : 0 < r₀) (hr : r₀ < 1 / 2) (hs : s = 1 ∨ s = -1) (cen : nonTrivialZeroSet → ℂ)
    (hre : ∀ ρ, |(cen ρ).re - 1 / 2| ≤ δ) (him : ∀ ρ, (cen ρ).im = s * (ρ : ℂ).im)
    (hM : ∀ σ ∈ Icc (1 / 2 - (δ + r₀)) (1 / 2 + (δ + r₀)),
      Integrable (fun g : ℝ => ‖f (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2))
        ∧ ∫ g : ℝ, ‖f (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2) ≤ M)
    (F : Finset nonTrivialZeroSet) :
    ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ) * ∫ z in ball (cen ρ) r₀, ‖f z‖ ^ 2
      ≤ 88 * (2 * (δ + r₀)) * M := by
  set w := δ + r₀
  set h : ℂ → ℝ := fun z => ‖f z‖ ^ 2
  have hh0 : ∀ z, 0 ≤ h z := fun z => sq_nonneg _
  have hw0 : 0 ≤ w := by simp only [w]; linarith
  have hM0 : 0 ≤ M := by
    have hmem : (1 / 2 : ℝ) ∈ Icc (1 / 2 - w) (1 / 2 + w) := ⟨by linarith, by linarith⟩
    refine le_trans (integral_nonneg fun g => ?_) (hM _ hmem).2
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [abs_nonneg g]))
  set B : nonTrivialZeroSet → ℝ≥0∞ := fun ρ => ∫⁻ z in ball (cen ρ) r₀, ENNReal.ofReal (h z)
  have hB : ∀ ρ, ∫ z in ball (cen ρ) r₀, h z = (B ρ).toReal := fun ρ =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hh0)
      ((hf.norm.pow 2).aestronglyMeasurable.restrict)
  set Φ : ℂ → ℝ := fun z => (strip w).indicator (fun z => 88 * Real.log (|z.im| + 7 / 2)) z * h z
  have hstep : ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ ≤ ∫⁻ z, ENNReal.ofReal (Φ z) := by
    have e : ∀ ρ, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ
        = ∫⁻ z, ENNReal.ofReal ((Cvs.Criterion.divisorWeight ρ : ℝ)
            * (ball (cen ρ) r₀).indicator (fun _ => (1 : ℝ)) z * h z) := fun ρ => by
      simp only [B]
      rw [← lintegral_indicator measurableSet_ball, ← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_congr fun z => ?_
      by_cases hz : z ∈ ball (cen ρ) r₀
      · simp [indicator_of_mem hz, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      · simp [indicator_of_notMem hz]
    simp only [e]
    refine (sum_lintegral_le _ _ _).trans (lintegral_mono fun z => ?_)
    have hnn : ∀ ρ ∈ F, 0 ≤ (Cvs.Criterion.divisorWeight ρ : ℝ)
        * (ball (cen ρ) r₀).indicator (fun _ => (1 : ℝ)) z * h z := fun ρ _ => by
      have : 0 ≤ (ball (cen ρ) r₀).indicator (fun _ => (1 : ℝ)) z :=
        indicator_nonneg (fun _ _ => zero_le_one) z
      have := hh0 z; positivity
    rw [← ENNReal.ofReal_sum_of_nonneg hnn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (overlap_le F hr hs cen hre him z) (hh0 z)
  have htail : ∫⁻ z, ENNReal.ofReal (Φ z) ≤ ENNReal.ofReal (88 * M) * ENNReal.ofReal (2 * w) := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding, Measure.volume_eq_prod]
    refine (lintegral_prod_le _).trans ?_
    have hin : ∀ σ : ℝ, ∫⁻ g : ℝ, ENNReal.ofReal (Φ (Complex.measurableEquivRealProd.symm (σ, g)))
        ≤ (Icc (1 / 2 - w) (1 / 2 + w)).indicator (fun _ => ENNReal.ofReal (88 * M)) σ := fun σ => by
      simp only [symm_equiv_real_prod]
      have hre' : ∀ g : ℝ, ((σ : ℂ) + g * I).re = σ := fun g => by simp
      have him' : ∀ g : ℝ, ((σ : ℂ) + g * I).im = g := fun g => by simp
      by_cases hσ : σ ∈ Icc (1 / 2 - w) (1 / 2 + w)
      · rw [indicator_of_mem hσ]
        have hmem : ∀ g : ℝ, (σ : ℂ) + g * I ∈ strip w := fun g => by
          show |((σ : ℂ) + g * I).re - 1 / 2| ≤ w
          rw [hre', abs_le]; constructor <;> linarith [hσ.1, hσ.2]
        obtain ⟨hI, hle⟩ := hM σ hσ
        have e : ∀ g : ℝ, Φ ((σ : ℂ) + g * I)
            = 88 * (‖f (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2)) := fun g => by
          simp only [Φ, h, indicator_of_mem (hmem g), him']; ring
        simp only [e]
        rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul 88) (ae_of_all _ fun g =>
          mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
            (Real.log_nonneg (by linarith [abs_nonneg g]))))]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]; linarith
      · rw [indicator_of_notMem hσ]
        have hnot : ∀ g : ℝ, (σ : ℂ) + g * I ∉ strip w := fun g hg => by
          apply hσ
          have : |((σ : ℂ) + g * I).re - 1 / 2| ≤ w := hg
          rw [hre', abs_le] at this
          exact ⟨by linarith, by linarith⟩
        simp [Φ, indicator_of_notMem (hnot _)]
    refine (lintegral_mono hin).trans_eq ?_
    rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    congr 2; ring
  have key : ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ ≤ ENNReal.ofReal (88 * (2 * w) * M) := by
    refine hstep.trans (htail.trans_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  have hfin : ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top key
  have hterm : ∀ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ ≠ ⊤ := fun ρ hρ =>
    ne_top_of_le_ne_top hfin
      (Finset.single_le_sum (f := fun ρ => (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ) (fun _ _ => zero_le) hρ)
  have hreal : ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ) * ∫ z in ball (cen ρ) r₀, ‖f z‖ ^ 2
      = (∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ≥0∞) * B ρ).toReal := by
    rw [ENNReal.toReal_sum hterm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← hB ρ]
  rw [hreal]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top key).trans_eq ?_
  exact ENNReal.toReal_ofReal (by positivity)

/-- **The pairing at a zero is bounded by two window values**: `⟪u, U_ρ⟫² ≤ (|F_u(w)|² + |F_u(−w)|²)/2` with
`w = (½ − Re ρ) + i Im ρ`. -/
theorem sq_inner_ueVec_le {x : ℕ} (hx0 : (0 : ℝ) < x) (u : Dom x) (ρ : nonTrivialZeroSet) :
    ⟪u, Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ (‖winLaplace u ((1 / 2 - (ρ : ℂ).re : ℝ) + (ρ : ℂ).im * I)‖ ^ 2
          + ‖winLaplace u (-((1 / 2 - (ρ : ℂ).re : ℝ) + (ρ : ℂ).im * I))‖ ^ 2) / 2 := by
  rw [Cvs.Route.Visibility.WindowLaplaceUPairing.inner_ueVec_eq_re hx0 u]
  have hz : (Cvs.ZeroCounting.zPoint ρ).im = 1 / 2 - (ρ : ℂ).re ∧ (Cvs.ZeroCounting.zPoint ρ).re = (ρ : ℂ).im := by
    simp only [Cvs.ZeroCounting.zPoint]; constructor <;> simp
  rw [hz.1, hz.2]
  set a := winLaplace u ((1 / 2 - (ρ : ℂ).re : ℝ) + (ρ : ℂ).im * I)
  set b := winLaplace u (-((1 / 2 - (ρ : ℂ).re : ℝ) + (ρ : ℂ).im * I))
  have h1 : |((a + b) / 2).re| ≤ (‖a‖ + ‖b‖) / 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [sq_abs] at h2
  have h3 : ((‖a‖ + ‖b‖) / 2) ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  linarith

/-- **The window Bessel disc bound with `A = 176/π`**, at every `δ` (`ZeroDensityTail`'s local count, `ExteriorTransformHolomorphy`'s disc mean). -/
theorem winBesselDisc : Cvs.Route.Visibility.MOnePrimeTopDepth.WinBesselDisc (176 / π) := by
  intro x hx0 u δ r₀ hδ hr₀ hr hdel M hM
  set f : ℂ → ℂ := fun z => winLaplace u (z - 1 / 2)
  have hfd : Differentiable ℂ f := (Cvs.Route.Visibility.WindowLaplaceUPairing.differentiable_winLaplace u).comp (differentiable_id.sub_const _)
  have hfc : Continuous f := hfd.continuous
  have hM' : ∀ σ ∈ Icc (1 / 2 - (δ + r₀)) (1 / 2 + (δ + r₀)),
      Integrable (fun g : ℝ => ‖f (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2))
        ∧ ∫ g : ℝ, ‖f (σ + g * I)‖ ^ 2 * Real.log (|g| + 7 / 2) ≤ M := fun σ hσ => by
    have hσ' : σ - 1 / 2 ∈ Icc (-(δ + r₀)) (δ + r₀) := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have e : ∀ g : ℝ, f (σ + g * I) = winLaplace u (((σ - 1 / 2 : ℝ) : ℂ) + g * I) := fun g => by
      simp only [f]; congr 1; push_cast; ring
    simp only [e]
    exact hM _ hσ'
  -- the two centre families, shifted by `½`
  set c₁ : nonTrivialZeroSet → ℂ := fun ρ => (((1 / 2 - (ρ : ℂ).re : ℝ) : ℂ) + (ρ : ℂ).im * I) + 1 / 2
  set c₂ : nonTrivialZeroSet → ℂ := fun ρ => -(((1 / 2 - (ρ : ℂ).re : ℝ) : ℂ) + (ρ : ℂ).im * I) + 1 / 2
  have hre1 : ∀ ρ, |(c₁ ρ).re - 1 / 2| ≤ δ := fun ρ => by
    have := hdel ρ; simp only [Cvs.GaussKernel.del] at this
    simp only [c₁]; simp
    rw [show (2⁻¹ : ℝ) - (ρ : ℂ).re = -((ρ : ℂ).re - 1 / 2) by ring, abs_neg]; exact this
  have hre2 : ∀ ρ, |(c₂ ρ).re - 1 / 2| ≤ δ := fun ρ => by
    have := hdel ρ; simp only [Cvs.GaussKernel.del] at this
    simp only [c₂]; simp
    rw [show (ρ : ℂ).re - (2⁻¹ : ℝ) = (ρ : ℂ).re - 1 / 2 by ring]; exact this
  have him1 : ∀ ρ, (c₁ ρ).im = 1 * (ρ : ℂ).im := fun ρ => by simp [c₁]
  have him2 : ∀ ρ, (c₂ ρ).im = -1 * (ρ : ℂ).im := fun ρ => by simp [c₂]
  have hS1 := sum_ball_le hfc hδ hr₀ hr (Or.inl rfl) c₁ hre1 him1 hM'
  have hS2 := sum_ball_le hfc hδ hr₀ hr (Or.inr rfl) c₂ hre2 him2 hM'
  set κ := (π * r₀ ^ 2)⁻¹
  have hκ : 0 ≤ κ := by positivity
  have hpt : ∀ ρ : nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪u, Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ κ / 2 * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (∫ z in ball (c₁ ρ) r₀, ‖f z‖ ^ 2)
          + (Cvs.Criterion.divisorWeight ρ : ℝ) * ∫ z in ball (c₂ ρ) r₀, ‖f z‖ ^ 2) := fun ρ => by
    have h := sq_inner_ueVec_le hx0 u ρ
    have b1 := Cvs.Route.Visibility.WindowLaplaceUPairing.norm_sq_winLaplace_le_ball u
      ((((1 / 2 - (ρ : ℂ).re : ℝ) : ℂ) + (ρ : ℂ).im * I)) hr₀
    have b2 := Cvs.Route.Visibility.WindowLaplaceUPairing.norm_sq_winLaplace_le_ball u
      (-((((1 / 2 - (ρ : ℂ).re : ℝ) : ℂ) + (ρ : ℂ).im * I))) hr₀
    have t : ∀ c : ℂ, ∫ z in ball c r₀, ‖winLaplace u z‖ ^ 2 = ∫ z in ball (c + 1 / 2) r₀, ‖f z‖ ^ 2 :=
      fun c => by
        have := (measurePreserving_add_right (volume : Measure ℂ) (1 / 2)).setIntegral_preimage_emb
          (measurableEmbedding_addRight (1 / 2)) (fun z => ‖f z‖ ^ 2) (ball (c + 1 / 2) r₀)
        rw [← this, preimage_add_right_ball, add_sub_cancel_right]
        simp [f]
    rw [t] at b1 b2
    have hm : (0 : ℝ) ≤ Cvs.Criterion.divisorWeight ρ := Nat.cast_nonneg _
    calc _ ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * ((‖winLaplace u ((1 / 2 - (ρ : ℂ).re : ℝ) + (ρ : ℂ).im * I)‖ ^ 2
          + ‖winLaplace u (-((1 / 2 - (ρ : ℂ).re : ℝ) + (ρ : ℂ).im * I))‖ ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h hm
      _ ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * ((κ * (∫ z in ball (c₁ ρ) r₀, ‖f z‖ ^ 2)
            + κ * ∫ z in ball (c₂ ρ) r₀, ‖f z‖ ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hm
          exact div_le_div_of_nonneg_right (add_le_add b1 b2) (by norm_num)
      _ = _ := by ring
  have hbound : ∀ F : Finset nonTrivialZeroSet, ∑ ρ ∈ F, (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪u, Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
      ≤ 176 / π * (δ + r₀) / r₀ ^ 2 * M := fun F => by
    refine (Finset.sum_le_sum fun ρ _ => hpt ρ).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have := add_le_add (hS1 F) (hS2 F)
    calc _ ≤ κ / 2 * (88 * (2 * (δ + r₀)) * M + 88 * (2 * (δ + r₀)) * M) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by simp only [κ]; field_simp; ring
  have hnn : 0 ≤ fun ρ : nonTrivialZeroSet => (Cvs.Criterion.divisorWeight ρ : ℝ)
        * ⟪u, Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2 := fun ρ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩

/-- **(M1′) at every top depth from the energy rate**: `WinLogReg ν` with `ν < m` gives `M1Prime m`. -/
theorem m1Prime_of_winLogReg {ν m : ℝ} (hR : Cvs.Route.Visibility.MOnePrimeTopDepth.WinLogReg ν) (hνm : ν < m) : M1Prime m :=
  Cvs.Route.Visibility.MOnePrimeTopDepth.m1Prime_of_win (by positivity) winBesselDisc hR hνm

/-- **(M1′) at `Θ' = ½` from the energy rate**: `WinLogReg ν` with `ν < 1` gives `M1Prime 1` when `Θ' = ½`. -/
theorem m1PrimeHalf_of_winLogReg {ν : ℝ} (hR : Cvs.Route.Visibility.MOnePrimeTopDepth.WinLogReg ν) (hν : ν < 1) : topDepth = 1 / 2 → M1Prime 1 :=
  fun _ => m1Prime_of_winLogReg hR hν

end Cvs.Route.Visibility.WindowBesselDiscBound

end
