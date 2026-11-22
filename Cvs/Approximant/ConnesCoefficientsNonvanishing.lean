import Mathlib
import Cvs.Approximant.ConnesResidualFixedScale
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.QuarticHermiteWindowPhi
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Approximant.StripApproxFromHermite
import Cvs.Finite.CoefficientsAreSamples
import Cvs.Finite.RecentredTransform
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Route.JointGapFromResidual
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Xi.XiValueAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Eventual nonvanishing of the actual Connes coefficients

The unnormalized Connes transform approximates Xi at zero, whose value is
nonzero, so every sufficiently large scale has positive actual coefficient mass.
-/

noncomputable section

open Real Matrix Finset Filter MeasureTheory Set
open scoped Topology

namespace Cvs.Approximant.ConnesCoefficientsNonvanishing
open Cvs.ZeroCounting

/-- The centered even-mode transform at zero is the window length times its constant coefficient. -/
theorem ctransform_zero_evaluation {L : ℝ} (hL : 0<L) (N : ℕ)
    (ξ : Cvs.Finite.SymmetricModeSet.Idx N → ℝ) (hξ : ∀ i, ξ (Cvs.Finite.SymmetricModeSet.negI N i)=ξ i) :
    Cvs.Route.GroundRouteJointGap.ctransform L N ξ 0 = ((L*ξ none : ℝ) : ℂ) := by
  have hg := Cvs.Finite.CoefficientsAreSamples.fourierLaplace_at_grid hL (Cvs.Finite.SymmetricModeSet.negI_involutive N)
    (Cvs.Finite.SymmetricModeSet.mode_negI N) (Cvs.Finite.SymmetricModeSet.mode_injective N) hξ none
  have hω : Cvs.Finite.TruncationZeroFreeOffAxes.omega L (Cvs.Finite.SymmetricModeSet.mode N) none=0 := by
    simp [Cvs.Finite.TruncationZeroFreeOffAxes.omega, Cvs.Finite.SymmetricModeSet.mode]
  rw [hω] at hg
  simpa only [Cvs.Route.GroundRouteJointGap.ctransform, Cvs.Finite.RecentredTransform.phase, mul_zero, zero_mul, zero_div,
    neg_zero, Complex.exp_zero, one_mul, Complex.ofReal_zero, Complex.ofReal_mul] using hg

/-- The constant Connes coefficient is independent of its retained mode order. -/
theorem connesCoef_none (x : ℝ) (N : ℕ) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x N none = Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0 := by
  simp [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff]

/-- Actual Connes coefficients stay nonzero when their retained mode order increases. -/
theorem connesCoef_mass_ne_zero_mono (x : ℝ) {N J : ℕ} (hNJ : N ≤ J)
    (hN : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    Cvs.Approximant.ConnesVectorRealScale.connesCoef x J ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x J ≠ 0 := by
  intro hJ
  have hz := dotProduct_self_eq_zero.mp hJ
  have hnz : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N = 0 := by
    funext i
    rcases i with _ | ⟨k,b⟩
    · have h := congrFun hz none
      simpa only [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Finset.mem_range, Nat.zero_lt_succ,
        if_true, Pi.zero_apply] using h
    · let kj : Fin J := ⟨k.val, k.isLt.trans_le hNJ⟩
      have h := congrFun hz (some (kj,b))
      have hkN : k.val+1<N+1 := Nat.succ_lt_succ k.isLt
      have hkJ : k.val+1<J+1 := Nat.succ_lt_succ (k.isLt.trans_le hNJ)
      simpa only [Cvs.Approximant.ConnesVectorRealScale.connesCoef, Cvs.Finite.SymmetricModeSet.coeff, Finset.mem_range, kj, hkN, hkJ,
        if_true, Pi.zero_apply] using h
  apply hN
  simp only [hnz, dotProduct_zero]

/-- Above the actual truncation threshold, the constant Connes coefficient is eventually nonzero. -/
theorem eventually_connesCoef_zero_ne_zero (N : ℝ → ℕ)
    (hN : ∀ᶠ x in atTop, Cvs.Route.JointGapAtConnesVectors.connesThreshold x ≤ N x) :
    ∀ᶠ x : ℝ in atTop,
      Cvs.Approximant.ConnesVectorRealScale.connesCoef x (N x) none ≠ 0 := by
  let G : ℝ → ℝ → ℝ := fun x => Cvs.Approximant.DeepIndexSpineSpan.spineG (2*π*x) (S := {1}) fun _ => 1
  let b : ℝ → ℝ := fun x => (Cvs.Approximant.SpineNearQuarticHermite.overlap (2*π*x))⁻¹
  let β : ℝ → ℝ := fun x => 32*b x*x ^ (-(3/4 : ℝ))
  let err : ℝ → ℝ := fun x =>
    2*√(Cvs.Approximant.StripApproxFromHermite.profileErr x 0 (b x) (G x))+
      2*√(Cvs.Approximant.StripApproxFromHermite.truncErr x 0 (N x))+Cvs.Approximant.StripApproxFromHermite.windowErr x 0
  have hb : ∀ᶠ x : ℝ in atTop, 1/20*x ^ (1/4 : ℝ) ≤ |b x| := by
    filter_upwards [eventually_ge_atTop 16] with x hx
    exact Cvs.Approximant.SpineNearQuarticHermite.le_abs_inv_overlap hx
  have hclose : ∀ᶠ x : ℝ in atTop,
      ∫ u in Icc (0 : ℝ) 1, (G x u-b x*Cvs.Approximant.QuarticHermiteWindowPhi.gH (2*π*x) u)^2
        ≤ 80217/4*x ^ (-(3/2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 16] with x hx
    exact Cvs.Approximant.SpineNearQuarticHermite.integral_spineG_sub_sq_le_rpow hx
  have hNr : ∀ᶠ x : ℝ in atTop, x ^ (1/4 : ℝ) ≤ (N x : ℝ) := by
    apply hN.mono
    intro x hx
    exact (Nat.le_ceil _).trans (by exact_mod_cast hx)
  have hp := Cvs.Approximant.StripApproxFromHermite.tendsto_profileErr (a := 0) (by norm_num) G b
    (b₀ := 1/20) (C := 80217/4) (by norm_num) hb hclose
  have ht := Cvs.Approximant.StripApproxFromHermite.tendsto_truncErr (a := 0) (by norm_num) hNr
  have hw := Cvs.Approximant.StripApproxFromHermite.tendsto_windowErr (a := 0) (by norm_num)
  have herr : Tendsto err atTop (𝓝 0) := by
    have h1 := ((continuous_sqrt.tendsto 0).comp hp).const_mul 2
    have h2 := ((continuous_sqrt.tendsto 0).comp ht).const_mul 2
    have h := (h1.add h2).add hw
    simpa only [err, Function.comp_apply, sqrt_zero, mul_zero, add_zero] using h
  have hest : ∀ᶠ x : ℝ in atTop,
      ‖((2/β x : ℝ) : ℂ)*Cvs.Route.GroundRouteJointGap.ctransform (log x) (N x)
          (Cvs.Approximant.ConnesVectorRealScale.connesCoef x (N x)) 0-Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ≤ err x := by
    filter_upwards [eventually_ge_atTop (exp 1), hb] with x hx hbx
    have hx0 : 0<x := (exp_pos 1).trans_le hx
    have hb0 : 0 < |b x| := lt_of_lt_of_le (by positivity) hbx
    have hβ0 : β x ≠ 0 := mul_ne_zero
      (mul_ne_zero (by norm_num) (abs_pos.mp hb0)) (rpow_pos_of_pos hx0 _).ne'
    have hc : ContinuousOn (G x) (Icc 0 1) :=
      (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)
    exact Cvs.Approximant.StripApproxFromHermite.norm_two_div_mul_ctransform_sub_Xi_le hx rfl hβ0 hc (N x)
      (a := 0) (by norm_num) (z := 0) (by simp)
  have hXi : 0<‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ := norm_pos_iff.mpr fun h => by
    have hp := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  filter_upwards [hest, herr.eventually (gt_mem_nhds hXi),
    eventually_ge_atTop (exp 1)] with x hx he hx1 hzero
  have hL : 0<log x := log_pos ((one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx1)
  rw [ctransform_zero_evaluation hL _ _ (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x (N x)), hzero,
    mul_zero, Complex.ofReal_zero, mul_zero, zero_sub, norm_neg] at hx
  linarith

/-- Above the actual truncation threshold, the unnormalized Connes coefficient mass is eventually nonzero. -/
theorem eventually_connesCoef_mass_ne_zero (N : ℝ → ℕ)
    (hN : ∀ᶠ x in atTop, Cvs.Route.JointGapAtConnesVectors.connesThreshold x ≤ N x) :
    ∀ᶠ x : ℝ in atTop,
      Cvs.Approximant.ConnesVectorRealScale.connesCoef x (N x) ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x (N x) ≠ 0 := by
  filter_upwards [eventually_connesCoef_zero_ne_zero N hN] with x hx hz
  exact hx (congrFun (dotProduct_self_eq_zero.mp hz) none)

/-- The actual constant Connes coefficient is nonzero at every sufficiently large scale. -/
theorem eventually_connes_constantCoef_ne_zero :
    ∀ᶠ x : ℝ in atTop, Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0 ≠ 0 := by
  simpa only [connesCoef_none] using eventually_connesCoef_zero_ne_zero
    Cvs.Route.JointGapAtConnesVectors.connesThreshold (Eventually.of_forall fun _ => le_rfl)

/-- Every actual finite Connes coefficient vector is nonzero at sufficiently large scales. -/
theorem eventually_all_connesCoef_mass_ne_zero :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,
      Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0 := by
  filter_upwards [eventually_connes_constantCoef_ne_zero] with x hx N hz
  apply hx
  have h := congrFun (dotProduct_self_eq_zero.mp hz) none
  simpa only [connesCoef_none, Pi.zero_apply] using h

/-- At all sufficiently large natural scales, every actual Connes cutoff has nonzero mass. -/
theorem eventually_nat_connesCoef_mass_ne_zero :
    ∀ᶠ x : ℕ in atTop, ∀ N : ℕ,
      Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0 :=
  eventually_all_connesCoef_mass_ne_zero.natCast_atTop

/-- Every sufficiently large natural scale has a nonzero actual finite Connes coefficient vector. -/
theorem eventually_exists_connesCoef_mass_ne_zero :
    ∀ᶠ x : ℕ in atTop, ∃ N : ℕ,
      Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0 := by
  filter_upwards [eventually_nat_connesCoef_mass_ne_zero] with x hx
  exact ⟨0, hx 0⟩

/-- The complete actual coefficient mass is positive at every sufficiently large natural scale. -/
theorem eventually_coefficientMass_pos :
    ∀ᶠ x : ℕ in atTop, 0<Cvs.Approximant.ConnesResidualFixedScale.coefficientMass x := by
  have hs : ∀ᶠ x : ℕ in atTop, 80≤2*π*x := by
    filter_upwards [(eventually_ge_atTop (80/(2*π) : ℝ)).natCast_atTop] with x hx
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0<2*π)).mp hx
  filter_upwards [hs, eventually_exists_connesCoef_mass_ne_zero] with x hx hp
  exact Cvs.Approximant.ConnesResidualFixedScale.coefficientMass_pos hx hp

/-- The actual fixed-scale Connes residual limit needs no nonzero-mass premise at sufficiently large scales. -/
theorem eventually_tendsto_connes_residual :
    ∀ᶠ x : ℕ in atTop,
      Tendsto (fun N => Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (log x) N
        (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x)) atTop (𝓝 (Cvs.Approximant.ConnesResidualFixedScale.residualLimit x)) := by
  have hs : ∀ᶠ x : ℕ in atTop, 80≤2*π*x := by
    filter_upwards [(eventually_ge_atTop (80/(2*π) : ℝ)).natCast_atTop] with x hx
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0<2*π)).mp hx
  filter_upwards [hs, eventually_exists_connesCoef_mass_ne_zero] with x hx hp
  exact Cvs.Approximant.ConnesResidualFixedScale.tendsto_connes_residual hx hp

/-- The actual fixed-scale Connes Rayleigh limit needs no nonzero-mass premise at sufficiently large scales. -/
theorem eventually_tendsto_connes_rayleigh :
    ∀ᶠ x : ℕ in atTop,
      Tendsto (fun N => Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ
        (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (log x) (Cvs.Finite.SymmetricModeSet.mode N) *ᵥ
          Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x)) atTop (𝓝 (Cvs.Approximant.ConnesResidualFixedScale.rayleighLimit x)) := by
  have hs : ∀ᶠ x : ℕ in atTop, 80≤2*π*x := by
    filter_upwards [(eventually_ge_atTop (80/(2*π) : ℝ)).natCast_atTop] with x hx
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0<2*π)).mp hx
  filter_upwards [hs, eventually_exists_connesCoef_mass_ne_zero] with x hx hp
  exact Cvs.Approximant.ConnesResidualFixedScale.tendsto_connes_rayleigh hx hp

end Cvs.Approximant.ConnesCoefficientsNonvanishing
