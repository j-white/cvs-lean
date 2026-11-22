import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.QuarticHermiteWindowPhi
import Cvs.Approximant.SpineNearQuarticHermite
import Cvs.Approximant.StripApproxFromHermite
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.WindowCosineBessel
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Xi.XiValueAtOrigin

/-!
# Quantitative mass of every actual Connes cutoff

The unnormalized Xi approximation at zero bounds the actual constant coefficient.
-/

noncomputable section

open Real Matrix Finset Filter MeasureTheory Set
open scoped Topology

namespace Cvs.Approximant.ConnesCutoffMass
open Cvs.ZeroCounting

/-- The positive Xi-zero constant in the actual coefficient-mass bound. -/
def massConstant : ℝ := 4 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 / 25

theorem massConstant_pos : 0 < massConstant := by
  have hXi : Cvs.Limit.ZeroFreeApproximantsRH.Xi 0 ≠ 0 := fun h => by
    have hp := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  unfold massConstant
  positivity

private def beta (x : ℝ) : ℝ :=
  32 * (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹ * x ^ (-(3 / 4 : ℝ))

private def error (x : ℝ) : ℝ :=
  2 * √(Cvs.Approximant.StripApproxFromHermite.profileErr x 0 ((Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹)
      (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)) +
    2 * √(Cvs.Approximant.StripApproxFromHermite.truncErr x 0 (Cvs.Route.JointGapAtConnesVectors.connesThreshold x)) + Cvs.Approximant.StripApproxFromHermite.windowErr x 0

private theorem beta_sq_lower {x : ℝ} (hx : 16 ≤ x) :
    64 / (25 * x) ≤ beta x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hb := Cvs.Approximant.SpineNearQuarticHermite.le_abs_inv_overlap hx
  have hab : (8 / 5 : ℝ) * x ^ (-(1 / 2 : ℝ)) ≤ |beta x| := by
    unfold beta
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32),
      abs_of_pos (rpow_pos_of_pos hx0 _)]
    calc
      (8 / 5 : ℝ) * x ^ (-(1 / 2 : ℝ)) =
          32 * ((1 / 20 : ℝ) * x ^ (1 / 4 : ℝ)) * x ^ (-(3 / 4 : ℝ)) := by
        rw [mul_assoc, mul_assoc, ← Real.rpow_add hx0]
        norm_num
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (by norm_num)) (rpow_nonneg hx0.le _)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (8 / 5 : ℝ) *
    x ^ (-(1 / 2 : ℝ))) hab 2
  have hp : (x ^ (-(1 / 2 : ℝ))) ^ 2 = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
    exact Real.rpow_neg_one x
  have hh : (8 / 5 : ℝ) ^ 2 * x⁻¹ = 64 / (25 * x) := by ring
  simpa only [mul_pow, hp, sq_abs, hh] using hsq

private theorem tendsto_error : Tendsto error atTop (𝓝 0) := by
  let G : ℝ → ℝ → ℝ := fun x => Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1
  let b : ℝ → ℝ := fun x => (Cvs.Approximant.SpineNearQuarticHermite.overlap (2 * π * x))⁻¹
  have hb : ∀ᶠ x : ℝ in atTop, 1 / 20 * x ^ (1 / 4 : ℝ) ≤ |b x| := by
    filter_upwards [eventually_ge_atTop 16] with x hx
    exact Cvs.Approximant.SpineNearQuarticHermite.le_abs_inv_overlap hx
  have hclose : ∀ᶠ x : ℝ in atTop,
      ∫ u in Icc (0 : ℝ) 1, (G x u - b x * Cvs.Approximant.QuarticHermiteWindowPhi.gH (2 * π * x) u) ^ 2
        ≤ 80217 / 4 * x ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [eventually_ge_atTop 16] with x hx
    exact Cvs.Approximant.SpineNearQuarticHermite.integral_spineG_sub_sq_le_rpow hx
  have hNr : ∀ᶠ x : ℝ in atTop, x ^ (1 / 4 : ℝ) ≤
      (Cvs.Route.JointGapAtConnesVectors.connesThreshold x : ℝ) :=
    Eventually.of_forall fun x => Nat.le_ceil _
  have hp := Cvs.Approximant.StripApproxFromHermite.tendsto_profileErr (a := 0) (by norm_num) G b
    (b₀ := 1 / 20) (C := 80217 / 4) (by norm_num) hb hclose
  have ht := Cvs.Approximant.StripApproxFromHermite.tendsto_truncErr (a := 0) (by norm_num) hNr
  have hw := Cvs.Approximant.StripApproxFromHermite.tendsto_windowErr (a := 0) (by norm_num)
  have h1 := ((continuous_sqrt.tendsto 0).comp hp).const_mul 2
  have h2 := ((continuous_sqrt.tendsto 0).comp ht).const_mul 2
  change Tendsto (fun x => error x) atTop (𝓝 0)
  simpa only [error, G, b, Function.comp_apply, sqrt_zero, mul_zero, add_zero]
    using (h1.add h2).add hw

private def scaledZero (x : ℝ) : ℂ :=
  ((2 / beta x : ℝ) : ℂ) * Cvs.Route.GroundRouteJointGap.ctransform (log x) (Cvs.Route.JointGapAtConnesVectors.connesThreshold x)
    (Cvs.Approximant.ConnesVectorRealScale.connesCoef x (Cvs.Route.JointGapAtConnesVectors.connesThreshold x)) 0

private theorem tendsto_scaledZero : Tendsto scaledZero atTop (𝓝 (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0)) := by
  have hest : ∀ᶠ x : ℝ in atTop, ‖scaledZero x - Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ≤ error x := by
    filter_upwards [eventually_ge_atTop (max 16 (exp 1))] with x hx
    have hx16 : 16 ≤ x := (le_max_left _ _).trans hx
    have hxe : exp 1 ≤ x := (le_max_right _ _).trans hx
    have hx0 : 0 < x := by linarith
    have hβ : beta x ≠ 0 := by
      have h := beta_sq_lower hx16
      have hpos : 0 < 64 / (25 * x) := by positivity
      exact fun hz => by rw [hz, zero_pow (by norm_num)] at h; linarith
    have hc : ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1)
        (Icc 0 1) :=
      (Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)
    exact Cvs.Approximant.StripApproxFromHermite.norm_two_div_mul_ctransform_sub_Xi_le hxe rfl hβ hc _
      (a := 0) (by norm_num) (z := 0) (by simp)
  have h := squeeze_zero_norm' hest tendsto_error
  simpa only [sub_add_cancel, zero_add] using h.add_const (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0)

/-- The actual constant cosine coefficient has a quantitative lower mass at large scales. -/
theorem eventually_constantCoef_sq_lower :
    ∀ᶠ x : ℝ in atTop,
      massConstant / (x * (log x) ^ 2) ≤
        (Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0) ^ 2 := by
  have hXi : 0 < ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ := by
    have hp := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    exact norm_pos_iff.mpr fun hz => by rw [hz, Complex.zero_re] at hp; linarith
  have hnorm := continuous_norm.tendsto (Cvs.Limit.ZeroFreeApproximantsRH.Xi 0) |>.comp tendsto_scaledZero
  filter_upwards [hnorm.eventually (lt_mem_nhds (show ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ / 2 <
      ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ by linarith)), eventually_ge_atTop (max 16 (exp 1))] with x hlarge hx
  have hx16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hxe : exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := log_pos
    ((one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hxe)
  have hβsq := beta_sq_lower hx16
  have hβpos : 0 < beta x ^ 2 := lt_of_lt_of_le (by positivity) hβsq
  have hscaled : ‖scaledZero x‖ ^ 2 =
      4 * ((log x) ^ 2 * (Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0) ^ 2) /
        beta x ^ 2 := by
    rw [scaledZero, Cvs.Approximant.ConnesCoefficientsNonvanishing.ctransform_zero_evaluation hL _ _
      (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even _ _), Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, div_pow]
    ring
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ / 2) hlarge.le 2
  simp only [Function.comp_apply] at hsq
  rw [hscaled] at hsq
  have hprod := (le_div_iff₀ hβpos).mp hsq
  have hbase : ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 * beta x ^ 2 / (16 * (log x) ^ 2) ≤
      (Cvs.Finite.WindowCosineBessel.coef (log x) (Cvs.Approximant.ConnesVectorRealScale.connesK x) 0) ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * (log x) ^ 2)).mpr
    nlinarith
  calc
    massConstant / (x * (log x) ^ 2) =
        ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 * (64 / (25 * x)) / (16 * (log x) ^ 2) := by
      unfold massConstant
      field_simp [hx0.ne', hL.ne']
      ring
    _ ≤ ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 * beta x ^ 2 / (16 * (log x) ^ 2) := by gcongr
    _ ≤ _ := hbase

/-- Every finite actual Connes vector shares the constant-mode lower mass. -/
theorem eventually_all_connesCoef_mass_lower :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,
      massConstant / (x * (log x) ^ 2) ≤
        Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N := by
  filter_upwards [eventually_constantCoef_sq_lower] with x hx N
  refine hx.trans ?_
  rw [← Cvs.Approximant.ConnesCoefficientsNonvanishing.connesCoef_none x N, dotProduct]
  simpa only [pow_two] using Finset.single_le_sum
    (fun i (_hi : i ∈ (Finset.univ : Finset (Cvs.Finite.SymmetricModeSet.Idx N))) => mul_self_nonneg
      (Cvs.Approximant.ConnesVectorRealScale.connesCoef x N i)) (Finset.mem_univ (none : Cvs.Finite.SymmetricModeSet.Idx N))

/-- The same quantitative lower mass holds at all sufficiently large natural scales. -/
theorem eventually_nat_connesCoef_mass_lower :
    ∀ᶠ x : ℕ in atTop, ∀ N : ℕ,
      massConstant / ((x : ℝ) * (log x) ^ 2) ≤
        Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N :=
  eventually_all_connesCoef_mass_lower.natCast_atTop

/-- A positive scale-independent constant bounds every actual cutoff's mass from below. -/
theorem exists_eventually_all_connesCoef_mass_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,
      C / (x * (log x) ^ 2) ≤
        Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N :=
  ⟨massConstant, massConstant_pos, eventually_all_connesCoef_mass_lower⟩

end Cvs.Approximant.ConnesCutoffMass
