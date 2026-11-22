import Mathlib
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.ProlateAliasSumLaw
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RightEdgePoissonSplit
import Cvs.Prolate.Mellin.RungUnitCircleLaw
import Cvs.Prolate.Mellin.RungWindowLawRightEdge
import Cvs.Prolate.Mellin.UnitCircleMellinSolution
import Cvs.Prolate.RungProfileEntireExtension
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Upstream.PeriodicAliasingIdentity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ray transform of a trapezoid error as an alias series

For entire `F` and `Im w > 0` put `Φ_w(t) = T_{F(t·)}(w)`. Differentiation under the ray integral makes `Φ_w`
smooth in `t`, Fubini gives `T_{S_F}(w) = (1/x)Σ_{n ≤ x}Φ_w(n/x) − ∫_0^1 Φ_w − (Φ_w(1) − Φ_w(0))/(2x)`, and for
even `F` the aliasing identity Cvs.Upstream.PeriodicAliasingIdentity gives `T_{S_F}(w) = Σ_{m ≥ 1} ∫_{−1}^{1} Φ_w(t) cos(2πxmt) dt`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.EvenRungsByIndex (rung)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.Prolate.Mellin.ProlateAliasSumLaw (trapErr)

namespace Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries
open Cvs.ZeroCounting

/-- The ray transform of the dilate: `Φ_w(t) = T_{F(t·)}(w)`. -/
def phiW (F : ℂ → ℂ) (w : ℂ) (t : ℝ) : ℂ := rayT (fun z => F (t * z)) w

/-- The ray integrand `F(e^{−is}) e^{−is/2} e^{iws}`. -/
def integrand (F : ℂ → ℂ) (w : ℂ) (s : ℝ) : ℂ :=
  F (Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I))

theorem rayT_eq_integral (F : ℂ → ℂ) (w : ℂ) : rayT F w = ∫ s in Ioi (0 : ℝ), integrand F w s := rfl

theorem continuous_integrand {F : ℂ → ℂ} (hF : Continuous F) (w : ℂ) : Continuous (integrand F w) := by
  unfold integrand; fun_prop

/-- A continuous function is bounded on a closed disc. -/
theorem exists_bound_ball {G : ℂ → ℂ} (hG : Continuous G) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℂ, ‖u‖ ≤ R → ‖G u‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hG.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun u hu => (hB u (by simpa using hu)).trans (le_max_left _ _)⟩

/-- **Differentiation under the ray integral**: for continuous `K`, entire `G` and `Im w > 0`,
`d/dt T_{K·G(t·)}(w) = T_{K·(z G′(tz))}(w)`. -/
theorem hasDerivAt_rayT_dilate {K G : ℂ → ℂ} (hK : Continuous K) (hG : Differentiable ℂ G) {w : ℂ}
    (hw : 0 < w.im) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => rayT (fun z => K z * G (t * z)) w)
      (rayT (fun z => K z * (z * deriv G (t₀ * z))) w) t₀ := by
  have hdG : Continuous (deriv G) := (Cvs.Prolate.Mellin.UnitCircleMellinSolution.deriv_differentiable hG).continuous
  obtain ⟨BK, hBK0, hBK⟩ := Cvs.Prolate.Mellin.RayTransformEdgeSum.exists_bound_circle hK
  obtain ⟨BG, hBG0, hBG⟩ := exists_bound_ball hdG (|t₀| + 1)
  have hcont : ∀ t : ℝ, Continuous fun z : ℂ => K z * G (t * z) := fun t =>
    hK.mul (hG.continuous.comp (by fun_prop))
  have hcont' : ∀ t : ℝ, Continuous fun z : ℂ => K z * (z * deriv G (t * z)) := fun t =>
    hK.mul (continuous_id.mul (hdG.comp (by fun_prop)))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (t : ℝ) (s : ℝ) => integrand (fun z => K z * G (t * z)) w s)
    (F' := fun (t : ℝ) (s : ℝ) => integrand (fun z => K z * (z * deriv G (t * z))) w s)
    (x₀ := t₀) (bound := fun s => BK * BG * Real.exp (-w.im * s))
    (Metric.ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t => (continuous_integrand (hcont t) w).aestronglyMeasurable)
    (Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand (hcont t₀) hw)
    ((continuous_integrand (hcont' t₀) w).aestronglyMeasurable)
    (Eventually.of_forall fun s t ht => by
      have ht' : |t| ≤ |t₀| + 1 := by
        have := Metric.mem_ball.1 ht
        rw [Real.dist_eq] at this
        have h1 := abs_sub_abs_le_abs_sub t t₀
        linarith
      unfold integrand
      rw [Cvs.Prolate.Mellin.RayTransformEdgeSum.norm_integrand (fun z => K z * (z * deriv G (↑t * z))) w s, neg_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [norm_mul, norm_mul]
      have hz : ‖Complex.exp (-(s * I))‖ = 1 := Cvs.Prolate.Mellin.UnitCircleMellinSolution.norm_zc s
      have hu : ‖(t : ℂ) * Complex.exp (-(s * I))‖ ≤ |t₀| + 1 := by
        rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact ht'
      rw [hz, one_mul]
      exact mul_le_mul (hBK s) (hBG _ hu) (norm_nonneg _) hBK0)
    (((exp_neg_integrableOn_Ioi 0 hw).const_mul (BK * BG)))
    (Eventually.of_forall fun s t _ => by
      unfold integrand
      have hz := Complex.exp (-(s * I))
      have h1 : HasDerivAt (fun u : ℂ => G (u * Complex.exp (-(s * I))))
          (deriv G (t * Complex.exp (-(s * I))) * Complex.exp (-(s * I))) (t : ℂ) :=
        (hG _).hasDerivAt.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const _ |>.congr_deriv (by simp))
      have h2 := h1.comp_ofReal
      have h3 := ((h2.const_mul (K (Complex.exp (-(s * I))))).mul_const
        (Complex.exp (-(s * I / 2)))).mul_const (Complex.exp (w * (s * I)))
      convert h3 using 1 <;> first | rfl | (beta_reduce; ring))
  exact key.2

/-- The dilate transform is continuous in `t`. -/
theorem continuous_rayT_dilate {K G : ℂ → ℂ} (hK : Continuous K) (hG : Differentiable ℂ G) {w : ℂ}
    (hw : 0 < w.im) : Continuous fun t : ℝ => rayT (fun z => K z * G (t * z)) w :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_rayT_dilate hK hG hw t).continuousAt

/-- `Φ_w` is even when `F` is. -/
theorem phiW_neg {F : ℂ → ℂ} (heven : ∀ z, F (-z) = F z) (w : ℂ) (t : ℝ) : phiW F w (-t) = phiW F w t := by
  unfold phiW
  congr 1
  funext z
  rw [Complex.ofReal_neg, neg_mul, heven]

/-- The three derivatives of `Φ_w`. -/
theorem phiW_derivs {F : ℂ → ℂ} (hF : Differentiable ℂ F) {w : ℂ} (hw : 0 < w.im) :
    (∀ t : ℝ, HasDerivAt (phiW F w) (rayT (fun z => z * deriv F (t * z)) w) t) ∧
    (∀ t : ℝ, HasDerivAt (fun t : ℝ => rayT (fun z => z * deriv F (t * z)) w)
      (rayT (fun z => z * (z * deriv (deriv F) (t * z))) w) t) ∧
    Continuous fun t : ℝ => rayT (fun z => z * (z * deriv (deriv F) (t * z))) w := by
  have hdF := Cvs.Prolate.Mellin.UnitCircleMellinSolution.deriv_differentiable hF
  have hddF := Cvs.Prolate.Mellin.UnitCircleMellinSolution.deriv_differentiable hdF
  refine ⟨fun t => ?_, fun t => ?_, ?_⟩
  · have h := hasDerivAt_rayT_dilate (K := fun _ => 1) continuous_const hF hw t
    simp only [one_mul] at h
    exact h
  · exact hasDerivAt_rayT_dilate (K := fun z => z) continuous_id hdF hw t
  · have h := continuous_rayT_dilate (K := fun z => z * z) (continuous_id.mul continuous_id) hddF hw
    exact h.congr fun t => by
      rw [show (fun z : ℂ => z * z * deriv (deriv F) (↑t * z)) = fun z => z * (z * deriv (deriv F) (↑t * z))
        from funext fun z => by ring]

/-- The integral part of the trapezoid error is continuous. -/
theorem continuous_intDilate {F : ℂ → ℂ} (hF : Continuous F) :
    Continuous fun ζ : ℂ => ∫ t in (0 : ℝ)..1, F (t * ζ) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (ζ : ℂ) (t : ℝ) => F (t * ζ)) (hF.comp (by fun_prop)) 0 1

/-- **Fubini for the integral part**: `T_{∫_0^1 F(t·)dt}(w) = ∫_0^1 Φ_w(t) dt`. -/
theorem rayT_intDilate {F : ℂ → ℂ} (hF : Continuous F) {w : ℂ} (hw : 0 < w.im) :
    rayT (fun ζ => ∫ t in (0 : ℝ)..1, F (t * ζ)) w = ∫ t in (0 : ℝ)..1, phiW F w t := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_ball hF 1
  unfold phiW
  simp only [rayT_eq_integral, integrand]
  have hswap := intervalIntegral_integral_swap (a := 0) (b := 1) (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun (t : ℝ) (s : ℝ) => F (t * Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2))
      * Complex.exp (w * (s * I))) ?_
  · rw [hswap]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  · have hmeas : AEStronglyMeasurable (Function.uncurry fun (t : ℝ) (s : ℝ) => F (t * Complex.exp (-(s * I)))
        * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I)))
        ((volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      (Continuous.aestronglyMeasurable (by
        unfold Function.uncurry
        exact ((hF.comp (by fun_prop)).mul (by fun_prop)).mul (by fun_prop)))
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := by
      rw [uIoc_of_le zero_le_one]; infer_instance
    have hdom := (integrable_const (μ := volume.restrict (uIoc (0 : ℝ) 1)) B).mul_prod
      (exp_neg_integrableOn_Ioi 0 hw)
    have hae : ∀ᵐ z ∂((volume.restrict (uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))),
        z.1 ∈ uIoc (0 : ℝ) 1 := by
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_Ioi)] with z hz using hz.1
    refine hdom.mono' hmeas (hae.mono fun z hz => ?_)
    obtain ⟨t, s⟩ := z
    have ht : |t| ≤ 1 := by
      rw [uIoc_of_le zero_le_one] at hz
      rw [abs_of_pos hz.1]; exact hz.2
    have h := Cvs.Prolate.Mellin.RayTransformEdgeSum.norm_integrand (fun z => F (t * z)) w s
    simp only [Function.uncurry]
    rw [h, neg_mul]
    refine mul_le_mul_of_nonneg_right (hB _ ?_) (Real.exp_pos _).le
    rw [norm_mul, show ‖Complex.exp (-(s * I))‖ = 1 from Cvs.Prolate.Mellin.UnitCircleMellinSolution.norm_zc s, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact ht

/-- **Fubini with a weight**: `T_{∫_{−1}^{1} F(t·)k(t)dt}(w) = ∫_{−1}^{1} Φ_w(t)k(t) dt` for continuous `F`, `k`. -/
theorem rayT_weighted {F : ℂ → ℂ} (hF : Continuous F) {k : ℝ → ℂ} (hk : Continuous k) {w : ℂ}
    (hw : 0 < w.im) :
    rayT (fun ζ => ∫ t in (-1 : ℝ)..1, F (t * ζ) * k t) w = ∫ t in (-1 : ℝ)..1, phiW F w t * k t := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_ball hF 1
  obtain ⟨Bk, hBk⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hk.continuousOn
  unfold phiW
  simp only [rayT_eq_integral, integrand]
  have hswap := intervalIntegral_integral_swap (a := -1) (b := 1) (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun (t : ℝ) (s : ℝ) => F (t * Complex.exp (-(s * I))) * k t * Complex.exp (-(s * I / 2))
      * Complex.exp (w * (s * I))) ?_
  · have e1 : ∀ s : ℝ, (∫ t in (-1 : ℝ)..1, F (t * Complex.exp (-(s * I))) * k t) * Complex.exp (-(s * I / 2))
        * Complex.exp (w * (s * I)) = ∫ t in (-1 : ℝ)..1, F (t * Complex.exp (-(s * I))) * k t
          * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I)) := fun s => by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
    have e2 : ∀ t : ℝ, (∫ s in Ioi (0 : ℝ), F (t * Complex.exp (-(s * I))) * Complex.exp (-(s * I / 2))
        * Complex.exp (w * (s * I))) * k t = ∫ s in Ioi (0 : ℝ), F (t * Complex.exp (-(s * I))) * k t
          * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I)) := fun t => by
      rw [← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      ring
    simp_rw [e1, e2]
    exact hswap.symm
  · have hmeas : AEStronglyMeasurable (Function.uncurry fun (t : ℝ) (s : ℝ) => F (t * Complex.exp (-(s * I)))
        * k t * Complex.exp (-(s * I / 2)) * Complex.exp (w * (s * I)))
        ((volume.restrict (uIoc (-1 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      (Continuous.aestronglyMeasurable (by
        unfold Function.uncurry
        exact (((hF.comp (by fun_prop)).mul (hk.comp continuous_fst)).mul (by fun_prop)).mul (by fun_prop)))
    have : IsFiniteMeasure (volume.restrict (uIoc (-1 : ℝ) 1)) := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; infer_instance
    have hdom := (integrable_const (μ := volume.restrict (uIoc (-1 : ℝ) 1)) (B * Bk)).mul_prod
      (exp_neg_integrableOn_Ioi 0 hw)
    have hae : ∀ᵐ z ∂((volume.restrict (uIoc (-1 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))),
        z.1 ∈ uIoc (-1 : ℝ) 1 := by
      rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_Ioi)] with z hz using hz.1
    refine hdom.mono' hmeas (hae.mono fun z hz => ?_)
    obtain ⟨t, s⟩ := z
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hz
    have ht : |t| ≤ 1 := abs_le.2 ⟨hz.1.le, hz.2⟩
    have h := Cvs.Prolate.Mellin.RayTransformEdgeSum.norm_integrand (fun z => F (t * z) * k t) w s
    simp only [Function.uncurry]
    rw [h, neg_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right (mul_le_mul (hB _ ?_) (hBk t ⟨hz.1.le, hz.2⟩) (norm_nonneg _) hB0)
      (Real.exp_pos _).le
    rw [norm_mul, show ‖Complex.exp (-(s * I))‖ = 1 from Cvs.Prolate.Mellin.UnitCircleMellinSolution.norm_zc s, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    exact ht

/-! ### Linearity of the ray transform -/

theorem rayT_sub' {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g) {w : ℂ} (hw : 0 < w.im) :
    rayT (fun z => f z - g z) w = rayT f w - rayT g w := by
  simp only [rayT_eq_integral]
  have hf' : IntegrableOn (integrand f w) (Ioi 0) := Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand hf hw
  have hg' : IntegrableOn (integrand g w) (Ioi 0) := Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand hg hw
  rw [← integral_sub hf' hg']
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  unfold integrand; ring

theorem rayT_const_mul (a : ℂ) (f : ℂ → ℂ) (w : ℂ) : rayT (fun z => a * f z) w = a * rayT f w := by
  simp only [rayT_eq_integral]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  unfold integrand; ring

theorem rayT_div_const (a : ℂ) (f : ℂ → ℂ) (w : ℂ) : rayT (fun z => f z / a) w = rayT f w / a := by
  simp only [rayT_eq_integral]
  rw [← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  unfold integrand; ring

theorem rayT_finset_sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i, Continuous (f i)) {w : ℂ}
    (hw : 0 < w.im) : rayT (fun z => ∑ i ∈ S, f i z) w = ∑ i ∈ S, rayT (f i) w := by
  simp only [rayT_eq_integral]
  have hf' : ∀ i, IntegrableOn (integrand (f i) w) (Ioi 0) := fun i => Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand (hf i) hw
  rw [← integral_finsetSum S fun i _ => hf' i]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  unfold integrand
  rw [Finset.sum_mul, Finset.sum_mul]

/-! ### The trapezoid error on the Mellin side -/

/-- **The transform of a trapezoid error is the trapezoid error of the transform**:
`T_{S_F}(w) = (1/x)Σ_{n ≤ x} Φ_w(n/x) − ∫_0^1 Φ_w − (Φ_w(1) − Φ_w(0))/(2x)`. -/
theorem rayT_trapErr {F : ℂ → ℂ} (hF : Continuous F) (x : ℕ) {w : ℂ} (hw : 0 < w.im) :
    rayT (trapErr x F) w = 1 / x * ∑ n ∈ Finset.Icc 1 x, phiW F w (n / x)
      - (∫ t in (0 : ℝ)..1, phiW F w t) - (phiW F w 1 - phiW F w 0) / (2 * x) := by
  have hn : ∀ n : ℕ, Continuous fun z : ℂ => F (n / x * z) := fun n => hF.comp (by fun_prop)
  have hS : Continuous fun z : ℂ => ∑ n ∈ Finset.Icc 1 x, F (n / x * z) :=
    continuous_finsetSum _ fun n _ => hn n
  have hI := continuous_intDilate hF
  have hE : Continuous fun z : ℂ => (F z - F 0) / (2 * x) := (hF.sub continuous_const).div_const _
  have e : trapErr x F = fun z => (1 / (x : ℂ) * ∑ n ∈ Finset.Icc 1 x, F (n / x * z)
      - ∫ t in (0 : ℝ)..1, F (t * z)) - (F z - F 0) / (2 * x) := rfl
  rw [e, rayT_sub' (f := fun z => 1 / (x : ℂ) * ∑ n ∈ Finset.Icc 1 x, F (n / x * z)
      - ∫ t in (0 : ℝ)..1, F (t * z)) (g := fun z => (F z - F 0) / (2 * x))
      ((continuous_const.mul hS).sub hI) hE hw,
    rayT_sub' (f := fun z => 1 / (x : ℂ) * ∑ n ∈ Finset.Icc 1 x, F (n / x * z))
      (g := fun z => ∫ t in (0 : ℝ)..1, F (t * z)) (continuous_const.mul hS) hI hw,
    rayT_const_mul, rayT_finset_sum _ hn hw, rayT_intDilate hF hw,
    rayT_div_const (2 * x) (fun z => F z - F 0),
    rayT_sub' (f := F) (g := fun _ => F 0) hF continuous_const hw]
  have h1 : ∀ n : ℕ, rayT (fun z => F (n / x * z)) w = phiW F w (n / x) := fun n => by
    unfold phiW; push_cast; rfl
  have h2 : rayT F w = phiW F w 1 := by unfold phiW; simp
  have h3 : rayT (fun _ => F 0) w = phiW F w 0 := by unfold phiW; simp
  simp_rw [h1]
  rw [h2, h3]

/-- **The alias series on the Mellin side**: for entire even `F`, `x ≥ 1` and `Im w > 0`,
`T_{S_F}(w) = Σ_{m ≥ 1} ∫_{−1}^{1} Φ_w(t) cos(2πxmt) dt`. -/
theorem hasSum_rayT_trapErr {F : ℂ → ℂ} (hF : Differentiable ℂ F) (heven : ∀ z, F (-z) = F z) {x : ℕ}
    (hx : 0 < x) {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun m : ℕ => ∫ t in (-1 : ℝ)..1, phiW F w t * Complex.cos (2 * π * x * (m + 1) * t))
      (rayT (trapErr x F) w) := by
  obtain ⟨d1, d2, c2⟩ := phiW_derivs hF hw
  rw [rayT_trapErr hF.continuous x hw]
  exact Cvs.Upstream.PeriodicAliasingIdentity.hasSum_alias_even (fun t _ => d1 t) (fun t _ => d2 t) c2.continuousOn
    (fun t _ => phiW_neg heven w t) hx

/-! ### The alias terms of a single prolate profile -/

/-- `H_k` is even. -/
theorem Hk_neg (c : ℝ) (k : ℕ) (z : ℂ) : Hk c k (-z) = Hk c k z := by
  unfold Hk; rw [Cvs.Prolate.Mellin.RightEdgePoissonSplit.psiC_neg]

/-- The `m`-th alias term `P_m(w) = ∫_{−1}^{1} Φ_w(t) cos(2πx(m + 1)t) dt` of the profile `H_{4j}`. -/
def aliasTerm (x j : ℕ) (w : ℂ) (m : ℕ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, phiW (Hk (2 * π * x) (2 * j)) w t * Complex.cos (2 * π * x * (m + 1) * t)

/-- **The single-profile alias series**: `T_{S_{H_{4j}}}(w) = Σ_{m ≥ 0} P_m(w)` on `Im w > 0`. -/
theorem hasSum_aliasTerm {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {w : ℂ} (hw : 0 < w.im) :
    HasSum (aliasTerm x j w) (rayT (trapErr x (Hk (2 * π * x) (2 * j))) w) := by
  obtain ⟨hA, -, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.zero_le _) hj
  exact hasSum_rayT_trapErr (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA) (Hk_neg _ _) hx0 hw

/-- **Each alias term is a ray transform**: `P_m(w) = T_{W_m}(w)` with
`W_m(ζ) = ∫_{−1}^{1} H_{4j}(tζ) cos(2πx(m + 1)t) dt`. -/
theorem aliasTerm_eq_rayT {x j : ℕ} (hx : 80 ≤ 2 * π * x) (hj : j < x) {w : ℂ} (hw : 0 < w.im) (m : ℕ) :
    aliasTerm x j w m = rayT (fun ζ => ∫ t in (-1 : ℝ)..1,
      Hk (2 * π * x) (2 * j) (t * ζ) * Complex.cos (2 * π * x * (m + 1) * t)) w := by
  obtain ⟨hA, -, -⟩ := Cvs.Prolate.Mellin.RungUnitCircleLaw.rung_data hx hj
  unfold aliasTerm
  exact (rayT_weighted (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hA).continuous (by fun_prop) hw).symm

/-- **The absolute alias law**: some subpolynomial `C` has, at all large `x`, for every `j < x`, `|σ| ≤ 1`,
`g ≥ 8πx` and `N`, `Σ_{m < N} g‖P_m(σ + ig)‖ ≤ C(x)|h_{4j}(1)|/√x`. -/
def AbsAliasLaw : Prop :=
  ∃ C : ℕ → ℝ, SubPoly C ∧ ∀ᶠ x : ℕ in atTop, ∀ j : ℕ, j < x → ∀ σ : ℝ, |σ| ≤ 1 → ∀ g : ℝ, 8 * π * x ≤ g →
    ∀ N : ℕ, ∑ m ∈ Finset.range N, g * ‖aliasTerm x j (σ + g * I) m‖
      ≤ C x * |rung (2 * π * x) (2 * j) 1| / √(x : ℝ)

/-- A series whose partial sums of norms stay below `B` has sum of norm at most `B`. -/
theorem norm_le_of_hasSum {a : ℕ → ℂ} {S : ℂ} (h : HasSum a S) {B : ℝ}
    (hB : ∀ N : ℕ, ∑ m ∈ Finset.range N, ‖a m‖ ≤ B) : ‖S‖ ≤ B := by
  have ht := (continuous_norm.tendsto S).comp h.tendsto_sum_nat
  refine le_of_tendsto' ht fun N => ?_
  exact (norm_sum_le _ _).trans (hB N)

/-- **The absolute alias law gives the single-profile law**. -/
theorem prolateAliasLaw_of_absAliasLaw (h : AbsAliasLaw) : Cvs.Prolate.Mellin.ProlateAliasSumLaw.ProlateAliasLaw := by
  obtain ⟨C, hC, hL⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hL, Cvs.Route.Visibility.ExteriorFactorMTwo.eventually_scale] with x hLx hx j hj σ hσ g hg
  have hxr : (0 : ℝ) < x := by
    have : 0 < x := lt_of_le_of_lt (Nat.zero_le _) hj
    exact_mod_cast this
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have hwi : 0 < ((σ : ℂ) + g * I).im := by simp [hg0]
  have hS := hasSum_aliasTerm hx hj hwi
  have hb : ∀ N : ℕ, ∑ m ∈ Finset.range N, ‖aliasTerm x j (σ + g * I) m‖
      ≤ C x * |rung (2 * π * x) (2 * j) 1| / √(x : ℝ) / g := fun N => by
    rw [le_div_iff₀ hg0, Finset.sum_mul]
    have := hLx j hj σ hσ g hg N
    simpa [mul_comm] using this
  have := norm_le_of_hasSum hS hb
  rw [le_div_iff₀ hg0] at this
  linarith

/-- **The absolute alias law gives the right-edge law**. -/
theorem edgeLawSum_of_absAliasLaw (h : AbsAliasLaw) : Cvs.Prolate.Mellin.RungWindowLawRightEdge.EdgeLawSum :=
  Cvs.Prolate.Mellin.ProlateAliasSumLaw.edgeLawSum_of_prolateAliasLaw (prolateAliasLaw_of_absAliasLaw h)

end Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries

end
