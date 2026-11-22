import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Fourier–Laplace extension of a test function supported in `(−∞, 0]`

`G(z) = ∫ g(η) e^{−2πizη} dη` is entire; for `Im z ≥ 0`, `|G z| ≤ ‖g‖₁` and, by two integrations by parts,
`4π² |z|² |G z| ≤ ‖g''‖₁`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open Complex (I)
open scoped ContDiff

namespace Cvs.Upstream.FourierLaplaceExtension

/-- The Fourier–Laplace extension `G(z) = ∫ g(η) e^{−2πizη} dη`. -/
def flExt (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ η : ℝ, g η * Complex.exp (-(2 * π * I * z * η))

theorem integrable_mul_exp {h : ℝ → ℂ} (hc : Continuous h) (hs : HasCompactSupport h) (a : ℂ) :
    Integrable fun η : ℝ => h η * Complex.exp (a * η) :=
  (hc.mul (by fun_prop)).integrable_of_hasCompactSupport (hs.mul_right)

/-- One integration by parts: `∫ h' e^{aη} = −a ∫ h e^{aη}`. -/
theorem integral_deriv_mul_exp {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hs : HasCompactSupport h) (a : ℂ) :
    ∫ η : ℝ, deriv h η * Complex.exp (a * η) = -a * ∫ η : ℝ, h η * Complex.exp (a * η) := by
  have hd : ∀ η : ℝ, HasDerivAt (fun y : ℝ => h y * Complex.exp (a * y))
      (deriv h η * Complex.exp (a * η) + h η * (a * Complex.exp (a * η))) η := by
    intro η
    have h1 : HasDerivAt h (deriv h η) η := (hh.differentiable (by simp) η).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => Complex.exp (a * y)) (Complex.exp (a * η) * (a * 1)) η :=
      ((hasDerivAt_id (η : ℂ)).const_mul a).cexp.comp_ofReal
    exact (h1.mul h2).congr_deriv (by ring)
  have hi1 := integrable_mul_exp (hh.continuous_deriv (by simp)) hs.deriv a
  have hi2 := integrable_mul_exp hh.continuous hs a
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd (hi1.add (hi2.const_mul a |>.congr
    (Eventually.of_forall fun η => by simp only; ring))) hi2
  rw [integral_add hi1 (hi2.const_mul a |>.congr (Eventually.of_forall fun η => by simp only; ring))] at h0
  have e : ∫ η : ℝ, h η * (a * Complex.exp (a * η)) = a * ∫ η : ℝ, h η * Complex.exp (a * η) := by
    rw [← integral_const_mul]; congr 1; ext η; ring
  rw [e] at h0
  linear_combination h0

theorem flExt_eq (g : ℝ → ℂ) (z : ℂ) :
    flExt g z = ∫ η : ℝ, g η * Complex.exp ((-(2 * π * I * z)) * η) := by
  unfold flExt; congr 1; ext η; ring_nf

/-- Two integrations by parts: `G_{g''}(z) = −4π² z² G_g(z)`. -/
theorem flExt_deriv_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) (z : ℂ) :
    flExt (deriv (deriv g)) z = -(4 * π ^ 2 * z ^ 2) * flExt g z := by
  have hg' : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.1 hg).2
  rw [flExt_eq, flExt_eq, integral_deriv_mul_exp hg' hs.deriv, integral_deriv_mul_exp hg hs]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_exp_le_one {z : ℂ} (hz : 0 ≤ z.im) {η : ℝ} (hη : η ≤ 0) :
    ‖Complex.exp (-(2 * π * I * z * η))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (-(2 * π * I * z * (η : ℂ))).re = 2 * π * z.im * η := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) hz) (neg_nonneg.2 hη)
  nlinarith

/-- `|G z| ≤ ‖g‖₁` on the closed upper half-plane. -/
theorem norm_flExt_le {g : ℝ → ℂ} (hc : Continuous g) (hs : HasCompactSupport g) (hsupp : tsupport g ⊆ Iic 0)
    {z : ℂ} (hz : 0 ≤ z.im) : ‖flExt g z‖ ≤ ∫ η : ℝ, ‖g η‖ := by
  refine norm_integral_le_of_norm_le (hc.norm.integrable_of_hasCompactSupport hs.norm)
    (Eventually.of_forall fun η => ?_)
  rw [norm_mul]
  by_cases hη : η ∈ tsupport g
  · exact mul_le_of_le_one_right (norm_nonneg _) (norm_exp_le_one hz (hsupp hη))
  · simp [image_eq_zero_of_notMem_tsupport hη]

/-- `G` is entire. -/
theorem differentiable_flExt {g : ℝ → ℂ} (hc : Continuous g) (hs : HasCompactSupport g) :
    Differentiable ℂ (flExt g) := by
  intro z₀
  set F : ℂ → ℝ → ℂ := fun z η => g η * Complex.exp (-(2 * π * I * z * η))
  set F' : ℂ → ℝ → ℂ := fun z η => g η * (-(2 * π * I * η) * Complex.exp (-(2 * π * I * z * η)))
  set bound : ℝ → ℝ := fun η => ‖g η‖ * (2 * π * |η| * Real.exp (2 * π * (‖z₀‖ + 1) * |η|))
  have hFc : ∀ z, Continuous (F z) := fun z => hc.mul (by fun_prop)
  have hbi : Integrable bound := by
    refine Continuous.integrable_of_hasCompactSupport (hc.norm.mul (by fun_prop)) hs.norm.mul_right
  have hFi : Integrable (F z₀) := by
    have := integrable_mul_exp hc hs (-(2 * π * I * z₀))
    refine this.congr (Eventually.of_forall fun η => ?_)
    simp only [F]; ring_nf
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := z₀) (bound := bound) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) hFi
    ((hc.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun η z hz => by
      have h1 : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' z z₀
        rw [Metric.mem_ball, dist_eq_norm] at hz; linarith
      have hre : (-(2 * π * I * z * (η : ℂ))).re ≤ 2 * π * (‖z₀‖ + 1) * |η| :=
        calc (-(2 * π * I * z * (η : ℂ))).re ≤ ‖-(2 * π * I * z * (η : ℂ))‖ := Complex.re_le_norm _
          _ = 2 * π * ‖z‖ * |η| := by
              simp [Complex.norm_real, abs_of_pos Real.pi_pos]
          _ ≤ 2 * π * (‖z₀‖ + 1) * |η| := by gcongr
      have hn : ‖-(2 * π * I * (η : ℂ))‖ = 2 * π * |η| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
      simp only [F', bound, norm_mul, Complex.norm_exp]
      rw [hn]
      gcongr)
    hbi
    (Eventually.of_forall fun η z _ => by
      have := (((hasDerivAt_id z).mul_const (-(2 * π * I * η))).cexp).const_mul (g η)
      have e1 : (fun x => F x η) = fun y => g η * Complex.exp (id y * -(2 * π * I * η)) := by
        funext y; simp only [F, id]; ring_nf
      rw [e1]
      exact this.congr_deriv (by simp only [F', id]; ring_nf))
  exact key.2.differentiableAt

/-- **Decay**: `|G z| (1 + |z|²) ≤ ‖g‖₁ + ‖g''‖₁ / 4π²` on the closed upper half-plane. -/
theorem norm_flExt_mul_le {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g)
    (hsupp : tsupport g ⊆ Iic 0) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖flExt g z‖ * (1 + ‖z‖ ^ 2) ≤ (∫ η : ℝ, ‖g η‖) + (∫ η : ℝ, ‖deriv (deriv g) η‖) / (4 * π ^ 2) := by
  have hg' : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.1 hg).2
  have hg'' : ContDiff ℝ ∞ (deriv (deriv g)) := (contDiff_infty_iff_deriv.1 hg').2
  have h0 := norm_flExt_le hg.continuous hs hsupp hz
  have h2 := norm_flExt_le hg''.continuous hs.deriv.deriv
    ((tsupport_deriv_subset).trans ((tsupport_deriv_subset).trans hsupp)) hz
  rw [flExt_deriv_deriv hg hs, norm_mul, norm_neg] at h2
  have e : ‖(4 * π ^ 2 * z ^ 2 : ℂ)‖ = 4 * π ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [e] at h2
  have hp : 0 < 4 * π ^ 2 := by positivity
  have h3 : ‖flExt g z‖ * ‖z‖ ^ 2 ≤ (∫ η : ℝ, ‖deriv (deriv g) η‖) / (4 * π ^ 2) := by
    rw [le_div_iff₀ hp]; linarith
  nlinarith
end Cvs.Upstream.FourierLaplaceExtension

end
