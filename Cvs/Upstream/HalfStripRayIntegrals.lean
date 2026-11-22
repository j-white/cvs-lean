import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Upward ray integrals of holomorphic functions on a vertical half-strip

On `U_a = {|Re z| < a, Im z > −1}`, a holomorphic `G` with `|G(z)| ≤ K/(m + (Im z)²)` has the ray integral
`F(z) = ∫_0^∞ G(z + is) ds` holomorphic with `F′ = iG` and `|F| ≤ Kπ/√m`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Metric
open Complex (I)

namespace Cvs.Upstream.HalfStripRayIntegrals

/-- The vertical half-strip `U_a = {|Re z| < a, Im z > −1}`. -/
def strip (a : ℝ) : Set ℂ := {z | |z.re| < a ∧ -1 < z.im}

theorem isOpen_strip (a : ℝ) : IsOpen (strip a) := by
  have h1 : IsOpen {z : ℂ | |z.re| < a} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have h2 : IsOpen {z : ℂ | -1 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  exact h1.inter h2

theorem add_mem_strip {a : ℝ} {z : ℂ} (hz : z ∈ strip a) {s : ℝ} (hs : 0 ≤ s) : z + s * I ∈ strip a := by
  refine ⟨?_, ?_⟩
  · simpa using hz.1
  · simp; linarith [hz.2]

/-- The ray bound `|G(z)| ≤ K/(m + (Im z)²)` on `U_a`. -/
def RayBound (a m K : ℝ) (G : ℂ → ℂ) : Prop := ∀ z ∈ strip a, ‖G z‖ ≤ K / (m + z.im ^ 2)

/-- The upward ray integral `F(z) = ∫_0^∞ G(z + is) ds`. -/
def rayInt (G : ℂ → ℂ) (z : ℂ) : ℂ := ∫ s in Ioi (0 : ℝ), G (z + s * I)

/-- Peetre's inequality in the form `1/(m + (y + s)²) ≤ 2(1 + y²)/(m(1 + s²))` for `0 < m ≤ 1`. -/
theorem peetre {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (y s : ℝ) :
    1 / (m + (y + s) ^ 2) ≤ 2 * (1 + y ^ 2) / (m * (1 + s ^ 2)) := by
  have h1 : 0 < m + (y + s) ^ 2 := by positivity
  rw [div_le_div_iff₀ h1 (by positivity)]
  nlinarith [sq_nonneg (y + s), sq_nonneg y, sq_nonneg s, sq_nonneg (y * (y + s)), mul_nonneg hm.le (sq_nonneg y),
    mul_nonneg hm.le (sq_nonneg (y + s)), mul_nonneg hm.le (mul_nonneg (sq_nonneg y) (sq_nonneg (y + s))),
    sq_nonneg (2 * y + s), mul_nonneg (sub_nonneg.2 hm1) (sq_nonneg (y + s))]

theorem integrableOn_inv_one_add_sq : IntegrableOn (fun s : ℝ => 1 / (1 + s ^ 2)) (Ioi 0) := by
  simpa [one_div] using integrable_inv_one_add_sq.integrableOn

/-- `∫_ℝ 1/(m + t²) dt = π/√m`. -/
theorem integral_inv_add_sq {m : ℝ} (hm : 0 < m) : ∫ t : ℝ, 1 / (m + t ^ 2) = π / √m := by
  have hs : 0 < √m := Real.sqrt_pos.2 hm
  have e : (fun t : ℝ => 1 / (m + t ^ 2)) = fun t => (1 / m) * (1 + ((√m)⁻¹ * t) ^ 2)⁻¹ := by
    ext t
    have : ((√m)⁻¹ * t) ^ 2 = t ^ 2 / m := by rw [mul_pow, inv_pow, Real.sq_sqrt hm.le]; field_simp
    rw [this]; field_simp
  rw [e, integral_const_mul, Measure.integral_comp_mul_left (fun u => (1 + u ^ 2)⁻¹) ((√m)⁻¹),
    integral_univ_inv_one_add_sq, inv_inv, abs_of_pos hs, smul_eq_mul]
  have hm' : √m * √m = m := Real.mul_self_sqrt hm.le
  field_simp
  rw [Real.sq_sqrt hm.le]

theorem integrable_inv_add_sq {m : ℝ} (hm : 0 < m) : Integrable (fun t : ℝ => 1 / (m + t ^ 2)) := by
  have hs : 0 < √m := Real.sqrt_pos.2 hm
  have e : (fun t : ℝ => 1 / (m + t ^ 2)) = fun t => (1 / m) * (1 + ((√m)⁻¹ * t) ^ 2)⁻¹ := by
    ext t
    have : ((√m)⁻¹ * t) ^ 2 = t ^ 2 / m := by rw [mul_pow, inv_pow, Real.sq_sqrt hm.le]; field_simp
    rw [this]; field_simp
  rw [e]
  exact (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hs.ne')).const_mul (1 / m)

/-- `∫_0^∞ 1/(m + (y + s)²) ds ≤ π/√m`, uniformly in `y`. -/
theorem integral_shift_le {m : ℝ} (hm : 0 < m) (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), 1 / (m + (y + s) ^ 2) ≤ π / √m := by
  rw [← integral_inv_add_sq hm]
  have hI : Integrable (fun s : ℝ => 1 / (m + (y + s) ^ 2)) := (integrable_inv_add_sq hm).comp_add_left y
  refine (setIntegral_le_integral hI (Eventually.of_forall fun _ => by positivity)).trans_eq ?_
  exact integral_add_left_eq_self (fun t : ℝ => 1 / (m + t ^ 2)) y

theorem integrableOn_shift {m : ℝ} (hm : 0 < m) (y : ℝ) :
    IntegrableOn (fun s : ℝ => 1 / (m + (y + s) ^ 2)) (Ioi 0) := by
  have := (integrable_inv_add_sq hm).comp_add_left y
  exact this.integrableOn

section

variable {a m K : ℝ} {G : ℂ → ℂ}

theorem continuousOn_ray (hG : DifferentiableOn ℂ G (strip a)) {z : ℂ} (hz : z ∈ strip a) :
    ContinuousOn (fun s : ℝ => G (z + s * I)) (Ici 0) := by
  refine hG.continuousOn.comp (by fun_prop) fun s hs => add_mem_strip hz hs

theorem aestronglyMeasurable_ray (hG : DifferentiableOn ℂ G (strip a)) {z : ℂ} (hz : z ∈ strip a) :
    AEStronglyMeasurable (fun s : ℝ => G (z + s * I)) (volume.restrict (Ioi 0)) :=
  ((continuousOn_ray hG hz).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi

theorem norm_ray_le (hB : RayBound a m K G) {z : ℂ} (hz : z ∈ strip a) {s : ℝ} (hs : 0 ≤ s) :
    ‖G (z + s * I)‖ ≤ K * (1 / (m + (z.im + s) ^ 2)) := by
  have h := hB _ (add_mem_strip hz hs)
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_one, mul_zero, add_zero] at h
  rw [mul_one_div]; exact h

theorem integrableOn_ray (hG : DifferentiableOn ℂ G (strip a)) (hm : 0 < m) (hB : RayBound a m K G)
    {z : ℂ} (hz : z ∈ strip a) : IntegrableOn (fun s : ℝ => G (z + s * I)) (Ioi 0) := by
  refine Integrable.mono' (((integrableOn_shift hm z.im)).const_mul K) (aestronglyMeasurable_ray hG hz) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact norm_ray_le hB hz (le_of_lt hs)

/-- The ray tends to `0`: `G(z + is) → 0` as `s → ∞`. -/
theorem tendsto_ray (hB : RayBound a m K G) {z : ℂ} (hz : z ∈ strip a) :
    Tendsto (fun s : ℝ => G (z + s * I)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun s : ℝ => K * (1 / (m + (z.im + s) ^ 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => m + (z.im + s) ^ 2) atTop atTop := by
      refine tendsto_atTop_add_const_left _ m ?_
      exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ _ tendsto_id)
    have := (tendsto_inv_atTop_zero.comp h1).const_mul K
    simpa [one_div, Function.comp_def] using this
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 0] with s hs using norm_ray_le hB hz hs

/-- The local derivative bound from Cauchy's estimate on the shifted discs. -/
theorem norm_deriv_ray_le (hG : DifferentiableOn ℂ G (strip a)) (hm : 0 < m) (hm1 : m ≤ 1) (hK : 0 ≤ K)
    (hB : RayBound a m K G) {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hball : ball z₀ ρ ⊆ strip a) {z : ℂ}
    (hz : z ∈ ball z₀ (ρ / 2)) {s : ℝ} (hs : 0 ≤ s) :
    ‖deriv G (z + s * I)‖ ≤ (4 / ρ) * (2 * K * (1 + (|z₀.im| + ρ) ^ 2) / m) * (1 / (1 + s ^ 2)) := by
  set w := z + s * I
  have hr : 0 < ρ / 4 := by positivity
  have hsub : closedBall w (ρ / 4) ⊆ strip a := by
    intro u hu
    have hu' : u - s * I ∈ ball z₀ ρ := by
      rw [mem_ball] at hz ⊢
      rw [mem_closedBall] at hu
      calc dist (u - s * I) z₀ ≤ dist (u - s * I) z + dist z z₀ := dist_triangle _ _ _
        _ = dist u w + dist z z₀ := by
            simp only [w, dist_eq_norm]; congr 1; ring_nf
        _ < ρ := by linarith
    have := add_mem_strip (hball hu') hs
    simpa using this
  have hd : DiffContOnCl ℂ G (ball w (ρ / 4)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball w hr.ne']
    exact hG.mono hsub
  refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (C := 2 * K * (1 + (|z₀.im| + ρ) ^ 2) / m * (1 / (1 + s ^ 2))) hr hd fun u hu => ?_).trans_eq
    (by field_simp)
  have hu' : u ∈ strip a := hsub (sphere_subset_closedBall hu)
  have h1 := hB u hu'
  have him : |u.im - s - z₀.im| ≤ ρ := by
    have h2 : |u.im - w.im| ≤ ρ / 4 := by
      have := Complex.abs_im_le_norm (u - w)
      rw [Complex.sub_im] at this
      rw [mem_sphere, dist_eq_norm] at hu
      linarith
    have h3 : |z.im - z₀.im| ≤ ρ / 2 := by
      have := Complex.abs_im_le_norm (z - z₀)
      rw [Complex.sub_im] at this
      rw [mem_ball, dist_eq_norm] at hz
      linarith
    have hw : w.im = z.im + s := by simp [w]
    rw [abs_le] at h2 h3 ⊢
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  have hp := peetre hm hm1 (u.im - s) s
  rw [show u.im - s + s = u.im by ring] at hp
  have hy : (u.im - s) ^ 2 ≤ (|z₀.im| + ρ) ^ 2 := by
    rw [← sq_abs]
    have : |u.im - s| ≤ |z₀.im| + ρ := by
      calc |u.im - s| = |(u.im - s - z₀.im) + z₀.im| := by ring_nf
        _ ≤ |u.im - s - z₀.im| + |z₀.im| := abs_add_le _ _
        _ ≤ |z₀.im| + ρ := by linarith
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ‖G u‖ ≤ K / (m + u.im ^ 2) := h1
    _ = K * (1 / (m + u.im ^ 2)) := by ring
    _ ≤ K * (2 * (1 + (u.im - s) ^ 2) / (m * (1 + s ^ 2))) := mul_le_mul_of_nonneg_left hp hK
    _ ≤ K * (2 * (1 + (|z₀.im| + ρ) ^ 2) / (m * (1 + s ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) (by positivity)) hK
    _ = 2 * K * (1 + (|z₀.im| + ρ) ^ 2) / m * (1 / (1 + s ^ 2)) := by field_simp

theorem exists_ball {z₀ : ℂ} (ha : z₀ ∈ strip a) : ∃ ρ > 0, ball z₀ ρ ⊆ strip a := by
  obtain ⟨ρ, hρ, h⟩ := Metric.isOpen_iff.1 (isOpen_strip a) z₀ ha
  exact ⟨ρ, hρ, h⟩

/-- **The ray integral is holomorphic** with `F′(z) = iG(z)`. -/
theorem hasDerivAt_rayInt (hG : DifferentiableOn ℂ G (strip a)) (hm : 0 < m) (hm1 : m ≤ 1) (hK : 0 ≤ K)
    (hB : RayBound a m K G) {z₀ : ℂ} (hz₀ : z₀ ∈ strip a) : HasDerivAt (rayInt G) (I * G z₀) z₀ := by
  obtain ⟨ρ, hρ, hball⟩ := exists_ball hz₀
  have hdG : DifferentiableOn ℂ (deriv G) (strip a) := hG.deriv (isOpen_strip a)
  have hmem : ∀ z ∈ ball z₀ (ρ / 2), z ∈ strip a := fun z hz =>
    hball (ball_subset_ball (by linarith) hz)
  set bound : ℝ → ℝ := fun s => (4 / ρ) * (2 * K * (1 + (|z₀.im| + ρ) ^ 2) / m) * (1 / (1 + s ^ 2))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun z s => G (z + s * I)) (F' := fun z s => deriv G (z + s * I)) (x₀ := z₀) (bound := bound)
    (ball_mem_nhds z₀ (by positivity : 0 < ρ / 2))
    (by filter_upwards [(isOpen_strip a).mem_nhds hz₀] with z hz using aestronglyMeasurable_ray hG hz)
    (integrableOn_ray hG hm hB hz₀) (aestronglyMeasurable_ray hdG hz₀)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs z hz
      exact norm_deriv_ray_le hG hm hm1 hK hB hρ hball hz (le_of_lt hs))
    (integrableOn_inv_one_add_sq.const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs z hz
      have hw : z + s * I ∈ strip a := add_mem_strip (hmem z hz) (le_of_lt hs)
      have h1 : HasDerivAt G (deriv G (z + s * I)) (z + s * I) :=
        (hG.differentiableAt ((isOpen_strip a).mem_nhds hw)).hasDerivAt
      have h2 : HasDerivAt (fun z : ℂ => z + s * I) 1 z := (hasDerivAt_id z).add_const _
      have h3 := HasDerivAt.comp (h := fun z : ℂ => z + (s : ℂ) * I) z h1 h2
      rw [mul_one] at h3
      exact h3)
  obtain ⟨-, hD⟩ := key
  have hval : ∫ s in Ioi (0 : ℝ), deriv G (z₀ + s * I) = I * G z₀ := by
    have hderiv : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun s : ℝ => G (z₀ + s * I)) (deriv G (z₀ + s * I) * I) s := by
      intro s hs
      have hw : z₀ + s * I ∈ strip a := add_mem_strip hz₀ hs
      have h1 : HasDerivAt G (deriv G (z₀ + s * I)) (z₀ + s * I) :=
        (hG.differentiableAt ((isOpen_strip a).mem_nhds hw)).hasDerivAt
      have h2 : HasDerivAt (fun s : ℝ => z₀ + (s : ℂ) * I) I s := by
        have h3 := (((hasDerivAt_id s).ofReal_comp).mul_const I).const_add z₀
        rw [Complex.ofReal_one, one_mul] at h3
        exact h3
      exact HasDerivAt.comp (h := fun s : ℝ => z₀ + (s : ℂ) * I) s h1 h2
    have hint : IntegrableOn (fun s : ℝ => deriv G (z₀ + s * I) * I) (Ioi 0) := by
      refine Integrable.mono' (integrableOn_inv_one_add_sq.const_mul ((4 / ρ) *
        (2 * K * (1 + (|z₀.im| + ρ) ^ 2) / m))) ?_ ?_
      · exact (aestronglyMeasurable_ray hdG hz₀).mul_const I
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        rw [norm_mul, Complex.norm_I, mul_one]
        exact norm_deriv_ray_le hG hm hm1 hK hB hρ hball (mem_ball_self (by positivity)) (le_of_lt hs)
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint (by simpa using tendsto_ray hB hz₀)
    rw [integral_mul_const] at h
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    set X := ∫ s in Ioi (0 : ℝ), deriv G (z₀ + s * I)
    have hX : X = -(X * I) * I := by rw [neg_mul, mul_assoc, Complex.I_mul_I]; ring
    rw [hX, h]; ring
  unfold rayInt
  rw [← hval]
  exact hD

end

end Cvs.Upstream.HalfStripRayIntegrals

end
