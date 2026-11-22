import Mathlib
import Cvs.Route.Visibility.ProjectionShareSawtooth
import Cvs.Upstream.TrigMellinIntegralsContinuation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Holomorphic parameter integrals, and the rotated sine integral

An integral `∫ f(s, a) dμ(a)` of functions holomorphic in `s` on an open `U` with `‖f(s, a)‖ ≤ g(a)`, `g ∈ L¹`, is
holomorphic on `U` (Cauchy's estimate bounds the `s`-derivative on smaller discs). Rotating `θ = 1 + iv` gives
`J₊(y, s) = ∫₁^∞ e^{iyθ}θ^{s−2} dθ = i∫₀^∞ e^{iy(1+iv)}(1 + iv)^{s−2} dv` for `y > 0`, `Re s < 1`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology Complex Metric
open scoped Interval

namespace Cvs.Upstream.HolomorphicParamIntegralSine

/-! ### Holomorphic parameter integrals -/

/-- **Holomorphy under the integral**: if `s ↦ f(s, a)` is holomorphic on the open set `U` for a.e. `a`, each
`f(s, ·)` is a.e. strongly measurable, and `‖f(s, a)‖ ≤ g(a)` on `U` with `g` integrable, then `s ↦ ∫ f(s, a) dμ` is
holomorphic on `U`. -/
theorem differentiableOn_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → α → ℂ} (hfm : ∀ s ∈ U, AEStronglyMeasurable (f s) μ)
    (hf : ∀ᵐ a ∂μ, DifferentiableOn ℂ (fun s => f s a) U) {g : α → ℝ} (hg : Integrable g μ)
    (hfg : ∀ᵐ a ∂μ, ∀ s ∈ U, ‖f s a‖ ≤ g a) : DifferentiableOn ℂ (fun s => ∫ a, f s a ∂μ) U := by
  intro s₀ hs₀
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hU s₀ hs₀
  set r := R / 3 with hr
  have hr0 : 0 < r := by positivity
  have hsub : ∀ s ∈ ball s₀ r, closedBall s r ⊆ U := fun s hs z hz => by
    apply hball
    rw [mem_ball] at hs ⊢
    rw [mem_closedBall] at hz
    calc dist z s₀ ≤ dist z s + dist s s₀ := dist_triangle _ _ _
      _ < R := by linarith
  have hU0 : ∀ s ∈ ball s₀ r, s ∈ U := fun s hs => hsub s hs (mem_closedBall_self hr0.le)
  have hderiv_le : ∀ᵐ a ∂μ, ∀ s ∈ ball s₀ r, ‖deriv (fun s => f s a) s‖ ≤ g a / r := by
    filter_upwards [hfg, hf] with a ha hfa s hs
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 (hfa.diffContOnCl_ball (hsub s hs))
      fun z hz => ha z (hsub s hs (sphere_subset_closedBall hz))
  have hhas : ∀ᵐ a ∂μ, ∀ s ∈ ball s₀ r, HasDerivAt (fun s => f s a) (deriv (fun s => f s a) s) s := by
    filter_upwards [hf] with a hfa s hs
    exact ((hfa s (hU0 s hs)).differentiableAt (hU.mem_nhds (hU0 s hs))).hasDerivAt
  -- the derivative is measurable, as a limit of difference quotients
  have hF'm : AEStronglyMeasurable (fun a => deriv (fun s => f s a) s₀) μ := by
    set t : ℕ → ℂ := fun n => ((r / (n + 2) : ℝ) : ℂ) with ht
    have ht0 : ∀ n, t n ≠ 0 := fun n => by
      simp only [ht, ne_eq, Complex.ofReal_eq_zero]; positivity
    have htb : ∀ n, s₀ + t n ∈ U := fun n => by
      apply hU0
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ht, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    have hlim : Tendsto t atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Eventually.of_forall ht0)
      have h1 : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      have := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at this
      exact this
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n a => (t n)⁻¹ • (f (s₀ + t n) a - f s₀ a))
      (fun n => ((hfm _ (htb n)).sub (hfm s₀ hs₀)).const_smul (t n)⁻¹) ?_
    filter_upwards [hhas] with a ha
    exact ((ha s₀ (mem_ball_self hr0)).tendsto_slope_zero).comp hlim
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := f)
    (F' := fun s a => deriv (fun s => f s a) s) (x₀ := s₀) (bound := fun a => g a / r)
    (ball_mem_nhds s₀ hr0) (Eventually.mono (hU.mem_nhds hs₀) fun s hs => hfm s hs)
    ((hg.mono' (hfm s₀ hs₀) (hfg.mono fun a ha => ha s₀ hs₀))) hF'm
    hderiv_le (hg.div_const r) hhas
  exact key.2.differentiableAt.differentiableWithinAt

/-! ### The rotated exponential integral -/

/-- The integrand `e^{iyz} z^{s−2}`. -/
def rotF (y : ℝ) (s z : ℂ) : ℂ := cexp (I * y * z) * z ^ (s - 2)

/-- `J₊(y, s) = i∫₀^∞ e^{iy(1+iv)}(1 + iv)^{s−2} dv`, the integral on the rotated ray. -/
def jPlus (y : ℝ) (s : ℂ) : ℂ := I * ∫ v in Ioi (0 : ℝ), rotF y s (1 + v * I)

theorem norm_cexp_I_mul (y : ℝ) (z : ℂ) : ‖cexp (I * y * z)‖ = Real.exp (-(y * z.im)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]

/-- `‖z^w‖ ≤ ‖z‖^{Re w} e^{|arg z||Im w|}`. -/
theorem norm_cpow_le_exp (z w : ℂ) : ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (|arg z| * |w.im|) := by
  refine (Complex.norm_cpow_le z w).trans (le_of_eq_of_le (by rw [div_eq_mul_inv, ← Real.exp_neg]) ?_)
  gcongr
  rw [← neg_mul]
  calc -arg z * w.im ≤ |-arg z * w.im| := le_abs_self _
    _ = |arg z| * |w.im| := by rw [abs_mul, abs_neg]

theorem abs_arg_le_of_re_pos {z : ℂ} (hz : 0 < z.re) : |arg z| ≤ π / 2 :=
  Complex.abs_arg_le_pi_div_two_iff.2 hz.le

/-- `arg(1 + iv) ≤ v` for `v ≥ 0`. -/
theorem arg_one_add_le {v : ℝ} (hv : 0 ≤ v) : |arg (1 + v * I)| ≤ v := by
  have hre : (1 + (v : ℂ) * I).re = 1 := by simp
  have him : (1 + (v : ℂ) * I).im = v := by simp
  have h0 : 0 ≤ arg (1 + v * I) := Complex.arg_nonneg_iff.2 (by rw [him]; exact hv)
  have hlt : arg (1 + v * I) < π / 2 := by
    have := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by rw [hre]; exact one_pos))
    exact (le_abs_self _).trans_lt this
  rw [abs_of_nonneg h0]
  have := Real.le_tan h0 hlt
  rwa [Complex.tan_arg, hre, him, div_one] at this

theorem slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ∈ Complex.slitPlane := Or.inl hz

theorem differentiableAt_rotF (y : ℝ) (s : ℂ) {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ (rotF y s) z := by
  unfold rotF
  exact ((differentiableAt_const _).mul differentiableAt_id).cexp.mul
    ((hasDerivAt_id z).cpow_const (slitPlane_of_re_pos hz)).differentiableAt

/-- `‖e^{iyz}z^{s−2}‖ ≤ e^{−y Im z}‖z‖^{Re s − 2}e^{(π/2)|Im s|}` on `Re z > 0`. -/
theorem norm_rotF_le (y : ℝ) (s : ℂ) {z : ℂ} (hz : 0 < z.re) :
    ‖rotF y s z‖ ≤ Real.exp (-(y * z.im)) * (‖z‖ ^ (s.re - 2) * Real.exp (π / 2 * |s.im|)) := by
  unfold rotF
  rw [norm_mul, norm_cexp_I_mul]
  refine mul_le_mul_of_nonneg_left ((norm_cpow_le_exp z (s - 2)).trans ?_) (Real.exp_pos _).le
  simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero]
  gcongr
  · exact abs_arg_le_of_re_pos hz

/-- The integrand is integrable on `(1, ∞)` for `Re s < 1`. -/
theorem integrableOn_rotF (y : ℝ) {s : ℂ} (hs : s.re < 1) :
    IntegrableOn (fun θ : ℝ => rotF y s θ) (Ioi 1) := by
  set C := Real.exp (π / 2 * |s.im|) with hC
  have hm : ContinuousOn (fun θ : ℝ => rotF y s θ) (Ioi 1) := fun θ hθ =>
    ((differentiableAt_rotF y s (by simpa using lt_trans one_pos hθ)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  refine ((integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 2 < -1) one_pos).mul_const C).mono'
    (hm.aestronglyMeasurable measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
  have h := norm_rotF_le y s (z := (θ : ℂ)) (by simpa using lt_trans one_pos hθ)
  simp only [Complex.ofReal_im, mul_zero, neg_zero, Real.exp_zero, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (lt_trans one_pos hθ)] at h
  exact h

/-- **The rotation**: for `y > 0` and `Re s < 1`, `∫₁^∞ e^{iyθ}θ^{s−2} dθ = J₊(y, s)`. -/
theorem integral_rotF_eq {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.re < 1) :
    ∫ θ in Ioi (1 : ℝ), rotF y s θ = jPlus y s := by
  set C := Real.exp (π / 2 * |s.im|) with hC
  have hC0 : 0 < C := Real.exp_pos _
  have hbot_int := integrableOn_rotF y hs
  -- the left side is integrable on `(0, ∞)`
  have hleft_int : IntegrableOn (fun v : ℝ => rotF y s (1 + v * I)) (Ioi 0) := by
    have hm : ContinuousOn (fun v : ℝ => rotF y s (1 + v * I)) (Ioi 0) := fun v _ =>
      ((differentiableAt_rotF y s (by simp)).continuousAt.comp (by fun_prop)).continuousWithinAt
    refine ((exp_neg_integrableOn_Ioi 0 hy).mul_const (1 * C)).mono'
      (hm.aestronglyMeasurable measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun v (hv : 0 < v) => ?_))
    refine (norm_rotF_le y s (by simp)).trans ?_
    have hn : 1 ≤ ‖(1 : ℂ) + v * I‖ := by
      have := Complex.abs_re_le_norm (1 + (v : ℂ) * I); simpa using this
    have hp : ‖(1 : ℂ) + v * I‖ ^ (s.re - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
    have him : (1 + (v : ℂ) * I).im = v := by simp
    rw [him]
    calc Real.exp (-(y * v)) * (‖(1 : ℂ) + v * I‖ ^ (s.re - 2) * C) ≤ Real.exp (-(y * v)) * (1 * C) := by
          gcongr
      _ = Real.exp (-y * v) * (1 * C) := by ring_nf
  -- Cauchy on the rectangles `[1, R] × [0, R]`
  have hrect : ∀ R : ℝ, 1 ≤ R →
      (∫ x in (1 : ℝ)..R, rotF y s x) - (∫ x in (1 : ℝ)..R, rotF y s (x + R * I))
        + I * (∫ v in (0 : ℝ)..R, rotF y s (R + v * I)) - I * (∫ v in (0 : ℝ)..R, rotF y s (1 + v * I)) = 0 := by
    intro R hR
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (rotF y s) 1 (R + R * I)
      (fun z hz => (differentiableAt_rotF y s (by
        have hz1 := hz.1
        simp only [Complex.one_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Set.mem_preimage] at hz1
        rw [Set.uIcc_of_le hR] at hz1
        linarith [hz1.1])).differentiableWithinAt)
    simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
      Complex.ofReal_zero, zero_mul, smul_eq_mul] at h
    convert h using 3
  set Rn : ℕ → ℝ := fun n => (n : ℝ) + 1 with hRn
  have hRt : Tendsto Rn atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hR1 : ∀ n, 1 ≤ Rn n := fun n => by simp [hRn]
  have hb := intervalIntegral_tendsto_integral_Ioi 1 hbot_int hRt
  have hl := intervalIntegral_tendsto_integral_Ioi 0 hleft_int hRt
  -- the top side vanishes in the limit
  have ht : Tendsto (fun n => ∫ x in (1 : ℝ)..Rn n, rotF y s (x + Rn n * I)) atTop (𝓝 0) := by
    have hbd : ∀ n, ‖∫ x in (1 : ℝ)..Rn n, rotF y s (x + Rn n * I)‖ ≤ C * (Rn n * Real.exp (-(y * Rn n))) := by
      intro n
      have hle : ∀ x ∈ Ι (1 : ℝ) (Rn n), ‖rotF y s (x + Rn n * I)‖ ≤ Real.exp (-(y * Rn n)) * C := by
        intro x hx
        rw [Set.uIoc_of_le (hR1 n)] at hx
        have hre : 0 < ((x : ℂ) + Rn n * I).re := by simp; linarith [hx.1]
        refine (norm_rotF_le y s hre).trans ?_
        have him : ((x : ℂ) + Rn n * I).im = Rn n := by simp
        have hn : 1 ≤ ‖(x : ℂ) + Rn n * I‖ := by
          have := Complex.abs_im_le_norm ((x : ℂ) + Rn n * I)
          rw [him, abs_of_pos (by linarith [hR1 n])] at this
          linarith [hR1 n]
        have hp : ‖(x : ℂ) + Rn n * I‖ ^ (s.re - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
        rw [him]
        calc Real.exp (-(y * Rn n)) * (‖(x : ℂ) + Rn n * I‖ ^ (s.re - 2) * C)
            ≤ Real.exp (-(y * Rn n)) * (1 * C) := by gcongr
          _ = Real.exp (-(y * Rn n)) * C := by ring
      refine (intervalIntegral.norm_integral_le_of_norm_le_const hle).trans ?_
      rw [abs_of_nonneg (by linarith [hR1 n])]
      have : 0 ≤ Real.exp (-(y * Rn n)) * C := by positivity
      nlinarith [Real.exp_pos (-(y * Rn n))]
    have hlim : Tendsto (fun n => C * (Rn n * Real.exp (-(y * Rn n)))) atTop (𝓝 0) := by
      have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (hRt.const_mul_atTop hy)
      have h2 := (h1.const_mul (C / y))
      rw [mul_zero] at h2
      refine h2.congr fun n => ?_
      simp only [Function.comp, pow_one]
      field_simp
    exact squeeze_zero_norm hbd hlim
  -- the right side vanishes in the limit
  have hr : Tendsto (fun n => ∫ v in (0 : ℝ)..Rn n, rotF y s (Rn n + v * I)) atTop (𝓝 0) := by
    have hbd : ∀ n, ‖∫ v in (0 : ℝ)..Rn n, rotF y s (Rn n + v * I)‖ ≤ C * Rn n ^ (s.re - 1) := by
      intro n
      have hR0 : 0 < Rn n := by linarith [hR1 n]
      have hle : ∀ v ∈ Ι (0 : ℝ) (Rn n), ‖rotF y s (Rn n + v * I)‖ ≤ Rn n ^ (s.re - 2) * C := by
        intro v hv
        rw [Set.uIoc_of_le hR0.le] at hv
        have hre : 0 < ((Rn n : ℂ) + v * I).re := by simp; exact hR0
        refine (norm_rotF_le y s hre).trans ?_
        have him : ((Rn n : ℂ) + v * I).im = v := by simp
        have hn : Rn n ≤ ‖(Rn n : ℂ) + v * I‖ := by
          have := Complex.abs_re_le_norm ((Rn n : ℂ) + v * I)
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im, mul_zero, mul_one, sub_zero, add_zero] at this
          rwa [abs_of_pos hR0] at this
        have hp : ‖(Rn n : ℂ) + v * I‖ ^ (s.re - 2) ≤ Rn n ^ (s.re - 2) :=
          Real.rpow_le_rpow_of_nonpos hR0 hn (by linarith)
        rw [him]
        have he : Real.exp (-(y * v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hv.1])
        calc Real.exp (-(y * v)) * (‖(Rn n : ℂ) + v * I‖ ^ (s.re - 2) * C)
            ≤ 1 * (Rn n ^ (s.re - 2) * C) := by
              gcongr
          _ = Rn n ^ (s.re - 2) * C := one_mul _
      refine (intervalIntegral.norm_integral_le_of_norm_le_const hle).trans (le_of_eq ?_)
      rw [sub_zero, abs_of_pos hR0, show s.re - 1 = (s.re - 2) + 1 by ring, Real.rpow_add_one hR0.ne']
      ring
    have hlim : Tendsto (fun n => C * Rn n ^ (s.re - 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - s.re)).comp hRt
      have h2 := this.const_mul C
      rw [mul_zero] at h2
      refine h2.congr fun n => ?_
      simp only [Function.comp]; congr 2; ring
    exact squeeze_zero_norm hbd hlim
  -- assemble the limits
  have hall := ((hb.sub ht).add (hr.const_mul I)).sub (hl.const_mul I)
  have hz : Tendsto (fun n => (∫ x in (1 : ℝ)..Rn n, rotF y s x) - (∫ x in (1 : ℝ)..Rn n, rotF y s (x + Rn n * I))
      + I * (∫ v in (0 : ℝ)..Rn n, rotF y s (Rn n + v * I))
      - I * (∫ v in (0 : ℝ)..Rn n, rotF y s (1 + v * I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun n => (hrect (Rn n) (hR1 n)).symm
  have huniq := tendsto_nhds_unique hall hz
  rw [sub_zero, mul_zero, add_zero] at huniq
  rw [jPlus]
  linear_combination huniq

/-! ### The rotated sine integral -/

open scoped ComplexConjugate

/-- `J(y, s) = (J₊(y, s) − conj J₊(y, s̄))/(2i)`, the continuation of `∫₁^∞ θ^{s−2} sin(yθ) dθ`. -/
def jRot (y : ℝ) (s : ℂ) : ℂ := (jPlus y s - conj (jPlus y (conj s))) / (2 * I)

theorem conj_rotF (y θ : ℝ) (hθ : 0 < θ) (s : ℂ) :
    conj (rotF y (conj s) θ) = cexp (-(I * y * θ)) * (θ : ℂ) ^ (s - 2) := by
  unfold rotF
  rw [map_mul, ← Complex.exp_conj]
  have harg : (θ : ℂ).arg ≠ π := by rw [Complex.arg_ofReal_of_nonneg hθ.le]; exact Real.pi_ne_zero.symm
  have h1 : conj ((θ : ℂ) ^ (conj s - 2)) = (θ : ℂ) ^ (s - 2) := by
    rw [show conj s - 2 = conj (s - 2) by rw [map_sub, map_ofNat], Complex.cpow_conj _ _ harg, Complex.conj_conj,
      Complex.conj_ofReal]
  rw [h1]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **The sine integral on the rotated rays**: `∫₁^∞ θ^{s−2} sin(yθ) dθ = J(y, s)` for `y > 0`, `Re s < 1`. -/
theorem sinM_sub_one_eq_jRot {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s.re < 1) :
    Cvs.Upstream.TrigMellinIntegralsContinuation.sinM y (s - 1) = jRot y s := by
  have hs' : (conj s).re < 1 := by simpa using hs
  have h1 := integral_rotF_eq hy hs
  have h2 := integral_rotF_eq hy hs'
  have hi1 := integrableOn_rotF y hs
  have hi2 : IntegrableOn (fun θ : ℝ => cexp (-(I * y * θ)) * (θ : ℂ) ^ (s - 2)) (Ioi 1) := by
    have hm : ContinuousOn (fun θ : ℝ => cexp (-(I * y * θ)) * (θ : ℂ) ^ (s - 2)) (Ioi 1) := fun θ hθ =>
      ((Complex.continuous_exp.comp (by fun_prop)).continuousAt.mul
        ((Cvs.Route.Visibility.ProjectionShareSawtooth.hasDerivAt_ofReal_cpow (lt_trans one_pos hθ) (s - 2)).continuousAt)).continuousWithinAt
    refine (integrableOn_rotF y hs').norm.mono' (hm.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
    rw [← conj_rotF y θ (lt_trans one_pos hθ), Complex.norm_conj]
  unfold Cvs.Upstream.TrigMellinIntegralsContinuation.sinM
  have e : ∀ θ : ℝ, 0 < θ → (θ : ℂ) ^ (s - 1 - 1) * ((Real.sin (y * θ) : ℝ) : ℂ)
      = (rotF y s θ - cexp (-(I * y * θ)) * (θ : ℂ) ^ (s - 2)) / (2 * I) := fun θ hθ => by
    unfold rotF
    rw [show s - 1 - 1 = s - 2 by ring, Complex.ofReal_sin, Complex.sin]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun θ (hθ : 1 < θ) => e θ (lt_trans one_pos hθ)),
    integral_div, integral_sub hi1 hi2, h1]
  have h3 : ∫ θ in Ioi (1 : ℝ), cexp (-(I * y * θ)) * (θ : ℂ) ^ (s - 2) = conj (jPlus y (conj s)) := by
    rw [← h2, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun θ (hθ : 1 < θ) => ?_
    rw [conj_rotF y θ (lt_trans one_pos hθ)]
  rw [h3, jRot]

/-- On the rotated ray, `‖e^{iy(1+iv)}(1 + iv)^{s−2}‖ ≤ e^{−(y − |Im s| − 1)v}` for `v ≥ 0`, `Re s ≤ 3`. -/
theorem norm_rotF_ray_le (y : ℝ) {s : ℂ} (hs : s.re ≤ 3) {v : ℝ} (hv : 0 ≤ v) :
    ‖rotF y s (1 + v * I)‖ ≤ Real.exp (-((y - |s.im| - 1) * v)) := by
  unfold rotF
  rw [norm_mul, norm_cexp_I_mul]
  have him : (1 + (v : ℂ) * I).im = v := by simp
  rw [him]
  have hn1 : 1 ≤ ‖(1 : ℂ) + v * I‖ := by
    have := Complex.abs_re_le_norm (1 + (v : ℂ) * I); simpa using this
  have hn2 : ‖(1 : ℂ) + v * I‖ ≤ 1 + v := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_one, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonneg hv]
  have hp : ‖(1 + (v : ℂ) * I) ^ (s - 2)‖ ≤ Real.exp v * Real.exp (v * |s.im|) := by
    refine (norm_cpow_le_exp _ _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero]
    gcongr
    · calc ‖(1 : ℂ) + v * I‖ ^ (s.re - 2) ≤ ‖(1 : ℂ) + v * I‖ ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ ≤ 1 + v := by rw [Real.rpow_one]; exact hn2
        _ ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
    · exact arg_one_add_le hv
  calc Real.exp (-(y * v)) * ‖(1 + (v : ℂ) * I) ^ (s - 2)‖
      ≤ Real.exp (-(y * v)) * (Real.exp v * Real.exp (v * |s.im|)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp (-((y - |s.im| - 1) * v)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- `‖J₊(y, s)‖ ≤ 1/(y − |Im s| − 1)` for `Re s ≤ 3` and `|Im s| + 1 < y`. -/
theorem norm_jPlus_le {y : ℝ} {s : ℂ} (hs : s.re ≤ 3) (hy : |s.im| + 1 < y) :
    ‖jPlus y s‖ ≤ 1 / (y - |s.im| - 1) := by
  have hd : 0 < y - |s.im| - 1 := by linarith
  unfold jPlus
  rw [norm_mul, Complex.norm_I, one_mul]
  have hint : IntegrableOn (fun v : ℝ => Real.exp (-(y - |s.im| - 1) * v)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hd
  calc ‖∫ v in Ioi (0 : ℝ), rotF y s (1 + v * I)‖ ≤ ∫ v in Ioi (0 : ℝ), Real.exp (-(y - |s.im| - 1) * v) :=
        norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun v (hv : 0 < v) => by
            rw [neg_mul]; exact norm_rotF_ray_le y hs hv.le))
    _ = 1 / (y - |s.im| - 1) := by
        rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]; field_simp

/-- **The bound for the rotated sine integral**: `‖J(y, s)‖ ≤ 1/(y − |Im s| − 1)` for `Re s ≤ 3`, `|Im s| + 1 < y`. -/
theorem norm_jRot_le {y : ℝ} {s : ℂ} (hs : s.re ≤ 3) (hy : |s.im| + 1 < y) :
    ‖jRot y s‖ ≤ 1 / (y - |s.im| - 1) := by
  have h1 := norm_jPlus_le hs hy
  have h2 := norm_jPlus_le (s := conj s) (by simpa using hs) (by simpa using hy)
  simp only [Complex.conj_im, abs_neg] at h2
  unfold jRot
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  calc ‖jPlus y s - conj (jPlus y (conj s))‖ / 2 ≤ (‖jPlus y s‖ + ‖jPlus y (conj s)‖) / 2 := by
        gcongr
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [Complex.norm_conj]
    _ ≤ (1 / (y - |s.im| - 1) + 1 / (y - |s.im| - 1)) / 2 := by gcongr
    _ = 1 / (y - |s.im| - 1) := by ring

/-- The region `Re s < 3`, `|Im s| < y − 2` where `J(y, ·)` is shown holomorphic. -/
def jRegion (y : ℝ) : Set ℂ := {s | s.re < 3 ∧ |s.im| < y - 2}

theorem isOpen_jRegion (y : ℝ) : IsOpen (jRegion y) :=
  (isOpen_lt Complex.continuous_re continuous_const).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem conj_mem_jRegion {y : ℝ} {s : ℂ} (hs : s ∈ jRegion y) : conj s ∈ jRegion y :=
  ⟨by simpa using hs.1, by simpa using hs.2⟩

/-- `J₊(y, ·)` is holomorphic on `Re s < 3`, `|Im s| < y − 2`. -/
theorem differentiableOn_jPlus (y : ℝ) : DifferentiableOn ℂ (jPlus y) (jRegion y) := by
  have hcont : ∀ s : ℂ, Continuous fun v : ℝ => rotF y s (1 + v * I) := fun s =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (g := rotF y s) (f := fun v : ℝ => 1 + (v : ℂ) * I)
        (differentiableAt_rotF y s (by simp : (0 : ℝ) < (1 + (v : ℂ) * I).re)).continuousAt (by fun_prop)
  have hG := differentiableOn_integral (μ := volume.restrict (Ioi (0 : ℝ))) (isOpen_jRegion y)
    (f := fun s v => rotF y s (1 + v * I)) (g := fun v => Real.exp (-1 * v))
    (fun s _ => (hcont s).aestronglyMeasurable)
    (Eventually.of_forall fun v => fun s _ => ?_) (exp_neg_integrableOn_Ioi 0 one_pos)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v (hv : 0 < v) s hs => ?_))
  · intro s hs
    exact (hG s hs).const_mul I
  · have hne : (1 : ℂ) + v * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    unfold rotF
    exact ((differentiableAt_const _).mul ((differentiableAt_id.sub_const 2).const_cpow
      (Or.inl hne))).differentiableWithinAt
  · refine (norm_rotF_ray_le y hs.1.le hv.le).trans (Real.exp_le_exp.2 ?_)
    have := hs.2
    nlinarith

/-- `J(y, ·)` is holomorphic on `Re s < 3`, `|Im s| < y − 2`. -/
theorem differentiableOn_jRot (y : ℝ) : DifferentiableOn ℂ (jRot y) (jRegion y) := by
  have h1 := differentiableOn_jPlus y
  have h2 : DifferentiableOn ℂ (fun s => conj (jPlus y (conj s))) (jRegion y) := fun s hs => by
    have hd : DifferentiableAt ℂ (jPlus y) (conj s) :=
      h1.differentiableAt ((isOpen_jRegion y).mem_nhds (conj_mem_jRegion hs))
    have := hd.hasDerivAt.conj_conj
    rw [Complex.conj_conj] at this
    exact this.differentiableAt.differentiableWithinAt
  exact (h1.sub h2).div_const _

end Cvs.Upstream.HolomorphicParamIntegralSine

end
