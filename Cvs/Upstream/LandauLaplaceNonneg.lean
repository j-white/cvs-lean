import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Landau's theorem for the Laplace transform of a nonnegative function

For `g ≥ 0` on `(0, ∞)` whose Laplace transform converges at every abscissa above `σ`, the transform
`lap g z = ∫₀^∞ g(L) e^{−zL} dL` is holomorphic on `Re z > σ` with iterated derivatives `∫ (−L)ⁿ g e^{−zL}`,
and if it agrees there with a function holomorphic on a ball around the real point `σ`, the integral converges
below `σ` (`conv_of_analytic`): the Taylor series at `σ + r/4` has nonnegative terms, so Tonelli sums it.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology

namespace Cvs.Upstream.LandauLaplaceNonneg

/-- Absolute convergence of the Laplace transform of `g` at the real abscissa `σ`. -/
def Conv (g : ℝ → ℝ) (σ : ℝ) : Prop :=
  IntegrableOn (fun L => g L * Real.exp (-(σ * L))) (Ioi 0)

/-- Convergence at every abscissa above `σ`. -/
def ConvAbove (g : ℝ → ℝ) (σ : ℝ) : Prop := ∀ τ, σ < τ → Conv g τ

/-- The Laplace transform as a function of a complex variable. -/
def lap (g : ℝ → ℝ) (z : ℂ) : ℂ := ∫ L in Ioi (0:ℝ), (g L : ℂ) * Complex.exp (-(z * L))

/-- The `(−L)ⁿ`-weighted transforms: the iterated derivatives of `lap g`. -/
def lapn (g : ℝ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ L in Ioi (0:ℝ), (-(L:ℂ)) ^ n * (g L : ℂ) * Complex.exp (-(z * L))

/-- The real moments `∫₀^∞ Lⁿ g(L) e^{−cL} dL`. -/
def moment (g : ℝ → ℝ) (n : ℕ) (c : ℝ) : ℝ := ∫ L in Ioi (0:ℝ), L ^ n * g L * Real.exp (-(c * L))

/-! ### Term-by-term integration, a.e.-measurable form -/

/-- **Term-by-term integration for a nonnegative series** (`OneCellLaplaceTransform`'s lemma with a.e.-strong measurability). -/
theorem integrable_tsum_of_nonneg' {μ : Measure ℝ} {F : ℕ → ℝ → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (F n) μ)
    (hnn : ∀ n L, 0 ≤ F n L) (hpt : ∀ L, Summable fun n => F n L) (hint : ∀ n, Integrable (F n) μ)
    (hsum : Summable fun n => ∫ L, F n L ∂μ) :
    Integrable (fun L => ∑' n, F n L) μ ∧ ∫ L, ∑' n, F n L ∂μ = ∑' n, ∫ L, F n L ∂μ := by
  have hrepr : (fun L => ∑' n, F n L) = fun L => (∑' n, ENNReal.ofReal (F n L)).toReal := by
    funext L
    rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
    congr 1
    funext n
    rw [ENNReal.toReal_ofReal (hnn n L)]
  have hmeas : AEStronglyMeasurable (fun L => ∑' n, F n L) μ := by
    rw [hrepr]
    exact ((AEMeasurable.tsum fun n => (hm n).aemeasurable.ennreal_ofReal).ennreal_toReal)
      |>.aestronglyMeasurable
  have hlin : ∀ n, ∫⁻ L, ‖F n L‖ₑ ∂μ = ENNReal.ofReal (∫ L, F n L ∂μ) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (hnn n))]
    congr 1
    funext L
    rw [Real.eNorm_eq_ofReal (hnn n L)]
  have hfin : ∑' n, ∫⁻ L, ‖F n L‖ₑ ∂μ ≠ ⊤ := by
    simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (hnn n)) hsum]
    exact ENNReal.ofReal_ne_top
  refine ⟨⟨hmeas, ?_⟩, integral_tsum (fun n => hm n) hfin⟩
  rw [HasFiniteIntegral]
  have h1 : ∀ L, ‖∑' n, F n L‖ₑ = ∑' n, ENNReal.ofReal (F n L) := by
    intro L
    rw [Real.eNorm_eq_ofReal (tsum_nonneg fun n => hnn n L),
      ENNReal.ofReal_tsum_of_nonneg (hnn · L) (hpt L)]
  simp_rw [h1]
  rw [lintegral_tsum fun n => (hm n).aemeasurable.ennreal_ofReal]
  have : ∑' n, ∫⁻ L, ENNReal.ofReal (F n L) ∂μ = ∑' n, ∫⁻ L, ‖F n L‖ₑ ∂μ := by
    congr 1; funext n; congr 1; funext L; rw [Real.eNorm_eq_ofReal (hnn n L)]
  rw [this]
  exact lt_top_iff_ne_top.2 hfin

/-! ### Convergence -/

variable {g : ℝ → ℝ}

theorem Conv.mono (hg0 : ∀ L, 0 < L → 0 ≤ g L) (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {σ τ : ℝ} (hσ : Conv g σ) (hστ : σ ≤ τ) : Conv g τ := by
  refine hσ.mono' (hgm.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun L hL => ?_)
  have hL : 0 < L := hL
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 L hL) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (hg0 L hL)

theorem Conv.convAbove (hg0 : ∀ L, 0 < L → 0 ≤ g L) (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {σ : ℝ} (hσ : Conv g σ) : ConvAbove g σ :=
  fun _ hτ => hσ.mono hg0 hgm hτ.le

/-- `Lⁿ ≤ n!/δⁿ · e^{δL}` for `L ≥ 0`, `δ > 0`. -/
theorem pow_le_exp_mul {δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L) (n : ℕ) :
    L ^ n ≤ (n.factorial / δ ^ n) * Real.exp (δ * L) := by
  have h := Real.pow_div_factorial_le_exp (δ * L) (mul_nonneg hδ.le hL) n
  rw [mul_pow] at h
  have hn : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hδn : 0 < δ ^ n := pow_pos hδ n
  rw [div_le_iff₀ hn] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hδn]
  nlinarith [h]

/-- The real moments converge above the abscissa. -/
theorem integrableOn_pow_mul (hg0 : ∀ L, 0 < L → 0 ≤ g L)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {σ c : ℝ} (hσ : Conv g σ) (hc : σ < c) (n : ℕ) :
    IntegrableOn (fun L => L ^ n * g L * Real.exp (-(c * L))) (Ioi 0) := by
  set δ := c - σ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine (hσ.const_mul (n.factorial / δ ^ n)).mono'
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul hgm |>.mul
      (Continuous.aestronglyMeasurable (by fun_prop))) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun L hL => ?_)
  have hL : 0 < L := hL
  have hgL := hg0 L hL
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := pow_le_exp_mul hδ0 hL.le n
  have h2 : Real.exp (δ * L) * Real.exp (-(c * L)) = Real.exp (-(σ * L)) := by
    rw [← Real.exp_add]; congr 1; rw [hδ]; ring
  calc L ^ n * g L * Real.exp (-(c * L))
      ≤ (n.factorial / δ ^ n) * Real.exp (δ * L) * g L * Real.exp (-(c * L)) := by gcongr
    _ = (n.factorial / δ ^ n) * (g L * Real.exp (-(σ * L))) := by rw [← h2]; ring

/-- The complex integrands converge on `Re z > σ`. -/
theorem integrableOn_lapn (hg0 : ∀ L, 0 < L → 0 ≤ g L)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {σ : ℝ} {z : ℂ} (hσ : Conv g σ) (hz : σ < z.re) (n : ℕ) :
    IntegrableOn (fun L : ℝ => (-(L:ℂ)) ^ n * (g L : ℂ) * Complex.exp (-(z * L))) (Ioi 0) := by
  refine (integrableOn_pow_mul hg0 hgm hσ hz n).mono'
    (((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hgm)).mul
      (Continuous.aestronglyMeasurable (by fun_prop))) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun L hL => ?_)
  have hL : 0 < L := hL
  have hgL := hg0 L hL
  rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real, Complex.norm_exp,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL, abs_of_nonneg hgL]
  have : (-(z * (L:ℂ))).re = -(z.re * L) := by simp [Complex.mul_re]
  rw [this]

/-! ### Holomorphy and the iterated derivatives -/

theorem hasDerivAt_lapn (hg0 : ∀ L, 0 < L → 0 ≤ g L)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {σ : ℝ} {z : ℂ} (hσ : Conv g σ) (hz : σ < z.re) (n : ℕ) :
    HasDerivAt (lapn g n) (lapn g (n + 1) z) z := by
  set ε := (z.re - σ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hmeas : ∀ x : ℂ, AEStronglyMeasurable
      (fun L : ℝ => (-(L:ℂ)) ^ n * (g L : ℂ) * Complex.exp (-(x * L))) (volume.restrict (Ioi 0)) :=
    fun x => ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hgm)).mul
      (Continuous.aestronglyMeasurable (by fun_prop))
  have hmeas' : ∀ x : ℂ, AEStronglyMeasurable
      (fun L : ℝ => (-(L:ℂ)) ^ (n + 1) * (g L : ℂ) * Complex.exp (-(x * L))) (volume.restrict (Ioi 0)) :=
    fun x => ((Continuous.aestronglyMeasurable (by fun_prop)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hgm)).mul
      (Continuous.aestronglyMeasurable (by fun_prop))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (x : ℂ) (L : ℝ) => (-(L:ℂ)) ^ n * (g L : ℂ) * Complex.exp (-(x * L)))
    (F' := fun (x : ℂ) (L : ℝ) => (-(L:ℂ)) ^ (n + 1) * (g L : ℂ) * Complex.exp (-(x * L)))
    (bound := fun L => ((n + 1).factorial / ε ^ (n + 1)) * (g L * Real.exp (-(σ * L))))
    (Metric.ball_mem_nhds z hε0) (Eventually.of_forall hmeas) (integrableOn_lapn hg0 hgm hσ hz n)
    (hmeas' z) ?_ (hσ.const_mul _) ?_
  · exact key.2
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun L hL x hx => ?_)
    have hL : 0 < L := hL
    have hgL := hg0 L hL
    have hxre : σ + ε < x.re := by
      have := Complex.abs_re_le_norm (x - z)
      rw [Metric.mem_ball, Complex.dist_eq] at hx
      have := abs_lt.1 (this.trans_lt hx)
      simp only [Complex.sub_re] at this
      linarith [this.1, hε]
    rw [norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_real, Complex.norm_real, Complex.norm_exp,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL, abs_of_nonneg hgL]
    have : (-(x * (L:ℂ))).re = -(x.re * L) := by simp [Complex.mul_re]
    rw [this]
    have h1 := pow_le_exp_mul hε0 hL.le (n + 1)
    have h2 : Real.exp (-(x.re * L)) ≤ Real.exp (-((σ + ε) * L)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 : Real.exp (ε * L) * Real.exp (-((σ + ε) * L)) = Real.exp (-(σ * L)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc L ^ (n + 1) * g L * Real.exp (-(x.re * L))
        ≤ ((n + 1).factorial / ε ^ (n + 1)) * Real.exp (ε * L) * g L * Real.exp (-((σ + ε) * L)) := by
          gcongr
      _ = ((n + 1).factorial / ε ^ (n + 1)) * (g L * Real.exp (-(σ * L))) := by rw [← h3]; ring
  · refine ae_of_all _ fun L x _ => ?_
    have h := ((((hasDerivAt_id x).mul_const (L:ℂ)).neg).cexp).const_mul ((-(L:ℂ)) ^ n * (g L : ℂ))
    refine HasDerivAt.congr_deriv (by exact h) ?_
    simp only [id, one_mul, pow_succ, Pi.neg_apply]
    ring

theorem lap_eq_lapn_zero (g : ℝ → ℝ) : lap g = lapn g 0 := by
  funext z; unfold lap lapn; simp

theorem differentiableOn_lap (hg0 : ∀ L, 0 < L → 0 ≤ g L)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {σ : ℝ} (hσ : ConvAbove g σ) : DifferentiableOn ℂ (lap g) {z | σ < z.re} := by
  intro z hz
  have hz' : σ < z.re := hz
  have hτ : Conv g ((σ + z.re) / 2) := hσ _ (by linarith)
  rw [lap_eq_lapn_zero]
  exact (hasDerivAt_lapn hg0 hgm hτ (by linarith) 0).differentiableAt.differentiableWithinAt

theorem isOpen_halfPlane (σ : ℝ) : IsOpen {z : ℂ | σ < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem iteratedDeriv_lap (hg0 : ∀ L, 0 < L → 0 ≤ g L)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {σ : ℝ} (hσ : ConvAbove g σ) (n : ℕ) {z : ℂ} (hz : σ < z.re) :
    iteratedDeriv n (lap g) z = lapn g n z := by
  induction n generalizing z with
  | zero => rw [lap_eq_lapn_zero]; simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (lap g) =ᶠ[𝓝 z] lapn g n :=
      Filter.eventually_of_mem ((isOpen_halfPlane σ).mem_nhds hz) fun w hw => ih hw
    rw [hev.deriv_eq]
    have hτ : Conv g ((σ + z.re) / 2) := hσ _ (by linarith)
    exact (hasDerivAt_lapn hg0 hgm hτ (by linarith) n).deriv

/-- At a real point the weighted transform is `(−1)ⁿ` times the real moment. -/
theorem lapn_real (g : ℝ → ℝ) (n : ℕ) (c : ℝ) :
    lapn g n (c : ℂ) = (((-1) ^ n * moment g n c : ℝ) : ℂ) := by
  have hfun : (fun L : ℝ => (-(L:ℂ)) ^ n * (g L : ℂ) * Complex.exp (-((c:ℂ) * L)))
      = fun L => (((-1) ^ n * (L ^ n * g L * Real.exp (-(c * L))) : ℝ) : ℂ) := by
    funext L
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_exp]
    ring
  unfold lapn moment
  rw [hfun, integral_complex_ofReal, integral_const_mul]

/-! ### Landau -/

/-- **Landau's theorem for Laplace transforms.** If `g ≥ 0` has a transform converging above `σ`, and a function
holomorphic on the ball of radius `r` about the real point `σ` agrees with the transform on the part of the ball
right of `σ`, then the transform converges at `σ − r/4`. -/
theorem conv_of_analytic (hg0 : ∀ L, 0 < L → 0 ≤ g L)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {σ : ℝ} (hσ : ConvAbove g σ) {F : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball (σ : ℂ) r))
    (hFeq : ∀ z ∈ Metric.ball (σ : ℂ) r, σ < z.re → F z = lap g z) :
    Conv g (σ - r / 4) := by
  set c : ℝ := σ + r / 4 with hc
  set s : ℝ := σ - r / 4 with hs
  have hcσ : σ < c := by rw [hc]; linarith
  have hτ : Conv g (σ + r / 8) := hσ _ (by linarith)
  have hτc : σ + r / 8 < c := by rw [hc]; linarith
  -- the ball about `c` of radius `3r/4` lies in the ball about `σ` of radius `r`
  have hsub : Metric.ball (c : ℂ) (3 * r / 4) ⊆ Metric.ball (σ : ℂ) r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have h1 : dist (c : ℂ) (σ : ℂ) = r / 4 := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hc,
        show σ + r / 4 - σ = r / 4 by ring, abs_of_pos (by linarith)]
    calc dist z (σ : ℂ) ≤ dist z (c : ℂ) + dist (c : ℂ) (σ : ℂ) := dist_triangle _ _ _
      _ < 3 * r / 4 + r / 4 := by rw [h1]; linarith
      _ = r := by ring
  have hF' : DifferentiableOn ℂ F (Metric.ball (c : ℂ) (3 * r / 4)) := hF.mono hsub
  -- near `c`, `F = lap g`
  have hev : F =ᶠ[𝓝 (c : ℂ)] lap g := by
    filter_upwards [Metric.ball_mem_nhds (c : ℂ) (show (0:ℝ) < r / 4 by linarith)] with z hz
    have hz1 : z ∈ Metric.ball (σ : ℂ) r := hsub (Metric.ball_subset_ball (by linarith) hz)
    have hz2 : σ < z.re := by
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have := abs_lt.1 ((Complex.abs_re_le_norm (z - c)).trans_lt hz)
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      linarith [this.1]
    exact hFeq z hz1 hz2
  -- Taylor at `c`, evaluated at the real point `s`
  have hsball : (s : ℂ) ∈ Metric.ball (c : ℂ) (3 * r / 4) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hs, hc,
      show σ - r / 4 - (σ + r / 4) = -(r / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have htaylor := Complex.hasSum_taylorSeries_on_ball hF' hsball
  have hterm : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ • ((s : ℂ) - c) ^ n • iteratedDeriv n F (c : ℂ)
      = ((moment g n c * (c - s) ^ n / n.factorial : ℝ) : ℂ) := by
    intro n
    rw [smul_eq_mul, smul_eq_mul, hev.iteratedDeriv_eq n,
      iteratedDeriv_lap hg0 hgm hσ n (by simpa using hcσ), lapn_real g n c]
    push_cast
    have : ((s : ℂ) - c) ^ n = (-1) ^ n * ((c : ℂ) - s) ^ n := by
      rw [← mul_pow]; congr 1; ring
    rw [this]
    have h1 : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp
    linear_combination (moment g n c * ((c : ℂ) - s) ^ n) * h1
  rw [show (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • ((s : ℂ) - c) ^ n • iteratedDeriv n F (c : ℂ))
      = fun n => ((moment g n c * (c - s) ^ n / n.factorial : ℝ) : ℂ) from funext hterm] at htaylor
  have hsum : Summable fun n : ℕ => moment g n c * (c - s) ^ n / n.factorial :=
    Complex.summable_ofReal.1 htaylor.summable
  -- the nonnegative series whose integral is the Taylor series
  set F2 : ℕ → ℝ → ℝ := fun n L => (c - s) ^ n * max L 0 ^ n / n.factorial * max (g L) 0 * Real.exp (-(c * L))
    with hF2
  have hcs : 0 < c - s := by rw [hc, hs]; linarith
  have hmax : AEStronglyMeasurable (fun L => max (g L) 0) (volume.restrict (Ioi 0)) :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable hgm
  have hm : ∀ n, AEStronglyMeasurable (F2 n) (volume.restrict (Ioi 0)) := fun n =>
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul hmax).mul (Continuous.aestronglyMeasurable (by fun_prop))
  have hnn : ∀ n L, 0 ≤ F2 n L := fun n L => by
    simp only [hF2]
    have : 0 ≤ max (g L) 0 := le_max_right _ _
    positivity
  have hpt : ∀ L, Summable fun n => F2 n L := by
    intro L
    have := (Real.summable_pow_div_factorial ((c - s) * max L 0)).mul_right (max (g L) 0 * Real.exp (-(c * L)))
    refine this.congr fun n => ?_
    simp only [hF2]; rw [mul_pow]; ring
  have hagree : ∀ n, ∀ L ∈ Ioi (0:ℝ), F2 n L = ((c - s) ^ n / n.factorial) * (L ^ n * g L * Real.exp (-(c * L))) := by
    intro n L hL
    have hL : 0 < L := hL
    simp only [hF2]
    rw [max_eq_left hL.le, max_eq_left (hg0 L hL)]; ring
  have hint : ∀ n, Integrable (F2 n) (volume.restrict (Ioi 0)) := fun n => by
    have hI0 : IntegrableOn (fun L => ((c - s) ^ n / n.factorial) * (L ^ n * g L * Real.exp (-(c * L))))
        (Ioi 0) := (integrableOn_pow_mul hg0 hgm hτ hτc n).const_mul _
    exact hI0.congr_fun (fun L hL => (hagree n L hL).symm) measurableSet_Ioi
  have hval : ∀ n, ∫ L in Ioi (0:ℝ), F2 n L = moment g n c * (c - s) ^ n / n.factorial := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioi (hagree n), integral_const_mul]
    unfold moment; ring
  have hsum' : Summable fun n => ∫ L in Ioi (0:ℝ), F2 n L := by simp_rw [hval]; exact hsum
  obtain ⟨hI, -⟩ := integrable_tsum_of_nonneg' hm hnn hpt hint hsum'
  -- the series sums to `g e^{−sL}` on `(0, ∞)`
  have hexp : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have htot : ∀ L ∈ Ioi (0:ℝ), ∑' n, F2 n L = g L * Real.exp (-(s * L)) := by
    intro L hL
    have hL : 0 < L := hL
    have h := (hexp ((c - s) * L)).mul_right (g L * Real.exp (-(c * L)))
    have e1 : Real.exp ((c - s) * L) * Real.exp (-(c * L)) = Real.exp (-(s * L)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e : g L * Real.exp (-(s * L)) = Real.exp ((c - s) * L) * (g L * Real.exp (-(c * L))) := by
      rw [← e1]; ring
    rw [e, ← h.tsum_eq]
    congr 1
    funext n
    rw [hagree n L hL, mul_pow]; ring
  exact (show IntegrableOn (fun L => ∑' n, F2 n L) (Ioi 0) volume from hI).congr_fun htot measurableSet_Ioi

end Cvs.Upstream.LandauLaplaceNonneg
