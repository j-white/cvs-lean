import Mathlib
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The defect `F² − F⁴` factors through the exterior sinc columns

For `F y(s) = √(c/2π)∫_{−1}^{1} cos(cst) y(t) dt` and the band function `B_y(u) = (1/π)∫_0^c cos(ωu) Y(ω) dω`,
`Y(ω) = ∫_{−1}^{1} cos(ωt) y(t) dt`: `F²y = B_y` on `[−1, 1]`, `∫_ℝ B_y² = ∫_{−1}^{1}(Fy)²`, and
`B_y(u) = ∫_{−1}^{1} e_u y` for `|u| > 1`; so `⟨(F² − F⁴)y, y'⟩ = 2∫_{u>1} ⟨e_u, y⟩⟨e_u, y'⟩`.
-/

noncomputable section

open Real Set MeasureTheory Filter FourierTransform intervalIntegral

namespace Cvs.Prolate.Hardy.FourierDefectColumns

/-- The cosine transform `Y(ω) = ∫_{−1}^{1} y(t) cos(ωt) dt`. -/
def cosT (y : ℝ → ℝ) (ω : ℝ) : ℝ := ∫ t in (-1 : ℝ)..1, y t * cos (ω * t)

/-- The finite cosine transform `F y(s) = √(c/2π) Y(cs)`. -/
def Fop (c : ℝ) (y : ℝ → ℝ) (s : ℝ) : ℝ := √(c / (2 * π)) * cosT y (c * s)

/-- The band function `B_y(u) = (1/π)∫_0^c cos(ωu) Y(ω) dω`. -/
def bandB (c : ℝ) (y : ℝ → ℝ) (u : ℝ) : ℝ := 1 / π * ∫ ω in (0 : ℝ)..c, cos (ω * u) * cosT y ω

/-- The even exterior sinc column `e_u(t)`. -/
def evenCol (c u t : ℝ) : ℝ := (sin (c * (t - u)) / (π * (t - u)) + sin (c * (-t - u)) / (π * (-t - u))) / 2

theorem continuous_cosT {y : ℝ → ℝ} (hy : Continuous y) : Continuous (cosT y) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop : Continuous fun p : ℝ × ℝ => y p.2 * cos (p.1 * p.2)) _ _

theorem cosT_neg (y : ℝ → ℝ) (ω : ℝ) : cosT y (-ω) = cosT y ω := by
  unfold cosT
  refine integral_congr fun t _ => ?_
  rw [neg_mul, cos_neg]

theorem bandB_neg (c : ℝ) (y : ℝ → ℝ) (u : ℝ) : bandB c y (-u) = bandB c y u := by
  unfold bandB
  refine congrArg (1 / π * ·) (integral_congr fun ω _ => ?_)
  simp only [mul_neg, cos_neg]

/-- `∫_0^c cos(ωd) dω = sin(cd)/d` for `d ≠ 0`. -/
theorem integral_cos_mul {d : ℝ} (hd : d ≠ 0) (c : ℝ) : ∫ ω in (0 : ℝ)..c, cos (ω * d) = sin (c * d) / d := by
  have h : ∀ ω ∈ uIcc (0 : ℝ) c, HasDerivAt (fun ω => sin (ω * d) / d) (cos (ω * d)) ω := by
    intro ω _
    refine (((hasDerivAt_id' ω).mul_const d).sin.div_const d).congr_deriv ?_
    field_simp
  rw [integral_eq_sub_of_hasDerivAt h ((by fun_prop : Continuous fun ω => cos (ω * d)).intervalIntegrable 0 c)]
  simp

/-- `(1/π)∫_0^c cos(ωu)cos(ωt) dω = e_u(t)` for `u ≠ ±t`. -/
theorem integral_cos_mul_cos {c u t : ℝ} (h1 : t - u ≠ 0) (h2 : -t - u ≠ 0) :
    1 / π * ∫ ω in (0 : ℝ)..c, cos (ω * u) * cos (ω * t) = evenCol c u t := by
  have e : (fun ω => cos (ω * u) * cos (ω * t)) = fun ω => (cos (ω * (t - u)) + cos (ω * (-t - u))) / 2 := by
    ext ω
    rw [show ω * (t - u) = ω * t - ω * u by ring, show ω * (-t - u) = -(ω * t + ω * u) by ring, cos_neg,
      cos_sub, cos_add]
    ring
  rw [e, intervalIntegral.integral_div, intervalIntegral.integral_add
    ((by fun_prop : Continuous fun ω => cos (ω * (t - u))).intervalIntegrable 0 c)
    ((by fun_prop : Continuous fun ω => cos (ω * (-t - u))).intervalIntegrable 0 c),
    integral_cos_mul h1, integral_cos_mul h2, evenCol]
  have hπ := Real.pi_pos.ne'
  field_simp

/-- **The band function is the column pairing**: `B_y(u) = ∫_{−1}^{1} e_u y` for `|u| > 1`. -/
theorem bandB_eq {c u : ℝ} {y : ℝ → ℝ} (hy : Continuous y) (hu : 1 < |u|) :
    bandB c y u = ∫ t in (-1 : ℝ)..1, evenCol c u t * y t := by
  have hcont : Continuous (Function.uncurry fun ω t => cos (ω * u) * (y t * cos (ω * t))) := by
    fun_prop
  have hint : IntegrableOn (Function.uncurry fun ω t => cos (ω * u) * (y t * cos (ω * t)))
      (uIoc 0 c ×ˢ uIoc (-1) 1) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hsw : ∫ ω in (0 : ℝ)..c, cos (ω * u) * ∫ t in (-1 : ℝ)..1, y t * cos (ω * t) =
      ∫ t in (-1 : ℝ)..1, ∫ ω in (0 : ℝ)..c, cos (ω * u) * (y t * cos (ω * t)) := by
    simp_rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral_intervalIntegral_swap hint
  unfold bandB cosT
  rw [hsw, ← intervalIntegral.integral_const_mul]
  refine integral_congr fun t ht => ?_
  have ht' : |t| ≤ 1 := by
    rcases mem_uIcc.1 ht with h | h
    · exact abs_le.2 ⟨h.1, h.2⟩
    · exact abs_le.2 ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  have h1 : t - u ≠ 0 := fun h => by
    have : t = u := by linarith
    rw [this] at ht'; linarith
  have h2 : -t - u ≠ 0 := fun h => by
    have : t = -u := by linarith
    rw [this, abs_neg] at ht'; linarith
  rw [← integral_cos_mul_cos (c := c) h1 h2, mul_assoc, ← intervalIntegral.integral_mul_const]
  congr 1
  refine integral_congr fun ω _ => ?_
  ring

/-! ### `F²y` is the band function on `[−1, 1]` -/

/-- `∫_{−a}^{a} g = 2∫_0^a g` for even integrable `g`. -/
theorem integral_even {g : ℝ → ℝ} (hg : Continuous g) (he : ∀ x, g (-x) = g x) (a : ℝ) :
    ∫ x in -a..a, g x = 2 * ∫ x in (0 : ℝ)..a, g x := by
  rw [← integral_add_adjacent_intervals (b := 0) (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have : ∫ x in -a..0, g x = ∫ x in (0 : ℝ)..a, g x := by
    rw [← neg_zero, ← integral_comp_neg]; simp only [he, neg_zero]
  rw [this]; ring

/-- `∫_{−a}^{a} g = 0` for odd continuous `g`. -/
theorem integral_odd {g : ℝ → ℝ} (hg : Continuous g) (ho : ∀ x, g (-x) = -g x) (a : ℝ) :
    ∫ x in -a..a, g x = 0 := by
  rw [← integral_add_adjacent_intervals (b := 0) (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have : ∫ x in -a..0, g x = -∫ x in (0 : ℝ)..a, g x := by
    rw [← neg_zero, ← integral_comp_neg, ← intervalIntegral.integral_neg]; simp only [ho, neg_zero]
  rw [this]; ring

/-- **`F²y = B_y`**: `F(Fy)(s) = (1/π)∫_0^c cos(ωs) Y(ω) dω`. -/
theorem Fop_Fop {c : ℝ} (hc : 0 < c) {y : ℝ → ℝ} (hy : Continuous y) (s : ℝ) :
    Fop c (Fop c y) s = bandB c y s := by
  have hk : √(c / (2 * π)) * √(c / (2 * π)) = c / (2 * π) := Real.mul_self_sqrt (by positivity)
  have hY := continuous_cosT hy
  have e1 : Fop c (Fop c y) s = c / (2 * π) * ∫ t in (-1 : ℝ)..1, cosT y (c * t) * cos (s * (c * t)) := by
    rw [Fop, cosT]
    simp only [Fop]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [show ∀ A B : ℝ, √(c / (2 * π)) * (√(c / (2 * π)) * A * B) = (√(c / (2 * π)) * √(c / (2 * π))) * (A * B)
      from fun A B => by ring, hk, show s * (c * t) = c * s * t by ring]
  rw [e1, intervalIntegral.integral_comp_mul_left (f := fun ω => cosT y ω * cos (s * ω)) hc.ne', smul_eq_mul,
    mul_neg, mul_one, integral_even (by fun_prop) (fun ω => by rw [cosT_neg, mul_neg, cos_neg])]
  unfold bandB
  have hπ := Real.pi_pos.ne'
  rw [show c / (2 * π) * (c⁻¹ * (2 * ∫ x in (0 : ℝ)..c, cosT y x * cos (s * x))) =
    1 / π * ∫ x in (0 : ℝ)..c, cosT y x * cos (s * x) by field_simp]
  congr 1
  apply intervalIntegral.integral_congr
  intro ω _
  simp only; rw [mul_comm ω s]; ring

/-- `∫_{−1}^{1} (Fy)² = (1/π)∫_0^c Y²`. -/
theorem integral_Fop_sq {c : ℝ} (hc : 0 < c) {y : ℝ → ℝ} (hy : Continuous y) :
    ∫ s in (-1 : ℝ)..1, Fop c y s ^ 2 = 1 / π * ∫ ω in (0 : ℝ)..c, cosT y ω ^ 2 := by
  have hk : √(c / (2 * π)) ^ 2 = c / (2 * π) := Real.sq_sqrt (by positivity)
  have hY := continuous_cosT hy
  have e1 : ∫ s in (-1 : ℝ)..1, Fop c y s ^ 2 = c / (2 * π) * ∫ s in (-1 : ℝ)..1, cosT y (c * s) ^ 2 := by
    simp only [Fop]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only; rw [mul_pow, hk]
  rw [e1, intervalIntegral.integral_comp_mul_left (f := fun ω => cosT y ω ^ 2) hc.ne', smul_eq_mul,
    mul_neg, mul_one, integral_even (by fun_prop) (fun ω => by rw [cosT_neg])]
  have hπ := Real.pi_pos.ne'
  field_simp

/-! ### Plancherel for the band function -/

/-- The band function `(1/π)∫_0^c cos(ωu) Y(ω) dω` of a profile `Y`. -/
def bandOf (c : ℝ) (Y : ℝ → ℝ) (u : ℝ) : ℝ := 1 / π * ∫ ω in (0 : ℝ)..c, cos (ω * u) * Y ω

/-- The complex profile `1_{[−c, c]} Y`. -/
def bandExt (c : ℝ) (Y : ℝ → ℝ) : ℝ → ℂ := (Icc (-c) c).indicator fun ω => (Y ω : ℂ)

theorem integrable_bandExt (c : ℝ) {Y : ℝ → ℝ} (hY : Continuous Y) : Integrable (bandExt c Y) := by
  unfold bandExt
  rw [integrable_indicator_iff measurableSet_Icc]
  exact (Complex.continuous_ofReal.comp hY).continuousOn.integrableOn_compact isCompact_Icc

theorem memLp_bandExt (c : ℝ) {Y : ℝ → ℝ} (hY : Continuous Y) : MemLp (bandExt c Y) 2 (volume : Measure ℝ) := by
  unfold bandExt
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_ofReal.comp hY).continuousOn (s := Icc (-c) c)
  refine MemLp.of_bound ((Complex.continuous_ofReal.comp hY).aestronglyMeasurable) M ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hM s hs

/-- `𝓕(1_{[−c, c]} Y)(ξ) = 2π B(2πξ)` for even `Y`. -/
theorem fourier_bandExt {c : ℝ} (hc : 0 ≤ c) {Y : ℝ → ℝ} (hY : Continuous Y) (he : ∀ ω, Y (-ω) = Y ω) (ξ : ℝ) :
    𝓕 (bandExt c Y) ξ = ((2 * π * bandOf c Y (2 * π * ξ) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e1 : (fun ω : ℝ => Complex.exp (↑(-2 * π * ω * ξ) * Complex.I) • bandExt c Y ω) =
      (Icc (-c) c).indicator fun ω => (((cos (2 * π * ξ * ω) * Y ω : ℝ) : ℂ) -
        ((sin (2 * π * ξ * ω) * Y ω : ℝ) : ℂ) * Complex.I) := by
    ext ω
    by_cases hω : ω ∈ Icc (-c) c
    · rw [bandExt, indicator_of_mem hω, indicator_of_mem hω, smul_eq_mul, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        show -2 * π * ω * ξ = -(2 * π * ξ * ω) by ring, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    · rw [bandExt, indicator_of_notMem hω, indicator_of_notMem hω, smul_zero]
  rw [e1, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -c ≤ c)]
  have hcs : Continuous fun ω => cos (2 * π * ξ * ω) * Y ω := by fun_prop
  have hsn : Continuous fun ω => sin (2 * π * ξ * ω) * Y ω := by fun_prop
  have h1 : IntervalIntegrable (fun ω => ((cos (2 * π * ξ * ω) * Y ω : ℝ) : ℂ)) volume (-c) c :=
    (Complex.continuous_ofReal.comp hcs).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun ω => ((sin (2 * π * ξ * ω) * Y ω : ℝ) : ℂ) * Complex.I) volume (-c) c :=
    ((Complex.continuous_ofReal.comp hsn).mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_odd hsn (fun ω => by rw [mul_neg, Real.sin_neg, he]; ring),
    integral_even hcs (fun ω => by rw [mul_neg, Real.cos_neg, he])]
  unfold bandOf
  have hπ := Real.pi_pos.ne'
  push_cast
  have e2 : ∫ ω in (0 : ℝ)..c, cos (ω * (2 * π * ξ)) * Y ω = ∫ ω in (0 : ℝ)..c, cos (2 * π * ξ * ω) * Y ω :=
    intervalIntegral.integral_congr fun ω _ => by rw [mul_comm ω]
  rw [e2]
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast hπ
  field_simp
  ring

theorem sq_bandOf_eq {c : ℝ} (hc : 0 ≤ c) {Y : ℝ → ℝ} (hY : Continuous Y) (he : ∀ ω, Y (-ω) = Y ω) (u : ℝ) :
    bandOf c Y u ^ 2 = ‖𝓕 (bandExt c Y) ((2 * π)⁻¹ * u)‖ ^ 2 / (2 * π) ^ 2 := by
  rw [fourier_bandExt hc hY he, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    show 2 * π * ((2 * π)⁻¹ * u) = u by field_simp]
  have : (2 * π) ^ 2 ≠ 0 := by positivity
  field_simp

theorem integrable_norm_sq_fourier_bandExt (c : ℝ) {Y : ℝ → ℝ} (hY : Continuous Y) :
    Integrable fun ξ => ‖𝓕 (bandExt c Y) ξ‖ ^ 2 := by
  have hF : MemLp (𝓕 (bandExt c Y)) 2 (volume : Measure ℝ) :=
    (Lp.memLp _).ae_eq (Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq (integrable_bandExt c hY) (memLp_bandExt c hY))
  exact (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF

/-- `B² ∈ L¹(ℝ)` for even continuous `Y`. -/
theorem integrable_bandOf_sq {c : ℝ} (hc : 0 ≤ c) {Y : ℝ → ℝ} (hY : Continuous Y) (he : ∀ ω, Y (-ω) = Y ω) :
    Integrable fun u => bandOf c Y u ^ 2 := by
  have h := ((integrable_norm_sq_fourier_bandExt c hY).comp_mul_left' (R := (2 * π)⁻¹) (by positivity)).div_const
    ((2 * π) ^ 2)
  exact h.congr (Filter.Eventually.of_forall fun u => (sq_bandOf_eq hc hY he u).symm)

/-- **Plancherel**: `∫_ℝ B² = (1/π)∫_0^c Y²` for even continuous `Y`. -/
theorem integral_bandOf_sq {c : ℝ} (hc : 0 ≤ c) {Y : ℝ → ℝ} (hY : Continuous Y) (he : ∀ ω, Y (-ω) = Y ω) :
    ∫ u, bandOf c Y u ^ 2 = 1 / π * ∫ ω in (0 : ℝ)..c, Y ω ^ 2 := by
  simp_rw [sq_bandOf_eq hc hY he]
  rw [MeasureTheory.integral_div, Measure.integral_comp_mul_left (fun ξ => ‖𝓕 (bandExt c Y) ξ‖ ^ 2),
    Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_norm_sq_fourier (integrable_bandExt c hY) (memLp_bandExt c hY)]
  have hG : ∫ ω, ‖bandExt c Y ω‖ ^ 2 = 2 * ∫ ω in (0 : ℝ)..c, Y ω ^ 2 := by
    have e : (fun ω => ‖bandExt c Y ω‖ ^ 2) = (Icc (-c) c).indicator fun ω => Y ω ^ 2 := by
      ext ω
      by_cases hω : ω ∈ Icc (-c) c
      · rw [bandExt, indicator_of_mem hω, indicator_of_mem hω, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · rw [bandExt, indicator_of_notMem hω, indicator_of_notMem hω, norm_zero]; ring
    rw [e, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -c ≤ c), integral_even (by fun_prop) (fun ω => by rw [he])]
  rw [hG, smul_eq_mul, inv_inv, abs_of_pos (by positivity)]
  have hπ := Real.pi_pos.ne'
  field_simp

/-! ### The defect identity -/

theorem continuous_Fop (c : ℝ) {y : ℝ → ℝ} (hy : Continuous y) : Continuous (Fop c y) :=
  continuous_const.mul ((continuous_cosT hy).comp (continuous_const.mul continuous_id))

theorem continuous_bandB (c : ℝ) {y : ℝ → ℝ} (hy : Continuous y) : Continuous (bandB c y) := by
  have hY := continuous_cosT hy
  exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop : Continuous fun p : ℝ × ℝ => cos (p.2 * p.1) * cosT y p.2) _ _)

theorem cosT_add {y y' : ℝ → ℝ} (hy : Continuous y) (hy' : Continuous y') (ω : ℝ) :
    cosT (fun t => y t + y' t) ω = cosT y ω + cosT y' ω := by
  unfold cosT
  rw [← intervalIntegral.integral_add ((by fun_prop : Continuous fun t => y t * cos (ω * t)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => y' t * cos (ω * t)).intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr fun t _ => by ring

theorem cosT_sub {y y' : ℝ → ℝ} (hy : Continuous y) (hy' : Continuous y') (ω : ℝ) :
    cosT (fun t => y t - y' t) ω = cosT y ω - cosT y' ω := by
  unfold cosT
  rw [← intervalIntegral.integral_sub ((by fun_prop : Continuous fun t => y t * cos (ω * t)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => y' t * cos (ω * t)).intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr fun t _ => by ring

theorem Fop_add (c : ℝ) {y y' : ℝ → ℝ} (hy : Continuous y) (hy' : Continuous y') :
    Fop c (fun t => y t + y' t) = fun s => Fop c y s + Fop c y' s := by
  ext s; unfold Fop; rw [cosT_add hy hy']; ring

theorem Fop_sub (c : ℝ) {y y' : ℝ → ℝ} (hy : Continuous y) (hy' : Continuous y') :
    Fop c (fun t => y t - y' t) = fun s => Fop c y s - Fop c y' s := by
  ext s; unfold Fop; rw [cosT_sub hy hy']; ring

theorem bandB_add (c : ℝ) {y y' : ℝ → ℝ} (hy : Continuous y) (hy' : Continuous y') (u : ℝ) :
    bandB c (fun t => y t + y' t) u = bandB c y u + bandB c y' u := by
  have h1 := continuous_cosT hy
  have h2 := continuous_cosT hy'
  unfold bandB
  rw [← mul_add, ← intervalIntegral.integral_add
    ((by fun_prop : Continuous fun ω => cos (ω * u) * cosT y ω).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun ω => cos (ω * u) * cosT y' ω).intervalIntegrable _ _)]
  congr 1
  exact intervalIntegral.integral_congr fun ω _ => by rw [cosT_add hy hy']; ring

theorem bandB_sub (c : ℝ) {y y' : ℝ → ℝ} (hy : Continuous y) (hy' : Continuous y') (u : ℝ) :
    bandB c (fun t => y t - y' t) u = bandB c y u - bandB c y' u := by
  have h1 := continuous_cosT hy
  have h2 := continuous_cosT hy'
  unfold bandB
  rw [← mul_sub, ← intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun ω => cos (ω * u) * cosT y ω).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun ω => cos (ω * u) * cosT y' ω).intervalIntegrable _ _)]
  congr 1
  exact intervalIntegral.integral_congr fun ω _ => by rw [cosT_sub hy hy']; ring

theorem integrable_bandB_sq {c : ℝ} (hc : 0 ≤ c) {y : ℝ → ℝ} (hy : Continuous y) :
    Integrable fun u => bandB c y u ^ 2 :=
  integrable_bandOf_sq hc (continuous_cosT hy) (cosT_neg y)

/-- **The quadratic defect**: `∫_{−1}^{1}(Fy)² − ∫_{−1}^{1}(F²y)² = 2∫_{u>1} B_y²`. -/
theorem defect_sq {c : ℝ} (hc : 0 < c) {y : ℝ → ℝ} (hy : Continuous y) :
    (∫ s in (-1 : ℝ)..1, Fop c y s ^ 2) - (∫ s in (-1 : ℝ)..1, Fop c (Fop c y) s ^ 2) =
      2 * ∫ u in Ioi 1, bandB c y u ^ 2 := by
  have hB := continuous_bandB c hy
  have hBi := integrable_bandB_sq hc.le hy
  have hfull : ∫ u, bandB c y u ^ 2 = ∫ s in (-1 : ℝ)..1, Fop c y s ^ 2 := by
    rw [integral_Fop_sq hc hy]
    exact integral_bandOf_sq hc.le (continuous_cosT hy) (cosT_neg y)
  have hFF : ∫ s in (-1 : ℝ)..1, Fop c (Fop c y) s ^ 2 = ∫ s in (-1 : ℝ)..1, bandB c y s ^ 2 :=
    intervalIntegral.integral_congr fun s _ => by rw [Fop_Fop hc hy]
  have heven : ∀ u, bandB c y |u| ^ 2 = bandB c y u ^ 2 := by
    intro u
    rcases abs_choice u with h | h <;> rw [h]
    rw [bandB_neg]
  have hR : ∫ u, bandB c y u ^ 2 = 2 * ∫ u in Ioi 0, bandB c y u ^ 2 := by
    rw [← integral_comp_abs (f := fun u => bandB c y u ^ 2)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => (heven u).symm)
  have hsplit : ∫ u in Ioi 0, bandB c y u ^ 2 = (∫ u in Ioc 0 1, bandB c y u ^ 2) + ∫ u in Ioi 1, bandB c y u ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hBi.integrableOn hBi.integrableOn]
  have hI : ∫ s in (-1 : ℝ)..1, bandB c y s ^ 2 = 2 * ∫ u in Ioc 0 1, bandB c y u ^ 2 := by
    rw [integral_even (by fun_prop) (fun u => by rw [bandB_neg]), intervalIntegral.integral_of_le zero_le_one]
  rw [hFF, hI, ← hfull, hR, hsplit]
  ring

/-- **The defect identity**: `⟨Fy, Fy'⟩ − ⟨F²y, F²y'⟩ = 2∫_{u>1} B_y B_{y'}` on `[−1, 1]`. -/
theorem defect {c : ℝ} (hc : 0 < c) {y y' : ℝ → ℝ} (hy : Continuous y) (hy' : Continuous y') :
    (∫ s in (-1 : ℝ)..1, Fop c y s * Fop c y' s) - (∫ s in (-1 : ℝ)..1, Fop c (Fop c y) s * Fop c (Fop c y') s) =
      2 * ∫ u in Ioi 1, bandB c y u * bandB c y' u := by
  have hp := defect_sq hc (y := fun t => y t + y' t) (hy.add hy')
  have hm := defect_sq hc (y := fun t => y t - y' t) (hy.sub hy')
  have hF := continuous_Fop c hy
  have hF' := continuous_Fop c hy'
  have hFF := continuous_Fop c hF
  have hFF' := continuous_Fop c hF'
  rw [Fop_add c hy hy', Fop_add c hF hF'] at hp
  rw [Fop_sub c hy hy', Fop_sub c hF hF'] at hm
  simp_rw [bandB_add c hy hy'] at hp
  simp_rw [bandB_sub c hy hy'] at hm
  have hBi := (integrable_bandB_sq hc.le hy).integrableOn (s := Ioi 1)
  have hBi' := (integrable_bandB_sq hc.le hy').integrableOn (s := Ioi 1)
  have hprod : IntegrableOn (fun u => bandB c y u * bandB c y' u) (Ioi 1) := by
    refine (hBi.add hBi').mono' ((continuous_bandB c hy).mul (continuous_bandB c hy')).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun u => ?_
    show ‖bandB c y u * bandB c y' u‖ ≤ bandB c y u ^ 2 + bandB c y' u ^ 2
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|bandB c y u| - |bandB c y' u|), sq_abs (bandB c y u), sq_abs (bandB c y' u)]
  have hq : IntegrableOn (fun u => 2 * (bandB c y u * bandB c y' u)) (Ioi 1) := hprod.const_mul 2
  have hpl : IntegrableOn (fun u => bandB c y u ^ 2 + 2 * (bandB c y u * bandB c y' u)) (Ioi 1) := hBi.add hq
  have hmi : IntegrableOn (fun u => bandB c y u ^ 2 - 2 * (bandB c y u * bandB c y' u)) (Ioi 1) := hBi.sub hq
  have e1 : ∫ u in Ioi 1, (bandB c y u + bandB c y' u) ^ 2 =
      (∫ u in Ioi 1, bandB c y u ^ 2) + 2 * (∫ u in Ioi 1, bandB c y u * bandB c y' u) +
        ∫ u in Ioi 1, bandB c y' u ^ 2 := by
    rw [show (fun u => (bandB c y u + bandB c y' u) ^ 2) =
      fun u => bandB c y u ^ 2 + 2 * (bandB c y u * bandB c y' u) + bandB c y' u ^ 2 by ext u; ring,
      integral_add hpl hBi', integral_add hBi hq, MeasureTheory.integral_const_mul]
  have e2 : ∫ u in Ioi 1, (bandB c y u - bandB c y' u) ^ 2 =
      (∫ u in Ioi 1, bandB c y u ^ 2) - 2 * (∫ u in Ioi 1, bandB c y u * bandB c y' u) +
        ∫ u in Ioi 1, bandB c y' u ^ 2 := by
    rw [show (fun u => (bandB c y u - bandB c y' u) ^ 2) =
      fun u => bandB c y u ^ 2 - 2 * (bandB c y u * bandB c y' u) + bandB c y' u ^ 2 by ext u; ring,
      integral_add hmi hBi', integral_sub hBi hq, MeasureTheory.integral_const_mul]
  have i1 : ∀ {f g : ℝ → ℝ}, Continuous f → Continuous g →
      ∫ s in (-1 : ℝ)..1, (f s + g s) ^ 2 = (∫ s in (-1 : ℝ)..1, f s ^ 2) + 2 * (∫ s in (-1 : ℝ)..1, f s * g s) +
        ∫ s in (-1 : ℝ)..1, g s ^ 2 := by
    intro f g hf hg
    have h1 : IntervalIntegrable (fun s => f s ^ 2) volume (-1) 1 := (hf.pow 2).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s => 2 * (f s * g s)) volume (-1) 1 :=
      ((hf.mul hg).const_mul 2).intervalIntegrable _ _
    have h3 : IntervalIntegrable (fun s => g s ^ 2) volume (-1) 1 := (hg.pow 2).intervalIntegrable _ _
    have h12 : IntervalIntegrable (fun s => f s ^ 2 + 2 * (f s * g s)) volume (-1) 1 := h1.add h2
    rw [show (fun s => (f s + g s) ^ 2) = fun s => f s ^ 2 + 2 * (f s * g s) + g s ^ 2 by ext s; ring,
      intervalIntegral.integral_add h12 h3, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]
  have i2 : ∀ {f g : ℝ → ℝ}, Continuous f → Continuous g →
      ∫ s in (-1 : ℝ)..1, (f s - g s) ^ 2 = (∫ s in (-1 : ℝ)..1, f s ^ 2) - 2 * (∫ s in (-1 : ℝ)..1, f s * g s) +
        ∫ s in (-1 : ℝ)..1, g s ^ 2 := by
    intro f g hf hg
    have h1 : IntervalIntegrable (fun s => f s ^ 2) volume (-1) 1 := (hf.pow 2).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s => 2 * (f s * g s)) volume (-1) 1 :=
      ((hf.mul hg).const_mul 2).intervalIntegrable _ _
    have h3 : IntervalIntegrable (fun s => g s ^ 2) volume (-1) 1 := (hg.pow 2).intervalIntegrable _ _
    have h12 : IntervalIntegrable (fun s => f s ^ 2 - 2 * (f s * g s)) volume (-1) 1 := h1.sub h2
    rw [show (fun s => (f s - g s) ^ 2) = fun s => f s ^ 2 - 2 * (f s * g s) + g s ^ 2 by ext s; ring,
      intervalIntegral.integral_add h12 h3, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  rw [i1 hF hF', i1 hFF hFF', e1] at hp
  rw [i2 hF hF', i2 hFF hFF', e2] at hm
  linarith

end Cvs.Prolate.Hardy.FourierDefectColumns

end
