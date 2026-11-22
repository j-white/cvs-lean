import Mathlib
import Cvs.Prolate.ForbiddenZoneGrowth
import Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.PlungeLawIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The forbidden zone in closed form

`Z(√χ/c) ≥ π(c² − χ)/(4c)` against the antiderivative `(c/2)(A arcsin(√(s² − a²)/√A) − √(s² − a²)√(1 − s²))`,
`a = √χ/c`, `A = 1 − a²`. `Φ_C` is monotone and 1-Lipschitz with `e^{−2Φ_C} = e^{3−2r}(r + ½)/2`, `r = √(Z² + 9/4)`;
`K ≤ (c/σ)π/2`; the phase drops by at most `(4/3)c(s − a)^{3/2}/√(1 − a)` near `a`, so `J ≥ d e^{2Φ_C(Z(a)) − 2}`.
-/

namespace Cvs.Prolate.ForbiddenZoneClosedForm

open Real Set Filter Topology MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.ForbiddenZoneGrowth Cvs.Prolate.PlungeLawIntegral

/-- `G(s) = (c/2)((1 − a²) arcsin(√(s² − a²)/√(1 − a²)) − √(s² − a²)√(1 − s²))`, an antiderivative of
`c s√(s² − a²)/√(1 − s²)` on `(a, 1)` vanishing at `a`. -/
noncomputable def forbG (c a s : ℝ) : ℝ :=
  c / 2 * ((1 - a ^ 2) * arcsin (√(s ^ 2 - a ^ 2) / √(1 - a ^ 2)) - √(s ^ 2 - a ^ 2) * √(1 - s ^ 2))

theorem continuous_forbG (c a : ℝ) : Continuous (forbG c a) := by
  have h1 : Continuous fun s : ℝ => √(s ^ 2 - a ^ 2) / √(1 - a ^ 2) := by fun_prop
  have h2 : Continuous fun s : ℝ => √(s ^ 2 - a ^ 2) * √(1 - s ^ 2) := by fun_prop
  exact continuous_const.mul ((continuous_const.mul (continuous_arcsin.comp h1)).sub h2)

theorem forbG_left (c a : ℝ) : forbG c a a = 0 := by
  unfold forbG; simp

theorem forbG_one {c a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) : forbG c a 1 = c / 2 * (1 - a ^ 2) * (π / 2) := by
  have hA : 0 < √(1 - a ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  unfold forbG
  rw [one_pow, div_self hA.ne', arcsin_one]
  simp only [sub_self, Real.sqrt_zero, mul_zero, sub_zero]
  ring

/-- `G' = c s√(s² − a²)/√(1 − s²)` on `(a, 1)`. -/
theorem hasDerivAt_forbG {c a s : ℝ} (ha0 : 0 ≤ a) (hs : s ∈ Ioo a 1) :
    HasDerivAt (forbG c a) (c * s * √(s ^ 2 - a ^ 2) / √(1 - s ^ 2)) s := by
  have hs0 : 0 < s := lt_of_le_of_lt ha0 hs.1
  have hx : 0 < s ^ 2 - a ^ 2 := by nlinarith [hs.1]
  have hy : 0 < 1 - s ^ 2 := by nlinarith [hs.2]
  have hA : 0 < 1 - a ^ 2 := by nlinarith [hs.1, hs.2]
  have hAne := hA.ne'
  have hX0 : 0 < √(s ^ 2 - a ^ 2) := Real.sqrt_pos.mpr hx
  have hY0 : 0 < √(1 - s ^ 2) := Real.sqrt_pos.mpr hy
  have hR0 : 0 < √(1 - a ^ 2) := Real.sqrt_pos.mpr hA
  have hX2 : √(s ^ 2 - a ^ 2) ^ 2 = s ^ 2 - a ^ 2 := Real.sq_sqrt hx.le
  have hY2 : √(1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hy.le
  have hR2 : √(1 - a ^ 2) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt hA.le
  have hdx : HasDerivAt (fun s : ℝ => s ^ 2 - a ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).sub_const (a ^ 2)
  have hdy : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_sub 1
  have hdX : HasDerivAt (fun s : ℝ => √(s ^ 2 - a ^ 2)) (2 * s / (2 * √(s ^ 2 - a ^ 2))) s := hdx.sqrt hx.ne'
  have hdY : HasDerivAt (fun s : ℝ => √(1 - s ^ 2)) (-(2 * s) / (2 * √(1 - s ^ 2))) s := hdy.sqrt hy.ne'
  have hv0 : 0 < √(s ^ 2 - a ^ 2) / √(1 - a ^ 2) := div_pos hX0 hR0
  have hv1 : √(s ^ 2 - a ^ 2) / √(1 - a ^ 2) < 1 := by
    rw [div_lt_one hR0]; exact Real.sqrt_lt_sqrt hx.le (by nlinarith [hs.2])
  have hdA : HasDerivAt (fun s : ℝ => arcsin (√(s ^ 2 - a ^ 2) / √(1 - a ^ 2)))
      (1 / √(1 - (√(s ^ 2 - a ^ 2) / √(1 - a ^ 2)) ^ 2) * (2 * s / (2 * √(s ^ 2 - a ^ 2)) / √(1 - a ^ 2))) s := by
    have h0 := (Real.hasDerivAt_arcsin (x := √(s ^ 2 - a ^ 2) / √(1 - a ^ 2)) (ne_of_gt (by linarith)) hv1.ne).comp s
      (hdX.div_const (√(1 - a ^ 2)))
    exact h0
  have hW : √(1 - (√(s ^ 2 - a ^ 2) / √(1 - a ^ 2)) ^ 2) = √(1 - s ^ 2) / √(1 - a ^ 2) := by
    rw [div_pow, hX2, hR2, show 1 - (s ^ 2 - a ^ 2) / (1 - a ^ 2) = (1 - s ^ 2) / (1 - a ^ 2) by
      field_simp; ring, Real.sqrt_div hy.le]
  have h := ((hdA.const_mul (1 - a ^ 2)).sub (hdX.mul hdY)).const_mul (c / 2)
  refine h.congr_deriv ?_
  rw [hW]
  field_simp
  linear_combination (-c) * hY2 + (-c) * hX2

/-- **P10, the forbidden-zone phase**: `Z(√χ/c) ≥ π(c² − χ)/(4c) = πS/4`, `S = (c² − χ)/c`; `Z + G` is antitone on
`[√χ/c, 1]` with `G(1) = (c/2)(1 − χ/c²)π/2`. -/
theorem forbZ_ge {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    π * (c ^ 2 - χ) / (4 * c) ≤ forbZ c χ (√χ / c) := by
  set a := √χ / c with ha
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hc.le
  have ha1 : a < 1 := by rw [ha, div_lt_one hc, Real.sqrt_lt' hc]; exact hχc
  have hca : c ^ 2 * a ^ 2 = χ := by rw [ha, div_pow, Real.sq_sqrt hχ0]; field_simp
  have hq : ∀ s, qP c χ s = c ^ 2 * (s ^ 2 - a ^ 2) := fun s => by unfold qP; rw [← hca]; ring
  set H : ℝ → ℝ := fun s => forbZ c χ s + forbG c a s with hH
  have hHc : ContinuousOn H (Icc a 1) :=
    ((continuousOn_forbZ c χ).mono (Icc_subset_Icc ha0 le_rfl)).add (continuous_forbG c a).continuousOn
  have hHd : ∀ s ∈ Ioo a 1, HasDerivAt H
      (-(√(qP c χ s) / √(1 - s ^ 2)) + c * s * √(s ^ 2 - a ^ 2) / √(1 - s ^ 2)) s :=
    fun s hs => (hasDerivAt_forbZ c χ ⟨by linarith [hs.1], hs.2⟩).add (hasDerivAt_forbG ha0 hs)
  have hanti : AntitoneOn H (Icc a 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a 1) hHc
    · rw [interior_Icc]; exact fun s hs => (hHd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro s hs
      rw [(hHd s hs).deriv, hq, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
      have h0 : 0 ≤ √(s ^ 2 - a ^ 2) / √(1 - s ^ 2) := by positivity
      have e : -(c * √(s ^ 2 - a ^ 2) / √(1 - s ^ 2)) + c * s * √(s ^ 2 - a ^ 2) / √(1 - s ^ 2)
          = c * (s - 1) * (√(s ^ 2 - a ^ 2) / √(1 - s ^ 2)) := by ring
      rw [e]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith [hs.2])) h0
  have h := hanti ⟨le_rfl, ha1.le⟩ ⟨ha1.le, le_rfl⟩ ha1.le
  simp only [hH, forbZ_one, forbG_left, forbG_one ha0 ha1, zero_add, add_zero] at h
  have e : π * (c ^ 2 - χ) / (4 * c) = c / 2 * (1 - a ^ 2) * (π / 2) := by
    rw [← hca]; field_simp; ring
  rw [e]; exact h

/-- `Φ_C` is monotone on `[0, ∞)`: `Φ_C' = κ_C ≥ 0` there. -/
theorem PhiC_monotoneOn : MonotoneOn PhiC (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) continuous_PhiC.continuousOn
  · exact fun Z _ => (hasDerivAt_PhiC Z).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro Z hZ
    rw [(hasDerivAt_PhiC Z).deriv]; exact kappaC_nonneg (le_of_lt hZ)

/-- `κ_C < 1`: `Z ≤ |Z| < √(Z² + 9/4)`. -/
theorem kappaC_lt_one (Z : ℝ) : kappaC Z < 1 := by
  have hr := root_pos Z
  have h : |Z| < √(Z ^ 2 + 9 / 4) := (Real.lt_sqrt (abs_nonneg Z)).mpr (by rw [sq_abs]; linarith)
  unfold kappaC
  rw [div_lt_one (by positivity)]
  linarith [le_abs_self Z]

/-- `Φ_C` is 1-Lipschitz upward: `Φ_C − id` is antitone since `κ_C < 1`. -/
theorem PhiC_sub_le {Z Z' : ℝ} (h : Z ≤ Z') : PhiC Z' - PhiC Z ≤ Z' - Z := by
  have hd : ∀ x, HasDerivAt (fun Z => PhiC Z - Z) (kappaC x - 1) x := fun x =>
    (hasDerivAt_PhiC x).sub (hasDerivAt_id' x)
  have hanti : Antitone (fun Z => PhiC Z - Z) :=
    antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt) fun x => by
      rw [(hd x).deriv]; linarith [kappaC_lt_one x]
  have := hanti h
  simp only at this
  linarith

/-- `e^{−2Φ_C(Z)} = e^{3 − 2r}(r + ½)/2`, `r = √(Z² + 9/4)`. -/
theorem exp_neg_two_PhiC (Z : ℝ) :
    Real.exp (-(2 * PhiC Z)) = Real.exp (3 - 2 * √(Z ^ 2 + 9 / 4)) * (√(Z ^ 2 + 9 / 4) + 1 / 2) / 2 := by
  have hr := root_pos Z
  have e : -(2 * PhiC Z) = (3 - 2 * √(Z ^ 2 + 9 / 4)) + Real.log ((1 / 2 + √(Z ^ 2 + 9 / 4)) / 2) := by
    unfold PhiC; ring
  rw [e, Real.exp_add, Real.exp_log (by positivity)]
  ring

/-- `e^{−2Φ_C(Z)} ≤ (e³/2)(Z + 2)e^{−2Z}` for `Z ≥ 0`: `Z ≤ r ≤ Z + 3/2`. -/
theorem exp_neg_two_PhiC_le {Z : ℝ} (hZ : 0 ≤ Z) :
    Real.exp (-(2 * PhiC Z)) ≤ Real.exp 3 / 2 * (Z + 2) * Real.exp (-(2 * Z)) := by
  have hr := root_pos Z
  have hr2 := root_sq Z
  have h1 : Z ≤ √(Z ^ 2 + 9 / 4) := by nlinarith
  have h2 : √(Z ^ 2 + 9 / 4) ≤ Z + 3 / 2 := by nlinarith
  rw [exp_neg_two_PhiC]
  have he : Real.exp (3 - 2 * √(Z ^ 2 + 9 / 4)) ≤ Real.exp (3 - 2 * Z) := Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul he (show √(Z ^ 2 + 9 / 4) + 1 / 2 ≤ Z + 2 by linarith) (by positivity)
    (Real.exp_pos _).le
  have e : Real.exp (3 - 2 * Z) = Real.exp 3 * Real.exp (-(2 * Z)) := by rw [← Real.exp_add]; ring_nf
  rw [e] at hm
  linarith

/-- `Z ↦ e^{−2Φ_C(Z)}` is antitone on `[0, ∞)`. -/
theorem exp_neg_two_PhiC_anti {Z Z' : ℝ} (hZ : 0 ≤ Z) (h : Z ≤ Z') :
    Real.exp (-(2 * PhiC Z')) ≤ Real.exp (-(2 * PhiC Z)) := by
  have := PhiC_monotoneOn (show Z ∈ Ici 0 from hZ) (show Z' ∈ Ici 0 from hZ.trans h) h
  exact Real.exp_le_exp.mpr (by linarith)

/-- `e^{−2Φ_C(Z(√χ/c))} ≤ e^{−2Φ_C(π(c² − χ)/(4c))}`. -/
theorem exp_neg_two_PhiC_forbZ_le {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    Real.exp (-(2 * PhiC (forbZ c χ (√χ / c)))) ≤ Real.exp (-(2 * PhiC (π * (c ^ 2 - χ) / (4 * c)))) := by
  have hD : 0 ≤ c ^ 2 - χ := by linarith
  exact exp_neg_two_PhiC_anti (by positivity) (forbZ_ge hc hχ0 hχc)

/-- `∫₁^∞ dξ/(ξ√(ξ² − 1)) = π/2`: the antiderivative `arccos(1/ξ)` runs from `0` to `π/2`. -/
theorem integral_arcsec_deriv : ∫ ξ in Ioi (1 : ℝ), 1 / (ξ * √(ξ ^ 2 - 1)) = π / 2 := by
  have hlim : Tendsto (fun s : ℝ => arccos (1 / s)) atTop (𝓝 (π / 2)) := by
    have h : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    have := (Real.continuous_arccos.tendsto 0).comp h
    rwa [Real.arccos_zero] at this
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun s => arccos (1 / s)) ?_
    (fun x hx => Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.hasDerivAt_arcsec (Set.mem_Ioi.mp hx)) integrableOn_arcsec_deriv hlim]
  · simp
  · exact (Real.continuous_arccos.continuousAt.comp
      (continuousAt_const.div continuousAt_id one_ne_zero)).continuousWithinAt

/-- `K ≤ (c/σ)π/2`, `σ = √(c² − χ)`: `1/a ≤ 1/(σξ√(ξ² − 1))` on `(1, ∞)`. -/
theorem ellK_le {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    ellK c χ ≤ c / √(c ^ 2 - χ) * (π / 2) := by
  have hle : ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ
      ≤ ∫ ξ in Ioi (1 : ℝ), 1 / √(c ^ 2 - χ) * (1 / (ξ * √(ξ ^ 2 - 1))) :=
    setIntegral_mono_on (integrableOn_inv_aP hc hχ0 hχc) (integrableOn_arcsec_deriv.const_mul _)
      measurableSet_Ioi fun ξ hξ => by
        rw [one_div_mul_one_div]; exact Cvs.Prolate.LiouvilleGreen.ProlateArcsinMassLaw.inv_a_le hξ hc hχ0 hχc
  rw [MeasureTheory.integral_const_mul, integral_arcsec_deriv] at hle
  unfold ellK
  calc c * ∫ ξ in Ioi (1 : ℝ), 1 / aP c χ ξ ≤ c * (1 / √(c ^ 2 - χ) * (π / 2)) :=
        mul_le_mul_of_nonneg_left hle hc.le
    _ = c / √(c ^ 2 - χ) * (π / 2) := by ring

/-- **The phase drop near the turning point**: on `[a, (1 + a)/2]`, `a = √χ/c`,
`Z(a) − Z(s) ≤ (4/3)c(s − a)^{3/2}/√(1 − a)`, from `√Q/√(1 − t²) ≤ 2c√(t − a)/√(1 − a)`. -/
theorem forbZ_drop_le {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hs : s ∈ Icc (√χ / c) ((1 + √χ / c) / 2)) :
    forbZ c χ (√χ / c) - forbZ c χ s ≤ 4 / 3 * c * ((s - √χ / c) * √(s - √χ / c)) / √(1 - √χ / c) := by
  set a := √χ / c with ha
  have ha0 : 0 ≤ a := div_nonneg (Real.sqrt_nonneg _) hc.le
  have ha1 : a < 1 := by rw [ha, div_lt_one hc, Real.sqrt_lt' hc]; exact hχc
  have hca : c ^ 2 * a ^ 2 = χ := by rw [ha, div_pow, Real.sq_sqrt hχ0]; field_simp
  clear_value a
  have hq : ∀ t, qP c χ t = c ^ 2 * (t - a) * (t + a) := fun t => by unfold qP; rw [← hca]; ring
  have hb : 0 < √(1 - a) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : s ≤ 1 := by linarith [hs.2]
  set h : ℝ → ℝ := fun t => forbZ c χ t + 4 / 3 * c * ((t - a) * √(t - a)) / √(1 - a) with hh
  have hhc : ContinuousOn h (Icc a s) := by
    refine ((continuousOn_forbZ c χ).mono (Icc_subset_Icc ha0 hs1)).add ?_
    exact Continuous.continuousOn (by fun_prop)
  have hhd : ∀ t ∈ Ioo a s, HasDerivAt h
      (-(√(qP c χ t) / √(1 - t ^ 2)) + 2 * c * √(t - a) / √(1 - a)) t := by
    intro t ht
    have hta : 0 < t - a := by linarith [ht.1]
    have hd1 : HasDerivAt (fun t => t - a) 1 t := (hasDerivAt_id' t).sub_const a
    have hd2 := ((hd1.mul (hd1.sqrt hta.ne')).const_mul (4 / 3 * c)).div_const (√(1 - a))
    refine ((hasDerivAt_forbZ c χ ⟨by linarith [ht.1], by linarith [ht.2]⟩).add hd2).congr_deriv ?_
    have hr := Real.sqrt_pos.mpr hta
    have hr2 := Real.sq_sqrt hta.le
    field_simp
    linear_combination (-4 * c) * hr2
  have hmono : MonotoneOn h (Icc a s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a s) hhc
    · rw [interior_Icc]; exact fun t ht => (hhd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht
      rw [(hhd t ht).deriv]
      have hta : 0 < t - a := by linarith [ht.1]
      have ht1 : t < 1 := by linarith [ht.2]
      have ht0 : 0 < t := by linarith [ht.1]
      have hP : 0 < 1 - t ^ 2 := by nlinarith
      have hq0 : 0 ≤ qP c χ t := by rw [hq]; exact mul_nonneg (by positivity) (by linarith)
      rw [neg_add_eq_sub, sub_nonneg, div_le_div_iff₀ (Real.sqrt_pos.mpr hP) hb]
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
      simp only [mul_pow]
      rw [Real.sq_sqrt hq0, Real.sq_sqrt (by linarith), Real.sq_sqrt hta.le, Real.sq_sqrt hP.le, hq]
      have key : (t + a) * (1 - a) ≤ 4 * (1 - t ^ 2) := by
        nlinarith [mul_nonneg (show 0 ≤ 2 - t - a by linarith) (show 0 ≤ 1 - a by linarith),
          mul_nonneg (show 0 ≤ 1 - t by linarith) ht0.le, hs.2, ht.2]
      have := mul_le_mul_of_nonneg_left key (show 0 ≤ c ^ 2 * (t - a) by positivity)
      linarith
  have := hmono ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
  simp only [hh, sub_self, Real.sqrt_zero, mul_zero, zero_div, add_zero] at this
  linarith

/-- **The `J` window**: if `0 < d ≤ (1 − a)/2` and `16c²d³ ≤ 9(1 − a)`, `a = √χ/c`, then the phase drops by at
most `1` on `[a, a + d]` and `J ≥ d e^{2Φ_C(Z(a)) − 2}`. -/
theorem forbJ_ge_window {c χ d : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hd : 0 < d)
    (hd1 : d ≤ (1 - √χ / c) / 2) (hdrop : 16 * c ^ 2 * d ^ 3 ≤ 9 * (1 - √χ / c)) :
    d * Real.exp (2 * PhiC (forbZ c χ (√χ / c)) - 2) ≤ forbJ c χ := by
  have ha0 : 0 ≤ √χ / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have ha1 : √χ / c < 1 := by rw [div_lt_one hc, Real.sqrt_lt' hc]; exact hχc
  have hb : 0 < √(1 - √χ / c) := Real.sqrt_pos.mpr (by linarith)
  have hcont : ContinuousOn (fun s => Real.exp (2 * PhiC (forbZ c χ s))) (Icc (√χ / c) 1) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_PhiC)).comp_continuousOn
      ((continuousOn_forbZ c χ).mono (Icc_subset_Icc ha0 le_rfl))
  have hpt : ∀ t ∈ Icc (√χ / c) (√χ / c + d),
      Real.exp (2 * PhiC (forbZ c χ (√χ / c)) - 2) ≤ Real.exp (2 * PhiC (forbZ c χ t)) := by
    intro t ht
    have hdrop' := forbZ_drop_le hc hχ0 hχc (s := t) ⟨ht.1, by linarith [ht.2]⟩
    have hu0 : 0 ≤ t - √χ / c := by linarith [ht.1]
    have hud : t - √χ / c ≤ d := by linarith [ht.2]
    have hle1 : 4 / 3 * c * ((t - √χ / c) * √(t - √χ / c)) / √(1 - √χ / c) ≤ 1 := by
      rw [div_le_one hb]
      refine (pow_le_pow_iff_left₀ (by positivity) hb.le two_ne_zero).mp ?_
      rw [Real.sq_sqrt (by linarith)]
      have h3 : (t - √χ / c) ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hu0 hud 3
      have e : (4 / 3 * c * ((t - √χ / c) * √(t - √χ / c))) ^ 2 = 16 / 9 * c ^ 2 * (t - √χ / c) ^ 3 := by
        simp only [mul_pow]; rw [Real.sq_sqrt hu0]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
      linarith
    have hZ : PhiC (forbZ c χ (√χ / c)) - 1 ≤ PhiC (forbZ c χ t) := by
      rcases le_or_gt (forbZ c χ (√χ / c)) (forbZ c χ t) with h | h
      · have := PhiC_monotoneOn (show forbZ c χ (√χ / c) ∈ Ici 0 from forbZ_nonneg _ _ _)
          (show forbZ c χ t ∈ Ici 0 from forbZ_nonneg _ _ _) h
        linarith
      · have := PhiC_sub_le h.le
        linarith
    exact Real.exp_le_exp.mpr (by linarith)
  have had : √χ / c + d ≤ 1 := by linarith
  have hsub : Icc (√χ / c) (√χ / c + d) ⊆ Icc (√χ / c) 1 := Icc_subset_Icc le_rfl had
  calc d * Real.exp (2 * PhiC (forbZ c χ (√χ / c)) - 2)
      = ∫ _ in (√χ / c)..(√χ / c + d), Real.exp (2 * PhiC (forbZ c χ (√χ / c)) - 2) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ ∫ s in (√χ / c)..(√χ / c + d), Real.exp (2 * PhiC (forbZ c χ s)) :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          ((hcont.mono hsub).intervalIntegrable_of_Icc (by linarith)) hpt
    _ ≤ forbJ c χ := by
        unfold forbJ
        exact intervalIntegral.integral_mono_interval le_rfl (by linarith) had
          (Filter.Eventually.of_forall fun s => (Real.exp_pos _).le) (hcont.intervalIntegrable_of_Icc ha1.le)

end Cvs.Prolate.ForbiddenZoneClosedForm
