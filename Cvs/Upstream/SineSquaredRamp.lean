import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The `sin²` ramp: a `C¹` cutoff with an explicit derivative and majorant

`ramp a h` is `0` up to `a`, `sin²(Real.pi(θ − a)/2h)` on `[a, a + h]` and `1` beyond: `C¹` on `ℝ` with derivative
`ramp' = (Real.pi/2h) sin(Real.pi(θ − a)/h)` on the ramp and `0` outside, `0 ≤ ramp ≤ 1`, and `ramp'² ≤ (Real.pi/h)² ramp`
everywhere (`sin²(2y) = 4 sin²y cos²y`): the cutoff weight of the hierarchy, and the majorant that Cvs.L2a.WeightedDerivativeMajorant needs.
-/

namespace Cvs.Upstream.SineSquaredRamp

open Real Set Filter Topology

/-- The `sin²` ramp from `0` at `a` to `1` at `a + h`. -/
noncomputable def ramp (a h θ : ℝ) : ℝ :=
  if θ ≤ a then 0 else if θ < a + h then Real.sin (Real.pi * (θ - a) / (2 * h)) ^ 2 else 1

/-- Its derivative. -/
noncomputable def ramp' (a h θ : ℝ) : ℝ :=
  if θ ≤ a then 0 else if θ < a + h then Real.pi / (2 * h) * Real.sin (Real.pi * (θ - a) / h) else 0

theorem ramp_of_le {a h θ : ℝ} (hθ : θ ≤ a) : ramp a h θ = 0 := by unfold ramp; rw [if_pos hθ]
theorem ramp_of_ge {a h θ : ℝ} (hh : 0 < h) (hθ : a + h ≤ θ) : ramp a h θ = 1 := by
  unfold ramp; rw [if_neg (by linarith), if_neg (not_lt.mpr hθ)]
theorem ramp'_of_le {a h θ : ℝ} (hθ : θ ≤ a) : ramp' a h θ = 0 := by unfold ramp'; rw [if_pos hθ]
theorem ramp'_of_ge {a h θ : ℝ} (hh : 0 < h) (hθ : a + h ≤ θ) : ramp' a h θ = 0 := by
  unfold ramp'; rw [if_neg (by linarith), if_neg (not_lt.mpr hθ)]

theorem ramp_nonneg (a h θ : ℝ) : 0 ≤ ramp a h θ := by unfold ramp; split_ifs <;> positivity

theorem ramp_le_one (a h θ : ℝ) : ramp a h θ ≤ 1 := by
  unfold ramp; split_ifs
  · norm_num
  · nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (θ - a) / (2 * h)), sq_nonneg (Real.cos (Real.pi * (θ - a) / (2 * h)))]
  · exact le_rfl

/-- **The majorant**: `ramp'² ≤ (Real.pi/h)² ramp`. -/
theorem ramp'_sq_le {a h : ℝ} (hh : 0 < h) (θ : ℝ) : ramp' a h θ ^ 2 ≤ (Real.pi / h) ^ 2 * ramp a h θ := by
  unfold ramp ramp'; split_ifs
  · simp
  · set y := Real.pi * (θ - a) / (2 * h) with hy
    have e2 : Real.pi * (θ - a) / h = 2 * y := by rw [hy]; field_simp
    rw [e2, Real.sin_two_mul]
    have e : (Real.pi / (2 * h) * (2 * Real.sin y * Real.cos y)) ^ 2 = (Real.pi / h) ^ 2 * Real.sin y ^ 2 * Real.cos y ^ 2 := by
      field_simp
    rw [e]
    exact mul_le_of_le_one_right (by positivity)
      (by nlinarith [Real.sin_sq_add_cos_sq y, sq_nonneg (Real.sin y)])
  · simp; positivity

/-- The smooth piece and its derivative. -/
theorem hasDerivAt_piece {a h : ℝ} (hh : 0 < h) (θ : ℝ) :
    HasDerivAt (fun θ => Real.sin (Real.pi * (θ - a) / (2 * h)) ^ 2) (Real.pi / (2 * h) * Real.sin (Real.pi * (θ - a) / h)) θ := by
  have hg : HasDerivAt (fun θ => Real.pi * (θ - a) / (2 * h)) (Real.pi / (2 * h)) θ := by
    have := (((hasDerivAt_id θ).sub_const a).const_mul Real.pi).div_const (2 * h)
    simpa using this
  have hs := (Real.hasDerivAt_sin _).comp θ hg
  have h2 := hs.pow 2
  refine h2.congr_deriv ?_
  simp only [Function.comp, Nat.cast_ofNat]
  have e2 : Real.pi * (θ - a) / h = 2 * (Real.pi * (θ - a) / (2 * h)) := by field_simp
  rw [e2, Real.sin_two_mul]
  ring

/-- **The ramp is `C¹`**: `HasDerivAt (ramp a h) (ramp' a h θ) θ` at every `θ`. -/
theorem hasDerivAt_ramp {a h : ℝ} (hh : 0 < h) (θ : ℝ) : HasDerivAt (ramp a h) (ramp' a h θ) θ := by
  rcases lt_trichotomy θ a with h1 | h1 | h1
  · -- below `a`: locally `0`
    rw [ramp'_of_le h1.le]
    refine (hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Iio_mem_nhds h1) fun x hx => ramp_of_le (le_of_lt hx)
  · -- at `a`: one-sided
    subst h1
    rw [ramp'_of_le le_rfl]
    have hl : HasDerivWithinAt (ramp θ h) 0 (Iic θ) θ :=
      (hasDerivAt_const θ (0 : ℝ)).hasDerivWithinAt.congr (fun y hy => ramp_of_le hy) (ramp_of_le le_rfl)
    have hr : HasDerivWithinAt (ramp θ h) 0 (Ici θ) θ := by
      have h0 := (hasDerivAt_piece (a := θ) hh θ).hasDerivWithinAt (s := Ici θ)
      have hd : Real.pi / (2 * h) * Real.sin (Real.pi * (θ - θ) / h) = 0 := by simp
      rw [hd] at h0
      refine h0.congr_of_eventuallyEq ?_ ?_
      · refine Filter.eventually_of_mem (Ico_mem_nhdsGE (by linarith : θ < θ + h)) fun x hx => ?_
        unfold ramp
        split_ifs with hx1 hx2
        · have : x = θ := le_antisymm hx1 hx.1
          subst this; simp
        · rfl
        · exact absurd hx.2 hx2
      · simp [ramp_of_le le_rfl]
    have := hl.union hr
    rw [Iic_union_Ici] at this
    exact hasDerivWithinAt_univ.mp this
  rcases lt_trichotomy θ (a + h) with h2 | h2 | h2
  · -- on the ramp: locally the smooth piece
    have hv : ramp' a h θ = Real.pi / (2 * h) * Real.sin (Real.pi * (θ - a) / h) := by
      unfold ramp'; rw [if_neg (not_le.mpr h1), if_pos h2]
    rw [hv]
    refine (hasDerivAt_piece hh θ).congr_of_eventuallyEq ?_
    refine Filter.eventually_of_mem (Ioo_mem_nhds h1 h2) fun x hx => ?_
    unfold ramp; rw [if_neg (not_le.mpr hx.1), if_pos hx.2]
  · -- at `a + h`: one-sided
    subst h2
    rw [ramp'_of_ge hh le_rfl]
    have hr : HasDerivWithinAt (ramp a h) 0 (Ici (a + h)) (a + h) :=
      (hasDerivAt_const (a + h) (1 : ℝ)).hasDerivWithinAt.congr (fun y hy => ramp_of_ge hh hy) (ramp_of_ge hh le_rfl)
    have hl : HasDerivWithinAt (ramp a h) 0 (Iic (a + h)) (a + h) := by
      have h0 := (hasDerivAt_piece (a := a) hh (a + h)).hasDerivWithinAt (s := Iic (a + h))
      have hd : Real.pi / (2 * h) * Real.sin (Real.pi * (a + h - a) / h) = 0 := by
        have : Real.pi * (a + h - a) / h = Real.pi := by field_simp; ring
        rw [this, Real.sin_pi, mul_zero]
      rw [hd] at h0
      have hpiece : ∀ x ∈ Ioc a (a + h), ramp a h x = Real.sin (Real.pi * (x - a) / (2 * h)) ^ 2 := by
        intro x hx
        unfold ramp
        split_ifs with hx1 hx2
        · exact absurd hx.1 (not_lt.mpr hx1)
        · rfl
        · have : x = a + h := le_antisymm hx.2 (not_lt.mp hx2)
          subst this
          have : Real.pi * (a + h - a) / (2 * h) = Real.pi / 2 := by field_simp; ring
          rw [this, Real.sin_pi_div_two]; norm_num
      refine h0.congr_of_eventuallyEq ?_ (hpiece _ ⟨by linarith, le_rfl⟩)
      exact Filter.eventually_of_mem (Ioc_mem_nhdsLE (by linarith : a < a + h)) hpiece
    have := hl.union hr
    rw [Iic_union_Ici] at this
    exact hasDerivWithinAt_univ.mp this
  · -- beyond `a + h`: locally `1`
    rw [ramp'_of_ge hh h2.le]
    refine (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Ioi_mem_nhds h2) fun x hx => ramp_of_ge hh (le_of_lt hx)

/-- **The derivative of the ramp is continuous.** -/
theorem continuous_ramp' {a h : ℝ} (hh : 0 < h) : Continuous (ramp' a h) := by
  have hF : Continuous fun θ => Real.pi / (2 * h) * Real.sin (Real.pi * (θ - a) / h) := by fun_prop
  rw [continuous_iff_continuousAt]
  intro θ
  rcases lt_trichotomy θ a with h1 | h1 | h1
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) θ).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Iio_mem_nhds h1) fun x hx => ramp'_of_le (le_of_lt hx)
  · subst h1
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · exact continuousWithinAt_const.congr (fun y hy => ramp'_of_le hy) (ramp'_of_le le_rfl)
    · have h0 := (hF.continuousAt (x := θ)).continuousWithinAt (s := Ici θ)
      refine h0.congr_of_eventuallyEq ?_ (by simp [ramp'_of_le le_rfl])
      refine Filter.eventually_of_mem (Ico_mem_nhdsGE (by linarith : θ < θ + h)) fun x hx => ?_
      unfold ramp'
      split_ifs with hx1 hx2
      · have : x = θ := le_antisymm hx1 hx.1
        subst this; simp
      · rfl
      · exact absurd hx.2 hx2
  rcases lt_trichotomy θ (a + h) with h2 | h2 | h2
  · refine hF.continuousAt.congr_of_eventuallyEq ?_
    refine Filter.eventually_of_mem (Ioo_mem_nhds h1 h2) fun x hx => ?_
    unfold ramp'; rw [if_neg (not_le.mpr hx.1), if_pos hx.2]
  · subst h2
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · have h0 := (hF.continuousAt (x := a + h)).continuousWithinAt (s := Iic (a + h))
      have hpiece : ∀ x ∈ Ioc a (a + h), ramp' a h x = Real.pi / (2 * h) * Real.sin (Real.pi * (x - a) / h) := by
        intro x hx
        unfold ramp'
        split_ifs with hx1 hx2
        · exact absurd hx.1 (not_lt.mpr hx1)
        · rfl
        · have : x = a + h := le_antisymm hx.2 (not_lt.mp hx2)
          subst this
          have : Real.pi * (a + h - a) / h = Real.pi := by field_simp; ring
          rw [this, Real.sin_pi, mul_zero]
      refine h0.congr_of_eventuallyEq ?_ (hpiece _ ⟨by linarith, le_rfl⟩)
      exact Filter.eventually_of_mem (Ioc_mem_nhdsLE (by linarith : a < a + h)) hpiece
    · exact continuousWithinAt_const.congr (fun y hy => ramp'_of_ge hh hy) (ramp'_of_ge hh le_rfl)
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) θ).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Ioi_mem_nhds h2) fun x hx => ramp'_of_ge hh (le_of_lt hx)

end Cvs.Upstream.SineSquaredRamp
