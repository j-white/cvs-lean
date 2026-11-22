import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CarrierBoundBothColumns
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.FilteredColumnCarriers

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The mixed term is `O(c^{−1/4})` and the exterior-column limits follow from the extension energy

Under the carrier bound, `|O_J| ≤ 2C²K_c Z(L + B)` with `Z(ρ) = ∫_{u>1} (π(u − ρ))⁻¹(u − 1)^{−3/4} du` and
`K_c = O(c^{−1/4})`; so the carrier bound and `limsup S_J ≤ σ` give `HighpassColumnLimsup σ`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Prolate.Hardy.MixedTermColumnLimits
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.CentralResolventTrace (L2I)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R extS extO colA colF)
open Cvs.Prolate.Hardy.CarrierBoundBothColumns (CarrierBound scaleK)

/-- The `u`-profile `(π(u − ρ))⁻¹(1/(u − 1))^{3/4}` of the mixed-term integrand. -/
def profile (ρ u : ℝ) : ℝ := 1 / (π * (u - ρ)) * (1 / (u - 1)) ^ (3 / 4 : ℝ)

/-- `Z(ρ) = ∫_{u>1} (π(u − ρ))⁻¹(1/(u − 1))^{3/4} du`. -/
def profZ (ρ : ℝ) : ℝ := ∫ u in Ioi 1, profile ρ u

theorem profile_nonneg {ρ u : ℝ} (hρ : ρ < 1) (hu : 1 < u) : 0 ≤ profile ρ u := by
  unfold profile
  have : 0 < u - ρ := by linarith
  have : 0 < u - 1 := by linarith
  positivity

theorem continuousOn_profile (ρ : ℝ) {s : Set ℝ} (hs : ∀ u ∈ s, ρ < u ∧ 1 < u) : ContinuousOn (profile ρ) s := by
  unfold profile
  have h1 : ContinuousOn (fun u : ℝ => 1 / (π * (u - ρ))) s := by
    have hc : ContinuousOn (fun u : ℝ => π * (u - ρ)) s := by fun_prop
    exact ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) (g := fun u : ℝ => π * (u - ρ))
      continuousOn_const hc fun u hu => mul_ne_zero Real.pi_pos.ne' (by linarith [(hs u hu).1])
  have h2 : ContinuousOn (fun u : ℝ => 1 / (u - 1)) s := by
    have hc : ContinuousOn (fun u : ℝ => u - 1) s := by fun_prop
    exact ContinuousOn.div₀ (f := fun _ : ℝ => (1 : ℝ)) (g := fun u : ℝ => u - 1)
      continuousOn_const hc fun u hu => by linarith [(hs u hu).2]
  exact h1.mul (h2.rpow_const fun _ _ => Or.inr (by norm_num))

theorem integrableOn_profile_Ioc {ρ : ℝ} (hρ : ρ < 1) : IntegrableOn (profile ρ) (Ioc 1 2) := by
  have h0 : IntervalIntegrable (fun u : ℝ => u ^ (-(3 / 4) : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h1 := h0.comp_sub_right 1
  norm_num at h1
  have hg : IntegrableOn (fun u : ℝ => (u - 1) ^ (-(3 / 4) : ℝ)) (Ioc 1 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 h1
  refine (hg.const_mul (1 / (π * (1 - ρ)))).mono' ((continuousOn_profile ρ fun u (hu : u ∈ Ioc 1 2) =>
    ⟨by linarith [hu.1], hu.1⟩).aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu1 : 0 < u - 1 := by linarith [hu.1]
  rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg hρ hu.1), profile]
  have e : (1 / (u - 1)) ^ (3 / 4 : ℝ) = (u - 1) ^ (-(3 / 4) : ℝ) := by
    rw [Real.rpow_neg hu1.le, one_div, Real.inv_rpow hu1.le]
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have : 0 < 1 - ρ := by linarith
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (by linarith [hu.1]) Real.pi_pos.le)

theorem integrableOn_profile_Ioi {ρ : ℝ} (hρ : ρ < 1) : IntegrableOn (profile ρ) (Ioi 2) := by
  have hg : IntegrableOn (fun u : ℝ => u ^ (-(7 / 4) : ℝ)) (Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  refine (hg.const_mul (4 / π)).mono' ((continuousOn_profile ρ fun u (hu : 2 < u) =>
    ⟨by linarith, by linarith⟩).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu2 : 2 < u := hu
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg hρ (by linarith)), profile]
  have hπ := Real.pi_pos
  have h1 : 1 / (π * (u - ρ)) ≤ 2 / π * (1 / u) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  have h2 : (1 / (u - 1)) ^ (3 / 4 : ℝ) ≤ 2 * (1 / u) ^ (3 / 4 : ℝ) := by
    have h3 : (1 / (u - 1)) ^ (3 / 4 : ℝ) ≤ (2 * (1 / u)) ^ (3 / 4 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      rw [mul_one_div, div_le_div_iff₀ hu1 hu0]; linarith
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h3
    have h4 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (show (3 / 4 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    exact h3.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
  have e : 1 / u * (1 / u) ^ (3 / 4 : ℝ) = u ^ (-(7 / 4) : ℝ) := by
    rw [Real.rpow_neg hu0.le, show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num, Real.rpow_add hu0, Real.rpow_one,
      one_div, Real.inv_rpow hu0.le, mul_inv]
  calc 1 / (π * (u - ρ)) * (1 / (u - 1)) ^ (3 / 4 : ℝ) ≤ 2 / π * (1 / u) * (2 * (1 / u) ^ (3 / 4 : ℝ)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 4 / π * (1 / u * (1 / u) ^ (3 / 4 : ℝ)) := by ring
    _ = 4 / π * u ^ (-(7 / 4) : ℝ) := by rw [e]

theorem integrableOn_profile {ρ : ℝ} (hρ : ρ < 1) : IntegrableOn (profile ρ) (Ioi 1) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)]
  exact (integrableOn_profile_Ioc hρ).union (integrableOn_profile_Ioi hρ)

/-- **The mixed-term bound** `|O_J| ≤ 2C²K_c Z(L + B)` under the carrier bound. -/
theorem abs_extO_le {c L B C : ℝ} {D E : Set ℂ} (hc : 0 < c) (hD : D ⊆ Metric.ball 0 1)
    (hE : ∀ z ∈ E, |z.re| ≤ L ∧ |z.im| ≤ B) (hLB : L + B < 1) {J : L2I →L[ℝ] L2R} (hJ : CarrierBound c D E C J) :
    |extO c J| ≤ 2 * (C ^ 2 * scaleK c L B * profZ (L + B)) := by
  unfold extO profZ
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_profile hLB).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : 1 < u := hu
  have hA := Cvs.Prolate.Hardy.CarrierBoundBothColumns.norm_J_colA_le hD hE hLB hJ hu1
  have hF := Cvs.Prolate.Hardy.CarrierBoundBothColumns.norm_J_colF_le hc hD hE hLB hJ hu1
  calc ‖inner ℝ (J (colA c u)) (J (colF c u))‖ ≤ ‖J (colA c u)‖ * ‖J (colF c u)‖ := norm_inner_le_norm _ _
    _ ≤ C * (1 / (π * (u - (L + B)))) * (C * (scaleK c L B * (1 / (u - 1)) ^ (3 / 4 : ℝ))) :=
        mul_le_mul hA hF (norm_nonneg _) ((norm_nonneg _).trans hA)
    _ = C ^ 2 * scaleK c L B * profile (L + B) u := by unfold profile; ring

/-- `K_c = 8Γ(3/4)/(2π√(2π)(1 − L − B)^{3/4}) · c^{−1/4}` for `c > 0`. -/
theorem scaleK_eq {c L B : ℝ} (hc : 0 < c) (hLB : L + B < 1) :
    scaleK c L B = 8 * Gamma (3 / 4) / (2 * π * √(2 * π) * (1 - L - B) ^ (3 / 4 : ℝ)) * c ^ (-(1 / 4) : ℝ) := by
  have hκ : 0 < 1 - L - B := by linarith
  have hπ := Real.pi_pos
  unfold scaleK Cvs.Prolate.Hardy.FilteredColumnCarriers.kap
  rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ 2 * π), Real.sqrt_eq_rpow c, one_div (c * (1 - L - B)),
    Real.inv_rpow (by positivity), Real.mul_rpow hc.le hκ.le,
    show (-(1 / 4) : ℝ) = 1 / 2 - 3 / 4 by norm_num, Real.rpow_sub hc]
  have h1 : 0 < c ^ (3 / 4 : ℝ) := by positivity
  have h2 : 0 < (1 - L - B) ^ (3 / 4 : ℝ) := by positivity
  have h3 : 0 < √(2 * π) := by positivity
  field_simp

theorem tendsto_scaleK {L B : ℝ} (hLB : L + B < 1) : Tendsto (fun c => scaleK c L B) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (8 * Gamma (3 / 4) / (2 * π * √(2 * π) * (1 - L - B) ^ (3 / 4 : ℝ)))
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  exact (scaleK_eq hc hLB).symm

/-- **The mixed term vanishes**: a family with a uniform carrier bound has `|O_J| ≤ ε` eventually. -/
theorem eventually_abs_extO_le {L B C : ℝ} {D E : Set ℂ} (hD : D ⊆ Metric.ball 0 1)
    (hE : ∀ z ∈ E, |z.re| ≤ L ∧ |z.im| ≤ B) (hLB : L + B < 1)
    (J : ℕ → L2I →L[ℝ] L2R) (hJ : ∀ᶠ x : ℕ in atTop, CarrierBound (2 * π * x) D E C (J x)) :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop, |extO (2 * π * x) (J x)| ≤ ε := by
  intro ε hε
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h := (((tendsto_scaleK hLB).comp hc).const_mul (C ^ 2)).mul_const (profZ (L + B)) |>.const_mul 2
  simp only [mul_zero, zero_mul] at h
  filter_upwards [h.eventually (eventually_le_nhds hε), hJ, eventually_ge_atTop 1] with x hx hJx h1
  have hpos : 0 < 2 * π * (x : ℝ) := by
    have : (1 : ℝ) ≤ x := by exact_mod_cast h1
    positivity
  refine (abs_extO_le hpos hD hE hLB hJx).trans ?_
  simpa [Function.comp, mul_assoc] using hx

theorem ellipse_sum_lt_one : 3 / 5 + √11 / 10 < (1 : ℝ) := by
  have : √11 < 4 := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem closedBall_subset_ball : Metric.closedBall (0 : ℂ) (3 / 5) ⊆ Metric.ball 0 1 :=
  Metric.closedBall_subset_ball (by norm_num)

theorem ellipse_box {z : ℂ} (hz : z ∈ Cvs.Prolate.Hardy.CarrierBoundBothColumns.ellipse (3 / 5) (√11 / 10)) : |z.re| ≤ 3 / 5 ∧ |z.im| ≤ √11 / 10 :=
  ⟨Cvs.Prolate.Hardy.CarrierBoundBothColumns.abs_re_le (by norm_num) hz, Cvs.Prolate.Hardy.CarrierBoundBothColumns.abs_im_le (by positivity) hz⟩

end Cvs.Prolate.Hardy.MixedTermColumnLimits

end
