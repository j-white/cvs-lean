import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Volterra resolvent at the regular singular point `ξ = 1`

For `((ξ²−1)y')' = −z` with `y(1) = 0` and zero flux at `1`, `y = −green z`, where `green` integrates the averaged
kernel `avg z t = (t+1)⁻¹ ⨍_{[1,t]} z`. On `C([a, b])`, `−1 < a ≤ 1 ≤ b`, the Volterra operator `W y = green y`
makes `1 + W M_q` invertible (Bielecki weight `cosh(Λ(ξ−1))`), so `regOn = (1 + W M_q)⁻¹ 1` solves `y + W(qy) = 1`;
it is local in `[a, b]`, and analytic in `χ` along `q − χ` with derivative `dotOn = (1 + W M_q)⁻¹ W regOn`.
-/

noncomputable section

open Real Set intervalIntegral MeasureTheory Filter Topology Asymptotics Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open scoped Interval

namespace Cvs.Prolate.VolterraResolventEdge

/-! ### The averaged kernel and its Green function -/

/-- The mean of `z` over the segment `[1, t]`, divided by `t + 1`. -/
def avg (z : ℝ → ℝ) (t : ℝ) : ℝ := (t + 1)⁻¹ * ∫ τ in (0:ℝ)..1, z (1 + (t - 1) * τ)

/-- The Green function of `y ↦ ((ξ²−1)y')'` with `y(1) = 0` and zero flux at `1` (up to sign). -/
def green (z : ℝ → ℝ) (ξ : ℝ) : ℝ := ∫ t in (1:ℝ)..ξ, avg z t

/-- The flux identity `(t² − 1) avg z t = ∫₁ᵗ z`; it needs no integrability hypothesis. -/
theorem pP_mul_avg (z : ℝ → ℝ) {t : ℝ} (ht : t ≠ -1) : pP t * avg z t = ∫ s in (1:ℝ)..t, z s := by
  unfold avg pP
  have h1 : t + 1 ≠ 0 := by intro h; apply ht; linarith
  have key := intervalIntegral.mul_integral_comp_mul_add (a := 0) (b := 1) (f := z) (t - 1) 1
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at key
  have e : ∀ τ : ℝ, z (1 + (t - 1) * τ) = z ((t - 1) * τ + 1) := fun τ => by rw [add_comm]
  simp_rw [e]
  rw [← key, show (t ^ 2 - 1) = (t - 1) * (t + 1) by ring]
  field_simp

theorem continuousOn_avg {z : ℝ → ℝ} (hz : Continuous z) : ContinuousOn (avg z) (Ioi (-1)) := by
  unfold avg
  apply ContinuousOn.mul
  · exact (continuousOn_id.add continuousOn_const).inv₀ (fun t ht => by
      have ht' : -1 < t := ht
      exact (show (0:ℝ) < id t + 1 by simp only [id]; linarith).ne')
  · apply Continuous.continuousOn
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 1

theorem uIcc_one_subset_Ioi {t : ℝ} (ht : -1 < t) : uIcc 1 t ⊆ Ioi (-1) := by
  intro x hx; rcases le_total 1 t with h | h
  · rw [uIcc_of_le h] at hx; simp; linarith [hx.1]
  · rw [uIcc_of_ge h] at hx; simp; linarith [hx.1]

/-- `green z` is `C¹` on `(−1, ∞)` with derivative `avg z`. -/
theorem hasDerivAt_green {z : ℝ → ℝ} (hz : Continuous z) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (green z) (avg z t) t := by
  have hc := continuousOn_avg hz
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (hc.mono (uIcc_one_subset_Ioi ht)).intervalIntegrable
  · exact hc.stronglyMeasurableAtFilter isOpen_Ioi t ht
  · exact hc.continuousAt (Ioi_mem_nhds ht)

theorem avg_add {z₁ z₂ : ℝ → ℝ} (h₁ : Continuous z₁) (h₂ : Continuous z₂) (t : ℝ) :
    avg (z₁ + z₂) t = avg z₁ t + avg z₂ t := by
  unfold avg
  rw [← mul_add, ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rfl

theorem avg_smul (r : ℝ) (z : ℝ → ℝ) (t : ℝ) : avg (r • z) t = r * avg z t := by
  unfold avg
  simp only [Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]; ring

theorem green_add {z₁ z₂ : ℝ → ℝ} (h₁ : Continuous z₁) (h₂ : Continuous z₂) {ξ : ℝ} (hξ : -1 < ξ) :
    green (z₁ + z₂) ξ = green z₁ ξ + green z₂ ξ := by
  unfold green
  simp_rw [avg_add h₁ h₂]
  exact intervalIntegral.integral_add
    ((continuousOn_avg h₁).mono (uIcc_one_subset_Ioi hξ)).intervalIntegrable
    ((continuousOn_avg h₂).mono (uIcc_one_subset_Ioi hξ)).intervalIntegrable

theorem green_smul (r : ℝ) (z : ℝ → ℝ) (ξ : ℝ) : green (r • z) ξ = r * green z ξ := by
  unfold green; simp_rw [avg_smul]; exact intervalIntegral.integral_const_mul _ _

theorem one_add_mul_mem_uIcc {t τ : ℝ} (hτ : τ ∈ Icc (0:ℝ) 1) : 1 + (t - 1) * τ ∈ uIcc 1 t := by
  rcases le_total 1 t with h | h
  · rw [uIcc_of_le h]; constructor <;> nlinarith [hτ.1, hτ.2]
  · rw [uIcc_of_ge h]; constructor <;> nlinarith [hτ.1, hτ.2]

/-- `avg z t` depends only on `z` on `[1, t]`. -/
theorem avg_congr {z₁ z₂ : ℝ → ℝ} {t : ℝ} (h : ∀ s ∈ uIcc 1 t, z₁ s = z₂ s) :
    avg z₁ t = avg z₂ t := by
  unfold avg
  congr 1
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [uIcc_of_le zero_le_one] at hτ
  exact h _ (one_add_mul_mem_uIcc hτ)

/-- `green z ξ` depends only on `z` on `[1, ξ]`. -/
theorem green_congr {z₁ z₂ : ℝ → ℝ} {ξ : ℝ} (h : ∀ s ∈ uIcc 1 ξ, z₁ s = z₂ s) :
    green z₁ ξ = green z₂ ξ := by
  unfold green
  apply intervalIntegral.integral_congr
  intro t ht
  exact avg_congr (fun s hs => h s (uIcc_subset_uIcc left_mem_uIcc ht hs))

/-! ### The Bielecki estimates -/

theorem abs_avg_le {z : ℝ → ℝ} {K t : ℝ} (ht : -1 < t) (hK : ∀ s ∈ uIcc 1 t, |z s| ≤ K) :
    |avg z t| ≤ K / (t + 1) := by
  unfold avg
  have ht1 : 0 < t + 1 := by linarith
  have hint : ‖∫ τ in (0:ℝ)..1, z (1 + (t - 1) * τ)‖ ≤ K * |1 - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun τ hτ => by
      rw [uIoc_of_le zero_le_one] at hτ
      exact hK _ (one_add_mul_mem_uIcc ⟨hτ.1.le, hτ.2⟩))
  rw [Real.norm_eq_abs] at hint
  rw [abs_mul, abs_inv, abs_of_pos ht1, inv_mul_eq_div]
  simpa using div_le_div_of_nonneg_right hint ht1.le

theorem cosh_le_of_mem_uIcc {Λ t s : ℝ} (hs : s ∈ uIcc 1 t) :
    cosh (Λ * (s - 1)) ≤ cosh (Λ * (t - 1)) := by
  rw [Real.cosh_le_cosh, abs_mul, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg Λ)
  rcases le_total 1 t with h | h
  · rw [uIcc_of_le h] at hs
    rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg (by linarith)]; linarith [hs.2]
  · rw [uIcc_of_ge h] at hs
    rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith)]; linarith [hs.1]

/-- The two-sided Bielecki estimate: a `cosh(Λ(s − 1))` bound on `z` passes to `green z`
with the gain `1/((1 + a)Λ)`. -/
theorem abs_green_le_cosh {z : ℝ → ℝ} {K Λ a ξ : ℝ} (ha : -1 < a) (ha1 : a ≤ 1) (haξ : a ≤ ξ)
    (hΛ : 0 < Λ) (hK : ∀ s ∈ uIcc 1 ξ, |z s| ≤ K * cosh (Λ * (s - 1))) :
    |green z ξ| ≤ K / ((1 + a) * Λ) * cosh (Λ * (ξ - 1)) := by
  have hK0 : 0 ≤ K := by
    have := hK 1 left_mem_uIcc; simp at this; linarith [abs_nonneg (z 1)]
  have ha0 : 0 < 1 + a := by linarith
  have hta : ∀ t ∈ uIcc 1 ξ, a ≤ t := by
    intro t ht; rcases le_total 1 ξ with h | h
    · rw [uIcc_of_le h] at ht; linarith [ht.1]
    · rw [uIcc_of_ge h] at ht; linarith [ht.1]
  have hb : ∀ t ∈ uIcc 1 ξ, ‖avg z t‖ ≤ K / (1 + a) * cosh (Λ * (t - 1)) := by
    intro t ht
    have ht1 : -1 < t := by linarith [hta t ht]
    have h1 := abs_avg_le (z := z) (K := K * cosh (Λ * (t - 1))) ht1 (fun s hs =>
      (hK s (uIcc_subset_uIcc left_mem_uIcc ht hs)).trans
        (mul_le_mul_of_nonneg_left (cosh_le_of_mem_uIcc hs) hK0))
    rw [Real.norm_eq_abs]
    calc |avg z t| ≤ K * cosh (Λ * (t - 1)) / (t + 1) := h1
      _ ≤ K * cosh (Λ * (t - 1)) / (1 + a) := by
          apply div_le_div_of_nonneg_left (by positivity) ha0; linarith [hta t ht]
      _ = K / (1 + a) * cosh (Λ * (t - 1)) := by ring
  have hprim : ∀ t, HasDerivAt (fun t => K / (1 + a) * (sinh (Λ * (t - 1)) / Λ))
      (K / (1 + a) * cosh (Λ * (t - 1))) t := by
    intro t
    have := ((((hasDerivAt_id t).sub_const 1).const_mul Λ).sinh.div_const Λ).const_mul (K / (1 + a))
    refine this.congr_deriv ?_; simp only [id]; field_simp
  have hcont : Continuous fun t => K / (1 + a) * cosh (Λ * (t - 1)) := by fun_prop
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim t)
    (hcont.intervalIntegrable 1 ξ)
  have hle := intervalIntegral.norm_integral_le_abs_of_norm_le (μ := volume) (f := avg z)
    (g := fun t => K / (1 + a) * cosh (Λ * (t - 1))) (a := 1) (b := ξ)
    (ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht => hb t (uIoc_subset_uIcc ht)))
    (hcont.intervalIntegrable 1 ξ)
  rw [Real.norm_eq_abs, hI] at hle
  simp only [sub_self, mul_zero, sinh_zero, zero_div, sub_zero] at hle
  unfold green
  refine hle.trans ?_
  rw [abs_mul, abs_of_nonneg (by positivity), abs_div, abs_of_pos hΛ, mul_div_assoc',
    div_le_iff₀ hΛ]
  have hs : |sinh (Λ * (ξ - 1))| ≤ cosh (Λ * (ξ - 1)) := by
    rw [abs_le]; constructor <;> nlinarith [Real.cosh_sq (Λ * (ξ - 1)), Real.cosh_pos (Λ * (ξ - 1)),
      sq_nonneg (sinh (Λ * (ξ - 1)) + cosh (Λ * (ξ - 1))),
      sq_nonneg (sinh (Λ * (ξ - 1)) - cosh (Λ * (ξ - 1)))]
  have : K / (1 + a) * |sinh (Λ * (ξ - 1))| ≤ K / (1 + a) * cosh (Λ * (ξ - 1)) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have e : K / ((1 + a) * Λ) * cosh (Λ * (ξ - 1)) * Λ = K / (1 + a) * cosh (Λ * (ξ - 1)) := by
    field_simp
  linarith

/-! ### The derivative at the singular point -/

/-- The mean of `z` over `[1, t]` has derivative `z'(1)/2` at `t = 1`. -/
theorem hasDerivAt_mean_one {z : ℝ → ℝ} {z₁ : ℝ} (hz : HasDerivAt z z₁ 1)
    (hzc : ∀ᶠ t in 𝓝 (1:ℝ), ContinuousOn z (uIcc 1 t)) :
    HasDerivAt (fun t => ∫ τ in (0:ℝ)..1, z (1 + (t - 1) * τ)) (z₁ / 2) 1 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hz' := hasDerivAt_iff_isLittleO_nhds_zero.mp hz
  rw [isLittleO_iff] at hz' ⊢
  intro c hc
  have hzc' : ∀ᶠ h in 𝓝 (0:ℝ), ContinuousOn z (uIcc 1 (1 + h)) := by
    have := (continuous_const_add (1:ℝ)).tendsto 0
    simp only [add_zero] at this
    exact this.eventually hzc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hz' hc)
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ, hzc'] with h hh hch
  simp only [add_sub_cancel_left, sub_self, zero_mul, add_zero, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul, one_mul]
  have hmaps : MapsTo (fun τ : ℝ => 1 + h * τ) (uIcc 0 1) (uIcc 1 (1 + h)) := by
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    rcases le_total 0 h with h0 | h0
    · rw [uIcc_of_le (by linarith)]; constructor <;> nlinarith [hτ.1, hτ.2]
    · rw [uIcc_of_ge (by linarith)]; constructor <;> nlinarith [hτ.1, hτ.2]
  have hint : IntervalIntegrable (fun τ => z (1 + h * τ)) volume 0 1 :=
    (hch.comp (by fun_prop : Continuous fun τ : ℝ => 1 + h * τ).continuousOn hmaps).intervalIntegrable
  have e : (∫ τ in (0:ℝ)..1, z (1 + h * τ)) - z 1 - h * (z₁ / 2)
      = ∫ τ in (0:ℝ)..1, (z (1 + h * τ) - z 1 - (h * τ) * z₁) := by
    rw [intervalIntegral.integral_sub (hint.sub intervalIntegrable_const)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul, integral_id]
    simp; ring
  rw [e]
  have hb : ∀ τ ∈ Ι (0:ℝ) 1, ‖z (1 + h * τ) - z 1 - (h * τ) * z₁‖ ≤ c * ‖h‖ := by
    intro τ hτ
    rw [uIoc_of_le zero_le_one] at hτ
    have hτb : h * τ ∈ Metric.ball (0:ℝ) δ := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, Real.norm_eq_abs τ, abs_of_pos hτ.1]
      rw [Metric.mem_ball, dist_zero_right] at hh
      nlinarith [norm_nonneg h, hτ.2]
    have := hball hτb
    simp only [smul_eq_mul] at this
    calc ‖z (1 + h * τ) - z 1 - (h * τ) * z₁‖ ≤ c * ‖h * τ‖ := this
      _ ≤ c * ‖h‖ := by
          apply mul_le_mul_of_nonneg_left _ hc.le
          rw [norm_mul, Real.norm_eq_abs τ, abs_of_pos hτ.1]
          nlinarith [norm_nonneg h, hτ.2]
  calc ‖∫ τ in (0:ℝ)..1, (z (1 + h * τ) - z 1 - (h * τ) * z₁)‖ ≤ c * ‖h‖ * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = c * ‖h‖ := by simp

/-- `avg z` has derivative `(z'(1) − z(1))/4` at the singular point `t = 1`. -/
theorem hasDerivAt_avg_one {z : ℝ → ℝ} {z₁ : ℝ} (hz : HasDerivAt z z₁ 1)
    (hzc : ∀ᶠ t in 𝓝 (1:ℝ), ContinuousOn z (uIcc 1 t)) :
    HasDerivAt (avg z) ((z₁ - z 1) / 4) 1 := by
  have hm := hasDerivAt_mean_one hz hzc
  have hi := ((hasDerivAt_id' (1:ℝ)).add_const 1).inv (by norm_num)
  have hp := hi.mul hm
  have e : avg z = fun t => (t + 1)⁻¹ * ∫ τ in (0:ℝ)..1, z (1 + (t - 1) * τ) := rfl
  rw [e]
  refine hp.congr_deriv ?_
  simp only [sub_self, zero_mul, add_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    one_mul]
  norm_num; ring

/-! ### The operator layer on `C([a, b])` -/

/-- Admissible intervals: `−1 < a ≤ 1 ≤ b`. -/
structure Adm (a b : ℝ) : Prop where
  neg_one_lt : -1 < a
  le_one : a ≤ 1
  one_le : 1 ≤ b

variable {a b : ℝ}

theorem Adm.le (h : Adm a b) : a ≤ b := h.le_one.trans h.one_le

theorem Adm.mem (h : Adm a b) (ξ : Icc a b) : -1 < (ξ : ℝ) := lt_of_lt_of_le h.neg_one_lt ξ.2.1

theorem Adm.sub (h : Adm a b) {ξ : ℝ} (hξ : ξ ∈ Icc a b) : uIcc 1 ξ ⊆ Icc a b :=
  uIcc_subset_Icc ⟨h.le_one, h.one_le⟩ hξ

variable (a b) in
/-- `C([a, b], ℝ)` as a type synonym, with one instance path. -/
def Cab := C(Icc a b, ℝ)

instance : NormedCommRing (Cab a b) := inferInstanceAs (NormedCommRing C(Icc a b, ℝ))
instance : NormedAlgebra ℝ (Cab a b) := inferInstanceAs (NormedAlgebra ℝ C(Icc a b, ℝ))
instance : CompleteSpace (Cab a b) := inferInstanceAs (CompleteSpace C(Icc a b, ℝ))

/-- The underlying continuous map. -/
def Cab.toC (y : Cab a b) : C(Icc a b, ℝ) := y

/-- The constant extension of `y` to the line. -/
def Cab.ext (h : a ≤ b) (y : Cab a b) : ℝ → ℝ := IccExtend h y.toC

theorem Cab.continuous_ext (h : a ≤ b) (y : Cab a b) : Continuous (y.ext h) :=
  continuous_IccExtend_iff.mpr y.toC.continuous

theorem Cab.ext_add (h : a ≤ b) (y₁ y₂ : Cab a b) : (y₁ + y₂).ext h = y₁.ext h + y₂.ext h := by
  funext x; rfl

theorem Cab.ext_smul (h : a ≤ b) (r : ℝ) (y : Cab a b) : (r • y).ext h = r • y.ext h := by
  funext x; rfl

theorem Cab.ext_mul (h : a ≤ b) (y₁ y₂ : Cab a b) : (y₁ * y₂).ext h = y₁.ext h * y₂.ext h := by
  funext x; rfl

/-- The element of `Cab a b` given by a function continuous on `[a, b]`. -/
def Cab.ofFun (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) : Cab a b :=
  (⟨fun ξ => f ξ, continuousOn_iff_continuous_domRestrict.mp hf⟩ : C(Icc a b, ℝ))

theorem Cab.ofFun_apply (f : ℝ → ℝ) (hf : ContinuousOn f (Icc a b)) (ξ : Icc a b) :
    (Cab.ofFun f hf).toC ξ = f ξ := rfl

theorem Cab.norm_le_iff (y : Cab a b) {C : ℝ} (hC : 0 ≤ C) : ‖y‖ ≤ C ↔ ∀ ξ, |y.toC ξ| ≤ C :=
  ContinuousMap.norm_le y.toC hC

theorem Cab.abs_le_norm (y : Cab a b) (ξ : Icc a b) : |y.toC ξ| ≤ ‖y‖ :=
  ContinuousMap.norm_coe_le_norm y.toC ξ

theorem Cab.ext_eq (h : a ≤ b) (y : Cab a b) {x : ℝ} (hx : x ∈ Icc a b) :
    y.ext h x = y.toC ⟨x, hx⟩ :=
  IccExtend_of_mem h _ hx

theorem Cab.abs_ext_le (h : a ≤ b) (y : Cab a b) (x : ℝ) : |y.ext h x| ≤ ‖y‖ :=
  Cab.abs_le_norm y _

/-- The restriction of a continuous function on the line. -/
def Cab.restr (Q : C(ℝ, ℝ)) : Cab a b := (Q.restrict (Icc a b) : C(Icc a b, ℝ))

theorem Cab.ext_restr (h : a ≤ b) (Q : C(ℝ, ℝ)) {x : ℝ} (hx : x ∈ Icc a b) :
    (Cab.restr Q : Cab a b).ext h x = Q x := by
  rw [Cab.ext_eq h _ hx]; rfl

/-- Evaluation of the extension at a point of the line, as a continuous linear functional. -/
def Cab.evalAt (h : a ≤ b) (x : ℝ) : Cab a b →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun y => y.ext h x
      map_add' := fun y₁ y₂ => by rw [Cab.ext_add]; rfl
      map_smul' := fun r y => by rw [Cab.ext_smul]; rfl }
    1 (fun y => by simpa [Real.norm_eq_abs] using Cab.abs_ext_le h y x)

theorem Cab.evalAt_apply (h : a ≤ b) (x : ℝ) (y : Cab a b) : Cab.evalAt h x y = y.ext h x := rfl

/-- `y ↦ green y` as a linear map of `Cab a b`. -/
def volterraLin (h : Adm a b) : Cab a b →ₗ[ℝ] Cab a b where
  toFun y := Cab.ofFun (green (y.ext h.le)) (fun ξ hξ =>
      (hasDerivAt_green (y.continuous_ext h.le)
        (lt_of_lt_of_le h.neg_one_lt hξ.1)).continuousAt.continuousWithinAt)
  map_add' y₁ y₂ := by
    apply ContinuousMap.ext; intro ξ
    show green ((y₁ + y₂).ext h.le) ξ = green (y₁.ext h.le) ξ + green (y₂.ext h.le) ξ
    rw [Cab.ext_add]
    exact green_add (y₁.continuous_ext h.le) (y₂.continuous_ext h.le) (h.mem ξ)
  map_smul' r y := by
    apply ContinuousMap.ext; intro ξ
    show green ((r • y).ext h.le) ξ = r * green (y.ext h.le) ξ
    rw [Cab.ext_smul]; exact green_smul r _ ξ

theorem volterraLin_bound (h : Adm a b) (y : Cab a b) :
    ‖volterraLin h y‖ ≤ cosh (b - a) / (1 + a) * ‖y‖ := by
  have ha0 : 0 < 1 + a := by linarith [h.neg_one_lt]
  rw [Cab.norm_le_iff _ (by positivity)]
  intro ξ
  have hb := abs_green_le_cosh (z := y.ext h.le) (K := ‖y‖) (Λ := 1) h.neg_one_lt
    h.le_one ξ.2.1 one_pos (fun s _ => (Cab.abs_ext_le h.le y s).trans
      (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_cosh _)))
  refine hb.trans ?_
  have hc : cosh (1 * ((ξ : ℝ) - 1)) ≤ cosh (b - a) := by
    rw [Real.cosh_le_cosh, one_mul]
    rw [abs_le]; constructor <;>
      linarith [ξ.2.1, ξ.2.2, h.le_one, h.one_le, abs_nonneg (b - a), le_abs_self (b - a)]
  calc ‖y‖ / ((1 + a) * 1) * cosh (1 * ((ξ : ℝ) - 1)) ≤ ‖y‖ / ((1 + a) * 1) * cosh (b - a) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
    _ = cosh (b - a) / (1 + a) * ‖y‖ := by field_simp

/-- The Volterra operator `y ↦ green y` on `C([a, b])`. -/
def volterra (h : Adm a b) : Cab a b →L[ℝ] Cab a b :=
  (volterraLin h).mkContinuous (cosh (b - a) / (1 + a)) (volterraLin_bound h)

theorem volterra_apply (h : Adm a b) (y : Cab a b) (ξ : Icc a b) :
    (volterra h y).toC ξ = green (y.ext h.le) ξ := rfl

/-- The multiplication operator `M_q`. -/
abbrev mulOp (q : Cab a b) : Cab a b →L[ℝ] Cab a b := ContinuousLinearMap.mul ℝ (Cab a b) q

/-! ### Invertibility through the Bielecki weight -/

theorem weighted_norm_lt (h : Adm a b) (q : Cab a b) :
    ∃ w w' : Cab a b, w * w' = 1 ∧ w' * w = 1 ∧ ‖mulOp w' * (volterra h * mulOp q) * mulOp w‖ < 1 := by
  have ha0 : 0 < 1 + a := by linarith [h.neg_one_lt]
  set Λ := 2 * (‖q‖ + 1) / (1 + a) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  let w : Cab a b := Cab.ofFun (fun ξ => cosh (Λ * (ξ - 1))) (by fun_prop)
  let w' : Cab a b := Cab.ofFun (fun ξ => (cosh (Λ * (ξ - 1)))⁻¹) (by
    apply Continuous.continuousOn; exact (by fun_prop : Continuous fun ξ : ℝ => cosh (Λ * (ξ - 1))).inv₀
      (fun ξ => (Real.cosh_pos _).ne'))
  have hww' : w * w' = 1 := by
    apply ContinuousMap.ext; intro ξ
    show cosh (Λ * ((ξ : ℝ) - 1)) * (cosh (Λ * ((ξ : ℝ) - 1)))⁻¹ = 1
    exact mul_inv_cancel₀ (Real.cosh_pos _).ne'
  refine ⟨w, w', hww', by rw [mul_comm]; exact hww', ?_⟩
  have hbound : ‖mulOp w' * (volterra h * mulOp q) * mulOp w‖ ≤ ‖q‖ / ((1 + a) * Λ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    rw [show ‖q‖ / ((1 + a) * Λ) * ‖y‖ = ‖q‖ * ‖y‖ / ((1 + a) * Λ) by ring]
    rw [Cab.norm_le_iff _ (by positivity)]
    intro ξ
    show |w'.toC ξ * (volterra h (q * (w * y))).toC ξ| ≤ _
    rw [volterra_apply]
    have hK : ∀ s ∈ uIcc 1 (ξ : ℝ), |(q * (w * y)).ext h.le s| ≤ ‖q‖ * ‖y‖ * cosh (Λ * (s - 1)) := by
      intro s hs
      have hsI := h.sub ξ.2 hs
      rw [Cab.ext_mul, Cab.ext_mul]
      simp only [Pi.mul_apply]
      rw [Cab.ext_eq h.le w hsI, abs_mul, abs_mul]
      have h1 := Cab.abs_ext_le h.le q s
      have h2 := Cab.abs_ext_le h.le y s
      have h3 : |w.toC ⟨s, hsI⟩| = cosh (Λ * (s - 1)) := abs_of_pos (Real.cosh_pos _)
      rw [h3]
      have := Real.cosh_pos (Λ * (s - 1))
      calc |q.ext h.le s| * (cosh (Λ * (s - 1)) * |y.ext h.le s|)
          ≤ ‖q‖ * (cosh (Λ * (s - 1)) * ‖y‖) := by gcongr
        _ = ‖q‖ * ‖y‖ * cosh (Λ * (s - 1)) := by ring
    have hg := abs_green_le_cosh h.neg_one_lt h.le_one ξ.2.1 hΛ0 hK
    rw [abs_mul]
    have hw' : |w'.toC ξ| = (cosh (Λ * ((ξ : ℝ) - 1)))⁻¹ := abs_of_pos (inv_pos.mpr (Real.cosh_pos _))
    rw [hw']
    have hcpos := Real.cosh_pos (Λ * ((ξ : ℝ) - 1))
    calc (cosh (Λ * ((ξ : ℝ) - 1)))⁻¹ * |green ((q * (w * y)).ext h.le) ξ|
        ≤ (cosh (Λ * ((ξ : ℝ) - 1)))⁻¹ * (‖q‖ * ‖y‖ / ((1 + a) * Λ) * cosh (Λ * ((ξ : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left hg (by positivity)
      _ = ‖q‖ * ‖y‖ / ((1 + a) * Λ) := by field_simp
  refine hbound.trans_lt ?_
  rw [hΛ, div_lt_one (by positivity)]
  field_simp
  nlinarith [norm_nonneg q]

/-- `1 + W M_q` is invertible on `C([a, b])`: conjugated by `cosh(Λ(ξ − 1))` it is `1 + T`, `‖T‖ < 1`. -/
theorem isUnit_one_add_volterra_mul (h : Adm a b) (q : Cab a b) :
    IsUnit (1 + volterra h * mulOp q) := by
  obtain ⟨w, w', hww', hw'w, hlt⟩ := weighted_norm_lt h q
  set T := mulOp w' * (volterra h * mulOp q) * mulOp w
  have hT : IsUnit (1 + T) := by
    have hn : ‖-T‖ < 1 := by rwa [norm_neg]
    simpa using isUnit_one_sub_of_norm_lt_one hn
  have hM1 : mulOp w * mulOp w' = 1 := by
    ext y : 1; simp [mulOp, ← mul_assoc, hww']
  have hM2 : mulOp w' * mulOp w = 1 := by
    ext y : 1; simp [mulOp, ← mul_assoc, hw'w]
  have hMu : IsUnit (mulOp w) := ⟨⟨mulOp w, mulOp w', hM1, hM2⟩, rfl⟩
  have hMu' : IsUnit (mulOp w') := ⟨⟨mulOp w', mulOp w, hM2, hM1⟩, rfl⟩
  have e : 1 + volterra h * mulOp q = mulOp w * (1 + T) * mulOp w' := by
    simp only [T, mul_add, add_mul, mul_one]
    rw [hM1]
    congr 1
    calc volterra h * mulOp q
        = (mulOp w * mulOp w') * (volterra h * mulOp q) * (mulOp w * mulOp w') := by rw [hM1]; simp
      _ = mulOp w * (mulOp w' * (volterra h * mulOp q) * mulOp w) * mulOp w' := by noncomm_ring
  rw [e]
  exact (hMu.mul hT).mul hMu'

/-! ### The regular solution and its `χ`-dependence -/

/-- The regular solution on `[a, b]`: the solution of `y + W(q y) = 1`. -/
def regOn (h : Adm a b) (q : Cab a b) : Cab a b :=
  Ring.inverse (1 + volterra h * mulOp q) 1

theorem regOn_add (h : Adm a b) (q : Cab a b) :
    regOn h q + volterra h (q * regOn h q) = 1 := by
  have hu := isUnit_one_add_volterra_mul h q
  have := congrArg (fun T : Cab a b →L[ℝ] Cab a b => T 1) (Ring.mul_inverse_cancel _ hu)
  simpa [regOn, mulOp] using this

/-- Every solution of `y + W(q y) = r` is `r` times the regular solution. -/
theorem eq_smul_regOn (h : Adm a b) {q y : Cab a b} {r : ℝ}
    (hy : y + volterra h (q * y) = r • 1) : y = r • regOn h q := by
  have hu := isUnit_one_add_volterra_mul h q
  have h1 : (1 + volterra h * mulOp q) y = r • 1 := by simpa [mulOp] using hy
  have := congrArg (fun z => Ring.inverse (1 + volterra h * mulOp q) z) h1
  rw [show Ring.inverse (1 + volterra h * mulOp q) ((1 + volterra h * mulOp q) y) =
      (Ring.inverse (1 + volterra h * mulOp q) * (1 + volterra h * mulOp q)) y from rfl,
    Ring.inverse_mul_cancel _ hu, map_smul] at this
  simpa [regOn] using this

/-- The integral equation, pointwise. -/
theorem regOn_apply (h : Adm a b) (q : Cab a b) (ξ : Icc a b) :
    (regOn h q).toC ξ = 1 - green ((q * regOn h q).ext h.le) ξ := by
  have := congrArg (fun y : Cab a b => y.toC ξ) (regOn_add h q)
  have hv := volterra_apply h (q * regOn h q) ξ
  have e : (regOn h q + volterra h (q * regOn h q)).toC ξ =
      (regOn h q).toC ξ + (volterra h (q * regOn h q)).toC ξ := rfl
  have e1 : (1 : Cab a b).toC ξ = 1 := rfl
  simp only [e, e1] at this
  linarith

/-- Locality: on a smaller admissible interval the regular solution is the restriction. -/
theorem regOn_restrict {a' b' : ℝ} (h : Adm a b) (h' : Adm a' b') (ha : a' ≤ a) (hb : b ≤ b')
    (Q : C(ℝ, ℝ)) {x : ℝ} (hx : x ∈ Icc a b) :
    (regOn h (Cab.restr Q)).ext h.le x = (regOn h' (Cab.restr Q)).ext h'.le x := by
  have hsub : Icc a b ⊆ Icc a' b' := Icc_subset_Icc ha hb
  set R' := (regOn h' (Cab.restr Q)).ext h'.le
  have hR'c : Continuous R' := Cab.continuous_ext _ _
  let y : Cab a b := Cab.ofFun R' hR'c.continuousOn
  have hy : y + volterra h (Cab.restr Q * y) = (1 : ℝ) • 1 := by
    apply ContinuousMap.ext; intro ξ
    show y.toC ξ + (volterra h (Cab.restr Q * y)).toC ξ = 1 * 1
    rw [volterra_apply, Cab.ofFun_apply]
    have hξ' : (ξ : ℝ) ∈ Icc a' b' := hsub ξ.2
    have h1 := regOn_apply h' (Cab.restr Q) ⟨ξ, hξ'⟩
    have hR : R' ξ = (regOn h' (Cab.restr Q)).toC ⟨ξ, hξ'⟩ := Cab.ext_eq _ _ hξ'
    have hg : green ((Cab.restr Q * y).ext h.le) ξ = green ((Cab.restr Q * regOn h' (Cab.restr Q)).ext h'.le) ξ := by
      apply green_congr
      intro s hs
      have hsI : s ∈ Icc a b := h.sub ξ.2 hs
      rw [Cab.ext_mul, Cab.ext_mul]
      simp only [Pi.mul_apply]
      rw [Cab.ext_restr _ _ hsI, Cab.ext_restr _ _ (hsub hsI), Cab.ext_eq _ _ hsI, Cab.ofFun_apply]
    rw [hg, hR, h1]; ring
  have := eq_smul_regOn h hy
  rw [one_smul] at this
  rw [← this, Cab.ext_eq _ _ hx, Cab.ofFun_apply]

theorem mulOp_algebraMap (χ : ℝ) :
    mulOp (algebraMap ℝ (Cab a b) χ) = χ • (1 : Cab a b →L[ℝ] Cab a b) := by
  ext y : 1
  simp [mulOp, Algebra.algebraMap_eq_smul_one]

theorem one_add_mulOp_sub (h : Adm a b) (q : Cab a b) (χ : ℝ) :
    1 + volterra h * mulOp (q - algebraMap ℝ (Cab a b) χ) =
      (1 + volterra h * mulOp q) - χ • volterra h := by
  have e1 : mulOp (q - algebraMap ℝ (Cab a b) χ) = mulOp q - χ • (1 : Cab a b →L[ℝ] Cab a b) := by
    rw [mulOp, map_sub, ← mulOp, ← mulOp, mulOp_algebraMap]
  have e2 : volterra h * χ • (1 : Cab a b →L[ℝ] Cab a b) = χ • volterra h := by
    ext y : 1; simp
  rw [e1, mul_sub, e2]; abel

/-- The variational solution on `[a, b]`: `ḟ = (1 + W M_q)⁻¹ W f`. -/
def dotOn (h : Adm a b) (q : Cab a b) : Cab a b :=
  Ring.inverse (1 + volterra h * mulOp q) (volterra h (regOn h q))

theorem dotOn_add (h : Adm a b) (q : Cab a b) :
    dotOn h q + volterra h (q * dotOn h q) = volterra h (regOn h q) := by
  have hu := isUnit_one_add_volterra_mul h q
  have := congrArg (fun T : Cab a b →L[ℝ] Cab a b => T (volterra h (regOn h q)))
    (Ring.mul_inverse_cancel _ hu)
  simpa [dotOn, mulOp] using this

/-- The `χ`-derivative of the regular solution along `q − χ` is `dotOn`. -/
theorem hasDerivAt_regOn_sub (h : Adm a b) (q : Cab a b) (χ : ℝ) :
    HasDerivAt (fun χ : ℝ => regOn h (q - algebraMap ℝ (Cab a b) χ))
      (dotOn h (q - algebraMap ℝ (Cab a b) χ)) χ := by
  obtain ⟨u, hu⟩ := isUnit_one_add_volterra_mul h (q - algebraMap ℝ (Cab a b) χ)
  have hpath : HasDerivAt (fun χ : ℝ => (1 + volterra h * mulOp q) - χ • volterra h)
      (-volterra h) χ := by
    simpa using ((hasDerivAt_id χ).smul_const (volterra h)).const_sub (1 + volterra h * mulOp q)
  have hpath' : HasDerivAt (fun χ : ℝ => 1 + volterra h * mulOp (q - algebraMap ℝ (Cab a b) χ))
      (-volterra h) χ := by
    simpa only [one_add_mulOp_sub] using hpath
  have hR := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hR
  have hinv := hR.comp_hasDerivAt χ hpath'
  have happ := hinv.clm_apply (hasDerivAt_const χ (1 : Cab a b))
  have hinvu : Ring.inverse (1 + volterra h * mulOp (q - algebraMap ℝ (Cab a b) χ)) = ↑u⁻¹ := by
    rw [← hu, Ring.inverse_unit]
  refine happ.congr_deriv ?_
  rw [map_zero, add_zero, map_neg]
  simp only [neg_apply, neg_neg, ContinuousLinearMap.mulLeftRight_apply]
  rw [dotOn, regOn, hinvu]
  rfl

/-- The regular solution is real-analytic in `χ` along `q − χ`. -/
theorem analyticAt_regOn_sub (h : Adm a b) (q : Cab a b) (χ : ℝ) :
    AnalyticAt ℝ (fun χ : ℝ => regOn h (q - algebraMap ℝ (Cab a b) χ)) χ := by
  obtain ⟨u, hu⟩ := isUnit_one_add_volterra_mul h (q - algebraMap ℝ (Cab a b) χ)
  have hpath : AnalyticAt ℝ (fun χ : ℝ => (1 + volterra h * mulOp q) - χ • volterra h) χ :=
    analyticAt_const.sub (analyticAt_id.smul analyticAt_const)
  have hinv : AnalyticAt ℝ Ring.inverse ((1 + volterra h * mulOp q) - χ • volterra h) := by
    rw [← one_add_mulOp_sub, ← hu]; exact analyticAt_inverse u
  have hcomp := AnalyticAt.comp (g := Ring.inverse)
    (f := fun χ : ℝ => (1 + volterra h * mulOp q) - χ • volterra h) hinv hpath
  have happ := AnalyticAt.comp (g := ContinuousLinearMap.apply ℝ (Cab a b) (1 : Cab a b))
    (f := Ring.inverse ∘ fun χ : ℝ => (1 + volterra h * mulOp q) - χ • volterra h)
    ((ContinuousLinearMap.apply ℝ (Cab a b) (1 : Cab a b)).analyticAt _) hcomp
  refine happ.congr (Filter.Eventually.of_forall fun χ' => ?_)
  simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, regOn, one_add_mulOp_sub]

end Cvs.Prolate.VolterraResolventEdge
