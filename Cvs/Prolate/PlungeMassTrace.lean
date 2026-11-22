import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.BandMassLaw
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RungMirrorIdentity
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plunge mass: `tr K − tr K²` in closed form and the even Bessel bound
For the sinc kernel `K(u) = sin(cu)/(πu)` on `[−1, 1]`: `tr K − tr K² = 2c/π − (4c/π²) Si(4c) + (2/π²) sin²(2c)
+ Cin(4c)/π²`, with `Si z = ∫₀^z sin t/t` and `Cin z = ∫₀^z (1 − cos t)/t`. For normalised even rungs at distinct
levels, Bessel's inequality for `y ↦ (K(ξ − y) + K(ξ + y))/2` at each `ξ > 1` gives
`Σ λ(1 − λ) ≤ (Cin(4c)/2 + 1/2 + 1/(4c) + (2 + log(2c³ + 1))/c)/π²` with no completeness.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.BandMassLaw
open scoped Interval

namespace Cvs.Prolate.PlungeMassTrace

/-! ### The sinc kernel, `Si` and `Cin` -/

/-- The sinc kernel `K(u) = (c/π) sinc(cu) = sin(cu)/(πu)`. -/
def kS (c u : ℝ) : ℝ := c / π * sinc (c * u)

/-- The entire cosine integral `Cin z = ∫₀^z (1 − cos t)/t dt`. -/
def Cin (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, (1 - cos t) / t

theorem continuous_kS (c : ℝ) : Continuous (kS c) := by
  unfold kS; fun_prop

theorem abs_kS_le {c : ℝ} (hc : 0 < c) (u : ℝ) : |kS c u| ≤ c / π := by
  unfold kS
  rw [abs_mul, abs_of_pos (by positivity : 0 < c / π)]
  exact mul_le_of_le_one_right (by positivity) (abs_sinc_le_one _)

theorem kS_of_ne {c u : ℝ} (hc : c ≠ 0) (hu : u ≠ 0) : kS c u = sin (c * u) / (π * u) := by
  unfold kS
  rw [sinc_of_ne_zero (mul_ne_zero hc hu)]
  field_simp

theorem kS_sq_of_ne {c u : ℝ} (hc : c ≠ 0) (hu : u ≠ 0) : kS c u ^ 2 = sin (c * u) ^ 2 / (π ^ 2 * u ^ 2) := by
  rw [kS_of_ne hc hu, div_pow, mul_pow]

/-- `(1 − cos t)/t = sin(t/2) sinc(t/2)` for every `t` (both sides vanish at `0`). -/
theorem cin_integrand_eq (t : ℝ) : (1 - cos t) / t = sin (t / 2) * sinc (t / 2) := by
  rcases eq_or_ne t 0 with h | h
  · subst h; simp
  · have h2 : t / 2 ≠ 0 := by positivity
    rw [sinc_of_ne_zero h2]
    have : cos t = 1 - 2 * sin (t / 2) ^ 2 := by
      rw [show t = 2 * (t / 2) by ring, cos_two_mul, cos_sq']; ring_nf
    rw [this]
    field_simp
    ring

theorem continuous_cin_integrand : Continuous fun t : ℝ => (1 - cos t) / t := by
  simp_rw [cin_integrand_eq]; fun_prop

/-! ### Integration by parts against `cos(kx)` -/

/-- **Integration by parts against `cos(kx)`**: `|∫_a^b w(x) cos(kx)| ≤ (|w a| + |w b| + ∫_a^b |w'|)/k`. -/
theorem abs_integral_mul_cos_le {w w' : ℝ → ℝ} {a b k : ℝ} (hab : a ≤ b) (hk : 0 < k)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw' : ContinuousOn w' (Icc a b)) :
    |∫ x in a..b, w x * cos (k * x)| ≤ (|w a| + |w b| + ∫ x in a..b, |w' x|) / k := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have hv : ∀ x ∈ uIcc a b, HasDerivAt (fun x => sin (k * x) / k) (cos (k * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => k * x) k x := by simpa using (hasDerivAt_id x).const_mul k
    have := h1.sin.div_const k
    rwa [mul_div_assoc, div_self hk.ne', mul_one] at this
  have hu : ∀ x ∈ uIcc a b, HasDerivAt w (w' x) x := fun x hx => hw x (hI ▸ hx)
  have hw'u : ContinuousOn w' (uIcc a b) := hI ▸ hw'
  have hcos : IntervalIntegrable (fun x => cos (k * x)) volume a b := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_mul_deriv_eq_deriv_mul hu hv hw'u.intervalIntegrable hcos]
  have hsin : ∀ x, |sin (k * x) / k| ≤ 1 / k := fun x => by
    rw [abs_div, abs_of_pos hk]; exact div_le_div_of_nonneg_right (abs_sin_le_one _) hk.le
  have hsc : Continuous fun x => sin (k * x) / k := by fun_prop
  have hint : |∫ x in a..b, w' x * (sin (k * x) / k)| ≤ (∫ x in a..b, |w' x|) / k := by
    calc |∫ x in a..b, w' x * (sin (k * x) / k)| ≤ ∫ x in a..b, |w' x * (sin (k * x) / k)| :=
          abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, |w' x| * (1 / k) := by
          apply integral_mono_on hab
          · exact ((hw'u.mul hsc.continuousOn).abs).intervalIntegrable
          · exact (hw'u.abs.mul continuousOn_const).intervalIntegrable
          · intro x _; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hsin x) (abs_nonneg _)
      _ = (∫ x in a..b, |w' x|) / k := by rw [intervalIntegral.integral_mul_const]; ring
  have hb : |w b * (sin (k * b) / k)| ≤ |w b| / k := by
    have := mul_le_mul_of_nonneg_left (hsin b) (abs_nonneg (w b))
    rw [abs_mul]; linarith [show |w b| * (1 / k) = |w b| / k by ring]
  have ha : |w a * (sin (k * a) / k)| ≤ |w a| / k := by
    have := mul_le_mul_of_nonneg_left (hsin a) (abs_nonneg (w a))
    rw [abs_mul]; linarith [show |w a| * (1 / k) = |w a| / k by ring]
  calc _ ≤ |w b * (sin (k * b) / k) - w a * (sin (k * a) / k)|
        + |∫ x in a..b, w' x * (sin (k * x) / k)| := abs_sub _ _
    _ ≤ (|w b * (sin (k * b) / k)| + |w a * (sin (k * a) / k)|)
        + |∫ x in a..b, w' x * (sin (k * x) / k)| := by gcongr; exact abs_sub _ _
    _ ≤ (|w b| / k + |w a| / k) + (∫ x in a..b, |w' x|) / k := by gcongr
    _ = _ := by ring

/-- For increasing `w ≥ 0` on `[a, b]`: `|∫_a^b w(x) cos(kx)| ≤ 2 w(b)/k`. -/
theorem abs_integral_mul_cos_le_of_mono {w w' : ℝ → ℝ} {a b k : ℝ} (hab : a ≤ b) (hk : 0 < k)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw' : ContinuousOn w' (Icc a b))
    (hw'0 : ∀ x ∈ Icc a b, 0 ≤ w' x) (hwa : 0 ≤ w a) :
    |∫ x in a..b, w x * cos (k * x)| ≤ 2 * w b / k := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have hFTC : ∫ x in a..b, w' x = w b - w a :=
    integral_eq_sub_of_hasDerivAt (fun x hx => hw x (hI ▸ hx)) (hI ▸ hw').intervalIntegrable
  have habs : ∫ x in a..b, |w' x| = w b - w a := by
    rw [← hFTC]
    exact integral_congr fun x hx => abs_of_nonneg (hw'0 x (hI ▸ hx))
  have hwb : w a ≤ w b := by
    have : 0 ≤ ∫ x in a..b, w' x := integral_nonneg hab fun x hx => hw'0 x hx
    linarith
  have h := abs_integral_mul_cos_le hab hk hw hw'
  rw [habs, abs_of_nonneg hwa, abs_of_nonneg (hwa.trans hwb)] at h
  calc _ ≤ _ := h
    _ = 2 * w b / k := by ring

/-- For decreasing `w` with `w(b) ≥ 0` on `[a, b]`: `|∫_a^b w(x) cos(kx)| ≤ 2 w(a)/k`. -/
theorem abs_integral_mul_cos_le_of_anti {w w' : ℝ → ℝ} {a b k : ℝ} (hab : a ≤ b) (hk : 0 < k)
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (w' x) x) (hw' : ContinuousOn w' (Icc a b))
    (hw'0 : ∀ x ∈ Icc a b, w' x ≤ 0) (hwb : 0 ≤ w b) :
    |∫ x in a..b, w x * cos (k * x)| ≤ 2 * w a / k := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have hFTC : ∫ x in a..b, w' x = w b - w a :=
    integral_eq_sub_of_hasDerivAt (fun x hx => hw x (hI ▸ hx)) (hI ▸ hw').intervalIntegrable
  have habs : ∫ x in a..b, |w' x| = w a - w b := by
    have : ∫ x in a..b, |w' x| = ∫ x in a..b, -w' x :=
      integral_congr fun x hx => abs_of_nonpos (hw'0 x (hI ▸ hx))
    rw [this, intervalIntegral.integral_neg, hFTC]; ring
  have hwa : w b ≤ w a := by
    have : 0 ≤ ∫ x in a..b, -w' x := integral_nonneg hab fun x hx => neg_nonneg.2 (hw'0 x hx)
    rw [intervalIntegral.integral_neg] at this
    linarith
  have h := abs_integral_mul_cos_le hab hk hw hw'
  rw [habs, abs_of_nonneg hwb, abs_of_nonneg (hwb.trans hwa)] at h
  calc _ ≤ _ := h
    _ = 2 * w a / k := by ring

/-! ### Cosine integrals and the even kernel -/

/-- `∫_{−1}^{1} cos(kx) dx = 2 sinc k`. -/
theorem integral_cos_mul (k : ℝ) : ∫ x in (-1 : ℝ)..1, cos (k * x) = 2 * sinc k := by
  rcases eq_or_ne k 0 with h | h
  · subst h; norm_num
  · rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) h, integral_cos, sinc_of_ne_zero h,
      smul_eq_mul, mul_neg, mul_one, sin_neg]
    field_simp
    ring

/-- `∫_{−1}^{1} cos(ax) cos(bx) dx = sinc(a − b) + sinc(a + b)`. -/
theorem integral_cos_mul_cos (a b : ℝ) :
    ∫ x in (-1 : ℝ)..1, cos (a * x) * cos (b * x) = sinc (a - b) + sinc (a + b) := by
  have e : ∀ x, cos (a * x) * cos (b * x) = (cos ((a - b) * x) + cos ((a + b) * x)) / 2 := by
    intro x
    rw [sub_mul, add_mul, cos_sub, cos_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add, integral_cos_mul, integral_cos_mul]
  · ring
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

/-- The even kernel `kE(ξ, y) = (K(ξ − y) + K(ξ + y))/2`. -/
def kE (c ξ y : ℝ) : ℝ := (kS c (ξ - y) + kS c (ξ + y)) / 2

theorem integral_cos_cos_eq_kE {c : ℝ} (hc : c ≠ 0) (ξ y : ℝ) :
    ∫ x in (-1 : ℝ)..1, cos (c * ξ * x) * cos (c * y * x) = 2 * π / c * kE c ξ y := by
  rw [integral_cos_mul_cos]
  unfold kE kS
  rw [mul_sub, mul_add]
  field_simp

/-- **The even kernel reproduces a rung**: `∫_{−1}^{1} kE(ξ, y) g(y) dy = (c/2π) μ ψ(ξ)` when `psi c g = μ g` on
`[−1, 1]`, by one Fubini swap. -/
theorem integral_kE_mul {g : ℝ → ℝ} {c μ : ℝ} (hc : 0 < c) (hgc : ContinuousOn g (Icc (-1) 1))
    (hμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μ * g s) (ξ : ℝ) :
    ∫ y in (-1 : ℝ)..1, kE c ξ y * g y = c / (2 * π) * μ * psi c g ξ := by
  have hu : ContinuousOn (fun x => cos (c * ξ * x)) (Icc (-1) 1) := by fun_prop
  have hsw := Cvs.Prolate.CosineChristoffelDarboux.swap_cos c hu hgc
  have hL : ∫ x in (-1 : ℝ)..1, cos (c * ξ * x) * (∫ s in (-1 : ℝ)..1, g s * cos (c * x * s))
      = μ * psi c g ξ := by
    have : ∀ x ∈ uIcc (-1 : ℝ) 1, cos (c * ξ * x) * (∫ s in (-1 : ℝ)..1, g s * cos (c * x * s))
        = μ * (g x * cos (c * ξ * x)) := by
      intro x hx
      rw [uIcc_of_le (by norm_num)] at hx
      have h1 : (∫ s in (-1 : ℝ)..1, g s * cos (c * x * s)) = psi c g x := rfl
      rw [h1, hμ x hx]; ring
    rw [integral_congr this, intervalIntegral.integral_const_mul]
    rfl
  have hR : ∫ s in (-1 : ℝ)..1, g s * (∫ x in (-1 : ℝ)..1, cos (c * ξ * x) * cos (c * s * x))
      = 2 * π / c * ∫ y in (-1 : ℝ)..1, kE c ξ y * g y := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun s _ => ?_
    rw [integral_cos_cos_eq_kE hc.ne']; ring
  rw [hL, hR] at hsw
  have hπ : 0 < 2 * π / c := by positivity
  field_simp at hsw ⊢
  linarith

/-! ### The trace identity -/

/-- `∫_{−1}^{1} f(x − y) dy = ∫₀^{x+1} f − ∫₀^{x−1} f` for continuous `f`. -/
theorem integral_comp_sub_eq {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    ∫ y in (-1 : ℝ)..1, f (x - y) = (∫ u in (0 : ℝ)..x + 1, f u) - ∫ u in (0 : ℝ)..x - 1, f u := by
  rw [intervalIntegral.integral_comp_sub_left (fun u => f u) x, sub_neg_eq_add,
    intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]

theorem hasDerivAt_primitive {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, f u) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
    hf.continuousAt

theorem continuous_primitive' {f : ℝ → ℝ} (hf : Continuous f) : Continuous fun x => ∫ u in (0 : ℝ)..x, f u :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_primitive hf x).continuousAt

/-- `∫₀^b F = b F(b) − ∫₀^b u f(u)` for the primitive `F` of a continuous `f`. -/
theorem integral_primitive {f : ℝ → ℝ} (hf : Continuous f) (b : ℝ) :
    ∫ x in (0 : ℝ)..b, (∫ u in (0 : ℝ)..x, f u)
      = b * (∫ u in (0 : ℝ)..b, f u) - ∫ u in (0 : ℝ)..b, u * f u := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := b)
    (u := fun x => ∫ u in (0 : ℝ)..x, f u) (u' := f) (v := fun x => x) (v' := fun _ => 1)
    (fun x _ => hasDerivAt_primitive hf x) (fun x _ => hasDerivAt_id x)
    (hf.intervalIntegrable _ _) intervalIntegrable_const
  simp only [mul_one, intervalIntegral.integral_same, mul_zero, sub_zero] at h
  rw [h]
  have : ∫ x in (0 : ℝ)..b, f x * x = ∫ x in (0 : ℝ)..b, x * f x := integral_congr fun x _ => mul_comm _ _
  rw [this, mul_comm]

theorem continuous_kS_sq (c : ℝ) : Continuous fun u => kS c u ^ 2 := (continuous_kS c).pow 2

/-- `∫₀² u K(u)² du = Cin(4c)/(2π²)`. -/
theorem integral_mul_kS_sq {c : ℝ} (hc : 0 < c) :
    ∫ u in (0 : ℝ)..2, u * kS c u ^ 2 = Cin (4 * c) / (2 * π ^ 2) := by
  have e : ∀ u, u * kS c u ^ 2 = c / π ^ 2 * ((fun t => (1 - cos t) / t) (2 * c * u)) := by
    intro u
    rcases eq_or_ne u 0 with h | h
    · subst h; simp
    · rw [kS_sq_of_ne hc.ne' h]
      simp only
      rw [show 2 * c * u = 2 * (c * u) by ring, cos_two_mul, cos_sq']
      field_simp
      ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t => (1 - cos t) / t) (by positivity : 2 * c ≠ 0)]
  rw [Cin, smul_eq_mul, mul_zero, show 2 * c * 2 = 4 * c by ring]
  field_simp

/-! ### The diagonal part of the even Bessel bound -/

/-- `∫_2^b (1/u²) cos(ku) du` is at most `1/(2k)` in size, `b ≥ 2`. -/
theorem abs_integral_inv_sq_cos_le {b k : ℝ} (hb : 2 ≤ b) (hk : 0 < k) :
    |∫ u in (2 : ℝ)..b, (u ^ 2)⁻¹ * cos (k * u)| ≤ 1 / (2 * k) := by
  have hpos : ∀ u ∈ Icc (2 : ℝ) b, u ≠ 0 := fun u hu => by linarith [hu.1]
  have hd : ∀ u ∈ Icc (2 : ℝ) b, HasDerivAt (fun u => (u ^ 2)⁻¹) (-(2 * u) / (u ^ 2) ^ 2) u := by
    intro u hu
    have h := (hasDerivAt_pow 2 u).inv (pow_ne_zero 2 (hpos u hu))
    refine h.congr_deriv ?_
    norm_num
  have hc : ContinuousOn (fun u : ℝ => -(2 * u) / (u ^ 2) ^ 2) (Icc 2 b) :=
    ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun u hu => pow_ne_zero 2 (pow_ne_zero 2 (hpos u hu))
  have h := abs_integral_mul_cos_le_of_anti hb hk hd hc
    (fun u hu => div_nonpos_of_nonpos_of_nonneg (by linarith [hu.1]) (by positivity)) (by positivity)
  calc _ ≤ _ := h
    _ = 1 / (2 * k) := by field_simp

/-- `∫₂^b K² ≤ (1/2 + 1/(4c))/(2π²)` for `b ≥ 2`: `K² = (1 − cos 2cu)/(2π²u²)` and the oscillating part is
`O(1/c)`. -/
theorem integral_kS_sq_tail_le {c b : ℝ} (hc : 0 < c) (hb : 2 ≤ b) :
    ∫ u in (2 : ℝ)..b, kS c u ^ 2 ≤ (1 / 2 + 1 / (4 * c)) / (2 * π ^ 2) := by
  have e : ∀ u ∈ uIcc (2 : ℝ) b,
      kS c u ^ 2 = ((u ^ 2)⁻¹ - (u ^ 2)⁻¹ * cos (2 * c * u)) / (2 * π ^ 2) := by
    intro u hu
    rw [uIcc_of_le hb] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    rw [kS_sq_of_ne hc.ne' hu0, show 2 * c * u = 2 * (c * u) by ring, cos_two_mul, cos_sq']
    field_simp
    ring
  have hpos : ∀ u ∈ uIcc (2 : ℝ) b, u ≠ 0 := fun u hu => by
    rw [uIcc_of_le hb] at hu; linarith [hu.1]
  have hi1 : IntervalIntegrable (fun u : ℝ => (u ^ 2)⁻¹) volume 2 b :=
    (ContinuousOn.inv₀ (by fun_prop) fun u hu => pow_ne_zero 2 (hpos u hu)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun u : ℝ => (u ^ 2)⁻¹ * cos (2 * c * u)) volume 2 b :=
    ((ContinuousOn.inv₀ (by fun_prop) fun u hu => pow_ne_zero 2 (hpos u hu)).mul
      (by fun_prop : Continuous fun u : ℝ => cos (2 * c * u)).continuousOn).intervalIntegrable
  rw [integral_congr e, intervalIntegral.integral_div, intervalIntegral.integral_sub hi1 hi2]
  have hI : ∫ u in (2 : ℝ)..b, (u ^ 2)⁻¹ = 1 / 2 - 1 / b := by
    have hd : ∀ u ∈ uIcc (2 : ℝ) b, HasDerivAt (fun u => -u⁻¹) ((u ^ 2)⁻¹) u := by
      intro u hu
      have := (hasDerivAt_inv (hpos u hu)).neg
      rw [neg_neg] at this
      exact this
    rw [integral_eq_sub_of_hasDerivAt hd hi1]
    ring
  have hJ := abs_integral_inv_sq_cos_le hb (by positivity : 0 < 2 * c)
  rw [hI]
  have hb0 : 0 < b := by linarith
  have h1b : 0 ≤ 1 / b := by positivity
  have hJ' : -(∫ u in (2 : ℝ)..b, (u ^ 2)⁻¹ * cos (2 * c * u)) ≤ 1 / (4 * c) := by
    have := neg_le_abs (∫ u in (2 : ℝ)..b, (u ^ 2)⁻¹ * cos (2 * c * u))
    have e2 : 1 / (2 * (2 * c)) = 1 / (4 * c) := by ring
    linarith
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- `∫_{−1}^{1} K(ξ − y)² dy`, the diagonal part. -/
def aK (c ξ : ℝ) : ℝ := ∫ y in (-1 : ℝ)..1, kS c (ξ - y) ^ 2

/-- **The diagonal bound**: `∫₁^R ∫_{−1}^{1} K(ξ − y)² dy dξ ≤ Cin(4c)/(2π²) + (1/2 + 1/(4c))/π²` for `R ≥ 1`. -/
theorem integral_aK_le {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) :
    ∫ ξ in (1 : ℝ)..R, aK c ξ ≤ Cin (4 * c) / (2 * π ^ 2) + (1 / 2 + 1 / (4 * c)) / π ^ 2 := by
  set f : ℝ → ℝ := fun u => kS c u ^ 2 with hf
  have hfc : Continuous f := continuous_kS_sq c
  set F : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, f u with hF
  have hFc : Continuous F := continuous_primitive' hfc
  have hin : ∀ ξ, aK c ξ = F (ξ + 1) - F (ξ - 1) := fun ξ => integral_comp_sub_eq hfc ξ
  simp_rw [hin]
  rw [intervalIntegral.integral_sub (f := fun x => F (x + 1)) (g := fun x => F (x - 1))
    ((hFc.comp (continuous_add_const 1)).intervalIntegrable _ _)
    ((hFc.comp (continuous_sub_right 1)).intervalIntegrable _ _),
    intervalIntegral.integral_comp_add_right F 1, intervalIntegral.integral_comp_sub_right F 1,
    show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num]
  have hFi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hFc.intervalIntegrable a b
  have hsplit : (∫ x in (2 : ℝ)..R + 1, F x) - ∫ x in (0 : ℝ)..R - 1, F x
      = (∫ x in R - 1..R + 1, F x) - ∫ x in (0 : ℝ)..2, F x := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hFi 0 2) (hFi 2 (R + 1))
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hFi 0 (R - 1)) (hFi (R - 1) (R + 1))
    linarith
  rw [hsplit]
  have hmono : ∫ x in R - 1..R + 1, F x ≤ ∫ x in R - 1..R + 1, F (R + 1) := by
    apply integral_mono_on (by linarith) (hFi _ _) intervalIntegrable_const
    intro x hx
    have hxx : F (R + 1) - F x = ∫ u in x..R + 1, f u := by
      simp only [hF]
      rw [intervalIntegral.integral_interval_sub_left (hfc.intervalIntegrable _ _)
        (hfc.intervalIntegrable _ _)]
    have : 0 ≤ ∫ u in x..R + 1, f u := integral_nonneg hx.2 fun u _ => sq_nonneg _
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hprim := integral_primitive hfc 2
  have h2 : F (R + 1) - F 2 = ∫ u in (2 : ℝ)..R + 1, f u := by
    simp only [hF]
    rw [intervalIntegral.integral_interval_sub_left (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
  have htail := integral_kS_sq_tail_le hc (show (2 : ℝ) ≤ R + 1 by linarith)
  have hmul := integral_mul_kS_sq hc
  have e1 : (∫ x in (0 : ℝ)..2, F x) = ∫ x in (0 : ℝ)..2, (∫ u in (0 : ℝ)..x, f u) := rfl
  rw [e1, hprim]
  have e3 : (∫ u in (0 : ℝ)..2, u * f u) = ∫ u in (0 : ℝ)..2, u * kS c u ^ 2 := rfl
  have e4 : (∫ u in (2 : ℝ)..R + 1, f u) = ∫ u in (2 : ℝ)..R + 1, kS c u ^ 2 := rfl
  have e5 : (∫ u in (0 : ℝ)..2, f u) = F 2 := rfl
  rw [e3, hmul, e5]
  rw [e4] at h2
  have hπ : 0 < π ^ 2 := by positivity
  have : (1 / 2 + 1 / (4 * c)) / π ^ 2 = 2 * ((1 / 2 + 1 / (4 * c)) / (2 * π ^ 2)) := by
    field_simp
  rw [this]
  nlinarith

/-! ### `Cin` grows like `log` -/

/-- `Cin z ≤ log z − log 2 + 2` for `z ≥ 2`: `(1 − cos t)/t ≤ t/2` on `[0, 2]`, and `|∫₂^z cos t/t| ≤ 1`. -/
theorem Cin_le {z : ℝ} (hz : 2 ≤ z) : Cin z ≤ log z - log 2 + 2 := by
  have hφ := continuous_cin_integrand
  unfold Cin
  rw [← intervalIntegral.integral_add_adjacent_intervals (hφ.intervalIntegrable 0 2) (hφ.intervalIntegrable 2 z)]
  have h1 : ∫ t in (0 : ℝ)..2, (1 - cos t) / t ≤ 1 := by
    have : ∫ t in (0 : ℝ)..2, (1 - cos t) / t ≤ ∫ t in (0 : ℝ)..2, t / 2 := by
      apply integral_mono_on (by norm_num) (hφ.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t : ℝ => t / 2).intervalIntegrable _ _)
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; simp
      · rw [div_le_iff₀ h]
        nlinarith [one_sub_sq_div_two_le_cos (x := t)]
    have e : ∫ t in (0 : ℝ)..2, t / 2 = 1 := by
      rw [intervalIntegral.integral_div, integral_id]; norm_num
    linarith
  have hpos : ∀ t ∈ uIcc (2 : ℝ) z, t ≠ 0 := fun t ht => by
    rw [uIcc_of_le hz] at ht; linarith [ht.1]
  have e : ∀ t ∈ uIcc (2 : ℝ) z, (1 - cos t) / t = 1 / t - t⁻¹ * cos (1 * t) := by
    intro t ht
    rw [one_mul]
    field_simp [hpos t ht]
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / t) volume 2 z :=
    (continuousOn_const.div₀ continuousOn_id fun t ht => hpos t ht).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => t⁻¹ * cos (1 * t)) volume 2 z :=
    ((continuousOn_id.inv₀ fun t ht => hpos t ht).mul
      (by fun_prop : Continuous fun t : ℝ => cos (1 * t)).continuousOn).intervalIntegrable
  rw [integral_congr e, intervalIntegral.integral_sub hi1 hi2, integral_one_div (by
    rw [uIcc_of_le hz]; intro h; linarith [h.1])]
  have hd : ∀ t ∈ Icc (2 : ℝ) z, HasDerivAt (fun t => t⁻¹) (-(t ^ 2)⁻¹) t := fun t ht =>
    hasDerivAt_inv (by linarith [ht.1])
  have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Icc 2 z) :=
    (ContinuousOn.inv₀ (by fun_prop) fun t ht => pow_ne_zero 2 (by linarith [ht.1])).neg
  have hJ := abs_integral_mul_cos_le_of_anti hz one_pos hd hc
    (fun t _ => neg_nonpos.2 (by positivity)) (by positivity)
  have hJ' : -(∫ t in (2 : ℝ)..z, t⁻¹ * cos (1 * t)) ≤ 1 := by
    have h3 := neg_le_abs (∫ t in (2 : ℝ)..z, t⁻¹ * cos (1 * t))
    norm_num at hJ h3 ⊢
    linarith
  rw [log_div (by linarith) (by norm_num)]
  linarith

/-! ### The cross part of the even Bessel bound -/

/-- `∫_{−1}^{1} K(ξ − y) K(ξ + y) dy`, the cross part. -/
def jK (c ξ : ℝ) : ℝ := ∫ y in (-1 : ℝ)..1, kS c (ξ - y) * kS c (ξ + y)

theorem continuous_aK (c : ℝ) : Continuous (aK c) := by
  unfold aK
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have := continuous_kS c
  fun_prop

theorem continuous_jK (c : ℝ) : Continuous (jK c) := by
  unfold jK
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have := continuous_kS c
  fun_prop

theorem abs_jK_le {c : ℝ} (hc : 0 < c) (ξ : ℝ) : |jK c ξ| ≤ 2 * (c / π) ^ 2 := by
  unfold jK
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1) (C := (c / π) ^ 2)
    (f := fun y => kS c (ξ - y) * kS c (ξ + y)) fun y _ => by
      rw [Real.norm_eq_abs, abs_mul, sq]
      exact mul_le_mul (abs_kS_le hc _) (abs_kS_le hc _) (abs_nonneg _) (by positivity)
  rw [Real.norm_eq_abs] at h
  norm_num at h
  linarith

/-- `K(ξ − y) K(ξ + y) = (cos 2cy − cos 2cξ)/(2π²(ξ² − y²))` off `ξ = ±y`. -/
theorem kS_mul_kS {c ξ y : ℝ} (hc : c ≠ 0) (h1 : ξ - y ≠ 0) (h2 : ξ + y ≠ 0) :
    kS c (ξ - y) * kS c (ξ + y) = (cos (2 * c * y) - cos (2 * c * ξ)) / (2 * π ^ 2 * (ξ ^ 2 - y ^ 2)) := by
  rw [kS_of_ne hc h1, kS_of_ne hc h2]
  have e1 : 2 * c * y = c * (ξ + y) - c * (ξ - y) := by ring
  have e2 : 2 * c * ξ = c * (ξ - y) + c * (ξ + y) := by ring
  rw [e1, e2, cos_sub, cos_add]
  have hsq : ξ ^ 2 - y ^ 2 = (ξ - y) * (ξ + y) := by ring
  rw [hsq]
  field_simp
  ring

/-- `∫_{−1}^{1} dy/(ξ² − y²) = ℓ(ξ)/ξ` for `ξ > 1`, with `ℓ(ξ) = log((ξ + 1)/(ξ − 1))`. -/
theorem integral_inv_sub_sq {ξ : ℝ} (hξ : 1 < ξ) : ∫ y in (-1 : ℝ)..1, 1 / (ξ ^ 2 - y ^ 2) = ellF ξ / ξ := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hp : ∀ y ∈ uIcc (-1 : ℝ) 1, 0 < ξ - y ∧ 0 < ξ + y := fun y hy => by
    rw [hI] at hy; constructor <;> linarith [hy.1, hy.2]
  have hd : ∀ y ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun y => (log (ξ + y) - log (ξ - y)) / (2 * ξ)) (1 / (ξ ^ 2 - y ^ 2)) y := by
    intro y hy
    obtain ⟨ha, hb⟩ := hp y hy
    have h1 : HasDerivAt (fun y => ξ + y) 1 y := by simpa using (hasDerivAt_id y).const_add ξ
    have h2 : HasDerivAt (fun y => ξ - y) (-1) y := by simpa using (hasDerivAt_id y).const_sub ξ
    have := ((h1.log hb.ne').sub (h2.log ha.ne')).div_const (2 * ξ)
    refine this.congr_deriv ?_
    have hsq : ξ ^ 2 - y ^ 2 = (ξ - y) * (ξ + y) := by ring
    rw [hsq]
    field_simp
    ring
  have hc : ContinuousOn (fun y : ℝ => 1 / (ξ ^ 2 - y ^ 2)) (uIcc (-1) 1) :=
    continuousOn_const.div₀ (by fun_prop) fun y hy => by
      obtain ⟨ha, hb⟩ := hp y hy; nlinarith
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  unfold ellF
  rw [log_div (by linarith) (by linarith)]
  have : ξ - -1 = ξ + 1 := by ring
  rw [this, show ξ + -1 = ξ - 1 by ring]
  field_simp
  ring

/-- **The cross part in closed form**: for `ξ > 1`,
`2π² jK(ξ) = ∫_{−1}^{1} cos(2cy)/(ξ² − y²) dy − cos(2cξ) ℓ(ξ)/ξ`. -/
theorem jK_eq {c ξ : ℝ} (hc : 0 < c) (hξ : 1 < ξ) :
    jK c ξ = ((∫ y in (-1 : ℝ)..1, 1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y)) - cos (2 * c * ξ) * (ellF ξ / ξ))
      / (2 * π ^ 2) := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hp : ∀ y ∈ uIcc (-1 : ℝ) 1, 0 < ξ - y ∧ 0 < ξ + y := fun y hy => by
    rw [hI] at hy; constructor <;> linarith [hy.1, hy.2]
  have e : ∀ y ∈ uIcc (-1 : ℝ) 1, kS c (ξ - y) * kS c (ξ + y)
      = (1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y) - cos (2 * c * ξ) * (1 / (ξ ^ 2 - y ^ 2))) / (2 * π ^ 2) := by
    intro y hy
    obtain ⟨ha, hb⟩ := hp y hy
    rw [kS_mul_kS hc.ne' ha.ne' hb.ne']
    have : ξ ^ 2 - y ^ 2 ≠ 0 := by nlinarith
    field_simp
  have hc1 : ContinuousOn (fun y : ℝ => 1 / (ξ ^ 2 - y ^ 2)) (uIcc (-1) 1) :=
    continuousOn_const.div₀ (by fun_prop) fun y hy => by
      obtain ⟨ha, hb⟩ := hp y hy; nlinarith
  have hcos : Continuous fun y : ℝ => cos (2 * c * y) := by fun_prop
  unfold jK
  rw [integral_congr e, intervalIntegral.integral_div, intervalIntegral.integral_sub
    (f := fun y => 1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y)) (g := fun y => cos (2 * c * ξ) * (1 / (ξ ^ 2 - y ^ 2)))
    (hc1.mul hcos.continuousOn).intervalIntegrable (continuousOn_const.mul hc1).intervalIntegrable,
    intervalIntegral.integral_const_mul, integral_inv_sub_sq hξ]

/-- `|∫_{−1}^{1} cos(2cy)/(ξ² − y²) dy| ≤ 2/(c(ξ² − 1))` for `ξ > 1`: integrate by parts on `[−1, 0]` and `[0, 1]`,
where `1/(ξ² − y²)` is monotone. -/
theorem abs_integral_inv_sub_sq_cos_le {c ξ : ℝ} (hc : 0 < c) (hξ : 1 < ξ) :
    |∫ y in (-1 : ℝ)..1, 1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y)| ≤ 2 / (c * (ξ ^ 2 - 1)) := by
  have hq : ∀ y ∈ Icc (-1 : ℝ) 1, 0 < ξ ^ 2 - y ^ 2 := fun y hy => by nlinarith [hy.1, hy.2]
  have hd : ∀ y ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun y => 1 / (ξ ^ 2 - y ^ 2)) (2 * y / (ξ ^ 2 - y ^ 2) ^ 2) y := by
    intro y hy
    have h1 : HasDerivAt (fun y => ξ ^ 2 - y ^ 2) (-(2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_sub (ξ ^ 2))
    have := (hasDerivAt_const y (1 : ℝ)).div h1 (hq y hy).ne'
    refine this.congr_deriv ?_
    ring
  have hdc : ContinuousOn (fun y : ℝ => 2 * y / (ξ ^ 2 - y ^ 2) ^ 2) (Icc (-1) 1) :=
    ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun y hy => pow_ne_zero 2 (hq y hy).ne'
  have hk : 0 < 2 * c := by positivity
  have hsub1 : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
  have hsub2 : Icc (-1 : ℝ) 0 ⊆ Icc (-1) 1 := Icc_subset_Icc le_rfl (by norm_num)
  have hR := abs_integral_mul_cos_le_of_mono (by norm_num : (0 : ℝ) ≤ 1) hk (fun y hy => hd y (hsub1 hy))
    (hdc.mono hsub1) (fun y hy => div_nonneg (by linarith [hy.1]) (by positivity))
    (by have := hq 0 ⟨by norm_num, by norm_num⟩; positivity)
  have hL := abs_integral_mul_cos_le_of_anti (by norm_num : (-1 : ℝ) ≤ 0) hk (fun y hy => hd y (hsub2 hy))
    (hdc.mono hsub2) (fun y hy => div_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) (by positivity))
    (by have := hq 0 ⟨by norm_num, by norm_num⟩; positivity)
  have hcI : ∀ a b : ℝ, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable (fun y => 1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y)) volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul _ (by fun_prop : Continuous fun y : ℝ => cos (2 * c * y)).continuousOn
    apply continuousOn_const.div₀ (by fun_prop)
    intro y hy
    have : y ∈ Icc (-1 : ℝ) 1 := by
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at hy; exact ⟨le_trans ha.1 hy.1, le_trans hy.2 hb.2⟩
      · rw [uIcc_of_ge h] at hy; exact ⟨le_trans hb.1 hy.1, le_trans hy.2 ha.2⟩
    exact (hq y this).ne'
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcI _ _ hm1 h0) (hcI _ _ h0 h1)]
  have e : 2 * (1 / (ξ ^ 2 - (-1) ^ 2)) / (2 * c) + 2 * (1 / (ξ ^ 2 - 1 ^ 2)) / (2 * c)
      = 2 / (c * (ξ ^ 2 - 1)) := by
    have : ξ ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  calc _ ≤ |∫ y in (-1 : ℝ)..0, 1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y)|
        + |∫ y in (0 : ℝ)..1, 1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y)| := abs_add_le _ _
    _ ≤ _ := add_le_add hL hR
    _ = _ := e

/-- `|∫_a^R cos(2cξ) ℓ(ξ)/ξ dξ| ≤ ℓ(a)/(ac)` for `1 < a ≤ R`: `ℓ(ξ)/ξ` decreases to `0`. -/
theorem abs_integral_ellF_cos_le {c a R : ℝ} (hc : 0 < c) (ha : 1 < a) (haR : a ≤ R) :
    |∫ ξ in a..R, ellF ξ / ξ * cos (2 * c * ξ)| ≤ ellF a / (a * c) := by
  have hξ : ∀ ξ ∈ Icc a R, 1 < ξ := fun ξ hξ => lt_of_lt_of_le ha hξ.1
  have hd : ∀ ξ ∈ Icc a R, HasDerivAt (fun ξ => ellF ξ / ξ)
      ((-(2 / pP ξ) * ξ - ellF ξ * 1) / ξ ^ 2) ξ := fun ξ hx =>
    (hasDerivAt_ellF (hξ ξ hx)).div (hasDerivAt_id ξ) (by linarith [hξ ξ hx])
  have hellc : ContinuousOn ellF (Icc a R) := fun ξ hx =>
    (hasDerivAt_ellF (hξ ξ hx)).continuousAt.continuousWithinAt
  have hpP : ∀ ξ ∈ Icc a R, 0 < pP ξ := fun ξ hx => by
    unfold pP; nlinarith [hξ ξ hx]
  have hdc : ContinuousOn (fun ξ => (-(2 / pP ξ) * ξ - ellF ξ * 1) / ξ ^ 2) (Icc a R) := by
    apply ContinuousOn.div₀ _ (by fun_prop) fun ξ hx => by have := hξ ξ hx; positivity
    apply ContinuousOn.sub _ (hellc.mul continuousOn_const)
    apply ContinuousOn.mul _ continuousOn_id
    exact (continuousOn_const.div₀ (by unfold pP; fun_prop) fun ξ hx => (hpP ξ hx).ne').neg
  have h := abs_integral_mul_cos_le_of_anti haR (by positivity : 0 < 2 * c) hd hdc
    (fun ξ hx => by
      have h1 := hξ ξ hx
      have h2 := ellF_pos h1
      have h3 := hpP ξ hx
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have : 0 ≤ 2 / pP ξ * ξ := by positivity
      linarith)
    (by have := hξ R ⟨haR, le_rfl⟩; have := ellF_pos this; positivity)
  calc _ ≤ _ := h
    _ = ellF a / (a * c) := by field_simp

/-- **The cross bound**: `|∫₁^R jK| ≤ (2 + log(2c³ + 1))/(π² c)` for `c ≥ 1`, `R ≥ 2`. Split at `a = 1 + 1/c³`:
`|jK| ≤ 2c²/π²` below `a`, and above `a` both pieces of `jK_eq` are `O(ℓ(a)/c)`. -/
theorem abs_integral_jK_le {c R : ℝ} (hc : 1 ≤ c) (hR : 2 ≤ R) :
    |∫ ξ in (1 : ℝ)..R, jK c ξ| ≤ (2 + log (2 * c ^ 3 + 1)) / (π ^ 2 * c) := by
  have hc0 : 0 < c := by linarith
  set a : ℝ := 1 + 1 / c ^ 3 with ha
  have hc3 : 1 ≤ c ^ 3 := one_le_pow₀ hc
  have ha1 : 1 < a := by rw [ha]; have : 0 < 1 / c ^ 3 := by positivity
                         linarith
  have ha2 : a ≤ 2 := by
    rw [ha]; have : 1 / c ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; exact hc3
    linarith
  have haR : a ≤ R := by linarith
  have hJc := continuous_jK c
  rw [← intervalIntegral.integral_add_adjacent_intervals (hJc.intervalIntegrable 1 a)
    (hJc.intervalIntegrable a R)]
  -- the near piece
  have hnear : |∫ ξ in (1 : ℝ)..a, jK c ξ| ≤ 2 / (π ^ 2 * c) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 : ℝ)) (b := a)
      (C := 2 * (c / π) ^ 2) (f := jK c) fun ξ _ => by rw [Real.norm_eq_abs]; exact abs_jK_le hc0 ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - 1)] at h
    calc _ ≤ _ := h
      _ = 2 / (π ^ 2 * c) := by rw [ha]; field_simp; ring
  -- the far piece
  have hpP : ∀ ξ ∈ uIcc a R, 1 < ξ := fun ξ hx => by
    rw [uIcc_of_le haR] at hx; linarith [hx.1]
  set m : ℝ → ℝ := fun ξ => ∫ y in (-1 : ℝ)..1, 1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y) with hm
  set h : ℝ → ℝ := fun ξ => ellF ξ / ξ * cos (2 * c * ξ) with hh
  have hellc : ContinuousOn ellF (uIcc a R) := fun ξ hx =>
    (hasDerivAt_ellF (hpP ξ hx)).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (uIcc a R) :=
    (hellc.div₀ continuousOn_id fun ξ hx => (show (0 : ℝ) < ξ by linarith [hpP ξ hx]).ne').mul
      (by fun_prop : Continuous fun ξ : ℝ => cos (2 * c * ξ)).continuousOn
  have hmeq : ∀ ξ ∈ uIcc a R, m ξ = 2 * π ^ 2 * jK c ξ + h ξ := by
    intro ξ hx
    rw [jK_eq hc0 (hpP ξ hx)]
    simp only [hm, hh]
    generalize (∫ y in (-1 : ℝ)..1, 1 / (ξ ^ 2 - y ^ 2) * cos (2 * c * y)) = M
    field_simp
    ring
  have hmc : ContinuousOn m (uIcc a R) :=
    ((continuousOn_const.mul hJc.continuousOn).add hhc).congr hmeq
  have hfar_eq : ∫ ξ in a..R, jK c ξ = ((∫ ξ in a..R, m ξ) - ∫ ξ in a..R, h ξ) / (2 * π ^ 2) := by
    rw [← intervalIntegral.integral_sub hmc.intervalIntegrable hhc.intervalIntegrable,
      ← intervalIntegral.integral_div]
    refine integral_congr fun ξ hx => ?_
    rw [hmeq ξ hx]
    field_simp
    ring
  have hmI : |∫ ξ in a..R, m ξ| ≤ ellF a / c := by
    calc |∫ ξ in a..R, m ξ| ≤ ∫ ξ in a..R, |m ξ| := abs_integral_le_integral_abs haR
      _ ≤ ∫ ξ in a..R, 2 / c * (1 / pP ξ) := by
          apply integral_mono_on haR hmc.abs.intervalIntegrable
          · have hpc : ContinuousOn pP (uIcc a R) := by unfold pP; fun_prop
            have hp0 : ∀ ξ ∈ uIcc a R, pP ξ ≠ 0 := fun ξ hx => by unfold pP; nlinarith [hpP ξ hx]
            exact (continuousOn_const.mul (continuousOn_const.div₀ hpc hp0)).intervalIntegrable
          · intro ξ hx
            have hx' : ξ ∈ uIcc a R := by rw [uIcc_of_le haR]; exact hx
            have := abs_integral_inv_sub_sq_cos_le hc0 (hpP ξ hx')
            calc |m ξ| ≤ 2 / (c * (ξ ^ 2 - 1)) := this
              _ = 2 / c * (1 / pP ξ) := by unfold pP; field_simp
      _ = 2 / c * ((ellF a - ellF R) / 2) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_pP ha1 haR]
      _ ≤ ellF a / c := by
          have := ellF_pos (show 1 < R by linarith)
          have : 2 / c * ((ellF a - ellF R) / 2) = (ellF a - ellF R) / c := by field_simp
          rw [this]
          exact div_le_div_of_nonneg_right (by linarith) hc0.le
  have hhI : |∫ ξ in a..R, h ξ| ≤ ellF a / c := by
    have h1 := abs_integral_ellF_cos_le hc0 ha1 haR
    have h2 : ellF a / (a * c) ≤ ellF a / c := by
      have := ellF_pos ha1
      apply div_le_div_of_nonneg_left this.le hc0
      nlinarith
    exact h1.trans h2
  have hfar : |∫ ξ in a..R, jK c ξ| ≤ ellF a / (π ^ 2 * c) := by
    rw [hfar_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π ^ 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := abs_sub (∫ ξ in a..R, m ξ) (∫ ξ in a..R, h ξ)
    have hπ : 0 < π ^ 2 * c := by positivity
    have : (|∫ ξ in a..R, m ξ| + |∫ ξ in a..R, h ξ|) * (π ^ 2 * c) ≤ ellF a * (2 * π ^ 2) := by
      have e : ellF a * (2 * π ^ 2) = (ellF a / c + ellF a / c) * (π ^ 2 * c) := by field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (add_le_add hmI hhI) hπ.le
    nlinarith
  have hell : ellF a = log (2 * c ^ 3 + 1) := by
    unfold ellF
    congr 1
    rw [ha]
    field_simp
    ring
  rw [hell] at hfar
  calc _ ≤ |∫ ξ in (1 : ℝ)..a, jK c ξ| + |∫ ξ in a..R, jK c ξ| := abs_add_le _ _
    _ ≤ 2 / (π ^ 2 * c) + log (2 * c ^ 3 + 1) / (π ^ 2 * c) := add_le_add hnear hfar
    _ = _ := by ring

/-! ### The even Bessel bound -/

/-- `psi c g` is continuous for `g` continuous on `[−1, 1]`. -/
theorem continuous_psi {c : ℝ} {g : ℝ → ℝ} (hgc : ContinuousOn g (Icc (-1) 1)) : Continuous (psi c g) := by
  have hgu : ContinuousOn g (uIcc (-1) 1) := by rwa [uIcc_of_le (by norm_num)]
  refine continuous_iff_continuousAt.2 fun ξ => ?_
  have h := hasDerivAt_kint (g := g) (k := fun ξ s => cos (c * ξ * s))
    (k' := fun ξ s => -(c * s * sin (c * ξ * s))) (C := |c|) hgu (fun s => by fun_prop)
    (fun ξ => by fun_prop) (fun ξ => by fun_prop)
    (fun ξ s => by
      have h1 : HasDerivAt (fun ξ => c * ξ * s) (c * s) ξ := by
        simpa using ((hasDerivAt_id ξ).const_mul c).mul_const s
      refine h1.cos.congr_deriv ?_
      ring)
    (fun ξ s hs => by
      rw [abs_neg, abs_mul, abs_mul]
      calc |c| * |s| * |sin (c * ξ * s)| ≤ |c| * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg c)) (abs_sin_le_one _) (abs_nonneg _)
              (by positivity)
        _ = |c| := by ring) ξ
  exact h.continuousAt

theorem continuous_kE (c ξ : ℝ) : Continuous (kE c ξ) := by
  unfold kE; have := continuous_kS c; fun_prop

/-- `∫_{−1}^{1} kE(ξ, y)² dy = (aK(ξ) + jK(ξ))/2`. -/
theorem integral_kE_sq (c ξ : ℝ) : ∫ y in (-1 : ℝ)..1, kE c ξ y ^ 2 = (aK c ξ + jK c ξ) / 2 := by
  have hK := continuous_kS c
  have hneg : ∫ y in (-1 : ℝ)..1, kS c (ξ + y) ^ 2 = aK c ξ := by
    have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) (fun y => kS c (ξ - y) ^ 2)
    simp only [sub_neg_eq_add, neg_neg] at h
    rw [h]; rfl
  have e : ∀ y, kE c ξ y ^ 2
      = (kS c (ξ - y) ^ 2 + kS c (ξ + y) ^ 2 + 2 * (kS c (ξ - y) * kS c (ξ + y))) / 4 := by
    intro y; unfold kE; ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun y => kS c (ξ - y) ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable (fun y => kS c (ξ + y) ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have i3 : IntervalIntegrable (fun y => 2 * (kS c (ξ - y) * kS c (ξ + y))) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (i1.add i2) i3,
    intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul, hneg]
  unfold aK jK
  ring

/-- The closed-form plunge bound `(Cin(4c)/2 + 1/2 + 1/(4c) + (2 + log(2c³ + 1))/c)/π²`. -/
def plungeBound (c : ℝ) : ℝ :=
  (Cin (4 * c) / 2 + 1 / 2 + 1 / (4 * c) + (2 + log (2 * c ^ 3 + 1)) / c) / π ^ 2

/-- **The even Bessel bound** (no completeness): for even `gᵢ` orthonormal on `[−1, 1]` with `psi c gᵢ = μᵢ gᵢ`,
`Σ λᵢ(1 − λᵢ) ≤ plungeBound c`, `λᵢ = (μᵢ√(c/2π))²`, `c ≥ 1`. -/
theorem sum_plunge_le {ι : Type*} [DecidableEq ι] (S : Finset ι) {g : ι → ℝ → ℝ} {c : ℝ} {μ : ι → ℝ}
    (hc : 1 ≤ c) (hgc : ∀ i ∈ S, ContinuousOn (g i) (Icc (-1) 1))
    (heven : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s)
    (horth : ∀ i ∈ S, ∀ j ∈ S, ∫ s in (-1 : ℝ)..1, g i s * g j s = if i = j then 1 else 0) :
    ∑ i ∈ S, (μ i * √(c / (2 * π))) ^ 2 * (1 - (μ i * √(c / (2 * π))) ^ 2) ≤ plungeBound c := by
  have hc0 : 0 < c := by linarith
  have hgu : ∀ i ∈ S, ContinuousOn (g i) (uIcc (-1) 1) := fun i hi => by
    rw [uIcc_of_le (by norm_num)]; exact hgc i hi
  -- pointwise Bessel
  have hpt : ∀ ξ, ∑ i ∈ S, (c / (2 * π) * μ i) ^ 2 * psi c (g i) ξ ^ 2 ≤ (aK c ξ + jK c ξ) / 2 := by
    intro ξ
    have hB := Cvs.Prolate.AngularBesselInequality.sum_sq_integral_le S g (f := kE c ξ) (continuous_kE c ξ).continuousOn
      hgu horth
    rw [integral_kE_sq] at hB
    have e : ∀ i ∈ S, (∫ s in (-1 : ℝ)..1, kE c ξ s * g i s) ^ 2
        = (c / (2 * π) * μ i) ^ 2 * psi c (g i) ξ ^ 2 := fun i hi => by
      rw [integral_kE_mul hc0 (hgc i hi) (hμ i hi)]; ring
    rwa [Finset.sum_congr rfl e] at hB
  have hψc : ∀ i ∈ S, Continuous (psi c (g i)) := fun i hi => continuous_psi (hgc i hi)
  -- integrated over `[1, R]`
  have hR : ∀ R, 2 ≤ R →
      ∑ i ∈ S, (c / (2 * π) * μ i) ^ 2 * ∫ ξ in (1 : ℝ)..R, psi c (g i) ξ ^ 2 ≤ plungeBound c / 2 := by
    intro R hR2
    have hR1 : (1 : ℝ) ≤ R := by linarith
    have hL : ∑ i ∈ S, (c / (2 * π) * μ i) ^ 2 * ∫ ξ in (1 : ℝ)..R, psi c (g i) ξ ^ 2
        = ∫ ξ in (1 : ℝ)..R, ∑ i ∈ S, (c / (2 * π) * μ i) ^ 2 * psi c (g i) ξ ^ 2 := by
      rw [intervalIntegral.integral_finsetSum (f := fun i ξ => (c / (2 * π) * μ i) ^ 2 * psi c (g i) ξ ^ 2)
        fun i hi => (continuous_const.mul ((hψc i hi).pow 2)).intervalIntegrable _ _]
      exact Finset.sum_congr rfl fun i _ => (intervalIntegral.integral_const_mul _ _).symm
    rw [hL]
    have hm : ∫ ξ in (1 : ℝ)..R, ∑ i ∈ S, (c / (2 * π) * μ i) ^ 2 * psi c (g i) ξ ^ 2
        ≤ ∫ ξ in (1 : ℝ)..R, (aK c ξ + jK c ξ) / 2 := by
      apply integral_mono_on hR1
      · exact (continuous_finsetSum _ fun i hi => continuous_const.mul ((hψc i hi).pow 2)).intervalIntegrable _ _
      · exact (((continuous_aK c).add (continuous_jK c)).div_const 2).intervalIntegrable _ _
      · exact fun ξ _ => hpt ξ
    refine hm.trans ?_
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add ((continuous_aK c).intervalIntegrable _ _)
      ((continuous_jK c).intervalIntegrable _ _)]
    have hA := integral_aK_le hc0 hR1
    have hJ := le_abs_self (∫ ξ in (1 : ℝ)..R, jK c ξ)
    have hJ' := abs_integral_jK_le hc hR2
    have e : Cin (4 * c) / (2 * π ^ 2) + (1 / 2 + 1 / (4 * c)) / π ^ 2 + (2 + log (2 * c ^ 3 + 1)) / (π ^ 2 * c)
        = plungeBound c := by
      unfold plungeBound; field_simp; ring
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith
  -- the limit `R → ∞`
  have hInt : ∀ i ∈ S, IntegrableOn (fun ξ => psi c (g i) ξ ^ 2) (Ioi 1) := by
    intro i hi
    have hm := Cvs.Prolate.RungMirrorIdentity.memLp_psi hc0 (hgc i hi) (heven i hi)
    have h0 : IntegrableOn (fun x => psi c (g i) x ^ 2) (Ioi 0) := by
      have := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact h0.mono_set (Ioi_subset_Ioi zero_le_one)
  have hT : Tendsto (fun R => ∑ i ∈ S, (c / (2 * π) * μ i) ^ 2 * ∫ ξ in (1 : ℝ)..R, psi c (g i) ξ ^ 2) atTop
      (𝓝 (∑ i ∈ S, (c / (2 * π) * μ i) ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2)) :=
    tendsto_finsetSum S fun i hi =>
      (intervalIntegral_tendsto_integral_Ioi 1 (hInt i hi) tendsto_id).const_mul _
  have hlim := le_of_tendsto hT (eventually_atTop.2 ⟨2, hR⟩)
  have hnorm : ∀ i ∈ S, ∫ s in (-1 : ℝ)..1, g i s ^ 2 = 1 := fun i hi => by
    have := horth i hi i hi; simp only [ite_true] at this; simpa only [sq] using this
  have e : ∀ i ∈ S, (c / (2 * π) * μ i) ^ 2 * ∫ ξ in Ioi 1, psi c (g i) ξ ^ 2
      = (μ i * √(c / (2 * π))) ^ 2 * (1 - (μ i * √(c / (2 * π))) ^ 2) / 2 := by
    intro i hi
    rw [Cvs.Prolate.AngularBesselInequality.mass_eq hc0 (hgc i hi) (heven i hi) (hμ i hi) (hnorm i hi)]
    have hs : (μ i * √(c / (2 * π))) ^ 2 = μ i ^ 2 * (c / (2 * π)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hs]
    field_simp
  rw [Finset.sum_congr rfl e, ← Finset.sum_div] at hlim
  linarith

/-- **The even Bessel bound for angular solutions**: normalised even angular solutions at distinct levels with
`psi c gᵢ = μᵢ gᵢ` satisfy `Σ λᵢ(1 − λᵢ) ≤ plungeBound c` for `c ≥ 1`. -/
theorem sum_plunge_le_angular {ι : Type*} [DecidableEq ι] (S : Finset ι) {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ}
    {χ μ : ι → ℝ} (hc : 1 ≤ c)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ : Set.InjOn χ S) (hnorm : ∀ i ∈ S, ∫ s in (-1 : ℝ)..1, g i s ^ 2 = 1)
    (heven : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, g i (-s) = g i s)
    (hμ : ∀ i ∈ S, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (g i) s = μ i * g i s) :
    ∑ i ∈ S, (μ i * √(c / (2 * π))) ^ 2 * (1 - (μ i * √(c / (2 * π))) ^ 2) ≤ plungeBound c :=
  sum_plunge_le S hc (fun i _ => Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt (hg i)) heven hμ
    (Cvs.Prolate.AngularBesselInequality.orthonormal_of_angular S hg hg₁ hang hχ hnorm)

/-- **The plunge bound in elementary terms**: `plungeBound c ≤ (log(2c)/2 + 3/2 + 1/(4c) + (2 + log(2c³ + 1))/c)/π²`
for `c ≥ 1`, from `Cin z ≤ log z − log 2 + 2`. -/
theorem plungeBound_le {c : ℝ} (hc : 1 ≤ c) :
    plungeBound c ≤ (log (2 * c) / 2 + 3 / 2 + 1 / (4 * c) + (2 + log (2 * c ^ 3 + 1)) / c) / π ^ 2 := by
  have hC := Cin_le (show (2 : ℝ) ≤ 4 * c by linarith)
  have hl : log (4 * c) - log 2 = log (2 * c) := by
    rw [← log_div (by positivity) (by norm_num)]; congr 1; ring
  unfold plungeBound
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-! ### From `λ(1 − λ)` to the deficit `1 − λ` -/

/-- **Paired deficit**: for `1/2 ≤ λ' ≤ λ ≤ 1`, `1 − λ ≤ λ(1 − λ) + λ'(1 − λ')`. -/
theorem one_sub_le_pair {l l' : ℝ} (hl1 : l ≤ 1) (hhalf : 1 / 2 ≤ l') (hle : l' ≤ l) :
    1 - l ≤ l * (1 - l) + l' * (1 - l') := by
  have h1 : 0 ≤ 1 - l := by linarith
  have h2 : 1 - l ≤ l' := by linarith
  have h3 : 1 - l ≤ 1 - l' := by linarith
  nlinarith [mul_le_mul h2 h3 h1 (by linarith : (0 : ℝ) ≤ l')]

end Cvs.Prolate.PlungeMassTrace
