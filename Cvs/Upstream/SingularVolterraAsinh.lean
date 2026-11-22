import Mathlib
import Cvs.Upstream.SecondOrderOdeEnergyBounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Singular Volterra bounds, the `asinh` integral and the phase defect

A solution of `e(x) = ∫₀ˣ K(x, v)p(v)(F(v) + e(v))dv` with `|K(x, v)| ≤ P(x)R(v)` has `|e(x)| ≤ P(x)Φ(x)e^{Λ(x)}`,
`Φ = ∫₀ˣ R|pF|`, `Λ = ∫₀ˣ R|p|P`; the backward form gives `|h| ≤ e^{∫w} − 1`; `∫₀ˣ (1 + v²)^{−1/2} = asinh x`
bounds `Λ` for the Coulomb potential; and `√(¼ + κ/v + 1/(4v²)) − √(¼ + κ/v) ≤ 1/(4v²)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace Cvs.Upstream.SingularVolterraAsinh

/-! ### Primitives -/

/-- The primitive `u ↦ ∫ₐᵘ f` is differentiable at interior continuity points. -/
theorem hasDerivAt_primitive {f : ℝ → ℝ} {a b x : ℝ} (hf : IntervalIntegrable f volume a b)
    (hc : ContinuousOn f (Ioo a b)) (hx : x ∈ Ioo a b) : HasDerivAt (fun u => ∫ v in a..u, f v) (f x) x :=
  integral_hasDerivAt_right (hf.mono_set (by
      rw [uIcc_of_le hx.1.le, uIcc_of_le (hx.1.trans hx.2).le]
      exact Icc_subset_Icc le_rfl hx.2.le))
    (hc.stronglyMeasurableAtFilter isOpen_Ioo x hx) (hc.continuousAt (Ioo_mem_nhds hx.1 hx.2))

/-- The primitive is continuous on `[a, b]`. -/
theorem continuousOn_primitive' {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    ContinuousOn (fun u => ∫ v in a..u, f v) (Icc a b) := by
  rw [← uIcc_of_le hab]
  exact continuousOn_primitive_interval' hf left_mem_uIcc

/-! ### Forward Volterra (Lemma V′) -/

/-- **Volterra–Gronwall**: if `|e| ≤ P(Φ + U)` on `(0, X)` with `U = ∫₀ R|p||e|`, `Φ = ∫₀ R|p||F|`, `R, P ≥ 0`, then
`Φ(X) + U(X) ≤ Φ(X)e^{Λ(X)}`, `Λ = ∫₀ R|p|P`. -/
theorem volterra_sum_le {F e p P R : ℝ → ℝ} {X : ℝ} (hX : 0 ≤ X)
    (hR : ∀ v ∈ Icc 0 X, 0 ≤ R v) (hP : ∀ v ∈ Ioo 0 X, 0 ≤ P v)
    (hiF : IntervalIntegrable (fun v => R v * |p v| * |F v|) volume 0 X)
    (hie : IntervalIntegrable (fun v => R v * |p v| * |e v|) volume 0 X)
    (hiP : IntervalIntegrable (fun v => R v * |p v| * P v) volume 0 X)
    (hce : ContinuousOn (fun v => R v * |p v| * |e v|) (Ioo 0 X))
    (hcP : ContinuousOn (fun v => R v * |p v| * P v) (Ioo 0 X))
    (hb : ∀ x ∈ Ioo 0 X, |e x| ≤ P x * ((∫ v in (0 : ℝ)..x, R v * |p v| * |F v|) +
      ∫ v in (0 : ℝ)..x, R v * |p v| * |e v|)) :
    (∫ v in (0 : ℝ)..X, R v * |p v| * |F v|) + (∫ v in (0 : ℝ)..X, R v * |p v| * |e v|) ≤
      (∫ v in (0 : ℝ)..X, R v * |p v| * |F v|) * exp (∫ v in (0 : ℝ)..X, R v * |p v| * P v) := by
  set fF : ℝ → ℝ := fun v => R v * |p v| * |F v|
  set fe : ℝ → ℝ := fun v => R v * |p v| * |e v|
  set fP : ℝ → ℝ := fun v => R v * |p v| * P v
  have hFnn : 0 ≤ᵐ[volume.restrict (Ioc 0 X)] fF :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun v hv =>
      mul_nonneg (mul_nonneg (hR v (Ioc_subset_Icc_self hv)) (abs_nonneg _)) (abs_nonneg _))
  have hΦ : ∀ x ∈ Ioo 0 X, (∫ v in (0 : ℝ)..x, fF v) ≤ ∫ v in (0 : ℝ)..X, fF v := fun x hx =>
    integral_mono_interval le_rfl hx.1.le hx.2.le hFnn hiF
  have h := Cvs.Upstream.SecondOrderOdeEnergyBounds.le_mul_exp_of_deriv_le (F := fun u => (∫ v in (0 : ℝ)..X, fF v) +
      ∫ v in (0 : ℝ)..u, fe v) (F₁ := fe) (τ := fun u => ∫ v in (0 : ℝ)..u, fP v) (τ₁ := fP) hX
    (continuousOn_const.add (continuousOn_primitive' hX hie)) (continuousOn_primitive' hX hiP)
    (fun x hx => (hasDerivAt_primitive hie hce hx).const_add _) (fun x hx => hasDerivAt_primitive hiP hcP hx)
    (fun x hx => by
      have hRx : 0 ≤ R x * |p x| := mul_nonneg (hR x ⟨hx.1.le, hx.2.le⟩) (abs_nonneg _)
      have h1 := mul_le_mul_of_nonneg_left (hb x hx) hRx
      have h2 := hΦ x hx
      have h3 : R x * |p x| * P x * ((∫ v in (0 : ℝ)..x, fF v) + ∫ v in (0 : ℝ)..x, fe v) ≤
          R x * |p x| * P x * ((∫ v in (0 : ℝ)..X, fF v) + ∫ v in (0 : ℝ)..x, fe v) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hRx (hP x hx))
      calc fe x = R x * |p x| * |e x| := rfl
        _ ≤ R x * |p x| * (P x * ((∫ v in (0 : ℝ)..x, fF v) + ∫ v in (0 : ℝ)..x, fe v)) := h1
        _ = R x * |p x| * P x * ((∫ v in (0 : ℝ)..x, fF v) + ∫ v in (0 : ℝ)..x, fe v) := by ring
        _ ≤ _ := h3)
  simpa using h

/-- **Lemma V′ (a priori form)**: a solution of `e(x) = ∫₀ˣ K(x, v)p(v)(F(v) + e(v))dv` with
`|K(x, v)| ≤ P(x)R(v)` satisfies `|e| ≤ P(Φ + U)`, `Φ = ∫₀ R|pF|`, `U = ∫₀ R|pe|`. -/
theorem abs_le_of_volterra_eq {F e p P R : ℝ → ℝ} {K : ℝ → ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hK : ∀ v ∈ Ioc 0 x, |K x v| ≤ P x * R v)
    (hiF : IntervalIntegrable (fun v => R v * |p v| * |F v|) volume 0 x)
    (hie : IntervalIntegrable (fun v => R v * |p v| * |e v|) volume 0 x)
    (heq : e x = ∫ v in (0 : ℝ)..x, K x v * p v * (F v + e v)) :
    |e x| ≤ P x * ((∫ v in (0 : ℝ)..x, R v * |p v| * |F v|) + ∫ v in (0 : ℝ)..x, R v * |p v| * |e v|) := by
  rw [heq, ← integral_add hiF hie, ← intervalIntegral.integral_const_mul]
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hx (Eventually.of_forall fun v hv => ?_)
    ((hiF.add hie).const_mul (P x))
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 : |F v + e v| ≤ |F v| + |e v| := abs_add_le _ _
  calc |K x v| * |p v| * |F v + e v| ≤ P x * R v * |p v| * (|F v| + |e v|) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hK v hv) (abs_nonneg _)) h1 (abs_nonneg _)
          (mul_nonneg (le_trans (abs_nonneg _) (hK v hv)) (abs_nonneg _))
    _ = P x * (R v * |p v| * |F v| + R v * |p v| * |e v|) := by ring

/-! ### Backward Volterra (the Liouville–Green error) -/

/-! ### The `asinh` integral -/

/-- `v ↦ (1 + v²)^{−1/2}` is continuous. -/
theorem continuous_inv_sqrt_one_add_sq : Continuous fun v : ℝ => (√(1 + v ^ 2))⁻¹ :=
  Continuous.inv₀ (by fun_prop) fun v => (sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + v ^ 2)).ne'

/-- `∫₀ˣ (1 + v²)^{−1/2} dv = asinh x`. -/
theorem integral_inv_sqrt_one_add_sq (x : ℝ) : ∫ v in (0 : ℝ)..x, (√(1 + v ^ 2))⁻¹ = arsinh x := by
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_arsinh v), arsinh_zero, sub_zero]
  exact (continuous_inv_sqrt_one_add_sq.continuousOn).intervalIntegrable

/-- **The Coulomb weight**: for `κ ≥ 0`, `v > 0`, `Q = ¼ + κ/v + 1/(4v²)` has `Q^{−1/2} ≤ 2v/√(1 + v²)`. -/
theorem inv_sqrt_coulombQ_le {κ v : ℝ} (hκ : 0 ≤ κ) (hv : 0 < v) :
    (√(1 / 4 + κ / v + 1 / (4 * v ^ 2)))⁻¹ ≤ 2 * v / √(1 + v ^ 2) := by
  have h1 : (1 + v ^ 2) / (4 * v ^ 2) ≤ 1 / 4 + κ / v + 1 / (4 * v ^ 2) := by
    have : 0 ≤ κ / v := div_nonneg hκ hv.le
    rw [show (1 + v ^ 2) / (4 * v ^ 2) = 1 / 4 + 1 / (4 * v ^ 2) by field_simp; ring]
    linarith
  have hpos : 0 < (1 + v ^ 2) / (4 * v ^ 2) := by positivity
  have h2 : √((1 + v ^ 2) / (4 * v ^ 2)) = √(1 + v ^ 2) / (2 * v) := by
    rw [sqrt_div (by positivity), show (4 : ℝ) * v ^ 2 = (2 * v) ^ 2 by ring, sqrt_sq (by positivity)]
  calc (√(1 / 4 + κ / v + 1 / (4 * v ^ 2)))⁻¹ ≤ (√((1 + v ^ 2) / (4 * v ^ 2)))⁻¹ :=
        inv_anti₀ (sqrt_pos.mpr hpos) (sqrt_le_sqrt h1)
    _ = 2 * v / √(1 + v ^ 2) := by rw [h2, inv_div]

/-- **The exponent `Λ`**: if `g(v) ≤ C(1 + v²)^{−1/2}` on `(0, x)`, then `∫₀ˣ g ≤ C asinh x`. -/
theorem integral_le_mul_arsinh {g : ℝ → ℝ} {C x : ℝ} (hx : 0 ≤ x) (hg : IntervalIntegrable g volume 0 x)
    (hle : ∀ v ∈ Ioo 0 x, g v ≤ C * (√(1 + v ^ 2))⁻¹) : ∫ v in (0 : ℝ)..x, g v ≤ C * arsinh x := by
  rw [← integral_inv_sqrt_one_add_sq, ← intervalIntegral.integral_const_mul]
  refine integral_mono_on_of_le_Ioo hx hg ?_ hle
  exact ((continuous_const.mul continuous_inv_sqrt_one_add_sq).continuousOn).intervalIntegrable

/-- **The `Λ` integrand**: with `|p(v)| ≤ Ψ/(2cv)` and `Q = ¼ + κ/v + 1/(4v²)`, `κ ≥ 0`,
`Q^{−1/2}|p| ≤ (Ψ/c)(1 + v²)^{−1/2}`. -/
theorem inv_sqrt_coulombQ_mul_le {κ v Ψ c pv : ℝ} (hκ : 0 ≤ κ) (hv : 0 < v) (hc : 0 < c)
    (hp : |pv| ≤ Ψ / (2 * c * v)) :
    (√(1 / 4 + κ / v + 1 / (4 * v ^ 2)))⁻¹ * |pv| ≤ Ψ / c * (√(1 + v ^ 2))⁻¹ := by
  have h1 := inv_sqrt_coulombQ_le hκ hv
  have hs : 0 < √(1 + v ^ 2) := sqrt_pos.mpr (by positivity)
  calc (√(1 / 4 + κ / v + 1 / (4 * v ^ 2)))⁻¹ * |pv| ≤ 2 * v / √(1 + v ^ 2) * (Ψ / (2 * c * v)) :=
        mul_le_mul h1 hp (abs_nonneg _) (by positivity)
    _ = Ψ / c * (√(1 + v ^ 2))⁻¹ := by field_simp

/-! ### The phase defect -/

end Cvs.Upstream.SingularVolterraAsinh
