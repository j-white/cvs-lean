import Mathlib
import Cvs.Route.Visibility.ProjectionShareSawtooth
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Mellin transform of the reflected remainder

By first-order Euler–Maclaurin `θ r_G(θ) = −a T(θ/a)` with `T(y) = ∫₀¹ G′(t)S(yt) dt`. For `Ψ′ = −T` with
`T, Ψ ∈ L²(x, ∞)`, `a = 1/x`: `∫_1^∞ θ^{−ρ} r_G = −a x^ρ[x^{−ρ−1}Ψ(x) − (ρ + 1)∫_x^∞ y^{−ρ−2}Ψ]`, `Ψ(x)² ≤ 2‖Ψ‖‖T‖`,
and the reflected half of Cvs.Route.Visibility.ProjectionShareSawtooth holds with `‖Ψ‖₂, ‖T‖₂` in place of `‖θ r_G‖₂`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open Cvs.Xi.EImageWindowPoisson (eimage window)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Route.Visibility.ProjectionShareSawtooth (saw reflRem)

namespace Cvs.Route.Visibility.ReflectedRemainderMellin

/-- The first-order Euler–Maclaurin remainder `T(y) = ∫₀¹ G′(t) S(yt) dt`. -/
def sawT (G₁ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, G₁ t * saw (y * t)

section EulerMaclaurin

variable {G G₁ : ℝ → ℝ}

/-- `G′(t)S(yt)` is interval integrable on `[0, 1]`. -/
theorem intervalIntegrable_mul_saw (hG₁ : ContinuousOn G₁ (Icc 0 1)) (y : ℝ) :
    IntervalIntegrable (fun u => G₁ u * saw (y * u)) volume 0 1 := by
  have hc : IntervalIntegrable G₁ volume 0 1 := hG₁.intervalIntegrable_of_Icc zero_le_one
  refine (hc.norm.mul_const (1 / 2)).mono_fun' ?_ ?_
  · exact hc.def'.aestronglyMeasurable.mul
      (Cvs.Route.Visibility.ProjectionShareSawtooth.measurable_saw.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  · filter_upwards with u
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Cvs.Route.Visibility.ProjectionShareSawtooth.abs_saw_le _) (abs_nonneg _)

variable (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
include hG hG₁

/-- **First-order Euler–Maclaurin**: for `y > 0`,
`Σ_{1 ≤ n ≤ y} G(n/y) = y∫₀¹G + G(1)S(y) − G(0)/2 − T(y)`. -/
theorem sum_eq_saw_sub_sawT {y : ℝ} (hy : 0 < y) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, G (n / y)
      = y * (∫ u in (0 : ℝ)..1, G u) + G 1 * saw y - G 0 / 2 - sawT G₁ y := by
  set f : ℝ → ℝ := fun t => G (t / y)
  have hfd : ∀ t ∈ Icc (0 : ℝ) y, HasDerivAt f (G₁ (t / y) / y) t := by
    intro t ht
    have hu : t / y ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1 hy.le, (div_le_one hy).2 ht.2⟩
    have := (hG _ hu).comp t ((hasDerivAt_id t).div_const y)
    simp only [Function.comp_def] at this
    simpa [f, div_eq_mul_inv, mul_comm] using this
  have hderiv : ∀ t ∈ Icc (0 : ℝ) y, deriv f t = G₁ (t / y) / y := fun t ht => (hfd t ht).deriv
  have hcont : ContinuousOn (fun t => G₁ (t / y) / y) (Icc 0 y) := by
    refine (hG₁.comp (continuous_id.div_const y).continuousOn fun t ht => ?_).div_const y
    exact ⟨div_nonneg ht.1 hy.le, (div_le_one hy).2 ht.2⟩
  have hint : IntegrableOn (deriv f) (Icc 0 y) :=
    (hcont.integrableOn_Icc).congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_integral_mul (c := fun _ => (1 : ℝ)) hy.le
    (fun t ht => (hfd t ht).differentiableAt) hint
  simp only [mul_one, Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul, mul_one] at habel
  have hG₁i : IntervalIntegrable G₁ volume 0 1 := hG₁.intervalIntegrable_of_Icc zero_le_one
  have hI : ∫ t in Ioc 0 y, deriv f t * (((⌊t⌋₊ + 1 : ℕ) : ℝ))
      = ∫ u in (0 : ℝ)..1, G₁ u * (y * u + 1 / 2 + saw (y * u)) := by
    rw [← intervalIntegral.integral_of_le hy.le]
    have e : ∀ t ∈ uIcc (0 : ℝ) y, deriv f t * (((⌊t⌋₊ + 1 : ℕ) : ℝ))
        = 1 / y * (fun u => G₁ u * (y * u + 1 / 2 + saw (y * u))) (t / y) := by
      intro t ht
      rw [uIcc_of_le hy.le] at ht
      have hyt : y * (t / y) = t := by field_simp
      dsimp only
      rw [hderiv t ht, hyt, Nat.cast_add, Nat.cast_one,
        natCast_floor_eq_intCast_floor ht.1, saw, ← Int.self_sub_fract]
      ring
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_div (fun u => G₁ u * (y * u + 1 / 2 + saw (y * u))) hy.ne', zero_div,
      div_self hy.ne', smul_eq_mul, ← mul_assoc, one_div_mul_cancel hy.ne', one_mul]
  have hsaw := intervalIntegrable_mul_saw hG₁ y
  have hlin : IntervalIntegrable (fun u => G₁ u * (y * u)) volume 0 1 :=
    hG₁i.mul_continuousOn (continuous_const.mul continuous_id).continuousOn
  have hsplit : ∫ u in (0 : ℝ)..1, G₁ u * (y * u + 1 / 2 + saw (y * u))
      = y * (∫ u in (0 : ℝ)..1, u * G₁ u) + (∫ u in (0 : ℝ)..1, G₁ u) / 2 + sawT G₁ y := by
    have hm : ∫ u in (0 : ℝ)..1, G₁ u * (y * u) = y * ∫ u in (0 : ℝ)..1, u * G₁ u := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun u _ => by ring
    calc ∫ u in (0 : ℝ)..1, G₁ u * (y * u + 1 / 2 + saw (y * u))
        = ∫ u in (0 : ℝ)..1, ((G₁ u * (y * u) + G₁ u / 2) + G₁ u * saw (y * u)) :=
          intervalIntegral.integral_congr fun u _ => by ring
      _ = (∫ u in (0 : ℝ)..1, G₁ u * (y * u)) + (∫ u in (0 : ℝ)..1, G₁ u / 2)
            + ∫ u in (0 : ℝ)..1, G₁ u * saw (y * u) := by
          rw [intervalIntegral.integral_add (hlin.add (hG₁i.div_const 2)) hsaw,
            intervalIntegral.integral_add hlin (hG₁i.div_const 2)]
      _ = _ := by rw [hm, intervalIntegral.integral_div, sawT]
  have hGc : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt G (G₁ u) u := by
    intro u hu; rw [uIcc_of_le zero_le_one] at hu; exact hG u hu
  have hmom : ∫ u in (0 : ℝ)..1, u * G₁ u = G 1 - ∫ u in (0 : ℝ)..1, G u := by
    have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := id) (u' := fun _ => (1 : ℝ))
      (fun u _ => hasDerivAt_id u) hGc intervalIntegrable_const hG₁i
    simpa using this
  have hftc : ∫ u in (0 : ℝ)..1, G₁ u = G 1 - G 0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hGc hG₁i
  rw [hI, hsplit, hmom, hftc] at habel
  have h0 : ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, f k = f 0 + ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, G (n / y) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, Nat.cast_zero]
    rfl
  rw [h0] at habel
  have hfy : f y = G 1 := by simp [f, div_self hy.ne']
  have hf0 : f 0 = G 0 := by simp [f]
  rw [hfy, hf0] at habel
  have hfl : ((⌊y⌋₊ : ℕ) : ℝ) = y - Int.fract y := by
    rw [natCast_floor_eq_intCast_floor hy.le, ← Int.self_sub_fract]
  rw [saw]
  push_cast at habel
  rw [hfl] at habel
  linarith

/-- **The reflected remainder is the Euler–Maclaurin remainder**: for `a, θ > 0` and `∫₀¹ G = 0`,
`θ r_G(θ) = −a T(θ/a)`. -/
theorem mul_reflRem_eq (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) :
    θ * reflRem a G θ = -a * sawT G₁ (θ / a) := by
  have hy : 0 < θ / a := div_pos hθ ha
  have hs := sum_eq_saw_sub_sawT hG hG₁ hy
  rw [hGi, mul_zero, zero_add] at hs
  have he : eimage a G θ = a / θ * ∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n / (θ / a)) := by
    unfold eimage
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [div_div_eq_mul_div]
  rw [reflRem, he, hs]
  field_simp
  ring

end EulerMaclaurin

/-! ### Square-integrable antiderivatives on a half-line -/

section HalfLine

variable {x : ℝ} {T Ψ : ℝ → ℝ}

variable (hΨ : ∀ y ∈ Ici x, HasDerivAt Ψ (-T y) y) (hT2 : IntegrableOn (fun y => T y ^ 2) (Ioi x))
  (hΨ2 : IntegrableOn (fun y => Ψ y ^ 2) (Ioi x))
include hΨ hT2 hΨ2

end HalfLine

/-! ### Power weights against square-integrable functions -/

section PowerWeight

variable {x : ℝ} {q : ℂ} {f : ℝ → ℝ}

variable (hx : 0 < x) (hq : 2 * q.re < -1) (hfm : AEStronglyMeasurable f (volume.restrict (Ioi x)))
  (hf2 : IntegrableOn (fun y => f y ^ 2) (Ioi x))
include hx hq hfm hf2

end PowerWeight

/-! ### The Mellin transform of the remainder by parts -/

section Mellin

variable {x : ℝ} {T Ψ : ℝ → ℝ} (hx : 0 < x) (hΨ : ∀ y ∈ Ici x, HasDerivAt Ψ (-T y) y)
  (hT2 : IntegrableOn (fun y => T y ^ 2) (Ioi x)) (hΨ2 : IntegrableOn (fun y => Ψ y ^ 2) (Ioi x))
include hx hΨ hT2 hΨ2

end Mellin

/-! ### The reflected remainder -/

section Reflected

variable {x : ℝ} {G G₁ Ψ : ℝ → ℝ} (hx : 0 < x) (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
  (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
include hx hG hG₁ hGi

variable (hΨ : ∀ y ∈ Ici x, HasDerivAt Ψ (-sawT G₁ y) y)
  (hT2 : IntegrableOn (fun y => sawT G₁ y ^ 2) (Ioi x)) (hΨ2 : IntegrableOn (fun y => Ψ y ^ 2) (Ioi x))
include hΨ hT2 hΨ2

end Reflected

/-! ### The reflected half without the `L²` hypothesis on `θ r_G` -/

end Cvs.Route.Visibility.ReflectedRemainderMellin
