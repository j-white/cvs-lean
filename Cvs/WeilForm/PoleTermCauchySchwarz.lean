import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# Cauchy–Schwarz by completing the square, and the pole term's bound

    (∫ f·h)² ≤ (∫ f²)·(∫ h²),   and on the window   (∫ f·e^{s/2})² ≤ g 0 · (e^{L/2} − e^{−L/2})

so both pole functionals of `Cvs.WeilForm.SelfConvolutionFunctional`'s form are bounded by the norm, with the window length
in closed form.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.PoleTermCauchySchwarz

/-- **Cauchy–Schwarz for integrals.**  The square `∫ (f − t·h)² ≥ 0` at `t = b/a`. -/
theorem sq_integral_mul_le {f h : ℝ → ℝ}
    (hf : Integrable fun s => (f s) ^ 2) (hh : Integrable fun s => (h s) ^ 2)
    (hfh : Integrable fun s => f s * h s) :
    (∫ s : ℝ, f s * h s) ^ 2 ≤ (∫ s : ℝ, (f s) ^ 2) * ∫ s : ℝ, (h s) ^ 2 := by
  set a : ℝ := ∫ s : ℝ, (h s) ^ 2 with hadef
  set b : ℝ := ∫ s : ℝ, f s * h s with hbdef
  set c : ℝ := ∫ s : ℝ, (f s) ^ 2 with hcdef
  have key : ∀ t : ℝ, 0 ≤ c - 2 * t * b + t ^ 2 * a := by
    intro t
    have hnn : 0 ≤ ∫ s : ℝ, (f s - t * h s) ^ 2 := integral_nonneg fun s => sq_nonneg _
    have hexp : ∀ s : ℝ, (f s - t * h s) ^ 2
        = ((f s) ^ 2 - 2 * t * (f s * h s)) + t ^ 2 * (h s) ^ 2 := by
      intro s; ring
    have h1 : Integrable fun s => (f s) ^ 2 - 2 * t * (f s * h s) :=
      hf.sub (hfh.const_mul (2 * t))
    have h2 : Integrable fun s => t ^ 2 * (h s) ^ 2 := hh.const_mul (t ^ 2)
    have hval : (∫ s : ℝ, (f s - t * h s) ^ 2) = c - 2 * t * b + t ^ 2 * a := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_add h1 h2,
        integral_sub hf (hfh.const_mul (2 * t)), integral_const_mul, integral_const_mul]
    linarith [hval ▸ hnn]
  have hanonneg : 0 ≤ a := integral_nonneg fun s => sq_nonneg _
  rcases eq_or_lt_of_le hanonneg with ha | ha
  · have hb : b = 0 := by
      by_contra hb
      have hkey := key ((c + 1) / (2 * b))
      have hz : ((c + 1) / (2 * b)) ^ 2 * a = 0 := by rw [← ha]; ring
      have hmul : 2 * ((c + 1) / (2 * b)) * b = c + 1 := by field_simp
      rw [hz, hmul] at hkey
      linarith
    rw [hb, ← ha]
    simp
  · have hk := key (b / a)
    have h1 : 2 * (b / a) * b = 2 * (b ^ 2 / a) := by field_simp <;> ring
    have h2 : (b / a) ^ 2 * a = b ^ 2 / a := by field_simp <;> ring
    rw [h1, h2] at hk
    have hdiv : b ^ 2 / a ≤ c := by linarith
    calc b ^ 2 = b ^ 2 / a * a := by field_simp <;> ring
      _ ≤ c * a := mul_le_mul_of_nonneg_right hdiv ha.le

/-- A weight cut down to the window. -/
def windowFn (L : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := (Icc (-(L / 2)) (L / 2)).indicator φ

/-- **The pole functional is bounded by the norm.**  A test function supported in the window
cannot see the weight outside it, so only the weight's energy on the window is charged. -/
theorem sq_integral_mul_le_window {f φ : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ x, x ∉ Icc (-(L / 2)) (L / 2) → f x = 0)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hφ : Continuous φ)
    (hcross : Integrable fun s => f s * φ s) :
    (∫ s : ℝ, f s * φ s) ^ 2
      ≤ selfConvolution f 0 * ∫ s in Icc (-(L / 2)) (L / 2), (φ s) ^ 2 := by
  have hsqOn : IntegrableOn (fun s => (φ s) ^ 2) (Icc (-(L / 2)) (L / 2)) :=
    (hφ.pow 2).integrableOn_Icc
  have hhsq : Integrable fun s => (windowFn L φ s) ^ 2 := by
    have hind : (fun s => (windowFn L φ s) ^ 2)
        = (Icc (-(L / 2)) (L / 2)).indicator fun s => (φ s) ^ 2 := by
      funext s
      by_cases hs : s ∈ Icc (-(L / 2)) (L / 2)
      · simp [windowFn, Set.indicator_of_mem hs]
      · simp [windowFn, Set.indicator_of_notMem hs]
    rw [hind, integrable_indicator_iff measurableSet_Icc]
    exact hsqOn
  have hmul : ∀ s : ℝ, f s * windowFn L φ s = f s * φ s := by
    intro s
    by_cases hs : s ∈ Icc (-(L / 2)) (L / 2)
    · rw [windowFn, Set.indicator_of_mem hs]
    · rw [hsupp s hs]; ring
  have hcross' : Integrable fun s => f s * windowFn L φ s := by
    refine hcross.congr (Filter.Eventually.of_forall fun s => (hmul s).symm)
  have hCS := sq_integral_mul_le hsq hhsq hcross'
  have hL : (∫ s : ℝ, f s * windowFn L φ s) = ∫ s : ℝ, f s * φ s :=
    integral_congr_ae (Filter.Eventually.of_forall hmul)
  have hR : (∫ s : ℝ, (windowFn L φ s) ^ 2)
      = ∫ s in Icc (-(L / 2)) (L / 2), (φ s) ^ 2 := by
    have hind : (fun s => (windowFn L φ s) ^ 2)
        = (Icc (-(L / 2)) (L / 2)).indicator fun s => (φ s) ^ 2 := by
      funext s
      by_cases hs : s ∈ Icc (-(L / 2)) (L / 2)
      · simp [windowFn, Set.indicator_of_mem hs]
      · simp [windowFn, Set.indicator_of_notMem hs]
    rw [hind, integral_indicator measurableSet_Icc]
  have hg0 : selfConvolution f 0 = ∫ s : ℝ, (f s) ^ 2 := by
    unfold selfConvolution
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [add_zero]
    ring
  rw [hL, hR] at hCS
  rw [hg0]
  exact hCS

/-! ### The two pole weights, in closed form -/

/-- **The pole weight's energy on the window.**  Both signs give the same `2·sinh(L/2)`. -/
theorem integral_sq_exp_half {L : ℝ} (hL : 0 ≤ L) :
    (∫ s in Icc (-(L / 2)) (L / 2), (Real.exp (s / 2)) ^ 2) = 2 * Real.sinh (L / 2) := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hsq : ∀ s : ℝ, (Real.exp (s / 2)) ^ 2 = Real.exp s := by
    intro s
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ => hsq s),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, integral_exp, Real.sinh_eq]
  ring

/-- **The reflected weight has the same energy.** -/
theorem integral_sq_exp_neg_half {L : ℝ} (hL : 0 ≤ L) :
    (∫ s in Icc (-(L / 2)) (L / 2), (Real.exp (-(s / 2))) ^ 2) = 2 * Real.sinh (L / 2) := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hsq : ∀ s : ℝ, (Real.exp (-(s / 2))) ^ 2 = Real.exp (-s) := by
    intro s
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ => hsq s),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  have hneg : (∫ x in (-(L / 2))..(L / 2), Real.exp (-x))
      = ∫ x in (-(L / 2))..(L / 2), Real.exp x := by
    rw [intervalIntegral.integral_comp_neg (f := Real.exp)]
    norm_num
  rw [hneg, integral_exp, Real.sinh_eq]
  ring

/-- **The pole term is bounded by the norm.**  `2·A(f)·M(f)` costs at most `4·sinh(L/2)`
times the norm, whichever sign it takes. -/
theorem neg_le_poleTerm {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hsupp : ∀ x, x ∉ Icc (-(L / 2)) (L / 2) → f x = 0)
    (hsq : Integrable fun s => (f s) ^ 2)
    (hA : Integrable fun s => f s * Real.exp (s / 2))
    (hM : Integrable fun s => f s * Real.exp (-(s / 2))) :
    -(4 * Real.sinh (L / 2) * selfConvolution f 0)
      ≤ 2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * ∫ x : ℝ, f x * Real.exp (-(x / 2)) := by
  have hAsq := sq_integral_mul_le_window (φ := fun s => Real.exp (s / 2)) hsupp hsq
    (Real.continuous_exp.comp (continuous_id.div_const 2)) hA
  have hMsq := sq_integral_mul_le_window (φ := fun s => Real.exp (-(s / 2))) hsupp hsq
    (Real.continuous_exp.comp ((continuous_id.div_const 2).neg)) hM
  rw [integral_sq_exp_half hL] at hAsq
  rw [integral_sq_exp_neg_half hL] at hMsq
  nlinarith [sq_nonneg ((∫ x : ℝ, f x * Real.exp (x / 2)) + ∫ x : ℝ, f x * Real.exp (-(x / 2)))]

end Cvs.WeilForm.PoleTermCauchySchwarz
