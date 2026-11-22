import Mathlib
import Cvs.StepA.OddSectorAsDerivatives
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform

/-!
# The window's Weil form of a derivative, on the prime side

For `g` supported in `(0, L)` with derivative `f` inside, the pole moments of `f` are `∓½` those
of `g`, the spectral density of `f` is `t²` times that of `g`, and so
`weilForm P R f = −¼·pole(g) + ∫ effSymbol(t)·t²·specDensity g t`.
-/

noncomputable section

open MeasureTheory intervalIntegral Set Complex Real
open scoped FourierTransform

namespace Cvs.StepA.DerivativeFormPrimeSide

variable {L : ℝ} {g f : ℝ → ℝ}

/-- A function vanishing off `(0, L)` integrates over `ℝ` as over `0..L`. -/
theorem integral_eq_interval (hL : 0 ≤ L) {φ : ℝ → ℝ} (h : ∀ s, s ∉ Ioo (0:ℝ) L → φ s = 0) :
    ∫ x : ℝ, φ x = ∫ x in (0:ℝ)..L, φ x := by
  rw [intervalIntegral.integral_of_le hL]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  apply h
  intro hx'
  exact hx ⟨hx'.1, hx'.2.le⟩

/-- **Integration by parts against a real exponential, with vanishing ends.** -/
theorem integral_deriv_mul_exp (hL : 0 ≤ L) (c : ℝ)
    (hg : ContinuousOn g (Icc 0 L))
    (hg' : ∀ x ∈ Ioo (0:ℝ) L, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume 0 L) (h0 : g 0 = 0) (hLz : g L = 0) :
    ∫ s in (0:ℝ)..L, f s * Real.exp (c * s) = -c * ∫ s in (0:ℝ)..L, g s * Real.exp (c * s) := by
  have hv : ∀ x : ℝ, HasDerivAt (fun s : ℝ => Real.exp (c * s)) (Real.exp (c * x) * c) x := by
    intro x
    have h1 : HasDerivAt (fun s : ℝ => c * s) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    exact h1.exp
  have huIcc : uIcc (0:ℝ) L = Icc 0 L := uIcc_of_le hL
  have hgi : IntervalIntegrable g volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL]
    exact hg.integrableOn_compact isCompact_Icc
  have hcont : ContinuousOn (fun s : ℝ => Real.exp (c * s)) (uIcc 0 L) :=
    fun x _ => (hv x).continuousAt.continuousWithinAt
  have key := integral_deriv_mul_eq_sub_of_hasDeriv_right (u := g)
    (v := fun s : ℝ => Real.exp (c * s)) (u' := f) (v' := fun x => Real.exp (c * x) * c)
    (a := 0) (b := L) (by rw [huIcc]; exact hg) hcont
    (by rw [min_eq_left hL, max_eq_right hL]; exact hg')
    (by intro x _; exact (hv x).hasDerivWithinAt) hf
    (by
      apply Continuous.intervalIntegrable
      exact (by fun_prop : Continuous fun x : ℝ => Real.exp (c * x)).mul continuous_const)
  rw [h0, hLz, zero_mul, zero_mul, sub_zero] at key
  have hv' : Continuous fun x : ℝ => Real.exp (c * x) * c :=
    (by fun_prop : Continuous fun x : ℝ => Real.exp (c * x)).mul continuous_const
  have hsplit : (∫ x in (0:ℝ)..L, f x * Real.exp (c * x) + g x * (Real.exp (c * x) * c))
      = (∫ x in (0:ℝ)..L, f x * Real.exp (c * x))
        + ∫ x in (0:ℝ)..L, g x * (Real.exp (c * x) * c) := by
    apply intervalIntegral.integral_add
    · exact hf.mul_continuousOn hcont
    · exact hgi.mul_continuousOn hv'.continuousOn
  rw [hsplit] at key
  have h2 : ∫ x in (0:ℝ)..L, g x * (Real.exp (c * x) * c)
      = c * ∫ x in (0:ℝ)..L, g x * Real.exp (c * x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  rw [h2] at key
  linarith

/-- **The pole moment `A` of a derivative is `−½` that of the function.** -/
theorem momentA_deriv (hL : 0 ≤ L)
    (hgs : ∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    (hg : ContinuousOn g (Icc 0 L))
    (hg' : ∀ x ∈ Ioo (0:ℝ) L, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume 0 L) :
    (∫ x : ℝ, f x * Real.exp (x / 2)) = -(1/2) * ∫ x : ℝ, g x * Real.exp (x / 2) := by
  have h0 : g 0 = 0 := hgs 0 (by simp)
  have hLz : g L = 0 := hgs L (by simp)
  rw [integral_eq_interval hL (fun s hs => by rw [hfs s hs, zero_mul]),
    integral_eq_interval hL (fun s hs => by rw [hgs s hs, zero_mul])]
  have := integral_deriv_mul_exp hL (1/2) hg hg' hf h0 hLz
  simp only [show ∀ x : ℝ, (1/2 : ℝ) * x = x / 2 from fun x => by ring] at this
  rw [this]

/-- **The pole moment `M` of a derivative is `½` that of the function.** -/
theorem momentM_deriv (hL : 0 ≤ L)
    (hgs : ∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    (hg : ContinuousOn g (Icc 0 L))
    (hg' : ∀ x ∈ Ioo (0:ℝ) L, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume 0 L) :
    (∫ x : ℝ, f x * Real.exp (-(x / 2))) = (1/2) * ∫ x : ℝ, g x * Real.exp (-(x / 2)) := by
  have h0 : g 0 = 0 := hgs 0 (by simp)
  have hLz : g L = 0 := hgs L (by simp)
  rw [integral_eq_interval hL (fun s hs => by rw [hfs s hs, zero_mul]),
    integral_eq_interval hL (fun s hs => by rw [hgs s hs, zero_mul])]
  have := integral_deriv_mul_exp hL (-(1/2)) hg hg' hf h0 hLz
  simp only [show ∀ x : ℝ, (-(1/2) : ℝ) * x = -(x / 2) from fun x => by ring] at this
  rw [this]; ring

/-- **The pole term of a derivative is `−¼` the pole term of the function.** -/
theorem pole_deriv (hL : 0 ≤ L)
    (hgs : ∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    (hg : ContinuousOn g (Icc 0 L))
    (hg' : ∀ x ∈ Ioo (0:ℝ) L, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume 0 L) :
    2 * (∫ x : ℝ, f x * Real.exp (x / 2)) * (∫ x : ℝ, f x * Real.exp (-(x / 2)))
      = -(1/4) * (2 * (∫ x : ℝ, g x * Real.exp (x / 2))
          * (∫ x : ℝ, g x * Real.exp (-(x / 2)))) := by
  rw [momentA_deriv hL hgs hfs hg hg' hf, momentM_deriv hL hgs hfs hg hg' hf]; ring

/-- **The transform of a derivative** is `2πi w` times the transform. -/
theorem fourier_deriv (hL : 0 ≤ L)
    (hgs : ∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    (hg : ContinuousOn g (Icc 0 L))
    (hg' : ∀ x ∈ Ioo (0:ℝ) L, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume 0 L) (w : ℝ) :
    𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) w = (I * (2 * π * w)) * 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf g) w := by
  have h0 : g 0 = 0 := hgs 0 (by simp)
  have hLz : g L = 0 := hgs L (by simp)
  -- unfold both transforms as interval integrals against `cexp (-(I * t) * s)`, `t = 2πw`
  have hchar : ∀ (φ : ℝ → ℝ), (∀ s, s ∉ Ioo (0:ℝ) L → φ s = 0) →
      𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf φ) w
        = ∫ s in (0:ℝ)..L, (φ s : ℂ) * cexp (-(I * (2 * π * w)) * s) := by
    intro φ hφ
    rw [Real.fourier_real_eq_integral_exp_smul]
    rw [intervalIntegral.integral_of_le hL]
    symm
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · congr 1; funext v
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, smul_eq_mul]
      rw [mul_comm]
      congr 1
      push_cast; ring_nf
    · intro x hx
      have : φ x = 0 := hφ x (fun hx' => hx ⟨hx'.1, hx'.2.le⟩)
      simp [Cvs.WeilForm.SelfConvolutionTransform.cf, this]
  rw [hchar f hfs, hchar g hgs]
  have := Cvs.StepA.OddSectorAsDerivatives.integral_deriv_mul_cexp (t := 2 * π * w) hL
    (g := fun s => (g s : ℂ)) (f := fun s => (f s : ℂ))
    (continuous_ofReal.comp_continuousOn hg)
    (fun x hx => ((hg' x hx).ofReal_comp))
    (by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL] at hf ⊢
      exact hf.ofReal)
    (by simp [h0]) (by simp [hLz])
  push_cast at this
  rw [this]

/-- **The spectral density of a derivative is `t²` times that of the function.** -/
theorem specDensity_deriv (hL : 0 ≤ L)
    (hgs : ∀ s, s ∉ Ioo (0:ℝ) L → g s = 0) (hfs : ∀ s, s ∉ Ioo (0:ℝ) L → f s = 0)
    (hg : ContinuousOn g (Icc 0 L))
    (hg' : ∀ x ∈ Ioo (0:ℝ) L, HasDerivWithinAt g (f x) (Ioi x) x)
    (hf : IntervalIntegrable f volume 0 L) (t : ℝ) :
    Cvs.WeilForm.SelfConvolutionCosine.specDensity f t = t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity g t := by
  unfold Cvs.WeilForm.SelfConvolutionCosine.specDensity
  rw [fourier_deriv hL hgs hfs hg hg' hf, norm_mul, mul_pow]
  have hπ : (0:ℝ) < π := Real.pi_pos
  have h1 : ‖I * (2 * π * ((t / (2 * π) : ℝ) : ℂ))‖ ^ 2 = t ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul]
    have : (2 * π * ((t / (2 * π) : ℝ) : ℂ)) = (t : ℂ) := by
      push_cast; field_simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h1]; ring

/-! ### Working backwards: the odd gap stated on the prime side -/

end Cvs.StepA.DerivativeFormPrimeSide
