import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Xi.PhiEvenExtension
import Cvs.Xi.PhiEvenRapidDecay
import Cvs.Xi.PhiEvenTransformCosine
import Cvs.Xi.RiemannPhiContinuous
import Cvs.Xi.RiemannPhiEven
import Cvs.Xi.RiemannPhiKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `Ξ` off the real line, and the transform of the `Φ` window

On `|Im z| < 1`, `Ξ z = 2∫ Φ(|u|) e^{izu} du`: the truncations to `[−n, n]` are entire and
converge uniformly on `|Im z| ≤ a < 1`, and the limit is `Ξ` on `ℝ`. The window
`1_(0,L] Φ(· − L/2)`, recentred, is the truncation to `[−L/2, L/2]`, so twice its transform is
within `4 C e^{−π} e^{−(1−a)L/2}/(1−a)` of `Ξ`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory FourierTransform

namespace Cvs.Xi.XiOffRealLine
open Cvs.ZeroCounting

open Cvs.Xi.RiemannPhiKernel (riemannPhi phiBoundConst)
open Cvs.Xi.PhiEvenExtension (phiEven phiEven_neg integrable_phiEven)
open Cvs.Limit.ZeroFreeApproximantsRH (Xi)
open FourierLaplace (fourierLaplace)

/-! ### The kernel on the strip -/

/-- The integrand of the Fourier–Laplace transform of `Φ`'s even extension at `z`. -/
def kernel (z : ℂ) (t : ℝ) : ℂ := phiEven t * Complex.exp (Complex.I * z * (t : ℂ))

theorem continuous_kernel (z : ℂ) : Continuous (kernel z) :=
  Cvs.Xi.RiemannPhiContinuous.continuous_phiEven.mul (by fun_prop)

theorem phiBoundConst_mul_nonneg : 0 ≤ phiBoundConst * Real.exp (-π) := by
  have h := (norm_nonneg _).trans (Cvs.Xi.PhiEvenRapidDecay.norm_phiEven_le 0)
  simpa using h

/-- At height at most `a`, the kernel is below `C e^{−π} e^{−(1−a)|t|}`. -/
theorem norm_kernel_le {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a) (t : ℝ) :
    ‖kernel z t‖ ≤ phiBoundConst * Real.exp (-π) * Real.exp (-((1 - a) * |t|)) := by
  rw [kernel, norm_mul, FourierLaplace.norm_exp_I_mul]
  have h1 := Cvs.Xi.PhiEvenRapidDecay.norm_phiEven_le t
  have h2 : -(t * z.im) ≤ |t| * a :=
    calc -(t * z.im) ≤ |t * z.im| := neg_le_abs _
      _ = |t| * |z.im| := abs_mul _ _
      _ ≤ |t| * a := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have hC := phiBoundConst_mul_nonneg
  calc ‖phiEven t‖ * Real.exp (-(t * z.im))
      ≤ (phiBoundConst * Real.exp (-π)) * Real.exp (-|t|) * Real.exp (|t| * a) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le
          (mul_nonneg hC (Real.exp_pos _).le)
    _ = phiBoundConst * Real.exp (-π) * Real.exp (-((1 - a) * |t|)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem norm_kernel_le_left {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a) (ha : a ≤ 1) (t : ℝ) :
    ‖kernel z t‖ ≤ phiBoundConst * Real.exp (-π) * Real.exp ((1 - a) * t) := by
  refine (norm_kernel_le hz t).trans (mul_le_mul_of_nonneg_left ?_ phiBoundConst_mul_nonneg)
  refine Real.exp_le_exp.mpr ?_
  have ha : 0 ≤ 1 - a := by linarith
  nlinarith [neg_abs_le t]

theorem norm_kernel_le_right {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a) (ha : a ≤ 1) (t : ℝ) :
    ‖kernel z t‖ ≤ phiBoundConst * Real.exp (-π) * Real.exp (-(1 - a) * t) := by
  refine (norm_kernel_le hz t).trans (mul_le_mul_of_nonneg_left ?_ phiBoundConst_mul_nonneg)
  refine Real.exp_le_exp.mpr ?_
  have ha : 0 ≤ 1 - a := by linarith
  nlinarith [le_abs_self t]

/-- The kernel is integrable below height `1`. -/
theorem integrable_kernel {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a) (ha : a < 1) :
    Integrable (kernel z) := by
  have hk : 0 < 1 - a := by linarith
  have hL : IntegrableOn (kernel z) (Iic 0) :=
    Integrable.mono' ((integrableOn_exp_mul_Iic hk 0).const_mul _)
      (continuous_kernel z).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Iic fun t _ => norm_kernel_le_left hz ha.le t)
  have hR : IntegrableOn (kernel z) (Ioi 0) :=
    Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _)
      (continuous_kernel z).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => norm_kernel_le_right hz ha.le t)
  have h := hL.union hR
  rwa [Iic_union_Ioi, integrableOn_univ] at h

/-! ### The truncations and their limit -/

/-- **Truncation error.** The transform differs from its truncation to `[−R, R]` by at most
`2 C e^{−π} e^{−(1−a)R}/(1−a)` at height at most `a < 1`. -/
theorem norm_fourierLaplace_sub_integral_le {z : ℂ} {a : ℝ} (hz : |z.im| ≤ a) (ha : a < 1)
    (R : ℝ) :
    ‖fourierLaplace phiEven z - ∫ t in (-R)..R, kernel z t‖
      ≤ 2 * (phiBoundConst * Real.exp (-π)) * Real.exp (-((1 - a) * R)) / (1 - a) := by
  have hk : 0 < 1 - a := by linarith
  have hI := integrable_kernel hz ha
  set C := phiBoundConst * Real.exp (-π)
  have hsplit : fourierLaplace phiEven z - ∫ t in (-R)..R, kernel z t
      = (∫ t in Iic (-R), kernel z t) + ∫ t in Ioi R, kernel z t := by
    rw [← intervalIntegral.integral_Iic_sub_Iic hI.integrableOn hI.integrableOn,
      show fourierLaplace phiEven z = ∫ t, kernel z t from rfl,
      ← intervalIntegral.integral_Iic_add_Ioi (b := R) hI.integrableOn hI.integrableOn]
    ring
  have hL : ‖∫ t in Iic (-R), kernel z t‖ ≤ C * Real.exp (-((1 - a) * R)) / (1 - a) := by
    calc ‖∫ t in Iic (-R), kernel z t‖ ≤ ∫ t in Iic (-R), C * Real.exp ((1 - a) * t) :=
          norm_integral_le_of_norm_le ((integrableOn_exp_mul_Iic hk _).const_mul C)
            (ae_restrict_of_forall_mem measurableSet_Iic fun t _ => norm_kernel_le_left hz ha.le t)
      _ = C * Real.exp (-((1 - a) * R)) / (1 - a) := by
          rw [integral_const_mul, integral_exp_mul_Iic hk]
          rw [mul_neg]
          ring
  have hR : ‖∫ t in Ioi R, kernel z t‖ ≤ C * Real.exp (-((1 - a) * R)) / (1 - a) := by
    calc ‖∫ t in Ioi R, kernel z t‖ ≤ ∫ t in Ioi R, C * Real.exp (-(1 - a) * t) :=
          norm_integral_le_of_norm_le
            ((integrableOn_exp_mul_Ioi (by linarith) _).const_mul C)
            (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => norm_kernel_le_right hz ha.le t)
      _ = C * Real.exp (-((1 - a) * R)) / (1 - a) := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by linarith),
            show -(1 - a) * R = -((1 - a) * R) by ring, div_neg, neg_div, neg_neg]
          ring
  rw [hsplit]
  calc ‖(∫ t in Iic (-R), kernel z t) + ∫ t in Ioi R, kernel z t‖
      ≤ ‖∫ t in Iic (-R), kernel z t‖ + ‖∫ t in Ioi R, kernel z t‖ := norm_add_le _ _
    _ ≤ C * Real.exp (-((1 - a) * R)) / (1 - a) + C * Real.exp (-((1 - a) * R)) / (1 - a) :=
        add_le_add hL hR
    _ = 2 * C * Real.exp (-((1 - a) * R)) / (1 - a) := by ring

/-- The truncation to `[−n, n]` is the transform of a compactly supported function. -/
theorem integral_kernel_eq (n : ℝ) (hn : 0 ≤ n) (z : ℂ) :
    ∫ t in (-n)..n, kernel z t = fourierLaplace ((Ioc (-n) n).indicator phiEven) z := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc,
    fourierLaplace]
  congr 1
  funext t
  by_cases ht : t ∈ Ioc (-n) n
  · simp [indicator_of_mem ht, kernel]
  · simp [indicator_of_notMem ht]

/-- Each truncation is entire. -/
theorem differentiable_integral_kernel (n : ℝ) (hn : 0 ≤ n) :
    Differentiable ℂ fun z => ∫ t in (-n)..n, kernel z t := by
  have h : (fun z => ∫ t in (-n)..n, kernel z t)
      = fourierLaplace ((Ioc (-n) n).indicator phiEven) :=
    funext (integral_kernel_eq n hn)
  rw [h]
  refine FourierLaplace.differentiable_fourierLaplace_of_integrable
    (integrable_phiEven.indicator measurableSet_Ioc)
    (HasCompactSupport.intro (isCompact_Icc (a := -n) (b := n)) ?_)
  intro t ht
  exact indicator_of_notMem (fun h => ht (Ioc_subset_Icc_self h)) _

/-- The open strip `|Im z| < 1`. -/
def strip : Set ℂ := {z | |z.im| < 1}

theorem isOpen_strip : IsOpen strip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem convex_strip : Convex ℝ strip := by
  have h : strip = Complex.imLm ⁻¹' Ioo (-1) 1 := by
    ext z
    simp [strip, abs_lt]
  rw [h]
  exact (convex_Ioo (-1 : ℝ) 1).linear_preimage Complex.imLm

/-- The truncations converge uniformly at height at most `a < 1`. -/
theorem tendstoUniformlyOn_integral_kernel {a : ℝ} (ha : a < 1) :
    TendstoUniformlyOn (fun (n : ℕ) z => ∫ t in (-(n : ℝ))..n, kernel z t)
      (fourierLaplace phiEven) atTop {z | |z.im| ≤ a} := by
  have hk : 0 < 1 - a := by linarith
  set C := phiBoundConst * Real.exp (-π)
  have hlim :
      Tendsto (fun n : ℕ => 2 * C * Real.exp (-((1 - a) * n)) / (1 - a)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.exp (-((1 - a) * n))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (Tendsto.const_mul_atTop hk tendsto_natCast_atTop_atTop))
    simpa using (h1.const_mul (2 * C)).div_const (1 - a)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn z hz
  rw [dist_eq_norm]
  exact (norm_fourierLaplace_sub_integral_le hz ha n).trans_lt hn

/-- The transform of `Φ`'s even extension is holomorphic on the strip `|Im z| < 1`. -/
theorem differentiableOn_fourierLaplace_phiEven :
    DifferentiableOn ℂ (fourierLaplace phiEven) strip := by
  have hloc : TendstoLocallyUniformlyOn (fun (n : ℕ) z => ∫ t in (-(n : ℝ))..n, kernel z t)
      (fourierLaplace phiEven) atTop strip := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_strip]
    intro K hKs hK
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact tendstoUniformlyOn_empty
    obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hne
      (continuous_abs.comp Complex.continuous_im).continuousOn
    exact (tendstoUniformlyOn_integral_kernel (hKs hz₀)).mono
      fun z hz => isMaxOn_iff.mp hmax z hz
  exact hloc.differentiableOn (Eventually.of_forall fun n =>
    (differentiable_integral_kernel n (Nat.cast_nonneg n)).differentiableOn) isOpen_strip

/-! ### `Ξ` on the strip -/

/-- On the real line, `Ξ` is twice the transform of `Φ`'s even extension. -/
theorem Xi_ofReal_eq (τ : ℝ) : Xi (τ : ℂ) = 2 * fourierLaplace phiEven (τ : ℂ) := by
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have h := Cvs.Xi.PhiEvenTransformCosine.Xi_eq_two_mul_fourierIntegral (τ / (2 * π))
  rw [show 2 * π * (τ / (2 * π)) = τ by field_simp] at h
  rw [h, ← FourierLaplace.fourierLaplace_even phiEven_neg, Real.fourier_real_eq_integral_exp_smul,
    fourierLaplace]
  congr 2
  funext t
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/-- **`Ξ` on the strip.** For `|Im z| < 1`, `Ξ z = 2∫ Φ(|u|) e^{izu} du`. -/
theorem Xi_eq_two_mul_fourierLaplace {z : ℂ} (hz : |z.im| < 1) :
    Xi z = 2 * fourierLaplace phiEven z := by
  have hXi : AnalyticOnNhd ℂ Xi strip :=
    Cvs.Limit.ZeroFreeApproximantsRH.differentiable_Xi.differentiableOn.analyticOnNhd isOpen_strip
  have hF : AnalyticOnNhd ℂ (fun z => 2 * fourierLaplace phiEven z) strip :=
    ((differentiableOn_fourierLaplace_phiEven.const_mul 2)).analyticOnNhd isOpen_strip
  have h0 : (0 : ℂ) ∈ strip := by show |(0 : ℂ).im| < 1; simp
  have hreal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using hx)
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), Xi w = 2 * fourierLaplace phiEven w :=
    hreal.frequently (Frequently.of_forall fun x => Xi_ofReal_eq x)
  exact hXi.eqOn_of_preconnected_of_frequently_eq hF convex_strip.isPreconnected h0 hfreq hz

/-! ### The `Φ` window -/

/-- The window `1_(0,L] Φ(· − L/2)`. -/
def phiWindow (L : ℝ) : ℝ → ℝ := (Ioc 0 L).indicator fun s => riemannPhi (s - L / 2)

/-- **The recentred window transform is the truncation of `Φ`'s transform to `[−L/2, L/2]`.** -/
theorem phase_mul_fourierLaplace_phiWindow {L : ℝ} (hL : 0 ≤ L) (z : ℂ) :
    Cvs.Finite.RecentredTransform.phase L z
        * fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (phiWindow L)) z
      = ∫ u in (-(L / 2))..(L / 2), phiEven u * Complex.exp (Complex.I * z * (u : ℂ)) := by
  rw [Cvs.Finite.RecentredTransform.fourierLaplace_shift _ (L / 2) z, ← mul_assoc,
    Cvs.Finite.RecentredTransform.phase, ← Complex.exp_add,
    show -(Complex.I * z * (L : ℂ) / 2) + Complex.I * z * ((L / 2 : ℝ) : ℂ) = 0 by
      push_cast; ring,
    Complex.exp_zero, one_mul, intervalIntegral.integral_of_le (by linarith),
    ← integral_indicator measurableSet_Ioc]
  congr 1
  funext s
  have hmem : L / 2 + s ∈ Ioc 0 L ↔ s ∈ Ioc (-(L / 2)) (L / 2) := by
    simp only [mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hs : s ∈ Ioc (-(L / 2)) (L / 2)
  · rw [indicator_of_mem hs, Cvs.WeilForm.SelfConvolutionTransform.cf, phiWindow,
      indicator_of_mem (hmem.mpr hs), Cvs.Xi.RiemannPhiEven.phiEven_eq]
    congr 3
    ring
  · rw [indicator_of_notMem hs, Cvs.WeilForm.SelfConvolutionTransform.cf, phiWindow,
      indicator_of_notMem (fun h => hs (hmem.mp h))]
    simp

/-- **Window error.** At height at most `a < 1`, twice the recentred window transform is within
`4 C e^{−π} e^{−(1−a)L/2}/(1−a)` of `Ξ`. -/
theorem norm_two_mul_phase_mul_sub_Xi_le {L a : ℝ} (hL : 0 ≤ L) (ha : a < 1) {z : ℂ}
    (hz : |z.im| ≤ a) :
    ‖2 * (Cvs.Finite.RecentredTransform.phase L z
        * fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf (phiWindow L)) z) - Xi z‖
      ≤ 4 * (phiBoundConst * Real.exp (-π)) * Real.exp (-((1 - a) * (L / 2))) / (1 - a) := by
  rw [phase_mul_fourierLaplace_phiWindow hL, Xi_eq_two_mul_fourierLaplace (hz.trans_lt ha)]
  have h := norm_fourierLaplace_sub_integral_le hz ha (L / 2)
  have he : 2 * (∫ u in (-(L / 2))..(L / 2), phiEven u * Complex.exp (Complex.I * z * (u : ℂ)))
      - 2 * fourierLaplace phiEven z
      = -(2 * (fourierLaplace phiEven z - ∫ t in (-(L / 2))..(L / 2), kernel z t)) := by
    simp only [kernel]
    ring
  rw [he, norm_neg, norm_mul, Complex.norm_two]
  calc 2 * ‖fourierLaplace phiEven z - ∫ t in (-(L / 2))..(L / 2), kernel z t‖
      ≤ 2 * (2 * (phiBoundConst * Real.exp (-π)) * Real.exp (-((1 - a) * (L / 2))) / (1 - a)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 4 * (phiBoundConst * Real.exp (-π)) * Real.exp (-((1 - a) * (L / 2))) / (1 - a) := by
        ring

end Cvs.Xi.XiOffRealLine
