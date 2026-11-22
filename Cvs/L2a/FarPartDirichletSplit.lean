import Mathlib
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpanPoleMellinFromRungs
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Per-rung reduction and the Dirichlet split of the far part

`specMass (Σ aᵢGᵢ) K ≤ (Σ aᵢ²mᵢ)·Σ specMass Gᵢ K/mᵢ` (Cvs.L2a.SpanPoleMellinFromRungs at each `t`); `specMass G K ≤ (K/π)B²` when the
transform is at most `B` in modulus below `K`; the far-part transform `posTail Φ X − posTail Φ k` at `t` is
`Z_k(t)·I(k,X;t) + Σ_{⌊k⌋<m≤⌊X⌋} m^{−1/2+it}·I(m,X;t)` with `Z_k = Σ_{m≤k} m^{−1/2+it}`; and the elementary sums
`Σ_{m≤k} m^{−1/2} ≤ 2√k`, `Σ_{m≥⌈k⌉} m^{−2} ≤ 3/(2k)` for `k ≥ 2`.
-/

namespace Cvs.L2a.FarPartDirichletSplit

open Real Set MeasureTheory Cvs.L2a.TailLogScaleTest Cvs.L2a.PositionTruncatedTail Cvs.L2a.SpectralMassLevelLeak
open Cvs.WeilForm.SelfConvolutionCosine (specDensity specDensity_nonneg)
open Cvs.Prolate.Mellin.MellinKernelSturmLiouville (ky kys)
open scoped FourierTransform

/-! ### Per-rung reduction -/

/-- The log-scale map of a finite linear combination is the combination of the log-scale maps. -/
theorem logScale_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (G : ι → ℝ → ℝ) :
    logScale (fun θ => ∑ i ∈ s, a i * G i θ) = fun x => ∑ i ∈ s, a i * logScale (G i) x := by
  funext x; simp only [logScale, Finset.sum_mul, mul_assoc]

/-- The Fourier transform of a complexified finite combination of integrable real functions is the combination
of the transforms. -/
theorem fourier_cf_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) {f : ι → ℝ → ℝ} (hf : ∀ i, Integrable (f i))
    (w : ℝ) :
    𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (fun x => ∑ i ∈ s, a i * f i x)) w
      = ∑ i ∈ s, (a i : ℂ) * 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (f i)) w := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  rw [← integral_finsetSum s fun i _ => (integrable_fourier_integrand (hf i) w).const_mul (a i : ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Pointwise per-rung reduction**: the spectral density of `Σ aᵢfᵢ` is at most
`(Σ aᵢ²mᵢ)·Σ specDensity fᵢ/mᵢ`. -/
theorem specDensity_sum_le {ι : Type} [Fintype ι] (a m : ι → ℝ) {f : ι → ℝ → ℝ} (hm : ∀ i, 0 < m i)
    (hf : ∀ i, Integrable (f i)) (t : ℝ) :
    specDensity (fun x => ∑ i, a i * f i x) t ≤ (∑ i, a i ^ 2 * m i) * ∑ i, specDensity (f i) t / m i := by
  set z : ι → ℂ := fun i => 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (f i)) (t / (2 * π))
  have hz : 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (fun x => ∑ i, a i * f i x)) (t / (2 * π)) = ∑ i, (a i : ℂ) * z i :=
    fourier_cf_sum Finset.univ a hf _
  have h1 : ‖∑ i, (a i : ℂ) * z i‖ ≤ ∑ i, |a i| * ‖z i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := Cvs.L2a.SpanPoleMellinFromRungs.abs_sum_le_mass (fun i => |a i|) (fun i => ‖z i‖) (fun i => ‖z i‖) m hm
    (fun i => (abs_norm _).le)
  have e1 : ∑ i, |a i| ^ 2 * m i = ∑ i, a i ^ 2 * m i := Finset.sum_congr rfl fun i _ => by rw [sq_abs]
  rw [e1] at h2
  have hS0 : 0 ≤ ∑ i, a i ^ 2 * m i := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hm i).le
  have hM0 := Cvs.L2a.SpanPoleMellinFromRungs.massSum_nonneg (fun i => ‖z i‖) hm
  have h3 : ‖∑ i, (a i : ℂ) * z i‖ ≤ √(∑ i, a i ^ 2 * m i) * √(Cvs.L2a.SpanPoleMellinFromRungs.massSum (fun i => ‖z i‖) m) :=
    h1.trans ((le_abs_self _).trans h2)
  have h4 : ‖∑ i, (a i : ℂ) * z i‖ ^ 2
      ≤ (∑ i, a i ^ 2 * m i) * Cvs.L2a.SpanPoleMellinFromRungs.massSum (fun i => ‖z i‖) m := by
    calc ‖∑ i, (a i : ℂ) * z i‖ ^ 2
        ≤ (√(∑ i, a i ^ 2 * m i) * √(Cvs.L2a.SpanPoleMellinFromRungs.massSum (fun i => ‖z i‖) m)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hS0, Real.sq_sqrt hM0]
  have hpi : 0 < 2 * π := by positivity
  unfold specDensity
  rw [hz]
  have e2 : ∑ i, ‖z i‖ ^ 2 / (2 * π) / m i = Cvs.L2a.SpanPoleMellinFromRungs.massSum (fun i => ‖z i‖) m / (2 * π) := by
    rw [Cvs.L2a.SpanPoleMellinFromRungs.massSum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2, mul_div_assoc']
  exact div_le_div_of_nonneg_right h4 hpi.le

/-- **Per-rung reduction of the spectral mass**: for masses `mᵢ > 0` and `logScale Gᵢ ∈ L¹ ∩ L²`,
`specMass (Σ aᵢGᵢ) K ≤ (Σ aᵢ²mᵢ)·Σ specMass Gᵢ K/mᵢ`. -/
theorem specMass_span_le {ι : Type} [Fintype ι] (a m : ι → ℝ) (G : ι → ℝ → ℝ) (hm : ∀ i, 0 < m i)
    (h2 : ∀ i, MemLp (logScale (G i)) 2 volume) (h1 : ∀ i, Integrable (logScale (G i))) (K : ℝ) :
    specMass (fun θ => ∑ i, a i * G i θ) K ≤ (∑ i, a i ^ 2 * m i) * ∑ i, specMass (G i) K / m i := by
  have hfi : ∀ i, Integrable (specDensity (logScale (G i))) := fun i =>
    Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity (h2 i) (h1 i)
  set S := {t : ℝ | |t| < K}
  have hR : Integrable (fun t => (∑ i, a i ^ 2 * m i) * ∑ i, specDensity (logScale (G i)) t / m i)
      (volume.restrict S) :=
    (integrable_finsetSum _ fun i _ => (hfi i).restrict.div_const _).const_mul _
  unfold specMass
  rw [logScale_sum]
  calc ∫ t in S, specDensity (fun x => ∑ i, a i * logScale (G i) x) t
      ≤ ∫ t in S, (∑ i, a i ^ 2 * m i) * ∑ i, specDensity (logScale (G i)) t / m i :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => specDensity_nonneg _ t) hR
          (Filter.Eventually.of_forall fun t => specDensity_sum_le a m hm h1 t)
    _ = (∑ i, a i ^ 2 * m i) * ∑ i, (∫ t in S, specDensity (logScale (G i)) t) / m i := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => (hfi i).restrict.div_const _]
        congr 1
        exact Finset.sum_congr rfl fun i _ => integral_div _ _

/-! ### Spectral mass from a transform bound -/

/-- The set `{t | |t| < K}` is the interval `(−K, K)`. -/
theorem abs_lt_eq_Ioo (K : ℝ) : {t : ℝ | |t| < K} = Ioo (-K) K := by
  ext t; simp only [mem_ofPred_eq, mem_Ioo, abs_lt]

/-- **Spectral mass from a sup bound on the transform**: if `‖𝓕(logScale G)(t/2π)‖² ≤ B²` for `|t| < K`, then
`specMass G K ≤ (K/π)·B²`. -/
theorem specMass_le_sup_fourier (G : ℝ → ℝ) {K B : ℝ} (hK : 0 ≤ K)
    (hB : ∀ t, |t| < K → ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (logScale G)) (t / (2 * π))‖ ^ 2 ≤ B ^ 2) :
    specMass G K ≤ K / π * B ^ 2 := by
  have hpi : 0 < 2 * π := by positivity
  have hfin : volume {t : ℝ | |t| < K} < ⊤ := by rw [abs_lt_eq_Ioo]; exact measure_Ioo_lt_top
  have h := norm_setIntegral_le_of_norm_le_const (f := specDensity (logScale G)) (C := B ^ 2 / (2 * π)) hfin
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (specDensity_nonneg _ t), specDensity]
      exact div_le_div_of_nonneg_right (hB t ht) hpi.le)
  rw [abs_lt_eq_Ioo, volume_real_Ioo_of_le (by linarith)] at h
  have e : B ^ 2 / (2 * π) * (K - -K) = K / π * B ^ 2 := by field_simp; ring
  rw [e] at h
  refine (Real.le_norm_self _).trans ?_
  rw [specMass, abs_lt_eq_Ioo]
  exact h

/-! ### The Dirichlet split of the far part -/

/-- The Dirichlet coefficient `m^{−1/2+it}`. -/
noncomputable def dch (m t : ℝ) : ℂ := ((√m)⁻¹ : ℝ) * Complex.exp (((t * Real.log m : ℝ) : ℂ) * Complex.I)

/-- The truncated Mellin integral `I(a,b;t) = ∫_a^b Φ(ξ) ξ^{−1/2−it} dξ`, written with `y_t` and `ỹ_t`. -/
noncomputable def mellinI (Φ : ℝ → ℝ) (a b t : ℝ) : ℂ :=
  ((∫ ξ in a..b, Φ ξ * ky t ξ : ℝ) : ℂ) - Complex.I * ((∫ ξ in a..b, Φ ξ * kys t ξ : ℝ) : ℂ)

/-- `|m^{−1/2+it}| = m^{−1/2}`. -/
theorem norm_dch (m t : ℝ) : ‖dch m t‖ = (√m)⁻¹ := by
  rw [dch, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]

/-- The kernel `y_t` is continuous on `[1, X]`. -/
theorem continuousOn_ky (t X : ℝ) : ContinuousOn (ky t) (Icc 1 X) := by
  have hpos : ∀ θ ∈ Icc (1 : ℝ) X, θ ≠ 0 := fun θ hθ => ne_of_gt (lt_of_lt_of_le one_pos hθ.1)
  refine ContinuousOn.div ?_ continuous_sqrt.continuousOn fun θ hθ => ?_
  · exact continuous_cos.comp_continuousOn (continuousOn_const.mul (Real.continuousOn_log.mono fun θ hθ => hpos θ hθ))
  · exact (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hθ.1)).ne'

/-- The kernel `ỹ_t` is continuous on `[1, X]`. -/
theorem continuousOn_kys (t X : ℝ) : ContinuousOn (kys t) (Icc 1 X) := by
  have hpos : ∀ θ ∈ Icc (1 : ℝ) X, θ ≠ 0 := fun θ hθ => ne_of_gt (lt_of_lt_of_le one_pos hθ.1)
  refine ContinuousOn.div ?_ continuous_sqrt.continuousOn fun θ hθ => ?_
  · exact continuous_sin.comp_continuousOn (continuousOn_const.mul (Real.continuousOn_log.mono fun θ hθ => hpos θ hθ))
  · exact (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hθ.1)).ne'

/-- Dilating `y_t`: `m⁻¹ y_t(ξ/m) = m^{−1/2}(cos(t log m) y_t(ξ) + sin(t log m) ỹ_t(ξ))` for `m, ξ > 0`. -/
theorem ky_div {m ξ : ℝ} (hm : 0 < m) (hξ : 0 < ξ) (t : ℝ) :
    m⁻¹ * ky t (ξ / m) = (√m)⁻¹ * (cos (t * Real.log m) * ky t ξ + sin (t * Real.log m) * kys t ξ) := by
  have hsm := Real.sqrt_pos.mpr hm
  have hsξ := Real.sqrt_pos.mpr hξ
  have hmm : m⁻¹ = (√m)⁻¹ * (√m)⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hm.le]
  unfold ky kys
  rw [Real.log_div hξ.ne' hm.ne', Real.sqrt_div' _ hm.le, mul_sub, cos_sub, hmm]
  field_simp

/-- Dilating `ỹ_t`: `m⁻¹ ỹ_t(ξ/m) = m^{−1/2}(cos(t log m) ỹ_t(ξ) − sin(t log m) y_t(ξ))` for `m, ξ > 0`. -/
theorem kys_div {m ξ : ℝ} (hm : 0 < m) (hξ : 0 < ξ) (t : ℝ) :
    m⁻¹ * kys t (ξ / m) = (√m)⁻¹ * (cos (t * Real.log m) * kys t ξ - sin (t * Real.log m) * ky t ξ) := by
  have hsm := Real.sqrt_pos.mpr hm
  have hsξ := Real.sqrt_pos.mpr hξ
  have hmm : m⁻¹ = (√m)⁻¹ * (√m)⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt hm.le]
  unfold ky kys
  rw [Real.log_div hξ.ne' hm.ne', Real.sqrt_div' _ hm.le, mul_sub, sin_sub, hmm]
  field_simp

/-- One mode of the tail transform: for `1 ≤ m ≤ Y`,
`m⁻¹ ∫_m^Y Φ(ξ) y_t(ξ/m) − i m⁻¹ ∫_m^Y Φ(ξ) ỹ_t(ξ/m) = m^{−1/2+it}·I(m,Y;t)`. -/
theorem mode_eq (Φ : ℝ → ℝ) {m Y : ℝ} (hm : 1 ≤ m) (hmY : m ≤ Y) (hΦ : ContinuousOn Φ (Icc 1 Y)) (t : ℝ) :
    ((m⁻¹ * ∫ ξ in m..Y, Φ ξ * ky t (ξ / m) : ℝ) : ℂ) - Complex.I * ((m⁻¹ * ∫ ξ in m..Y, Φ ξ * kys t (ξ / m) : ℝ) : ℂ)
      = dch m t * mellinI Φ m Y t := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have hsub : uIcc m Y ⊆ Icc 1 Y := by rw [uIcc_of_le hmY]; exact Icc_subset_Icc_left hm
  have hiy : IntervalIntegrable (fun ξ => Φ ξ * ky t ξ) volume m Y :=
    ((hΦ.mul (continuousOn_ky t Y)).mono hsub).intervalIntegrable
  have hiys : IntervalIntegrable (fun ξ => Φ ξ * kys t ξ) volume m Y :=
    ((hΦ.mul (continuousOn_kys t Y)).mono hsub).intervalIntegrable
  set c := cos (t * Real.log m) with hc
  set s := sin (t * Real.log m) with hs
  have hpos : ∀ ξ ∈ uIcc m Y, 0 < ξ := fun ξ hξ => by rw [uIcc_of_le hmY] at hξ; linarith [hξ.1]
  have e1 : m⁻¹ * ∫ ξ in m..Y, Φ ξ * ky t (ξ / m)
      = (√m)⁻¹ * (c * (∫ ξ in m..Y, Φ ξ * ky t ξ) + s * ∫ ξ in m..Y, Φ ξ * kys t ξ) := by
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_congr (g := fun ξ => (√m)⁻¹ * (c * (Φ ξ * ky t ξ) + s * (Φ ξ * kys t ξ)))
        fun ξ hξ => ?_,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hiy.const_mul c) (hiys.const_mul s),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have := ky_div hm0 (hpos ξ hξ) t
    calc m⁻¹ * (Φ ξ * ky t (ξ / m)) = Φ ξ * (m⁻¹ * ky t (ξ / m)) := by ring
      _ = _ := by rw [this]; ring
  have e2 : m⁻¹ * ∫ ξ in m..Y, Φ ξ * kys t (ξ / m)
      = (√m)⁻¹ * (c * (∫ ξ in m..Y, Φ ξ * kys t ξ) - s * ∫ ξ in m..Y, Φ ξ * ky t ξ) := by
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_congr (g := fun ξ => (√m)⁻¹ * (c * (Φ ξ * kys t ξ) - s * (Φ ξ * ky t ξ)))
        fun ξ hξ => ?_,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hiys.const_mul c) (hiy.const_mul s),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have := kys_div hm0 (hpos ξ hξ) t
    calc m⁻¹ * (Φ ξ * kys t (ξ / m)) = Φ ξ * (m⁻¹ * kys t (ξ / m)) := by ring
      _ = _ := by rw [this]; ring
  rw [hc, hs] at e1 e2
  rw [e1, e2, dch, mellinI, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The tail transform as a Dirichlet sum**: for `1 ≤ Y` and `Φ` continuous on `[1, Y]`,
`∫_{θ>1} posTail Φ Y·y_t − i∫_{θ>1} posTail Φ Y·ỹ_t = Σ_{1≤m≤⌊Y⌋} m^{−1/2+it}·I(m,Y;t)`. -/
theorem mellin_posTail_eq (Φ : ℝ → ℝ) {Y : ℝ} (hY : 1 ≤ Y) (hΦ : ContinuousOn Φ (Icc 1 Y)) (t : ℝ) :
    ((∫ θ in Ioi 1, posTail Φ Y θ * ky t θ : ℝ) : ℂ) - Complex.I * ((∫ θ in Ioi 1, posTail Φ Y θ * kys t θ : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, dch m t * mellinI Φ m Y t := by
  rw [Cvs.L2a.PositionTailSpanAdapters.integral_posTail_mul hY hΦ (continuousOn_ky t Y),
    Cvs.L2a.PositionTailSpanAdapters.integral_posTail_mul hY hΦ (continuousOn_kys t Y)]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hmY : (m : ℝ) ≤ Y := (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by linarith))
  have := mode_eq Φ hm1 hmY hΦ t
  push_cast at this
  exact this

/-- `I(a,b;t) = I(a,k;t) + I(k,b;t)` for `1 ≤ a ≤ k ≤ b` and `Φ` continuous on `[1, b]`. -/
theorem mellinI_add (Φ : ℝ → ℝ) {a k b : ℝ} (ha : 1 ≤ a) (hak : a ≤ k) (hkb : k ≤ b)
    (hΦ : ContinuousOn Φ (Icc 1 b)) (t : ℝ) : mellinI Φ a b t = mellinI Φ a k t + mellinI Φ k b t := by
  have hs1 : uIcc a k ⊆ Icc 1 b := by rw [uIcc_of_le hak]; exact Icc_subset_Icc ha hkb
  have hs2 : uIcc k b ⊆ Icc 1 b := by rw [uIcc_of_le hkb]; exact Icc_subset_Icc (ha.trans hak) le_rfl
  have hc1 : ContinuousOn (fun ξ => Φ ξ * ky t ξ) (Icc 1 b) := hΦ.mul (continuousOn_ky t b)
  have hc2 : ContinuousOn (fun ξ => Φ ξ * kys t ξ) (Icc 1 b) := hΦ.mul (continuousOn_kys t b)
  unfold mellinI
  rw [← intervalIntegral.integral_add_adjacent_intervals ((hc1.mono hs1).intervalIntegrable)
      ((hc1.mono hs2).intervalIntegrable),
    ← intervalIntegral.integral_add_adjacent_intervals ((hc2.mono hs1).intervalIntegrable)
      ((hc2.mono hs2).intervalIntegrable)]
  push_cast
  ring

/-- **The Dirichlet split of the far part**: for `1 ≤ k ≤ X` and `Φ` continuous on `[1, X]`, the transform of
`logScale (posTail Φ X − posTail Φ k)` at `t` is
`(Σ_{1≤m≤⌊k⌋} m^{−1/2+it})·I(k,X;t) + Σ_{⌊k⌋<m≤⌊X⌋} m^{−1/2+it}·I(m,X;t)`. -/
theorem fourier_far_eq (Φ : ℝ → ℝ) {k X : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X) (hΦ : ContinuousOn Φ (Icc 1 X)) (t : ℝ) :
    𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (logScale (posTail Φ X - posTail Φ k))) (t / (2 * π))
      = (∑ m ∈ Finset.Icc 1 ⌊k⌋₊, dch m t) * mellinI Φ k X t
        + ∑ m ∈ Finset.Ioc ⌊k⌋₊ ⌊X⌋₊, dch m t * mellinI Φ m X t := by
  have hX : 1 ≤ X := hk.trans hkX
  have hΦk : ContinuousOn Φ (Icc 1 k) := hΦ.mono (Icc_subset_Icc le_rfl hkX)
  have hF0 : ∀ θ ≤ 1, (posTail Φ X - posTail Φ k) θ = 0 := fun θ hθ => by
    simp [posTail_zero Φ X hθ, posTail_zero Φ k hθ]
  have iX1 := integrableOn_posTail_mul Φ hΦ (continuousOn_ky t X)
  have iX2 := integrableOn_posTail_mul Φ hΦ (continuousOn_kys t X)
  have ik1 := integrableOn_posTail_mul Φ hΦk (continuousOn_ky t k)
  have ik2 := integrableOn_posTail_mul Φ hΦk (continuousOn_kys t k)
  have hs1 : (fun θ => (posTail Φ X - posTail Φ k) θ * ky t θ)
      = fun θ => posTail Φ X θ * ky t θ - posTail Φ k θ * ky t θ := by funext θ; simp only [Pi.sub_apply]; ring
  have hs2 : (fun θ => (posTail Φ X - posTail Φ k) θ * kys t θ)
      = fun θ => posTail Φ X θ * kys t θ - posTail Φ k θ * kys t θ := by funext θ; simp only [Pi.sub_apply]; ring
  rw [fourier_eq _ hF0 t (by rw [hs1]; exact iX1.sub ik1) (by rw [hs2]; exact iX2.sub ik2), hs1, hs2,
    integral_sub iX1 ik1, integral_sub iX2 ik2]
  have eX := mellin_posTail_eq Φ hX hΦ t
  have ek := mellin_posTail_eq Φ hk hΦk t
  have hfl : ⌊k⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hkX
  have hsplit : ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, dch m t * mellinI Φ m X t
      = ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, dch m t * mellinI Φ m X t
        + ∑ m ∈ Finset.Ioc ⌊k⌋₊ ⌊X⌋₊, dch m t * mellinI Φ m X t := by
    have e : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
      ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [e, e, Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  have hlow : ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, dch m t * mellinI Φ m X t
      - ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, dch m t * mellinI Φ m k t
      = (∑ m ∈ Finset.Icc 1 ⌊k⌋₊, dch m t) * mellinI Φ k X t := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hmk : (m : ℝ) ≤ k := (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by linarith))
    rw [mellinI_add Φ hm1 hmk hkX hΦ t]
    ring
  push_cast
  calc ((∫ θ in Ioi 1, posTail Φ X θ * ky t θ : ℝ) : ℂ) - ((∫ θ in Ioi 1, posTail Φ k θ * ky t θ : ℝ) : ℂ)
        - Complex.I * (((∫ θ in Ioi 1, posTail Φ X θ * kys t θ : ℝ) : ℂ)
          - ((∫ θ in Ioi 1, posTail Φ k θ * kys t θ : ℝ) : ℂ))
      = (((∫ θ in Ioi 1, posTail Φ X θ * ky t θ : ℝ) : ℂ)
          - Complex.I * ((∫ θ in Ioi 1, posTail Φ X θ * kys t θ : ℝ) : ℂ))
        - (((∫ θ in Ioi 1, posTail Φ k θ * ky t θ : ℝ) : ℂ)
          - Complex.I * ((∫ θ in Ioi 1, posTail Φ k θ * kys t θ : ℝ) : ℂ)) := by ring
    _ = _ := by rw [eX, ek, hsplit, ← hlow]; ring

/-! ### Two elementary sums -/

/-- `Σ_{m=1}^{N} m^{−1/2} ≤ 2√N`. -/
theorem sum_inv_sqrt_Icc_le (N : ℕ) : ∑ m ∈ Finset.Icc 1 N, (√(m : ℝ))⁻¹ ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs := Real.sqrt_nonneg (n : ℝ)
    have hu : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hs2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hu2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    push_cast
    have key : 2 * √(n : ℝ) + (√((n : ℝ) + 1))⁻¹ ≤ 2 * √((n : ℝ) + 1) := by
      rw [← sub_nonneg]
      have e : 2 * √((n : ℝ) + 1) - (2 * √(n : ℝ) + (√((n : ℝ) + 1))⁻¹)
          = (2 * √((n : ℝ) + 1) ^ 2 - 2 * √(n : ℝ) * √((n : ℝ) + 1) - 1) / √((n : ℝ) + 1) := by
        field_simp
        ring
      rw [e]
      refine div_nonneg ?_ hu.le
      have h4 : (2 * √(n : ℝ) * √((n : ℝ) + 1)) ^ 2 ≤ (2 * √(n : ℝ) ^ 2 + 1) ^ 2 := by
        rw [mul_pow, mul_pow, hs2, hu2]; nlinarith
      have h5 : 2 * √(n : ℝ) * √((n : ℝ) + 1) ≤ 2 * √(n : ℝ) ^ 2 + 1 :=
        (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h4
      nlinarith
    linarith

/-- **`Σ_{1≤m≤k} m^{−1/2} ≤ 2√k`** for `k ≥ 0`. -/
theorem sum_inv_sqrt_le {k : ℝ} (hk : 0 ≤ k) : ∑ m ∈ Finset.Icc 1 ⌊k⌋₊, (√(m : ℝ))⁻¹ ≤ 2 * √k := by
  refine (sum_inv_sqrt_Icc_le _).trans ?_
  have := Real.sqrt_le_sqrt (Nat.floor_le hk)
  linarith

/-- `Σ_{n≤m<M} m^{−2} + 2/(2M−1) ≤ 2/(2n−1)` for `1 ≤ n ≤ M` (telescoping against `2/(2m−1) − 2/(2m+1)`). -/
theorem sum_inv_sq_Ico_add_le {n : ℕ} (hn : 1 ≤ n) {M : ℕ} (hnM : n ≤ M) :
    ∑ m ∈ Finset.Ico n M, ((m : ℝ) ^ 2)⁻¹ + 2 / (2 * (M : ℝ) - 1) ≤ 2 / (2 * (n : ℝ) - 1) := by
  induction M, hnM using Nat.le_induction with
  | base => simp
  | succ M hnM ih =>
    rw [Finset.sum_Ico_succ_top hnM]
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast hn.trans hnM
    have step : ((M : ℝ) ^ 2)⁻¹ + 2 / (2 * ((M + 1 : ℕ) : ℝ) - 1) ≤ 2 / (2 * (M : ℝ) - 1) := by
      push_cast
      rw [← sub_nonneg]
      have e : 2 / (2 * (M : ℝ) - 1) - (((M : ℝ) ^ 2)⁻¹ + 2 / (2 * ((M : ℝ) + 1) - 1))
          = 1 / ((M : ℝ) ^ 2 * (2 * M - 1) * (2 * M + 1)) := by
        have h1 : (2 * (M : ℝ) - 1) ≠ 0 := by linarith
        have h2 : (2 * ((M : ℝ) + 1) - 1) ≠ 0 := by linarith
        have h3 : (M : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      rw [e]
      have : 0 < (M : ℝ) ^ 2 * (2 * M - 1) * (2 * M + 1) := by
        have : 0 < 2 * (M : ℝ) - 1 := by linarith
        positivity
      positivity
    linarith

/-- `Σ_{n≤m<M} m^{−2} ≤ 2/(2n−1)` for `n ≥ 1`. -/
theorem sum_inv_sq_Ico_le {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    ∑ m ∈ Finset.Ico n M, ((m : ℝ) ^ 2)⁻¹ ≤ 2 / (2 * (n : ℝ) - 1) := by
  rcases le_or_gt n M with hnM | hMn
  · have h := sum_inv_sq_Ico_add_le hn hnM
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast hn.trans hnM
    have : 0 ≤ 2 / (2 * (M : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
    linarith
  · rw [Finset.Ico_eq_empty_of_le hMn.le, Finset.sum_empty]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (by norm_num) (by linarith)

/-- **`Σ_{m≥⌈k⌉} m^{−2} ≤ 3/(2k)`** for `k ≥ 2`, uniformly in the upper cutoff `M`. -/
theorem sum_inv_sq_ceil_le {k : ℝ} (hk : 2 ≤ k) (M : ℕ) :
    ∑ m ∈ Finset.Ico ⌈k⌉₊ M, ((m : ℝ) ^ 2)⁻¹ ≤ 3 / (2 * k) := by
  have hc : k ≤ ⌈k⌉₊ := Nat.le_ceil k
  have hc1 : 1 ≤ ⌈k⌉₊ := by
    have : (1 : ℝ) ≤ ⌈k⌉₊ := by linarith
    exact_mod_cast this
  refine (sum_inv_sq_Ico_le hc1 M).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **The far Dirichlet tail**: `Σ_{⌊k⌋<m≤M} m^{−2} ≤ 3/(2k)` for `k ≥ 2`. -/
theorem sum_inv_sq_far_le {k : ℝ} (hk : 2 ≤ k) (M : ℕ) :
    ∑ m ∈ Finset.Ioc ⌊k⌋₊ M, ((m : ℝ) ^ 2)⁻¹ ≤ 3 / (2 * k) := by
  have hsub : Finset.Ioc ⌊k⌋₊ M ⊆ Finset.Ico ⌈k⌉₊ (M + 1) := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_Ico]
    refine ⟨?_, by omega⟩
    have h1 : ⌈k⌉₊ ≤ ⌊k⌋₊ + 1 := Nat.ceil_le_floor_add_one k
    omega
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity) ?_
  exact sum_inv_sq_ceil_le hk (M + 1)

end Cvs.L2a.FarPartDirichletSplit
