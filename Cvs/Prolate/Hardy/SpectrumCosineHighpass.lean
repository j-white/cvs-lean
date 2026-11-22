import Mathlib
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.HighpassExtensionRung
import Cvs.Upstream.CosineTransformHalfLine
import Cvs.Upstream.FourierLpConjReflect
import Cvs.Upstream.HardyProjectionReal
import Cvs.Upstream.L2FourierIntegralL1L2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The real part of a function with spectrum in `[c/4π, ∞)` is cosine-highpass

`S_c g = ½(𝓕 H + 𝓕⁻ H̄)` with `H(x) = κ⁻¹ (1_I g)(x/κ)`, `κ = c/2π`, supported in `[−κ/2, κ/2]`; so Plancherel gives
`∫ Re(u) · S_c g = 0` when `𝓕 u = 0` a.e. on `(−∞, κ/2)`.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform

namespace Cvs.Prolate.Hardy.SpectrumCosineHighpass
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C specGe)
open Cvs.Upstream.FourierLpConjReflect (reflLp)
open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI synth)

/-- `H(x) = κ⁻¹ (1_I g)(κ⁻¹ x)`. -/
def bandH (κ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℂ := (κ⁻¹ : ℂ) * Cvs.Prolate.Hardy.CosineSynthesisPlancherel.ext g (κ⁻¹ * x)

theorem bandH_eq_indicator {κ : ℝ} (hκ : 0 < κ) (g : ℝ → ℝ) :
    bandH κ g = (Icc (-(κ / 2)) (κ / 2)).indicator fun x => (κ⁻¹ : ℂ) * (g (κ⁻¹ * x) : ℂ) := by
  ext x
  have hmem : κ⁻¹ * x ∈ cI ↔ x ∈ Icc (-(κ / 2)) (κ / 2) := by
    simp only [mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · have := mul_le_mul_of_nonneg_left h1 hκ.le
        rw [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] at this; linarith
      · have := mul_le_mul_of_nonneg_left h2 hκ.le
        rw [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] at this; linarith
    · rintro ⟨h1, h2⟩
      have hi : 0 < κ⁻¹ := inv_pos.2 hκ
      constructor
      · have := mul_le_mul_of_nonneg_left h1 hi.le
        rw [show κ⁻¹ * -(κ / 2) = -1 / 2 by field_simp] at this; exact this
      · have := mul_le_mul_of_nonneg_left h2 hi.le
        rw [show κ⁻¹ * (κ / 2) = 1 / 2 by field_simp] at this; exact this
  by_cases hx : x ∈ Icc (-(κ / 2)) (κ / 2)
  · rw [indicator_of_mem hx, bandH, Cvs.Prolate.Hardy.CosineSynthesisPlancherel.ext, indicator_of_mem (hmem.2 hx)]
  · rw [indicator_of_notMem hx, bandH, Cvs.Prolate.Hardy.CosineSynthesisPlancherel.ext, indicator_of_notMem (fun h => hx (hmem.1 h)), mul_zero]

theorem continuous_bandH_piece (κ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous fun x => (κ⁻¹ : ℂ) * (g (κ⁻¹ * x) : ℂ) := by fun_prop

theorem integrable_bandH {κ : ℝ} (hκ : 0 < κ) {g : ℝ → ℝ} (hg : Continuous g) : Integrable (bandH κ g) := by
  rw [bandH_eq_indicator hκ, integrable_indicator_iff measurableSet_Icc]
  exact (continuous_bandH_piece κ hg).continuousOn.integrableOn_compact isCompact_Icc

theorem memLp_bandH {κ : ℝ} (hκ : 0 < κ) {g : ℝ → ℝ} (hg : Continuous g) :
    MemLp (bandH κ g) 2 (volume : Measure ℝ) := by
  rw [bandH_eq_indicator hκ, memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_bandH_piece κ hg).continuousOn
    (s := Icc (-(κ / 2)) (κ / 2))
  refine MemLp.of_bound (continuous_bandH_piece κ hg).aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hM s hs

theorem bandH_vanish {κ : ℝ} (hκ : 0 < κ) (g : ℝ → ℝ) {x : ℝ} (hx : κ / 2 < |x|) : bandH κ g x = 0 := by
  rw [bandH_eq_indicator hκ, indicator_of_notMem]
  rw [mem_Icc, not_and_or, not_le, not_le]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx; exact Or.inr hx
  · rw [abs_of_neg h] at hx; exact Or.inl (by linarith)

/-- `𝓕 H (t) = 𝓕(1_I g)(κt)`. -/
theorem fourier_bandH {κ : ℝ} (hκ : 0 < κ) (g : ℝ → ℝ) (t : ℝ) : 𝓕 (bandH κ g) t = 𝓕 (Cvs.Prolate.Hardy.CosineSynthesisPlancherel.ext g) (κ * t) := by
  have h1 : 𝓕 (bandH κ g) t = (κ⁻¹ : ℂ) * 𝓕 (fun x => Cvs.Prolate.Hardy.CosineSynthesisPlancherel.ext g (κ⁻¹ * x)) t := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
    congr 1; ext v
    simp only [bandH, Circle.smul_def, smul_eq_mul]; ring
  rw [h1, Cvs.Upstream.CosineTransformHalfLine.fourier_comp_mul _ (inv_ne_zero hκ.ne'), inv_inv, abs_inv,
    abs_of_pos hκ, inv_inv, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ hκ.ne',
    Complex.ofReal_one, one_mul]

/-- `S_c g = ½(𝓕 H + 𝓕⁻ H̄)` pointwise, `κ = c/2π`. -/
theorem synth_eq_half {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    (synth c g t : ℂ) = (1 / 2 : ℂ) * (𝓕 (bandH (c / (2 * π)) g) t +
      𝓕⁻ (fun x => (starRingEnd ℂ) (bandH (c / (2 * π)) g x)) t) := by
  have hκ : 0 < c / (2 * π) := by positivity
  rw [Real.fourierInv_eq_fourier_neg, Cvs.Upstream.FourierLpConjReflect.fourier_conj_apply, neg_neg, Cvs.Prolate.Hardy.CosineSynthesisPlancherel.synth_eq_re c hg,
    Complex.re_eq_add_conj, fourier_bandH hκ]
  ring

/-- A pairing vanishes when, a.e., one of the two factors vanishes. -/
theorem inner_eq_zero_of_ae {a b : L2C} (h : ∀ᵐ x ∂volume, (a : ℝ → ℂ) x = 0 ∨ (b : ℝ → ℂ) x = 0) :
    inner ℂ a b = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h] with x hx
  rcases hx with hx | hx <;> simp [hx]

theorem inner_fourier_left (a b : L2C) : inner ℂ (𝓕 a : L2C) b = inner ℂ a (𝓕⁻ b : L2C) := by
  set E := Lp.fourierTransformₗᵢ ℝ ℂ
  change inner ℂ (E a) b = inner ℂ a (E.symm b)
  conv_lhs => rw [← E.apply_symm_apply b]
  exact E.inner_map_map a _

theorem inner_fourierInv_left (a b : L2C) : inner ℂ (𝓕⁻ a : L2C) b = inner ℂ a (𝓕 b : L2C) := by
  set E := Lp.fourierTransformₗᵢ ℝ ℂ
  change inner ℂ (E.symm a) b = inner ℂ a (E b)
  conv_rhs => rw [← E.apply_symm_apply a]
  exact (E.inner_map_map _ b).symm

theorem ae_ne (a : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a :=
  compl_mem_ae_iff.2 (measure_singleton a)

/-- **The real part of a function with spectrum in `[c/4π, ∞)` is orthogonal to every synthesis `S_c g`.** -/
theorem integral_re_mul_synth {c : ℝ} (hc : 0 < c) {u : L2C} (hu : u ∈ specGe (c / (4 * π))) {g : ℝ → ℝ}
    (hg : Continuous g) : ∫ t, ((u : ℝ → ℂ) t).re * synth c g t = 0 := by
  set κ := c / (2 * π) with hκdef
  have hκ : 0 < κ := by positivity
  have hβ : c / (4 * π) = κ / 2 := by rw [hκdef]; field_simp; ring
  rw [hβ] at hu
  set H := bandH κ g
  have hH1 : Integrable H := integrable_bandH hκ hg
  have hH2 : MemLp H 2 (volume : Measure ℝ) := memLp_bandH hκ hg
  set Ht : L2C := hH2.toLp H
  set Hc : L2C := Cvs.Upstream.FourierLpConjReflect.conjLp Ht
  have hHc1 : Integrable fun x => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (H x) :=
    ContinuousLinearMap.integrable_comp _ hH1
  have hHc2 : MemLp (fun x => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (H x)) 2 (volume : Measure ℝ) :=
    hH2.continuousLinearMap_comp _
  have hHc : Hc = hHc2.toLp _ := Cvs.Upstream.FourierLpConjReflect.conjLp_toLp hH2
  set Φ : L2C := (1 / 2 : ℂ) • ((𝓕 Ht : L2C) + 𝓕⁻ Hc)
  -- `Φ` is the synthesis
  have hΦ : (Φ : ℝ → ℂ) =ᵐ[volume] fun t => (synth c g t : ℂ) := by
    have hinv : (𝓕⁻ Hc : L2C) = reflLp (𝓕 Hc) := Cvs.Upstream.FourierLpConjReflect.fourierInv_eq Hc
    have h2 : ((𝓕 Hc : L2C) : ℝ → ℂ) =ᵐ[volume] 𝓕 fun x => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (H x) := by
      rw [hHc]; exact Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hHc1 hHc2
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) ((𝓕 Ht : L2C) + 𝓕⁻ Hc),
      Lp.coeFn_add (𝓕 Ht : L2C) (𝓕⁻ Hc), Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hH1 hH2,
      Cvs.Upstream.FourierLpConjReflect.coeFn_reflLp (𝓕 Hc : L2C), (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae h2]
      with t e1 e2 e3 e4 e5
    rw [e1, Pi.smul_apply, e2, Pi.add_apply, e3, hinv, e4, e5, synth_eq_half hc hg t, smul_eq_mul,
      Real.fourierInv_eq_fourier_neg]
    rfl
  -- the integral is the real part of `⟪Φ, u⟫`
  have hre : ∫ t, ((u : ℝ → ℂ) t).re * synth c g t = RCLike.re (inner ℂ Φ u) := by
    rw [L2.inner_def, ← integral_re (L2.integrable_inner Φ u)]
    refine integral_congr_ae ?_
    filter_upwards [hΦ] with t ht
    rw [ht]
    simp [mul_comm]
  -- the two pairings vanish
  have hFu := Cvs.Upstream.HardyProjectionReal.mem_specGe_iff.1 hu
  have p1 : inner ℂ (𝓕 Ht : L2C) u = 0 := by
    rw [inner_fourier_left, Cvs.Upstream.FourierLpConjReflect.fourierInv_eq u]
    refine inner_eq_zero_of_ae ?_
    filter_upwards [hH2.coeFn_toLp, Cvs.Upstream.FourierLpConjReflect.coeFn_reflLp (𝓕 u : L2C), Cvs.Upstream.HardyProjectionReal.vanish_neg hFu, ae_ne (-(κ / 2))]
      with x h1 h2 h3 h4
    by_cases hx : -x < κ / 2
    · exact Or.inr (by rw [h2]; exact h3 hx)
    · refine Or.inl ?_
      rw [h1]
      refine bandH_vanish hκ g ?_
      have : x < -(κ / 2) := lt_of_le_of_ne (by linarith) h4
      rw [abs_of_neg (by linarith)]; linarith
  have p2 : inner ℂ (𝓕⁻ Hc : L2C) u = 0 := by
    rw [inner_fourierInv_left, hHc]
    refine inner_eq_zero_of_ae ?_
    filter_upwards [hHc2.coeFn_toLp, hFu, ae_ne (κ / 2)] with x h1 h3 h4
    by_cases hx : x < κ / 2
    · exact Or.inr (h3 hx)
    · refine Or.inl ?_
      rw [h1]
      have : κ / 2 < x := lt_of_le_of_ne (not_lt.1 hx) (Ne.symm h4)
      have hv := bandH_vanish hκ g (x := x) (by rw [abs_of_pos (by linarith)]; exact this)
      change (starRingEnd ℂ) (H x) = 0
      rw [show H x = 0 from hv, map_zero]
  rw [hre, inner_smul_left, inner_add_left, p1, p2, add_zero, mul_zero, map_zero]

/-- The function `2 Re u` is cosine-highpass at `c` when `𝓕 u = 0` a.e. on `(−∞, c/4π)`. -/
theorem cosHighpass_two_re {c : ℝ} (hc : 0 < c) {u : L2C} (hu : u ∈ specGe (c / (4 * π))) {v : ℝ → ℝ}
    (hv : v =ᵐ[volume] fun t => 2 * ((u : ℝ → ℂ) t).re) : Cvs.Prolate.Hardy.HighpassExtensionRung.CosHighpass c v := by
  intro g hg
  have e : ∫ t, v t * synth c g t = ∫ t, 2 * (((u : ℝ → ℂ) t).re * synth c g t) := by
    refine integral_congr_ae ?_
    filter_upwards [hv] with t ht
    rw [ht]; ring
  rw [e, integral_const_mul, integral_re_mul_synth hc hu hg, mul_zero]

end Cvs.Prolate.Hardy.SpectrumCosineHighpass

end
