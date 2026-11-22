import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandTransferKernelForm
import Cvs.L2a.FarFarBound
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.Prolate.RungCauchySplit
import Cvs.Upstream.ExpDifferenceBound
import Cvs.Upstream.L2FourierIntegralL1L2
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.Upstream.QuinticSmoothStep

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The band form of the localised band transfer

A multiplier `μ(ξ) = μ̃(ξ/c)`, `C³` near `±[1, Y_max(x₀)]`, is cut by the quintic step to `m = μ̃·cut`; its kernel
`K = (2π)⁻¹∫e^{iξz}m` inverts to `m`, has `‖K‖₂² = (2π)⁻¹‖m‖₂²`, and moments bounded by `‖m^{(j)}‖₂`, so Cvs.L2a.BandTransferKernelForm gives
`|Σaₙ Sₙ[μ]|² ≤ (2π)⁻¹∫_B|μ|²·∫_{x₀−d}^{x₀+d}Φ² + ρ_T(c, x₀, d, δ; #ι)·c·‖μ̃‖²_{C³}·∫₁^∞Φ²` with `ρ_T` in closed form.
-/

namespace Cvs.L2a.BandTransferBandForm

open Complex Set MeasureTheory FourierTransform Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungCauchySplit Cvs.Upstream.ExpDifferenceBound Cvs.L2a.BandTransferKernelForm
open scoped Real ComplexConjugate

/-! ### The kernel of a compactly supported multiplier -/

section fourier

/-- Integration by parts under the Fourier integral: `𝓕F' = 2πiw·𝓕F` for `F` supported in `[L, R]`. -/
theorem fourier_deriv_eq {F F' : ℝ → ℂ} {L R : ℝ} {s : Set ℝ} (hLR : L ≤ R) (hs : s.Countable)
    (hF : Continuous F) (hd : ∀ x ∉ s, HasDerivAt F (F' x) x)
    (hF0 : ∀ x ∉ Ioo L R, F x = 0) (hF'0 : ∀ x ∉ Ioo L R, F' x = 0)
    (hF' : IntegrableOn F' (Icc L R)) (w : ℝ) :
    𝓕 F' w = (2 * π * I * w) * 𝓕 F w := by
  have hfull : ∀ G : ℝ → ℂ, (∀ x ∉ Ioo L R, G x = 0) → ∫ v, G v = ∫ v in L..R, G v := by
    intro G hG
    rw [intervalIntegral.integral_of_le hLR,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hG x fun h => hx (Ioo_subset_Ioc_self h)]
  set e : ℝ → ℂ := fun v => exp (((-2 * π * v * w : ℝ) : ℂ) * I) with he
  have hde : ∀ v, HasDerivAt e (e v * (((-2 * π * w : ℝ) : ℂ) * I)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => ((-2 * π * v * w : ℝ) : ℂ)) ((-2 * π * w : ℝ) : ℂ) v := by
      have := (((hasDerivAt_id v).const_mul (-2 * π)).mul_const w).ofReal_comp
      simpa using this
    exact (h1.mul_const I).cexp
  have hec : Continuous e := by rw [he]; fun_prop
  have hne : ∀ v, ‖e v‖ = 1 := fun v => norm_exp_ofReal_mul_I _
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [hfull _ fun x hx => by simp [hF'0 x hx], hfull _ fun x hx => by simp [hF0 x hx]]
  set G : ℝ → ℂ := fun v => e v * F v
  set G' : ℝ → ℂ := fun v => e v * F' v + e v * (((-2 * π * w : ℝ) : ℂ) * I) * F v
  have hGd : ∀ x ∈ Ioo L R \ s, HasDerivAt G (G' x) x := by
    intro x hx
    have := (hde x).mul (hd x hx.2)
    exact this.congr_deriv (by simp only [G']; ring)
  have hi1 : IntervalIntegrable (fun v => e v * F' v) volume L R := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hLR]
    exact hF'.bdd_mul (c := 1) hec.aestronglyMeasurable (ae_of_all _ fun v => (hne v).le)
  have hi2 : IntervalIntegrable (fun v => e v * (((-2 * π * w : ℝ) : ℂ) * I) * F v) volume L R :=
    ((hec.mul continuous_const).mul hF).intervalIntegrable _ _
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le G G' hLR hs
    ((hec.mul hF).continuousOn) hGd (hi1.add hi2)
  have hGL : G L = 0 := by simp [G, hF0 L (fun h => lt_irrefl _ h.1)]
  have hGR : G R = 0 := by simp [G, hF0 R (fun h => lt_irrefl _ h.2)]
  rw [hGL, hGR, sub_zero, intervalIntegral.integral_add hi1 hi2] at hftc
  have e2 : ∫ v in L..R, e v * (((-2 * π * w : ℝ) : ℂ) * I) * F v
      = (((-2 * π * w : ℝ) : ℂ) * I) * ∫ v in L..R, e v * F v := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; ext v; ring
  rw [e2] at hftc
  have : ∫ v in L..R, e v * F' v = -((((-2 * π * w : ℝ) : ℂ) * I) * ∫ v in L..R, e v * F v) :=
    eq_neg_of_add_eq_zero_left hftc
  rw [this]; push_cast; ring

/-- The kernel `K(z) = (2π)⁻¹∫e^{iξz}F(ξ)dξ` of a multiplier `F`. -/
noncomputable def kern (F : ℝ → ℂ) (z : ℝ) : ℂ := (((2 * π)⁻¹ : ℝ) : ℂ) * 𝓕 F (z / (-(2 * π)))

/-- **Moments are derivatives**: `z·K_F(z) = i·K_{F'}(z)` for `F` supported in `[L, R]`. -/
theorem mul_kern_eq {F F' : ℝ → ℂ} {L R : ℝ} {s : Set ℝ} (hLR : L ≤ R) (hs : s.Countable)
    (hF : Continuous F) (hd : ∀ x ∉ s, HasDerivAt F (F' x) x)
    (hF0 : ∀ x ∉ Ioo L R, F x = 0) (hF'0 : ∀ x ∉ Ioo L R, F' x = 0)
    (hF' : IntegrableOn F' (Icc L R)) (z : ℝ) :
    (z : ℂ) * kern F z = I * kern F' z := by
  unfold kern
  rw [fourier_deriv_eq hLR hs hF hd hF0 hF'0 hF' (z / (-(2 * π)))]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf
  rw [I_sq]; ring

theorem memLp_fourier {F : ℝ → ℂ} (hF : Integrable F) (hF2 : MemLp F 2) : MemLp (𝓕 F) 2 :=
  (Lp.memLp _).ae_eq (Cvs.Upstream.L2FourierIntegralL1L2.fourier_toLp_ae_eq hF hF2)

theorem continuous_kern {F : ℝ → ℂ} (hF : Integrable F) : Continuous (kern F) := by
  have h : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hF
  unfold kern
  fun_prop

theorem norm_kern_sq (F : ℝ → ℂ) (z : ℝ) :
    ‖kern F z‖ ^ 2 = ((2 * π)⁻¹) ^ 2 * ‖𝓕 F (z / (-(2 * π)))‖ ^ 2 := by
  unfold kern
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow]

theorem integrable_norm_kern_sq {F : ℝ → ℂ} (hF : Integrable F) (hF2 : MemLp F 2) :
    Integrable fun z => ‖kern F z‖ ^ 2 := by
  have h := (memLp_two_iff_integrable_sq_norm (memLp_fourier hF hF2).aestronglyMeasurable).mp (memLp_fourier hF hF2)
  have h2 := (h.comp_div (show (-(2 * π) : ℝ) ≠ 0 by have := Real.pi_pos; linarith)).const_mul
    (((2 * π)⁻¹) ^ 2)
  simpa only [norm_kern_sq] using h2

theorem memLp_kern {F : ℝ → ℂ} (hF : Integrable F) (hF2 : MemLp F 2) : MemLp (kern F) 2 :=
  (memLp_two_iff_integrable_sq_norm (continuous_kern hF).aestronglyMeasurable).mpr
    (integrable_norm_kern_sq hF hF2)

/-- **Plancherel for the kernel**: `∫‖K_F‖² = (2π)⁻¹∫‖F‖²` on `L¹ ∩ L²`. -/
theorem integral_norm_kern_sq {F : ℝ → ℂ} (hF : Integrable F) (hF2 : MemLp F 2) :
    ∫ z, ‖kern F z‖ ^ 2 = (2 * π)⁻¹ * ∫ ξ, ‖F ξ‖ ^ 2 := by
  simp_rw [norm_kern_sq]
  rw [integral_const_mul, Measure.integral_comp_div (fun w => ‖𝓕 F w‖ ^ 2) (-(2 * π)),
    Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_norm_sq_fourier hF hF2, abs_neg, abs_of_pos (by positivity),
    smul_eq_mul]
  have := Real.pi_pos
  field_simp

/-- **Inversion**: the kernel's transform `∫e^{−iξz}K_F(z)dz` is `F`, when `F` is continuous and `K_F ∈ L¹`. -/
theorem ft_kern {F : ℝ → ℂ} (hFc : Continuous F) (hF : Integrable F) (hK : Integrable (kern F))
    (ξ : ℝ) : Cvs.L2a.BandTransferKernelForm.ft (kern F) ξ = F ξ := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hFF : Integrable (𝓕 F) := by
    have h := (hK.comp_mul_left' (show (-(2 * π) : ℝ) ≠ 0 by linarith)).const_mul ((2 * π : ℝ) : ℂ)
    refine h.congr (ae_of_all _ fun w => ?_)
    simp only [kern]
    have : -(2 * π) * w / -(2 * π) = w := by field_simp
    rw [this, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hπ.ne', ofReal_one, one_mul]
  have hinv := congrFun (hFc.fourierInv_fourier_eq hF hFF) ξ
  rw [← hinv, Real.fourierInv_eq']
  unfold Cvs.L2a.BandTransferKernelForm.ft kern
  set H : ℝ → ℂ := fun v => exp (((2 * π * inner ℝ v ξ : ℝ) : ℂ) * I) • 𝓕 F v with hH
  have e : ∀ z : ℝ, exp (((-(ξ * z)) : ℝ) * I) * ((((2 * π)⁻¹ : ℝ) : ℂ) * 𝓕 F (z / (-(2 * π))))
      = (((2 * π)⁻¹ : ℝ) : ℂ) * H (z / (-(2 * π))) := by
    intro z
    simp only [hH, smul_eq_mul, RCLike.inner_apply, conj_trivial]
    have : 2 * π * (ξ * (z / -(2 * π))) = -(ξ * z) := by field_simp
    rw [this]; ring
  rw [integral_congr_ae (ae_of_all _ e), integral_const_mul, Measure.integral_comp_div H (-(2 * π)),
    abs_neg, abs_of_pos hπ, Complex.real_smul, ← mul_assoc, ← ofReal_mul, inv_mul_cancel₀ hπ.ne',
    ofReal_one, one_mul]

/-! ### `L¹` moments from `L²` moments -/

theorem integral_inv_add_sq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Integrable (fun z : ℝ => (α + β * z ^ 2)⁻¹) ∧ ∫ z : ℝ, (α + β * z ^ 2)⁻¹ = π / √(α * β) := by
  set r := √(β / α) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (div_pos hβ hα)
  have hr2 : r ^ 2 = β / α := Real.sq_sqrt (div_pos hβ hα).le
  have e : ∀ z : ℝ, (α + β * z ^ 2)⁻¹ = α⁻¹ * (1 + (r * z) ^ 2)⁻¹ := by
    intro z
    rw [mul_pow, hr2]; field_simp
  simp_rw [e]
  refine ⟨(integrable_inv_one_add_sq.comp_mul_left' hr0.ne').const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun z => (1 + z ^ 2)⁻¹) r,
    integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
  have hab : √(α * β) = α * r := by
    rw [show α * β = (α * r) ^ 2 by rw [mul_pow, hr2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [hab]; field_simp

/-- **`L¹` from two `L²` moments**: `∫f ≤ √(2π‖f‖₂‖zf‖₂)` for `f ≥ 0`, by Cauchy–Schwarz against `(α+βz²)^{-1/2}`. -/
theorem integral_le_moments {f : ℝ → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hfm : AEStronglyMeasurable f)
    (h0 : Integrable fun z => f z ^ 2) (h1 : Integrable fun z => z ^ 2 * f z ^ 2) :
    Integrable f ∧ ∫ z, f z ≤ √(2 * π * √(∫ z, f z ^ 2) * √(∫ z, z ^ 2 * f z ^ 2)) := by
  -- the pointwise AM–GM bound against the weight `α + βz²`
  have hpt : ∀ α β : ℝ, 0 < α → 0 < β → ∀ z,
      f z ≤ (α * f z ^ 2 + β * (z ^ 2 * f z ^ 2) + (α + β * z ^ 2)⁻¹) / 2 := by
    intro α β hα hβ z
    have hw : 0 < α + β * z ^ 2 := by positivity
    have : 2 * f z ≤ (α + β * z ^ 2) * f z ^ 2 + (α + β * z ^ 2)⁻¹ := by
      have h := sq_nonneg ((α + β * z ^ 2) * f z - 1)
      have : (α + β * z ^ 2) * ((α + β * z ^ 2) * f z ^ 2 + (α + β * z ^ 2)⁻¹ - 2 * f z)
          = ((α + β * z ^ 2) * f z - 1) ^ 2 := by field_simp; ring
      nlinarith
    nlinarith
  have hbound : ∀ α β : ℝ, 0 < α → 0 < β →
      Integrable (fun z => (α * f z ^ 2 + β * (z ^ 2 * f z ^ 2) + (α + β * z ^ 2)⁻¹) / 2) := by
    intro α β hα hβ
    exact (((h0.const_mul α).add (h1.const_mul β)).add (integral_inv_add_sq hα hβ).1).div_const 2
  have hint : Integrable f := by
    refine Integrable.mono' (hbound 1 1 one_pos one_pos) hfm (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]; exact hpt 1 1 one_pos one_pos z
  refine ⟨hint, ?_⟩
  set A := ∫ z, f z ^ 2
  set B := ∫ z, z ^ 2 * f z ^ 2
  have hA : 0 ≤ A := integral_nonneg fun z => sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun z => by positivity
  have hle : ∀ α β : ℝ, 0 < α → 0 < β → ∫ z, f z ≤ (α * A + β * B + π / √(α * β)) / 2 := by
    intro α β hα hβ
    refine (integral_mono hint (hbound α β hα hβ) (hpt α β hα hβ)).trans (le_of_eq ?_)
    have i12 : Integrable (fun z => α * f z ^ 2 + β * (z ^ 2 * f z ^ 2)) :=
      (h0.const_mul α).add (h1.const_mul β)
    rw [integral_div, integral_add i12 (integral_inv_add_sq hα hβ).1,
      integral_add (h0.const_mul α) (h1.const_mul β), integral_const_mul, integral_const_mul,
      (integral_inv_add_sq hα hβ).2]
  -- a vanishing moment forces `f = 0` a.e.
  have hzero : (A = 0 ∨ B = 0) → ∫ z, f z = 0 := by
    intro h
    have hf_ae : f =ᵐ[volume] 0 := by
      rcases h with h | h
      · have := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (f z)) h0).mp h
        filter_upwards [this] with z hz
        simpa using hz
      · have := (integral_eq_zero_iff_of_nonneg (fun z => by positivity) h1).mp h
        filter_upwards [this, Measure.ae_ne volume (0 : ℝ)] with z hz hz0
        simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true] at hz
        rcases hz with hz | hz
        · exact absurd hz hz0
        · exact hz
    rw [integral_congr_ae hf_ae]; simp
  by_cases hAB : A = 0 ∨ B = 0
  · rw [hzero hAB]; exact Real.sqrt_nonneg _
  simp only [not_or] at hAB
  have ha : 0 < √A := Real.sqrt_pos.mpr (lt_of_le_of_ne hA (Ne.symm hAB.1))
  have hb : 0 < √B := Real.sqrt_pos.mpr (lt_of_le_of_ne hB (Ne.symm hAB.2))
  set p := √(π * √A * √B / 2) with hp
  have hp0 : 0 < p := Real.sqrt_pos.mpr (by positivity)
  have hp2 : p ^ 2 = π * √A * √B / 2 := Real.sq_sqrt (by positivity)
  have hA2 : √A ^ 2 = A := Real.sq_sqrt hA
  have hB2 : √B ^ 2 = B := Real.sq_sqrt hB
  have h := hle (p / A) (p / B) (div_pos hp0 (by rw [← hA2]; positivity))
    (div_pos hp0 (by rw [← hB2]; positivity))
  have hsq : √(p / A * (p / B)) = p / (√A * √B) := by
    have : p / A * (p / B) = (p / (√A * √B)) ^ 2 := by rw [div_pow, mul_pow, hA2, hB2]; ring
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hsq, div_mul_cancel₀ _ hAB.1, div_mul_cancel₀ _ hAB.2] at h
  have h2p : π / (p / (√A * √B)) = 2 * p := by
    rw [div_div_eq_mul_div, eq_comm, eq_div_iff hp0.ne']; nlinarith [hp2]
  have hs : √(2 * π * √A * √B) = 2 * p := by
    rw [show 2 * π * √A * √B = (2 * p) ^ 2 by rw [mul_pow, hp2]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [h2p] at h
  rw [hs]; linarith

/-- **The tail mass**: `∫_{|z|>R} f ≤ √(∫z⁶f²)·√(2/(5R⁵))`. -/
theorem setIntegral_tail_le {f : ℝ → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hfm : AEStronglyMeasurable f)
    (h3 : Integrable fun z => z ^ 6 * f z ^ 2) {R : ℝ} (hR : 0 < R) :
    ∫ z in {z : ℝ | R < |z|}, f z ≤ √(∫ z, z ^ 6 * f z ^ 2) * √(2 / (5 * R ^ 5)) := by
  set T : Set ℝ := {z : ℝ | R < |z|}
  have hT : MeasurableSet T := measurableSet_lt measurable_const continuous_abs.measurable
  set w : ℝ → ℝ := fun z => (|z| ^ 3)⁻¹
  set u : ℝ → ℝ := fun z => |z| ^ 3 * f z
  have hw2 : ∀ z, w z ^ 2 = (|z| ^ 6)⁻¹ := fun z => by simp only [w]; rw [inv_pow, ← pow_mul]
  have hu2 : ∀ z, u z ^ 2 = z ^ 6 * f z ^ 2 := fun z => by
    simp only [u]; rw [mul_pow, ← pow_mul, show 3 * 2 = 6 by rfl, pow_abs, abs_of_nonneg (by positivity)]
  -- the weight's square integrates over the tail to `2/(5R⁵)`
  have hIoi : IntegrableOn (fun t : ℝ => t ^ (-6 : ℝ)) (Ioi R) := integrableOn_Ioi_rpow_of_lt (by norm_num) hR
  have hIoi' : ∫ t in Ioi R, t ^ (-6 : ℝ) = R ^ (-5 : ℝ) / 5 := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hR]; norm_num
  set G : ℝ → ℝ := (Ioi R).indicator (fun t : ℝ => t ^ (-6 : ℝ))
  have hGi : Integrable G := (integrable_indicator_iff measurableSet_Ioi).mpr hIoi
  have hrp : ∀ t : ℝ, 0 < t → t ^ (-6 : ℝ) = (t ^ 6)⁻¹ := fun t ht => by
    rw [Real.rpow_neg ht.le, show ((6 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hg : ∀ z, T.indicator (fun z => (|z| ^ 6)⁻¹) z = G z + G (-z) := by
    intro z
    simp only [G]
    by_cases h1 : R < z
    · rw [indicator_of_mem (show z ∈ T by show R < |z|; rw [abs_of_pos (hR.trans h1)]; exact h1),
        indicator_of_mem (show z ∈ Ioi R from h1), indicator_of_notMem (show -z ∉ Ioi R by
          simp only [mem_Ioi, not_lt]; linarith), add_zero, abs_of_pos (hR.trans h1), hrp z (hR.trans h1)]
    by_cases h2 : z < -R
    · rw [indicator_of_mem (show z ∈ T by show R < |z|; rw [abs_of_neg (by linarith)]; linarith),
        indicator_of_notMem (show z ∉ Ioi R from h1), indicator_of_mem (show -z ∈ Ioi R by
          simp only [mem_Ioi]; linarith), zero_add, abs_of_neg (by linarith), hrp (-z) (by linarith)]
    · rw [indicator_of_notMem (show z ∉ T by
          show ¬ R < |z|; rw [not_lt]; exact abs_le.mpr ⟨by linarith, by linarith⟩),
        indicator_of_notMem (show z ∉ Ioi R from h1), indicator_of_notMem (show -z ∉ Ioi R by
          simp only [mem_Ioi, not_lt]; linarith), add_zero]
  have hwT : ∫ z in T, w z ^ 2 = 2 / (5 * R ^ 5) := by
    simp_rw [hw2]
    rw [← integral_indicator hT]
    simp_rw [hg]
    rw [integral_add hGi hGi.comp_neg, integral_neg_eq_self G volume, integral_indicator measurableSet_Ioi,
      hIoi', Real.rpow_neg hR.le, show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp; norm_num
  have hwI : IntegrableOn (fun z => w z ^ 2) T := by
    simp_rw [hw2]
    rw [← integrable_indicator_iff hT, show T.indicator (fun z => (|z| ^ 6)⁻¹) = fun z => G z + G (-z)
      from funext hg]
    exact hGi.add hGi.comp_neg
  have hwm : AEStronglyMeasurable w (volume.restrict T) :=
    (by fun_prop : Measurable w).aestronglyMeasurable
  have hwL : MemLp w 2 (volume.restrict T) := by
    refine (memLp_two_iff_integrable_sq_norm hwm).mpr ?_
    simp only [Real.norm_eq_abs, sq_abs]; exact hwI
  have hum : AEStronglyMeasurable u := (continuous_abs.pow 3).aestronglyMeasurable.mul hfm
  have huL : MemLp u 2 := by
    refine (memLp_two_iff_integrable_sq_norm hum).mpr ?_
    simpa only [Real.norm_eq_abs, sq_abs, hu2] using h3
  have hcs := Cvs.L2a.FarFarBound.integral_mul_abs_le (μ := volume.restrict T) (fun z => by positivity)
    hwL (huL.restrict T)
  have hlhs : ∫ z in T, w z * |u z| = ∫ z in T, f z := by
    refine setIntegral_congr_fun hT fun z hz => ?_
    have hz0 : 0 < |z| := hR.trans hz
    simp only [w, u]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ |z| ^ 3), abs_of_nonneg (hf0 z)]
    field_simp
  rw [hlhs, hwT] at hcs
  refine hcs.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  simp_rw [hu2]
  exact setIntegral_le_integral h3 (ae_of_all _ fun z => by positivity)

end fourier

/-! ### The kernel of a profile -/

/-- The `L²` norm `‖F‖₂ = √(∫‖F‖²)`. -/
noncomputable def nrm (F : ℝ → ℂ) : ℝ := √(∫ ξ, ‖F ξ‖ ^ 2)

/-- A multiplier profile: `F ∈ C²` with `F″` piecewise `C¹` off a countable set, all supported in `[L, R]`. -/
structure IsProfile (m m₁ m₂ m₃ : ℝ → ℂ) (L R : ℝ) (s : Set ℝ) : Prop where
  le : L ≤ R
  countable : s.Countable
  d0 : ∀ x, HasDerivAt m (m₁ x) x
  d1 : ∀ x, HasDerivAt m₁ (m₂ x) x
  c2 : Continuous m₂
  d2 : ∀ x ∉ s, HasDerivAt m₂ (m₃ x) x
  supp : ∀ x ∉ Ioo L R, m x = 0 ∧ m₁ x = 0 ∧ m₂ x = 0 ∧ m₃ x = 0
  mem3 : MemLp m₃ 2

theorem integrable_of_supp {E : Type*} [NormedAddCommGroup E] {F : ℝ → E} {L R : ℝ} (hF : IntegrableOn F (Icc L R))
    (h0 : ∀ x ∉ Ioo L R, F x = 0) : Integrable F :=
  (integrableOn_iff_integrable_of_support_subset fun x hx => by
    by_contra h; exact hx (h0 x fun h' => h (Ioo_subset_Icc_self h'))).mp hF

theorem hasCompactSupport_of_supp {F : ℝ → ℂ} {L R : ℝ} (h0 : ∀ x ∉ Ioo L R, F x = 0) :
    HasCompactSupport F :=
  HasCompactSupport.intro isCompact_Icc fun x hx => h0 x fun h => hx (Ioo_subset_Icc_self h)

section profile

variable {m m₁ m₂ m₃ : ℝ → ℂ} {L R : ℝ} {s : Set ℝ}

theorem IsProfile.c0 (h : IsProfile m m₁ m₂ m₃ L R s) : Continuous m :=
  continuous_iff_continuousAt.mpr fun x => (h.d0 x).continuousAt

theorem IsProfile.c1 (h : IsProfile m m₁ m₂ m₃ L R s) : Continuous m₁ :=
  continuous_iff_continuousAt.mpr fun x => (h.d1 x).continuousAt

theorem IsProfile.int0 (h : IsProfile m m₁ m₂ m₃ L R s) : Integrable m ∧ MemLp m 2 :=
  ⟨h.c0.integrable_of_hasCompactSupport (hasCompactSupport_of_supp fun x hx => (h.supp x hx).1),
    h.c0.memLp_of_hasCompactSupport (hasCompactSupport_of_supp fun x hx => (h.supp x hx).1)⟩

theorem IsProfile.int1 (h : IsProfile m m₁ m₂ m₃ L R s) : Integrable m₁ ∧ MemLp m₁ 2 :=
  ⟨h.c1.integrable_of_hasCompactSupport (hasCompactSupport_of_supp fun x hx => (h.supp x hx).2.1),
    h.c1.memLp_of_hasCompactSupport (hasCompactSupport_of_supp fun x hx => (h.supp x hx).2.1)⟩

theorem IsProfile.int2 (h : IsProfile m m₁ m₂ m₃ L R s) : Integrable m₂ ∧ MemLp m₂ 2 :=
  ⟨h.c2.integrable_of_hasCompactSupport (hasCompactSupport_of_supp fun x hx => (h.supp x hx).2.2.1),
    h.c2.memLp_of_hasCompactSupport (hasCompactSupport_of_supp fun x hx => (h.supp x hx).2.2.1)⟩

theorem IsProfile.int3 (h : IsProfile m m₁ m₂ m₃ L R s) : Integrable m₃ ∧ MemLp m₃ 2 := by
  have : IsFiniteMeasure (volume.restrict (Icc L R)) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  exact ⟨integrable_of_supp ((h.mem3.restrict _).integrable one_le_two)
    fun x hx => (h.supp x hx).2.2.2, h.mem3⟩

/-- The three moment identities `|z|^j‖K_m‖ = ‖K_{m^{(j)}}‖`. -/
theorem IsProfile.abs_mul_norm_kern (h : IsProfile m m₁ m₂ m₃ L R s) (z : ℝ) :
    |z| * ‖kern m z‖ = ‖kern m₁ z‖ ∧ |z| * ‖kern m₁ z‖ = ‖kern m₂ z‖ ∧
      |z| * ‖kern m₂ z‖ = ‖kern m₃ z‖ := by
  have key : ∀ {F F' : ℝ → ℂ}, (z : ℂ) * kern F z = I * kern F' z → |z| * ‖kern F z‖ = ‖kern F' z‖ := by
    intro F F' he
    have := congrArg norm he
    rwa [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, one_mul] at this
  refine ⟨key (mul_kern_eq h.le countable_empty h.c0 (fun x _ => h.d0 x) (fun x hx => (h.supp x hx).1)
    (fun x hx => (h.supp x hx).2.1) h.int1.1.integrableOn z), key (mul_kern_eq h.le countable_empty h.c1
    (fun x _ => h.d1 x) (fun x hx => (h.supp x hx).2.1) (fun x hx => (h.supp x hx).2.2.1)
    h.int2.1.integrableOn z), key (mul_kern_eq h.le h.countable h.c2 h.d2 (fun x hx => (h.supp x hx).2.2.1)
    (fun x hx => (h.supp x hx).2.2.2) h.int3.1.integrableOn z)⟩

theorem sqrt_two_pi_mul (a b : ℝ) :
    √(2 * π * √((2 * π)⁻¹ * a) * √((2 * π)⁻¹ * b)) = √(√a * √b) := by
  congr 1
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have h := Real.mul_self_sqrt (show (0:ℝ) ≤ (2 * π)⁻¹ by positivity)
  have hπ : (2 * π) * (2 * π)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  calc 2 * π * (√(2 * π)⁻¹ * √a) * (√(2 * π)⁻¹ * √b) = 2 * π * (√(2 * π)⁻¹ * √(2 * π)⁻¹) * (√a * √b) := by ring
    _ = √a * √b := by rw [h, hπ, one_mul]

/-- **The kernel of a profile**: integrable with two moments, inverting to `m`, with Plancherel,
`∫|z||K| ≤ √(‖m′‖₂‖m″‖₂)`, `∫z²|K| ≤ √(‖m″‖₂‖m‴‖₂)` and `∫_{|z|>r}|K| ≤ ‖m‴‖₂/√(5πr⁵)`. -/
theorem IsProfile.kern_bounds (h : IsProfile m m₁ m₂ m₃ L R s) :
    Integrable (kern m) ∧ MemLp (kern m) 2 ∧ Integrable (fun z => |z| * ‖kern m z‖) ∧
      Integrable (fun z => z ^ 2 * ‖kern m z‖) ∧ (∀ ξ, Cvs.L2a.BandTransferKernelForm.ft (kern m) ξ = m ξ) ∧
      ∫ z, ‖kern m z‖ ^ 2 = (2 * π)⁻¹ * ∫ ξ, ‖m ξ‖ ^ 2 ∧
      ∫ z, |z| * ‖kern m z‖ ≤ √(nrm m₁ * nrm m₂) ∧ ∫ z, z ^ 2 * ‖kern m z‖ ≤ √(nrm m₂ * nrm m₃) ∧
      ∀ r, 0 < r → ∫ z in {z : ℝ | r < |z|}, ‖kern m z‖ ≤ nrm m₃ / √(5 * π * r ^ 5) := by
  obtain ⟨i0, l0⟩ := h.int0
  obtain ⟨i1, l1⟩ := h.int1
  obtain ⟨i2, l2⟩ := h.int2
  obtain ⟨i3, l3⟩ := h.int3
  have e1 : ∀ z, |z| * ‖kern m z‖ = ‖kern m₁ z‖ := fun z => (h.abs_mul_norm_kern z).1
  have e2 : ∀ z, |z| * ‖kern m₁ z‖ = ‖kern m₂ z‖ := fun z => (h.abs_mul_norm_kern z).2.1
  have e3 : ∀ z, |z| * ‖kern m₂ z‖ = ‖kern m₃ z‖ := fun z => (h.abs_mul_norm_kern z).2.2
  have hsq : ∀ {F G : ℝ → ℂ}, (∀ z, |z| * ‖kern F z‖ = ‖kern G z‖) →
      (fun z => z ^ 2 * ‖kern F z‖ ^ 2) = fun z => ‖kern G z‖ ^ 2 := by
    intro F G he; funext z; rw [← he, mul_pow, sq_abs]
  have z2 : ∀ z, z ^ 2 * ‖kern m z‖ = ‖kern m₂ z‖ := fun z => by
    rw [← e2, ← e1, ← mul_assoc, ← pow_two, sq_abs]
  have m0 := integral_le_moments (fun z => norm_nonneg (kern m z)) (continuous_kern i0).norm.aestronglyMeasurable
    (integrable_norm_kern_sq i0 l0) (by rw [hsq e1]; exact integrable_norm_kern_sq i1 l1)
  have m1 := integral_le_moments (fun z => norm_nonneg (kern m₁ z))
    (continuous_kern i1).norm.aestronglyMeasurable
    (integrable_norm_kern_sq i1 l1) (by rw [hsq e2]; exact integrable_norm_kern_sq i2 l2)
  have m2 := integral_le_moments (fun z => norm_nonneg (kern m₂ z))
    (continuous_kern i2).norm.aestronglyMeasurable
    (integrable_norm_kern_sq i2 l2) (by rw [hsq e3]; exact integrable_norm_kern_sq i3 l3)
  have hK : Integrable (kern m) := (integrable_norm_iff (continuous_kern i0).aestronglyMeasurable).mp m0.1
  have n0 : ∀ F : ℝ → ℂ, 0 ≤ ∫ ξ, ‖F ξ‖ ^ 2 := fun F => integral_nonneg fun ξ => sq_nonneg _
  refine ⟨hK, memLp_kern i0 l0, by simp_rw [e1]; exact m1.1, by simp_rw [z2]; exact m2.1,
    ft_kern h.c0 i0 hK, integral_norm_kern_sq i0 l0, ?_, ?_, ?_⟩
  · simp_rw [e1]
    refine m1.2.trans (le_of_eq ?_)
    rw [hsq e2, integral_norm_kern_sq i1 l1, integral_norm_kern_sq i2 l2, sqrt_two_pi_mul _ _]
    rfl
  · simp_rw [z2]
    refine m2.2.trans (le_of_eq ?_)
    rw [hsq e3, integral_norm_kern_sq i2 l2, integral_norm_kern_sq i3 l3, sqrt_two_pi_mul _ _]
    rfl
  · intro r hr
    have h6 : (fun z => z ^ 6 * ‖kern m z‖ ^ 2) = fun z => ‖kern m₃ z‖ ^ 2 := by
      funext z
      rw [← e3, ← e2, ← e1]
      rw [show z ^ 6 = (|z| ^ 2) ^ 3 by rw [sq_abs, ← pow_mul]]
      ring
    have ht := setIntegral_tail_le (fun z => norm_nonneg (kern m z))
      (continuous_kern i0).norm.aestronglyMeasurable (by rw [h6]; exact integrable_norm_kern_sq i3 l3) hr
    refine ht.trans (le_of_eq ?_)
    rw [h6, integral_norm_kern_sq i3 l3, ← Real.sqrt_mul (by positivity), nrm, ← Real.sqrt_div (n0 _)]
    congr 1
    have := Real.pi_pos
    field_simp

end profile

/-! ### The span transfer through a profile -/

/-- The rung sample `S[μ] = μ(k)ψ⁺(x₀) + μ(−k)ψ⁻(x₀)` of a multiplier `μ`, with `k = k(x₀)`. -/
noncomputable def smp (μ : ℝ → ℂ) (c χ : ℝ) (g : ℝ → ℝ) (x₀ : ℝ) : ℂ :=
  μ (kP c χ x₀) * psiP c χ g x₀ + μ (-kP c χ x₀) * conj (psiP c χ g x₀)

/-- The transfer constant in `L²` terms: `2β_W e^{β_W d}√(ℓ₁ℓ₂) + (c/2)Y'_W√(ℓ₂ℓ₃) + (e^{2β_W d}+1)ℓ₃/√(5π(d/2)⁵)`. -/
noncomputable def tauL (c x₀ d l₁ l₂ l₃ : ℝ) : ℝ :=
  2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * √(l₁ * l₂) + c / 2 * chirpW x₀ d * √(l₂ * l₃)
    + (Real.exp (2 * betaW x₀ d * d) + 1) * (l₃ / √(5 * π * (d / 2) ^ 5))

theorem isWindow_indicator {x₀ d : ℝ} (hd : 0 ≤ d) :
    IsWindow ((Icc (x₀ - d) (x₀ + d)).indicator fun _ => 1) x₀ d where
  meas := measurable_const.indicator measurableSet_Icc
  nonneg x := indicator_nonneg (fun _ _ => zero_le_one) x
  le_one x := by
    by_cases h : x ∈ Icc (x₀ - d) (x₀ + d)
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]; exact zero_le_one
  eq_one x hx := indicator_of_mem (show x ∈ Icc (x₀ - d) (x₀ + d) by
    constructor <;> linarith [abs_le.mp hx]) _
  eq_zero x hx := indicator_of_notMem (fun h => by
    have := abs_le.mpr (show -d ≤ x - x₀ ∧ x - x₀ ≤ d by constructor <;> linarith [h.1, h.2]); linarith) _

/-- **LBT-h through a profile**: if `m = μ` on `±[c, cY_max(x₀)]`, then `|Σaₙ Sₙ[μ]| ≤ √((2π)⁻¹∫|m|²)·‖Φ‖_{L²(x₀±d)}
+ τ_L(‖m′‖₂, ‖m″‖₂, ‖m‴‖₂)·√(6J/(x₀²−1))·√P`. -/
theorem lbt_profile {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {X x₀ d : ℝ} {μ m m₁ m₂ m₃ : ℝ → ℂ} {L R : ℝ} {s : Set ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hx₀ : x₀ ∈ Icc (6 / 5 : ℝ) X)
    (hd : 0 < d) (hxd : 1 < x₀ - d) (hm : IsProfile m m₁ m₂ m₃ L R s)
    (hband : ∀ ξ, |ξ| ∈ Icc c (c * Cvs.L2a.OrbitGapIntegerM.Ymax x₀) → m ξ = μ ξ) :
    ‖∑ i, (a i : ℂ) * smp μ c (χ i) (g i) x₀‖
      ≤ √((2 * π)⁻¹ * ∫ ξ, ‖m ξ‖ ^ 2) * √(∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + tauL c x₀ d (nrm m₁) (nrm m₂) (nrm m₃) * √(6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1))
          * √(∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) := by
  obtain ⟨hK, hKL2, hK₁, hK₂, hft, hpl, hm1, hm2, htail⟩ := hm.kern_bounds
  have hc0 : 0 < c := by linarith
  have hω := isWindow_indicator (x₀ := x₀) hd.le
  have hmain := lbt_kernel a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hx₀ hd.le hxd hω hK hKL2 hK₁ hK₂
  -- the samples of the kernel are the samples of `μ`
  have hsm : ∀ i, sample (kern m) c (χ i) (g i) x₀ = smp μ c (χ i) (g i) x₀ := by
    intro i
    have hk := kP_mem_Icc (lt_of_lt_of_le (by norm_num) hx₀.1) hc0 (hχ0 i) (hχc i)
    have hk0 : 0 ≤ kP c (χ i) x₀ := hc0.le.trans hk.1
    unfold sample smp
    rw [hft, hft, hband _ (by rw [abs_of_nonneg hk0]; exact hk),
      hband _ (by rw [abs_neg, abs_of_nonneg hk0]; exact hk)]
  simp_rw [hsm] at hmain
  -- the windowed span is the span on `[x₀ − d, x₀ + d]`
  have hwin : ∫ x, ((Icc (x₀ - d) (x₀ + d)).indicator (fun _ => (1 : ℝ)) x * ∑ i, a i * psi c (g i) x) ^ 2
      = ∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2 := by
    have e : ∀ x, ((Icc (x₀ - d) (x₀ + d)).indicator (fun _ => (1 : ℝ)) x * ∑ i, a i * psi c (g i) x) ^ 2
        = (Icc (x₀ - d) (x₀ + d)).indicator (fun x => (∑ i, a i * psi c (g i) x) ^ 2) x := by
      intro x
      by_cases h : x ∈ Icc (x₀ - d) (x₀ + d)
      · rw [indicator_of_mem h, indicator_of_mem h, one_mul]
      · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]; ring
    simp_rw [e]
    rw [integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc]
  rw [hwin, hpl] at hmain
  refine hmain.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
  -- the transfer constant through the moment bounds
  have hb := betaW_nonneg hxd
  have hy := chirpW_nonneg hd.le hxd
  unfold tauK tauL
  have hT := htail (d / 2) (by linarith)
  gcongr

/-! ### The quintic band cutoff -/

section cutoff

open Cvs.Upstream.QuinticSmoothStep

/-- The rising collar coordinate `(η − (1 − δ))/δ`. -/
noncomputable def up (δ η : ℝ) : ℝ := (η - (1 - δ)) / δ

/-- The falling collar coordinate `(Y + δ − η)/δ`. -/
noncomputable def dn (δ Y η : ℝ) : ℝ := (Y + δ - η) / δ

/-- The band cutoff: `1` on `±[1, Y]`, quintic collars of width `δ`, `0` off `±(1 − δ, Y + δ)`. -/
noncomputable def cut (δ Y η : ℝ) : ℝ :=
  S (up δ η) + S (dn δ Y η) + S (up δ (-η)) + S (dn δ Y (-η)) - 2

noncomputable def cut1 (δ Y η : ℝ) : ℝ :=
  (dS (up δ η) - dS (dn δ Y η) - dS (up δ (-η)) + dS (dn δ Y (-η))) / δ

noncomputable def cut2 (δ Y η : ℝ) : ℝ :=
  (d2S (up δ η) + d2S (dn δ Y η) + d2S (up δ (-η)) + d2S (dn δ Y (-η))) / δ ^ 2

noncomputable def cut3 (δ Y η : ℝ) : ℝ :=
  (d3S (up δ η) - d3S (dn δ Y η) - d3S (up δ (-η)) + d3S (dn δ Y (-η))) / δ ^ 3

/-- The eight collar endpoints, where `cut″` has corners. -/
def corners (δ Y : ℝ) : Set ℝ := {1 - δ, 1, Y, Y + δ, -(1 - δ), -1, -Y, -(Y + δ)}

/-- The quintic step cut to `(0, 1)`: `S` there and `0` elsewhere. -/
noncomputable def qS (u : ℝ) : ℝ := glue (fun _ => 0) quintic (fun _ => 0) u

theorem derivs_zero {u : ℝ} (h : u ≤ 0 ∨ 1 ≤ u) : dS u = 0 ∧ d2S u = 0 ∧ d3S u = 0 := by
  rcases h with h | h
  · exact ⟨glue_of_nonpos _ _ _ h, glue_of_nonpos _ _ _ h, glue_of_nonpos _ _ _ h⟩
  · exact ⟨glue_of_one_le _ _ _ h, glue_of_one_le _ _ _ h, glue_of_one_le _ _ _ h⟩

theorem S_eq_qS {u : ℝ} (hu : u < 1) : S u = qS u := by
  rcases le_or_gt u 0 with h | h
  · rw [S_of_nonpos h, qS, glue_of_nonpos _ _ _ h]
  · rw [S, qS, glue_of_mem_Ioo _ _ _ ⟨h, hu⟩, glue_of_mem_Ioo _ _ _ ⟨h, hu⟩]

section geometry

variable {δ Y η : ℝ}

theorem up_nonpos (hδ : 0 < δ) (h : η ≤ 1 - δ) : up δ η ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le

theorem one_le_up (hδ : 0 < δ) (h : 1 ≤ η) : 1 ≤ up δ η := by
  rw [up, le_div_iff₀ hδ]; linarith

theorem one_le_dn (hδ : 0 < δ) (h : η ≤ Y) : 1 ≤ dn δ Y η := by
  rw [dn, le_div_iff₀ hδ]; linarith

theorem dn_nonpos (hδ : 0 < δ) (h : Y + δ ≤ η) : dn δ Y η ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le

theorem up_lt_one (hδ : 0 < δ) (h : η < 1) : up δ η < 1 := by
  rw [up, div_lt_iff₀ hδ]; linarith

theorem dn_lt_one (hδ : 0 < δ) (h : Y < η) : dn δ Y η < 1 := by
  rw [dn, div_lt_iff₀ hδ]; linarith

/-- On `[0, Y]` only the rising right collar is active. -/
theorem cut_reg1 (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h0 : 0 ≤ η) (hη : η ≤ Y) :
    cut δ Y η = S (up δ η) ∧ cut1 δ Y η = dS (up δ η) / δ ∧ cut2 δ Y η = d2S (up δ η) / δ ^ 2 ∧
      cut3 δ Y η = d3S (up δ η) / δ ^ 3 := by
  have h2 := one_le_dn (Y := Y) hδ hη
  have h3 := up_nonpos (η := -η) hδ (by linarith)
  have h4 := one_le_dn (Y := Y) (η := -η) hδ (by linarith)
  obtain ⟨a2, b2, c2⟩ := derivs_zero (Or.inr h2)
  obtain ⟨a3, b3, c3⟩ := derivs_zero (Or.inl h3)
  obtain ⟨a4, b4, c4⟩ := derivs_zero (Or.inr h4)
  simp only [cut, cut1, cut2, cut3, S_of_one_le h2, S_of_nonpos h3, S_of_one_le h4, a2, b2, c2, a3, b3, c3,
    a4, b4, c4]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- On `[1, ∞)` only the falling right collar is active. -/
theorem cut_reg2 (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y) (hη : 1 ≤ η) :
    cut δ Y η = S (dn δ Y η) ∧ cut1 δ Y η = -dS (dn δ Y η) / δ ∧ cut2 δ Y η = d2S (dn δ Y η) / δ ^ 2 ∧
      cut3 δ Y η = -d3S (dn δ Y η) / δ ^ 3 := by
  have h1 := one_le_up hδ hη
  have h3 := up_nonpos (η := -η) hδ (by linarith)
  have h4 := one_le_dn (Y := Y) (η := -η) hδ (by linarith)
  obtain ⟨a1, b1, c1⟩ := derivs_zero (Or.inr h1)
  obtain ⟨a3, b3, c3⟩ := derivs_zero (Or.inl h3)
  obtain ⟨a4, b4, c4⟩ := derivs_zero (Or.inr h4)
  simp only [cut, cut1, cut2, cut3, S_of_one_le h1, S_of_nonpos h3, S_of_one_le h4, a1, b1, c1, a3, b3, c3,
    a4, b4, c4]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- On `[−Y, 0]` only the rising left collar is active. -/
theorem cut_reg3 (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y) (h0 : η ≤ 0) (hη : -Y ≤ η) :
    cut δ Y η = S (up δ (-η)) ∧ cut1 δ Y η = -dS (up δ (-η)) / δ ∧
      cut2 δ Y η = d2S (up δ (-η)) / δ ^ 2 ∧ cut3 δ Y η = -d3S (up δ (-η)) / δ ^ 3 := by
  have h1 := up_nonpos (η := η) hδ (by linarith)
  have h2 := one_le_dn (Y := Y) (η := η) hδ (by linarith)
  have h4 := one_le_dn (Y := Y) (η := -η) hδ (by linarith)
  obtain ⟨a1, b1, c1⟩ := derivs_zero (Or.inl h1)
  obtain ⟨a2, b2, c2⟩ := derivs_zero (Or.inr h2)
  obtain ⟨a4, b4, c4⟩ := derivs_zero (Or.inr h4)
  simp only [cut, cut1, cut2, cut3, S_of_nonpos h1, S_of_one_le h2, S_of_one_le h4, a1, b1, c1, a2, b2, c2,
    a4, b4, c4]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- On `(−∞, −1]` only the falling left collar is active. -/
theorem cut_reg4 (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y) (hη : η ≤ -1) :
    cut δ Y η = S (dn δ Y (-η)) ∧ cut1 δ Y η = dS (dn δ Y (-η)) / δ ∧
      cut2 δ Y η = d2S (dn δ Y (-η)) / δ ^ 2 ∧ cut3 δ Y η = d3S (dn δ Y (-η)) / δ ^ 3 := by
  have h1 := up_nonpos (η := η) hδ (by linarith)
  have h2 := one_le_dn (Y := Y) (η := η) hδ (by linarith)
  have h3 := one_le_up (η := -η) hδ (by linarith)
  obtain ⟨a1, b1, c1⟩ := derivs_zero (Or.inl h1)
  obtain ⟨a2, b2, c2⟩ := derivs_zero (Or.inr h2)
  obtain ⟨a3, b3, c3⟩ := derivs_zero (Or.inr h3)
  simp only [cut, cut1, cut2, cut3, S_of_nonpos h1, S_of_one_le h2, S_of_one_le h3, a1, b1, c1, a2, b2, c2,
    a3, b3, c3]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- `cut = 1` on the band `±[1, Y]`. -/
theorem cut_eq_one (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y) (h : |η| ∈ Icc 1 Y) : cut δ Y η = 1 := by
  rcases le_or_gt 0 η with h0 | h0
  · rw [abs_of_nonneg h0] at h
    rw [(cut_reg1 hδ hδ1 h0 h.2).1, S_of_one_le (one_le_up hδ h.1)]
  · rw [abs_of_neg h0] at h
    rw [(cut_reg3 hδ hδ1 hY h0.le (by linarith [h.2])).1, S_of_one_le (one_le_up hδ h.1)]

/-- The cutoff and its derivatives vanish off `±(1 − δ, Y + δ)`. -/
theorem cut_eq_zero (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y) (h : |η| ∉ Ioo (1 - δ) (Y + δ)) :
    cut δ Y η = 0 ∧ cut1 δ Y η = 0 ∧ cut2 δ Y η = 0 ∧ cut3 δ Y η = 0 := by
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
  rcases le_or_gt 0 η with h0 | h0
  · rw [abs_of_nonneg h0] at h
    rcases h with h | h
    · obtain ⟨e0, e1, e2, e3⟩ := cut_reg1 (Y := Y) hδ hδ1 h0 (by linarith)
      obtain ⟨z1, z2, z3⟩ := derivs_zero (Or.inl (up_nonpos hδ h))
      rw [e0, e1, e2, e3, S_of_nonpos (up_nonpos hδ h), z1, z2, z3]; simp
    · obtain ⟨e0, e1, e2, e3⟩ := cut_reg2 (Y := Y) hδ hδ1 hY (by linarith)
      obtain ⟨z1, z2, z3⟩ := derivs_zero (Or.inl (dn_nonpos hδ h))
      rw [e0, e1, e2, e3, S_of_nonpos (dn_nonpos hδ h), z1, z2, z3]; simp
  · rw [abs_of_neg h0] at h
    rcases h with h | h
    · obtain ⟨e0, e1, e2, e3⟩ := cut_reg3 (Y := Y) hδ hδ1 hY h0.le (by linarith)
      obtain ⟨z1, z2, z3⟩ := derivs_zero (Or.inl (up_nonpos hδ h))
      rw [e0, e1, e2, e3, S_of_nonpos (up_nonpos hδ h), z1, z2, z3]; simp
    · obtain ⟨e0, e1, e2, e3⟩ := cut_reg4 (Y := Y) hδ hδ1 hY (by linarith)
      obtain ⟨z1, z2, z3⟩ := derivs_zero (Or.inl (dn_nonpos hδ h))
      rw [e0, e1, e2, e3, S_of_nonpos (dn_nonpos hδ h), z1, z2, z3]; simp

theorem cut_mem_Icc (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y) (η : ℝ) : cut δ Y η ∈ Icc (0 : ℝ) 1 := by
  rcases le_or_gt 0 η with h0 | h0
  · rcases le_or_gt η Y with h | h
    · rw [(cut_reg1 hδ hδ1 h0 h).1]; exact S_mem_Icc _
    · rw [(cut_reg2 hδ hδ1 hY (by linarith)).1]; exact S_mem_Icc _
  · rcases le_or_gt (-Y) η with h | h
    · rw [(cut_reg3 hδ hδ1 hY h0.le h).1]; exact S_mem_Icc _
    · rw [(cut_reg4 hδ hδ1 hY (by linarith)).1]; exact S_mem_Icc _

/-- Off the band, `cut² ≤ Σ q(Aₖ)²` over the four collar coordinates. -/
theorem cut_sq_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y) (h : |η| ∉ Icc 1 Y) :
    cut δ Y η ^ 2 ≤ qS (up δ η) ^ 2 + qS (dn δ Y η) ^ 2 + qS (up δ (-η)) ^ 2 + qS (dn δ Y (-η)) ^ 2 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  have p1 := sq_nonneg (qS (up δ η)); have p2 := sq_nonneg (qS (dn δ Y η))
  have p3 := sq_nonneg (qS (up δ (-η))); have p4 := sq_nonneg (qS (dn δ Y (-η)))
  rcases le_or_gt 0 η with h0 | h0
  · rw [abs_of_nonneg h0] at h
    rcases h with h | h
    · rw [(cut_reg1 (Y := Y) hδ hδ1 h0 (by linarith)).1, S_eq_qS (up_lt_one hδ h)]; linarith
    · rw [(cut_reg2 hδ hδ1 hY (by linarith)).1, S_eq_qS (dn_lt_one hδ h)]; linarith
  · rw [abs_of_neg h0] at h
    rcases h with h | h
    · rw [(cut_reg3 hδ hδ1 hY h0.le (by linarith)).1, S_eq_qS (up_lt_one hδ h)]; linarith
    · rw [(cut_reg4 hδ hδ1 hY (by linarith)).1, S_eq_qS (dn_lt_one hδ (by linarith))]; linarith

/-- For a profile vanishing off `(0, 1)`, the four collar terms have disjoint supports. -/
theorem collar_sq {F : ℝ → ℝ} (hF : ∀ u, (u ≤ 0 ∨ 1 ≤ u) → F u = 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hY : 1 ≤ Y) (ε₁ ε₂ ε₃ ε₄ : ℝ) (hε : ε₁ ^ 2 = 1 ∧ ε₂ ^ 2 = 1 ∧ ε₃ ^ 2 = 1 ∧ ε₄ ^ 2 = 1) :
    (ε₁ * F (up δ η) + ε₂ * F (dn δ Y η) + ε₃ * F (up δ (-η)) + ε₄ * F (dn δ Y (-η))) ^ 2
      = F (up δ η) ^ 2 + F (dn δ Y η) ^ 2 + F (up δ (-η)) ^ 2 + F (dn δ Y (-η)) ^ 2 := by
  obtain ⟨e1, e2, e3, e4⟩ := hε
  rcases le_or_gt 0 η with h0 | h0
  · rcases le_or_gt η Y with h | h
    · rw [hF (dn δ Y η) (Or.inr (one_le_dn hδ h)), hF (up δ (-η)) (Or.inl (up_nonpos hδ (by linarith))),
        hF (dn δ Y (-η)) (Or.inr (one_le_dn hδ (by linarith)))]
      linear_combination F (up δ η) ^ 2 * e1
    · rw [hF (up δ η) (Or.inr (one_le_up hδ (by linarith))),
        hF (up δ (-η)) (Or.inl (up_nonpos hδ (by linarith))),
        hF (dn δ Y (-η)) (Or.inr (one_le_dn hδ (by linarith)))]
      linear_combination F (dn δ Y η) ^ 2 * e2
  · rcases le_or_gt (-Y) η with h | h
    · rw [hF (up δ η) (Or.inl (up_nonpos hδ (by linarith))), hF (dn δ Y η) (Or.inr (one_le_dn hδ (by linarith))),
        hF (dn δ Y (-η)) (Or.inr (one_le_dn hδ (by linarith)))]
      linear_combination F (up δ (-η)) ^ 2 * e3
    · rw [hF (up δ η) (Or.inl (up_nonpos hδ (by linarith))), hF (dn δ Y η) (Or.inr (one_le_dn hδ (by linarith))),
        hF (up δ (-η)) (Or.inr (one_le_up hδ (by linarith)))]
      linear_combination F (dn δ Y (-η)) ^ 2 * e4

theorem hasDerivAt_up (δ η : ℝ) : HasDerivAt (up δ) (1 / δ) η :=
  ((hasDerivAt_id η).sub_const (1 - δ)).div_const δ

theorem hasDerivAt_up_neg (δ η : ℝ) : HasDerivAt (fun η => up δ (-η)) (-1 / δ) η :=
  ((hasDerivAt_neg η).sub_const (1 - δ)).div_const δ

theorem hasDerivAt_dn (δ Y η : ℝ) : HasDerivAt (dn δ Y) (-1 / δ) η :=
  ((hasDerivAt_id η).const_sub (Y + δ)).div_const δ

theorem hasDerivAt_dn_neg (δ Y η : ℝ) : HasDerivAt (fun η => dn δ Y (-η)) (1 / δ) η :=
  (((hasDerivAt_neg η).const_sub (Y + δ)).div_const δ).congr_deriv (by ring)

theorem hasDerivAt_cut (hδ : 0 < δ) (η : ℝ) : HasDerivAt (cut δ Y) (cut1 δ Y η) η := by
  have := (((((hasDerivAt_S _).comp η (hasDerivAt_up δ η)).add ((hasDerivAt_S _).comp η
    (hasDerivAt_dn δ Y η))).add ((hasDerivAt_S _).comp η (hasDerivAt_up_neg δ η))).add
    ((hasDerivAt_S _).comp η (hasDerivAt_dn_neg δ Y η))).sub_const 2
  refine this.congr_deriv ?_
  simp only [cut1]; field_simp; ring

theorem hasDerivAt_cut1 (hδ : 0 < δ) (η : ℝ) : HasDerivAt (cut1 δ Y) (cut2 δ Y η) η := by
  have := (((((hasDerivAt_dS _).comp η (hasDerivAt_up δ η)).sub ((hasDerivAt_dS _).comp η
    (hasDerivAt_dn δ Y η))).sub ((hasDerivAt_dS _).comp η (hasDerivAt_up_neg δ η))).add
    ((hasDerivAt_dS _).comp η (hasDerivAt_dn_neg δ Y η))).div_const δ
  refine this.congr_deriv ?_
  simp only [cut2]; field_simp; ring

theorem hasDerivAt_cut2 (hδ : 0 < δ) {η : ℝ} (hη : η ∉ corners δ Y) :
    HasDerivAt (cut2 δ Y) (cut3 δ Y η) η := by
  simp only [corners, mem_insert_iff, mem_singleton_iff, not_or] at hη
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hη
  have z : ∀ {x : ℝ}, x / δ = 0 → x = 0 := fun h => (div_eq_zero_iff.mp h).resolve_right hδ.ne'
  have o : ∀ {x : ℝ}, x / δ = 1 → x = δ := fun h => (div_eq_one_iff_eq hδ.ne').mp h
  have d1 := hasDerivAt_d2S (u := up δ η) (fun h => c1 (by linarith [z h])) (fun h => c2 (by linarith [o h]))
  have d2 := hasDerivAt_d2S (u := dn δ Y η) (fun h => c4 (by linarith [z h])) (fun h => c3 (by linarith [o h]))
  have d3 := hasDerivAt_d2S (u := up δ (-η)) (fun h => c5 (by linarith [z h]))
    (fun h => c6 (by linarith [o h]))
  have d4 := hasDerivAt_d2S (u := dn δ Y (-η)) (fun h => c8 (by linarith [z h]))
    (fun h => c7 (by linarith [o h]))
  have := ((((d1.comp η (hasDerivAt_up δ η)).add (d2.comp η (hasDerivAt_dn δ Y η))).add
    (d3.comp η (hasDerivAt_up_neg δ η))).add (d4.comp η (hasDerivAt_dn_neg δ Y η))).div_const (δ ^ 2)
  refine this.congr_deriv ?_
  simp only [cut3]; field_simp; ring

theorem corners_countable (δ Y : ℝ) : (corners δ Y).Countable := by
  unfold corners; simp

theorem continuous_cut (hδ : 0 < δ) : Continuous (cut δ Y) :=
  continuous_iff_continuousAt.mpr fun η => (hasDerivAt_cut hδ η).continuousAt

theorem continuous_cut1 (hδ : 0 < δ) : Continuous (cut1 δ Y) :=
  continuous_iff_continuousAt.mpr fun η => (hasDerivAt_cut1 hδ η).continuousAt

theorem continuous_cut2 : Continuous (cut2 δ Y) := by
  have h := continuous_d2S
  unfold cut2 up dn; fun_prop

end geometry

/-! ### Exact `L²` norms of the cutoff -/

theorem measurable_glue {a b c : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable (glue a b c) := by
  unfold glue
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) ha
    (Measurable.ite (measurableSet_le measurable_const measurable_id) hc hb)

theorem measurable_qS : Measurable qS :=
  measurable_glue measurable_const (by unfold quintic; fun_prop) measurable_const

theorem measurable_dS : Measurable dS :=
  (continuous_iff_continuousAt.mpr fun u => (hasDerivAt_dS u).differentiableAt.continuousAt).measurable

theorem measurable_d3S : Measurable d3S :=
  measurable_glue measurable_const (by unfold quintic3; fun_prop) measurable_const

theorem abs_d3S_le (u : ℝ) : |d3S u| ≤ 60 := by
  rcases le_or_gt u 0 with h | h
  · rw [d3S, glue_of_nonpos _ _ _ h]; norm_num
  rcases le_or_gt 1 u with h' | h'
  · rw [d3S, glue_of_one_le _ _ _ h']; norm_num
  rw [d3S, glue_of_mem_Ioo _ _ _ ⟨h, h'⟩, quintic3, abs_le]
  constructor <;> nlinarith

theorem abs_qS_le (u : ℝ) : |qS u| ≤ 1 := by
  rcases le_or_gt u 0 with h | h
  · rw [qS, glue_of_nonpos _ _ _ h]; norm_num
  rcases le_or_gt 1 u with h' | h'
  · rw [qS, glue_of_one_le _ _ _ h']; norm_num
  rw [← S_eq_qS h', abs_of_nonneg (S_mem_Icc u).1]; exact (S_mem_Icc u).2

theorem qS_zero {u : ℝ} (h : u ≤ 0 ∨ 1 ≤ u) : qS u = 0 := by
  rcases h with h | h
  · exact glue_of_nonpos _ _ _ h
  · exact glue_of_one_le _ _ _ h

/-- A bounded measurable profile vanishing off `(0, 1)` is square integrable. -/
theorem integrable_sq_unit {F : ℝ → ℝ} {B : ℝ} (hm : Measurable F) (hB : ∀ u, |F u| ≤ B)
    (h0 : ∀ u, (u ≤ 0 ∨ 1 ≤ u) → F u = 0) : Integrable fun u => F u ^ 2 := by
  refine integrable_of_supp (L := 0) (R := 1) ?_ fun u hu => ?_
  · refine Measure.integrableOn_of_bounded (M := B ^ 2) measure_Icc_lt_top.ne
      (hm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hB u
    nlinarith [abs_nonneg (F u), sq_abs (F u)]
  · rw [mem_Ioo, not_and_or, not_lt, not_lt] at hu
    rw [h0 u hu]; ring

theorem integral_qS_sq : ∫ u, qS u ^ 2 = 181 / 462 := by
  rw [integral_eq_unit fun u hu => by simp [qS, glue_zero_of_not_mem hu], ← integral_quintic_sq]
  exact integral_congr_Ioo fun u hu => by rw [qS, glue_of_mem_Ioo _ _ _ hu]

section collar

variable {δ Y : ℝ}

theorem integral_comp_up (G : ℝ → ℝ) (hδ : 0 < δ) : ∫ η, G (up δ η) = δ * ∫ u, G u := by
  have := integral_sub_right_eq_self (μ := volume) (fun η => G (η / δ)) (1 - δ)
  unfold up
  rw [this, Measure.integral_comp_div G δ, abs_of_pos hδ, smul_eq_mul]

theorem integral_comp_dn (G : ℝ → ℝ) (hδ : 0 < δ) : ∫ η, G (dn δ Y η) = δ * ∫ u, G u := by
  have := integral_sub_left_eq_self (fun η => G (η / δ)) volume (Y + δ)
  unfold dn
  rw [this, Measure.integral_comp_div G δ, abs_of_pos hδ, smul_eq_mul]

theorem integrable_comp_up {G : ℝ → ℝ} (hG : Integrable G) (hδ : 0 < δ) :
    Integrable fun η => G (up δ η) :=
  (hG.comp_div hδ.ne').comp_sub_right (1 - δ)

theorem integrable_comp_dn {G : ℝ → ℝ} (hG : Integrable G) (hδ : 0 < δ) :
    Integrable fun η => G (dn δ Y η) :=
  (hG.comp_div hδ.ne').comp_sub_left (Y + δ)

/-- The four collar copies of `F²` integrate to `4δ∫F²`. -/
theorem integral_collar {F : ℝ → ℝ} (hF : Integrable fun u => F u ^ 2) (hδ : 0 < δ) :
    Integrable (fun η => F (up δ η) ^ 2 + F (dn δ Y η) ^ 2 + F (up δ (-η)) ^ 2 + F (dn δ Y (-η)) ^ 2) ∧
    ∫ η, (F (up δ η) ^ 2 + F (dn δ Y η) ^ 2 + F (up δ (-η)) ^ 2 + F (dn δ Y (-η)) ^ 2)
      = 4 * δ * ∫ u, F u ^ 2 := by
  have i1 := integrable_comp_up hF hδ
  have i2 := integrable_comp_dn (Y := Y) hF hδ
  have i3 := i1.comp_neg
  have i4 := i2.comp_neg
  have i12 : Integrable fun η => F (up δ η) ^ 2 + F (dn δ Y η) ^ 2 := i1.add i2
  have i123 : Integrable fun η => F (up δ η) ^ 2 + F (dn δ Y η) ^ 2 + F (up δ (-η)) ^ 2 := i12.add i3
  refine ⟨i123.add i4, ?_⟩
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_neg_eq_self (fun η => F (up δ η) ^ 2) volume,
    integral_neg_eq_self (fun η => F (dn δ Y η) ^ 2) volume,
    integral_comp_up (fun u => F u ^ 2) hδ, integral_comp_dn (fun u => F u ^ 2) hδ]
  ring

theorem sq_dS_int : Integrable fun u => dS u ^ 2 :=
  integrable_sq_unit measurable_dS abs_dS_le fun _ h => (derivs_zero h).1

theorem sq_d2S_int : Integrable fun u => d2S u ^ 2 :=
  integrable_sq_unit continuous_d2S.measurable abs_d2S_le fun _ h => (derivs_zero h).2.1

theorem sq_d3S_int : Integrable fun u => d3S u ^ 2 :=
  integrable_sq_unit measurable_d3S abs_d3S_le fun _ h => (derivs_zero h).2.2

theorem sq_qS_int : Integrable fun u => qS u ^ 2 :=
  integrable_sq_unit measurable_qS abs_qS_le fun _ h => qS_zero h

variable (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y)
include hδ hδ1 hY

/-- `‖cut′‖₂² = 4δς₁²/δ²` with `ς₁² = 10/7`. -/
theorem integral_cut1_sq : Integrable (fun η => cut1 δ Y η ^ 2) ∧ ∫ η, cut1 δ Y η ^ 2 = 4 * δ * (10 / 7) / δ ^ 2 := by
  have e : ∀ η, cut1 δ Y η ^ 2
      = (dS (up δ η) ^ 2 + dS (dn δ Y η) ^ 2 + dS (up δ (-η)) ^ 2 + dS (dn δ Y (-η)) ^ 2) / δ ^ 2 := by
    intro η
    rw [← collar_sq (F := dS) (fun _ h => (derivs_zero h).1) hδ hδ1 hY 1 (-1) (-1) 1 (by norm_num)]
    unfold cut1; ring
  simp_rw [e]
  obtain ⟨hi, hv⟩ := integral_collar (Y := Y) sq_dS_int hδ
  exact ⟨hi.div_const _, by rw [integral_div, hv, integral_dS_sq]⟩

/-- `‖cut″‖₂² = 4δς₂²/δ⁴` with `ς₂² = 120/7`. -/
theorem integral_cut2_sq : Integrable (fun η => cut2 δ Y η ^ 2) ∧
    ∫ η, cut2 δ Y η ^ 2 = 4 * δ * (120 / 7) / (δ ^ 2) ^ 2 := by
  have e : ∀ η, cut2 δ Y η ^ 2
      = (d2S (up δ η) ^ 2 + d2S (dn δ Y η) ^ 2 + d2S (up δ (-η)) ^ 2 + d2S (dn δ Y (-η)) ^ 2) / (δ ^ 2) ^ 2 := by
    intro η
    rw [← collar_sq (F := d2S) (fun _ h => (derivs_zero h).2.1) hδ hδ1 hY 1 1 1 1 (by norm_num)]
    unfold cut2; ring
  simp_rw [e]
  obtain ⟨hi, hv⟩ := integral_collar (Y := Y) sq_d2S_int hδ
  exact ⟨hi.div_const _, by rw [integral_div, hv, integral_d2S_sq]⟩

/-- `‖cut‴‖₂² = 4δς₃²/δ⁶` with `ς₃² = 720`. -/
theorem integral_cut3_sq : Integrable (fun η => cut3 δ Y η ^ 2) ∧
    ∫ η, cut3 δ Y η ^ 2 = 4 * δ * 720 / (δ ^ 3) ^ 2 := by
  have e : ∀ η, cut3 δ Y η ^ 2
      = (d3S (up δ η) ^ 2 + d3S (dn δ Y η) ^ 2 + d3S (up δ (-η)) ^ 2 + d3S (dn δ Y (-η)) ^ 2) / (δ ^ 3) ^ 2 := by
    intro η
    rw [← collar_sq (F := d3S) (fun _ h => (derivs_zero h).2.2) hδ hδ1 hY 1 (-1) (-1) 1 (by norm_num)]
    unfold cut3; ring
  simp_rw [e]
  obtain ⟨hi, hv⟩ := integral_collar (Y := Y) sq_d3S_int hδ
  exact ⟨hi.div_const _, by rw [integral_div, hv, integral_d3S_sq]⟩

/-- `cut² ≤ 1_{[1,Y]} + 1_{[−Y,−1]} + Σₖ q(Aₖ)²`. -/
theorem cut_sq_le_band (η : ℝ) :
    cut δ Y η ^ 2 ≤ (Icc 1 Y).indicator 1 η + (Icc (-Y) (-1)).indicator 1 η
      + (qS (up δ η) ^ 2 + qS (dn δ Y η) ^ 2 + qS (up δ (-η)) ^ 2 + qS (dn δ Y (-η)) ^ 2) := by
  have i1 : 0 ≤ (Icc 1 Y).indicator (1 : ℝ → ℝ) η := indicator_nonneg (fun _ _ => zero_le_one) η
  have i2 : 0 ≤ (Icc (-Y) (-1)).indicator (1 : ℝ → ℝ) η := indicator_nonneg (fun _ _ => zero_le_one) η
  by_cases h : |η| ∈ Icc 1 Y
  · rw [cut_eq_one hδ hδ1 hY h, one_pow]
    have hq : 0 ≤ qS (up δ η) ^ 2 + qS (dn δ Y η) ^ 2 + qS (up δ (-η)) ^ 2 + qS (dn δ Y (-η)) ^ 2 := by
      positivity
    rcases le_or_gt 0 η with h0 | h0
    · rw [abs_of_nonneg h0] at h
      rw [indicator_of_mem h]; simp only [Pi.one_apply]; linarith
    · rw [abs_of_neg h0] at h
      rw [indicator_of_mem (show η ∈ Icc (-Y) (-1) from ⟨by linarith [h.2], by linarith [h.1]⟩)]
      simp only [Pi.one_apply]; linarith
  · have := cut_sq_le hδ hδ1 hY h
    linarith

/-- `‖cut‖₂² ≤ 2(Y − 1) + 4δκ_S` with `κ_S = 181/462`. -/
theorem integral_cut_sq : Integrable (fun η => cut δ Y η ^ 2) ∧
    ∫ η, cut δ Y η ^ 2 ≤ 2 * (Y - 1) + 4 * δ * (181 / 462) := by
  obtain ⟨hi, hv⟩ := integral_collar (Y := Y) sq_qS_int hδ
  have j1 : Integrable ((Icc 1 Y).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  have j2 : Integrable ((Icc (-Y) (-1)).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const measure_Icc_lt_top.ne)
  have hb : Integrable fun η => (Icc 1 Y).indicator 1 η + (Icc (-Y) (-1)).indicator 1 η
      + (qS (up δ η) ^ 2 + qS (dn δ Y η) ^ 2 + qS (up δ (-η)) ^ 2 + qS (dn δ Y (-η)) ^ 2) :=
    (j1.add j2).add hi
  have hc : Integrable fun η => cut δ Y η ^ 2 :=
    hb.mono' ((continuous_cut hδ).pow 2).aestronglyMeasurable (ae_of_all _ fun η => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact cut_sq_le_band hδ hδ1 hY η)
  refine ⟨hc, (integral_mono hc hb (cut_sq_le_band hδ hδ1 hY)).trans (le_of_eq ?_)⟩
  have j12 : Integrable fun η => (Icc 1 Y).indicator (1 : ℝ → ℝ) η + (Icc (-Y) (-1)).indicator 1 η :=
    j1.add j2
  rw [integral_add j12 hi, integral_add j1 j2, hv, integral_qS_sq,
    integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc,
    Real.volume_real_Icc_of_le hY, Real.volume_real_Icc_of_le (by linarith)]
  ring

end collar

end cutoff

/-! ### The band multiplier `μ̃·cut` and its profile -/

section band

/-- The region `{η : |η| ∈ [1 − δ, Y + δ]}` carrying the cutoff. -/
def bandRg (δ Y : ℝ) : Set ℝ := {η | |η| ∈ Icc (1 - δ) (Y + δ)}

/-- `μ̃ ∈ C³` on the cutoff's region, with `sup|μ̃^{(j)}| ≤ N j` there. -/
structure IsBandMult (μ μ₁ μ₂ μ₃ : ℝ → ℂ) (δ Y : ℝ) (N : ℕ → ℝ) : Prop where
  d0 : ∀ η ∈ bandRg δ Y, HasDerivAt μ (μ₁ η) η
  d1 : ∀ η ∈ bandRg δ Y, HasDerivAt μ₁ (μ₂ η) η
  d2 : ∀ η ∈ bandRg δ Y, HasDerivAt μ₂ (μ₃ η) η
  c3 : ContinuousOn μ₃ (bandRg δ Y)
  bd : ∀ η ∈ bandRg δ Y, ‖μ η‖ ≤ N 0 ∧ ‖μ₁ η‖ ≤ N 1 ∧ ‖μ₂ η‖ ≤ N 2 ∧ ‖μ₃ η‖ ≤ N 3

/-- `n = cut·μ̃`. -/
noncomputable def bm0 (δ Y : ℝ) (μ : ℝ → ℂ) (η : ℝ) : ℂ := (cut δ Y η : ℂ) * μ η

/-- `n′ = cut′μ̃ + cut μ̃′`. -/
noncomputable def bm1 (δ Y : ℝ) (μ μ₁ : ℝ → ℂ) (η : ℝ) : ℂ :=
  (cut1 δ Y η : ℂ) * μ η + (cut δ Y η : ℂ) * μ₁ η

/-- `n″ = cut″μ̃ + 2cut′μ̃′ + cut μ̃″`. -/
noncomputable def bm2 (δ Y : ℝ) (μ μ₁ μ₂ : ℝ → ℂ) (η : ℝ) : ℂ :=
  (cut2 δ Y η : ℂ) * μ η + 2 * (cut1 δ Y η : ℂ) * μ₁ η + (cut δ Y η : ℂ) * μ₂ η

/-- `n‴ = cut‴μ̃ + 3cut″μ̃′ + 3cut′μ̃″ + cut μ̃‴`. -/
noncomputable def bm3 (δ Y : ℝ) (μ μ₁ μ₂ μ₃ : ℝ → ℂ) (η : ℝ) : ℂ :=
  (cut3 δ Y η : ℂ) * μ η + 3 * (cut2 δ Y η : ℂ) * μ₁ η + 3 * (cut1 δ Y η : ℂ) * μ₂ η
    + (cut δ Y η : ℂ) * μ₃ η

/-- The rescaled `m(ξ) = F(ξ/c)/c^j`. -/
noncomputable def sc (c : ℝ) (F : ℝ → ℂ) (j : ℕ) (ξ : ℝ) : ℂ := F (ξ / c) / (c : ℂ) ^ j

variable {δ Y : ℝ} {μ μ₁ μ₂ μ₃ : ℝ → ℂ} {N : ℕ → ℝ}

theorem isClosed_bandRg (δ Y : ℝ) : IsClosed (bandRg δ Y) := isClosed_Icc.preimage continuous_abs

theorem one_mem_bandRg (hδ : 0 < δ) (hY : 1 ≤ Y) : (1 : ℝ) ∈ bandRg δ Y := by
  show |(1 : ℝ)| ∈ Icc (1 - δ) (Y + δ)
  rw [abs_one]; constructor <;> linarith

variable (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hY : 1 ≤ Y)
include hδ hδ1 hY

theorem cut_zero_off {η : ℝ} (h : η ∉ bandRg δ Y) :
    cut δ Y η = 0 ∧ cut1 δ Y η = 0 ∧ cut2 δ Y η = 0 ∧ cut3 δ Y η = 0 :=
  cut_eq_zero hδ hδ1 hY fun h' => h (Ioo_subset_Icc_self h')

omit hδ hδ1 hY in
/-- A function vanishing off the region is differentiable with derivative `0` off it. -/
theorem hasDerivAt_off {f f' : ℝ → ℂ} {η : ℝ} (h : η ∉ bandRg δ Y)
    (hf : ∀ y, y ∉ bandRg δ Y → f y = 0) (hf' : f' η = 0) : HasDerivAt f (f' η) η := by
  rw [hf']
  refine (hasDerivAt_const η (0 : ℂ)).congr_of_eventuallyEq ?_
  filter_upwards [(isClosed_bandRg δ Y).isOpen_compl.mem_nhds h] with y hy
  exact hf y hy

theorem bm_zero_off {η : ℝ} (h : η ∉ bandRg δ Y) :
    bm0 δ Y μ η = 0 ∧ bm1 δ Y μ μ₁ η = 0 ∧ bm2 δ Y μ μ₁ μ₂ η = 0 ∧ bm3 δ Y μ μ₁ μ₂ μ₃ η = 0 := by
  obtain ⟨z0, z1, z2, z3⟩ := cut_zero_off hδ hδ1 hY h
  simp [bm0, bm1, bm2, bm3, z0, z1, z2, z3]

theorem hasDerivAt_bm0 (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) (η : ℝ) :
    HasDerivAt (bm0 δ Y μ) (bm1 δ Y μ μ₁ η) η := by
  by_cases h : η ∈ bandRg δ Y
  · exact ((hasDerivAt_cut (Y := Y) hδ η).ofReal_comp.mul (hμ.d0 η h))
  · exact hasDerivAt_off h (fun y hy => (bm_zero_off (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃) hδ hδ1 hY hy).1)
      (bm_zero_off (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃) hδ hδ1 hY h).2.1

theorem hasDerivAt_bm1 (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) (η : ℝ) :
    HasDerivAt (bm1 δ Y μ μ₁) (bm2 δ Y μ μ₁ μ₂ η) η := by
  by_cases h : η ∈ bandRg δ Y
  · have := ((hasDerivAt_cut1 (Y := Y) hδ η).ofReal_comp.mul (hμ.d0 η h)).add
      ((hasDerivAt_cut (Y := Y) hδ η).ofReal_comp.mul (hμ.d1 η h))
    refine this.congr_deriv ?_
    simp only [bm2]; ring
  · exact hasDerivAt_off h (fun y hy => (bm_zero_off (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃) hδ hδ1 hY hy).2.1)
      (bm_zero_off (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃) hδ hδ1 hY h).2.2.1

theorem hasDerivAt_bm2 (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) {η : ℝ} (hη : η ∉ corners δ Y) :
    HasDerivAt (bm2 δ Y μ μ₁ μ₂) (bm3 δ Y μ μ₁ μ₂ μ₃ η) η := by
  by_cases h : η ∈ bandRg δ Y
  · have := ((((hasDerivAt_cut2 hδ hη).ofReal_comp.mul (hμ.d0 η h)).add
      (((hasDerivAt_cut1 (Y := Y) hδ η).ofReal_comp.const_mul 2).mul (hμ.d1 η h))).add
      ((hasDerivAt_cut (Y := Y) hδ η).ofReal_comp.mul (hμ.d2 η h)))
    refine this.congr_deriv ?_
    simp only [bm3]; ring
  · exact hasDerivAt_off h (fun y hy => (bm_zero_off (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃) hδ hδ1 hY hy).2.2.1)
      (bm_zero_off (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃) hδ hδ1 hY h).2.2.2

theorem continuous_bm2 (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) : Continuous (bm2 δ Y μ μ₁ μ₂) := by
  refine continuous_iff_continuousAt.mpr fun η => ?_
  by_cases h : η ∈ bandRg δ Y
  · have c0 := (hμ.d0 η h).continuousAt
    have c1 := (hμ.d1 η h).continuousAt
    have c2 := (hμ.d2 η h).continuousAt
    have k0 := (continuous_ofReal.comp (continuous_cut (Y := Y) hδ)).continuousAt (x := η)
    have k1 := (continuous_ofReal.comp (continuous_cut1 (Y := Y) hδ)).continuousAt (x := η)
    have k2 := (continuous_ofReal.comp (continuous_cut2 (δ := δ) (Y := Y))).continuousAt (x := η)
    exact ((k2.mul c0).add ((continuousAt_const.mul k1).mul c1)).add (k0.mul c2)
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [(isClosed_bandRg δ Y).isOpen_compl.mem_nhds h] with y hy
    exact ((bm_zero_off (μ := μ) (μ₁ := μ₁) (μ₂ := μ₂) (μ₃ := μ₃) hδ hδ1 hY hy).2.2.1).symm

theorem measurable_bm3 (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) : Measurable (bm3 δ Y μ μ₁ μ₂ μ₃) := by
  classical
  have hR : MeasurableSet (bandRg δ Y) := (isClosed_bandRg δ Y).measurableSet
  have hm : ∀ {f : ℝ → ℂ}, ContinuousOn f (bandRg δ Y) → Measurable ((bandRg δ Y).indicator f) := by
    intro f hf
    have := hf.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hR
    convert this using 1
    funext η; simp [Set.indicator, Set.piecewise]
  have c0 : ContinuousOn μ (bandRg δ Y) := fun η h => (hμ.d0 η h).continuousAt.continuousWithinAt
  have c1 : ContinuousOn μ₁ (bandRg δ Y) := fun η h => (hμ.d1 η h).continuousAt.continuousWithinAt
  have c2 : ContinuousOn μ₂ (bandRg δ Y) := fun η h => (hμ.d2 η h).continuousAt.continuousWithinAt
  have e : bm3 δ Y μ μ₁ μ₂ μ₃ = fun η => (cut3 δ Y η : ℂ) * (bandRg δ Y).indicator μ η
      + 3 * (cut2 δ Y η : ℂ) * (bandRg δ Y).indicator μ₁ η + 3 * (cut1 δ Y η : ℂ) * (bandRg δ Y).indicator μ₂ η
      + (cut δ Y η : ℂ) * (bandRg δ Y).indicator μ₃ η := by
    funext η
    by_cases h : η ∈ bandRg δ Y
    · simp only [bm3, indicator_of_mem h]
    · obtain ⟨z0, z1, z2, z3⟩ := cut_zero_off hδ hδ1 hY h
      simp [bm3, indicator_of_notMem h, z0, z1, z2, z3]
  rw [e]
  have k3 : Measurable fun η => (cut3 δ Y η : ℂ) := by
    have h := measurable_d3S
    unfold cut3 up dn; exact measurable_ofReal.comp (by fun_prop)
  have k2 : Measurable fun η => (cut2 δ Y η : ℂ) := (continuous_ofReal.comp continuous_cut2).measurable
  have k1 : Measurable fun η => (cut1 δ Y η : ℂ) := (continuous_ofReal.comp (continuous_cut1 hδ)).measurable
  have k0 : Measurable fun η => (cut δ Y η : ℂ) := (continuous_ofReal.comp (continuous_cut hδ)).measurable
  exact (((k3.mul (hm c0)).add ((measurable_const.mul k2).mul (hm c1))).add
    ((measurable_const.mul k1).mul (hm c2))).add (k0.mul (hm hμ.c3))

omit hδ1 in
theorem N_nonneg (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) : 0 ≤ N 0 ∧ 0 ≤ N 1 ∧ 0 ≤ N 2 ∧ 0 ≤ N 3 := by
  obtain ⟨h0, h1, h2, h3⟩ := hμ.bd 1 (one_mem_bandRg hδ hY)
  exact ⟨(norm_nonneg _).trans h0, (norm_nonneg _).trans h1, (norm_nonneg _).trans h2,
    (norm_nonneg _).trans h3⟩

omit hδ hδ1 hY in
theorem norm_term_le {x : ℝ} {z : ℂ} {M : ℝ} (k : ℕ) (h : ‖z‖ ≤ M) :
    ‖(k : ℂ) * (x : ℂ) * z‖ ≤ k * M * |x| := by
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  have := abs_nonneg x
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (k : ℝ) * |x| * ‖z‖ ≤ k * |x| * M := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- Pointwise Leibniz bounds `‖n^{(j)}‖ ≤ Σᵢ C(j,i) N_{j−i}|cut^{(i)}|`. -/
theorem norm_bm_le (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) (η : ℝ) :
    ‖bm0 δ Y μ η‖ ≤ N 0 * |cut δ Y η| ∧
    ‖bm1 δ Y μ μ₁ η‖ ≤ N 0 * |cut1 δ Y η| + N 1 * |cut δ Y η| ∧
    ‖bm2 δ Y μ μ₁ μ₂ η‖ ≤ N 0 * |cut2 δ Y η| + 2 * N 1 * |cut1 δ Y η| + N 2 * |cut δ Y η| ∧
    ‖bm3 δ Y μ μ₁ μ₂ μ₃ η‖
      ≤ N 0 * |cut3 δ Y η| + 3 * N 1 * |cut2 δ Y η| + 3 * N 2 * |cut1 δ Y η| + N 3 * |cut δ Y η| := by
  by_cases h : η ∈ bandRg δ Y
  · obtain ⟨b0, b1, b2, b3⟩ := hμ.bd η h
    have t : ∀ {x : ℝ} {z : ℂ} {M : ℝ}, ‖z‖ ≤ M → ‖(x : ℂ) * z‖ ≤ M * |x| := fun hz => by
      simpa using norm_term_le (x := _) 1 hz
    refine ⟨t b0, ?_, ?_, ?_⟩
    · exact (norm_add_le _ _).trans (add_le_add (t b0) (t b1))
    · refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (t b0) ?_)) (t b2))
      have := norm_term_le (x := cut1 δ Y η) 2 b1; push_cast at this; linarith
    · refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (t b0) ?_)) ?_)) (t b3))
      · have := norm_term_le (x := cut2 δ Y η) 3 b1; push_cast at this; linarith
      · have := norm_term_le (x := cut1 δ Y η) 3 b2; push_cast at this; linarith
  · obtain ⟨z0, z1, z2, z3⟩ := cut_zero_off hδ hδ1 hY h
    simp [bm0, bm1, bm2, bm3, z0, z1, z2, z3]

omit hδ hδ1 hY in
/-- **Minkowski** for two nonnegative `L²` functions, with integrability of the square of the sum. -/
theorem mink {p q : ℝ → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) (hpm : AEStronglyMeasurable p)
    (hqm : AEStronglyMeasurable q) (hp : Integrable fun x => p x ^ 2) (hq : Integrable fun x => q x ^ 2) :
    Integrable (fun x => (p x + q x) ^ 2) ∧
      √(∫ x, (p x + q x) ^ 2) ≤ √(∫ x, p x ^ 2) + √(∫ x, q x ^ 2) := by
  refine ⟨((hp.const_mul 2).add (hq.const_mul 2)).mono' ((hpm.add hqm).pow 2)
    (ae_of_all _ fun x => ?_), Cvs.L2a.SpectralMassLevelLeak.sqrt_integral_add_sq_le hp0 hq0 hpm hqm hp hq⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (p x - q x)]

omit hδ hδ1 hY in
/-- A scaled modulus `a|f|` with `f² ∈ L¹`: nonnegative, measurable, `‖a|f|‖₂ = a‖f‖₂`. -/
theorem scaled_abs {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hf : AEStronglyMeasurable f)
    (hf2 : Integrable fun x => f x ^ 2) :
    (∀ x, 0 ≤ a * |f x|) ∧ AEStronglyMeasurable (fun x => a * |f x|) ∧
      Integrable (fun x => (a * |f x|) ^ 2) ∧ √(∫ x, (a * |f x|) ^ 2) = a * √(∫ x, f x ^ 2) := by
  have e : (fun x => (a * |f x|) ^ 2) = fun x => a ^ 2 * f x ^ 2 := by funext x; rw [mul_pow, sq_abs]
  refine ⟨fun x => by positivity, aestronglyMeasurable_const.mul hf.norm, by rw [e]; exact hf2.const_mul _,
    ?_⟩
  rw [e, integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha]

omit hδ hδ1 hY in
theorem sqrt_le_of_norm_le {F : ℝ → ℂ} {p : ℝ → ℝ} (hp : Integrable fun x => p x ^ 2)
    (h : ∀ x, ‖F x‖ ≤ p x) : √(∫ x, ‖F x‖ ^ 2) ≤ √(∫ x, p x ^ 2) :=
  Real.sqrt_le_sqrt (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hp
    (ae_of_all _ fun x => pow_le_pow_left₀ (norm_nonneg _) (h x) 2))

/-- **`L²` Leibniz bounds**: `‖n^{(j)}‖₂ ≤ Σᵢ C(j,i) N_{j−i}‖cut^{(i)}‖₂`, and `n‴ ∈ L²`. -/
theorem l2_bm (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) :
    ∫ η, ‖bm0 δ Y μ η‖ ^ 2 ≤ N 0 ^ 2 * ∫ η, cut δ Y η ^ 2 ∧
    √(∫ η, ‖bm1 δ Y μ μ₁ η‖ ^ 2) ≤ N 0 * √(∫ η, cut1 δ Y η ^ 2) + N 1 * √(∫ η, cut δ Y η ^ 2) ∧
    √(∫ η, ‖bm2 δ Y μ μ₁ μ₂ η‖ ^ 2) ≤ N 0 * √(∫ η, cut2 δ Y η ^ 2) + 2 * N 1 * √(∫ η, cut1 δ Y η ^ 2)
      + N 2 * √(∫ η, cut δ Y η ^ 2) ∧
    √(∫ η, ‖bm3 δ Y μ μ₁ μ₂ μ₃ η‖ ^ 2) ≤ N 0 * √(∫ η, cut3 δ Y η ^ 2)
      + 3 * N 1 * √(∫ η, cut2 δ Y η ^ 2) + 3 * N 2 * √(∫ η, cut1 δ Y η ^ 2) + N 3 * √(∫ η, cut δ Y η ^ 2) ∧
    MemLp (bm3 δ Y μ μ₁ μ₂ μ₃) 2 := by
  obtain ⟨n0, n1, n2, n3⟩ := N_nonneg hδ hY hμ
  have m0 : AEStronglyMeasurable (cut δ Y) := (continuous_cut hδ).aestronglyMeasurable
  have m1 : AEStronglyMeasurable (cut1 δ Y) := (continuous_cut1 hδ).aestronglyMeasurable
  have m2 : AEStronglyMeasurable (cut2 δ Y) := continuous_cut2.aestronglyMeasurable
  have m3 : AEStronglyMeasurable (cut3 δ Y) := by
    have h := measurable_d3S
    unfold cut3 up dn; exact (by fun_prop : Measurable _).aestronglyMeasurable
  have i0 := (integral_cut_sq hδ hδ1 hY).1
  have i1 := (integral_cut1_sq hδ hδ1 hY).1
  have i2 := (integral_cut2_sq hδ hδ1 hY).1
  have i3 := (integral_cut3_sq hδ hδ1 hY).1
  have hb := norm_bm_le (μ₃ := μ₃) hδ hδ1 hY hμ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, -, j, -⟩ := scaled_abs n0 m0 i0
    refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) j
      (ae_of_all _ fun x => pow_le_pow_left₀ (norm_nonneg _) (hb x).1 2)).trans (le_of_eq ?_)
    simp_rw [mul_pow, sq_abs]; rw [integral_const_mul]
  · obtain ⟨a0, b0, c0, d0⟩ := scaled_abs n0 m1 i1
    obtain ⟨a1, b1, c1, d1⟩ := scaled_abs n1 m0 i0
    obtain ⟨k, hk⟩ := mink a0 a1 b0 b1 c0 c1
    refine (sqrt_le_of_norm_le k fun x => (hb x).2.1).trans ?_
    rw [← d0, ← d1]; exact hk
  · obtain ⟨a0, b0, c0, d0⟩ := scaled_abs n0 m2 i2
    obtain ⟨a1, b1, c1, d1⟩ := scaled_abs (by positivity : (0:ℝ) ≤ 2 * N 1) m1 i1
    obtain ⟨a2, b2, c2, d2⟩ := scaled_abs n2 m0 i0
    obtain ⟨k, hk⟩ := mink a0 a1 b0 b1 c0 c1
    obtain ⟨k', hk'⟩ := mink (fun x => add_nonneg (a0 x) (a1 x)) a2 (b0.add b1) b2 k c2
    refine (sqrt_le_of_norm_le k' fun x => (hb x).2.2.1).trans ?_
    rw [← d0, ← d1, ← d2]; linarith
  · obtain ⟨a0, b0, c0, d0⟩ := scaled_abs n0 m3 i3
    obtain ⟨a1, b1, c1, d1⟩ := scaled_abs (by positivity : (0:ℝ) ≤ 3 * N 1) m2 i2
    obtain ⟨a2, b2, c2, d2⟩ := scaled_abs (by positivity : (0:ℝ) ≤ 3 * N 2) m1 i1
    obtain ⟨a3, b3, c3, d3⟩ := scaled_abs n3 m0 i0
    obtain ⟨k, hk⟩ := mink a0 a1 b0 b1 c0 c1
    obtain ⟨k', hk'⟩ := mink (fun x => add_nonneg (a0 x) (a1 x)) a2 (b0.add b1) b2 k c2
    obtain ⟨k'', hk''⟩ := mink (fun x => add_nonneg (add_nonneg (a0 x) (a1 x)) (a2 x)) a3
      ((b0.add b1).add b2) b3 k' c3
    refine (sqrt_le_of_norm_le k'' fun x => (hb x).2.2.2).trans ?_
    rw [← d0, ← d1, ← d2, ← d3]; linarith
  · obtain ⟨a0, b0, c0, -⟩ := scaled_abs n0 m3 i3
    obtain ⟨a1, b1, c1, -⟩ := scaled_abs (by positivity : (0:ℝ) ≤ 3 * N 1) m2 i2
    obtain ⟨a2, b2, c2, -⟩ := scaled_abs (by positivity : (0:ℝ) ≤ 3 * N 2) m1 i1
    obtain ⟨a3, b3, c3, -⟩ := scaled_abs n3 m0 i0
    obtain ⟨k, -⟩ := mink a0 a1 b0 b1 c0 c1
    obtain ⟨k', -⟩ := mink (fun x => add_nonneg (a0 x) (a1 x)) a2 (b0.add b1) b2 k c2
    obtain ⟨k'', -⟩ := mink (fun x => add_nonneg (add_nonneg (a0 x) (a1 x)) (a2 x)) a3
      ((b0.add b1).add b2) b3 k' c3
    have hpm := ((b0.add b1).add b2).add b3
    have hp : MemLp (fun x => N 0 * |cut3 δ Y x| + 3 * N 1 * |cut2 δ Y x| + 3 * N 2 * |cut1 δ Y x|
        + N 3 * |cut δ Y x|) 2 := (memLp_two_iff_integrable_sq hpm).mpr k''
    refine hp.of_le (measurable_bm3 hδ hδ1 hY hμ).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    refine (hb x).2.2.2.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (add_nonneg (add_nonneg (a0 x) (a1 x)) (a2 x)) (a3 x))]

omit hδ hδ1 hY in
theorem hasDerivAt_sc {c : ℝ} (hc : c ≠ 0) {F F' : ℝ → ℂ} {ξ : ℝ} (h : HasDerivAt F (F' (ξ / c)) (ξ / c))
    (j : ℕ) : HasDerivAt (sc c F j) (sc c F' (j + 1) ξ) ξ := by
  have h1 : HasDerivAt (fun x : ℝ => x / c) (1 / c) ξ := (hasDerivAt_id ξ).div_const c
  have := (h.scomp ξ h1).div_const ((c : ℂ) ^ j)
  refine this.congr_deriv ?_
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  simp only [sc, Complex.real_smul]; push_cast; field_simp; ring

omit hδ hδ1 hY in
theorem integral_norm_sc_sq {c : ℝ} (hc : 0 < c) (F : ℝ → ℂ) (j : ℕ) :
    ∫ ξ, ‖sc c F j ξ‖ ^ 2 = c / (c ^ j) ^ 2 * ∫ η, ‖F η‖ ^ 2 := by
  simp only [sc, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, div_pow]
  rw [integral_div, Measure.integral_comp_div (fun η => ‖F η‖ ^ 2) c, abs_of_pos hc, smul_eq_mul]; ring

omit hδ hδ1 hY in
theorem nrm_sc {c : ℝ} (hc : 0 < c) (F : ℝ → ℂ) (j : ℕ) :
    nrm (sc c F j) = √c / c ^ j * √(∫ η, ‖F η‖ ^ 2) := by
  rw [nrm, integral_norm_sc_sq hc, Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq (by positivity)]

/-- **The band profile**: `m(ξ) = cut(ξ/c)μ̃(ξ/c)` and its scaled derivatives form a profile on `±c(Y + δ)`. -/
theorem isProfile_band {c : ℝ} (hc : 0 < c) (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) :
    IsProfile (sc c (bm0 δ Y μ) 0) (sc c (bm1 δ Y μ μ₁) 1) (sc c (bm2 δ Y μ μ₁ μ₂) 2)
      (sc c (bm3 δ Y μ μ₁ μ₂ μ₃) 3) (-(c * (Y + δ))) (c * (Y + δ)) ((fun η => c * η) '' corners δ Y) where
  le := by have : 0 ≤ c * (Y + δ) := by positivity
           linarith
  countable := (corners_countable δ Y).image _
  d0 ξ := hasDerivAt_sc hc.ne' (hasDerivAt_bm0 hδ hδ1 hY hμ (ξ / c)) 0
  d1 ξ := hasDerivAt_sc hc.ne' (hasDerivAt_bm1 hδ hδ1 hY hμ (ξ / c)) 1
  c2 := ((continuous_bm2 hδ hδ1 hY hμ).comp (continuous_id.div_const c)).div_const _
  d2 ξ hξ := hasDerivAt_sc hc.ne' (hasDerivAt_bm2 hδ hδ1 hY hμ fun h =>
    hξ ⟨ξ / c, h, by field_simp⟩) 2
  supp ξ hξ := by
    have h : |ξ / c| ∉ Ioo (1 - δ) (Y + δ) := by
      intro h
      apply hξ
      have := h.2
      rw [abs_div, abs_of_pos hc, div_lt_iff₀ hc, abs_lt] at this
      exact ⟨by linarith, by linarith⟩
    obtain ⟨z0, z1, z2, z3⟩ := cut_eq_zero hδ hδ1 hY h
    simp [sc, bm0, bm1, bm2, bm3, z0, z1, z2, z3]
  mem3 := by
    have hm := measurable_bm3 hδ hδ1 hY hμ
    have hL := (l2_bm hδ hδ1 hY hμ).2.2.2.2
    have hsq := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hL
    refine (memLp_two_iff_integrable_sq_norm
      ((hm.comp (measurable_id.div_const c)).div_const _).aestronglyMeasurable).mpr ?_
    have := (hsq.comp_div hc.ne').div_const (((c : ℝ) ^ 3) ^ 2)
    refine this.congr (ae_of_all _ fun ξ => ?_)
    simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, div_pow, Function.comp, id,
      abs_of_pos hc]

/-- `ς_i = ‖S^{(i)}‖₂` for the quintic step: `ς₀² = 181/462`, `ς₁² = 10/7`, `ς₂² = 120/7`, `ς₃² = 720`. -/
noncomputable def varsig : ℕ → ℝ
  | 0 => √(181 / 462)
  | 1 => √(10 / 7)
  | 2 => √(120 / 7)
  | _ => √720

/-- `σ_j = √(2ΔY)N_j + 2Σ_{i≤j} C(j,i) ς_i δ^{1/2−i} N_{j−i}`. -/
noncomputable def sigmaB (dY δ : ℝ) (N : ℕ → ℝ) (j : ℕ) : ℝ :=
  √(2 * dY) * N j + 2 * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * varsig i * (√δ / δ ^ i) * N (j - i)

omit hδ1 hY in
theorem sqrt_four_mul {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : √(4 * δ * a / (δ ^ k) ^ 2) = 2 * √a * (√δ / δ ^ k) := by
  have hs : 0 ≤ √δ := Real.sqrt_nonneg δ
  rw [show 4 * δ * a / (δ ^ k) ^ 2 = (2 * √a * (√δ / δ ^ k)) ^ 2 by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt ha, Real.sq_sqrt hδ.le]; ring]
  exact Real.sqrt_sq (by positivity)

theorem sqrt_integral_cut_le : √(∫ η, cut δ Y η ^ 2) ≤ √(2 * (Y - 1)) + 2 * varsig 0 * (√δ / δ ^ 0) := by
  refine (Real.sqrt_le_sqrt (integral_cut_sq hδ hδ1 hY).2).trans ?_
  have h4 : √(4 * δ * (181 / 462)) = 2 * varsig 0 * (√δ / δ ^ 0) := by
    simpa [varsig] using sqrt_four_mul hδ (a := 181 / 462) (by norm_num) 0
  rw [← h4, Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (Y - 1) by linarith)
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 4 * δ * (181 / 462) by positivity)
  nlinarith [Real.sqrt_nonneg (2 * (Y - 1)), Real.sqrt_nonneg (4 * δ * (181 / 462))]

/-- **The `L²` norms of the band profile**: `‖m^{(j)}‖₂ ≤ √c·c^{−j}·σ_j` for `j = 1, 2, 3`. -/
theorem nrm_band_le {c : ℝ} (hc : 0 < c) (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) :
    nrm (sc c (bm1 δ Y μ μ₁) 1) ≤ √c / c ^ 1 * sigmaB (Y - 1) δ N 1 ∧
    nrm (sc c (bm2 δ Y μ μ₁ μ₂) 2) ≤ √c / c ^ 2 * sigmaB (Y - 1) δ N 2 ∧
    nrm (sc c (bm3 δ Y μ μ₁ μ₂ μ₃) 3) ≤ √c / c ^ 3 * sigmaB (Y - 1) δ N 3 := by
  obtain ⟨n0, n1, n2, n3⟩ := N_nonneg hδ hY hμ
  obtain ⟨-, l1, l2, l3, -⟩ := l2_bm hδ hδ1 hY hμ
  have w0 := sqrt_integral_cut_le hδ hδ1 hY
  have w1 : √(∫ η, cut1 δ Y η ^ 2) = 2 * varsig 1 * (√δ / δ ^ 1) := by
    rw [(integral_cut1_sq hδ hδ1 hY).2, show δ ^ 2 = (δ ^ 1) ^ 2 by ring]
    exact sqrt_four_mul hδ (by norm_num) 1
  have w2 : √(∫ η, cut2 δ Y η ^ 2) = 2 * varsig 2 * (√δ / δ ^ 2) := by
    rw [(integral_cut2_sq hδ hδ1 hY).2]; exact sqrt_four_mul hδ (by norm_num) 2
  have w3 : √(∫ η, cut3 δ Y η ^ 2) = 2 * varsig 3 * (√δ / δ ^ 3) := by
    rw [(integral_cut3_sq hδ hδ1 hY).2]; exact sqrt_four_mul hδ (by norm_num) 3
  have hc' : 0 ≤ √c / c ^ 1 := by positivity
  rw [nrm_sc hc, nrm_sc hc, nrm_sc hc]
  simp only [sigmaB, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, zero_add, Nat.cast_one,
    Nat.sub_zero, Nat.sub_self, Nat.add_one_sub_one] at *
  refine ⟨mul_le_mul_of_nonneg_left ?_ hc', mul_le_mul_of_nonneg_left ?_ (by positivity),
    mul_le_mul_of_nonneg_left ?_ (by positivity)⟩
  · rw [w1] at l1; nlinarith [mul_le_mul_of_nonneg_left w0 n1]
  · rw [w1, w2] at l2; nlinarith [mul_le_mul_of_nonneg_left w0 n2]
  · rw [w1, w2, w3] at l3; nlinarith [mul_le_mul_of_nonneg_left w0 n3]

/-- **The main term**: `∫|m|² ≤ ∫_B|μ|² + 4cδκ_S N₀²` for `B ⊇ ±c[1, Y]`, and `∫|m|² ≤ cN₀²(2(Y−1) + 4δκ_S)`. -/
theorem integral_band_le {c : ℝ} (hc : 0 < c) (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ Y N) {B : Set ℝ}
    (hB : MeasurableSet B) (hBc : ∀ ξ, |ξ| ∈ Icc c (c * Y) → ξ ∈ B)
    (hBi : IntegrableOn (fun ξ => ‖μ (ξ / c)‖ ^ 2) B) :
    ∫ ξ, ‖sc c (bm0 δ Y μ) 0 ξ‖ ^ 2 ≤ (∫ ξ in B, ‖μ (ξ / c)‖ ^ 2) + c * (4 * δ * (181 / 462)) * N 0 ^ 2 ∧
    ∫ ξ, ‖sc c (bm0 δ Y μ) 0 ξ‖ ^ 2 ≤ c * N 0 ^ 2 * (2 * (Y - 1) + 4 * δ * (181 / 462)) := by
  obtain ⟨n0, -, -, -⟩ := N_nonneg hδ hY hμ
  constructor
  · obtain ⟨hQi, hQv⟩ := integral_collar (Y := Y) sq_qS_int hδ
    set Q : ℝ → ℝ := fun η => qS (up δ η) ^ 2 + qS (dn δ Y η) ^ 2 + qS (up δ (-η)) ^ 2 + qS (dn δ Y (-η)) ^ 2
    have hQ0 : ∀ η, 0 ≤ Q η := fun η => by positivity
    have i1 : Integrable (B.indicator fun ξ => ‖μ (ξ / c)‖ ^ 2) := hBi.integrable_indicator hB
    have i2 : Integrable fun ξ => N 0 ^ 2 * Q (ξ / c) := (hQi.comp_div hc.ne').const_mul _
    have hpt : ∀ ξ, ‖sc c (bm0 δ Y μ) 0 ξ‖ ^ 2
        ≤ B.indicator (fun ξ => ‖μ (ξ / c)‖ ^ 2) ξ + N 0 ^ 2 * Q (ξ / c) := by
      intro ξ
      have hcut := cut_mem_Icc hδ hδ1 hY (ξ / c)
      have e : ‖sc c (bm0 δ Y μ) 0 ξ‖ ^ 2 = cut δ Y (ξ / c) ^ 2 * ‖μ (ξ / c)‖ ^ 2 := by
        simp only [sc, bm0, pow_zero, div_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [e]
      by_cases hξ : ξ ∈ B
      · rw [indicator_of_mem hξ]
        have : cut δ Y (ξ / c) ^ 2 ≤ 1 := by nlinarith [hcut.1, hcut.2]
        nlinarith [hQ0 (ξ / c), sq_nonneg (N 0), sq_nonneg ‖μ (ξ / c)‖]
      · rw [indicator_of_notMem hξ, zero_add]
        have hb : |ξ / c| ∉ Icc 1 Y := by
          intro h
          apply hξ (hBc ξ _)
          rw [abs_div, abs_of_pos hc] at h
          obtain ⟨h1, h2⟩ := h
          rw [le_div_iff₀ hc] at h1; rw [div_le_iff₀ hc] at h2
          exact ⟨by linarith, by linarith⟩
        have hq := cut_sq_le hδ hδ1 hY hb
        by_cases hr : ξ / c ∈ bandRg δ Y
        · have hN := (hμ.bd _ hr).1
          have : ‖μ (ξ / c)‖ ^ 2 ≤ N 0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hN 2
          calc cut δ Y (ξ / c) ^ 2 * ‖μ (ξ / c)‖ ^ 2 ≤ Q (ξ / c) * N 0 ^ 2 :=
                mul_le_mul hq this (sq_nonneg _) (hQ0 _)
            _ = _ := by ring
        · rw [(cut_zero_off hδ hδ1 hY hr).1]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
          exact mul_nonneg (sq_nonneg _) (hQ0 _)
    have i12 : Integrable fun ξ => B.indicator (fun ξ => ‖μ (ξ / c)‖ ^ 2) ξ + N 0 ^ 2 * Q (ξ / c) :=
      i1.add i2
    refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) i12
      (ae_of_all _ hpt)).trans (le_of_eq ?_)
    rw [integral_add i1 i2, integral_indicator hB, integral_const_mul,
      Measure.integral_comp_div Q c, abs_of_pos hc, smul_eq_mul, hQv, integral_qS_sq]
    ring
  · rw [integral_norm_sc_sq hc, pow_zero, one_pow, div_one]
    have h0 := (l2_bm (μ₃ := μ₃) hδ hδ1 hY hμ).1
    have h1 := (integral_cut_sq hδ hδ1 hY).2
    calc c * ∫ η, ‖bm0 δ Y μ η‖ ^ 2 ≤ c * (N 0 ^ 2 * ∫ η, cut δ Y η ^ 2) :=
          mul_le_mul_of_nonneg_left h0 hc.le
      _ ≤ c * (N 0 ^ 2 * (2 * (Y - 1) + 4 * δ * (181 / 462))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) hc.le
      _ = _ := by ring

end band

/-! ### LBT-h (B): the band form -/

section final

open Cvs.L2a.OrbitGapIntegerM

/-- `τ̂ = 2β_W e^{β_W d}√(σ₁σ₂)/c + Y'_W√(σ₂σ₃)/(2c) + (e^{2β_W d}+1)σ₃/(√(5π)(cd/2)^{5/2})`, `ΔY = Y_max(x₀) − 1`. -/
noncomputable def tauHat (c x₀ d δ : ℝ) (N : ℕ → ℝ) : ℝ :=
  2 * betaW x₀ d * Real.exp (betaW x₀ d * d)
      * √(sigmaB (Ymax x₀ - 1) δ N 1 * sigmaB (Ymax x₀ - 1) δ N 2) / c
    + chirpW x₀ d * √(sigmaB (Ymax x₀ - 1) δ N 2 * sigmaB (Ymax x₀ - 1) δ N 3) / (2 * c)
    + (Real.exp (2 * betaW x₀ d * d) + 1) * sigmaB (Ymax x₀ - 1) δ N 3 / (√(5 * π) * √((c * d / 2) ^ 5))

theorem one_le_Ymax {x : ℝ} (hx : 1 < x) : 1 ≤ Ymax x := by
  have h0 : 0 < x ^ 2 - 1 := by nlinarith
  have hs : 0 < √(x ^ 2 - 1) := Real.sqrt_pos.mpr h0
  rw [Ymax, le_div_iff₀ hs, one_mul, Real.sqrt_le_left (by linarith)]
  linarith

/-- `τ_L ≤ τ̂` once `ℓ_j ≤ √c·c^{−j}σ_j`. -/
theorem tauL_le {c x₀ d l₁ l₂ l₃ s₁ s₂ s₃ : ℝ} (hc : 0 < c) (hd : 0 < d) (hxd : 1 < x₀ - d)
    (h1 : 0 ≤ l₁) (h2 : 0 ≤ l₂) (h3 : 0 ≤ l₃)
    (hl1 : l₁ ≤ √c / c ^ 1 * s₁) (hl2 : l₂ ≤ √c / c ^ 2 * s₂) (hl3 : l₃ ≤ √c / c ^ 3 * s₃) :
    tauL c x₀ d l₁ l₂ l₃ ≤ 2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * √(s₁ * s₂) / c
      + chirpW x₀ d * √(s₂ * s₃) / (2 * c)
      + (Real.exp (2 * betaW x₀ d * d) + 1) * s₃ / (√(5 * π) * √((c * d / 2) ^ 5)) := by
  have hb := betaW_nonneg hxd
  have hy := chirpW_nonneg hd.le hxd
  have hsc : √c ^ 2 = c := Real.sq_sqrt hc.le
  have hsc0 : 0 < √c := Real.sqrt_pos.mpr hc
  have hs2 : 0 ≤ s₂ := by
    have : 0 ≤ √c / c ^ 2 * s₂ := h2.trans hl2
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : 0 < √c / c ^ 2)
  have k1 : √(l₁ * l₂) ≤ √(s₁ * s₂) / c := by
    calc √(l₁ * l₂) ≤ √((√c / c ^ 1 * s₁) * (√c / c ^ 2 * s₂)) :=
          Real.sqrt_le_sqrt (mul_le_mul hl1 hl2 h2 (h1.trans hl1))
      _ = √(s₁ * s₂) / c := by
          rw [show (√c / c ^ 1 * s₁) * (√c / c ^ 2 * s₂) = s₁ * s₂ / c ^ 2 by
            field_simp; rw [hsc], Real.sqrt_div' _ (by positivity), Real.sqrt_sq hc.le]
  have k2 : √(l₂ * l₃) ≤ √(s₂ * s₃) / c ^ 2 := by
    calc √(l₂ * l₃) ≤ √((√c / c ^ 2 * s₂) * (√c / c ^ 3 * s₃)) :=
          Real.sqrt_le_sqrt (mul_le_mul hl2 hl3 h3 (h2.trans hl2))
      _ = √(s₂ * s₃) / c ^ 2 := by
          rw [show (√c / c ^ 2 * s₂) * (√c / c ^ 3 * s₃) = s₂ * s₃ / (c ^ 2) ^ 2 by
            field_simp; rw [hsc], Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  have hq : 0 < √(5 * π * (d / 2) ^ 5) := Real.sqrt_pos.mpr (by positivity)
  have k3 : l₃ / √(5 * π * (d / 2) ^ 5) ≤ s₃ / (√(5 * π) * √((c * d / 2) ^ 5)) := by
    have e : s₃ / (√(5 * π) * √((c * d / 2) ^ 5)) = (√c / c ^ 3 * s₃) / √(5 * π * (d / 2) ^ 5) := by
      have r1 : √((c * d / 2) ^ 5) = c ^ 2 * √c * √((d / 2) ^ 5) := by
        rw [show (c * d / 2) ^ 5 = (c ^ 2 * √c) ^ 2 * (d / 2) ^ 5 by rw [mul_pow, hsc]; ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      have r2 : √(5 * π * (d / 2) ^ 5) = √(5 * π) * √((d / 2) ^ 5) := Real.sqrt_mul (by positivity) _
      have r3 : 0 < √((d / 2) ^ 5) := Real.sqrt_pos.mpr (by positivity)
      have r4 : 0 < √(5 * π) := Real.sqrt_pos.mpr (by positivity)
      rw [r1, r2]
      field_simp
      rw [hsc]
    rw [e]; exact div_le_div_of_nonneg_right hl3 hq.le
  unfold tauL
  have e1 : 2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * √(s₁ * s₂) / c
      = 2 * betaW x₀ d * Real.exp (betaW x₀ d * d) * (√(s₁ * s₂) / c) := by ring
  have e2 : chirpW x₀ d * √(s₂ * s₃) / (2 * c) = c / 2 * chirpW x₀ d * (√(s₂ * s₃) / c ^ 2) := by
    field_simp
  have e3 : (Real.exp (2 * betaW x₀ d * d) + 1) * s₃ / (√(5 * π) * √((c * d / 2) ^ 5))
      = (Real.exp (2 * betaW x₀ d * d) + 1) * (s₃ / (√(5 * π) * √((c * d / 2) ^ 5))) := by ring
  rw [e1, e2, e3]
  gcongr

theorem sq_le_expand {s A T A2 A' T' : ℝ} (hs : 0 ≤ s) (h : s ≤ A + T) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hA2 : A ^ 2 ≤ A2) (hA' : A ≤ A') (hT' : T ≤ T') : s ^ 2 ≤ A2 + 2 * A' * T' + T' ^ 2 := by
  have h1 : s ^ 2 ≤ (A + T) ^ 2 := pow_le_pow_left₀ hs h 2
  have h2 : A * T ≤ A' * T' := mul_le_mul hA' hT' hT (hA.trans hA')
  have h3 : T ^ 2 ≤ T' ^ 2 := pow_le_pow_left₀ hT hT' 2
  nlinarith

/-- **LBT-h (B), general form**: for `μ(ξ) = μ̃(ξ/c)` with `μ̃ ∈ C³` on `±[1 − δ, Y_max(x₀) + δ]` and
`sup|μ̃^{(j)}| ≤ N_j` there, the band sum obeys `|Σaₙ Sₙ[μ]|² ≤ (2π)⁻¹∫_B|μ|²·W + c(…)` with `τ̂` from `σ_j(N)`. -/
theorem lbt_band_gen {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {X x₀ d δ : ℝ} {μ μ₁ μ₂ μ₃ : ℝ → ℂ} {N : ℕ → ℝ} {B : Set ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hx₀ : x₀ ∈ Icc (6 / 5 : ℝ) X)
    (hd : 0 < d) (hxd : 1 < x₀ - d) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hμ : IsBandMult μ μ₁ μ₂ μ₃ δ (Ymax x₀) N)
    (hB : MeasurableSet B) (hBc : ∀ ξ, |ξ| ∈ Icc c (c * Ymax x₀) → ξ ∈ B)
    (hBi : IntegrableOn (fun ξ => ‖μ (ξ / c)‖ ^ 2) B) :
    ‖∑ i, (a i : ℂ) * smp (fun ξ => μ (ξ / c)) c (χ i) (g i) x₀‖ ^ 2
      ≤ (2 * π)⁻¹ * (∫ ξ in B, ‖μ (ξ / c)‖ ^ 2) * (∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2)
        + c * (2 * (181 / 462) / π * δ * N 0 ^ 2 * (∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2)
          + 2 * N 0 * tauHat c x₀ d δ N
            * √((Ymax x₀ - 1 + 2 * (181 / 462) * δ) * (6 * (Fintype.card ι : ℝ) / (c * (x₀ ^ 2 - 1))) / π)
            * √((∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2)
              * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
          + tauHat c x₀ d δ N ^ 2 * (6 * (Fintype.card ι : ℝ) / (c * (x₀ ^ 2 - 1)))
            * ∑ i, a i ^ 2 * (∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)) := by
  set Y := Ymax x₀ with hYdef
  set W := ∫ x in (x₀ - d)..(x₀ + d), (∑ i, a i * psi c (g i) x) ^ 2 with hWdef
  set P := ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 with hPdef
  set G := 6 * (Fintype.card ι : ℝ) / (c * (x₀ ^ 2 - 1)) with hGdef
  set τ := tauHat c x₀ d δ N with hτ
  have hc0 : 0 < c := by linarith
  have hx1 : 1 < x₀ := by linarith
  have hY : 1 ≤ Y := one_le_Ymax hx1
  have hW : 0 ≤ W := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
    (intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _)
  have hG : 0 ≤ G := by have : 0 < x₀ ^ 2 - 1 := by nlinarith
                        positivity
  have hcG : 6 * (Fintype.card ι : ℝ) / (x₀ ^ 2 - 1) = c * G := by
    rw [hGdef]; field_simp
  obtain ⟨n0, -, -, -⟩ := N_nonneg hδ hY hμ
  -- the profile and the transfer through it
  have hprof := isProfile_band hδ hδ1 hY hc0 hμ
  have hband : ∀ ξ, |ξ| ∈ Icc c (c * Y) → sc c (bm0 δ Y μ) 0 ξ = (fun ξ => μ (ξ / c)) ξ := by
    intro ξ h
    have h' : |ξ / c| ∈ Icc 1 Y := by
      rw [abs_div, abs_of_pos hc0]
      exact ⟨(le_div_iff₀ hc0).mpr (by linarith [h.1]), (div_le_iff₀ hc0).mpr (by linarith [h.2])⟩
    simp only [sc, bm0, cut_eq_one hδ hδ1 hY h', ofReal_one, one_mul, pow_zero, div_one]
  have hmain := lbt_profile a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hx₀ hd hxd hprof hband
  obtain ⟨hI1, hI2⟩ := integral_band_le (μ₃ := μ₃) hδ hδ1 hY hc0 hμ hB hBc hBi
  obtain ⟨hn1, hn2, hn3⟩ := nrm_band_le hδ hδ1 hY hc0 hμ
  have htau : tauL c x₀ d (nrm (sc c (bm1 δ Y μ μ₁) 1)) (nrm (sc c (bm2 δ Y μ μ₁ μ₂) 2))
      (nrm (sc c (bm3 δ Y μ μ₁ μ₂ μ₃) 3)) ≤ τ :=
    tauL_le hc0 hd hxd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hn1 hn2 hn3
  have htau0 : 0 ≤ tauL c x₀ d (nrm (sc c (bm1 δ Y μ μ₁) 1)) (nrm (sc c (bm2 δ Y μ μ₁ μ₂) 2))
      (nrm (sc c (bm3 δ Y μ μ₁ μ₂ μ₃) 3)) := by
    have := betaW_nonneg hxd; have := chirpW_nonneg hd.le hxd
    unfold tauL nrm; positivity
  rw [hcG] at hmain
  set Im := ∫ ξ, ‖sc c (bm0 δ Y μ) 0 ξ‖ ^ 2 with hIm
  have hIm0 : 0 ≤ Im := integral_nonneg fun _ => sq_nonneg _
  have hpi : 0 < π := Real.pi_pos
  -- the abstract expansion
  refine (sq_le_expand (norm_nonneg _) hmain (by positivity) (by positivity)
    (A2 := (2 * π)⁻¹ * ((∫ ξ in B, ‖μ (ξ / c)‖ ^ 2) + c * (4 * δ * (181 / 462)) * N 0 ^ 2) * W)
    (A' := N 0 * √c * √((Y - 1 + 2 * (181 / 462) * δ) / π) * √W)
    (T' := τ * √c * √G * √P) ?_ ?_ ?_).trans (le_of_eq ?_)
  · rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hW]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI1 (by positivity)) hW
  · refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    calc √((2 * π)⁻¹ * Im) ≤ √((2 * π)⁻¹ * (c * N 0 ^ 2 * (2 * (Y - 1) + 4 * δ * (181 / 462)))) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hI2 (by positivity))
      _ = N 0 * √c * √((Y - 1 + 2 * (181 / 462) * δ) / π) := by
          rw [show (2 * π)⁻¹ * (c * N 0 ^ 2 * (2 * (Y - 1) + 4 * δ * (181 / 462)))
              = N 0 ^ 2 * (c * ((Y - 1 + 2 * (181 / 462) * δ) / π)) by field_simp; ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq n0, Real.sqrt_mul hc0.le]
          ring
  · rw [Real.sqrt_mul hc0.le]
    nlinarith [mul_le_mul_of_nonneg_right htau (by positivity : (0:ℝ) ≤ √c * √G * √P)]
  · have hsc : √c ^ 2 = c := Real.sq_sqrt hc0.le
    have hsG : √G ^ 2 = G := Real.sq_sqrt hG
    have hsP : √P ^ 2 = P := Real.sq_sqrt hP
    rw [Real.sqrt_mul hW P]
    have hpi' : (2 * π)⁻¹ * (c * (4 * δ * (181 / 462)) * N 0 ^ 2) * W
        = c * (2 * (181 / 462) / π * δ * N 0 ^ 2 * W) := by field_simp; ring
    calc (2 * π)⁻¹ * ((∫ ξ in B, ‖μ (ξ / c)‖ ^ 2) + c * (4 * δ * (181 / 462)) * N 0 ^ 2) * W
          + 2 * (N 0 * √c * √((Y - 1 + 2 * (181 / 462) * δ) / π) * √W) * (τ * √c * √G * √P)
          + (τ * √c * √G * √P) ^ 2
        = (2 * π)⁻¹ * (∫ ξ in B, ‖μ (ξ / c)‖ ^ 2) * W
          + c * (2 * (181 / 462) / π * δ * N 0 ^ 2 * W)
          + 2 * N 0 * τ * √((Y - 1 + 2 * (181 / 462) * δ) / π) * √G * √W * √P * √c ^ 2
          + τ ^ 2 * √c ^ 2 * √G ^ 2 * √P ^ 2 := by rw [← hpi']; ring
      _ = _ := by
          rw [hsc, hsG, hsP]
          rw [show (Y - 1 + 2 * (181 / 462) * δ) * G / π = (Y - 1 + 2 * (181 / 462) * δ) / π * G by ring,
            Real.sqrt_mul (by positivity) G]
          ring

end final

end Cvs.L2a.BandTransferBandForm
