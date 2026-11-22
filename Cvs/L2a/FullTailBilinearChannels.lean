import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailPrimeChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PositionTailSpanAdapters
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungTailIntegralMass
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
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
# The three channels of `W_∞(Φ, Ψ)` against `T⁺ = F_∞(Ψ)`

Pole: `|Π₋Φ| ≤ √N` and `|Π₊Φ| ≤ C_π√P`. Arch: `|∫ a ρ_{f,k}| ≤ ‖f‖ C_A`. Prime, split at `k = 2`: `C_L1√N`,
`2‖log θ T⁺‖√N`, `log 2 ‖T⁺‖(√N + √P)` on `(1, 2]`, and mode by mode for `k > 2` one integration by parts against
`T_β` with `|T_β(θ₀)| + ∫|T_β'| ≤ ½ + V₀`, TI's `|∫_y^Y Φ| ≤ K/y` and `Σ 1/(m·max(m, k)) ≤ (3 + log k)/k`.
-/

namespace Cvs.L2a.FullTailBilinearChannels

open Real Set Filter Topology MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail Cvs.L2a.FullTailConvergence Cvs.L2a.TailLogScaleTest Cvs.L2a.BetaProfilePoissonTail Cvs.L2a.FullTailPolarisation
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open scoped FourierTransform ComplexConjugate

/-! ### The functionals of `T⁺` -/

/-- `‖T⁺‖ = (∫_{(1,∞)} T⁺²)^{1/2}`. -/
noncomputable def normT : ℝ := √(∫ θ in Ioi 1, fullTail Psi θ ^ 2)

/-- `‖log θ · T⁺‖ = (∫_{(1,∞)} (log θ T⁺)²)^{1/2}`. -/
noncomputable def normLogT : ℝ := √(∫ θ in Ioi 1, (Real.log θ * fullTail Psi θ) ^ 2)

/-- `V₀ = ∫_{(1,∞)} |T_β'|`, with `T_β' = −T_γ/θ`. -/
noncomputable def V0 : ℝ := ∫ θ in Ioi 1, |-(1 / θ) * profTail gamma θ|

theorem V0_nonneg : 0 ≤ V0 := setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _

theorem continuous_Psi : Continuous Psi :=
  (contDiff_psi (fun _ _ => continuous_beta.continuousWithinAt) (2 * π)).continuous

/-- `|T⁺(θ)| ≤ B_β/θ`, `FullTailConvergence`'s bound at `c = 2π`. -/
theorem abs_fullTail_Psi_le_BG {θ : ℝ} (hθ : 0 < θ) :
    |fullTail Psi θ| ≤ BG (2 * π) (beta 1 + beta (-1)) (|beta1 1 - beta1 (-1)| + ∫ s in (-1 : ℝ)..1, |beta2 s|) / θ :=
  abs_fullTail_le hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 (by positivity) hθ

/-- `|F_k(Ψ)(θ) − T⁺(θ)| ≤ 2B_β/θ`. -/
theorem abs_posTail_sub_fullTail_Psi_le (k : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    |posTail Psi k θ - fullTail Psi θ|
      ≤ 2 * BG (2 * π) (beta 1 + beta (-1)) (|beta1 1 - beta1 (-1)| + ∫ s in (-1 : ℝ)..1, |beta2 s|) / θ :=
  abs_posTail_sub_le hasDerivAt_beta_on hasDerivAt_beta1_on continuousOn_beta2 (by positivity) k hθ

/-! ### The rescaled profile of `Ψ` -/

/-- The profile `a⁻¹β(·/a)`, `a = 2π/c`, whose transform at scale `c` is `Ψ`. -/
noncomputable def betaA (c s : ℝ) : ℝ := (2 * π / c)⁻¹ * beta (s / (2 * π / c))

/-- Its first derivative. -/
noncomputable def betaA1 (c s : ℝ) : ℝ := (2 * π / c)⁻¹ * (beta1 (s / (2 * π / c)) * (1 / (2 * π / c)))

/-- Its second derivative. -/
noncomputable def betaA2 (c s : ℝ) : ℝ :=
  (2 * π / c)⁻¹ * (beta2 (s / (2 * π / c)) * (1 / (2 * π / c)) * (1 / (2 * π / c)))

theorem hasDerivAt_betaA (c s : ℝ) : HasDerivAt (betaA c) (betaA1 c s) s := by
  set a : ℝ := 2 * π / c with ha
  have h1 : HasDerivAt (fun x : ℝ => x / a) (1 / a) s := (hasDerivAt_id' s).div_const a
  have h2 : HasDerivAt (beta ∘ fun x : ℝ => x / a) (beta1 (s / a) * (1 / a)) s :=
    HasDerivAt.comp (h₂ := beta) (h := fun x : ℝ => x / a) s (hasDerivAt_beta (s / a)) h1
  exact h2.const_mul a⁻¹

theorem hasDerivAt_betaA1 (c s : ℝ) : HasDerivAt (betaA1 c) (betaA2 c s) s := by
  set a : ℝ := 2 * π / c with ha
  have h1 : HasDerivAt (fun x : ℝ => x / a) (1 / a) s := (hasDerivAt_id' s).div_const a
  have h2 : HasDerivAt (beta1 ∘ fun x : ℝ => x / a) (beta2 (s / a) * (1 / a)) s :=
    HasDerivAt.comp (h₂ := beta1) (h := fun x : ℝ => x / a) s (hasDerivAt_beta1 (s / a)) h1
  exact (h2.mul_const (1 / a)).const_mul a⁻¹

theorem continuous_betaA2 (c : ℝ) : Continuous (betaA2 c) := by
  unfold betaA2; have := continuous_beta2; fun_prop

theorem psi_betaA {c : ℝ} (hc : 2 * π ≤ c) : psi c (betaA c) = Psi := psi_comp_div_eq_Psi hc

/-! ### The arch channel -/

/-- `|Re(A·conj B)|/(2π) ≤ √ρ_f √ρ_k`: the polarised density is dominated by the geometric mean. -/
theorem abs_crossSpec_le (f k : ℝ → ℝ) (t : ℝ) :
    |crossSpec f k t|
      ≤ √(Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) * √(Cvs.WeilForm.SelfConvolutionCosine.specDensity k t) := by
  unfold crossSpec Cvs.WeilForm.SelfConvolutionCosine.specDensity
  set A := 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf f) (t / (2 * π))
  set B := 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf k) (t / (2 * π))
  have hπ : 0 < 2 * π := by positivity
  have h1 : |(A * conj B).re| ≤ ‖A‖ * ‖B‖ := by
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_conj]
  rw [← Real.sqrt_mul (by positivity),
    show ‖A‖ ^ 2 / (2 * π) * (‖B‖ ^ 2 / (2 * π)) = (‖A‖ * ‖B‖ / (2 * π)) ^ 2 by ring,
    Real.sqrt_sq (by positivity), abs_div, abs_of_pos hπ]
  exact div_le_div_of_nonneg_right h1 hπ.le

/-- **Cauchy–Schwarz on the spectrum**: `|∫ a ρ_{f,k}| ≤ (∫ ρ_f)^{1/2} (∫ a² ρ_k)^{1/2}`. -/
theorem abs_integral_arch_crossSpec_le {f k : ℝ → ℝ} (hf2 : MemLp f 2 volume) (hf1 : Integrable f)
    (hka : Integrable fun t => archSymbol t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity k t) :
    |∫ t, archSymbol t * crossSpec f k t|
      ≤ √(∫ t, Cvs.WeilForm.SelfConvolutionCosine.specDensity f t)
        * √(∫ t, archSymbol t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity k t) := by
  set ρf := Cvs.WeilForm.SelfConvolutionCosine.specDensity f
  set ρk := fun t => archSymbol t ^ 2 * Cvs.WeilForm.SelfConvolutionCosine.specDensity k t
  have hρf : Integrable ρf := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf1
  have hρf0 : ∀ t, 0 ≤ ρf t := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f
  have hρk0 : ∀ t, 0 ≤ ρk t := fun t => mul_nonneg (sq_nonneg _) (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg k t)
  have hsf : AEStronglyMeasurable (fun t => √(ρf t)) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hρf.aestronglyMeasurable
  have hsk : AEStronglyMeasurable (fun t => √(ρk t)) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hka.aestronglyMeasurable
  have hprod : Integrable fun t => √(ρf t) * √(ρk t) := by
    refine ((hρf.add hka).div_const 2).mono' (hsf.mul hsk) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 := Real.sq_sqrt (hρf0 t)
    have h2 := Real.sq_sqrt (hρk0 t)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (√(ρf t) - √(ρk t))]
  have hsq_f : IntegrableOn (fun t => √(ρf t) ^ 2) univ :=
    (integrableOn_univ.2 hρf).congr_fun (fun t _ => (Real.sq_sqrt (hρf0 t)).symm) MeasurableSet.univ
  have hsq_k : IntegrableOn (fun t => √(ρk t) ^ 2) univ :=
    (integrableOn_univ.2 hka).congr_fun (fun t _ => (Real.sq_sqrt (hρk0 t)).symm) MeasurableSet.univ
  have hCS := abs_setIntegral_mul_le hsq_f hsq_k (integrableOn_univ.2 hprod)
  simp only [Measure.restrict_univ] at hCS
  have ef : ∫ t, √(ρf t) ^ 2 = ∫ t, ρf t := integral_congr_ae (Eventually.of_forall fun t => Real.sq_sqrt (hρf0 t))
  have ek : ∫ t, √(ρk t) ^ 2 = ∫ t, ρk t := integral_congr_ae (Eventually.of_forall fun t => Real.sq_sqrt (hρk0 t))
  rw [ef, ek] at hCS
  have hpt : ∀ t, |archSymbol t * crossSpec f k t| ≤ √(ρf t) * √(ρk t) := fun t => by
    rw [abs_mul]
    have hc := abs_crossSpec_le f k t
    have e : √(ρk t) = |archSymbol t| * √(Cvs.WeilForm.SelfConvolutionCosine.specDensity k t) := by
      simp only [ρk]
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    rw [e]
    calc |archSymbol t| * |crossSpec f k t|
        ≤ |archSymbol t| * (√(ρf t) * √(Cvs.WeilForm.SelfConvolutionCosine.specDensity k t)) :=
          mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ = √(ρf t) * (|archSymbol t| * √(Cvs.WeilForm.SelfConvolutionCosine.specDensity k t)) := by ring
  calc |∫ t, archSymbol t * crossSpec f k t| ≤ ∫ t, |archSymbol t * crossSpec f k t| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t, √(ρf t) * √(ρk t) :=
        integral_mono_of_nonneg (Eventually.of_forall fun t => abs_nonneg _) hprod (Eventually.of_forall hpt)
    _ ≤ |∫ t, √(ρf t) * √(ρk t)| := le_abs_self _
    _ ≤ _ := hCS

section rung

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

/-- **The arch channel against `T⁺`**: `|Arch(Φ, Ψ)| ≤ C_A √N`, `N = ∫_{(1,∞)} F_∞(Φ)²`, for `c ≥ 2π`. -/
theorem abs_archBil_Psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 2 * π ≤ c) :
    |archBil (psi c g) Psi| ≤ CA * √(∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  have e := arch_bil_eq_spectral hg hg₁ hg₂c (fun s _ => hasDerivAt_betaA c s) (fun s _ => hasDerivAt_betaA1 c s)
    (continuous_betaA2 c).continuousOn hc0
  rw [psi_betaA hc] at e
  rw [e]
  obtain ⟨hf2, hf1⟩ := memLp_logScale_fullTail hg hg₁ hg₂c hc0
  refine (abs_integral_arch_crossSpec_le hf2 hf1 CA_sq_le.1).trans (le_of_eq ?_)
  rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity hf1 hf2,
    integral_sq _ fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ, CA]
  ring

/-! ### The pole channel -/

/-- `|Π₋(Φ)| = |∫_{(1,∞)} F_∞/θ| ≤ √N`, Cauchy–Schwarz with `∫_{(1,∞)} θ⁻² = 1`. -/
theorem abs_integral_fullTail_div_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    |∫ θ in Ioi 1, fullTail (psi c g) θ / θ| ≤ √(∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) := by
  set b := fullTail (psi c g)
  have hbm := measurable_fullTail hg hg₁ hg₂c hc
  have hwm : Measurable fun θ : ℝ => θ⁻¹ := measurable_inv
  have hwb : ∀ θ : ℝ, 0 < θ → |θ⁻¹| ≤ 1 / θ := fun θ hθ => by rw [abs_of_pos (inv_pos.mpr hθ), one_div]
  have hbb := fun θ (hθ : 0 < θ) => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have ib : IntegrableOn (fun θ => b θ * θ⁻¹) (Ioi 1) := integrableOn_mul_of_le hbm hwm hbb hwb
  have hb2 : IntegrableOn (fun θ => b θ ^ 2) (Ioi 1) := integrableOn_sq_of_le hbm hbb
  have hw2 : IntegrableOn (fun θ : ℝ => θ⁻¹ ^ 2) (Ioi 1) := integrableOn_sq_of_le hwm hwb
  have hw1 : ∫ θ in Ioi 1, (θ⁻¹ : ℝ) ^ 2 = 1 := by
    have h := integral_one_div_sq (a := 1) one_pos
    simpa only [one_div, inv_pow, inv_one] using h
  simp only [div_eq_mul_inv]
  refine (abs_setIntegral_mul_le hb2 hw2 ib).trans (le_of_eq ?_)
  rw [hw1, Real.sqrt_one, mul_one]

/-- **The pole channel against `T⁺`**: `|Pole(Φ, Ψ)| ≤ Π₋(Ψ)|Π₊(Φ)| + |Π₊(Ψ)|√N`, with `Π₋(Ψ) = 59/630`. -/
theorem abs_poleBil_Psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    |poleBil (psi c g) Psi|
      ≤ 59 / 630 * |Cvs.L2a.FullTailPoleChannel.piPlus (psi c g)|
        + |Cvs.L2a.FullTailPoleChannel.piPlus Psi| * √(∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) := by
  unfold poleBil
  rw [piMinus_Psi]
  have h := abs_integral_fullTail_div_le hg hg₁ hg₂c hc
  calc |Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) * (59 / 630)
        + Cvs.L2a.FullTailPoleChannel.piPlus Psi * ∫ θ in Ioi 1, fullTail (psi c g) θ / θ|
      ≤ |Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) * (59 / 630)|
        + |Cvs.L2a.FullTailPoleChannel.piPlus Psi * ∫ θ in Ioi 1, fullTail (psi c g) θ / θ| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 59 / 630), mul_comm]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h (abs_nonneg _))

/-! ### The prime channel, one mode at a time -/

/-- **The variation of `T_β`** from `1`: `|T_β(a)| + ∫_a^b |T_β'| ≤ ½ + V₀` for `1 ≤ a ≤ b`. -/
theorem abs_Tb_add_integral_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |Tb a| + ∫ θ in a..b, |-(1 / θ) * profTail gamma θ| ≤ 1 / 2 + V0 := by
  have hcont : ∀ x y : ℝ, 1 ≤ x → x ≤ y → ContinuousOn (fun θ => -(1 / θ) * profTail gamma θ) (uIcc x y) :=
    fun x y hx hxy => continuousOn_deriv_Tb.mono fun θ hθ => by
      rw [uIcc_of_le hxy] at hθ; exact mem_Ioi.mpr (by linarith [hθ.1])
  have hFTC : Tb a - Tb 1 = ∫ θ in (1 : ℝ)..a, -(1 / θ) * profTail gamma θ := by
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ hθ => hasDerivAt_Tb ?_)
      ((hcont 1 a le_rfl ha).intervalIntegrable)).symm
    rw [uIcc_of_le ha] at hθ; linarith [hθ.1]
  have h1 : |Tb a| ≤ 1 / 2 + ∫ θ in (1 : ℝ)..a, |-(1 / θ) * profTail gamma θ| := by
    have e : Tb a = Tb 1 + ∫ θ in (1 : ℝ)..a, -(1 / θ) * profTail gamma θ := by linarith
    rw [e, Tb_one]
    refine (abs_add_le _ _).trans (add_le_add (le_of_eq (by norm_num)) ?_)
    exact intervalIntegral.abs_integral_le_integral_abs ha
  have hi : ∀ x y : ℝ, 1 ≤ x → x ≤ y →
      IntervalIntegrable (fun θ => |-(1 / θ) * profTail gamma θ|) volume x y :=
    fun x y hx hxy => (hcont x y hx hxy).abs.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi 1 a le_rfl ha) (hi a b ha hab)
  have hV : ∫ θ in (1 : ℝ)..b, |-(1 / θ) * profTail gamma θ| ≤ V0 := by
    rw [intervalIntegral.integral_of_le (ha.trans hab)]
    exact setIntegral_mono_set V0_le.1 (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall (Ioc_subset_Ioi_self : Ioc (1 : ℝ) b ⊆ Ioi 1))
  linarith

/-- `m · max(1, k/m) = max(m, k)` for `m > 0`. -/
theorem mul_max_one_div {m k : ℝ} (hm : 0 < m) : m * max 1 (k / m) = max m k := by
  rw [mul_max_of_nonneg _ _ hm.le, mul_one, mul_div_cancel₀ _ hm.ne']

/-- **One mode, one integration by parts**: with `|∫_y^Y Φ| ≤ K/y` for `2 ≤ y ≤ Y`,
`|∫_{max(1,k/m)}^{X/m} T_β(θ)Φ(mθ)| ≤ (½ + V₀)K/(m·max(m, k))` for `2 ≤ k ≤ X`, `1 ≤ m ≤ X`. -/
theorem abs_integral_Tb_mode_le {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {K : ℝ}
    (hK : ∀ y Y : ℝ, 2 ≤ y → y ≤ Y → |∫ ξ in y..Y, Φ ξ| ≤ K / y) {m : ℕ} (hm : 1 ≤ m) {k X : ℝ}
    (hk : 2 ≤ k) (hkX : k ≤ X) (hmX : (m : ℝ) ≤ X) :
    |∫ θ in (max 1 (k / m))..(X / m), Tb θ * Φ (m * θ)| ≤ (1 / 2 + V0) * (K / (m * max (m : ℝ) k)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hK0 : 0 ≤ K := by
    have h := hK 2 2 le_rfl le_rfl
    rw [intervalIntegral.integral_same, abs_zero] at h
    linarith [(div_nonneg_iff.mp h).elim (fun h => h.1) fun h => absurd h.2 (by norm_num)]
  set a := max 1 (k / m) with had
  set b := X / m with hbd
  set D := K / (m * max (m : ℝ) k) with hDd
  have ha1 : 1 ≤ a := le_max_left _ _
  have hab : a ≤ b := max_le ((one_le_div hm0).mpr hmX) (div_le_div_of_nonneg_right hkX hm0.le)
  have hma : (m : ℝ) * a = max (m : ℝ) k := mul_max_one_div hm0
  have hM2 : (2 : ℝ) ≤ max (m : ℝ) k := le_max_of_le_right hk
  have hD0 : 0 ≤ D := by positivity
  set v : ℝ → ℝ := fun θ => -(∫ x in X..(m * θ), Φ x) / m with hvd
  have hv : ∀ θ, HasDerivAt v (-Φ (m * θ)) θ := fun θ => by
    have h1 : HasDerivAt (fun t => ∫ x in X..t, Φ x) (Φ (m * θ)) (m * θ) :=
      (hΦ.integral_hasStrictDerivAt X (m * θ)).hasDerivAt
    have h2 : HasDerivAt (fun θ : ℝ => (m : ℝ) * θ) (m : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (m : ℝ)
    have h3 := ((h1.comp θ h2).neg).div_const (m : ℝ)
    refine h3.congr_deriv ?_
    field_simp
  have hvb : v b = 0 := by
    simp only [hvd, hbd, mul_div_cancel₀ X hm0.ne', intervalIntegral.integral_same, neg_zero, zero_div]
  have hvbd : ∀ θ ∈ uIcc a b, |v θ| ≤ D := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have hmθ : max (m : ℝ) k ≤ m * θ := by rw [← hma]; exact mul_le_mul_of_nonneg_left hθ.1 hm0.le
    have hmθX : (m : ℝ) * θ ≤ X := by
      have := mul_le_mul_of_nonneg_left hθ.2 hm0.le
      rwa [hbd, mul_div_cancel₀ X hm0.ne'] at this
    have h := hK (m * θ) X (hM2.trans hmθ) hmθX
    simp only [hvd]
    rw [neg_div, abs_neg, abs_div, abs_of_pos hm0, intervalIntegral.integral_symm, abs_neg]
    calc |∫ x in (m * θ)..X, Φ x| / m ≤ K / (m * θ) / m := div_le_div_of_nonneg_right h hm0.le
      _ ≤ K / max (m : ℝ) k / m :=
          div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hK0 (by positivity) hmθ) hm0.le
      _ = D := by rw [hDd]; field_simp
  have hsubI : uIcc a b ⊆ Ioi 0 := fun θ hθ => by
    rw [uIcc_of_le hab] at hθ; exact mem_Ioi.mpr (by linarith [hθ.1])
  have hu' : IntervalIntegrable (fun θ => -(1 / θ) * profTail gamma θ) volume a b :=
    (continuousOn_deriv_Tb.mono hsubI).intervalIntegrable
  have hv' : IntervalIntegrable (fun θ => -Φ (m * θ)) volume a b :=
    (by fun_prop : Continuous fun θ => -Φ (m * θ)).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b) (u := Tb)
    (u' := fun θ => -(1 / θ) * profTail gamma θ) (v := v) (v' := fun θ => -Φ (m * θ))
    (fun θ hθ => hasDerivAt_Tb (hsubI hθ)) (fun θ _ => hv θ) hu' hv'
  rw [hvb, mul_zero, zero_sub] at hibp
  have e : ∫ θ in a..b, Tb θ * Φ (m * θ)
      = Tb a * v a + ∫ θ in a..b, -(1 / θ) * profTail gamma θ * v θ := by
    have : ∫ θ in a..b, Tb θ * -Φ (m * θ) = -∫ θ in a..b, Tb θ * Φ (m * θ) := by
      rw [← intervalIntegral.integral_neg]; congr 1; funext θ; ring
    linarith
  have hvc : ContinuousOn v (uIcc a b) := fun θ _ => (hv θ).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun θ => |-(1 / θ) * profTail gamma θ| * D) volume a b :=
    ((continuousOn_deriv_Tb.mono hsubI).abs.mul continuousOn_const).intervalIntegrable
  have h2 : |∫ θ in a..b, -(1 / θ) * profTail gamma θ * v θ|
      ≤ (∫ θ in a..b, |-(1 / θ) * profTail gamma θ|) * D := by
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_mono_on hab
      (((continuousOn_deriv_Tb.mono hsubI).mul hvc).abs.intervalIntegrable) hint fun θ hθ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hvbd θ (by rw [uIcc_of_le hab]; exact hθ)) (abs_nonneg _)
  have h1 : |Tb a * v a| ≤ |Tb a| * D := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hvbd a left_mem_uIcc) (abs_nonneg _)
  have hW := abs_Tb_add_integral_le ha1 hab
  rw [e]
  calc |Tb a * v a + ∫ θ in a..b, -(1 / θ) * profTail gamma θ * v θ|
      ≤ |Tb a| * D + (∫ θ in a..b, |-(1 / θ) * profTail gamma θ|) * D := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = (|Tb a| + ∫ θ in a..b, |-(1 / θ) * profTail gamma θ|) * D := by ring
    _ ≤ (1 / 2 + V0) * D := mul_le_mul_of_nonneg_right hW hD0

/-- **The mode sum**: `Σ_{m ≤ n} 1/(m·max(m, k)) ≤ (3 + log k)/k` for `k ≥ 2`. -/
theorem sum_inv_mul_max_le {k : ℝ} (hk : 2 ≤ k) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, 1 / ((m : ℝ) * max (m : ℝ) k) ≤ (3 + Real.log k) / k := by
  have hk0 : 0 < k := by linarith
  set q := ⌊k⌋₊ with hqd
  have hq1 : 1 ≤ q := Nat.le_floor (by norm_num; linarith)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqk : (q : ℝ) ≤ k := Nat.floor_le hk0.le
  have hkq : k < q + 1 := Nat.lt_floor_add_one k
  have hf0 : ∀ m : ℕ, 0 ≤ 1 / ((m : ℝ) * max (m : ℝ) k) := fun m => by
    have : (0 : ℝ) ≤ max (m : ℝ) k := le_max_of_le_right hk0.le
    positivity
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun m => m ≤ q)]
  have hA : ∑ m ∈ (Finset.Icc 1 n).filter (fun m => m ≤ q), 1 / ((m : ℝ) * max (m : ℝ) k)
      ≤ (1 + Real.log k) / k := by
    calc ∑ m ∈ (Finset.Icc 1 n).filter (fun m => m ≤ q), 1 / ((m : ℝ) * max (m : ℝ) k)
        ≤ ∑ m ∈ Finset.Icc 1 q, 1 / ((m : ℝ) * max (m : ℝ) k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => by
            simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢; omega) fun m _ _ => hf0 m
      _ = (∑ m ∈ Finset.Icc 1 q, (m : ℝ)⁻¹) / k := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun m hm => ?_
          have hmq : (m : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hm).2
          rw [max_eq_right (hmq.trans hqk)]; field_simp
      _ ≤ (1 + Real.log k) / k := by
          refine div_le_div_of_nonneg_right ?_ hk0.le
          have h := harmonic_le_one_add_log q
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
          exact h.trans (by linarith [Real.log_le_log hq0 hqk])
  have hB : ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬m ≤ q), 1 / ((m : ℝ) * max (m : ℝ) k) ≤ 2 / k := by
    calc ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬m ≤ q), 1 / ((m : ℝ) * max (m : ℝ) k)
        = ∑ m ∈ (Finset.Icc 1 n).filter (fun m => ¬m ≤ q), 1 / (m : ℝ) ^ 2 := by
          refine Finset.sum_congr rfl fun m hm => ?_
          simp only [Finset.mem_filter, Finset.mem_Icc, not_le] at hm
          have : k < m := by
            have h1 : (q : ℝ) + 1 ≤ m := by exact_mod_cast hm.2
            linarith
          rw [max_eq_left this.le, sq]
      _ ≤ ∑ m ∈ Finset.Ioc q n, 1 / (m : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => by
            simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hm ⊢; omega)
            fun m _ _ => by positivity
      _ ≤ 1 / (q : ℝ) := sum_Ioc_one_div_sq_le hq1 n
      _ ≤ 2 / k := by rw [div_le_div_iff₀ hq0 hk0]; linarith
  calc _ ≤ (1 + Real.log k) / k + 2 / k := add_le_add hA hB
    _ = (3 + Real.log k) / k := by ring

/-! ### The prime channel on the span side: `⟨T⁺, F_∞(Φ) − F_k(Φ)⟩` -/

/-- **The mode decomposition** of `⟨T⁺, F_X − F_k⟩` for `1 ≤ k ≤ X`: a sum over `m ≤ X` of
`∫_{max(1,k/m)}^{X/m} T_β(θ)Φ(mθ)`. -/
theorem integral_Psi_mul_posTail_sub {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {k X : ℝ} (hk : 1 ≤ k) (hkX : k ≤ X) :
    ∫ θ in Ioi 1, fullTail Psi θ * (posTail Φ X θ - posTail Φ k θ)
      = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ∫ θ in (max 1 (k / m))..(X / m), Tb θ * Φ (m * θ) := by
  have hX0 : 0 < X := by linarith
  have hS : ∀ m : ℕ, Ioc (max 1 (k / m)) (X / m) ⊆ Ioi 1 := fun m θ hθ =>
    mem_Ioi.mpr (lt_of_le_of_lt (le_max_left _ _) hθ.1)
  have hpt : (fun θ => fullTail Psi θ * (posTail Φ X θ - posTail Φ k θ))
      = fun θ => ∑ m ∈ Finset.Icc 1 ⌊X⌋₊,
          (Ioc (max 1 (k / m)) (X / m)).indicator (fun θ => fullTail Psi θ * Φ (m * θ)) θ := by
    funext θ
    rw [Cvs.L2a.PositionTailSpanAdapters.posTail_sub_posTail Φ hk hkX, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h : θ ∈ Ioc (max 1 (k / m)) (X / m)
    · rw [indicator_of_mem h, indicator_of_mem h]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  have hon : ∀ m : ℕ, 1 ≤ m → IntegrableOn (fun θ => fullTail Psi θ * Φ (m * θ)) (Ioc (max 1 (k / m)) (X / m)) := by
    intro m _
    have hc : ContinuousOn (fun θ => Tb θ * Φ (m * θ)) (Icc (max 1 (k / m)) (X / m)) :=
      (continuousOn_Tb.mono fun θ (hθ : θ ∈ Icc (max 1 (k / m)) (X / m)) => mem_Ioi.mpr (lt_of_lt_of_le one_pos ((le_max_left _ _).trans hθ.1))).mul
        (by fun_prop : Continuous fun θ => Φ (m * θ)).continuousOn
    exact (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
      (fun θ hθ => by rw [fullTail_Psi (hS m hθ)]) measurableSet_Ioc
  rw [hpt, integral_finsetSum _ fun m hm =>
    ((integrable_indicator_iff measurableSet_Ioc).2 (hon m (Finset.mem_Icc.mp hm).1)).integrableOn]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hmX : (m : ℝ) ≤ X := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hm).2) (Nat.floor_le hX0.le)
  have hab : max 1 (k / m) ≤ X / m := max_le ((one_le_div hm0).mpr hmX) (div_le_div_of_nonneg_right hkX hm0.le)
  rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr (hS m), intervalIntegral.integral_of_le hab]
  exact setIntegral_congr_fun measurableSet_Ioc fun θ hθ => by rw [fullTail_Psi (hS m hθ)]

/-- **The span side for `k ≥ 2`**: `|⟨T⁺, F_∞(Φ) − F_k(Φ)⟩| ≤ (½ + V₀)K(3 + log k)/k` when
`|∫_y^Y Φ| ≤ K/y` for `2 ≤ y ≤ Y`. -/
theorem abs_inner_Psi_sub_le_of_two_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {K : ℝ} (hK : ∀ y Y : ℝ, 2 ≤ y → y ≤ Y → |∫ ξ in y..Y, psi c g ξ| ≤ K / y)
    {k : ℝ} (hk : 2 ≤ k) :
    |∫ θ in Ioi 1, fullTail Psi θ * (fullTail (psi c g) θ - posTail (psi c g) k θ)|
      ≤ (1 / 2 + V0) * K * ((3 + Real.log k) / k) := by
  have hΦ : Continuous (psi c g) :=
    (contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  have hk1 : (1 : ℝ) ≤ k := by linarith
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  set Bψ := BG (2 * π) (beta 1 + beta (-1)) (|beta1 1 - beta1 (-1)| + ∫ s in (-1 : ℝ)..1, |beta2 s|)
  -- the finite-`X` bound
  have hX : ∀ X, k ≤ X → |∫ θ in Ioi 1, fullTail Psi θ * (posTail (psi c g) X θ - posTail (psi c g) k θ)|
      ≤ (1 / 2 + V0) * K * ((3 + Real.log k) / k) := fun X hkX => by
    rw [integral_Psi_mul_posTail_sub hΦ hk1 hkX]
    have hX0 : 0 < X := by linarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, |∫ θ in (max 1 (k / m))..(X / m), Tb θ * psi c g (m * θ)|
        ≤ ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, (1 / 2 + V0) * K * (1 / ((m : ℝ) * max (m : ℝ) k)) :=
          Finset.sum_le_sum fun m hm => by
            have hmX : (m : ℝ) ≤ X :=
              le_trans (by exact_mod_cast (Finset.mem_Icc.mp hm).2) (Nat.floor_le hX0.le)
            refine (abs_integral_Tb_mode_le hΦ hK (Finset.mem_Icc.mp hm).1 hk hkX hmX).trans (le_of_eq ?_)
            ring
      _ = (1 / 2 + V0) * K * ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, 1 / ((m : ℝ) * max (m : ℝ) k) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / 2 + V0) * K * ((3 + Real.log k) / k) := by
          have hK0 : 0 ≤ K := by
            have h := hK 2 2 le_rfl le_rfl
            rw [intervalIntegral.integral_same, abs_zero] at h
            linarith [(div_nonneg_iff.mp h).elim (fun h => h.1) fun h => absurd h.2 (by norm_num)]
          exact mul_le_mul_of_nonneg_left (sum_inv_mul_max_le hk _)
            (mul_nonneg (by linarith [V0_nonneg]) hK0)
  -- dominated convergence `X → ∞`
  have hlim : Tendsto (fun X => ∫ θ in Ioi 1, fullTail Psi θ * (posTail (psi c g) X θ - posTail (psi c g) k θ))
      atTop (𝓝 (∫ θ in Ioi 1, fullTail Psi θ * (fullTail (psi c g) θ - posTail (psi c g) k θ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun θ => Bψ * (2 * B) * (1 / θ ^ 2)) ?_ ?_
      ((integrableOn_one_div_sq one_pos).const_mul _) ?_
    · exact Eventually.of_forall fun X => (measurable_fullTail_Psi.mul
        ((measurable_posTail_psi hg c X).sub (measurable_posTail_psi hg c k))).aestronglyMeasurable
    · refine Eventually.of_forall fun X => (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_)
      have hθ0 : 0 < θ := by linarith
      have h1 := abs_fullTail_Psi_le_BG hθ0
      have h2 := abs_posTail_le hg hg₁ hg₂c hc X hθ0
      have h3 := abs_posTail_le hg hg₁ hg₂c hc k hθ0
      have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
      rw [Real.norm_eq_abs, abs_mul]
      calc |fullTail Psi θ| * |posTail (psi c g) X θ - posTail (psi c g) k θ| ≤ Bψ / θ * (2 * B / θ) :=
            mul_le_mul h1 ((abs_sub _ _).trans (by rw [mul_div_assoc, two_mul]; linarith))
              (abs_nonneg _) ((abs_nonneg _).trans h1)
        _ = Bψ * (2 * B) * (1 / θ ^ 2) := by field_simp
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_)
      exact tendsto_const_nhds.mul ((Cvs.L2a.FullTailPrimeChannel.tendsto_posTail hg hg₁ hg₂c hc hθ).sub_const _)
  exact le_of_tendsto hlim.abs ((eventually_ge_atTop k).mono fun X hkX => hX X hkX)

/-- For `k ≤ 2` only the mode `m = 1` truncates: `F_k(Φ) = Φ·1_{(1,k]}`. -/
theorem posTail_of_le_two (Φ : ℝ → ℝ) {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 2) (θ : ℝ) :
    posTail Φ k θ = (Ioc 1 k).indicator Φ θ := by
  rw [posTail_eq_sum, Finset.sum_eq_single 1]
  · simp only [Nat.cast_one, div_one, one_mul]
  · intro m hm hm1
    have hm2 : (2 : ℝ) ≤ m := by
      have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (show 2 ≤ m by omega)
    refine indicator_of_notMem (fun h => ?_) _
    have h1 : k / m ≤ 1 := (div_le_one (by linarith)).mpr (hk.trans hm2)
    linarith [h.1, h.2]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_floor (by exact_mod_cast hk1)⟩) h

/-- **The span side for `1 < k ≤ 2`**: `|⟨T⁺, F_∞(Φ) − F_k(Φ)⟩| ≤ ‖T⁺‖(√N + √Q)`, `Q = ∫_{(1,∞)} Φ²`. -/
theorem abs_inner_Psi_sub_le_of_le_two (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (hΦ2 : IntegrableOn (fun ξ => psi c g ξ ^ 2) (Ioi 1)) {k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 2) :
    |∫ θ in Ioi 1, fullTail Psi θ * (fullTail (psi c g) θ - posTail (psi c g) k θ)|
      ≤ normT * (√(∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) + √(∫ ξ in Ioi 1, psi c g ξ ^ 2)) := by
  set T := fullTail Psi
  set F := fullTail (psi c g)
  set P := posTail (psi c g) k
  have hTm := measurable_fullTail_Psi
  have hFm := measurable_fullTail hg hg₁ hg₂c hc
  have hPm := measurable_posTail_psi hg c k
  have hTb := fun θ (hθ : 0 < θ) => abs_fullTail_Psi_le_BG hθ
  have hFb := fun θ (hθ : 0 < θ) => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hPb := fun θ (hθ : 0 < θ) => abs_posTail_le hg hg₁ hg₂c hc k hθ
  have iTF : IntegrableOn (fun θ => T θ * F θ) (Ioi 1) := integrableOn_mul_of_le hTm hFm hTb hFb
  have iTP : IntegrableOn (fun θ => T θ * P θ) (Ioi 1) := integrableOn_mul_of_le hTm hPm hTb hPb
  have hT2 : IntegrableOn (fun θ => T θ ^ 2) (Ioi 1) := fullTail_Psi_sq.1
  have hF2 : IntegrableOn (fun θ => F θ ^ 2) (Ioi 1) := integrableOn_sq_of_le hFm hFb
  have hP2 : IntegrableOn (fun θ => P θ ^ 2) (Ioi 1) := integrableOn_sq_of_le hPm hPb
  have hPQ : ∫ θ in Ioi 1, P θ ^ 2 ≤ ∫ ξ in Ioi 1, psi c g ξ ^ 2 := by
    refine setIntegral_mono_on hP2 hΦ2 measurableSet_Ioi fun θ _ => ?_
    simp only [P]
    rw [posTail_of_le_two _ hk1 hk]
    by_cases h : θ ∈ Ioc 1 k
    · rw [indicator_of_mem h]
    · rw [indicator_of_notMem h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  have e : ∫ θ in Ioi 1, T θ * (F θ - P θ) = (∫ θ in Ioi 1, T θ * F θ) - ∫ θ in Ioi 1, T θ * P θ := by
    rw [← integral_sub iTF iTP]; congr 1; funext θ; ring
  rw [e]
  have h1 := abs_setIntegral_mul_le hT2 hF2 iTF
  have h2 := (abs_setIntegral_mul_le hT2 hP2 iTP).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hPQ) (Real.sqrt_nonneg _))
  calc |(∫ θ in Ioi 1, T θ * F θ) - ∫ θ in Ioi 1, T θ * P θ|
      ≤ |∫ θ in Ioi 1, T θ * F θ| + |∫ θ in Ioi 1, T θ * P θ| := abs_sub _ _
    _ ≤ normT * √(∫ θ in Ioi 1, F θ ^ 2) + normT * √(∫ ξ in Ioi 1, psi c g ξ ^ 2) := add_le_add h1 h2
    _ = _ := by ring

/-- **The `Ψ` side**: `|⟨F_∞(Φ), T⁺ − F_k(Ψ)⟩| ≤ √N ‖F_k(Ψ) − T⁺‖`. -/
theorem abs_inner_sub_Psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (k : ℝ) :
    |∫ θ in Ioi 1, fullTail (psi c g) θ * (fullTail Psi θ - posTail Psi k θ)|
      ≤ √(∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) * √(∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2) := by
  have hFm := measurable_fullTail hg hg₁ hg₂c hc
  have hFb := fun θ (hθ : 0 < θ) => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hDm : Measurable fun θ => fullTail Psi θ - posTail Psi k θ :=
    measurable_fullTail_Psi.sub (measurable_posTail continuous_Psi k)
  have hDb : ∀ θ, 0 < θ → |fullTail Psi θ - posTail Psi k θ| ≤ _ / θ := fun θ hθ => by
    rw [abs_sub_comm]; exact abs_posTail_sub_fullTail_Psi_le k hθ
  have e : ∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2
      = ∫ θ in Ioi 1, (fullTail Psi θ - posTail Psi k θ) ^ 2 := by congr 1; funext θ; ring
  rw [e]
  exact abs_setIntegral_mul_le (integrableOn_sq_of_le hFm hFb) (integrableOn_sq_of_le hDm hDb)
    (integrableOn_mul_of_le hFm hDm hFb hDb)

/-- **The log term**: `|∫_{(1,∞)} log θ F_∞(Φ) T⁺| ≤ √N ‖log θ T⁺‖`. -/
theorem abs_integral_log_Psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    |∫ θ in Ioi 1, Real.log θ * (fullTail (psi c g) θ * fullTail Psi θ)|
      ≤ √(∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) * normLogT := by
  have hFm := measurable_fullTail hg hg₁ hg₂c hc
  have hFb := fun θ (hθ : 0 < θ) => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hi := integrableOn_log_mul_of_le hFm measurable_fullTail_Psi hFb fun θ hθ => abs_fullTail_Psi_le_BG hθ
  have e : (fun θ => Real.log θ * (fullTail (psi c g) θ * fullTail Psi θ))
      = fun θ => fullTail (psi c g) θ * (Real.log θ * fullTail Psi θ) := by funext θ; ring
  rw [e] at hi ⊢
  exact abs_setIntegral_mul_le (integrableOn_sq_of_le hFm hFb) log_fullTail_Psi_sq.1 hi

/-! ### The level integrals in `k` -/

/-- **`k ↦ ‖F_k(Ψ) − T⁺‖/k` is integrable on `(1, ∞)`**, so `C_L1` is an absolutely convergent integral. -/
theorem integrableOn_CL1 :
    IntegrableOn (fun k => √(∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2) / k) (Ioi 1) := by
  have hf : Measurable fun p : ℝ × ℝ => (posTail Psi p.1 p.2 - fullTail Psi p.2) ^ 2 :=
    ((Cvs.L2a.FullTailPrimeChannel.measurable_posTail_uncurry continuous_Psi).sub
      (measurable_fullTail_Psi.comp measurable_snd)).pow_const 2
  have hm : Measurable fun k => ∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2 :=
    (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (1 : ℝ)))).measurable
  set C := C1beta * √(1 / (2 * π ^ 4) + 1 / 576)
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (show -(5 / 4 : ℝ) < -1 by norm_num) one_pos).const_mul C)
    (hm.sqrt.div measurable_id).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun k (hk : 1 < k) => ?_))
  have hk0 : 0 < k := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc √(∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2) / k ≤ C * k ^ (-(1 / 4 : ℝ)) / k :=
        div_le_div_of_nonneg_right (norm_posTail_sub_fullTail_Psi_le hk.le) hk0.le
    _ = C * k ^ (-(5 / 4 : ℝ)) := by
        rw [mul_div_assoc, show -(5 / 4 : ℝ) = -(1 / 4) + -1 by norm_num, rpow_add hk0, rpow_neg_one]
        ring

/-- `−(4 + log k)/k` is a primitive of `(3 + log k)/k²` on `k > 0`. -/
theorem hasDerivAt_log_prim {k : ℝ} (hk : 0 < k) :
    HasDerivAt (fun k => -((4 + Real.log k) / k)) ((3 + Real.log k) / k ^ 2) k := by
  have h1 : HasDerivAt (fun k => 4 + Real.log k) k⁻¹ k := by
    exact (Real.hasDerivAt_log hk.ne').const_add 4
  refine ((h1.div (hasDerivAt_id' k) hk.ne').neg).congr_deriv ?_
  field_simp
  ring

theorem tendsto_log_prim : Tendsto (fun k : ℝ => -((4 + Real.log k) / k)) atTop (𝓝 0) := by
  have h4 : Tendsto (fun k : ℝ => 4 / k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hl : Tendsto (fun k : ℝ => Real.log k / k) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have := (h4.add hl).neg
  simp only [add_zero, neg_zero] at this
  refine this.congr fun k => ?_
  ring

/-- **`∫_{(2,∞)} (3 + log k)/k² = 2 + ½ log 2`**, with integrability. -/
theorem integral_log_div_sq :
    IntegrableOn (fun k => (3 + Real.log k) / k ^ 2) (Ioi 2)
      ∧ ∫ k in Ioi (2 : ℝ), (3 + Real.log k) / k ^ 2 = 2 + Real.log 2 / 2 := by
  have hcont : ContinuousWithinAt (fun k : ℝ => -((4 + Real.log k) / k)) (Ici 2) 2 :=
    (hasDerivAt_log_prim two_pos).continuousAt.continuousWithinAt
  have hder : ∀ k ∈ Ioi (2 : ℝ), HasDerivAt (fun k => -((4 + Real.log k) / k)) ((3 + Real.log k) / k ^ 2) k :=
    fun k hk => hasDerivAt_log_prim (lt_trans two_pos hk)
  have hpos : ∀ k ∈ Ioi (2 : ℝ), 0 ≤ (3 + Real.log k) / k ^ 2 := fun k hk => by
    have : 0 ≤ Real.log k := Real.log_nonneg (by linarith [mem_Ioi.mp hk])
    positivity
  have hi := integrableOn_Ioi_deriv_of_nonneg hcont hder hpos tendsto_log_prim
  refine ⟨hi, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hder hi tendsto_log_prim]
  ring

/-- `∫_{(1,2]} C/k = C log 2`. -/
theorem integral_Ioc_div (C : ℝ) : ∫ k in Ioc (1 : ℝ) 2, C / k = C * Real.log 2 := by
  rw [← intervalIntegral.integral_of_le one_le_two]
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos two_pos, div_one]

/-! ### The prime channel -/

/-- **The prime channel against `T⁺`**, split at `k = 2`: with `|∫_y^Y Φ| ≤ K/y` for `2 ≤ y ≤ Y`,
`|Prime(Φ, Ψ)| ≤ (C_L1 + log 2 ‖T⁺‖ + 2‖log θ T⁺‖)√N + log 2 ‖T⁺‖ √Q + (½ + V₀)(2 + ½ log 2)K`. -/
theorem abs_primeBil_Psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (hΦ2 : IntegrableOn (fun ξ => psi c g ξ ^ 2) (Ioi 1)) {K : ℝ}
    (hK : ∀ y Y : ℝ, 2 ≤ y → y ≤ Y → |∫ ξ in y..Y, psi c g ξ| ≤ K / y) :
    |primeBil (psi c g) Psi|
      ≤ (CL1 + Real.log 2 * normT + 2 * normLogT) * √(∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)
        + Real.log 2 * normT * √(∫ ξ in Ioi 1, psi c g ξ ^ 2) + (1 / 2 + V0) * (2 + Real.log 2 / 2) * K := by
  set F := fullTail (psi c g)
  set T := fullTail Psi
  set sN := √(∫ θ in Ioi 1, F θ ^ 2)
  set sQ := √(∫ ξ in Ioi 1, psi c g ξ ^ 2)
  set W := 1 / 2 + V0
  set q : ℝ → ℝ := fun k => √(∫ θ in Ioi 1, (posTail Psi k θ - fullTail Psi θ) ^ 2)
  have hsN : 0 ≤ sN := Real.sqrt_nonneg _
  have hsQ : 0 ≤ sQ := Real.sqrt_nonneg _
  have hnT : 0 ≤ normT := Real.sqrt_nonneg _
  have hW : 0 ≤ W := add_nonneg (by norm_num) V0_nonneg
  have hK0 : 0 ≤ K := by
    have h := hK 2 2 le_rfl le_rfl
    rw [intervalIntegral.integral_same, abs_zero] at h
    linarith [(div_nonneg_iff.mp h).elim (fun h => h.1) fun h => absurd h.2 (by norm_num)]
  set f2 : ℝ → ℝ := fun k => normT * (sN + sQ) / k
  set f3 : ℝ → ℝ := fun k => W * K * ((3 + Real.log k) / k ^ 2)
  set h : ℝ → ℝ := fun k => sN * (q k / k) + (Ioc 1 2).indicator f2 k + (Ioi 2).indicator f3 k
  have i1 : IntegrableOn (fun k => sN * (q k / k)) (Ioi 1) := integrableOn_CL1.const_mul sN
  have i2 : IntegrableOn ((Ioc 1 2).indicator f2) (Ioi 1) := by
    refine ((integrable_indicator_iff measurableSet_Ioc).2 ?_).integrableOn
    exact ((continuousOn_const.div continuousOn_id fun k (hk : k ∈ Icc (1 : ℝ) 2) => (lt_of_lt_of_le one_pos hk.1).ne').integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have i3 : IntegrableOn ((Ioi 2).indicator f3) (Ioi 1) :=
    ((integrable_indicator_iff measurableSet_Ioi).2 (integral_log_div_sq.1.const_mul (W * K))).integrableOn
  have hint : IntegrableOn h (Ioi 1) := (i1.add i2).add i3
  have hval : ∫ k in Ioi 1, h k = sN * CL1 + normT * (sN + sQ) * Real.log 2 + W * K * (2 + Real.log 2 / 2) := by
    have e1 : ∫ k in Ioi 1, h k = (∫ k in Ioi 1, (sN * (q k / k) + (Ioc 1 2).indicator f2 k))
        + ∫ k in Ioi 1, (Ioi 2).indicator f3 k := integral_add (i1.add i2) i3
    have e2 : ∫ k in Ioi 1, (sN * (q k / k) + (Ioc 1 2).indicator f2 k)
        = (∫ k in Ioi 1, sN * (q k / k)) + ∫ k in Ioi 1, (Ioc 1 2).indicator f2 k := integral_add i1 i2
    rw [e1, e2, integral_const_mul,
      setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr Ioc_subset_Ioi_self, inter_eq_right.mpr (Ioi_subset_Ioi one_le_two),
      integral_Ioc_div, integral_const_mul, integral_log_div_sq.2]
    rfl
  -- the pointwise bound in `k`
  have hFm := measurable_fullTail hg hg₁ hg₂c hc
  have hFb := fun θ (hθ : 0 < θ) => abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hTm := measurable_fullTail_Psi
  have hTb := fun θ (hθ : 0 < θ) => abs_fullTail_Psi_le_BG hθ
  have hpt : ∀ k ∈ Ioi (1 : ℝ),
      ‖(∫ θ in Ioi 1, (F θ * (T θ - posTail Psi k θ) + T θ * (F θ - posTail (psi c g) k θ))) / k‖ ≤ h k := by
    intro k hk
    have hk1 : 1 < k := hk
    have hk0 : 0 < k := by linarith
    have hDm : Measurable fun θ => T θ - posTail Psi k θ := hTm.sub (measurable_posTail continuous_Psi k)
    have hDb : ∀ θ, 0 < θ → |T θ - posTail Psi k θ| ≤ _ / θ := fun θ hθ => by
      rw [abs_sub_comm]; exact abs_posTail_sub_fullTail_Psi_le k hθ
    have hEm : Measurable fun θ => F θ - posTail (psi c g) k θ := hFm.sub (measurable_posTail_psi hg c k)
    have hEb : ∀ θ, 0 < θ → |F θ - posTail (psi c g) k θ| ≤ _ / θ := fun θ hθ => by
      rw [abs_sub_comm]; exact abs_posTail_sub_le hg hg₁ hg₂c hc k hθ
    rw [integral_add (integrableOn_mul_of_le hFm hDm hFb hDb) (integrableOn_mul_of_le hTm hEm hTb hEb),
      Real.norm_eq_abs, abs_div, abs_of_pos hk0]
    have hL1 := abs_inner_sub_Psi_le hg hg₁ hg₂c hc k
    have hL2 : |∫ θ in Ioi 1, T θ * (F θ - posTail (psi c g) k θ)|
        ≤ k * ((Ioc 1 2).indicator f2 k + (Ioi 2).indicator f3 k) := by
      rcases le_or_gt k 2 with hk2 | hk2
      · rw [indicator_of_mem (show k ∈ Ioc 1 2 from ⟨hk1, hk2⟩),
          indicator_of_notMem (show k ∉ Ioi 2 from fun h => absurd (mem_Ioi.mp h) (not_lt.mpr hk2)), add_zero]
        refine (abs_inner_Psi_sub_le_of_le_two hg hg₁ hg₂c hc hΦ2 hk1.le hk2).trans (le_of_eq ?_)
        simp only [f2]; field_simp; try rfl
      · rw [indicator_of_notMem (show k ∉ Ioc 1 2 from fun h => absurd h.2 (not_le.mpr hk2)),
          indicator_of_mem (show k ∈ Ioi 2 from hk2), zero_add]
        refine (abs_inner_Psi_sub_le_of_two_le hg hg₁ hg₂c hc hK hk2.le).trans (le_of_eq ?_)
        simp only [f3, W]; field_simp; try ring
    rw [div_le_iff₀ hk0]
    calc |(∫ θ in Ioi 1, F θ * (T θ - posTail Psi k θ)) + ∫ θ in Ioi 1, T θ * (F θ - posTail (psi c g) k θ)|
        ≤ sN * q k + k * ((Ioc 1 2).indicator f2 k + (Ioi 2).indicator f3 k) := (abs_add_le _ _).trans
          (add_le_add hL1 hL2)
      _ = h k * k := by simp only [h]; field_simp; try ring
  have hA : |∫ k in Ioi 1,
      (∫ θ in Ioi 1, (F θ * (T θ - posTail Psi k θ) + T θ * (F θ - posTail (psi c g) k θ))) / k|
      ≤ ∫ k in Ioi 1, h k := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
  have hLog := abs_integral_log_Psi_le hg hg₁ hg₂c hc
  unfold primeBil
  rw [hval] at hA
  calc |(∫ k in Ioi 1,
        (∫ θ in Ioi 1, (F θ * (T θ - posTail Psi k θ) + T θ * (F θ - posTail (psi c g) k θ))) / k)
        - 2 * ∫ θ in Ioi 1, Real.log θ * (F θ * T θ)|
      ≤ |∫ k in Ioi 1,
          (∫ θ in Ioi 1, (F θ * (T θ - posTail Psi k θ) + T θ * (F θ - posTail (psi c g) k θ))) / k|
        + |2 * ∫ θ in Ioi 1, Real.log θ * (F θ * T θ)| := abs_sub _ _
    _ ≤ (sN * CL1 + normT * (sN + sQ) * Real.log 2 + W * K * (2 + Real.log 2 / 2)) + 2 * (sN * normLogT) := by
        rw [abs_mul, abs_two]; exact add_le_add hA (mul_le_mul_of_nonneg_left hLog two_pos.le)
    _ = _ := by ring

end rung

/-! ### On the span of rungs -/

section span

variable {ι : Type} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}

/-- **TI on the span, at finite `Y`**: `|∫_y^Y Φ| ≤ 3√(6J)·y/(c(y² − 1))·√P` for `6/5 ≤ y ≤ Y`. -/
theorem abs_integral_span_le (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) {y Y : ℝ} (hy : 6 / 5 ≤ y) (hyY : y ≤ Y) :
    |∫ ξ in y..Y, ∑ i, b i * psi c (g i) ξ|
      ≤ 3 * √(6 * (Fintype.card ι : ℝ)) * y / (c * (y ^ 2 - 1))
        * √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) := by
  set M : ι → ℝ := fun i => ∫ t in Ioi 1, psi c (g i) t ^ 2 with hMdef
  have hM : ∀ i, 0 ≤ M i := fun i => setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
  have hc0 : 0 < c := by linarith
  have hyp : 0 < y ^ 2 - 1 := by nlinarith
  have hψ : ∀ i, Continuous (psi c (g i)) := fun i =>
    (contDiff_psi (fun s hs => (hg i s hs).continuousAt.continuousWithinAt) c).continuous
  set B := 3 * √6 * y / (c * (y ^ 2 - 1)) with hBdef
  have hB : 0 ≤ B := by positivity
  rw [intervalIntegral.integral_finsetSum fun i _ => ((hψ i).intervalIntegrable _ _).const_mul _]
  have hi : ∀ i, |∫ ξ in y..Y, b i * psi c (g i) ξ| ≤ B * (|b i| * √(M i)) := fun i => by
    rw [intervalIntegral.integral_const_mul, abs_mul]
    have h := Cvs.Prolate.RungTailIntegralMass.abs_integral_psi_le_mass (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i)
      (hχc i) hy hyY
    have e : 3 * √(6 * M i) * y / (c * (y ^ 2 - 1)) = B * √(M i) := by
      rw [hBdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]; ring
    rw [e] at h
    calc |b i| * |∫ ξ in y..Y, psi c (g i) ξ| ≤ |b i| * (B * √(M i)) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = B * (|b i| * √(M i)) := by ring
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) (fun i => |b i| * √(M i))
  have e1 : ∑ _i : ι, (1 : ℝ) ^ 2 = (Fintype.card ι : ℝ) := by simp
  have e2 : ∑ i, (|b i| * √(M i)) ^ 2 = ∑ i, b i ^ 2 * M i := Finset.sum_congr rfl fun i _ => by
    rw [mul_pow, sq_abs, Real.sq_sqrt (hM i)]
  rw [e1, e2] at hCS
  simp only [one_mul] at hCS
  have e3 : 3 * √(6 * (Fintype.card ι : ℝ)) * y / (c * (y ^ 2 - 1)) = B * √(Fintype.card ι : ℝ) := by
    rw [hBdef, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]; ring
  rw [e3]
  calc |∑ i, ∫ ξ in y..Y, b i * psi c (g i) ξ| ≤ ∑ i, |∫ ξ in y..Y, b i * psi c (g i) ξ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, B * (|b i| * √(M i)) := Finset.sum_le_sum fun i _ => hi i
    _ = B * ∑ i, |b i| * √(M i) := by rw [Finset.mul_sum]
    _ ≤ B * (√(Fintype.card ι : ℝ) * √(∑ i, b i ^ 2 * M i)) := mul_le_mul_of_nonneg_left hCS hB
    _ = B * √(Fintype.card ι : ℝ) * √(∑ i, b i ^ 2 * M i) := by ring

/-- **TI in the form the prime channel takes**: `|∫_y^Y Φ| ≤ (4√(6J)/c)√P / y` for `2 ≤ y ≤ Y`,
since `y/(y² − 1) ≤ 4/(3y)` there. -/
theorem abs_integral_span_le_div (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) {y Y : ℝ} (hy : 2 ≤ y) (hyY : y ≤ Y) :
    |∫ ξ in y..Y, ∑ i, b i * psi c (g i) ξ|
      ≤ 4 * √(6 * (Fintype.card ι : ℝ)) / c * √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) / y := by
  refine (abs_integral_span_le b hg hg₁ hg₂c hang hc hχ0 hχc (by linarith) hyY).trans ?_
  set A := √(6 * (Fintype.card ι : ℝ))
  set S := √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2)
  have hc0 : 0 < c := by linarith
  have hy0 : 0 < y := by linarith
  have hyp : 0 < y ^ 2 - 1 := by nlinarith
  have hAS : 0 ≤ A * S / c := by positivity
  have key : 3 * y / (y ^ 2 - 1) ≤ 4 / y := by
    rw [div_le_div_iff₀ hyp hy0]; nlinarith
  calc 3 * A * y / (c * (y ^ 2 - 1)) * S = A * S / c * (3 * y / (y ^ 2 - 1)) := by field_simp
    _ ≤ A * S / c * (4 / y) := mul_le_mul_of_nonneg_left key hAS
    _ = 4 * A / c * S / y := by field_simp

/-- The span is the transform of the combined profile: `Σ bᵢ psi c gᵢ = psi c (Σ bᵢ gᵢ)`. -/
theorem span_eq_psi (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s) :
    (fun ξ => ∑ i, b i * psi c (g i) ξ) = psi c (fun s => ∑ i, b i * g i s) :=
  funext fun ξ => (psi_sum Finset.univ b g (fun i _ =>
    (ContinuousOn.intervalIntegrable fun s hs => (hg i s hs).continuousAt.continuousWithinAt)) c ξ).symm

theorem hasDerivAt_span (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s) :
    ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => ∑ i, b i * g i s) (∑ i, b i * g₁ i s) s :=
  fun s hs => HasDerivAt.fun_sum fun i _ => (hg i s hs).const_mul (b i)

/-- **The pole channel on the span**: `|Pole(Φ, Ψ)| ≤ (59/630) C_π √P + |Π₊(Ψ)| √N`. -/
theorem pole_bil_le (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχ : Function.Injective χ) :
    |poleBil (fun ξ => ∑ i, b i * psi c (g i) ξ) Psi|
      ≤ 59 / 630 * Cvs.Prolate.RungTailIntegralMass.piConst (Fintype.card ι) c
          * √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2)
        + |Cvs.L2a.FullTailPoleChannel.piPlus Psi|
          * √(∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ ^ 2) := by
  have hc0 : 0 < c := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (g i) ξ with hΦdef
  have e : Φ = psi c (fun s => ∑ i, b i * g i s) := span_eq_psi b hg
  have h := abs_poleBil_Psi_le (hasDerivAt_span b hg) (hasDerivAt_span b hg₁)
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hg₂c i)) hc0
  rw [← e] at h
  refine h.trans (add_le_add ?_ le_rfl)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (Cvs.Prolate.RungTailIntegralMass.abs_piPlus_span_le b hg hg₁ hg₂c hang hc hχ0 hχc hχ)
    (by norm_num)

/-- **The arch channel on the span**: `|Arch(Φ, Ψ)| ≤ C_A √N`. -/
theorem arch_bil_le (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1)) (hc : 2 * π ≤ c) :
    |archBil (fun ξ => ∑ i, b i * psi c (g i) ξ) Psi|
      ≤ CA * √(∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ ^ 2) := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (g i) ξ with hΦdef
  have e : Φ = psi c (fun s => ∑ i, b i * g i s) := span_eq_psi b hg
  have h := abs_archBil_Psi_le (hasDerivAt_span b hg) (hasDerivAt_span b hg₁)
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hg₂c i)) hc
  rwa [← e] at h

/-- **The prime channel on the span**, split at `k = 2`:
`|Prime(Φ, Ψ)| ≤ (C_L1 + log 2 ‖T⁺‖ + 2‖log θ T⁺‖)√N + (log 2 ‖T⁺‖ + (4√(6J)/c)(½ + V₀)(2 + ½ log 2))√P`. -/
theorem prime_bil_le (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχ : Function.Injective χ) :
    |primeBil (fun ξ => ∑ i, b i * psi c (g i) ξ) Psi|
      ≤ (CL1 + Real.log 2 * normT + 2 * normLogT)
          * √(∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, b i * psi c (g i) ξ) θ ^ 2)
        + (Real.log 2 * normT
            + 4 * √(6 * (Fintype.card ι : ℝ)) / c * (1 / 2 + V0) * (2 + Real.log 2 / 2))
          * √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) := by
  have hc0 : 0 < c := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, b i * psi c (g i) ξ with hΦdef
  set S := √(∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) with hSdef
  have e : Φ = psi c (fun s => ∑ i, b i * g i s) := span_eq_psi b hg
  have hmem : MemLp Φ 2 (volume.restrict (Ioi 1)) :=
    memLp_finsetSum Finset.univ fun i _ =>
      (Cvs.Prolate.RungExactOrthogonality.memLp_psi (hg i) (hg₁ i) (hg₂c i) (hang i) hc0).const_mul (b i)
  have hint : IntegrableOn (fun t => Φ t ^ 2) (Ioi 1) := hmem.integrable_sq
  have hQ : ∫ ξ in Ioi 1, Φ ξ ^ 2 = ∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 :=
    Cvs.Prolate.RungExactOrthogonality.integral_span_sq b hg hg₁ hg₂c hang hc0 hχ
  have hK : ∀ y Y : ℝ, 2 ≤ y → y ≤ Y →
      |∫ ξ in y..Y, psi c (fun s => ∑ i, b i * g i s) ξ| ≤ 4 * √(6 * (Fintype.card ι : ℝ)) / c * S / y := by
    intro y Y hy hyY
    rw [← e]
    exact abs_integral_span_le_div b hg hg₁ hg₂c hang hc hχ0 hχc hy hyY
  rw [e] at hint
  have h := abs_primeBil_Psi_le (hasDerivAt_span b hg) (hasDerivAt_span b hg₁)
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hg₂c i)) hc0 hint hK
  rw [← e, hQ] at h
  refine h.trans (le_of_eq ?_)
  ring

end span

end Cvs.L2a.FullTailBilinearChannels
