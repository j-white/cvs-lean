import Mathlib
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.TailLogScaleTest
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
# The θ-space Weil form and Parseval on the critical line

`weilθ F G` is the polarised Weil form written on `(0, ∞)`: pole channel `P₊P₋`, the spectral arch channel
`∫ a(t) ρ_{f,g}(t) dt`, and the full von Mangoldt sum of dilates. On `Re s = ½` the cross density is
`Re(MF(1 − s) MG(s))/2π`, so `∫_{θ>0} F G = (1/2π) ∫ Re(MF(1 − s) MG(s)) dt`.
-/

namespace Cvs.WeilForm.ThetaSpaceParseval

open Real Set Filter Topology MeasureTheory
open Complex (I)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.FullTailPolarisation (crossSpec)
open scoped FourierTransform ComplexConjugate

/-! ### Definitions -/

/-- The Mellin transform of a real function, `∫_{θ>0} θ^{s−1} F(θ) dθ`. -/
noncomputable def mellinR (F : ℝ → ℝ) (s : ℂ) : ℂ := mellin (fun θ => (F θ : ℂ)) s

/-- The improper integral `P₊F = lim_{Y→∞} ∫₀^Y F`. -/
noncomputable def poleP (F : ℝ → ℝ) : ℝ := limUnder atTop fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, F θ

/-- The pole functional `P₋F = ∫_{θ>0} F(θ)/θ dθ`. -/
noncomputable def poleM (F : ℝ → ℝ) : ℝ := ∫ θ in Ioi (0 : ℝ), F θ / θ

/-- The dilate pairing `⟨F, G(n·)⟩ = ∫_{θ>0} F(θ) G(nθ) dθ`. -/
noncomputable def dil (F G : ℝ → ℝ) (n : ℕ) : ℝ := ∫ θ in Ioi (0 : ℝ), F θ * G (n * θ)

/-- The θ-space polarised Weil form: pole plus spectral arch less the von Mangoldt sum of dilates. -/
noncomputable def weilθ (F G : ℝ → ℝ) : ℝ :=
  poleP F * poleM G + poleM F * poleP G
    + (∫ t, archSymbol t * crossSpec (logScale F) (logScale G) t)
    - ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F G n + dil G F n)

/-! ### Parseval for the cross density -/

/-- **Parseval for the cross density**: `∫ ρ_{f,k} = ∫ f k` on `L¹ ∩ L²`. -/
theorem integral_crossSpec {f k : ℝ → ℝ} (hf : Integrable f) (hf2 : MemLp f 2 volume)
    (hk : Integrable k) (hk2 : MemLp k 2 volume) :
    ∫ t, crossSpec f k t = ∫ x, f x * k x := by
  have hs1 : Integrable (fun x => f x + 1 * k x) := hf.add (hk.const_mul 1)
  have hs2 : MemLp (fun x => f x + 1 * k x) 2 volume := hf2.add (hk2.const_mul 1)
  have iS := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hs2 hs1
  have iF := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf
  have iK := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hk2 hk
  have e : ∀ t, crossSpec f k t
      = (Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => f x + 1 * k x) t
        - Cvs.WeilForm.SelfConvolutionCosine.specDensity f t - Cvs.WeilForm.SelfConvolutionCosine.specDensity k t) / 2 := by
    intro t; rw [Cvs.L2a.FullTailPolarisation.specDensity_add_smul hf hk 1 t]; ring
  have qS : Integrable (fun x => (f x + 1 * k x) ^ 2) := hs2.integrable_sq
  have qF : Integrable (fun x => f x ^ 2) := hf2.integrable_sq
  have qK : Integrable (fun x => k x ^ 2) := hk2.integrable_sq
  have qFK : Integrable (fun x => f x * k x) := hf2.integrable_mul hk2
  have iSF : Integrable (fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => f x + 1 * k x) t
      - Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) := iS.sub iF
  have qSF : Integrable (fun x => (f x + 1 * k x) ^ 2 - f x ^ 2) := qS.sub qF
  rw [integral_congr_ae (Eventually.of_forall e), integral_div, integral_sub iSF iK,
    integral_sub iS iF, Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity hs1 hs2,
    Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity hf hf2, Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity hk hk2,
    ← integral_sub qS qF, ← integral_sub qSF qK, ← integral_div]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

/-! ### The Mellin transform on the critical line -/

/-- **Mellin transforms of real functions commute with conjugation**: `conj (MF s) = MF (conj s)`. -/
theorem mellinR_conj (F : ℝ → ℝ) (s : ℂ) : conj (mellinR F s) = mellinR F (conj s) := by
  unfold mellinR mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
  have harg : (θ : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt hθ)]; exact Real.pi_pos.ne
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [show conj s - 1 = conj (s - 1) by simp, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- **The Fourier transform of the log-scale function is the Mellin transform on `Re s = ½`**:
`𝓕 f (t/2π) = MF(½ − it)`, `f(x) = F(eˣ)e^{x/2}`. -/
theorem fourier_logScale (F : ℝ → ℝ) (t : ℝ) :
    𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (logScale F)) (t / (2 * π)) = mellinR F (1 / 2 - t * I) := by
  have hre : ((1 : ℂ) / 2 - t * I).re = 1 / 2 := by simp
  have him : ((1 : ℂ) / 2 - t * I).im = -t := by simp
  unfold mellinR
  rw [mellin_eq_fourier, hre, him, Real.fourier_eq, Real.fourier_eq, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, logScale, Real.inner_apply, Complex.real_smul]
  push_cast
  congr 1
  · congr 2; ring
  · rw [mul_comm]; congr 2; ring_nf

/-- **The cross density of log-scale functions** is `Re(MF(1 − s) MG(s))/2π` at `s = ½ + it`. -/
theorem crossSpec_logScale (F G : ℝ → ℝ) (t : ℝ) :
    crossSpec (logScale F) (logScale G) t
      = (mellinR F (1 - (1 / 2 + t * I)) * mellinR G (1 / 2 + t * I)).re / (2 * π) := by
  have hc : conj ((1 : ℂ) / 2 - t * I) = 1 / 2 + t * I := by apply Complex.ext <;> simp
  unfold crossSpec
  rw [fourier_logScale, fourier_logScale, mellinR_conj, hc,
    show (1 : ℂ) - (1 / 2 + t * I) = 1 / 2 - t * I by ring]

/-- The substitution `θ = eˣ` over the whole line. -/
theorem integral_exp_smul_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x, exp x • g (exp x) = ∫ θ in Ioi (0 : ℝ), g θ := by
  rw [← Real.range_exp, ← image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g,
    Measure.restrict_univ]
  simp only [abs_of_pos (exp_pos _)]

/-- **Parseval on the critical line**: `∫_{θ>0} F G = (1/2π) ∫ Re(MF(1 − s) MG(s)) dt`, `s = ½ + it`. -/
theorem integral_mul_eq_mellin {F G : ℝ → ℝ} (hF1 : Integrable (logScale F))
    (hF2 : MemLp (logScale F) 2 volume) (hG1 : Integrable (logScale G))
    (hG2 : MemLp (logScale G) 2 volume) :
    ∫ θ in Ioi (0 : ℝ), F θ * G θ
      = (1 / (2 * π)) * ∫ t : ℝ, (mellinR F (1 - (1 / 2 + t * I)) * mellinR G (1 / 2 + t * I)).re := by
  have e : (fun x => logScale F x * logScale G x) = fun x => exp x • (fun θ => F θ * G θ) (exp x) := by
    funext x; unfold logScale
    rw [smul_eq_mul, ← Cvs.L2a.TailLogScaleTest.exp_half_sq]; ring
  rw [← integral_exp_smul_Ioi, ← e, ← integral_crossSpec hF1 hF2 hG1 hG2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  rw [crossSpec_logScale]; ring

/-! ### Symmetry and additivity -/

/-- `ρ_{f,k}` is symmetric. -/
theorem crossSpec_comm (f k : ℝ → ℝ) (t : ℝ) : crossSpec f k t = crossSpec k f t := by
  unfold crossSpec
  congr 1
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/-- `weilθ` is symmetric. -/
theorem weilθ_comm (F G : ℝ → ℝ) : weilθ F G = weilθ G F := by
  unfold weilθ
  simp only [crossSpec_comm (logScale F) (logScale G), add_comm (dil F G _)]
  ring

/-- `ρ_{f,k}` is additive in `f` on `L¹`. -/
theorem crossSpec_add_left {f₁ f₂ : ℝ → ℝ} (h₁ : Integrable f₁) (h₂ : Integrable f₂) (k : ℝ → ℝ) (t : ℝ) :
    crossSpec (fun x => f₁ x + f₂ x) k t = crossSpec f₁ k t + crossSpec f₂ k t := by
  have e : (fun x => f₁ x + f₂ x) = fun x => f₁ x + (1 : ℝ) * f₂ x := by simp
  unfold crossSpec
  rw [e, Cvs.L2a.FullTailPolarisation.fourier_cf_add_smul h₁ h₂, Complex.ofReal_one, one_mul, add_mul,
    Complex.add_re, add_div]

/-- `logScale` is additive. -/
theorem logScale_add (F₁ F₂ : ℝ → ℝ) :
    logScale (fun θ => F₁ θ + F₂ θ) = fun x => logScale F₁ x + logScale F₂ x := by
  funext x; unfold logScale; ring

/-- `P₊` evaluates a convergent improper integral. -/
theorem poleP_eq_of_tendsto {F : ℝ → ℝ} {p : ℝ}
    (h : Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, F θ) atTop (𝓝 p)) : poleP F = p :=
  h.limUnder_eq

/-- A function with `F(θ)/θ` integrable on `(0, ∞)` is integrable on `(0, Y]`. -/
theorem intervalIntegrable_of_integrableOn_div {F : ℝ → ℝ}
    (hM : IntegrableOn (fun θ => F θ / θ) (Ioi 0)) {Y : ℝ} (hY : 0 ≤ Y) :
    IntervalIntegrable F volume 0 Y := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY]
  have hM' : IntegrableOn (fun θ => F θ / θ) (Ioc 0 Y) := hM.mono_set Ioc_subset_Ioi_self
  have hb : Integrable (fun θ => θ * (F θ / θ)) (volume.restrict (Ioc 0 Y)) := by
    refine hM'.bdd_mul (c := Y) continuous_id.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos hθ.1]; exact hθ.2
  refine hb.congr ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun θ hθ => ?_))
  field_simp [hθ.1.ne']

/-- `P₊` is additive on convergent improper integrals with `F/θ` integrable. -/
theorem poleP_add {F₁ F₂ : ℝ → ℝ}
    (hP₁ : ∃ p, Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, F₁ θ) atTop (𝓝 p))
    (hP₂ : ∃ p, Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, F₂ θ) atTop (𝓝 p))
    (hM₁ : IntegrableOn (fun θ => F₁ θ / θ) (Ioi 0)) (hM₂ : IntegrableOn (fun θ => F₂ θ / θ) (Ioi 0)) :
    poleP (fun θ => F₁ θ + F₂ θ) = poleP F₁ + poleP F₂ := by
  obtain ⟨p₁, h₁⟩ := hP₁
  obtain ⟨p₂, h₂⟩ := hP₂
  rw [poleP_eq_of_tendsto h₁, poleP_eq_of_tendsto h₂]
  refine poleP_eq_of_tendsto ((h₁.add h₂).congr' ?_)
  filter_upwards [eventually_ge_atTop 0] with Y hY
  exact (intervalIntegral.integral_add (intervalIntegrable_of_integrableOn_div hM₁ hY)
    (intervalIntegrable_of_integrableOn_div hM₂ hY)).symm

/-- `P₋` is additive. -/
theorem poleM_add {F₁ F₂ : ℝ → ℝ} (hM₁ : IntegrableOn (fun θ => F₁ θ / θ) (Ioi 0))
    (hM₂ : IntegrableOn (fun θ => F₂ θ / θ) (Ioi 0)) :
    poleM (fun θ => F₁ θ + F₂ θ) = poleM F₁ + poleM F₂ := by
  unfold poleM
  simp only [add_div]
  exact integral_add hM₁ hM₂

/-- The dilate pairing is additive in its first slot. -/
theorem dil_add_left {F₁ F₂ G : ℝ → ℝ} {n : ℕ}
    (h₁ : IntegrableOn (fun θ => F₁ θ * G (n * θ)) (Ioi 0))
    (h₂ : IntegrableOn (fun θ => F₂ θ * G (n * θ)) (Ioi 0)) :
    dil (fun θ => F₁ θ + F₂ θ) G n = dil F₁ G n + dil F₂ G n := by
  unfold dil
  simp only [add_mul]
  exact integral_add h₁ h₂

/-- The dilate pairing is additive in its second slot. -/
theorem dil_add_right {F₁ F₂ G : ℝ → ℝ} {n : ℕ}
    (h₁ : IntegrableOn (fun θ => G θ * F₁ (n * θ)) (Ioi 0))
    (h₂ : IntegrableOn (fun θ => G θ * F₂ (n * θ)) (Ioi 0)) :
    dil G (fun θ => F₁ θ + F₂ θ) n = dil G F₁ n + dil G F₂ n := by
  unfold dil
  simp only [mul_add]
  exact integral_add h₁ h₂

/-- **`weilθ` is additive in its first slot** when every channel converges for both summands. -/
theorem weilθ_add_left {F₁ F₂ G : ℝ → ℝ}
    (hP₁ : ∃ p, Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, F₁ θ) atTop (𝓝 p))
    (hP₂ : ∃ p, Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, F₂ θ) atTop (𝓝 p))
    (hM₁ : IntegrableOn (fun θ => F₁ θ / θ) (Ioi 0)) (hM₂ : IntegrableOn (fun θ => F₂ θ / θ) (Ioi 0))
    (hf₁ : Integrable (logScale F₁)) (hf₂ : Integrable (logScale F₂))
    (hA₁ : Integrable fun t => archSymbol t * crossSpec (logScale F₁) (logScale G) t)
    (hA₂ : Integrable fun t => archSymbol t * crossSpec (logScale F₂) (logScale G) t)
    (hD₁ : ∀ n : ℕ, 0 < n → IntegrableOn (fun θ => F₁ θ * G (n * θ)) (Ioi 0))
    (hD₂ : ∀ n : ℕ, 0 < n → IntegrableOn (fun θ => F₂ θ * G (n * θ)) (Ioi 0))
    (hE₁ : ∀ n : ℕ, 0 < n → IntegrableOn (fun θ => G θ * F₁ (n * θ)) (Ioi 0))
    (hE₂ : ∀ n : ℕ, 0 < n → IntegrableOn (fun θ => G θ * F₂ (n * θ)) (Ioi 0))
    (hS₁ : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F₁ G n + dil G F₁ n))
    (hS₂ : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F₂ G n + dil G F₂ n)) :
    weilθ (fun θ => F₁ θ + F₂ θ) G = weilθ F₁ G + weilθ F₂ G := by
  have hA : ∫ t, archSymbol t * crossSpec (logScale fun θ => F₁ θ + F₂ θ) (logScale G) t
      = (∫ t, archSymbol t * crossSpec (logScale F₁) (logScale G) t)
        + ∫ t, archSymbol t * crossSpec (logScale F₂) (logScale G) t := by
    rw [← integral_add hA₁ hA₂]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [logScale_add, crossSpec_add_left hf₁ hf₂]; ring
  have hT : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ)
        * (dil (fun θ => F₁ θ + F₂ θ) G n + dil G (fun θ => F₁ θ + F₂ θ) n)
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F₁ G n + dil G F₁ n)
        + (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F₂ G n + dil G F₂ n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [dil_add_left (hD₁ n hn) (hD₂ n hn), dil_add_right (hE₁ n hn) (hE₂ n hn)]; ring
  unfold weilθ
  rw [poleP_add hP₁ hP₂ hM₁ hM₂, poleM_add hM₁ hM₂, hA, tsum_congr hT, hS₁.tsum_add hS₂]
  ring

end Cvs.WeilForm.ThetaSpaceParseval
