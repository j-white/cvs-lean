import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailArchChannel
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PartOneWeilForm
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTonelli
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.Archimedean.LevyUnitBlocks
import Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic
import Cvs.WeilForm.EImageRadical
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.MellinProfileStrips
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImagePoleFunctionals
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.WeilPositivityStatement
import Cvs.Zeta.ZetaDerivFunctionalEquation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form against the tail limit: `QW(k_G) − W_X(F_X) = W(r_X, F_X) − W(r_X, k_G)`

With `E_G = k_G + F_X + r_X` a.e. and (R) at `v = k_G` and `v = F_X`, the window form differs from the
truncated tail form by the couplings of `r_X`; their pole and arch channels tend to `0`, so the prime
coupling tends to `W_∞ − QW(k_G)`, and `QW(k_G) = W_∞(psi c G)` exactly when it tends to `0`.
-/

namespace Cvs.L2a.WindowFormTailLimit

open Real Set Filter Topology MeasureTheory
open scoped ArithmeticFunction
open Cvs.WeilForm.ThetaSpaceParseval (mellinR poleP poleM dil weilθ)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.FullTailPolarisation (crossSpec)
open Cvs.Xi.EImageWindowPoisson (eimage window)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.AngularProlateTailPositive (psi)

/-! ### Almost-everywhere congruence of the channels -/

/-- A composition `F ∘ φ` respects `F =ᵐ F'` when `φ` has a left inverse differentiable on its range. -/
theorem comp_ae_of_leftInv {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') {φ ψ : ℝ → ℝ} {S : Set ℝ}
    (hψ : DifferentiableOn ℝ ψ S) (hS : ∀ x, φ x ∈ S ∧ ψ (φ x) = x) :
    (fun x => F (φ x)) =ᵐ[volume] fun x => F' (φ x) := by
  rw [Filter.EventuallyEq, ae_iff] at h ⊢
  refine measure_mono_null (t := ψ '' ({y | ¬F y = F' y} ∩ S))
    (fun x hx => ⟨φ x, ⟨hx, (hS x).1⟩, (hS x).2⟩) ?_
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (hψ.mono inter_subset_right)
    (measure_mono_null inter_subset_left h)

theorem logScale_ae {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') : logScale F =ᵐ[volume] logScale F' := by
  have h' := comp_ae_of_leftInv h (φ := exp) (ψ := Real.log) (S := Ioi 0)
    (Real.differentiableOn_log.mono fun x hx => ne_of_gt hx) fun x => ⟨exp_pos x, Real.log_exp x⟩
  filter_upwards [h'] with x hx
  simp only [logScale, hx]

theorem comp_mul_ae {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') {n : ℝ} (hn : n ≠ 0) :
    (fun θ => F (n * θ)) =ᵐ[volume] fun θ => F' (n * θ) :=
  comp_ae_of_leftInv h (φ := fun θ => n * θ) (ψ := fun y => y / n) (S := univ)
    (differentiableOn_id.div_const n) fun x => ⟨mem_univ _, by field_simp⟩

theorem crossSpec_congr_left {f f' : ℝ → ℝ} (h : f =ᵐ[volume] f') (k : ℝ → ℝ) :
    crossSpec f k = crossSpec f' k := by
  have e : FourierTransform.fourier (Cvs.WeilForm.SelfConvolutionTransform.cf f)
      = FourierTransform.fourier (Cvs.WeilForm.SelfConvolutionTransform.cf f') := by
    funext w
    rw [Real.fourier_eq, Real.fourier_eq]
    exact integral_congr_ae (h.mono fun x hx => by simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, hx])
  funext t
  unfold crossSpec
  rw [e]

theorem poleP_congr {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') : poleP F = poleP F' := by
  unfold poleP
  congr 1
  funext Y
  exact intervalIntegral.integral_congr_ae (h.mono fun x hx _ => hx)

theorem poleM_congr {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') : poleM F = poleM F' :=
  integral_congr_ae (ae_restrict_of_ae (h.mono fun x hx => by simp only [hx]))

theorem dil_congr_left {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') (G : ℝ → ℝ) (n : ℕ) :
    dil F G n = dil F' G n :=
  integral_congr_ae (ae_restrict_of_ae (h.mono fun x hx => by simp only [hx]))

theorem dil_congr_right {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') (G : ℝ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    dil G F n = dil G F' n :=
  integral_congr_ae (ae_restrict_of_ae ((comp_mul_ae h (Nat.cast_ne_zero.mpr hn)).mono
    fun x hx => by simp only at hx; simp only [hx]))

/-- The prime channel `Σ Λ(n)(⟨F, G(n·)⟩ + ⟨G, F(n·)⟩)` of `weilθ`. -/
noncomputable def primeθ (F G : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F G n + dil G F n)

theorem primeθ_congr_left {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') (G : ℝ → ℝ) :
    primeθ F G = primeθ F' G := by
  unfold primeθ
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [dil_congr_left h G n, dil_congr_right h G hn]

/-- `weilθ` depends on its first argument only up to null sets. -/
theorem weilθ_congr_left {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') (G : ℝ → ℝ) :
    weilθ F G = weilθ F' G := by
  have hp := primeθ_congr_left h G
  unfold primeθ at hp
  unfold weilθ
  rw [poleP_congr h, poleM_congr h, crossSpec_congr_left (logScale_ae h), hp]

/-! ### Channel convergence and linearity -/

/-- The channel hypotheses under which `weilθ (·) G` is additive (those of `ThetaSpaceParseval`'s `weilθ_add_left`). -/
structure Adm (F G : ℝ → ℝ) : Prop where
  pole : ∃ p, Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, F θ) atTop (𝓝 p)
  div : IntegrableOn (fun θ => F θ / θ) (Ioi 0)
  log : Integrable (logScale F)
  arch : Integrable fun t => archSymbol t * crossSpec (logScale F) (logScale G) t
  left : ∀ n : ℕ, 0 < n → IntegrableOn (fun θ => F θ * G (n * θ)) (Ioi 0)
  right : ∀ n : ℕ, 0 < n → IntegrableOn (fun θ => G θ * F (n * θ)) (Ioi 0)
  prime : Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (dil F G n + dil G F n)

theorem weilθ_add {F₁ F₂ G : ℝ → ℝ} (h₁ : Adm F₁ G) (h₂ : Adm F₂ G) :
    weilθ (fun θ => F₁ θ + F₂ θ) G = weilθ F₁ G + weilθ F₂ G :=
  Cvs.WeilForm.ThetaSpaceParseval.weilθ_add_left h₁.pole h₂.pole h₁.div h₂.div h₁.log h₂.log h₁.arch h₂.arch
    h₁.left h₂.left h₁.right h₂.right h₁.prime h₂.prime

theorem crossSpec_smul_left {f : ℝ → ℝ} (hf : Integrable f) (k : ℝ → ℝ) (t : ℝ) (x : ℝ) :
    crossSpec (fun y => t * f y) k x = t * crossSpec f k x := by
  have e := Cvs.L2a.FullTailPolarisation.fourier_cf_add_smul (f := fun _ : ℝ => (0 : ℝ)) (k := f)
    (integrable_zero ℝ ℝ volume) hf t (x / (2 * π))
  have e1 : (fun y : ℝ => (0 : ℝ) + t * f y) = fun y => t * f y := funext fun y => zero_add _
  have e0 : FourierTransform.fourier (Cvs.WeilForm.SelfConvolutionTransform.cf fun _ : ℝ => (0 : ℝ)) (x / (2 * π)) = 0 := by
    rw [Real.fourier_eq]; simp [Cvs.WeilForm.SelfConvolutionTransform.cf]
  rw [e1, e0, zero_add] at e
  unfold crossSpec
  have e' : FourierTransform.fourier (Cvs.WeilForm.SelfConvolutionTransform.cf fun y => t * f y) (x / (2 * π))
      = (t : ℂ) * FourierTransform.fourier (Cvs.WeilForm.SelfConvolutionTransform.cf f) (x / (2 * π)) := e
  rw [e', mul_assoc, Complex.re_ofReal_mul, mul_div_assoc]

theorem logScale_smul (F : ℝ → ℝ) (t : ℝ) :
    logScale (fun θ => t * F θ) = fun x => t * logScale F x := by
  funext x; simp only [logScale]; ring

theorem dil_smul_left (F G : ℝ → ℝ) (t : ℝ) (n : ℕ) : dil (fun θ => t * F θ) G n = t * dil F G n := by
  unfold dil; rw [← integral_const_mul]; simp only [mul_assoc]

theorem dil_smul_right (F G : ℝ → ℝ) (t : ℝ) (n : ℕ) : dil G (fun θ => t * F θ) n = t * dil G F n := by
  unfold dil; rw [← integral_const_mul]; congr 1; funext θ; ring

theorem Adm.add {F₁ F₂ G : ℝ → ℝ} (h₁ : Adm F₁ G) (h₂ : Adm F₂ G) : Adm (fun θ => F₁ θ + F₂ θ) G where
  pole := by
    obtain ⟨p, hp⟩ := h₁.pole
    obtain ⟨q, hq⟩ := h₂.pole
    refine ⟨p + q, (hp.add hq).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 0] with Y hY
    rw [intervalIntegral.integral_add
      (Cvs.WeilForm.ThetaSpaceParseval.intervalIntegrable_of_integrableOn_div h₁.div hY)
      (Cvs.WeilForm.ThetaSpaceParseval.intervalIntegrable_of_integrableOn_div h₂.div hY)]
  div := (h₁.div.add h₂.div).congr (ae_of_all _ fun θ => by simp only [Pi.add_apply, add_div])
  log := by rw [Cvs.WeilForm.ThetaSpaceParseval.logScale_add]; exact h₁.log.add h₂.log
  arch := by
    rw [Cvs.WeilForm.ThetaSpaceParseval.logScale_add]
    simp_rw [Cvs.WeilForm.ThetaSpaceParseval.crossSpec_add_left h₁.log h₂.log, mul_add]
    exact h₁.arch.add h₂.arch
  left n hn := ((h₁.left n hn).add (h₂.left n hn)).congr
    (ae_of_all _ fun θ => by simp only [Pi.add_apply, add_mul])
  right n hn := ((h₁.right n hn).add (h₂.right n hn)).congr
    (ae_of_all _ fun θ => by simp only [Pi.add_apply, mul_add])
  prime := by
    refine (h₁.prime.add h₂.prime).congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [Cvs.WeilForm.ThetaSpaceParseval.dil_add_left (h₁.left n hn) (h₂.left n hn),
      Cvs.WeilForm.ThetaSpaceParseval.dil_add_right (h₁.right n hn) (h₂.right n hn)]
    ring

theorem Adm.smul {F G : ℝ → ℝ} (h : Adm F G) (t : ℝ) : Adm (fun θ => t * F θ) G where
  pole := by
    obtain ⟨p, hp⟩ := h.pole
    exact ⟨t * p, (hp.const_mul t).congr fun Y => (intervalIntegral.integral_const_mul t _).symm⟩
  div := (h.div.const_mul t).congr (ae_of_all _ fun θ => by simp only [mul_div_assoc])
  log := by rw [logScale_smul]; exact h.log.const_mul t
  arch := by
    rw [logScale_smul]
    simp_rw [crossSpec_smul_left h.log]
    simpa only [mul_left_comm] using h.arch.const_mul t
  left n hn := ((h.left n hn).const_mul t).congr (ae_of_all _ fun θ => by simp only; ring)
  right n hn := ((h.right n hn).const_mul t).congr (ae_of_all _ fun θ => by simp only; ring)
  prime := by
    refine (h.prime.mul_left t).congr fun n => ?_
    rw [dil_smul_left, dil_smul_right]
    ring

theorem Adm.sub {F₁ F₂ G : ℝ → ℝ} (h₁ : Adm F₁ G) (h₂ : Adm F₂ G) : Adm (fun θ => F₁ θ - F₂ θ) G := by
  have e : (fun θ => F₁ θ - F₂ θ) = fun θ => F₁ θ + -1 * F₂ θ := funext fun θ => by ring
  rw [e]
  exact h₁.add (h₂.smul (-1))

theorem Adm.congr {F F' G : ℝ → ℝ} (h : F =ᵐ[volume] F') (hA : Adm F G) : Adm F' G where
  pole := by
    obtain ⟨p, hp⟩ := hA.pole
    exact ⟨p, hp.congr fun Y => intervalIntegral.integral_congr_ae (h.mono fun x hx _ => hx)⟩
  div := hA.div.congr (ae_restrict_of_ae (h.mono fun x hx => by simp only [hx]))
  log := hA.log.congr (logScale_ae h)
  arch := by rw [← crossSpec_congr_left (logScale_ae h)]; exact hA.arch
  left n hn := (hA.left n hn).congr (ae_restrict_of_ae (h.mono fun x hx => by simp only [hx]))
  right n hn := (hA.right n hn).congr (ae_restrict_of_ae ((comp_mul_ae h
    (Nat.cast_ne_zero.mpr hn.ne')).mono fun x hx => by simp only at hx; simp only [hx]))
  prime := by
    refine hA.prime.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [dil_congr_left h G n, dil_congr_right h G hn]

/-! ### Tame test functions -/

/-- The test-function hypotheses of the radical lemma: bounded, measurable, supported in `[α, β] ⊂ (0, ∞)`,
with `|Mv(s)| ≤ C/|Im s|` on `−½ ≤ Re s ≤ 2`. -/
structure Tame (v : ℝ → ℝ) (α β : ℝ) : Prop where
  pos : 0 < α
  supp : ∀ θ ∉ Icc α β, v θ = 0
  meas : Measurable v
  bdd : ∃ M, ∀ θ, |v θ| ≤ M
  dec : ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im|

theorem Tame.log {v : ℝ → ℝ} {α β : ℝ} (h : Tame v α β) :
    Integrable (logScale v) ∧ MemLp (logScale v) 2 volume :=
  let ⟨_, hM⟩ := h.bdd
  Cvs.WeilForm.EImageRadical.integrable_logScale_of_support h.meas hM h.pos h.supp

theorem Tame.arch {v : ℝ → ℝ} {α β : ℝ} (h : Tame v α β) :
    Integrable fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale v) t * (archSymbol t - archSymbol 0) :=
  Cvs.WeilForm.ThetaFormWindowIdentification.integrable_specDensity_mul_arch_of_decay h.log.1 h.dec

/-- The arch integrand `a(t) ρ_{f,g}(t)` is integrable when `ρ_f (a − a(0))` and `ρ_g (a − a(0))` are. -/
theorem integrable_arch_crossSpec {f g : ℝ → ℝ} (hf : Integrable f) (hf2 : MemLp f 2 volume)
    (hfa : Integrable fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (archSymbol t - archSymbol 0))
    (hg : Integrable g) (hg2 : MemLp g 2 volume)
    (hga : Integrable fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity g t * (archSymbol t - archSymbol 0)) :
    Integrable fun t => archSymbol t * crossSpec f g t := by
  have hρf := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hf2 hf
  have hρg := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity hg2 hg
  have hc : Continuous fun t => crossSpec f g t := by
    have e : (fun t => crossSpec f g t) = fun t => (Cvs.WeilForm.SelfConvolutionCosine.specDensity (fun x => f x + 1 * g x) t
        - Cvs.WeilForm.SelfConvolutionCosine.specDensity f t - Cvs.WeilForm.SelfConvolutionCosine.specDensity g t) / 2 := by
      funext t; rw [Cvs.L2a.FullTailPolarisation.specDensity_add_smul hf hg 1 t]; ring
    rw [e]
    exact (((Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity (hf.add (hg.const_mul 1))).sub
      (Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity hf)).sub
      (Cvs.WeilForm.Archimedean.LevyTonelli.continuous_specDensity hg)).div_const 2
  have hdom : Integrable fun t => (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t * (archSymbol t - archSymbol 0)
      + Cvs.WeilForm.SelfConvolutionCosine.specDensity g t * (archSymbol t - archSymbol 0)
      + |archSymbol 0| * (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t + Cvs.WeilForm.SelfConvolutionCosine.specDensity g t)) / 2 :=
    ((hfa.add hga).add ((hρf.add hρg).const_mul _)).div_const 2
  refine hdom.mono' (Cvs.WeilForm.Archimedean.ArchFormIntegrable.continuous_archSymbol.mul hc).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  have h0f := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg f t
  have h0g := Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg g t
  have ha := Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg t
  have hcs := Cvs.L2a.FullTailBilinearChannels.abs_crossSpec_le f g t
  have hsq : √(Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) * √(Cvs.WeilForm.SelfConvolutionCosine.specDensity g t)
      ≤ (Cvs.WeilForm.SelfConvolutionCosine.specDensity f t + Cvs.WeilForm.SelfConvolutionCosine.specDensity g t) / 2 := by
    nlinarith [sq_nonneg (√(Cvs.WeilForm.SelfConvolutionCosine.specDensity f t) - √(Cvs.WeilForm.SelfConvolutionCosine.specDensity g t)),
      Real.sq_sqrt h0f, Real.sq_sqrt h0g]
  have habs : |archSymbol t| ≤ (archSymbol t - archSymbol 0) + |archSymbol 0| := by
    calc |archSymbol t| = |(archSymbol t - archSymbol 0) + archSymbol 0| := by ring_nf
      _ ≤ |archSymbol t - archSymbol 0| + |archSymbol 0| := abs_add_le _ _
      _ = (archSymbol t - archSymbol 0) + |archSymbol 0| := by rw [abs_of_nonneg ha]
  rw [Real.norm_eq_abs, abs_mul]
  calc |archSymbol t| * |crossSpec f g t|
      ≤ ((archSymbol t - archSymbol 0) + |archSymbol 0|)
        * ((Cvs.WeilForm.SelfConvolutionCosine.specDensity f t + Cvs.WeilForm.SelfConvolutionCosine.specDensity g t) / 2) :=
        mul_le_mul habs (hcs.trans hsq) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem tendsto_integral_of_support {F : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hsupp : ∀ θ ∉ Icc α β, F θ = 0) :
    Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, F θ) atTop (𝓝 (∫ θ in Ioi (0 : ℝ), F θ)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (max β 0)] with Y hY
  rw [intervalIntegral.integral_of_le (le_trans (le_max_right _ _) hY)]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun θ hθ => hsupp θ fun h => hθ.2 ⟨hα.trans_le h.1, h.2.trans (le_trans (le_max_left _ _) hY)⟩

/-- `⟨F, G(n·)⟩ = 0` once `n > β'/α`, for `F` vanishing off `[α, β]` and `G` off `[α', β']`. -/
theorem dil_eq_zero_of_support {F G : ℝ → ℝ} {α β α' β' : ℝ} (hα : 0 < α) (hF : ∀ θ ∉ Icc α β, F θ = 0)
    (hG : ∀ θ ∉ Icc α' β', G θ = 0) {n : ℕ} (hn : β' / α < n) : dil F G n = 0 := by
  unfold dil
  refine setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_
  by_cases hθ : θ ∈ Icc α β
  · have h1 : β' < n * α := by rwa [div_lt_iff₀ hα] at hn
    have h2 : β' < n * θ := h1.trans_le (mul_le_mul_of_nonneg_left hθ.1 n.cast_nonneg)
    rw [hG _ fun h => absurd h.2 (not_le.mpr h2), mul_zero]
  · rw [hF θ hθ, zero_mul]

theorem integrable_mul_of_support {u w : ℝ → ℝ} (hu : Measurable u) {M M' p q : ℝ} (hub : ∀ θ, |u θ| ≤ M)
    (hus : ∀ θ ∉ Icc p q, u θ = 0) (hw : Measurable w) (hwb : ∀ θ, |w θ| ≤ M') :
    Integrable fun θ => u θ * w θ := by
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hwb 0)
  refine Cvs.WeilForm.EImageRadical.integrable_of_bound_support (hu.mul hw) (K := M * M') (fun θ => ?_)
    (fun θ hθ => by rw [hus θ hθ, zero_mul])
  rw [abs_mul]
  exact mul_le_mul (hub θ) (hwb θ) (abs_nonneg _) ((abs_nonneg _).trans (hub θ))

theorem Tame.div {v : ℝ → ℝ} {α β : ℝ} (h : Tame v α β) : Integrable fun θ => v θ / θ := by
  obtain ⟨M, hM⟩ := h.bdd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine Cvs.WeilForm.EImageRadical.integrable_of_bound_support (h.meas.div measurable_id) (K := M / α)
    (fun θ => ?_) (fun θ hθ => by rw [h.supp θ hθ, zero_div])
  by_cases hθ : θ ∈ Icc α β
  · have hθ0 : 0 < θ := h.pos.trans_le hθ.1
    rw [abs_div, abs_of_pos hθ0]
    calc |v θ| / θ ≤ M / θ := div_le_div_of_nonneg_right (hM θ) hθ0.le
      _ ≤ M / α := div_le_div_of_nonneg_left hM0 h.pos hθ.1
  · rw [h.supp θ hθ, zero_div, abs_zero]; exact div_nonneg hM0 h.pos.le

theorem Tame.comp {v : ℝ → ℝ} {α β : ℝ} (h : Tame v α β) (n : ℕ) :
    Measurable (fun θ => v (n * θ)) ∧ ∃ M, ∀ θ, |v (n * θ)| ≤ M :=
  ⟨h.meas.comp (measurable_const.mul measurable_id), let ⟨M, hM⟩ := h.bdd; ⟨M, fun _ => hM _⟩⟩

/-- Two tame functions meet every channel hypothesis. -/
theorem adm_of_tame {F v : ℝ → ℝ} {α β α' β' : ℝ} (hF : Tame F α β) (hv : Tame v α' β') : Adm F v where
  pole := ⟨_, tendsto_integral_of_support hF.pos hF.supp⟩
  div := hF.div.integrableOn
  log := hF.log.1
  arch := integrable_arch_crossSpec hF.log.1 hF.log.2 hF.arch hv.log.1 hv.log.2 hv.arch
  left n _ := by
    obtain ⟨M, hM⟩ := hF.bdd
    obtain ⟨hm, M', hM'⟩ := hv.comp n
    exact (integrable_mul_of_support hF.meas hM hF.supp hm hM').integrableOn
  right n _ := by
    obtain ⟨M, hM⟩ := hv.bdd
    obtain ⟨hm, M', hM'⟩ := hF.comp n
    exact (integrable_mul_of_support hv.meas hM hv.supp hm hM').integrableOn
  prime := by
    refine summable_of_ne_finset_zero (s := Finset.range (⌊max (β' / α) (β / α')⌋₊ + 1)) fun n hn => ?_
    rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hn
    have hlt : max (β' / α) (β / α') < n := Nat.lt_of_floor_lt hn
    rw [dil_eq_zero_of_support hF.pos hF.supp hv.supp ((le_max_left _ _).trans_lt hlt),
      dil_eq_zero_of_support hv.pos hv.supp hF.supp ((le_max_right _ _).trans_lt hlt), add_zero, mul_zero]

/-! ### The E-image against a tame test function -/

section Eimage

variable {a : ℝ} {G G₁ : ℝ → ℝ}

theorem abs_eimage_le_const (ha : 0 < a) (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) :
    ∃ K, 0 ≤ K ∧ (∀ θ, 0 < θ → |eimage a G θ| ≤ K / θ) ∧ ∀ θ, |eimage a G θ| ≤ K / a := by
  obtain ⟨K, hK0, hK⟩ := Cvs.Xi.EImageMellin.abs_eimage_le ha hG hG₁ hGi
  refine ⟨K, hK0, hK, fun θ => ?_⟩
  rcases lt_or_ge θ a with h | h
  · rw [Cvs.Xi.EImageWindowPoisson.eimage_of_lt ha h, abs_zero]; positivity
  · exact (hK θ (ha.trans_le h)).trans (div_le_div_of_nonneg_left hK0 ha h)

theorem continuousOn_of_hasDerivAt (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) :
    ContinuousOn G (Icc 0 1) := fun u hu => (hG u hu).continuousAt.continuousWithinAt

theorem comp_supp {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) {n : ℕ} (hn : 0 < n) :
    ∀ θ ∉ Icc (α / n) (β / n), v (n * θ) = 0 := by
  intro θ hθ
  refine hv.supp _ fun h => hθ ⟨?_, ?_⟩
  · rw [div_le_iff₀ (by exact_mod_cast hn)]; linarith [h.1]
  · rw [le_div_iff₀ (by exact_mod_cast hn)]; linarith [h.2]

/-- `E_G` against a tame `v` meets every channel hypothesis. -/
theorem adm_eimage (ha : 0 < a) (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hG0 : G 0 = 0) (hGi : ∫ u in (0 : ℝ)..1, G u = 0)
    {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) : Adm (eimage a G) v := by
  obtain ⟨K, hK0, hK, hKa⟩ := abs_eimage_le_const ha hG hG₁ hGi
  have hEm := Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha (continuousOn_of_hasDerivAt hG)
  refine
    { pole := ⟨_, Cvs.Xi.EImagePoleFunctionals.tendsto_integral_eimage ha hG hG₁ hG0 hGi⟩
      div := ?_
      log := (Cvs.Xi.EImageMellin.integrable_logScale_eimage ha hG hG₁ hGi).1
      arch := ?_
      left := fun n hn => ?_
      right := fun n _ => ?_
      prime := ?_ }
  · have hind : IntegrableOn (fun θ => K * (Ici a).indicator (fun θ : ℝ => 1 / θ ^ 2) θ) (Ioi 0) :=
      (((Cvs.L2a.FullTailConvergence.integrableOn_one_div_sq (half_pos ha)).mono_set
        (Ici_subset_Ioi.2 (half_lt_self ha))).integrable_indicator measurableSet_Ici).const_mul K
        |>.integrableOn
    refine hind.mono' (hEm.div measurable_id).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun θ hθ => ?_))
    have hθ : 0 < θ := hθ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hθ]
    rcases lt_or_ge θ a with h | h
    · rw [Cvs.Xi.EImageWindowPoisson.eimage_of_lt ha h, abs_zero, zero_div,
        indicator_of_notMem (show θ ∉ Ici a from not_le.mpr h), mul_zero]
    · rw [indicator_of_mem (show θ ∈ Ici a from h)]
      calc |eimage a G θ| / θ ≤ K / θ / θ := div_le_div_of_nonneg_right (hK θ hθ) hθ.le
        _ = K * (1 / θ ^ 2) := by field_simp
  · have hint := Cvs.WeilForm.EImageRadical.integrable_archA_line ha hG hG₁ hG0 hGi hv.pos hv.supp hv.meas hv.bdd
      hv.dec
    have hpt : ∀ t : ℝ, archSymbol t * crossSpec (logScale (eimage a G)) (logScale v) t
        = (Cvs.Zeta.ZetaDerivFunctionalEquation.archA (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t)
            * riemannZeta₁ (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t)
            * Cvs.WeilForm.MellinProfileStrips.Hfun a G v (Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t)).re / (2 * π) := by
      intro t
      rw [Cvs.WeilForm.ThetaSpaceParseval.crossSpec_logScale]
      have e : (1 / 2 : ℂ) + t * Complex.I = Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t := by
        simp only [Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl]; ring
      rw [e, Cvs.Xi.EImageMellin.mellinR_eimage ha hG hG₁ hG0 hGi (w := 1 - Cvs.WeilForm.Archimedean.ArchSymbolZetaLogDeriv.cl t)
        (by simp), sub_sub_cancel, Cvs.Zeta.ZetaDerivFunctionalEquation.archA_cl, mul_div_assoc',
        ← Complex.re_ofReal_mul]
      simp only [Cvs.WeilForm.MellinProfileStrips.Hfun]
      congr 2
      ring
    exact (hint.re.div_const (2 * π)).congr (ae_of_all _ fun t => (hpt t).symm)
  · obtain ⟨M, hM⟩ := hv.bdd
    obtain ⟨hm, _⟩ := hv.comp n
    exact ((integrable_mul_of_support hm (fun θ => hM _) (comp_supp hv hn) hEm hKa).congr
      (ae_of_all _ fun θ => mul_comm _ _)).integrableOn
  · obtain ⟨M, hM⟩ := hv.bdd
    exact (integrable_mul_of_support hv.meas hM hv.supp (hEm.comp (measurable_const.mul measurable_id))
      (fun θ => hKa _)).integrableOn
  · have hR := Cvs.WeilForm.EImageRadical.hasSum_primeRight ha hG hG₁ hG0 hGi hv.pos hv.supp hv.meas hv.bdd hv.dec
    have hLfin : ∀ n ∉ Finset.range (⌊β / a⌋₊ + 1),
        (ArithmeticFunction.vonMangoldt n : ℝ) * dil (eimage a G) v n = 0 := by
      intro n hn
      rw [Finset.mem_range, not_lt, Nat.succ_le_iff] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) hn
      have hβ : β < n * a := by
        have := Nat.lt_of_floor_lt hn
        rwa [div_lt_iff₀ ha] at this
      unfold dil
      rw [setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_, mul_zero]
      by_cases hvz : v (n * θ) = 0
      · rw [hvz, mul_zero]
      · have hmem : (n : ℝ) * θ ∈ Icc α β := by
          by_contra h; exact hvz (hv.supp _ h)
        rw [Cvs.Xi.EImageWindowPoisson.eimage_of_lt ha (lt_of_mul_lt_mul_left (hmem.2.trans_lt hβ) hn0.le),
          zero_mul]
    exact ((summable_of_ne_finset_zero hLfin).add hR.summable).congr fun n => by ring

end Eimage

/-! ### The truncated tail and the window are tame -/

theorem mellinR_congr {F F' : ℝ → ℝ} (h : F =ᵐ[volume] F') : mellinR F = mellinR F' := by
  funext s
  unfold mellinR mellin
  exact integral_congr_ae (ae_restrict_of_ae (h.mono fun x hx => by simp only [hx]))

/-- Mellin decay from a piecewise-`C¹` representative almost everywhere. -/
theorem dec_of_pieces {ι : Type*} {v : ℝ → ℝ} (J : Finset ι) (p q : ι → ℝ) (w w₁ : ι → ℝ → ℝ)
    (hp : ∀ j ∈ J, 0 < p j) (hwc : ∀ j ∈ J, ContinuousOn (w j) (Icc (p j) (q j)))
    (hw : ∀ j ∈ J, ∀ θ ∈ Ioo (p j) (q j), HasDerivAt (w j) (w₁ j θ) θ)
    (hw₁ : ∀ j ∈ J, IntervalIntegrable (w₁ j) volume (p j) (q j))
    (hv : v =ᵐ[volume] fun θ => ∑ j ∈ J, (Ico (p j) (q j)).indicator (w j) θ) :
    ∃ C, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| → ‖mellinR v s‖ ≤ C / |s.im| := by
  obtain ⟨C, hC⟩ := Cvs.WeilForm.MellinProfileStrips.norm_mellinR_le_of_pieces J p q w w₁ hp hwc hw hw₁ rfl (-1 / 2) 2
  refine Cvs.WeilForm.ThetaFormWindowIdentification.mellin_decay_of_div_norm ⟨C, fun s h1 h2 h0 => ?_⟩
  rw [mellinR_congr hv]
  exact hC s h1 h2 h0

theorem posTail_ae_eq_pieces (Φ : ℝ → ℝ) {X : ℝ} (hX : 0 ≤ X) :
    posTail Φ X =ᵐ[volume] fun θ => ∑ m ∈ Finset.Icc 1 ⌊X⌋₊,
      (Ico (1 : ℝ) (X / m)).indicator (fun θ => Φ (m * θ)) θ := by
  set S : Finset ℝ := insert 1 ((Finset.Icc 1 ⌊X⌋₊).image fun m : ℕ => X / m)
  have hS : volume (S : Set ℝ) = 0 := (S.finite_toSet).measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS] with θ hθ
  have h1 : θ ≠ 1 := fun h => hθ (by simp [S, h])
  have hXm : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, θ ≠ X / m := fun m hm h =>
    hθ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, hm, h.symm⟩)))
  unfold posTail
  by_cases h : θ ∈ Ioc 1 X
  · rw [indicator_of_mem h]
    refine Finset.sum_congr rfl fun m hm => ?_
    by_cases hθm : θ ≤ X / m
    · rw [indicator_of_mem (show θ ∈ Iic (X / m) from hθm),
        indicator_of_mem (show θ ∈ Ico 1 (X / m) from ⟨h.1.le, lt_of_le_of_ne hθm (hXm m hm)⟩)]
    · rw [indicator_of_notMem (show θ ∉ Iic (X / m) from hθm),
        indicator_of_notMem (show θ ∉ Ico 1 (X / m) from fun h' => hθm h'.2.le)]
  · rw [indicator_of_notMem h]
    refine (Finset.sum_eq_zero fun m hm => indicator_of_notMem (fun h' => h ⟨?_, ?_⟩) _).symm
    · exact lt_of_le_of_ne h'.1 (Ne.symm h1)
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      exact h'.2.le.trans (div_le_self hX hm1)

/-- `F_X = posTail Φ X` is tame on `[1, X]` for `Φ ∈ C¹` and `X ≥ 1`. -/
theorem tame_posTail {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {X : ℝ} (hX : 1 ≤ X)
    (hb : ∃ M, ∀ θ, |posTail Φ X θ| ≤ M) : Tame (posTail Φ X) 1 X where
  pos := one_pos
  supp θ hθ := by
    rcases le_or_gt θ 1 with h | h
    · exact Cvs.L2a.PositionTruncatedTail.posTail_zero Φ X h
    · exact Cvs.L2a.PositionTruncatedTail.posTail_of_gt Φ (lt_of_not_ge fun h' => hθ ⟨h.le, h'⟩)
  meas := Cvs.L2a.FullTailConvergence.measurable_posTail hΦ.continuous X
  bdd := hb
  dec := by
    refine dec_of_pieces (Finset.Icc 1 ⌊X⌋₊) (fun _ => 1) (fun m => X / m) (fun m θ => Φ (m * θ))
      (fun m θ => deriv Φ (m * θ) * m) (fun _ _ => one_pos)
      (fun m _ => (hΦ.continuous.comp (continuous_const.mul continuous_id)).continuousOn)
      (fun m _ θ _ => ?_) (fun m _ => ?_) (posTail_ae_eq_pieces Φ (by linarith))
    · have h := ((hΦ.differentiable one_ne_zero) (m * θ)).hasDerivAt.comp θ
        ((hasDerivAt_id θ).const_mul (m : ℝ))
      simp only [mul_one] at h
      exact h
    · exact (((hΦ.continuous_deriv le_rfl).comp (continuous_const.mul continuous_id)).mul
        continuous_const).intervalIntegrable _ _

theorem window_ae_eq_pieces {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) :
    window a G =ᵐ[volume] fun θ => ∑ n ∈ Finset.Icc 1 ⌊1 / a⌋₊,
      (Ico (n * a) (min ((n + 1) * a) 1)).indicator
        (fun θ => a / θ * ∑ j ∈ Finset.Icc 1 n, G (j * a / θ)) θ := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (1 : ℝ))] with θ hθ1
  have h1 : θ ≠ 1 := hθ1
  unfold window
  by_cases h : θ ∈ Icc a 1
  · rw [indicator_of_mem h]
    have hθ0 : 0 < θ := ha.trans_le h.1
    have hlt1 : θ < 1 := lt_of_le_of_ne h.2 h1
    have hta : 0 ≤ θ / a := by positivity
    set n0 := ⌊θ / a⌋₊ with hn0
    have hn0J : n0 ∈ Finset.Icc 1 ⌊1 / a⌋₊ := by
      refine Finset.mem_Icc.mpr ⟨Nat.le_floor ?_, Nat.floor_le_floor ?_⟩
      · rw [Nat.cast_one, le_div_iff₀ ha, one_mul]; exact h.1
      · exact div_le_div_of_nonneg_right h.2 ha.le
    have hlo : (n0 : ℝ) * a ≤ θ := by
      have := Nat.floor_le hta; rwa [le_div_iff₀ ha] at this
    have hhi : θ < (n0 + 1) * a := by
      have := Nat.lt_floor_add_one (θ / a); rwa [div_lt_iff₀ ha] at this
    rw [Finset.sum_eq_single n0]
    · rw [indicator_of_mem (show θ ∈ Ico ((n0 : ℝ) * a) (min (((n0 : ℝ) + 1) * a) 1) from
        ⟨hlo, lt_min hhi hlt1⟩)]
      rfl
    · intro n _ hn
      refine indicator_of_notMem (fun hm => hn ?_) _
      rw [hn0]
      refine ((Nat.floor_eq_iff hta).mpr ⟨?_, ?_⟩).symm
      · rw [le_div_iff₀ ha]; exact hm.1
      · rw [div_lt_iff₀ ha]; exact hm.2.trans_le (min_le_left _ _)
    · intro hn; exact absurd hn0J hn
  · rw [indicator_of_notMem h]
    refine (Finset.sum_eq_zero fun n hn => indicator_of_notMem (fun hm => h ⟨?_, ?_⟩) _).symm
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      nlinarith [hm.1]
    · exact (hm.2.trans_le (min_le_right _ _)).le

/-- The window `k_G = E_G 1_{[a, 1]}` is tame on `[a, 1]` for `G ∈ C¹[0, 1]` with `∫₀¹ G = 0`. -/
theorem tame_window {a : ℝ} (ha : 0 < a) {G G₁ : ℝ → ℝ} (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u)
    (hG₁ : ContinuousOn G₁ (Icc 0 1)) (hGi : ∫ u in (0 : ℝ)..1, G u = 0) : Tame (window a G) a 1 where
  pos := ha
  supp θ hθ := Cvs.Xi.EImageWindowPoisson.window_of_notMem G hθ
  meas := (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha
    (continuousOn_of_hasDerivAt hG)).indicator measurableSet_Icc
  bdd := by
    obtain ⟨K, _, _, hKa⟩ := abs_eimage_le_const ha hG hG₁ hGi
    refine ⟨K / a, fun θ => ?_⟩
    unfold window
    by_cases h : θ ∈ Icc a 1
    · rw [indicator_of_mem h]; exact hKa θ
    · rw [indicator_of_notMem h, abs_zero]; exact (abs_nonneg _).trans (hKa 0)
  dec := by
    have hGc := continuousOn_of_hasDerivAt hG
    -- the summation points `ja/θ` lie in `[0, 1]` on each piece
    have hmaps : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ θ, (n : ℝ) * a ≤ θ → ∀ j ∈ Finset.Icc 1 n,
        (j : ℝ) * a / θ ∈ Icc (0 : ℝ) 1 := by
      intro n hn θ hθ j hj
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hj).2
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hθ0]
      exact (mul_le_mul_of_nonneg_right hjn ha.le).trans hθ
    have hpq : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, (n : ℝ) * a ≤ min ((n + 1) * a) 1 := by
      intro n hn
      refine le_min (by nlinarith) ?_
      have := (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
      rwa [le_div_iff₀ ha] at this
    have hpos : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, 0 < (n : ℝ) * a := fun n hn => by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      positivity
    -- continuity of the pieces and of their derivatives on the closed pieces
    have hcont : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ F : ℝ → ℝ, ContinuousOn F (Icc 0 1) →
        ContinuousOn (fun θ => ∑ j ∈ Finset.Icc 1 n, F (j * a / θ)) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) := by
      intro n hn F hF
      refine continuousOn_finsetSum _ fun j hj => hF.comp
        (continuousOn_const.div continuousOn_id fun θ hθ => (lt_of_lt_of_le (hpos n hn) hθ.1).ne')
        fun θ hθ => hmaps n hn θ hθ.1 j hj
    have hinv : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ b : ℝ,
        ContinuousOn (fun θ : ℝ => b / θ) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) := fun n hn b =>
      continuousOn_const.div continuousOn_id fun θ hθ => (lt_of_lt_of_le (hpos n hn) hθ.1).ne'
    refine dec_of_pieces (Finset.Icc 1 ⌊1 / a⌋₊) (fun n => n * a) (fun n => min ((n + 1) * a) 1)
      (fun n θ => a / θ * ∑ j ∈ Finset.Icc 1 n, G (j * a / θ))
      (fun n θ => a * -(θ ^ 2)⁻¹ * ∑ j ∈ Finset.Icc 1 n, G (j * a / θ)
        + a / θ * ∑ j ∈ Finset.Icc 1 n, G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹))
      hpos (fun n hn => (hinv n hn a).mul (hcont n hn G hGc)) (fun n hn θ hθ => ?_) (fun n hn => ?_)
      (window_ae_eq_pieces ha G)
    · have hθ0 : 0 < θ := (hpos n hn).trans hθ.1
      have hdiv : ∀ b : ℝ, HasDerivAt (fun y : ℝ => b / y) (b * -(θ ^ 2)⁻¹) θ := fun b => by
        simpa only [div_eq_mul_inv] using (hasDerivAt_inv hθ0.ne').const_mul b
      have hsum : HasDerivAt (fun y => ∑ j ∈ Finset.Icc 1 n, G (j * a / y))
          (∑ j ∈ Finset.Icc 1 n, G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹)) θ :=
        HasDerivAt.fun_sum fun j hj => (hG _ (hmaps n hn θ hθ.1.le j hj)).comp θ (hdiv ((j : ℝ) * a))
      exact (hdiv a).mul hsum
    · refine ContinuousOn.intervalIntegrable_of_Icc (hpq n hn) ?_
      have hsq : ContinuousOn (fun θ : ℝ => -(θ ^ 2)⁻¹) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) :=
        ((continuousOn_pow 2).inv₀ fun θ (hθ : θ ∈ Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) =>
          pow_ne_zero 2 (lt_of_lt_of_le (hpos n hn) hθ.1).ne').neg
      have hs2 : ContinuousOn (fun θ : ℝ => ∑ j ∈ Finset.Icc 1 n, G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹))
          (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) :=
        continuousOn_finsetSum (f := fun (j : ℕ) (θ : ℝ) => G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹)) _
          fun j hj => (hG₁.comp (hinv n hn ((j : ℝ) * a)) fun θ hθ => hmaps n hn θ hθ.1 j hj).mul
            (continuousOn_const.mul hsq)
      have h1 : ContinuousOn (fun θ : ℝ => a * -(θ ^ 2)⁻¹ * ∑ j ∈ Finset.Icc 1 n, G (j * a / θ))
          (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) :=
        (continuousOn_const.mul hsq).mul (hcont n hn G hGc)
      exact h1.add ((hinv n hn a).mul hs2)

/-! ### The exact identity from the radical lemma at `v = k_G` and `v = F_X` -/

/-- The truncation remainder `r_X = F_∞ − F_X`. -/
noncomputable def tailRem (Φ : ℝ → ℝ) (X θ : ℝ) : ℝ := fullTail Φ θ - posTail Φ X θ

section Identity

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- An even `C²` profile on `[−1, 1]` with `∫ G = 0` is `C¹` on `[0, 1]` with `∫₀¹ G = 0`. -/
theorem std_of_even (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) :
    (∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) ∧ ContinuousOn G₁ (Icc 0 1) ∧ ∫ u in (0 : ℝ)..1, G u = 0 := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  rw [hI] at hg hg₁
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
  refine ⟨fun u hu => hg u (hsub hu), fun u hu => (hg₁ u (hsub hu)).continuousAt.continuousWithinAt, ?_⟩
  exact Cvs.WeilForm.EImageRadical.integral_zero_one_of_even
    (fun s hs => (hg s hs).continuousAt.continuousWithinAt) heven hGi

theorem abs_posTail_psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (X : ℝ) : ∃ M, ∀ θ, |posTail (psi c G) X θ| ≤ M := by
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  refine ⟨B, fun θ => ?_⟩
  rcases le_or_gt θ 1 with h | h
  · rw [Cvs.L2a.PositionTruncatedTail.posTail_zero _ X h, abs_zero]; exact hB
  · exact (Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc X (by linarith)).trans
      (div_le_self hB h.le)

theorem tame_posTail_psi (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) : Tame (posTail (psi c G) X) 1 X :=
  tame_posTail (Cvs.L2a.FullTailConvergence.contDiff_psi
    (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c) hX (abs_posTail_psi_le hg hg₁ hg₂c hc X)

/-- `E_G = k_G + F_X + r_X` almost everywhere, for `G ∈ S₀` even and `C²`. -/
theorem eimage_ae_eq_split (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) (X : ℝ) :
    eimage (2 * π / c) G =ᵐ[volume] fun θ => (window (2 * π / c) G θ + posTail (psi c G) X θ)
      + tailRem (psi c G) X θ :=
  (Cvs.Xi.EImageWindowPoisson.eimage_ae_eq_window_add_fullTail hg hg₁ hg₂c heven hc hG0 hGi).mono
    fun θ hθ => by rw [hθ]; simp only [tailRem]; ring

theorem adm_tailRem (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) {X : ℝ} (hX : 1 ≤ X) {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) :
    Adm (tailRem (psi c G) X) v := by
  obtain ⟨hG01, hG₁c, hGi01⟩ := std_of_even hg hg₁ heven hGi
  have ha : 0 < 2 * π / c := by positivity
  have hk := tame_window ha hG01 hG₁c hGi01
  have hF := tame_posTail_psi hg hg₁ hg₂c hc hX
  refine ((adm_eimage ha hG01 hG₁c hG0 hGi01 hv).sub ((adm_of_tame hk hv).add (adm_of_tame hF hv))).congr ?_
  filter_upwards [eimage_ae_eq_split hg hg₁ hg₂c heven hc hG0 hGi X] with θ hθ
  rw [hθ]; ring

/-- Splitting `weilθ(E_G, v) = 0` along `E_G = k_G + F_X + r_X`. -/
theorem weilθ_split_eq_zero (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) {X : ℝ} (hX : 1 ≤ X) {v : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) :
    weilθ (window (2 * π / c) G) v + weilθ (posTail (psi c G) X) v + weilθ (tailRem (psi c G) X) v = 0 := by
  obtain ⟨hG01, hG₁c, hGi01⟩ := std_of_even hg hg₁ heven hGi
  have ha : 0 < 2 * π / c := by positivity
  have hk := tame_window ha hG01 hG₁c hGi01
  have hF := tame_posTail_psi hg hg₁ hg₂c hc hX
  have hR := Cvs.WeilForm.EImageRadical.radical_lemma ha hG01 hG₁c hG0 hGi01 hv.pos hv.supp hv.meas hv.bdd hv.dec
  rw [weilθ_congr_left (eimage_ae_eq_split hg hg₁ hg₂c heven hc hG0 hGi X),
    weilθ_add ((adm_of_tame hk hv).add (adm_of_tame hF hv))
      (adm_tailRem hg hg₁ hg₂c heven hc hG0 hGi hX hv),
    weilθ_add (adm_of_tame hk hv) (adm_of_tame hF hv)] at hR
  exact hR

/-- **E1, the exact identity**: `W(k_G, k_G) − W(F_X, F_X) = W(r_X, F_X) − W(r_X, k_G)`, from (R) at
`v = k_G` and `v = F_X`. -/
theorem window_tail_identity (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) {X : ℝ} (hX : 1 ≤ X) :
    weilθ (window (2 * π / c) G) (window (2 * π / c) G) - weilθ (posTail (psi c G) X) (posTail (psi c G) X)
      = weilθ (tailRem (psi c G) X) (posTail (psi c G) X)
        - weilθ (tailRem (psi c G) X) (window (2 * π / c) G) := by
  obtain ⟨hG01, hG₁c, hGi01⟩ := std_of_even hg hg₁ heven hGi
  have ha : 0 < 2 * π / c := by positivity
  have h1 := weilθ_split_eq_zero hg hg₁ hg₂c heven hc hG0 hGi hX (tame_window ha hG01 hG₁c hGi01)
  have h2 := weilθ_split_eq_zero hg hg₁ hg₂c heven hc hG0 hGi hX (tame_posTail_psi hg hg₁ hg₂c hc hX)
  have h3 := Cvs.WeilForm.ThetaSpaceParseval.weilθ_comm (window (2 * π / c) G) (posTail (psi c G) X)
  linarith

/-- `QW(k_G) = weilθ(k_G, k_G)` for `P ≥ 1/a` and `R log 2 ≥ log(1/a)`, `a = 2π/c`. -/
theorem weilθ_window_eq_weilForm (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s)
    (hc : 0 < c) (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) {P R : ℕ} (hP : 1 / (2 * π / c) ≤ P)
    (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2) :
    weilθ (window (2 * π / c) G) (window (2 * π / c) G)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (window (2 * π / c) G)) := by
  obtain ⟨hG01, hG₁c, hGi01⟩ := std_of_even hg hg₁ heven hGi
  have hk := tame_window (by positivity : 0 < 2 * π / c) hG01 hG₁c hGi01
  exact Cvs.WeilForm.ThetaFormWindowIdentification.weilθ_self_eq_weilForm hk.pos hk.supp hk.meas hk.bdd hk.dec hP hR

theorem log_le_mul_log_two (N : ℕ) : Real.log N ≤ N * Real.log 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  exact Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast (Nat.lt_two_pow_self).le)

/-- `W_N(F_N) = weilθ(F_N, F_N)` for integer `N ≥ 1`. -/
theorem weilθ_posTail_eq_weilForm (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    weilθ (posTail (psi c G) N) (posTail (psi c G) N)
      = Cvs.WeilForm.SelfConvolutionFunctional.weilForm N N (logScale (posTail (psi c G) N)) := by
  have hF := tame_posTail_psi hg hg₁ hg₂c hc (X := N) (by exact_mod_cast hN)
  exact Cvs.WeilForm.ThetaFormWindowIdentification.weilθ_self_eq_weilForm hF.pos hF.supp hF.meas hF.bdd hF.dec
    (by rw [div_one]) (by rw [div_one]; exact log_le_mul_log_two N)

end Identity

/-! ### The pole channel of the coupling -/

section Pole

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

theorem abs_fullTail_le_BG (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (θ : ℝ) :
    |fullTail (psi c G) θ|
      ≤ Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) := by
  have hB := Cvs.L2a.FullTailConvergence.BG_nonneg hc (G 1 + G (-1)) (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  rcases le_or_gt θ 1 with h | h
  · rw [Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ h, abs_zero]; exact hB
  · exact (Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc (by linarith)).trans (div_le_self hB h.le)

theorem summable_inv_succ_sq : Summable fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2 := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  exact h.congr fun i => by push_cast; ring

/-- **`Π₊` is the improper integral of `F_∞`**: `∫₀^Y F_∞ → Π₊ = Σ_m I(m)/m`. -/
theorem tendsto_integral_fullTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun Y : ℝ => ∫ θ in (0 : ℝ)..Y, fullTail (psi c G) θ) atTop
      (𝓝 (Cvs.L2a.FullTailPoleChannel.piPlus (psi c G))) := by
  set Φ := psi c G with hΦ
  set K := (2 * |G 1 + G (-1)| + (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)) / c ^ 2 with hK
  have hK0 : 0 ≤ K := by
    have := Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂
    positivity
  have hΦc : Continuous Φ :=
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  have hI : ∀ t, 1 ≤ t → |Cvs.L2a.FullTailPoleChannel.tailInt Φ t| ≤ K / t := fun t ht => by
    have := Cvs.L2a.FullTailPoleChannel.abs_tailInt_le hg hg₁ hg₂c hc ht
    rwa [hK, div_div]
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB0 : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  have hB := abs_fullTail_le_BG hg hg₁ hg₂c hc
  have hτm := Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc
  have hτi : ∀ p q : ℝ, IntervalIntegrable (fullTail Φ) volume p q := fun p q =>
    IntervalIntegrable.mono_fun' (g := fun _ => B) intervalIntegrable_const hτm.aestronglyMeasurable
      (ae_of_all _ fun θ => by show ‖fullTail Φ θ‖ ≤ B; rw [Real.norm_eq_abs]; exact hB θ)
  set T : ℝ → ℝ := fun Y => ∑' i : ℕ, Cvs.L2a.FullTailPoleChannel.tailInt Φ (((i : ℝ) + 1) * Y) / ((i : ℝ) + 1)
  have hTb : ∀ Y, 1 ≤ Y → ∀ i : ℕ,
      |Cvs.L2a.FullTailPoleChannel.tailInt Φ (((i : ℝ) + 1) * Y) / ((i : ℝ) + 1)| ≤ K / Y * (1 / ((i : ℝ) + 1) ^ 2) := by
    intro Y hY i
    have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [i.cast_nonneg (α := ℝ)]
    have hY0 : 0 < Y := by linarith
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (i : ℝ) + 1)]
    calc |Cvs.L2a.FullTailPoleChannel.tailInt Φ (((i : ℝ) + 1) * Y)| / ((i : ℝ) + 1)
        ≤ K / (((i : ℝ) + 1) * Y) / ((i : ℝ) + 1) :=
          div_le_div_of_nonneg_right (hI _ (one_le_mul_of_one_le_of_one_le hi hY)) (by linarith)
      _ = K / Y * (1 / ((i : ℝ) + 1) ^ 2) := by field_simp
  have hTs : ∀ Y, 1 ≤ Y →
      Summable fun i : ℕ => Cvs.L2a.FullTailPoleChannel.tailInt Φ (((i : ℝ) + 1) * Y) / ((i : ℝ) + 1) :=
    fun Y hY => Summable.of_norm_bounded (summable_inv_succ_sq.mul_left (K / Y))
      fun i => by rw [Real.norm_eq_abs]; exact hTb Y hY i
  -- `∫₀^Y F_∞ = Π₊ − T(Y)`
  have hkey : ∀ Y, 1 ≤ Y → ∫ θ in (0 : ℝ)..Y, fullTail Φ θ = Cvs.L2a.FullTailPoleChannel.piPlus Φ - T Y := by
    intro Y hY
    have h01 : ∫ θ in (0 : ℝ)..1, fullTail Φ θ = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ hθ => ?_]
      · simp
      · rw [uIcc_of_le zero_le_one] at hθ
        exact Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ.2
    rw [← intervalIntegral.integral_add_adjacent_intervals (hτi 0 1) (hτi 1 Y), h01, zero_add]
    -- partial sums of modes
    have hmode : ∀ M : ℕ, ∫ θ in (1 : ℝ)..Y, ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)
        = ∑ i ∈ Finset.range M, (Cvs.L2a.FullTailPoleChannel.tailInt Φ ((i : ℝ) + 1) / ((i : ℝ) + 1)
          - Cvs.L2a.FullTailPoleChannel.tailInt Φ (((i : ℝ) + 1) * Y) / ((i : ℝ) + 1)) := by
      intro M
      rw [intervalIntegral.integral_finsetSum (f := fun (m : ℕ) (θ : ℝ) => Φ (m * θ)) fun m _ =>
        (hΦc.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _,
        Cvs.L2a.FullTailPoleChannel.sum_Icc_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [i.cast_nonneg (α := ℝ)]
      have hi0 : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [intervalIntegral.integral_comp_mul_left (fun x => Φ x) hi0, mul_one]
      push_cast
      rw [← Cvs.L2a.FullTailPoleChannel.tailInt_sub hg hg₁ hg₂c hc hi (one_le_mul_of_one_le_of_one_le hi hY),
        smul_eq_mul]
      field_simp
      rfl
    have hlimL : Tendsto (fun M : ℕ => ∫ θ in (1 : ℝ)..Y, ∑ m ∈ Finset.Icc 1 M, Φ (m * θ)) atTop
        (𝓝 (∫ θ in (1 : ℝ)..Y, fullTail Φ θ)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B)
        (Eventually.of_forall fun M => (continuous_finsetSum _ fun m _ =>
          hΦc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
        (Eventually.of_forall fun M => ae_of_all _ fun θ hθ => ?_) intervalIntegrable_const
        (ae_of_all _ fun θ hθ => ?_)
      · rw [uIoc_of_le hY] at hθ
        rw [Real.norm_eq_abs]
        exact (Cvs.L2a.FullTailConvergence.abs_partial_le hg hg₁ hg₂c hc hθ.1.le M).trans
          (div_le_self hB0 hθ.1.le)
      · rw [uIoc_of_le hY] at hθ
        exact Cvs.L2a.FullTailConvergence.tendsto_partial hg hg₁ hg₂c hc hθ.1
    have hlimR : Tendsto (fun M : ℕ => ∑ i ∈ Finset.range M,
        (Cvs.L2a.FullTailPoleChannel.tailInt Φ ((i : ℝ) + 1) / ((i : ℝ) + 1)
          - Cvs.L2a.FullTailPoleChannel.tailInt Φ (((i : ℝ) + 1) * Y) / ((i : ℝ) + 1))) atTop
        (𝓝 (Cvs.L2a.FullTailPoleChannel.piPlus Φ - T Y)) := by
      simp_rw [Finset.sum_sub_distrib]
      exact (Cvs.L2a.FullTailPoleChannel.summable_piPlus hg hg₁ hg₂c hc).hasSum.tendsto_sum_nat.sub
        (hTs Y hY).hasSum.tendsto_sum_nat
    exact tendsto_nhds_unique (hlimL.congr hmode) hlimR
  -- `T(Y) → 0`
  have hT : Tendsto T atTop (𝓝 0) := by
    have hbd : Tendsto (fun Y : ℝ => K / Y * ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := K)).div_atTop tendsto_id).mul_const
        (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2)
      simpa only [id, zero_mul] using this
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [eventually_ge_atTop 1] with Y hY
    have hn : Summable fun i : ℕ => ‖Cvs.L2a.FullTailPoleChannel.tailInt Φ (((i : ℝ) + 1) * Y) / ((i : ℝ) + 1)‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _)
        (fun i => by rw [Real.norm_eq_abs]; exact hTb Y hY i) (summable_inv_succ_sq.mul_left _)
    calc ‖T Y‖ ≤ ∑' i : ℕ, ‖Cvs.L2a.FullTailPoleChannel.tailInt Φ (((i : ℝ) + 1) * Y) / ((i : ℝ) + 1)‖ :=
          norm_tsum_le_tsum_norm hn
      _ ≤ ∑' i : ℕ, K / Y * (1 / ((i : ℝ) + 1) ^ 2) :=
          hn.tsum_le_tsum (fun i => by rw [Real.norm_eq_abs]; exact hTb Y hY i)
            (summable_inv_succ_sq.mul_left _)
      _ = K / Y * ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ 2 := tsum_mul_left
  have := (tendsto_const_nhds (x := Cvs.L2a.FullTailPoleChannel.piPlus Φ)).sub hT
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  exact (hkey Y hY).symm

theorem setIntegral_Ioi_zero_eq_one {F : ℝ → ℝ} (hF : ∀ θ ≤ 1, F θ = 0) :
    ∫ θ in Ioi (0 : ℝ), F θ = ∫ θ in Ioi (1 : ℝ), F θ :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi zero_le_one)
    fun θ hθ => hF θ (not_lt.mp hθ.2)

theorem tailRem_of_le_one (Φ : ℝ → ℝ) (X : ℝ) {θ : ℝ} (hθ : θ ≤ 1) : tailRem Φ X θ = 0 := by
  rw [tailRem, Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ, Cvs.L2a.PositionTruncatedTail.posTail_zero _ X hθ, sub_zero]

theorem tendsto_integral_posTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail (psi c G) X θ) atTop
      (𝓝 (Cvs.L2a.FullTailPoleChannel.piPlus (psi c G))) := by
  set K := 2 * |G 1 + G (-1)| + (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hu : Tendsto (fun X : ℝ => K / c ^ 2 * (3 + Real.log X) / X) atTop (𝓝 0) := by
    have h3 : Tendsto (fun X : ℝ => 3 / X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hl : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa only [pow_one, one_mul, add_zero] using this
    have := (h3.add hl).const_mul (K / c ^ 2)
    rw [add_zero, mul_zero] at this
    refine this.congr fun X => ?_
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun X => norm_nonneg _) ?_ hu
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_eq_abs]
  exact Cvs.L2a.FullTailPoleChannel.abs_integral_posTail_sub_le hg hg₁ hg₂c hc hX

theorem tendsto_integral_posTail_div (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun X : ℝ => (∫ θ in Ioi 1, posTail (psi c G) X θ / θ) - ∫ θ in Ioi 1, fullTail (psi c G) θ / θ)
      atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (Cvs.L2a.FullTailConvergence.tendsto_sqrt_div_sqrt
    (Cvs.L2a.FullTailConvergence.K1b c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)))
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [Real.norm_eq_abs]
  exact (Cvs.L2a.FullTailPoleChannel.abs_integral_posTail_div_sub_le hg hg₁ hg₂c hc hX).trans
    (Real.sqrt_le_sqrt (Cvs.L2a.FullTailConvergence.K1_le hc _ _ hX))

theorem poleP_tailRem (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) :
    poleP (tailRem (psi c G) X)
      = Cvs.L2a.FullTailPoleChannel.piPlus (psi c G) - ∫ θ in Ioi 1, posTail (psi c G) X θ := by
  have hF := tame_posTail_psi hg hg₁ hg₂c hc hX
  obtain ⟨M, hM⟩ := hF.bdd
  have hτm := Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc
  have hτi : ∀ Y : ℝ, IntervalIntegrable (fullTail (psi c G)) volume 0 Y := fun Y =>
    IntervalIntegrable.mono_fun' (g := fun _ => Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1))
      (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)) intervalIntegrable_const hτm.aestronglyMeasurable
      (ae_of_all _ fun θ => by
        show ‖fullTail (psi c G) θ‖ ≤ _; rw [Real.norm_eq_abs]; exact abs_fullTail_le_BG hg hg₁ hg₂c hc θ)
  have hFi : ∀ Y : ℝ, IntervalIntegrable (posTail (psi c G) X) volume 0 Y := fun Y =>
    IntervalIntegrable.mono_fun' (g := fun _ => M) intervalIntegrable_const hF.meas.aestronglyMeasurable
      (ae_of_all _ fun θ => by show ‖posTail (psi c G) X θ‖ ≤ M; rw [Real.norm_eq_abs]; exact hM θ)
  refine Cvs.WeilForm.ThetaSpaceParseval.poleP_eq_of_tendsto ?_
  have h := (tendsto_integral_fullTail hg hg₁ hg₂c hc).sub (tendsto_integral_of_support hF.pos hF.supp)
  rw [setIntegral_Ioi_zero_eq_one fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero _ X hθ] at h
  refine h.congr fun Y => ?_
  rw [← intervalIntegral.integral_sub (hτi Y) (hFi Y)]
  rfl

theorem poleM_tailRem (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (X : ℝ) :
    poleM (tailRem (psi c G) X)
      = (∫ θ in Ioi 1, fullTail (psi c G) θ / θ) - ∫ θ in Ioi 1, posTail (psi c G) X θ / θ := by
  have hτ := Cvs.L2a.FullTailPolarisation.integrableOn_div_of_le (Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc)
    fun θ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hF := Cvs.L2a.FullTailPolarisation.integrableOn_div_of_le (Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c X)
    fun θ hθ => Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc X hθ
  unfold poleM
  rw [setIntegral_Ioi_zero_eq_one fun θ hθ => by rw [tailRem_of_le_one _ X hθ, zero_div],
    ← integral_sub hτ hF]
  congr 1; funext θ; rw [tailRem, sub_div]

theorem poleM_posTail (Φ : ℝ → ℝ) (X : ℝ) :
    poleM (posTail Φ X) = ∫ θ in Ioi 1, posTail Φ X θ / θ := by
  unfold poleM
  exact setIntegral_Ioi_zero_eq_one fun θ hθ => by rw [Cvs.L2a.PositionTruncatedTail.posTail_zero _ X hθ, zero_div]

theorem poleP_posTail (Φ : ℝ → ℝ) (X : ℝ) : poleP (posTail Φ X) = ∫ θ in Ioi 1, posTail Φ X θ := by
  have hs : ∀ θ ∉ Icc (1 : ℝ) (max X 1), posTail Φ X θ = 0 := fun θ hθ => by
    rcases le_or_gt θ 1 with h | h
    · exact Cvs.L2a.PositionTruncatedTail.posTail_zero Φ X h
    · exact Cvs.L2a.PositionTruncatedTail.posTail_of_gt Φ
        (lt_of_le_of_lt (le_max_left X 1) (lt_of_not_ge fun h' => hθ ⟨h.le, h'⟩))
  rw [Cvs.WeilForm.ThetaFormWindowIdentification.poleP_eq_integral hs,
    setIntegral_Ioi_zero_eq_one fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero _ X hθ]

/-- **The pole channel of the coupling tends to `0`**: `P₊r_X → 0`, `P₋r_X → 0`, and the poles of `F_X`
converge. -/
theorem tendsto_pole_coupling (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (k : ℝ → ℝ) :
    Tendsto (fun X : ℝ => (poleP (tailRem (psi c G) X) * poleM (posTail (psi c G) X)
        + poleM (tailRem (psi c G) X) * poleP (posTail (psi c G) X))
      - (poleP (tailRem (psi c G) X) * poleM k + poleM (tailRem (psi c G) X) * poleP k)) atTop (𝓝 0) := by
  have h1 := tendsto_integral_posTail hg hg₁ hg₂c hc
  have h2 := tendsto_integral_posTail_div hg hg₁ hg₂c hc
  have hP : Tendsto (fun X : ℝ => Cvs.L2a.FullTailPoleChannel.piPlus (psi c G) - ∫ θ in Ioi 1, posTail (psi c G) X θ)
      atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := Cvs.L2a.FullTailPoleChannel.piPlus (psi c G))).sub h1
    rwa [sub_self] at this
  have hM : Tendsto (fun X : ℝ => (∫ θ in Ioi 1, fullTail (psi c G) θ / θ)
      - ∫ θ in Ioi 1, posTail (psi c G) X θ / θ) atTop (𝓝 0) := by
    have := h2.neg; rw [neg_zero] at this
    exact this.congr fun X => by ring
  have hMF : Tendsto (fun X : ℝ => ∫ θ in Ioi 1, posTail (psi c G) X θ / θ) atTop
      (𝓝 (∫ θ in Ioi 1, fullTail (psi c G) θ / θ)) := by
    have := h2.add_const (∫ θ in Ioi 1, fullTail (psi c G) θ / θ)
    rw [zero_add] at this
    exact this.congr fun X => by ring
  have hlim := (hP.mul (hMF.sub_const (poleM k))).add (hM.mul (h1.sub_const (poleP k)))
  rw [zero_mul, zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [poleP_tailRem hg hg₁ hg₂c hc hX, poleM_tailRem hg hg₁ hg₂c hc X, poleM_posTail, poleP_posTail]
  ring

end Pole

/-! ### The arch channel of the coupling -/

section Arch

theorem Tame.levy {v : ℝ → ℝ} {α β : ℝ} (h : Tame v α β) :
    IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale v)) (Ioi 0) volume := by
  obtain ⟨hf1, hf2⟩ := h.log
  have hnn : 0 ≤ᵐ[volume] fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity (logScale v) t
      * (archSymbol t - archSymbol 0) :=
    Eventually.of_forall fun t => mul_nonneg (Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t)
      (Cvs.WeilForm.Archimedean.SymbolIncrementQuadratic.archSymbol_sub_nonneg t)
  exact (Cvs.WeilForm.LevyDomainSpectral.levyDom_iff hf2 hf1 hf2.integrable_sq
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_cross hf2 hf2)).mpr ((hasFiniteIntegral_iff_ofReal hnn).mp h.arch.2)

/-- `∫ a ρ_h = a(0) ∫ h² + archFull h` on `L¹ ∩ L²` with integrable Lévy integrand. -/
theorem arch_spectral {h : ℝ → ℝ} (h2 : MemLp h 2 volume) (h1 : Integrable h)
    (hl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy h) (Ioi 0) volume) :
    ∫ t, archSymbol t * Cvs.WeilForm.SelfConvolutionCosine.specDensity h t
      = archSymbol 0 * (∫ x, h x ^ 2) + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull h := by
  rw [← Cvs.L2a.PartOneWeilForm.arch_eq h2 h1 h2.integrable_sq (Cvs.WeilForm.TruncatedFormPolarised.integrable_cross h2 h2) hl
    (Cvs.WeilForm.Archimedean.LevyTonelli.integrable_specDensity_mul_arch h2 h1 hl)
    (Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1)]
  simp only [Cvs.Zeta.Explicit.Weil.selfConvolution, add_zero, sq, Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull]

/-- **The polarised arch identity**: `∫ a ρ_{f,g} = a(0) ∫ f g + archFullBil f g`. -/
theorem integral_arch_crossSpec_eq {f g : ℝ → ℝ} (hf2 : MemLp f 2 volume) (hf1 : Integrable f)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume)
    (hg2 : MemLp g 2 volume) (hg1 : Integrable g)
    (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume) :
    ∫ t, archSymbol t * crossSpec f g t
      = archSymbol 0 * (∫ x, f x * g x) + Cvs.L2a.FullTailPolarisation.archFullBil f g := by
  have hs2 : MemLp (fun x => f x + 1 * g x) 2 volume := hf2.add (hg2.const_mul 1)
  have hs1 : Integrable (fun x => f x + 1 * g x) := hf1.add (hg1.const_mul 1)
  have hsl := Cvs.L2a.FullTailPolarisation.integrableOn_levy_add_smul hf2 hg2 hfl hgl 1
  rw [Cvs.L2a.FullTailPolarisation.integral_arch_crossSpec hf2 hf1 hfl hg2 hg1 hgl, arch_spectral hs2 hs1 hsl,
    arch_spectral hf2 hf1 hfl, arch_spectral hg2 hg1 hgl,
    Cvs.L2a.FullTailPolarisation.archFull_add_smul hf2 hg2 hfl hgl 1]
  have hsq : ∫ x, (f x + 1 * g x) ^ 2 = (∫ x, f x ^ 2) + 2 * (∫ x, f x * g x) + ∫ x, g x ^ 2 := by
    have i1 : Integrable fun x => f x ^ 2 := hf2.integrable_sq
    have i2 : Integrable fun x => 2 * (f x * g x) := (hf2.integrable_mul hg2).const_mul 2
    have i3 : Integrable fun x => g x ^ 2 := hg2.integrable_sq
    have i12 : Integrable fun x => f x ^ 2 + 2 * (f x * g x) := i1.add i2
    calc ∫ x, (f x + 1 * g x) ^ 2 = ∫ x, (f x ^ 2 + 2 * (f x * g x)) + g x ^ 2 :=
          integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = (∫ x, f x ^ 2 + 2 * (f x * g x)) + ∫ x, g x ^ 2 := integral_add i12 i3
      _ = (∫ x, f x ^ 2) + 2 * (∫ x, f x * g x) + ∫ x, g x ^ 2 := by
          rw [integral_add i1 i2, integral_const_mul]
  rw [hsq]
  ring

/-- **Cauchy–Schwarz for the polarised Lévy integral**: `|archFullBil f g| ≤ √archFull f · √archFull g`. -/
theorem abs_archFullBil_le {f g : ℝ → ℝ} (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume)
    (hfl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy f) (Ioi 0) volume)
    (hgl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Ioi 0) volume) :
    |Cvs.L2a.FullTailPolarisation.archFullBil f g|
      ≤ √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f) * √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g) := by
  have hf0 := Cvs.WeilForm.Archimedean.LevyUnitBlocks.archFull_nonneg hf2
  have hq : ∀ t : ℝ, 0 ≤ Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull g * (t * t)
      + 2 * Cvs.L2a.FullTailPolarisation.archFullBil f g * t + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull f := by
    intro t
    have h := Cvs.WeilForm.Archimedean.LevyUnitBlocks.archFull_nonneg (hf2.add (hg2.const_mul t))
    have e : (f + fun x => t * g x) = fun x => f x + t * g x := rfl
    rw [e, Cvs.L2a.FullTailPolarisation.archFull_add_smul hf2 hg2 hfl hgl t] at h
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [← Real.sqrt_mul hf0]
  refine Real.abs_le_sqrt ?_
  nlinarith

theorem logScale_tailRem (Φ : ℝ → ℝ) (X : ℝ) :
    logScale (tailRem Φ X) = logScale (fullTail Φ) - logScale (posTail Φ X) := by
  funext x; simp only [logScale, tailRem, Pi.sub_apply]; ring

theorem abs_integral_mul_le {f g : ℝ → ℝ} (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ √(∫ x, f x ^ 2) * √(∫ x, g x ^ 2) := by
  have h := Cvs.L2a.FullTailConvergence.abs_setIntegral_mul_le (S := univ) hf2.integrable_sq.integrableOn
    hg2.integrable_sq.integrableOn (hf2.integrable_mul hg2).integrableOn
  simpa only [Measure.restrict_univ] using h

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- **The arch channel of the coupling tends to `0`**: `‖r_X‖ → 0` and `archFull r_X → 0`, while the
corresponding norms of `F_X` converge. -/
theorem tendsto_arch_coupling (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {k : ℝ → ℝ} {α β : ℝ} (hk : Tame k α β) :
    Tendsto (fun X : ℝ => (∫ t, archSymbol t * crossSpec (logScale (tailRem (psi c G) X))
        (logScale (posTail (psi c G) X)) t)
      - ∫ t, archSymbol t * crossSpec (logScale (tailRem (psi c G) X)) (logScale k) t) atTop (𝓝 0) := by
  have hgc : ContinuousOn G (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  obtain ⟨hτ2, hτ1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hg hg₁ hg₂c hc
  have hτl := Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc
  obtain ⟨hk1, hk2⟩ := hk.log
  have hkl := hk.levy
  set Ak := Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale k)
  set Nk := ∫ x, logScale k x ^ 2
  set K1b := Cvs.L2a.FullTailConvergence.K1b c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  -- the bound and its limit
  set bound : ℝ → ℝ := fun X => √(K1b / √X) * (|archSymbol 0| * (√(∫ θ in Ioi 1, posTail (psi c G) X θ ^ 2) + √Nk))
    + √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c G)) - logScale (posTail (psi c G) X)))
      * (√(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (posTail (psi c G) X))) + √Ak)
  have hbound : Tendsto bound atTop (𝓝 0) := by
    have hN := (Cvs.L2a.FullTailConvergence.tendsto_N hg hg₁ hg₂c hc).sqrt
    have hA := (Cvs.L2a.FullTailArchChannel.tendsto_archFull hg hg₁ hg₂c hc).sqrt
    have hA0 := (Cvs.L2a.FullTailArchChannel.tendsto_archFull_sub hg hg₁ hg₂c hc).sqrt
    rw [Real.sqrt_zero] at hA0
    have := ((Cvs.L2a.FullTailConvergence.tendsto_sqrt_div_sqrt K1b).mul
      ((hN.add_const √Nk).const_mul |archSymbol 0|)).add (hA0.mul (hA.add_const √Ak))
    simpa only [zero_mul, add_zero] using this
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [eventually_ge_atTop 1] with X hX
  have hadm := Cvs.L2a.PositionTailAdmissible.admissible_posTail hX
    ((Cvs.L2a.FullTailConvergence.contDiff_psi hgc c).contDiffOn (s := Icc 1 X))
  obtain ⟨hF2, hF1, -, -, hFl⟩ := hadm
  have hr2 : MemLp (logScale (tailRem (psi c G) X)) 2 volume := by
    rw [logScale_tailRem]; exact hτ2.sub hF2
  have hr1 : Integrable (logScale (tailRem (psi c G) X)) := by rw [logScale_tailRem]; exact hτ1.sub hF1
  have hrl : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy (logScale (tailRem (psi c G) X))) (Ioi 0) volume := by
    rw [logScale_tailRem]; exact Cvs.WeilForm.Archimedean.LevyUnitBlocks.integrableOn_levy_sub hτ2 hF2 hτl hFl
  have hNr : √(∫ x, logScale (tailRem (psi c G) X) x ^ 2) ≤ √(K1b / √X) := by
    refine Real.sqrt_le_sqrt ?_
    rw [Cvs.L2a.TailLogScaleTest.integral_sq _ fun θ hθ => tailRem_of_le_one _ X hθ]
    refine le_trans (le_of_eq ?_) ((Cvs.L2a.FullTailConvergence.integral_sub_sq_le hg hg₁ hg₂c hc hX).trans
      (Cvs.L2a.FullTailConvergence.K1_le hc _ _ hX))
    congr 1; funext θ; rw [tailRem]; ring
  have hNF : ∫ x, logScale (posTail (psi c G) X) x ^ 2 = ∫ θ in Ioi 1, posTail (psi c G) X θ ^ 2 :=
    Cvs.L2a.TailLogScaleTest.integral_sq _ fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero _ X hθ
  have hAr : Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (tailRem (psi c G) X))
      = Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c G)) - logScale (posTail (psi c G) X)) := by
    rw [logScale_tailRem]
  rw [integral_arch_crossSpec_eq hr2 hr1 hrl hF2 hF1 hFl, integral_arch_crossSpec_eq hr2 hr1 hrl hk2 hk1 hkl,
    Real.norm_eq_abs]
  have c1 := abs_integral_mul_le hr2 hF2
  have c2 := abs_integral_mul_le hr2 hk2
  have c3 := abs_archFullBil_le hr2 hF2 hrl hFl
  have c4 := abs_archFullBil_le hr2 hk2 hrl hkl
  rw [hNF] at c1
  rw [hAr] at c3 c4
  have s0 := Real.sqrt_nonneg (∫ x, logScale (tailRem (psi c G) X) x ^ 2)
  have s1 := Real.sqrt_nonneg (∫ θ in Ioi 1, posTail (psi c G) X θ ^ 2)
  have s2 := Real.sqrt_nonneg Nk
  have s3 := Real.sqrt_nonneg (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c G))
    - logScale (posTail (psi c G) X)))
  have s4 := Real.sqrt_nonneg (Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (posTail (psi c G) X)))
  have s5 := Real.sqrt_nonneg Ak
  have ha0 := abs_nonneg (archSymbol 0)
  have e1 := abs_mul (archSymbol 0) (∫ x, logScale (tailRem (psi c G) X) x * logScale (posTail (psi c G) X) x)
  have e2 := abs_mul (archSymbol 0) (∫ x, logScale (tailRem (psi c G) X) x * logScale k x)
  have t1 : |archSymbol 0| * |∫ x, logScale (tailRem (psi c G) X) x * logScale (posTail (psi c G) X) x|
      ≤ |archSymbol 0| * (√(K1b / √X) * √(∫ θ in Ioi 1, posTail (psi c G) X θ ^ 2)) :=
    mul_le_mul_of_nonneg_left (c1.trans (mul_le_mul_of_nonneg_right hNr s1)) ha0
  have t2 : |archSymbol 0| * |∫ x, logScale (tailRem (psi c G) X) x * logScale k x|
      ≤ |archSymbol 0| * (√(K1b / √X) * √Nk) :=
    mul_le_mul_of_nonneg_left (c2.trans (mul_le_mul_of_nonneg_right hNr s2)) ha0
  calc |archSymbol 0 * (∫ x, logScale (tailRem (psi c G) X) x * logScale (posTail (psi c G) X) x)
        + Cvs.L2a.FullTailPolarisation.archFullBil (logScale (tailRem (psi c G) X)) (logScale (posTail (psi c G) X))
        - (archSymbol 0 * (∫ x, logScale (tailRem (psi c G) X) x * logScale k x)
          + Cvs.L2a.FullTailPolarisation.archFullBil (logScale (tailRem (psi c G) X)) (logScale k))|
      ≤ |archSymbol 0 * (∫ x, logScale (tailRem (psi c G) X) x * logScale (posTail (psi c G) X) x)|
        + |Cvs.L2a.FullTailPolarisation.archFullBil (logScale (tailRem (psi c G) X)) (logScale (posTail (psi c G) X))|
        + (|archSymbol 0 * (∫ x, logScale (tailRem (psi c G) X) x * logScale k x)|
          + |Cvs.L2a.FullTailPolarisation.archFullBil (logScale (tailRem (psi c G) X)) (logScale k)|) :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ bound X := by
        have hb : bound X = |archSymbol 0| * (√(K1b / √X) * √(∫ θ in Ioi 1, posTail (psi c G) X θ ^ 2))
            + |archSymbol 0| * (√(K1b / √X) * √Nk)
            + √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c G)) - logScale (posTail (psi c G) X)))
              * √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (posTail (psi c G) X)))
            + √(Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale (fullTail (psi c G)) - logScale (posTail (psi c G) X)))
              * √Ak := by
          simp only [bound]; ring
        rw [hb, e1, e2]
        linarith
end Arch

/-! ### The limit: the prime coupling carries `W_∞ − QW(k_G)` -/

/-- **E1's prime channel**: the prime coupling `Σ Λ(n)(⟨r_N, F_N(n·)⟩ + ⟨F_N, r_N(n·)⟩) − (same with k_G)`
tends to `0` along the integers. -/
def PrimeTailLimit (c : ℝ) (G : ℝ → ℝ) : Prop :=
  Tendsto (fun N : ℕ => primeθ (tailRem (psi c G) N) (posTail (psi c G) N)
    - primeθ (tailRem (psi c G) N) (window (2 * π / c) G)) atTop (𝓝 0)

/-- `⟨r_X, k_G(n·)⟩ = 0` for `n ≥ 1`, so the `k_G` half of the prime coupling is `Σ Λ(n) ⟨k_G, r_X(n·)⟩`. -/
theorem primeθ_tailRem_window (Φ : ℝ → ℝ) (X a : ℝ) (G : ℝ → ℝ) :
    primeθ (tailRem Φ X) (window a G)
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * dil (window a G) (tailRem Φ X) n := by
  unfold primeθ
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h0 : dil (tailRem Φ X) (window a G) n = 0 := by
    unfold dil
    refine setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_
    rcases le_or_gt θ 1 with h | h
    · rw [tailRem_of_le_one Φ X h, zero_mul]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [Cvs.Xi.EImageWindowPoisson.window_of_notMem G fun hm => absurd hm.2 (not_le.mpr (by nlinarith)),
        mul_zero]
  rw [h0, zero_add]

section Limit

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

theorem weilθ_sub_eq_channels (r F k : ℝ → ℝ) :
    weilθ r F - weilθ r k
      = ((poleP r * poleM F + poleM r * poleP F) - (poleP r * poleM k + poleM r * poleP k))
        + ((∫ t, archSymbol t * crossSpec (logScale r) (logScale F) t)
          - ∫ t, archSymbol t * crossSpec (logScale r) (logScale k) t)
        - (primeθ r F - primeθ r k) := by
  unfold weilθ primeθ; ring

/-- **The prime coupling converges, to `W_∞(psi c G) − QW(k_G)`**, for `G ∈ S₀` even and `C²`: the pole
and arch couplings vanish in the limit and `W_N(F_N) → W_∞`. -/
theorem tendsto_prime_coupling (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) :
    Tendsto (fun N : ℕ => primeθ (tailRem (psi c G) N) (posTail (psi c G) N)
        - primeθ (tailRem (psi c G) N) (window (2 * π / c) G)) atTop
      (𝓝 (Cvs.L2a.FullTailWeilFormLimit.Winf (psi c G)
        - weilθ (window (2 * π / c) G) (window (2 * π / c) G))) := by
  obtain ⟨hG01, hG₁c, hGi01⟩ := std_of_even hg hg₁ heven hGi
  have hk := tame_window (by positivity : 0 < 2 * π / c) hG01 hG₁c hGi01
  have hpole := (tendsto_pole_coupling hg hg₁ hg₂c hc (window (2 * π / c) G)).comp tendsto_natCast_atTop_atTop
  have harch := (tendsto_arch_coupling hg hg₁ hg₂c hc hk).comp tendsto_natCast_atTop_atTop
  have hW := (Cvs.L2a.FullTailWeilFormLimit.tendsto_weilForm hg hg₁ hg₂c hc).comp tendsto_natCast_atTop_atTop
  have hlim := ((hpole.add harch).sub_const (weilθ (window (2 * π / c) G) (window (2 * π / c) G))).add hW
  rw [zero_add, zero_sub, neg_add_eq_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hX : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hid := window_tail_identity hg hg₁ hg₂c heven hc hG0 hGi hX
  have hch := weilθ_sub_eq_channels (tailRem (psi c G) N) (posTail (psi c G) N) (window (2 * π / c) G)
  have hF := weilθ_posTail_eq_weilForm hg hg₁ hg₂c hc hN
  simp only [Function.comp_apply, Nat.floor_natCast]
  rw [← hF]
  linarith

/-- **E1**: `QW(k_G) = W_∞(psi c G)` exactly when the prime coupling tends to `0`, for `G ∈ S₀` even and
`C²`, `P ≥ 1/a` and `R log 2 ≥ log(1/a)`. -/
theorem window_eq_Winf_iff (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) {P R : ℕ} (hP : 1 / (2 * π / c) ≤ P)
    (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (window (2 * π / c) G)) = Cvs.L2a.FullTailWeilFormLimit.Winf (psi c G)
      ↔ PrimeTailLimit c G := by
  have hlim := tendsto_prime_coupling hg hg₁ hg₂c heven hc hG0 hGi
  rw [← weilθ_window_eq_weilForm hg hg₁ heven hc hGi hP hR]
  constructor
  · intro h
    rw [h, sub_self] at hlim
    exact hlim
  · intro h
    exact (sub_eq_zero.mp (tendsto_nhds_unique hlim h)).symm

/-- **E1, the window-tail limit**: `QW(k_G) = W_∞(psi c G)` for `G ∈ S₀` even and `C²`, given the prime
coupling limit. -/
theorem window_eq_Winf (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hc : 0 < c) (hG0 : G 0 = 0)
    (hGi : ∫ s in (-1 : ℝ)..1, G s = 0) {P R : ℕ} (hP : 1 / (2 * π / c) ≤ P)
    (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2) (hE1 : PrimeTailLimit c G) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (window (2 * π / c) G)) = Cvs.L2a.FullTailWeilFormLimit.Winf (psi c G) :=
  (window_eq_Winf_iff hg hg₁ hg₂c heven hc hG0 hGi hP hR).mpr hE1

end Limit

/-! ### The polar algebra (C) -/

/-- The regularised profile `G̃ = G − aG(0) · a⁻¹β(·/a)`, `a = 2π/c`, with `ψ_c(a⁻¹β(·/a)) = Ψ`. -/
noncomputable def regProfile (c : ℝ) (G : ℝ → ℝ) (s : ℝ) : ℝ :=
  G s + -(2 * π / c * G 0) * Cvs.L2a.FullTailBilinearChannels.betaA c s

section Polar

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

theorem regProfile_eq (hc : 0 < c) (G : ℝ → ℝ) :
    regProfile c G = fun s => G s - G 0 * Cvs.L2a.BetaProfilePoissonTail.beta (s / (2 * π / c)) := by
  have ha : 2 * π / c ≠ 0 := by positivity
  funext s
  simp only [regProfile, Cvs.L2a.FullTailBilinearChannels.betaA]
  field_simp
  ring

theorem betaA_neg (c s : ℝ) : Cvs.L2a.FullTailBilinearChannels.betaA c (-s) = Cvs.L2a.FullTailBilinearChannels.betaA c s := by
  simp only [Cvs.L2a.FullTailBilinearChannels.betaA, neg_div, Cvs.L2a.BetaProfilePoissonTail.beta_neg]

/-- `∫_{−1}^{1} a⁻¹β(s/a) ds = ∫ β = 0` for `a = 2π/c ≤ 1`. -/
theorem integral_betaA (hc : 2 * π ≤ c) : ∫ s in (-1 : ℝ)..1, Cvs.L2a.FullTailBilinearChannels.betaA c s = 0 := by
  have hc0 : 0 < c := by linarith [pi_pos]
  set a := 2 * π / c with ha_def
  have ha : 0 < a := by positivity
  have ha1 : 1 ≤ 1 / a := by
    rw [ha_def, one_div_div, le_div_iff₀ (by positivity)]; linarith
  have hβc : Continuous Cvs.L2a.BetaProfilePoissonTail.beta := Cvs.L2a.BetaProfilePoissonTail.contDiff_beta.continuous
  have hii : ∀ p q : ℝ, IntervalIntegrable Cvs.L2a.BetaProfilePoissonTail.beta volume p q :=
    fun p q => hβc.intervalIntegrable p q
  have hout : ∀ p q : ℝ, (∀ y ∈ uIcc p q, 1 ≤ |y|) → ∫ y in p..q, Cvs.L2a.BetaProfilePoissonTail.beta y = 0 :=
    fun p q h => by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun y hy =>
        Cvs.L2a.BetaProfilePoissonTail.beta_of_one_le_abs (h y hy)]
      simp
  simp only [Cvs.L2a.FullTailBilinearChannels.betaA]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div _ ha.ne', smul_eq_mul,
    ← intervalIntegral.integral_add_adjacent_intervals (hii _ (-1)) (hii (-1) _),
    ← intervalIntegral.integral_add_adjacent_intervals (hii (-1) 1) (hii 1 _),
    Cvs.L2a.BetaProfilePoissonTail.integral_beta, hout (-1 / a) (-1) ?_, hout 1 (1 / a) ?_]
  · ring
  · intro y hy
    rw [uIcc_of_le ha1] at hy
    rw [abs_of_pos (by linarith [hy.1])]; exact hy.1
  · intro y hy
    have : -1 / a ≤ -1 := by rw [neg_div]; linarith
    rw [uIcc_of_le this] at hy
    rw [abs_of_neg (by linarith [hy.2])]; linarith [hy.2]

/-- **The polar algebra (C)**: for `G` even and `C²` with `∫ G = 0`, `c ≥ 2π`, `a = 2π/c` and `Ψ = psi 2π β`,
`QW(k_G) = W_∞(Φ) − 2aG(0) W_∞(Φ, Ψ) + a²G(0)² W_∞(Ψ)`, given E1's prime coupling limit for `G̃`. -/
theorem window_eq_polar (hc : 2 * π ≤ c) (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hGi : ∫ s in (-1 : ℝ)..1, G s = 0)
    {P R : ℕ} (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2)
    (hE1 : PrimeTailLimit c (regProfile c G)) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (window (2 * π / c) G))
      = Cvs.L2a.FullTailWeilFormLimit.Winf (psi c G)
        - 2 * (2 * π / c * G 0) * Cvs.L2a.FullTailPolarisation.WinfBil (psi c G) Cvs.L2a.BetaProfilePoissonTail.Psi
        + (2 * π / c * G 0) ^ 2 * Cvs.L2a.FullTailWeilFormLimit.Winf Cvs.L2a.BetaProfilePoissonTail.Psi := by
  have hc0 : 0 < c := by linarith [pi_pos]
  have ha : 0 < 2 * π / c := by positivity
  have ha1 : 2 * π / c ≤ 1 := by rw [div_le_one hc0]; exact hc
  set t := -(2 * π / c * G 0) with ht
  have hgt : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (regProfile c G)
      (G₁ s + t * Cvs.L2a.FullTailBilinearChannels.betaA1 c s) s := fun s hs =>
    (hg s hs).add ((Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA c s).const_mul t)
  have hgt₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => G₁ s + t * Cvs.L2a.FullTailBilinearChannels.betaA1 c s)
      (G₂ s + t * Cvs.L2a.FullTailBilinearChannels.betaA2 c s) s := fun s hs =>
    (hg₁ s hs).add ((Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA1 c s).const_mul t)
  have hgt₂c : ContinuousOn (fun s => G₂ s + t * Cvs.L2a.FullTailBilinearChannels.betaA2 c s) (uIcc (-1) 1) :=
    hg₂c.add (continuous_const.mul (Cvs.L2a.FullTailBilinearChannels.continuous_betaA2 c)).continuousOn
  have hevent : ∀ s ∈ Icc (-1 : ℝ) 1, regProfile c G (-s) = regProfile c G s := fun s hs => by
    simp only [regProfile, heven s hs, betaA_neg]
  have hGt0 : regProfile c G 0 = 0 := by
    rw [regProfile_eq hc0]; simp [Cvs.L2a.BetaProfilePoissonTail.beta_zero]
  have hGti : ∫ s in (-1 : ℝ)..1, regProfile c G s = 0 := by
    have hGc : Continuous fun s => t * Cvs.L2a.FullTailBilinearChannels.betaA c s := by
      unfold Cvs.L2a.FullTailBilinearChannels.betaA
      exact continuous_const.mul (continuous_const.mul
        (Cvs.L2a.BetaProfilePoissonTail.contDiff_beta.continuous.comp (continuous_id.div_const _)))
    have hGii : IntervalIntegrable G volume (-1) 1 :=
      ContinuousOn.intervalIntegrable fun s hs => (hg s hs).continuousAt.continuousWithinAt
    simp only [regProfile]
    rw [intervalIntegral.integral_add hGii (hGc.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      hGi, integral_betaA hc]
    ring
  have hwin : window (2 * π / c) (regProfile c G) = window (2 * π / c) G := by
    rw [regProfile_eq hc0]
    exact Cvs.Xi.EImageWindowPoisson.window_sub_rescale ha ha1 G (G 0) fun y hy =>
      Cvs.L2a.BetaProfilePoissonTail.beta_of_one_le_abs (by rw [abs_of_pos (by linarith)]; exact hy)
  rw [← hwin, window_eq_Winf hgt hgt₁ hgt₂c hevent hc0 hGt0 hGti hP hR hE1]
  have hW := Cvs.L2a.FullTailPolarisation.Winf_psi_add_smul hg hg₁ hg₂c
    (fun s _ => Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA c s) (fun s _ => Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA1 c s)
    (Cvs.L2a.FullTailBilinearChannels.continuous_betaA2 c).continuousOn hc0 t
  rw [Cvs.L2a.FullTailBilinearChannels.psi_betaA hc] at hW
  have e : regProfile c G = fun s => G s + t * Cvs.L2a.FullTailBilinearChannels.betaA c s := rfl
  rw [e, hW, ht]
  ring

end Polar

end Cvs.L2a.WindowFormTailLimit
