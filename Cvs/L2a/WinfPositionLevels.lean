import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailArchChannel
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailPrimeChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Upstream.PlancherelL1L2SpectralDensity
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanCoercive
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.GradedArchFloor
import Cvs.WeilForm.Archimedean.LevyIntegrandSpectral
import Cvs.WeilForm.Archimedean.LevyTruncationExhausts
import Cvs.WeilForm.EffectiveSymbolThreeFacts
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.Zeta.Digamma
import Cvs.Zeta.DigammaCriticalAsymptotic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `W_∞` from above by its position levels

`2⟨F, F − F_k⟩ = (N − N_k) + ‖F − F_k‖²` and `‖F − F_k‖² ≥ ∫_{θ ≥ k} F²`, whose level integral is `∫ log θ F²`, so
`Prime_∞ ≥ ∫_{k>1} (N − N_k)/k − ∫ log θ F²`. With the arch channel in spectral form and `∫ρ log⁺(|t|/T)` in level
form: `W_∞ ≤ 2Π₊∫F/θ + ∫(a − log⁺(|t|/T))ρ + ∫_{k>1} (N_k − specMass F (kT))/k + ∫ log θ F²`.
-/

noncomputable section

open Real Set Filter MeasureTheory

namespace Cvs.L2a.WinfPositionLevels

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.PositionTruncatedTail (posTail posTail_of_gt)
open Cvs.L2a.FullTailConvergence (fullTail BG K1b K1 C1_nonneg BG_nonneg)
open Cvs.L2a.TailLogScaleTest (logScale)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.WeilForm.SelfConvolutionCosine (specDensity)
open Cvs.L2a.SpectralMassLevelLeak (specMass)

variable {g g₁ g₂ : ℝ → ℝ} {c : ℝ}

/-! ### The position log in level form -/

/-- **One level of the position log**: with `ρ = 1_{θ>1} F²` and `q = 0` beyond `k > 1`,
`∫ρ − ∫_{|t|<k} ρ = ∫_{θ ≥ k} F² ≤ ∫_{θ>1} (F − q)²`. -/
theorem level_le {F q : ℝ → ℝ} {k : ℝ} (hk : 1 < k) (hq : ∀ θ, k < θ → q θ = 0)
    (hF : IntegrableOn (fun θ => F θ ^ 2) (Ioi 1)) (hFq : IntegrableOn (fun θ => (F θ - q θ) ^ 2) (Ioi 1)) :
    (∫ t, (Ioi 1).indicator (fun θ => F θ ^ 2) t)
        - ∫ t in {t : ℝ | |t| < k * 1}, (Ioi 1).indicator (fun θ => F θ ^ 2) t
      ≤ ∫ θ in Ioi 1, (F θ - q θ) ^ 2 := by
  set ρ := (Ioi (1 : ℝ)).indicator fun θ => F θ ^ 2
  have hρ : Integrable ρ := (integrable_indicator_iff measurableSet_Ioi).2 hF
  have hS := Cvs.L2a.SpectralMassLevelLeak.measurableSet_abs_lt (k * 1)
  have hsplit := integral_add_compl hS hρ
  have hset : {t : ℝ | |t| < k * 1}ᶜ ∩ Ioi 1 = Ici k := by
    ext t
    simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq, mem_Ioi, mem_Ici, mul_one, not_lt]
    constructor
    · rintro ⟨h1, h2⟩; rwa [abs_of_pos (one_pos.trans h2)] at h1
    · intro h; exact ⟨by rw [abs_of_pos (by linarith)]; exact h, by linarith⟩
  have hc : ∫ t in {t : ℝ | |t| < k * 1}ᶜ, ρ t = ∫ θ in Ici k, F θ ^ 2 := by
    rw [setIntegral_indicator measurableSet_Ioi, hset]
  have hIci : ∫ θ in Ici k, F θ ^ 2 = ∫ θ in Ioi k, (F θ - q θ) ^ 2 := by
    rw [integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
    simp only [hq θ hθ, sub_zero]
  have hmono : ∫ θ in Ioi k, (F θ - q θ) ^ 2 ≤ ∫ θ in Ioi 1, (F θ - q θ) ^ 2 :=
    setIntegral_mono_set hFq (Eventually.of_forall fun θ => sq_nonneg _)
      (Eventually.of_forall (Ioi_subset_Ioi hk.le))
  linarith

/-- `k ↦ ∫_{θ>1} (a − F_k)²` is measurable for measurable `a` and continuous `Φ`. -/
theorem measurable_gap {Φ a : ℝ → ℝ} (hΦ : Continuous Φ) (ha : Measurable a) :
    Measurable fun k => ∫ θ in Ioi 1, (a θ - posTail Φ k θ) ^ 2 := by
  have hf : Measurable fun p : ℝ × ℝ => (a p.2 - posTail Φ p.1 p.2) ^ 2 :=
    ((ha.comp measurable_snd).sub (Cvs.L2a.FullTailPrimeChannel.measurable_posTail_uncurry hΦ)).pow_const 2
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (1 : ℝ)))).measurable

theorem continuous_psi (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (c : ℝ) : Continuous (psi c g) :=
  (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous

/-- **The gap is integrable against `dk/k`**: `‖F_∞ − F_k‖² ≤ K1b/√k`. -/
theorem integrableOn_gap (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    IntegrableOn (fun k => (∫ θ in Ioi 1, (fullTail (psi c g) θ - posTail (psi c g) k θ) ^ 2) / k) (Ioi 1) := by
  set Kb := K1b c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hmeas := (measurable_gap (continuous_psi hg c) (Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc)).div
    measurable_id
  refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (show -(3 / 2 : ℝ) < -1 by norm_num) one_pos).const_mul Kb)
    hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun k (hk : 1 < k) => ?_))
  have hk0 : 0 < k := one_pos.trans hk
  have h0 : 0 ≤ ∫ θ in Ioi 1, (fullTail (psi c g) θ - posTail (psi c g) k θ) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hle : ∫ θ in Ioi 1, (fullTail (psi c g) θ - posTail (psi c g) k θ) ^ 2 ≤ Kb / √k := by
    have e : ∫ θ in Ioi 1, (fullTail (psi c g) θ - posTail (psi c g) k θ) ^ 2
        = ∫ θ in Ioi 1, (posTail (psi c g) k θ - fullTail (psi c g) θ) ^ 2 := by
      congr 1; funext θ; ring
    rw [e]
    exact (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hg hg₁ hg₂c hc hk.le).trans
      (Cvs.L2a.FullTailConvergence.K1_le hc _ _ hk.le)
  have hr : k ^ (-(3 / 2 : ℝ)) = 1 / (√k * k) := by
    rw [Real.sqrt_eq_rpow, show -(3 / 2 : ℝ) = -(1 / 2 + 1) by norm_num, rpow_neg hk0.le, rpow_add hk0, rpow_one]
    ring
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg h0, abs_of_pos hk0, hr]
  have hs : 0 < √k := Real.sqrt_pos.mpr hk0
  calc (∫ θ in Ioi 1, (fullTail (psi c g) θ - posTail (psi c g) k θ) ^ 2) / k ≤ Kb / √k / k :=
        div_le_div_of_nonneg_right hle hk0.le
    _ = Kb * (1 / (√k * k)) := by field_simp

/-- **The position log against the gaps**: `∫_{θ>1} log θ F_∞² ≤ ∫_{k>1} ‖F_∞ − F_k‖²/k`. -/
theorem integral_log_le_gaps (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    ∫ θ in Ioi 1, Real.log θ * fullTail (psi c g) θ ^ 2
      ≤ ∫ k in Ioi 1, (∫ θ in Ioi 1, (fullTail (psi c g) θ - posTail (psi c g) k θ) ^ 2) / k := by
  set F := fullTail (psi c g)
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hB : 0 ≤ B := BG_nonneg hc _ (C1_nonneg g₁ g₂)
  have hFm := Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc
  have hFB : ∀ θ, 0 < θ → |F θ| ≤ B / θ := fun θ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc hθ
  have hF2 : IntegrableOn (fun θ => F θ ^ 2) (Ioi 1) := Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hFm hFB
  set ρ := (Ioi (1 : ℝ)).indicator fun θ => F θ ^ 2 with hρd
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => indicator_nonneg (fun θ _ => sq_nonneg _) t
  have hρ : Integrable ρ := (integrable_indicator_iff measurableSet_Ioi).2 hF2
  -- `ρ log⁺|t|` is `1_{θ>1} log θ F²`
  have hlogeq : (fun t => ρ t * max 0 (Real.log (|t| / 1)))
      = (Ioi (1 : ℝ)).indicator fun θ => Real.log θ * F θ ^ 2 := by
    funext t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · have ht1 : (1 : ℝ) < t := ht
      rw [hρd, indicator_of_mem ht, indicator_of_mem ht, div_one, abs_of_pos (one_pos.trans ht1),
        max_eq_right (Real.log_nonneg ht1.le)]
      ring
    · rw [hρd, indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
  have hlogi : IntegrableOn (fun θ => Real.log θ * F θ ^ 2) (Ioi 1) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (show -(7 / 4 : ℝ) < -1 by norm_num)
      one_pos).const_mul (4 * B ^ 2)) (measurable_log.mul (hFm.pow_const 2)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
    have hθ0 : 0 < θ := one_pos.trans hθ
    have hl0 : 0 ≤ Real.log θ := Real.log_nonneg hθ.le
    have hlog : Real.log θ ≤ θ ^ (1 / 4 : ℝ) / (1 / 4) := Real.log_le_rpow_div hθ0.le (by norm_num)
    have hsq : F θ ^ 2 ≤ (B / θ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hFB θ hθ0) 2
    have hr : θ ^ (-(7 / 4 : ℝ)) = θ ^ (1 / 4 : ℝ) / θ ^ 2 := by
      rw [show -(7 / 4 : ℝ) = 1 / 4 - 2 by norm_num, rpow_sub hθ0, rpow_two]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl0 (sq_nonneg _)), hr]
    calc Real.log θ * F θ ^ 2 ≤ θ ^ (1 / 4 : ℝ) / (1 / 4) * (B / θ) ^ 2 :=
          mul_le_mul hlog hsq (sq_nonneg _) (hl0.trans hlog)
      _ = 4 * B ^ 2 * (θ ^ (1 / 4 : ℝ) / θ ^ 2) := by field_simp
  have hA : Integrable fun t => ρ t * max 0 (Real.log (|t| / 1)) := by
    rw [hlogeq]; exact (integrable_indicator_iff measurableSet_Ioi).2 hlogi
  obtain ⟨hlev, heq⟩ := Cvs.L2a.SpectralMassLevelLeak.integral_mul_logPlus_levels hρ0 hρ one_pos
  have hL : ∫ θ in Ioi 1, Real.log θ * F θ ^ 2 = ∫ t, ρ t * max 0 (Real.log (|t| / 1)) := by
    rw [hlogeq, integral_indicator measurableSet_Ioi]
  rw [hL, heq]
  refine setIntegral_mono_on (hlev hA) (integrableOn_gap hg hg₁ hg₂c hc) measurableSet_Ioi fun k (hk : 1 < k) => ?_
  refine div_le_div_of_nonneg_right ?_ (one_pos.trans hk).le
  have hq : ∀ θ, k < θ → posTail (psi c g) k θ = 0 := fun θ hθ => posTail_of_gt _ hθ
  have hFq : IntegrableOn (fun θ => (F θ - posTail (psi c g) k θ) ^ 2) (Ioi 1) := by
    have hd : ∀ θ, 0 < θ → |F θ - posTail (psi c g) k θ| ≤ 2 * B / θ := fun θ hθ => by
      rw [abs_sub_comm]; exact Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc k hθ
    exact Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le (hFm.sub (Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c k)) hd
  exact level_le hk hq hF2 hFq

/-! ### The prime channel and `W_∞` -/

/-- **The level identity**: `2⟨F, F − q⟩ = (∫F² − ∫q²) + ∫(F − q)²` on `(1, ∞)`. -/
theorem two_inner_eq {F q : ℝ → ℝ} (hF : IntegrableOn (fun θ => F θ ^ 2) (Ioi 1))
    (hq : IntegrableOn (fun θ => q θ ^ 2) (Ioi 1)) (hFq : IntegrableOn (fun θ => (F θ - q θ) ^ 2) (Ioi 1)) :
    2 * ∫ θ in Ioi 1, F θ * (F θ - q θ)
      = ((∫ θ in Ioi 1, F θ ^ 2) - ∫ θ in Ioi 1, q θ ^ 2) + ∫ θ in Ioi 1, (F θ - q θ) ^ 2 := by
  have e : ((∫ θ in Ioi 1, F θ ^ 2) - ∫ θ in Ioi 1, q θ ^ 2) + ∫ θ in Ioi 1, (F θ - q θ) ^ 2
      = ∫ θ in Ioi 1, ((F θ ^ 2 - q θ ^ 2) + (F θ - q θ) ^ 2) := by
    have hs : IntegrableOn (fun θ => F θ ^ 2 - q θ ^ 2) (Ioi 1) volume := hF.sub hq
    have h1 := integral_add hs hFq
    have h2 := integral_sub hF hq
    rw [h1, h2]
  rw [e, ← integral_const_mul]
  congr 1; funext θ; ring

/-- **The prime channel from below**: `Prime_∞ ≥ ∫_{k>1} (N − N_k)/k − ∫ log θ F²`, with the level integrand
integrable. -/
theorem primeInf_ge (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    IntegrableOn (fun k => ((∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) - ∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) / k)
        (Ioi 1)
      ∧ (∫ k in Ioi 1, ((∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) - ∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) / k)
          - ∫ θ in Ioi 1, Real.log θ * fullTail (psi c g) θ ^ 2
        ≤ Cvs.L2a.FullTailPrimeChannel.primeInf (psi c g) := by
  set F := fullTail (psi c g)
  set B := BG c (g 1 + g (-1)) (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|)
  have hFm := Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc
  have hFB : ∀ θ, 0 < θ → |F θ| ≤ B / θ := fun θ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc hθ
  set L : ℝ → ℝ := fun k => (∫ θ in Ioi 1, F θ * (F θ - posTail (psi c g) k θ)) / k with hLd
  set D : ℝ → ℝ := fun k => (∫ θ in Ioi 1, (F θ - posTail (psi c g) k θ) ^ 2) / k with hDd
  set E : ℝ → ℝ := fun k => ((∫ θ in Ioi 1, F θ ^ 2) - ∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) / k with hEd
  have hLi : IntegrableOn L (Ioi 1) := Cvs.L2a.FullTailPrimeChannel.integrableOn_level hg hg₁ hg₂c hc
  have hDi : IntegrableOn D (Ioi 1) := integrableOn_gap hg hg₁ hg₂c hc
  have hE : EqOn E (fun k => 2 * L k - D k) (Ioi 1) := by
    intro k _
    have hqm := Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c k
    have hqB : ∀ θ, 0 < θ → |posTail (psi c g) k θ| ≤ B / θ := fun θ hθ =>
      Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc k hθ
    have hd : ∀ θ, 0 < θ → |F θ - posTail (psi c g) k θ| ≤ 2 * B / θ := fun θ hθ => by
      rw [abs_sub_comm]; exact Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc k hθ
    have h := two_inner_eq (Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hFm hFB)
      (Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hqm hqB)
      (Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le (hFm.sub hqm) hd)
    simp only [hEd, hLd, hDd]
    rw [mul_div_assoc', h]; ring
  have hEi : IntegrableOn E (Ioi 1) :=
    IntegrableOn.congr_fun (show IntegrableOn (fun k => 2 * L k - D k) (Ioi 1) volume from (hLi.const_mul 2).sub hDi)
      hE.symm measurableSet_Ioi
  refine ⟨hEi, ?_⟩
  have hEint : ∫ k in Ioi 1, E k = 2 * (∫ k in Ioi 1, L k) - ∫ k in Ioi 1, D k := by
    rw [setIntegral_congr_fun measurableSet_Ioi hE, integral_sub (hLi.const_mul 2) hDi, integral_const_mul]
  have hlog := integral_log_le_gaps hg hg₁ hg₂c hc
  have hP : Cvs.L2a.FullTailPrimeChannel.primeInf (psi c g)
      = 2 * (∫ k in Ioi 1, L k) - 2 * ∫ θ in Ioi 1, Real.log θ * F θ ^ 2 := rfl
  rw [hP, hEint]
  linarith

/-- **`W_∞` from above by its position levels**: for `T ≥ 2`,
`W_∞ ≤ 2Π₊∫F/θ + ∫(a(t) − log⁺(|t|/T))ρ + ∫_{k>1} (N_k − specMass F (kT))/k + ∫ log θ F²`. -/
theorem Winf_le_levels (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {T : ℝ} (hT : 2 ≤ T) :
    IntegrableOn (fun k => ((∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass (fullTail (psi c g)) (k * T)) / k)
        (Ioi 1)
      ∧ Cvs.L2a.FullTailWeilFormLimit.Winf (psi c g)
        ≤ 2 * Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) * (∫ θ in Ioi 1, fullTail (psi c g) θ / θ)
          + (∫ t, (archSymbol t - max 0 (Real.log (|t| / T))) * specDensity (logScale (fullTail (psi c g))) t)
          + (∫ k in Ioi 1, ((∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass (fullTail (psi c g)) (k * T)) / k)
          + ∫ θ in Ioi 1, Real.log θ * fullTail (psi c g) θ ^ 2 := by
  set F := fullTail (psi c g)
  set ρ := specDensity (logScale F)
  set N := ∫ θ in Ioi 1, F θ ^ 2
  have hT0 : 0 < T := by linarith
  obtain ⟨h2, h1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hg hg₁ hg₂c hc
  have hlevy := Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc
  have hρ0 : ∀ t, 0 ≤ ρ t := fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t
  have hρ := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1
  have haρ : Integrable fun t => archSymbol t * ρ t := Cvs.WeilForm.EffectiveSymbolThreeFacts.integrable_arch_mul h2 h1 hlevy
  have hlp := Cvs.WeilForm.Archimedean.GradedArchFloor.integrable_mul_logPlus ρ hρ0 hρ haρ hT
  have hF0 : ∀ θ ≤ 1, F θ = 0 := fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ
  have hSi := Cvs.L2a.SpectralMassLevelLeak.integrableOn_levels hF0 h2 h1 hT0 hlp
  have hSe := Cvs.L2a.SpectralMassLevelLeak.integral_mul_logPlus_eq hF0 h2 h1 hT0
  obtain ⟨hEi, hpr⟩ := primeInf_ge hg hg₁ hg₂c hc
  set S : ℝ → ℝ := fun k => (N - specMass F (k * T)) / k with hSd
  set E : ℝ → ℝ := fun k => (N - ∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) / k with hEd
  have hdiff : EqOn (fun k => ((∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass F (k * T)) / k)
      (fun k => S k - E k) (Ioi 1) := fun k _ => by simp only [hSd, hEd]; ring
  have hDi : IntegrableOn (fun k => ((∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass F (k * T)) / k) (Ioi 1) :=
    IntegrableOn.congr_fun (show IntegrableOn (fun k => S k - E k) (Ioi 1) volume from hSi.sub hEi) hdiff.symm
      measurableSet_Ioi
  refine ⟨hDi, ?_⟩
  have harch : archSymbol 0 * N + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale F) = ∫ t, archSymbol t * ρ t :=
    Cvs.L2a.FullTailWeilFormLimit.arch_fullTail_eq_spectral hg hg₁ hg₂c hc
  have hsplit : ∫ t, archSymbol t * ρ t
      = (∫ t, (archSymbol t - max 0 (Real.log (|t| / T))) * ρ t) + ∫ t, ρ t * max 0 (Real.log (|t| / T)) := by
    rw [← integral_add (haρ.sub hlp |>.congr (Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)) hlp]
    congr 1; funext t; ring
  have hlev : ∫ k in Ioi 1, ((∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass F (k * T)) / k
      = (∫ k in Ioi 1, S k) - ∫ k in Ioi 1, E k := by
    rw [setIntegral_congr_fun measurableSet_Ioi hdiff, integral_sub hSi hEi]
  have hW : Cvs.L2a.FullTailWeilFormLimit.Winf (psi c g)
      = 2 * Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) * (∫ θ in Ioi 1, F θ / θ)
        + (archSymbol 0 * N + Cvs.WeilForm.Archimedean.LevyTruncationExhausts.archFull (logScale F))
        - Cvs.L2a.FullTailPrimeChannel.primeInf (psi c g) := rfl
  rw [hW, harch, hsplit, hSe, hlev]
  linarith

/-! ### The arch bracket and the position log -/

/-- For `2 ≤ T`, `archSymbol t − log⁺(|t|/T) ≤ archSymbol T + 114/T` at every `t`. -/
theorem archSymbol_sub_logPlus_le {T : ℝ} (hT : 2 ≤ T) (t : ℝ) :
    archSymbol t - max 0 (Real.log (|t| / T)) ≤ archSymbol T + 114 / T := by
  have hT0 : (0:ℝ) < T := by linarith
  have h114 : 0 ≤ 114 / T := by positivity
  rcases le_or_gt |t| T with ht | ht
  · have hm : archSymbol t ≤ archSymbol T := by
      rw [← Cvs.WeilForm.Archimedean.GradedArchFloor.archSymbol_abs t]
      exact Cvs.WeilForm.Archimedean.ArchimedeanCoercive.archSymbol_mono (pow_le_pow_left₀ (abs_nonneg _) ht 2)
    have := le_max_left 0 (Real.log (|t| / T))
    linarith
  · have hs : 2 ≤ |t| := hT.trans ht.le
    have hhi := (abs_le.mp (DigammaAsym.abs_re_digamma_sub_log_le |t| hs)).2
    have hlo := (abs_le.mp (DigammaAsym.abs_re_digamma_sub_log_le T hT)).1
    have hlog : Real.log (|t| / T) = Real.log (|t| / 2) - Real.log (T / 2) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1; field_simp
    have h57 : 57 / |t| ≤ 57 / T := div_le_div_of_nonneg_left (by norm_num) hT0 ht.le
    have hmax := le_max_right 0 (Real.log (|t| / T))
    rw [← Cvs.WeilForm.Archimedean.GradedArchFloor.archSymbol_abs t]
    unfold archSymbol
    have : 114 / T = 57 / T + 57 / T := by ring
    linarith

/-- **The arch bracket**: `∫(a(t) − log⁺(|t|/T))ρ ≤ (a(T) + 114/T) ∫ρ` for `ρ ≥ 0` integrable with `aρ` integrable. -/
theorem integral_arch_sub_logPlus_le {ρ : ℝ → ℝ} (hρ0 : ∀ t, 0 ≤ ρ t) (hρ : Integrable ρ)
    (hA : Integrable fun t => archSymbol t * ρ t) {T : ℝ} (hT : 2 ≤ T) :
    ∫ t, (archSymbol t - max 0 (Real.log (|t| / T))) * ρ t ≤ (archSymbol T + 114 / T) * ∫ t, ρ t := by
  have hlp := Cvs.WeilForm.Archimedean.GradedArchFloor.integrable_mul_logPlus ρ hρ0 hρ hA hT
  rw [← integral_const_mul]
  refine integral_mono (hA.sub hlp |>.congr (Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring))
    (hρ.const_mul _) fun t => ?_
  exact mul_le_mul_of_nonneg_right (archSymbol_sub_logPlus_le hT t) (hρ0 t)

/-- `∫_Θ^∞ log θ/θ² = (1 + log Θ)/Θ` for `Θ ≥ 1`, with integrability. -/
theorem integral_log_div_sq {Θ : ℝ} (hΘ : 1 ≤ Θ) :
    IntegrableOn (fun θ => Real.log θ / θ ^ 2) (Ioi Θ)
      ∧ ∫ θ in Ioi Θ, Real.log θ / θ ^ 2 = (1 + Real.log Θ) / Θ := by
  have hΘ0 : 0 < Θ := by linarith
  have hderiv : ∀ θ ∈ Ici Θ, HasDerivAt (fun θ => -(1 + Real.log θ) / θ) (Real.log θ / θ ^ 2) θ := by
    intro θ hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le hΘ0 hθ
    have h1 : HasDerivAt (fun θ => -(1 + Real.log θ)) (-θ⁻¹) θ := by
      exact ((hasDerivAt_log hθ0.ne').const_add 1).neg
    refine (h1.div (hasDerivAt_id' θ) hθ0.ne').congr_deriv ?_
    field_simp
    ring
  have hnn : ∀ θ ∈ Ioi Θ, 0 ≤ Real.log θ / θ ^ 2 := fun θ hθ =>
    div_nonneg (Real.log_nonneg (hΘ.trans (le_of_lt hθ))) (sq_nonneg _)
  have hlim : Tendsto (fun θ => -(1 + Real.log θ) / θ) atTop (nhds 0) := by
    have h1 : Tendsto (fun θ : ℝ => Real.log θ / θ) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun θ : ℝ => 1 / θ) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
    have := (h2.add h1).neg
    simp only [add_zero, neg_zero] at this
    refine this.congr' (eventually_gt_atTop 0 |>.mono fun θ hθ => ?_)
    field_simp
  have hint : IntegrableOn (fun θ => Real.log θ / θ ^ 2) (Ioi Θ) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hnn hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn hlim]
  ring

/-- **The position log, split at `Θ`**: if `|F| ≤ B/θ` then `∫_{θ>1} log θ F² ≤ log Θ · ∫_{θ>1} F² + B²(1 + log Θ)/Θ`
for every `Θ ≥ 1`. -/
theorem integral_log_mul_sq_le {F : ℝ → ℝ} (hFm : Measurable F) {B : ℝ} (hFB : ∀ θ, 0 < θ → |F θ| ≤ B / θ)
    {Θ : ℝ} (hΘ : 1 ≤ Θ) :
    ∫ θ in Ioi 1, Real.log θ * F θ ^ 2
      ≤ Real.log Θ * (∫ θ in Ioi 1, F θ ^ 2) + B ^ 2 * ((1 + Real.log Θ) / Θ) := by
  have hΘ0 : 0 < Θ := by linarith
  have hF2 : IntegrableOn (fun θ => F θ ^ 2) (Ioi 1) := Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hFm hFB
  obtain ⟨hli, hlv⟩ := integral_log_div_sq hΘ
  have hsq : ∀ θ, 0 < θ → F θ ^ 2 ≤ B ^ 2 / θ ^ 2 := fun θ hθ => by
    rw [← sq_abs, ← div_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hFB θ hθ) 2
  -- the majorant `log Θ · F² 1_{θ ≤ Θ} + B² log θ/θ² 1_{θ > Θ}`
  set M : ℝ → ℝ := fun θ => Real.log Θ * F θ ^ 2 + (Ioi Θ).indicator (fun θ => B ^ 2 * (Real.log θ / θ ^ 2)) θ
  have hMi : IntegrableOn M (Ioi 1) :=
    (hF2.const_mul _).add (((integrable_indicator_iff measurableSet_Ioi).2 (hli.const_mul (B ^ 2))).integrableOn)
  have hle : ∀ θ ∈ Ioi (1 : ℝ), Real.log θ * F θ ^ 2 ≤ M θ := by
    intro θ (hθ : 1 < θ)
    have hθ0 : 0 < θ := one_pos.trans hθ
    have hl0 : 0 ≤ Real.log θ := Real.log_nonneg hθ.le
    simp only [M]
    by_cases hθΘ : θ ∈ Ioi Θ
    · rw [indicator_of_mem hθΘ]
      have h1 : Real.log θ * F θ ^ 2 ≤ B ^ 2 * (Real.log θ / θ ^ 2) := by
        rw [mul_div_assoc', mul_comm (B ^ 2)]; rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hsq θ hθ0) hl0
      have h2 : 0 ≤ Real.log Θ * F θ ^ 2 := mul_nonneg (Real.log_nonneg hΘ) (sq_nonneg _)
      linarith
    · rw [indicator_of_notMem hθΘ, add_zero]
      have hθΘ' : θ ≤ Θ := not_lt.mp hθΘ
      exact mul_le_mul_of_nonneg_right (Real.log_le_log hθ0 hθΘ') (sq_nonneg _)
  have hlogi : IntegrableOn (fun θ => Real.log θ * F θ ^ 2) (Ioi 1) := by
    refine Integrable.mono' hMi (measurable_log.mul (hFm.pow_const 2)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun θ (hθ : 1 < θ) => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.log_nonneg hθ.le) (sq_nonneg _))]
    exact hle θ hθ
  refine (setIntegral_mono_on hlogi hMi measurableSet_Ioi hle).trans (le_of_eq ?_)
  simp only [M]
  rw [integral_add (hF2.const_mul _) ((integrable_indicator_iff measurableSet_Ioi).2 (hli.const_mul (B ^ 2))).integrableOn,
    integral_const_mul, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Ioi_subset_Ioi hΘ), integral_const_mul, hlv]

/-! ### The bracket -/

/-- **One level, against the full tail's low mass**: if `specMass (F_k − F) K ≤ e N`, then
`N_k − specMass F K ≤ (N_k − specMass F_k K) + (2√e + e) N`. -/
theorem level_gap_le {F Fk : ℝ → ℝ} (hF : ∀ θ ≤ 1, F θ = 0)
    (h2 : MemLp (logScale F) 2 volume) (h1 : Integrable (logScale F) volume)
    (h2k : MemLp (logScale Fk) 2 volume) (h1k : Integrable (logScale Fk) volume) {K e : ℝ} (he : 0 ≤ e)
    (hfar : specMass (Fk - F) K ≤ e * ∫ θ in Ioi 1, F θ ^ 2) :
    (∫ θ in Ioi 1, Fk θ ^ 2) - specMass F K
      ≤ ((∫ θ in Ioi 1, Fk θ ^ 2) - specMass Fk K) + (2 * √e + e) * ∫ θ in Ioi 1, F θ ^ 2 := by
  set N := ∫ θ in Ioi 1, F θ ^ 2
  have hN0 : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hAN : specMass F K ≤ N := Cvs.L2a.SpectralMassLevelLeak.specMass_le hF h2 h1 K
  have hM : √(specMass Fk K) ≤ √(specMass F K) + √(specMass (Fk - F) K) := by
    have e1 : Fk = F + (Fk - F) := (add_sub_cancel F Fk).symm
    conv_lhs => rw [e1]
    refine Cvs.L2a.SpectralMassLevelLeak.sqrt_specMass_add_le h2 h1 ?_ ?_ K
    · rw [Cvs.L2a.SpectralMassLevelLeak.logScale_sub]; exact h2k.sub h2
    · rw [Cvs.L2a.SpectralMassLevelLeak.logScale_sub]; exact h1k.sub h1
  set A := specMass F K
  set B := specMass Fk K
  set C := specMass (Fk - F) K
  have hA0 := Cvs.L2a.SpectralMassLevelLeak.specMass_nonneg F K
  have hB0 := Cvs.L2a.SpectralMassLevelLeak.specMass_nonneg Fk K
  have hC0 := Cvs.L2a.SpectralMassLevelLeak.specMass_nonneg (Fk - F) K
  have hsA := Real.sq_sqrt hA0
  have hsB := Real.sq_sqrt hB0
  have hsC := Real.sq_sqrt hC0
  have hsN := Real.sq_sqrt hN0
  have hc : √C ≤ √e * √N := by rw [← Real.sqrt_mul' e hN0]; exact Real.sqrt_le_sqrt hfar
  have ha : √A ≤ √N := Real.sqrt_le_sqrt hAN
  have hse := Real.sq_sqrt he
  have hB : B ≤ A + 2 * √A * √C + C := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hM 2
    nlinarith
  have hAC : √A * √C ≤ √e * N := by
    calc √A * √C ≤ √N * (√e * √N) :=
          mul_le_mul ha hc (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = √e * N := by rw [← hsN]; ring_nf; rw [hsN]; ring_nf; nlinarith [Real.sqrt_nonneg N, Real.sqrt_nonneg e]
  have hCN : C ≤ e * N := hfar
  nlinarith [Real.sqrt_nonneg e]

/-- **The `W_∞` bracket**: for `T ≥ 2` and a level majorant `N_k − specMass F (kT) ≤ λ(k)` on `(1, ∞)` with `λ/k`
integrable, `W_∞ ≤ 2Π₊∫F/θ + (a(T) + 114/T) N + ∫_{k>1} λ(k)/k + ∫ log θ F²`. -/
theorem Winf_le_bracket (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) {T : ℝ} (hT : 2 ≤ T) (lam : ℝ → ℝ) (hlam : IntegrableOn (fun k => lam k / k) (Ioi 1))
    (hlev : ∀ k, 1 < k → (∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass (fullTail (psi c g)) (k * T) ≤ lam k) :
    Cvs.L2a.FullTailWeilFormLimit.Winf (psi c g)
      ≤ 2 * Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) * (∫ θ in Ioi 1, fullTail (psi c g) θ / θ)
        + (archSymbol T + 114 / T) * (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)
        + (∫ k in Ioi 1, lam k / k)
        + ∫ θ in Ioi 1, Real.log θ * fullTail (psi c g) θ ^ 2 := by
  obtain ⟨hDi, hW⟩ := Winf_le_levels hg hg₁ hg₂c hc hT
  obtain ⟨h2, h1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hg hg₁ hg₂c hc
  have hlevy := Cvs.L2a.FullTailArchChannel.integrableOn_levy_fullTail hg hg₁ hg₂c hc
  have hρ := Cvs.WeilForm.Archimedean.LevyIntegrandSpectral.integrable_specDensity h2 h1
  have haρ := Cvs.WeilForm.EffectiveSymbolThreeFacts.integrable_arch_mul h2 h1 hlevy
  have harch := integral_arch_sub_logPlus_le (fun t => Cvs.WeilForm.SelfConvolutionCosine.specDensity_nonneg _ t) hρ haρ hT
  have hN : ∫ t, specDensity (logScale (fullTail (psi c g))) t = ∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2 := by
    rw [Cvs.Upstream.PlancherelL1L2SpectralDensity.integral_specDensity h1 h2,
      Cvs.L2a.TailLogScaleTest.integral_sq _ fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ]
  rw [hN] at harch
  have hmono := setIntegral_mono_on hDi hlam measurableSet_Ioi fun k (hk : 1 < k) =>
    div_le_div_of_nonneg_right (hlev k hk) (one_pos.trans hk).le
  linarith

end Cvs.L2a.WinfPositionLevels
