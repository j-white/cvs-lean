import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.Envelope.RungDuhamelRemainder
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Route.Visibility.CaseFiniteFromWindowChain
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.WeilForm.PoleTermCauchySchwarz

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The centre bound `λ(1 − λ)h(0)² ≤ 2/π²` and the `g0` part of the per-rung box

For `ψ_φ(ξ) = ∫_{−1}^{1} φ(s) cos(cξs) ds`, polarised Plancherel gives `∫_ℝ ψ_φ ψ_1 = (2π/c)∫_{−1}^{1} φ`, and Fubini
gives `∫_{−1}^{1} φ ψ_1 = ∫_{−1}^{1} ψ_φ`. On a rung `ψ = μh` on `[−1, 1]`, so the exterior pairing is
`∫_{|ξ|>1} ψ ψ_1 = μh(0)(2π/c − μ²)`, and Cauchy–Schwarz with `ψ_1(ξ)² ≤ 4/(cξ)²` gives `λ(1 − λ)h(0)² ≤ 2/π²`.
With `G_j(0) = (1 − μ_{4j}/μ_0)h_{4j}(0)` this is `|g0 x e_j| ≤ (4/π)x⁻¹√(1 − λ_j)`.
-/

noncomputable section

open Real Set MeasureTheory Filter
open scoped FourierTransform Interval
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)
open Cvs.Prolate.EvenRungsByIndex (IsLevelIdx rung rung_spec muR lamR psi_rung continuousOn_rung)
open Cvs.Prolate.RungSpanBernsteinNikolskii (winLift fourier_winLift norm_sub_mul_I_sq)

namespace Cvs.Prolate.Envelope.RungCentreBound
open Cvs.ZeroCounting

/-! ### Polarised Plancherel for the cosine transform -/

/-- `‖𝓕(1_{[−1,1]}φ)(cξ/2π)‖² = ψ_φ(ξ)² + (∫_{−1}^{1} φ(t) sin(cξt) dt)²`. -/
theorem norm_fourier_sq {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (ξ : ℝ) :
    ‖𝓕 (winLift φ) (c / (2 * π) * ξ)‖ ^ 2
      = psi c φ ξ ^ 2 + (∫ t in (-1 : ℝ)..1, φ t * sin (c * ξ * t)) ^ 2 := by
  rw [fourier_winLift hφ, norm_sub_mul_I_sq]
  have e : ∀ t, 2 * π * (c / (2 * π) * ξ) * t = c * ξ * t := fun t => by field_simp
  simp only [e]
  rfl

/-- The sine transform of the constant `1` over `[−1, 1]` vanishes. -/
theorem integral_sin_eq_zero (k : ℝ) : ∫ t in (-1 : ℝ)..1, sin (k * t) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1) fun t => sin (k * t)
  simp only [neg_neg, mul_neg, sin_neg, intervalIntegral.integral_neg] at h
  linarith

/-- `ψ_{φ+d} = ψ_φ + d·ψ_1`. -/
theorem psi_add_const (c d : ℝ) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (ξ : ℝ) :
    psi c (fun s => φ s + d) ξ = psi c φ ξ + d * psi c (fun _ => 1) ξ := by
  simp only [psi, kint]
  have h1 : IntervalIntegrable (fun s => φ s * cos (c * ξ * s)) volume (-1) 1 :=
    (hφ.mul (by fun_prop)).intervalIntegrable
  have h2 : IntervalIntegrable (fun s => d * cos (c * ξ * s)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [← intervalIntegral.integral_const_mul]
  simp only [one_mul]
  rw [← intervalIntegral.integral_add h1 h2]
  exact intervalIntegral.integral_congr fun s _ => by ring

/-- The sine part of `φ + d` is the sine part of `φ`. -/
theorem sinPart_add_const (c d : ℝ) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) (ξ : ℝ) :
    ∫ t in (-1 : ℝ)..1, (φ t + d) * sin (c * ξ * t) = ∫ t in (-1 : ℝ)..1, φ t * sin (c * ξ * t) := by
  have h1 : IntervalIntegrable (fun t => φ t * sin (c * ξ * t)) volume (-1) 1 :=
    (hφ.mul (by fun_prop)).intervalIntegrable
  have h2 : IntervalIntegrable (fun t => d * sin (c * ξ * t)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have e : (fun t => (φ t + d) * sin (c * ξ * t)) = fun t => φ t * sin (c * ξ * t) + d * sin (c * ξ * t) := by
    funext t; ring
  rw [e, intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul, integral_sin_eq_zero, mul_zero,
    add_zero]

/-- `|ab| ≤ (a² + b²)/2` makes `ψ_φ ψ_1` integrable. -/
theorem integrable_psi_mul {c : ℝ} (hc : 0 < c) {φ χ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1))
    (hχ : ContinuousOn χ (uIcc (-1) 1)) : Integrable fun ξ => psi c φ ξ * psi c χ ξ := by
  refine (((Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc hφ).add (Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc hχ)).div_const 2).mono'
    ((Cvs.Prolate.RungSpanBernsteinNikolskii.continuous_psi hφ).mul (Cvs.Prolate.RungSpanBernsteinNikolskii.continuous_psi hχ)).aestronglyMeasurable
    (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|psi c φ ξ| - |psi c χ ξ|), sq_abs (psi c φ ξ), sq_abs (psi c χ ξ)]

/-- **Polarised Plancherel**: `∫_ℝ ψ_φ ψ_1 = (2π/c)∫_{−1}^{1} φ`. -/
theorem integral_psi_mul_psi_one {c : ℝ} (hc : 0 < c) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    ∫ ξ, psi c φ ξ * psi c (fun _ => 1) ξ = 2 * π / c * ∫ s in (-1 : ℝ)..1, φ s := by
  have hp : ContinuousOn (fun s => φ s + 1) (uIcc (-1) 1) := hφ.add continuousOn_const
  have hm : ContinuousOn (fun s => φ s + -1) (uIcc (-1) 1) := hφ.add continuousOn_const
  obtain ⟨ip, ep⟩ := Cvs.Prolate.RungSpanBernsteinNikolskii.fourier_scaled hc hp
  obtain ⟨im, em⟩ := Cvs.Prolate.RungSpanBernsteinNikolskii.fourier_scaled hc hm
  have key : ∀ ξ, ‖𝓕 (winLift fun s => φ s + 1) (c / (2 * π) * ξ)‖ ^ 2
      - ‖𝓕 (winLift fun s => φ s + -1) (c / (2 * π) * ξ)‖ ^ 2 = 4 * (psi c φ ξ * psi c (fun _ => 1) ξ) := fun ξ => by
    rw [norm_fourier_sq hc hp, norm_fourier_sq hc hm, psi_add_const c 1 hφ, psi_add_const c (-1) hφ,
      sinPart_add_const c 1 hφ, sinPart_add_const c (-1) hφ]
    ring
  have h := integral_sub ip im
  simp only [key] at h
  rw [integral_const_mul, ep, em] at h
  have hφi : IntervalIntegrable φ volume (-1) 1 := hφ.intervalIntegrable
  have hsq : ∀ d : ℝ, ∫ s in (-1 : ℝ)..1, (φ s + d) ^ 2
      = (∫ s in (-1 : ℝ)..1, φ s ^ 2) + 2 * d * (∫ s in (-1 : ℝ)..1, φ s) + d ^ 2 * 2 := fun d => by
    have e : (fun s => (φ s + d) ^ 2) = fun s => (φ s ^ 2 + 2 * d * φ s) + d ^ 2 := by funext s; ring
    have i1 : IntervalIntegrable (fun s => φ s ^ 2) volume (-1) 1 := (hφ.pow 2).intervalIntegrable
    rw [e, intervalIntegral.integral_add (i1.add (hφi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_add i1 (hφi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp; ring
  rw [hsq, hsq] at h
  linarith

/-! ### The transform of `1` and the exterior -/

/-- `ψ_1(ξ) = ∫_{−1}^{1} cos(cξs) ds` satisfies `(cξ)²ψ_1(ξ)² ≤ 4`. -/
theorem sq_mul_psi_one_sq_le (c ξ : ℝ) : (c * ξ) ^ 2 * psi c (fun _ => 1) ξ ^ 2 ≤ 4 := by
  by_cases hk : c * ξ = 0
  · rw [hk]; norm_num
  have e : psi c (fun _ => 1) ξ = (c * ξ)⁻¹ * (sin (c * ξ) - sin (c * ξ * -1)) := by
    simp only [psi, kint, one_mul]
    rw [intervalIntegral.integral_comp_mul_left (fun s => cos s) hk, integral_cos, smul_eq_mul, mul_one]
  rw [e, mul_neg_one, sin_neg]
  generalize c * ξ = k at hk ⊢
  have h1 := abs_sin_le_one k
  have e2 : k ^ 2 * (k⁻¹ * (sin k - -sin k)) ^ 2 = 4 * sin k ^ 2 := by
    field_simp; ring
  rw [e2]
  nlinarith [sq_abs (sin k), abs_nonneg (sin k)]

/-- The exterior of the window, `{ξ : 1 < |ξ|}`. -/
abbrev extSet : Set ℝ := (Icc (-1 : ℝ) 1)ᶜ

/-- The bound on the exterior, supported on `ξ > 1`: `4/(cξ)²`. -/
def tailBound (c : ℝ) (ξ : ℝ) : ℝ := (Ioi (1 : ℝ)).indicator (fun t => 4 / c ^ 2 * t ^ (-2 : ℝ)) ξ

/-- The tail bound is integrable. -/
theorem integrable_tailBound (c : ℝ) : Integrable (tailBound c) := by
  unfold tailBound
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul _

/-- `∫_{ξ>1} 4/(cξ)² = 4/c²`. -/
theorem integral_tailBound (c : ℝ) : ∫ ξ, tailBound c ξ = 4 / c ^ 2 := by
  unfold tailBound
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos]
  norm_num

/-- `ψ_1² ≤ 4/(cξ)²` on the exterior, split into the two half-lines. -/
theorem indicator_psi_one_sq_le {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    extSet.indicator (fun ξ => psi c (fun _ => 1) ξ ^ 2) ξ ≤ tailBound c ξ + tailBound c (-ξ) := by
  have h0 : ∀ t, 0 ≤ tailBound c t := fun t => by
    unfold tailBound
    exact indicator_nonneg (fun t ht => by have : (0 : ℝ) < t := lt_trans one_pos ht; positivity) t
  by_cases hξ : ξ ∈ extSet
  · rw [indicator_of_mem hξ]
    have key : ∀ t : ℝ, 1 < t → t ^ 2 = ξ ^ 2 → psi c (fun _ => 1) ξ ^ 2 ≤ tailBound c t := fun t ht he => by
      unfold tailBound
      rw [indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), Real.rpow_neg (by linarith),
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, he]
      have hξ0 : ξ ^ 2 ≠ 0 := by rw [← he]; exact pow_ne_zero 2 (ne_of_gt (by linarith))
      have := sq_mul_psi_one_sq_le c ξ
      rw [mul_pow] at this
      rw [show 4 / c ^ 2 * (ξ ^ 2)⁻¹ = 4 / (c ^ 2 * ξ ^ 2) by field_simp, le_div_iff₀ (by positivity)]
      linarith
    simp only [extSet, mem_compl_iff, mem_Icc, not_and_or, not_le] at hξ
    rcases hξ with h | h
    · have := key (-ξ) (by linarith) (by ring)
      linarith [h0 ξ]
    · have := key ξ h rfl
      linarith [h0 (-ξ)]
  · rw [indicator_of_notMem hξ]; linarith [h0 ξ, h0 (-ξ)]

/-- `∫_{|ξ|>1} ψ_1² ≤ 8/c²`. -/
theorem integral_ext_psi_one_sq_le {c : ℝ} (hc : 0 < c) :
    ∫ ξ in extSet, psi c (fun _ => 1) ξ ^ 2 ≤ 8 / c ^ 2 := by
  have hI : Integrable fun ξ => tailBound c ξ + tailBound c (-ξ) :=
    (integrable_tailBound c).add (integrable_tailBound c).comp_neg
  rw [← integral_indicator (measurableSet_Icc.compl)]
  refine (integral_mono_of_nonneg (ae_of_all _ fun ξ => indicator_nonneg (fun _ _ => sq_nonneg _) ξ) hI
    (ae_of_all _ (indicator_psi_one_sq_le hc))).trans_eq ?_
  rw [integral_add (integrable_tailBound c) (integrable_tailBound c).comp_neg,
    integral_neg_eq_self (tailBound c), integral_tailBound]
  ring

/-! ### Fubini on the window -/

/-- `∫_{−1}^{1} φ ψ_1 = ∫_{−1}^{1} ψ_φ`. -/
theorem integral_mul_psi_one (c : ℝ) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (uIcc (-1) 1)) :
    ∫ ξ in (-1 : ℝ)..1, φ ξ * psi c (fun _ => 1) ξ = ∫ t in (-1 : ℝ)..1, psi c φ t := by
  simp only [psi, kint, one_mul]
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hφ
  have hF : ContinuousOn (fun p : ℝ × ℝ => φ p.1 * cos (c * p.1 * p.2)) (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) :=
    (hφ.comp continuousOn_fst fun (p : ℝ × ℝ) (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) =>
      (Set.mem_prod.1 hp).1).mul (by fun_prop)
  have hint : Integrable (Function.uncurry fun ξ s : ℝ => φ ξ * cos (c * ξ * s))
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod (volume.restrict (Ioc (-1 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simp only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have e1 : ∀ ξ, φ ξ * ∫ s in Ioc (-1 : ℝ) 1, cos (c * ξ * s) = ∫ s in Ioc (-1 : ℝ) 1, φ ξ * cos (c * ξ * s) :=
    fun ξ => (integral_const_mul _ _).symm
  simp only [e1]
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  simp only [mul_assoc, mul_comm (c : ℝ)]
  ring_nf

/-! ### The centre bound -/

section rung

variable {c : ℝ} {k : ℕ}

/-- The window pairing on a rung: `∫_{−1}^{1} ψ ψ_1 = μ²∫_{−1}^{1} h`. -/
theorem integral_Icc_psi_mul_psi_one (h : ∃ χ, IsLevelIdx c k χ) :
    ∫ ξ in Icc (-1 : ℝ) 1, psi c (rung c k) ξ * psi c (fun _ => 1) ξ
      = muR c k ^ 2 * ∫ s in (-1 : ℝ)..1, rung c k s := by
  have hg : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact continuousOn_rung h
  have hu : ∀ ξ ∈ uIcc (-1 : ℝ) 1, ξ ∈ Icc (-1 : ℝ) 1 := fun ξ hξ => by
    rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hξ
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_congr (g := fun ξ => muR c k * (rung c k ξ * psi c (fun _ => 1) ξ))
      fun ξ hξ => by simp only; rw [psi_rung h ξ (hu ξ hξ)]; ring,
    intervalIntegral.integral_const_mul, integral_mul_psi_one c hg,
    intervalIntegral.integral_congr (g := fun t => muR c k * rung c k t) fun t ht => psi_rung h t (hu t ht),
    intervalIntegral.integral_const_mul]
  ring

/-- `∫_{−1}^{1} h = μh(0)`. -/
theorem integral_rung_eq (h : ∃ χ, IsLevelIdx c k χ) : ∫ s in (-1 : ℝ)..1, rung c k s = muR c k * rung c k 0 := by
  rw [← psi_rung h 0 ⟨by norm_num, by norm_num⟩]
  simp [psi, kint]

/-- `∫_{|ξ|>1} ψ² ≤ 2π/c − μ²`. -/
theorem integral_ext_psi_sq_le (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) :
    ∫ ξ in extSet, psi c (rung c k) ξ ^ 2 ≤ 2 * π / c - muR c k ^ 2 := by
  obtain ⟨-, -, -, -, -, hnorm⟩ := rung_spec h
  have hg : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact continuousOn_rung h
  have hfull := Cvs.Prolate.RungSpanBernsteinNikolskii.integral_psi_sq_le hc hg
  rw [hnorm, mul_one] at hfull
  have hsplit := integral_add_compl (measurableSet_Icc (a := (-1 : ℝ)) (b := 1)) (Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc hg)
  have hin : ∫ ξ in Icc (-1 : ℝ) 1, psi c (rung c k) ξ ^ 2 = muR c k ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_congr (g := fun ξ => muR c k ^ 2 * rung c k ξ ^ 2) fun ξ hξ => by
        simp only
        rw [psi_rung h ξ (by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hξ)]; ring,
      intervalIntegral.integral_const_mul, hnorm, mul_one]
  linarith

/-- **The exterior pairing**: `∫_{|ξ|>1} ψ ψ_1 = μh(0)(2π/c − μ²)`. -/
theorem integral_ext_psi_mul_psi_one (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) :
    ∫ ξ in extSet, psi c (rung c k) ξ * psi c (fun _ => 1) ξ
      = muR c k * rung c k 0 * (2 * π / c - muR c k ^ 2) := by
  have hg : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact continuousOn_rung h
  have hsplit := integral_add_compl (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))
    (integrable_psi_mul hc hg (continuousOn_const (c := (1 : ℝ))))
  rw [integral_psi_mul_psi_one hc hg, integral_Icc_psi_mul_psi_one h, integral_rung_eq h] at hsplit
  linarith

/-- **The centre bound**: `λ(1 − λ)h(0)² ≤ 2/π²` on every rung. -/
theorem rung_zero_sq_mul_le (hc : 0 < c) (h : ∃ χ, IsLevelIdx c k χ) :
    rung c k 0 ^ 2 * lamR c k * (1 - lamR c k) ≤ 2 / π ^ 2 := by
  have hg : ContinuousOn (rung c k) (uIcc (-1) 1) := by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact continuousOn_rung h
  set f := extSet.indicator (psi c (rung c k))
  set g := extSet.indicator (psi c (fun _ => 1))
  have hm : MeasurableSet extSet := measurableSet_Icc.compl
  have hf2 : (fun ξ => f ξ ^ 2) = extSet.indicator fun ξ => psi c (rung c k) ξ ^ 2 := by
    funext ξ; by_cases hξ : ξ ∈ extSet <;> simp [f, hξ]
  have hg2 : (fun ξ => g ξ ^ 2) = extSet.indicator fun ξ => psi c (fun _ => 1) ξ ^ 2 := by
    funext ξ; by_cases hξ : ξ ∈ extSet <;> simp [g, hξ]
  have hfg : (fun ξ => f ξ * g ξ) = extSet.indicator fun ξ => psi c (rung c k) ξ * psi c (fun _ => 1) ξ := by
    funext ξ; by_cases hξ : ξ ∈ extSet <;> simp [f, g, hξ]
  have hcs := Cvs.WeilForm.PoleTermCauchySchwarz.sq_integral_mul_le (f := f) (h := g)
    (by rw [hf2]; exact (Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc hg).indicator hm)
    (by rw [hg2]; exact (Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc (continuousOn_const (c := (1 : ℝ)))).indicator hm)
    (by rw [hfg]; exact (integrable_psi_mul hc hg (continuousOn_const (c := (1 : ℝ)))).indicator hm)
  rw [hf2, hg2, hfg, integral_indicator hm, integral_indicator hm, integral_indicator hm,
    integral_ext_psi_mul_psi_one hc h] at hcs
  have hE := integral_ext_psi_sq_le hc h
  have hP := integral_ext_psi_one_sq_le hc
  have hE0 : 0 ≤ ∫ ξ in extSet, psi c (rung c k) ξ ^ 2 := setIntegral_nonneg hm fun _ _ => sq_nonneg _
  have hP0 : 0 ≤ ∫ ξ in extSet, psi c (fun _ => 1) ξ ^ 2 := setIntegral_nonneg hm fun _ _ => sq_nonneg _
  have hlam := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq (k := k) hc
  have hle1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc h
  set μ := muR c k
  set D := 2 * π / c - μ ^ 2
  have hD : D = 2 * π / c * (1 - lamR c k) := by
    simp only [D]; rw [hlam]; field_simp
  have hD0 : 0 ≤ D := by rw [hD]; exact mul_nonneg (by positivity) (by linarith)
  have key : (μ * rung c k 0 * D) ^ 2 ≤ D * (8 / c ^ 2) :=
    hcs.trans (mul_le_mul hE hP hP0 hD0)
  rcases hD0.eq_or_lt with h0 | hpos
  · have : 1 - lamR c k = 0 := by
      rw [hD] at h0
      rcases mul_eq_zero.mp h0.symm with h1 | h1
      · exact absurd h1 (by positivity)
      · exact h1
    rw [this, mul_zero]; positivity
  · have k2 : μ ^ 2 * rung c k 0 ^ 2 * D ≤ 8 / c ^ 2 := by
      have : (μ * rung c k 0 * D) ^ 2 = D * (μ ^ 2 * rung c k 0 ^ 2 * D) := by ring
      rw [this] at key
      exact le_of_mul_le_mul_left key hpos
    rw [hlam]
    have e : rung c k 0 ^ 2 * (μ ^ 2 * (c / (2 * π))) * (1 - μ ^ 2 * (c / (2 * π)))
        = (μ ^ 2 * rung c k 0 ^ 2 * D) * (c ^ 2 / (4 * π ^ 2)) := by
      simp only [D]; field_simp; ring
    rw [e]
    calc (μ ^ 2 * rung c k 0 ^ 2 * D) * (c ^ 2 / (4 * π ^ 2)) ≤ 8 / c ^ 2 * (c ^ 2 / (4 * π ^ 2)) :=
          mul_le_mul_of_nonneg_right k2 (by positivity)
      _ = 2 / π ^ 2 := by field_simp; ring

end rung

/-! ### The `g0` part of the per-rung box -/

/-- **The profile at `0`**: for `λ_{4j}, λ_0 ≥ ½`, `G_j(0)² ≤ (16/π²)(1 − λ_{4j})`. -/
theorem profile_zero_sq_le {c : ℝ} {j : ℕ} (hc : 0 < c) (h : ∃ χ, IsLevelIdx c (2 * j) χ)
    (hlam : 1 / 2 ≤ lamR c (2 * j)) (hlam0 : 1 / 2 ≤ lamR c 0) :
    (rung c (2 * j) 0 - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 0) ^ 2 ≤ 16 / π ^ 2 * (1 - lamR c (2 * j)) := by
  have h0 := Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c
  have hμ0 := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h0 (⟨0, rfl⟩ : Even 0)
  have hμ := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc h (⟨j, by ring⟩ : Even (2 * j))
  have hanti := Cvs.Prolate.EvenRungsByIndex.lamR_anti hc h (Nat.zero_le (2 * j))
  have hl01 := Cvs.Prolate.EvenRungsByIndex.lamR_zero_le_one hc
  have e1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq (k := 2 * j) hc
  have e0 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq (k := 0) hc
  set r := muR c (2 * j) / muR c 0 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = lamR c (2 * j) / lamR c 0 := by
    rw [e1, e0, hr, div_pow]; field_simp
  have hr1 : r ≤ 1 := by
    have : r ^ 2 ≤ 1 := by rw [hr2, div_le_one (by linarith)]; exact hanti
    nlinarith
  have hgap : 1 - r ≤ 2 * (1 - lamR c (2 * j)) := by
    have h1 : 1 - r ≤ 1 - r ^ 2 := by nlinarith
    have h2 : 1 - r ^ 2 ≤ 2 * (1 - lamR c (2 * j)) := by
      rw [hr2]
      have k : (2 * lamR c (2 * j) - 1) * lamR c 0 ≤ lamR c (2 * j) := by nlinarith
      have := (le_div_iff₀ (by linarith : (0 : ℝ) < lamR c 0)).mpr k
      linarith
    linarith
  have hcb := rung_zero_sq_mul_le hc h
  have hle1 := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_le_one hc h
  have e : rung c (2 * j) 0 - Cvs.Approximant.DeepIndexSpineSpan.alpha c j * rung c 0 0 = (1 - r) * rung c (2 * j) 0 := by
    rw [Cvs.Prolate.Envelope.RungDuhamelRemainder.alpha_mul_rung_zero hc h]; ring
  rw [e, mul_pow]
  set ω := 1 - lamR c (2 * j)
  have hω : 0 ≤ ω := by simp only [ω]; linarith
  have hh : rung c (2 * j) 0 ^ 2 * ω ≤ 4 / π ^ 2 := by
    have : rung c (2 * j) 0 ^ 2 * ω * (1 / 2) ≤ rung c (2 * j) 0 ^ 2 * lamR c (2 * j) * ω := by
      have := mul_le_mul_of_nonneg_left hlam (mul_nonneg (sq_nonneg (rung c (2 * j) 0)) hω)
      linarith
    have h2 : 2 / π ^ 2 * 2 = 4 / π ^ 2 := by ring
    nlinarith
  have h1r : (1 - r) ^ 2 ≤ 4 * ω * ω := by nlinarith
  calc (1 - r) ^ 2 * rung c (2 * j) 0 ^ 2 ≤ 4 * ω * ω * rung c (2 * j) 0 ^ 2 :=
        mul_le_mul_of_nonneg_right h1r (sq_nonneg _)
    _ = 4 * ω * (rung c (2 * j) 0 ^ 2 * ω) := by ring
    _ ≤ 4 * ω * (4 / π ^ 2) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 16 / π ^ 2 * ω := by ring

/-- **`|g0 x e_j| ≤ (4/π)x⁻¹√(1 − λ_j)`** on every rung of the spine. -/
theorem abs_g0_single_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Cvs.Approximant.SpineSubspace.SF x) :
    |Cvs.StepA.Edge.TransplantAngleHighZeros.g0 x (Pi.single j 1)| ≤ 4 / π / x * √(1 - lamR (2 * π * x) (2 * (j : ℕ))) := by
  have hc : 0 < 2 * π * (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hjx := Cvs.Approximant.SpineSubspace.SF_lt x j j.2
  have h := Cvs.Prolate.RungFamilyRangePartners.exists_main hx ⟨j, Finset.mem_range.2 hjx⟩
  have hl := Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx hjx
  have hl0 : 1 / 2 ≤ lamR (2 * π * x) 0 := by
    simpa using Cvs.L2a.WindowChainInputsProlate.half_le_lamR hx (lt_of_le_of_lt (Nat.zero_le _) hjx)
  have hG := profile_zero_sq_le hc h hl hl0
  have hs : |rung (2 * π * x) (2 * (j : ℕ)) 0 - Cvs.Approximant.DeepIndexSpineSpan.alpha (2 * π * x) j * rung (2 * π * x) 0 0|
      ≤ 4 / π * √(1 - lamR (2 * π * x) (2 * (j : ℕ))) := by
    refine (Real.abs_le_sqrt hG).trans_eq ?_
    rw [Real.sqrt_mul (by positivity), show 16 / π ^ 2 = (4 / π) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  simp only [Cvs.StepA.Edge.TransplantAngleHighZeros.g0, Cvs.Route.Visibility.CaseFiniteFromWindowChain.spineG_single]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / x),
    show 4 / π / (x : ℝ) * √(1 - lamR (2 * π * x) (2 * (j : ℕ)))
      = 1 / x * (4 / π * √(1 - lamR (2 * π * x) (2 * (j : ℕ)))) by ring]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

end Cvs.Prolate.Envelope.RungCentreBound

end
