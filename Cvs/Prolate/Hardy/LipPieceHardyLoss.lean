import Mathlib
import Cvs.Prolate.Hardy.CarrierBoundaryValues
import Cvs.Prolate.Hardy.CarrierNegativeFreqRate
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.LipPhaseDecay
import Cvs.Upstream.HardyHalvesFourier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A lip piece of the carrier loses its wrong-sign Hardy half at rate `c^{−1/2}`

On `[α, β] ⊂ (½, 3/5]` the carrier is `H = Ae^{icφ}` (and `Ae^{−icφ(−x)}` on `[−β, −α]`); if `φ' ≤ −δ` there,
`‖P₊(1_{piece}H)‖² ≤ K²/(2πcδ)`, and if `φ' ≥ δ`, `‖(1 − P₊)(1_{piece}H)‖² ≤ K²/(2πcδ)`, with
`K = 2G₀ + (β − α)(G₁ + G₀φ''(α)/δ)` for `|A| ≤ G₀`, `|A'| ≤ G₁`.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform intervalIntegral
open Complex (I)

namespace Cvs.Prolate.Hardy.LipPieceHardyLoss
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C posProj wR)
open Cvs.Prolate.Hardy.CarrierBoundaryValues (sR)
open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (carH)
open Cvs.Prolate.Hardy.LipPhaseDecay (lipPhase lipD lipDD)

/-- `∫_{ξ>0}|F|² ≤ K²/(pq)` when `|F(ξ)| ≤ K/(p + qξ)` on `ξ > 0`. -/
theorem integral_Ioi_sq_le {F : ℝ → ℂ} {K p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hF : ∀ ξ, 0 < ξ → ‖F ξ‖ ≤ K / (p + q * ξ)) :
    ∫ ξ in Ioi (0 : ℝ), ‖F ξ‖ ^ 2 ≤ K ^ 2 * (1 / (p * q)) := by
  rw [← Cvs.Prolate.Hardy.LipPhaseDecay.integral_inv_sq_Ioi hp hq, ← MeasureTheory.integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    ((Cvs.Prolate.Hardy.LipPhaseDecay.integrableOn_inv_sq_Ioi hp hq).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hpq : 0 < p + q * ξ := by nlinarith [hξ.out]
  calc ‖F ξ‖ ^ 2 ≤ (K / (p + q * ξ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hF ξ hξ) 2
    _ = K ^ 2 * (1 / (p + q * ξ) ^ 2) := by field_simp

theorem carH_of_ge (c : ℝ) (A : ℂ → ℂ) {x : ℝ} (hx : 1 / 2 ≤ x) :
    carH c A x = A x * Complex.exp (I * ((c * lipPhase x : ℝ) : ℂ)) := by
  have hw := Cvs.Prolate.Hardy.CarrierBoundaryValues.wR_of_half_le_abs (c / 2) (x := x) (by rw [abs_of_nonneg (by linarith)]; exact hx)
  have hs : sR x = √(x ^ 2 - 1 / 4) := by rw [Cvs.Prolate.Hardy.CarrierBoundaryValues.sR, if_pos (by linarith)]
  unfold carH
  rw [hw, hs, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
  congr 2
  unfold lipPhase
  push_cast; ring

theorem carH_of_le (c : ℝ) (A : ℂ → ℂ) {y : ℝ} (hy : 1 / 2 ≤ y) :
    carH c A (-y) = A ↑(-y) * Complex.exp (I * ((-(c * lipPhase y) : ℝ) : ℂ)) := by
  have hw := Cvs.Prolate.Hardy.CarrierBoundaryValues.wR_of_half_le_abs (c / 2) (x := -y) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hy)
  have hs : sR (-y) = -√(y ^ 2 - 1 / 4) := by rw [Cvs.Prolate.Hardy.CarrierBoundaryValues.sR_neg, Cvs.Prolate.Hardy.CarrierBoundaryValues.sR, if_pos (by linarith)]
  unfold carH
  rw [hw, hs, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
  congr 2
  unfold lipPhase
  push_cast; ring

/-- The right piece `𝓕(1_{(α,β]}H)(ξ) = ∫_α^β A e^{i(cφ − 2πξx)}`. -/
theorem fourier_right (c ξ : ℝ) (A : ℂ → ℂ) {α β : ℝ} (hα : 1 / 2 ≤ α) (hαβ : α ≤ β) :
    𝓕 ((Ioc α β).indicator (carH c A)) ξ =
      ∫ x in α..β, A x * Complex.exp (I * (((1 : ℝ) * (c * lipPhase x - 2 * π * ξ * x) : ℝ) : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le hαβ,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  congr 1
  ext x
  by_cases hx : x ∈ Ioc α β
  · rw [indicator_of_mem hx, indicator_of_mem hx, carH_of_ge c A (by linarith [hx.1]), smul_eq_mul,
      mul_left_comm, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]

/-- The left piece `𝓕(1_{(−β,−α]}H)(ξ) = ∫_α^β A(−y) e^{−i(cφ(y) − 2πξy)}`. -/
theorem fourier_left (c ξ : ℝ) (A : ℂ → ℂ) {α β : ℝ} (hα : 1 / 2 ≤ α) (hαβ : α ≤ β) :
    𝓕 ((Ioc (-β) (-α)).indicator (carH c A)) ξ =
      ∫ y in α..β, A ↑(-y) * Complex.exp (I * (((-1 : ℝ) * (c * lipPhase y - 2 * π * ξ * y) : ℝ) : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have e : ∫ v : ℝ, Complex.exp (↑(-2 * π * v * ξ) * I) • (Ioc (-β) (-α)).indicator (carH c A) v =
      ∫ v in -β..-α, Complex.exp (↑(-2 * π * v * ξ) * I) • carH c A v := by
    rw [intervalIntegral.integral_of_le (by linarith), ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1
    ext x
    by_cases hx : x ∈ Ioc (-β) (-α)
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
  rw [e, ← intervalIntegral.integral_comp_neg]
  refine integral_congr fun y hy => ?_
  rw [uIcc_of_le hαβ] at hy
  rw [carH_of_le c A (by linarith [hy.1]), smul_eq_mul, mul_left_comm, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem hasDerivAt_real (A : ℂ → ℂ) {x : ℝ} (h : DifferentiableAt ℂ A x) :
    HasDerivAt (fun x : ℝ => A x) (deriv A x) x := h.hasDerivAt.comp_ofReal

theorem hasDerivAt_real_neg (A : ℂ → ℂ) {y : ℝ} (h : DifferentiableAt ℂ A ↑(-y)) :
    HasDerivAt (fun y : ℝ => A ↑(-y)) (-deriv A ↑(-y)) y := by
  have h1 : HasDerivAt (fun x : ℝ => A x) (deriv A ↑(-y)) (-y) := hasDerivAt_real A h
  have h2 := h1.scomp y (hasDerivAt_neg y)
  have e : ((fun x : ℝ => A ↑x) ∘ Neg.neg) = fun y : ℝ => A ↑(-y) := rfl
  rw [e] at h2
  simpa using h2

/-- The amplitude hypotheses: holomorphic on the unit disc, with bounds on `[−3/5, 3/5]`. -/
structure AmpBound (A : ℂ → ℂ) (G₀ G₁ : ℝ) : Prop where
  diff : DifferentiableOn ℂ A (Metric.ball 0 1)
  bound : ∀ x ∈ Icc (-(3 / 5) : ℝ) (3 / 5), ‖A x‖ ≤ G₀
  dbound : ∀ x ∈ Icc (-(3 / 5) : ℝ) (3 / 5), ‖deriv A x‖ ≤ G₁

theorem AmpBound.differentiableAt {A : ℂ → ℂ} {G₀ G₁ : ℝ} (h : AmpBound A G₀ G₁) {x : ℝ}
    (hx : x ∈ Icc (-(3 / 5) : ℝ) (3 / 5)) : DifferentiableAt ℂ A x := by
  refine h.diff.differentiableAt (Metric.isOpen_ball.mem_nhds ?_)
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact lt_of_le_of_lt (abs_le.2 hx) (by norm_num)

theorem AmpBound.continuousOn_deriv {A : ℂ → ℂ} {G₀ G₁ : ℝ} (h : AmpBound A G₀ G₁) :
    ContinuousOn (fun x : ℝ => deriv A x) (Icc (-(3 / 5) : ℝ) (3 / 5)) := by
  have hc := (h.diff.contDiffOn (n := 1) Metric.isOpen_ball).continuousOn_deriv_of_isOpen Metric.isOpen_ball
    (by norm_num)
  refine hc.comp Complex.continuous_ofReal.continuousOn fun x hx => ?_
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact lt_of_le_of_lt (abs_le.2 hx) (by norm_num)

/-- The piece constant `K = 2G₀ + (β − α)(G₁ + G₀φ''(α)/δ)`. -/
def pieceK (G₀ G₁ α β δ : ℝ) : ℝ := 2 * G₀ + (β - α) * (G₁ + G₀ * lipDD α / δ)

theorem mem_Icc_of_piece {α β x : ℝ} (hα : 1 / 2 < α) (hβ : β ≤ 3 / 5) (hx : x ∈ Icc α β) :
    x ∈ Icc (-(3 / 5) : ℝ) (3 / 5) := ⟨by linarith [hx.1], hx.2.trans hβ⟩

theorem neg_mem_Icc_of_piece {α β x : ℝ} (hα : 1 / 2 < α) (hβ : β ≤ 3 / 5) (hx : x ∈ Icc α β) :
    -x ∈ Icc (-(3 / 5) : ℝ) (3 / 5) := ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- **The piece Fourier bound** for both lips and both signs, with `κ ≤ |cφ' − 2πξ|`, `cδ ≤ κ`. -/
theorem norm_fourier_piece_le {c δ α β ξ κ G₀ G₁ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hα : 1 / 2 < α)
    (hαβ : α ≤ β) (hβ : β ≤ 3 / 5) (hκ : c * δ ≤ κ) (hκx : ∀ x ∈ Icc α β, κ ≤ |c * lipD x - 2 * π * ξ|)
    {A : ℂ → ℂ} (hA : AmpBound A G₀ G₁) :
    ‖𝓕 ((Ioc α β).indicator (carH c A)) ξ‖ ≤ pieceK G₀ G₁ α β δ / κ ∧
      ‖𝓕 ((Ioc (-β) (-α)).indicator (carH c A)) ξ‖ ≤ pieceK G₀ G₁ α β δ / κ := by
  constructor
  · rw [fourier_right c ξ A hα.le hαβ]
    exact Cvs.Prolate.Hardy.LipPhaseDecay.norm_lip_le (by norm_num) hα hαβ hδ hc hκ hκx
      (fun x hx => hasDerivAt_real A (hA.differentiableAt (mem_Icc_of_piece hα hβ hx)))
      (hA.continuousOn_deriv.mono fun x hx => mem_Icc_of_piece hα hβ hx)
      (fun x hx => hA.bound x (mem_Icc_of_piece hα hβ hx)) (fun x hx => hA.dbound x (mem_Icc_of_piece hα hβ hx))
  · rw [fourier_left c ξ A hα.le hαβ]
    refine Cvs.Prolate.Hardy.LipPhaseDecay.norm_lip_le (by norm_num) hα hαβ hδ hc hκ hκx
      (fun x hx => hasDerivAt_real_neg A (by
        have := hA.differentiableAt (neg_mem_Icc_of_piece hα hβ hx); exact_mod_cast this))
      ?_ (fun x hx => by have := hA.bound _ (neg_mem_Icc_of_piece hα hβ hx); exact_mod_cast this)
      (fun x hx => by rw [norm_neg]; have := hA.dbound _ (neg_mem_Icc_of_piece hα hβ hx); exact_mod_cast this)
    have := (hA.continuousOn_deriv.comp continuous_neg.continuousOn
      fun x hx => neg_mem_Icc_of_piece hα hβ hx).neg
    refine this.congr fun x _ => ?_
    simp [Function.comp]

theorem continuousOn_carH_piece (c : ℝ) {A : ℂ → ℂ} {G₀ G₁ : ℝ} (hA : AmpBound A G₀ G₁) :
    ContinuousOn (carH c A) (Icc (-(3 / 5)) (3 / 5)) :=
  Cvs.Prolate.Hardy.CarrierNegativeFreqRate.continuousOn_carH c fun z hz => hA.diff.differentiableAt (Metric.isOpen_ball.mem_nhds (by
    rw [Metric.mem_ball, dist_zero_right]; linarith))

theorem integrable_memLp_piece (c : ℝ) {A : ℂ → ℂ} {G₀ G₁ : ℝ} (hA : AmpBound A G₀ G₁) {a b : ℝ}
    (ha : -(3 / 5) ≤ a) (hb : b ≤ 3 / 5) :
    Integrable ((Ioc a b).indicator (carH c A)) ∧ MemLp ((Ioc a b).indicator (carH c A)) 2 volume :=
  Cvs.Prolate.Hardy.CarrierNegativeFreqRate.integrable_memLp_indicator ((continuousOn_carH_piece c hA).mono (Icc_subset_Icc ha hb))

/-- **Negative phase**: `φ' ≤ −δ` on `[α, β]` gives `‖P₊(1_{piece}H)‖² ≤ K²/(2πcδ)` on both lips. -/
theorem norm_posProj_piece_sq_le {c δ α β G₀ G₁ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hα : 1 / 2 < α)
    (hαβ : α ≤ β) (hβ : β ≤ 3 / 5) (hD : ∀ x ∈ Icc α β, lipD x ≤ -δ) {A : ℂ → ℂ} (hA : AmpBound A G₀ G₁)
    {s : Set ℝ} (hs : s = Ioc α β ∨ s = Ioc (-β) (-α)) (h2 : MemLp (s.indicator (carH c A)) 2 volume) :
    ‖posProj (h2.toLp _)‖ ^ 2 ≤ pieceK G₀ G₁ α β δ ^ 2 * (1 / (c * δ * (2 * π))) := by
  have hint : Integrable (s.indicator (carH c A)) := by
    rcases hs with rfl | rfl
    · exact (integrable_memLp_piece c hA (by linarith) hβ).1
    · exact (integrable_memLp_piece c hA (by linarith) (by linarith)).1
  rw [Cvs.Upstream.HardyHalvesFourier.norm_posProj_toLp_sq hint h2, integral_Ici_eq_integral_Ioi]
  refine integral_Ioi_sq_le (mul_pos hc hδ) (by positivity) fun ξ hξ => ?_
  have hκx : ∀ x ∈ Icc α β, c * δ + 2 * π * ξ ≤ |c * lipD x - 2 * π * ξ| := by
    intro x hx
    have := hD x hx
    rw [abs_of_neg (by nlinarith [Real.pi_pos])]
    nlinarith [Real.pi_pos]
  have hb := norm_fourier_piece_le hc hδ hα hαβ hβ (by nlinarith [Real.pi_pos]) hκx hA
  rcases hs with rfl | rfl
  · exact hb.1
  · exact hb.2

/-- **Positive phase**: `φ' ≥ δ` on `[α, β]` gives `‖(1 − P₊)(1_{piece}H)‖² ≤ K²/(2πcδ)` on both lips. -/
theorem norm_sub_posProj_piece_sq_le {c δ α β G₀ G₁ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hα : 1 / 2 < α)
    (hαβ : α ≤ β) (hβ : β ≤ 3 / 5) (hD : ∀ x ∈ Icc α β, δ ≤ lipD x) {A : ℂ → ℂ} (hA : AmpBound A G₀ G₁)
    {s : Set ℝ} (hs : s = Ioc α β ∨ s = Ioc (-β) (-α)) (h2 : MemLp (s.indicator (carH c A)) 2 volume) :
    ‖h2.toLp _ - posProj (h2.toLp _)‖ ^ 2 ≤ pieceK G₀ G₁ α β δ ^ 2 * (1 / (c * δ * (2 * π))) := by
  have hint : Integrable (s.indicator (carH c A)) := by
    rcases hs with rfl | rfl
    · exact (integrable_memLp_piece c hA (by linarith) hβ).1
    · exact (integrable_memLp_piece c hA (by linarith) (by linarith)).1
  rw [Cvs.Upstream.HardyHalvesFourier.norm_sub_posProj_toLp_sq hint h2,
    Cvs.Prolate.Hardy.CarrierNegativeFreqRate.integral_Iio_eq_Ioi_neg (fun ξ => ‖𝓕 (s.indicator (carH c A)) ξ‖ ^ 2)]
  refine integral_Ioi_sq_le (F := fun ξ => 𝓕 (s.indicator (carH c A)) (-ξ)) (mul_pos hc hδ) (by positivity)
    fun ξ hξ => ?_
  have hκx : ∀ x ∈ Icc α β, c * δ + 2 * π * ξ ≤ |c * lipD x - 2 * π * (-ξ)| := by
    intro x hx
    have := hD x hx
    rw [abs_of_pos (by nlinarith [Real.pi_pos])]
    nlinarith [Real.pi_pos]
  have hb := norm_fourier_piece_le hc hδ hα hαβ hβ (by nlinarith [Real.pi_pos]) hκx hA
  rcases hs with rfl | rfl
  · exact hb.1
  · exact hb.2

end Cvs.Prolate.Hardy.LipPieceHardyLoss

end
