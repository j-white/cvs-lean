import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CarrierNegativeFreqRate
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.ColumnAmplitudeBound
import Cvs.Prolate.Hardy.ColumnTwoCarrierWave
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.ExteriorSincColumns
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.LipPhaseDecay
import Cvs.Prolate.Hardy.LipPieceHardyLoss
import Cvs.Prolate.Hardy.LipSymmetricPieces

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `‖J_c(Qe_u) − V_u‖ ≤ 2g_u E_c` with `g_u = 1/(π(u − 3/5))` and an explicit `E_c`

For `½ < α ≤ x₀ < ℓ = 1/√3 < x₁ ≤ 3/5`, `φ' ≤ φ'(x₀) < 0` on `[α, x₀]` and `φ' ≥ φ'(x₁) > 0` on `[x₁, 3/5]`, so the
five Hardy errors give `E_c = O(c^{−1/2}) + √(2(α − ½)) + √(2(ℓ − x₀)) + √(2(x₁ − ℓ))` uniformly in `u > 1`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.Hardy.ColumnWaveErrorBound
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R colA)
open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C posProj hardyJ)
open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (carH)
open Cvs.Prolate.Hardy.LipPhaseDecay (lipD lipDD)
open Cvs.Prolate.Hardy.LipSymmetricPieces (symS)
open Cvs.Prolate.Hardy.ColumnTwoCarrierWave (toL2 piece kL2 waveV)
open Cvs.Prolate.Hardy.ColumnAmplitudeBound (gU)

/-- The turning point `ℓ = 1/√3` of the lip phase. -/
def ell : ℝ := 1 / √3

theorem lipD_neg {x : ℝ} (hx : 1 / 2 < x) (hxl : x < ell) : lipD x < 0 := by
  have h3 : x ^ 2 < 1 / 3 := by
    have hs : 0 < √3 := by positivity
    have : x * √3 < 1 := by rw [ell, lt_div_iff₀ hs] at hxl; exact hxl
    have h33 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith
  have := (Cvs.Prolate.Hardy.ExteriorSincColumns.lip_turn_half hx).2 h3
  unfold lipD
  rw [show x / (2 * √(x ^ 2 - 1 / 4)) = 1 / 2 * x / √(x ^ 2 - (1 / 2) ^ 2) by norm_num; ring]
  linarith

theorem half_lt_ell : (1 / 2 : ℝ) < ell := by
  unfold ell
  rw [lt_div_iff₀ (by positivity)]
  have : √3 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] ]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem lipD_pos {x : ℝ} (hxl : ell < x) : 0 < lipD x := by
  have hl := half_lt_ell
  have hx : 1 / 2 < x := hl.trans hxl
  have h3 : ¬ x ^ 2 < 1 / 3 := by
    have hs : 0 < √3 := by positivity
    have : 1 < x * √3 := by rw [ell, div_lt_iff₀ hs] at hxl; exact hxl
    have h33 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith
  have := mt (Cvs.Prolate.Hardy.ExteriorSincColumns.lip_turn_half hx).1 h3
  unfold lipD
  rw [show x / (2 * √(x ^ 2 - 1 / 4)) = 1 / 2 * x / √(x ^ 2 - (1 / 2) ^ 2) by norm_num; ring]
  push Not at this
  have hne : 1 / 2 * x / √(x ^ 2 - (1 / 2) ^ 2) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq (by have := Cvs.Prolate.Hardy.LipPhaseDecay.sqrt_pos_of_half_lt hx; norm_num at this ⊢; positivity)] at h
    have h2 := congrArg (· ^ 2) h
    rw [Real.sq_sqrt (by nlinarith)] at h2
    have h33 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have : x * √3 > 1 := by rw [ell, div_lt_iff₀ (by positivity)] at hxl; exact hxl
    nlinarith
  linarith [lt_of_le_of_ne this hne]

theorem norm_le_of_sq_le {E : Type*} [NormedAddCommGroup E] {v : E} {X Y : ℝ} (hX : 0 ≤ X)
    (h : ‖v‖ ^ 2 ≤ X ^ 2 * Y) : ‖v‖ ≤ X * √Y := by
  have hY : 0 ≤ X ^ 2 * Y := (sq_nonneg _).trans h
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_sq hX, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

/-- The piece factor `κ(a, b, δ) = 2 + (b − a)(5/2 + φ''(a)/δ)`. -/
def kap (a b δ : ℝ) : ℝ := 2 + (b - a) * (5 / 2 + lipDD a / δ)

theorem pieceK_eq (g a b δ : ℝ) : Cvs.Prolate.Hardy.LipPieceHardyLoss.pieceK g (5 / 2 * g) a b δ = g * kap a b δ := by
  unfold Cvs.Prolate.Hardy.LipPieceHardyLoss.pieceK kap; ring

theorem kap_nonneg {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) : 0 ≤ kap a b δ := by
  unfold kap
  have := Cvs.Prolate.Hardy.LipPhaseDecay.lipDD_nonneg (x := a)
  have : 0 ≤ (b - a) * (5 / 2 + lipDD a / δ) := mul_nonneg (by linarith) (by positivity)
  linarith

/-- The column error constant `E_c`. -/
def errC (c α x₀ x₁ : ℝ) : ℝ :=
  3 / 5 * π * √(1 / (c * (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))) +
    2 * (kap x₁ (3 / 5) (lipD x₁) * √(1 / (c * lipD x₁ * (2 * π)))) +
    2 * (kap α x₀ (-lipD x₀) * √(1 / (c * (-lipD x₀) * (2 * π)))) +
    (√(2 * (α - 1 / 2)) + √(2 * (ell - x₀)) + √(2 * (x₁ - ell)))

theorem piece_eq_add (c : ℝ) {u : ℝ} (hu : 1 < u) {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : b ≤ 3 / 5) :
    piece c u a b = toL2 ((Ioc a b).indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))) +
      toL2 ((Ioc (-b) (-a)).indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))) := by
  have hA := Cvs.Prolate.Hardy.ColumnAmplitudeBound.ampBound c hu
  have m1 := (Cvs.Prolate.Hardy.LipPieceHardyLoss.integrable_memLp_piece c hA (a := a) (b := b) (by linarith) hb).2
  have m2 := (Cvs.Prolate.Hardy.LipPieceHardyLoss.integrable_memLp_piece c hA (a := -b) (b := -a) (by linarith) (by linarith)).2
  refine Lp.ext ?_
  filter_upwards [Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 (Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_symS c hu (a := a) (b := b) (by linarith) hb),
    Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 m1, Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 m2, Lp.coeFn_add (toL2 ((Ioc a b).indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))))
      (toL2 ((Ioc (-b) (-a)).indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))))] with x h1 h2 h3 h4
  simp only [piece] at h1 ⊢
  rw [h1, h4, Pi.add_apply, h2, h3, Cvs.Prolate.Hardy.LipSymmetricPieces.indicator_symS (by linarith)]
  rfl

theorem norm_sub_posProj_add_le (a b : L2C) :
    ‖(a + b) - posProj (a + b)‖ ≤ ‖a - posProj a‖ + ‖b - posProj b‖ := by
  rw [map_add, show a + b - (posProj a + posProj b) = (a - posProj a) + (b - posProj b) by abel]
  exact norm_add_le _ _

theorem norm_posProj_add_le (a b : L2C) : ‖posProj (a + b)‖ ≤ ‖posProj a‖ + ‖posProj b‖ := by
  rw [map_add]; exact norm_add_le _ _

/-- **The uniform column bound** `‖J_c(Qe_u) − V_u‖ ≤ 2g_u E_c`. -/
theorem norm_col_err_le {c u α x₀ x₁ : ℝ} (hc : 0 < c) (hu : 1 < u) (hα : 1 / 2 < α) (h1 : α ≤ x₀)
    (h2 : x₀ < ell) (h3 : ell < x₁) (h4 : x₁ ≤ 3 / 5) :
    ‖hardyJ c (colA c u) - waveV c u ell‖ ≤ 2 * (gU u * errC c α x₀ x₁) := by
  have hA := Cvs.Prolate.Hardy.ColumnAmplitudeBound.ampBound c hu
  have hg := (Cvs.Prolate.Hardy.ColumnAmplitudeBound.gU_pos hu).le
  have hδ₂ : 0 < -lipD x₀ := by linarith [lipD_neg (hα.trans_le h1) h2]
  have hδ₁ : 0 < lipD x₁ := lipD_pos h3
  have hD₂ : ∀ x ∈ Icc α x₀, lipD x ≤ -(-lipD x₀) := fun x hx => by
    rw [neg_neg]; exact Cvs.Prolate.Hardy.LipPhaseDecay.lipD_le (hα.trans_le hx.1) hx.2
  have hl : (1 / 2 : ℝ) < ell := half_lt_ell
  have hD₁ : ∀ x ∈ Icc x₁ (3 / 5), lipD x₁ ≤ lipD x := fun x hx => Cvs.Prolate.Hardy.LipPhaseDecay.lipD_le (hl.trans h3) hx.1
  have hx₁ : 1 / 2 < x₁ := by linarith
  -- the five terms
  have tk : ‖kL2 c u - posProj (kL2 c u)‖ ≤
      gU u * (3 / 5 * π) * √(1 / (c * (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))) := by
    have h := Cvs.Prolate.Hardy.CarrierNegativeFreqRate.norm_sub_posProj_kC_sq_le hc (fun z hz => Cvs.Prolate.Hardy.ColumnTwoCarrierWave.differentiableAt_amp c hu hz)
      (fun θ _ => Cvs.Prolate.Hardy.ColumnAmplitudeBound.norm_amp_arc_le c hu θ) (Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_kC c hu)
    rw [show kL2 c u = (Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_kC c hu).toLp _ from Cvs.Prolate.Hardy.ColumnTwoCarrierWave.toL2_eq _]
    have := norm_le_of_sq_le (by positivity) (h.trans_eq (by ring) :
      _ ≤ (gU u * (3 / 5 * π)) ^ 2 * (1 / (c * (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))))
    exact this
  have tpiece : ∀ {a b δ : ℝ} {s : Set ℝ}, 1 / 2 < a → a ≤ b → b ≤ 3 / 5 → 0 < δ →
      (s = Ioc a b ∨ s = Ioc (-b) (-a)) → (h2 : MemLp (s.indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))) 2 volume) →
      ((∀ x ∈ Icc a b, lipD x ≤ -δ) → ‖posProj (toL2 (s.indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))))‖ ≤
        gU u * kap a b δ * √(1 / (c * δ * (2 * π)))) ∧
      ((∀ x ∈ Icc a b, δ ≤ lipD x) →
        ‖toL2 (s.indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))) - posProj (toL2 (s.indicator (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u))))‖ ≤
        gU u * kap a b δ * √(1 / (c * δ * (2 * π)))) := by
    intro a b δ s ha hab hb hδ hs hm
    rw [Cvs.Prolate.Hardy.ColumnTwoCarrierWave.toL2_eq hm]
    have hk : 0 ≤ gU u * kap a b δ := mul_nonneg hg (kap_nonneg hab hδ)
    refine ⟨fun hD => ?_, fun hD => ?_⟩
    · have h := Cvs.Prolate.Hardy.LipPieceHardyLoss.norm_posProj_piece_sq_le hc hδ ha hab hb hD hA hs hm
      rw [pieceK_eq] at h
      exact norm_le_of_sq_le hk h
    · have h := Cvs.Prolate.Hardy.LipPieceHardyLoss.norm_sub_posProj_piece_sq_le hc hδ ha hab hb hD hA hs hm
      rw [pieceK_eq] at h
      exact norm_le_of_sq_le hk h
  have mR := fun {a b : ℝ} (ha : 1 / 2 < a) (hb : b ≤ 3 / 5) =>
    (Cvs.Prolate.Hardy.LipPieceHardyLoss.integrable_memLp_piece c hA (a := a) (b := b) (by linarith) hb).2
  have mL := fun {a b : ℝ} (ha : 1 / 2 < a) (hb : b ≤ 3 / 5) =>
    (Cvs.Prolate.Hardy.LipPieceHardyLoss.integrable_memLp_piece c hA (a := -b) (b := -a) (by linarith) (by linarith)).2
  have tm₁ : ‖piece c u x₁ (3 / 5) - posProj (piece c u x₁ (3 / 5))‖ ≤
      2 * (gU u * kap x₁ (3 / 5) (lipD x₁) * √(1 / (c * lipD x₁ * (2 * π)))) := by
    rw [piece_eq_add c hu hx₁.le le_rfl]
    refine (norm_sub_posProj_add_le _ _).trans ?_
    have e1 := (tpiece hx₁ h4 le_rfl hδ₁ (Or.inl rfl) (mR hx₁ le_rfl)).2 hD₁
    have e2 := (tpiece hx₁ h4 le_rfl hδ₁ (Or.inr rfl) (mL hx₁ le_rfl)).2 hD₁
    linarith
  have tm₂ : ‖posProj (piece c u α x₀)‖ ≤
      2 * (gU u * kap α x₀ (-lipD x₀) * √(1 / (c * (-lipD x₀) * (2 * π)))) := by
    have hx₀ : x₀ ≤ 3 / 5 := by linarith
    rw [piece_eq_add c hu hα.le hx₀]
    refine (norm_posProj_add_le _ _).trans ?_
    have e1 := (tpiece hα h1 hx₀ hδ₂ (Or.inl rfl) (mR hα hx₀)).1 hD₂
    have e2 := (tpiece hα h1 hx₀ hδ₂ (Or.inr rfl) (mL hα hx₀)).1 hD₂
    linarith
  have trem : ∀ {a b : ℝ}, 1 / 2 ≤ a → a ≤ b → b ≤ 3 / 5 → ‖piece c u a b‖ ≤ gU u * √(2 * (b - a)) := by
    intro a b ha hab hb
    have hm := Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_symS c hu (a := a) (b := b) (by linarith) hb
    have h := Cvs.Prolate.Hardy.LipSymmetricPieces.norm_sq_symS_le ha hab (fun x hx => hA.bound x (by
      rcases hx with hx | hx
      · exact ⟨by linarith [hx.1], hx.2.trans hb⟩
      · exact ⟨hx.1.le.trans' (by linarith), by linarith [hx.2]⟩)) hm
    simp only [piece]
    rw [Cvs.Prolate.Hardy.ColumnTwoCarrierWave.toL2_eq hm]
    exact norm_le_of_sq_le hg h
  have hJ := Cvs.Prolate.Hardy.ColumnTwoCarrierWave.norm_hardyJ_sub_waveV_le c hc.le hu hα.le h1 h2.le h3.le h4
  have r1 := trem (le_refl (1 / 2 : ℝ)) hα.le (by linarith)
  have r2 := trem (hα.le.trans h1) h2.le (by linarith)
  have r3 := trem hl.le h3.le h4
  refine hJ.trans ?_
  unfold errC
  have hsum : ‖kL2 c u - posProj (kL2 c u)‖ + ‖piece c u x₁ (3 / 5) - posProj (piece c u x₁ (3 / 5))‖ +
      ‖posProj (piece c u α x₀)‖ + (‖piece c u (1 / 2) α‖ + ‖piece c u x₀ ell‖) + ‖piece c u ell x₁‖ ≤
      gU u * (3 / 5 * π * √(1 / (c * (√11 / 10 - 3 / 10) * (2 * π * (√11 / 10)))) +
        2 * (kap x₁ (3 / 5) (lipD x₁) * √(1 / (c * lipD x₁ * (2 * π)))) +
        2 * (kap α x₀ (-lipD x₀) * √(1 / (c * (-lipD x₀) * (2 * π)))) +
        (√(2 * (α - 1 / 2)) + √(2 * (ell - x₀)) + √(2 * (x₁ - ell)))) := by
    nlinarith [tk, tm₁, tm₂, r1, r2, r3]
  linarith

end Cvs.Prolate.Hardy.ColumnWaveErrorBound

end
