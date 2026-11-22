import Mathlib
import Cvs.Prolate.LadderRatioWkbMomenta
import Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint
import Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent
import Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ladder ratio in closed form

Past `a ≥ 2√χ_b/c`, `√(pq) ≤ csr` and `γ ≤ 2/(3s)`, so `U ≤ W = csr + 1/s` with `W² − pq ≤ 2c + 1/a² + χ`;
Cvs.Prolate.LadderRatioWkbMomenta then gives `log(g_b(1)g_a(a)/(g_a(1)g_b(a))) ≥ ((χ_b − χ_a)/(2c)) log((2c + K₀)/(2ca + K₀))`,
`K₀ = 2/a + κ`, `κ = 2 + √(2X)`, `X = 2c + 1/a² + χ_b`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.LadderRatioClosedForm

open Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier (pp qq Bb gam)
open Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent (U)
open Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint (sm)

/-- `√(pq) ≤ c s r` on `[0, 1]`. -/
theorem Bb_le {c χ s : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Bb c χ s ≤ c * s * √(1 - s ^ 2) := by
  unfold Bb pp qq
  have hp : 0 ≤ 1 - s ^ 2 := by nlinarith
  rw [show c * s * √(1 - s ^ 2) = √((c * s) ^ 2 * (1 - s ^ 2)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- `γ ≤ 2/(3s)` once `4χ ≤ c²s²`. -/
theorem gam_le {c χ s : ℝ} (hc : 0 < c) (hχ : 0 < χ) (hs0 : 0 < s) (hs1 : s < 1) (h4 : 4 * χ ≤ c ^ 2 * s ^ 2) :
    gam c χ s ≤ 2 / (3 * s) := by
  unfold gam pp qq
  have hq : 0 < c ^ 2 * s ^ 2 - χ := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hc hc, sq_nonneg s, mul_pos hs0 hχ]

/-- **The momenta bound** `U ≤ csr + 1/s` on `[a, 1]`, `a ≥ 2√χ/c`, `a ≤ 1/2`, `3χ ≤ c²`, `g > 0` there. -/
theorem U_le_W {g g₁ g₂ : ℝ → ℝ} {c χ a : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 < χ) (h3 : 3 * χ ≤ c ^ 2) (ha : 2 * √χ / c ≤ a) (ha2 : a ≤ 1 / 2)
    (hpos : ∀ s ∈ Icc a 1, 0 < g s) :
    ∀ s ∈ Icc a 1, U g g₁ s ≤ c * s * √(1 - s ^ 2) + 1 / s := by
  have hχc : χ < c ^ 2 := by linarith
  have hs00 : 0 < √χ / c := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hsmh : 1 / 2 ≤ sm c χ := by
    have h := Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.sm_sq hc hχ
    have : (1 / 2 : ℝ) ^ 2 ≤ sm c χ ^ 2 := by
      rw [h, le_div_iff₀ (by positivity)]; nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) (Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.sm_pos hc hχ).le two_ne_zero).1 this
  have hs₁ : √χ / c < a := by
    have : √χ / c < 2 * √χ / c := by rw [mul_div_assoc]; linarith
    linarith
  have hsq : ∀ s, a ≤ s → 4 * χ ≤ c ^ 2 * s ^ 2 := fun s hs => by
    have h1 : 2 * √χ ≤ c * s := by rw [div_le_iff₀ hc] at ha; nlinarith
    have := Real.sq_sqrt hχ.le
    nlinarith [Real.sqrt_nonneg χ]
  intro s hs
  have hs0 : 0 < s := ha0.trans_le hs.1
  rcases le_or_gt s (sm c χ) with hsm | hsm
  · have hW := Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.U_le_W hg hg₁ hang hc hχ h3 hs₁ (ha2.trans hsmh)
      (fun t ht => hpos t ⟨ht.1, ht.2⟩) s ⟨hs.1, hsm⟩
    have hs1 : s < 1 := lt_of_le_of_lt hsm (Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.sm_lt_one hc hχ hχc)
    have h1 := Bb_le hc hχ.le hs0.le hs.2
    have h2 := gam_le hc hχ hs0 hs1 (hsq s hs.1)
    have h3' : 2 / (3 * s) ≤ 1 / s := by rw [div_le_div_iff₀ (by positivity) hs0]; nlinarith
    linarith
  · have hW := Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint.U_le_Bb hg hg₁ hang hc hχ hχc
      (fun t ht => hpos t ⟨(ha2.trans hsmh).trans ht.1 |>.trans' le_rfl |> fun h => by linarith [ht.1, hsmh, ha2], ht.2⟩)
      s ⟨hsm.le, hs.2⟩
    have h1 := Bb_le hc hχ.le hs0.le hs.2
    have : 0 < 1 / s := by positivity
    linarith

/-- `W² − pq = 2cr + 1/s² + r²χ ≤ 2c + 1/a² + χ` for `W = csr + 1/s`, `a ≤ s ≤ 1`. -/
theorem W_sq_sub_le {c χ a s : ℝ} (hc : 0 < c) (hχ : 0 ≤ χ) (ha : 0 < a) (hs : a ≤ s) (hs1 : s ≤ 1) :
    (c * s * √(1 - s ^ 2) + 1 / s) ^ 2 - (1 - s ^ 2) * (c ^ 2 * s ^ 2 - χ) ≤ 2 * c + 1 / a ^ 2 + χ := by
  have hs0 : 0 < s := ha.trans_le hs
  have hp : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hr2 : √(1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hp
  have hr1 : √(1 - s ^ 2) ≤ 1 := by rw [Real.sqrt_le_one]; nlinarith [sq_nonneg s]
  have hr0 := Real.sqrt_nonneg (1 - s ^ 2)
  have e : (c * s * √(1 - s ^ 2) + 1 / s) ^ 2 - (1 - s ^ 2) * (c ^ 2 * s ^ 2 - χ)
      = 2 * c * √(1 - s ^ 2) + 1 / s ^ 2 + (1 - s ^ 2) * χ := by
    field_simp
    linear_combination (c ^ 2 * s ^ 4) * hr2
  rw [e]
  have h1 : 1 / s ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ha.le hs 2)
  have h2 : (1 - s ^ 2) * χ ≤ χ := by nlinarith [sq_nonneg s]
  nlinarith

/-- `∫_a^1 1/(2cs + K) = (1/(2c)) log((2c + K)/(2ca + K))`. -/
theorem integral_inv_lin {c K a : ℝ} (hc : 0 < c) (hK : 0 < K) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ s in a..1, 1 / (2 * c * s + K) = 1 / (2 * c) * log ((2 * c + K) / (2 * c * a + K)) := by
  have hpos : ∀ s, 0 ≤ s → 0 < 2 * c * s + K := fun s hs => by positivity
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := 1)
    (f := fun s => 1 / (2 * c) * log (2 * c * s + K)) (f' := fun s => 1 / (2 * c * s + K)) ?_ ?_
  · rw [h, mul_one, log_div (by linarith [hpos 1 zero_le_one] : 2 * c + K ≠ 0) (hpos a ha).ne']; ring
  · intro s hs
    rw [uIcc_of_le ha1] at hs
    have hp := hpos s (ha.trans hs.1)
    have := (((hasDerivAt_id s).const_mul (2 * c)).add_const K).log hp.ne'
    refine (this.const_mul (1 / (2 * c))).congr_deriv ?_
    simp only [id]
    field_simp
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ha1]
    have hg : ContinuousOn (fun s : ℝ => 2 * c * s + K) (Icc a 1) := by fun_prop
    exact continuousOn_const.div hg fun s hs => (hpos s (ha.trans hs.1)).ne'

/-- The constant `κ = 2 + √(2X)`, `X = 2c + 1/a² + χ`. -/
def kap (c χ a : ℝ) : ℝ := 2 + √(2 * (2 * c + 1 / a ^ 2 + χ))

set_option maxHeartbeats 1000000 in
/-- **The ladder ratio in closed form**: for even angular eigen-solutions at `χ_a ≤ χ_b`, `3χ_b ≤ c²`, positive with
`U ≥ 0` on `[a, 1]`, `2√χ_b/c ≤ a ≤ 1/2`:
`((χ_b − χ_a)/(2c)) log((2c + K₀)/(2ca + K₀)) ≤ log(g_b(1)/g_a(1)) − log(g_b(a)/g_a(a))`, `K₀ = 2/a + κ`. -/
theorem log_ratio_closed {ga ga₁ ga₂ gb gb₁ gb₂ : ℝ → ℝ} {c χa χb a : ℝ}
    (ha : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga (ga₁ t) t) (ha₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga₁ (ga₂ t) t)
    (hanga : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * ga₂ t - 2 * t * ga₁ t - c ^ 2 * t ^ 2 * ga t + χa * ga t = 0)
    (hb : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb (gb₁ t) t) (hb₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb₁ (gb₂ t) t)
    (hangb : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * gb₂ t - 2 * t * gb₁ t - c ^ 2 * t ^ 2 * gb t + χb * gb t = 0)
    (hc : 0 < c) (hχa : 0 < χa) (hχ : χa ≤ χb) (h3 : 3 * χb ≤ c ^ 2) (hab : 2 * √χb / c ≤ a) (ha2 : a ≤ 1 / 2)
    (hpa : ∀ t ∈ Icc a 1, 0 < ga t) (hpb : ∀ t ∈ Icc a 1, 0 < gb t)
    (hUa0 : ∀ t ∈ Icc a 1, 0 ≤ U ga ga₁ t) (hUb0 : ∀ t ∈ Icc a 1, 0 ≤ U gb gb₁ t) :
    (χb - χa) * (1 / (2 * c) * log ((2 * c + (2 / a + kap c χb a)) / (2 * c * a + (2 / a + kap c χb a))))
      ≤ log (gb 1 / ga 1) - log (gb a / ga a) := by
  have hχb : 0 < χb := hχa.trans_le hχ
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) hab
  have ha' : 2 * √χa / c ≤ a := le_trans (by gcongr) hab
  set W : ℝ → ℝ := fun s => c * s * √(1 - s ^ 2) + 1 / s with hWd
  set X := 2 * c + 1 / a ^ 2 + χb with hX
  have hX0 : 0 < X := by positivity
  set κ := kap c χb a with hκd
  have hκ2 : 2 ≤ κ := by simp only [hκd, kap]; linarith [Real.sqrt_nonneg (2 * (2 * c + 1 / a ^ 2 + χb))]
  have hκκ : κ * (κ - 2) = 2 * X + 2 * √(2 * X) := by
    simp only [hκd, kap, ← hX]
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * X by positivity)
    nlinarith
  have hUa := U_le_W ha ha₁ hanga hc hχa (by linarith) ha' ha2 hpa
  have hUb := U_le_W hb hb₁ hangb hc hχb h3 hab ha2 hpb
  have hWc : ContinuousOn (fun t => 1 / (W t + W t + κ)) (Icc a 1) := by
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hWt : 0 ≤ W t := by
      have := Real.sqrt_nonneg (1 - t ^ 2); simp only [hWd]; positivity
    refine ContinuousAt.continuousWithinAt ?_
    have hW1 : ContinuousAt W t := by
      simp only [hWd]
      have h1 : ContinuousAt (fun s : ℝ => c * s * √(1 - s ^ 2)) t :=
        (continuousAt_const.mul continuousAt_id).mul
          ((Real.continuous_sqrt.comp (by fun_prop)).continuousAt)
      have h2 : ContinuousAt (fun s : ℝ => 1 / s) t := continuousAt_const.div continuousAt_id ht0.ne'
      exact h1.add h2
    have hg : ContinuousAt (fun s => W s + W s + κ) t := (hW1.add hW1).add continuousAt_const
    have hne : W t + W t + κ ≠ 0 := by linarith
    exact continuousAt_const.div hg hne
  have hcond : ∀ t ∈ Ico a 1, (W t ^ 2 - (1 - t ^ 2) * (c ^ 2 * t ^ 2 - χa))
      + (W t ^ 2 - (1 - t ^ 2) * (c ^ 2 * t ^ 2 - χb)) < κ * (κ - 2) := by
    intro t ht
    have h1 := W_sq_sub_le hc hχa.le ha0 ht.1 ht.2.le
    have h2 := W_sq_sub_le hc hχb.le ha0 ht.1 ht.2.le
    have hs : 0 < √(2 * X) := Real.sqrt_pos.2 (by positivity)
    rw [hκκ]
    simp only [hWd] at *
    linarith
  have hmain := Cvs.Prolate.LadderRatioWkbMomenta.log_ratio_ge ha ha₁ hanga hb hb₁ hangb hχ ha0 (by linarith) hκ2
    hpa hpb hUa0 hUb0 hUa hUb hWc hcond
  refine le_trans ?_ hmain
  rw [← integral_inv_lin hc (by positivity) ha0.le (by linarith)]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    have hg : ContinuousOn (fun s : ℝ => 2 * c * s + (2 / a + κ)) (Icc a 1) := by fun_prop
    exact continuousOn_const.div hg fun s hs => (by
      have : 0 ≤ s := ha0.le.trans hs.1
      have : 0 < 2 * c * s + (2 / a + κ) := by positivity
      exact this.ne')
  · exact (hWc.mono (by rw [uIcc_of_le (by linarith)])).intervalIntegrable
  · intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hr1 : √(1 - t ^ 2) ≤ 1 := by rw [Real.sqrt_le_one]; nlinarith [sq_nonneg t]
    have hW : W t + W t + κ ≤ 2 * c * t + (2 / a + κ) := by
      simp only [hWd]
      have h1 : c * t * √(1 - t ^ 2) ≤ c * t := by
        have := mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ c * t); linarith
      have h2 : 1 / t ≤ 1 / a := one_div_le_one_div_of_le ha0 ht.1
      have e : 2 / a = 2 * (1 / a) := by ring
      rw [e]; linarith
    have hpos : 0 < W t + W t + κ := by
      have := Real.sqrt_nonneg (1 - t ^ 2); simp only [hWd]; positivity
    exact one_div_le_one_div_of_le hpos hW

end Cvs.Prolate.LadderRatioClosedForm
