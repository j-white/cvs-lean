import Mathlib
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.RampIntegrals
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Chebyshev's integral inequality and the one-piece bound on `‖xw/p‖²`

For `f` nondecreasing and `g` nonincreasing on `[a, b]`, `(b − a)∫fg ≤ ∫f ∫g`. With `∫_{3/2}^2 w² = 3/16` this gives
`∫_{3/2}^2 w²g ≤ (3/8)∫_{3/2}^2 g`, and with `∫_2^∞ x²/p² = 1/3 + (log 3)/4`: `‖xw/p‖² ≤ 13/30 + (5/32)log 3 + (3/32)log 5`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts Cvs.L2a.FarFarBound Cvs.L2a.RampIntegrals

namespace Cvs.L2a.ChebyshevRampBound

/-- **Chebyshev's integral inequality**: for `f` nondecreasing and `g` nonincreasing on `[a, b]`, both continuous,
`(b − a) ∫ fg ≤ ∫ f ∫ g`. -/
theorem integral_mul_le_of_monotoneOn_antitoneOn {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc a b))
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b)) :
    (b - a) * ∫ x in a..b, f x * g x ≤ (∫ x in a..b, f x) * ∫ x in a..b, g x := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  have hfi : IntervalIntegrable f volume a b := (hI ▸ hfc).intervalIntegrable
  have hgi : IntervalIntegrable g volume a b := (hI ▸ hgc).intervalIntegrable
  have hfgi : IntervalIntegrable (fun x => f x * g x) volume a b := (hI ▸ hfc.mul hgc).intervalIntegrable
  have hpt : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, (f s - f t) * (g s - g t) ≤ 0 := by
    intro s hs t ht
    rcases le_total s t with h | h
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hf hs ht h)) (sub_nonneg.2 (hg hs ht h))
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hf ht hs h)) (sub_nonpos.2 (hg ht hs h))
  have hinner : ∀ s, ∫ t in a..b, (f s - f t) * (g s - g t)
      = (b - a) * (f s * g s) - f s * (∫ x in a..b, g x) - g s * (∫ x in a..b, f x)
        + ∫ x in a..b, f x * g x := by
    intro s
    have e : (fun t => (f s - f t) * (g s - g t))
        = fun t => ((f s * g s - f s * g t) - g s * f t) + f t * g t := by funext t; ring
    rw [e, intervalIntegral.integral_add
        ((((intervalIntegrable_const).sub (hgi.const_mul _))).sub (hfi.const_mul _)) hfgi,
      intervalIntegral.integral_sub ((intervalIntegrable_const).sub (hgi.const_mul _)) (hfi.const_mul _),
      intervalIntegral.integral_sub intervalIntegrable_const (hgi.const_mul _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, smul_eq_mul]
  have hle : ∀ s ∈ Icc a b, (b - a) * (f s * g s) - f s * (∫ x in a..b, g x) - g s * (∫ x in a..b, f x)
      + (∫ x in a..b, f x * g x) ≤ 0 := by
    intro s hs
    rw [← hinner]
    have := intervalIntegral.integral_mono_on (μ := volume) hab
      (f := fun t => (f s - f t) * (g s - g t)) (g := fun _ => (0 : ℝ))
      ((hI ▸ ((continuousOn_const.sub hfc).mul (continuousOn_const.sub hgc))).intervalIntegrable)
      intervalIntegrable_const (fun t ht => hpt s hs t ht)
    simpa using this
  have hout := intervalIntegral.integral_mono_on (μ := volume) hab
    (f := fun s => (b - a) * (f s * g s) - f s * (∫ x in a..b, g x) - g s * (∫ x in a..b, f x)
      + (∫ x in a..b, f x * g x)) (g := fun _ => (0 : ℝ))
    ((((hfgi.const_mul _).sub (hfi.mul_const _)).sub (hgi.mul_const _)).add intervalIntegrable_const)
    intervalIntegrable_const hle
  rw [intervalIntegral.integral_add (((hfgi.const_mul _).sub (hfi.mul_const _)).sub (hgi.mul_const _))
      intervalIntegrable_const,
    intervalIntegral.integral_sub ((hfgi.const_mul _).sub (hfi.mul_const _)) (hgi.mul_const _),
    intervalIntegral.integral_sub (hfgi.const_mul _) (hfi.mul_const _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, intervalIntegral.integral_const,
    intervalIntegral.integral_zero, smul_eq_mul] at hout
  nlinarith

/-! ### The ramp on `[3/2, 2]` -/

/-- On `[3/2, 2]`, `w = sin²(πx − 3π/2)`. -/
theorem wF_eq_on {x : ℝ} (hx : x ∈ Icc (3 / 2 : ℝ) 2) : wF x = Real.sin (π * x - 3 * π / 2) ^ 2 := by
  have hcl : clampW x = x := by unfold clampW; rw [min_eq_left hx.2, max_eq_right hx.1]
  unfold wF; rw [hcl, show π * (x - 3 / 2) = π * x - 3 * π / 2 by ring]

/-- `w²` is nondecreasing on `[3/2, 2]`. -/
theorem wF_sq_monotoneOn : MonotoneOn (fun x => wF x ^ 2) (Icc (3 / 2) 2) := by
  intro s hs t ht hst
  simp only
  rw [wF_eq_on hs, wF_eq_on ht]
  have h0 : 0 ≤ Real.sin (π * s - 3 * π / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [pi_pos, hs.1])
    (by nlinarith [pi_pos, hs.2])
  have h1 : Real.sin (π * s - 3 * π / 2) ≤ Real.sin (π * t - 3 * π / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [pi_pos, hs.1]) (by nlinarith [pi_pos, ht.2])
      (by nlinarith [pi_pos])
  have := pow_le_pow_left₀ h0 h1 4
  calc (Real.sin (π * s - 3 * π / 2) ^ 2) ^ 2 = Real.sin (π * s - 3 * π / 2) ^ 4 := by ring
    _ ≤ Real.sin (π * t - 3 * π / 2) ^ 4 := this
    _ = _ := by ring

/-- `∫_{3/2}^2 w² = 3/16`. -/
theorem integral_wF_sq : ∫ x in (3 / 2 : ℝ)..2, wF x ^ 2 = 3 / 16 := by
  rw [intervalIntegral.integral_congr (g := fun x => Real.sin (π * x - 3 * π / 2) ^ 4) (fun x hx => by
    rw [uIcc_of_le (by norm_num)] at hx
    simp only; rw [wF_eq_on hx]; ring)]
  rw [intervalIntegral.integral_comp_mul_sub (fun u => Real.sin u ^ 4) pi_ne_zero (3 * π / 2),
    show π * (3 / 2) - 3 * π / 2 = 0 by ring, show π * 2 - 3 * π / 2 = π / 2 by ring,
    show (4 : ℕ) = 2 + 2 from rfl, integral_sin_pow, integral_sin_sq]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two, smul_eq_mul]
  field_simp
  ring

/-- **The one-piece bound**: `∫_{3/2}^2 w²g ≤ (3/8)∫_{3/2}^2 g` for `g` nonincreasing and continuous on `[3/2, 2]`. -/
theorem integral_wF_sq_mul_le {g : ℝ → ℝ} (hg : AntitoneOn g (Icc (3 / 2) 2))
    (hgc : ContinuousOn g (Icc (3 / 2) 2)) :
    ∫ x in (3 / 2 : ℝ)..2, wF x ^ 2 * g x ≤ 3 / 8 * ∫ x in (3 / 2 : ℝ)..2, g x := by
  have h := integral_mul_le_of_monotoneOn_antitoneOn (by norm_num) wF_sq_monotoneOn hg
    ((continuous_wF.1.pow 2).continuousOn) hgc
  rw [integral_wF_sq] at h
  linarith

/-! ### `x²/p²` -/

/-- `x²/p²` is nonincreasing on `[3/2, 2]`. -/
theorem sq_div_pP_sq_antitoneOn : AntitoneOn (fun x => x ^ 2 / pP x ^ 2) (Icc (3 / 2) 2) := by
  intro s hs t ht hst
  have hs1 : (1 : ℝ) < s := by linarith [hs.1]
  have ht1 : (1 : ℝ) < t := by linarith [ht.1]
  have hps := pP_pos hs1
  have hpt := pP_pos ht1
  have key : t / pP t ≤ s / pP s := by
    rw [div_le_div_iff₀ hpt hps]; unfold pP
    nlinarith [mul_nonneg (sub_nonneg.2 hst) (by nlinarith : (0:ℝ) ≤ s * t + 1)]
  have := pow_le_pow_left₀ (by positivity) key 2
  simp only [div_pow] at this
  exact this

/-- The primitive `¼ log((x − 1)/(x + 1)) − x/(2p)` of `x²/p²`. -/
def primSq (x : ℝ) : ℝ := 1 / 2 * (1 / 2 * Real.log ((x - 1) / (x + 1))) - x / (2 * pP x)

/-- `(¼ log((x − 1)/(x + 1)) − x/(2p))′ = x²/p²` for `x > 1`. -/
theorem hasDerivAt_primSq {x : ℝ} (hx : 1 < x) : HasDerivAt primSq (x ^ 2 / pP x ^ 2) x := by
  have hp : pP x ≠ 0 := (pP_pos hx).ne'
  have h1 := (hasDerivAt_half_log hx).const_mul (1 / 2)
  have hpd : HasDerivAt (fun x => 2 * pP x) (2 * (2 * x)) x := by
    have := ((hasDerivAt_pow 2 x).sub_const 1).const_mul 2
    refine this.congr_deriv ?_
    simp
  have h2 := (hasDerivAt_id x).div hpd (by positivity)
  have := h1.sub h2
  unfold primSq
  refine this.congr_deriv ?_
  simp only [id_eq]
  unfold pP at hp ⊢
  field_simp
  ring

/-- `¼ log((x − 1)/(x + 1)) − x/(2p) → 0` as `x → ∞`. -/
theorem tendsto_primSq : Tendsto primSq atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (x - 1) / (x + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun x : ℝ => 1 - 2 / (x + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_id))
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp; ring
  have hlog : Tendsto (fun x : ℝ => Real.log ((x - 1) / (x + 1))) atTop (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rwa [Real.log_one] at this
  have h2 : Tendsto (fun x : ℝ => x / (2 * pP x)) atTop (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have := pP_pos hx; positivity
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      have hp := pP_pos (by linarith : (1 : ℝ) < x)
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      unfold pP; nlinarith
  have := ((hlog.const_mul (1 / 2)).const_mul (1 / 2)).sub h2
  simp only [mul_zero, sub_zero] at this
  exact this

/-- `∫_2^∞ x²/p² = 1/3 + (log 3)/4`. -/
theorem integral_sq_div_pP_sq_Ioi_two : ∫ x in Ioi (2 : ℝ), x ^ 2 / pP x ^ 2 = 1 / 3 + Real.log 3 / 4 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => hasDerivAt_primSq (by linarith [mem_Ici.mp hx]))
    (fun x _ => by positivity) tendsto_primSq]
  unfold primSq pP
  rw [show ((2 : ℝ) - 1) / (2 + 1) = (3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- `∫_{3/2}^2 x²/p² = 4/15 + (log 5 − log 3)/4`. -/
theorem integral_sq_div_pP_sq_mid :
    ∫ x in (3 / 2 : ℝ)..2, x ^ 2 / pP x ^ 2 = 4 / 15 + (Real.log 5 - Real.log 3) / 4 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := primSq)
    (fun x hx => hasDerivAt_primSq (by rw [uIcc_of_le (by norm_num)] at hx; linarith [hx.1]))
    (ContinuousOn.intervalIntegrable (by
      have hn : ContinuousOn (fun x : ℝ => x ^ 2) (uIcc (3 / 2 : ℝ) 2) := by fun_prop
      have hd : ContinuousOn (fun x : ℝ => pP x ^ 2) (uIcc (3 / 2 : ℝ) 2) := by
        unfold pP; fun_prop
      refine ContinuousOn.div₀ hn hd fun x hx => ?_
      rw [uIcc_of_le (by norm_num)] at hx
      exact pow_ne_zero 2 (pP_pos (by linarith [hx.1])).ne'))]
  unfold primSq pP
  rw [show ((2 : ℝ) - 1) / (2 + 1) = (3 : ℝ)⁻¹ by norm_num, show ((3 / 2 : ℝ) - 1) / (3 / 2 + 1) = (5 : ℝ)⁻¹ by
    norm_num, Real.log_inv, Real.log_inv]
  ring

/-! ### `‖xw/p‖` -/

/-- `‖xw/p‖² = ∫_{3/2}^2 w²x²/p² + ∫_2^∞ x²/p²`. -/
theorem nN_xP₂_sq_eq :
    nN xP₂ ^ 2 = (∫ x in (3 / 2 : ℝ)..2, wF x ^ 2 * (x ^ 2 / pP x ^ 2)) + ∫ x in Ioi (2 : ℝ), x ^ 2 / pP x ^ 2 := by
  have hi : IntegrableOn (fun x => xP₂ x ^ 2) (Ioi (3 / 2)) :=
    (memLp_two_iff_integrable_sq memLp_xP.1.aestronglyMeasurable).mp memLp_xP.1
  rw [nN_sq, ← Ioc_union_Ioi_eq_Ioi (by norm_num : (3 / 2 : ℝ) ≤ 2),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self)
      (hi.mono_set (Ioi_subset_Ioi (by norm_num))),
    ← intervalIntegral.integral_of_le (by norm_num)]
  congr 1
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [xP₂]; ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [xP₂]; rw [(wF_of_two_le (le_of_lt hx)).1]; ring

/-- **The one-piece closed form**: `‖xw/p‖² ≤ 13/30 + (5/32) log 3 + (3/32) log 5`. -/
theorem nN_xP₂_sq_le : nN xP₂ ^ 2 ≤ 13 / 30 + 5 / 32 * Real.log 3 + 3 / 32 * Real.log 5 := by
  have hn : ContinuousOn (fun x : ℝ => x ^ 2) (Icc (3 / 2 : ℝ) 2) := by fun_prop
  have hd : ContinuousOn (fun x : ℝ => pP x ^ 2) (Icc (3 / 2 : ℝ) 2) := by
    unfold pP; fun_prop
  have h := integral_wF_sq_mul_le sq_div_pP_sq_antitoneOn (ContinuousOn.div₀ hn hd
    fun x hx => pow_ne_zero 2 (pP_pos (by linarith [hx.1])).ne')
  rw [nN_xP₂_sq_eq, integral_sq_div_pP_sq_Ioi_two]
  rw [integral_sq_div_pP_sq_mid] at h
  linarith

/-- `‖xw/p‖ ≤ (13/30 + (5/32) log 3 + (3/32) log 5)^{1/2}`, an admissible `ν₂`. -/
theorem nN_xP₂_le : nN xP₂ ≤ √(13 / 30 + 5 / 32 * Real.log 3 + 3 / 32 * Real.log 5) :=
  Real.le_sqrt_of_sq_le nN_xP₂_sq_le

end Cvs.L2a.ChebyshevRampBound

end
