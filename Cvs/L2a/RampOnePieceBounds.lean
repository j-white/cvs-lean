import Mathlib
import Cvs.L2a.ChebyshevRampBound
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
# The one-piece bounds on `‖x²w/p²‖²`, `‖w/p‖²` and `‖w/p²‖²`

A profile with `f² = w²g`, `g` nonincreasing on `[3/2, 2]` with primitive `G → 0`, has `‖f‖² ≤ (3/8)(G 2 − G(3/2)) − G 2`.
The primitives of `x⁴/p⁴`, `1/p²`, `1/p⁴` are `(ax + bx³ + cx⁵)/(48p³) + (k/2) log((x − 1)/(x + 1))`, which gives
`‖x²w/p²‖² ≤ 82747/324000 − (5/256)log 3 − (3/256)log 5`, `‖w/p‖² ≤ 13/30 − (5/32)log 3 − (3/32)log 5` and
`‖w/p²‖² ≤ 72127/324000 − (25/256)log 3 − (15/256)log 5`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.FarIntegrationByParts Cvs.L2a.FarFarBound Cvs.L2a.RampIntegrals Cvs.L2a.ChebyshevRampBound

namespace Cvs.L2a.RampOnePieceBounds

/-! ### The one-piece bound for a profile `f² = w²g` -/

/-- `‖f‖² = ∫_{3/2}^2 w²g + ∫_2^∞ g` when `f² = w²g` on `(3/2, ∞)`. -/
theorem nN_sq_eq_split {f g : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioi (3 / 2))))
    (hfg : ∀ x, 3 / 2 < x → f x ^ 2 = wF x ^ 2 * g x) :
    nN f ^ 2 = (∫ x in (3 / 2 : ℝ)..2, wF x ^ 2 * g x) + ∫ x in Ioi (2 : ℝ), g x := by
  have hi : IntegrableOn (fun x => f x ^ 2) (Ioi (3 / 2)) := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  rw [nN_sq, ← Ioc_union_Ioi_eq_Ioi (by norm_num : (3 / 2 : ℝ) ≤ 2),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self)
      (hi.mono_set (Ioi_subset_Ioi (by norm_num))),
    intervalIntegral.integral_of_le (by norm_num)]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioc fun x hx => hfg x hx.1
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx2 : (2 : ℝ) < x := hx
    rw [hfg x (by linarith), (wF_of_two_le hx2.le).1]; ring

/-- **The one-piece bound**: if `f² = w²g` on `(3/2, ∞)`, `g` is nonincreasing and continuous on `[3/2, 2]` and
nonnegative beyond `2`, and `G′ = g` on `(1, ∞)` with `G → 0`, then `‖f‖² ≤ (3/8)(G 2 − G(3/2)) − G 2`. -/
theorem nN_sq_le_of_primitive {f g G : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioi (3 / 2))))
    (hfg : ∀ x, 3 / 2 < x → f x ^ 2 = wF x ^ 2 * g x) (hg : AntitoneOn g (Icc (3 / 2) 2))
    (hgc : ContinuousOn g (Icc (3 / 2) 2)) (hg0 : ∀ x, 2 < x → 0 ≤ g x)
    (hG : ∀ x, 1 < x → HasDerivAt G (g x) x) (hlim : Tendsto G atTop (𝓝 0)) :
    nN f ^ 2 ≤ 3 / 8 * (G 2 - G (3 / 2)) - G 2 := by
  have hI : uIcc (3 / 2 : ℝ) 2 = Icc (3 / 2) 2 := uIcc_of_le (by norm_num)
  have hmid : ∫ x in (3 / 2 : ℝ)..2, g x = G 2 - G (3 / 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hG x (by rw [hI] at hx; linarith [hx.1])) ((hI ▸ hgc).intervalIntegrable)
  have htail : ∫ x in Ioi (2 : ℝ), g x = 0 - G 2 :=
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun x hx => hG x (by linarith [mem_Ici.mp hx]))
      (fun x hx => hg0 x hx) hlim
  have h := integral_wF_sq_mul_le hg hgc
  rw [nN_sq_eq_split hf hfg, htail]
  rw [hmid] at h
  linarith

/-! ### The primitives `(ax + bx³ + cx⁵)/(48p³) + (k/2) log((x − 1)/(x + 1))` -/

/-- The primitive family `(ax + bx³ + cx⁵)/(48p³) + k·½ log((x − 1)/(x + 1))`. -/
def primC (a b c k x : ℝ) : ℝ :=
  (a * x + b * x ^ 3 + c * x ^ 5) / (48 * pP x ^ 3) + k * (1 / 2 * Real.log ((x - 1) / (x + 1)))

/-- The derivative of `primC` on `x > 1`. -/
theorem hasDerivAt_primC (a b c k : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (primC a b c k) (((a + 3 * b * x ^ 2 + 5 * c * x ^ 4) * pP x - 6 * x * (a * x + b * x ^ 3 + c * x ^ 5)
      + 48 * k * pP x ^ 3) / (48 * pP x ^ 4)) x := by
  have hp : pP x ≠ 0 := (pP_pos hx).ne'
  have hN : HasDerivAt (fun x => a * x + b * x ^ 3 + c * x ^ 5) (a + 3 * b * x ^ 2 + 5 * c * x ^ 4) x := by
    have := (((hasDerivAt_id x).const_mul a).add ((hasDerivAt_pow 3 x).const_mul b)).add
      ((hasDerivAt_pow 5 x).const_mul c)
    refine this.congr_deriv ?_
    push_cast; ring
  have hD : HasDerivAt (fun x => 48 * pP x ^ 3) (48 * (3 * pP x ^ 2 * (2 * x))) x := by
    have hpd : HasDerivAt pP (2 * x) x := by
      have := (hasDerivAt_pow 2 x).sub_const 1
      refine this.congr_deriv ?_
      simp
    have := (hpd.pow 3).const_mul 48
    refine this.congr_deriv ?_
    push_cast; ring
  have := (hN.div hD (by positivity)).add ((hasDerivAt_half_log hx).const_mul k)
  refine this.congr_deriv ?_
  unfold pP at hp ⊢
  field_simp
  ring

/-- `½ log((x − 1)/(x + 1)) → 0` as `x → ∞`. -/
theorem tendsto_half_log : Tendsto (fun x : ℝ => 1 / 2 * Real.log ((x - 1) / (x + 1))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (x - 1) / (x + 1)) atTop (𝓝 1) := by
    have : Tendsto (fun x : ℝ => 1 - 2 / (x + 1)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_id))
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp; ring
  have := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).const_mul (1 / 2)
  rwa [Real.log_one, mul_zero] at this

/-- `(ax + bx³ + cx⁵)/(48p³) → 0` as `x → ∞` (substitute `t = 1/x`). -/
theorem tendsto_ratCube (a b c : ℝ) :
    Tendsto (fun x => (a * x + b * x ^ 3 + c * x ^ 5) / (48 * pP x ^ 3)) atTop (𝓝 0) := by
  set q : ℝ → ℝ := fun t => (a * t ^ 5 + b * t ^ 3 + c * t) / (48 * (1 - t ^ 2) ^ 3) with hq
  have hc : ContinuousAt q 0 := by
    have h1 : ContinuousAt (fun t : ℝ => a * t ^ 5 + b * t ^ 3 + c * t) 0 := by fun_prop
    have h2 : ContinuousAt (fun t : ℝ => 48 * (1 - t ^ 2) ^ 3) 0 := by fun_prop
    exact h1.div₀ h2 (by norm_num)
  have h := hc.tendsto.comp tendsto_inv_atTop_zero
  have h0 : q 0 = 0 := by simp [hq]
  rw [h0] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by positivity
  have hp : x ^ 2 - 1 ≠ 0 := by nlinarith
  simp only [Function.comp_apply, hq]
  unfold pP
  rw [div_eq_div_iff (by
      have : (1 : ℝ) - x⁻¹ ^ 2 = (x ^ 2 - 1) / x ^ 2 := by field_simp
      rw [this]; positivity) (by positivity)]
  field_simp

/-- `primC → 0` as `x → ∞`. -/
theorem tendsto_primC (a b c k : ℝ) : Tendsto (primC a b c k) atTop (𝓝 0) := by
  have := (tendsto_ratCube a b c).add (tendsto_half_log.const_mul k)
  rw [mul_zero, add_zero] at this
  exact this

/-- The one-piece bound evaluated: `‖f‖² ≤ −(5/8) primC 2 − (3/8) primC (3/2)`. -/
theorem nN_sq_le_primC {f g : ℝ → ℝ} {a b c k : ℝ} (hf : MemLp f 2 (volume.restrict (Ioi (3 / 2))))
    (hfg : ∀ x, 3 / 2 < x → f x ^ 2 = wF x ^ 2 * g x) (hg : AntitoneOn g (Icc (3 / 2) 2))
    (hgc : ContinuousOn g (Icc (3 / 2) 2)) (hg0 : ∀ x, 2 < x → 0 ≤ g x)
    (hG : ∀ x, 1 < x → HasDerivAt (primC a b c k) (g x) x) :
    nN f ^ 2 ≤ (-(2 * a + 8 * b + 32 * c) * (5 / 10368) - 3 / 8 * ((3 / 2 * a + 27 / 8 * b + 243 / 32 * c) * (4 / 375)))
      + (5 / 16 * k * Real.log 3 + 3 / 16 * k * Real.log 5) := by
  refine (nN_sq_le_of_primitive hf hfg hg hgc hg0 hG (tendsto_primC a b c k)).trans (le_of_eq ?_)
  unfold primC pP
  rw [show ((2 : ℝ) - 1) / (2 + 1) = (3 : ℝ)⁻¹ by norm_num,
    show ((3 / 2 : ℝ) - 1) / (3 / 2 + 1) = (5 : ℝ)⁻¹ by norm_num, Real.log_inv, Real.log_inv]
  ring

/-! ### Monotonicity on `[3/2, 2]` -/

/-- `1/pᵏ` is nonincreasing on `[3/2, 2]`. -/
theorem inv_pP_pow_antitoneOn (n : ℕ) : AntitoneOn (fun x => 1 / pP x ^ n) (Icc (3 / 2) 2) := by
  intro s hs t ht hst
  have hps := pP_pos (by linarith [hs.1] : (1 : ℝ) < s)
  have hpst : pP s ≤ pP t := by unfold pP; nlinarith [hs.1]
  exact one_div_le_one_div_of_le (pow_pos hps n) (pow_le_pow_left₀ hps.le hpst n)

/-- `x⁴/p⁴` is nonincreasing on `[3/2, 2]`. -/
theorem pow_four_div_pP_antitoneOn : AntitoneOn (fun x => x ^ 4 / pP x ^ 4) (Icc (3 / 2) 2) := by
  intro s hs t ht hst
  have h := sq_div_pP_sq_antitoneOn hs ht hst
  have ht0 : 0 ≤ t ^ 2 / pP t ^ 2 := by have := pP_pos (by linarith [ht.1] : (1 : ℝ) < t); positivity
  have := pow_le_pow_left₀ ht0 h 2
  simp only [div_pow, ← pow_mul] at this
  simpa only [div_pow, ← pow_mul] using this

/-- `u/pⁿ` is continuous on `[3/2, 2]` for continuous `u`. -/
theorem continuousOn_div_pP_pow {u : ℝ → ℝ} (hu : Continuous u) (n : ℕ) :
    ContinuousOn (fun x => u x / pP x ^ n) (Icc (3 / 2) 2) := by
  have hc : Continuous (fun x => pP x ^ n) := by unfold pP; fun_prop
  exact ContinuousOn.div₀ hu.continuousOn hc.continuousOn fun x hx =>
    pow_ne_zero n (pP_pos (by linarith [hx.1])).ne'

/-! ### The three closed forms -/

/-- `primC 3 (−8) (−3) (−1/16)` is a primitive of `x⁴/p⁴`. -/
theorem hasDerivAt_primC_xP₃ {x : ℝ} (hx : 1 < x) :
    HasDerivAt (primC 3 (-8) (-3) (-1 / 16)) (x ^ 4 / pP x ^ 4) x := by
  refine (hasDerivAt_primC _ _ _ _ hx).congr_deriv ?_
  have hp : pP x ≠ 0 := (pP_pos hx).ne'
  rw [div_eq_div_iff (by positivity) (by positivity)]
  unfold pP; ring

/-- `primC (−24) 48 (−24) (−1/2)` is a primitive of `1/p²`. -/
theorem hasDerivAt_primC_xP₄ {x : ℝ} (hx : 1 < x) :
    HasDerivAt (primC (-24) 48 (-24) (-1 / 2)) (1 / pP x ^ 2) x := by
  refine (hasDerivAt_primC _ _ _ _ hx).congr_deriv ?_
  have hp : pP x ≠ 0 := (pP_pos hx).ne'
  rw [div_eq_div_iff (by positivity) (by positivity)]
  unfold pP; ring

/-- `primC (−33) 40 (−15) (−5/16)` is a primitive of `1/p⁴`. -/
theorem hasDerivAt_primC_xP₇ {x : ℝ} (hx : 1 < x) :
    HasDerivAt (primC (-33) 40 (-15) (-5 / 16)) (1 / pP x ^ 4) x := by
  refine (hasDerivAt_primC _ _ _ _ hx).congr_deriv ?_
  have hp : pP x ≠ 0 := (pP_pos hx).ne'
  rw [div_eq_div_iff (by positivity) (by positivity)]
  unfold pP; ring

/-- **`ν₃`**: `‖x²w/p²‖² ≤ 82747/324000 − (5/256) log 3 − (3/256) log 5`. -/
theorem nN_xP₃_sq_le : nN xP₃ ^ 2 ≤ 82747 / 324000 - 5 / 256 * Real.log 3 - 3 / 256 * Real.log 5 := by
  refine (nN_sq_le_primC (g := fun x => x ^ 4 / pP x ^ 4) memLp_xP.2.1 (fun x hx => ?_)
    pow_four_div_pP_antitoneOn (continuousOn_div_pP_pow (by fun_prop) 4)
    (fun x hx => by have := pP_pos (by linarith : (1 : ℝ) < x); positivity)
    fun x hx => hasDerivAt_primC_xP₃ hx).trans (le_of_eq ?_)
  · unfold xP₃; ring
  · norm_num; ring

/-- **`ν₄`**: `‖w/p‖² ≤ 13/30 − (5/32) log 3 − (3/32) log 5`. -/
theorem nN_xP₄_sq_le : nN xP₄ ^ 2 ≤ 13 / 30 - 5 / 32 * Real.log 3 - 3 / 32 * Real.log 5 := by
  refine (nN_sq_le_primC (g := fun x => 1 / pP x ^ 2) memLp_xP.2.2.1 (fun x hx => ?_)
    (inv_pP_pow_antitoneOn 2) (continuousOn_div_pP_pow (by fun_prop) 2)
    (fun x hx => by have := pP_pos (by linarith : (1 : ℝ) < x); positivity)
    fun x hx => hasDerivAt_primC_xP₄ hx).trans (le_of_eq ?_)
  · unfold xP₄; ring
  · norm_num; ring

/-- **`ν₇`**: `‖w/p²‖² ≤ 72127/324000 − (25/256) log 3 − (15/256) log 5`. -/
theorem nN_xP₇_sq_le : nN xP₇ ^ 2 ≤ 72127 / 324000 - 25 / 256 * Real.log 3 - 15 / 256 * Real.log 5 := by
  refine (nN_sq_le_primC (g := fun x => 1 / pP x ^ 4) memLp_xP.2.2.2.2.2 (fun x hx => ?_)
    (inv_pP_pow_antitoneOn 4) (continuousOn_div_pP_pow (by fun_prop) 4)
    (fun x hx => by have := pP_pos (by linarith : (1 : ℝ) < x); positivity)
    fun x hx => hasDerivAt_primC_xP₇ hx).trans (le_of_eq ?_)
  · unfold xP₇; ring
  · norm_num; ring

/-- An admissible `ν₃`: `‖x²w/p²‖ ≤ (82747/324000 − (5/256) log 3 − (3/256) log 5)^{1/2}`. -/
theorem nN_xP₃_le : nN xP₃ ≤ √(82747 / 324000 - 5 / 256 * Real.log 3 - 3 / 256 * Real.log 5) :=
  Real.le_sqrt_of_sq_le nN_xP₃_sq_le

/-- An admissible `ν₄`: `‖w/p‖ ≤ (13/30 − (5/32) log 3 − (3/32) log 5)^{1/2}`. -/
theorem nN_xP₄_le : nN xP₄ ≤ √(13 / 30 - 5 / 32 * Real.log 3 - 3 / 32 * Real.log 5) :=
  Real.le_sqrt_of_sq_le nN_xP₄_sq_le

/-- An admissible `ν₇`: `‖w/p²‖ ≤ (72127/324000 − (25/256) log 3 − (15/256) log 5)^{1/2}`. -/
theorem nN_xP₇_le : nN xP₇ ≤ √(72127 / 324000 - 25 / 256 * Real.log 3 - 15 / 256 * Real.log 5) :=
  Real.le_sqrt_of_sq_le nN_xP₇_sq_le

end Cvs.L2a.RampOnePieceBounds

end
