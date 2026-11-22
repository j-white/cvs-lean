import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ZetaValues
import Cvs.Prolate.ExteriorMassArcsineFinite
import Cvs.Prolate.ExteriorMassEdgeLayer
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sizes of the arcsine law's error at `ξ = √(1 + y/c²)`

At `ξ_y = √(1 + y/c²)`: `p = y/c²`, `q = c²(1 + r − u)`, `a = √(y(1 + r − u))` and
`w √y = ξ_y (1 + 2r − u)/((1 + r − u)^{3/2})`, with `r = y/c²`, `u = χ/c²`. If `χ/c² → 0`, then with the base point
`y = 1` and the reference point `y = √c`: `w(ξ_b) → 1`, `p q(ξ_b) → 1`, `K_b → 4e`, `w(ξ₀) → 0`, and `errR → 0`.
-/

noncomputable section

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.ExteriorMassEdgeLayer Cvs.Prolate.ExteriorMassArcsineFinite

namespace Cvs.Prolate.ArcsineLawErrorSizes

/-- The point `ξ_y = √(1 + y/c²)`, where `p(ξ_y) = y/c²`. -/
def xiAt (c y : ℝ) : ℝ := √(1 + y / c ^ 2)

/-- The energy factor as a function of the rate: `fac = facW ∘ w`. -/
def facW (w : ℝ) : ℝ := (1 + w / 2) / (1 - w / 2) * exp (w / (2 - w))

section fixed

variable {c χ y : ℝ}

theorem sq_xiAt (hy : 0 ≤ y) : xiAt c y ^ 2 = 1 + y / c ^ 2 :=
  sq_sqrt (by positivity)

theorem one_le_xiAt (hy : 0 ≤ y) : 1 ≤ xiAt c y := by
  have : 0 ≤ y / c ^ 2 := by positivity
  have h := sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + y / c ^ 2 by linarith)
  simpa [xiAt] using h

theorem one_lt_xiAt (hc : c ≠ 0) (hy : 0 < y) : 1 < xiAt c y := by
  have : 0 < y / c ^ 2 := by positivity
  have h := sqrt_lt_sqrt zero_le_one (show (1 : ℝ) < 1 + y / c ^ 2 by linarith)
  simpa [xiAt] using h

theorem pP_xiAt (hy : 0 ≤ y) : pP (xiAt c y) = y / c ^ 2 := by
  unfold pP; rw [sq_xiAt hy]; ring

theorem qP_xiAt (hc : c ≠ 0) (hy : 0 ≤ y) :
    qP c χ (xiAt c y) = c ^ 2 * (1 + y / c ^ 2 - χ / c ^ 2) := by
  unfold qP; rw [sq_xiAt hy]; field_simp

theorem pq_xiAt (hc : c ≠ 0) (hy : 0 ≤ y) :
    pP (xiAt c y) * qP c χ (xiAt c y) = y * (1 + y / c ^ 2 - χ / c ^ 2) := by
  rw [pP_xiAt hy, qP_xiAt hc hy]; field_simp

theorem aP_xiAt (hc : c ≠ 0) (hy : 0 ≤ y) :
    aP c χ (xiAt c y) = √y * √(1 + y / c ^ 2 - χ / c ^ 2) := by
  unfold aP; rw [pq_xiAt hc hy, sqrt_mul hy]

/-- **The rate at `ξ_y`, times `√y`**: `w √y = ξ_y (1 + 2r − u)/((1 + r − u)√(1 + r − u))`. -/
theorem wP_mul_sqrt (hc : c ≠ 0) (hy : 0 < y) (hpos : 0 < 1 + y / c ^ 2 - χ / c ^ 2) :
    wP c χ (xiAt c y) * √y = xiAt c y * (1 + 2 * (y / c ^ 2) - χ / c ^ 2)
      / ((1 + y / c ^ 2 - χ / c ^ 2) * √(1 + y / c ^ 2 - χ / c ^ 2)) := by
  have hsy : 0 < √y := sqrt_pos.mpr hy
  have hs : 0 < √(1 + y / c ^ 2 - χ / c ^ 2) := sqrt_pos.mpr hpos
  unfold wP dP
  rw [qP_xiAt hc hy.le, aP_xiAt hc hy.le, sq_xiAt hy.le]
  field_simp
  ring

end fixed

/-! ### Limits along `c → ∞` with `χ/c² → 0` -/

section limits

variable {χ : ℝ → ℝ} (hu : Tendsto (fun c => χ c / c ^ 2) atTop (𝓝 0))
include hu

omit hu in
theorem tendsto_inv_sq' : Tendsto (fun c : ℝ => 1 / c ^ 2) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) two_ne_zero)
  simpa [one_div, Function.comp_def] using h

omit hu in
theorem tendsto_sqrt_div_sq : Tendsto (fun c : ℝ => √c / c ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c * √c) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ tendsto_sqrt_atTop
  refine (tendsto_inv_atTop_zero.comp h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ c = t ^ 2 := ⟨√c, sqrt_pos.2 hc, (sq_sqrt hc.le).symm⟩
  simp only [Function.comp_apply, sqrt_sq ht.le]
  field_simp

omit hu in
theorem tendsto_xiAt {y : ℝ → ℝ} (hr : Tendsto (fun c => y c / c ^ 2) atTop (𝓝 0)) :
    Tendsto (fun c => xiAt c (y c)) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hr).sqrt
  simpa [xiAt] using h

/-- With `y/c² → 0` and `y > 0` eventually, `w(ξ_y) √y → 1`. -/
theorem tendsto_wP_mul_sqrt {y : ℝ → ℝ} (hr : Tendsto (fun c => y c / c ^ 2) atTop (𝓝 0))
    (hy : ∀ᶠ c in atTop, 0 < y c) :
    Tendsto (fun c => wP c (χ c) (xiAt c (y c)) * √(y c)) atTop (𝓝 1) := by
  have hm : Tendsto (fun c => 1 + y c / c ^ 2 - χ c / c ^ 2) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hr).sub hu
    simpa using h
  have hm2 : Tendsto (fun c => 1 + 2 * (y c / c ^ 2) - χ c / c ^ 2) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add (hr.const_mul 2)).sub hu
    simpa using h
  have hξ := tendsto_xiAt hr
  have hsq : Tendsto (fun c => √(1 + y c / c ^ 2 - χ c / c ^ 2)) atTop (𝓝 1) := by
    simpa using hm.sqrt
  have hlim : Tendsto (fun c => xiAt c (y c) * (1 + 2 * (y c / c ^ 2) - χ c / c ^ 2)
      / ((1 + y c / c ^ 2 - χ c / c ^ 2) * √(1 + y c / c ^ 2 - χ c / c ^ 2))) atTop
      (𝓝 (1 * 1 / (1 * 1))) := (hξ.mul hm2).div (hm.mul hsq) (by norm_num)
  rw [show (1 : ℝ) * 1 / (1 * 1) = 1 by norm_num] at hlim
  refine hlim.congr' ?_
  filter_upwards [hy, hm.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ne_atTop 0]
    with c hyc hpos hc
  exact (wP_mul_sqrt hc hyc hpos).symm

/-- The base point `ξ_b = √(1 + 1/c²)` has rate `w → 1`. -/
theorem tendsto_wP_base : Tendsto (fun c => wP c (χ c) (xiAt c 1)) atTop (𝓝 1) := by
  simpa using tendsto_wP_mul_sqrt hu (y := fun _ => 1) tendsto_inv_sq' (Eventually.of_forall fun _ => one_pos)

/-- The reference point `ξ₀ = √(1 + √c/c²)` has rate `w → 0`. -/
theorem tendsto_wP_ref : Tendsto (fun c => wP c (χ c) (xiAt c √c)) atTop (𝓝 0) := by
  have h := tendsto_wP_mul_sqrt hu (y := fun c => √c) tendsto_sqrt_div_sq
    (eventually_gt_atTop 0 |>.mono fun c hc => sqrt_pos.mpr hc)
  have hinv : Tendsto (fun c : ℝ => (√(√c))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp tendsto_sqrt_atTop)
  have h2 : Tendsto (fun c => wP c (χ c) (xiAt c √c) * √(√c) * (√(√c))⁻¹) atTop (𝓝 (1 * 0)) :=
    h.mul hinv
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  have : 0 < √(√c) := sqrt_pos.mpr (sqrt_pos.mpr hc)
  field_simp

/-- `p q(ξ_b) → 1`. -/
theorem tendsto_pq_base :
    Tendsto (fun c => pP (xiAt c 1) * qP c (χ c) (xiAt c 1)) atTop (𝓝 1) := by
  have hm : Tendsto (fun c => 1 * (1 + 1 / c ^ 2 - χ c / c ^ 2)) atTop (𝓝 (1 * (1 + 0 - 0))) :=
    (((tendsto_const_nhds).add tendsto_inv_sq').sub hu).const_mul 1
  rw [show (1 : ℝ) * (1 + 0 - 0) = 1 by norm_num] at hm
  refine hm.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with c hc
  rw [pq_xiAt hc zero_le_one]

omit hu in
theorem continuousAt_facW {w : ℝ} (hw : w ≠ 2) : ContinuousAt facW w := by
  have h2 : 1 - w / 2 ≠ 0 := by intro h; apply hw; linarith
  have h2' : 2 - w ≠ 0 := by intro h; apply hw; linarith
  unfold facW
  exact ((continuousAt_const.add (continuousAt_id.div_const 2)).div
    (continuousAt_const.sub (continuousAt_id.div_const 2)) h2).mul
    (continuous_exp.continuousAt.comp (continuousAt_id.div (continuousAt_const.sub continuousAt_id) h2'))

omit hu in
theorem facW_zero : facW 0 = 1 := by simp [facW]

omit hu in
theorem facW_one : facW 1 = 3 * exp 1 := by
  unfold facW; norm_num

/-- `fac(ξ₀) → 1`. -/
theorem tendsto_fac_ref :
    Tendsto (fun c => Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c (χ c) (xiAt c √c)) atTop (𝓝 1) := by
  have h := (continuousAt_facW (w := 0) (by norm_num)).tendsto.comp (tendsto_wP_ref hu)
  rw [facW_zero] at h
  exact h

/-- **The edge constant tends to `4e`**: `K_b = fac(ξ_b)/(a(ξ_b)(1 − a(ξ_b)²/4)) → 3e/(3/4)`. -/
theorem tendsto_kEdge : Tendsto (fun c => kEdge c (χ c) (xiAt c 1)) atTop (𝓝 (4 * exp 1)) := by
  have hF := (continuousAt_facW (w := 1) (by norm_num)).tendsto.comp (tendsto_wP_base hu)
  rw [facW_one] at hF
  have hpq := tendsto_pq_base hu
  have ha : Tendsto (fun c => aP c (χ c) (xiAt c 1)) atTop (𝓝 1) := by
    simpa [aP] using hpq.sqrt
  have hlim : Tendsto (fun c => facW (wP c (χ c) (xiAt c 1)) / (aP c (χ c) (xiAt c 1) *
      (1 - pP (xiAt c 1) * qP c (χ c) (xiAt c 1) / 4))) atTop (𝓝 (3 * exp 1 / (1 * (1 - 1 / 4)))) :=
    hF.div (ha.mul (tendsto_const_nhds.sub (hpq.div_const 4))) (by norm_num)
  rw [show 3 * exp 1 / (1 * (1 - 1 / 4 : ℝ)) = 4 * exp 1 by ring] at hlim
  exact hlim

omit hu in
/-- `c (ξ₀ − 1) → 0`. -/
theorem tendsto_c_mul_sub : Tendsto (fun c => c * (xiAt c √c - 1)) atTop (𝓝 0) := by
  -- `c(√(1 + r) − 1) = c r/(√(1 + r) + 1)` and `c r = 1/√c`
  have hcr : Tendsto (fun c : ℝ => c * (√c / c ^ 2)) atTop (𝓝 0) := by
    refine (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with c hc
    obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ c = t ^ 2 := ⟨√c, sqrt_pos.2 hc, (sq_sqrt hc.le).symm⟩
    simp only [Function.comp_apply, sqrt_sq ht.le]
    field_simp
  have hsq : Tendsto (fun c : ℝ => xiAt c √c + 1) atTop (𝓝 (1 + 1)) :=
    (tendsto_xiAt tendsto_sqrt_div_sq).add_const 1
  have h : Tendsto (fun c : ℝ => c * (√c / c ^ 2) / (xiAt c √c + 1)) atTop (𝓝 (0 / (1 + 1))) :=
    hcr.div hsq (by norm_num)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  have hs1 : 0 < xiAt c √c + 1 := by have := one_le_xiAt (c := c) (sqrt_nonneg c); linarith
  have hsq2 : xiAt c √c ^ 2 = 1 + √c / c ^ 2 := sq_xiAt (sqrt_nonneg c)
  rw [div_eq_iff hs1.ne']
  have e : c * (xiAt c √c - 1) * (xiAt c √c + 1) = c * (xiAt c √c ^ 2 - 1) := by ring
  rw [e, hsq2]; ring

/-- `c/√(c² − χ) → 1`. -/
theorem tendsto_c_div_sigma : Tendsto (fun c => c / √(c ^ 2 - χ c)) atTop (𝓝 1) := by
  have hm : Tendsto (fun c => 1 - χ c / c ^ 2) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hu
  rw [sub_zero] at hm
  have h : Tendsto (fun c => 1 / √(1 - χ c / c ^ 2)) atTop (𝓝 (1 / √1)) :=
    tendsto_const_nhds.div hm.sqrt (by simp)
  rw [sqrt_one, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with c hc hlt
  have hc2 : 0 < c ^ 2 := by positivity
  have e : c ^ 2 - χ c = c ^ 2 * (1 - χ c / c ^ 2) := by field_simp
  rw [e, sqrt_mul hc2.le, sqrt_sq hc.le]
  have : 0 < √(1 - χ c / c ^ 2) := sqrt_pos.mpr (by linarith)
  field_simp

/-- `c/(c² − χ) → 0`. -/
theorem tendsto_c_div_sub : Tendsto (fun c => c / (c ^ 2 - χ c)) atTop (𝓝 0) := by
  have hm : Tendsto (fun c => 1 - χ c / c ^ 2) atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hu
  rw [sub_zero] at hm
  have h : Tendsto (fun c : ℝ => c⁻¹ / (1 - χ c / c ^ 2)) atTop (𝓝 (0 / 1)) :=
    tendsto_inv_atTop_zero.div hm (by norm_num)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with c hc hlt
  have : 0 < 1 - χ c / c ^ 2 := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have e : c ^ 2 - χ c = c ^ 2 * (1 - χ c / c ^ 2) := by field_simp
  rw [e]; field_simp

omit hu in
/-- `ℓ = (2/π) arcsin(1/ξ₀) → 1`. -/
theorem tendsto_ellA : Tendsto (fun c => ellA (xiAt c √c)) atTop (𝓝 1) := by
  have hξ := tendsto_xiAt tendsto_sqrt_div_sq
  have hi : Tendsto (fun c => 1 / xiAt c √c) atTop (𝓝 (1 / 1)) := tendsto_const_nhds.div hξ one_ne_zero
  rw [div_one] at hi
  have h : Tendsto (fun c => 2 / π * arcsin (1 / xiAt c √c)) atTop (𝓝 (2 / π * arcsin 1)) :=
    ((continuous_arcsin.tendsto 1).comp hi).const_mul (2 / π)
  rw [arcsin_one, show 2 / π * (π / 2) = 1 by field_simp] at h
  exact h

/-- `L = ℓ/fac(ξ₀) → 1`. -/
theorem tendsto_lowL : Tendsto (fun c => lowL c (χ c) (xiAt c √c)) atTop (𝓝 1) := by
  have h : Tendsto (fun c => ellA (xiAt c √c) / Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c (χ c) (xiAt c √c)) atTop
      (𝓝 (1 / 1)) := tendsto_ellA.div (tendsto_fac_ref hu) one_ne_zero
  rw [div_one] at h
  exact h

/-- `e = fac(ξ₀) c/(c² − χ) → 0`. -/
theorem tendsto_errE : Tendsto (fun c => errE c (χ c) (xiAt c √c)) atTop (𝓝 0) := by
  have h : Tendsto (fun c => Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c (χ c) (xiAt c √c) * (c / (c ^ 2 - χ c))) atTop
      (𝓝 (1 * 0)) := (tendsto_fac_ref hu).mul (tendsto_c_div_sub hu)
  rw [mul_zero] at h
  exact h

/-- `U → 1`. -/
theorem tendsto_upU : Tendsto (fun c => upU c (χ c) (xiAt c 1) (xiAt c √c)) atTop (𝓝 1) := by
  have h : Tendsto (fun c => Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay.fac c (χ c) (xiAt c √c) * (c / √(c ^ 2 - χ c))
      + 4 / π * (c * (xiAt c √c - 1)) * kEdge c (χ c) (xiAt c 1)) atTop
      (𝓝 (1 * 1 + 4 / π * 0 * (4 * exp 1))) :=
    ((tendsto_fac_ref hu).mul (tendsto_c_div_sigma hu)).add
      ((tendsto_c_mul_sub.const_mul (4 / π)).mul (tendsto_kEdge hu))
  rw [show (1 : ℝ) * 1 + 4 / π * 0 * (4 * exp 1) = 1 by ring] at h
  exact h

/-- **The relative error tends to `0`.** -/
theorem tendsto_errR : Tendsto (fun c => errR c (χ c) (xiAt c 1) (xiAt c √c)) atTop (𝓝 0) := by
  have hξ := tendsto_xiAt tendsto_sqrt_div_sq
  have h : Tendsto (fun c => xiAt c √c * (π / 2 * (upU c (χ c) (xiAt c 1) (xiAt c √c)
      - ellA (xiAt c √c) * lowL c (χ c) (xiAt c √c)) + 2 * errE c (χ c) (xiAt c √c))
      / (π / 2 * lowL c (χ c) (xiAt c √c) - errE c (χ c) (xiAt c √c))) atTop
      (𝓝 (1 * (π / 2 * (1 - 1 * 1) + 2 * 0) / (π / 2 * 1 - 0))) :=
    (hξ.mul ((((tendsto_upU hu).sub (tendsto_ellA.mul (tendsto_lowL hu))).const_mul (π / 2)).add
      ((tendsto_errE hu).const_mul 2))).div (((tendsto_lowL hu).const_mul (π / 2)).sub (tendsto_errE hu))
      (by have := pi_pos; intro h; linarith)
  rw [show (1 : ℝ) * (π / 2 * (1 - 1 * 1) + 2 * 0) / (π / 2 * 1 - 0) = 0 by ring] at h
  exact h

/-- **The finite-`c` hypotheses of Cvs.Prolate.ExteriorMassArcsineFinite hold eventually** at `ξ_b = √(1 + 1/c²)`, `ξ₀ = √(1 + √c/c²)`. -/
theorem eventually_hyps (hχ0 : ∀ᶠ c in atTop, 0 ≤ χ c) :
    ∀ᶠ c in atTop, 0 < c ∧ 0 ≤ χ c ∧ χ c < c ^ 2 ∧ 1 < xiAt c 1 ∧ xiAt c 1 ≤ xiAt c √c ∧
      pP (xiAt c 1) * qP c (χ c) (xiAt c 1) < 4 ∧ wP c (χ c) (xiAt c 1) < 2 ∧
      wP c (χ c) (xiAt c √c) < 2 ∧ errE c (χ c) (xiAt c √c) < π / 2 * lowL c (χ c) (xiAt c √c) := by
  have hL : Tendsto (fun c => π / 2 * lowL c (χ c) (xiAt c √c) - errE c (χ c) (xiAt c √c)) atTop
      (𝓝 (π / 2 * 1 - 0)) := ((tendsto_lowL hu).const_mul (π / 2)).sub (tendsto_errE hu)
  rw [mul_one, sub_zero] at hL
  filter_upwards [eventually_ge_atTop 1, hχ0, hu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (tendsto_pq_base hu).eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 4)),
    (tendsto_wP_base hu).eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    (tendsto_wP_ref hu).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2)),
    hL.eventually (lt_mem_nhds (by positivity : (0 : ℝ) < π / 2))]
    with c hc1 hχc hu1 hpq hwb hw0 hden
  have hc : 0 < c := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  refine ⟨hc, hχc, (div_lt_one hc2).mp hu1, one_lt_xiAt hc.ne' one_pos, ?_, hpq, hwb, hw0, by linarith⟩
  unfold xiAt
  apply sqrt_le_sqrt
  have h1 : 1 ≤ √c := by simpa using sqrt_le_sqrt hc1
  have := div_le_div_of_nonneg_right h1 hc2.le
  linarith

end limits

end Cvs.Prolate.ArcsineLawErrorSizes

end
