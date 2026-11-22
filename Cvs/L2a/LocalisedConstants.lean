import Mathlib
import Cvs.L2a.CornerSuprema
import Cvs.L2a.FarFarBound
import Cvs.L2a.FarFarConstantClosedForm
import Cvs.L2a.FarFarProfileClosedForm
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.MiddlePartQStep
import Cvs.L2a.OrbitGapIntegerM
import Cvs.L2a.RampTopQuadratic
import Cvs.L2a.TopCornerConstants

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# LOC's constants: `L_near(2)`, `g_m`, the far collar, the thresholds and `A(c₀) ≥ 0`

`41/2500 ≤ L_near(2) ≤ 17/1000`; `|g_m(2)| ≤ 1/(2(m² − 1)(m² − 4))`, summing to `5/288`;
`g_m(M) = π²L_far/M` and `Σ g_m(M) ≤ 5/(24M)`; the far-collar log bound; antitonicity in `M` and `c`;
the main terms below `R̄ = 0.1238 + r̄_bot` at `X_t = 68`, `X_b = 550`; `A(c) ≥ 0` for `c ≥ 10¹⁶`.
-/
noncomputable section

open Real Finset

namespace Cvs.L2a.LocalisedConstants

open Cvs.L2a.CornerSuprema

/-! ### Taylor bounds for `sin` and `cos` on `x ≥ 0` -/

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y _ => (hf y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [(hf y).deriv]; rw [interior_Ici] at hy; exact hd y (le_of_lt hy))
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  rwa [h0] at this

theorem cos_le_taylor4 {x : ℝ} (hx : 0 ≤ x) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have h := nonneg_of_hasDerivAt (f := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - cos y)
    (f' := fun y => -y + y ^ 3 / 6 + sin y) (fun y => by
      have := ((((hasDerivAt_pow 2 y).div_const 2).const_sub 1).add
        ((hasDerivAt_pow 4 y).div_const 24)).sub (hasDerivAt_cos y)
      exact this.congr_deriv (by norm_num; ring))
    (by simp) (fun y hy => by linarith [sin_ge_sub_cube hy]) hx
  linarith

theorem sin_le_taylor5 {x : ℝ} (hx : 0 ≤ x) : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have h := nonneg_of_hasDerivAt (f := fun y => y - y ^ 3 / 6 + y ^ 5 / 120 - sin y)
    (f' := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - cos y) (fun y => by
      have := ((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
        ((hasDerivAt_pow 5 y).div_const 120)).sub (hasDerivAt_sin y))
      exact this.congr_deriv (by norm_num; ring))
    (by simp) (fun y hy => by linarith [cos_le_taylor4 hy]) hx
  linarith

theorem cos_ge_taylor6 {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ cos x := by
  have h := nonneg_of_hasDerivAt (f := fun y => cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720))
    (f' := fun y => -sin y + (y - y ^ 3 / 6 + y ^ 5 / 120)) (fun y => by
      have := (hasDerivAt_cos y).sub (((((hasDerivAt_pow 2 y).div_const 2).const_sub 1).add
        ((hasDerivAt_pow 4 y).div_const 24)).sub ((hasDerivAt_pow 6 y).div_const 720))
      exact this.congr_deriv (by norm_num; ring))
    (by simp) (fun y hy => by linarith [sin_le_taylor5 hy]) hx
  linarith

theorem sin_ge_taylor7 {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ sin x := by
  have h := nonneg_of_hasDerivAt
    (f := fun y => sin y - (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040))
    (f' := fun y => cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720)) (fun y => by
      have := (hasDerivAt_sin y).sub (((((hasDerivAt_id y).sub ((hasDerivAt_pow 3 y).div_const 6)).add
        ((hasDerivAt_pow 5 y).div_const 120)).sub ((hasDerivAt_pow 7 y).div_const 5040)))
      exact this.congr_deriv (by norm_num; ring))
    (by simp) (fun y hy => by linarith [cos_ge_taylor6 hy]) hx
  linarith

/-! ### Rational enclosures of `π^k` and `√3` -/

theorem pi_lo : (3141592 / 1000000 : ℝ) < π := by
  have := Real.pi_gt_d6; norm_num at this ⊢; linarith

theorem pi_hi : π < (3141593 / 1000000 : ℝ) := by
  have := Real.pi_lt_d6; norm_num at this ⊢; linarith

theorem pi_pow_bounds (k : ℕ) (hk : k ≠ 0) :
    (3141592 / 1000000 : ℝ) ^ k < π ^ k ∧ π ^ k < (3141593 / 1000000 : ℝ) ^ k :=
  ⟨pow_lt_pow_left₀ pi_lo (by norm_num) hk, pow_lt_pow_left₀ pi_hi pi_pos.le hk⟩

theorem sqrt3_lo : (17320508 / 10000000 : ℝ) ≤ √3 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

theorem sqrt3_hi : √3 ≤ 17320509 / 10000000 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-! ### `L_near(2)` -/

theorem bm_two : bm 2 = 4 / √3 := by unfold bm; norm_num

theorem bm_two_sq : bm 2 ^ 2 = 16 / 3 := by rw [bm_sq (by norm_num)]; norm_num

/-- `k = b₂/2 = 2/√3 ∈ [1.1547, 1.1548]`. -/
theorem k_bounds : (11547 / 10000 : ℝ) ≤ bm 2 / 2 ∧ bm 2 / 2 ≤ 11548 / 10000 := by
  rw [bm_two]
  have h0 : 0 < √3 := by positivity
  have := sqrt3_lo; have := sqrt3_hi
  constructor
  · rw [div_div, le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_div, div_le_iff₀ (by positivity)]; nlinarith

/-- The `L_near(2)` integrand `w(t) f₂(t)`. -/
def nearInt (t : ℝ) : ℝ := (1 - Cvs.L2a.FarIntegrationByParts.wF t) * fm 2 t

theorem Lnear_two_eq : Lnear 2 = (π ^ 2)⁻¹ * ∫ t in (1 : ℝ)..2, nearInt t := rfl

theorem fm_two_eq_split (t : ℝ) :
    fm 2 t = 1 / ((2 - t) * (4 - (2 - t))) - bm 2 / 2 / (16 / 3 - t ^ 2) := by
  unfold fm; rw [bm_two_sq]; congr 2; ring

theorem fm_two_nonneg {t : ℝ} (h0 : -2 < t) (ht : t < 2) : 0 ≤ fm 2 t :=
  fm_nonneg (by norm_num) (by nlinarith)

theorem nearInt_nonneg {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) : 0 ≤ nearInt t := by
  unfold nearInt
  have hw : 0 ≤ 1 - Cvs.L2a.FarIntegrationByParts.wF t := by
    linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
  rcases lt_or_eq_of_le h2 with h | h
  · exact mul_nonneg hw (fm_two_nonneg (by linarith) h)
  · rw [h, (Cvs.L2a.FarIntegrationByParts.wF_of_two_le le_rfl).1]; simp

theorem nearInt_le {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) : nearInt t ≤ π ^ 2 := by
  rcases lt_or_eq_of_le h2 with h | h
  · unfold nearInt
    have hw0 : 0 ≤ 1 - Cvs.L2a.FarIntegrationByParts.wF t := by
      linarith [(Cvs.L2a.FarFarBound.wF_bounds t).2.1]
    have hw := Cvs.L2a.RampTopQuadratic.one_sub_wF_le t
    have hu : 0 < 2 - t := by linarith
    have hk : 0 ≤ bm 2 / 2 / (16 / 3 - t ^ 2) := by
      have := (k_bounds).1
      apply div_nonneg (by linarith) (by nlinarith)
    have hf : fm 2 t ≤ 1 / ((2 - t) * (4 - (2 - t))) := by rw [fm_two_eq_split]; linarith
    have hf0 := fm_two_nonneg (by linarith) h
    calc (1 - Cvs.L2a.FarIntegrationByParts.wF t) * fm 2 t ≤ π ^ 2 * (2 - t) ^ 2 * (1 / ((2 - t) * (4 - (2 - t)))) :=
          mul_le_mul hw hf hf0 (by positivity)
      _ = π ^ 2 * ((2 - t) / (4 - (2 - t))) := by field_simp
      _ ≤ π ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by linarith)]; linarith
      _ = π ^ 2 := mul_one _
  · rw [h]; unfold nearInt; rw [(Cvs.L2a.FarIntegrationByParts.wF_of_two_le le_rfl).1]; simp; positivity

theorem measurable_fm_two : Measurable (fm 2) := by
  unfold fm; fun_prop

theorem intervalIntegrable_nearInt {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    IntervalIntegrable nearInt MeasureTheory.volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => π ^ 2) intervalIntegrable_const
    ((continuous_one_sub_wF.measurable.mul measurable_fm_two).aestronglyMeasurable) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_
  rw [Set.uIoc_of_le hab] at ht
  show ‖nearInt t‖ ≤ π ^ 2
  rw [Real.norm_of_nonneg (nearInt_nonneg (by linarith [ht.1]) (by linarith [ht.2]))]
  exact nearInt_le (by linarith [ht.1]) (by linarith [ht.2])

/-- `R = (7/3)(b₂ − 3/2)(b₂ + 1)/((b₂ + 3/2)(b₂ − 1))`, the argument of the `[1, 3/2]` closed form. -/
def rNear : ℝ := 7 / 3 * ((bm 2 - 3 / 2) * (bm 2 + 1)) / ((bm 2 + 3 / 2) * (bm 2 - 1))

theorem bm_two_bounds : (23094010 / 10000000 : ℝ) ≤ bm 2 ∧ bm 2 ≤ 23094011 / 10000000 := by
  have h2 := bm_two_sq
  have h0 : 0 < bm 2 := by rw [bm_two]; positivity
  constructor <;> nlinarith

/-- `∫₁^{3/2} f₂ = (1/4) log R`. -/
theorem integral_near_first : ∫ t in (1 : ℝ)..(3 / 2), nearInt t = Real.log rNear / 4 := by
  obtain ⟨hb1, hb2⟩ := bm_two_bounds
  set b := bm 2 with hbdef
  have hcongr : ∫ t in (1 : ℝ)..(3 / 2), nearInt t = ∫ t in (1 : ℝ)..(3 / 2), fm 2 t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    unfold nearInt; rw [Cvs.L2a.FarFarBound.wF_eq_zero_of_le ht.2]; ring
  set F : ℝ → ℝ := fun t =>
    (Real.log (2 + t) - Real.log (2 - t) - Real.log (b + t) + Real.log (b - t)) / 4 with hF
  have hFd : ∀ x ∈ Set.uIcc (1 : ℝ) (3 / 2), HasDerivAt F (fm 2 x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have h1 : 0 < 2 + x := by linarith [hx.1]
    have h2 : 0 < 2 - x := by linarith [hx.2]
    have h3 : 0 < b + x := by linarith [hx.1]
    have h4 : 0 < b - x := by linarith [hx.2]
    have d1 := ((hasDerivAt_id' x).const_add 2).log h1.ne'
    have d2 := ((hasDerivAt_id' x).const_sub 2).log h2.ne'
    have d3 := ((hasDerivAt_id' x).const_add b).log h3.ne'
    have d4 := ((hasDerivAt_id' x).const_sub b).log h4.ne'
    refine ((((d1.sub d2).sub d3).add d4).div_const 4).congr_deriv ?_
    unfold fm
    rw [← hbdef, show (2 : ℝ) ^ 2 = 4 by norm_num]
    have : (4 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
    have : b ^ 2 - x ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  have hcont : IntervalIntegrable (fm 2) MeasureTheory.volume 1 (3 / 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    unfold fm; rw [← hbdef, bm_two_sq]
    have hc1 : ContinuousOn (fun t : ℝ => (2 : ℝ) ^ 2 - t ^ 2) (Set.Icc 1 (3 / 2)) := by fun_prop
    have hc2 : ContinuousOn (fun t : ℝ => (16 / 3 : ℝ) - t ^ 2) (Set.Icc 1 (3 / 2)) := by fun_prop
    have hn1 : ∀ t ∈ Set.Icc (1 : ℝ) (3 / 2), (2 : ℝ) ^ 2 - t ^ 2 ≠ 0 := by
      intro t ht; rw [Set.mem_Icc] at ht; nlinarith [ht.1, ht.2]
    have hn2 : ∀ t ∈ Set.Icc (1 : ℝ) (3 / 2), (16 / 3 : ℝ) - t ^ 2 ≠ 0 := by
      intro t ht; rw [Set.mem_Icc] at ht; nlinarith [ht.1, ht.2]
    apply ContinuousOn.sub
    · exact ContinuousOn.div₀ (f := fun _ => (1 : ℝ)) continuousOn_const hc1 hn1
    · exact ContinuousOn.div₀ (f := fun _ => b / 2) continuousOn_const hc2 hn2
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hFd hcont]
  simp only [hF]
  have hR : Real.log rNear = Real.log 7 - Real.log 3 + Real.log (b - 3 / 2) + Real.log (b + 1)
      - Real.log (b + 3 / 2) - Real.log (b - 1) := by
    unfold rNear
    rw [← hbdef, Real.log_div (by apply mul_ne_zero (by norm_num); apply mul_ne_zero <;> linarith)
      (by apply mul_ne_zero <;> linarith), Real.log_mul (by norm_num)
      (by apply mul_ne_zero <;> linarith), Real.log_mul (by linarith) (by linarith),
      Real.log_mul (by linarith) (by linarith), Real.log_div (by norm_num) (by norm_num)]
    ring
  rw [hR, show (2 : ℝ) + 3 / 2 = 7 / 2 by norm_num, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num,
    show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one,
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

theorem rNear_bounds : (1253027 / 1000000 : ℝ) ≤ rNear ∧ rNear ≤ 1253028 / 1000000 := by
  obtain ⟨hb1, hb2⟩ := bm_two_bounds
  set b := bm 2 with hbdef
  have hD : 0 < (b + 3 / 2) * (b - 1) := by apply mul_pos <;> linarith
  have hm : 0 ≤ (b - 23094010 / 10000000) * (23094011 / 10000000 - b) := by
    apply mul_nonneg <;> linarith
  unfold rNear
  rw [← hbdef]
  constructor
  · rw [le_div_iff₀ hD]; nlinarith
  · rw [div_le_iff₀ hD]; nlinarith

/-- `∫₁^{3/2} f₂ ∈ [0.05638, 0.05640]`. -/
theorem integral_near_first_bounds :
    (5638 / 100000 : ℝ) ≤ ∫ t in (1 : ℝ)..(3 / 2), nearInt t ∧
      ∫ t in (1 : ℝ)..(3 / 2), nearInt t ≤ 5640 / 100000 := by
  rw [integral_near_first]
  obtain ⟨hlo, hhi⟩ := rNear_bounds
  have hR0 : 0 < rNear := lt_of_lt_of_le (by norm_num) hlo
  have l1 : Real.log (1253027 / 1000000) ≤ Real.log rNear := Real.log_le_log (by norm_num) hlo
  have l2 : Real.log rNear ≤ Real.log (1253028 / 1000000) := Real.log_le_log hR0 hhi
  have s1 := Real.abs_log_sub_add_sum_range_le (x := 1 - 1253027 / 1000000) (by norm_num) 8
  have s2 := Real.abs_log_sub_add_sum_range_le (x := 1 - 1253028 / 1000000) (by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at s1 s2
  norm_num at s1 s2
  have a1 := (abs_le.1 s1).1
  have a2 := (abs_le.1 s2).2
  constructor <;> linarith

/-- `w(2 − u) f₂(2 − u) = sin²(πu) f₂(2 − u)` on `[0, 1/2]`. -/
theorem nearInt_sub {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    nearInt (2 - u) = sin (π * u) ^ 2 * fm 2 (2 - u) := by
  unfold nearInt
  rw [Cvs.L2a.RampTopQuadratic.one_sub_wF_eq ⟨by linarith, by linarith⟩]
  ring_nf

/-- The lower polynomial on `[0, 1/2]`. -/
def cL : ℕ → ℝ
  | 0 => 0
  | 1 => (1 / 4 : ℝ) * π ^ 2
  | 2 => (-2009 / 2500 : ℝ) * π ^ 2
  | 3 => (-1 / 12 : ℝ) * π ^ 4 + (88574233 / 54760000 : ℝ) * π ^ 2
  | 4 => (-4235229 / 3422500 : ℝ) * π ^ 2 + (2009 / 7500 : ℝ) * π ^ 4
  | 5 => (-88574233 / 164280000 : ℝ) * π ^ 4 + (1 / 90 : ℝ) * π ^ 6
  | 6 => (-2009 / 56250 : ℝ) * π ^ 6 + (1411743 / 3422500 : ℝ) * π ^ 4
  | 7 => (-1 / 1260 : ℝ) * π ^ 8 + (88574233 / 1232100000 : ℝ) * π ^ 6
  | 8 => (-470581 / 8556250 : ℝ) * π ^ 6 + (287 / 112500 : ℝ) * π ^ 8
  | 9 => (-88574233 / 17249400000 : ℝ) * π ^ 8 + (41 / 1209600 : ℝ) * π ^ 10
  | 10 => (-11767 / 108000000 : ℝ) * π ^ 10 + (470581 / 119787500 : ℝ) * π ^ 8
  | 11 => (-1 / 1209600 : ℝ) * π ^ 12 + (3631543553 / 16559424000000 : ℝ) * π ^ 10
  | 12 => (-19293821 / 114996000000 : ℝ) * π ^ 10 + (287 / 108000000 : ℝ) * π ^ 12
  | 13 => (-88574233 / 16559424000000 : ℝ) * π ^ 12 + (1 / 101606400 : ℝ) * π ^ 14
  | 14 => (-41 / 1296000000 : ℝ) * π ^ 14 + (470581 / 114996000000 : ℝ) * π ^ 12
  | 15 => (88574233 / 1390991616000000 : ℝ) * π ^ 14
  | 16 => (-470581 / 9659664000000 : ℝ) * π ^ 14
  | _ => 0

/-- The upper polynomial on `[0, 1/2]`. -/
def cU : ℕ → ℝ
  | 0 => 0
  | 1 => (1 / 4 : ℝ) * π ^ 2
  | 2 => (-1088742090911 / 1411581610000 : ℝ) * π ^ 2
  | 3 => (-1 / 12 : ℝ) * π ^ 4 + (9861481975297 / 4940535635000 : ℝ) * π ^ 2
  | 4 => (-295189540272 / 88223850625 : ℝ) * π ^ 2 + (1088742090911 / 4234744830000 : ℝ) * π ^ 4
  | 5 => (-9861481975297 / 14821606905000 : ℝ) * π ^ 4 + (1 / 90 : ℝ) * π ^ 6
      + (225152089344 / 88223850625 : ℝ) * π ^ 2
  | 6 => (-1088742090911 / 31760586225000 : ℝ) * π ^ 6 + (98396513424 / 88223850625 : ℝ) * π ^ 4
  | 7 => (-75050696448 / 88223850625 : ℝ) * π ^ 4 + (-1 / 1440 : ℝ) * π ^ 8
      + (9861481975297 / 111162051787500 : ℝ) * π ^ 6
  | 8 => (-65597675616 / 441119253125 : ℝ) * π ^ 6 + (1088742090911 / 508169379600000 : ℝ) * π ^ 8
  | 9 => (-9861481975297 / 1778592828600000 : ℝ) * π ^ 8 + (1 / 57600 : ℝ) * π ^ 10
      + (50033797632 / 441119253125 : ℝ) * π ^ 6
  | 10 => (-1088742090911 / 20326775184000000 : ℝ) * π ^ 10 + (4099854726 / 441119253125 : ℝ) * π ^ 8
  | 11 => (-3127112352 / 441119253125 : ℝ) * π ^ 8 + (9861481975297 / 71143713144000000 : ℝ) * π ^ 10
  | 12 => (-2049927363 / 8822385062500 : ℝ) * π ^ 10
  | 13 => (390889044 / 2205596265625 : ℝ) * π ^ 10
  | _ => 0

/-- `h(t) = 1/(16/3 − t²) ≤ p(t)`, the Hermite quadratic at `3/2` (double) and `2`. -/
theorem h_le_p {t : ℝ} (h1 : 3 / 2 ≤ t) (h2 : t ≤ 2) :
    1 / (16 / 3 - t ^ 2) ≤ 1467 / 1369 * t ^ 2 - 3969 / 1369 * t + 12387 / 5476 := by
  have hD : 0 < 16 / 3 - t ^ 2 := by nlinarith
  rw [div_le_iff₀ hD]
  have e : (1467 / 1369 * t ^ 2 - 3969 / 1369 * t + 12387 / 5476) * (16 / 3 - t ^ 2) - 1
      = 9 * (2 - t) * (2 * t - 3) ^ 2 * (163 * t + 374) / 5476 := by ring
  have : 0 ≤ 9 * (2 - t) * (2 * t - 3) ^ 2 * (163 * t + 374) / 5476 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
  linarith

/-- `h(t) ≥ T₃(t)`, the cubic Taylor polynomial at `7/4`. -/
theorem T3_le_h {t : ℝ} (h1 : 0 ≤ t) (h2 : t ≤ 2) :
    311980032 / 141158161 * t ^ 3 - 1462853376 / 141158161 * t ^ 2 + 2349478656 / 141158161 * t
      - 1241455776 / 141158161 ≤ 1 / (16 / 3 - t ^ 2) := by
  have hD : 0 < 16 / 3 - t ^ 2 := by nlinarith
  rw [le_div_iff₀ hD]
  have e : (311980032 / 141158161 * t ^ 3 - 1462853376 / 141158161 * t ^ 2 + 2349478656 / 141158161 * t
      - 1241455776 / 141158161) * (16 / 3 - t ^ 2) - 1
      = -(9 * (4 * t - 7) ^ 4 * (135408 * t + 312937) / 141158161) := by ring
  have : 0 ≤ 9 * (4 * t - 7) ^ 4 * (135408 * t + 312937) / 141158161 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (by positivity) (by linarith)
  linarith

theorem nearInt_sub_ge {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    ∑ n ∈ range 17, cL n * u ^ n ≤ nearInt (2 - u) := by
  have hsum : ∑ n ∈ range 17, cL n * u ^ n =
      π ^ 2 * u * (1 - (π * u) ^ 2 / 6 + (π * u) ^ 4 / 120 - (π * u) ^ 6 / 5040) ^ 2
          * (1 / 4 + u / 16 + u ^ 2 / 64)
        - π ^ 2 * u ^ 2 * (1 - (π * u) ^ 2 / 6 + (π * u) ^ 4 / 120 - (π * u) ^ 6 / 5040) ^ 2
          * (11548 / 10000) * (1467 / 1369 * (2 - u) ^ 2 - 3969 / 1369 * (2 - u) + 12387 / 5476) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cL]; ring
  rw [hsum, nearInt_sub hu0 hu1]
  rcases eq_or_lt_of_le hu0 with h0 | hpos
  · subst h0; simp
  set x := π * u with hx
  have hx0 : 0 < x := by positivity
  have hxπ : x ≤ π / 2 := by rw [hx]; nlinarith [pi_pos]
  have hx16 : x ≤ 16 / 10 := by linarith [pi_hi]
  set T := 1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040 with hT
  have hT0 : 0 ≤ T := by
    have h2 : x ^ 2 ≤ 256 / 100 := by nlinarith
    have h6 : x ^ 6 ≤ 17 := by
      have : x ^ 6 = (x ^ 2) ^ 3 := by ring
      rw [this]; calc (x ^ 2) ^ 3 ≤ (256 / 100) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
        _ ≤ 17 := by norm_num
    nlinarith [sq_nonneg (x ^ 2)]
  have hsl : x * T ≤ sin x := by rw [hT]; have := sin_ge_taylor7 hx0.le; linarith
  have hsx0 : 0 ≤ x * T := mul_nonneg hx0.le hT0
  have hsin2 : (x * T) ^ 2 ≤ sin x ^ 2 := pow_le_pow_left₀ hsx0 hsl 2
  have hu4 : 0 < 4 - u := by linarith
  have hfm := fm_two_nonneg (t := 2 - u) (by linarith) (by linarith)
  have hsplit := fm_two_eq_split (2 - u)
  rw [show (2 : ℝ) - (2 - u) = u by ring] at hsplit
  have hk := (k_bounds).2
  have hk0 : 0 ≤ bm 2 / 2 := by linarith [(k_bounds).1]
  have hp := h_le_p (t := 2 - u) (by linarith) (by linarith)
  have hD : 0 < 16 / 3 - (2 - u) ^ 2 := by nlinarith
  have hinv : 1 / 4 + u / 16 + u ^ 2 / 64 ≤ 1 / (4 - u) := by
    rw [le_div_iff₀ hu4]; nlinarith [pow_pos hpos 3]
  have hh0 : 0 ≤ 1 / (16 / 3 - (2 - u) ^ 2) := by positivity
  have hkh : bm 2 / 2 / (16 / 3 - (2 - u) ^ 2) ≤
      11548 / 10000 * (1467 / 1369 * (2 - u) ^ 2 - 3969 / 1369 * (2 - u) + 12387 / 5476) := by
    rw [div_eq_mul_one_div (bm 2 / 2)]
    calc bm 2 / 2 * (1 / (16 / 3 - (2 - u) ^ 2)) ≤ 11548 / 10000 * (1 / (16 / 3 - (2 - u) ^ 2)) :=
          mul_le_mul_of_nonneg_right hk hh0
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  have hfm_lo : (1 / u) * (1 / 4 + u / 16 + u ^ 2 / 64)
      - 11548 / 10000 * (1467 / 1369 * (2 - u) ^ 2 - 3969 / 1369 * (2 - u) + 12387 / 5476) ≤ fm 2 (2 - u) := by
    rw [hsplit]
    have : (1 / u) * (1 / 4 + u / 16 + u ^ 2 / 64) ≤ 1 / (u * (4 - u)) := by
      rw [show 1 / (u * (4 - u)) = (1 / u) * (1 / (4 - u)) by field_simp]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    linarith
  calc π ^ 2 * u * T ^ 2 * (1 / 4 + u / 16 + u ^ 2 / 64)
        - π ^ 2 * u ^ 2 * T ^ 2 * (11548 / 10000)
          * (1467 / 1369 * (2 - u) ^ 2 - 3969 / 1369 * (2 - u) + 12387 / 5476)
      = (x * T) ^ 2 * ((1 / u) * (1 / 4 + u / 16 + u ^ 2 / 64)
          - 11548 / 10000 * (1467 / 1369 * (2 - u) ^ 2 - 3969 / 1369 * (2 - u) + 12387 / 5476)) := by
        rw [hx]; field_simp
    _ ≤ (x * T) ^ 2 * fm 2 (2 - u) := mul_le_mul_of_nonneg_left hfm_lo (sq_nonneg _)
    _ ≤ sin x ^ 2 * fm 2 (2 - u) := mul_le_mul_of_nonneg_right hsin2 hfm

theorem nearInt_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    nearInt (2 - u) ≤ ∑ n ∈ range 14, cU n * u ^ n := by
  have hsum : ∑ n ∈ range 14, cU n * u ^ n =
      π ^ 2 * u * (1 - (π * u) ^ 2 / 6 + (π * u) ^ 4 / 120) ^ 2 * (1 / 4 + u / 16 + u ^ 2 / 56)
        - π ^ 2 * u ^ 2 * (1 - (π * u) ^ 2 / 6 + (π * u) ^ 4 / 120) ^ 2 * (11547 / 10000)
          * (311980032 / 141158161 * (2 - u) ^ 3 - 1462853376 / 141158161 * (2 - u) ^ 2
            + 2349478656 / 141158161 * (2 - u) - 1241455776 / 141158161) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cU]; ring
  rw [hsum, nearInt_sub hu0 hu1]
  rcases eq_or_lt_of_le hu0 with h0 | hpos
  · subst h0; simp
  set x := π * u with hx
  have hx0 : 0 < x := by positivity
  have hxπ : x ≤ π := by rw [hx]; nlinarith [pi_pos]
  set T := 1 - x ^ 2 / 6 + x ^ 4 / 120 with hT
  have hsin0 : 0 ≤ sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0.le hxπ
  have hsu : sin x ≤ x * T := by rw [hT]; have := sin_le_taylor5 hx0.le; linarith
  have hsin2 : sin x ^ 2 ≤ (x * T) ^ 2 := pow_le_pow_left₀ hsin0 hsu 2
  have hu4 : 0 < 4 - u := by linarith
  have hfm := fm_two_nonneg (t := 2 - u) (by linarith) (by linarith)
  have hsplit := fm_two_eq_split (2 - u)
  rw [show (2 : ℝ) - (2 - u) = u by ring] at hsplit
  have hk := (k_bounds).1
  have hT3 := T3_le_h (t := 2 - u) (by linarith) (by linarith)
  have hD : 0 < 16 / 3 - (2 - u) ^ 2 := by nlinarith
  have hinv : 1 / (4 - u) ≤ 1 / 4 + u / 16 + u ^ 2 / 56 := by
    rw [div_le_iff₀ hu4]; nlinarith [pow_pos hpos 3]
  have hh0 : 0 ≤ 1 / (16 / 3 - (2 - u) ^ 2) := by positivity
  have hkh : 11547 / 10000 * (311980032 / 141158161 * (2 - u) ^ 3 - 1462853376 / 141158161 * (2 - u) ^ 2
            + 2349478656 / 141158161 * (2 - u) - 1241455776 / 141158161)
      ≤ bm 2 / 2 / (16 / 3 - (2 - u) ^ 2) := by
    rw [div_eq_mul_one_div (bm 2 / 2)]
    calc _ ≤ 11547 / 10000 * (1 / (16 / 3 - (2 - u) ^ 2)) := mul_le_mul_of_nonneg_left hT3 (by norm_num)
      _ ≤ bm 2 / 2 * (1 / (16 / 3 - (2 - u) ^ 2)) := mul_le_mul_of_nonneg_right hk hh0
  have hfm_hi : fm 2 (2 - u) ≤ (1 / u) * (1 / 4 + u / 16 + u ^ 2 / 56)
      - 11547 / 10000 * (311980032 / 141158161 * (2 - u) ^ 3 - 1462853376 / 141158161 * (2 - u) ^ 2
            + 2349478656 / 141158161 * (2 - u) - 1241455776 / 141158161) := by
    rw [hsplit]
    have : 1 / (u * (4 - u)) ≤ (1 / u) * (1 / 4 + u / 16 + u ^ 2 / 56) := by
      rw [show 1 / (u * (4 - u)) = (1 / u) * (1 / (4 - u)) by field_simp]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    linarith
  calc sin x ^ 2 * fm 2 (2 - u) ≤ (x * T) ^ 2 * fm 2 (2 - u) := mul_le_mul_of_nonneg_right hsin2 hfm
    _ ≤ (x * T) ^ 2 * ((1 / u) * (1 / 4 + u / 16 + u ^ 2 / 56)
      - 11547 / 10000 * (311980032 / 141158161 * (2 - u) ^ 3 - 1462853376 / 141158161 * (2 - u) ^ 2
            + 2349478656 / 141158161 * (2 - u) - 1241455776 / 141158161)) :=
        mul_le_mul_of_nonneg_left hfm_hi (sq_nonneg _)
    _ = _ := by rw [hx]; field_simp

/-- `∫_a^b Σ cₙuⁿ = Σ cₙ(b^{n+1} − a^{n+1})/(n + 1)`. -/
theorem integral_poly (c : ℕ → ℝ) (N : ℕ) (a b : ℝ) :
    ∫ u in a..b, ∑ n ∈ range N, c n * u ^ n = ∑ n ∈ range N, c n * ((b ^ (n + 1) - a ^ (n + 1)) / (n + 1)) := by
  rw [intervalIntegral.integral_finsetSum (f := fun n u => c n * u ^ n)
    (fun n _ => (by fun_prop : Continuous fun u : ℝ => c n * u ^ n).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]

/-- `∫_{3/2}^2 w f₂ ∈ [0.10574, 0.11094]`. -/
theorem integral_near_second_bounds :
    (10574 / 100000 : ℝ) ≤ ∫ t in (3 / 2 : ℝ)..2, nearInt t ∧
      ∫ t in (3 / 2 : ℝ)..2, nearInt t ≤ 11094 / 100000 := by
  have hsub : ∫ t in (3 / 2 : ℝ)..2, nearInt t = ∫ u in (0 : ℝ)..(1 / 2), nearInt (2 - u) := by
    rw [intervalIntegral.integral_comp_sub_left nearInt 2]; norm_num
  have hI : IntervalIntegrable (fun u => nearInt (2 - u)) MeasureTheory.volume 0 (1 / 2) := by
    have := (intervalIntegrable_nearInt (a := 3 / 2) (b := 2) (by norm_num) (by norm_num) le_rfl).comp_sub_left 2
    norm_num at this; exact this.symm
  have hpL : IntervalIntegrable (fun u => ∑ n ∈ range 17, cL n * u ^ n) MeasureTheory.volume 0 (1 / 2) :=
    (continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
  have hpU : IntervalIntegrable (fun u => ∑ n ∈ range 14, cU n * u ^ n) MeasureTheory.volume 0 (1 / 2) :=
    (continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_pow n)).intervalIntegrable _ _
  have hlo := intervalIntegral.integral_mono_on (by norm_num) hpL hI fun u hu => nearInt_sub_ge hu.1 hu.2
  have hhi := intervalIntegral.integral_mono_on (by norm_num) hI hpU fun u hu => nearInt_sub_le hu.1 hu.2
  rw [integral_poly] at hlo hhi
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cL, cU] at hlo hhi
  norm_num at hlo hhi
  obtain ⟨p2a, p2b⟩ := pi_pow_bounds 2 (by norm_num)
  obtain ⟨p4a, p4b⟩ := pi_pow_bounds 4 (by norm_num)
  obtain ⟨p6a, p6b⟩ := pi_pow_bounds 6 (by norm_num)
  obtain ⟨p8a, p8b⟩ := pi_pow_bounds 8 (by norm_num)
  obtain ⟨p10a, p10b⟩ := pi_pow_bounds 10 (by norm_num)
  obtain ⟨p12a, p12b⟩ := pi_pow_bounds 12 (by norm_num)
  obtain ⟨p14a, p14b⟩ := pi_pow_bounds 14 (by norm_num)
  norm_num at p2a p2b p4a p4b p6a p6b p8a p8b p10a p10b p12a p12b p14a p14b
  rw [hsub]
  constructor <;> linarith

/-- **`L_near(2)` enclosed**: `41/2500 ≤ L_near(2) ≤ 17/1000`. -/
theorem Lnear_two_bounds : (41 / 2500 : ℝ) ≤ Lnear 2 ∧ Lnear 2 ≤ 17 / 1000 := by
  have hsplit : ∫ t in (1 : ℝ)..2, nearInt t =
      (∫ t in (1 : ℝ)..(3 / 2), nearInt t) + ∫ t in (3 / 2 : ℝ)..2, nearInt t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_nearInt le_rfl (by norm_num) (by norm_num))
      (intervalIntegrable_nearInt (by norm_num) (by norm_num) le_rfl)).symm
  obtain ⟨a1, a2⟩ := integral_near_first_bounds
  obtain ⟨b1, b2⟩ := integral_near_second_bounds
  obtain ⟨p2a, p2b⟩ := pi_pow_bounds 2 (by norm_num)
  norm_num at p2a p2b
  have hπ2 : 0 < π ^ 2 := by positivity
  rw [Lnear_two_eq, hsplit, ← div_eq_inv_mul]
  constructor
  · rw [le_div_iff₀ hπ2]; nlinarith
  · rw [div_le_iff₀ hπ2]; nlinarith

/-! ### `g_m(t) = ∫_1^{Y(m)} dv/(t² − m²v²)`: the value at `t = 2` and the sum `5/288` -/

open Cvs.L2a.OrbitGapIntegerM (Ymax) in
/-- `g_m(t) = ∫_1^{Y(m)} dv/(t² − m²v²)`, the oscillation kernel of the bottom band integral. -/
def gm (m t : ℝ) : ℝ := ∫ v in (1 : ℝ)..Cvs.L2a.OrbitGapIntegerM.Ymax m, 1 / (t ^ 2 - m ^ 2 * v ^ 2)

theorem one_le_Ymax {m : ℝ} (hm : 1 < m) : 1 ≤ Cvs.L2a.OrbitGapIntegerM.Ymax m := by
  have := Cvs.L2a.TopCornerConstants.dY_nonneg hm
  unfold Cvs.L2a.TopCornerConstants.dY at this; linarith

/-- `|g_m(2)| ≤ ΔY(m)/(m² − 4)`. -/
theorem abs_gm_two_le_dY {m : ℝ} (hm : 2 < m) : |gm m 2| ≤ Cvs.L2a.TopCornerConstants.dY m / (m ^ 2 - 4) := by
  have hY := one_le_Ymax (by linarith : (1 : ℝ) < m)
  have hm4 : 0 < m ^ 2 - 4 := by nlinarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := Cvs.L2a.OrbitGapIntegerM.Ymax m)
    (C := 1 / (m ^ 2 - 4)) (f := fun v => 1 / ((2 : ℝ) ^ 2 - m ^ 2 * v ^ 2)) (by
      intro v hv
      rw [Set.uIoc_of_le hY] at hv
      have hv1 : 1 < v := hv.1
      have hmv : m ^ 2 ≤ m ^ 2 * v ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ v ^ 2 by nlinarith) (sq_nonneg m)]
      rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_neg (by nlinarith), neg_sub]
      exact one_div_le_one_div_of_le hm4 (by linarith))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ Cvs.L2a.OrbitGapIntegerM.Ymax m - 1)] at h
  unfold gm Cvs.L2a.TopCornerConstants.dY
  calc _ ≤ 1 / (m ^ 2 - 4) * (Cvs.L2a.OrbitGapIntegerM.Ymax m - 1) := h
    _ = _ := by ring

/-- **`|g_m(2)| ≤ 1/(2(m² − 1)(m² − 4))`** for `m > 2`. -/
theorem abs_gm_two_le {m : ℝ} (hm : 2 < m) : |gm m 2| ≤ 1 / (2 * (m ^ 2 - 1) * (m ^ 2 - 4)) := by
  have hm4 : 0 < m ^ 2 - 4 := by nlinarith
  refine (abs_gm_two_le_dY hm).trans ?_
  have := Cvs.L2a.TopCornerConstants.dY_lt (by linarith : (1 : ℝ) < m)
  calc Cvs.L2a.TopCornerConstants.dY m / (m ^ 2 - 4) ≤ 1 / (2 * (m ^ 2 - 1)) / (m ^ 2 - 4) :=
        div_le_div_of_nonneg_right this.le hm4.le
    _ = _ := by rw [div_div]

/-! ### `g_m(M) = π²L_far(m, M)/M` and `Σ g_m(M) ≤ 5/(24M)` -/

theorem m_mul_Ymax (m : ℝ) : m * Cvs.L2a.OrbitGapIntegerM.Ymax m = bm m := by
  unfold Cvs.L2a.OrbitGapIntegerM.Ymax bm; ring

/-! ### Antitonicity in `M` -/

/-! ### The far collar: `g₀`, `β₀` and the log bound -/

/-- `g₀ = 3 − 4/√3`, the least gap `M − b_m` over `2 ≤ m ≤ M − 1`. -/
def g0 : ℝ := 3 - 4 / √3

/-- `β₀ = 4/√3 − 2 + g₀/2`. -/
def beta0 : ℝ := 4 / √3 - 2 + g0 / 2

theorem one_sub_beta0 : 1 - beta0 = g0 / 2 := by unfold beta0 g0; ring

theorem g0_bounds : (69 / 100 : ℝ) ≤ g0 ∧ g0 ≤ 691 / 1000 := by
  have h1 := sqrt3_lo; have h2 := sqrt3_hi
  have h0 : 0 < √3 := by positivity
  unfold g0
  constructor
  · have : 4 / √3 ≤ 231 / 100 := by rw [div_le_iff₀ h0]; nlinarith
    linarith
  · have : 2309 / 1000 ≤ 4 / √3 := by rw [le_div_iff₀ h0]; nlinarith
    linarith

theorem beta0_bounds : (65 / 100 : ℝ) ≤ beta0 ∧ beta0 ≤ 66 / 100 := by
  have := one_sub_beta0; have := g0_bounds; constructor <;> linarith

/-- `b_m − m ≤ b₂ − 2 = 4/√3 − 2` for `m ≥ 2`. -/
theorem bm_sub_self_le {m : ℝ} (hm : 2 ≤ m) : bm m - m ≤ 4 / √3 - 2 := by
  set s := √(m ^ 2 - 1) with hs
  set r := √3 with hr
  have hs2 : s ^ 2 = m ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hr2 : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < r := by positivity
  have hsr : r ≤ s := Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 < s := lt_of_lt_of_le hr0 hsr
  have h2s : r * m ≤ 2 * s := by nlinarith
  have hb : bm m - m = m / (s * (m + s)) := by
    unfold bm; rw [← hs]
    field_simp
    nlinarith
  have hr' : 4 / r - 2 = 2 / (r * (2 + r)) := by
    field_simp; nlinarith
  rw [hb, hr', div_le_div_iff₀ (by positivity) (by positivity)]
  have : r * m * (2 + r) ≤ 2 * s * (m + s) := by
    have h1 : r * m * (2 + r) ≤ r * m * (m + s) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have h2 : r * m * (m + s) ≤ 2 * s * (m + s) := mul_le_mul_of_nonneg_right h2s (by positivity)
    linarith
  nlinarith

/-- **Lemma `g₀`**: `g₀ ≤ M − b_m` for `2 ≤ m ≤ M − 1`. -/
theorem g0_le_sub_bm {m M : ℝ} (hm : 2 ≤ m) (hM : m + 1 ≤ M) : g0 ≤ M - bm m := by
  have := bm_sub_self_le hm; unfold g0; linarith

/-- The far collar `δ_m = min(δ, g₀/(2m))`. -/
def deltaM (δ m : ℝ) : ℝ := min δ (g0 / (2 * m))

/-- `M − b′_m ≥ (M − m) − β₀`. -/
theorem sub_bprime_ge {δ m : ℝ} (M : ℝ) (hm : 2 ≤ m) :
    (M - m) - beta0 ≤ M - (bm m + m * deltaM δ m) := by
  have h1 := bm_sub_self_le hm
  have h2 : m * deltaM δ m ≤ g0 / 2 := by
    have : deltaM δ m ≤ g0 / (2 * m) := min_le_right _ _
    have hm0 : 0 < m := by linarith
    calc m * deltaM δ m ≤ m * (g0 / (2 * m)) := mul_le_mul_of_nonneg_left this hm0.le
      _ = g0 / 2 := by field_simp
  unfold beta0; linarith

/-- `1/y ≤ (log y − log x)/(y − x)` for `0 < x < y`. -/
theorem inv_le_log_sub {x y : ℝ} (hx : 0 < x) (hxy : x < y) : 1 / y ≤ (Real.log y - Real.log x) / (y - x) := by
  have hy : 0 < y := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at hl
  rw [le_div_iff₀ (by linarith)]
  have : (y - x) * (1 / y) = 1 - x / y := by field_simp
  linarith

/-- `Σ_{3 ≤ j < n} 1/(j − β₀) ≤ log((n − 1 − β₀)/(2 − β₀))` for `n ≥ 3`. -/
theorem sum_inv_beta0_le {n : ℕ} (hn : 3 ≤ n) :
    ∑ j ∈ Ico 3 n, 1 / ((j : ℝ) - beta0) ≤ Real.log (((n : ℝ) - 1 - beta0) / (2 - beta0)) := by
  obtain ⟨b1, b2⟩ := beta0_bounds
  set g : ℕ → ℝ := fun j => -Real.log ((j : ℝ) - 1 - beta0) with hg
  have hterm : ∀ j ∈ Ico 3 n, 1 / ((j : ℝ) - beta0) ≤ g j - g (j + 1) := by
    intro j hj
    simp only [mem_Ico] at hj
    have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj.1
    have := inv_le_log_sub (x := (j : ℝ) - 1 - beta0) (y := (j : ℝ) - beta0) (by linarith) (by linarith)
    rw [show (j : ℝ) - beta0 - ((j : ℝ) - 1 - beta0) = 1 by ring, div_one] at this
    simp only [hg]; push_cast
    rw [show (j : ℝ) + 1 - 1 - beta0 = j - beta0 by ring]
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [sum_Ico_telescope g hn]
  simp only [hg]
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.log_div (by linarith) (by linarith)]
  push_cast
  rw [show (3 : ℝ) - 1 - beta0 = 2 - beta0 by ring]
  ring_nf
  linarith

/-- `Σ_{1 ≤ j < K − 1} 1/(j − β₀) ≤ 2/g₀ + 1/(2 − β₀) + log((X − 2 − β₀)/(2 − β₀))` for `K ≤ X`, `X ≥ 4`. -/
theorem sum_inv_beta0_full {K X : ℕ} (hKX : K ≤ X) (hX : 4 ≤ X) :
    ∑ j ∈ Ico 1 (K - 1), 1 / ((j : ℝ) - beta0)
      ≤ 2 / g0 + 1 / (2 - beta0) + Real.log (((X : ℝ) - 2 - beta0) / (2 - beta0)) := by
  obtain ⟨b1, b2⟩ := beta0_bounds
  obtain ⟨g1, g2⟩ := g0_bounds
  have hXr : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log (((X : ℝ) - 2 - beta0) / (2 - beta0)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have h1 : 1 / ((1 : ℝ) - beta0) = 2 / g0 := by rw [one_sub_beta0]; field_simp
  have h2 : 0 < 1 / (2 - beta0) := by apply div_pos one_pos; linarith
  have h3 : 0 < 2 / g0 := div_pos two_pos (by linarith)
  rcases Nat.lt_or_ge K 3 with hK | hK
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; linarith
  rcases Nat.lt_or_ge K 4 with hK4 | hK4
  · have : K = 3 := by omega
    subst this
    simp only [show 3 - 1 = 2 by rfl]
    rw [show Ico 1 2 = {1} by rfl, Finset.sum_singleton]; push_cast
    rw [h1]; linarith
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < K - 1), Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < K - 1)]
  push_cast
  rw [h1]
  have hS := sum_inv_beta0_le (n := K - 1) (by omega)
  have hK1 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hK1] at hS
  have hKr : (4 : ℝ) ≤ K := by exact_mod_cast hK4
  have hKX' : (K : ℝ) ≤ X := by exact_mod_cast hKX
  have hmono : Real.log (((K : ℝ) - 1 - 1 - beta0) / (2 - beta0)) ≤ Real.log (((X : ℝ) - 2 - beta0) / (2 - beta0)) := by
    apply Real.log_le_log (by apply div_pos <;> linarith)
    apply div_le_div_of_nonneg_right _ (by linarith); linarith
  linarith

/-! ### The main terms at the thresholds `X_t = 68`, `X_b = 550` -/

theorem r1globBar_le_one {κ θ : ℝ} (hκ1 : κ ≤ 1) (hθ : 0 ≤ θ) {M : ℕ} (hM : 3 ≤ M) :
    r1globBar κ θ M ≤ r1globBar 1 θ M := by
  unfold r1globBar
  have hN := Nbar_nonneg hθ M hM
  have hs : √κ ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hκ1
  rw [Real.sqrt_one]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  nlinarith [Real.sqrt_nonneg κ]

theorem Tbar_le_one {κ : ℝ} (hκ1 : κ ≤ 1) {m : ℝ} (hm : 3 ≤ m) : Tbar κ m ≤ Tbar 1 m := by
  have h1 := Tbar_nonneg (κ := 1) hm
  unfold Tbar at h1 ⊢
  rw [Real.sqrt_one] at h1 ⊢
  have hs : √κ ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hκ1
  have hB : 0 ≤ 1 / (m - 2) + (√(thetaT m))⁻¹ * (√(1 - 1 / (m - 1 / 2) ^ 2))⁻¹ * (2 * √2 / exp 1)
      * (√(m - 1 / 2))⁻¹ := by nlinarith
  exact mul_le_mul_of_nonneg_right (by linarith) hB

/-- `(√x)⁻¹ ≤ c` from `1/c² ≤ x`. -/
theorem inv_sqrt_le {x c : ℝ} (hc : 0 < c) (h : 1 / c ^ 2 ≤ x) : (√x)⁻¹ ≤ c := by
  have h1 : 1 / c ≤ √x := by
    rw [Real.le_sqrt (by positivity) (le_trans (by positivity) h)]; rwa [div_pow, one_pow]
  rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) h1) hc, ← one_div]; exact h1

theorem harmonic_65_69 : (harmonic 65 : ℝ) ≤ 47593 / 10000 ∧ (harmonic 69 : ℝ) ≤ 48186 / 10000 := by
  constructor <;> (simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; push_cast; norm_num)

/-- **`X_t = 68`**: `r̄₁^glob(68) ≤ 0.1238` at `κ = 1`, `θ = Θ₂`. -/
theorem r1globBar_68_le : r1globBar 1 (Theta 2) 68 ≤ 1238 / 10000 := by
  unfold r1globBar Nbar
  rw [Real.sqrt_one, show (68 : ℕ) - 3 = 65 by rfl, show (68 : ℕ) + 1 = 69 by rfl]
  obtain ⟨h65, h69⟩ := harmonic_65_69
  have hθ := Theta_two_le
  have h11 : √11 ≤ 331663 / 100000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hS : √11 / 8 * ((harmonic 65 : ℝ) + harmonic 69 - 25 / 12)
      ≤ 331663 / 100000 / 8 * (47593 / 10000 + 48186 / 10000 - 25 / 12) := by
    calc √11 / 8 * ((harmonic 65 : ℝ) + harmonic 69 - 25 / 12)
        ≤ √11 / 8 * (47593 / 10000 + 48186 / 10000 - 25 / 12) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := by gcongr
  have hden : (6799 / 100 : ℝ) ≤ √((68 : ℕ) ^ 2 - 1 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)]
  nlinarith

/-- **`X_b = 550`**: `T̄_bot(550) + r̄₁^glob(551) ≤ 0.1238` at `κ = 1`, `θ = Θ₂`. -/
theorem Tbar_r1glob_550_le : Tbar 1 550 + r1globBar 1 (Theta 2) 551 ≤ 1238 / 10000 := by
  have i1 : (√(thetaT 550))⁻¹ ≤ 10006 / 10000 := inv_sqrt_le (by norm_num) (by unfold thetaT; norm_num)
  have i2 : (√(1 - 1 / ((550 : ℝ) - 1 / 2) ^ 2))⁻¹ ≤ 100001 / 100000 :=
    inv_sqrt_le (by norm_num) (by norm_num)
  have i4 : (√((550 : ℝ) - 1 / 2))⁻¹ ≤ 42661 / 1000000 := inv_sqrt_le (by norm_num) (by norm_num)
  have he := Real.exp_one_gt_d9
  have h2 : √2 ≤ 1414214 / 1000000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have i3 : 2 * √2 / exp 1 ≤ 104053 / 100000 := by
    rw [div_le_iff₀ (by positivity)]; norm_num at he; nlinarith
  have P : (√(thetaT 550))⁻¹ * (√(1 - 1 / ((550 : ℝ) - 1 / 2) ^ 2))⁻¹ * (2 * √2 / exp 1)
      * (√((550 : ℝ) - 1 / 2))⁻¹ ≤ 10006 / 10000 * (100001 / 100000) * (104053 / 100000) * (42661 / 1000000) := by
    gcongr
  have e : Tbar 1 550 = 2 * (1 / 548 + (√(thetaT 550))⁻¹ * (√(1 - 1 / ((550 : ℝ) - 1 / 2) ^ 2))⁻¹
      * (2 * √2 / exp 1) * (√((550 : ℝ) - 1 / 2))⁻¹) := by
    unfold Tbar; rw [Real.sqrt_one]; norm_num
  have hT : Tbar 1 550 ≤ 2 * (1 / 548 + 10006 / 10000 * (100001 / 100000) * (104053 / 100000) * (42661 / 1000000)) := by
    rw [e]; linarith
  have hH : ∀ n : ℕ, n ≤ 1024 → (harmonic n : ℝ) ≤ 1 + 10 * (6931471808 / 10000000000) := by
    intro n hn
    refine (harmonic_le_one_add_log n).trans ?_
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp; positivity
    have : Real.log n ≤ Real.log 1024 := Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hn)
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow] at this
    have := Real.log_two_lt_d9
    norm_num at this ⊢; push_cast at *; linarith
  have hθ := Theta_two_le
  have h11 : √11 ≤ 331663 / 100000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hR : r1globBar 1 (Theta 2) 551 ≤ 2 * (20158 / 10000 / 2 + 331663 / 100000 / 8
      * (2 * (1 + 10 * (6931471808 / 10000000000)) - 25 / 12)) / (55099 / 100) := by
    unfold r1globBar Nbar
    rw [Real.sqrt_one, show (551 : ℕ) - 3 = 548 by rfl, show (551 : ℕ) + 1 = 552 by rfl]
    have a := hH 548 (by norm_num)
    have b := hH 552 (by norm_num)
    have hS : √11 / 8 * ((harmonic 548 : ℝ) + harmonic 552 - 25 / 12)
        ≤ 331663 / 100000 / 8 * (2 * (1 + 10 * (6931471808 / 10000000000)) - 25 / 12) := by
      calc √11 / 8 * ((harmonic 548 : ℝ) + harmonic 552 - 25 / 12)
          ≤ √11 / 8 * (2 * (1 + 10 * (6931471808 / 10000000000)) - 25 / 12) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ _ := by gcongr
    have hden : (55099 / 100 : ℝ) ≤ √((551 : ℕ) ^ 2 - 1 : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hN0 : 0 ≤ 2 * 1 * (Theta 2 / 2 + √11 / 8 * ((harmonic 548 : ℝ) + harmonic 552 - 25 / 12)) := by
      have := Nbar_nonneg (θ := Theta 2) (by linarith [Theta_two_ge]) 551 (by norm_num)
      unfold Nbar at this
      rw [show (551 : ℕ) - 3 = 548 by rfl, show (551 : ℕ) + 1 = 552 by rfl] at this
      linarith
    calc 2 * 1 * (Theta 2 / 2 + √11 / 8 * ((harmonic 548 : ℝ) + harmonic 552 - 25 / 12)) / √((551 : ℕ) ^ 2 - 1 : ℝ)
        ≤ 2 * 1 * (Theta 2 / 2 + √11 / 8 * ((harmonic 548 : ℝ) + harmonic 552 - 25 / 12)) / (55099 / 100) :=
          div_le_div_of_nonneg_left hN0 (by norm_num) hden
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by norm_num)
  norm_num at hT hR
  linarith

/-- The top main term: `R̄₁(M)` below `X_t = 68`, `r̄₁^glob(M)` from `68` on. -/
def r1main (κ : ℝ) (M : ℕ) : ℝ := if M < 68 then R1bar (Theta 2) M else r1globBar κ (Theta 2) M

/-- The bottom main term: `r_bot,550(M)`, plus `T̄_bot(550)` beyond `X_b = 550`. -/
def botMain (κ : ℝ) (M : ℕ) : ℝ :=
  √(∑ m ∈ Ico 2 (min M 550), (Lnear m + Lfar m M)) + if 550 < M then Tbar κ 550 else 0

/-- `R̄ = 0.1238 + r̄_bot`. -/
def Rbar : ℝ := 1238 / 10000 + √rbarBotSq

/-- **The threshold checks**: for `κ ≤ 1` and every `M ≥ 3`, the main terms stay below `R̄`. -/
theorem main_le_Rbar {κ : ℝ} (hκ1 : κ ≤ 1) {M : ℕ} (hM : 3 ≤ M) :
    r1main κ M + botMain κ M ≤ Rbar := by
  have hθ0 : 0 ≤ Theta 2 := by linarith [Theta_two_ge]
  have hstep := step_of_ge Theta_two_ge
  have hbot : √(∑ m ∈ Ico 2 (min M 550), (Lnear m + Lfar m M)) ≤ √rbarBotSq :=
    Real.sqrt_le_sqrt (rbot_le M (min M 550) (min_le_left _ _))
  unfold r1main botMain Rbar
  split_ifs with h1 h2 h2
  · omega
  · have := (R1bar_Theta_le_four M hM).trans R1bar_four_le; linarith
  · have a := r1glob_antitone (κ := κ) hstep (by norm_num : 4 ≤ 551) (show 551 ≤ M by omega)
    have b := r1globBar_le_one hκ1 hθ0 (M := 551) (by norm_num)
    have c := Tbar_le_one hκ1 (m := 550) (by norm_num)
    have d := Tbar_r1glob_550_le
    linarith
  · have a := r1glob_antitone (κ := κ) hstep (by norm_num : 4 ≤ 68) (show 68 ≤ M by omega)
    have b := r1globBar_le_one hκ1 hθ0 (M := 68) (by norm_num)
    have d := r1globBar_68_le
    linarith

/-- `r̄_bot ≤ 0.20192`. -/
theorem sqrt_rbarBotSq_le : √rbarBotSq ≤ 20192 / 100000 := by
  have h := rbarBotSq_le
  have hL := Lnear_two_bounds.2
  obtain ⟨p2a, -⟩ := pi_pow_bounds 2 (by norm_num)
  norm_num at p2a
  have hπ : 0 < π ^ 2 := by positivity
  have a : 3 / (4 * π ^ 2) ≤ 3 / (4 * (98696 / 10000)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have b : 5 / (24 * π ^ 2) ≤ 5 / (24 * (98696 / 10000)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num at a b ⊢
  linarith

/-- **`R̄ ≤ 0.3258`**. -/
theorem Rbar_le : Rbar ≤ 3258 / 10000 := by
  unfold Rbar; linarith [sqrt_rbarBotSq_le]

/-! ### Antitonicity in `c` -/

/-- `κ_ι = 12J/(πc)`. -/
def kappaI (J c : ℝ) : ℝ := 12 * J / (π * c)

/-- `0 ≤ κ_ι ≤ 1` for `0 ≤ J ≤ c/4 + 1` and `c ≥ 85`. -/
theorem kappaI_mem {J c : ℝ} (hc : 85 ≤ c) (hJ0 : 0 ≤ J) (hJ : J ≤ c / 4 + 1) :
    0 ≤ kappaI J c ∧ kappaI J c ≤ 1 := by
  have hπ := pi_lo
  unfold kappaI
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]; nlinarith

open Cvs.L2a.MiddlePartQStep in
theorem KS_nonneg : 0 ≤ KS₁ 5 ∧ 0 ≤ KS₂ 5 ∧ 0 ≤ KS₃ 5 := by
  unfold KS₁ KS₂ KS₃; refine ⟨by positivity, by positivity, by positivity⟩

/-! ### The certificate at `c₀ = 10¹⁶` -/

theorem sqrt_pi_bounds : (17724 / 10000 : ℝ) ≤ √π ∧ √π ≤ 17725 / 10000 := by
  have := pi_lo; have := pi_hi
  constructor
  · rw [Real.le_sqrt (by norm_num) pi_pos.le]; norm_num; linarith
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num; linarith

theorem Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  have h := Real.Gamma_add_one (s := 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, Real.Gamma_one_half_eq] at h
  rw [h]; ring

theorem Gamma_five_halves : Real.Gamma (5 / 2) = 3 * √π / 4 := by
  have h := Real.Gamma_add_one (s := 3 / 2) (by norm_num)
  rw [show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num, Gamma_three_halves] at h
  rw [h]; ring

theorem Gamma_seven_halves : Real.Gamma (7 / 2) = 15 * √π / 8 := by
  have h := Real.Gamma_add_one (s := 5 / 2) (by norm_num)
  rw [show (5 / 2 : ℝ) + 1 = 7 / 2 by norm_num, Gamma_five_halves] at h
  rw [h]; ring

theorem Gamma_nine_halves : Real.Gamma (9 / 2) = 105 * √π / 16 := by
  have h := Real.Gamma_add_one (s := 7 / 2) (by norm_num)
  rw [show (7 / 2 : ℝ) + 1 = 9 / 2 by norm_num, Gamma_seven_halves] at h
  rw [h]; ring

/-- `Γ(1/4) ≤ 2(1 + √π/2)`, from convexity of `Γ` on `[1, 3/2]`. -/
theorem Gamma_quarter_le : Real.Gamma (1 / 4) ≤ 2 * (1 + √π / 2) := by
  have h := Real.convexOn_Gamma.2 (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by norm_num : (3 / 2 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * 1 + 1 / 2 * (3 / 2) = 5 / 4 by norm_num, Real.Gamma_one, Gamma_three_halves] at h
  have h2 := Real.Gamma_add_one (s := 1 / 4) (by norm_num)
  rw [show (1 / 4 : ℝ) + 1 = 5 / 4 by norm_num] at h2
  linarith

/-- `Γ(3/4) ≤ (2/3)(√π/2 + 1)`, from convexity of `Γ` on `[3/2, 2]`. -/
theorem Gamma_three_quarters_le : Real.Gamma (3 / 4) ≤ 2 / 3 * (√π / 2 + 1) := by
  have h := Real.convexOn_Gamma.2 (by norm_num : (3 / 2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * (3 / 2) + 1 / 2 * 2 = 7 / 4 by norm_num, Real.Gamma_two, Gamma_three_halves] at h
  have h2 := Real.Gamma_add_one (s := 3 / 4) (by norm_num)
  rw [show (3 / 4 : ℝ) + 1 = 7 / 4 by norm_num] at h2
  linarith

theorem Gamma_seven_quarters_le : Real.Gamma (7 / 4) ≤ 1 := by
  have h := Real.convexOn_Gamma.2 (by norm_num : (3 / 2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * (3 / 2) + 1 / 2 * 2 = 7 / 4 by norm_num, Real.Gamma_two, Gamma_three_halves] at h
  have := sqrt_pi_bounds.2
  linarith

/-- `x^{k/4} ≥ q` from `q⁴ ≤ x^k`. -/
theorem le_rpow_quarter {x q : ℝ} {k : ℕ} (hx : 0 ≤ x) (hq : 0 ≤ q) (h : q ^ 4 ≤ x ^ k) :
    q ≤ x ^ ((k : ℝ) / 4) := by
  have hy : 0 ≤ x ^ ((k : ℝ) / 4) := Real.rpow_nonneg hx _
  have e : (x ^ ((k : ℝ) / 4)) ^ 4 = x ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; push_cast
    rw [show (k : ℝ) / 4 * 4 = k by ring, Real.rpow_natCast]
  rw [← e] at h
  exact (pow_le_pow_iff_left₀ hq hy (by norm_num)).1 h

/-- `x^{k/4} ≤ q` from `x^k ≤ q⁴`. -/
theorem rpow_quarter_le {x q : ℝ} {k : ℕ} (hx : 0 ≤ x) (hq : 0 ≤ q) (h : x ^ k ≤ q ^ 4) :
    x ^ ((k : ℝ) / 4) ≤ q := by
  have hy : 0 ≤ x ^ ((k : ℝ) / 4) := Real.rpow_nonneg hx _
  have e : (x ^ ((k : ℝ) / 4)) ^ 4 = x ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; push_cast
    rw [show (k : ℝ) / 4 * 4 = k by ring, Real.rpow_natCast]
  rw [← e] at h
  exact (pow_le_pow_iff_left₀ hy hq (by norm_num)).1 h

open Cvs.L2a.MiddlePartQStep in
/-- **`K₁(5) ≤ 128`**, the leading strip coefficient: `r_S(c, 5c) = K₁c^{−1/4} + ⋯`. -/
theorem KS1_le : KS₁ 5 ≤ 128 := by
  have hπ1 := pi_lo; have hπ2 := pi_hi
  obtain ⟨sp1, sp2⟩ := sqrt_pi_bounds
  have a1 : √(2 / π) ≤ 7979 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ pi_pos]; nlinarith
  have a2 : 16 * π ^ 2 / 9 ≤ 17546 / 1000 := by nlinarith
  have a3 : √(Real.Gamma (7 / 2)) ≤ 18231 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num), Gamma_seven_halves]; nlinarith
  have a4 : (3 / 2 : ℝ) ^ (-(7 / 4 : ℝ)) ≤ 4919 / 10000 := by
    rw [Real.rpow_neg (by norm_num)]
    have : (10000 / 4919 : ℝ) ≤ (3 / 2 : ℝ) ^ (((7 : ℕ) : ℝ) / 4) := le_rpow_quarter (by norm_num) (by norm_num) (by norm_num)
    rw [show (((7 : ℕ) : ℝ) / 4) = 7 / 4 by norm_num] at this
    rw [inv_le_comm₀ (lt_of_lt_of_le (by norm_num) this) (by norm_num)]
    rw [show ((4919 / 10000 : ℝ))⁻¹ = 10000 / 4919 by norm_num]; exact this
  have a5 : (1 / 5 : ℝ) ^ (1 / 4 : ℝ) ≤ 6688 / 10000 := by
    have := rpow_quarter_le (x := 1 / 5) (q := 6688 / 10000) (k := 1) (by norm_num) (by norm_num) (by norm_num)
    rwa [show (((1 : ℕ) : ℝ) / 4) = 1 / 4 by norm_num] at this
  have a6 : Real.Gamma (1 / 4) ≤ 37726 / 10000 := by have := Gamma_quarter_le; linarith
  unfold KS₁
  calc √(2 / π) * (16 * π ^ 2 / 9) * (4 * √(Real.Gamma (7 / 2)) * (3 / 2 : ℝ) ^ (-(7 / 4 : ℝ))
        * ((1 / 5) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4)))
      ≤ 7979 / 10000 * (17546 / 1000) * (4 * (18231 / 10000) * (4919 / 10000) * (6688 / 10000 * (37726 / 10000))) := by
        gcongr
    _ ≤ 128 := by norm_num

open Cvs.L2a.MiddlePartQStep in
theorem KS23_le : KS₂ 5 ≤ 2000 ∧ KS₃ 5 ≤ 500 := by
  have hπ2 := pi_hi
  obtain ⟨-, sp2⟩ := sqrt_pi_bounds
  have a1 : √(2 / π) ≤ 1 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ pi_pos]; linarith [pi_gt_three]
  have a2 : 16 * π ^ 2 / 9 ≤ 18 := by nlinarith [pi_pos]
  have g52 : √(Real.Gamma (5 / 2)) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num), Gamma_five_halves]; nlinarith
  have g92 : √(Real.Gamma (9 / 2)) ≤ 4 := by
    rw [Real.sqrt_le_left (by norm_num), Gamma_nine_halves]; nlinarith
  have g34 : Real.Gamma (3 / 4) ≤ 2 := by have := Gamma_three_quarters_le; nlinarith
  have g74 := Gamma_seven_quarters_le
  have r1 : (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have r2 : (3 / 2 : ℝ) ^ (-(9 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have r3 : (1 / 5 : ℝ) ^ (3 / 4 : ℝ) ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  have r4 : (1 / 5 : ℝ) ^ (7 / 4 : ℝ) ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  unfold KS₂ KS₃
  constructor
  · calc √(2 / π) * (16 * π ^ 2 / 9) * (10 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
          * ((1 / 5) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4))
        + 8 * √(Real.Gamma (9 / 2)) * (3 / 2 : ℝ) ^ (-(9 / 4 : ℝ)) * ((1 / 5) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4)))
        ≤ 1 * 18 * (10 * 2 * 1 * (1 * 2) + 8 * 4 * 1 * (1 * 2)) := by gcongr
      _ ≤ 2000 := by norm_num
  · calc √(2 / π) * (16 * π ^ 2 / 9) * (2 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
          * ((1 / 5) ^ (3 / 4 : ℝ) * Real.Gamma (3 / 4))
        + 8 * √(Real.Gamma (5 / 2)) * (3 / 2 : ℝ) ^ (-(5 / 4 : ℝ)) * ((1 / 5) ^ (7 / 4 : ℝ) * Real.Gamma (7 / 4)))
        ≤ 1 * 18 * (2 * 2 * 1 * (1 * 2) + 8 * 2 * 1 * (1 * 1)) := by gcongr
      _ ≤ 500 := by norm_num

/-- `c^{−1/4} ≤ 10⁻⁴` for `c ≥ 10¹⁶`. -/
theorem rpow_quarter_c0 {c : ℝ} (hc : 10 ^ 16 ≤ c) : c ^ (-(1 / 4 : ℝ)) ≤ 1 / 10 ^ 4 := by
  have h : ((10 : ℝ) ^ 16) ^ (-(1 / 4 : ℝ)) = 1 / 10 ^ 4 := by
    rw [show ((10 : ℝ) ^ 16) = (10 ^ 4) ^ 4 by norm_num, Real.rpow_neg (by positivity),
      show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
    norm_num
  rw [← h]; exact Real.rpow_le_rpow_of_nonpos (by positivity) hc (by norm_num)

open Cvs.L2a.MiddlePartQStep in
/-- **`r_S(c, 5c) ≤ 0.01281`** for `c ≥ 10¹⁶`. -/
theorem rStrip_le_c0 {c : ℝ} (hc : 10 ^ 16 ≤ c) : rStrip c (5 * c) ≤ 1281 / 100000 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  rw [rStrip_eq hc0 (by norm_num)]
  set x := c ^ (-(1 / 4 : ℝ)) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hc0.le _
  have hx1 : x ≤ 1 / 10 ^ 4 := rpow_quarter_c0 hc
  have e3 : c ^ (-(3 / 4 : ℝ)) = x ^ 3 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have e7 : c ^ (-(7 / 4 : ℝ)) = x ^ 7 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  rw [e3, e7]
  obtain ⟨k1, k2, k3⟩ := KS_nonneg
  have b1 := KS1_le
  obtain ⟨b2, b3⟩ := KS23_le
  have p3 : x ^ 3 ≤ (1 / 10 ^ 4) ^ 3 := pow_le_pow_left₀ hx0 hx1 3
  have p7 : x ^ 7 ≤ (1 / 10 ^ 4) ^ 7 := pow_le_pow_left₀ hx0 hx1 7
  have t1 : KS₁ 5 * x ≤ 128 * (1 / 10 ^ 4) := mul_le_mul b1 hx1 hx0 (by norm_num)
  have t2 : KS₂ 5 * x ^ 3 ≤ 2000 * (1 / 10 ^ 4) ^ 3 := mul_le_mul b2 p3 (by positivity) (by norm_num)
  have t3 : KS₃ 5 * x ^ 7 ≤ 500 * (1 / 10 ^ 4) ^ 7 := mul_le_mul b3 p7 (by positivity) (by norm_num)
  norm_num at t1 t2 t3 ⊢
  linarith

open Cvs.L2a.MiddlePartQStep in
/-- **`r_D(c) ≤ 10⁻⁵`** for `c ≥ 10¹⁶`. -/
theorem rOne_le_c0 {c : ℝ} (hc : 10 ^ 16 ≤ c) : rOne c ≤ 1 / 10 ^ 5 := by
  have hc1 : 1 ≤ c := le_trans (by norm_num) hc
  refine (rOne_le hc1).trans ?_
  have hs : (10 : ℝ) ^ 8 ≤ √c := by
    rw [Real.le_sqrt (by positivity) (by linarith)]; norm_num; linarith
  have a1 : √(2 / π) ≤ 8 / 10 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ pi_pos]; nlinarith [pi_lo]
  have h2 : √2 ≤ 14143 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have eF : KF 1 = (15 / 11) ^ 2 * (16 / 3 + 364 / 45 + 64 / 45) + (15 / 11) ^ 3 * (128 / 9 + 256 / 75) := by
    unfold KF K2far K3far; norm_num
  have eN : KN 1 = (49 / 40) ^ 2 * (27 / 5 + 2619 / 400 + 243 / 200) + (49 / 40) ^ 3 * (243 / 20 + 243 / 125) := by
    unfold KN K2near K3near; norm_num
  rw [eF, eN, div_le_iff₀ (by positivity)]
  have hK : √(2 / π) * (8 * ((15 / 11) ^ 2 * (16 / 3 + 364 / 45 + 64 / 45) + (15 / 11) ^ 3 * (128 / 9 + 256 / 75))
      + 2 * √2 * ((49 / 40) ^ 2 * (27 / 5 + 2619 / 400 + 243 / 200) + (49 / 40) ^ 3 * (243 / 20 + 243 / 125)))
      ≤ 8 / 10 * (8 * ((15 / 11) ^ 2 * (16 / 3 + 364 / 45 + 64 / 45) + (15 / 11) ^ 3 * (128 / 9 + 256 / 75))
      + 2 * (14143 / 10000) * ((49 / 40) ^ 2 * (27 / 5 + 2619 / 400 + 243 / 200) + (49 / 40) ^ 3 * (243 / 20 + 243 / 125))) := by
    gcongr
  have : (8 / 10 : ℝ) * (8 * ((15 / 11) ^ 2 * (16 / 3 + 364 / 45 + 64 / 45) + (15 / 11) ^ 3 * (128 / 9 + 256 / 75))
      + 2 * (14143 / 10000) * ((49 / 40) ^ 2 * (27 / 5 + 2619 / 400 + 243 / 200) + (49 / 40) ^ 3 * (243 / 20 + 243 / 125)))
      ≤ 1 / 10 ^ 5 * 10 ^ 8 := by norm_num
  nlinarith

open Cvs.L2a.FarFarConstantClosedForm in
/-- **`C_η(10¹⁶) ≤ 200`**, from crude bounds on `β₁, …, β₄`. -/
theorem cEta_c0_le : cEtaClosed (10 ^ 16) ≤ 200 := by
  have hπ1 := pi_lo; have hπ2 := pi_hi
  have l3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have l5 : Real.log 5 ≤ 4 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
  have l3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have l5' : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have l15 : Real.log (15 / 11) ≤ 4 / 11 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 15 / 11)]
  have l15' : 0 ≤ Real.log (15 / 11) := Real.log_nonneg (by norm_num)
  have s5 : √5 ≤ 22361 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have s5' : 0 ≤ √5 := Real.sqrt_nonneg 5
  have hlam : lamL ≤ 9 := by
    unfold lamL
    have a := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (29 + 12 * √5) / 11 by positivity)
    have b := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 + 4 * √5 by positivity)
    linarith
  have hlam0 := lamL_nonneg
  have j1 : jJ₁ ≤ 26 / 10 := by unfold jJ₁; nlinarith [mul_le_mul s5 hlam hlam0 (by norm_num)]
  have j2 : jJ₂ ≤ 32 / 10 := by unfold jJ₂; nlinarith [mul_le_mul s5 hlam hlam0 (by norm_num)]
  have j3 : jJ₃ ≤ 44 / 10 := by unfold jJ₃; nlinarith [mul_le_mul s5 hlam hlam0 (by norm_num)]
  obtain ⟨j1', j2', j3'⟩ := jJ_nonneg
  obtain ⟨n2, n3, n4, n5, n6, n7⟩ := νB_facts
  have n2u : νB₂ ≤ 107 / 100 := by
    unfold νB₂; rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have n2l : 65 / 100 ≤ νB₂ := by
    unfold νB₂; rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  have n3u : νB₃ ≤ 1 := by unfold νB₃; rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have n4u : νB₄ ≤ 1 := by unfold νB₄; rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have n7u : νB₇ ≤ 1 := by unfold νB₇; rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have n5u : νB₅ ≤ 2 := by
    unfold νB₅
    have : √(1937 / 10890 + 1 / 8 * Real.log (15 / 11)) ≤ 48 / 100 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    nlinarith [Real.sqrt_nonneg (1937 / 10890 + 1 / 8 * Real.log (15 / 11))]
  have n6u : νB₆ ≤ 2 := by
    unfold νB₆
    have : √(1277 / 10890 - 1 / 8 * Real.log (15 / 11)) ≤ 35 / 100 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    nlinarith [Real.sqrt_nonneg (1277 / 10890 - 1 / 8 * Real.log (15 / 11))]
  have s23 : √(2 / 3 : ℝ) ≤ 1 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have s23' : 0 ≤ √(2 / 3 : ℝ) := Real.sqrt_nonneg _
  have b1 : βB₁ ≤ 14 := by
    unfold βB₁; rw [Real.sqrt_le_left (by norm_num)]
    have e1 : π ^ 2 * jJ₁ ≤ 99 / 10 * (26 / 10) := mul_le_mul (by nlinarith) j1 j1' (by norm_num)
    have e2 : 8 * π * νB₂ * jJ₂ ≤ 8 * (315 / 100) * (107 / 100) * (32 / 10) := by
      apply mul_le_mul _ j2 j2' (by norm_num)
      apply mul_le_mul _ n2u n2.le (by norm_num)
      linarith
    have e3 : 16 * νB₂ ^ 2 * jJ₃ ≤ 16 * (107 / 100) ^ 2 * (44 / 10) := by
      apply mul_le_mul _ j3 j3' (by norm_num)
      have := pow_le_pow_left₀ n2.le n2u 2; linarith
    linarith
  have b2 : βB₂ ≤ 700 := by
    unfold βB₂
    calc √(2 / 3 : ℝ) * (2000 / 3 * νB₃) ≤ 1 * (2000 / 3 * 1) := by gcongr
      _ ≤ 700 := by norm_num
  have b3 : βB₃ ≤ 2000 := by
    unfold βB₃
    have q1 : 10 * (6 * νB₅ ^ 2 + 2 * νB₆ ^ 2 + π ^ 4) / (9 * π) ≤ 1320 / 27 := by
      have p4 : π ^ 4 ≤ 100 := by have := (pi_pow_bounds 4 (by norm_num)).2; norm_num at this; linarith
      have : νB₅ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ n5 n5u 2
      have : νB₆ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ n6 n6u 2
      have hn : 10 * (6 * νB₅ ^ 2 + 2 * νB₆ ^ 2 + π ^ 4) ≤ 1320 := by linarith
      calc 10 * (6 * νB₅ ^ 2 + 2 * νB₆ ^ 2 + π ^ 4) / (9 * π) ≤ 1320 / (9 * π) :=
            div_le_div_of_nonneg_right hn (by positivity)
        _ ≤ 1320 / 27 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have q2 : 5 * (4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄) ^ 2 / (2 * νB₂) ≤ 1620 / (13 / 10) := by
      have : 4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄ ≤ 18 := by linarith
      have h0 : 0 ≤ 4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄ := by positivity
      have h2 := pow_le_pow_left₀ h0 this 2
      have hn : 5 * (4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄) ^ 2 ≤ 1620 := by linarith
      calc 5 * (4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄) ^ 2 / (2 * νB₂) ≤ 1620 / (2 * νB₂) :=
            div_le_div_of_nonneg_right hn (by positivity)
        _ ≤ 1620 / (13 / 10) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have hin : 0 ≤ 10 * (6 * νB₅ ^ 2 + 2 * νB₆ ^ 2 + π ^ 4) / (9 * π) + 400 / 9 * νB₆
        + 5 * (4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄) ^ 2 / (2 * νB₂) := by positivity
    have : √(2 / 3 : ℝ) * (10 * (6 * νB₅ ^ 2 + 2 * νB₆ ^ 2 + π ^ 4) / (9 * π) + 400 / 9 * νB₆
        + 5 * (4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄) ^ 2 / (2 * νB₂))
        ≤ 1 * (10 * (6 * νB₅ ^ 2 + 2 * νB₆ ^ 2 + π ^ 4) / (9 * π) + 400 / 9 * νB₆
        + 5 * (4 * νB₃ + 4 * νB₅ + 2 * νB₄ + 4 * νB₄) ^ 2 / (2 * νB₂)) := mul_le_mul_of_nonneg_right s23 hin
    have q3 : 400 / 9 * νB₆ ≤ 400 / 9 * 2 := by linarith
    have : (1320 / 27 : ℝ) + 400 / 9 * 2 + 1620 / (13 / 10) ≤ 2000 := by norm_num
    linarith
  have b4 : βB₄ ≤ 300 := by
    unfold βB₄
    calc √(2 / 3 : ℝ) * (8000 / 27 * νB₇) ≤ 1 * (8000 / 27 * 1) := by gcongr
      _ ≤ 300 := by norm_num
  obtain ⟨b1', b2', b3', b4'⟩ := βB_nonneg
  unfold cEtaClosed Cvs.L2a.FarFarProfileClosedForm.cEtaSym
  have hsum : βB₁ + βB₂ / (10 ^ 16 : ℝ) + βB₃ / ((10 : ℝ) ^ 16) ^ 2 + βB₄ / ((10 : ℝ) ^ 16) ^ 3 ≤ 15 := by
    have : βB₂ / (10 ^ 16 : ℝ) ≤ 700 / 10 ^ 16 := div_le_div_of_nonneg_right b2 (by positivity)
    have : βB₃ / ((10 : ℝ) ^ 16) ^ 2 ≤ 2000 / ((10 : ℝ) ^ 16) ^ 2 := div_le_div_of_nonneg_right b3 (by positivity)
    have : βB₄ / ((10 : ℝ) ^ 16) ^ 3 ≤ 300 / ((10 : ℝ) ^ 16) ^ 3 := div_le_div_of_nonneg_right b4 (by positivity)
    norm_num at *
    linarith
  have h0 : 0 ≤ βB₁ + βB₂ / (10 ^ 16 : ℝ) + βB₃ / ((10 : ℝ) ^ 16) ^ 2 + βB₄ / ((10 : ℝ) ^ 16) ^ 3 := by positivity
  have hsq := pow_le_pow_left₀ h0 hsum 2
  have h2π : 2 / π ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  calc 2 / π * (βB₁ + βB₂ / (10 ^ 16 : ℝ) + βB₃ / ((10 : ℝ) ^ 16) ^ 2 + βB₄ / ((10 : ℝ) ^ 16) ^ 3) ^ 2
      ≤ 2 / 3 * 15 ^ 2 := mul_le_mul h2π hsq (by positivity) (by norm_num)
    _ ≤ 200 := by norm_num

/-- **`η(c) ≤ 10⁻⁶`** for `c ≥ 10¹⁶`, with `η(c)² = C_η(10¹⁶)/c`. -/
theorem eta_le_c0 {c : ℝ} (hc : 10 ^ 16 ≤ c) :
    √(Cvs.L2a.FarFarConstantClosedForm.cEtaClosed (10 ^ 16) / c) ≤ 1 / 10 ^ 6 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  have h := cEta_c0_le
  rw [Real.sqrt_le_left (by positivity), div_le_iff₀ hc0]
  have : (1 / 10 ^ 6 : ℝ) ^ 2 * 10 ^ 16 ≤ (1 / 10 ^ 6) ^ 2 * c := mul_le_mul_of_nonneg_left hc (by positivity)
  norm_num at this h ⊢; linarith

end Cvs.L2a.LocalisedConstants
