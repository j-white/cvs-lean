import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The quintic step

`S(u) = u³(10 − 15u + 6u²)` on `[0, 1]`, `0` below and `1` above: a `C²` step with `S(1 − u) = 1 − S(u)`. Its first
three derivatives have exact `L²` norms `ς₁² = 10/7`, `ς₂² = 120/7`, `ς₃² = 720`, with `∫₀¹ S² = 181/462`, and exact
sups `|S′| ≤ 15/8`, `|S″| ≤ 10/√3`, both attained.
-/

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace Cvs.Upstream.QuinticSmoothStep

/-! ### Gluing three pieces at `0` and `1` -/

/-- Three pieces glued at `0` and `1`: `a` on `(−∞, 0]`, `b` on `(0, 1)`, `c` on `[1, ∞)`. -/
def glue (a b c : ℝ → ℝ) (u : ℝ) : ℝ := if u ≤ 0 then a u else if 1 ≤ u then c u else b u

theorem glue_of_nonpos (a b c : ℝ → ℝ) {u : ℝ} (hu : u ≤ 0) : glue a b c u = a u := by
  simp [glue, hu]

theorem glue_of_one_le (a b c : ℝ → ℝ) {u : ℝ} (hu : 1 ≤ u) : glue a b c u = c u := by
  simp [glue, show ¬ u ≤ 0 by linarith, hu]

theorem glue_of_mem_Ioo (a b c : ℝ → ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1) : glue a b c u = b u := by
  simp [glue, not_le.2 hu.1, not_le.2 hu.2]

/-- A one-sided derivative from each side is a derivative. -/
theorem hasDerivAt_of_Iic_Ici {f : ℝ → ℝ} {d x : ℝ} (hl : HasDerivWithinAt f d (Iic x) x)
    (hr : HasDerivWithinAt f d (Ici x) x) : HasDerivAt f d x := by
  have h := hl.union hr
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h

/-- Away from `0` and `1` the glued function has the derivative of the active piece. -/
theorem hasDerivAt_glue_of_ne {a b c a' b' c' : ℝ → ℝ} (ha : ∀ u, HasDerivAt a (a' u) u)
    (hb : ∀ u, HasDerivAt b (b' u) u) (hc : ∀ u, HasDerivAt c (c' u) u) {x : ℝ} (h0 : x ≠ 0)
    (h1 : x ≠ 1) : HasDerivAt (glue a b c) (glue a' b' c' x) x := by
  rcases lt_or_gt_of_ne h0 with hx | hx
  · rw [glue_of_nonpos _ _ _ hx.le]
    refine (ha x).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with u hu using glue_of_nonpos _ _ _ (le_of_lt hu)
  rcases lt_or_gt_of_ne h1 with hx1 | hx1
  · rw [glue_of_mem_Ioo _ _ _ ⟨hx, hx1⟩]
    refine (hb x).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx hx1] with u hu using glue_of_mem_Ioo _ _ _ hu
  · rw [glue_of_one_le _ _ _ hx1.le]
    refine (hc x).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx1] with u hu using glue_of_one_le _ _ _ (le_of_lt hu)

/-- If the pieces and their derivatives match at `0` and `1`, the glued function is differentiable everywhere with
the glued derivative. -/
theorem hasDerivAt_glue {a b c a' b' c' : ℝ → ℝ} (ha : ∀ u, HasDerivAt a (a' u) u)
    (hb : ∀ u, HasDerivAt b (b' u) u) (hc : ∀ u, HasDerivAt c (c' u) u) (h0 : a 0 = b 0)
    (h0' : a' 0 = b' 0) (h1 : b 1 = c 1) (h1' : b' 1 = c' 1) (x : ℝ) :
    HasDerivAt (glue a b c) (glue a' b' c' x) x := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [glue_of_nonpos _ _ _ le_rfl]
    refine hasDerivAt_of_Iic_Ici ?_ ?_
    · refine (ha 0).hasDerivWithinAt.congr (fun u hu => glue_of_nonpos _ _ _ hu)
        (glue_of_nonpos _ _ _ le_rfl)
    · rw [h0']
      refine (hb 0).hasDerivWithinAt.congr_of_eventuallyEq ?_ (by rw [glue_of_nonpos _ _ _ le_rfl, h0])
      filter_upwards [Ico_mem_nhdsGE zero_lt_one] with u hu
      rcases eq_or_lt_of_le hu.1 with rfl | hpos
      · rw [glue_of_nonpos _ _ _ le_rfl, h0]
      · exact glue_of_mem_Ioo _ _ _ ⟨hpos, hu.2⟩
  by_cases hx1 : x = 1
  · subst hx1
    rw [glue_of_one_le _ _ _ le_rfl]
    refine hasDerivAt_of_Iic_Ici ?_ ?_
    · rw [← h1']
      refine (hb 1).hasDerivWithinAt.congr_of_eventuallyEq ?_ (by rw [glue_of_one_le _ _ _ le_rfl, h1])
      filter_upwards [Ioc_mem_nhdsLE zero_lt_one] with u hu
      rcases eq_or_lt_of_le hu.2 with rfl | hlt
      · rw [glue_of_one_le _ _ _ le_rfl, h1]
      · exact glue_of_mem_Ioo _ _ _ ⟨hu.1, hlt⟩
    · exact (hc 1).hasDerivWithinAt.congr (fun u hu => glue_of_one_le _ _ _ hu)
        (glue_of_one_le _ _ _ le_rfl)
  exact hasDerivAt_glue_of_ne ha hb hc hx0 hx1

/-- Continuous pieces that match at `0` and `1` glue to a continuous function. -/
theorem continuous_glue {a b c : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (h0 : a 0 = b 0) (h1 : b 1 = c 1) : Continuous (glue a b c) := by
  have hin : Continuous fun u : ℝ => if (1 : ℝ) ≤ u then c u else b u :=
    Continuous.if_le hc hb continuous_const continuous_id (fun u hu => by subst hu; exact h1.symm)
  exact Continuous.if_le ha hin continuous_id continuous_const
    (fun u (hu : u = 0) => by subst hu; simp [h0])

/-! ### The polynomial pieces -/

/-- The quintic `u³(10 − 15u + 6u²)`. -/
def quintic (u : ℝ) : ℝ := u ^ 3 * (10 - 15 * u + 6 * u ^ 2)

/-- Its derivative `30u²(1 − u)²`. -/
def quintic1 (u : ℝ) : ℝ := 30 * u ^ 2 * (1 - u) ^ 2

/-- Its second derivative `60u(1 − u)(1 − 2u)`. -/
def quintic2 (u : ℝ) : ℝ := 60 * u * (1 - u) * (1 - 2 * u)

/-- Its third derivative `60(1 − 6u + 6u²)`. -/
def quintic3 (u : ℝ) : ℝ := 60 * (1 - 6 * u + 6 * u ^ 2)

theorem hasDerivAt_quintic (u : ℝ) : HasDerivAt quintic (quintic1 u) u := by
  have hf : quintic = fun x => 10 * x ^ 3 - 15 * x ^ 4 + 6 * x ^ 5 := by funext x; simp only [quintic]; ring
  rw [hf]
  refine ((((hasDerivAt_pow 3 u).const_mul 10).sub ((hasDerivAt_pow 4 u).const_mul 15)).add
    ((hasDerivAt_pow 5 u).const_mul 6)).congr_deriv ?_
  simp only [quintic1]; push_cast; ring

theorem hasDerivAt_quintic1 (u : ℝ) : HasDerivAt quintic1 (quintic2 u) u := by
  have hf : quintic1 = fun x => 30 * x ^ 2 - 60 * x ^ 3 + 30 * x ^ 4 := by
    funext x; simp only [quintic1]; ring
  rw [hf]
  refine ((((hasDerivAt_pow 2 u).const_mul 30).sub ((hasDerivAt_pow 3 u).const_mul 60)).add
    ((hasDerivAt_pow 4 u).const_mul 30)).congr_deriv ?_
  simp only [quintic2]; push_cast; ring

theorem hasDerivAt_quintic2 (u : ℝ) : HasDerivAt quintic2 (quintic3 u) u := by
  have hf : quintic2 = fun x => 60 * x ^ 1 - 180 * x ^ 2 + 120 * x ^ 3 := by
    funext x; simp only [quintic2]; ring
  rw [hf]
  refine ((((hasDerivAt_pow 1 u).const_mul 60).sub ((hasDerivAt_pow 2 u).const_mul 180)).add
    ((hasDerivAt_pow 3 u).const_mul 120)).congr_deriv ?_
  simp only [quintic3]; push_cast; ring

/-! ### The step and its derivatives -/

/-- The quintic step: `0` on `(−∞, 0]`, `u³(10 − 15u + 6u²)` on `(0, 1)`, `1` on `[1, ∞)`. -/
def S (u : ℝ) : ℝ := glue (fun _ => 0) quintic (fun _ => 1) u

/-- `S′`: `30u²(1 − u)²` on `(0, 1)` and `0` elsewhere. -/
def dS (u : ℝ) : ℝ := glue (fun _ => 0) quintic1 (fun _ => 0) u

/-- `S″`: `60u(1 − u)(1 − 2u)` on `(0, 1)` and `0` elsewhere. -/
def d2S (u : ℝ) : ℝ := glue (fun _ => 0) quintic2 (fun _ => 0) u

/-- `S‴` off `{0, 1}`: `60(1 − 6u + 6u²)` on `(0, 1)` and `0` elsewhere. -/
def d3S (u : ℝ) : ℝ := glue (fun _ => 0) quintic3 (fun _ => 0) u

theorem S_zero : S 0 = 0 := glue_of_nonpos _ _ _ le_rfl
theorem dS_zero : dS 0 = 0 := glue_of_nonpos _ _ _ le_rfl
theorem S_one : S 1 = 1 := glue_of_one_le _ _ _ le_rfl
theorem dS_one : dS 1 = 0 := glue_of_one_le _ _ _ le_rfl

theorem S_of_nonpos {u : ℝ} (hu : u ≤ 0) : S u = 0 := glue_of_nonpos _ _ _ hu
theorem S_of_one_le {u : ℝ} (hu : 1 ≤ u) : S u = 1 := glue_of_one_le _ _ _ hu

theorem hasDerivAt_S (u : ℝ) : HasDerivAt S (dS u) u :=
  hasDerivAt_glue (fun _ => hasDerivAt_const _ _) hasDerivAt_quintic (fun _ => hasDerivAt_const _ _)
    (by simp [quintic]) (by simp [quintic1]) (by norm_num [quintic]) (by norm_num [quintic1]) u

theorem hasDerivAt_dS (u : ℝ) : HasDerivAt dS (d2S u) u :=
  hasDerivAt_glue (fun _ => hasDerivAt_const _ _) hasDerivAt_quintic1 (fun _ => hasDerivAt_const _ _)
    (by simp [quintic1]) (by simp [quintic2]) (by norm_num [quintic1]) (by norm_num [quintic2]) u

/-- `S‴ = d3S` off the two corners. -/
theorem hasDerivAt_d2S {u : ℝ} (h0 : u ≠ 0) (h1 : u ≠ 1) : HasDerivAt d2S (d3S u) u :=
  hasDerivAt_glue_of_ne (fun _ => hasDerivAt_const _ _) hasDerivAt_quintic2
    (fun _ => hasDerivAt_const _ _) h0 h1

theorem continuous_d2S : Continuous d2S :=
  continuous_glue continuous_const (by unfold quintic2; fun_prop) continuous_const
    (by simp [quintic2]) (by norm_num [quintic2])

theorem deriv_S : deriv S = dS := funext fun u => (hasDerivAt_S u).deriv

theorem deriv_dS : deriv dS = d2S := funext fun u => (hasDerivAt_dS u).deriv

/-- **The step is `C²`.** -/
theorem contDiff_S : ContDiff ℝ 2 S := by
  have h1 : ContDiff ℝ 1 dS := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiff_succ_iff_deriv]
    exact ⟨fun u => (hasDerivAt_dS u).differentiableAt, by simp, by
      rw [deriv_dS]; exact contDiff_zero.2 continuous_d2S⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun u => (hasDerivAt_S u).differentiableAt, by simp, by rw [deriv_S]; exact h1⟩

/-- **Antisymmetry about `½`**: `S(1 − u) = 1 − S(u)`. -/
theorem S_one_sub (u : ℝ) : S (1 - u) = 1 - S u := by
  rcases le_or_gt u 0 with h | h
  · rw [S_of_one_le (by linarith), S_of_nonpos h]; ring
  rcases le_or_gt 1 u with h' | h'
  · rw [S_of_nonpos (by linarith), S_of_one_le h']; ring
  unfold S
  rw [glue_of_mem_Ioo _ _ _ (show 1 - u ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩),
    glue_of_mem_Ioo _ _ _ ⟨h, h'⟩, quintic, quintic]
  ring

theorem S_mem_Icc (u : ℝ) : S u ∈ Icc (0 : ℝ) 1 := by
  rcases le_or_gt u 0 with h | h
  · rw [S_of_nonpos h]; exact ⟨le_rfl, zero_le_one⟩
  rcases le_or_gt 1 u with h' | h'
  · rw [S_of_one_le h']; exact ⟨zero_le_one, le_rfl⟩
  rw [S, glue_of_mem_Ioo _ _ _ ⟨h, h'⟩, quintic]
  have e : 1 - u ^ 3 * (10 - 15 * u + 6 * u ^ 2) = (1 - u) ^ 3 * (1 + 3 * u + 6 * u ^ 2) := by ring
  constructor
  · have : 0 < 10 - 15 * u + 6 * u ^ 2 := by nlinarith [sq_nonneg (u - 5 / 4)]
    positivity
  · have : 0 ≤ (1 - u) ^ 3 * (1 + 3 * u + 6 * u ^ 2) := by
      have : 0 ≤ 1 - u := by linarith
      positivity
    linarith

/-! ### Exact `L²` norms -/

/-- `∫₀¹ Σ cₖ uᵏ = Σ cₖ / (k + 1)`. -/
theorem integral_unit_poly (c : ℕ → ℝ) (n : ℕ) :
    ∫ u in (0 : ℝ)..1, ∑ k ∈ Finset.range n, c k * u ^ k = ∑ k ∈ Finset.range n, c k / (k + 1) := by
  rw [integral_finsetSum (fun k _ => (by fun_prop : Continuous fun u : ℝ => c k * u ^ k).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp [div_eq_mul_inv]

/-- Interval integrals over `[0, 1]` see only `(0, 1)`. -/
theorem integral_congr_Ioo {f g : ℝ → ℝ} (h : EqOn f g (Ioo 0 1)) :
    ∫ u in (0 : ℝ)..1, f u = ∫ u in (0 : ℝ)..1, g u := by
  rw [integral_of_le zero_le_one, integral_of_le zero_le_one, ← setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← setIntegral_congr_set Ioo_ae_eq_Ioc]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- A function vanishing off `(0, 1]` integrates over `ℝ` as over `[0, 1]`. -/
theorem integral_eq_unit {f : ℝ → ℝ} (h : ∀ u, u ∉ Ioc (0 : ℝ) 1 → f u = 0) :
    ∫ u, f u = ∫ u in (0 : ℝ)..1, f u := by
  rw [integral_of_le zero_le_one, setIntegral_eq_integral_of_forall_compl_eq_zero h]

theorem glue_zero_of_not_mem {b : ℝ → ℝ} {u : ℝ} (hu : u ∉ Ioc (0 : ℝ) 1) :
    glue (fun _ => 0) b (fun _ => 0) u = 0 := by
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with h | h
  · exact glue_of_nonpos _ _ _ h
  · exact glue_of_one_le _ _ _ h.le

theorem integral_quintic_sq : ∫ u in (0 : ℝ)..1, quintic u ^ 2 = 181 / 462 := by
  have e : ∀ u : ℝ, quintic u ^ 2 = ∑ k ∈ Finset.range 11,
      ([0, 0, 0, 0, 0, 0, 100, -300, 345, -180, 36] : List ℝ).getD k 0 * u ^ k := by
    intro u; simp [Finset.sum_range_succ, quintic]; ring
  simp_rw [e, integral_unit_poly]
  simp [Finset.sum_range_succ]; norm_num

theorem integral_quintic1_sq : ∫ u in (0 : ℝ)..1, quintic1 u ^ 2 = 10 / 7 := by
  have e : ∀ u : ℝ, quintic1 u ^ 2 = ∑ k ∈ Finset.range 9,
      ([0, 0, 0, 0, 900, -3600, 5400, -3600, 900] : List ℝ).getD k 0 * u ^ k := by
    intro u; simp [Finset.sum_range_succ, quintic1]; ring
  simp_rw [e, integral_unit_poly]
  simp [Finset.sum_range_succ]; norm_num

theorem integral_quintic2_sq : ∫ u in (0 : ℝ)..1, quintic2 u ^ 2 = 120 / 7 := by
  have e : ∀ u : ℝ, quintic2 u ^ 2 = ∑ k ∈ Finset.range 7,
      ([0, 0, 3600, -21600, 46800, -43200, 14400] : List ℝ).getD k 0 * u ^ k := by
    intro u; simp [Finset.sum_range_succ, quintic2]; ring
  simp_rw [e, integral_unit_poly]
  simp [Finset.sum_range_succ]; norm_num

theorem integral_quintic3_sq : ∫ u in (0 : ℝ)..1, quintic3 u ^ 2 = 720 := by
  have e : ∀ u : ℝ, quintic3 u ^ 2 = ∑ k ∈ Finset.range 5,
      ([3600, -43200, 172800, -259200, 129600] : List ℝ).getD k 0 * u ^ k := by
    intro u; simp [Finset.sum_range_succ, quintic3]; ring
  simp_rw [e, integral_unit_poly]
  simp [Finset.sum_range_succ]; norm_num

/-- **`ς₁² = ‖S′‖₂² = 10/7`.** -/
theorem integral_dS_sq : ∫ u, dS u ^ 2 = 10 / 7 := by
  rw [integral_eq_unit fun u hu => by simp [dS, glue_zero_of_not_mem hu], ← integral_quintic1_sq]
  exact integral_congr_Ioo fun u hu => by rw [dS, glue_of_mem_Ioo _ _ _ hu]

/-- **`ς₂² = ‖S″‖₂² = 120/7`.** -/
theorem integral_d2S_sq : ∫ u, d2S u ^ 2 = 120 / 7 := by
  rw [integral_eq_unit fun u hu => by simp [d2S, glue_zero_of_not_mem hu], ← integral_quintic2_sq]
  exact integral_congr_Ioo fun u hu => by rw [d2S, glue_of_mem_Ioo _ _ _ hu]

/-- **`ς₃² = ‖S‴‖₂² = 720`.** -/
theorem integral_d3S_sq : ∫ u, d3S u ^ 2 = 720 := by
  rw [integral_eq_unit fun u hu => by simp [d3S, glue_zero_of_not_mem hu], ← integral_quintic3_sq]
  exact integral_congr_Ioo fun u hu => by rw [d3S, glue_of_mem_Ioo _ _ _ hu]

/-! ### Exact sups -/

/-- `0 ≤ S′ ≤ 15/8`. -/
theorem dS_mem_Icc (u : ℝ) : dS u ∈ Icc (0 : ℝ) (15 / 8) := by
  rcases le_or_gt u 0 with h | h
  · rw [dS, glue_of_nonpos _ _ _ h]; norm_num
  rcases le_or_gt 1 u with h' | h'
  · rw [dS, glue_of_one_le _ _ _ h']; norm_num
  rw [dS, glue_of_mem_Ioo _ _ _ ⟨h, h'⟩, quintic1]
  have h1 : 0 ≤ u * (1 - u) := mul_nonneg h.le (by linarith)
  have h2 : u * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  rw [show 30 * u ^ 2 * (1 - u) ^ 2 = 30 * (u * (1 - u)) ^ 2 by ring]
  exact ⟨by positivity, by nlinarith⟩

/-- **`sup |S′| = 15/8`**: the bound. -/
theorem abs_dS_le (u : ℝ) : |dS u| ≤ 15 / 8 := by
  rw [abs_of_nonneg (dS_mem_Icc u).1]; exact (dS_mem_Icc u).2

/-- `S″² ≤ 100/3`, from `100/3 − S″² = (100/3)(1 − 12t²)²(1 − 3t²)` with `t = u − ½`. -/
theorem d2S_sq_le (u : ℝ) : d2S u ^ 2 ≤ 100 / 3 := by
  rcases le_or_gt u 0 with h | h
  · rw [d2S, glue_of_nonpos _ _ _ h]; norm_num
  rcases le_or_gt 1 u with h' | h'
  · rw [d2S, glue_of_one_le _ _ _ h']; norm_num
  rw [d2S, glue_of_mem_Ioo _ _ _ ⟨h, h'⟩, quintic2]
  have e : 100 / 3 - (60 * u * (1 - u) * (1 - 2 * u)) ^ 2 =
      100 / 3 * (1 - 12 * (u - 1 / 2) ^ 2) ^ 2 * (1 - 3 * (u - 1 / 2) ^ 2) := by ring
  have ht : 0 ≤ 1 - 3 * (u - 1 / 2) ^ 2 := by nlinarith
  have : 0 ≤ 100 / 3 * (1 - 12 * (u - 1 / 2) ^ 2) ^ 2 * (1 - 3 * (u - 1 / 2) ^ 2) := by positivity
  linarith

theorem sqrt_hundred_thirds : √(100 / 3 : ℝ) = 10 / √3 := by
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 3),
    show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **`sup |S″| = 10/√3`**: the bound. -/
theorem abs_d2S_le (u : ℝ) : |d2S u| ≤ 10 / √3 := by
  rw [← sqrt_hundred_thirds]; exact Real.abs_le_sqrt (d2S_sq_le u)

end Cvs.Upstream.QuinticSmoothStep
