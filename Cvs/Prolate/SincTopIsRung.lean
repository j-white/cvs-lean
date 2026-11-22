import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformEigenRelation
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.ComplexificationIsometryL2
import Cvs.Upstream.LipschitzFamilyTotallyBoundedL2
import Cvs.WeilForm.ChannelKernelBoundedOperator
import Cvs.WeilForm.ChannelOperatorCompact
import Cvs.WeilForm.KernelOperatorParitySectors
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.TruncatedFormPolarised
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowCutBoundedBridge
import Cvs.WeilForm.WindowOrthogonalComplement
import Cvs.WeilForm.WindowRepresentative

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A rung from a test function: the top of the even sinc operator on `W^⊥` is an angular rung

On the window `L²(0, 1]` the folded cosine transform `F` is compact and symmetric, `K = (c/2π)F²` is the even sinc
operator, and the even angular operator commutes with `F`; so an even `f ⊥ W` with `⟨Kf, f⟩ ≥ ½‖f‖²` yields an even
angular rung `g ⊥ W` with `(μ√(c/2π))² ≥ ½`.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open Real Set MeasureTheory Filter Topology
open scoped Interval

namespace Cvs.Prolate.SincTopIsRung

open Cvs.WeilForm.WindowRepresentative (rep rep_supp)

/-! ### The folded cosine transform of a window class -/

/-- The folded cosine transform `F φ(ξ) = 2∫ φ(s) cos(cξs) ds` of a class of `L²(0, 1]`. -/
def cosFn (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) : ℝ := 2 * ∫ s, rep φ s * cos (c * ξ * s)

theorem integrable_rep_mul_cos (c ξ : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    Integrable (fun s => rep φ s * cos (c * ξ * s)) :=
  Cvs.WeilForm.TruncatedFormPolarised.integrable_rep_mul φ (by fun_prop)

/-- The `L¹` mass of a class of `L²(0, 1]` is at most its norm. -/
theorem integral_abs_rep_le (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : ∫ s, |rep φ s| ≤ ‖φ‖ := by
  have h := Cvs.WeilForm.ChannelKernelBoundedOperator.sq_integral_abs_rep_le φ
  rw [one_mul] at h
  have h0 : 0 ≤ ∫ s, |rep φ s| := integral_nonneg fun s => abs_nonneg _
  nlinarith [norm_nonneg φ]

theorem abs_cosFn_le (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    |cosFn c φ ξ| ≤ 2 * ∫ s, |rep φ s| := by
  unfold cosFn
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (abs_integral_le_integral_abs).trans (integral_mono (integrable_rep_mul_cos c ξ φ).abs
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).abs fun s => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

/-- **`F φ` is Lipschitz with constant `2|c|∫|φ|`**: the support lies in `(0, 1]`. -/
theorem abs_cosFn_sub_le (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ ξ' : ℝ) :
    |cosFn c φ ξ - cosFn c φ ξ'| ≤ 2 * |c| * (∫ s, |rep φ s|) * |ξ - ξ'| := by
  unfold cosFn
  rw [← mul_sub, ← integral_sub (integrable_rep_mul_cos c ξ φ) (integrable_rep_mul_cos c ξ' φ), abs_mul,
    abs_two]
  have hpt : ∀ s, |rep φ s * cos (c * ξ * s) - rep φ s * cos (c * ξ' * s)| ≤ |c| * |ξ - ξ'| * |rep φ s| := by
    intro s
    rw [← mul_sub, abs_mul]
    by_cases hs : s ∈ Ioc (0 : ℝ) 1
    · have h1 : |cos (c * ξ * s) - cos (c * ξ' * s)| ≤ |c| * |ξ - ξ'| := by
        refine (abs_cos_sub_cos_le _ _).trans ?_
        rw [show c * ξ * s - c * ξ' * s = c * (ξ - ξ') * s by ring, abs_mul, abs_mul]
        have : |s| ≤ 1 := by rw [abs_of_pos hs.1]; exact hs.2
        nlinarith [abs_nonneg c, abs_nonneg (ξ - ξ'), abs_nonneg s, mul_nonneg (abs_nonneg c) (abs_nonneg (ξ - ξ'))]
      nlinarith [abs_nonneg (rep φ s)]
    · rw [rep_supp φ s hs, abs_zero, zero_mul, mul_zero]
  have hint : Integrable (fun s => |c| * |ξ - ξ'| * |rep φ s|) :=
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ).abs.const_mul _
  calc 2 * |∫ s, (rep φ s * cos (c * ξ * s) - rep φ s * cos (c * ξ' * s))|
      ≤ 2 * ∫ s, |c| * |ξ - ξ'| * |rep φ s| := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact (abs_integral_le_integral_abs).trans (integral_mono
          ((integrable_rep_mul_cos c ξ φ).sub (integrable_rep_mul_cos c ξ' φ)).abs hint hpt)
    _ = 2 * |c| * (∫ s, |rep φ s|) * |ξ - ξ'| := by rw [integral_const_mul]; ring

theorem continuous_cosFn (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : Continuous (cosFn c φ) := by
  refine (LipschitzWith.of_dist_le_mul fun ξ ξ' => ?_ :
    LipschitzWith (Real.toNNReal (2 * |c| * ∫ s, |rep φ s|)) (cosFn c φ)).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  exact abs_cosFn_sub_le c φ ξ ξ'

theorem cosFn_neg (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) : cosFn c φ (-ξ) = cosFn c φ ξ := by
  unfold cosFn
  congr 2
  funext s
  rw [show c * -ξ * s = -(c * ξ * s) by ring, cos_neg]

theorem cosFn_add (c : ℝ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    cosFn c (φ + ψ) ξ = cosFn c φ ξ + cosFn c ψ ξ := by
  unfold cosFn
  rw [← mul_add, ← integral_add (integrable_rep_mul_cos c ξ φ) (integrable_rep_mul_cos c ξ ψ)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Cvs.WeilForm.TruncatedFormPolarised.rep_add_ae φ ψ] with s hs
  rw [hs]; ring

theorem cosFn_smul (c t : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    cosFn c (t • φ) ξ = t * cosFn c φ ξ := by
  unfold cosFn
  have h : ∫ s, rep (t • φ) s * cos (c * ξ * s) = ∫ s, t * (rep φ s * cos (c * ξ * s)) := by
    refine integral_congr_ae ?_
    filter_upwards [Cvs.WeilForm.ChannelKernelBoundedOperator.rep_smul_ae t φ] with s hs
    rw [hs]; ring
  rw [h, integral_const_mul]; ring

/-! ### Window classes of continuous functions -/

/-- The class of `1_{(0,1]} h` for continuous `h`. -/
def cutCls {h : ℝ → ℝ} (hh : Continuous h) : Cvs.WeilForm.WeilFormOnWindowL2.window 1 :=
  ⟨(Cvs.WeilForm.ChannelKernelBoundedOperator.memLp_cut_of_continuous hh 1).toLp _, by
    filter_upwards [(Cvs.WeilForm.ChannelKernelBoundedOperator.memLp_cut_of_continuous hh 1).coeFn_toLp] with x hx hxne
    rw [hx]
    exact Cvs.WeilForm.WindowCutBoundedBridge.cut_of_notMem hxne⟩

theorem rep_cutCls {h : ℝ → ℝ} (hh : Continuous h) : rep (cutCls hh) =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h :=
  (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.WeilForm.ChannelKernelBoundedOperator.memLp_cut_of_continuous hh 1).coeFn_toLp

/-- `∫ 1_{(0,1]} h · u = ∫_0^1 h u`. -/
theorem integral_cut_mul {h u : ℝ → ℝ} :
    ∫ s, Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h s * u s = ∫ s in (0 : ℝ)..1, h s * u s := by
  have e : (fun s => Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h s * u s) = (Ioc (0 : ℝ) 1).indicator (fun s => h s * u s) := by
    funext s
    unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
    by_cases hs : s ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hs, indicator_of_mem hs]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, zero_mul]
  rw [e, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le zero_le_one]

/-- For `h` even and continuous, `∫_{−1}^{1} h(s) u(s) ds = 2 ∫_0^1 h(s) u(s) ds` when `u` is even. -/
theorem integral_even_eq_two_mul {v : ℝ → ℝ} (hv : Continuous v) (heven : ∀ s, v (-s) = v s) :
    ∫ s in (-1 : ℝ)..1, v s = 2 * ∫ s in (0 : ℝ)..1, v s := by
  have hi1 : IntervalIntegrable v volume (-1) 0 := hv.intervalIntegrable _ _
  have hi2 : IntervalIntegrable v volume 0 1 := hv.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) v
  simp only [neg_zero, heven] at h
  rw [← h]
  ring

/-- **`F` of a cut even function is its cosine transform**: `F(1_{(0,1]} h) = psi c h` for `h` even. -/
theorem cosFn_cutCls {c : ℝ} {h : ℝ → ℝ} (hh : Continuous h) (heven : ∀ s, h (-s) = h s) (ξ : ℝ) :
    cosFn c (cutCls hh) ξ = Cvs.L2a.AngularProlateTailPositive.psi c h ξ := by
  unfold cosFn
  have h1 : ∫ s, rep (cutCls hh) s * cos (c * ξ * s) = ∫ s, Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h s * cos (c * ξ * s) := by
    refine integral_congr_ae ?_
    filter_upwards [rep_cutCls hh] with s hs
    rw [hs]
  rw [h1, integral_cut_mul]
  show 2 * (∫ s in (0 : ℝ)..1, h s * cos (c * ξ * s)) = ∫ s in (-1 : ℝ)..1, h s * cos (c * ξ * s)
  rw [integral_even_eq_two_mul (by fun_prop) (fun s => by
    rw [heven, show c * ξ * -s = -(c * ξ * s) by ring, cos_neg])]

/-! ### The cosine operator on `L²(0, 1]` -/

/-- `F φ`, as a class of `L²(0, 1]`. -/
def cosMap (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : Cvs.WeilForm.WeilFormOnWindowL2.window 1 :=
  cutCls (continuous_cosFn c φ)

theorem rep_cosMap (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    rep (cosMap c φ) =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 (cosFn c φ) :=
  rep_cutCls _

theorem cosMap_add (c : ℝ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    cosMap c (φ + ψ) = cosMap c φ + cosMap c ψ := by
  refine Cvs.WeilForm.ChannelKernelBoundedOperator.window_ext ?_
  filter_upwards [rep_cosMap c (φ + ψ), Cvs.WeilForm.TruncatedFormPolarised.rep_add_ae (cosMap c φ) (cosMap c ψ),
    rep_cosMap c φ, rep_cosMap c ψ] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, cosFn_add]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, add_zero]

theorem cosMap_smul (c t : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    cosMap c (t • φ) = t • cosMap c φ := by
  refine Cvs.WeilForm.ChannelKernelBoundedOperator.window_ext ?_
  filter_upwards [rep_cosMap c (t • φ), Cvs.WeilForm.ChannelKernelBoundedOperator.rep_smul_ae t (cosMap c φ),
    rep_cosMap c φ] with x h1 h2 h3
  rw [h1, h2, h3]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hx, indicator_of_mem hx, cosFn_smul]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

theorem norm_cosMap_le (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : ‖cosMap c φ‖ ≤ 2 * ‖φ‖ := by
  have hM : ∀ x, |cosFn c φ x| ≤ 2 * ‖φ‖ := fun x =>
    (abs_cosFn_le c φ x).trans (by linarith [integral_abs_rep_le φ])
  have hpt : ∀ x, (Cvs.WeilForm.WindowCutBoundedBridge.cut 1 (cosFn c φ) x) ^ 2
      ≤ (Ioc (0 : ℝ) 1).indicator (fun _ => (2 * ‖φ‖) ^ 2) x := by
    intro x
    unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      have := hM x
      nlinarith [abs_nonneg (cosFn c φ x), sq_abs (cosFn c φ x)]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
  have hint : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => (2 * ‖φ‖) ^ 2) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
  have hsq : ‖cosMap c φ‖ ^ 2 ≤ (2 * ‖φ‖) ^ 2 := by
    rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep,
      integral_congr_ae ((rep_cosMap c φ).mono fun x hx => by rw [hx])]
    calc (∫ x, (Cvs.WeilForm.WindowCutBoundedBridge.cut 1 (cosFn c φ) x) ^ 2)
        ≤ ∫ x, (Ioc (0 : ℝ) 1).indicator (fun _ => (2 * ‖φ‖) ^ 2) x :=
          integral_mono ((Cvs.WeilForm.ChannelKernelBoundedOperator.memLp_cut_of_continuous (continuous_cosFn c φ) 1).integrable_sq)
            hint hpt
      _ = (2 * ‖φ‖) ^ 2 := by
          rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul, measureReal_def, Real.volume_Ioc,
            ENNReal.toReal_ofReal (by norm_num)]
          ring
  nlinarith [norm_nonneg (cosMap c φ), norm_nonneg φ]

/-- `F` as a linear map. -/
def cosHom (c : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window 1 →ₗ[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window 1 where
  toFun := cosMap c
  map_add' := cosMap_add c
  map_smul' := fun t φ => by simpa using cosMap_smul c t φ

/-- **The folded cosine transform** `F` as a continuous linear map on `L²(0, 1]`. -/
def cosCLM (c : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window 1 →L[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window 1 :=
  LinearMap.mkContinuous (cosHom c) 2 (norm_cosMap_le c)

theorem cosCLM_apply (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : cosCLM c φ = cosMap c φ := rfl

/-! ### Symmetry -/

/-- `⟨Fφ, ψ⟩ = 2∫∫ ψ(x) φ(s) cos(cxs)`. -/
theorem inner_cosMap (c : ℝ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    (inner ℝ (cosMap c φ) ψ : ℝ) = 2 * ∫ x, ∫ s, rep ψ x * rep φ s * cos (c * x * s) := by
  rw [Cvs.WeilForm.WindowOrthogonalComplement.inner_rep, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [rep_cosMap c φ] with x hx
  rw [hx]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hxm : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxm]
    have h : (∫ s, rep φ s * cos (c * x * s)) * rep ψ x = ∫ s, rep ψ x * rep φ s * cos (c * x * s) := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only []
      ring
    unfold cosFn
    rw [mul_assoc, h]
  · rw [indicator_of_notMem hxm, rep_supp ψ x hxm]
    simp

theorem integrable_cross (c : ℝ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    Integrable (fun p : ℝ × ℝ => rep ψ p.1 * rep φ p.2 * cos (c * p.1 * p.2)) (volume.prod volume) := by
  have hprod : Integrable (fun p : ℝ × ℝ => rep ψ p.1 * rep φ p.2) (volume.prod volume) :=
    (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep ψ).mul_prod (Cvs.WeilForm.TruncatedFormPolarised.integrable_rep φ)
  refine hprod.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact hprod.aestronglyMeasurable.mul (by fun_prop : Continuous fun p : ℝ × ℝ => cos (c * p.1 * p.2)).aestronglyMeasurable
  · rw [norm_mul (rep ψ p.1 * rep φ p.2)]
    have hc : ‖cos (c * p.1 * p.2)‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact abs_cos_le_one _
    exact mul_le_of_le_one_right (norm_nonneg _) hc

/-- **`F` is symmetric**: `⟨Fφ, ψ⟩ = ⟨φ, Fψ⟩`. -/
theorem inner_cosMap_comm (c : ℝ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    (inner ℝ (cosMap c φ) ψ : ℝ) = (inner ℝ φ (cosMap c ψ) : ℝ) := by
  rw [real_inner_comm (cosMap c ψ) φ, inner_cosMap, inner_cosMap]
  congr 1
  rw [integral_integral_swap (integrable_cross c φ ψ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only []
  rw [show c * s * x = c * x * s by ring]
  ring

/-! ### Compactness -/

/-- The complexified `F`-images of the unit ball. -/
def fam (c : ℝ) : Set (ℝ → ℂ) :=
  {g | ∃ φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1, ‖φ‖ ≤ 1 ∧ g = fun x => ((cosFn c φ x : ℝ) : ℂ)}

theorem fam_bdd (c : ℝ) (g : ℝ → ℂ) (hg : g ∈ fam c) (x : ℝ) : ‖g x‖ ≤ ((2 : NNReal) : ℝ) := by
  obtain ⟨φ, hφ, rfl⟩ := hg
  simp only [Complex.norm_real, Real.norm_eq_abs, NNReal.coe_ofNat]
  have := abs_cosFn_le c φ x
  have := integral_abs_rep_le φ
  linarith

theorem fam_lip (c : ℝ) (g : ℝ → ℂ) (hg : g ∈ fam c) : LipschitzWith (Real.toNNReal (2 * |c|)) g := by
  obtain ⟨φ, hφ, rfl⟩ := hg
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  have hd : dist ((cosFn c φ x : ℝ) : ℂ) ((cosFn c φ y : ℝ) : ℂ) = |cosFn c φ x - cosFn c φ y| := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hd, Real.dist_eq]
  have h1 := abs_cosFn_sub_le c φ x y
  have h2 : ∫ s, |rep φ s| ≤ 1 := (integral_abs_rep_le φ).trans hφ
  have h3 : 0 ≤ ∫ s, |rep φ s| := integral_nonneg fun s => abs_nonneg _
  calc |cosFn c φ x - cosFn c φ y| ≤ 2 * |c| * (∫ s, |rep φ s|) * |x - y| := h1
    _ ≤ 2 * |c| * 1 * |x - y| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * |c| * |x - y| := by ring

theorem totallyBounded_fam (c : ℝ) :
    TotallyBounded {u : Lp ℂ 2 (volume : Measure ℝ) |
      ∃ g ∈ fam c, (u : ℝ → ℂ) =ᵐ[volume] (Ioc (0 : ℝ) 1).indicator g} :=
  Cvs.Upstream.LipschitzFamilyTotallyBoundedL2.totallyBounded_of_lipschitz zero_le_one (fam c) (fam_bdd c) (fam_lip c)
    measurableSet_Ioc Ioc_subset_Icc_self

theorem Psi_cosMap_ae (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    ((Cvs.WeilForm.ChannelOperatorCompact.Psi 1 (cosMap c φ) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] (Ioc (0 : ℝ) 1).indicator (fun x => ((cosFn c φ x : ℝ) : ℂ)) := by
  filter_upwards [Cvs.Upstream.ComplexificationIsometryL2.emb_ae
      ((cosMap c φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : Lp ℝ 2 (volume : Measure ℝ)),
    Cvs.WeilForm.WindowRepresentative.ae_eq_rep (cosMap c φ), rep_cosMap c φ] with x h1 h2 h3
  unfold Cvs.WeilForm.ChannelOperatorCompact.Psi
  rw [h1]
  show ((Cvs.WeilForm.WindowRepresentative.fn (cosMap c φ) x : ℝ) : ℂ) = _
  rw [h2, h3]
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx, Cvs.WeilForm.WindowCutBoundedBridge.cut_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Cvs.WeilForm.WindowCutBoundedBridge.cut_of_notMem hx, Complex.ofReal_zero]

theorem image_ball_subset (c : ℝ) :
    Cvs.WeilForm.ChannelOperatorCompact.Psi 1 '' (cosCLM c '' Metric.ball 0 1) ⊆
      {u : Lp ℂ 2 (volume : Measure ℝ) |
        ∃ g ∈ fam c, (u : ℝ → ℂ) =ᵐ[volume] (Ioc (0 : ℝ) 1).indicator g} := by
  rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
  have hn : ‖φ‖ ≤ 1 := le_of_lt (by simpa using hφ)
  exact ⟨_, ⟨φ, hn, rfl⟩, Psi_cosMap_ae c φ⟩

/-- **`F` is compact.** -/
theorem isCompactOperator_cosCLM (c : ℝ) : IsCompactOperator (cosCLM c) := by
  have hTB : TotallyBounded (cosCLM c '' Metric.ball 0 1) :=
    (totallyBounded_image_iff (Cvs.WeilForm.ChannelOperatorCompact.isometry_Psi 1).isUniformInducing).mp
      ((totallyBounded_fam c).subset (image_ball_subset c))
  refine (isCompactOperator_iff_isCompact_closure_image_ball
    ((cosCLM c : Cvs.WeilForm.WeilFormOnWindowL2.window 1 →ₗ[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window 1)) one_pos).mpr ?_
  exact hTB.closure.isCompact_of_isClosed isClosed_closure

/-! ### The square `F²` -/

/-- `F²` on `L²(0, 1]`; the even sinc operator is `(c/2π) F²`. -/
def sqCLM (c : ℝ) : Cvs.WeilForm.WeilFormOnWindowL2.window 1 →L[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window 1 :=
  (cosCLM c).comp (cosCLM c)

theorem sqCLM_apply (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : sqCLM c φ = cosMap c (cosMap c φ) := rfl

theorem isCompactOperator_sqCLM (c : ℝ) : IsCompactOperator (sqCLM c) :=
  (isCompactOperator_cosCLM c).comp_clm (cosCLM c)

theorem inner_sqCLM_comm (c : ℝ) (φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    (inner ℝ (sqCLM c φ) ψ : ℝ) = (inner ℝ φ (sqCLM c ψ) : ℝ) := by
  rw [sqCLM_apply, sqCLM_apply, inner_cosMap_comm, inner_cosMap_comm]

theorem inner_sqCLM_self (c : ℝ) (φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    (inner ℝ (sqCLM c φ) φ : ℝ) = ‖cosMap c φ‖ ^ 2 := by
  rw [sqCLM_apply, inner_cosMap_comm, real_inner_self_eq_norm_sq]

/-! ### Eigenspaces of a compact operator -/

/-- **A compact operator has finite-dimensional eigenspaces at nonzero eigenvalues.** -/
theorem finiteDimensional_eigenspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hT : IsCompactOperator T) {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (T : H →ₗ[ℝ] H) μ) := by
  set E := Module.End.eigenspace (T : H →ₗ[ℝ] H) μ with hE
  have hclosed : IsClosed (E : Set H) := by
    have : (E : Set H) = {x | T x = μ • x} := by
      ext x; simp [hE]
    rw [this]
    exact isClosed_eq T.continuous (continuous_const_smul μ)
  have : CompleteSpace E := hclosed.completeSpace_coe
  have hmaps : ∀ v ∈ E, (T : H →ₗ[ℝ] H) v ∈ E := fun v hv => by
    have h' := Module.End.mem_eigenspace_iff.1 hv
    rw [h']
    exact E.smul_mem μ hv
  have hcpt : IsCompactOperator ((T : H →ₗ[ℝ] H).restrict hmaps) := hT.restrict' hmaps
  have hid : IsCompactOperator (fun v : E => v) := by
    have e : (fun v : E => v) = fun v => μ⁻¹ • ((T : H →ₗ[ℝ] H).restrict hmaps v) := by
      funext v
      apply Subtype.ext
      have hv : T v = μ • (v : H) := Module.End.mem_eigenspace_iff.1 v.2
      simp only [LinearMap.restrict_apply, Submodule.coe_smul_of_tower, ContinuousLinearMap.coe_coe]
      rw [hv, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    rw [e]
    exact hcpt.smul μ⁻¹
  refine FiniteDimensional.of_isCompact_closedBall₀ ℝ one_pos ?_
  have := (isCompactOperator_iff_isCompact_closure_image_closedBall (LinearMap.id : E →ₗ[ℝ] E) one_pos).1 hid
  simpa [Metric.isClosed_closedBall.closure_eq] using this

/-! ### Scalars on the window -/

theorem inner_smul_left' (r : ℝ) (x y : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    (inner ℝ (r • x) y : ℝ) = r * inner ℝ x y := real_inner_smul_left x y r

theorem inner_smul_right' (r : ℝ) (x y : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    (inner ℝ x (r • y) : ℝ) = r * inner ℝ x y := real_inner_smul_right x y r

/-! ### Clamped extensions -/

/-- `h` clamped to `[−1, 1]`: `s ↦ h(max(−1, min(1, s)))`. -/
def clampExt (h : ℝ → ℝ) (s : ℝ) : ℝ := h (max (-1) (min 1 s))

theorem clamp_mem (s : ℝ) : max (-1 : ℝ) (min 1 s) ∈ Icc (-1 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clampExt_of_mem {h : ℝ → ℝ} {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) : clampExt h s = h s := by
  unfold clampExt
  rw [min_eq_right hs.2, max_eq_right hs.1]

theorem continuous_clampExt {h : ℝ → ℝ} (hh : ContinuousOn h (Icc (-1) 1)) : Continuous (clampExt h) :=
  hh.comp_continuous (by fun_prop) clamp_mem

theorem clampExt_neg {h : ℝ → ℝ} (heven : ∀ s ∈ Icc (-1 : ℝ) 1, h (-s) = h s) (s : ℝ) :
    clampExt h (-s) = clampExt h s := by
  unfold clampExt
  have e : max (-1 : ℝ) (min 1 (-s)) = -max (-1) (min 1 s) := by
    rw [max_def, min_def, max_def, min_def]
    split_ifs <;> linarith
  rw [e, heven _ (clamp_mem s)]

theorem psi_clampExt {c : ℝ} {h : ℝ → ℝ} (ξ : ℝ) :
    Cvs.L2a.AngularProlateTailPositive.psi c (clampExt h) ξ = Cvs.L2a.AngularProlateTailPositive.psi c h ξ := by
  show ∫ s in (-1 : ℝ)..1, clampExt h s * cos (c * ξ * s) = ∫ s in (-1 : ℝ)..1, h s * cos (c * ξ * s)
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (by norm_num)] at hs
  simp only [clampExt_of_mem hs]

/-! ### The rung classes and their complement -/

section Rungs

variable {ι : Type*} {c : ℝ} {w : ι → ℝ → ℝ} {μw : ι → ℝ}

/-- The class of the rung `w i` in `L²(0, 1]`. -/
def wCls (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) (i : ι) : Cvs.WeilForm.WeilFormOnWindowL2.window 1 :=
  cutCls (continuous_clampExt (hw i))

theorem rep_wCls (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) (i : ι) :
    rep (wCls hw i) =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 (w i) := by
  unfold wCls
  filter_upwards [rep_cutCls (continuous_clampExt (hw i))] with x hx
  rw [hx]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hxm : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxm, indicator_of_mem hxm, clampExt_of_mem ⟨by linarith [hxm.1], hxm.2⟩]
  · rw [indicator_of_notMem hxm, indicator_of_notMem hxm]

/-- **A rung is an eigenvector of `F`**: `F(w i) = μ_i w i`. -/
theorem cosMap_wCls (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hweven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hwμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (w i) s = μw i * w i s) (i : ι) :
    cosMap c (wCls hw i) = μw i • wCls hw i := by
  refine Cvs.WeilForm.ChannelKernelBoundedOperator.window_ext ?_
  filter_upwards [rep_cosMap c (wCls hw i), Cvs.WeilForm.ChannelKernelBoundedOperator.rep_smul_ae (μw i) (wCls hw i),
    rep_wCls hw i] with x h1 h2 h3
  rw [h1, h2, h3]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hxm : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxm, indicator_of_mem hxm]
    unfold wCls
    rw [cosFn_cutCls (continuous_clampExt (hw i)) (clampExt_neg (hweven i)), psi_clampExt]
    exact hwμ i x ⟨by linarith [hxm.1], hxm.2⟩
  · rw [indicator_of_notMem hxm, indicator_of_notMem hxm, mul_zero]

/-- The orthogonal complement of the rung classes. -/
def compl (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) : Submodule ℝ (Cvs.WeilForm.WeilFormOnWindowL2.window 1) :=
  (Submodule.span ℝ (Set.range (wCls hw)))ᗮ

theorem mem_compl (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} :
    v ∈ compl hw ↔ ∀ i, (inner ℝ (wCls hw i) v : ℝ) = 0 := by
  unfold compl
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_left' a x v, hx, mul_zero]

/-- **`F²` preserves the complement.** -/
theorem sqCLM_mem_compl (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hweven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hwμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (w i) s = μw i * w i s)
    {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} (hv : v ∈ compl hw) : sqCLM c v ∈ compl hw := by
  rw [mem_compl] at hv ⊢
  intro i
  rw [← inner_sqCLM_comm, sqCLM_apply, cosMap_wCls hw hweven hwμ i, cosMap_smul,
    cosMap_wCls hw hweven hwμ i, smul_smul, inner_smul_left', hv i, mul_zero]

theorem isClosed_compl (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) :
    IsClosed (compl hw : Set (Cvs.WeilForm.WeilFormOnWindowL2.window 1)) :=
  Submodule.isClosed_orthogonal _

end Rungs

/-! ### Inner products of cut classes -/

theorem inner_cut_classes {h₁ h₂ : ℝ → ℝ} {φ ψ : Cvs.WeilForm.WeilFormOnWindowL2.window 1}
    (h1 : rep φ =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h₁) (h2 : rep ψ =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h₂) :
    (inner ℝ φ ψ : ℝ) = ∫ s in (0 : ℝ)..1, h₁ s * h₂ s := by
  rw [Cvs.WeilForm.WindowOrthogonalComplement.inner_rep]
  have e : ∫ x, rep φ x * rep ψ x = ∫ x, Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h₁ x * Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h₂ x := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with x hx hy
    rw [hx, hy]
  rw [e, integral_cut_mul]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
  rw [uIoc_of_le zero_le_one] at hx
  simp only [Cvs.WeilForm.WindowCutBoundedBridge.cut_of_mem hx]

theorem sq_norm_cut_class {h : ℝ → ℝ} {φ : Cvs.WeilForm.WeilFormOnWindowL2.window 1}
    (h1 : rep φ =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h) : ‖φ‖ ^ 2 = ∫ s in (0 : ℝ)..1, h s ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_cut_classes h1 h1]
  simp_rw [sq]

/-! ### `F²` restricted to the complement -/

section Perp

variable {ι : Type*} {c : ℝ} {w : ι → ℝ → ℝ}

instance completeSpace_compl (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) : CompleteSpace ↥(compl hw) :=
  (isClosed_compl hw).completeSpace_coe

/-- The operator norm on `↥(compl hw) →L[ℝ] ↥(compl hw)`, supplied explicitly: instance search no longer
unifies `ContinuousLinearMap.hasOpNorm` against a submodule of a submodule of `Lp`. -/
instance normCLM_compl (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) : Norm (↥(compl hw) →L[ℝ] ↥(compl hw)) :=
  @ContinuousLinearMap.hasOpNorm ℝ ℝ ↥(compl hw) ↥(compl hw) _ _ _ _ InnerProductSpace.toNormedSpace
    InnerProductSpace.toNormedSpace (RingHom.id ℝ)

/-- `F²` restricted to an invariant complement. -/
def sqPerp (c : ℝ) (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hinv : ∀ v : Cvs.WeilForm.WeilFormOnWindowL2.window 1, v ∈ compl hw → sqCLM c v ∈ compl hw) :
    ↥(compl hw) →L[ℝ] ↥(compl hw) :=
  ((sqCLM c).comp (compl hw).subtypeL).codRestrict (compl hw) (fun v => hinv (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) v.2)

theorem sqPerp_coe (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hinv : ∀ v : Cvs.WeilForm.WeilFormOnWindowL2.window 1, v ∈ compl hw → sqCLM c v ∈ compl hw) (v : ↥(compl hw)) :
    ((sqPerp c hw hinv v : ↥(compl hw)) : Cvs.WeilForm.WeilFormOnWindowL2.window 1) = sqCLM c (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :=
  rfl

theorem inner_sqPerp (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hinv : ∀ v : Cvs.WeilForm.WeilFormOnWindowL2.window 1, v ∈ compl hw → sqCLM c v ∈ compl hw) (u v : ↥(compl hw)) :
    (inner ℝ (sqPerp c hw hinv u) v : ℝ) = (inner ℝ u (sqPerp c hw hinv v) : ℝ) :=
  inner_sqCLM_comm c (u : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1)

theorem isCompactOperator_sqPerp (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hinv : ∀ v : Cvs.WeilForm.WeilFormOnWindowL2.window 1, v ∈ compl hw → sqCLM c v ∈ compl hw) :
    IsCompactOperator (sqPerp c hw hinv) :=
  ((isCompactOperator_sqCLM c).comp_clm (compl hw).subtypeL).codRestrict _ (isClosed_compl hw)

theorem eigenvector_sqPerp (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hinv : ∀ v : Cvs.WeilForm.WeilFormOnWindowL2.window 1, v ∈ compl hw → sqCLM c v ∈ compl hw)
    (hne : sqPerp c hw hinv ≠ 0) :
    (∃ u : ↥(compl hw), u ≠ 0 ∧ sqPerp c hw hinv u = ‖sqPerp c hw hinv‖ • u) ∨
      (∃ u : ↥(compl hw), u ≠ 0 ∧ sqPerp c hw hinv u = (-‖sqPerp c hw hinv‖) • u) := by
  -- instance-transparency unification: default `isDefEq` times out on the nested-submodule instances
  refine Cvs.WeilForm.KernelOperatorParitySectors.exists_eigenvector_norm_or_neg (E := ↥(compl hw))
    (sqPerp c hw hinv) ?_ ?_ ?_
  · with_reducible_and_instances exact inner_sqPerp hw hinv
  · with_reducible_and_instances exact isCompactOperator_sqPerp hw hinv
  · with_reducible_and_instances exact hne

end Perp

/-! ### The top of `F²` on the complement -/

section Top

variable {ι : Type*} {c : ℝ} {w : ι → ℝ → ℝ} {μw : ι → ℝ}

/-- **The top eigenvector of `F²` on the complement**: an even `f ⊥ W` with `⟨Kf, f⟩ ≥ ½‖f‖²` forces an eigenvector
`h ⊥ W` of `F²` with eigenvalue `ν ≥ π/c`. -/
theorem exists_top (hc : 0 < c) (hw : ∀ i, ContinuousOn (w i) (Icc (-1) 1))
    (hweven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hwμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (w i) s = μw i * w i s)
    {f : ℝ → ℝ} (hf : Continuous f) (hfeven : ∀ s, f (-s) = f s) (hf0 : 0 < ∫ s in (-1 : ℝ)..1, f s ^ 2)
    (horth : ∀ i, ∫ s in (-1 : ℝ)..1, f s * w i s = 0)
    (hK : 1 / 2 * ∫ s in (-1 : ℝ)..1, f s ^ 2 ≤ c / π * ∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f ξ ^ 2) :
    ∃ (ν : ℝ) (h : Cvs.WeilForm.WeilFormOnWindowL2.window 1), h ∈ compl hw ∧ h ≠ 0 ∧ sqCLM c h = ν • h ∧ π / c ≤ ν := by
  set fC := cutCls hf with hfC
  -- `fC ⊥ W`
  have hfU : fC ∈ compl hw := by
    rw [mem_compl]
    intro i
    rw [inner_cut_classes (rep_wCls hw i) (rep_cutCls hf)]
    have hv : Continuous (fun s => clampExt (w i) s * f s) := (continuous_clampExt (hw i)).mul hf
    have hve : ∀ s, clampExt (w i) (-s) * f (-s) = clampExt (w i) s * f s := fun s => by
      rw [clampExt_neg (hweven i), hfeven]
    have h2 := integral_even_eq_two_mul hv hve
    have h3 : ∫ s in (-1 : ℝ)..1, clampExt (w i) s * f s = 0 := by
      rw [← horth i]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      simp only [clampExt_of_mem hs]; ring
    have h4 : ∫ s in (0 : ℝ)..1, w i s * f s = ∫ s in (0 : ℝ)..1, clampExt (w i) s * f s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le zero_le_one] at hs
      simp only [clampExt_of_mem ⟨by linarith [hs.1], hs.2⟩]
    linarith
  -- the Rayleigh quotient of `fC`
  have hnorm : ‖fC‖ ^ 2 = ∫ s in (0 : ℝ)..1, f s ^ 2 := sq_norm_cut_class (rep_cutCls hf)
  have hF : ‖cosMap c fC‖ ^ 2 = ∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f ξ ^ 2 := by
    rw [sq_norm_cut_class (rep_cosMap c fC)]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    simp only [hfC, cosFn_cutCls hf hfeven]
  have hhalf : ∫ s in (-1 : ℝ)..1, f s ^ 2 = 2 * ∫ s in (0 : ℝ)..1, f s ^ 2 :=
    integral_even_eq_two_mul (hf.pow 2) (fun s => by rw [hfeven])
  have hray : π / c * ‖fC‖ ^ 2 ≤ (inner ℝ (sqCLM c fC) fC : ℝ) := by
    rw [inner_sqCLM_self, hF, hnorm]
    have hπ : 0 < π := pi_pos
    rw [hhalf] at hK
    have : π / c * (c / π * ∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f ξ ^ 2)
        = ∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f ξ ^ 2 := by field_simp
    nlinarith [div_pos hπ hc]
  have hfC0 : 0 < ‖fC‖ ^ 2 := by rw [hnorm]; linarith
  -- the restriction of `F²` to the complement
  have hmaps : ∀ v : Cvs.WeilForm.WeilFormOnWindowL2.window 1, v ∈ compl hw → sqCLM c v ∈ compl hw :=
    fun v hv => sqCLM_mem_compl hw hweven hwμ hv
  set T := sqPerp c hw hmaps with hT
  set fU : ↥(compl hw) := ⟨fC, hfU⟩
  have hfUray : π / c * ‖fU‖ ^ 2 ≤ (inner ℝ (T fU) fU : ℝ) := hray
  have hne : T ≠ 0 := by
    intro h0
    have : (inner ℝ (T fU) fU : ℝ) = 0 := by rw [h0]; simp
    have hpos : 0 < π / c * ‖fU‖ ^ 2 := mul_pos (div_pos pi_pos hc) hfC0
    linarith
  have hle := Cvs.WeilForm.KernelOperatorParitySectors.inner_apply_le_norm T fU
  have hν : π / c ≤ ‖T‖ := by
    have h1 : π / c * ‖fU‖ ^ 2 ≤ ‖T‖ * ‖fU‖ ^ 2 := hfUray.trans hle
    exact le_of_mul_le_mul_right h1 hfC0
  rcases eigenvector_sqPerp hw hmaps hne with ⟨x, hx0, hx⟩ | ⟨x, hx0, hx⟩
  · refine ⟨‖T‖, x, x.2, fun h => hx0 (Subtype.ext h), ?_, hν⟩
    have := congrArg (fun v : ↥(compl hw) => (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1)) hx
    simpa [sqPerp_coe] using this
  · exfalso
    have hpos : 0 ≤ (inner ℝ (T x) x : ℝ) := by
      show 0 ≤ (inner ℝ (sqCLM c (x : Cvs.WeilForm.WeilFormOnWindowL2.window 1)) (x : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : ℝ)
      rw [inner_sqCLM_self]; positivity
    have hTx : (inner ℝ (T x) x : ℝ) = -‖T‖ * ‖x‖ ^ 2 := by
      have e1 : (inner ℝ (T x) x : ℝ) = (-‖T‖) * (inner ℝ x x : ℝ) := by
        rw [hx]; exact real_inner_smul_left x x _
      rw [e1, real_inner_self_eq_norm_sq]
    have hx2 : 0 < ‖x‖ ^ 2 := by
      have : x ≠ 0 := hx0
      positivity
    have hT0 : 0 < ‖T‖ := lt_of_lt_of_le (div_pos pi_pos hc) hν
    nlinarith

end Top

/-! ### Smooth representatives of eigenvectors of `F²` -/

/-- If `rep v = 1_{(0,1]} h` with `h` even and continuous, then `F v = psi c h`. -/
theorem cosFn_of_rep {c : ℝ} {h : ℝ → ℝ} (hh : Continuous h) (heven : ∀ s, h (-s) = h s)
    {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} (hv : rep v =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h) (ξ : ℝ) :
    cosFn c v ξ = Cvs.L2a.AngularProlateTailPositive.psi c h ξ := by
  have e : cosFn c v ξ = cosFn c (cutCls hh) ξ := by
    unfold cosFn
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hv, rep_cutCls hh] with s h1 h2
    rw [h1, h2]
  rw [e, cosFn_cutCls hh heven]

/-- The smooth representative `ν⁻¹ psi c (F v)` of an eigenvector of `F²`. -/
def smRep (c ν : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) : ℝ :=
  ν⁻¹ * Cvs.L2a.AngularProlateTailPositive.psi c (cosFn c v) ξ

/-- Its derivative. -/
def smRep₁ (c ν : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) : ℝ :=
  ν⁻¹ * Cvs.Prolate.SlepianCommutingRelation.kint (cosFn c v) (fun ξ s => -(c * s * sin (c * ξ * s))) ξ

/-- Its second derivative. -/
def smRep₂ (c ν : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) : ℝ :=
  ν⁻¹ * Cvs.Prolate.SlepianCommutingRelation.kint (cosFn c v) (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) ξ

/-- `psi c g` has derivative `kint g (−cs sin(cξs))` for `g` continuous on `[−1, 1]`. -/
theorem hasDerivAt_psi {c : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1)) (ξ : ℝ) :
    HasDerivAt (Cvs.L2a.AngularProlateTailPositive.psi c g)
      (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ) ξ := by
  apply Cvs.Prolate.SlepianCommutingRelation.hasDerivAt_kint (C := |c|) hg (fun s => by fun_prop) (fun ξ => by fun_prop)
    (fun ξ => by fun_prop)
  · intro ξ s
    have := ((hasDerivAt_id ξ).const_mul c |>.mul_const s).cos
    refine this.congr_deriv ?_; simp; ring
  · intro ξ s hs
    rw [abs_neg, abs_mul, abs_mul]
    calc |c| * |s| * |sin (c * ξ * s)| ≤ |c| * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg c)) (abs_sin_le_one _) (abs_nonneg _) (by positivity)
      _ = |c| := by ring

/-- `kint g (−cs sin(cξs))` has derivative `kint g (−c²s² cos(cξs))`. -/
theorem hasDerivAt_psi₁ {c : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1)) (ξ : ℝ) :
    HasDerivAt (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s))))
      (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) ξ) ξ := by
  apply Cvs.Prolate.SlepianCommutingRelation.hasDerivAt_kint (C := c ^ 2) hg (fun s => by fun_prop) (fun ξ => by fun_prop)
    (fun ξ => by fun_prop)
  · intro ξ s
    have := (((hasDerivAt_id ξ).const_mul c |>.mul_const s).sin.const_mul (c * s)).neg
    refine this.congr_deriv ?_; simp; ring
  · intro ξ s hs
    rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_nonneg (sq_nonneg s)]
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [abs_nonneg s, sq_abs s]
    calc c ^ 2 * s ^ 2 * |cos (c * ξ * s)| ≤ c ^ 2 * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs2 (sq_nonneg c)) (abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ = c ^ 2 := by ring

theorem continuous_kint {c : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1)) :
    Continuous (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))) := by
  have h : ∀ ξ, HasDerivAt (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))))
      (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => (c ^ 3 * s ^ 3 * sin (c * ξ * s))) ξ) ξ := by
    intro ξ
    apply Cvs.Prolate.SlepianCommutingRelation.hasDerivAt_kint (C := |c| ^ 3) hg (fun s => by fun_prop) (fun ξ => by fun_prop)
      (fun ξ => by fun_prop)
    · intro ξ s
      have := ((((hasDerivAt_id ξ).const_mul c |>.mul_const s).cos).const_mul (c ^ 2 * s ^ 2)).neg
      refine this.congr_deriv ?_; simp; ring
    · intro ξ s hs
      rw [abs_mul, abs_mul, abs_pow, abs_pow]
      have h3 : |s| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
      calc |c| ^ 3 * |s| ^ 3 * |sin (c * ξ * s)| ≤ |c| ^ 3 * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h3 (by positivity)) (abs_sin_le_one _) (abs_nonneg _)
              (by positivity)
        _ = |c| ^ 3 := by ring
  exact continuous_iff_continuousAt.2 fun ξ => (h ξ).continuousAt

section Smooth

variable {c ν : ℝ} {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1}

theorem hasDerivAt_smRep (ξ : ℝ) : HasDerivAt (smRep c ν v) (smRep₁ c ν v ξ) ξ :=
  (hasDerivAt_psi (continuous_cosFn c v).continuousOn ξ).const_mul ν⁻¹

theorem hasDerivAt_smRep₁ (ξ : ℝ) : HasDerivAt (smRep₁ c ν v) (smRep₂ c ν v ξ) ξ :=
  (hasDerivAt_psi₁ (continuous_cosFn c v).continuousOn ξ).const_mul ν⁻¹

theorem continuous_smRep : Continuous (smRep c ν v) :=
  continuous_iff_continuousAt.2 fun ξ => (hasDerivAt_smRep ξ).continuousAt

theorem continuous_smRep₁ : Continuous (smRep₁ c ν v) :=
  continuous_iff_continuousAt.2 fun ξ => (hasDerivAt_smRep₁ ξ).continuousAt

theorem continuous_smRep₂ : Continuous (smRep₂ c ν v) :=
  continuous_const.mul (continuous_kint (continuous_cosFn c v).continuousOn)

theorem smRep_neg (ξ : ℝ) : smRep c ν v (-ξ) = smRep c ν v ξ := by
  unfold smRep
  refine congrArg (ν⁻¹ * ·) ?_
  show ∫ s in (-1 : ℝ)..1, cosFn c v s * cos (c * -ξ * s) = ∫ s in (-1 : ℝ)..1, cosFn c v s * cos (c * ξ * s)
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show c * -ξ * s = -(c * ξ * s) by ring, cos_neg]

theorem smRep₁_neg (ξ : ℝ) : smRep₁ c ν v (-ξ) = -smRep₁ c ν v ξ := by
  unfold smRep₁ Cvs.Prolate.SlepianCommutingRelation.kint
  rw [← mul_neg, ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only
  rw [show c * -ξ * s = -(c * ξ * s) by ring, sin_neg]
  ring

theorem smRep₂_neg (ξ : ℝ) : smRep₂ c ν v (-ξ) = smRep₂ c ν v ξ := by
  unfold smRep₂ Cvs.Prolate.SlepianCommutingRelation.kint
  refine congrArg (ν⁻¹ * ·) ?_
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only
  rw [show c * -ξ * s = -(c * ξ * s) by ring, cos_neg]

theorem integral_cosFn_add {k : ℝ → ℝ} (hk : Continuous k) (u v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    ∫ s in (-1 : ℝ)..1, cosFn c (u + v) s * k s
      = (∫ s in (-1 : ℝ)..1, cosFn c u s * k s) + ∫ s in (-1 : ℝ)..1, cosFn c v s * k s := by
  have hu : IntervalIntegrable (fun s => cosFn c u s * k s) volume (-1) 1 :=
    ((continuous_cosFn c u).mul hk).intervalIntegrable _ _
  have hv : IntervalIntegrable (fun s => cosFn c v s * k s) volume (-1) 1 :=
    ((continuous_cosFn c v).mul hk).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add hu hv]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [cosFn_add]; ring

theorem integral_cosFn_smul {k : ℝ → ℝ} (t : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
    ∫ s in (-1 : ℝ)..1, cosFn c (t • v) s * k s = t * ∫ s in (-1 : ℝ)..1, cosFn c v s * k s := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [cosFn_smul]; ring

theorem smRep_add (u v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    smRep c ν (u + v) ξ = smRep c ν u ξ + smRep c ν v ξ := by
  show ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c (u + v) s * cos (c * ξ * s)
    = ν⁻¹ * (∫ s in (-1 : ℝ)..1, cosFn c u s * cos (c * ξ * s)) + ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c v s * cos (c * ξ * s)
  rw [integral_cosFn_add (k := fun s => cos (c * ξ * s)) (by fun_prop)]; ring

theorem smRep_smul (t : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    smRep c ν (t • v) ξ = t * smRep c ν v ξ := by
  show ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c (t • v) s * cos (c * ξ * s)
    = t * (ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c v s * cos (c * ξ * s))
  rw [integral_cosFn_smul (k := fun s => cos (c * ξ * s))]; ring

theorem smRep₁_add (u v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    smRep₁ c ν (u + v) ξ = smRep₁ c ν u ξ + smRep₁ c ν v ξ := by
  show ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c (u + v) s * -(c * s * sin (c * ξ * s))
    = ν⁻¹ * (∫ s in (-1 : ℝ)..1, cosFn c u s * -(c * s * sin (c * ξ * s)))
      + ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c v s * -(c * s * sin (c * ξ * s))
  rw [integral_cosFn_add (k := fun s => -(c * s * sin (c * ξ * s))) (by fun_prop)]; ring

theorem smRep₁_smul (t : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    smRep₁ c ν (t • v) ξ = t * smRep₁ c ν v ξ := by
  show ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c (t • v) s * -(c * s * sin (c * ξ * s))
    = t * (ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c v s * -(c * s * sin (c * ξ * s)))
  rw [integral_cosFn_smul (k := fun s => -(c * s * sin (c * ξ * s)))]; ring

theorem smRep₂_add (u v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    smRep₂ c ν (u + v) ξ = smRep₂ c ν u ξ + smRep₂ c ν v ξ := by
  show ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c (u + v) s * -(c ^ 2 * s ^ 2 * cos (c * ξ * s))
    = ν⁻¹ * (∫ s in (-1 : ℝ)..1, cosFn c u s * -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))
      + ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c v s * -(c ^ 2 * s ^ 2 * cos (c * ξ * s))
  rw [integral_cosFn_add (k := fun s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) (by fun_prop)]; ring

theorem smRep₂_smul (t : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (ξ : ℝ) :
    smRep₂ c ν (t • v) ξ = t * smRep₂ c ν v ξ := by
  show ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c (t • v) s * -(c ^ 2 * s ^ 2 * cos (c * ξ * s))
    = t * (ν⁻¹ * ∫ s in (-1 : ℝ)..1, cosFn c v s * -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))
  rw [integral_cosFn_smul (k := fun s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))]; ring

/-- **An eigenvector of `F²` is represented by its smooth representative**: `rep v = 1_{(0,1]} ṽ` a.e. -/
theorem rep_eq_smRep (hν : ν ≠ 0) (hv : sqCLM c v = ν • v) :
    rep v =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1 (smRep c ν v) := by
  have h1 : rep (sqCLM c v) =ᵐ[volume] Cvs.WeilForm.WindowCutBoundedBridge.cut 1
      (Cvs.L2a.AngularProlateTailPositive.psi c (cosFn c v)) := by
    rw [sqCLM_apply]
    filter_upwards [rep_cosMap c (cosMap c v)] with x hx
    rw [hx]
    unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
    by_cases hxm : x ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem hxm, indicator_of_mem hxm]
      exact cosFn_cutCls (continuous_cosFn c v) (cosFn_neg c v) x
    · rw [indicator_of_notMem hxm, indicator_of_notMem hxm]
  rw [hv] at h1
  filter_upwards [h1, Cvs.WeilForm.ChannelKernelBoundedOperator.rep_smul_ae ν v] with x hx1 hx2
  rw [hx2] at hx1
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut at hx1 ⊢
  by_cases hxm : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxm] at hx1 ⊢
    unfold smRep
    rw [← hx1]
    field_simp
  · rw [indicator_of_notMem hxm] at hx1 ⊢
    exact (mul_eq_zero.1 hx1).resolve_left hν

/-- `F v = psi c ṽ` for an eigenvector `v` of `F²`. -/
theorem cosFn_eq_psi_smRep (hν : ν ≠ 0) (hv : sqCLM c v = ν • v) (ξ : ℝ) :
    cosFn c v ξ = Cvs.L2a.AngularProlateTailPositive.psi c (smRep c ν v) ξ :=
  cosFn_of_rep continuous_smRep smRep_neg (rep_eq_smRep hν hv) ξ

/-- **`ṽ = ν⁻¹ F²ṽ` pointwise.** -/
theorem smRep_eq (hν : ν ≠ 0) (hv : sqCLM c v = ν • v) (ξ : ℝ) :
    smRep c ν v ξ = ν⁻¹ * Cvs.L2a.AngularProlateTailPositive.psi c (Cvs.L2a.AngularProlateTailPositive.psi c (smRep c ν v)) ξ := by
  have : cosFn c v = Cvs.L2a.AngularProlateTailPositive.psi c (smRep c ν v) := funext (cosFn_eq_psi_smRep hν hv)
  show ν⁻¹ * Cvs.L2a.AngularProlateTailPositive.psi c (cosFn c v) ξ = _
  rw [this]

end Smooth

/-! ### Slepian's commutation for every `C²` function -/

/-- The angular operator `A g = (1 − s²) g'' − 2s g' − c²s² g`, from given derivatives. -/
def angOp (c : ℝ) (g g₁ g₂ : ℝ → ℝ) (s : ℝ) : ℝ := (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s

/-- **Slepian's commutation**: for `g` with `g', g''` on `[−1, 1]` and `g''` continuous,
`A_ξ (psi c g) = psi c (A_s g)`, the left side computed with the derivative kernels of `psi c g`. -/
theorem psi_comm {c : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (ξ : ℝ) :
    angOp c (Cvs.L2a.AngularProlateTailPositive.psi c g)
        (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s))))
        (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))) ξ
      = Cvs.L2a.AngularProlateTailPositive.psi c (angOp c g g₁ g₂) ξ := by
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  have hK : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => cos (c * ξ * s)) (-(c * ξ * sin (c * ξ * s))) s := by
    intro s _
    have := ((hasDerivAt_id s).const_mul (c * ξ)).cos
    refine this.congr_deriv ?_; simp; ring
  have hK₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => -(c * ξ * sin (c * ξ * s)))
      (-(c ^ 2 * ξ ^ 2 * cos (c * ξ * s))) s := by
    intro s _
    have := (((hasDerivAt_id s).const_mul (c * ξ)).sin.const_mul (c * ξ)).neg
    refine this.congr_deriv ?_; simp; ring
  have ibp := Cvs.Prolate.SlepianCommutingRelation.ibp_weighted hg hg₁ hK hK₁ hg₂c (by fun_prop)
  have hI : ∀ k : ℝ → ℝ, Continuous k → IntervalIntegrable (fun s => g s * k s) volume (-1) 1 :=
    fun k hk => (hgc.mul hk.continuousOn).intervalIntegrable
  have hL : angOp c (Cvs.L2a.AngularProlateTailPositive.psi c g)
        (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s))))
        (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s)))) ξ
      = ∫ s in (-1 : ℝ)..1, g s * ((1 - ξ ^ 2) * -(c ^ 2 * s ^ 2 * cos (c * ξ * s))
          - 2 * ξ * -(c * s * sin (c * ξ * s)) - c ^ 2 * ξ ^ 2 * cos (c * ξ * s)) := by
    unfold angOp Cvs.L2a.AngularProlateTailPositive.psi Cvs.Prolate.SlepianCommutingRelation.kint
    simp only []
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    · exact ((hI _ (by fun_prop)).const_mul _).sub ((hI _ (by fun_prop)).const_mul _)
    · exact (hI _ (by fun_prop)).const_mul _
    · exact (hI _ (by fun_prop)).const_mul _
    · exact (hI _ (by fun_prop)).const_mul _
  have hR : Cvs.L2a.AngularProlateTailPositive.psi c (angOp c g g₁ g₂) ξ
      = (∫ s in (-1 : ℝ)..1, g s * ((1 - s ^ 2) * -(c ^ 2 * ξ ^ 2 * cos (c * ξ * s))
          - 2 * s * -(c * ξ * sin (c * ξ * s))))
        - ∫ s in (-1 : ℝ)..1, g s * (c ^ 2 * s ^ 2 * cos (c * ξ * s)) := by
    rw [ibp]
    unfold angOp Cvs.L2a.AngularProlateTailPositive.psi Cvs.Prolate.SlepianCommutingRelation.kint
    simp only []
    rw [← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    · exact ((((continuousOn_const.sub (continuousOn_id.pow 2)).mul hg₂c).sub
        ((continuousOn_const.mul continuousOn_id).mul hg₁c)).mul (by fun_prop)).intervalIntegrable
    · exact hI _ (by fun_prop)
  rw [hL, hR, ← intervalIntegral.integral_sub (hI _ (by fun_prop)) (hI _ (by fun_prop))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hk := Cvs.Prolate.SlepianCommutingRelation.kernel_sym c ξ s
  linear_combination (-(g s)) * hk

/-! ### Cut classes: algebra -/

theorem cutCls_eq {h₁ h₂ : ℝ → ℝ} (hh₁ : Continuous h₁) (hh₂ : Continuous h₂)
    (h : ∀ s ∈ Ioc (0 : ℝ) 1, h₁ s = h₂ s) : cutCls hh₁ = cutCls hh₂ := by
  refine Cvs.WeilForm.ChannelKernelBoundedOperator.window_ext ?_
  filter_upwards [rep_cutCls hh₁, rep_cutCls hh₂] with x hx1 hx2
  rw [hx1, hx2]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hxm : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxm, indicator_of_mem hxm, h x hxm]
  · rw [indicator_of_notMem hxm, indicator_of_notMem hxm]

theorem cutCls_smul {h : ℝ → ℝ} (hh : Continuous h) (t : ℝ) (hth : Continuous fun s => t * h s) :
    cutCls hth = t • cutCls hh := by
  refine Cvs.WeilForm.ChannelKernelBoundedOperator.window_ext ?_
  filter_upwards [rep_cutCls hth, Cvs.WeilForm.ChannelKernelBoundedOperator.rep_smul_ae t (cutCls hh), rep_cutCls hh] with x h1 h2 h3
  rw [h1, h2, h3]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hxm : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxm, indicator_of_mem hxm]
  · rw [indicator_of_notMem hxm, indicator_of_notMem hxm, mul_zero]

theorem cutCls_add {h₁ h₂ : ℝ → ℝ} (hh₁ : Continuous h₁) (hh₂ : Continuous h₂)
    (hh : Continuous fun s => h₁ s + h₂ s) : cutCls hh = cutCls hh₁ + cutCls hh₂ := by
  refine Cvs.WeilForm.ChannelKernelBoundedOperator.window_ext ?_
  filter_upwards [rep_cutCls hh, Cvs.WeilForm.TruncatedFormPolarised.rep_add_ae (cutCls hh₁) (cutCls hh₂), rep_cutCls hh₁,
    rep_cutCls hh₂] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hxm : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxm, indicator_of_mem hxm, indicator_of_mem hxm]
  · rw [indicator_of_notMem hxm, indicator_of_notMem hxm, indicator_of_notMem hxm, add_zero]

/-- `F(1_{(0,1]} h) = 1_{(0,1]} psi c h` for `h` even and continuous. -/
theorem cosMap_cutCls {c : ℝ} {h : ℝ → ℝ} (hh : Continuous h) (heven : ∀ s, h (-s) = h s) :
    cosMap c (cutCls hh) = cutCls (Cvs.Prolate.PlungeMassTrace.continuous_psi (c := c) hh.continuousOn) := by
  refine Cvs.WeilForm.ChannelKernelBoundedOperator.window_ext ?_
  filter_upwards [rep_cosMap c (cutCls hh), rep_cutCls (Cvs.Prolate.PlungeMassTrace.continuous_psi (c := c) hh.continuousOn)]
    with x h1 h2
  rw [h1, h2]
  unfold Cvs.WeilForm.WindowCutBoundedBridge.cut
  by_cases hxm : x ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hxm, indicator_of_mem hxm, cosFn_cutCls hh heven]
  · rw [indicator_of_notMem hxm, indicator_of_notMem hxm]

theorem psi_neg {c : ℝ} (g : ℝ → ℝ) (ξ : ℝ) :
    Cvs.L2a.AngularProlateTailPositive.psi c g (-ξ) = Cvs.L2a.AngularProlateTailPositive.psi c g ξ := by
  show ∫ s in (-1 : ℝ)..1, g s * cos (c * -ξ * s) = ∫ s in (-1 : ℝ)..1, g s * cos (c * ξ * s)
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [show c * -ξ * s = -(c * ξ * s) by ring, cos_neg]

/-- `F²(1_{(0,1]} h) = 1_{(0,1]} psi c (psi c h)` for `h` even and continuous. -/
theorem sqCLM_cutCls {c : ℝ} {h : ℝ → ℝ} (hh : Continuous h) (heven : ∀ s, h (-s) = h s) :
    sqCLM c (cutCls hh) = cutCls (Cvs.Prolate.PlungeMassTrace.continuous_psi (c := c)
      (Cvs.Prolate.PlungeMassTrace.continuous_psi (c := c) hh.continuousOn).continuousOn) := by
  rw [sqCLM_apply, cosMap_cutCls hh heven, cosMap_cutCls _ (psi_neg h)]

/-! ### Symmetry of the angular operator -/

/-- **`A` is symmetric on `C²[−1, 1]`**: `∫ g · A K = ∫ A g · K`. -/
theorem integral_mul_angOp {c : ℝ} {g g₁ g₂ K K₁ K₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hK : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt K (K₁ s) s) (hK₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt K₁ (K₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hK₂c : ContinuousOn K₂ (uIcc (-1) 1)) :
    ∫ s in (-1 : ℝ)..1, g s * angOp c K K₁ K₂ s = ∫ s in (-1 : ℝ)..1, angOp c g g₁ g₂ s * K s := by
  have ibp := Cvs.Prolate.SlepianCommutingRelation.ibp_weighted hg hg₁ hK hK₁ hg₂c hK₂c
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  have hKc : ContinuousOn K (uIcc (-1) 1) := fun s hs => (hK s hs).continuousAt.continuousWithinAt
  have hK₁c : ContinuousOn K₁ (uIcc (-1) 1) := fun s hs => (hK₁ s hs).continuousAt.continuousWithinAt
  have e1 : ∀ s, g s * angOp c K K₁ K₂ s = g s * ((1 - s ^ 2) * K₂ s - 2 * s * K₁ s) - c ^ 2 * s ^ 2 * g s * K s := by
    intro s; unfold angOp; ring
  have e2 : ∀ s, angOp c g g₁ g₂ s * K s = ((1 - s ^ 2) * g₂ s - 2 * s * g₁ s) * K s - c ^ 2 * s ^ 2 * g s * K s := by
    intro s; unfold angOp; ring
  simp_rw [e1, e2]
  have hi3 : IntervalIntegrable (fun s => c ^ 2 * s ^ 2 * g s * K s) volume (-1) 1 :=
    ((((continuousOn_const.mul (continuousOn_id.pow 2)).mul hgc).mul hKc)).intervalIntegrable
  rw [intervalIntegral.integral_sub _ hi3, intervalIntegral.integral_sub _ hi3, ibp]
  · exact ((((continuousOn_const.sub (continuousOn_id.pow 2)).mul hg₂c).sub
      ((continuousOn_const.mul continuousOn_id).mul hg₁c)).mul hKc).intervalIntegrable
  · exact (hgc.mul (((continuousOn_const.sub (continuousOn_id.pow 2)).mul hK₂c).sub
      ((continuousOn_const.mul continuousOn_id).mul hK₁c))).intervalIntegrable

/-! ### The angular operator on the smooth representatives -/

section Ang

variable {c ν : ℝ}

/-- `A ṽ`, the angular operator on the smooth representative of `v`. -/
def angRep (c ν : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) : ℝ → ℝ :=
  angOp c (smRep c ν v) (smRep₁ c ν v) (smRep₂ c ν v)

theorem continuous_angRep {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} : Continuous (angRep c ν v) := by
  have h0 := continuous_smRep (c := c) (ν := ν) (v := v)
  have h1 := continuous_smRep₁ (c := c) (ν := ν) (v := v)
  have h2 := continuous_smRep₂ (c := c) (ν := ν) (v := v)
  unfold angRep angOp
  fun_prop

theorem angRep_neg {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} (s : ℝ) : angRep c ν v (-s) = angRep c ν v s := by
  unfold angRep angOp
  rw [smRep_neg, smRep₁_neg, smRep₂_neg]
  ring

theorem angRep_add (u v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (s : ℝ) :
    angRep c ν (u + v) s = angRep c ν u s + angRep c ν v s := by
  unfold angRep angOp
  rw [smRep_add, smRep₁_add, smRep₂_add]
  ring

theorem angRep_smul (t : ℝ) (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) (s : ℝ) :
    angRep c ν (t • v) s = t * angRep c ν v s := by
  unfold angRep angOp
  rw [smRep_smul, smRep₁_smul, smRep₂_smul]
  ring

/-- **`F²` acts on `Aṽ` by `ν`**: two commutations and `F²ṽ = νṽ`. -/
theorem psi_psi_angRep {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} (hν : ν ≠ 0) (hv : sqCLM c v = ν • v) (ξ : ℝ) :
    Cvs.L2a.AngularProlateTailPositive.psi c (Cvs.L2a.AngularProlateTailPositive.psi c (angRep c ν v)) ξ = ν * angRep c ν v ξ := by
  have hsm : ContinuousOn (smRep c ν v) (uIcc (-1) 1) := continuous_smRep.continuousOn
  set P := Cvs.L2a.AngularProlateTailPositive.psi c (smRep c ν v) with hPdef
  set P₁ := Cvs.Prolate.SlepianCommutingRelation.kint (smRep c ν v) (fun ξ s => -(c * s * sin (c * ξ * s))) with hP₁def
  set P₂ := Cvs.Prolate.SlepianCommutingRelation.kint (smRep c ν v) (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) with hP₂def
  have h1 : Cvs.L2a.AngularProlateTailPositive.psi c (angRep c ν v) = angOp c P P₁ P₂ := by
    funext x
    exact (psi_comm (fun s _ => hasDerivAt_smRep s) (fun s _ => hasDerivAt_smRep₁ s)
      continuous_smRep₂.continuousOn x).symm
  have hP : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt P (P₁ s) s := fun s _ => hasDerivAt_psi hsm s
  have hP₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt P₁ (P₂ s) s := fun s _ => hasDerivAt_psi₁ hsm s
  have hP₂c : ContinuousOn P₂ (uIcc (-1) 1) := (continuous_kint hsm).continuousOn
  have h2 := psi_comm (c := c) hP hP₁ hP₂c ξ
  rw [h1, ← h2]
  have hPcont : Continuous P := Cvs.Prolate.PlungeMassTrace.continuous_psi continuous_smRep.continuousOn
  have hQ : ∀ x, Cvs.L2a.AngularProlateTailPositive.psi c P x = ν * smRep c ν v x := by
    intro x
    rw [smRep_eq hν hv x]
    field_simp
    rfl
  have hQfun : Cvs.L2a.AngularProlateTailPositive.psi c P = fun x => ν * smRep c ν v x := funext hQ
  have hQ1 : ∀ x, Cvs.Prolate.SlepianCommutingRelation.kint P (fun ξ s => -(c * s * sin (c * ξ * s))) x = ν * smRep₁ c ν v x := by
    intro x
    have d1 := hasDerivAt_psi (c := c) hPcont.continuousOn x
    have d2 : HasDerivAt (Cvs.L2a.AngularProlateTailPositive.psi c P) (ν * smRep₁ c ν v x) x := by
      rw [hQfun]; exact (hasDerivAt_smRep x).const_mul ν
    exact d1.unique d2
  have hQ1fun : Cvs.Prolate.SlepianCommutingRelation.kint P (fun ξ s => -(c * s * sin (c * ξ * s))) = fun x => ν * smRep₁ c ν v x :=
    funext hQ1
  have hQ2 : ∀ x, Cvs.Prolate.SlepianCommutingRelation.kint P (fun ξ s => -(c ^ 2 * s ^ 2 * cos (c * ξ * s))) x
      = ν * smRep₂ c ν v x := by
    intro x
    have d1 := hasDerivAt_psi₁ (c := c) hPcont.continuousOn x
    have d2 : HasDerivAt (Cvs.Prolate.SlepianCommutingRelation.kint P (fun ξ s => -(c * s * sin (c * ξ * s))))
        (ν * smRep₂ c ν v x) x := by
      rw [hQ1fun]; exact (hasDerivAt_smRep₁ x).const_mul ν
    exact d1.unique d2
  unfold angOp angRep
  rw [hQ ξ, hQ1 ξ, hQ2 ξ]
  unfold angOp
  ring

/-- **`F²` preserves `Aṽ`'s class with eigenvalue `ν`.** -/
theorem sqCLM_angCls {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} (hν : ν ≠ 0) (hv : sqCLM c v = ν • v) :
    sqCLM c (cutCls (continuous_angRep (c := c) (ν := ν) (v := v)))
      = ν • cutCls (continuous_angRep (c := c) (ν := ν) (v := v)) := by
  rw [sqCLM_cutCls continuous_angRep angRep_neg]
  have hc2 : Continuous fun s => ν * angRep c ν v s := continuous_const.mul continuous_angRep
  rw [cutCls_eq _ hc2 (fun s _ => psi_psi_angRep hν hv s)]
  exact cutCls_smul continuous_angRep ν hc2

end Ang

/-! ### Pairings on the eigenspace -/

/-- An eigenvector of `F²` is the cut class of its smooth representative. -/
theorem eq_cutCls_smRep {c ν : ℝ} {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} (hν : ν ≠ 0) (hv : sqCLM c v = ν • v) :
    v = cutCls (continuous_smRep (c := c) (ν := ν) (v := v)) :=
  Cvs.WeilForm.ChannelKernelBoundedOperator.window_ext ((rep_eq_smRep hν hv).trans (rep_cutCls _).symm)

/-- Two continuous functions with the same cut class agree on `[0, 1]`. -/
theorem eqOn_of_cutCls_eq {h₁ h₂ : ℝ → ℝ} (hh₁ : Continuous h₁) (hh₂ : Continuous h₂)
    (he : cutCls hh₁ = cutCls hh₂) : EqOn h₁ h₂ (Icc 0 1) := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h₁ x = Cvs.WeilForm.WindowCutBoundedBridge.cut 1 h₂ x := by
    filter_upwards [rep_cutCls hh₁, rep_cutCls hh₂] with x h1 h2
    rw [← h1, ← h2, he]
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]; simp
  have hres : h₁ =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] h₂ := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae, h0] with x hx hx0 hxm
    have hxm' : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hxm.1 (Ne.symm hx0), hxm.2⟩
    rwa [Cvs.WeilForm.WindowCutBoundedBridge.cut_of_mem hxm', Cvs.WeilForm.WindowCutBoundedBridge.cut_of_mem hxm'] at hx
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num) hres hh₁.continuousOn hh₂.continuousOn

section Pair

variable {ι : Type*} {c ν : ℝ} {w w₁ w₂ : ι → ℝ → ℝ} {χw μw : ι → ℝ}

/-- **`Aṽ ⊥ W`** for `v ⊥ W`: `A` is symmetric and the rungs solve `A w = −χ w`. -/
theorem inner_wCls_angCls (hw : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w i) (w₁ i s) s)
    (hw₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w₁ i) (w₂ i s) s)
    (hw₂c : ∀ i, ContinuousOn (w₂ i) (uIcc (-1) 1))
    (hwang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * w₂ i s - 2 * s * w₁ i s - c ^ 2 * s ^ 2 * w i s + χw i * w i s = 0)
    (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) (hweven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} (hν : ν ≠ 0) (hv : sqCLM c v = ν • v) (hvU : v ∈ compl hwc) (i : ι) :
    (inner ℝ (wCls hwc i) (cutCls (continuous_angRep (c := c) (ν := ν) (v := v))) : ℝ) = 0 := by
  rw [inner_cut_classes (rep_wCls hwc i) (rep_cutCls _)]
  have hvi := (mem_compl hwc).1 hvU i
  rw [inner_cut_classes (rep_wCls hwc i) (rep_eq_smRep hν hv)] at hvi
  -- pass to `[−1, 1]` through the clamped extension
  have hev : ∀ (u : ℝ → ℝ), Continuous u → (∀ s, u (-s) = u s) →
      ∫ s in (0 : ℝ)..1, w i s * u s = 1 / 2 * ∫ s in (-1 : ℝ)..1, w i s * u s := by
    intro u hu hue
    have h1 := integral_even_eq_two_mul (v := fun s => clampExt (w i) s * u s)
      ((continuous_clampExt (hwc i)).mul hu) (fun s => by rw [clampExt_neg (hweven i), hue])
    have h2 : ∫ s in (-1 : ℝ)..1, clampExt (w i) s * u s = ∫ s in (-1 : ℝ)..1, w i s * u s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      simp only [clampExt_of_mem hs]
    have h3 : ∫ s in (0 : ℝ)..1, clampExt (w i) s * u s = ∫ s in (0 : ℝ)..1, w i s * u s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le zero_le_one] at hs
      simp only [clampExt_of_mem ⟨by linarith [hs.1], hs.2⟩]
    rw [← h2, ← h3, h1]; ring
  rw [hev _ continuous_angRep angRep_neg]
  rw [hev _ continuous_smRep smRep_neg] at hvi
  have hsym := integral_mul_angOp (c := c) (hw i) (hw₁ i) (fun s _ => hasDerivAt_smRep (c := c) (ν := ν) (v := v) s)
    (fun s _ => hasDerivAt_smRep₁ s) (hw₂c i) continuous_smRep₂.continuousOn
  have hode : ∫ s in (-1 : ℝ)..1, angOp c (w i) (w₁ i) (w₂ i) s * smRep c ν v s
      = -χw i * ∫ s in (-1 : ℝ)..1, w i s * smRep c ν v s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have := hwang i s hs
    unfold angOp
    linear_combination (smRep c ν v s) * this
  unfold angRep
  rw [hsym, hode]
  have : ∫ s in (-1 : ℝ)..1, w i s * smRep c ν v s = 0 := by linarith
  rw [this]; ring

/-- **`A` is symmetric on the eigenspace**: `⟨Aũ, v⟩ = ⟨u, Aṽ⟩`. -/
theorem inner_angCls_comm {u v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} (hν : ν ≠ 0) (hu : sqCLM c u = ν • u)
    (hv : sqCLM c v = ν • v) :
    (inner ℝ (cutCls (continuous_angRep (c := c) (ν := ν) (v := u))) v : ℝ)
      = (inner ℝ u (cutCls (continuous_angRep (c := c) (ν := ν) (v := v))) : ℝ) := by
  rw [inner_cut_classes (rep_cutCls _) (rep_eq_smRep hν hv), inner_cut_classes (rep_eq_smRep hν hu) (rep_cutCls _)]
  have h1 := integral_even_eq_two_mul (v := fun s => angRep c ν u s * smRep c ν v s)
    (continuous_angRep.mul continuous_smRep) (fun s => by rw [angRep_neg (v := u), smRep_neg (v := v)])
  have h2 := integral_even_eq_two_mul (v := fun s => smRep c ν u s * angRep c ν v s)
    (continuous_smRep.mul continuous_angRep) (fun s => by rw [smRep_neg (v := u), angRep_neg (v := v)])
  have hsym := integral_mul_angOp (c := c) (fun s _ => hasDerivAt_smRep (c := c) (ν := ν) (v := u) s)
    (fun s _ => hasDerivAt_smRep₁ s) (fun s _ => hasDerivAt_smRep (c := c) (ν := ν) (v := v) s)
    (fun s _ => hasDerivAt_smRep₁ s) continuous_smRep₂.continuousOn continuous_smRep₂.continuousOn
  unfold angRep at h1 h2 ⊢
  linarith

end Pair

/-! ### The angular operator on the eigenspace, and the rung -/

section Main

variable {ι : Type*} {c ν : ℝ} {w : ι → ℝ → ℝ}

/-- The `ν`-eigenspace of `F²` inside the complement of the rung classes. -/
def eigE (c ν : ℝ) (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) : Submodule ℝ (Cvs.WeilForm.WeilFormOnWindowL2.window 1) :=
  compl hwc ⊓ Module.End.eigenspace
    ((sqCLM c : Cvs.WeilForm.WeilFormOnWindowL2.window 1 →L[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window 1) :
      Cvs.WeilForm.WeilFormOnWindowL2.window 1 →ₗ[ℝ] Cvs.WeilForm.WeilFormOnWindowL2.window 1) ν

theorem mem_eigE (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) {v : Cvs.WeilForm.WeilFormOnWindowL2.window 1} :
    v ∈ eigE c ν hwc ↔ v ∈ compl hwc ∧ sqCLM c v = ν • v := by
  unfold eigE
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff]
  rfl

theorem finiteDimensional_eigE (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) (hν : ν ≠ 0) :
    FiniteDimensional ℝ ↥(eigE c ν hwc) := by
  have h := finiteDimensional_eigenspace (sqCLM c) (isCompactOperator_sqCLM c) hν
  exact Submodule.finiteDimensional_of_le inf_le_right

end Main

section Main2

variable {ι : Type*} {c ν : ℝ} {w w₁ w₂ : ι → ℝ → ℝ} {χw : ι → ℝ}

/-- The angular operator on the eigenspace. -/
def angE (hw : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w i) (w₁ i s) s)
    (hw₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w₁ i) (w₂ i s) s)
    (hw₂c : ∀ i, ContinuousOn (w₂ i) (uIcc (-1) 1))
    (hwang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * w₂ i s - 2 * s * w₁ i s - c ^ 2 * s ^ 2 * w i s + χw i * w i s = 0)
    (hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1)) (hweven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hν : ν ≠ 0) : ↥(eigE c ν hwc) →ₗ[ℝ] ↥(eigE c ν hwc) where
  toFun v := ⟨cutCls (continuous_angRep (c := c) (ν := ν) (v := (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1))), by
    have hv := (mem_eigE hwc).1 v.2
    exact (mem_eigE hwc).2 ⟨(mem_compl hwc).2 fun i =>
      inner_wCls_angCls hw hw₁ hw₂c hwang hwc hweven hν hv.2 hv.1 i, sqCLM_angCls hν hv.2⟩⟩
  map_add' u v := by
    apply Subtype.ext
    have hsum : Continuous fun s => angRep c ν (u : Cvs.WeilForm.WeilFormOnWindowL2.window 1) s
        + angRep c ν (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) s := continuous_angRep.add continuous_angRep
    show cutCls (continuous_angRep (c := c) (ν := ν) (v := (u : Cvs.WeilForm.WeilFormOnWindowL2.window 1)
        + (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1)))
      = cutCls (continuous_angRep (c := c) (ν := ν) (v := (u : Cvs.WeilForm.WeilFormOnWindowL2.window 1)))
        + cutCls (continuous_angRep (c := c) (ν := ν) (v := (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1)))
    rw [cutCls_eq _ hsum (fun s _ => angRep_add _ _ s), cutCls_add continuous_angRep continuous_angRep hsum]
  map_smul' t v := by
    apply Subtype.ext
    have hsm : Continuous fun s => t * angRep c ν (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1) s :=
      continuous_const.mul continuous_angRep
    show cutCls (continuous_angRep (c := c) (ν := ν) (v := t • (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1)))
      = t • cutCls (continuous_angRep (c := c) (ν := ν) (v := (v : Cvs.WeilForm.WeilFormOnWindowL2.window 1)))
    rw [cutCls_eq _ hsm (fun s _ => angRep_smul _ _ s), cutCls_smul continuous_angRep t hsm]

end Main2

/-! ### A rung from a test function -/

/-- **A rung from a test function**: for even angular rungs `w i` and an even continuous `f ⊥ w i` with
`½‖f‖² ≤ (c/π)∫_0^1 (psi c f)²`, there is an even angular rung `g ⊥ w i` with `(μ√(c/2π))² ≥ ½`. -/
theorem exists_rung_of_test {ι : Type*} {c : ℝ} (hc : 0 < c) {w w₁ w₂ : ι → ℝ → ℝ} {χw μw : ι → ℝ}
    (hw : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w i) (w₁ i s) s)
    (hw₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (w₁ i) (w₂ i s) s)
    (hw₂c : ∀ i, ContinuousOn (w₂ i) (uIcc (-1) 1))
    (hwang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * w₂ i s - 2 * s * w₁ i s - c ^ 2 * s ^ 2 * w i s + χw i * w i s = 0)
    (hweven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, w i (-s) = w i s)
    (hwμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c (w i) s = μw i * w i s)
    {f : ℝ → ℝ} (hf : Continuous f) (hfeven : ∀ s, f (-s) = f s) (hf0 : 0 < ∫ s in (-1 : ℝ)..1, f s ^ 2)
    (horth : ∀ i, ∫ s in (-1 : ℝ)..1, f s * w i s = 0)
    (hK : 1 / 2 * ∫ s in (-1 : ℝ)..1, f s ^ 2 ≤ c / π * ∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f ξ ^ 2) :
    ∃ (χ μ : ℝ) (g g₁ g₂ : ℝ → ℝ), (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) ∧ ContinuousOn g₂ (uIcc (-1) 1) ∧
      (∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) ∧ (∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) ∧
      (∀ s ∈ Icc (-1 : ℝ) 1, Cvs.L2a.AngularProlateTailPositive.psi c g s = μ * g s) ∧
      (∀ i, ∫ s in (-1 : ℝ)..1, g s * w i s = 0) ∧ 1 / 2 ≤ (μ * √(c / (2 * π))) ^ 2 := by
  have hwc : ∀ i, ContinuousOn (w i) (Icc (-1) 1) := fun i s hs =>
    (hw i s (by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])).continuousAt.continuousWithinAt
  obtain ⟨ν, h, hhU, hh0, hhν, hνc⟩ := exists_top hc hwc hweven hwμ hf hfeven hf0 horth hK
  have hν0 : 0 < ν := lt_of_lt_of_le (div_pos pi_pos hc) hνc
  have hν : ν ≠ 0 := hν0.ne'
  have := finiteDimensional_eigE (c := c) hwc hν
  have hhE : h ∈ eigE c ν hwc := (mem_eigE hwc).2 ⟨hhU, hhν⟩
  have : Nontrivial ↥(eigE c ν hwc) := ⟨⟨⟨h, hhE⟩, 0, fun he => hh0 (congrArg Subtype.val he)⟩⟩
  set A := angE hw hw₁ hw₂c hwang hwc hweven hν with hAdef
  have hsym : LinearMap.IsSymmetric (𝕜 := ℝ) (E := ↥(eigE c ν hwc)) A := by
    intro u v
    exact inner_angCls_comm hν ((mem_eigE hwc).1 u.2).2 ((mem_eigE hwc).1 v.2).2
  have hEV := LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional (𝕜 := ℝ) (E := ↥(eigE c ν hwc)) hsym
  obtain ⟨g, hg⟩ := hEV.exists_hasEigenvector
  set χ' := ((⨆ x : {x : ↥(eigE c ν hwc) // x ≠ 0},
    RCLike.re (inner ℝ (A (x : ↥(eigE c ν hwc))) (x : ↥(eigE c ν hwc))) / ‖(x : ↥(eigE c ν hwc))‖ ^ 2 : ℝ) : ℝ)
    with hχ'
  have hgA : A g = χ' • g := Module.End.mem_eigenspace_iff.1 hg.1
  have hg0 : g ≠ 0 := hg.2
  set gv : Cvs.WeilForm.WeilFormOnWindowL2.window 1 := (g : Cvs.WeilForm.WeilFormOnWindowL2.window 1) with hgvdef
  have hgv := (mem_eigE hwc).1 g.2
  -- `A ĝ = χ' ĝ` on `[−1, 1]`
  have hsc : Continuous fun s => χ' * smRep c ν gv s := continuous_const.mul continuous_smRep
  have hcls : cutCls (continuous_angRep (c := c) (ν := ν) (v := gv)) = cutCls hsc := by
    have e1 : ((A g : ↥(eigE c ν hwc)) : Cvs.WeilForm.WeilFormOnWindowL2.window 1)
        = cutCls (continuous_angRep (c := c) (ν := ν) (v := gv)) := rfl
    rw [← e1, hgA, cutCls_smul continuous_smRep χ' hsc]
    show χ' • gv = _
    rw [← eq_cutCls_smRep hν hgv.2]
  have heq := eqOn_of_cutCls_eq continuous_angRep hsc hcls
  have heq' : ∀ s ∈ Icc (-1 : ℝ) 1, angRep c ν gv s = χ' * smRep c ν gv s := by
    intro s hs
    rcases le_total 0 s with h0 | h0
    · exact heq ⟨h0, hs.2⟩
    · have := heq (show -s ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith [hs.1]⟩)
      simp only at this
      rwa [angRep_neg, smRep_neg] at this
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgd : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (smRep c ν gv) (smRep₁ c ν gv s) s := fun s _ => hasDerivAt_smRep s
  have hgd₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (smRep₁ c ν gv) (smRep₂ c ν gv s) s :=
    fun s _ => hasDerivAt_smRep₁ s
  have hg₂c : ContinuousOn (smRep₂ c ν gv) (uIcc (-1) 1) := continuous_smRep₂.continuousOn
  have hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * smRep₂ c ν gv s - 2 * s * smRep₁ c ν gv s
      - c ^ 2 * s ^ 2 * smRep c ν gv s + (-χ') * smRep c ν gv s = 0 := by
    intro s hs
    rw [hI] at hs
    have := heq' s hs
    unfold angRep angOp at this
    linarith
  obtain ⟨μ, hμ⟩ := Cvs.Prolate.CosineTransformEigenRelation.eigen_relation hgd hgd₁ hg₂c hang
  -- `ĝ` is not identically zero on `[−1, 1]`
  have hne : ∃ s ∈ Icc (-1 : ℝ) 1, smRep c ν gv s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hg0
    apply Subtype.ext
    show gv = 0
    have hgv2 : sqCLM c gv = ν • gv := hgv.2
    have e0 : gv = cutCls (continuous_smRep (c := c) (ν := ν) (v := gv)) := eq_cutCls_smRep hν hgv2
    have hz : cutCls (continuous_smRep (c := c) (ν := ν) (v := gv)) = cutCls (continuous_const (y := (0 : ℝ))) :=
      cutCls_eq _ _ (fun s hs => hcon s ⟨by linarith [hs.1], hs.2⟩)
    have h00 : cutCls (continuous_const (y := (0 : ℝ))) = 0 := by
      have hz' : Continuous fun s => (0 : ℝ) * smRep c ν gv s := continuous_const.mul continuous_smRep
      rw [cutCls_eq continuous_const hz' (fun s _ => by simp), cutCls_smul continuous_smRep 0 hz', zero_smul]
    rw [e0, hz, h00]
  -- orthogonality to the rungs
  have horth' : ∀ i, ∫ s in (-1 : ℝ)..1, smRep c ν gv s * w i s = 0 := by
    intro i
    have hvi := (mem_compl hwc).1 hgv.1 i
    rw [inner_cut_classes (rep_wCls hwc i) (rep_eq_smRep hν hgv.2)] at hvi
    have h1 := integral_even_eq_two_mul (v := fun s => clampExt (w i) s * smRep c ν gv s)
      ((continuous_clampExt (hwc i)).mul continuous_smRep) (fun s => by rw [clampExt_neg (hweven i), smRep_neg])
    have h2 : ∫ s in (-1 : ℝ)..1, clampExt (w i) s * smRep c ν gv s = ∫ s in (-1 : ℝ)..1, smRep c ν gv s * w i s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      simp only [clampExt_of_mem hs]; ring
    have h3 : ∫ s in (0 : ℝ)..1, clampExt (w i) s * smRep c ν gv s = ∫ s in (0 : ℝ)..1, w i s * smRep c ν gv s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le zero_le_one] at hs
      simp only [clampExt_of_mem ⟨by linarith [hs.1], hs.2⟩]
    rw [← h2, h1, h3, hvi, mul_zero]
  -- the concentration `μ²c/2π = νc/2π ≥ ½`
  obtain ⟨s₀, hs₀, hgs₀⟩ := hne
  have hpp : Cvs.L2a.AngularProlateTailPositive.psi c (Cvs.L2a.AngularProlateTailPositive.psi c (smRep c ν gv)) s₀
      = μ * (μ * smRep c ν gv s₀) := by
    show ∫ t in (-1 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c (smRep c ν gv) t * cos (c * s₀ * t) = _
    rw [← hμ s₀ hs₀]
    show _ = μ * ∫ t in (-1 : ℝ)..1, smRep c ν gv t * cos (c * s₀ * t)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hI] at ht
    simp only [hμ t ht]; ring
  have hfix := smRep_eq hν hgv.2 s₀
  rw [hpp] at hfix
  have hμν : μ ^ 2 = ν := by
    have : smRep c ν gv s₀ * (ν - μ ^ 2) = 0 := by
      field_simp at hfix
      linarith
    have := (mul_eq_zero.1 this).resolve_left hgs₀
    linarith
  refine ⟨-χ', μ, smRep c ν gv, smRep₁ c ν gv, smRep₂ c ν gv, hgd, hgd₁, hg₂c, hang, fun s _ => smRep_neg s,
    ⟨s₀, hs₀, hgs₀⟩, hμ, horth', ?_⟩
  rw [mul_pow, Real.sq_sqrt (by positivity), hμν]
  calc (1 : ℝ) / 2 = π / c * (c / (2 * π)) := by field_simp
    _ ≤ ν * (c / (2 * π)) := mul_le_mul_of_nonneg_right hνc (by positivity)

end Cvs.Prolate.SincTopIsRung
