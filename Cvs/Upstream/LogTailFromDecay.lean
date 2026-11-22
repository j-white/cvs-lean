import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The log tail of a line function with a pointwise `1/g` decay

A continuous line function with `‖F(g)‖²g² ≤ A` for `|g| ≥ T` has `∫ ‖F‖² log⁺(|g|/T) ≤ 8A/T`, since
`log y ≤ 2√y` and `∫_{|g|>T} |g|^{−3/2} = 4/√T`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex

namespace Cvs.Upstream.LogTailFromDecay

/-! ### The majorant `|g|^{-3/2}` beyond `T` -/

/-- The majorant `1_{|g| > T}·|g|^{-3/2}`. -/
def tailMaj (T : ℝ) (g : ℝ) : ℝ := (Ioi T).indicator (fun y : ℝ => y ^ (-(3 / 2) : ℝ)) |g|

theorem tailMaj_nonneg (T g : ℝ) (hT : 0 < T) : 0 ≤ tailMaj T g := by
  unfold tailMaj
  by_cases h : |g| ∈ Ioi T
  · rw [indicator_of_mem h]; exact Real.rpow_nonneg (hT.le.trans (le_of_lt h)) _
  · rw [indicator_of_notMem h]

/-- `y ↦ 1_{y > T} y^{-3/2}` is integrable on `(0, ∞)`. -/
theorem integrableOn_tailMaj {T : ℝ} (hT : 0 < T) :
    IntegrableOn ((Ioi T).indicator fun y : ℝ => y ^ (-(3 / 2) : ℝ)) (Ioi 0) := by
  have h : Integrable ((Ioi T).indicator fun y : ℝ => y ^ (-(3 / 2) : ℝ)) :=
    (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_Ioi_rpow_of_lt (by norm_num) hT)
  exact h.integrableOn

/-- **The majorant is integrable on the line**. -/
theorem integrable_tailMaj {T : ℝ} (hT : 0 < T) : Integrable (tailMaj T) := by
  have hI := integrableOn_tailMaj hT
  have hR : IntegrableOn (tailMaj T) (Ioi 0) := by
    refine hI.congr_fun (fun y hy => ?_) measurableSet_Ioi
    unfold tailMaj; rw [abs_of_pos (mem_Ioi.1 hy)]
  have hL : IntegrableOn (tailMaj T) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [neg_preimage, neg_Iic, neg_zero]
    refine ((integrableOn_Ici_iff_integrableOn_Ioi).2 hR).congr_fun (fun y _ => ?_) measurableSet_Ici
    simp [tailMaj, abs_neg]
  have := hL.union hR
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- **The majorant integrates to `4/√T`**. -/
theorem integral_tailMaj {T : ℝ} (hT : 0 < T) : ∫ g, tailMaj T g = 4 * T ^ (-(1 / 2) : ℝ) := by
  unfold tailMaj
  rw [integral_comp_abs (f := (Ioi T).indicator fun y : ℝ => y ^ (-(3 / 2) : ℝ))]
  have hsub : Ioi T ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hT.le
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 hsub,
    integral_Ioi_rpow_of_lt (by norm_num) hT]
  norm_num
  ring

/-! ### From pointwise decay to the log tail -/

/-- `log y ≤ 2√y` for `y ≥ 1`. -/
theorem log_le_two_sqrt {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ 2 * √y := by
  have hs : 0 < √y := Real.sqrt_pos.2 (by linarith)
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt (by linarith)] at h
  linarith

/-- The pointwise bound `‖F‖² log⁺(|g|/T) ≤ 2A T^{-1/2}·1_{|g|>T}|g|^{-3/2}`. -/
theorem norm_sq_mul_logPos_le {F : ℝ → ℂ} {T A : ℝ} (hT : 0 < T)
    (hF : ∀ g : ℝ, T ≤ |g| → ‖F g‖ ^ 2 * g ^ 2 ≤ A) (g : ℝ) :
    ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0 ≤ 2 * A * T ^ (-(1 / 2) : ℝ) * tailMaj T g := by
  by_cases hg : T < |g|
  · have hg0 : 0 < |g| := hT.trans hg
    have hy : 1 ≤ |g| / T := by rw [le_div_iff₀ hT]; linarith
    have hlog : 0 ≤ Real.log (|g| / T) := Real.log_nonneg hy
    rw [max_eq_left hlog]
    have hm : tailMaj T g = |g| ^ (-(3 / 2) : ℝ) := by
      unfold tailMaj; rw [indicator_of_mem (mem_Ioi.2 hg)]
    rw [hm]
    have hF' := hF g hg.le
    have hg2 : g ^ 2 = |g| ^ 2 := (sq_abs g).symm
    have hpos : 0 < |g| ^ 2 := by positivity
    have hFle : ‖F g‖ ^ 2 ≤ A / |g| ^ 2 := by rw [le_div_iff₀ hpos, ← hg2]; exact hF'
    have hA : 0 ≤ A := le_trans (by positivity) hF'
    calc ‖F g‖ ^ 2 * Real.log (|g| / T) ≤ A / |g| ^ 2 * (2 * √(|g| / T)) :=
          mul_le_mul hFle (log_le_two_sqrt hy) hlog (by positivity)
      _ = 2 * A * T ^ (-(1 / 2) : ℝ) * |g| ^ (-(3 / 2) : ℝ) := by
          rw [Real.sqrt_div' _ hT.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
            Real.rpow_neg hT.le, Real.rpow_neg hg0.le]
          have h32 : |g| ^ (3 / 2 : ℝ) = |g| ^ 2 * |g| ^ (-(1 / 2) : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hg0]; norm_num
          rw [h32, Real.rpow_neg hg0.le]
          have h1 : 0 < |g| ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hg0 _
          have h2 : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT _
          field_simp
  · have hle : |g| / T ≤ 1 := by rw [div_le_one hT]; linarith
    have hlog : Real.log (|g| / T) ≤ 0 := Real.log_nonpos (by positivity) hle
    rw [max_eq_right hlog, mul_zero]
    have hA : 0 ≤ A := le_trans (by positivity) (hF T (by rw [abs_of_pos hT]))
    have := tailMaj_nonneg T g hT
    have : 0 ≤ T ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hT.le _
    positivity

/-- **The log tail from a pointwise `1/g` decay**: a continuous `F` with `‖F(g)‖² g² ≤ A` for `|g| ≥ T > 0` has an
integrable log tail with `∫ ‖F‖² log⁺(|g|/T) ≤ 8A/T`. -/
theorem logTail_le_of_decay {F : ℝ → ℂ} (hFc : Continuous F) {T A : ℝ} (hT : 0 < T)
    (hF : ∀ g : ℝ, T ≤ |g| → ‖F g‖ ^ 2 * g ^ 2 ≤ A) :
    (Integrable fun g : ℝ => ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0)
      ∧ ∫ g : ℝ, ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0 ≤ 8 * A / T := by
  have hmaj : Integrable fun g => 2 * A * T ^ (-(1 / 2) : ℝ) * tailMaj T g := (integrable_tailMaj hT).const_mul _
  have hmeas : AEStronglyMeasurable (fun g : ℝ => ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0) volume :=
    ((hFc.norm.pow 2).aestronglyMeasurable).mul
      ((Real.measurable_log.comp (by fun_prop : Measurable fun g : ℝ => |g| / T)).max
        measurable_const).aestronglyMeasurable
  have hnn : ∀ g : ℝ, 0 ≤ ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0 := fun g =>
    mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have hI : Integrable fun g : ℝ => ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0 :=
    hmaj.mono' hmeas (Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn g)]; exact norm_sq_mul_logPos_le hT hF g)
  refine ⟨hI, ?_⟩
  calc ∫ g : ℝ, ‖F g‖ ^ 2 * max (Real.log (|g| / T)) 0
      ≤ ∫ g : ℝ, 2 * A * T ^ (-(1 / 2) : ℝ) * tailMaj T g :=
        integral_mono hI hmaj fun g => norm_sq_mul_logPos_le hT hF g
    _ = 2 * A * T ^ (-(1 / 2) : ℝ) * (4 * T ^ (-(1 / 2) : ℝ)) := by
        rw [integral_const_mul, integral_tailMaj hT]
    _ = 8 * A / T := by
        have h : T ^ (-(1 / 2) : ℝ) * T ^ (-(1 / 2) : ℝ) = T⁻¹ := by
          rw [← Real.rpow_add hT]; norm_num; exact Real.rpow_neg_one T
        calc 2 * A * T ^ (-(1 / 2) : ℝ) * (4 * T ^ (-(1 / 2) : ℝ))
            = 8 * A * (T ^ (-(1 / 2) : ℝ) * T ^ (-(1 / 2) : ℝ)) := by ring
          _ = 8 * A / T := by rw [h, div_eq_mul_inv]

end Cvs.Upstream.LogTailFromDecay

end
