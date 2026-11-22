import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionChiVariation
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Consecutive even levels couple positively

For the regular solutions `f_χ = regSol Q χ`, the tail coupling `Z_t(ξ) = ∫_ξ^1 f_χ f_t` satisfies the cross-Wronskian
form `f_χ U_t − U_χ f_t = −(t − χ) Z_t`. If `χ` is an even level and no even level lies in `(χ, χ')`, a first-zero
argument in `(t, ξ)` gives `Z_{χ'} > 0` on `(0, 1)`, and integration by parts gives `∫_0^1 s² f_χ f_χ' > 0`.
-/

noncomputable section

open Real Set Filter Topology intervalIntegral MeasureTheory Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.RegularSolutionChiVariation Cvs.Prolate.EdgeCentreSign
open scoped Interval

namespace Cvs.Prolate.EvenLevelPositiveCoupling

/-- The tail coupling `Z_t(ξ) = ∫_ξ^1 f_χ f_t`. -/
def tailC (Q : C(ℝ, ℝ)) (χ t ξ : ℝ) : ℝ := ∫ s in ξ..1, regSol Q χ s * regSol Q t s

/-- The clamp to `[0, 1]`. -/
def clamp01 (s : ℝ) : ℝ := max 0 (min s 1)

theorem clamp01_mem (s : ℝ) : clamp01 s ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clamp01_of_mem {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : clamp01 s = s := by
  unfold clamp01; rw [min_eq_left hs.2, max_eq_right hs.1]

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The clamped product `f_χ(clamp s) f_t(clamp s)` is jointly continuous. -/
theorem continuous_prodC (Q : C(ℝ, ℝ)) (χ : ℝ) :
    Continuous (fun p : ℝ × ℝ => regSol Q χ (clamp01 p.2) * regSol Q p.1 (clamp01 p.2)) := by
  have hj := continuousOn_regSol_joint Q
  have h1 : Continuous (fun p : ℝ × ℝ => regSol Q p.1 (clamp01 p.2)) :=
    hj.comp_continuous (f := fun p : ℝ × ℝ => (p.1, clamp01 p.2))
      (continuous_fst.prodMk (continuous_clamp01.comp continuous_snd))
      (fun p => ⟨trivial, lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (clamp01_mem p.2).1⟩)
  have h2 : Continuous (fun p : ℝ × ℝ => regSol Q χ (clamp01 p.2)) :=
    hj.comp_continuous (f := fun p : ℝ × ℝ => (χ, clamp01 p.2))
      (continuous_const.prodMk (continuous_clamp01.comp continuous_snd))
      (fun p => ⟨trivial, lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (clamp01_mem p.2).1⟩)
  exact h2.mul h1

/-- On `[0, 1]` the tail coupling is the clamped one. -/
theorem tailC_eq_clamp (Q : C(ℝ, ℝ)) (χ t : ℝ) {ξ : ℝ} (hξ : ξ ∈ Icc (0:ℝ) 1) :
    tailC Q χ t ξ = -∫ s in (1:ℝ)..ξ, regSol Q χ (clamp01 s) * regSol Q t (clamp01 s) := by
  rw [tailC, intervalIntegral.integral_symm ξ 1, neg_neg]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hξ.2] at hs
  simp only [clamp01_of_mem ⟨hξ.1.trans hs.1, hs.2⟩]

/-- **Joint continuity** of `(t, ξ) ↦ Z_t(ξ)` on `ℝ × [0, 1]`. -/
theorem continuousOn_tailC (Q : C(ℝ, ℝ)) (χ : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => tailC Q χ p.1 p.2) ((univ : Set ℝ) ×ˢ Icc 0 1) := by
  have hG : Continuous (Function.uncurry fun t s => regSol Q χ (clamp01 s) * regSol Q t (clamp01 s)) :=
    continuous_prodC Q χ
  have hprim := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume) (a₀ := 1) hG
  refine hprim.neg.continuousOn.congr ?_
  intro p hp
  exact tailC_eq_clamp Q χ p.1 hp.2

/-- **The cross-Wronskian form**: `f_χ U_t − U_χ f_t = −(t − χ) Z_t` on `(−1, ∞)`. -/
theorem cross_eq_tailC (Q : C(ℝ, ℝ)) (χ t : ℝ) {ξ : ℝ} (hξ : -1 < ξ) :
    regSol Q χ ξ * regU Q t ξ - regU Q χ ξ * regSol Q t ξ = -((t - χ) * tailC Q χ t ξ) := by
  rw [cross_wronskian Q Q χ t hξ, tailC, intervalIntegral.integral_symm ξ 1, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- `Z_t` has derivative `−f_χ f_t` on `(−1, ∞)`. -/
theorem hasDerivAt_tailC (Q : C(ℝ, ℝ)) (χ t : ℝ) {ξ : ℝ} (hξ : -1 < ξ) :
    HasDerivAt (tailC Q χ t) (-(regSol Q χ ξ * regSol Q t ξ)) ξ := by
  have hc : ContinuousOn (fun s => regSol Q χ s * regSol Q t s) (Ioi (-1)) :=
    (continuousOn_regSol Q χ).mul (continuousOn_regSol Q t)
  have hsub : uIcc ξ 1 ⊆ Ioi (-1) := by
    intro s hs
    rcases le_total ξ 1 with h | h
    · rw [uIcc_of_le h] at hs; exact lt_of_lt_of_le hξ hs.1
    · rw [uIcc_of_ge h] at hs; exact lt_of_lt_of_le (by norm_num : (-1:ℝ) < 1) hs.1
  have hint : IntervalIntegrable (fun s => regSol Q χ s * regSol Q t s) volume ξ 1 :=
    (hc.mono hsub).intervalIntegrable
  exact intervalIntegral.integral_hasDerivAt_left hint
    ((hc.stronglyMeasurableAtFilter isOpen_Ioi) ξ hξ) (hc.continuousAt (Ioi_mem_nhds hξ))

/-- **No interior touching**: for `ξ₀ ∈ (−1, 1)`, `Z_t` cannot vanish at `ξ₀` and stay `≥ 0` around it.
At such a point `f_χ f_t = 0` (interior minimum), the cross-Wronskian vanishes, so both solutions vanish there with
nonzero slopes; then `f_χ f_t` has one sign on both sides of `ξ₀` and `Z_t` crosses zero. -/
theorem not_touch (Q : C(ℝ, ℝ)) {χ t ξ₀ : ℝ} (h1 : -1 < ξ₀) (h2 : ξ₀ < 1)
    (h0 : tailC Q χ t ξ₀ = 0) (hge : ∀ᶠ ξ in 𝓝 ξ₀, 0 ≤ tailC Q χ t ξ) : False := by
  have hmin : IsLocalMin (tailC Q χ t) ξ₀ := by
    filter_upwards [hge] with ξ hξ
    rw [h0]; exact hξ
  have hd := hasDerivAt_tailC Q χ t h1
  have hF0 : regSol Q χ ξ₀ * regSol Q t ξ₀ = 0 := by
    have := hmin.hasDerivAt_eq_zero hd; linarith
  have hY := cross_eq_tailC Q χ t h1
  rw [h0, mul_zero, neg_zero] at hY
  have hboth : regSol Q χ ξ₀ = 0 ∧ regSol Q t ξ₀ = 0 := by
    rcases mul_eq_zero.mp hF0 with h | h
    · refine ⟨h, ?_⟩
      have hU := regU_ne_zero_of_regSol_eq_zero Q χ h1 h2 h
      rw [h, zero_mul, zero_sub, neg_eq_zero] at hY
      exact (mul_eq_zero.mp hY).resolve_left hU
    · refine ⟨?_, h⟩
      have hU := regU_ne_zero_of_regSol_eq_zero Q t h1 h2 h
      rw [h, mul_zero, sub_zero] at hY
      exact (mul_eq_zero.mp hY).resolve_right hU
  obtain ⟨hz1, hz2⟩ := hboth
  have hV1 := regV_ne_zero_of_regSol_eq_zero Q χ h1 h2 hz1
  have hV2 := regV_ne_zero_of_regSol_eq_zero Q t h1 h2 hz2
  have hd1 := hasDerivAt_regSol Q χ h1
  have hd2 := hasDerivAt_regSol Q t h1
  set P := regV Q χ ξ₀ * regV Q t ξ₀ with hPdef
  have hR : ∀ᶠ s in 𝓝[>] ξ₀, 0 < (regSol Q χ s * regSol Q t s) * P := by
    filter_upwards [eventually_mul_deriv_pos hd1 hz1 hV1, eventually_mul_deriv_pos hd2 hz2 hV2] with s ha hb
    have := mul_pos ha hb
    calc (0:ℝ) < regSol Q χ s * regV Q χ ξ₀ * (regSol Q t s * regV Q t ξ₀) := this
      _ = (regSol Q χ s * regSol Q t s) * P := by rw [hPdef]; ring
  have hL : ∀ᶠ s in 𝓝[<] ξ₀, 0 < (regSol Q χ s * regSol Q t s) * P := by
    filter_upwards [eventually_mul_deriv_neg hd1 hz1 hV1, eventually_mul_deriv_neg hd2 hz2 hV2] with s ha hb
    have := mul_pos_of_neg_of_neg ha hb
    calc (0:ℝ) < regSol Q χ s * regV Q χ ξ₀ * (regSol Q t s * regV Q t ξ₀) := this
      _ = (regSol Q χ s * regSol Q t s) * P := by rw [hPdef]; ring
  -- a neighbourhood where `Z_t ≥ 0` and `ξ > −1`
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hge.and (Ioi_mem_nhds h1))
  rcases lt_or_gt_of_ne (mul_ne_zero hV1 hV2) with hP | hP
  · -- `P < 0`: `f_χ f_t < 0` just left of `ξ₀`; `Z_t` increases into `ξ₀`, so it is negative just before
    obtain ⟨a, ha, haS⟩ := (mem_nhdsLT_iff_exists_Ioo_subset.mp hL)
    set b := max a (ξ₀ - δ / 2) with hb
    have hbξ : b < ξ₀ := max_lt ha (by linarith)
    have hab : a ≤ b := le_max_left _ _
    have hbδ : dist b ξ₀ < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]; have := le_max_right a (ξ₀ - δ / 2); linarith
    have hb1 : -1 < b := (hball hbδ).2
    have hcont : ContinuousOn (tailC Q χ t) (Icc b ξ₀) := fun x hx =>
      (hasDerivAt_tailC Q χ t (lt_of_lt_of_le hb1 hx.1)).continuousAt.continuousWithinAt
    obtain ⟨c0, hc0, hslope⟩ := exists_hasDerivAt_eq_slope (tailC Q χ t)
      (fun x => -(regSol Q χ x * regSol Q t x)) hbξ hcont
      (fun x hx => hasDerivAt_tailC Q χ t (lt_trans hb1 hx.1))
    have hFc : 0 < (regSol Q χ c0 * regSol Q t c0) * P := haS ⟨lt_of_le_of_lt hab hc0.1, hc0.2⟩
    have hFneg : regSol Q χ c0 * regSol Q t c0 < 0 := by
      by_contra hcon; push Not at hcon; nlinarith
    have hZb : 0 ≤ tailC Q χ t b := (hball hbδ).1
    rw [h0] at hslope
    have hpos : 0 < (0 - tailC Q χ t b) / (ξ₀ - b) := by rw [← hslope]; linarith
    have : 0 < 0 - tailC Q χ t b := by
      have hd' : 0 < ξ₀ - b := by linarith
      exact (div_pos_iff_of_pos_right hd').mp hpos
    linarith
  · -- `P > 0`: `f_χ f_t > 0` just right of `ξ₀`; `Z_t` decreases, so it is negative just after
    obtain ⟨a, ha, haS⟩ := (mem_nhdsGT_iff_exists_Ioo_subset.mp hR)
    set b := min a (ξ₀ + δ / 2) with hb
    have hbξ : ξ₀ < b := lt_min ha (by linarith)
    have hab : b ≤ a := min_le_left _ _
    have hbδ : dist b ξ₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]; have := min_le_right a (ξ₀ + δ / 2); linarith
    have hcont : ContinuousOn (tailC Q χ t) (Icc ξ₀ b) := fun x hx =>
      (hasDerivAt_tailC Q χ t (lt_of_lt_of_le h1 hx.1)).continuousAt.continuousWithinAt
    obtain ⟨c0, hc0, hslope⟩ := exists_hasDerivAt_eq_slope (tailC Q χ t)
      (fun x => -(regSol Q χ x * regSol Q t x)) hbξ hcont
      (fun x hx => hasDerivAt_tailC Q χ t (lt_trans h1 hx.1))
    have hFc : 0 < (regSol Q χ c0 * regSol Q t c0) * P := haS ⟨hc0.1, lt_of_lt_of_le hc0.2 hab⟩
    have hFpos : 0 < regSol Q χ c0 * regSol Q t c0 := by
      by_contra hcon; push Not at hcon; nlinarith
    have hZb : 0 ≤ tailC Q χ t b := (hball hbδ).1
    rw [h0] at hslope
    have hneg : (tailC Q χ t b - 0) / (b - ξ₀) < 0 := by rw [← hslope]; linarith
    have : tailC Q χ t b - 0 < 0 := by
      have hd' : 0 < b - ξ₀ := by linarith
      by_contra hc; push Not at hc
      exact absurd hneg (not_lt.mpr (div_nonneg hc hd'.le))
    linarith

/-- `Z_χ(ξ) = ∫_ξ^1 f_χ² > 0` for `ξ ∈ (−1, 1)`. -/
theorem tailC_self_pos (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (h1 : -1 < ξ) (h2 : ξ < 1) : 0 < tailC Q χ χ ξ := by
  unfold tailC
  refine intervalIntegral.integral_pos h2 ?_ (fun x _ => mul_self_nonneg _) ⟨1, ⟨h2.le, le_rfl⟩, by simp [regSol_one]⟩
  exact ((continuousOn_regSol Q χ).mul (continuousOn_regSol Q χ)).mono fun x hx => lt_of_lt_of_le h1 hx.1

/-- **Uniform positivity near `ξ = 1`**: for `t ∈ [a, b]`, `Z_t > 0` on `(m, 1)` for some `m ∈ [0, 1)`. -/
theorem tailC_pos_near_one (Q : C(ℝ, ℝ)) (χ a b : ℝ) :
    ∃ m, 0 ≤ m ∧ m < 1 ∧ ∀ t ∈ Icc a b, ∀ ξ ∈ Ioo m 1, 0 < tailC Q χ t ξ := by
  set F : ℝ × ℝ → ℝ := fun p => regSol Q χ p.2 * regSol Q p.1 p.2 with hF
  have hFc : ContinuousOn F (Icc a b ×ˢ Icc 0 1) := by
    have hj := continuousOn_regSol_joint Q
    have hsub : Icc a b ×ˢ Icc (0:ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Ioi (-1) := fun p hp =>
      ⟨trivial, lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) hp.2.1⟩
    have h1 : ContinuousOn (fun p : ℝ × ℝ => regSol Q p.1 p.2) (Icc a b ×ˢ Icc 0 1) := hj.mono hsub
    have h2 : ContinuousOn (fun p : ℝ × ℝ => regSol Q χ p.2) (Icc a b ×ˢ Icc 0 1) :=
      (continuousOn_regSol Q χ).comp continuous_snd.continuousOn
        (fun p hp => lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) hp.2.1)
    exact h2.mul h1
  set K := Icc a b ×ˢ Icc (0:ℝ) 1 ∩ F ⁻¹' Iic 0 with hK
  have hKc : IsClosed K := hFc.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc) isClosed_Iic
  have hKcpt : IsCompact K := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKc inter_subset_left
  have hint_pos : ∀ t, ∀ ξ ∈ Ico (0:ℝ) 1, (∀ s ∈ Ioo ξ 1, 0 < F (t, s)) → 0 < tailC Q χ t ξ := by
    intro t ξ hξ hpos
    unfold tailC
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ hpos hξ.2
    refine (((continuousOn_regSol Q χ).mul (continuousOn_regSol Q t)).mono ?_).intervalIntegrable
    intro s hs
    rw [uIcc_of_le hξ.2.le] at hs
    exact lt_of_lt_of_le (by linarith [hξ.1] : (-1:ℝ) < ξ) hs.1
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, le_rfl, one_pos, fun t ht ξ hξ => hint_pos t ξ ⟨hξ.1.le, hξ.2⟩ (fun s hs => ?_)⟩
    by_contra hle
    push Not at hle
    have hmem : (t, s) ∈ K := ⟨⟨ht, hξ.1.le.trans hs.1.le, hs.2.le⟩, hle⟩
    rw [hKe] at hmem
    exact hmem
  · obtain ⟨p, hpK, hpmax⟩ := hKcpt.exists_isMaxOn hKne continuous_snd.continuousOn
    have hp1 : p.2 < 1 := by
      rcases eq_or_lt_of_le hpK.1.2.2 with h | h
      · exfalso
        have hle : regSol Q χ p.2 * regSol Q p.1 p.2 ≤ 0 := hpK.2
        rw [h, regSol_one, regSol_one] at hle
        linarith
      · exact h
    refine ⟨p.2, hpK.1.2.1, hp1, fun t ht ξ hξ =>
      hint_pos t ξ ⟨hpK.1.2.1.trans hξ.1.le, hξ.2⟩ (fun s hs => ?_)⟩
    by_contra hle
    push Not at hle
    have hmem : (t, s) ∈ K := ⟨⟨ht, (hpK.1.2.1.trans hξ.1.le).trans hs.1.le, hs.2.le⟩, hle⟩
    have := hpmax hmem
    simp only [Set.mem_ofPred_eq] at this
    linarith [hs.1, hξ.1]

/-- The level map `t ↦ Z_t(ξ)` is continuous on `ℝ` for `ξ ∈ [0, 1]`. -/
theorem continuous_tailC_level (Q : C(ℝ, ℝ)) (χ : ℝ) {ξ : ℝ} (hξ : ξ ∈ Icc (0:ℝ) 1) :
    Continuous fun t => tailC Q χ t ξ := by
  exact (continuousOn_tailC Q χ).comp_continuous (f := fun t => (t, ξ))
    (continuous_id.prodMk continuous_const) (fun t => ⟨trivial, hξ⟩)

/-- **The bottom edge**: `Z_t(0) > 0` for `t ∈ [χ, χ')` when no even level lies in `(χ, χ')`. -/
theorem tailC_zero_pos (Q : C(ℝ, ℝ)) {χ χ' : ℝ} (hχ : regU Q χ 0 = 0)
    (hcons : ∀ t ∈ Ioo χ χ', regU Q t 0 ≠ 0) : ∀ t ∈ Ico χ χ', 0 < tailC Q χ t 0 := by
  have hf0 : regSol Q χ 0 ≠ 0 := fun h =>
    regU_ne_zero_of_regSol_eq_zero Q χ (by norm_num) (by norm_num) h hχ
  have hne : ∀ t ∈ Ioo χ χ', tailC Q χ t 0 ≠ 0 := by
    intro t ht hz
    have hY := cross_eq_tailC Q χ t (ξ := 0) (by norm_num)
    rw [hz, hχ, mul_zero, neg_zero, zero_mul, sub_zero] at hY
    exact (mul_ne_zero hf0 (hcons t ht)) hY
  have hpos0 := tailC_self_pos Q χ (ξ := 0) (by norm_num) (by norm_num)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; exact hpos0
  · have hcont : ContinuousOn (fun t => tailC Q χ t 0) (Icc χ t) :=
      (continuous_tailC_level Q χ ⟨le_rfl, zero_le_one⟩).continuousOn
    have := mul_pos_of_ne_zero hcont (fun u hu => by
      rcases eq_or_lt_of_le hu.1 with h' | h'
      · rw [← h']; exact hpos0.ne'
      · exact hne u ⟨h', lt_of_le_of_lt hu.2 ht.2⟩) t ⟨h.le, le_rfl⟩
    exact (pos_iff_pos_of_mul_pos this).mp hpos0

/-- **Below the next level the coupling is positive**: if `χ` is an even level and no even level lies in `(χ, χ')`,
then `Z_t > 0` on `[0, 1)` for every `t ∈ [χ, χ')`. First-zero argument on `[χ, T] × [0, ξ_m]`. -/
theorem tailC_pos_before (Q : C(ℝ, ℝ)) {χ χ' : ℝ} (hχ : regU Q χ 0 = 0)
    (hcons : ∀ t ∈ Ioo χ χ', regU Q t 0 ≠ 0) : ∀ t ∈ Ico χ χ', ∀ ξ ∈ Ico (0:ℝ) 1, 0 < tailC Q χ t ξ := by
  obtain ⟨m, hm0, hm1, hnear⟩ := tailC_pos_near_one Q χ χ χ'
  have hbot := tailC_zero_pos Q hχ hcons
  set ξm := (m + 1) / 2 with hξm
  have hmξ : m < ξm := by rw [hξm]; linarith
  have hξ1 : ξm < 1 := by rw [hξm]; linarith
  intro T hT
  -- the claim on the rectangle `[χ, T] × [0, ξm]`
  have hrect : ∀ t ∈ Icc χ T, ∀ ξ ∈ Icc (0:ℝ) ξm, 0 < tailC Q χ t ξ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t0, ht0, ξ0, hξ0, hz0⟩ := hcon
    have hRsub : Icc χ T ×ˢ Icc (0:ℝ) ξm ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 := fun p hp =>
      ⟨trivial, hp.2.1, hp.2.2.trans hξ1.le⟩
    have hFc : ContinuousOn (fun p : ℝ × ℝ => tailC Q χ p.1 p.2) (Icc χ T ×ˢ Icc 0 ξm) :=
      (continuousOn_tailC Q χ).mono hRsub
    set K := Icc χ T ×ˢ Icc (0:ℝ) ξm ∩ (fun p : ℝ × ℝ => tailC Q χ p.1 p.2) ⁻¹' Iic 0 with hK
    have hKc : IsClosed K :=
      hFc.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc) isClosed_Iic
    have hKcpt : IsCompact K := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKc inter_subset_left
    have hKne : K.Nonempty := ⟨(t0, ξ0), ⟨ht0, hξ0⟩, hz0⟩
    obtain ⟨p, hpK, hpmin⟩ := hKcpt.exists_isMinOn hKne continuous_fst.continuousOn
    obtain ⟨⟨hp1, hp2⟩, hp0⟩ := hpK
    have hp0' : tailC Q χ p.1 p.2 ≤ 0 := hp0
    have hmin : ∀ t ∈ Icc χ T, ∀ ξ ∈ Icc (0:ℝ) ξm, tailC Q χ t ξ ≤ 0 → p.1 ≤ t := fun t ht ξ hξ h => by
      have := hpmin (show (t, ξ) ∈ K from ⟨⟨ht, hξ⟩, h⟩)
      simpa using this
    have hpT : p.1 < χ' := lt_of_le_of_lt hp1.2 hT.2
    have hχs : χ < p.1 := by
      rcases eq_or_lt_of_le hp1.1 with h | h
      · exfalso
        have := tailC_self_pos Q χ (ξ := p.2) (by linarith [hp2.1]) (by linarith [hp2.2])
        have h' : tailC Q χ p.1 p.2 = tailC Q χ χ p.2 := by rw [← h]
        linarith
      · exact h
    have hξs : 0 < p.2 := by
      rcases eq_or_lt_of_le hp2.1 with h | h
      · exfalso
        have := hbot p.1 ⟨hp1.1, hpT⟩
        have h' : tailC Q χ p.1 p.2 = tailC Q χ p.1 0 := by rw [← h]
        linarith
      · exact h
    have hξs1 : p.2 < 1 := lt_of_le_of_lt hp2.2 hξ1
    -- before `p.1`, `Z_t > 0` on all of `[0, 1)`
    have hpre : ∀ t ∈ Ico χ p.1, ∀ ξ ∈ Ico (0:ℝ) 1, 0 < tailC Q χ t ξ := by
      intro t ht ξ hξ
      by_cases hξle : ξ ≤ ξm
      · by_contra hle
        push Not at hle
        have := hmin t ⟨ht.1, ht.2.le.trans hp1.2⟩ ξ ⟨hξ.1, hξle⟩ hle
        linarith [ht.2]
      · push Not at hξle
        exact hnear t ⟨ht.1, (ht.2.trans hpT).le⟩ ξ ⟨lt_trans hmξ hξle, hξ.2⟩
    -- at `p.1`, `Z ≥ 0` on `[0, 1)` by continuity in the level
    have hlim : ∀ ξ ∈ Ico (0:ℝ) 1, 0 ≤ tailC Q χ p.1 ξ := by
      intro ξ hξ
      have hc := (continuous_tailC_level Q χ ⟨hξ.1, hξ.2.le⟩).continuousAt (x := p.1)
      exact ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
        (by filter_upwards [Ioo_mem_nhdsLT hχs] with t ht using (hpre t ⟨ht.1.le, ht.2⟩ ξ hξ).le)
    have hz : tailC Q χ p.1 p.2 = 0 := le_antisymm hp0' (hlim p.2 ⟨hp2.1, hξs1⟩)
    refine not_touch Q (t := p.1) (ξ₀ := p.2) (by linarith) hξs1 hz ?_
    filter_upwards [Ioo_mem_nhds hξs hξs1] with ξ hξ using hlim ξ ⟨hξ.1.le, hξ.2⟩
  intro ξ hξ
  by_cases hξle : ξ ≤ ξm
  · exact hrect T ⟨hT.1, le_rfl⟩ ξ ⟨hξ.1, hξle⟩
  · push Not at hξle
    exact hnear T ⟨hT.1, hT.2.le⟩ ξ ⟨lt_trans hmξ hξle, hξ.2⟩

/-- **ORD-C: consecutive even levels couple positively.** If `χ` is an even level of `Q`, `χ < χ'`, and no even
level lies in `(χ, χ')`, then `∫_ξ^1 f_χ f_χ' > 0` for every `ξ ∈ (0, 1)`. -/
theorem coupling_pos (Q : C(ℝ, ℝ)) {χ χ' : ℝ} (hlt : χ < χ') (hχ : regU Q χ 0 = 0)
    (hcons : ∀ t ∈ Ioo χ χ', regU Q t 0 ≠ 0) : ∀ ξ ∈ Ioo (0:ℝ) 1, 0 < tailC Q χ χ' ξ := by
  have hpre := tailC_pos_before Q hχ hcons
  have hlim : ∀ ξ ∈ Ico (0:ℝ) 1, 0 ≤ tailC Q χ χ' ξ := by
    intro ξ hξ
    have hc := (continuous_tailC_level Q χ ⟨hξ.1, hξ.2.le⟩).continuousAt (x := χ')
    exact ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsLT hlt] with t ht using (hpre t ⟨ht.1.le, ht.2⟩ ξ hξ).le)
  intro ξ hξ
  rcases eq_or_lt_of_le (hlim ξ ⟨hξ.1.le, hξ.2⟩) with h | h
  · exfalso
    refine not_touch Q (t := χ') (ξ₀ := ξ) (by linarith [hξ.1]) hξ.2 h.symm ?_
    filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with x hx using hlim x ⟨hx.1.le, hx.2⟩
  · exact h

/-- **The `s²`-moment of consecutive even levels is positive**: `∫_0^1 s² f_χ f_χ' = 2 ∫_0^1 s Z > 0`. -/
theorem moment_pos (Q : C(ℝ, ℝ)) {χ χ' : ℝ} (hlt : χ < χ') (hχ : regU Q χ 0 = 0)
    (hcons : ∀ t ∈ Ioo χ χ', regU Q t 0 ≠ 0) :
    0 < ∫ s in (0:ℝ)..1, s ^ 2 * (regSol Q χ s * regSol Q χ' s) := by
  have hZ := coupling_pos Q hlt hχ hcons
  set Z := tailC Q χ χ' with hZdef
  set F : ℝ → ℝ := fun s => regSol Q χ s * regSol Q χ' s with hF
  have hFc : ContinuousOn F (Icc 0 1) :=
    ((continuousOn_regSol Q χ).mul (continuousOn_regSol Q χ')).mono fun x hx => lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) hx.1
  have hZd : ∀ x ∈ Icc (0:ℝ) 1, HasDerivAt Z (-F x) x := fun x hx =>
    hasDerivAt_tailC Q χ χ' (lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) hx.1)
  have hZc : ContinuousOn Z (Icc 0 1) := fun x hx => (hZd x hx).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun s => s ^ 2 * Z s) (2 * x * Z x - x ^ 2 * F x) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have := ((hasDerivAt_pow 2 x).mul (hZd x hx))
    refine this.congr_deriv ?_
    simp; ring
  have hint1 : IntervalIntegrable (fun s => 2 * s * Z s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_const.mul continuousOn_id).mul hZc
  have hint2 : IntervalIntegrable (fun s => s ^ 2 * F s) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_id.pow 2).mul hFc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hint1.sub hint2)
  have hZ1 : Z 1 = 0 := by rw [hZdef, tailC]; simp
  rw [intervalIntegral.integral_sub hint1 hint2] at hFTC
  simp only [one_pow, one_mul, hZ1, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    sub_self] at hFTC
  have hpos : 0 < ∫ s in (0:ℝ)..1, 2 * s * Z s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hint1 (fun x hx => ?_) zero_lt_one
    exact mul_pos (by linarith [hx.1]) (hZ x hx)
  have : ∫ s in (0:ℝ)..1, s ^ 2 * F s = ∫ s in (0:ℝ)..1, 2 * s * Z s := by linarith
  show 0 < ∫ s in (0:ℝ)..1, s ^ 2 * F s
  rw [this]; exact hpos

end Cvs.Prolate.EvenLevelPositiveCoupling
