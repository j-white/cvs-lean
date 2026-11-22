import Mathlib
import Cvs.Prolate.LadderWronskian
import Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent
import Cvs.Upstream.BackwardComparisonRiccati

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ladder ratio from the WKB momenta

For positive angular solutions `g_a`, `g_b` on `[a, 1]` at levels `χ_a ≤ χ_b`, with `0 ≤ U_i ≤ W_i` and
`Σ(W_i² − p q_i) < κ(κ − 2)` (`κ ≥ 2`), `Y = ∫_s^1 g_a g_b/(g_a g_b) ≥ p/(U_a + U_b + κ)` by comparison, so
`log(g_b(1)/g_a(1)) − log(g_b(a)/g_a(a)) ≥ (χ_b − χ_a)∫_a^1 1/(W_a + W_b + κ)`.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Prolate.LadderRatioWkbMomenta

open Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent (U)

/-- `g₁ = −Ug/p` where `g ≠ 0` and `p ≠ 0`. -/
theorem g₁_eq {g g₁ : ℝ → ℝ} {x : ℝ} (hg : g x ≠ 0) (hp : 1 - x ^ 2 ≠ 0) :
    g₁ x = -(U g g₁ x * g x) / (1 - x ^ 2) := by
  unfold U; field_simp

set_option maxHeartbeats 1000000 in
/-- **The ladder ratio from the momenta.** -/
theorem log_ratio_ge {ga ga₁ ga₂ gb gb₁ gb₂ Wa Wb : ℝ → ℝ} {c χa χb a κ : ℝ}
    (ha : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga (ga₁ t) t) (ha₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt ga₁ (ga₂ t) t)
    (hanga : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * ga₂ t - 2 * t * ga₁ t - c ^ 2 * t ^ 2 * ga t + χa * ga t = 0)
    (hb : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb (gb₁ t) t) (hb₁ : ∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt gb₁ (gb₂ t) t)
    (hangb : ∀ t ∈ uIcc (-1 : ℝ) 1, (1 - t ^ 2) * gb₂ t - 2 * t * gb₁ t - c ^ 2 * t ^ 2 * gb t + χb * gb t = 0)
    (hχ : χa ≤ χb) (ha0 : 0 < a) (ha1 : a < 1) (hκ : 2 ≤ κ)
    (hpa : ∀ t ∈ Icc a 1, 0 < ga t) (hpb : ∀ t ∈ Icc a 1, 0 < gb t)
    (hUa0 : ∀ t ∈ Icc a 1, 0 ≤ U ga ga₁ t) (hUb0 : ∀ t ∈ Icc a 1, 0 ≤ U gb gb₁ t)
    (hUa : ∀ t ∈ Icc a 1, U ga ga₁ t ≤ Wa t) (hUb : ∀ t ∈ Icc a 1, U gb gb₁ t ≤ Wb t)
    (hWc : ContinuousOn (fun t => 1 / (Wa t + Wb t + κ)) (Icc a 1))
    (hcond : ∀ t ∈ Ico a 1, (Wa t ^ 2 - (1 - t ^ 2) * (c ^ 2 * t ^ 2 - χa))
      + (Wb t ^ 2 - (1 - t ^ 2) * (c ^ 2 * t ^ 2 - χb)) < κ * (κ - 2)) :
    (χb - χa) * ∫ t in a..1, 1 / (Wa t + Wb t + κ) ≤ log (gb 1 / ga 1) - log (gb a / ga a) := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hm : ∀ t ∈ Icc a 1, t ∈ uIcc (-1 : ℝ) 1 := fun t ht => by rw [hI]; exact ⟨by linarith [ht.1], ht.2⟩
  have hm' : ∀ t ∈ Icc a 1, t ∈ Icc (-1 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  -- the product `P`, its tail integral `J` and `Y = J/P`
  set P : ℝ → ℝ := fun t => ga t * gb t with hPd
  have hPpos : ∀ t ∈ Icc a 1, 0 < P t := fun t ht => mul_pos (hpa t ht) (hpb t ht)
  have hPc : ContinuousOn P (uIcc (-1 : ℝ) 1) := fun t ht =>
    ((ha t ht).continuousAt.mul (hb t ht).continuousAt).continuousWithinAt
  set J : ℝ → ℝ := fun s => ∫ t in s..1, P t with hJd
  set S : ℝ → ℝ := fun t => U ga ga₁ t + U gb gb₁ t with hSd
  set Y : ℝ → ℝ := fun s => J s / P s with hYd
  set L : ℝ → ℝ := fun s => (1 - s ^ 2) / (S s + κ) with hLd
  have hS0 : ∀ t ∈ Icc a 1, 0 ≤ S t := fun t ht => add_nonneg (hUa0 t ht) (hUb0 t ht)
  -- derivatives on `(a, 1)`
  have hJd' : ∀ s ∈ Ioo a 1, HasDerivAt J (-P s) s := by
    intro s hs
    have hs' : s ∈ Icc a 1 := Ioo_subset_Icc_self hs
    have hcont : ContinuousAt P s := ((ha s (hm s hs')).continuousAt.mul (hb s (hm s hs')).continuousAt)
    have hint : IntervalIntegrable P volume s 1 := by
      refine ContinuousOn.intervalIntegrable (hPc.mono ?_)
      rw [hI, uIcc_of_le hs'.2]; exact Icc_subset_Icc_left (by linarith [hs.1])
    have hmeas : StronglyMeasurableAtFilter P (nhds s) volume :=
      (hPc.mono (by rw [hI]; exact Ioo_subset_Icc_self)).stronglyMeasurableAtFilter isOpen_Ioo s
        ⟨by linarith [hs.1], hs.2⟩
    exact intervalIntegral.integral_hasDerivAt_left hint hmeas hcont
  have hp_pos : ∀ s ∈ Ioo a 1, 0 < 1 - s ^ 2 := fun s hs => by nlinarith [hs.1, hs.2]
  have hga₁ : ∀ s ∈ Icc a 1, s ^ 2 < 1 → ga₁ s = -(U ga ga₁ s * ga s) / (1 - s ^ 2) := fun s hs h1 =>
    g₁_eq (hpa s hs).ne' (by linarith)
  have hgb₁ : ∀ s ∈ Icc a 1, s ^ 2 < 1 → gb₁ s = -(U gb gb₁ s * gb s) / (1 - s ^ 2) := fun s hs h1 =>
    g₁_eq (hpb s hs).ne' (by linarith)
  have hYd' : ∀ s ∈ Ioo a 1, HasDerivAt Y (-1 + S s * Y s / (1 - s ^ 2)) s := by
    intro s hs
    have hs' := Ioo_subset_Icc_self hs
    have hP' : HasDerivAt P (ga₁ s * gb s + ga s * gb₁ s) s := (ha s (hm s hs')).mul (hb s (hm s hs'))
    have := (hJd' s hs).div hP' (hPpos s hs').ne'
    refine this.congr_deriv ?_
    have hs1 : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
    rw [hga₁ s hs' hs1, hgb₁ s hs' hs1]
    have hp := hp_pos s hs
    have hga0 := (hpa s hs').ne'
    have hgb0 := (hpb s hs').ne'
    simp only [hYd, hSd, hPd]
    field_simp
    ring
  have hUad : ∀ s ∈ Ioo a 1, HasDerivAt (U ga ga₁) (U ga ga₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χa)) s :=
    fun s hs => Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent.hasDerivAt_U (ha s (hm s (Ioo_subset_Icc_self hs)))
      (ha₁ s (hm s (Ioo_subset_Icc_self hs))) (hanga s (hm s (Ioo_subset_Icc_self hs)))
      (by nlinarith [hs.1, hs.2]) (hpa s (Ioo_subset_Icc_self hs)).ne'
  have hUbd : ∀ s ∈ Ioo a 1, HasDerivAt (U gb gb₁) (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb)) s :=
    fun s hs => Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent.hasDerivAt_U (hb s (hm s (Ioo_subset_Icc_self hs)))
      (hb₁ s (hm s (Ioo_subset_Icc_self hs))) (hangb s (hm s (Ioo_subset_Icc_self hs)))
      (by nlinarith [hs.1, hs.2]) (hpb s (Ioo_subset_Icc_self hs)).ne'
  -- `L ≤ Y` on `[a, 1]`
  have hUc : ∀ g g₁ g₂ : ℝ → ℝ, (∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ t) t) →
      (∀ t ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ t) t) → (∀ t ∈ Icc a 1, 0 < g t) →
      ContinuousOn (U g g₁) (Icc a 1) := fun g g₁ g₂ hg hg₁ hp t ht => by
    unfold U
    exact (((continuousAt_const.sub (continuousAt_id.pow 2)).mul (hg₁ t (hm t ht)).continuousAt).neg.div
      (hg t (hm t ht)).continuousAt (hp t ht).ne').continuousWithinAt
  have hSc : ContinuousOn S (Icc a 1) := (hUc ga ga₁ ga₂ ha ha₁ hpa).add (hUc gb gb₁ gb₂ hb hb₁ hpb)
  have hLY : ∀ s ∈ Icc a 1, L s ≤ Y s := by
    have key := Cvs.Upstream.BackwardComparisonRiccati.nonpos_of_deriv_pos (D := fun s => L s - Y s)
      (D' := fun s => ((-(2 * s)) * (S s + κ) - (1 - s ^ 2) * ((U ga ga₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χa))
        + (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb)))) / (S s + κ) ^ 2
        - (-1 + S s * Y s / (1 - s ^ 2))) ha1.le ?_ ?_ ?_ ?_
    · intro s hs; have := key s hs; linarith
    · refine ContinuousOn.sub ?_ ?_
      · refine (continuousOn_const.sub (continuousOn_id.pow 2)).div (hSc.add continuousOn_const) fun t ht => ?_
        have := hS0 t ht
        exact ne_of_gt (show (0 : ℝ) < S t + κ by linarith)
      · refine ContinuousOn.div (fun s hs => ?_) (hPc.mono fun t ht => hm t ht) fun t ht => (hPpos t ht).ne'
        have hint : ContinuousOn (fun s => ∫ t in s..1, P t) (uIcc (-1 : ℝ) 1) :=
          intervalIntegral.continuousOn_primitive_interval_left (hPc.integrableOn_compact isCompact_uIcc)
        exact (hint s (hm s hs)).mono fun t ht => hm t ht
    · intro s hs
      have hsum := ((hUad s hs).add (hUbd s hs)).add_const κ
      have hp : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
        simpa using ((hasDerivAt_pow 2 s).const_sub 1)
      have hden : S s + κ ≠ 0 := by have := hS0 s (Ioo_subset_Icc_self hs); linarith
      have hL := hp.div hsum hden
      exact hL.sub (hYd' s hs)
    · intro s hs hD
      have hs' := Ioo_subset_Icc_self hs
      have hp := hp_pos s hs
      have hS := hS0 s hs'
      have hd : 0 < S s + κ := by linarith
      -- the subsolution slack
      have hUa2 : U ga ga₁ s ^ 2 ≤ Wa s ^ 2 := pow_le_pow_left₀ (hUa0 s hs') (hUa s hs') 2
      have hUb2 : U gb gb₁ s ^ 2 ≤ Wb s ^ 2 := pow_le_pow_left₀ (hUb0 s hs') (hUb s hs') 2
      have hc := hcond s ⟨hs'.1, hs.2⟩
      have hslack : (1 - s ^ 2) * ((U ga ga₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χa))
          + (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb))) < (κ - 2 * s) * (S s + κ) := by
        have e : (1 - s ^ 2) * ((U ga ga₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χa))
            + (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb)))
            = (U ga ga₁ s ^ 2 - (1 - s ^ 2) * (c ^ 2 * s ^ 2 - χa))
              + (U gb gb₁ s ^ 2 - (1 - s ^ 2) * (c ^ 2 * s ^ 2 - χb)) := by field_simp
        rw [e]
        have h1 : κ * (κ - 2) ≤ (κ - 2 * s) * (S s + κ) := by
          have hs1 : s ≤ 1 := hs.2.le
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ κ - 2 * s) hS]
        linarith
      -- `L' − (SL/p − 1) > 0`, then add `S(L − Y)/p ≥ 0`
      have hLpart : 0 < ((-(2 * s)) * (S s + κ) - (1 - s ^ 2) * ((U ga ga₁ s ^ 2 / (1 - s ^ 2)
          - (c ^ 2 * s ^ 2 - χa)) + (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb)))) / (S s + κ) ^ 2
          - (-1 + S s * L s / (1 - s ^ 2)) := by
        simp only [hLd]
        rw [show S s * ((1 - s ^ 2) / (S s + κ)) / (1 - s ^ 2) = S s / (S s + κ) by field_simp]
        rw [show ((-(2 * s)) * (S s + κ) - (1 - s ^ 2) * ((U ga ga₁ s ^ 2 / (1 - s ^ 2)
          - (c ^ 2 * s ^ 2 - χa)) + (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb)))) / (S s + κ) ^ 2
          - (-1 + S s / (S s + κ)) = ((κ - 2 * s) * (S s + κ) - (1 - s ^ 2) * ((U ga ga₁ s ^ 2 / (1 - s ^ 2)
          - (c ^ 2 * s ^ 2 - χa)) + (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb)))) / (S s + κ) ^ 2 by
          field_simp; ring]
        exact div_pos (by linarith) (by positivity)
      have hextra : 0 ≤ S s * (L s - Y s) / (1 - s ^ 2) := div_nonneg (mul_nonneg hS hD.le) hp.le
      have e : ((-(2 * s)) * (S s + κ) - (1 - s ^ 2) * ((U ga ga₁ s ^ 2 / (1 - s ^ 2)
          - (c ^ 2 * s ^ 2 - χa)) + (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb)))) / (S s + κ) ^ 2
          - (-1 + S s * Y s / (1 - s ^ 2))
          = (((-(2 * s)) * (S s + κ) - (1 - s ^ 2) * ((U ga ga₁ s ^ 2 / (1 - s ^ 2)
          - (c ^ 2 * s ^ 2 - χa)) + (U gb gb₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χb)))) / (S s + κ) ^ 2
          - (-1 + S s * L s / (1 - s ^ 2))) + S s * (L s - Y s) / (1 - s ^ 2) := by
        field_simp; ring
      rw [e]; linarith
    · simp only [hLd, hYd, hJd]
      simp
  -- the log-ratio derivative dominates `(χ_b − χ_a)/(W_a + W_b + κ)` on `[a, 1]`
  have hderiv_ge : ∀ s ∈ Icc a 1,
      (χb - χa) * (1 / (Wa s + Wb s + κ)) ≤ gb₁ s / gb s - ga₁ s / ga s := by
    intro s hs
    have hWS : S s ≤ Wa s + Wb s := add_le_add (hUa s hs) (hUb s hs)
    have hS := hS0 s hs
    have hΔ : 0 ≤ χb - χa := by linarith
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · -- at `s = 1` the log-derivative is `(χ_b − χ_a)/2`
      subst h1
      have e1 := hanga 1 (hm 1 hs); have e2 := hangb 1 (hm 1 hs)
      norm_num at e1 e2
      have hg1a : ga₁ 1 = -(c ^ 2 - χa) * ga 1 / 2 := by linarith
      have hg1b : gb₁ 1 = -(c ^ 2 - χb) * gb 1 / 2 := by linarith
      rw [hg1a, hg1b]
      have hga0 := (hpa 1 hs).ne'; have hgb0 := (hpb 1 hs).ne'
      rw [show -(c ^ 2 - χb) * gb 1 / 2 / gb 1 - -(c ^ 2 - χa) * ga 1 / 2 / ga 1 = (χb - χa) / 2 by
        field_simp; ring]
      have hW0 : 0 ≤ Wa 1 + Wb 1 := le_trans hS hWS
      have : 1 / (Wa 1 + Wb 1 + κ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      nlinarith
    · have hs1 : s ^ 2 < 1 := by nlinarith [hs.1, ha0]
      have hlog := Cvs.Prolate.LadderWronskian.logderiv_sub_eq ha ha₁ hanga hb hb₁ hangb (hm' s hs) hs1
        (hpa s hs).ne' (hpb s hs).ne'
      rw [hlog]
      have hp : 0 < 1 - s ^ 2 := by linarith
      have hY := hLY s hs
      simp only [hLd, hYd, hJd, hPd] at hY
      have hd : 0 < S s + κ := by linarith
      calc (χb - χa) * (1 / (Wa s + Wb s + κ)) ≤ (χb - χa) * (1 / (S s + κ)) := by
            apply mul_le_mul_of_nonneg_left _ hΔ
            exact one_div_le_one_div_of_le hd (by linarith)
        _ = (χb - χa) * ((1 - s ^ 2) / (S s + κ)) / (1 - s ^ 2) := by field_simp
        _ ≤ (χb - χa) * ((∫ t in s..1, ga t * gb t) / (ga s * gb s)) / (1 - s ^ 2) := by
            apply div_le_div_of_nonneg_right _ hp.le
            exact mul_le_mul_of_nonneg_left hY hΔ
        _ = (χb - χa) * (∫ t in s..1, ga t * gb t) / ((1 - s ^ 2) * (ga s * gb s)) := by
            field_simp
  -- integrate
  have hcd : ContinuousOn (fun s => gb₁ s / gb s - ga₁ s / ga s) (Icc a 1) := fun s hs =>
    (((hb₁ s (hm s hs)).continuousAt.div (hb s (hm s hs)).continuousAt (hpb s hs).ne').sub
      ((ha₁ s (hm s hs)).continuousAt.div (ha s (hm s hs)).continuousAt (hpa s hs).ne')).continuousWithinAt
  have hftc : ∫ s in a..1, (gb₁ s / gb s - ga₁ s / ga s) = log (gb 1 / ga 1) - log (gb a / ga a) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => log (gb s / ga s)) (fun s hs => ?_) ?_
    · rw [uIcc_of_le ha1.le] at hs
      have hq := (hpb s hs).ne'; have hr := (hpa s hs).ne'
      have hd := ((hb s (hm s hs)).div (ha s (hm s hs)) hr).log (div_pos (hpb s hs) (hpa s hs)).ne'
      refine hd.congr_deriv ?_
      simp only [Pi.div_apply]
      field_simp
    · exact (hcd.mono (by rw [uIcc_of_le ha1.le])).intervalIntegrable
  rw [← hftc, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on ha1.le ?_ ?_ hderiv_ge
  · exact ((hWc.const_smul (χb - χa)).mono (by rw [uIcc_of_le ha1.le])).intervalIntegrable
  · exact (hcd.mono (by rw [uIcc_of_le ha1.le])).intervalIntegrable

end Cvs.Prolate.LadderRatioWkbMomenta
