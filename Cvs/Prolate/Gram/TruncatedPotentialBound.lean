import Mathlib
import Cvs.Prolate.Gram.EquilibriumPotential
import Cvs.Prolate.Gram.SelectionTargetMeasure
import Cvs.Upstream.AbelLogIntegral
import Cvs.Upstream.SliceMeasurePushforward

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The truncated potential: `|∫ log|y − v| d(μ⁺ − μ⁻) − Ψ_a(y)| ≤ η(U)/2` on `[0, 2U²]`

The `u`-tail `τ = ∫_U^∞ (log|u² − y + t²| − log|u² − y|) du` is at most `2/U` when `y ≤ U²/2`, and, by the closed
form of the Abel antiderivative, at most `η(U) = (2 + √2(2 log 3U + log U))/U` when `U²/2 ≤ y ≤ 2U²`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Upstream.AbelLogIntegral (lgAnti)
open Cvs.Upstream.SliceMeasurePushforward (kap sliceMeas)
open Cvs.Prolate.Gram.EquilibriumPotential (tE)

namespace Cvs.Prolate.Gram.TruncatedPotentialBound
open Cvs.ZeroCounting

/-! ### The `u`-tail -/

/-- The tail `τ_U(A, B) = ∫_U^∞ (log|u² − A| − log|u² − B|) du`. -/
def tailT (U A B : ℝ) : ℝ := ∫ u in Ioi U, (log (u ^ 2 - A) - log (u ^ 2 - B))

/-- The tail bound `η(U) = (2 + √2(2 log 3U + log U))/U`. -/
def etaU (U : ℝ) : ℝ := (2 + √2 * (2 * log (3 * U) + log U)) / U

/-- **The split at `U`**: `∫_0^U (log|u² − A| − log|u² − B|) = π√(−A)₊ − π√(−B)₊ − τ_U(A, B)`. -/
theorem integral_eq_sub_tail (A B : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    ∫ u in (0 : ℝ)..U, (log (u ^ 2 - A) - log (u ^ 2 - B)) = π * √(-A) - π * √(-B) - tailT U A B := by
  have hi := Cvs.Upstream.AbelLogIntegral.integrableOn_log_sub A B
  rw [← Cvs.Upstream.AbelLogIntegral.integral_log_sq_sub A B, ← Ioc_union_Ioi_eq_Ioi hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi (hi.mono_set (Ioc_subset_Ioi_self)) (hi.mono_set (Ioi_subset_Ioi hU)),
    intervalIntegral.integral_of_le hU, tailT]
  ring

/-- **The far tail**: `0 ≤ B − A ≤ 1`, `B ≤ U²/2`, `U ≥ 2` give `|τ_U(A, B)| ≤ 2/U`. -/
theorem abs_tailT_le_far {U A B : ℝ} (hU : 2 ≤ U) (hBA : 0 ≤ B - A) (hBA1 : B - A ≤ 1) (hB : B ≤ U ^ 2 / 2) :
    |tailT U A B| ≤ 2 / U := by
  have hU0 : 0 < U := by linarith
  have hpt : ∀ u ∈ Ioi U, 0 ≤ log (u ^ 2 - A) - log (u ^ 2 - B) ∧
      log (u ^ 2 - A) - log (u ^ 2 - B) ≤ 2 * u ^ (-2 : ℝ) := by
    intro u hu
    have hu0 : 0 < u := hU0.trans hu
    have hu2 : U ^ 2 < u ^ 2 := by nlinarith [mem_Ioi.mp hu]
    have hB2 : u ^ 2 / 2 ≤ u ^ 2 - B := by linarith
    have hpos : 0 < u ^ 2 - B := by nlinarith
    refine ⟨sub_nonneg.mpr (Real.log_le_log hpos (by linarith)), ?_⟩
    rw [← Real.log_div (by linarith) hpos.ne']
    have h1 : (u ^ 2 - A) / (u ^ 2 - B) = 1 + (B - A) / (u ^ 2 - B) := by field_simp; ring
    rw [h1]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [add_sub_cancel_left, Real.rpow_neg hu0.le, Real.rpow_two, div_le_iff₀ hpos]
    have : (u ^ 2)⁻¹ * u ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
    nlinarith
  have hint : IntegrableOn (fun u : ℝ => 2 * u ^ (-2 : ℝ)) (Ioi U) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hU0).const_mul 2
  have hfi : IntegrableOn (fun u => log (u ^ 2 - A) - log (u ^ 2 - B)) (Ioi U) :=
    (Cvs.Upstream.AbelLogIntegral.integrableOn_log_sub A B).mono_set (Ioi_subset_Ioi hU0.le)
  have h0 : 0 ≤ tailT U A B := setIntegral_nonneg measurableSet_Ioi fun u hu => (hpt u hu).1
  have h1 : tailT U A B ≤ ∫ u in Ioi U, 2 * u ^ (-2 : ℝ) :=
    setIntegral_mono_on hfi hint measurableSet_Ioi fun u hu => (hpt u hu).2
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hU0] at h1
  rw [abs_of_nonneg h0]
  refine h1.trans_eq ?_
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- `κ_1 ≤ κ_ρ + log(1/ρ)` for `0 < ρ ≤ 1`. -/
theorem kap_one_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (w : ℝ) : kap 1 w ≤ kap ρ w + log (1 / ρ) := by
  unfold kap
  have h1 : 0 < max |w| ρ := lt_max_of_lt_right hρ
  have h2 : max |w| 1 ≤ max |w| ρ / ρ := by
    rw [le_div_iff₀ hρ]
    rcases le_total 1 |w| with h | h
    · rw [max_eq_left h]; exact (mul_le_of_le_one_right (abs_nonneg w) hρ1).trans (le_max_left _ _)
    · rw [max_eq_right h, one_mul]; exact le_max_right _ _
  have h3 := Real.log_le_log (lt_max_of_lt_right one_pos) h2
  rw [Real.log_div h1.ne' hρ.ne'] at h3
  rw [Real.log_div one_ne_zero hρ.ne', Real.log_one]
  linarith

/-- `∫_a^b κ_ρ ≤ 2ρ`. -/
theorem integral_kap_le {ρ a b : ℝ} (hρ : 0 < ρ) (hab : a ≤ b) : ∫ w in a..b, kap ρ w ≤ 2 * ρ := by
  rw [intervalIntegral.integral_of_le hab]
  have hne : ∀ᵐ w ∂(volume.restrict (Ioc a b)), 0 ≤ kap ρ w := by
    refine ae_restrict_of_ae ?_
    have : ∀ᵐ w ∂(volume : Measure ℝ), w ≠ 0 := by rw [ae_iff]; simp
    exact this.mono fun w hw => Cvs.Upstream.SliceMeasurePushforward.kap_nonneg hw
  rw [integral_eq_lintegral_of_nonneg_ae hne (Cvs.Upstream.SliceMeasurePushforward.measurable_kap ρ).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (setLIntegral_le_lintegral _ _).trans ?_
  have := Cvs.Upstream.SliceMeasurePushforward.lintegral_kap hρ 0
  simp only [sub_zero] at this
  rw [this]

/-- **The near tail in closed form**: for `A, B ≥ 0`, `τ_U(A, B) = ∫_{U+√A}^{U+√B} log − ∫_{U−√B}^{U−√A} log`. -/
theorem tailT_eq {U A B : ℝ} (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    tailT U A B = (∫ w in (U + √A)..(U + √B), log w) - ∫ w in (U - √B)..(U - √A), log w := by
  have h := integral_eq_sub_tail A B hU
  rw [Cvs.Upstream.AbelLogIntegral.integral_log_sub A B hU, Real.sqrt_eq_zero_of_nonpos (by linarith : -A ≤ 0),
    Real.sqrt_eq_zero_of_nonpos (by linarith : -B ≤ 0)] at h
  rw [integral_log, integral_log]
  unfold lgAnti at h
  rw [ite_eq_left hA, ite_eq_left hB] at h
  linarith

/-- **The near tail**: `0 ≤ B − A ≤ 1`, `U²/2 ≤ B ≤ 2U²`, `U ≥ 4` give `|τ_U(A, B)| ≤ η(U)`. -/
theorem abs_tailT_le_near {U A B : ℝ} (hU : 4 ≤ U) (hBA : 0 ≤ B - A) (hBA1 : B - A ≤ 1) (hB1 : U ^ 2 / 2 ≤ B)
    (hB2 : B ≤ 2 * U ^ 2) : |tailT U A B| ≤ etaU U := by
  have hU0 : 0 < U := by linarith
  have hA : 0 ≤ A := by nlinarith
  have hB : 0 ≤ B := by linarith
  set α := √A with hα
  set β := √B with hβ
  have hα0 : 0 ≤ α := Real.sqrt_nonneg A
  have hαβ : α ≤ β := Real.sqrt_le_sqrt (by linarith)
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs20 : 0 < √2 := by positivity
  have hβU : β ≤ √2 * U := by
    rw [hβ, Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by norm_num)]; linarith
  have hβL : U ≤ √2 * β := by
    have : U ^ 2 ≤ (√2 * β) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num), hβ, Real.sq_sqrt hB]; linarith
    exact (pow_le_pow_iff_left₀ hU0.le (by positivity) two_ne_zero).mp this
  have hβ0 : 0 < β := by nlinarith
  set ℓ := β - α with hℓ
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hℓU : ℓ ≤ √2 / U := by
    have e : ℓ * (α + β) = B - A := by
      rw [hℓ]; nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB]
    rw [le_div_iff₀ hU0]
    have : ℓ * β ≤ 1 := by nlinarith
    nlinarith
  have hl3 : 0 ≤ log (3 * U) := Real.log_nonneg (by linarith)
  have hlU : 0 ≤ log U := Real.log_nonneg (by linarith)
  have h3U : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  -- the outer integral
  have i1 : |∫ w in (U + α)..(U + β), log w| ≤ ℓ * log (3 * U) := by
    have h0 : 0 ≤ ∫ w in (U + α)..(U + β), log w := intervalIntegral.integral_nonneg (by linarith)
      fun w hw => Real.log_nonneg (by linarith [hw.1])
    have h1 : ∫ w in (U + α)..(U + β), log w ≤ ∫ w in (U + α)..(U + β), log (3 * U) :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegral.intervalIntegrable_log'
        intervalIntegrable_const fun w hw => Real.log_le_log (by linarith [hw.1]) (by nlinarith [hw.2])
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    rw [abs_of_nonneg h0]; linarith
  -- the inner integral
  have i2 : |∫ w in (U - β)..(U - α), log w| ≤ ℓ * log (3 * U) + 2 / U + ℓ * log U := by
    have hab : U - β ≤ U - α := by linarith
    have hpt : ∀ w ∈ Icc (U - β) (U - α), |log w| ≤ log (3 * U) + (kap (1 / U) w + log U) := by
      intro w hw
      have hw' : |w| ≤ U := by rw [abs_le]; constructor <;> nlinarith [hw.1, hw.2]
      have h1 := Cvs.Upstream.SliceMeasurePushforward.abs_log_le hw'
      rw [Real.log_abs] at h1
      have h2 := kap_one_le (ρ := 1 / U) (by positivity) (by rw [div_le_one hU0]; linarith) w
      rw [one_div_one_div] at h2
      have h3 : log (1 + U) ≤ log (3 * U) := Real.log_le_log (by linarith) (by linarith)
      linarith
    have hki : IntervalIntegrable (fun w => kap (1 / U) w) volume (U - β) (U - α) := by
      have e : (fun w => kap (1 / U) w) = fun w => log (max |w| (1 / U)) - log |w| := rfl
      rw [e]
      refine IntervalIntegrable.sub ?_ ?_
      · exact (ContinuousOn.log (by fun_prop) fun w _ =>
          (lt_max_of_lt_right (by positivity)).ne').intervalIntegrable
      · simp_rw [Real.log_abs]; exact intervalIntegral.intervalIntegrable_log'
    calc |∫ w in (U - β)..(U - α), log w| ≤ ∫ w in (U - β)..(U - α), |log w| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ w in (U - β)..(U - α), (log (3 * U) + (kap (1 / U) w + log U)) :=
          intervalIntegral.integral_mono_on hab intervalIntegral.intervalIntegrable_log'.abs
            (intervalIntegrable_const.add (hki.add intervalIntegrable_const)) hpt
      _ = ℓ * log (3 * U) + (∫ w in (U - β)..(U - α), kap (1 / U) w) + ℓ * log U := by
          rw [intervalIntegral.integral_add intervalIntegrable_const (hki.add intervalIntegrable_const),
            intervalIntegral.integral_add hki intervalIntegrable_const, intervalIntegral.integral_const,
            intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
          rw [hℓ]; ring
      _ ≤ ℓ * log (3 * U) + 2 / U + ℓ * log U := by
          have := integral_kap_le (ρ := 1 / U) (by positivity) hab
          have e : 2 * (1 / U) = 2 / U := by ring
          linarith
  rw [tailT_eq hU0.le hA hB]
  refine (abs_sub _ _).trans ?_
  have hfin : ℓ * (2 * log (3 * U) + log U) ≤ √2 / U * (2 * log (3 * U) + log U) :=
    mul_le_mul_of_nonneg_right hℓU (by positivity)
  unfold etaU
  rw [add_div]
  have e : √2 * (2 * log (3 * U) + log U) / U = √2 / U * (2 * log (3 * U) + log U) := by ring
  rw [e]
  nlinarith

/-- **The tail bound**: `0 ≤ B ≤ 2U²`, `0 ≤ B − A ≤ 1`, `U ≥ 4` give `|τ_U(A, B)| ≤ η(U)`. -/
theorem abs_tailT_le {U A B : ℝ} (hU : 4 ≤ U) (hBA : 0 ≤ B - A) (hBA1 : B - A ≤ 1) (hB2 : B ≤ 2 * U ^ 2) :
    |tailT U A B| ≤ etaU U := by
  rcases le_total B (U ^ 2 / 2) with h | h
  · refine (abs_tailT_le_far (by linarith) hBA hBA1 h).trans ?_
    unfold etaU
    have hl3 : 0 ≤ log (3 * U) := Real.log_nonneg (by linarith)
    have hlU : 0 ≤ log U := Real.log_nonneg (by linarith)
    gcongr
    nlinarith [Real.sqrt_nonneg 2]
  · exact abs_tailT_le_near hU hBA hBA1 h hB2

/-! ### The potential of `μ⁺ − μ⁻` -/

open Cvs.Prolate.Gram.SelectionTargetMeasure (phiZ muP muM)

/-- **The slice potential**: `∫ log|y − v| dν = ∫_α^β φ(t)∫_0^U log|y − t² − u²| du dt` for a box slice. -/
theorem integral_log_box {α β U : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β < 1) (hU : 0 ≤ U) (y : ℝ) :
    ∫ v, log |y - v| ∂(sliceMeas phiZ (fun _ => U) α β) =
      ∫ t in α..β, phiZ t * ∫ u in (0 : ℝ)..U, log |y - (t ^ 2 + u ^ 2)| ∧
    IntegrableOn (fun t => phiZ t * ∫ u in (0 : ℝ)..U, log |y - (t ^ 2 + u ^ 2)|) (Icc α β) := by
  have : IsFiniteMeasure (sliceMeas phiZ (fun _ => U) α β) := Cvs.Prolate.Gram.SelectionTargetMeasure.isFiniteMeasure_box hβ hα
  have hφi : IntegrableOn phiZ (Icc α β) := Cvs.Prolate.Gram.SelectionTargetMeasure.integrableOn_phiZ_of_subset hα hβ.le
  have hsupp : sliceMeas phiZ (fun _ => U) α β (Icc 0 (1 + U ^ 2))ᶜ = 0 :=
    Cvs.Upstream.SliceMeasurePushforward.sliceMeas_compl Cvs.Prolate.Gram.SelectionTargetMeasure.measurable_phiZ measurable_const fun t ht => by nlinarith [ht.1, ht.2]
  have hint := Cvs.Upstream.SliceMeasurePushforward.integrable_log_sliceMeas Cvs.Prolate.Gram.SelectionTargetMeasure.measurable_phiZ measurable_const
    (fun t _ => Cvs.Prolate.Gram.SelectionTargetMeasure.phiZ_nonneg t) hφi hsupp y
  have hg : Measurable fun v => log |y - v| := Real.measurable_log.comp (measurable_const.sub measurable_id).abs
  have hL : Measurable (fun _ : ℝ => U) := measurable_const
  have hφ0 : ∀ t ∈ Icc α β, 0 ≤ phiZ t := fun t _ => Cvs.Prolate.Gram.SelectionTargetMeasure.phiZ_nonneg t
  have hL0 : ∀ t ∈ Icc α β, 0 ≤ (fun _ : ℝ => U) t := fun _ _ => hU
  have e1 := Cvs.Upstream.SliceMeasurePushforward.integral_sliceMeas
    Cvs.Prolate.Gram.SelectionTargetMeasure.measurable_phiZ hL hφ0 hL0 hαβ hg hint
  have e2 := Cvs.Upstream.SliceMeasurePushforward.integrableOn_inner
    Cvs.Prolate.Gram.SelectionTargetMeasure.measurable_phiZ hL hφ0 hL0 hg hint
  exact ⟨e1, e2⟩

/-- **The inner integral**: `∫_0^U log|y − t² − u²| − ∫_0^U log|y − u²| = π√(t² − y)₊ − τ_U(y − t², y)` for `y ≥ 0`. -/
theorem inner_sub_eq {U y : ℝ} (t : ℝ) (hU : 0 ≤ U) (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..U, log |y - (t ^ 2 + u ^ 2)|) - ∫ u in (0 : ℝ)..U, log |y - u ^ 2| =
      π * √(t ^ 2 - y) - tailT U (y - t ^ 2) y := by
  have e1 : ∀ u : ℝ, log |y - (t ^ 2 + u ^ 2)| = log (u ^ 2 - (y - t ^ 2)) := fun u => by
    rw [Real.log_abs, show y - (t ^ 2 + u ^ 2) = -(u ^ 2 - (y - t ^ 2)) by ring, Real.log_neg_eq_log]
  have e2 : ∀ u : ℝ, log |y - u ^ 2| = log (u ^ 2 - y) := fun u => by
    rw [Real.log_abs, show y - u ^ 2 = -(u ^ 2 - y) by ring, Real.log_neg_eq_log]
  simp_rw [e1, e2]
  rw [← intervalIntegral.integral_sub (Cvs.Upstream.AbelLogIntegral.intervalIntegrable_log_sq_sub _ 0 U)
    (Cvs.Upstream.AbelLogIntegral.intervalIntegrable_log_sq_sub _ 0 U), integral_eq_sub_tail _ _ hU, neg_sub,
    Real.sqrt_eq_zero_of_nonpos (by linarith : -y ≤ 0)]
  ring

/-- **The potential of `μ_a^{(U)}`**: for `a ∈ [½, 3/5]`, `U ≥ 4` and `0 ≤ y ≤ 2U²`,
`|∫ log|y − v| dμ⁺ − ∫ log|y − v| dμ⁻ − Ψ_a(y)| ≤ η(U)/2`. -/
theorem abs_pot_sub_psiA_le {a U y : ℝ} (ha : a ∈ Icc (1 / 2 : ℝ) (3 / 5)) (hU : 4 ≤ U) (hy0 : 0 ≤ y)
    (hy : y ≤ 2 * U ^ 2) :
    |(∫ v, log |y - v| ∂(muP a U)) - (∫ v, log |y - v| ∂(muM a U)) - Cvs.Prolate.Gram.EquilibriumPotential.psiA a y| ≤ etaU U / 2 := by
  obtain ⟨h0, hat, hte, h2⟩ := Cvs.Prolate.Gram.SelectionTargetMeasure.tE_facts ha
  have ha1 : a < 1 := hat.trans_lt hte
  have hU0 : 0 ≤ U := by linarith
  set Lt : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..U, log |y - (t ^ 2 + u ^ 2)| with hLt
  set L0 : ℝ := ∫ u in (0 : ℝ)..U, log |y - u ^ 2| with hL0
  obtain ⟨hP, hPi⟩ := integral_log_box h0 hat hte hU0 y
  obtain ⟨hM, hMi⟩ := integral_log_box le_rfl h0 ha1 hU0 y
  have hPi' : IntervalIntegrable (fun t => phiZ t * Lt t) volume a (tE a) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hat).mpr hPi
  have hMi' : IntervalIntegrable (fun t => phiZ t * Lt t) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le h0).mpr hMi
  have hsq : Continuous fun t : ℝ => π * √(t ^ 2 - y) := by fun_prop
  have hqP := Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ_mul h0 hat hte.le hsq
  have hqM := Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ_mul le_rfl h0 ha1.le hsq
  have hcP := Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ_mul h0 hat hte.le (continuous_const (y := L0))
  have hcM := Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ_mul le_rfl h0 ha1.le (continuous_const (y := L0))
  -- `Ψ_a` through `φ`
  have hφπ : ∀ α β : ℝ, ∫ t in α..β, phiZ t * (π * √(t ^ 2 - y)) =
      1 / 2 * ∫ t in α..β, 1 / √(1 - t ^ 2) * √(t ^ 2 - y) := fun α β => by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [phiZ]; field_simp
  have hΨ : Cvs.Prolate.Gram.EquilibriumPotential.psiA a y = (∫ t in a..tE a, phiZ t * (π * √(t ^ 2 - y))) -
      ∫ t in (0 : ℝ)..a, phiZ t * (π * √(t ^ 2 - y)) := by
    have hs := (Cvs.Prolate.Gram.EquilibriumPotential.integral_wA_mul h0 h2 (g := fun t => √(t ^ 2 - y)) (by fun_prop)).2
    rw [hφπ, hφπ]
    unfold Cvs.Prolate.Gram.EquilibriumPotential.psiA
    rw [hs]; ring
  have hz : ∫ t in a..tE a, phiZ t * L0 = ∫ t in (0 : ℝ)..a, phiZ t * L0 := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, Cvs.Prolate.Gram.SelectionTargetMeasure.integral_phiZ_eq ha]
  -- the remainder
  have hr : ∀ t ∈ Icc (0 : ℝ) 1, |Lt t - π * √(t ^ 2 - y) - L0| ≤ etaU U := fun t ht => by
    have e : Lt t - π * √(t ^ 2 - y) - L0 = -tailT U (y - t ^ 2) y := by
      have := inner_sub_eq (y := y) t hU0 hy0; simp only [hLt, hL0] at this ⊢; linarith
    rw [e, abs_neg]
    exact abs_tailT_le hU (by nlinarith [sq_nonneg t]) (by nlinarith [ht.1, ht.2]) hy
  have hb : ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 1 →
      IntervalIntegrable (fun t => phiZ t * Lt t) volume α β →
      IntervalIntegrable (fun t => phiZ t * (π * √(t ^ 2 - y))) volume α β →
      IntervalIntegrable (fun t => phiZ t * L0) volume α β →
      |(∫ t in α..β, phiZ t * Lt t) - (∫ t in α..β, phiZ t * (π * √(t ^ 2 - y))) - ∫ t in α..β, phiZ t * L0| ≤
        etaU U * ∫ t in α..β, phiZ t := fun α β hα hαβ hβ i1 i2 i3 => by
    rw [← intervalIntegral.integral_sub i1 i2, ← intervalIntegral.integral_sub (i1.sub i2) i3,
      ← intervalIntegral.integral_const_mul]
    refine (Real.norm_eq_abs _ ▸ intervalIntegral.norm_integral_le_of_norm_le hαβ (Eventually.of_forall
      fun t ht => ?_) ((Cvs.Prolate.Gram.SelectionTargetMeasure.intervalIntegrable_phiZ hα hαβ hβ).const_mul _))
    rw [Real.norm_eq_abs, show phiZ t * Lt t - phiZ t * (π * √(t ^ 2 - y)) - phiZ t * L0 =
      phiZ t * (Lt t - π * √(t ^ 2 - y) - L0) by ring, abs_mul, abs_of_nonneg (Cvs.Prolate.Gram.SelectionTargetMeasure.phiZ_nonneg t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hr t ⟨hα.trans ht.1.le, ht.2.trans hβ⟩) (Cvs.Prolate.Gram.SelectionTargetMeasure.phiZ_nonneg t)
  have bP := hb a (tE a) h0 hat hte.le hPi' hqP hcP
  have bM := hb 0 a le_rfl h0 ha1.le hMi' hqM hcM
  have hI : ∫ t in (0 : ℝ)..a, phiZ t ≤ 1 / 4 := by
    rw [Cvs.Prolate.Gram.SelectionTargetMeasure.integral_phiZ_eq ha]; exact Cvs.Prolate.Gram.SelectionTargetMeasure.integral_phiZ_le ha
  have hη : 0 ≤ etaU U := by
    unfold etaU
    have hl3 : 0 ≤ log (3 * U) := Real.log_nonneg (by linarith)
    have hlU : 0 ≤ log U := Real.log_nonneg (by linarith)
    positivity
  have muP_eq : muP a U = sliceMeas phiZ (fun _ => U) a (tE a) := rfl
  have muM_eq : muM a U = sliceMeas phiZ (fun _ => U) 0 a := rfl
  rw [muP_eq, muM_eq, hP, hM, hΨ]
  have e : (∫ t in a..tE a, phiZ t * Lt t) - (∫ t in (0 : ℝ)..a, phiZ t * Lt t) -
      ((∫ t in a..tE a, phiZ t * (π * √(t ^ 2 - y))) - ∫ t in (0 : ℝ)..a, phiZ t * (π * √(t ^ 2 - y))) =
      ((∫ t in a..tE a, phiZ t * Lt t) - (∫ t in a..tE a, phiZ t * (π * √(t ^ 2 - y))) -
        ∫ t in a..tE a, phiZ t * L0) -
      ((∫ t in (0 : ℝ)..a, phiZ t * Lt t) - (∫ t in (0 : ℝ)..a, phiZ t * (π * √(t ^ 2 - y))) -
        ∫ t in (0 : ℝ)..a, phiZ t * L0) := by rw [hz]; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [← Cvs.Prolate.Gram.SelectionTargetMeasure.integral_phiZ_eq ha] at bP
  nlinarith [mul_le_mul_of_nonneg_left hI hη]

/-- **`η(U) → 0`**. -/
theorem tendsto_etaU : Tendsto etaU atTop (𝓝 0) := by
  have h1 : Tendsto (fun U : ℝ => log U / U) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun U : ℝ => 1 / U) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h := ((h2.const_mul (2 + 2 * √2 * log 3)).add (h1.const_mul (3 * √2)))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with U hU
  unfold etaU
  rw [Real.log_mul (by norm_num) hU.ne']
  field_simp
  ring

end Cvs.Prolate.Gram.TruncatedPotentialBound

end
