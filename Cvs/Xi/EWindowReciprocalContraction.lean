import Mathlib
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.SpineProfileWindowNormPos
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.AngularBesselInequality
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Reciprocal reversibility and contraction of the E-window

The reciprocal branches of the finite window preserve their integration interval.
Their transposed row mass is the same as their row mass, which is at most one.
Pointwise Cauchy–Schwarz therefore gives contraction in physical Lebesgue measure.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.Xi.EWindowReciprocalContraction
open Cvs.ZeroCounting

open Cvs.Xi.EImageWindowPoisson (window eimage)

/-- One reciprocal branch of the finite E-window. -/
def branch (a : ℝ) (n : ℕ) (G : ℝ → ℝ) : ℝ → ℝ :=
  (Icc (n * a) 1).indicator (fun θ => a / θ * G (n * a / θ))

/-- The reciprocal map preserves the interval `[b,1]`, for `b > 0`. -/
theorem image_recip_Icc {b : ℝ} (hb : 0 < b) :
    (fun θ => b / θ) '' Icc b 1 = Icc b 1 := by
  ext u
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have hθ0 : 0 < θ := hb.trans_le hθ.1
    refine ⟨?_, (div_le_one hθ0).mpr hθ.1⟩
    rw [le_div_iff₀ hθ0]
    nlinarith [hθ.2]
  · intro hu
    have hu0 : 0 < u := hb.trans_le hu.1
    refine ⟨b / u, ⟨?_, (div_le_one hu0).mpr hu.1⟩, ?_⟩
    · rw [le_div_iff₀ hu0]
      nlinarith [hu.2]
    · field_simp

/-- Reciprocal change of variables transposes a branch in physical Lebesgue measure. -/
theorem integral_branch_recip {a b : ℝ} (hb : 0 < b) (G H : ℝ → ℝ) :
    ∫ θ in Icc b 1, a / θ * G (b / θ) * H θ
      = ∫ u in Icc b 1, a / u * G u * H (b / u) := by
  have hderiv := Cvs.Xi.EImageWindowPoisson.hasDerivWithinAt_recip hb 1
  have hinj := Cvs.Xi.EImageWindowPoisson.injOn_recip hb (n := 1) (by omega)
  simp only [Nat.cast_one, one_mul] at hderiv hinj
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj
    (fun u : ℝ => a / u * G u * H (b / u))
  rw [image_recip_Icc hb] at hchange
  rw [hchange]
  refine setIntegral_congr_fun (measurableSet_Icc (a := b) (b := (1 : ℝ))) fun θ hθ => ?_
  have hθ0 : 0 < θ := hb.trans_le hθ.1
  simp only [smul_eq_mul]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _))]
  have e : b / (b / θ) = θ := by field_simp
  rw [e]
  field_simp

/-- The window is the finite sum of its reciprocal branches. -/
theorem window_eq_sum_branch {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) :
    window a G = fun θ => ∑ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, branch a n G θ := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · have hθ0 : 0 < θ := ha.trans_le hθ.1
    rw [window, indicator_of_mem hθ,
      Cvs.Xi.EImageWindowPoisson.eimage_eq_sum_indicator ha hθ0 hθ.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hna : 0 < (n : ℝ) * a := by positivity
    by_cases h : n * a ≤ θ
    · have hu : n * a / θ ∈ Icc (0 : ℝ) 1 :=
        ⟨(div_pos hna hθ0).le, (div_le_one hθ0).mpr h⟩
      have hm : θ ∈ Icc (n * a) 1 := ⟨h, hθ.2⟩
      simp only [branch, indicator_of_mem hu, indicator_of_mem hm]
    · have hu : n * a / θ ∉ Icc (0 : ℝ) 1 := fun hu =>
        h ((div_le_one hθ0).mp hu.2)
      simp only [branch, indicator_of_notMem hu,
        indicator_of_notMem (fun hm : θ ∈ Icc (n * a) 1 => h hm.1), mul_zero]
  · rw [Cvs.Xi.EImageWindowPoisson.window_of_notMem G hθ]
    symm
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hna : a ≤ n * a := by nlinarith
    exact indicator_of_notMem (fun hm : θ ∈ Icc (n * a) 1 => hθ ⟨hna.trans hm.1, hm.2⟩) _

/-- A reciprocal branch of a continuous profile is integrable. -/
theorem integrable_branch {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    {G : ℝ → ℝ} (hG : ContinuousOn G (Icc 0 1)) : Integrable (branch a n G) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < (n : ℝ) * a := by positivity
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  apply ContinuousOn.integrableOn_Icc
  have hrec : ContinuousOn (fun θ => (n : ℝ) * a / θ) (Icc (n * a) 1) :=
    continuousOn_const.div continuousOn_id (fun θ hθ => (hb.trans_le hθ.1).ne')
  exact (continuousOn_const.div continuousOn_id
    (fun θ (hθ : θ ∈ Icc ((n : ℝ) * a) 1) => (hb.trans_le hθ.1).ne')).mul
      (hG.comp hrec (fun θ hθ => ⟨(div_pos hb (hb.trans_le hθ.1)).le,
        (div_le_one (hb.trans_le hθ.1)).mpr hθ.1⟩))

/-- The continuous E-window is integrable. -/
theorem integrable_window {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc 0 1)) : Integrable (window a G) := by
  rw [window_eq_sum_branch ha]
  exact integrable_finsetSum _ fun n hn =>
    integrable_branch ha (Finset.mem_Icc.mp hn).1 hG

/-- The row mass of the E-window lies in `[0,1]`. -/
theorem window_one_mem_Icc {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    window a (fun _ => 1) θ ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · by_cases hθ : θ ∈ Icc a 1
    · have hθ0 : 0 < θ := ha.trans_le hθ.1
      simp only [window, indicator_of_mem hθ, eimage]
      positivity
    · rw [Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hθ]
  · exact (le_abs_self _).trans (Cvs.L2a.SpineProfileWindowNormPos.abs_window_le ha zero_le_one
      (by intro u hu; norm_num) θ)

/-- Pointwise Jensen for the E-window, with its exact row mass at most one. -/
theorem window_sq_le_window_sq {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) (θ : ℝ) :
    window a G θ ^ 2 ≤ window a (fun u => G u ^ 2) θ := by
  by_cases hθ : θ ∈ Icc a 1
  · have hθ0 : 0 < θ := ha.trans_le hθ.1
    have hb : 0 ≤ a / θ := (div_pos ha hθ0).le
    have hfl : (⌊θ / a⌋₊ : ℝ) ≤ θ / a := Nat.floor_le (by positivity)
    have hmass : (a / θ) * ⌊θ / a⌋₊ ≤ 1 := by
      calc a / θ * ⌊θ / a⌋₊ ≤ a / θ * (θ / a) := mul_le_mul_of_nonneg_left hfl hb
        _ = 1 := by field_simp
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 ⌊θ / a⌋₊)
      (f := fun n : ℕ => G (n * a / θ))
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcs
    have hsum : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ) ^ 2 :=
      Finset.sum_nonneg fun n hn => sq_nonneg _
    simp only [window, indicator_of_mem hθ, eimage, mul_pow]
    calc (a / θ) ^ 2 * (∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)) ^ 2
        ≤ (a / θ) ^ 2 * (⌊θ / a⌋₊ * ∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      _ = (a / θ * ⌊θ / a⌋₊) * (a / θ * ∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ) ^ 2) := by ring
      _ ≤ 1 * (a / θ * ∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hmass (mul_nonneg hb hsum)
      _ = _ := one_mul _
  · simp [Cvs.Xi.EImageWindowPoisson.window_of_notMem _ hθ]

/-- Integrating a window transposes its row mass onto the original profile. -/
theorem integral_window_eq_row_mass {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc 0 1)) :
    ∫ θ, window a G θ = ∫ u in Icc a 1, G u * window a (fun _ => 1) u := by
  rw [window_eq_sum_branch ha,
    integral_finsetSum _ (fun n hn => integrable_branch ha (Finset.mem_Icc.mp hn).1 hG)]
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊,
      ∫ θ, branch a n G θ = ∫ u, (Icc (n * a) 1).indicator (fun u => a / u * G u) u := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hb : 0 < (n : ℝ) * a := by positivity
    rw [branch, integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc]
    simpa only [mul_one] using integral_branch_recip (a := a) hb G (fun _ => 1)
  rw [Finset.sum_congr rfl hterm]
  have hi : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊,
      Integrable ((Icc (n * a) 1).indicator (fun u => a / u * G u)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hb : 0 < (n : ℝ) * a := by positivity
    refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
    apply ContinuousOn.integrableOn_Icc
    exact (continuousOn_const.div continuousOn_id
      (fun u (hu : u ∈ Icc ((n : ℝ) * a) 1) => (hb.trans_le hu.1).ne')).mul
        (hG.mono (fun u hu => ⟨hb.le.trans hu.1, hu.2⟩))
  rw [← integral_finsetSum _ hi, ← integral_indicator measurableSet_Icc]
  congr 1
  funext u
  rw [window_eq_sum_branch ha]
  by_cases hu : u ∈ Icc a 1
  · rw [indicator_of_mem hu]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases hn : u ∈ Icc (n * a) 1
    · simp only [branch, indicator_of_mem hn]; ring
    · simp only [branch, indicator_of_notMem hn, mul_zero]
  · rw [indicator_of_notMem hu]
    exact Finset.sum_eq_zero fun n hn => by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hna : a ≤ n * a := by nlinarith
      exact indicator_of_notMem (fun hm : u ∈ Icc (n * a) 1 => hu ⟨hna.trans hm.1, hm.2⟩) _

/-- The E-window contracts the squared norm to the physical profile energy on `[a,1]`. -/
theorem integral_window_sq_le_cut {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc 0 1)) :
    ∫ θ, window a G θ ^ 2 ≤ ∫ u in Icc a 1, G u ^ 2 := by
  have hG2 : ContinuousOn (fun u => G u ^ 2) (Icc (0 : ℝ) 1) := hG.pow 2
  have hW2 : Integrable (window a (fun u => G u ^ 2)) :=
    integrable_window (G := fun u => G u ^ 2) ha hG2
  calc ∫ θ, window a G θ ^ 2 ≤ ∫ θ, window a (fun u => G u ^ 2) θ :=
      integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
        hW2
        (ae_of_all _ fun θ => window_sq_le_window_sq ha G θ)
    _ = ∫ u in Icc a 1, G u ^ 2 * window a (fun _ => 1) u :=
      integral_window_eq_row_mass ha hG2
    _ ≤ ∫ u in Icc a 1, G u ^ 2 := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun u => mul_nonneg (sq_nonneg _) (window_one_mem_Icc ha u).1)
        (hG2.mono (fun u (hu : u ∈ Icc a 1) => ⟨ha.le.trans hu.1, hu.2⟩)).integrableOn_Icc
      exact ae_of_all _ fun u => mul_le_of_le_one_right (sq_nonneg _) (window_one_mem_Icc ha u).2

/-- The E-window is an `L²` contraction, with no harmonic-number loss. -/
theorem integral_window_sq_le {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc 0 1)) :
    ∫ θ, window a G θ ^ 2 ≤ ∫ u in Icc (0 : ℝ) 1, G u ^ 2 := by
  refine (integral_window_sq_le_cut ha hG).trans ?_
  exact setIntegral_mono_set (hG.pow 2).integrableOn_Icc
    (ae_of_all _ fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall (Icc_subset_Icc ha.le le_rfl))

/-- For an even profile the window energy is at most half the full angular energy. -/
theorem integral_window_sq_le_half {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc (-1 : ℝ) 1))
    (heven : ∀ u ∈ Icc (-1 : ℝ) 1, G (-u) = G u) :
    ∫ θ, window a G θ ^ 2 ≤ 1 / 2 * ∫ u in (-1 : ℝ)..1, G u ^ 2 := by
  have h := integral_window_sq_le ha
    (hG.mono (Icc_subset_Icc (by norm_num) le_rfl))
  rw [Cvs.Prolate.AngularBesselInequality.integral_sq_even hG heven,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  linarith

/-- Log scaling and translation preserve the contraction energy bound. -/
theorem integral_logScale_window_sq_le {x : ℝ} (hx : 0 < x) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc 0 1)) (L : ℝ) :
    ∫ s, Cvs.L2a.TailLogScaleTest.logScale (window (1 / x) G) (s - L) ^ 2
      ≤ ∫ u in Icc (0 : ℝ) 1, G u ^ 2 := by
  set W := window (1 / x) G with hW
  have ha : 0 < 1 / x := one_div_pos.mpr hx
  rw [integral_sub_right_eq_self (fun s => Cvs.L2a.TailLogScaleTest.logScale W s ^ 2) L]
  have h1 : ∫ s, Cvs.L2a.TailLogScaleTest.logScale W s ^ 2
      = ∫ θ in Ioi (0 : ℝ), W θ ^ 2 := by
    have h := Cvs.WeilForm.ThetaFormWindowIdentification.selfConvolution_logScale_log W (k := 1) one_pos
    simp only [Cvs.Zeta.Explicit.Weil.selfConvolution, Real.log_one, add_zero,
      Real.sqrt_one, one_mul] at h
    simpa [sq] using h
  have h2 : ∫ θ in Ioi (0 : ℝ), W θ ^ 2 = ∫ θ, W θ ^ 2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun θ hθ => ?_
    have hn : θ ∉ Icc (1 / x) 1 := fun h => hθ (ha.trans_le h.1)
    rw [hW, Cvs.Xi.EImageWindowPoisson.window_of_notMem G hn]
    ring
  rw [h1, h2]
  exact integral_window_sq_le ha hG

/-- The actual Connes window has at most the energy of its singleton spine profile. -/
theorem integral_connesK_sq_le {x : ℝ} (hx : 0 < x) :
    ∫ s, Cvs.Approximant.ConnesVectorRealScale.connesK x s ^ 2
      ≤ ∫ u in Icc (0 : ℝ) 1,
        Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) (fun _ => 1) u ^ 2 := by
  exact integral_logScale_window_sq_le hx
    ((Cvs.Approximant.ConnesVectorRealScale.continuousOn_spineG _ _).mono
      (Icc_subset_Icc (by norm_num) le_rfl)) _

end Cvs.Xi.EWindowReciprocalContraction
