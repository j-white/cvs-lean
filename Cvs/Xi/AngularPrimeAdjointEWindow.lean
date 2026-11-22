import Mathlib
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.WindowFormTailLimit
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.MangoldtDilationEWindow
import Cvs.Xi.MobiusReconstruction

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The angular prime adjoint and the actual E-window

The Jacobian-weighted prime adjoint intertwines the actual E-window with
forward Mangoldt dilation, including every finite interval gate.
-/

noncomputable section

open Real Set MeasureTheory
open scoped ArithmeticFunction

namespace Cvs.Xi.AngularPrimeAdjointEWindow

open Cvs.Xi.EImageWindowPoisson (eimage window)
open Cvs.Xi.MangoldtDilationEWindow (primeWindow centeredLog)

/-- The angular prime adjoint, with its exact Jacobian and window gate. -/
def primeAdjoint (a : ℝ) (F : ℝ → ℝ) : ℝ → ℝ :=
  (Icc a 1).indicator (fun θ =>
    ∑ m ∈ Finset.Icc 1 ⌊θ / a⌋₊, Λ m / m * F (θ / m))

/-- The finite product triangle may be summed in either order. -/
theorem sum_mul_triangle_comm (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / n), F n m)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / m), F n m := by
  have hswap : ∀ n m : ℕ,
      n ∈ Finset.Icc 1 N ∧ m ∈ Finset.Icc 1 (N / n) ↔
        n ∈ Finset.Icc 1 (N / m) ∧ m ∈ Finset.Icc 1 N := by
    intro n m
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, _⟩, hm1, hmn⟩
      have hmul : m * n ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hmn
      refine ⟨⟨hn1, (Nat.le_div_iff_mul_le (by omega)).mpr
        (by simpa [Nat.mul_comm] using hmul)⟩, hm1, ?_⟩
      exact (Nat.le_mul_of_pos_right m (by omega)).trans hmul
    · rintro ⟨⟨hn1, hnm⟩, hm1, _⟩
      have hmul : n * m ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hnm
      refine ⟨⟨hn1, (Nat.le_mul_of_pos_right n (by omega)).trans hmul⟩, hm1,
        (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [Nat.mul_comm] using hmul)⟩
  exact Finset.sum_comm' hswap

/-- Every backward prime sample remains inside the physical window. -/
theorem div_sample_mem_Icc {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1)
    {m : ℕ} (hm : m ∈ Finset.Icc 1 ⌊θ / a⌋₊) : θ / m ∈ Icc a 1 := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  have hmle : (m : ℝ) ≤ θ / a :=
    (Nat.le_floor_iff (by positivity : 0 ≤ θ / a)).mp (Finset.mem_Icc.mp hm).2
  exact ⟨(le_div_iff₀ hm0).mpr (by nlinarith [(le_div_iff₀ ha).mp hmle]),
    (div_le_one hm0).mpr (hθ.2.trans hm1)⟩

/-- The angular adjoint applied to the actual window is its log-weighted sum. -/
theorem primeAdjoint_window_apply {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Icc a 1)
    (G : ℝ → ℝ) :
    primeAdjoint a (window a G) θ
      = a / θ * ∑ r ∈ Finset.Icc 1 ⌊θ / a⌋₊,
          Real.log r * G (r * a / θ) := by
  have hθ0 : 0 < θ := ha.trans_le hθ.1
  rw [primeAdjoint, indicator_of_mem hθ]
  set N := ⌊θ / a⌋₊ with hN
  calc
    _ = a / θ * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / m),
        Λ m * G (((n * m : ℕ) : ℝ) * a / θ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
      rw [window, indicator_of_mem (div_sample_mem_Icc ha hθ hm), eimage]
      have hden : (θ / m) / a = (θ / a) / m := by ring
      rw [hden, Nat.floor_div_natCast]
      have he : Λ m / m * (a / (θ / m)) = a / θ * Λ m := by field_simp
      rw [← mul_assoc, he, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (n : ℝ) * a / (θ / m) = ((n * m : ℕ) : ℝ) * a / θ by
        push_cast; field_simp]
      ring
    _ = a / θ * ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / n),
        Λ m * G (((m * n : ℕ) : ℝ) * a / θ) := by
      congr 1
      simpa only [Nat.mul_comm] using
        sum_mul_triangle_comm N (fun m n => Λ m * G (((n * m : ℕ) : ℝ) * a / θ))
    _ = a / θ * ∑ r ∈ Finset.Icc 1 N, (∑ m ∈ r.divisors, Λ m) * G (r * a / θ) := by
      rw [Cvs.Xi.MobiusReconstruction.sum_sigma_mul N (fun r => G (r * a / θ)) (fun m => Λ m)]
    _ = _ := by simp only [ArithmeticFunction.vonMangoldt_sum]

/-- The actual prime adjoint and forward prime dilation agree through the E-window. -/
theorem primeAdjoint_window {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) :
    primeAdjoint a (window a G) = window a (primeWindow a G) := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · rw [primeAdjoint_window_apply ha hθ, window, indicator_of_mem hθ,
      Cvs.Xi.MangoldtDilationEWindow.eimage_primeWindow ha hθ]
  · simp only [primeAdjoint, window, indicator_of_notMem hθ]

/-- Both actual prime intertwiners are the centered-log anticommutator. -/
theorem primeAdjoint_window_eq_anticommutator {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) :
    primeAdjoint a (window a G)
      = fun θ => centeredLog a θ * window a G θ
        + window a (fun u => centeredLog a u * G u) θ := by
  rw [primeAdjoint_window ha, Cvs.Xi.MangoldtDilationEWindow.window_primeWindow_eq_anticommutator ha]

/-- One forward prime branch, including the upper support gate. -/
def forwardBranch (a : ℝ) (n : ℕ) (G : ℝ → ℝ) : ℝ → ℝ :=
  (Icc a (1 / (n : ℝ))).indicator (fun θ => Λ n * G (n * θ))

/-- The Jacobian-weighted backward prime branch. -/
def adjointBranch (a : ℝ) (n : ℕ) (F : ℝ → ℝ) : ℝ → ℝ :=
  (Icc ((n : ℝ) * a) 1).indicator (fun θ => Λ n / n * F (θ / n))

/-- A floor-cut sum may be taken over a fixed larger cap with its exact gate. -/
theorem sum_floor_cut {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (F : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, F n) =
      ∑ n ∈ Finset.Icc 1 ⌊T⌋₊, if (n : ℝ) ≤ t then F n else 0 := by
  have he : Finset.Icc 1 ⌊t⌋₊ =
      (Finset.Icc 1 ⌊T⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ t) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hn
      exact ⟨⟨hn.1, hn.2.trans (Nat.floor_mono htT)⟩, (Nat.le_floor_iff ht).mp hn.2⟩
    · intro hn
      exact ⟨hn.1.1, (Nat.le_floor_iff ht).mpr hn.2⟩
  rw [he, Finset.sum_filter]

/-- Forward prime dilation is a finite sum over the fixed window cap. -/
theorem primeWindow_eq_sum_forward {a : ℝ} (ha : 0 < a) (G : ℝ → ℝ) :
    primeWindow a G = fun θ =>
      ∑ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, forwardBranch a n G θ := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · have hθ0 : 0 < θ := ha.trans_le hθ.1
    rw [primeWindow, indicator_of_mem hθ,
      sum_floor_cut (one_div_pos.mpr hθ0).le (one_div_le_one_div_of_le ha hθ.1)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    have he : (n : ℝ) ≤ 1 / θ ↔ θ ∈ Icc a (1 / (n : ℝ)) := by
      simp only [mem_Icc, hθ.1, true_and]
      rw [le_div_iff₀ hθ0, le_div_iff₀ hn0, mul_comm]
    by_cases h : (n : ℝ) ≤ 1 / θ
    · simp only [ite_eq_left h, forwardBranch, indicator_of_mem (he.mp h)]
    · simp only [ite_eq_right h, forwardBranch, indicator_of_notMem (fun hm => h (he.mpr hm))]
  · rw [primeWindow, indicator_of_notMem hθ]
    symm
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hupper : 1 / (n : ℝ) ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn1
    exact indicator_of_notMem (fun hm : θ ∈ Icc a (1 / (n : ℝ)) =>
      hθ ⟨hm.1, hm.2.trans hupper⟩) _

/-- The prime adjoint has the same fixed finite cap. -/
theorem primeAdjoint_eq_sum_adjoint {a : ℝ} (ha : 0 < a) (F : ℝ → ℝ) :
    primeAdjoint a F = fun θ =>
      ∑ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, adjointBranch a n F θ := by
  funext θ
  by_cases hθ : θ ∈ Icc a 1
  · have hθ0 : 0 < θ := ha.trans_le hθ.1
    rw [primeAdjoint, indicator_of_mem hθ,
      sum_floor_cut (div_pos hθ0 ha).le (div_le_div_of_nonneg_right hθ.2 ha.le)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have he : (n : ℝ) ≤ θ / a ↔ θ ∈ Icc ((n : ℝ) * a) 1 := by
      simp only [mem_Icc, hθ.2, and_true]
      exact le_div_iff₀ ha
    by_cases h : (n : ℝ) ≤ θ / a
    · simp only [ite_eq_left h, adjointBranch, indicator_of_mem (he.mp h)]
    · simp only [ite_eq_right h, adjointBranch, indicator_of_notMem (fun hm => h (he.mpr hm))]
  · rw [primeAdjoint, indicator_of_notMem hθ]
    symm
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hna : a ≤ (n : ℝ) * a := by nlinarith
    exact indicator_of_notMem (fun hm : θ ∈ Icc ((n : ℝ) * a) 1 =>
      hθ ⟨hna.trans hm.1, hm.2⟩) _

/-- Nonzero physical dilations preserve square integrability. -/
theorem memLp_comp_mul {G : ℝ → ℝ} (hG : MemLp G 2 volume) {r : ℝ} (hr : r ≠ 0) :
    MemLp (fun θ => G (r * θ)) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun θ => G (r * θ)) volume := by
    simpa only [smul_eq_mul, Function.comp_def] using
      hG.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_smul volume hr)
  exact (memLp_two_iff_integrable_sq hmeas).mpr (hG.integrable_sq.comp_mul_left' hr)

/-- Nonzero backward physical dilations preserve square integrability. -/
theorem memLp_comp_div {F : ℝ → ℝ} (hF : MemLp F 2 volume) {r : ℝ} (hr : r ≠ 0) :
    MemLp (fun θ => F (θ / r)) 2 volume := by
  simpa only [div_eq_mul_inv, mul_comm] using memLp_comp_mul hF (inv_ne_zero hr)

/-- Every forward prime branch is square integrable on square-integrable profiles. -/
theorem memLp_forwardBranch {a : ℝ} {n : ℕ} (hn : 1 ≤ n)
    {G : ℝ → ℝ} (hG : MemLp G 2 volume) : MemLp (forwardBranch a n G) 2 volume := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact ((memLp_comp_mul hG hn0).const_mul (Λ n)).indicator measurableSet_Icc.nullMeasurableSet

/-- Every backward prime branch is square integrable on square-integrable profiles. -/
theorem memLp_adjointBranch {a : ℝ} {n : ℕ} (hn : 1 ≤ n)
    {F : ℝ → ℝ} (hF : MemLp F 2 volume) : MemLp (adjointBranch a n F) 2 volume := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact ((memLp_comp_div hF hn0).const_mul (Λ n / n)).indicator measurableSet_Icc.nullMeasurableSet

/-- A prime branch has exactly the physical Jacobian adjoint. -/
theorem integral_forwardBranch_mul {a : ℝ} {n : ℕ} (hn : 1 ≤ n) (G F : ℝ → ℝ) :
    ∫ θ, forwardBranch a n G θ * F θ = ∫ θ, G θ * adjointBranch a n F θ := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : (fun θ => forwardBranch a n G θ * F θ) =
      fun θ => (n : ℝ) * (G (n * θ) * adjointBranch a n F (n * θ)) := by
    funext θ
    have hg : (n : ℝ) * θ ∈ Icc ((n : ℝ) * a) 1 ↔ θ ∈ Icc a (1 / (n : ℝ)) := by
      simp only [mem_Icc]
      constructor
      · intro h
        exact ⟨by nlinarith [h.1], (le_div_iff₀ hn0).mpr (by simpa [mul_comm] using h.2)⟩
      · intro h
        exact ⟨mul_le_mul_of_nonneg_left h.1 hn0.le,
          by simpa [mul_comm] using (le_div_iff₀ hn0).mp h.2⟩
    by_cases hθ : θ ∈ Icc a (1 / (n : ℝ))
    · simp only [forwardBranch, adjointBranch, indicator_of_mem hθ, indicator_of_mem (hg.mpr hθ)]
      rw [mul_div_cancel_left₀ _ hn0.ne']
      field_simp
    · simp only [forwardBranch, adjointBranch, indicator_of_notMem hθ,
        indicator_of_notMem (fun h => hθ (hg.mp h)), zero_mul, mul_zero]
  rw [he, integral_const_mul]
  change (n : ℝ) * ∫ θ, (fun u => G u * adjointBranch a n F u) ((n : ℝ) * θ) = _
  have hi := Measure.integral_comp_mul_left (fun u => G u * adjointBranch a n F u) (n : ℝ)
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hn0)] at hi
  rw [hi, ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]

/-- Actual finite prime dilation and its adjoint are adjoint in physical Lebesgue measure. -/
theorem integral_primeWindow_mul {a : ℝ} (ha : 0 < a) {G F : ℝ → ℝ}
    (hG : MemLp G 2 volume) (hF : MemLp F 2 volume) :
    ∫ θ, primeWindow a G θ * F θ = ∫ θ, G θ * primeAdjoint a F θ := by
  rw [primeWindow_eq_sum_forward ha, primeAdjoint_eq_sum_adjoint ha]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum (f := fun n θ => forwardBranch a n G θ * F θ) _ (fun n hn =>
      (memLp_forwardBranch (Finset.mem_Icc.mp hn).1 hG).integrable_mul hF),
    integral_finsetSum (f := fun n θ => G θ * adjointBranch a n F θ) _ (fun n hn =>
      hG.integrable_mul (memLp_adjointBranch (Finset.mem_Icc.mp hn).1 hF))]
  exact Finset.sum_congr rfl fun n hn => integral_forwardBranch_mul (Finset.mem_Icc.mp hn).1 G F

/-- A supported forward branch is exactly the angular dilate pairing. -/
theorem integral_mul_forwardBranch {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    (F G : ℝ → ℝ) (hF : ∀ θ ∉ Icc a 1, F θ = 0) (hG : ∀ θ ∉ Icc a 1, G θ = 0) :
    ∫ θ, F θ * forwardBranch a n G θ = Λ n * Cvs.WeilForm.ThetaSpaceParseval.dil F G n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : (fun θ => F θ * forwardBranch a n G θ) =
      fun θ => Λ n * (F θ * G (n * θ)) := by
    funext θ
    by_cases hθ : θ ∈ Icc a (1 / (n : ℝ))
    · simp only [forwardBranch, indicator_of_mem hθ]
      ring
    · rw [forwardBranch, indicator_of_notMem hθ, mul_zero]
      by_cases hw : θ ∈ Icc a 1
      · have hup : 1 / (n : ℝ) < θ := lt_of_not_ge (fun ht => hθ ⟨hw.1, ht⟩)
        have hg0 : G ((n : ℝ) * θ) = 0 := hG _ (fun hm =>
          not_le_of_gt ((div_lt_iff₀ hn0).mp hup) (by simpa [mul_comm] using hm.2))
        simp only [hg0, mul_zero]
      · simp only [hF _ hw, zero_mul, mul_zero]
  have hg : (fun θ => F θ * G (n * θ)) =
      (Ioi (0 : ℝ)).indicator (fun θ => F θ * G (n * θ)) := by
    funext θ
    by_cases hθ : 0 < θ
    · rw [indicator_of_mem (show θ ∈ Ioi (0 : ℝ) from hθ)]
    · rw [indicator_of_notMem (show θ ∉ Ioi (0 : ℝ) from hθ),
        hF θ (fun hw => hθ (ha.trans_le hw.1)), zero_mul]
  rw [he, integral_const_mul]
  congr 1
  rw [hg, integral_indicator measurableSet_Ioi]
  rfl

/-- The finite prime-window pairing is the complete finite angular Mangoldt sum. -/
theorem integral_mul_primeWindow_eq {a : ℝ} (ha : 0 < a) {F G : ℝ → ℝ}
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hFsupp : ∀ θ ∉ Icc a 1, F θ = 0) (hGsupp : ∀ θ ∉ Icc a 1, G θ = 0) :
    ∫ θ, F θ * primeWindow a G θ
      = ∑ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, Λ n * Cvs.WeilForm.ThetaSpaceParseval.dil F G n := by
  rw [primeWindow_eq_sum_forward ha]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum (f := fun n θ => F θ * forwardBranch a n G θ) _
    (fun n hn => hF.integrable_mul (memLp_forwardBranch (Finset.mem_Icc.mp hn).1 hG))]
  exact Finset.sum_congr rfl fun n hn =>
    integral_mul_forwardBranch ha (Finset.mem_Icc.mp hn).1 F G hFsupp hGsupp

/-- The actual Weil prime channel is the two physical prime-window pairings. -/
theorem primeθ_eq_primeWindow_pairing {a : ℝ} (ha : 0 < a) {F G : ℝ → ℝ}
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hFsupp : ∀ θ ∉ Icc a 1, F θ = 0) (hGsupp : ∀ θ ∉ Icc a 1, G θ = 0) :
    Cvs.L2a.WindowFormTailLimit.primeθ F G = (∫ θ, F θ * primeWindow a G θ)
      + ∫ θ, primeWindow a F θ * G θ := by
  rw [integral_mul_primeWindow_eq ha hF hG hFsupp hGsupp,
    show (∫ θ, primeWindow a F θ * G θ) = ∫ θ, G θ * primeWindow a F θ by
      apply integral_congr_ae; exact ae_of_all _ fun θ => mul_comm _ _,
    integral_mul_primeWindow_eq ha hG hF hGsupp hFsupp,
    ← Finset.sum_add_distrib]
  unfold Cvs.L2a.WindowFormTailLimit.primeθ
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊1 / a⌋₊) ?_]
  · exact Finset.sum_congr rfl fun n _ => by ring
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have hcap : ⌊1 / a⌋₊ < n := by
        have hnot := hn
        simp only [Finset.mem_Icc, not_and] at hnot
        exact lt_of_not_ge (hnot hn0)
      have hcut : (1 : ℝ) / a < n := Nat.lt_of_floor_lt hcap
      rw [Cvs.L2a.WindowFormTailLimit.dil_eq_zero_of_support ha hFsupp hGsupp hcut,
        Cvs.L2a.WindowFormTailLimit.dil_eq_zero_of_support ha hGsupp hFsupp hcut, add_zero, mul_zero]

end Cvs.Xi.AngularPrimeAdjointEWindow
