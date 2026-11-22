import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BetaProfilePoissonTail
import Cvs.L2a.FullTailBilinearChannels
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPolarisation
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PositionTailPrimePairs
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TruncationRemainderPrimitive
import Cvs.L2a.WindowFormDeepSpan
import Cvs.L2a.WindowFormTailLimit
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionEdge
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# E1's prime channel: `PrimeTailLimit c G` for every `C²` profile and every `c > 0`

`Λ ∗ 1 = log` turns `Σ Λ(n)(F_Q − F_Y)(nθ)` into `Σ_{Y<qθ≤Q} log q Φ(qθ)`, which Abel summation writes as
`log(Y/θ)(F_Q − F_Y)(θ) + ∫_Y^Q (F_Q − F_X)(θ) dX/X`; the `L²` rate of `F_X → F_∞` bounds both couplings by
`B_G √K1b (6 log N + 8) N^{−1/4}`, and the remainder primitive of Cvs.L2a.TruncationRemainderPrimitive sends the window coupling to `0`.
-/

noncomputable section

namespace Cvs.L2a.PrimeTailLimitProfiles

open Real Set Filter Topology MeasureTheory
open scoped Interval ArithmeticFunction
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.WindowFormTailLimit (tailRem primeθ PrimeTailLimit)
open Cvs.WeilForm.ThetaSpaceParseval (dil)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.L2a.AngularProlateTailPositive (psi)

/-! ### The truncations as cut sums -/

/-- `F_X(θ) = Σ_{q ≤ M, qθ ≤ X} Φ(qθ)` for `θ > 1` and `⌊X⌋ ≤ M`. -/
theorem posTail_eq_sum_ite (Φ : ℝ → ℝ) {X θ : ℝ} {M : ℕ} (hθ : 1 < θ) (hM : ⌊X⌋₊ ≤ M) :
    posTail Φ X θ = ∑ q ∈ Finset.Icc 1 M, if (q : ℝ) * θ ≤ X then Φ (q * θ) else 0 := by
  rw [Cvs.L2a.TruncationRemainderPrimitive.posTail_eq_sum_of_le Φ hM θ]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  by_cases h : (q : ℝ) * θ ≤ X
  · rw [ite_eq_left h, indicator_of_mem]
    exact ⟨hθ, by rw [le_div_iff₀ hq0]; linarith⟩
  · rw [ite_eq_right h, indicator_of_notMem]
    intro h'
    have := h'.2
    rw [le_div_iff₀ hq0] at this
    exact h (by linarith)

/-- The cut sum `Σ_{q ≤ ⌊Q⌋, X < qθ ≤ Q} Φ(qθ)`. -/
def cutSum (Φ : ℝ → ℝ) (Q X θ : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, if X < (q : ℝ) * θ ∧ (q : ℝ) * θ ≤ Q then Φ (q * θ) else 0

/-- The log-weighted cut sum `Σ_{q ≤ ⌊Q⌋, Y < qθ ≤ Q} log q · Φ(qθ)`. -/
def logCutSum (Φ : ℝ → ℝ) (Q Y θ : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, if Y < (q : ℝ) * θ ∧ (q : ℝ) * θ ≤ Q then Real.log q * Φ (q * θ) else 0

theorem ite_sub_ite_eq {X Y t : ℝ} (hXY : X ≤ Y) (a : ℝ) :
    ((if t ≤ Y then a else 0) - if t ≤ X then a else 0) = if X < t ∧ t ≤ Y then a else 0 := by
  by_cases h1 : t ≤ X
  · rw [ite_eq_left (h1.trans hXY), ite_eq_left h1, ite_eq_right (fun h => not_lt.mpr h1 h.1), sub_self]
  · by_cases h2 : t ≤ Y
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left ⟨not_le.mp h1, h2⟩, sub_zero]
    · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (fun h => h2 h.2), sub_zero]

/-- `F_Q(θ) − F_X(θ)` is the cut sum, for `θ > 1` and `X ≤ Q`. -/
theorem cutSum_eq (Φ : ℝ → ℝ) {Q X θ : ℝ} (hθ : 1 < θ) (hXQ : X ≤ Q) :
    cutSum Φ Q X θ = posTail Φ Q θ - posTail Φ X θ := by
  rw [posTail_eq_sum_ite Φ hθ le_rfl, posTail_eq_sum_ite Φ hθ (Nat.floor_mono hXQ), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => (ite_sub_ite_eq hXQ _).symm

/-! ### `Λ ∗ 1 = log` on the truncations -/

/-- **The regrouping**: `Σ_{n ≤ M} Λ(n) F_X(nθ) = Σ_{q ≤ M, qθ ≤ X} log q · Φ(qθ)` for `θ > 1`, `⌊X⌋ ≤ M`. -/
theorem sum_vonMangoldt_posTail (Φ : ℝ → ℝ) {X θ : ℝ} {M : ℕ} (hθ : 1 < θ) (hM : ⌊X⌋₊ ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, (Λ n : ℝ) * posTail Φ X (n * θ)
      = ∑ q ∈ Finset.Icc 1 M, Real.log q * (if (q : ℝ) * θ ≤ X then Φ (q * θ) else 0) := by
  set f : ℕ → ℝ := fun q => if (q : ℝ) * θ ≤ X then Φ (q * θ) else 0 with hf
  have hXM : X < M + 1 := by
    rcases le_or_gt 0 X with hX | hX
    · have h1 := Nat.lt_floor_add_one X
      have h2 : (⌊X⌋₊ : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    · have : (0 : ℝ) ≤ M := M.cast_nonneg
      linarith
  have h1 : ∀ n ∈ Finset.Icc 1 M, posTail Φ X (n * θ)
      = ∑ m ∈ (Finset.Icc 1 M).filter (fun m => n * m ≤ M), f (n * m) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnθ : 1 < (n : ℝ) * θ := by nlinarith
    rw [posTail_eq_sum_ite Φ hnθ hM, Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun m _ => ?_
      simp only [hf]
      push_cast
      rw [show (m : ℝ) * (n * θ) = n * m * θ by ring]
    · intro m _ hm
      by_contra hnm
      apply hm
      simp only [hf]
      rw [ite_eq_right]
      intro hle
      have : (M : ℝ) + 1 ≤ ((n * m : ℕ) : ℝ) := by exact_mod_cast (not_le.mp hnm)
      have hθ1 : ((n * m : ℕ) : ℝ) ≤ ((n * m : ℕ) : ℝ) * θ := by
        have : (0 : ℝ) ≤ ((n * m : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
  rw [Finset.sum_congr rfl fun n hn => by rw [h1 n hn] ]
  have h2 : ∑ n ∈ Finset.Icc 1 M, (Λ n : ℝ) * ∑ m ∈ (Finset.Icc 1 M).filter (fun m => n * m ≤ M), f (n * m)
      = ∑ k ∈ (Finset.Icc 1 M).filter IsPrimePow,
          (Λ k : ℝ) * ∑ m ∈ (Finset.Icc 1 M).filter (fun m => k * m ≤ M), f (k * m) := by
    rw [Finset.sum_filter_of_ne]
    intro k _ hk
    by_contra h
    exact hk (by rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h, zero_mul])
  rw [h2, Cvs.L2a.PositionTailPrimePairs.sum_vonMangoldt_regroup (fun k hk => (Finset.mem_filter.mp hk).2)
    (fun k hk hkM => Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk.one_lt.le, hkM⟩, hk⟩) f]

/-- **`Λ ∗ 1 = log` on a difference of truncations**: `Σ_{n ≤ ⌊X⌋} Λ(n)(F_X − F_Y)(nθ)` is the log-weighted cut
sum, for `θ > 1` and `Y ≤ X`. -/
theorem sum_vonMangoldt_posTail_sub (Φ : ℝ → ℝ) {X Y θ : ℝ} (hθ : 1 < θ) (hYX : Y ≤ X) :
    ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (Λ n : ℝ) * (posTail Φ X (n * θ) - posTail Φ Y (n * θ)) = logCutSum Φ X Y θ := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, sum_vonMangoldt_posTail Φ hθ le_rfl,
    sum_vonMangoldt_posTail Φ hθ (Nat.floor_mono hYX), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_sub, ite_sub_ite_eq hYX]
  split_ifs <;> simp

/-! ### Abel summation in the cut: `log q = log(Y/θ) + ∫_Y^{qθ} dX/X` -/

theorem intervalIntegrable_cut_div (φ t R : ℝ) {Y Z : ℝ} (hY : 0 < Y) (hYZ : Y ≤ Z) :
    IntervalIntegrable (fun X : ℝ => (if X < t ∧ t ≤ R then φ else 0) / X) volume Y Z := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => |φ| / Y) intervalIntegrable_const ?_ ?_
  · exact ((Measurable.ite ((measurableSet_Iio (a := t)).inter (MeasurableSet.const (t ≤ R))) measurable_const
      measurable_const).div measurable_id).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun X hX => ?_)
    rw [uIoc_of_le hYZ] at hX
    have hX0 : 0 < X := hY.trans hX.1
    show ‖(if X < t ∧ t ≤ R then φ else 0) / X‖ ≤ |φ| / Y
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hX0]
    have h1 : |if X < t ∧ t ≤ R then φ else 0| ≤ |φ| := by split_ifs <;> simp
    calc |if X < t ∧ t ≤ R then φ else 0| / X ≤ |φ| / X := div_le_div_of_nonneg_right h1 hX0.le
      _ ≤ |φ| / Y := div_le_div_of_nonneg_left (abs_nonneg _) hY hX.1.le

/-- One mode of the Abel identity: `∫_Y^Q 1[X < t ≤ Q] φ dX/X = 1[Y < t ≤ Q] φ log(t/Y)`. -/
theorem integral_cut_div (φ t : ℝ) {Q Y : ℝ} (hY : 0 < Y) (hYQ : Y ≤ Q) :
    ∫ X in Y..Q, (if X < t ∧ t ≤ Q then φ else 0) / X
      = if Y < t ∧ t ≤ Q then φ * Real.log (t / Y) else 0 := by
  by_cases h : Y < t ∧ t ≤ Q
  · rw [ite_eq_left h]
    have ht : 0 < t := hY.trans h.1
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cut_div φ t Q hY h.1.le) (intervalIntegrable_cut_div φ t Q ht h.2)]
    have h1 : ∫ X in Y..t, (if X < t ∧ t ≤ Q then φ else 0) / X = ∫ X in Y..t, φ * X⁻¹ := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton t)] with X hXt hX
      rw [uIoc_of_le h.1.le] at hX
      have hlt : X < t := lt_of_le_of_ne hX.2 hXt
      rw [ite_eq_left ⟨hlt, h.2⟩, div_eq_mul_inv]
    have h2 : ∫ X in t..Q, (if X < t ∧ t ≤ Q then φ else 0) / X = 0 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun X hX => ?_)]
      · simp
      rw [uIoc_of_le h.2] at hX
      rw [ite_eq_right (fun h' => absurd h'.1 (not_lt.mpr hX.1.le)), zero_div]
    rw [h1, h2, add_zero, intervalIntegral.integral_const_mul, integral_inv_of_pos hY ht]
  · rw [ite_eq_right h]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun X hX => ?_]
    · simp
    rw [uIcc_of_le hYQ] at hX
    rw [ite_eq_right (fun h' => h ⟨lt_of_le_of_lt hX.1 h'.1, h'.2⟩), zero_div]

/-- **Abel summation in the cut**: `Σ_{Y<qθ≤Q} log q · Φ(qθ) = log(Y/θ) · cut(Y) + ∫_Y^Q cut(X) dX/X`, where
`cut(X) = Σ_{X<qθ≤Q} Φ(qθ)`, for `θ, Y > 0` and `Y ≤ Q`. -/
theorem logCutSum_eq (Φ : ℝ → ℝ) {Q Y θ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hYQ : Y ≤ Q) :
    logCutSum Φ Q Y θ = Real.log (Y / θ) * cutSum Φ Q Y θ + ∫ X in Y..Q, cutSum Φ Q X θ / X := by
  have hint : ∫ X in Y..Q, cutSum Φ Q X θ / X
      = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∫ X in Y..Q,
          (if X < (q : ℝ) * θ ∧ (q : ℝ) * θ ≤ Q then Φ (q * θ) else 0) / X := by
    simp only [cutSum, Finset.sum_div]
    exact intervalIntegral.integral_finsetSum
      (f := fun (q : ℕ) (X : ℝ) => (if X < (q : ℝ) * θ ∧ (q : ℝ) * θ ≤ Q then Φ (q * θ) else 0) / X)
      fun q _ => intervalIntegrable_cut_div _ _ _ hY hYQ
  rw [hint, cutSum, logCutSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [integral_cut_div _ _ hY hYQ]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
  split_ifs with h
  · rw [Real.log_div (by positivity) hθ.ne', Real.log_div (by positivity) hY.ne',
      Real.log_mul hq0.ne' hθ.ne']
    ring
  · simp

/-- The cut sum is jointly measurable in `(θ, X)`. -/
theorem measurable_cutSum {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (Q : ℝ) :
    Measurable fun p : ℝ × ℝ => cutSum Φ Q p.2 p.1 := by
  simp only [cutSum]
  refine Finset.measurable_sum _ fun q _ => Measurable.ite ?_
    (hΦ.measurable.comp (measurable_const.mul measurable_fst)) measurable_const
  exact (measurableSet_lt measurable_snd (measurable_const.mul measurable_fst)).inter
    (measurableSet_le (measurable_const.mul measurable_fst) measurable_const)

theorem measurable_logCutSum {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (Q Y : ℝ) : Measurable (logCutSum Φ Q Y) := by
  unfold logCutSum
  refine Finset.measurable_sum _ fun q _ => Measurable.ite ?_
    (measurable_const.mul (hΦ.measurable.comp (measurable_const.mul measurable_id))) measurable_const
  exact (measurableSet_lt measurable_const (measurable_const.mul measurable_id)).inter
    (measurableSet_le (measurable_const.mul measurable_id) measurable_const)

/-! ### Bounds for `Φ = psi c G` -/

section Psi

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

theorem abs_posTail_le_BG (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (X θ : ℝ) :
    |posTail (psi c G) X θ|
      ≤ Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) := by
  have hB := Cvs.L2a.FullTailConvergence.BG_nonneg hc (G 1 + G (-1)) (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  rcases le_or_gt θ 1 with h | h
  · rw [Cvs.L2a.PositionTruncatedTail.posTail_zero _ X h, abs_zero]; exact hB
  · exact (Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc X (by linarith)).trans (div_le_self hB h.le)

theorem abs_tailRem_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (X θ : ℝ) :
    |tailRem (psi c G) X θ|
      ≤ 2 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) := by
  have h1 := Cvs.L2a.WindowFormTailLimit.abs_fullTail_le_BG hg hg₁ hg₂c hc θ
  have h2 := abs_posTail_le_BG hg hg₁ hg₂c hc X θ
  have := abs_sub (fullTail (psi c G) θ) (posTail (psi c G) X θ)
  unfold tailRem
  linarith

theorem measurable_tailRem (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (X : ℝ) : Measurable (tailRem (psi c G) X) :=
  (Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc).sub
    (Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c X)

theorem abs_posTail_sub_posTail_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) (Q X : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    |posTail (psi c G) Q θ - posTail (psi c G) X θ|
      ≤ 2 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) / θ := by
  have h1 := Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc Q hθ
  have h2 := Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc X hθ
  have := abs_sub (posTail (psi c G) Q θ) (posTail (psi c G) X θ)
  rw [mul_div_assoc]
  linarith

theorem abs_cutSum_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {Q X θ : ℝ} (hθ : 1 < θ) (hXQ : X ≤ Q) :
    |cutSum (psi c G) Q X θ|
      ≤ 2 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) / θ := by
  rw [cutSum_eq _ hθ hXQ]
  exact abs_posTail_sub_posTail_le hg hg₁ hg₂c hc Q X (by linarith)

/-- `|∫_Y^Q cut(X) dX/X| ≤ (2B_G/θ) log(Q/Y)`. -/
theorem abs_integral_cutSum_div_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {Q Y θ : ℝ} (hθ : 1 < θ) (hY : 0 < Y) (hYQ : Y ≤ Q) :
    |∫ X in Y..Q, cutSum (psi c G) Q X θ / X|
      ≤ 2 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) / θ
        * Real.log (Q / Y) := by
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hQ : 0 < Q := hY.trans_le hYQ
  have hint : IntervalIntegrable (fun X : ℝ => 2 * B / θ * X⁻¹) volume Y Q :=
    ((continuousOn_inv₀.mono fun X hX => by
      rw [uIcc_of_le hYQ] at hX; exact (hY.trans_le hX.1).ne').intervalIntegrable).const_mul _
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le hYQ (ae_of_all _ fun X hX => ?_) hint).trans
    (le_of_eq ?_)
  · have hX0 : 0 < X := hY.trans hX.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hX0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (abs_cutSum_le hg hg₁ hg₂c hc hθ hX.2) (inv_nonneg.mpr hX0.le)
  · rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hY hQ]

/-- **The `L`-multiplier is `O(log N/θ)`**: `|Σ_{qθ ≤ N} log q · Φ(qθ)| ≤ 4B_G log N/θ` for `θ > 1`, `N ≥ 1`. -/
theorem abs_logCutSum_one_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {N θ : ℝ} (hN : 1 ≤ N) (hθ : 1 < θ) :
    |logCutSum (psi c G) N 1 θ|
      ≤ 4 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
        * Real.log N / θ := by
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  have hθ0 : 0 < θ := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  rcases lt_or_ge N θ with hNθ | hθN
  · have h0 : logCutSum (psi c G) N 1 θ = 0 := by
      refine Finset.sum_eq_zero fun q hq => ite_eq_right fun h => ?_
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
      nlinarith [h.2]
    rw [h0, abs_zero]; positivity
  rw [logCutSum_eq _ hθ0 one_pos hN]
  have h1 := abs_cutSum_le hg hg₁ hg₂c hc hθ hN
  have h2 := abs_integral_cutSum_div_le hg hg₁ hg₂c hc hθ one_pos hN
  rw [div_one] at h2
  have hl : |Real.log (1 / θ)| ≤ Real.log N := by
    rw [one_div, Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg hθ.le)]
    exact Real.log_le_log hθ0 hθN
  have h3 : |Real.log (1 / θ) * cutSum (psi c G) N 1 θ| ≤ Real.log N * (2 * B / θ) := by
    rw [abs_mul]; exact mul_le_mul hl h1 (abs_nonneg _) hlogN
  calc |Real.log (1 / θ) * cutSum (psi c G) N 1 θ + ∫ X in (1 : ℝ)..N, cutSum (psi c G) N X θ / X|
      ≤ Real.log N * (2 * B / θ) + 2 * B / θ * Real.log N := (abs_add_le _ _).trans (add_le_add h3 h2)
    _ = 4 * B * Real.log N / θ := by ring

end Psi

/-! ### The `L²` rate in quarter powers -/

/-- `√(K/√X) = √K · X^{−1/4}`. -/
theorem sqrt_div_sqrt_eq (K : ℝ) {X : ℝ} (hX : 0 < X) : √(K / √X) = √K * X ^ (-(1 / 4 : ℝ)) := by
  rw [Real.sqrt_div' K (Real.sqrt_nonneg X), Real.rpow_neg hX.le, div_eq_mul_inv]
  congr 2
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le]
  norm_num

theorem K1b_nonneg {c : ℝ} (hc : 0 < c) (A C1 : ℝ) : 0 ≤ Cvs.L2a.FullTailConvergence.K1b c A C1 := by
  unfold Cvs.L2a.FullTailConvergence.K1b
  have h1 : 0 ≤ 8 * π / c := div_nonneg (by positivity) hc.le
  have h2 : 0 ≤ 16 * (1 + π) * A ^ 2 * (3 + 8 * π / c) / c ^ 2 :=
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  positivity

theorem sqrt_K1_le {c : ℝ} (hc : 0 < c) (A C1 : ℝ) {X : ℝ} (hX : 1 ≤ X) :
    √(Cvs.L2a.FullTailConvergence.K1 c A C1 X) ≤ √(Cvs.L2a.FullTailConvergence.K1b c A C1) * X ^ (-(1 / 4 : ℝ)) :=
  (Real.sqrt_le_sqrt (Cvs.L2a.FullTailConvergence.K1_le hc A C1 hX)).trans
    (le_of_eq (sqrt_div_sqrt_eq _ (by linarith)))

/-- `√(2K1(Q) + 2K1(X)) ≤ 2√K1b · X^{−1/4}` for `1 ≤ X ≤ Q`. -/
theorem sqrt_two_K1_add_le {c : ℝ} (hc : 0 < c) (A C1 : ℝ) {X Q : ℝ} (hX : 1 ≤ X) (hXQ : X ≤ Q) :
    √(2 * Cvs.L2a.FullTailConvergence.K1 c A C1 Q + 2 * Cvs.L2a.FullTailConvergence.K1 c A C1 X)
      ≤ 2 * √(Cvs.L2a.FullTailConvergence.K1b c A C1) * X ^ (-(1 / 4 : ℝ)) := by
  have hX0 : 0 < X := by linarith
  have hK := K1b_nonneg hc A C1
  have h1 := Cvs.L2a.FullTailConvergence.K1_le hc A C1 (hX.trans hXQ)
  have h2 := Cvs.L2a.FullTailConvergence.K1_le hc A C1 hX
  have h3 : Cvs.L2a.FullTailConvergence.K1b c A C1 / √Q ≤ Cvs.L2a.FullTailConvergence.K1b c A C1 / √X :=
    div_le_div_of_nonneg_left hK (Real.sqrt_pos.mpr hX0) (Real.sqrt_le_sqrt hXQ)
  calc √(2 * Cvs.L2a.FullTailConvergence.K1 c A C1 Q + 2 * Cvs.L2a.FullTailConvergence.K1 c A C1 X)
      ≤ √(4 * (Cvs.L2a.FullTailConvergence.K1b c A C1 / √X)) := Real.sqrt_le_sqrt (by linarith)
    _ = 2 * (√(Cvs.L2a.FullTailConvergence.K1b c A C1) * X ^ (-(1 / 4 : ℝ))) := by
        rw [Real.sqrt_mul (by norm_num), sqrt_div_sqrt_eq _ hX0,
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    _ = _ := by ring

/-- **Cauchy–Schwarz on `(1, ∞)`** for two functions bounded by multiples of `1/θ`. -/
theorem abs_integral_mul_le_of_le {f h : ℝ → ℝ} {K K' : ℝ} (hf : Measurable f) (hh : Measurable h)
    (hfK : ∀ θ, 0 < θ → |f θ| ≤ K / θ) (hhK : ∀ θ, 0 < θ → |h θ| ≤ K' / θ) :
    |∫ θ in Ioi 1, f θ * h θ| ≤ √(∫ θ in Ioi 1, f θ ^ 2) * √(∫ θ in Ioi 1, h θ ^ 2) :=
  Cvs.L2a.FullTailConvergence.abs_setIntegral_mul_le (Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hf hfK)
    (Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hh hhK) (Cvs.L2a.FullTailConvergence.integrableOn_mul_of_le hf hh hfK hhK)

section L2

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- `‖F_Q − F_X‖² ≤ 2K1(Q) + 2K1(X)` on `(1, ∞)`. -/
theorem integral_sq_posTail_sub_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ X) :
    ∫ θ in Ioi 1, (posTail (psi c G) Q θ - posTail (psi c G) X θ) ^ 2
      ≤ 2 * Cvs.L2a.FullTailConvergence.K1 c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) Q
        + 2 * Cvs.L2a.FullTailConvergence.K1 c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) X := by
  have hm := fun Y => Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c Y
  have hτ := Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc
  have i1 : IntegrableOn (fun θ => (posTail (psi c G) Q θ - fullTail (psi c G) θ) ^ 2) (Ioi 1) :=
    Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le ((hm Q).sub hτ)
      fun θ hθ => Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc Q hθ
  have i2 : IntegrableOn (fun θ => (posTail (psi c G) X θ - fullTail (psi c G) θ) ^ 2) (Ioi 1) :=
    Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le ((hm X).sub hτ)
      fun θ hθ => Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc X hθ
  have i0 : IntegrableOn (fun θ => (posTail (psi c G) Q θ - posTail (psi c G) X θ) ^ 2) (Ioi 1) :=
    Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le ((hm Q).sub (hm X))
      fun θ hθ => abs_posTail_sub_posTail_le hg hg₁ hg₂c hc Q X hθ
  have i3 : IntegrableOn (fun θ => 2 * (posTail (psi c G) Q θ - fullTail (psi c G) θ) ^ 2
      + 2 * (posTail (psi c G) X θ - fullTail (psi c G) θ) ^ 2) (Ioi 1) :=
    (i1.const_mul 2).add (i2.const_mul 2)
  calc ∫ θ in Ioi 1, (posTail (psi c G) Q θ - posTail (psi c G) X θ) ^ 2
      ≤ ∫ θ in Ioi 1, (2 * (posTail (psi c G) Q θ - fullTail (psi c G) θ) ^ 2
          + 2 * (posTail (psi c G) X θ - fullTail (psi c G) θ) ^ 2) :=
        setIntegral_mono_on i0 i3 measurableSet_Ioi fun θ _ => by
          nlinarith [sq_nonneg (posTail (psi c G) Q θ - fullTail (psi c G) θ
            + (posTail (psi c G) X θ - fullTail (psi c G) θ))]
    _ = (2 * ∫ θ in Ioi 1, (posTail (psi c G) Q θ - fullTail (psi c G) θ) ^ 2)
          + 2 * ∫ θ in Ioi 1, (posTail (psi c G) X θ - fullTail (psi c G) θ) ^ 2 := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        linarith [Cvs.L2a.FullTailConvergence.integral_sub_sq_le hg hg₁ hg₂c hc hQ,
          Cvs.L2a.FullTailConvergence.integral_sub_sq_le hg hg₁ hg₂c hc hX]

/-- **The `L`-term**: `|Σ_n Λ(n) ⟨r_N, F_N(n·)⟩| ≤ √K1(N) · 4B_G log N`, by `Λ ∗ 1 = log` and Cauchy–Schwarz. -/
theorem abs_tsum_dil_tailRem_posTail_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    |∑' n : ℕ, (Λ n : ℝ) * dil (tailRem (psi c G) N) (posTail (psi c G) N) n|
      ≤ √(Cvs.L2a.FullTailConvergence.K1 c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) N)
        * (4 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
          * Real.log N) := by
  set Φ := psi c G with hΦ
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  set F := posTail Φ N with hFd
  set r := tailRem Φ N with hrd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hΦc : Continuous Φ :=
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  have hF := Cvs.L2a.WindowFormTailLimit.tame_posTail_psi hg hg₁ hg₂c hc hN1
  have hrm := measurable_tailRem hg hg₁ hg₂c hc N
  have hzero : ∀ n ∉ Finset.Icc 1 N, (Λ n : ℝ) * dil r F n = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have hnN : N < n := by
      by_contra h
      exact hn (Finset.mem_Icc.mpr ⟨hn0, not_lt.mp h⟩)
    have hd : dil r F n = 0 := by
      unfold dil
      refine setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_
      rcases le_or_gt θ 1 with h | h
      · rw [hrd, Cvs.L2a.WindowFormTailLimit.tailRem_of_le_one _ _ h, zero_mul]
      · have h1 : (N : ℝ) < n := by exact_mod_cast hnN
        have h2 : (N : ℝ) < n * θ := by nlinarith
        rw [hFd, Cvs.L2a.PositionTruncatedTail.posTail_of_gt _ h2, mul_zero]
    rw [hd, mul_zero]
  rw [tsum_eq_sum hzero]
  have hint : ∀ n ∈ Finset.Icc 1 N,
      Integrable (fun θ => (Λ n : ℝ) * (r θ * F (n * θ))) (volume.restrict (Ioi 0)) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    obtain ⟨M, hM⟩ := hF.bdd
    obtain ⟨hm, _⟩ := hF.comp n
    exact (((Cvs.L2a.WindowFormTailLimit.integrable_mul_of_support hm (fun θ => hM _)
      (Cvs.L2a.WindowFormTailLimit.comp_supp hF hn0) hrm (abs_tailRem_le hg hg₁ hg₂c hc N)).congr
        (ae_of_all _ fun θ => mul_comm _ _)).integrableOn).const_mul _
  have hw : ∀ θ, 1 < θ → ∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) * F (n * θ) = logCutSum Φ N 1 θ := by
    intro θ hθ
    have h := sum_vonMangoldt_posTail_sub Φ hθ hN1
    rw [Nat.floor_natCast] at h
    rw [← h]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [Cvs.L2a.PositionTruncatedTail.posTail_of_gt Φ (show (1 : ℝ) < n * θ by nlinarith), sub_zero]
  set u : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (logCutSum Φ N 1) with hud
  have hum : Measurable u := (measurable_logCutSum hΦc _ _).indicator measurableSet_Ioi
  have hu : ∀ θ, 0 < θ → |u θ| ≤ 4 * B * Real.log N / θ := by
    intro θ hθ
    by_cases h : θ ∈ Ioi (1 : ℝ)
    · rw [hud, indicator_of_mem h]; exact abs_logCutSum_one_le hg hg₁ hg₂c hc hN1 h
    · rw [hud, indicator_of_notMem h, abs_zero]
      have := Real.log_nonneg hN1
      positivity
  have hrK : ∀ θ, 0 < θ → |r θ| ≤ 2 * B / θ := fun θ hθ => by
    rw [hrd, tailRem, abs_sub_comm]
    exact Cvs.L2a.FullTailConvergence.abs_posTail_sub_le hg hg₁ hg₂c hc N hθ
  have key : ∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) * dil r F n = ∫ θ in Ioi 1, r θ * u θ := by
    calc ∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) * dil r F n
        = ∑ n ∈ Finset.Icc 1 N, ∫ θ in Ioi 0, (Λ n : ℝ) * (r θ * F (n * θ)) :=
          Finset.sum_congr rfl fun n _ => (integral_const_mul _ _).symm
      _ = ∫ θ in Ioi 0, ∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) * (r θ * F (n * θ)) :=
          (integral_finsetSum _ hint).symm
      _ = ∫ θ in Ioi 0, r θ * ∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) * F (n * θ) := by
          congr 1; funext θ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
      _ = ∫ θ in Ioi 1, r θ * ∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ) * F (n * θ) :=
          Cvs.L2a.WindowFormTailLimit.setIntegral_Ioi_zero_eq_one fun θ hθ => by
            rw [hrd, Cvs.L2a.WindowFormTailLimit.tailRem_of_le_one _ _ hθ, zero_mul]
      _ = ∫ θ in Ioi 1, r θ * u θ := setIntegral_congr_fun measurableSet_Ioi fun θ hθ => by
          simp only [hud, indicator_of_mem hθ]; rw [hw θ hθ]
  rw [key]
  refine (abs_integral_mul_le_of_le hrm hum hrK hu).trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _))
  · refine Real.sqrt_le_sqrt (le_trans (le_of_eq ?_) (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hg hg₁ hg₂c hc hN1))
    congr 1; funext θ; rw [tailRem]; ring
  · refine (Real.sqrt_le_sqrt (Cvs.L2a.FullTailConvergence.integral_sq_le_of_le hum hu)).trans (le_of_eq ?_)
    have := Real.log_nonneg hN1
    exact Real.sqrt_sq (by positivity)

end L2

/-! ### Piecewise-`C¹` tests against the dilated remainder -/

/-- `Σ Λ(n)/n²` converges: `Λ(n) ≤ log n ≤ 2√n`. -/
theorem summable_vonMangoldt_div_sq : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _))
    (fun n => ?_) ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : (Λ n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 2)
    calc (Λ n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) := this
      _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
  have e : (n : ℝ) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  have hp : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hq : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  rw [e, div_le_iff₀ (by positivity)]
  calc (Λ n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := hlog
    _ = 2 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ)) := by
        field_simp

/-- **The dilation against pieces**: for `v = Σ_j 1_{[p_j, q_j)} w_j` a.e. and `f` bounded measurable,
`⟨v, f(n·)⟩ = Σ_j ∫_{p_j}^{q_j} w_j(θ) f(nθ) dθ`. -/
theorem dil_eq_sum_pieces {ι : Type*} {v f : ℝ → ℝ} (J : Finset ι) (p q : ι → ℝ) (w : ι → ℝ → ℝ)
    (hp : ∀ j ∈ J, 0 < p j) (hpq : ∀ j ∈ J, p j ≤ q j)
    (hwc : ∀ j ∈ J, ContinuousOn (w j) (Icc (p j) (q j)))
    (hv : v =ᵐ[volume] fun θ => ∑ j ∈ J, (Ico (p j) (q j)).indicator (w j) θ)
    (hf : Measurable f) {M : ℝ} (hM : ∀ θ, |f θ| ≤ M) (n : ℕ) :
    dil v f n = ∑ j ∈ J, ∫ θ in p j..q j, w j θ * f (n * θ) := by
  have hpiece : ∀ j ∈ J, IntegrableOn (fun θ => w j θ * f (n * θ)) (Ico (p j) (q j)) := by
    intro j hj
    have hw : IntegrableOn (w j) (Icc (p j) (q j)) := (hwc j hj).integrableOn_Icc
    have h := hw.bdd_mul (f := fun θ => f (n * θ)) (c := M)
      ((hf.comp (measurable_id.const_mul (n : ℝ))).aestronglyMeasurable)
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hM _)
    have h2 : IntegrableOn (fun θ => w j θ * f (n * θ)) (Icc (p j) (q j)) :=
      h.congr (ae_of_all _ fun θ => mul_comm _ _)
    exact h2.mono_set Ico_subset_Icc_self
  have e : ∀ j θ, (Ico (p j) (q j)).indicator (w j) θ * f (n * θ)
      = (Ico (p j) (q j)).indicator (fun θ => w j θ * f (n * θ)) θ := fun j θ =>
    (indicator_mul_left _ _ (fun θ => f (n * θ))).symm
  rw [Cvs.L2a.WindowFormTailLimit.dil_congr_left hv f n]
  unfold dil
  simp_rw [Finset.sum_mul, e]
  rw [integral_finsetSum _ fun j hj => ?_]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [setIntegral_indicator measurableSet_Ico,
      inter_eq_right.mpr (fun θ (hθ : θ ∈ Ico (p j) (q j)) => (show θ ∈ Ioi (0 : ℝ) from (hp j hj).trans_le hθ.1)),
      integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le (hpq j hj)]
  · exact ((integrable_indicator_iff measurableSet_Ico).mpr (hpiece j hj)).integrableOn

/-- The mass `(|w(q)| + ∫|w′|) · 2K_T(3 + log(q/p))` of one piece against the remainder primitive. -/
def pieceMass (c : ℝ) (G G₁ G₂ w w₁ : ℝ → ℝ) (p q : ℝ) : ℝ :=
  (|w q| + ∫ u in p..q, |w₁ u|)
    * (2 * ((2 * |G 1 + G (-1)| + (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)) / c ^ 2) * (3 + Real.log (q / p)))

theorem pieceMass_nonneg {c : ℝ} (G G₁ G₂ w w₁ : ℝ → ℝ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    0 ≤ pieceMass c G G₁ G₂ w w₁ p q := by
  unfold pieceMass
  have h1 : 0 ≤ ∫ u in p..q, |w₁ u| := intervalIntegral.integral_nonneg hpq fun u _ => abs_nonneg _
  have h2 : 0 ≤ Real.log (q / p) := Real.log_nonneg ((one_le_div hp).mpr hpq)
  have h3 := Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂
  have h4 : 0 ≤ (2 * |G 1 + G (-1)| + (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)) / c ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg _)
  have h5 : (0 : ℝ) ≤ 3 + Real.log (q / p) := by linarith
  positivity

section Pieces

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- **Pieces against the dilated remainder**: `|⟨v, r_Q(n·)⟩| ≤ Σ_j mass_j/(n max(Q, n p_j))`. -/
theorem abs_dil_tailRem_pieces_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {ι : Type*} {v : ℝ → ℝ} (J : Finset ι) (p q : ι → ℝ) (w w₁ : ι → ℝ → ℝ)
    (hp : ∀ j ∈ J, 0 < p j) (hpq : ∀ j ∈ J, p j ≤ q j)
    (hwc : ∀ j ∈ J, ContinuousOn (w j) (Icc (p j) (q j)))
    (hw : ∀ j ∈ J, ∀ θ ∈ Ioo (p j) (q j), HasDerivAt (w j) (w₁ j θ) θ)
    (hw₁ : ∀ j ∈ J, IntervalIntegrable (w₁ j) volume (p j) (q j))
    (hv : v =ᵐ[volume] fun θ => ∑ j ∈ J, (Ico (p j) (q j)).indicator (w j) θ) (Q : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |dil v (tailRem (psi c G) Q) n|
      ≤ ∑ j ∈ J, pieceMass c G G₁ G₂ (w j) (w₁ j) (p j) (q j) / (n * max Q (n * p j)) := by
  rw [dil_eq_sum_pieces J p q w hp hpq hwc hv (measurable_tailRem hg hg₁ hg₂c hc Q)
    (abs_tailRem_le hg hg₁ hg₂c hc Q) n]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  refine (Cvs.L2a.TruncationRemainderPrimitive.abs_integral_mul_tailRem_psi_le hg hg₁ hg₂c hc Q hn (hp j hj) (hpq j hj)
    (hwc j hj) (hw j hj) (hw₁ j hj)).trans (le_of_eq ?_)
  unfold pieceMass
  ring

/-- **The test-function channel vanishes in the limit**: `Σ_n Λ(n) ⟨v, r_Q(n·)⟩` converges for every `Q` and
tends to `0` as `Q → ∞`, for `v` piecewise `C¹` on finitely many intervals in `(0, ∞)`. -/
theorem tendsto_tsum_dil_tailRem_pieces (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {ι : Type*} {v : ℝ → ℝ} (J : Finset ι) (p q : ι → ℝ) (w w₁ : ι → ℝ → ℝ)
    (hp : ∀ j ∈ J, 0 < p j) (hpq : ∀ j ∈ J, p j ≤ q j)
    (hwc : ∀ j ∈ J, ContinuousOn (w j) (Icc (p j) (q j)))
    (hw : ∀ j ∈ J, ∀ θ ∈ Ioo (p j) (q j), HasDerivAt (w j) (w₁ j θ) θ)
    (hw₁ : ∀ j ∈ J, IntervalIntegrable (w₁ j) volume (p j) (q j))
    (hv : v =ᵐ[volume] fun θ => ∑ j ∈ J, (Ico (p j) (q j)).indicator (w j) θ) :
    (∀ Q : ℝ, Summable fun n : ℕ => (Λ n : ℝ) * dil v (tailRem (psi c G) Q) n)
      ∧ Tendsto (fun Q : ℝ => ∑' n : ℕ, (Λ n : ℝ) * dil v (tailRem (psi c G) Q) n) atTop (𝓝 0) := by
  set D : ι → ℝ := fun j => pieceMass c G G₁ G₂ (w j) (w₁ j) (p j) (q j) with hDd
  have hD : ∀ j ∈ J, 0 ≤ D j := fun j hj => pieceMass_nonneg _ _ _ _ _ (hp j hj) (hpq j hj)
  set S : ℝ := ∑ j ∈ J, D j / p j with hSd
  have hS : 0 ≤ S := Finset.sum_nonneg fun j hj => div_nonneg (hD j hj) (hp j hj).le
  have hpt : ∀ Q : ℝ, ∀ n : ℕ, 1 ≤ n → |dil v (tailRem (psi c G) Q) n|
      ≤ ∑ j ∈ J, D j / (n * max Q (n * p j)) := fun Q n hn =>
    abs_dil_tailRem_pieces_le hg hg₁ hg₂c hc J p q w w₁ hp hpq hwc hw hw₁ hv Q hn
  have hbound : ∀ Q : ℝ, ∀ n : ℕ, ‖(Λ n : ℝ) * dil v (tailRem (psi c G) Q) n‖ ≤ (Λ n : ℝ) / (n : ℝ) ^ 2 * S := by
    intro Q n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛ]
    have h1 : ∑ j ∈ J, D j / (n * max Q (n * p j)) ≤ S / (n : ℝ) ^ 2 := by
      rw [hSd, Finset.sum_div]
      refine Finset.sum_le_sum fun j hj => ?_
      have hpj := hp j hj
      calc D j / (n * max Q (n * p j)) ≤ D j / (n * (n * p j)) :=
            div_le_div_of_nonneg_left (hD j hj) (by positivity)
              (mul_le_mul_of_nonneg_left (le_max_right _ _) hn0.le)
        _ = D j / p j / (n : ℝ) ^ 2 := by field_simp
    calc (Λ n : ℝ) * |dil v (tailRem (psi c G) Q) n| ≤ Λ n * (S / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left ((hpt Q n hn).trans h1) hΛ
      _ = (Λ n : ℝ) / (n : ℝ) ^ 2 * S := by ring
  have hsum : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ 2 * S := summable_vonMangoldt_div_sq.mul_right S
  refine ⟨fun Q => Summable.of_norm_bounded hsum (hbound Q), ?_⟩
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℝ))
    (f := fun (Q : ℝ) (n : ℕ) => (Λ n : ℝ) * dil v (tailRem (psi c G) Q) n) (g := fun _ => (0 : ℝ))
    hsum (fun n => ?_) (Eventually.of_forall fun Q n => hbound Q n)
  · simpa only [tsum_zero] using hlim
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  set C : ℝ := (Λ n : ℝ) * ∑ j ∈ J, D j / n with hCd
  refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun Q : ℝ => C / Q) atTop (𝓝 0))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛ, hCd, mul_div_assoc, Finset.sum_div]
  refine mul_le_mul_of_nonneg_left ((hpt Q n hn).trans (Finset.sum_le_sum fun j hj => ?_)) hΛ
  calc D j / (n * max Q (n * p j)) ≤ D j / (n * Q) :=
        div_le_div_of_nonneg_left (hD j hj) (by positivity) (mul_le_mul_of_nonneg_left (le_max_left _ _) hn0.le)
    _ = D j / n / Q := by rw [div_div]

end Pieces

/-! ### The window and the truncation as pieces -/

section Tests

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- **The window channel vanishes**: `Σ_n Λ(n) ⟨k_G, r_Q(n·)⟩ → 0` as `Q → ∞`, for every `a > 0`. -/
theorem tendsto_tsum_dil_window_tailRem (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {a : ℝ} (ha : 0 < a) :
    (∀ Q : ℝ, Summable fun n : ℕ => (Λ n : ℝ) * dil (window a G) (tailRem (psi c G) Q) n)
      ∧ Tendsto (fun Q : ℝ => ∑' n : ℕ, (Λ n : ℝ) * dil (window a G) (tailRem (psi c G) Q) n) atTop
        (𝓝 0) := by
  have hsub : Icc (0 : ℝ) 1 ⊆ uIcc (-1) 1 := by
    rw [uIcc_of_le (by norm_num)]; exact Icc_subset_Icc (by norm_num) le_rfl
  have hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u := fun u hu => hg u (hsub hu)
  have hG₁ : ContinuousOn G₁ (Icc 0 1) := fun u hu => (hg₁ u (hsub hu)).continuousAt.continuousWithinAt
  have hGc := Cvs.L2a.WindowFormTailLimit.continuousOn_of_hasDerivAt hG
  have hmaps : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ θ, (n : ℝ) * a ≤ θ → ∀ j ∈ Finset.Icc 1 n,
      (j : ℝ) * a / θ ∈ Icc (0 : ℝ) 1 := by
    intro n hn θ hθ j hj
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hθ0]
    exact (mul_le_mul_of_nonneg_right hjn ha.le).trans hθ
  have hpq : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, (n : ℝ) * a ≤ min ((n + 1) * a) 1 := by
    intro n hn
    refine le_min (by nlinarith) ?_
    have := (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
    rwa [le_div_iff₀ ha] at this
  have hpos : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, 0 < (n : ℝ) * a := fun n hn => by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    positivity
  have hcont : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ F : ℝ → ℝ, ContinuousOn F (Icc 0 1) →
      ContinuousOn (fun θ => ∑ j ∈ Finset.Icc 1 n, F (j * a / θ)) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) := by
    intro n hn F hF
    refine continuousOn_finsetSum _ fun j hj => hF.comp
      (continuousOn_const.div continuousOn_id fun θ hθ => (lt_of_lt_of_le (hpos n hn) hθ.1).ne')
      fun θ hθ => hmaps n hn θ hθ.1 j hj
  have hinv : ∀ n ∈ Finset.Icc 1 ⌊1 / a⌋₊, ∀ b : ℝ,
      ContinuousOn (fun θ : ℝ => b / θ) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) := fun n hn b =>
    continuousOn_const.div continuousOn_id fun θ hθ => (lt_of_lt_of_le (hpos n hn) hθ.1).ne'
  refine tendsto_tsum_dil_tailRem_pieces hg hg₁ hg₂c hc (Finset.Icc 1 ⌊1 / a⌋₊) (fun n => n * a)
    (fun n => min ((n + 1) * a) 1) (fun n θ => a / θ * ∑ j ∈ Finset.Icc 1 n, G (j * a / θ))
    (fun n θ => a * -(θ ^ 2)⁻¹ * ∑ j ∈ Finset.Icc 1 n, G (j * a / θ)
      + a / θ * ∑ j ∈ Finset.Icc 1 n, G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹))
    hpos hpq (fun n hn => (hinv n hn a).mul (hcont n hn G hGc)) (fun n hn θ hθ => ?_) (fun n hn => ?_)
    (Cvs.L2a.WindowFormTailLimit.window_ae_eq_pieces ha G)
  · have hθ0 : 0 < θ := (hpos n hn).trans hθ.1
    have hdiv : ∀ b : ℝ, HasDerivAt (fun y : ℝ => b / y) (b * -(θ ^ 2)⁻¹) θ := fun b => by
      simpa only [div_eq_mul_inv] using (hasDerivAt_inv hθ0.ne').const_mul b
    have hsum : HasDerivAt (fun y => ∑ j ∈ Finset.Icc 1 n, G (j * a / y))
        (∑ j ∈ Finset.Icc 1 n, G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹)) θ :=
      HasDerivAt.fun_sum fun j hj => (hG _ (hmaps n hn θ hθ.1.le j hj)).comp θ (hdiv ((j : ℝ) * a))
    exact (hdiv a).mul hsum
  · refine ContinuousOn.intervalIntegrable_of_Icc (hpq n hn) ?_
    have hsq : ContinuousOn (fun θ : ℝ => -(θ ^ 2)⁻¹) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) :=
      ((continuousOn_id.pow 2).inv₀ fun θ (hθ : θ ∈ Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) =>
        pow_ne_zero 2 (lt_of_lt_of_le (hpos n hn) hθ.1).ne').neg
    have h2 : ContinuousOn (fun θ : ℝ => ∑ j ∈ Finset.Icc 1 n, G₁ (j * a / θ) * ((j : ℝ) * a * -(θ ^ 2)⁻¹))
        (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) := by
      refine continuousOn_finsetSum _ fun j hj => ?_
      exact (hG₁.comp (hinv n hn ((j : ℝ) * a)) fun θ hθ => hmaps n hn θ hθ.1 j hj).mul
        (continuousOn_const.mul hsq)
    have h1 : ContinuousOn (fun θ : ℝ => a * -(θ ^ 2)⁻¹) (Icc ((n : ℝ) * a) (min ((n + 1) * a) 1)) :=
      continuousOn_const.mul hsq
    exact (h1.mul (hcont n hn G hGc)).add ((hinv n hn a).mul h2)

/-- **The truncation channel vanishes**: `Σ_n Λ(n) ⟨F_X, r_Q(n·)⟩ → 0` as `Q → ∞`, for fixed `X ≥ 1`. -/
theorem tendsto_tsum_dil_posTail_tailRem (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {X : ℝ} (hX : 1 ≤ X) :
    (∀ Q : ℝ, Summable fun n : ℕ => (Λ n : ℝ) * dil (posTail (psi c G) X) (tailRem (psi c G) Q) n)
      ∧ Tendsto (fun Q : ℝ => ∑' n : ℕ, (Λ n : ℝ) * dil (posTail (psi c G) X) (tailRem (psi c G) Q) n)
        atTop (𝓝 0) := by
  have hΦ : ContDiff ℝ 1 (psi c G) :=
    Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c
  refine tendsto_tsum_dil_tailRem_pieces hg hg₁ hg₂c hc (Finset.Icc 1 ⌊X⌋₊) (fun _ => 1) (fun m => X / m)
    (fun m θ => psi c G (m * θ)) (fun m θ => deriv (psi c G) (m * θ) * m) (fun _ _ => one_pos)
    (fun m hm => ?_) (fun m _ => (hΦ.continuous.comp (continuous_const.mul continuous_id)).continuousOn)
    (fun m _ θ _ => ?_) (fun m _ => ?_) (Cvs.L2a.WindowFormTailLimit.posTail_ae_eq_pieces _ (by linarith))
  · have hm1 := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmX : (m : ℝ) ≤ X := (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le (by linarith))
    rw [le_div_iff₀ hm0, one_mul]; exact hmX
  · have h := ((hΦ.differentiable one_ne_zero) (m * θ)).hasDerivAt.comp θ ((hasDerivAt_id θ).const_mul (m : ℝ))
    simp only [mul_one] at h
    exact h
  · exact (((hΦ.continuous_deriv le_rfl).comp (continuous_const.mul continuous_id)).mul
      continuous_const).intervalIntegrable _ _

end Tests

/-! ### The truncation coupling -/

theorem dil_tailRem_posTail_eq_zero (Φ : ℝ → ℝ) {N n : ℕ} (hn : N < n) :
    dil (tailRem Φ N) (posTail Φ N) n = 0 := by
  unfold dil
  refine setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_
  rcases le_or_gt θ 1 with h | h
  · rw [Cvs.L2a.WindowFormTailLimit.tailRem_of_le_one _ _ h, zero_mul]
  · have h1 : (N : ℝ) < n := by exact_mod_cast hn
    have h2 : (N : ℝ) < n * θ := by nlinarith
    rw [Cvs.L2a.PositionTruncatedTail.posTail_of_gt _ h2, mul_zero]

theorem integral_rpow_neg_five_quarters_le {N Q : ℝ} (hN : 0 < N) (hNQ : N ≤ Q) :
    ∫ X in N..Q, X ^ (-(5 / 4 : ℝ)) ≤ 4 * N ^ (-(1 / 4 : ℝ)) := by
  rw [integral_rpow (Or.inr ⟨by norm_num, fun h => ?_⟩)]
  · have e : -(5 / 4 : ℝ) + 1 = -(1 / 4) := by norm_num
    rw [e]
    have hQ : 0 ≤ Q ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have e2 : (Q ^ (-(1 / 4 : ℝ)) - N ^ (-(1 / 4 : ℝ))) / (-(1 / 4 : ℝ))
        = 4 * N ^ (-(1 / 4 : ℝ)) - 4 * Q ^ (-(1 / 4 : ℝ)) := by field_simp; ring
    rw [e2]
    linarith
  · rw [uIcc_of_le hNQ] at h; linarith [h.1]

section Coupling

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- **Fubini in the Abel identity**: `∫_{(1,N]} F_N(θ) ∫_N^Q cut(X, θ) dX/X dθ = ∫_N^Q ⟨F_N, cut(X, ·)⟩ dX/X`. -/
theorem integral_posTail_mul_integral_cutSum (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {N Q : ℝ} (hN : 1 ≤ N) (hNQ : N ≤ Q) :
    IntegrableOn (fun θ => posTail (psi c G) N θ * ∫ X in N..Q, cutSum (psi c G) Q X θ / X) (Ioc 1 N)
      ∧ ∫ θ in Ioc 1 N, posTail (psi c G) N θ * ∫ X in N..Q, cutSum (psi c G) Q X θ / X
        = ∫ X in N..Q, (∫ θ in Ioc 1 N, posTail (psi c G) N θ * cutSum (psi c G) Q X θ) / X := by
  set Φ := psi c G with hΦd
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  have hΦc : Continuous Φ :=
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg s hs).continuousAt.continuousWithinAt) c).continuous
  set f : ℝ → ℝ → ℝ := fun θ X => posTail Φ N θ * (cutSum Φ Q X θ / X) with hfd
  have hfm : Measurable (Function.uncurry f) := by
    show Measurable fun p : ℝ × ℝ => posTail Φ N p.1 * (cutSum Φ Q p.2 p.1 / p.2)
    exact ((Cvs.L2a.FullTailConvergence.measurable_posTail hΦc N).comp measurable_fst).mul
      ((measurable_cutSum hΦc Q).div measurable_snd)
  have hfi : Integrable (Function.uncurry f) ((volume.restrict (Ioc 1 N)).prod (volume.restrict (Ioc N Q))) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (2 * B ^ 2) ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).mpr (ae_of_all _ fun p hp => ?_)
    obtain ⟨h1, h2⟩ := hp
    have hX1 : 1 ≤ p.2 := by linarith [h2.1]
    show ‖posTail Φ N p.1 * (cutSum Φ Q p.2 p.1 / p.2)‖ ≤ 2 * B ^ 2
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < p.2)]
    have a1 := abs_posTail_le_BG hg hg₁ hg₂c hc N p.1
    have a2 : |cutSum Φ Q p.2 p.1| ≤ 2 * B :=
      (abs_cutSum_le hg hg₁ hg₂c hc h1.1 h2.2).trans (div_le_self (by positivity) h1.1.le)
    have a3 : |cutSum Φ Q p.2 p.1| / p.2 ≤ 2 * B := (div_le_self (abs_nonneg _) hX1).trans a2
    calc |posTail Φ N p.1| * (|cutSum Φ Q p.2 p.1| / p.2) ≤ B * (2 * B) :=
          mul_le_mul a1 a3 (by positivity) hB
      _ = 2 * B ^ 2 := by ring
  have hleft : ∀ θ, posTail Φ N θ * ∫ X in N..Q, cutSum Φ Q X θ / X = ∫ X in Ioc N Q, f θ X := by
    intro θ
    rw [intervalIntegral.integral_of_le hNQ, ← integral_const_mul]
  have hright : ∀ X, (∫ θ in Ioc 1 N, posTail Φ N θ * cutSum Φ Q X θ) / X = ∫ θ in Ioc 1 N, f θ X := by
    intro X
    rw [← integral_div]
    congr 1; funext θ; simp only [hfd]; ring
  refine ⟨?_, ?_⟩
  · have := hfi.integral_prod_left
    exact this.congr (ae_of_all _ fun θ => (hleft θ).symm)
  · simp_rw [hleft]
    rw [integral_integral_swap hfi, intervalIntegral.integral_of_le hNQ]
    simp_rw [hright]

/-- One Fubini slice: `|⟨F_N, cut(X, ·)⟩| ≤ B_G · 2√K1b X^{−1/4}` for `1 ≤ X ≤ Q`. -/
theorem abs_integral_posTail_mul_cutSum_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {N X Q : ℝ} (hX : 1 ≤ X) (hXQ : X ≤ Q) :
    |∫ θ in Ioc 1 N, posTail (psi c G) N θ * cutSum (psi c G) Q X θ|
      ≤ Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
        * (2 * √(Cvs.L2a.FullTailConvergence.K1b c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|))
          * X ^ (-(1 / 4 : ℝ))) := by
  set Φ := psi c G with hΦd
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  have hm := fun Y => Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c Y
  have e1 : ∫ θ in Ioc 1 N, posTail Φ N θ * cutSum Φ Q X θ
      = ∫ θ in Ioi 1, posTail Φ N θ * (posTail Φ Q θ - posTail Φ X θ) := by
    rw [setIntegral_congr_fun measurableSet_Ioc fun θ hθ => by rw [cutSum_eq _ hθ.1 hXQ] ]
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun θ hθ => ?_).symm
    have hθN : N < θ := not_le.mp fun h => hθ.2 ⟨hθ.1, h⟩
    rw [Cvs.L2a.PositionTruncatedTail.posTail_of_gt _ hθN, zero_mul]
  rw [e1]
  refine (abs_integral_mul_le_of_le (hm N) ((hm Q).sub (hm X))
    (fun θ hθ => Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc N hθ)
    (fun θ hθ => abs_posTail_sub_posTail_le hg hg₁ hg₂c hc Q X hθ)).trans
    (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) hB)
  · refine (Real.sqrt_le_sqrt (Cvs.L2a.FullTailConvergence.integral_sq_le_of_le (hm N)
      fun θ hθ => Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc N hθ)).trans (le_of_eq ?_)
    exact Real.sqrt_sq hB
  · exact (Real.sqrt_le_sqrt (integral_sq_posTail_sub_le hg hg₁ hg₂c hc (hX.trans hXQ) hX)).trans
      (sqrt_two_K1_add_le hc _ _ hX hXQ)

/-- **The `R_F`-term**: `|Σ_n Λ(n) ⟨F_N, r_N(n·)⟩| ≤ 2B_G √K1b (log N + 4) N^{−1/4}`. -/
theorem abs_tsum_dil_posTail_tailRem_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    |∑' n : ℕ, (Λ n : ℝ) * dil (posTail (psi c G) N) (tailRem (psi c G) N) n|
      ≤ 2 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
        * √(Cvs.L2a.FullTailConvergence.K1b c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|))
        * (Real.log N + 4) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  set Φ := psi c G with hΦd
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  set K := Cvs.L2a.FullTailConvergence.K1b c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  have hK : 0 ≤ √K := Real.sqrt_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNq : 0 ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hN0.le _
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hm := fun Y => Cvs.L2a.FullTailConvergence.measurable_posTail_psi hg c Y
  have hFt := Cvs.L2a.WindowFormTailLimit.tame_posTail_psi hg hg₁ hg₂c hc hN1
  obtain ⟨hsumQ, hlimQ⟩ := tendsto_tsum_dil_posTail_tailRem hg hg₁ hg₂c hc hN1
  set S := ∑' n : ℕ, (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ N) n with hSd
  have hA : ∀ Q : ℕ, N ≤ Q →
      |S - ∑' n : ℕ, (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ Q) n|
        ≤ 2 * B * √K * (Real.log N + 4) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
    intro Q hNQ
    have hNQr : (N : ℝ) ≤ Q := by exact_mod_cast hNQ
    have hQ1 : (1 : ℝ) ≤ Q := hN1.trans hNQr
    -- split `r_N = (F_Q − F_N) + r_Q`
    have hr : tailRem Φ N = fun θ => (posTail Φ Q θ - posTail Φ N θ) + tailRem Φ Q θ := by
      funext θ; simp only [tailRem]; ring
    have hint1 : ∀ n : ℕ, IntegrableOn (fun θ => posTail Φ N θ * (posTail Φ Q (n * θ) - posTail Φ N (n * θ)))
        (Ioi 0) := by
      intro n
      have hwb : ∀ θ, |posTail Φ Q (n * θ) - posTail Φ N (n * θ)| ≤ 2 * B := fun θ => by
        have := abs_sub (posTail Φ Q (n * θ)) (posTail Φ N (n * θ))
        linarith [abs_posTail_le_BG hg hg₁ hg₂c hc Q (n * θ), abs_posTail_le_BG hg hg₁ hg₂c hc N (n * θ)]
      have hwm : Measurable fun θ => posTail Φ Q (n * θ) - posTail Φ N (n * θ) :=
        ((hm Q).comp (measurable_id.const_mul _)).sub ((hm N).comp (measurable_id.const_mul _))
      exact (Cvs.L2a.WindowFormTailLimit.integrable_mul_of_support (hm N) (abs_posTail_le_BG hg hg₁ hg₂c hc N)
        hFt.supp hwm hwb).integrableOn
    have hint2 : ∀ n : ℕ, IntegrableOn (fun θ => posTail Φ N θ * tailRem Φ Q (n * θ)) (Ioi 0) := fun n =>
      (Cvs.L2a.WindowFormTailLimit.integrable_mul_of_support (hm N) (abs_posTail_le_BG hg hg₁ hg₂c hc N) hFt.supp
        ((measurable_tailRem hg hg₁ hg₂c hc Q).comp (measurable_id.const_mul _))
        (fun θ => abs_tailRem_le hg hg₁ hg₂c hc Q (n * θ))).integrableOn
    have hsplit : ∀ n : ℕ, (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ N) n
        = (Λ n : ℝ) * dil (posTail Φ N) (fun θ => posTail Φ Q θ - posTail Φ N θ) n
          + (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ Q) n := by
      intro n
      rw [hr, Cvs.WeilForm.ThetaSpaceParseval.dil_add_right (hint1 n) (hint2 n), mul_add]
    have hfin : ∀ n ∉ Finset.Icc 1 Q,
        (Λ n : ℝ) * dil (posTail Φ N) (fun θ => posTail Φ Q θ - posTail Φ N θ) n = 0 := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      have hnQ : Q < n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨hn0, not_lt.mp h⟩)
      have hd : dil (posTail Φ N) (fun θ => posTail Φ Q θ - posTail Φ N θ) n = 0 := by
        unfold dil
        refine setIntegral_eq_zero_of_forall_eq_zero fun θ _ => ?_
        rcases le_or_gt θ 1 with h | h
        · rw [Cvs.L2a.PositionTruncatedTail.posTail_zero _ _ h, zero_mul]
        · have h1 : (Q : ℝ) < n := by exact_mod_cast hnQ
          have h2 : (Q : ℝ) < n * θ := by nlinarith
          simp only
          rw [Cvs.L2a.PositionTruncatedTail.posTail_of_gt _ h2,
            Cvs.L2a.PositionTruncatedTail.posTail_of_gt _ (hNQr.trans_lt h2), sub_self, mul_zero]
      rw [hd, mul_zero]
    have hS1 : Summable fun n : ℕ =>
        (Λ n : ℝ) * dil (posTail Φ N) (fun θ => posTail Φ Q θ - posTail Φ N θ) n :=
      summable_of_ne_finset_zero hfin
    have hdiff : S - ∑' n : ℕ, (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ Q) n
        = ∑ n ∈ Finset.Icc 1 Q, (Λ n : ℝ) * dil (posTail Φ N) (fun θ => posTail Φ Q θ - posTail Φ N θ) n := by
      rw [hSd, tsum_congr hsplit, hS1.tsum_add (hsumQ Q), tsum_eq_sum hfin]
      ring
    -- the finite sum is `∫_{(1,N]} F_N · logCutSum`
    have hintn : ∀ n ∈ Finset.Icc 1 Q, Integrable
        (fun θ => (Λ n : ℝ) * (posTail Φ N θ * (posTail Φ Q (n * θ) - posTail Φ N (n * θ))))
        (volume.restrict (Ioi 0)) := fun n _ => (hint1 n).const_mul _
    have hfinite : ∑ n ∈ Finset.Icc 1 Q, (Λ n : ℝ) * dil (posTail Φ N) (fun θ => posTail Φ Q θ - posTail Φ N θ) n
        = ∫ θ in Ioc 1 (N : ℝ), posTail Φ N θ * logCutSum Φ Q N θ := by
      calc ∑ n ∈ Finset.Icc 1 Q, (Λ n : ℝ) * dil (posTail Φ N) (fun θ => posTail Φ Q θ - posTail Φ N θ) n
          = ∑ n ∈ Finset.Icc 1 Q, ∫ θ in Ioi 0,
              (Λ n : ℝ) * (posTail Φ N θ * (posTail Φ Q (n * θ) - posTail Φ N (n * θ))) :=
            Finset.sum_congr rfl fun n _ => (integral_const_mul _ _).symm
        _ = ∫ θ in Ioi 0, ∑ n ∈ Finset.Icc 1 Q,
              (Λ n : ℝ) * (posTail Φ N θ * (posTail Φ Q (n * θ) - posTail Φ N (n * θ))) :=
            (integral_finsetSum _ hintn).symm
        _ = ∫ θ in Ioi 0, posTail Φ N θ
              * ∑ n ∈ Finset.Icc 1 Q, (Λ n : ℝ) * (posTail Φ Q (n * θ) - posTail Φ N (n * θ)) := by
            congr 1; funext θ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
        _ = ∫ θ in Ioi 1, posTail Φ N θ
              * ∑ n ∈ Finset.Icc 1 Q, (Λ n : ℝ) * (posTail Φ Q (n * θ) - posTail Φ N (n * θ)) :=
            Cvs.L2a.WindowFormTailLimit.setIntegral_Ioi_zero_eq_one fun θ hθ => by
              rw [Cvs.L2a.PositionTruncatedTail.posTail_zero _ _ hθ, zero_mul]
        _ = ∫ θ in Ioi 1, posTail Φ N θ * logCutSum Φ Q N θ :=
            setIntegral_congr_fun measurableSet_Ioi fun θ hθ => by
              have h := sum_vonMangoldt_posTail_sub Φ hθ hNQr
              rw [Nat.floor_natCast] at h
              rw [h]
        _ = ∫ θ in Ioc 1 (N : ℝ), posTail Φ N θ * logCutSum Φ Q N θ :=
            setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
              fun θ hθ => by
                have hθN : (N : ℝ) < θ := not_le.mp fun h => hθ.2 ⟨hθ.1, h⟩
                rw [Cvs.L2a.PositionTruncatedTail.posTail_of_gt _ hθN, zero_mul]
    -- Abel summation on `(1, N]`
    obtain ⟨hFub, hswap⟩ := integral_posTail_mul_integral_cutSum hg hg₁ hg₂c hc hN1 hNQr
    set u : ℝ → ℝ := fun θ => posTail Φ N θ * Real.log (N / θ) with hud
    have hum : Measurable u := (hm N).mul (Real.measurable_log.comp (measurable_const.div measurable_id))
    have huK : ∀ θ, 0 < θ → |u θ| ≤ B * Real.log N / θ := by
      intro θ hθ
      by_cases h : θ ∈ Ioc 1 (N : ℝ)
      · rw [hud, abs_mul, mul_div_right_comm]
        refine mul_le_mul (Cvs.L2a.FullTailConvergence.abs_posTail_le hg hg₁ hg₂c hc N hθ) ?_ (abs_nonneg _)
          (by positivity)
        rw [abs_of_nonneg (Real.log_nonneg ((one_le_div hθ).mpr h.2))]
        exact Real.log_le_log (div_pos hN0 hθ) (div_le_self hN0.le h.1.le)
      · have h0 : posTail Φ N θ = 0 := by
          rcases le_or_gt θ 1 with h1 | h1
          · exact Cvs.L2a.PositionTruncatedTail.posTail_zero _ _ h1
          · exact Cvs.L2a.PositionTruncatedTail.posTail_of_gt _ (not_le.mp fun h2 => h ⟨h1, h2⟩)
        rw [hud]; simp only [h0, zero_mul, abs_zero]; positivity
    have hvK : ∀ θ, 0 < θ → |posTail Φ Q θ - posTail Φ N θ| ≤ 2 * B / θ := fun θ hθ =>
      abs_posTail_sub_posTail_le hg hg₁ hg₂c hc Q N hθ
    have hI1 : IntegrableOn (fun θ => u θ * (posTail Φ Q θ - posTail Φ N θ)) (Ioc 1 (N : ℝ)) :=
      (Cvs.L2a.FullTailConvergence.integrableOn_mul_of_le hum ((hm Q).sub (hm N)) huK hvK).mono_set
        Ioc_subset_Ioi_self
    have habel : ∫ θ in Ioc 1 (N : ℝ), posTail Φ N θ * logCutSum Φ Q N θ
        = (∫ θ in Ioc 1 (N : ℝ), u θ * (posTail Φ Q θ - posTail Φ N θ))
          + ∫ θ in Ioc 1 (N : ℝ), posTail Φ N θ * ∫ X in (N : ℝ)..Q, cutSum Φ Q X θ / X := by
      rw [← integral_add hI1 hFub]
      refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
      rw [logCutSum_eq Φ (by linarith [hθ.1]) hN0 hNQr, cutSum_eq Φ hθ.1 hNQr, hud]
      ring
    -- the two bounds
    have hb1 : |∫ θ in Ioc 1 (N : ℝ), u θ * (posTail Φ Q θ - posTail Φ N θ)|
        ≤ B * Real.log N * (2 * √K * (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
      have e : ∫ θ in Ioc 1 (N : ℝ), u θ * (posTail Φ Q θ - posTail Φ N θ)
          = ∫ θ in Ioi 1, u θ * (posTail Φ Q θ - posTail Φ N θ) := by
        refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
          fun θ hθ => ?_).symm
        have hθN : (N : ℝ) < θ := not_le.mp fun h => hθ.2 ⟨hθ.1, h⟩
        rw [hud]; simp only [Cvs.L2a.PositionTruncatedTail.posTail_of_gt _ hθN, zero_mul]
      rw [e]
      refine (abs_integral_mul_le_of_le hum ((hm Q).sub (hm N)) huK hvK).trans
        (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (by positivity))
      · exact (Real.sqrt_le_sqrt (Cvs.L2a.FullTailConvergence.integral_sq_le_of_le hum huK)).trans
          (le_of_eq (Real.sqrt_sq (by positivity)))
      · exact (Real.sqrt_le_sqrt (integral_sq_posTail_sub_le hg hg₁ hg₂c hc hQ1 hN1)).trans
          (sqrt_two_K1_add_le hc _ _ hN1 hNQr)
    have hb2 : |∫ X in (N : ℝ)..Q, (∫ θ in Ioc 1 (N : ℝ), posTail Φ N θ * cutSum Φ Q X θ) / X|
        ≤ 2 * B * √K * (4 * (N : ℝ) ^ (-(1 / 4 : ℝ))) := by
      have hint : IntervalIntegrable (fun X : ℝ => 2 * B * √K * X ^ (-(5 / 4 : ℝ))) volume N Q :=
        (intervalIntegral.intervalIntegrable_rpow (Or.inr fun h => by
          rw [uIcc_of_le hNQr] at h; linarith [h.1])).const_mul _
      rw [← Real.norm_eq_abs]
      refine (intervalIntegral.norm_integral_le_of_norm_le hNQr (ae_of_all _ fun X hX => ?_) hint).trans ?_
      · have hX0 : 0 < X := hN0.trans hX.1
        have hb := abs_integral_posTail_mul_cutSum_le hg hg₁ hg₂c hc (N := N) (hN1.trans hX.1.le) hX.2
        have e : X ^ (-(5 / 4 : ℝ)) = X ^ (-(1 / 4 : ℝ)) / X := by
          rw [show -(5 / 4 : ℝ) = -(1 / 4) + (-1) by norm_num, Real.rpow_add hX0, Real.rpow_neg_one]
          ring
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hX0, e]
        calc |∫ θ in Ioc 1 (N : ℝ), posTail Φ N θ * cutSum Φ Q X θ| / X
            ≤ B * (2 * √K * X ^ (-(1 / 4 : ℝ))) / X := div_le_div_of_nonneg_right hb hX0.le
          _ = 2 * B * √K * (X ^ (-(1 / 4 : ℝ)) / X) := by ring
      · rw [intervalIntegral.integral_const_mul]
        exact mul_le_mul_of_nonneg_left (integral_rpow_neg_five_quarters_le hN0 hNQr) (by positivity)
    rw [hdiff, hfinite, habel, hswap]
    calc |(∫ θ in Ioc 1 (N : ℝ), u θ * (posTail Φ Q θ - posTail Φ N θ))
          + ∫ X in (N : ℝ)..Q, (∫ θ in Ioc 1 (N : ℝ), posTail Φ N θ * cutSum Φ Q X θ) / X|
        ≤ B * Real.log N * (2 * √K * (N : ℝ) ^ (-(1 / 4 : ℝ))) + 2 * B * √K * (4 * (N : ℝ) ^ (-(1 / 4 : ℝ))) :=
          (abs_add_le _ _).trans (add_le_add hb1 hb2)
      _ = 2 * B * √K * (Real.log N + 4) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
  have hlim : Tendsto (fun Q : ℕ => |S - ∑' n : ℕ, (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ Q) n|) atTop
      (𝓝 |S - 0|) := ((tendsto_const_nhds).sub (hlimQ.comp tendsto_natCast_atTop_atTop)).abs
  rw [sub_zero] at hlim
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun Q hQ => hA Q hQ⟩)

end Coupling

/-! ### E1's prime channel -/

section Limit

variable {c : ℝ} {G G₁ G₂ : ℝ → ℝ}

/-- **The truncation half of the prime coupling**: `|Σ_n Λ(n)(⟨r_N, F_N(n·)⟩ + ⟨F_N, r_N(n·)⟩)|
≤ 2B_G √K1b (3 log N + 4) N^{−1/4}` for every integer `N ≥ 1`. -/
theorem abs_primeθ_tailRem_posTail_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    |primeθ (tailRem (psi c G) N) (posTail (psi c G) N)|
      ≤ 2 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
        * √(Cvs.L2a.FullTailConvergence.K1b c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|))
        * (3 * Real.log N + 4) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by
  set Φ := psi c G with hΦd
  set B := Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  set K := Cvs.L2a.FullTailConvergence.K1b c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
  have hB : 0 ≤ B := Cvs.L2a.FullTailConvergence.BG_nonneg hc _ (Cvs.L2a.FullTailConvergence.C1_nonneg G₁ G₂)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hL : Summable fun n : ℕ => (Λ n : ℝ) * dil (tailRem Φ N) (posTail Φ N) n :=
    summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      rw [dil_tailRem_posTail_eq_zero _ (by omega : N < n), mul_zero]
  have hR := (tendsto_tsum_dil_posTail_tailRem hg hg₁ hg₂c hc hN1).1 N
  have e : primeθ (tailRem Φ N) (posTail Φ N)
      = (∑' n : ℕ, (Λ n : ℝ) * dil (tailRem Φ N) (posTail Φ N) n)
        + ∑' n : ℕ, (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ N) n := by
    unfold primeθ
    rw [← hL.tsum_add hR]
    exact tsum_congr fun n => mul_add _ _ _
  rw [e]
  have h1 := abs_tsum_dil_tailRem_posTail_le hg hg₁ hg₂c hc hN
  have h2 := abs_tsum_dil_posTail_tailRem_le hg hg₁ hg₂c hc hN
  have h3 := sqrt_K1_le hc (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) hN1
  have h4 := mul_le_mul_of_nonneg_right h3 (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hB) hlogN)
  calc |(∑' n : ℕ, (Λ n : ℝ) * dil (tailRem Φ N) (posTail Φ N) n)
        + ∑' n : ℕ, (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ N) n|
      ≤ |∑' n : ℕ, (Λ n : ℝ) * dil (tailRem Φ N) (posTail Φ N) n|
        + |∑' n : ℕ, (Λ n : ℝ) * dil (posTail Φ N) (tailRem Φ N) n| := abs_add_le _ _
    _ ≤ √K * (N : ℝ) ^ (-(1 / 4 : ℝ)) * (4 * B * Real.log N)
        + 2 * B * √K * (Real.log N + 4) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by linarith
    _ = 2 * B * √K * (3 * Real.log N + 4) * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by ring

/-- The truncation half of the prime coupling tends to `0`. -/
theorem tendsto_primeθ_tailRem_posTail (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) :
    Tendsto (fun N : ℕ => primeθ (tailRem (psi c G) N) (posTail (psi c G) N)) atTop (𝓝 0) := by
  set C := 2 * Cvs.L2a.FullTailConvergence.BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)
    * √(Cvs.L2a.FullTailConvergence.K1b c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|)) with hCd
  have hlog : Tendsto (fun x : ℝ => Real.log x * x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    refine (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  have hq : Tendsto (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by norm_num)
  have hb : Tendsto (fun x : ℝ => C * (3 * Real.log x + 4) * x ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    have := ((hlog.const_mul 3).add (hq.const_mul 4)).const_mul C
    simp only [mul_zero, add_zero] at this
    exact this.congr fun x => by ring
  refine squeeze_zero_norm' ?_ (hb.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs, Function.comp_apply, hCd]
  exact abs_primeθ_tailRem_posTail_le hg hg₁ hg₂c hc hN

/-- The window half of the prime coupling tends to `0`, for every `a > 0`. -/
theorem tendsto_primeθ_tailRem_window (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => primeθ (tailRem (psi c G) N) (window a G)) atTop (𝓝 0) := by
  simp_rw [Cvs.L2a.WindowFormTailLimit.primeθ_tailRem_window]
  exact (tendsto_tsum_dil_window_tailRem hg hg₁ hg₂c hc ha).2.comp tendsto_natCast_atTop_atTop

/-- **E1's prime channel**: `PrimeTailLimit c G` for every `G ∈ C²[−1, 1]` and every `c > 0`. -/
theorem primeTailLimit (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) : PrimeTailLimit c G := by
  have h := (tendsto_primeθ_tailRem_posTail hg hg₁ hg₂c hc).sub
    (tendsto_primeθ_tailRem_window hg hg₁ hg₂c hc (a := 2 * π / c) (by positivity))
  rw [sub_zero] at h
  exact h

/-- `PrimeTailLimit c G̃` for the regularised profile `G̃ = G − aG(0) a⁻¹β(·/a)`, `G ∈ C²[−1, 1]`, `c > 0`. -/
theorem primeTailLimit_regProfile (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (hc : 0 < c) : PrimeTailLimit c (Cvs.L2a.WindowFormTailLimit.regProfile c G) := by
  set t := -(2 * π / c * G 0) with ht
  have hgt : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (Cvs.L2a.WindowFormTailLimit.regProfile c G)
      (G₁ s + t * Cvs.L2a.FullTailBilinearChannels.betaA1 c s) s := fun s hs =>
    (hg s hs).add ((Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA c s).const_mul t)
  have hgt₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => G₁ s + t * Cvs.L2a.FullTailBilinearChannels.betaA1 c s)
      (G₂ s + t * Cvs.L2a.FullTailBilinearChannels.betaA2 c s) s := fun s hs =>
    (hg₁ s hs).add ((Cvs.L2a.FullTailBilinearChannels.hasDerivAt_betaA1 c s).const_mul t)
  have hgt₂c : ContinuousOn (fun s => G₂ s + t * Cvs.L2a.FullTailBilinearChannels.betaA2 c s) (uIcc (-1) 1) :=
    hg₂c.add (continuous_const.mul (Cvs.L2a.FullTailBilinearChannels.continuous_betaA2 c)).continuousOn
  exact primeTailLimit hgt hgt₁ hgt₂c hc

/-- **The polar algebra (C)**: for `G` even and `C²` with `∫ G = 0` and `c ≥ 2π`,
`QW(k_G) = W_∞(Φ) − 2aG(0) W_∞(Φ, Ψ) + a²G(0)² W_∞(Ψ)`. -/
theorem window_eq_polar' (hc : 2 * π ≤ c) (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G (G₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt G₁ (G₂ s) s) (hg₂c : ContinuousOn G₂ (uIcc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (hGi : ∫ s in (-1 : ℝ)..1, G s = 0)
    {P R : ℕ} (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale (window (2 * π / c) G))
      = Cvs.L2a.FullTailWeilFormLimit.Winf (psi c G)
        - 2 * (2 * π / c * G 0) * Cvs.L2a.FullTailPolarisation.WinfBil (psi c G) Cvs.L2a.BetaProfilePoissonTail.Psi
        + (2 * π / c * G 0) ^ 2 * Cvs.L2a.FullTailWeilFormLimit.Winf Cvs.L2a.BetaProfilePoissonTail.Psi :=
  Cvs.L2a.WindowFormTailLimit.window_eq_polar hc hg hg₁ hg₂c heven hGi hP hR
    (primeTailLimit_regProfile hg hg₁ hg₂c (by linarith [pi_pos]))

end Limit

/-! ### SPINE-L2a(5) from the prime tail limit -/

section Spine

open Cvs.L2a.WindowFormDeepSpan (c0 Hx)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem c0_pos {c : ℝ} (hc : c0 ≤ c) : 0 < c :=
  lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hc)

omit [DecidableEq ι] in
/-- `PrimeTailLimit` for the regularised span profile `Σ_i b_i h_i`, each `h_i ∈ C²[−1, 1]`. -/
theorem primeTailLimit_span {c : ℝ} (b : ι → ℝ) {h h₁ h₂ : ι → ℝ → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1)) (hc : 0 < c) :
    PrimeTailLimit c (Cvs.L2a.WindowFormTailLimit.regProfile c fun s => ∑ i, b i * h i s) :=
  primeTailLimit_regProfile (Cvs.L2a.FullTailBilinearChannels.hasDerivAt_span b hg) (Cvs.L2a.FullTailBilinearChannels.hasDerivAt_span b hg₁)
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul (hg₂c i)) hc

/-- **SPINE-L2a(5)**: `WindowFormDeepSpan`'s deep-family window bound, with `primeTailLimit` supplying E1's prime channel. -/
theorem L2a_window_deep' (i₀ : ι) {h h₁ h₂ : ι → ℝ → ℝ} {g g₁ g₂ : ℝ → ℝ} {c χg μg : ℝ} {χ μ : ι → ℝ}
    (b : ι → ℝ) {m : ℕ} {P R : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h i) (h₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (h₁ i) (h₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (h₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * h₂ i s - 2 * s * h₁ i s - c ^ 2 * s ^ 2 * h i s + χ i * h i s = 0)
    (hc : c0 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hσ : ∀ i, 5 * c ≤ c ^ 2 - χ i) (hχi : Function.Injective χ)
    (heven : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, h i (-s) = h i s) (hnorm : ∀ i, ∫ s in (-1 : ℝ)..1, h i s ^ 2 = 1)
    (hμ : ∀ i, ∀ s ∈ Icc (-1 : ℝ) 1, psi c (h i) s = μ i * h i s)
    (hground : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i₀)).ncard = 0)
    (hidx : ∀ i, Even (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hJ : (Fintype.card ι : ℝ) ≤ c / 4 + 1)
    (hm : 1 ≤ m) (hcount : ∀ i, i ≠ i₀ →
      m ≤ (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio (χ i)).ncard)
    (hgd : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hgd₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hgd₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hgang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χg * g s = 0)
    (hgeven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hgnorm : ∫ s in (-1 : ℝ)..1, g s ^ 2 = 1)
    (hgμ : ∀ s ∈ Icc (-1 : ℝ) 1, psi c g s = μg * g s)
    (hgcount : (Cvs.Prolate.EdgeCentreSign.evenSpec (Cvs.Prolate.RegularSolutionEdge.sqC c) ∩ Iio χg).ncard = m)
    (hpole : ∑ i, b i * ∫ s in (-1 : ℝ)..1, h i s = 0)
    (hP : 1 / (2 * π / c) ≤ P) (hR : Real.log (1 / (2 * π / c)) ≤ R * Real.log 2) :
    π / (8 * c * Hx c * (1 + 2 * c / (π * (μ i₀ * √(c / (2 * π))) ^ 2))) * (1 - (μg * √(c / (2 * π))) ^ 2)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (fun s => ∑ i, b i * h i s) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / c) fun s => ∑ i, b i * h i s)) :=
  Cvs.L2a.WindowFormDeepSpan.L2a_window_deep i₀ b hg hg₁ hg₂c hang hc hχ0 hσ hχi heven hnorm hμ hground hidx hJ hm
    hcount hgd hgd₁ hgd₂c hgang hgeven hgnorm hgμ hgcount hpole hP hR
    (primeTailLimit_span b hg hg₁ hg₂c (c0_pos hc))

end Spine

end Cvs.L2a.PrimeTailLimitProfiles
