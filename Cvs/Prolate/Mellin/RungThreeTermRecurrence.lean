import Mathlib
import Cvs.Prolate.EvenRungsByIndex

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Mellin transform of a prolate rung satisfies an exact three-term recurrence

If `(1 − w²)h'' − 2wh' − c²w²h + χh = 0` on `[0, 1]`, then `mel h s = ∫₀¹ w^{s−1} h(w) dw` satisfies
`s(s + 1) mel h s − ((s + 1)(s + 2) − χ) mel h (s + 2) − c² mel h (s + 4) = 0` for `Re s > 0`. The factor `1 − w²`
kills the boundary terms at `w = 1`, and those at `w = 0` are `O(ε^{Re s})`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology intervalIntegral

namespace Cvs.Prolate.Mellin.RungThreeTermRecurrence

/-- The Mellin transform over `[0, 1]`: `mel f s = ∫₀¹ w^{s−1} f(w) dw`. -/
def mel (f : ℝ → ℝ) (s : ℂ) : ℂ := ∫ w in (0 : ℝ)..1, (w : ℂ) ^ (s - 1) * (f w : ℂ)

/-- The recurrence integrand: `(s(s+1)w^{s−1} − ((s+1)(s+2) − χ)w^{s+1} − c²w^{s+3}) h(w)`. -/
def recInt (c χ : ℝ) (h : ℝ → ℝ) (s : ℂ) (w : ℝ) : ℂ :=
  (s * (s + 1) * (w : ℂ) ^ (s - 1) - ((s + 1) * (s + 2) - χ) * (w : ℂ) ^ (s + 1) - (c : ℂ) ^ 2 * (w : ℂ) ^ (s + 3))
    * (h w : ℂ)

/-- The primitive: `w^{s+1}(1 − w²)h'(w) − (s+1)w^s(1 − w²)h(w)`. -/
def prim (h h₁ : ℝ → ℝ) (s : ℂ) (w : ℝ) : ℂ :=
  (w : ℂ) ^ (s + 1) * (((1 - w ^ 2) * h₁ w : ℝ) : ℂ) - (s + 1) * (w : ℂ) ^ s * (((1 - w ^ 2) * h w : ℝ) : ℂ)

theorem cpow_add_nat {w : ℝ} (hw : 0 < w) (s : ℂ) (n : ℕ) : (w : ℂ) ^ (s + n) = (w : ℂ) ^ s * (w : ℂ) ^ n := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hw.ne'), Complex.cpow_natCast]

/-- **The primitive differentiates to minus the recurrence integrand** at every `w > 0` where `h` solves the angular
equation. -/
theorem hasDerivAt_prim {c χ : ℝ} {h h₁ h₂ : ℝ → ℝ} {s : ℂ} (hs : 0 < s.re) {w : ℝ} (hw : 0 < w)
    (hd : HasDerivAt h (h₁ w) w) (hd₁ : HasDerivAt h₁ (h₂ w) w)
    (hode : (1 - w ^ 2) * h₂ w - 2 * w * h₁ w - c ^ 2 * w ^ 2 * h w + χ * h w = 0) :
    HasDerivAt (prim h h₁ s) (-recInt c χ h s w) w := by
  have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
  have hs1 : s + 1 ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hp : HasDerivAt (fun y => (1 - y ^ 2) * h₁ y) (-2 * w * h₁ w + (1 - w ^ 2) * h₂ w) w := by
    have := ((hasDerivAt_pow 2 w).const_sub 1).mul hd₁
    exact this.congr_deriv (by push_cast; ring)
  have hq : HasDerivAt (fun y => (1 - y ^ 2) * h y) (-2 * w * h w + (1 - w ^ 2) * h₁ w) w := by
    have := ((hasDerivAt_pow 2 w).const_sub 1).mul hd
    exact this.congr_deriv (by push_cast; ring)
  have hA := hasDerivAt_ofReal_cpow_const hw.ne' hs1
  have hB := hasDerivAt_ofReal_cpow_const hw.ne' hs0
  have H := (hA.mul hp.ofReal_comp).sub ((hB.const_mul (s + 1)).mul hq.ofReal_comp)
  unfold prim
  refine H.congr_deriv ?_
  have hw0 : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  have e1 : (w : ℂ) ^ (s + 1 - 1) = (w : ℂ) ^ (s - 1) * (w : ℂ) := by
    rw [show s + 1 - 1 = (s - 1) + (1 : ℕ) by push_cast; ring, cpow_add_nat hw, pow_one]
  have e2 : (w : ℂ) ^ (s + 1) = (w : ℂ) ^ (s - 1) * (w : ℂ) ^ 2 := by
    rw [show s + 1 = (s - 1) + (2 : ℕ) by push_cast; ring, cpow_add_nat hw]
  have e3 : (w : ℂ) ^ (s + 3) = (w : ℂ) ^ (s - 1) * (w : ℂ) ^ 4 := by
    rw [show s + 3 = (s - 1) + (4 : ℕ) by push_cast; ring, cpow_add_nat hw]
  have e4 : (w : ℂ) ^ s = (w : ℂ) ^ (s - 1) * (w : ℂ) := by
    rw [show s = (s - 1) + (1 : ℕ) by push_cast; ring, cpow_add_nat hw, pow_one]
    simp
  have hodeC : ((1 - w ^ 2) * h₂ w - 2 * w * h₁ w - c ^ 2 * w ^ 2 * h w + χ * h w : ℝ) = (0 : ℂ) := by
    exact_mod_cast hode
  unfold recInt
  rw [e1, e2, e3, e4]
  push_cast at hodeC ⊢
  linear_combination ((w : ℂ) ^ (s - 1) * (w : ℂ) ^ 2) * hodeC

/-- `‖w^{s+n}‖ ≤ w^{Re s − 1}` for `0 < w ≤ 1` and `n ≥ −1`. -/
theorem norm_cpow_le {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (s : ℂ) {t : ℝ} (ht : s.re - 1 ≤ t) (e : ℂ)
    (he : e.re = t) : ‖(w : ℂ) ^ e‖ ≤ w ^ (s.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hw, he]
  exact Real.rpow_le_rpow_of_exponent_ge hw hw1 ht

/-- **The recurrence integrand is integrable on `[0, 1]`** for `Re s > 0` and continuous `h`. -/
theorem intervalIntegrable_recInt {c χ : ℝ} {h : ℝ → ℝ} {s : ℂ} (hs : 0 < s.re)
    (hc : ContinuousOn h (Icc 0 1)) : IntervalIntegrable (recInt c χ h s) volume 0 1 := by
  have hcC : ContinuousOn (fun w => (h w : ℂ)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact Complex.continuous_ofReal.comp_continuousOn hc
  have i1 : IntervalIntegrable (fun w : ℝ => (w : ℂ) ^ (s - 1)) volume 0 1 :=
    intervalIntegrable_cpow' (by simp; linarith)
  have i2 : IntervalIntegrable (fun w : ℝ => (w : ℂ) ^ (s + 1)) volume 0 1 :=
    intervalIntegrable_cpow' (by simp; linarith)
  have i3 : IntervalIntegrable (fun w : ℝ => (w : ℂ) ^ (s + 3)) volume 0 1 :=
    intervalIntegrable_cpow' (by simp; linarith)
  have := (((i1.const_mul (s * (s + 1))).sub (i2.const_mul ((s + 1) * (s + 2) - χ))).sub
    (i3.const_mul ((c : ℂ) ^ 2))).mul_continuousOn hcC
  exact this

/-- **The recurrence as one integral.** -/
theorem integral_recInt_eq {c χ : ℝ} {h : ℝ → ℝ} {s : ℂ} (hs : 0 < s.re) (hc : ContinuousOn h (Icc 0 1)) :
    ∫ w in (0 : ℝ)..1, recInt c χ h s w =
      s * (s + 1) * mel h s - ((s + 1) * (s + 2) - χ) * mel h (s + 2) - (c : ℂ) ^ 2 * mel h (s + 4) := by
  have hcC : ContinuousOn (fun w => (h w : ℂ)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact Complex.continuous_ofReal.comp_continuousOn hc
  have j : ∀ e : ℂ, -1 < e.re → IntervalIntegrable (fun w : ℝ => (w : ℂ) ^ e * (h w : ℂ)) volume 0 1 :=
    fun e he => (intervalIntegrable_cpow' he).mul_continuousOn hcC
  have j1 := j (s - 1) (by simp; linarith)
  have j2 := j (s + 1) (by simp; linarith)
  have j3 := j (s + 3) (by simp; linarith)
  unfold mel
  rw [show s + 2 - 1 = s + 1 by ring, show s + 4 - 1 = s + 3 by ring,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (j1.const_mul _) (j2.const_mul _),
    ← intervalIntegral.integral_sub ((j1.const_mul _).sub (j2.const_mul _)) (j3.const_mul _)]
  refine intervalIntegral.integral_congr fun w _ => ?_
  simp only [recInt]
  ring

/-- **The exact Mellin recurrence** for any `C²` solution of the angular equation on `[0, 1]`. -/
theorem mel_recurrence {c χ : ℝ} {h h₁ h₂ : ℝ → ℝ}
    (hd : ∀ w ∈ Icc (0 : ℝ) 1, HasDerivAt h (h₁ w) w) (hd₁ : ∀ w ∈ Icc (0 : ℝ) 1, HasDerivAt h₁ (h₂ w) w)
    (hode : ∀ w ∈ Icc (0 : ℝ) 1, (1 - w ^ 2) * h₂ w - 2 * w * h₁ w - c ^ 2 * w ^ 2 * h w + χ * h w = 0)
    {s : ℂ} (hs : 0 < s.re) :
    s * (s + 1) * mel h s - ((s + 1) * (s + 2) - χ) * mel h (s + 2) - (c : ℂ) ^ 2 * mel h (s + 4) = 0 := by
  have hc : ContinuousOn h (Icc 0 1) := fun w hw => (hd w hw).continuousAt.continuousWithinAt
  have hc₁ : ContinuousOn h₁ (Icc 0 1) := fun w hw => (hd₁ w hw).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc₁
  set σ := s.re
  set R := s * (s + 1) * mel h s - ((s + 1) * (s + 2) - χ) * mel h (s + 2) - (c : ℂ) ^ 2 * mel h (s + 4)
  set K := (‖s * (s + 1)‖ + ‖(s + 1) * (s + 2) - (χ : ℂ)‖ + ‖(c : ℂ) ^ 2‖) * |B|
  have hint := intervalIntegrable_recInt (c := c) (χ := χ) hs hc
  -- pointwise bound on (0, 1]
  have hg : ∀ w ∈ Ioc (0 : ℝ) 1, ‖recInt c χ h s w‖ ≤ K * w ^ (σ - 1) := by
    intro w ⟨hw, hw1⟩
    have hhB : ‖(h w : ℂ)‖ ≤ |B| := by
      rw [Complex.norm_real]
      exact (hB w ⟨hw.le, hw1⟩).trans (le_abs_self B)
    have b1 := norm_cpow_le hw hw1 s le_rfl (s - 1) (by simp)
    have b2 := norm_cpow_le hw hw1 s (t := σ + 1) (by linarith) (s + 1) (by simp [σ])
    have b3 := norm_cpow_le hw hw1 s (t := σ + 3) (by linarith) (s + 3) (by simp [σ])
    have hp : 0 ≤ w ^ (σ - 1) := Real.rpow_nonneg hw.le _
    have hsum : ‖s * (s + 1) * (w : ℂ) ^ (s - 1) - ((s + 1) * (s + 2) - χ) * (w : ℂ) ^ (s + 1)
        - (c : ℂ) ^ 2 * (w : ℂ) ^ (s + 3)‖
        ≤ (‖s * (s + 1)‖ + ‖(s + 1) * (s + 2) - (χ : ℂ)‖ + ‖(c : ℂ) ^ 2‖) * w ^ (σ - 1) := by
      set A := s * (s + 1) * (w : ℂ) ^ (s - 1)
      set B' := ((s + 1) * (s + 2) - χ) * (w : ℂ) ^ (s + 1)
      set C' := (c : ℂ) ^ 2 * (w : ℂ) ^ (s + 3)
      have hA : ‖A‖ ≤ ‖s * (s + 1)‖ * w ^ (σ - 1) := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left b1 (norm_nonneg _)
      have hB' : ‖B'‖ ≤ ‖(s + 1) * (s + 2) - (χ : ℂ)‖ * w ^ (σ - 1) := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left b2 (norm_nonneg _)
      have hC' : ‖C'‖ ≤ ‖(c : ℂ) ^ 2‖ * w ^ (σ - 1) := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left b3 (norm_nonneg _)
      calc ‖A - B' - C'‖ ≤ ‖A - B'‖ + ‖C'‖ := norm_sub_le _ _
        _ ≤ ‖A‖ + ‖B'‖ + ‖C'‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith
    unfold recInt
    rw [norm_mul]
    calc _ ≤ ((‖s * (s + 1)‖ + ‖(s + 1) * (s + 2) - (χ : ℂ)‖ + ‖(c : ℂ) ^ 2‖) * w ^ (σ - 1)) * |B| :=
          mul_le_mul hsum hhB (norm_nonneg _) (by positivity)
      _ = K * w ^ (σ - 1) := by ring
  -- the primitive at ε
  have hprim : ∀ ε ∈ Ioc (0 : ℝ) 1, ∫ w in ε..1, recInt c χ h s w = prim h h₁ s ε := by
    intro ε ⟨hε, hε1⟩
    have hder : ∀ w ∈ uIcc ε 1, HasDerivAt (prim h h₁ s) (-recInt c χ h s w) w := by
      intro w hw
      rw [uIcc_of_le hε1] at hw
      have hw0 : 0 < w := hε.trans_le hw.1
      exact hasDerivAt_prim hs hw0 (hd w ⟨hw0.le, hw.2⟩) (hd₁ w ⟨hw0.le, hw.2⟩) (hode w ⟨hw0.le, hw.2⟩)
    have hsub : uIcc ε 1 ⊆ uIcc 0 1 := by
      rw [uIcc_of_le hε1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hε.le le_rfl
    have hi : IntervalIntegrable (fun w => -recInt c χ h s w) volume ε 1 := (hint.mono_set hsub).neg
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi
    rw [intervalIntegral.integral_neg] at this
    have h1 : prim h h₁ s 1 = 0 := by simp [prim]
    rw [h1] at this
    linear_combination -this
  -- R = ∫₀^ε g + prim(ε)
  have hsplit : ∀ ε ∈ Ioc (0 : ℝ) 1, R = (∫ w in (0 : ℝ)..ε, recInt c χ h s w) + prim h h₁ s ε := by
    intro ε hε
    have hsub : uIcc 0 ε ⊆ uIcc 0 1 := by
      rw [uIcc_of_le hε.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hε.2
    have hsub' : uIcc ε 1 ⊆ uIcc 0 1 := by
      rw [uIcc_of_le hε.2, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hε.1.le le_rfl
    rw [← hprim ε hε, intervalIntegral.integral_add_adjacent_intervals (hint.mono_set hsub)
      (hint.mono_set hsub'), integral_recInt_eq hs hc]
  -- both pieces are O(ε^σ)
  have hbound : ∀ ε ∈ Ioc (0 : ℝ) 1, ‖R‖ ≤ (K / σ + (|B₁| + ‖s + 1‖ * |B|)) * ε ^ σ := by
    intro ε hε
    have hε0 := hε.1
    have hI : ‖∫ w in (0 : ℝ)..ε, recInt c χ h s w‖ ≤ K / σ * ε ^ σ := by
      have hle : ∀ᵐ w ∂volume, w ∈ Ioc (0 : ℝ) ε → ‖recInt c χ h s w‖ ≤ K * w ^ (σ - 1) :=
        Eventually.of_forall fun w hw => hg w ⟨hw.1, hw.2.trans hε.2⟩
      have hii : IntervalIntegrable (fun w : ℝ => K * w ^ (σ - 1)) volume 0 ε :=
        (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul K
      refine (intervalIntegral.norm_integral_le_of_norm_le hε0.le hle hii).trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
        show σ - 1 + 1 = σ by ring, Real.zero_rpow hs.ne']
      ring
    have hP : ‖prim h h₁ s ε‖ ≤ (|B₁| + ‖s + 1‖ * |B|) * ε ^ σ := by
      have hb : ‖(ε : ℂ) ^ (s + 1)‖ ≤ ε ^ σ := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hε0]
        simp only [Complex.add_re, Complex.one_re]
        exact Real.rpow_le_rpow_of_exponent_ge hε0 hε.2 (by linarith)
      have hb' : ‖(ε : ℂ) ^ s‖ = ε ^ σ := Complex.norm_cpow_eq_rpow_re_of_pos hε0 s
      have h1 : ‖((((1 - ε ^ 2) * h₁ ε : ℝ)) : ℂ)‖ ≤ |B₁| := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have : |1 - ε ^ 2| ≤ 1 := by
          rw [abs_le]; constructor <;> nlinarith [hε.2, hε0]
        have hb1 : |h₁ ε| ≤ |B₁| := by
          have := hB₁ ε ⟨hε0.le, hε.2⟩
          rw [Real.norm_eq_abs] at this
          exact this.trans (le_abs_self B₁)
        calc |1 - ε ^ 2| * |h₁ ε| ≤ 1 * |B₁| := mul_le_mul this hb1 (abs_nonneg _) zero_le_one
          _ = |B₁| := one_mul _
      have h2 : ‖((((1 - ε ^ 2) * h ε : ℝ)) : ℂ)‖ ≤ |B| := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have : |1 - ε ^ 2| ≤ 1 := by
          rw [abs_le]; constructor <;> nlinarith [hε.2, hε0]
        have hb1 : |h ε| ≤ |B| := by
          have := hB ε ⟨hε0.le, hε.2⟩
          rw [Real.norm_eq_abs] at this
          exact this.trans (le_abs_self B)
        calc |1 - ε ^ 2| * |h ε| ≤ 1 * |B| := mul_le_mul this hb1 (abs_nonneg _) zero_le_one
          _ = |B| := one_mul _
      unfold prim
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, hb']
      have he : 0 ≤ ε ^ σ := Real.rpow_nonneg hε0.le _
      have t1 : ‖(ε : ℂ) ^ (s + 1)‖ * ‖((((1 - ε ^ 2) * h₁ ε : ℝ)) : ℂ)‖ ≤ ε ^ σ * |B₁| :=
        mul_le_mul hb h1 (norm_nonneg _) he
      have t2 : ‖s + 1‖ * ε ^ σ * ‖((((1 - ε ^ 2) * h ε : ℝ)) : ℂ)‖ ≤ ‖s + 1‖ * ε ^ σ * |B| :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith [t1, t2]
    rw [hsplit ε hε]
    refine (norm_add_le _ _).trans ?_
    linarith
  -- let ε → 0
  have ht : Tendsto (fun ε : ℝ => (K / σ + (|B₁| + ‖s + 1‖ * |B|)) * ε ^ σ) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 σ (Or.inr hs.le)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rw [Real.zero_rpow hs.ne'] at this
    simpa using this.const_mul (K / σ + (|B₁| + ‖s + 1‖ * |B|))
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖R‖ ≤ (K / σ + (|B₁| + ‖s + 1‖ * |B|)) * ε ^ σ := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    exact hbound ε ⟨hε.1, hε.2.le⟩
  have h0 : ‖R‖ ≤ 0 := ge_of_tendsto ht hev
  exact norm_le_zero_iff.mp h0

/-- **The Mellin recurrence for the prolate rung of index `k`.** -/
theorem mel_rung_recurrence {c : ℝ} {k : ℕ} (h : ∃ χ, Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c k χ) {s : ℂ} (hs : 0 < s.re) :
    s * (s + 1) * mel (Cvs.Prolate.EvenRungsByIndex.rung c k) s - ((s + 1) * (s + 2) - Cvs.Prolate.EvenRungsByIndex.lev c k) * mel (Cvs.Prolate.EvenRungsByIndex.rung c k) (s + 2)
      - (c : ℂ) ^ 2 * mel (Cvs.Prolate.EvenRungsByIndex.rung c k) (s + 4) = 0 := by
  obtain ⟨hd, hd₁, -, hang, -, -⟩ := Cvs.Prolate.EvenRungsByIndex.rung_spec h
  have hsub : Icc (0 : ℝ) 1 ⊆ uIcc (-1) 1 := by
    rw [uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  exact mel_recurrence (fun w hw => hd w (hsub hw)) (fun w hw => hd₁ w (hsub hw))
    (fun w hw => hang w (hsub hw)) hs

end Cvs.Prolate.Mellin.RungThreeTermRecurrence
