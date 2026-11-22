import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.FarRegionDamping
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenRootDecayOffLine
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.LawRatioRecurrence
import Cvs.Prolate.Mellin.RungThreeTermRecurrence
import Cvs.Prolate.Mellin.StepAmplification
import Cvs.Prolate.Mellin.TrueRatioDownwardStep
import Cvs.Prolate.Mellin.TrueRatioMatchesFrozen
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum
import Cvs.Upstream.ComplexArsinhStrip
import Cvs.Upstream.GammaModulusOffAxis

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two lines agree at infinity

For `s₀ = ½ + iz` and `s₀′ = ½`: as `K → ∞`, `log‖P(s_K)‖ − log‖P(s′_K)‖ → 0`, `log‖p(s_K)/(1 + r(s_K))‖ → log ½`,
and `Re(Ĝ(u_K) − ĝ(u_K)) − Re(Ĝ(u′_K) − ĝ(u′_K)) → 0`.
-/

noncomputable section

open Filter Topology Finset

namespace Cvs.Prolate.Mellin.TwoLinesAgreeModulus

open Cvs.Prolate.Mellin.RungThreeTermRecurrence Cvs.Prolate.Mellin.LawRatioRecurrence Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.TrueRatioDownwardStep Cvs.Upstream.ComplexArsinhStrip Cvs.Prolate.Mellin.WkbPhaseAntiderivative Cvs.Prolate.Mellin.FrozenForcingIdentities

/-- `log‖mg(s)‖ − log‖mg(s′)‖ = log‖Γ(s/2)‖ − log‖Γ(s′/2)‖` when `Re s = Re s′ > 0`. -/
theorem log_norm_mg_sub {c : ℝ} (hc : 0 < c) {s s' : ℂ} (hs : 0 < s.re) (hre : s.re = s'.re) :
    Real.log ‖mg c s‖ - Real.log ‖mg c s'‖
      = Real.log ‖Complex.Gamma (s / 2)‖ - Real.log ‖Complex.Gamma (s' / 2)‖ := by
  have h2c : (0 : ℝ) < 2 / c := by positivity
  have hG : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG' : Complex.Gamma (s' / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  unfold mg
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h2c,
    Complex.norm_cpow_eq_rpow_re_of_pos h2c]
  have hre2 : (s / 2).re = (s' / 2).re := by simp [hre]
  rw [hre2]
  have hp : 0 < ‖(1 / 2 : ℂ)‖ * (2 / c) ^ (s' / 2).re := by
    have : 0 < (2 / c) ^ (s' / 2).re := Real.rpow_pos_of_pos h2c _
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12]; positivity
  rw [Real.log_mul hp.ne' (norm_ne_zero_iff.mpr hG), Real.log_mul hp.ne' (norm_ne_zero_iff.mpr hG')]
  ring

/-- **The Gamma factor at infinity.** -/
theorem tendsto_log_Gamma_sub (z : ℝ) :
    Tendsto (fun K : ℕ => Real.log ‖Complex.Gamma (((1 / 2 : ℂ) + Complex.I * z + 2 * K) / 2)‖
      - Real.log ‖Complex.Gamma (((1 / 2 : ℂ) + 2 * K) / 2)‖) atTop (𝓝 0) := by
  have hb : Tendsto (fun K : ℕ => (z / 2) ^ 2 / (1 / 4 + (K : ℝ))) atTop (𝓝 0) := by
    have : Tendsto (fun K : ℕ => 1 / 4 + (K : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop this
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hx : (1 : ℝ) ≤ 1 / 4 + K := by linarith
  have e1 : ((1 / 2 : ℂ) + Complex.I * z + 2 * K) / 2 = ((1 / 4 + K : ℝ) : ℂ) + Complex.I * ((z / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : ((1 / 2 : ℂ) + 2 * K) / 2 = ((1 / 4 + K : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, Real.norm_eq_abs]
  exact Cvs.Upstream.GammaModulusOffAxis.abs_log_norm_Gamma_sub_le hx

/-- `‖ĝ′(w)‖ ≤ 13/(2‖S‖)` once `‖S‖ ≥ max(1, c)`. -/
theorem norm_gh1_le {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : |w.im| < 2 * c) (h1 : 1 ≤ ‖Sq c w‖)
    (hcs : c ≤ ‖Sq c w‖) : ‖gh1 c w‖ ≤ 13 / (2 * ‖Sq c w‖) := by
  set σ := ‖Sq c w‖
  have hσ : 0 < σ := by linarith
  have hcn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  have hS2 : σ ≤ ‖Sq c w + 2 * c‖ := by
    have := Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum.norm_add_sq_ge hc hw
    nlinarith [norm_nonneg (Sq c w + 2 * c)]
  have hnum : ‖2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w + 4 * c ^ 2‖ ≤ 13 * σ ^ 3 := by
    have t1 := norm_add_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w) (4 * (c : ℂ) ^ 2)
    have t2 := norm_add_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2) (2 * (c : ℂ) * Sq c w)
    have t3 := norm_sub_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2) (Sq c w ^ 2)
    have t4 := norm_add_le (2 * Sq c w ^ 3) (4 * (c : ℂ) * Sq c w ^ 2)
    simp only [norm_mul, norm_pow, hcn, Complex.norm_ofNat] at t1 t2 t3 t4
    have : c * σ ^ 2 ≤ σ ^ 3 := by nlinarith
    have : σ ^ 2 ≤ σ ^ 3 := by nlinarith
    have : c * σ ≤ σ ^ 3 := by nlinarith
    have : c ^ 2 ≤ σ ^ 3 := by nlinarith
    linarith
  unfold gh1
  rw [norm_div, norm_neg, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat,
    div_le_div_iff₀ (by have := lt_of_lt_of_le hσ hS2; positivity) (by positivity)]
  calc ‖2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w + 4 * c ^ 2‖ * (2 * σ)
      ≤ 13 * σ ^ 3 * (2 * σ) := by gcongr
    _ = 13 * (2 * σ ^ 3 * σ) := by ring
    _ ≤ 13 * (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) := by gcongr

/-- `ĝ` is real on the positive reals. -/
theorem im_gh_ofReal {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) : (gh c (x : ℂ)).im = 0 := by
  have hS : Sq c (x : ℂ) = ((Real.sqrt (x ^ 2 + 4 * c ^ 2) : ℝ) : ℂ) := by
    unfold Sq
    rw [show (x : ℂ) ^ 2 + 4 * (c : ℂ) ^ 2 = ((x ^ 2 + 4 * c ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact csqrt_ofReal (by positivity)
  have ha : ash ((x : ℂ) / (2 * c)) = ((Real.log (x / (2 * c) + Real.sqrt ((x / (2 * c)) ^ 2 + 1)) : ℝ) : ℂ) := by
    unfold ash
    rw [show (x : ℂ) / (2 * c) = ((x / (2 * c) : ℝ) : ℂ) by push_cast; ring,
      show ((x / (2 * c) : ℝ) : ℂ) ^ 2 + 1 = (((x / (2 * c)) ^ 2 + 1 : ℝ) : ℂ) by push_cast; ring,
      csqrt_ofReal (by positivity), ← Complex.ofReal_add, ← Complex.ofReal_log (by positivity)]
  unfold gh
  rw [ha, hS]
  set r := Real.sqrt (x ^ 2 + 4 * c ^ 2)
  simp
  rw [show (x : ℂ) / (2 * (r : ℂ) * ((r : ℂ) + 2 * (c : ℂ))) = ((x / (2 * r * (r + 2 * c)) : ℝ) : ℂ) by
    push_cast; ring]
  exact Complex.ofReal_im _

/-- On the vertical segment from `x` to `x + iz` (`x ≥ |z| + c + 1`), `‖ĝ′‖ ≤ 13/(2(x − |z|))`. -/
theorem norm_gh1_vert {c : ℝ} (hc : 0 < c) {x z : ℝ} (hz : |z| < 2 * c) (hx : |z| + c + 1 ≤ x) {w : ℂ}
    (hw : w ∈ segment ℝ (x : ℂ) ((x : ℂ) + Complex.I * z)) :
    |w.im| < 2 * c ∧ ‖gh1 c w‖ ≤ 13 / (2 * (x - |z|)) := by
  rw [segment_eq_image'] at hw
  obtain ⟨l, hl, rfl⟩ := hw
  have hre : ((x : ℂ) + l • ((x : ℂ) + Complex.I * z - x)).re = x := by simp
  have him : ((x : ℂ) + l • ((x : ℂ) + Complex.I * z - x)).im = l * z := by simp
  set w := (x : ℂ) + l • ((x : ℂ) + Complex.I * z - x)
  have hlz : |l * z| ≤ |z| := by
    rw [abs_mul, abs_of_nonneg hl.1]; nlinarith [abs_nonneg z, hl.2]
  have hw2 : |w.im| < 2 * c := by rw [him]; linarith
  refine ⟨hw2, ?_⟩
  have hσ : x - |z| ≤ ‖Sq c w‖ := by
    have h1 : (w ^ 2 + 4 * c ^ 2).re ≤ ‖w ^ 2 + 4 * (c : ℂ) ^ 2‖ := Complex.re_le_norm _
    have h2 : (w ^ 2 + 4 * (c : ℂ) ^ 2).re = w.re ^ 2 - w.im ^ 2 + 4 * c ^ 2 := by simp [sq]
    have h3 : ‖Sq c w‖ ^ 2 = ‖w ^ 2 + 4 * (c : ℂ) ^ 2‖ := by rw [← norm_pow, Sq_sq]
    rw [hre, him] at h2
    have h4 : (l * z) ^ 2 ≤ z ^ 2 := by
      have := sq_abs (l * z); have := sq_abs z; nlinarith [abs_nonneg (l * z)]
    have h5 : (x - |z|) ^ 2 ≤ ‖Sq c w‖ ^ 2 := by
      have := sq_abs z; nlinarith [abs_nonneg z]
    exact (pow_le_pow_iff_left₀ (by linarith) (norm_nonneg _) two_ne_zero).mp h5
  refine (norm_gh1_le hc hw2 (by linarith) (by linarith)).trans ?_
  apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- **The phase terms agree at infinity.** -/
theorem tendsto_phase_sub {c : ℝ} (hc : 0 < c) {z : ℝ} (hz : |z| < 2 * c) :
    Tendsto (fun K : ℕ => (Gh c ((1 / 2 + Complex.I * z) + 3 / 2 + 2 * K)
        - gh c ((1 / 2 + Complex.I * z) + 3 / 2 + 2 * K)).re
      - (Gh c ((1 / 2 : ℂ) + 3 / 2 + 2 * K) - gh c ((1 / 2 : ℂ) + 3 / 2 + 2 * K)).re) atTop (𝓝 0) := by
  -- the bound `13(|z| + |z|²)/(2(x − |z|))` with `x = 2 + 2K`
  have hb : Tendsto (fun K : ℕ => 13 * (|z| + |z| ^ 2) / (2 * ((2 + 2 * (K : ℝ)) - |z|))) atTop (𝓝 0) := by
    have : Tendsto (fun K : ℕ => 2 * ((2 + 2 * (K : ℝ)) - |z|)) atTop atTop := by
      apply Tendsto.const_mul_atTop two_pos
      apply tendsto_atTop_add_const_right
      have : Tendsto (fun K : ℕ => 2 + 2 * (K : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
      exact this
    exact tendsto_const_nhds.div_atTop this
  refine squeeze_zero_norm' ?_ hb
  have hev : ∀ᶠ K : ℕ in atTop, |z| + c + 1 ≤ 2 + 2 * (K : ℝ) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((|z| + c + 1) / 2)
    filter_upwards [this] with K hK; linarith
  filter_upwards [hev] with K hK
  set x : ℝ := 2 + 2 * (K : ℝ)
  have hxK : (1 / 2 + Complex.I * z) + 3 / 2 + 2 * (K : ℂ) = (x : ℂ) + Complex.I * z := by
    simp only [x]; push_cast; ring
  have hxK' : (1 / 2 : ℂ) + 3 / 2 + 2 * (K : ℂ) = (x : ℂ) := by simp only [x]; push_cast; ring
  rw [hxK, hxK', Real.norm_eq_abs]
  set M := 13 / (2 * (x - |z|))
  have hM0 : 0 ≤ M := by apply div_nonneg (by norm_num); linarith [abs_nonneg z]
  have hseg := fun w (hw : w ∈ segment ℝ (x : ℂ) ((x : ℂ) + Complex.I * z)) => norm_gh1_vert hc hz hK hw
  -- `ĝ` step
  have hg : ‖gh c ((x : ℂ) + Complex.I * z) - gh c (x : ℂ)‖ ≤ M * |z| := by
    have := (convex_segment (x : ℂ) ((x : ℂ) + Complex.I * z)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := gh c) (f' := gh1 c) (C := M)
      (fun w hw => (hasDerivAt_gh hc (hseg w hw).1).hasDerivWithinAt) (fun w hw => (hseg w hw).2)
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    refine this.trans (le_of_eq ?_)
    congr 1; simp [Complex.norm_real]
  -- `Ĝ` step with its linear part removed
  have hG : ‖Gh c ((x : ℂ) + Complex.I * z) - Gh c (x : ℂ) - Complex.I * z * gh c (x : ℂ)‖ ≤ M * |z| * |z| := by
    have := (convex_segment (x : ℂ) ((x : ℂ) + Complex.I * z)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun w => Gh c w - w * gh c (x : ℂ)) (f' := fun w => gh c w - gh c (x : ℂ)) (C := M * |z|)
      (fun w hw => by
        have h1 := hasDerivAt_Gh hc (hseg w hw).1
        have h2 := (hasDerivAt_id w).mul_const (gh c (x : ℂ))
        exact ((h1.sub h2).congr_deriv (by simp)).hasDerivWithinAt)
      (fun w hw => by
        have := (convex_segment (x : ℂ) ((x : ℂ) + Complex.I * z)).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := gh c) (f' := gh1 c) (C := M)
          (fun v hv => (hasDerivAt_gh hc (hseg v hv).1).hasDerivWithinAt) (fun v hv => (hseg v hv).2)
          (left_mem_segment ℝ _ _) hw
        refine this.trans ?_
        gcongr
        rw [segment_eq_image'] at hw
        obtain ⟨l, hl, rfl⟩ := hw
        simp [Complex.real_smul, abs_of_nonneg hl.1]
        nlinarith [abs_nonneg z, hl.2])
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    rw [show (x : ℂ) + Complex.I * z - x = Complex.I * z by ring, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs] at this
    refine le_of_eq_of_le ?_ this
    congr 1; ring
  have hIm := im_gh_ofReal hc (show (0 : ℝ) < x by linarith [abs_nonneg z])
  have hre : (Gh c ((x : ℂ) + Complex.I * z) - Gh c (x : ℂ)).re
      = (Gh c ((x : ℂ) + Complex.I * z) - Gh c (x : ℂ) - Complex.I * z * gh c (x : ℂ)).re := by
    simp [Complex.mul_re, hIm]
  have e : (Gh c ((x : ℂ) + Complex.I * z) - gh c ((x : ℂ) + Complex.I * z)).re - (Gh c (x : ℂ) - gh c (x : ℂ)).re
      = (Gh c ((x : ℂ) + Complex.I * z) - Gh c (x : ℂ)).re - (gh c ((x : ℂ) + Complex.I * z) - gh c (x : ℂ)).re := by
    simp only [Complex.sub_re]; ring
  rw [e, hre]
  have a1 := Complex.abs_re_le_norm (Gh c ((x : ℂ) + Complex.I * z) - Gh c (x : ℂ) - Complex.I * z * gh c (x : ℂ))
  have a2 := Complex.abs_re_le_norm (gh c ((x : ℂ) + Complex.I * z) - gh c (x : ℂ))
  calc |_ - _| ≤ |(Gh c ((x : ℂ) + Complex.I * z) - Gh c (x : ℂ) - Complex.I * z * gh c (x : ℂ)).re|
        + |(gh c ((x : ℂ) + Complex.I * z) - gh c (x : ℂ)).re| := abs_sub _ _
    _ ≤ M * |z| * |z| + M * |z| := by linarith
    _ = 13 * (|z| + |z| ^ 2) / (2 * (x - |z|)) := by simp only [M]; field_simp; ring

/-- **The Mellin factor at infinity.** -/
theorem tendsto_log_mel_sub (c : ℝ) {s₀ s₀' : ℂ} (hs : 0 < s₀.re) (hs' : 0 < s₀'.re) :
    Tendsto (fun K : ℕ => Real.log ‖mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * K)‖ - Real.log ‖mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀' + 2 * K)‖)
      atTop (𝓝 0) := by
  have hne : (Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ) ≠ 0 := by
    exact_mod_cast Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
  have hn : ‖(Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have t1 := ((Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs).norm).log hn
  have t2 := ((Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs').norm).log hn
  -- `‖s_K/s′_K‖ → 1`
  have hq : Tendsto (fun K : ℕ => (s₀ + 2 * K) / (s₀' + 2 * K)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun K : ℕ => (s₀' + 2 * (K : ℂ))⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hgrow : Tendsto (fun K : ℕ => ‖s₀' + 2 * (K : ℂ)‖) atTop atTop := by
        refine tendsto_atTop_mono (fun K => ?_) (tendsto_atTop_add_const_left _ s₀'.re
          (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
        have := Complex.re_le_norm (s₀' + 2 * (K : ℂ)); simp at this; linarith
      simp only [norm_inv]
      exact hgrow.inv_tendsto_atTop
    have e : ∀ K : ℕ, (s₀ + 2 * K) / (s₀' + 2 * K) = 1 + (s₀ - s₀') * (s₀' + 2 * (K : ℂ))⁻¹ := fun K => by
      have : s₀' + 2 * (K : ℂ) ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; have := K.cast_nonneg (α := ℝ); linarith
      field_simp; ring
    simp only [e]
    simpa using (hinv.const_mul (s₀ - s₀')).const_add 1
  have t3 := (hq.norm).log (by simp)
  simp only [norm_one, Real.log_one] at t3
  have := (t1.sub t2).sub t3
  rw [sub_self, sub_zero] at this
  refine this.congr' ?_
  filter_upwards [(Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs).eventually_ne hne,
    (Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs').eventually_ne hne] with K h1 h2
  have hs0 : s₀ + 2 * (K : ℂ) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact h1 rfl
  have hs0' : s₀' + 2 * (K : ℂ) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h2; exact h2 rfl
  have hm : mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀ + 2 * K) ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact h1 rfl
  have hm' : mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) (s₀' + 2 * K) ≠ 0 := fun h0 => by rw [h0, mul_zero] at h2; exact h2 rfl
  rw [norm_mul, norm_mul, norm_div, Real.log_mul (norm_ne_zero_iff.mpr hs0) (norm_ne_zero_iff.mpr hm),
    Real.log_mul (norm_ne_zero_iff.mpr hs0') (norm_ne_zero_iff.mpr hm'),
    Real.log_div (norm_ne_zero_iff.mpr hs0) (norm_ne_zero_iff.mpr hs0')]
  ring

/-- **The forcing boundary at infinity**: `log‖p(s_K)‖ − log‖1 + r(s_K)‖ → −log 2`. -/
theorem Hyp.tendsto_log_pp {ε c χ : ℝ} {s₀ : ℂ} (h : Hyp ε c χ s₀) :
    Tendsto (fun K : ℕ => Real.log ‖pp c χ (s₀ + 2 * K)‖ - Real.log ‖1 + rr (s₀ + 2 * K)‖) atTop
      (𝓝 (Real.log 1 - Real.log 2)) := by
  have hc := h.c_pos
  -- `ρ*(s_K) → 0`
  have hρ : Tendsto (fun K : ℕ => rhoStar c χ (s₀ + 2 * K)) atTop (𝓝 0) := by
    have hb : Tendsto (fun K : ℕ => 4 * c / (s₀.re + 2 * (K : ℝ) + 3 / 2)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_left _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
    refine squeeze_zero_norm' ?_ hb
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop c
    filter_upwards [this] with K hK
    have hl := Cvs.Prolate.Mellin.StepAmplification.hyp_line h K
    have hx : 2 * c ≤ (s₀ + 2 * (K : ℂ)).re := by simp; linarith [h.hre]
    have := Cvs.Prolate.Mellin.FrozenRootDecayOffLine.Hyp.norm_rho_le_far hl (Cvs.Prolate.Mellin.FarRegionDamping.Hyp.far_omega hl hx)
    simpa using this
  -- `r(s_K) → 1`
  have hr : Tendsto (fun K : ℕ => rr (s₀ + 2 * K)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun K : ℕ => (s₀ + 2 * (K : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hgrow : Tendsto (fun K : ℕ => ‖s₀ + 2 * (K : ℂ) + 1‖) atTop atTop := by
        refine tendsto_atTop_mono (fun K => ?_) (tendsto_atTop_add_const_left _ (s₀.re + 1)
          (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
        have := Complex.re_le_norm (s₀ + 2 * (K : ℂ) + 1); simp at this; linarith
      simp only [norm_inv]
      exact hgrow.inv_tendsto_atTop
    have e : ∀ K : ℕ, rr (s₀ + 2 * K) = 1 + (s₀ + 2 * (K : ℂ) + 1)⁻¹ := fun K => by
      have : s₀ + 2 * (K : ℂ) + 1 ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; have := K.cast_nonneg (α := ℝ); linarith [h.hre]
      unfold rr; field_simp; ring
    simp only [e]
    simpa using hinv.const_add 1
  have hp : Tendsto (fun K : ℕ => pp c χ (s₀ + 2 * K)) atTop (𝓝 1) := by
    have := (hr.mul (hρ.pow 2)).const_add 1
    simpa [pp] using this
  have h1 := (hp.norm).log (by simp)
  have h2 := ((hr.const_add 1).norm).log (by norm_num)
  have := h1.sub h2
  have e2 : ‖(1 : ℂ) + 1‖ = 2 := by norm_num
  simpa [e2] using this

/-- **The two lines agree at infinity.** -/
theorem tendsto_TK_sub {ε c : ℝ} {z : ℝ} (h : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + Complex.I * z))
    (h' : Hyp ε c (Cvs.Prolate.EvenRungsByIndex.lev c 0) (1 / 2 : ℂ)) :
    Tendsto (fun K : ℕ =>
      (Real.log ‖Pk c ((1 / 2 : ℂ) + Complex.I * z) K‖
        + 1 / 2 * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 + Complex.I * z) + 2 * K)‖
          - Real.log ‖1 + rr ((1 / 2 + Complex.I * z) + 2 * K)‖)
        - 1 / 2 * (Gh c ((1 / 2 + Complex.I * z) + 3 / 2 + 2 * K) - gh c ((1 / 2 + Complex.I * z) + 3 / 2 + 2 * K)).re)
      - (Real.log ‖Pk c (1 / 2 : ℂ) K‖
        + 1 / 2 * (Real.log ‖pp c (Cvs.Prolate.EvenRungsByIndex.lev c 0) ((1 / 2 : ℂ) + 2 * K)‖ - Real.log ‖1 + rr ((1 / 2 : ℂ) + 2 * K)‖)
        - 1 / 2 * (Gh c ((1 / 2 : ℂ) + 3 / 2 + 2 * K) - gh c ((1 / 2 : ℂ) + 3 / 2 + 2 * K)).re)) atTop (𝓝 0) := by
  have hc := h.c_pos
  have hz : |z| < 2 * c := by
    have := h.him; simp at this; have := h.hε; nlinarith
  have hs : 0 < ((1 / 2 : ℂ) + Complex.I * z).re := by simp
  have hs' : 0 < (1 / 2 : ℂ).re := by norm_num
  -- the `P` part
  have tP : Tendsto (fun K : ℕ => Real.log ‖Pk c ((1 / 2 : ℂ) + Complex.I * z) K‖ - Real.log ‖Pk c (1 / 2 : ℂ) K‖)
      atTop (𝓝 0) := by
    have t1 := tendsto_log_mel_sub c hs hs'
    have t2 := tendsto_log_Gamma_sub z
    have := t1.sub t2
    rw [sub_zero] at this
    have hne : (Cvs.Prolate.EvenRungsByIndex.rung c 0 1 : ℂ) ≠ 0 := by
      exact_mod_cast Cvs.Prolate.EvenRungsByIndex.rung_one_ne_zero (Cvs.Prolate.EvenRungsByIndex.exists_isLevelIdx_zero c)
    refine this.congr' ?_
    filter_upwards [(Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs).eventually_ne hne,
      (Cvs.Prolate.Mellin.TrueRatioMatchesFrozen.tendsto_mul_mel c hs').eventually_ne hne] with K h1 h2
    have hm1 : mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + Complex.I * z + 2 * K) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h1; exact h1 rfl
    have hm2 : mel (Cvs.Prolate.EvenRungsByIndex.rung c 0) ((1 / 2 : ℂ) + 2 * K) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h2; exact h2 rfl
    have hg1 := mg_ne_zero hc (s := (1 / 2 : ℂ) + Complex.I * z + 2 * K) (by simp; positivity)
    have hg2 := mg_ne_zero hc (s := (1 / 2 : ℂ) + 2 * K) (by simp; positivity)
    have hm := log_norm_mg_sub hc (s := (1 / 2 : ℂ) + Complex.I * z + 2 * K) (s' := (1 / 2 : ℂ) + 2 * K)
      (by simp; positivity) (by simp)
    unfold Pk lawRatio
    rw [norm_div, norm_div, Real.log_div (norm_ne_zero_iff.mpr hm1) (norm_ne_zero_iff.mpr hg1),
      Real.log_div (norm_ne_zero_iff.mpr hm2) (norm_ne_zero_iff.mpr hg2)]
    linarith
  have tp1 := Hyp.tendsto_log_pp h
  have tp2 := Hyp.tendsto_log_pp h'
  have tph := tendsto_phase_sub hc hz
  have := (tP.add ((tp1.sub tp2).const_mul (1 / 2))).sub (tph.const_mul (1 / 2))
  simp only [sub_self, mul_zero, add_zero, sub_zero] at this
  refine this.congr fun K => ?_
  ring

end Cvs.Prolate.Mellin.TwoLinesAgreeModulus
