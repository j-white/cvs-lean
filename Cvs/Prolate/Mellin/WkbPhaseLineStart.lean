import Mathlib
import Cvs.Prolate.Mellin.ForcingSmallBound
import Cvs.Prolate.Mellin.ForcingUnifiedSizes
import Cvs.Prolate.Mellin.FrozenForcingIdentities
import Cvs.Prolate.Mellin.FrozenRootCanonicalLog
import Cvs.Prolate.Mellin.FrozenRootErrorIdentity
import Cvs.Prolate.Mellin.FrozenRootSizeBounds
import Cvs.Prolate.Mellin.UniformRootBounds
import Cvs.Prolate.Mellin.WkbPhaseAntiderivative
import Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum
import Cvs.Upstream.ComplexArsinhStrip

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The WKB phase at the start of the line

With `a = √(3ε)c` and `G₁ = 1/(2c) + 1/a + 1/(4ca) + 1/(2a²) + c/a³`: `‖ĝ′‖ ≤ G₁` on `|Im u| ≤ (2−ε)c`, and for
`|z| ≤ (2−ε)c`, `sin θ = z/(2c)`:
`|½ Re(Ĝ − ĝ)(2 + iz) − ½ Re(Ĝ − ĝ)(2) − (c(θ sin θ + cos θ − 1) − ¼ log((1 + cos θ)/2))| ≤ 6G₁`.
-/

noncomputable section

open Complex

namespace Cvs.Prolate.Mellin.WkbPhaseLineStart

open Cvs.Prolate.Mellin.WkbPhaseAntiderivative

/-- The derivative budget. -/
def G1 (ε c : ℝ) : ℝ :=
  1 / (2 * c) + 1 / (Real.sqrt (3 * ε) * c) + 1 / (4 * c * (Real.sqrt (3 * ε) * c))
    + 1 / (2 * (Real.sqrt (3 * ε) * c) ^ 2) + c / (Real.sqrt (3 * ε) * c) ^ 3

variable {ε c : ℝ}

/-- **`‖ĝ′‖ ≤ G₁`** on the region. -/
theorem norm_gh1_region (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 1 ≤ c) {w : ℂ} (hy : |w.im| ≤ (2 - ε) * c) :
    ‖gh1 c w‖ ≤ G1 ε c := by
  have hc0 : 0 < c := by linarith
  have hw : |w.im| < 2 * c := by nlinarith
  set a := Real.sqrt (3 * ε) * c
  have ha : 0 < a := by have : 0 < Real.sqrt (3 * ε) := Real.sqrt_pos.mpr (by linarith); positivity
  have hσ2 := Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum.norm_Sq_sq_ge hε hε1 hc0 hy
  set σ := ‖Sq c w‖
  have hsq3 : Real.sqrt (3 * ε) ^ 2 = 3 * ε := Real.sq_sqrt (by linarith)
  have hσa : a ≤ σ := by
    have : a ^ 2 ≤ σ ^ 2 := by simp only [a]; rw [mul_pow, hsq3]; nlinarith [sq_nonneg w.re]
    exact (pow_le_pow_iff_left₀ ha.le (norm_nonneg _) two_ne_zero).mp this
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  have hcn : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_of_nonneg hc0.le]
  have hS2 : σ ^ 2 + 4 * c ^ 2 ≤ ‖Sq c w + 2 * c‖ ^ 2 := Cvs.Prolate.Mellin.WkbPhaseTrapezoidSum.norm_add_sq_ge hc0 hw
  have hD1 : σ ≤ ‖Sq c w + 2 * c‖ := by nlinarith [norm_nonneg (Sq c w + 2 * c)]
  have hD2 : 2 * c ≤ ‖Sq c w + 2 * c‖ := by nlinarith [norm_nonneg (Sq c w + 2 * c)]
  have hnum : ‖2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w + 4 * c ^ 2‖
      ≤ 2 * σ ^ 3 + 4 * c * σ ^ 2 + σ ^ 2 + 2 * c * σ + 4 * c ^ 2 := by
    have t1 := norm_add_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w) (4 * (c : ℂ) ^ 2)
    have t2 := norm_add_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2) (2 * (c : ℂ) * Sq c w)
    have t3 := norm_sub_le (2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2) (Sq c w ^ 2)
    have t4 := norm_add_le (2 * Sq c w ^ 3) (4 * (c : ℂ) * Sq c w ^ 2)
    simp only [norm_mul, norm_pow, hcn, Complex.norm_ofNat] at t1 t2 t3 t4
    linarith
  unfold gh1
  rw [norm_div, norm_neg, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
  have hden : 0 < 2 * σ ^ 3 * ‖Sq c w + 2 * c‖ := by have := lt_of_lt_of_le hσ hD1; positivity
  calc ‖2 * Sq c w ^ 3 + 4 * c * Sq c w ^ 2 - Sq c w ^ 2 + 2 * c * Sq c w + 4 * c ^ 2‖ / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖)
      ≤ (2 * σ ^ 3 + 4 * c * σ ^ 2 + σ ^ 2 + 2 * c * σ + 4 * c ^ 2) / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) := by gcongr
    _ = 2 * σ ^ 3 / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) + 4 * c * σ ^ 2 / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖)
        + σ ^ 2 / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) + 2 * c * σ / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖)
        + 4 * c ^ 2 / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) := by ring
    _ ≤ 1 / (2 * c) + 1 / a + 1 / (4 * c * a) + 1 / (2 * a ^ 2) + c / a ^ 3 := by
        have b1 : 2 * σ ^ 3 / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) ≤ 1 / (2 * c) := by
          rw [div_le_div_iff₀ hden (by positivity)]; nlinarith [pow_pos hσ 3]
        have b2 : 4 * c * σ ^ 2 / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) ≤ 1 / a := by
          rw [div_le_div_iff₀ hden ha]
          have : 4 * c * σ ^ 2 * a ≤ 4 * c * σ ^ 2 * σ := by gcongr
          nlinarith [pow_pos hσ 2, mul_le_mul_of_nonneg_left hD2 (show 0 ≤ σ ^ 3 by positivity)]
        have b3 : σ ^ 2 / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) ≤ 1 / (4 * c * a) := by
          rw [div_le_div_iff₀ hden (by positivity)]
          have : σ ^ 2 * (4 * c * a) ≤ σ ^ 2 * (4 * c * σ) := by gcongr
          nlinarith [mul_le_mul_of_nonneg_left hD2 (show 0 ≤ 2 * σ ^ 3 by positivity)]
        have b4 : 2 * c * σ / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) ≤ 1 / (2 * a ^ 2) := by
          rw [div_le_div_iff₀ hden (by positivity)]
          have : 2 * c * σ * (2 * a ^ 2) ≤ 2 * c * σ * (2 * σ ^ 2) := by gcongr
          nlinarith [mul_le_mul_of_nonneg_left hD2 (show 0 ≤ 2 * σ ^ 3 by positivity)]
        have b5 : 4 * c ^ 2 / (2 * σ ^ 3 * ‖Sq c w + 2 * c‖) ≤ c / a ^ 3 := by
          rw [div_le_div_iff₀ hden (by positivity)]
          have : 4 * c ^ 2 * a ^ 3 ≤ 4 * c ^ 2 * σ ^ 3 := by gcongr
          nlinarith [mul_le_mul_of_nonneg_left hD2 (show 0 ≤ 2 * σ ^ 3 * c by positivity)]
        linarith
    _ = G1 ε c := by unfold G1; rfl

/-- Taylor along the horizontal segment from `iz` to `iz + 2`. -/
theorem taylor_start (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 1 ≤ c) {z : ℝ} (hz : |z| ≤ (2 - ε) * c) :
    ‖Gh c (I * z + 2) - Gh c (I * z) - 2 * gh c (I * z)‖ ≤ 4 * G1 ε c
      ∧ ‖gh c (I * z + 2) - gh c (I * z)‖ ≤ 2 * G1 ε c := by
  have hc0 : 0 < c := by linarith
  have hseg : ∀ w ∈ segment ℝ (I * z) (I * z + 2), |w.im| ≤ (2 - ε) * c ∧ ‖w - I * z‖ ≤ 2 := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨l, hl, rfl⟩ := hw
    simp only [add_sub_cancel_left]
    constructor
    · simp; exact hz
    · simp [Complex.real_smul, abs_of_nonneg hl.1]; linarith [hl.2]
  have hstrip : ∀ w ∈ segment ℝ (I * z) (I * z + 2), |w.im| < 2 * c := fun w hw => by
    have := (hseg w hw).1; nlinarith
  have hg := fun w (hw : w ∈ segment ℝ (I * z) (I * z + 2)) =>
    (convex_segment (I * z) (I * z + 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := gh c) (f' := gh1 c) (C := G1 ε c)
      (fun v hv => (hasDerivAt_gh hc0 (hstrip v hv)).hasDerivWithinAt)
      (fun v hv => norm_gh1_region hε hε1 hc (hseg v hv).1) (left_mem_segment ℝ _ _) hw
  have hG1 : 0 ≤ G1 ε c := (norm_nonneg _).trans (norm_gh1_region hε hε1 hc (w := I * z) (by simpa using hz))
  constructor
  · have := (convex_segment (I * z) (I * z + 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun w => Gh c w - w * gh c (I * z)) (f' := fun w => gh c w - gh c (I * z)) (C := 2 * G1 ε c)
      (fun w hw => by
        have h1 := hasDerivAt_Gh hc0 (hstrip w hw)
        have h2 := (hasDerivAt_id w).mul_const (gh c (I * z))
        exact ((h1.sub h2).congr_deriv (by simp)).hasDerivWithinAt)
      (fun w hw => (hg w hw).trans (by have := (hseg w hw).2; nlinarith))
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    rw [show I * (z : ℂ) + 2 - I * z = 2 by ring, Complex.norm_ofNat] at this
    refine le_of_eq_of_le ?_ (this.trans (by linarith))
    congr 1; ring
  · have := hg (I * z + 2) (right_mem_segment ℝ _ _)
    rw [show I * (z : ℂ) + 2 - I * z = 2 by ring, Complex.norm_ofNat] at this
    linarith

/-- **The phase at the start of the line.** -/
theorem phase_start (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 1 ≤ c) {z : ℝ} (hz : |z| ≤ (2 - ε) * c) :
    |1 / 2 * (Gh c ((1 / 2 + I * z) + 3 / 2) - gh c ((1 / 2 + I * z) + 3 / 2)).re
      - 1 / 2 * (Gh c ((1 / 2 : ℂ) + 3 / 2) - gh c ((1 / 2 : ℂ) + 3 / 2)).re
      - (c * (Real.arcsin (z / (2 * c)) * Real.sin (Real.arcsin (z / (2 * c))) + Real.cos (Real.arcsin (z / (2 * c))) - 1)
        - 1 / 4 * Real.log ((1 + Real.cos (Real.arcsin (z / (2 * c)))) / 2))| ≤ 6 * G1 ε c := by
  have hc0 : 0 < c := by linarith
  have hz2 : |z| < 2 * c := by nlinarith
  have hz0 : |(0 : ℝ)| ≤ (2 - ε) * c := by simp; nlinarith
  have hx : |z / (2 * c)| < 1 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * c), div_lt_one (by linarith)]; exact hz2
  have hx1 := abs_lt.mp hx
  set θ := Real.arcsin (z / (2 * c))
  have hsin : Real.sin θ = z / (2 * c) := Real.sin_arcsin (by linarith) (by linarith)
  have hcos : 0 < Real.cos θ := by
    simp only [θ]; rw [Real.cos_arcsin]; apply Real.sqrt_pos.mpr; nlinarith
  obtain ⟨t1, t2⟩ := taylor_start hε hε1 hc hz
  obtain ⟨u1, u2⟩ := taylor_start hε hε1 hc hz0
  have hG := Gh_I_mul hc0 hz2
  have hG0 := Gh_I_mul hc0 (z := 0) (by simp; linarith)
  have hr := re_gh_I_mul hc0 hz2
  have hr0 := re_gh_I_mul hc0 (z := 0) (by simp; linarith)
  simp only [Complex.ofReal_zero, mul_zero, zero_add, zero_div, Real.arcsin_zero, Real.cos_zero] at hG0 hr0 u1 u2
  have e1 : (1 / 2 + I * z) + 3 / 2 = I * (z : ℂ) + 2 := by ring
  have e2 : (1 / 2 : ℂ) + 3 / 2 = 2 := by norm_num
  rw [e1, e2]
  -- real parts
  have r1 : |(Gh c (I * z + 2) - gh c (I * z + 2)).re - (Gh c (I * z)).re| ≤ 6 * G1 ε c := by
    have : (Gh c (I * z + 2) - gh c (I * z + 2)).re - (Gh c (I * z)).re
        = (Gh c (I * z + 2) - Gh c (I * z) - 2 * gh c (I * z)).re - (gh c (I * z + 2) - gh c (I * z)).re
          + (gh c (I * z)).re := by simp only [Complex.sub_re, Complex.mul_re]; norm_num; ring
    rw [this, hr, add_zero]
    have a1 := Complex.abs_re_le_norm (Gh c (I * z + 2) - Gh c (I * z) - 2 * gh c (I * z))
    have a2 := Complex.abs_re_le_norm (gh c (I * z + 2) - gh c (I * z))
    calc |_ - _| ≤ |(Gh c (I * z + 2) - Gh c (I * z) - 2 * gh c (I * z)).re|
          + |(gh c (I * z + 2) - gh c (I * z)).re| := abs_sub _ _
      _ ≤ 6 * G1 ε c := by linarith
  have r0 : |(Gh c ((0 : ℂ) + 2) - gh c ((0 : ℂ) + 2)).re - (Gh c 0).re| ≤ 6 * G1 ε c := by
    have : (Gh c ((0 : ℂ) + 2) - gh c ((0 : ℂ) + 2)).re - (Gh c 0).re
        = (Gh c ((0 : ℂ) + 2) - Gh c 0 - 2 * gh c 0).re - (gh c ((0 : ℂ) + 2) - gh c 0).re
          + (gh c 0).re := by simp only [Complex.sub_re, Complex.mul_re]; norm_num; ring
    rw [this, hr0, add_zero]
    have a1 := Complex.abs_re_le_norm (Gh c ((0 : ℂ) + 2) - Gh c 0 - 2 * gh c 0)
    have a2 := Complex.abs_re_le_norm (gh c ((0 : ℂ) + 2) - gh c 0)
    calc |_ - _| ≤ |(Gh c ((0 : ℂ) + 2) - Gh c 0 - 2 * gh c 0).re| + |(gh c ((0 : ℂ) + 2) - gh c 0).re| :=
          abs_sub _ _
      _ ≤ 6 * G1 ε c := by simp only [zero_add] at u1 u2 a1 a2 ⊢; linarith
  rw [zero_add] at r0
  rw [hG, Complex.ofReal_re] at r1
  rw [hG0, Complex.ofReal_re] at r0
  -- the closed-form difference
  have hlog : Real.log (2 * c * (1 + Real.cos θ)) - Real.log (2 * c * (1 + 1)) = Real.log ((1 + Real.cos θ) / 2) := by
    rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp; ring
  rw [hsin]
  rw [abs_le] at r1 r0 ⊢
  constructor <;> nlinarith [r1.1, r1.2, r0.1, r0.2, hlog]

/-- The start-of-line budget `γ` for `‖g(s₀) + iθ‖`. -/
def gam (ε c : ℝ) : ℝ := 80 / ((ε / 4) ^ 5 * c) + 2 * G1 ε c + 1 / (2 * c * ε)

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Upstream.ComplexArsinhStrip Cvs.Prolate.Mellin.FrozenRootCanonicalLog Cvs.Prolate.Mellin.FrozenForcingIdentities in
/-- **`g(½ + iz) ≈ −iθ`.** -/
theorem norm_gL_add_le {χ : ℝ} (hε4 : ε ≤ 1 / 4) {z : ℝ} (h : Hyp ε c χ ((1 / 2 : ℂ) + I * z)) :
    ‖gL c χ ((1 / 2 : ℂ) + I * z) + I * Real.arcsin (z / (2 * c))‖ ≤ gam ε c := by
  have hε := h.hε
  have hc := h.c_pos
  have hc1 : 1 ≤ c := by linarith [h.c_ge]
  have hz : |z| ≤ (2 - ε) * c := by have := h.him; simpa using this
  have hz2 : |z| < 2 * c := by nlinarith
  have hx : |z / (2 * c)| < 1 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * c), div_lt_one (by linarith)]; exact hz2
  have hx1 := abs_lt.mp hx
  set θ := Real.arcsin (z / (2 * c))
  have hsin : Real.sin θ = z / (2 * c) := Real.sin_arcsin (by linarith) (by linarith)
  have hθ : |θ| < Real.pi / 2 := by
    rw [abs_lt]; exact ⟨Real.neg_pi_div_two_lt_arcsin.mpr hx1.1, Real.arcsin_lt_pi_div_two.mpr hx1.2⟩
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩
  -- `cos θ ≥ ε/2`
  have hcosε : ε / 2 ≤ Real.cos θ := by
    have h1 : Real.cos θ ^ 2 = 1 - (z / (2 * c)) ^ 2 := by rw [← hsin]; linarith [Real.sin_sq_add_cos_sq θ]
    have h2 : (z / (2 * c)) ^ 2 ≤ (1 - ε / 2) ^ 2 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have := sq_abs z; have : |z| ^ 2 ≤ ((2 - ε) * c) ^ 2 := pow_le_pow_left₀ (abs_nonneg z) hz 2
      nlinarith
    have : (ε / 2) ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith [h.hε1]
    exact (pow_le_pow_iff_left₀ (by positivity) hcos.le two_ne_zero).mp this
  -- the three pieces
  have p1 := Hyp.norm_gL_sub_gh_le h hε4
  have hu : (1 / 2 : ℂ) + I * z + 3 / 2 = I * z + 2 := by ring
  rw [hu] at p1
  have hU : 2 ≤ ‖I * (z : ℂ) + 2‖ := by
    have := Complex.re_le_norm (I * (z : ℂ) + 2); simp at this; linarith
  have p1' : ‖gL c χ ((1 / 2 : ℂ) + I * z) - gh c (I * z + 2)‖ ≤ 80 / ((ε / 4) ^ 5 * c) := by
    refine p1.trans ?_
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 * c ≤ ‖I * (z : ℂ) + 2‖ * (‖I * (z : ℂ) + 2‖ + c) := by nlinarith
    nlinarith [pow_pos (show (0 : ℝ) < ε / 4 by positivity) 5]
  have p2 := (taylor_start hε h.hε1 hc1 hz).2
  have p3 : ‖gh c (I * z) + I * θ‖ ≤ 1 / (2 * c * ε) := by
    have hw : I * (z : ℂ) / (2 * c) = I * (Real.sin θ : ℂ) := by
      rw [hsin]; push_cast; field_simp
    unfold gh
    rw [hw, ash_I_mul_sin hθ, Sq_I_mul hc hz2]
    set r := 2 * c * Real.cos θ
    have e : -(I * (θ : ℂ)) - I * z / (2 * (r : ℂ) * ((r : ℂ) + 2 * c)) + I * θ
        = -(I * ((z / (2 * r * (r + 2 * c)) : ℝ) : ℂ)) := by push_cast; ring
    rw [e, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * r * (r + 2 * c))]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hr0 : 0 < r := by positivity
    have hrc : c * ε ≤ r := by simp only [r]; nlinarith
    have k1 : |z| * (2 * c * ε) ≤ 2 * c * (2 * c * ε) := mul_le_mul_of_nonneg_right hz2.le (by positivity)
    have k2 : 2 * c * (2 * c * ε) ≤ 2 * r * (r + 2 * c) := by nlinarith
    linarith
  have e : gL c χ ((1 / 2 : ℂ) + I * z) + I * θ
      = (gL c χ ((1 / 2 : ℂ) + I * z) - gh c (I * z + 2)) + (gh c (I * z + 2) - gh c (I * z))
        + (gh c (I * z) + I * θ) := by ring
  rw [e]
  have n1 := norm_add_le ((gL c χ ((1 / 2 : ℂ) + I * z) - gh c (I * z + 2)) + (gh c (I * z + 2) - gh c (I * z)))
    (gh c (I * z) + I * θ)
  have n2 := norm_add_le (gL c χ ((1 / 2 : ℂ) + I * z) - gh c (I * z + 2)) (gh c (I * z + 2) - gh c (I * z))
  unfold gam
  linarith

open Cvs.Prolate.Mellin.FrozenRootErrorIdentity Cvs.Prolate.Mellin.UniformRootBounds Cvs.Prolate.Mellin.FrozenRootCanonicalLog Cvs.Prolate.Mellin.FrozenForcingIdentities in
/-- **The forcing boundary at the start**: `log‖p(s₀)‖ − log‖1 + r(s₀)‖ = log cos θ + O((γ + 1/c)/ε)`. -/
theorem log_pp_start {χ : ℝ} (hε4 : ε ≤ 1 / 4) {z : ℝ} (h : Hyp ε c χ ((1 / 2 : ℂ) + I * z))
    (hγ : 2 * gam ε c ≤ 1) (hη : 2 * gam ε c + 2 / c ≤ ε / 4) :
    |Real.log ‖pp c χ ((1 / 2 : ℂ) + I * z)‖ - Real.log ‖1 + rr ((1 / 2 : ℂ) + I * z)‖
      - Real.log (Real.cos (Real.arcsin (z / (2 * c))))| ≤ 3 * (2 * gam ε c + 2 / c) / ε := by
  have hε := h.hε
  have hc := h.c_pos
  have hz : |z| ≤ (2 - ε) * c := by have := h.him; simpa using this
  have hz2 : |z| < 2 * c := by nlinarith
  have hx : |z / (2 * c)| < 1 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * c), div_lt_one (by linarith)]; exact hz2
  have hx1 := abs_lt.mp hx
  set s₀ : ℂ := (1 / 2 : ℂ) + I * z
  set θ := Real.arcsin (z / (2 * c))
  have hsin : Real.sin θ = z / (2 * c) := Real.sin_arcsin (by linarith) (by linarith)
  have hθ : |θ| < Real.pi / 2 := by
    rw [abs_lt]; exact ⟨Real.neg_pi_div_two_lt_arcsin.mpr hx1.1, Real.arcsin_lt_pi_div_two.mpr hx1.2⟩
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩
  have hcosε : ε / 2 ≤ Real.cos θ := by
    have h1 : Real.cos θ ^ 2 = 1 - (z / (2 * c)) ^ 2 := by rw [← hsin]; linarith [Real.sin_sq_add_cos_sq θ]
    have h2 : (z / (2 * c)) ^ 2 ≤ (1 - ε / 2) ^ 2 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      have : |z| ^ 2 ≤ ((2 - ε) * c) ^ 2 := pow_le_pow_left₀ (abs_nonneg z) hz 2
      have := sq_abs z; nlinarith
    have : (ε / 2) ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith [h.hε1]
    exact (pow_le_pow_iff_left₀ (by positivity) hcos.le two_ne_zero).mp this
  -- the target value `b = cos θ e^{−iθ}`
  set b : ℂ := ((Real.cos θ : ℝ) : ℂ) * Complex.exp (-(I * θ))
  have hb : ‖b‖ = Real.cos θ := by
    simp only [b]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcos.le]
    rw [show -(I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hb2 : b = (1 + Complex.exp (-(2 * (I * θ)))) / 2 := by
    simp only [b]
    rw [Complex.ofReal_cos, Complex.cos, show -(2 * (I * (θ : ℂ))) = -(I * θ) + -(I * θ) by ring, Complex.exp_add]
    rw [show -(θ : ℂ) * I = -(I * θ) by ring, show (θ : ℂ) * I = I * θ by ring]
    have : Complex.exp (I * θ) * Complex.exp (-(I * θ)) = 1 := by rw [← Complex.exp_add]; simp
    linear_combination (1 / 2 : ℂ) * this
  -- `ρ² − e^{−2iθ}`
  have hexp := Hyp.exp_gL h
  have hg := norm_gL_add_le hε4 h
  set g := gL c χ s₀
  have hρ2 : ‖rhoStar c χ s₀ ^ 2 - Complex.exp (-(2 * (I * θ)))‖ ≤ 4 * gam ε c := by
    rw [← hexp, ← Complex.exp_nat_mul]
    have e : ((2 : ℕ) : ℂ) * g = -(2 * (I * θ)) + 2 * (g + I * θ) := by push_cast; ring
    rw [e, Complex.exp_add, ← mul_sub_one, norm_mul,
      show -(2 * (I * (θ : ℂ))) = ((-(2 * θ) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h2 : ‖2 * (g + I * θ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith
    refine (Complex.norm_exp_sub_one_le h2).trans ?_
    rw [norm_mul, Complex.norm_ofNat]; linarith
  -- the `r`-correction
  have hs1 := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.norm_s1_ge h
  have hs1ne := Cvs.Prolate.Mellin.ForcingSmallBound.Hyp.s1_ne h
  have hr2 := Cvs.Prolate.Mellin.ForcingUnifiedSizes.Hyp.norm_one_add_rr_ge h
  have hrne : 1 + rr s₀ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hr2; linarith
  have h1ρ := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_one_sub_rho_le h
  have hρn := Cvs.Prolate.Mellin.FrozenRootSizeBounds.Hyp.norm_rho_le h
  have hcorr : ‖(rr s₀ - 1) * (rhoStar c χ s₀ ^ 2 - 1) / (2 * (1 + rr s₀))‖ ≤ 2 / c := by
    have er : rr s₀ - 1 = 1 / (s₀ + 1) := by unfold rr; field_simp; ring
    have eρ : rhoStar c χ s₀ ^ 2 - 1 = -(1 - rhoStar c χ s₀) * (rhoStar c χ s₀ + 1) := by ring
    rw [er, eρ, norm_div, norm_mul, norm_mul, norm_neg, norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    have hp1 : ‖rhoStar c χ s₀ + 1‖ ≤ 13 / 4 := by
      have := norm_add_le (rhoStar c χ s₀) 1; rw [norm_one] at this; linarith
    rw [div_le_div_iff₀ (by positivity) hc]
    calc 1 / ‖s₀ + 1‖ * (‖1 - rhoStar c χ s₀‖ * ‖rhoStar c χ s₀ + 1‖) * c
        ≤ 1 / ‖s₀ + 1‖ * ((‖s₀ + 1‖ + 1) / c * (13 / 4)) * c := by gcongr
      _ = 13 / 4 * (1 + 1 / ‖s₀ + 1‖) := by field_simp
      _ ≤ 13 / 4 * (1 + 2 / 3) := by
          have : 1 / ‖s₀ + 1‖ ≤ 2 / 3 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
          linarith
      _ ≤ 2 * (2 * ‖1 + rr s₀‖) := by nlinarith
  -- `X − b`
  set X := pp c χ s₀ / (1 + rr s₀)
  have hXb : X - b = (rr s₀ - 1) * (rhoStar c χ s₀ ^ 2 - 1) / (2 * (1 + rr s₀))
      + (rhoStar c χ s₀ ^ 2 - Complex.exp (-(2 * (I * θ)))) / 2 := by
    simp only [X]; rw [hb2]; unfold pp; field_simp; ring
  have hXb' : ‖X - b‖ ≤ 2 * gam ε c + 2 / c := by
    rw [hXb]
    have := norm_add_le ((rr s₀ - 1) * (rhoStar c χ s₀ ^ 2 - 1) / (2 * (1 + rr s₀)))
      ((rhoStar c χ s₀ ^ 2 - Complex.exp (-(2 * (I * θ)))) / 2)
    rw [norm_div (rhoStar c χ s₀ ^ 2 - Complex.exp (-(2 * (I * θ)))) 2, Complex.norm_ofNat] at this
    linarith
  have hbne : b ≠ 0 := fun h0 => by rw [h0, norm_zero] at hb; linarith
  have hq : ‖(X - b) / b‖ ≤ (2 * gam ε c + 2 / c) / (ε / 2) := by
    rw [norm_div, hb]
    calc ‖X - b‖ / Real.cos θ ≤ (2 * gam ε c + 2 / c) / Real.cos θ := by gcongr
      _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by have := (norm_nonneg _).trans hXb'; linarith) (by positivity) hcosε
  have hq2 : ‖(X - b) / b‖ ≤ 1 / 2 := hq.trans (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hl := Cvs.Prolate.Mellin.FrozenForcingIdentities.abs_log_norm_one_add_le hq2
  have e : 1 + (X - b) / b = X / b := by field_simp; ring
  rw [e, norm_div, hb] at hl
  have hX0 : X ≠ 0 := fun h0 => by
    rw [h0, norm_zero, zero_div, Real.log_zero] at hl; simp at hl
    have : (3 / 2 : ℝ) * ‖(X - b) / b‖ ≤ 3 / 4 := by linarith
    rw [h0, zero_sub, neg_div, div_self hbne, norm_neg, norm_one] at this; linarith
  have hpp : pp c χ s₀ ≠ 0 := fun h0 => hX0 (by simp only [X]; rw [h0, zero_div])
  rw [Real.log_div (norm_ne_zero_iff.mpr hX0) hcos.ne'] at hl
  have eX : Real.log ‖X‖ = Real.log ‖pp c χ s₀‖ - Real.log ‖1 + rr s₀‖ := by
    simp only [X]; rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hpp) (norm_ne_zero_iff.mpr hrne)]
  rw [← eX]
  refine hl.trans ?_
  calc 3 / 2 * ‖(X - b) / b‖ ≤ 3 / 2 * ((2 * gam ε c + 2 / c) / (ε / 2)) := by gcongr
    _ = 3 * (2 * gam ε c + 2 / c) / ε := by field_simp

end Cvs.Prolate.Mellin.WkbPhaseLineStart
