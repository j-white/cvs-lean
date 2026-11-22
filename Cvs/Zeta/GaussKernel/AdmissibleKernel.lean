import Mathlib
import Cvs.Zeta.GaussKernel.FiniteBlockDivergence
import Cvs.Zeta.GaussKernel.OffsetKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The admissible kernel

`gaussKernel` is a sum of two Gaussians, and a sum of two Gaussians is not a square — so it is
the zero side of the *explicit formula*, not a Weil test.
-/

open Complex Real

namespace Cvs.Zeta.GaussKernel.AdmissibleKernel

/-!
## Is this kernel a Weil test?

`weilSummand ĝ ρ` is `Re(ĝ(w_ρ) · conj(ĝ(w_{conj ρ})))` — bilinear in `ĝ`, a square.
-/

/-- The two-bump amplitude: half the exponent, so that its square is a candidate
Weil kernel. -/
noncomputable def gaussAmp (lam a : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2 / 2)
    + Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2 / 2)

/-- **The square of the amplitude is not `gaussKernel`.** It is `gaussKernel` plus a third bump,
centred at `0`: `gaussAmp² = gaussKernel + 2 e^{-lam(w² + a²)}`. -/
theorem gaussAmp_sq (lam a : ℝ) (w : ℂ) :
    gaussAmp lam a w ^ 2
      = gaussKernel lam a w
        + 2 * Complex.exp (-(lam : ℂ) * (w ^ 2 + (a : ℂ) ^ 2)) := by
  have hA : Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2 / 2)
      * Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2 / 2)
      = Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hB : Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2 / 2)
      * Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2 / 2)
      = Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hAB : Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2 / 2)
      * Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2 / 2)
      = Complex.exp (-(lam : ℂ) * (w ^ 2 + (a : ℂ) ^ 2)) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc gaussAmp lam a w ^ 2
      = Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2 / 2)
            * Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2 / 2)
          + 2 * (Complex.exp (-(lam : ℂ) * (w - (a : ℂ)) ^ 2 / 2)
            * Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2 / 2))
          + Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2 / 2)
            * Complex.exp (-(lam : ℂ) * (w + (a : ℂ)) ^ 2 / 2) := by
        simp only [gaussAmp]; ring
    _ = gaussKernel lam a w
          + 2 * Complex.exp (-(lam : ℂ) * (w ^ 2 + (a : ℂ) ^ 2)) := by
        rw [hA, hB, hAB]; simp only [gaussKernel]; ring

/-- The cross term at an off-line point, in closed form.  Its rate is
`δ² - γ² - a²`. -/
theorem re_cross_summand (lam a γ δ : ℝ) :
    (Complex.exp (-(lam : ℂ)
        * (((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2 + (a : ℂ) ^ 2))).re
      = Real.exp (lam * (δ ^ 2 - γ ^ 2 - a ^ 2)) * Real.cos (2 * lam * γ * δ) := by
  rw [Complex.exp_re]
  refine congrArg₂ (· * ·) (congrArg Real.exp ?_) (congrArg Real.cos ?_)
  · simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  · simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring

/-- **The cross term's rate is `δ² - γ² - a²`** , strictly below the target's `δ₀² - ε²` whenever
`ε < |a|` and `δ² ≤ δ₀²` — the same smallness on `ε` the offset already required. -/
theorem cross_rate_lt {δ₀ δ γ a ε : ℝ} (hδ : δ ^ 2 ≤ δ₀ ^ 2) (hε : 0 < ε)
    (ha : ε < |a|) : δ ^ 2 - γ ^ 2 - a ^ 2 < δ₀ ^ 2 - ε ^ 2 := by
  have h1 : ε ^ 2 < a ^ 2 := by
    nlinarith [sq_abs a, abs_nonneg a]
  nlinarith [sq_nonneg γ]

/-! ## The admissible kernel, in closed form

Everything above is re-derived here on `gaussAmp²`, which is the object a Weil
test actually contributes.  The shape is unchanged — three bumps instead of two,
and the third is dominated on the same linear-in-`lam` condition as the second. -/

/-- **The admissible kernel at an off-line point.**  Three bumps, with rates
`δ²-(γ-a)²`, `δ²-(γ+a)²` and `δ²-γ²-a²`. -/
theorem re_gaussAmp_sq (lam a γ δ : ℝ) :
    (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re
      = Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2)) * Real.cos (2 * lam * (γ - a) * δ)
        + Real.exp (lam * (δ ^ 2 - (γ + a) ^ 2)) * Real.cos (2 * lam * (γ + a) * δ)
        + 2 * (Real.exp (lam * (δ ^ 2 - γ ^ 2 - a ^ 2))
            * Real.cos (2 * lam * γ * δ)) := by
  rw [gaussAmp_sq, Complex.add_re, re_gaussKernel]
  congr 1
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, re_cross_summand]
  ring

/-- The target's bound for the admissible kernel.  Both competing bumps are
dominated at a quarter each, leaving `-(E₁/2)` exactly as before. -/
theorem re_gaussAmp_sq_le_neg_half {lam a γ δ : ℝ}
    (hcos : Real.cos (2 * lam * (γ - a) * δ) = -1)
    (h2 : Real.exp (lam * (δ ^ 2 - (γ + a) ^ 2))
      < Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2)) / 4)
    (h3 : 2 * Real.exp (lam * (δ ^ 2 - γ ^ 2 - a ^ 2))
      < Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2)) / 4) :
    (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re
      ≤ -(1 / 2 * Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2))) := by
  rw [re_gaussAmp_sq, hcos]
  have e2 := Real.exp_pos (lam * (δ ^ 2 - (γ + a) ^ 2))
  have e3 := Real.exp_pos (lam * (δ ^ 2 - γ ^ 2 - a ^ 2))
  have c2 := mul_le_mul_of_nonneg_left
    (Real.cos_le_one (2 * lam * (γ + a) * δ)) e2.le
  have c3 := mul_le_mul_of_nonneg_left
    (Real.cos_le_one (2 * lam * γ * δ)) e3.le
  simp only [mul_one] at c2 c3
  linarith

/-- Comparing two exponentials at a ratio.  `exp_snd_lt_half` is the case
`K = 2`; the third bump needs `K = 8`, and the statement is the same. -/
theorem exp_ratio_lt {lam K X Y : ℝ} (hK : 0 < K)
    (h : Real.log K < lam * (X - Y)) :
    Real.exp (lam * Y) < Real.exp (lam * X) / K := by
  rw [lt_div_iff₀ hK, ← Real.exp_log hK, ← Real.exp_add]
  exact Real.exp_lt_exp.mpr (by nlinarith)

/-- Each domination condition is linear in `lam`, so it holds eventually
whenever `γ a > 0`. -/
theorem eventually_log_lt (C : ℝ) {c γ a : ℝ} (hc : 0 < c) (hγa : 0 < γ * a) :
    ∀ᶠ lam : ℝ in Filter.atTop, Real.log C < c * lam * γ * a := by
  have hpos : (0 : ℝ) < c * (γ * a) := by positivity
  have hT : Filter.Tendsto (fun lam : ℝ => lam * (c * (γ * a)))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hpos (Filter.tendsto_id (α := ℝ))
  filter_upwards [hT.eventually_gt_atTop (Real.log C)] with lam h
  have he : c * lam * γ * a = lam * (c * (γ * a)) := by ring
  rw [he]; exact h

/-- All three of the admissible kernel's conditions hold together at arbitrarily
large `lam`: the cosine frequently, the two dominations eventually. -/
theorem frequently_amp_conditions {γ δ a : ℝ} (hδ : δ ≠ 0) (hu : γ - a ≠ 0)
    (hγa : 0 < γ * a) :
    ∃ᶠ lam : ℝ in Filter.atTop,
      Real.cos (2 * lam * (γ - a) * δ) = -1
        ∧ Real.log 4 < 4 * lam * γ * a ∧ Real.log 8 < 2 * lam * γ * a := by
  have hfreq : ∃ᶠ lam : ℝ in Filter.atTop,
      Real.cos (2 * lam * (γ - a) * δ) = -1 := by
    refine Filter.frequently_atTop'.mpr fun M => ?_
    obtain ⟨lam, hM, _, hc⟩ := exists_lam_cos_eq_neg_one hu hδ M
    exact ⟨lam, hM, hc⟩
  exact hfreq.and_eventually
    ((eventually_log_lt 4 (by norm_num) hγa).and
      (eventually_log_lt 8 (by norm_num) hγa))

/-- The target's bound for the admissible kernel, against the predicate
`frequently_amp_conditions` supplies. -/
theorem re_gaussAmp_sq_le_neg_half_of {lam a γ δ : ℝ}
    (h : Real.cos (2 * lam * (γ - a) * δ) = -1
      ∧ Real.log 4 < 4 * lam * γ * a ∧ Real.log 8 < 2 * lam * γ * a) :
    (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re
      ≤ -(1 / 2 * Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2))) := by
  obtain ⟨hcos, h4, h8⟩ := h
  refine re_gaussAmp_sq_le_neg_half hcos
    (exp_ratio_lt (by norm_num) (by nlinarith)) ?_
  have h3 : Real.exp (lam * (δ ^ 2 - γ ^ 2 - a ^ 2))
      < Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2)) / 8 :=
    exp_ratio_lt (by norm_num) (by nlinarith)
  linarith

/-! ## The competitor bound for the admissible kernel -/

/-- The rate a zero contributes at under the admissible kernel: the largest of
the three bumps' exponents per unit `lam`. -/
noncomputable def ampRate (a γ δ : ℝ) : ℝ :=
  max (max (δ ^ 2 - (γ - a) ^ 2) (δ ^ 2 - (γ + a) ^ 2)) (δ ^ 2 - γ ^ 2 - a ^ 2)

theorem ampRate_def (a γ δ : ℝ) :
    ampRate a γ δ
      = max (max (δ ^ 2 - (γ - a) ^ 2) (δ ^ 2 - (γ + a) ^ 2))
          (δ ^ 2 - γ ^ 2 - a ^ 2) := rfl

/-- A competitor's contribution under the admissible kernel, bounded by a single
exponential at its largest rate.  The factor `4` is three bumps with the cross
term counted twice. -/
theorem re_gaussAmp_sq_le_four_exp {lam : ℝ} (hlam : 0 ≤ lam) (a γ δ : ℝ) :
    (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re
      ≤ 4 * Real.exp (lam * ampRate a γ δ) := by
  rw [re_gaussAmp_sq, ampRate_def]
  have e1 := Real.exp_pos (lam * (δ ^ 2 - (γ - a) ^ 2))
  have e2 := Real.exp_pos (lam * (δ ^ 2 - (γ + a) ^ 2))
  have e3 := Real.exp_pos (lam * (δ ^ 2 - γ ^ 2 - a ^ 2))
  have m1 : Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2))
      ≤ Real.exp (lam * max (max (δ ^ 2 - (γ - a) ^ 2) (δ ^ 2 - (γ + a) ^ 2))
        (δ ^ 2 - γ ^ 2 - a ^ 2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((le_max_left _ _).trans (le_max_left _ _)) hlam)
  have m2 : Real.exp (lam * (δ ^ 2 - (γ + a) ^ 2))
      ≤ Real.exp (lam * max (max (δ ^ 2 - (γ - a) ^ 2) (δ ^ 2 - (γ + a) ^ 2))
        (δ ^ 2 - γ ^ 2 - a ^ 2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((le_max_right _ _).trans (le_max_left _ _)) hlam)
  have m3 : Real.exp (lam * (δ ^ 2 - γ ^ 2 - a ^ 2))
      ≤ Real.exp (lam * max (max (δ ^ 2 - (γ - a) ^ 2) (δ ^ 2 - (γ + a) ^ 2))
        (δ ^ 2 - γ ^ 2 - a ^ 2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_right _ _) hlam)
  have c1 := mul_le_mul_of_nonneg_left
    (Real.cos_le_one (2 * lam * (γ - a) * δ)) e1.le
  have c2 := mul_le_mul_of_nonneg_left
    (Real.cos_le_one (2 * lam * (γ + a) * δ)) e2.le
  have c3 := mul_le_mul_of_nonneg_left (Real.cos_le_one (2 * lam * γ * δ)) e3.le
  simp only [mul_one] at c1 c2 c3
  linarith

/-- The three envelopes bound the contribution in absolute value — the form the
tail estimate needs. -/
theorem abs_re_gaussAmp_sq_le (lam a γ δ : ℝ) :
    |(gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re|
      ≤ Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2))
        + Real.exp (lam * (δ ^ 2 - (γ + a) ^ 2))
        + 2 * Real.exp (lam * (δ ^ 2 - γ ^ 2 - a ^ 2)) := by
  rw [re_gaussAmp_sq, abs_le]
  have e1 := Real.exp_pos (lam * (δ ^ 2 - (γ - a) ^ 2))
  have e2 := Real.exp_pos (lam * (δ ^ 2 - (γ + a) ^ 2))
  have e3 := Real.exp_pos (lam * (δ ^ 2 - γ ^ 2 - a ^ 2))
  constructor <;>
    nlinarith [e1, e2, e3, Real.neg_one_le_cos (2 * lam * (γ - a) * δ),
      Real.cos_le_one (2 * lam * (γ - a) * δ),
      Real.neg_one_le_cos (2 * lam * (γ + a) * δ),
      Real.cos_le_one (2 * lam * (γ + a) * δ),
      Real.neg_one_le_cos (2 * lam * γ * δ), Real.cos_le_one (2 * lam * γ * δ)]

/-- **Zeros away from the offset vanish, for the admissible kernel.**  The third
bump needs no extra hypothesis: `2δ² < (γ-a)² + (γ+a)² = 2(γ² + a²)`, so its
exponent is negative as soon as the other two are. -/
theorem tendsto_re_gaussAmp_sq_of_far {a γ δ : ℝ}
    (h1 : δ ^ 2 < (γ - a) ^ 2) (h2 : δ ^ 2 < (γ + a) ^ 2) :
    Filter.Tendsto
      (fun lam : ℝ => (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re)
      Filter.atTop (nhds 0) := by
  have h3 : δ ^ 2 - γ ^ 2 - a ^ 2 < 0 := by nlinarith
  have ht1 := tendsto_exp_mul_nhds_zero (by linarith : δ ^ 2 - (γ - a) ^ 2 < 0)
  have ht2 := tendsto_exp_mul_nhds_zero (by linarith : δ ^ 2 - (γ + a) ^ 2 < 0)
  have ht3 := tendsto_exp_mul_nhds_zero h3
  have hsum := (ht1.add ht2).add (ht3.const_mul 2)
  simp only [add_zero, mul_zero] at hsum
  refine squeeze_zero_norm (fun lam => ?_) hsum
  simpa [Real.norm_eq_abs] using abs_re_gaussAmp_sq_le lam a γ δ

/-- The far contributions decrease in `lam`, so one summable function dominates
the whole ray — the hypothesis Tannery's theorem needs. -/
theorem abs_re_gaussAmp_sq_le_of_le {lam lam₀ a γ δ : ℝ} (hlam : lam₀ ≤ lam)
    (h1 : δ ^ 2 < (γ - a) ^ 2) (h2 : δ ^ 2 < (γ + a) ^ 2) :
    |(gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re|
      ≤ Real.exp (lam₀ * (δ ^ 2 - (γ - a) ^ 2))
        + Real.exp (lam₀ * (δ ^ 2 - (γ + a) ^ 2))
        + 2 * Real.exp (lam₀ * (δ ^ 2 - γ ^ 2 - a ^ 2)) := by
  have h3 : δ ^ 2 - γ ^ 2 - a ^ 2 < 0 := by nlinarith
  refine (abs_re_gaussAmp_sq_le lam a γ δ).trans ?_
  have e1 : lam * (δ ^ 2 - (γ - a) ^ 2) ≤ lam₀ * (δ ^ 2 - (γ - a) ^ 2) :=
    mul_le_mul_of_nonpos_right hlam (by linarith)
  have e2 : lam * (δ ^ 2 - (γ + a) ^ 2) ≤ lam₀ * (δ ^ 2 - (γ + a) ^ 2) :=
    mul_le_mul_of_nonpos_right hlam (by linarith)
  have e3 : lam * (δ ^ 2 - γ ^ 2 - a ^ 2) ≤ lam₀ * (δ ^ 2 - γ ^ 2 - a ^ 2) :=
    mul_le_mul_of_nonpos_right hlam (by linarith)
  have g1 := Real.exp_le_exp.mpr e1
  have g2 := Real.exp_le_exp.mpr e2
  have g3 := Real.exp_le_exp.mpr e3
  linarith

/-! ## Summability for the admissible kernel -/

/-- Inside the strip the three envelopes carry the uniform factor `e^{lam/4}`. -/
theorem abs_re_gaussAmp_sq_le_strip {lam δ : ℝ} (hlam : 0 ≤ lam) (hδ : |δ| ≤ 1 / 2)
    (a γ : ℝ) :
    |(gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re|
      ≤ Real.exp (lam / 4) * (Real.exp (-(lam * (γ - a) ^ 2))
          + Real.exp (-(lam * (γ + a) ^ 2))
          + 2 * Real.exp (-(lam * (γ ^ 2 + a ^ 2)))) := by
  have hsq : δ ^ 2 ≤ 1 / 4 := by
    have := abs_nonneg δ
    nlinarith [sq_abs δ]
  have hd : lam * δ ^ 2 ≤ lam / 4 := by nlinarith
  refine (abs_re_gaussAmp_sq_le lam a γ δ).trans ?_
  have b1 : Real.exp (lam * (δ ^ 2 - (γ - a) ^ 2))
      ≤ Real.exp (lam / 4) * Real.exp (-(lam * (γ - a) ^ 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have b2 : Real.exp (lam * (δ ^ 2 - (γ + a) ^ 2))
      ≤ Real.exp (lam / 4) * Real.exp (-(lam * (γ + a) ^ 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have b3 : Real.exp (lam * (δ ^ 2 - γ ^ 2 - a ^ 2))
      ≤ Real.exp (lam / 4) * Real.exp (-(lam * (γ ^ 2 + a ^ 2))) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  nlinarith [b1, b2, b3]

/-- The admissible kernel's contribution at inverse-fourth strength. -/
theorem abs_re_gaussAmp_sq_le_inv_quartic {lam δ : ℝ} (hlam : 0 < lam)
    (hδ : |δ| ≤ 1 / 2) (a γ : ℝ) :
    |(gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re|
      ≤ Real.exp (lam / 4) * (4 * (1 + 2 * a ^ 2 + 4 / lam) ^ 2) / (1 + γ ^ 4) := by
  refine (abs_re_gaussAmp_sq_le_strip hlam.le hδ a γ).trans ?_
  have h1 := exp_neg_sq_le_const_div_quartic hlam a γ
  have h2 := exp_neg_sq_le_const_div_quartic hlam (-a) γ
  rw [show γ - -a = γ + a by ring, show (-a) ^ 2 = a ^ 2 by ring] at h2
  have h0 := exp_neg_sq_le_const_div_quartic hlam 0 γ
  rw [show γ - 0 = γ by ring, show (0 : ℝ) ^ 2 = 0 by ring] at h0
  have hcross : Real.exp (-(lam * (γ ^ 2 + a ^ 2))) ≤ Real.exp (-(lam * γ ^ 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg a])
  have hmono : (1 + 2 * 0 + 4 / lam) ^ 2 / (1 + γ ^ 4)
      ≤ (1 + 2 * a ^ 2 + 4 / lam) ^ 2 / (1 + γ ^ 4) := by
    gcongr
    exact sq_nonneg a
  have hE : (0 : ℝ) < Real.exp (lam / 4) := Real.exp_pos _
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hE.le
  rw [mul_div_assoc]
  linarith [h1, h2, h0, hcross, hmono]

/-!
## Parity: the other combination

`gaussAmp` is the *symmetric* combination of two packets at `±a`.
-/

/-!
## Admissibility

Weil's criterion asks two things of a kernel, both only on the real axis: that it be real
there, and that it factor as `ĝ(t)·conj(ĝ(t))`.
-/

/-!
## The Weil summand collapses to a square

`weilSummand ĝ ρ` is `Re(ĝ(w_ρ) · conj(ĝ(w_{conj ρ})))`, a two-point product.
-/

/-- The two points `weilSummand` evaluates at are `w` and `-conj w`. -/
theorem ofCritical_arg_conj (ρ : ℂ) :
    -Complex.I * ((starRingEnd ℂ) ρ - 1 / 2)
      = -((starRingEnd ℂ) (-Complex.I * (ρ - 1 / 2))) := by
  simp [Complex.ext_iff]

/-- **`gaussAmp` is Hermitian**: `ĝ(-conj w) = conj(ĝ(w))`.  The two bumps swap
under the involution, and `lam`, `a` being real carries the conjugation inside
the exponentials. -/
theorem gaussAmp_hermitian (lam a : ℝ) (w : ℂ) :
    gaussAmp lam a (-(starRingEnd ℂ w)) = (starRingEnd ℂ) (gaussAmp lam a w) := by
  have h2 : (starRingEnd ℂ) 2 = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have hA : (starRingEnd ℂ) (-(lam : ℂ) * (w - (a : ℂ)) ^ 2 / 2)
      = -(lam : ℂ) * ((-(starRingEnd ℂ) w) + (a : ℂ)) ^ 2 / 2 := by
    rw [map_div₀, map_mul, map_neg, map_pow, map_sub, Complex.conj_ofReal,
      Complex.conj_ofReal, h2]
    ring
  have hB : (starRingEnd ℂ) (-(lam : ℂ) * (w + (a : ℂ)) ^ 2 / 2)
      = -(lam : ℂ) * ((-(starRingEnd ℂ) w) - (a : ℂ)) ^ 2 / 2 := by
    rw [map_div₀, map_mul, map_neg, map_pow, map_add, Complex.conj_ofReal,
      Complex.conj_ofReal, h2]
    ring
  simp only [gaussAmp, map_add, ← Complex.exp_conj, hA, hB]
  ring

/-- **The collapse.**  With `gaussAmp` Hermitian, the two-point product is the
square — so `weilSummand gaussAmp ρ` is `(gaussAmp (w_ρ)²).re`, the quantity
every bound above is stated on. -/
theorem re_mul_conj_gaussAmp (lam a : ℝ) (w : ℂ) :
    (gaussAmp lam a w
        * (starRingEnd ℂ) (gaussAmp lam a (-(starRingEnd ℂ w)))).re
      = (gaussAmp lam a w ^ 2).re := by
  rw [gaussAmp_hermitian, Complex.conj_conj, ← pow_two]

/-!
## The rate comparison for all three bumps

`hlt` in the capstone is about `ampRate`, the max of all three.
-/

/-- The target's rate is positive exactly when `ε` is below the off-line
distance.  This is the `0 < c₀` the capstone needs, and it is the only place the
off-line assumption enters. -/
theorem target_rate_pos {δ₀ ε : ℝ} (hε : 0 < ε) (h : ε < |δ₀|) :
    0 < δ₀ ^ 2 - ε ^ 2 := by
  have : ε ^ 2 < δ₀ ^ 2 := by nlinarith [sq_abs δ₀, abs_nonneg δ₀]
  linarith

/-- The same at the target's own ordinate, where a strictly smaller off-line
distance suffices for the first bump and no smallness in `ε` is needed there. -/
theorem ampRate_lt_of_same_ordinate {δ₀ δ γ₀ ε : ℝ} (hε : 0 < ε)
    (hδ : δ ^ 2 < δ₀ ^ 2) (hsnd : ε < |γ₀ + (γ₀ - ε)|) (ha : ε < |γ₀ - ε|) :
    ampRate (γ₀ - ε) γ₀ δ < δ₀ ^ 2 - ε ^ 2 := by
  rw [ampRate_def]
  refine max_lt (max_lt ?_ (rate_snd_lt hε hδ.le hsnd)) (cross_rate_lt hδ.le hε ha)
  have he : γ₀ - (γ₀ - ε) = ε := by ring
  rw [he]
  linarith

/-- Two of the conditions mention `ε` on both sides (`ε < |x - ε|`). -/
theorem lt_abs_sub_of_lt_half {x ε : ℝ} (hε : 0 < ε) (h : 2 * ε < x) :
    ε < |x - ε| := by
  rw [abs_of_pos (by linarith)]
  linarith

/-! ## Choosing one `ε` for all of it

The four bounds are strict lower bounds by positive quantities, and the
competing set is finite, so a single `ε` meets them all.  This is the last
arithmetic step: after it, `hlt` and `0 < c₀` are both discharged. -/

/-! ## Discharging the remaining hypotheses

Three of the capstone's hypotheses were carried rather than proved.  All three
follow from what is already here plus the inverse-square input. -/

/-- `hδ` is a maximiser.  Over a finite nonempty set some zero has the largest
off-line distance, and that is the one to target. -/
theorem exists_max_sq {ι : Type*} {R : Finset ι} (hR : R.Nonempty) (δ : ι → ℝ) :
    ∃ i₀ ∈ R, ∀ i ∈ R, (δ i) ^ 2 ≤ (δ i₀) ^ 2 :=
  Finset.exists_max_image R (fun i => (δ i) ^ 2) hR

/-!
## The quadruple, for the admissible kernel

The same-side condition `0 < γ + γ₀` fails for conjugate partners, which sit at `-γ₀`.
-/

/-- The admissible kernel's contribution is even in the ordinate. -/
theorem re_gaussAmp_sq_even_ordinate (lam a γ δ : ℝ) :
    (gaussAmp lam a (((-γ : ℝ) : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re
      = (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re := by
  rw [re_gaussAmp_sq, re_gaussAmp_sq]
  have e1 : (-γ - a) ^ 2 = (γ + a) ^ 2 := by ring
  have e2 : (-γ + a) ^ 2 = (γ - a) ^ 2 := by ring
  have e3 : (-γ) ^ 2 = γ ^ 2 := by ring
  have c1 : 2 * lam * (-γ - a) * δ = -(2 * lam * (γ + a) * δ) := by ring
  have c2 : 2 * lam * (-γ + a) * δ = -(2 * lam * (γ - a) * δ) := by ring
  have c3 : 2 * lam * (-γ) * δ = -(2 * lam * γ * δ) := by ring
  rw [e1, e2, e3, c1, c2, c3, Real.cos_neg, Real.cos_neg, Real.cos_neg]
  ring

/-- And even in the off-line distance. -/
theorem re_gaussAmp_sq_even_offline (lam a γ δ : ℝ) :
    (gaussAmp lam a ((γ : ℂ) - ((-δ : ℝ) : ℂ) * Complex.I) ^ 2).re
      = (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re := by
  rw [re_gaussAmp_sq, re_gaussAmp_sq]
  have e : (-δ) ^ 2 = δ ^ 2 := by ring
  have c1 : 2 * lam * (γ - a) * -δ = -(2 * lam * (γ - a) * δ) := by ring
  have c2 : 2 * lam * (γ + a) * -δ = -(2 * lam * (γ + a) * δ) := by ring
  have c3 : 2 * lam * γ * -δ = -(2 * lam * γ * δ) := by ring
  rw [e, c1, c2, c3, Real.cos_neg, Real.cos_neg, Real.cos_neg]

/-- All four members of the quadruple contribute the same amount. -/
theorem re_gaussAmp_sq_quadruple (lam a γ δ : ℝ) :
    (gaussAmp lam a (((-γ : ℝ) : ℂ) - ((-δ : ℝ) : ℂ) * Complex.I) ^ 2).re
      = (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re := by
  rw [re_gaussAmp_sq_even_offline, re_gaussAmp_sq_even_ordinate]

/-!
## Reducing the arithmetic input

The one thing this block does not prove is `Summable (1/(1 + γ²))` over the zeros.
-/

/-!
## The interface to the canonical product

`Cvs.Zeta/Hadamard.lean` proves `Summable (fun n => ‖ρ_n‖⁻¹ ^ 2)` for the zeros of an entire
function, from a counting law — including the `r·log r` shape Riemann–von Mangoldt gives
(`summable_inv_norm_sq_zeroSeq_of_rlogr`).
-/

/-!
## The window is finite for the same reason

`finite_surviving` used Mathlib's discreteness of the zeta zero set.
-/

/-- Only finitely many ordinates are bounded, given the inverse-fourth input. -/
theorem finite_window_of_summable {ι : Type*} (γ : ι → ℝ)
    (hs : Summable fun i => 1 / (1 + (γ i) ^ 4)) (M : ℝ) :
    {i | |γ i| ≤ M}.Finite := by
  have hM : (0 : ℝ) < 1 / (1 + M ^ 4) := by positivity
  have hev := hs.tendsto_cofinite_zero.eventually_lt_const hM
  refine (Filter.eventually_cofinite.mp hev).subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq, not_lt] at hi ⊢
  have hsq : (γ i) ^ 2 ≤ M ^ 2 := by
    nlinarith [sq_abs (γ i), abs_nonneg (γ i)]
  have h4 : (γ i) ^ 4 ≤ M ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq)
      (by positivity : (0 : ℝ) ≤ M ^ 2 + (γ i) ^ 2)]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-! ## The distinguished set is an orbit

`T` cannot be a singleton.  A mirror partner at `-γ₀` has `γ + a = -ε`, so
`rate_snd_lt` fails for it — its second bump has *exactly* the target's rate.
That is the reinforcement, not a competition, and the fix is to put the whole
orbit in `T` rather than to weaken the comparison. -/

/-- Every point of the orbit `(±γ₀, ±δ₀)` contributes the same amount. -/
theorem re_gaussAmp_sq_orbit {lam a γ δ γ₀ δ₀ : ℝ}
    (hγ : γ = γ₀ ∨ γ = -γ₀) (hδ : δ = δ₀ ∨ δ = -δ₀) :
    (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re
      = (gaussAmp lam a ((γ₀ : ℂ) - (δ₀ : ℂ) * Complex.I) ^ 2).re := by
  rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
  · rfl
  · exact re_gaussAmp_sq_even_offline _ _ _ _
  · exact re_gaussAmp_sq_even_ordinate _ _ _ _
  · exact re_gaussAmp_sq_quadruple _ _ _ _

/-- **`hdom` holds on the whole orbit** as soon as it holds at the target.  This
is what lets `T` be the quadruple, which is what `tendsto_finset_sum_atBot`
needed a *subset* for. -/
theorem re_gaussAmp_sq_le_neg_half_orbit {lam a γ δ γ₀ δ₀ c₀ : ℝ}
    (hγ : γ = γ₀ ∨ γ = -γ₀) (hδ : δ = δ₀ ∨ δ = -δ₀)
    (h : (gaussAmp lam a ((γ₀ : ℂ) - (δ₀ : ℂ) * Complex.I) ^ 2).re
      ≤ -(1 / 2 * Real.exp (lam * c₀))) :
    (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re
      ≤ -(1 / 2 * Real.exp (lam * c₀)) := by
  rw [re_gaussAmp_sq_orbit hγ hδ]; exact h

/-!
## Breaking the circularity in the choice of `S`

The competing window is `{|γ ∓ a| ≤ 1/2}`, which depends on `a = γ₀ - ε`; but `ε` is chosen by
`exists_eps_bounds` from the competing set.
-/

/-!
## The third competitor case

Competitors split three ways by ordinate: equal to `γ₀`, equal to `-γ₀`, or neither.
-/

/-- A zero at the mirror ordinate `-γ₀` with strictly smaller off-line distance
has all three rates below the target's. -/
theorem ampRate_lt_of_mirror_ordinate {δ₀ δ γ₀ ε : ℝ} (hε : 0 < ε)
    (hδ : δ ^ 2 < δ₀ ^ 2) (hγ₀ : 2 * ε < γ₀) :
    ampRate (γ₀ - ε) (-γ₀) δ < δ₀ ^ 2 - ε ^ 2 := by
  rw [ampRate_def]
  refine max_lt (max_lt ?_ ?_) ?_
  · have h : -γ₀ - (γ₀ - ε) = -(2 * γ₀ - ε) := by ring
    rw [h]
    nlinarith
  · have h : -γ₀ + (γ₀ - ε) = -ε := by ring
    rw [h]
    nlinarith
  · nlinarith [sq_nonneg (γ₀ - ε), sq_nonneg γ₀]

/-! ## Building `S` and `T`

`S` is the fixed window as a `Finset`, `T` the target's orbit inside it.  Both
come from what is already proved: `S` from `finite_window_of_summable`, `T` by
filtering. -/

/-- The fixed window, as a `Finset`. -/
theorem exists_window_finset {ι : Type*} (γ : ι → ℝ)
    (hs : Summable fun i => 1 / (1 + (γ i) ^ 4)) (M : ℝ) :
    ∃ S : Finset ι, ∀ i, i ∈ S ↔ |γ i| ≤ M := by
  classical
  exact ⟨(finite_window_of_summable γ hs M).toFinset,
    fun i => by simp [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]⟩

/-- `δ² = δ₀²` is the sign ambiguity, in the form the orbit bound consumes. -/
theorem eq_or_eq_neg_of_sq_eq_sq {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have hz : (x - y) * (x + y) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h' | h'
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **`hdom` on the orbit, from the filter's own condition.**  This is the form
`exists_orbit_finset` produces, so `T`'s membership fact discharges the
capstone's `hdom` directly. -/
theorem re_gaussAmp_sq_le_neg_half_of_orbit {lam a γ δ γ₀ δ₀ c₀ : ℝ}
    (hγ : γ = γ₀ ∨ γ = -γ₀) (hδ : δ ^ 2 = δ₀ ^ 2)
    (h : (gaussAmp lam a ((γ₀ : ℂ) - (δ₀ : ℂ) * Complex.I) ^ 2).re
      ≤ -(1 / 2 * Real.exp (lam * c₀))) :
    (gaussAmp lam a ((γ : ℂ) - (δ : ℂ) * Complex.I) ^ 2).re
      ≤ -(1 / 2 * Real.exp (lam * c₀)) :=
  re_gaussAmp_sq_le_neg_half_orbit hγ (eq_or_eq_neg_of_sq_eq_sq hδ) h

/-- Outside the fixed window, both bumps are far: `|γ| > |γ₀| + 1` and
`|a| ≤ |γ₀| + 1/4` give a gap of at least `3/4`. -/
theorem far_of_not_mem_window {γ₀ ε γ : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (h : |γ₀| + 1 < |γ|) :
    1 / 2 < |γ - (γ₀ - ε)| ∧ 1 / 2 < |γ + (γ₀ - ε)| := by
  have ha : |γ₀ - ε| ≤ |γ₀| + 1 / 4 := by
    have h1 : |γ₀ - ε| ≤ |γ₀| + |ε| := abs_sub γ₀ ε
    rw [abs_of_pos hε] at h1
    linarith
  constructor
  · have := abs_sub_abs_le_abs_sub γ (γ₀ - ε)
    linarith
  · have h2 : |γ| - |(-(γ₀ - ε))| ≤ |γ - (-(γ₀ - ε))| :=
      abs_sub_abs_le_abs_sub γ (-(γ₀ - ε))
    rw [abs_neg, show γ - -(γ₀ - ε) = γ + (γ₀ - ε) by ring] at h2
    linarith

/-! ## The assembly

Every producer is in place.  The order is forced: `S` first (offset-independent),
then `ε` from the competitors inside `S`, then `a = γ₀ - ε`, then `T` as the
orbit. -/

/-!
## Dropping the same-side condition

`hside` asked competitors at other ordinates to satisfy `0 < γ + γ₀`.
-/

/-- `ε` chosen against both ordinate distances as magnitudes, so no competitor
needs to lie on a particular side. -/
theorem exists_eps_bounds_abs {ι : Type*} [DecidableEq ι] (R : Finset ι)
    (γ : ι → ℝ) {γ₀ δ₀ : ℝ} (hγ₀ : 0 < γ₀) (hδ₀ : δ₀ ≠ 0)
    (hne : ∀ i ∈ R, γ i ≠ γ₀) (hne2 : ∀ i ∈ R, γ i ≠ -γ₀) :
    ∃ ε, 0 < ε ∧ ε ≤ 1 / 4 ∧ ε < |δ₀| ∧ 2 * ε < γ₀ ∧
      ∀ i ∈ R, 2 * ε < |γ i - γ₀| ∧ 2 * ε < |γ i + γ₀| := by
  obtain ⟨ε₀, hε₀pos, hall⟩ := exists_pos_lt_all R
    (fun i => min (|γ i - γ₀| / 2) (|γ i + γ₀| / 2)) (fun i hi => by
      have h1 : 0 < |γ i - γ₀| := abs_pos.mpr (sub_ne_zero.mpr (hne i hi))
      have h2 : 0 < |γ i + γ₀| := by
        refine abs_pos.mpr fun h => hne2 i hi ?_
        linarith [eq_neg_of_add_eq_zero_left h]
      exact lt_min (by linarith) (by linarith))
  have hd : 0 < |δ₀| := abs_pos.mpr hδ₀
  refine ⟨min (min ε₀ (1 / 8)) (min (|δ₀| / 2) (γ₀ / 4)), ?_, ?_, ?_, ?_,
    fun i hi => ?_⟩
  · exact lt_min (lt_min hε₀pos (by norm_num)) (lt_min (by linarith) (by linarith))
  · exact (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num))
  · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  · have : min (min ε₀ (1 / 8)) (min (|δ₀| / 2) (γ₀ / 4)) ≤ γ₀ / 4 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  · have hle : min (min ε₀ (1 / 8)) (min (|δ₀| / 2) (γ₀ / 4)) ≤ ε₀ :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hmin := hall i hi
    have hA : ε₀ < |γ i - γ₀| / 2 := lt_of_lt_of_le hmin (min_le_left _ _)
    have hB : ε₀ < |γ i + γ₀| / 2 := lt_of_lt_of_le hmin (min_le_right _ _)
    exact ⟨by linarith, by linarith⟩

/-!
## Deriving the maximality hypothesis

`hmax` is stated over the window `{|γ| ≤ |γ₀| + 1}`, which depends on `γ₀`, so "take the
maximiser over the window" is circular: the maximiser's own window may be larger than the one
it was chosen in.
-/

/-!
## Replacing the maximiser by a near-maximiser

`hmax` asks the target to attain the largest `|δ|`, which is a real restriction: if the
off-line deviations increase to a supremum never reached, no such target exists.
-/

/-- **The three competitor cases, with the third left as a rate bound.**  This
is `ampRate_lt_cases_margin` with nothing assumed about *how* the different
ordinate case is won — the assembly only ever uses the conclusion. -/
theorem ampRate_lt_cases_rate {δ₀ δ γ γ₀ ε : ℝ} (hε : 0 < ε) (hγ₀ : 2 * ε < γ₀)
    (hsame : γ = γ₀ ∨ γ = -γ₀ → δ ^ 2 < δ₀ ^ 2)
    (hrate : γ ≠ γ₀ → γ ≠ -γ₀ → ampRate (γ₀ - ε) γ δ < δ₀ ^ 2 - ε ^ 2) :
    ampRate (γ₀ - ε) γ δ < δ₀ ^ 2 - ε ^ 2 := by
  have ha : ε < |γ₀ - ε| := lt_abs_sub_of_lt_half hε hγ₀
  by_cases h1 : γ = γ₀
  · subst h1
    refine ampRate_lt_of_same_ordinate hε (hsame (Or.inl rfl)) ?_ ha
    rw [show γ + (γ - ε) = 2 * γ - ε by ring]
    exact lt_abs_sub_of_lt_half hε (by linarith)
  · by_cases h2 : γ = -γ₀
    · subst h2
      exact ampRate_lt_of_mirror_ordinate hε (hsame (Or.inr rfl)) hγ₀
    · exact hrate h1 h2

/-!
## Conjugate symmetry, and the positive-ordinate reduction

`hγ₀ : 0 < γ i₀` asks the target to sit at positive ordinate.
-/

/-!
## The bridge to the Weil summand, in coordinates

`weilSummand ĝ ρ` is `Re(ĝ(-i(ρ-1/2)) · conj(ĝ(-i(conj ρ - 1/2))))`.
-/

/-- The critical-line coordinate change: `-i(ρ - 1/2) = γ - δi` with `γ = ρ.im`
and `δ = ρ.re - 1/2`. -/
theorem ofCritical_arg_eq (ρ : ℂ) :
    -Complex.I * (ρ - 1 / 2)
      = ((ρ.im : ℝ) : ℂ) - (((ρ.re - 1 / 2 : ℝ)) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

/-- **The Weil summand at `gaussAmp`, in `(γ, δ)` coordinates.**  This is
`Cvs.Zeta.weilSummand (gaussAmp lam a) ρ` with the definition unfolded, shown
equal to the three-bump quantity `re_gaussAmp_sq` computes. -/
theorem weilSummand_gaussAmp (lam a : ℝ) (ρ : ℂ) :
    (gaussAmp lam a (-Complex.I * (ρ - 1 / 2))
        * (starRingEnd ℂ)
          (gaussAmp lam a (-Complex.I * ((starRingEnd ℂ) ρ - 1 / 2)))).re
      = (gaussAmp lam a (((ρ.im : ℝ) : ℂ)
          - (((ρ.re - 1 / 2 : ℝ)) : ℂ) * Complex.I) ^ 2).re := by
  rw [ofCritical_arg_conj, re_mul_conj_gaussAmp, ofCritical_arg_eq]

end Cvs.Zeta.GaussKernel.AdmissibleKernel
