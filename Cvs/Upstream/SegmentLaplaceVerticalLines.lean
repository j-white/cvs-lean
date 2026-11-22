import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Laplace transform of an entire function on a segment through its two vertical lines

For `Φ` entire and `w = σ + ig` with `g > 0`, Cauchy on `[a, b] × [0, S]` and `S → ∞` give
`∫_a^b Φ(t)e^{wt} dt = i∫_0^∞ Φ(a + is)e^{w(a+is)} ds − i∫_0^∞ Φ(b + is)e^{w(b+is)} ds` when `Φ` is bounded on the
half strip, so the transform is at most `∫_0^∞ (‖Φ(a + is)‖e^{σa} + ‖Φ(b + is)‖e^{σb}) e^{−gs} ds`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology intervalIntegral

namespace Cvs.Upstream.SegmentLaplaceVerticalLines

/-- `‖e^{w(t + is)}‖ = e^{σt − gs}` for `w = σ + ig`. -/
theorem norm_exp_mul (w : ℂ) (t s : ℝ) :
    ‖Complex.exp (w * (t + s * I))‖ = Real.exp (w.re * t - w.im * s) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **Cauchy on the rectangle `[a, b] × [0, S]`**: the transform on the segment is the difference of the two
vertical integrals plus the top edge. -/
theorem laplace_eq_rect {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (w : ℂ) (a b S : ℝ) :
    ∫ t in a..b, Φ t * Complex.exp (w * t)
      = I * (∫ s in (0 : ℝ)..S, Φ (a + s * I) * Complex.exp (w * (a + s * I)))
        - I * (∫ s in (0 : ℝ)..S, Φ (b + s * I) * Complex.exp (w * (b + s * I)))
        + ∫ t in a..b, Φ (t + S * I) * Complex.exp (w * (t + S * I)) := by
  have hf : Differentiable ℂ fun z => Φ z * Complex.exp (w * z) := hΦ.mul (by fun_prop)
  have h := integral_boundary_rect_eq_zero_of_differentiableOn (fun z => Φ z * Complex.exp (w * z))
    (a : ℂ) (b + S * I) hf.differentiableOn
  simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, mul_zero,
    mul_one, sub_zero, zero_add, add_zero, smul_eq_mul] at h
  have e0 : ∀ x : ℝ, ((x : ℂ) + (0 : ℝ) * I) = x := fun x => by simp
  simp only [e0] at h
  linear_combination h

/-- The vertical integrand `s ↦ Φ(t + is)e^{w(t+is)}` of a bounded entire `Φ` is integrable on `(0, ∞)` for
`Im w > 0`. -/
theorem integrableOn_vertical {Φ : ℂ → ℂ} (hΦ : Continuous Φ) {w : ℂ} (hw : 0 < w.im) (t : ℝ) {M : ℝ}
    (hM : ∀ s : ℝ, 0 ≤ s → ‖Φ (t + s * I)‖ ≤ M) :
    IntegrableOn (fun s : ℝ => Φ (t + s * I) * Complex.exp (w * (t + s * I))) (Ioi 0) := by
  have hdom : IntegrableOn (fun s : ℝ => M * Real.exp (w.re * t) * Real.exp (-(w.im * s))) (Ioi 0) := by
    have : IntegrableOn (fun s : ℝ => M * Real.exp (w.re * t) * Real.exp (-w.im * s)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hw).const_mul (M * Real.exp (w.re * t))
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  refine hdom.mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => ?_))
  rw [norm_mul, norm_exp_mul, sub_eq_add_neg, Real.exp_add]
  have h0 : 0 ≤ Real.exp (w.re * t) * Real.exp (-(w.im * s)) := by positivity
  calc ‖Φ (t + s * I)‖ * (Real.exp (w.re * t) * Real.exp (-(w.im * s)))
      ≤ M * (Real.exp (w.re * t) * Real.exp (-(w.im * s))) := mul_le_mul_of_nonneg_right (hM s (le_of_lt hs)) h0
    _ = M * Real.exp (w.re * t) * Real.exp (-(w.im * s)) := by ring

/-- **The transform on a segment through its two vertical lines**: for `Φ` entire and bounded by `M` on
`[a, b] × [0, ∞)` and `Im w > 0`, `∫_a^b Φ(t)e^{wt} = i∫_0^∞ Φ(a + is)e^{w(a+is)} − i∫_0^∞ Φ(b + is)e^{w(b+is)}`. -/
theorem laplace_eq_vertical {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {w : ℂ} (hw : 0 < w.im) {a b : ℝ}
    (hab : a ≤ b) {M : ℝ} (hM : ∀ t ∈ Icc a b, ∀ s : ℝ, 0 ≤ s → ‖Φ (t + s * I)‖ ≤ M) :
    ∫ t in a..b, Φ t * Complex.exp (w * t)
      = I * (∫ s in Ioi (0 : ℝ), Φ (a + s * I) * Complex.exp (w * (a + s * I)))
        - I * (∫ s in Ioi (0 : ℝ), Φ (b + s * I) * Complex.exp (w * (b + s * I))) := by
  have hc := hΦ.continuous
  have hIa := integrableOn_vertical hc hw a (hM a ⟨le_rfl, hab⟩)
  have hIb := integrableOn_vertical hc hw b (hM b ⟨hab, le_rfl⟩)
  have hA := intervalIntegral_tendsto_integral_Ioi 0 hIa tendsto_id
  have hB := intervalIntegral_tendsto_integral_Ioi 0 hIb tendsto_id
  -- the top edge vanishes
  have hTop : Tendsto (fun S : ℝ => ∫ t in a..b, Φ (t + S * I) * Complex.exp (w * (t + S * I))) atTop (𝓝 0) := by
    set K := (b - a) * (max M 0) * Real.exp (|w.re| * (|a| + |b|)) with hK
    have hbound : ∀ S : ℝ, 0 ≤ S →
        ‖∫ t in a..b, Φ (t + S * I) * Complex.exp (w * (t + S * I))‖ ≤ K * Real.exp (-(w.im * S)) := by
      intro S hS
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := max M 0 * Real.exp (|w.re| * (|a| + |b|)) * Real.exp (-(w.im * S))) ?_).trans ?_
      · intro t ht
        rw [uIoc_of_le hab] at ht
        rw [norm_mul, norm_exp_mul, sub_eq_add_neg, Real.exp_add]
        have h1 : ‖Φ (t + S * I)‖ ≤ max M 0 := (hM t ⟨le_of_lt ht.1, ht.2⟩ S hS).trans (le_max_left _ _)
        have h2 : Real.exp (w.re * t) ≤ Real.exp (|w.re| * (|a| + |b|)) := by
          refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rcases le_total 0 t with h | h
          · rw [abs_of_nonneg h]; linarith [le_abs_self b, abs_nonneg a, ht.2]
          · rw [abs_of_nonpos h]; linarith [neg_abs_le a, abs_nonneg b, ht.1]
        have := Real.exp_pos (-(w.im * S))
        calc ‖Φ (t + S * I)‖ * (Real.exp (w.re * t) * Real.exp (-(w.im * S)))
            ≤ max M 0 * (Real.exp (|w.re| * (|a| + |b|)) * Real.exp (-(w.im * S))) := by gcongr
          _ = _ := by ring
      · rw [abs_of_nonneg (by linarith : 0 ≤ b - a), hK]; ring_nf; rfl
    have hexp : Tendsto (fun S : ℝ => K * Real.exp (-(w.im * S))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hw)))
      simpa using this.const_mul K
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [eventually_ge_atTop 0] with S hS using hbound S hS
  have hlim : Tendsto (fun S : ℝ => I * (∫ s in (0 : ℝ)..S, Φ (a + s * I) * Complex.exp (w * (a + s * I)))
      - I * (∫ s in (0 : ℝ)..S, Φ (b + s * I) * Complex.exp (w * (b + s * I)))
      + ∫ t in a..b, Φ (t + S * I) * Complex.exp (w * (t + S * I))) atTop
      (𝓝 (I * (∫ s in Ioi (0 : ℝ), Φ (a + s * I) * Complex.exp (w * (a + s * I)))
        - I * (∫ s in Ioi (0 : ℝ), Φ (b + s * I) * Complex.exp (w * (b + s * I))) + 0)) :=
    ((hA.const_mul I).sub (hB.const_mul I)).add hTop
  rw [add_zero] at hlim
  have hconst : (fun S : ℝ => I * (∫ s in (0 : ℝ)..S, Φ (a + s * I) * Complex.exp (w * (a + s * I)))
      - I * (∫ s in (0 : ℝ)..S, Φ (b + s * I) * Complex.exp (w * (b + s * I)))
      + ∫ t in a..b, Φ (t + S * I) * Complex.exp (w * (t + S * I)))
      = fun _ => ∫ t in a..b, Φ t * Complex.exp (w * t) := by
    funext S; exact (laplace_eq_rect hΦ w a b S).symm
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end Cvs.Upstream.SegmentLaplaceVerticalLines

end
