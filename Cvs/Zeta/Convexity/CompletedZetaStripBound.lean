import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The completed zeta is bounded on the critical strip, with no Phragmén–Lindelöf
-/

open Complex MeasureTheory Set

namespace Cvs.ZetaGrowth

/-- The modulus of a Mellin integrand depends only on `Re s`. -/
theorem norm_mellin_integrand {f : ℝ → ℂ} (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • f t‖ = t ^ (s.re - 1) * ‖f t‖ := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

theorem integrableOn_norm_of_mellinConvergent {f : ℝ → ℂ} {s : ℂ}
    (h : MellinConvergent f s) :
    IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * ‖f t‖) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • f t‖) (Ioi 0) :=
    MeasureTheory.Integrable.norm h
  exact MeasureTheory.IntegrableOn.congr_fun h1
    (fun t ht => norm_mellin_integrand s ht) measurableSet_Ioi

/-- **A Mellin transform is bounded by the real-exponent integral.** -/
theorem norm_mellin_le (f : ℝ → ℂ) (s : ℂ) :
    ‖mellin f s‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * ‖f t‖ := by
  rw [mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => norm_mellin_integrand s ht)

/-- `t^{σ-1}` is dominated by the sum of its values at the two edges of the strip: for `t ≥ 1`
the larger exponent wins, for `t ≤ 1` the smaller. -/
theorem rpow_le_edges {α β σ t : ℝ} (ht : 0 < t) (h1 : α ≤ σ) (h2 : σ ≤ β) :
    t ^ (σ - 1) ≤ t ^ (α - 1) + t ^ (β - 1) := by
  rcases le_total 1 t with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (by linarith : σ - 1 ≤ β - 1)
    have hnn : (0 : ℝ) ≤ t ^ (α - 1) := Real.rpow_nonneg (le_of_lt ht) _
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ht h (by linarith : α - 1 ≤ σ - 1)
    have hnn : (0 : ℝ) ≤ t ^ (β - 1) := Real.rpow_nonneg (le_of_lt ht) _
    linarith

/-- **A Mellin transform is bounded on every vertical strip on which it converges** , by the sum
of the two edge integrals — a bound with no dependence on `Im s` whatsoever. -/
theorem norm_mellin_le_strip {f : ℝ → ℂ} {α β : ℝ} {s : ℂ}
    (hs : MellinConvergent f s) (hα : MellinConvergent f (α : ℂ))
    (hβ : MellinConvergent f (β : ℂ)) (h1 : α ≤ s.re) (h2 : s.re ≤ β) :
    ‖mellin f s‖ ≤ (∫ t in Ioi (0 : ℝ), t ^ (α - 1) * ‖f t‖)
      + ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * ‖f t‖ := by
  have hIα : IntegrableOn (fun t : ℝ => t ^ (α - 1) * ‖f t‖) (Ioi 0) := by
    have := integrableOn_norm_of_mellinConvergent hα
    simpa using this
  have hIβ : IntegrableOn (fun t : ℝ => t ^ (β - 1) * ‖f t‖) (Ioi 0) := by
    have := integrableOn_norm_of_mellinConvergent hβ
    simpa using this
  refine le_trans (norm_mellin_le f s) ?_
  rw [← MeasureTheory.integral_add hIα hIβ]
  refine setIntegral_mono_on (integrableOn_norm_of_mellinConvergent hs) (hIα.add hIβ)
    measurableSet_Ioi (fun t ht => ?_)
  have htp : (0 : ℝ) < t := ht
  have hle := rpow_le_edges htp h1 h2
  have hnn : (0 : ℝ) ≤ ‖f t‖ := norm_nonneg _
  nlinarith

/-- **The modified function's Mellin transform converges everywhere.**  `f_modif` decays faster
than every power both at `∞` and at `0` — that is exactly what makes the pair *strong* — so the
`MellinConvergent` hypothesis is vacuous for it. -/
theorem mellinConvergent_f_modif (P : WeakFEPair ℂ) (w : ℂ) :
    MellinConvergent P.f_modif w := by
  have hP := P.isStrongFEPair_toStrongFEPair
  exact mellinConvergent_of_isBigO_rpow (a := w.re + 1) (b := w.re - 1)
    P.toStrongFEPair.hf_int (hP.hf_top _) (by linarith) (hP.hf_zero _) (by linarith)

/-- **`Λ₀` is bounded on every vertical strip**, with a bound depending only on the two edges.
No Phragmén–Lindelöf, no bootstrapping: `Λ₀` is a Mellin transform, and `‖t^{s-1}‖` does not
see `Im s`. -/
theorem norm_Λ₀_le_strip (P : WeakFEPair ℂ) {α β : ℝ} {w : ℂ}
    (h1 : α ≤ w.re) (h2 : w.re ≤ β) :
    ‖P.Λ₀ w‖ ≤ (∫ t in Ioi (0 : ℝ), t ^ (α - 1) * ‖P.f_modif t‖)
      + ∫ t in Ioi (0 : ℝ), t ^ (β - 1) * ‖P.f_modif t‖ := by
  rw [WeakFEPair.Λ₀]
  exact norm_mellin_le_strip (mellinConvergent_f_modif P w)
    (mellinConvergent_f_modif P (α : ℂ)) (mellinConvergent_f_modif P (β : ℂ)) h1 h2

/-- The strip constant for the completed zeta, at the two edges `σ = -1/2` and `σ = 3/2`
(halved by `s ↦ s/2`, so `-1/4` and `3/4`). -/
noncomputable def zetaStripConst : ℝ :=
  (∫ t in Ioi (0 : ℝ), t ^ (-1/4 - 1 : ℝ) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖)
    + ∫ t in Ioi (0 : ℝ), t ^ (3/4 - 1 : ℝ) * ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖

/-- **`Λ₀` for the Riemann zeta is bounded on the critical strip**, unconditionally. -/
theorem norm_completedRiemannZeta₀_le {s : ℂ} (h1 : -1/2 ≤ s.re) (h2 : s.re ≤ 3/2) :
    ‖completedRiemannZeta₀ s‖ ≤ zetaStripConst / 2 := by
  have hre : (s / 2).re = s.re / 2 := by simp
  have h := norm_Λ₀_le_strip (HurwitzZeta.hurwitzEvenFEPair 0) (α := -1/4) (β := 3/4) (w := s / 2)
    (by rw [hre]; linarith) (by rw [hre]; linarith)
  have heq : completedRiemannZeta₀ s = ((HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2 := rfl
  rw [heq, norm_div, Complex.norm_ofNat]
  rw [zetaStripConst]
  exact div_le_div_of_nonneg_right h (by norm_num)

end Cvs.ZetaGrowth
