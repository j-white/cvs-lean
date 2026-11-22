import Mathlib
import Cvs.Zeta.DigammaStrip
import Cvs.Zeta.GammaRLogDeriv
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.ZetaLowerBound

/-!
# The vertical sides of the contour

The horizontal segments are `Cvs.Zeta.XiLogSqFull`.
-/

open Complex LSeries ArithmeticFunction Real
open scoped LSeries.notation

namespace Cvs.Zeta

/-! ### The Dirichlet-series vertical -/

/-- `Σ Λ(n)/n²`, the value bounding `‖ζ'/ζ‖` on and to the right of the line `Re s = 2`. -/
noncomputable def vonMangoldtSumTwo : ℝ :=
  ∑' n : ℕ, ‖term (fun n => (Λ n : ℂ)) (2 : ℂ) n‖

lemma summable_norm_term_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖term (fun n => (Λ n : ℂ)) s n‖ :=
  summable_norm_iff.mpr (LSeriesSummable_vonMangoldt hs)

lemma vonMangoldtSumTwo_nonneg : 0 ≤ vonMangoldtSumTwo :=
  tsum_nonneg fun _ => norm_nonneg _

/-- `‖ζ'/ζ(s)‖ ≤ Σ Λ(n)/n²` for `Re s ≥ 2`: the right-hand vertical is *bounded*, not
merely `O(log T)`.  This is the one side of the contour where the Dirichlet series
converges absolutely, and the whole estimate is its triangle inequality. -/
theorem norm_logDeriv_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ vonMangoldtSumTwo := by
  have hs1 : 1 < s.re := by linarith
  have hL : logDeriv riemannZeta s = - LSeries (fun n => (Λ n : ℂ)) s := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1, logDeriv_apply, neg_div, neg_neg]
  rw [hL, norm_neg,
    show LSeries (fun n => (Λ n : ℂ)) s = ∑' n, term (fun n => (Λ n : ℂ)) s n from rfl]
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_term_vonMangoldt hs1)) ?_
  exact (summable_norm_term_vonMangoldt hs1).tsum_le_tsum
    (fun n => norm_term_le_of_re_le_re _ (by simpa using hs) n)
    (summable_norm_term_vonMangoldt (by simp))

/-! ### The functional-equation fold -/

/-- `ξ(1 − s) = ξ(s)`.  Immediate from `completedRiemannZeta₀_one_sub`: the prefactor
`s(s−1)/2` is itself invariant under `s ↦ 1 − s`. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  simp only [riemannXi, completedRiemannZeta₀_one_sub]
  ring

/-- The fold, differentiated: `ξ'/ξ(1 − s) = −ξ'/ξ(s)`.  This is what carries the
left-hand vertical `Re s = −1` to the right-hand one `Re s = 2`. -/
theorem logDeriv_riemannXi_one_sub (s : ℂ) :
    logDeriv riemannXi (1 - s) = - logDeriv riemannXi s := by
  have hd : deriv riemannXi s = - deriv riemannXi (1 - s) := by
    have h1 : HasDerivAt (fun z : ℂ => riemannXi (1 - z)) (deriv riemannXi (1 - s) * -1) s :=
      HasDerivAt.comp s (differentiable_riemannXi (1 - s)).hasDerivAt
        ((hasDerivAt_id s).const_sub 1)
    rw [funext riemannXi_one_sub] at h1
    rw [h1.deriv]; ring
  rw [logDeriv_apply, logDeriv_apply, riemannXi_one_sub, hd, neg_div, neg_neg]

/-! ### The vertical estimate -/

/-- **`ξ'/ξ = O(log|Im s|)` on the line `Re s = 2`.** -/
theorem exists_norm_logDeriv_riemannXi_le_re_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = 2 → 2 ≤ |s.im| →
      ‖logDeriv riemannXi s‖ ≤ C * (1 + Real.log (2 + |s.im|)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_digamma_le_strip 1 1
  refine ⟨3 / 2 + ‖Complex.log (π : ℂ)‖ / 2 + C₀ / 2 + vonMangoldtSumTwo,
    by linarith [hC₀0, vonMangoldtSumTwo_nonneg, norm_nonneg (Complex.log (π : ℂ))], ?_⟩
  intro s hre him
  have him0 : s.im ≠ 0 := by
    intro h; rw [h] at him; simp at him; linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_re_eq_two hre
  have hlog : 0 ≤ Real.log (2 + |s.im|) :=
    Real.log_nonneg (by have := abs_nonneg s.im; linarith)
  -- `1/s`
  have hns : (2 : ℝ) ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hre] at this; simpa using le_trans (le_abs_self 2) this
  have h1 : ‖1 / s‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hns
  -- `1/(s-1)`
  have hns1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re, hre] at this
    norm_num at this
    exact this
  have h2 : ‖1 / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]; linarith
  -- the archimedean factor
  have hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    have : (s / 2).im = 0 := by rw [hm]; simp
    simp at this
    exact him0 (by linarith [this])
  have hre2 : (s / 2).re = 1 := by simp [hre]
  have him2 : 1 ≤ |(s / 2).im| := by
    have : (s / 2).im = s.im / 2 := by simp
    rw [this, abs_div]
    rw [le_div_iff₀ (by norm_num)]
    simpa using by linarith [him]
  have h3 : ‖logDeriv Gammaℝ s‖
      ≤ ‖Complex.log (π : ℂ)‖ / 2 + C₀ / 2 * (1 + Real.log (2 + |s.im|)) := by
    rw [logDeriv_gammaR hhalf]
    refine le_trans (norm_add_le _ _) ?_
    have hd := hC₀ (s / 2) hre2.ge hre2.le him2
    have hmono : Real.log (2 + |(s / 2).im|) ≤ Real.log (2 + |s.im|) := by
      have hij : (s / 2).im = s.im / 2 := by simp
      refine Real.log_le_log (by positivity) ?_
      rw [hij, abs_div]
      simp only [abs_two]
      linarith [abs_nonneg s.im]
    rw [norm_div, norm_div]
    simp only [Complex.norm_ofNat]
    have : ‖Complex.digamma (s / 2)‖ ≤ C₀ * (1 + Real.log (2 + |s.im|)) :=
      hd.trans (by nlinarith [hC₀0, hlog])
    rw [norm_neg]
    linarith
  -- assemble
  rw [logDeriv_riemannXi_eq_zeta_of_im_ne_zero him0 hζ]
  have h4 := norm_logDeriv_riemannZeta_le_of_two_le_re (s := s) (by rw [hre])
  have hone : (1 : ℝ) ≤ 1 + Real.log (2 + |s.im|) := by linarith
  calc ‖1 / s + 1 / (s - 1) + logDeriv Gammaℝ s + logDeriv riemannZeta s‖
      ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ + ‖logDeriv Gammaℝ s‖ + ‖logDeriv riemannZeta s‖ := by
        refine le_trans (norm_add_le _ _) ?_
        gcongr
        refine le_trans (norm_add_le _ _) ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ (3 / 2 + ‖Complex.log (π : ℂ)‖ / 2 + C₀ / 2 + vonMangoldtSumTwo)
          * (1 + Real.log (2 + |s.im|)) := by
        nlinarith [h1, h2, h3, h4, hone, hlog, vonMangoldtSumTwo_nonneg,
          norm_nonneg (Complex.log (π : ℂ)), hC₀0]

end Cvs.Zeta
