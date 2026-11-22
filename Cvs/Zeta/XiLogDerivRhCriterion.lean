import Mathlib
import Cvs.Zeta.AllZerosOnLine
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.Hadamard
import Cvs.Zeta.HadamardProduct.GenusOneSummable
import Cvs.Zeta.HadamardProduct.HadamardXiSplit
import Cvs.Zeta.HadamardProduct.XiLogDerivClean
import Cvs.Zeta.HadamardProduct.XiLogDerivReflection
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiStrip
import Cvs.Zeta.XiVertical

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The global criterion: RH ⟺ `Re ξ'/ξ ≥ 0` on `Re s > 1/2`

Every window form is a restriction of one Weil distribution whose Laplace transform is `ξ'/ξ`; this is that
object's positivity. With `XiLogDerivClean`'s closed form and `ξ'/ξ(1/2) = 0`, `ξ'/ξ(z) = Σ_ρ (1/(z − ρ) − 1/(1/2 − ρ))`, a sum of
Poisson terms `(σ − 1/2)/|z − ρ|²` under RH; conversely an off-line zero `ρ` makes `Re ξ'/ξ → −∞` just left of `ρ`.
The criterion is Lagarias, Acta Arith. 89 (1999); see also Hinkkanen (1997) and Sondow–Dumitrescu (2010).
-/

noncomputable section

open Complex Filter Topology Cvs.Zeta

namespace Cvs.Zeta.XiLogDerivRhCriterion
open Cvs.ZeroFree

/-- Zeros of `ξ` lie outside the closed unit disc. -/
theorem one_lt_norm_zeroSeq (n : zeroIndex riemannXi) : 1 < ‖zeroSeq riemannXi n‖ := by
  by_contra h
  push Not at h
  exact Cvs.ZeroFree.riemannXi_ne_zero_of_norm_le_one h (Cvs.ZeroFree.riemannXi_zeroSeq n)

theorem summable_genus {z : ℂ} (hz : riemannXi z ≠ 0) :
    Summable fun n : zeroIndex riemannXi => 1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n :=
  Cvs.ZeroFree.summable_genus_one summable_inv_norm_sq_riemannXi (fun n => (one_lt_norm_zeroSeq n).le)
    fun n h => hz (h ▸ Cvs.ZeroFree.riemannXi_zeroSeq n)

theorem riemannXi_half_ne_zero : riemannXi (1 / 2) ≠ 0 :=
  Cvs.ZeroFree.riemannXi_ne_zero_of_norm_le_one (by norm_num)

/-- **`ξ'/ξ` centred at `1/2`**: `ξ'/ξ(z) = Σ_ρ (1/(z − ρ) − 1/(1/2 − ρ))` off the zeros. -/
theorem logDeriv_eq_tsum {z : ℂ} (hz : riemannXi z ≠ 0) :
    logDeriv riemannXi z
      = ∑' n : zeroIndex riemannXi, (1 / (z - zeroSeq riemannXi n) - 1 / (1 / 2 - zeroSeq riemannXi n)) := by
  have h1 := Cvs.ZeroFree.logDeriv_riemannXi_clean hz
  have h2 := Cvs.ZeroFree.logDeriv_riemannXi_clean riemannXi_half_ne_zero
  rw [Cvs.ZeroFree.logDeriv_riemannXi_half] at h2
  have hsub := ((summable_genus hz).tsum_sub (summable_genus riemannXi_half_ne_zero)).symm
  have e : (fun n : zeroIndex riemannXi =>
      (1 / (z - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n)
        - (1 / (1 / 2 - zeroSeq riemannXi n) + 1 / zeroSeq riemannXi n))
      = fun n => 1 / (z - zeroSeq riemannXi n) - 1 / (1 / 2 - zeroSeq riemannXi n) := by
    funext n; ring
  rw [e] at hsub
  rw [← hsub]
  linear_combination h1 - h2

/-- Under RH every zero of `ξ` is on the line. -/
theorem re_zeroSeq_of_rh (hRH : RiemannHypothesis) (n : zeroIndex riemannXi) :
    (zeroSeq riemannXi n).re = 1 / 2 := by
  have hξ := Cvs.ZeroFree.riemannXi_zeroSeq n
  obtain ⟨h0, h1⟩ := riemannXi_zero_mem_strip hξ
  have hne : zeroSeq riemannXi n ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hζ := (riemannXi_eq_zero_iff_riemannZeta h0 hne).mp hξ
  refine hRH _ hζ ?_ hne
  rintro ⟨k, hk⟩
  have := congrArg Complex.re hk
  simp at this
  linarith

/-- **The Poisson form under RH**: `Re ξ'/ξ(z) = Σ_ρ (σ − 1/2)/|z − ρ|² ≥ 0` for `Re z > 1/2`. -/
theorem re_logDeriv_nonneg_of_rh (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re) (hξ : riemannXi z ≠ 0) :
    0 ≤ (logDeriv riemannXi z).re := by
  rw [logDeriv_eq_tsum hξ]
  have hs : Summable fun n : zeroIndex riemannXi =>
      1 / (z - zeroSeq riemannXi n) - 1 / (1 / 2 - zeroSeq riemannXi n) := by
    have := (summable_genus hξ).sub (summable_genus riemannXi_half_ne_zero)
    refine this.congr fun n => ?_
    ring
  rw [Complex.re_tsum hs]
  refine tsum_nonneg fun n => ?_
  have hρ := re_zeroSeq_of_rh hRH n
  set ρ := zeroSeq riemannXi n
  rw [Complex.sub_re, one_div, one_div, Complex.inv_re, Complex.inv_re]
  have h2 : (1 / 2 - ρ).re = 0 := by simp [hρ]
  have h1 : 0 < (z - ρ).re := by simp [hρ]; linarith
  rw [h2, zero_div, sub_zero]
  exact div_nonneg h1.le (Complex.normSq_nonneg _)

/-- `log`-derivative of `(w − ρ)^n · g` off `ρ`. -/
theorem logDeriv_pow_mul {ρ z : ℂ} {g : ℂ → ℂ} (n : ℕ) (hz : z ≠ ρ) (hg : g z ≠ 0) (hgd : DifferentiableAt ℂ g z) :
    logDeriv (fun w => (w - ρ) ^ n * g w) z = n / (z - ρ) + logDeriv g z := by
  have hzρ : z - ρ ≠ 0 := sub_ne_zero.mpr hz
  have hpd : DifferentiableAt ℂ (fun w : ℂ => (w - ρ) ^ n) z := ((differentiableAt_id).sub_const ρ).pow n
  rw [show (fun w => (w - ρ) ^ n * g w) = (fun w : ℂ => (w - ρ) ^ n) * g from rfl,
    logDeriv_mul (f := fun w : ℂ => (w - ρ) ^ n) z (pow_ne_zero n hzρ) hg hpd hgd]
  congr 1
  have hd : HasDerivAt (fun w : ℂ => (w - ρ) ^ n) ((n : ℂ) * (z - ρ) ^ (n - 1) * 1) z :=
    ((hasDerivAt_id z).sub_const ρ).pow n
  rw [logDeriv_apply, hd.deriv]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel, mul_one, pow_succ]
    field_simp

/-- **An off-line zero drives `Re ξ'/ξ` to `−∞` on its left.** If `Re ξ'/ξ ≥ 0` on `Re s > 1/2` off the zeros, RH. -/
theorem riemannHypothesis_of_re_logDeriv_nonneg
    (h : ∀ z : ℂ, 1 / 2 < z.re → riemannXi z ≠ 0 → 0 ≤ (logDeriv riemannXi z).re) : RiemannHypothesis := by
  rw [← Cvs.Operator.allZerosOnLine_iff_rh]
  by_contra hnot
  obtain ⟨ρ₀, hre⟩ := Cvs.Zeta.GaussKernel.AdmissibleKernel.exists_offLine_of_not_allZerosOnLine hnot
  obtain ⟨hz, h0, h1⟩ := ρ₀.2
  have hρ1 : (ρ₀ : ℂ) ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hξ0 : riemannXi ρ₀ = 0 := (riemannXi_eq_zero_iff_riemannZeta h0 hρ1).2 hz
  obtain ⟨ρ, hξ, hβ⟩ : ∃ ρ : ℂ, riemannXi ρ = 0 ∧ 1 / 2 < ρ.re := by
    rcases lt_or_gt_of_ne hre with hl | hl
    · exact ⟨1 - ρ₀, by rw [riemannXi_one_sub]; exact hξ0, by simp; linarith⟩
    · exact ⟨ρ₀, hξ0, hl⟩
  -- the local factorisation `ξ = (z − ρ)^n g`, `g(ρ) ≠ 0`
  have hA : AnalyticAt ℂ riemannXi ρ := analyticOnNhd_riemannXi ρ (Set.mem_univ _)
  have hnz : ¬ ∀ᶠ z in 𝓝 ρ, riemannXi z = 0 := by
    intro hev
    exact riemannXi_half_ne_zero (analyticOnNhd_riemannXi.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ ρ) hev (Set.mem_univ _))
  obtain ⟨n, g, hg, hgρ, hfac⟩ := hA.exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hnz
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have := hfac.self_of_nhds
      simp only [pow_zero, one_smul] at this
      exact absurd (this.symm.trans hξ) hgρ
    · exact hpos
  -- a ball on which the factorisation holds, `g ≠ 0`, `g` is differentiable and `‖g'/g‖ ≤ M`
  set M := ‖logDeriv g ρ‖ + 1 with hM
  have hcont : ContinuousAt (logDeriv g) ρ := by
    have hdg : ContinuousAt (deriv g) ρ := hg.deriv.continuousAt
    have : ContinuousAt (fun w => deriv g w / g w) ρ := hdg.div hg.continuousAt hgρ
    exact this
  have hevM : ∀ᶠ w in 𝓝 ρ, ‖logDeriv g w‖ < M := by
    have := hcont.norm.eventually (gt_mem_nhds (show ‖logDeriv g ρ‖ < M by rw [hM]; linarith))
    exact this
  have hevall := hfac.and ((hg.eventually_analyticAt).and ((hg.continuousAt.eventually_ne hgρ).and hevM))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevall
  -- the point `z = ρ − ε`
  set δ := ρ.re - 1 / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ε : ℝ := min (r / 2) (min (δ / 2) (1 / (M + 1))) with hε
  have hM0 : 0 < M := by rw [hM]; positivity
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεδ : ε < δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hεM : ε ≤ 1 / (M + 1) := (min_le_right _ _).trans (min_le_right _ _)
  set z : ℂ := ρ - (ε : ℂ) with hzdef
  have hzball : z ∈ Metric.ball ρ r := by
    rw [Metric.mem_ball, hzdef, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε0]
    exact hεr
  obtain ⟨hfz, hgaz, hgz, hMz⟩ := hball z hzball
  have hzρ : z ≠ ρ := by
    rw [hzdef]; intro h
    have := congrArg Complex.re h
    simp at this; linarith
  have hzre : 1 / 2 < z.re := by rw [hzdef]; simp; linarith
  have hξz : riemannXi z ≠ 0 := by
    rw [hfz, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzρ)) hgz
  -- `ξ'/ξ(z) = n/(z − ρ) + g'/g(z)`
  have hloc : riemannXi =ᶠ[𝓝 z] fun w => (w - ρ) ^ n * g w := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzball] with w hw
    have := (hball w hw).1
    rw [this, smul_eq_mul]
  have hld : logDeriv riemannXi z = n / (z - ρ) + logDeriv g z := by
    rw [logDeriv_apply, hloc.deriv_eq, hloc.self_of_nhds, ← logDeriv_apply]
    exact logDeriv_pow_mul n hzρ hgz hgaz.differentiableAt
  have hpos := h z hzre hξz
  rw [hld, Complex.add_re] at hpos
  have hzρv : z - ρ = -(ε : ℂ) := by rw [hzdef]; ring
  have hfirst : ((n : ℂ) / (z - ρ)).re = -(n / ε) := by
    rw [hzρv, div_neg, Complex.neg_re, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsecond : (logDeriv g z).re < M := lt_of_le_of_lt (Complex.re_le_norm _) hMz
  have hbig : M + 1 ≤ n / ε := by
    have h1' : M + 1 ≤ 1 / ε := by
      rw [le_div_iff₀ hε0]
      calc (M + 1) * ε ≤ (M + 1) * (1 / (M + 1)) := mul_le_mul_of_nonneg_left hεM (by positivity)
        _ = 1 := by field_simp
    have h2' : 1 / ε ≤ n / ε := div_le_div_of_nonneg_right (by exact_mod_cast hn) hε0.le
    linarith
  rw [hfirst] at hpos
  linarith

/-- **The global criterion**: RH ⟺ `Re ξ'/ξ(z) ≥ 0` for every `z` with `Re z > 1/2` off the zeros of `ξ`. -/
theorem riemannHypothesis_iff_re_logDeriv_nonneg :
    RiemannHypothesis ↔ ∀ z : ℂ, 1 / 2 < z.re → riemannXi z ≠ 0 → 0 ≤ (logDeriv riemannXi z).re :=
  ⟨fun hRH _ hz hξ => re_logDeriv_nonneg_of_rh hRH hz hξ, riemannHypothesis_of_re_logDeriv_nonneg⟩

end Cvs.Zeta.XiLogDerivRhCriterion
