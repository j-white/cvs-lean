import Mathlib
import Cvs.Zeta.DigammaStrip
import Cvs.Zeta.GammaRLogDeriv
import Cvs.Zeta.RiemannXi
import Cvs.Zeta.XiZeroCountBridge
import Cvs.Zeta.ZetaLogDeriv
import Cvs.Zeta.ZetaPolyGrowth

/-!
# `ξ'/ξ` at height `T`

Rung 6's input, in the form the explicit formula sums over.
-/

open Complex Real Set Metric Finset

namespace Cvs.Zeta

/-- `ζ₁'/ζ₁ = 1/(s−1) + ζ'/ζ`, since `ζ₁ = (s−1)ζ`. -/
theorem logDeriv_riemannZeta₁_eq {z : ℂ} (hz : z ≠ 1) (hζ : riemannZeta z ≠ 0) :
    logDeriv riemannZeta₁ z = 1 / (z - 1) + logDeriv riemannZeta z := by
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hev : riemannZeta₁ =ᶠ[nhds z] fun w : ℂ => (w - 1) * riemannZeta w := by
    filter_upwards [(isOpen_compl_singleton (x := (1 : ℂ))).mem_nhds hz] with w hw
    exact riemannZeta₁_eq_mul hw
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := (differentiable_id.sub_const 1) z
  have hd2 : DifferentiableAt ℂ riemannZeta z := differentiableAt_riemannZeta hz
  have hlog : logDeriv riemannZeta₁ z
      = logDeriv (fun w : ℂ => (w - 1) * riemannZeta w) z := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hlog, logDeriv_fun_mul z hsub hζ hd1 hd2]
  congr 1
  rw [logDeriv_apply]
  simp

/-- `ξ'/ξ = 1/s + (Γ_ℝ)'/Γ_ℝ + ζ₁'/ζ₁` — the `1/(s−1)` is absorbed into `ζ₁`. -/
theorem logDeriv_riemannXi_eq_zeta₁ {z : ℂ} (hs : z.im ≠ 0)
    (hζ : riemannZeta z ≠ 0) :
    logDeriv riemannXi z = 1 / z + logDeriv Gammaℝ z + logDeriv riemannZeta₁ z := by
  rw [logDeriv_riemannXi_eq_zeta_of_im_ne_zero hs hζ,
    logDeriv_riemannZeta₁_eq (ne_one_of_im_ne_zero hs) hζ]
  ring

/-- **`ξ'/ξ` minus its nearby poles is `O(log T)`** — rung 6's input, in the form the explicit
formula sums over. -/
theorem exists_logDeriv_riemannXi_bound_at_height {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : 1 ≤ k) (hkr : 2 * r ≤ (k : ℝ) + 3 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 2 * r + 4 ≤ |T| →
      ∃ (S : Finset ℂ) (m : ℂ → ℕ), (∀ σ ∈ S, ‖σ‖ ≤ r) ∧
        ((∑ σ ∈ S, (m σ : ℤ))
          = ∑ᶠ u, MeromorphicOn.divisor (fun w : ℂ => riemannZeta₁ ((2 + T * I) + w))
              (Metric.closedBall (0 : ℂ) r) u) ∧
        (∀ σ ∈ S, riemannZeta₁ ((2 + T * I) + σ) = 0) ∧
        ∀ z : ℂ, ‖z - (2 + T * I)‖ ≤ r / 4 → (z - (2 + T * I)) ∉ S →
          riemannZeta z ≠ 0 →
          ‖logDeriv riemannXi z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ))‖
            ≤ K * (1 + Real.log |T|) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_logDeriv_riemannZeta₁_bound_at_height r hr k hk hkr
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_norm_digamma_le_strip (1 - r / 8) (1 + r / 8)
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine ⟨K₁ + 1 + ‖Complex.log (π : ℂ)‖ / 2 + Cψ * (1 + Real.log 3) / 2, by positivity, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ |T| := by linarith
  have hlogT : 0 ≤ Real.log |T| := Real.log_nonneg hT1
  obtain ⟨S, m, hSr, hcount, hSzero, hbound⟩ := hK₁ T (by linarith)
  refine ⟨S, m, hSr, hcount, hSzero, fun z hz hzS hζ => ?_⟩
  -- geometry of the disc
  have hre : |(z - (2 + T * I)).re| ≤ r / 4 := le_trans (Complex.abs_re_le_norm _) hz
  have him : |(z - (2 + T * I)).im| ≤ r / 4 := le_trans (Complex.abs_im_le_norm _) hz
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  simp only [Complex.add_re, Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  norm_num at hre him
  have hb1 := abs_le.mp hre
  have hb2 := abs_le.mp him
  have hzre : 2 - r / 4 ≤ z.re := by linarith
  have hzre2 : z.re ≤ 2 + r / 4 := by linarith
  have hzim : 2 ≤ |z.im| := by
    have := abs_sub_abs_le_abs_sub T z.im
    have h2 : |z.im - T| ≤ r / 4 := abs_le.mpr hb2
    have h3 : |T - z.im| ≤ r / 4 := by rwa [abs_sub_comm]
    linarith
  have hzim2 : |z.im| ≤ |T| + r / 4 := by
    linarith [abs_sub_abs_le_abs_sub z.im T, abs_le.mpr hb2]
  have hz1 : z ≠ 1 := by intro h; rw [h] at hzim; norm_num at hzim
  have hzim0 : z.im ≠ 0 := by
    intro h; rw [h] at hzim; norm_num at hzim
  -- the decomposition
  rw [logDeriv_riemannXi_eq_zeta₁ hzim0 hζ]
  have hhalf : ∀ mm : ℕ, z / 2 ≠ -mm := by
    intro mm hc
    have him0 : (z / 2).im = 0 := by rw [hc]; simp
    have hd : (z / 2).im = z.im / 2 := by simp
    rw [hd] at him0
    have hz0 : z.im = 0 := by linarith
    rw [hz0] at hzim
    norm_num at hzim
  rw [logDeriv_gammaR hhalf]
  -- the three pieces
  have hpsi : ‖Complex.digamma (z / 2)‖ ≤ Cψ * (1 + Real.log 3 + Real.log |T|) := by
    have hre2 : (z / 2).re = z.re / 2 := by simp
    have him2 : (z / 2).im = z.im / 2 := by simp
    have h := hCψ (z / 2) (by rw [hre2]; linarith) (by rw [hre2]; linarith)
      (by rw [him2, abs_div]; norm_num; linarith)
    refine h.trans ?_
    have harg : 2 + |(z / 2).im| ≤ 3 * |T| := by
      rw [him2, abs_div]
      norm_num
      linarith
    have := Real.log_le_log (by rw [him2]; positivity) harg
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    nlinarith [hCψ0]
  have hinv : ‖(1 : ℂ) / z‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by
      refine lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) ?_
      exact le_trans hzim (Complex.abs_im_le_norm z))]
    exact le_trans (by norm_num) (le_trans hzim (Complex.abs_im_le_norm z))
  have hz1b := hbound z hz hzS
  calc ‖1 / z + (-(Complex.log (π : ℂ)) / 2 + Complex.digamma (z / 2) / 2)
        + logDeriv riemannZeta₁ z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ))‖
      ≤ ‖(1 : ℂ) / z‖ + ‖-(Complex.log (π : ℂ)) / 2‖ + ‖Complex.digamma (z / 2) / 2‖
        + ‖logDeriv riemannZeta₁ z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ))‖ := by
        have := norm_add_le (1 / z + (-(Complex.log (π : ℂ)) / 2 + Complex.digamma (z / 2) / 2))
          (logDeriv riemannZeta₁ z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ)))
        have h2 := norm_add_le ((1 : ℂ) / z)
          (-(Complex.log (π : ℂ)) / 2 + Complex.digamma (z / 2) / 2)
        have h3 := norm_add_le (-(Complex.log (π : ℂ)) / 2) (Complex.digamma (z / 2) / 2)
        have h4 : (1 / z + (-(Complex.log (π : ℂ)) / 2 + Complex.digamma (z / 2) / 2)
            + logDeriv riemannZeta₁ z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ)))
            = (1 / z + (-(Complex.log (π : ℂ)) / 2 + Complex.digamma (z / 2) / 2))
              + (logDeriv riemannZeta₁ z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ))) := by
          ring
        rw [h4]
        linarith
    _ ≤ (K₁ + 1 + ‖Complex.log (π : ℂ)‖ / 2 + Cψ * (1 + Real.log 3) / 2)
        * (1 + Real.log |T|) := by
        have e1 : ‖-(Complex.log (π : ℂ)) / 2‖ = ‖Complex.log (π : ℂ)‖ / 2 := by
          rw [norm_div, norm_neg, Complex.norm_ofNat]
        have e2 : ‖Complex.digamma (z / 2) / 2‖ = ‖Complex.digamma (z / 2)‖ / 2 := by
          rw [norm_div, Complex.norm_ofNat]
        rw [e1, e2]
        nlinarith [hpsi, hinv, hz1b, hlogT, hCψ0, hK₁0, hlog3,
          norm_nonneg (Complex.log (π : ℂ)),
          mul_nonneg hCψ0 hlogT, mul_nonneg hK₁0 hlogT, mul_nonneg hlog3 hlogT,
          mul_nonneg (norm_nonneg (Complex.log (π : ℂ))) hlogT,
          mul_nonneg (mul_nonneg hCψ0 hlog3) hlogT]

end Cvs.Zeta
