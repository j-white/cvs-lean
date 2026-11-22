import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Cvs.Zeta.XiLogDeriv
import Cvs.Zeta.ZetaLowerBound
import Cvs.Zeta.ZetaPolyGrowth
import Cvs.Zeta.ZetaPolyGrowthK

/-!
# `ζ'/ζ` minus its nearby poles is `O(log T)`

Rung 6's actual input, and the end of the Landau programme.
-/

open Complex Real Set Metric

namespace Cvs.Zeta

theorem analyticOnNhd_riemannZeta₁ : AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
  fun z _ => differentiable_riemannZeta₁.analyticAt z

/-- `ζ₁` is not identically zero near any point: `ζ₁(1) = 1`. -/
theorem analyticOrderAt_riemannZeta₁_ne_top (u : ℂ) :
    analyticOrderAt riemannZeta₁ u ≠ ⊤ := by
  intro htop
  have hev : riemannZeta₁ =ᶠ[nhds u] 0 := analyticOrderAt_eq_top.mp htop
  have hall : Set.EqOn riemannZeta₁ 0 Set.univ :=
    analyticOnNhd_riemannZeta₁.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ u) hev
  have h1 : riemannZeta₁ 1 = 0 := hall (Set.mem_univ 1)
  rw [riemannZeta₁_one] at h1
  norm_num at h1

/-- **`ζ₁` is bounded below at `2 + iT`, uniformly in `T`.** This is what makes `ζ₁` and not `ξ`
the right function to run Landau on: `‖ζ₁(2+iT)‖ = ‖1+iT‖·‖ζ(2+iT)‖ ≥ 1·(2 − π²/6)`, with no
archimedean factor to decay. -/
theorem norm_riemannZeta₁_ge_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    (1 : ℝ) / 3 ≤ ‖riemannZeta₁ s‖ := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [riemannZeta₁_eq_mul hs1, norm_mul]
  have hz := one_third_le_norm_riemannZeta_of_re_eq_two hs
  have hlow : (1 : ℝ) ≤ ‖s - 1‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm (s - 1))
    have : (s - 1).re = 1 := by rw [Complex.sub_re, hs]; norm_num
    rw [this]; norm_num
  nlinarith [norm_nonneg (riemannZeta s)]

theorem riemannZeta₁_ne_zero_of_re_eq_two {s : ℂ} (hs : s.re = 2) : riemannZeta₁ s ≠ 0 := by
  intro h
  have := norm_riemannZeta₁_ge_of_re_eq_two hs
  rw [h, norm_zero] at this
  linarith

/-- `ζ₁` is polynomially bounded on any strip `[1/2 − k, b]` off the real axis. -/
theorem exists_norm_riemannZeta₁_le_pow_strip (k : ℕ) (hk : 1 ≤ k) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (1 / 2 : ℝ) - k ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖riemannZeta₁ s‖ ≤ C * (1 + |s.im|) ^ (k + 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta_le_pow_of_re_ge k hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set B : ℝ := |b| + k + 1 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨B * C, by positivity, fun s h1 h2 h3 => ?_⟩
  have hu : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hs1 : s ≠ 1 := by intro h; rw [h] at h3; norm_num at h3
  have hup : ‖s - 1‖ ≤ B * (1 + |s.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hr : (s - 1).re = s.re - 1 := by simp
    have hi : (s - 1).im = s.im := by simp
    rw [hr, hi]
    have hb1 : s.re ≤ |b| := le_trans h2 (le_abs_self b)
    have hb2 : -(|b| + (k : ℝ) + 1) ≤ s.re - 1 := by linarith [abs_nonneg b]
    have : |s.re - 1| ≤ B := abs_le.mpr ⟨by rw [hB]; linarith, by rw [hB]; linarith⟩
    nlinarith
  rw [riemannZeta₁_eq_mul hs1, norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖
      ≤ (B * (1 + |s.im|)) * (C * (1 + |s.im|) ^ (k + 1)) :=
        mul_le_mul hup (hC s h1 h3) (norm_nonneg _) (by positivity)
    _ = B * C * (1 + |s.im|) ^ (k + 2) := by rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ]; ring

/-- **`ζ'/ζ` minus its nearby poles is `O(log T)`** — rung 6's input, at last. -/
theorem exists_logDeriv_riemannZeta₁_bound_at_height (r : ℝ) (hr : 0 < r) (k : ℕ)
    (hk : 1 ≤ k) (hkr : 2 * r ≤ (k : ℝ) + 3 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 2 * r + 1 ≤ |T| →
      ∃ (S : Finset ℂ) (m : ℂ → ℕ), (∀ σ ∈ S, ‖σ‖ ≤ r) ∧
        ((∑ σ ∈ S, (m σ : ℤ))
          = ∑ᶠ u, MeromorphicOn.divisor (fun w : ℂ => riemannZeta₁ ((2 + T * I) + w))
              (Metric.closedBall (0 : ℂ) r) u) ∧
        (∀ σ ∈ S, riemannZeta₁ ((2 + T * I) + σ) = 0) ∧
        ∀ z : ℂ, ‖z - (2 + T * I)‖ ≤ r / 4 → (z - (2 + T * I)) ∉ S →
          ‖logDeriv riemannZeta₁ z - ∑ σ ∈ S, (m σ : ℂ) / (z - ((2 + T * I) + σ))‖
            ≤ K * (1 + Real.log |T|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta₁_le_pow_strip k hk (2 + 2 * r)
  set C' : ℝ := C + 1 with hC'
  have hC'0 : 0 < C' := by rw [hC']; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set a : ℝ := 8 * (Real.log C' + ((k : ℝ) + 2) * (Real.log (1 + 2 * r) + Real.log 2)
    + Real.log 3 + 1) / r with hadef
  set bb : ℝ := 8 * ((k : ℝ) + 2) / r with hbdef
  refine ⟨max (max a bb) 0, le_max_right _ _, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ |T| := by linarith
  have hlogT : 0 ≤ Real.log |T| := Real.log_nonneg hT1
  set c : ℂ := 2 + T * I with hcdef
  have hcre : c.re = 2 := by simp [hcdef]
  have hcim : c.im = T := by simp [hcdef]
  set M : ℝ := C' * (1 + |T| + 2 * r) ^ (k + 2) with hMdef
  -- the circle bound
  have hMbd : ∀ z : ℂ, ‖z - c‖ = 2 * r → ‖riemannZeta₁ z‖ ≤ M := by
    intro z hz
    have hre : |(z - c).re| ≤ 2 * r := le_trans (Complex.abs_re_le_norm _) (le_of_eq hz)
    have him : |(z - c).im| ≤ 2 * r := le_trans (Complex.abs_im_le_norm _) (le_of_eq hz)
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    have hb1 := abs_le.mp hre
    have hb2 := abs_le.mp him
    have h2 : |z.im - T| ≤ 2 * r := abs_le.mpr hb2
    have h3 : |T - z.im| ≤ 2 * r := by rwa [abs_sub_comm]
    have hlow : (1 : ℝ) ≤ |z.im| := by
      linarith [abs_sub_abs_le_abs_sub T z.im]
    have hhigh : |z.im| ≤ |T| + 2 * r := by
      linarith [abs_sub_abs_le_abs_sub z.im T]
    have hzb := hC z (by linarith [hb1.1]) (by linarith [hb1.2]) hlow
    refine hzb.trans ?_
    rw [hMdef]
    have hmono : (1 + |z.im|) ^ (k + 2) ≤ (1 + |T| + 2 * r) ^ (k + 2) :=
      pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) (by linarith) _
    nlinarith [hC0, pow_nonneg (by linarith [abs_nonneg z.im] : (0:ℝ) ≤ 1 + |z.im|) (k + 2)]
  obtain ⟨S, m, hSr, hcount, hSzero, hbound⟩ := exists_logDeriv_sub_sum_le_center analyticOnNhd_riemannZeta₁
    analyticOrderAt_riemannZeta₁_ne_top hr (riemannZeta₁_ne_zero_of_re_eq_two hcre) hMbd
  refine ⟨S, m, hSr, hcount, hSzero, fun z hz hzS => ?_⟩
  refine (hbound z hz hzS).trans ?_
  -- now the arithmetic: `log M` is `O(log T)` and `log ‖ζ₁ c‖ ≥ -log 3`
  have hnorm : (1 : ℝ) / 3 ≤ ‖riemannZeta₁ c‖ := norm_riemannZeta₁_ge_of_re_eq_two hcre
  have hnorm0 : (0 : ℝ) < ‖riemannZeta₁ c‖ := by linarith
  have hlogc : -Real.log 3 ≤ Real.log ‖riemannZeta₁ c‖ := by
    have := Real.log_le_log (by norm_num) hnorm
    rw [show (1 : ℝ) / 3 = 3⁻¹ by norm_num, Real.log_inv] at this
    linarith
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hlogM : Real.log M ≤ Real.log C' + ((k : ℝ) + 2)
      * (Real.log (1 + 2 * r) + Real.log 2 + Real.log |T|) := by
    rw [hMdef, Real.log_mul (ne_of_gt hC'0) (by positivity), Real.log_pow]
    have h1 : (1 : ℝ) + |T| + 2 * r ≤ (1 + 2 * r) * (2 * |T|) := by nlinarith
    have h2 : Real.log (1 + |T| + 2 * r) ≤ Real.log (1 + 2 * r) + Real.log 2 + Real.log |T| := by
      refine (Real.log_le_log (by positivity) h1).trans ?_
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by linarith)]
      linarith
    push_cast
    nlinarith [h2]
  have hfin : 8 * (Real.log M - Real.log ‖riemannZeta₁ c‖ + 1) / r ≤ a + bb * Real.log |T| := by
    rw [hadef, hbdef, div_mul_eq_mul_div, ← add_div]
    gcongr
    nlinarith [hlogM, hlogc]
  refine hfin.trans ?_
  have hA : a ≤ max (max a bb) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hB : bb ≤ max (max a bb) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  nlinarith [hlogT]

end Cvs.Zeta
