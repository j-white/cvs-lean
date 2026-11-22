import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Cvs.Zeta.ZetaLowerBound
import Cvs.Zeta.ZetaPolyGrowthK
import Cvs.Zeta.ZetaZeroCount

/-!
# The zero count at an arbitrary radius

`Cvs.Zeta.ZetaZeroCount` fixes the counting radius at `9/4`.
-/

open Complex Real Set Metric

namespace Cvs.Zeta

theorem one_le_abs_im_of_mem_ball {R T : ℝ} (hT : R + 1 ≤ |T|) {z : ℂ}
    (hz : z ∈ closedBall (2 + T * I) R) : 1 ≤ |z.im| := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have him : |(z - (2 + T * I)).im| ≤ ‖z - (2 + T * I)‖ := Complex.abs_im_le_norm _
  have him' : (z - (2 + T * I)).im = z.im - T := by simp
  rw [him'] at him
  have hb : |z.im - T| ≤ R := le_trans him hz
  have h3 : |T - z.im| ≤ R := by rwa [abs_sub_comm] at hb
  linarith [abs_sub_abs_le_abs_sub T z.im]

theorem ne_one_of_mem_ball' {R T : ℝ} (hT : R + 1 ≤ |T|) {z : ℂ}
    (hz : z ∈ closedBall (2 + T * I) R) : z ≠ 1 := by
  intro h
  have := one_le_abs_im_of_mem_ball hT hz
  rw [h] at this
  norm_num at this

theorem re_ge_of_mem_ball {R T : ℝ} {z : ℂ} (hz : z ∈ closedBall (2 + T * I) R) :
    2 - R ≤ z.re ∧ z.re ≤ 2 + R := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre : |(z - (2 + T * I)).re| ≤ ‖z - (2 + T * I)‖ := Complex.abs_re_le_norm _
  have hre' : (z - (2 + T * I)).re = z.re - 2 := by simp
  rw [hre'] at hre
  have := abs_le.mp (le_trans hre hz)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

theorem abs_im_le_of_mem_ball {R T : ℝ} {z : ℂ} (hz : z ∈ closedBall (2 + T * I) R) :
    |z.im| ≤ |T| + R := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have him : |(z - (2 + T * I)).im| ≤ ‖z - (2 + T * I)‖ := Complex.abs_im_le_norm _
  have him' : (z - (2 + T * I)).im = z.im - T := by simp
  rw [him'] at him
  linarith [abs_sub_abs_le_abs_sub z.im T, le_trans him hz]

/-- The `ζ` bound on a sphere of arbitrary radius about `2 + iT`. -/
theorem norm_riemannZeta_le_on_sphere' {R T : ℝ} (hR : 0 < R) (k : ℕ) (hk : 1 ≤ k)
    (hkR : R ≤ (k : ℝ) + 3 / 2) (hT : R + 1 ≤ |T|) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : ℂ, (1 / 2 : ℝ) - k ≤ s.re → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ (k + 1))
    {z : ℂ} (hz : z ∈ sphere (2 + T * I) R) :
    ‖riemannZeta z‖ ≤ C * (1 + |T| + R) ^ (k + 1) := by
  have hzb : z ∈ closedBall (2 + T * I) R := by
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_sphere_iff_norm] at hz
    exact le_of_eq hz
  obtain ⟨hre1, hre2⟩ := re_ge_of_mem_ball hzb
  have him1 := one_le_abs_im_of_mem_ball hT hzb
  have him2 := abs_im_le_of_mem_ball hzb
  refine (hC z (by linarith) him1).trans ?_
  have : (1 + |z.im|) ^ (k + 1) ≤ (1 + |T| + R) ^ (k + 1) :=
    pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) (by linarith) _
  nlinarith [pow_nonneg (by linarith [abs_nonneg z.im] : (0:ℝ) ≤ 1 + |z.im|) (k + 1)]

/-- **The `O(log T)` zero count, at an arbitrary counting radius.** -/
theorem exists_zero_count_riemannZeta_ball' (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (hk : 1 ≤ k)
    (hkr : 2 * ρ ≤ (k : ℝ) + 3 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 2 * ρ + 1 ≤ |T| →
      ((∑ᶠ u, MeromorphicOn.divisor riemannZeta
          (closedBall (2 + T * I) ρ) u : ℤ) : ℝ)
        ≤ K * (1 + Real.log |T|) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannZeta_le_pow_of_re_ge k hk
  set C' : ℝ := C + 1 with hC'
  have hC'0 : 0 < C' := by rw [hC']; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmax0 : (0 : ℝ) < max 1 C' := lt_of_lt_of_le one_pos (le_max_left _ _)
  set A : ℝ := Real.log (max 1 C') with hA
  have hA0 : 0 ≤ A := Real.log_nonneg (le_max_left _ _)
  have hlr : (0 : ℝ) ≤ Real.log (1 + 2 * ρ) := Real.log_nonneg (by linarith)
  set a : ℝ := (A + ((k : ℝ) + 1) * (Real.log (1 + 2 * ρ) + Real.log 2)
    + Real.log 3) / Real.log 2 with hadef
  set bb : ℝ := ((k : ℝ) + 1) / Real.log 2 with hbdef
  refine ⟨max (max a bb) 0, le_max_right _ _, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ |T| := by linarith
  have hL : 0 ≤ Real.log |T| := Real.log_nonneg hT1
  set c : ℂ := 2 + T * I with hcdef
  have hcre : c.re = 2 := by simp [hcdef]
  set M : ℝ := max 1 (C' * (1 + |T| + 2 * ρ) ^ (k + 1)) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have habs_r : |ρ| = ρ := abs_of_pos hρ
  have habs_R : |2 * ρ| = 2 * ρ := abs_of_pos (by linarith)
  have hTR : 2 * ρ + 1 ≤ |T| := hT
  have hj := AnalyticOnNhd.sum_divisor_le (c := c) (r := ρ) (R := 2 * ρ) (M := M)
    (f := riemannZeta)
    (by rw [habs_r]; exact hρ)
    (by rw [habs_r, habs_R]; linarith)
    hM1
    (by
      rw [habs_R]
      exact fun z hz => analyticAt_riemannZeta (ne_one_of_mem_ball' hTR hz))
    (riemannZeta_ne_zero_of_re_eq_two hcre)
    (fun z hz => by
      rw [habs_R] at hz
      refine le_trans (norm_riemannZeta_le_on_sphere' (C := C') (by linarith) k hk hkr hTR
        hC'0.le ?_ hz) (le_max_right _ _)
      intro s h1 h2
      refine (hC s h1 h2).trans ?_
      have hp : (0 : ℝ) ≤ (1 + |s.im|) ^ (k + 1) :=
        pow_nonneg (by linarith [abs_nonneg s.im]) _
      rw [hC']
      nlinarith)
  rw [habs_r] at hj
  refine le_trans hj ?_
  rw [show (2 * ρ) / ρ = 2 by field_simp]
  have hzc : (1 : ℝ) / 3 ≤ ‖riemannZeta c‖ := one_third_le_norm_riemannZeta_of_re_eq_two hcre
  have hzc0 : (0 : ℝ) < ‖riemannZeta c‖ := by linarith
  have hlogzc : -Real.log 3 ≤ Real.log ‖riemannZeta c‖ := by
    have := Real.log_le_log (by norm_num) hzc
    rw [show (1 : ℝ) / 3 = 3⁻¹ by norm_num, Real.log_inv] at this
    linarith
  have hlogM : Real.log M ≤ A + ((k : ℝ) + 1)
      * (Real.log (1 + 2 * ρ) + Real.log 2 + Real.log |T|) := by
    have hpow1 : (1 : ℝ) ≤ (1 + |T| + 2 * ρ) ^ (k + 1) :=
      one_le_pow₀ (by linarith [abs_nonneg T])
    have hMle : M ≤ max 1 C' * (1 + |T| + 2 * ρ) ^ (k + 1) := by
      refine max_le ?_ ?_
      · nlinarith [le_max_left (1 : ℝ) C']
      · nlinarith [le_max_right (1 : ℝ) C']
    refine le_trans (Real.log_le_log hM0 hMle) ?_
    rw [Real.log_mul (ne_of_gt hmax0) (by positivity), Real.log_pow, hA]
    have h1 : (1 : ℝ) + |T| + 2 * ρ ≤ (1 + 2 * ρ) * (2 * |T|) := by nlinarith
    have h2 : Real.log (1 + |T| + 2 * ρ)
        ≤ Real.log (1 + 2 * ρ) + Real.log 2 + Real.log |T| := by
      refine (Real.log_le_log (by linarith [abs_nonneg T]) h1).trans ?_
      rw [Real.log_mul (by linarith) (by positivity),
        Real.log_mul (by norm_num) (by linarith)]
      linarith
    push_cast
    nlinarith [h2]
  have hfin : Real.log (M / ‖riemannZeta c‖) / Real.log 2 ≤ a + bb * Real.log |T| := by
    rw [Real.log_div (ne_of_gt hM0) (ne_of_gt hzc0), hadef, hbdef,
      div_mul_eq_mul_div, ← add_div]
    gcongr
    nlinarith [hlogM, hlogzc]
  refine hfin.trans ?_
  have hA' : a ≤ max (max a bb) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hB' : bb ≤ max (max a bb) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  nlinarith [hL]

end Cvs.Zeta
