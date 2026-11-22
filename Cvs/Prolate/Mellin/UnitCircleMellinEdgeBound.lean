import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Cvs.Prolate.Mellin.FrozenRiccatiRoot
import Cvs.Prolate.Mellin.FrozenRootLogIntegral
import Cvs.Prolate.Mellin.FrozenRootResidual
import Cvs.Prolate.Mellin.UnitCircleMellinSolution
import Cvs.Upstream.DiscreteGronwallRecurrence

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The unit-circle Mellin transform of a prolate solution is bounded by its edge value

For an entire solution `H` of `(1 − z²)H″ − 2zH′ + (χ − c²z²)H = 0`, `|χ| ≤ c²`, `c ≥ 10`, `p = τ − ig`,
`τ ∈ [−1/2, 3/2]`, `g ≥ 4c`: `|pM(p)| ≤ 4e⁶|H(1)|`. Along `p_m = p + 2m` the recurrence of Cvs.Prolate.Mellin.UnitCircleMellinSolution divided by the
partial products of the frozen roots `σ(p_k^{−2})` is a perturbed contraction (Cvs.Prolate.Mellin.FrozenRootResidual), so Cvs.Upstream.DiscreteGronwallRecurrence applies; the real
part of `Σ log σ(p_k^{−2})` is a trapezoid remainder plus `−½ Re ∫_0^{x₁} F`, by `Re ∫_0^∞ F = 0` (Cvs.Prolate.Mellin.FrozenRootLogIntegral).
-/

noncomputable section

open Real Set MeasureTheory Complex Filter Topology intervalIntegral
open scoped Interval
open Cvs.Prolate.Mellin.FrozenRiccatiRoot (sig hh norm_hh_le norm_hh_sub_le)
open Cvs.Prolate.Mellin.FrozenRootLogIntegral (Fq lineF)
open Cvs.Prolate.Mellin.FrozenRootResidual (pm aR bR)

namespace Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound

theorem pm_eq (τ g : ℝ) (m : ℕ) : pm τ g m = pm τ g 0 + 2 * m := by unfold pm; push_cast; ring

theorem pm_succ (τ g : ℝ) (m : ℕ) : pm τ g (m + 1) = pm τ g m + 2 := by unfold pm; push_cast; ring

theorem im_pm (τ g : ℝ) (m : ℕ) : (pm τ g m).im = -g := by simp [pm]

theorem re_pm (τ g : ℝ) (m : ℕ) : (pm τ g m).re = τ + 2 * m := by simp [pm]

theorem norm_pm_ge (τ g : ℝ) (m : ℕ) : g ≤ ‖pm τ g m‖ := Cvs.Prolate.Mellin.FrozenRootLogIntegral.le_norm_line

/-- `F(p_m) = log σ(p_m^{−2})` is the line function at `x_m = τ + 2m`. -/
theorem Fq_pm (χ c τ g : ℝ) (m : ℕ) : Fq χ c (pm τ g m) = lineF χ c g (τ + 2 * m) := rfl

/-- **The recurrence along the lattice**: `R_m = a(p_{m+1})R_{m+1} + b(p_{m+1})R_{m+2}`, `R = pM(p)`. -/
theorem rec_lattice {H : ℂ → ℂ} (hH : Differentiable ℂ H) {χ c : ℝ}
    (hode : ∀ z, (1 - z ^ 2) * deriv (deriv H) z - 2 * z * deriv H z + ((χ : ℂ) - (c : ℂ) ^ 2 * z ^ 2) * H z = 0)
    {τ g : ℝ} (hg : 0 < g) (m : ℕ) :
    pm τ g m * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H (pm τ g m) = aR χ (pm τ g (m + 1)) * (pm τ g (m + 1) * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H (pm τ g (m + 1)))
      + bR c (pm τ g (m + 1)) * (pm τ g (m + 2) * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H (pm τ g (m + 2))) := by
  set q := pm τ g (m + 1) with hqd
  have hq : q.im < 0 := by rw [hqd, im_pm]; linarith
  have h := Cvs.Prolate.Mellin.UnitCircleMellinSolution.recurrence hH hode hq
  have e1 : q - 2 = pm τ g m := by rw [hqd, pm_succ]; ring
  have e2 : q + 2 = pm τ g (m + 2) := by rw [hqd]; exact (pm_succ τ g (m + 1)).symm
  rw [← e1, ← e2]
  have hne : ∀ z : ℂ, z.im = -g → z ≠ 0 := fun z hz h0 => by rw [h0] at hz; simp at hz; linarith
  have hq0 : q ≠ 0 := hne q (by rw [hqd, im_pm])
  have hq1 : q - 1 ≠ 0 := hne (q - 1) (by rw [hqd]; simp [im_pm])
  have hq2 : q + 2 ≠ 0 := hne (q + 2) (by rw [hqd]; simp [im_pm])
  unfold aR bR
  field_simp
  linear_combination h

/-! ### The frozen-root product -/

section product

variable {χ c τ g : ℝ}

theorem c_sq_div_le (hc : 0 < c) (hg : 4 * c ≤ g) : c ^ 2 / g ^ 2 ≤ 1 / 16 := by
  rw [div_le_iff₀ (by nlinarith)]; nlinarith

/-- `x_{k+1} = τ + 2(k + 1) ≥ k + 1` bounds `|p_{k+1}|` below. -/
theorem norm_pm_ge_succ (hτ : -1 / 2 ≤ τ) (k : ℕ) : (k : ℝ) + 1 ≤ ‖pm τ g (k + 1)‖ := by
  have := Complex.re_le_norm (pm τ g (k + 1))
  rw [re_pm] at this; push_cast at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The terms `log σ(p_{k+1}^{−2})` are absolutely summable. -/
theorem summable_Fq (hc : 0 < c) (hχ : |χ| ≤ c ^ 2) (hτ : -1 / 2 ≤ τ) (hg : 4 * c ≤ g) :
    Summable fun k : ℕ => ‖Fq χ c (pm τ g (k + 1))‖ := by
  have hb : ∀ k : ℕ, ‖Fq χ c (pm τ g (k + 1))‖ ≤ 6 * c ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := fun k => by
    have h1 := Cvs.Prolate.Mellin.FrozenRootLogIntegral.norm_Fq_le hc hχ (hg.trans (norm_pm_ge τ g (k + 1)))
    have h2 := norm_pm_ge_succ (g := g) hτ k
    refine h1.trans ?_
    rw [mul_one_div]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    push_cast; exact pow_le_pow_left₀ (by positivity) h2 2
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ((Summable.mul_left _ ?_))
  exact (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)

/-- **The trapezoid remainder**: `|F(p_{k+1}) − ½∫_{x}^{x+2} F(u − ig) du| ≤ 66c²/|p_{k+1}|³`. -/
theorem norm_trap_le (hc : 10 ≤ c) (hχ : |χ| ≤ c ^ 2) (hτ : -1 / 2 ≤ τ) (hg : 4 * c ≤ g) (k : ℕ) :
    ‖Fq χ c (pm τ g (k + 1)) - (1 / 2) * ∫ u in (τ + 2 * ((k + 1 : ℕ) : ℝ))..(τ + 2 * ((k + 1 : ℕ) : ℝ)) + 2,
      lineF χ c g u‖ ≤ 66 * c ^ 2 / ‖pm τ g (k + 1)‖ ^ 3 := by
  have hc0 : 0 < c := by linarith
  set x := τ + 2 * ((k + 1 : ℕ) : ℝ) with hxd
  set p := pm τ g (k + 1) with hpd
  set P := ‖p‖ with hPd
  have hP : 4 * c ≤ P := hg.trans (norm_pm_ge τ g (k + 1))
  have hP40 : 40 ≤ P := by linarith
  have hre : 0 ≤ p.re := by
    rw [hpd, re_pm]; push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hp0 : p ≠ 0 := norm_pos_iff.1 (by linarith)
  have hcont : Continuous (lineF χ c g) := Cvs.Prolate.Mellin.FrozenRootLogIntegral.continuous_lineF hc0 hχ hg
  have hpt : ∀ u ∈ Ι x (x + 2), ‖lineF χ c g x - lineF χ c g u‖ ≤ 66 * c ^ 2 / P ^ 3 := by
    intro u hu
    rw [uIoc_of_le (by linarith)] at hu
    set t := u - x with htd
    have ht0 : 0 ≤ t := by linarith [hu.1]
    have ht2 : t ≤ 2 := by linarith [hu.2]
    have hq : (u : ℂ) + ((-g : ℝ) : ℂ) * I = p + t := by
      rw [hpd, htd]; unfold pm; rw [hxd]; push_cast; ring
    have hlx : lineF χ c g x = hh χ c ((p ^ 2)⁻¹) := rfl
    have hlu : lineF χ c g u = hh χ c (((p + t) ^ 2)⁻¹) := by
      show Fq χ c ((u : ℂ) + ((-g : ℝ) : ℂ) * I) = _
      rw [hq]; rfl
    rw [hlx, hlu]
    have hw1 := Cvs.Prolate.Mellin.FrozenRootResidual.c_sq_w_le hc0 hP
    have hPt : P ≤ ‖p + t‖ := Cvs.Prolate.Mellin.FrozenRootResidual.norm_le_norm_add hre ht0
    have hw2 := Cvs.Prolate.Mellin.FrozenRootResidual.c_sq_w_le hc0 (hP.trans hPt)
    have hlip := norm_hh_sub_le hχ hw1 hw2
    have hws := Cvs.Prolate.Mellin.FrozenRootResidual.norm_w_sub_le hre hp0 ht0
    rw [norm_sub_rev (((p + t) ^ 2)⁻¹)] at hws
    have hbound : t * (2 * P + t) / P ^ 4 ≤ (41 / 10) / P ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : t * (2 * P + t) ≤ 2 * (2 * P + 2) := by nlinarith
      have h2 : 2 * (2 * P + 2) ≤ 41 / 10 * P := by linarith
      have h3 : 0 ≤ P ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (h1.trans h2) h3]
    calc ‖hh χ c ((p ^ 2)⁻¹) - hh χ c (((p + t) ^ 2)⁻¹)‖ ≤ 16 * c ^ 2 * ‖(p ^ 2)⁻¹ - ((p + t) ^ 2)⁻¹‖ := hlip
      _ ≤ 16 * c ^ 2 * ((41 / 10) / P ^ 3) := by gcongr; exact hws.trans hbound
      _ ≤ 66 * c ^ 2 / P ^ 3 := by
          rw [show 16 * c ^ 2 * ((41 / 10) / P ^ 3) = (328 / 5) * (c ^ 2 / P ^ 3) by ring,
            show 66 * c ^ 2 / P ^ 3 = 66 * (c ^ 2 / P ^ 3) by ring]
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hint : IntervalIntegrable (lineF χ c g) volume x (x + 2) := hcont.intervalIntegrable _ _
  have e : Fq χ c p - (1 / 2) * ∫ u in x..x + 2, lineF χ c g u
      = (1 / 2) * ∫ u in x..x + 2, (lineF χ c g x - lineF χ c g u) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint, intervalIntegral.integral_const]
    simp only [add_sub_cancel_left, real_smul]
    have : Fq χ c p = lineF χ c g x := rfl
    rw [this]; push_cast; ring
  rw [e, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  have := norm_integral_le_of_norm_le_const hpt
  rw [show |x + 2 - x| = 2 by rw [add_sub_cancel_left, abs_of_pos two_pos] ] at this
  linarith

/-- **The real part of the frozen-root series is at most `6`**. -/
theorem re_tsum_Fq_le (hc : 10 ≤ c) (hχ : |χ| ≤ c ^ 2) (hτ : -1 / 2 ≤ τ) (hτ' : τ ≤ 3 / 2) (hg : 4 * c ≤ g) :
    (∑' k : ℕ, Fq χ c (pm τ g (k + 1))).re ≤ 6 := by
  have hc0 : 0 < c := by linarith
  have hg1 : 1 ≤ g := by linarith
  have hcont : Continuous (lineF χ c g) := Cvs.Prolate.Mellin.FrozenRootLogIntegral.continuous_lineF hc0 hχ hg
  have hI := Cvs.Prolate.Mellin.FrozenRootLogIntegral.integrable_lineF hc0 hχ hg
  have hc16 := c_sq_div_le hc0 hg
  set e : ℕ → ℝ := fun k => τ + 2 * ((k + 1 : ℕ) : ℝ) with hed
  have he : ∀ k, e k + 2 = e (k + 1) := fun k => by simp only [hed]; push_cast; ring
  set T : ℕ → ℂ := fun k => Fq χ c (pm τ g (k + 1)) with hTd
  set r : ℕ → ℂ := fun k => T k - (1 / 2) * ∫ u in e k..e k + 2, lineF χ c g u with hrd
  set Kr : ℝ := 66 * c ^ 2 * (3 * π / 8 / g ^ 2) with hKr
  -- partial sums
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, r k
      = ∑ k ∈ Finset.range N, T k - (1 / 2) * ∫ u in e 0..e N, lineF χ c g u := by
    intro N
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := lineF χ c g)
      (a := e) (n := N) (fun k _ => hcont.intervalIntegrable _ _)
    simp only [hrd, Finset.sum_sub_distrib, ← Finset.mul_sum, he, hsum]
  have hrb : ∀ N : ℕ, ‖∑ k ∈ Finset.range N, r k‖ ≤ Kr := by
    intro N
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ k ∈ Finset.range N, ‖r k‖ ≤ 66 * c ^ 2 * (1 / ‖pm τ g (k + 1)‖ ^ 3) := fun k _ => by
      have := norm_trap_le hc hχ hτ hg k
      rw [mul_one_div]; exact this
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Cvs.Prolate.Mellin.FrozenRootResidual.sum_inv_norm_cube_le hτ hg1 N) (by positivity)
  -- limits
  have hS : HasSum T (∑' k, T k) := ((summable_Fq hc0 hχ hτ hg).of_norm).hasSum
  have hlimT := hS.tendsto_sum_nat
  have heN : Tendsto e atTop atTop := by
    simp only [hed]
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    refine tendsto_atTop_add_const_left _ τ ?_
    refine (h.atTop_add tendsto_const_nhds (C := 2)).congr fun k => ?_
    push_cast; ring
  have hlimI := intervalIntegral_tendsto_integral_Ioi (e 0) hI.integrableOn heN
  have hlimR : Tendsto (fun N => ∑ k ∈ Finset.range N, r k) atTop
      (𝓝 ((∑' k, T k) - (1 / 2) * ∫ u in Ioi (e 0), lineF χ c g u)) := by
    simp only [hpart]
    exact hlimT.sub (hlimI.const_mul _)
  have hD : ‖(∑' k, T k) - (1 / 2) * ∫ u in Ioi (e 0), lineF χ c g u‖ ≤ Kr :=
    le_of_tendsto' hlimR.norm hrb
  -- the half-line integral
  have he0 : e 0 = τ + 2 := by simp only [hed]; push_cast; ring
  have hx0 : (0 : ℝ) ≤ e 0 := by rw [he0]; linarith
  have hJ := intervalIntegral.integral_Ioi_sub_Ioi hI.integrableOn hx0
  have hre0 := Cvs.Prolate.Mellin.FrozenRootLogIntegral.re_integral_Ioi_lineF hc0 hχ hg
  have hseg : ‖∫ u in (0 : ℝ)..e 0, lineF χ c g u‖ ≤ 6 * c ^ 2 / g ^ 2 * (e 0) := by
    have hb : ∀ u ∈ Ι (0 : ℝ) (e 0), ‖lineF χ c g u‖ ≤ 6 * c ^ 2 / g ^ 2 := fun u _ => by
      refine (Cvs.Prolate.Mellin.FrozenRootLogIntegral.norm_lineF_le hc0 hχ hg u).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (by nlinarith) (by nlinarith [sq_nonneg u])
    have := norm_integral_le_of_norm_le_const hb
    rwa [sub_zero, abs_of_nonneg hx0] at this
  have hreJ : |(∫ u in Ioi (e 0), lineF χ c g u).re| ≤ 6 * c ^ 2 / g ^ 2 * (e 0) := by
    have : ∫ u in Ioi (e 0), lineF χ c g u = (∫ u in Ioi (0 : ℝ), lineF χ c g u)
        - ∫ u in (0 : ℝ)..e 0, lineF χ c g u := by rw [← hJ]; ring
    rw [this, Complex.sub_re, hre0, zero_sub, abs_neg]
    exact (Complex.abs_re_le_norm _).trans hseg
  -- assemble
  have hsplit : (∑' k, T k).re = ((∑' k, T k) - (1 / 2) * ∫ u in Ioi (e 0), lineF χ c g u).re
      + (1 / 2) * (∫ u in Ioi (e 0), lineF χ c g u).re := by
    simp only [Complex.sub_re, Complex.mul_re]; norm_num
  have h1 := (Complex.re_le_norm _).trans hD
  have h2 : (1 / 2) * (∫ u in Ioi (e 0), lineF χ c g u).re ≤ (1 / 2) * (6 * c ^ 2 / g ^ 2 * (e 0)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hreJ) (by norm_num)
  have hKr : Kr ≤ 99 * π / 64 := by
    rw [hKr, show 66 * c ^ 2 * (3 * π / 8 / g ^ 2) = 99 * π / 4 * (c ^ 2 / g ^ 2) by ring]
    have := Real.pi_pos
    nlinarith
  have h3 : 6 * c ^ 2 / g ^ 2 * (e 0) ≤ 6 / 16 * (7 / 2) := by
    rw [he0, show 6 * c ^ 2 / g ^ 2 = 6 * (c ^ 2 / g ^ 2) by ring]
    have : 0 ≤ c ^ 2 / g ^ 2 := by positivity
    nlinarith
  have hpi := Real.pi_lt_d2
  show (∑' k, T k).re ≤ 6
  rw [hsplit]
  nlinarith

end product

/-- **The unit-circle Mellin law for a prolate solution**: `|pM(p)| ≤ 4e⁶|H(1)|` at `p = τ − ig`,
`τ ∈ [−1/2, 3/2]`, `g ≥ 4c`, `c ≥ 10`, `|χ| ≤ c²`. -/
theorem norm_mul_circM_le {H : ℂ → ℂ} (hH : Differentiable ℂ H) {χ c : ℝ} (hc : 10 ≤ c) (hχ : |χ| ≤ c ^ 2)
    (hode : ∀ z, (1 - z ^ 2) * deriv (deriv H) z - 2 * z * deriv H z + ((χ : ℂ) - (c : ℂ) ^ 2 * z ^ 2) * H z = 0)
    {τ g : ℝ} (hτ : -1 / 2 ≤ τ) (hτ' : τ ≤ 3 / 2) (hg : 4 * c ≤ g) :
    ‖pm τ g 0 * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H (pm τ g 0)‖ ≤ 4 * Real.exp 6 * ‖H 1‖ := by
  have hc0 : 0 < c := by linarith
  have hg0 : 0 < g := by linarith
  have hg1 : 1 ≤ g := by linarith
  set σk : ℕ → ℂ := fun k => sig χ c ((pm τ g k ^ 2)⁻¹) with hσd
  have hσ0 : ∀ k, σk k ≠ 0 := fun k h => by
    have := (Cvs.Prolate.Mellin.FrozenRootResidual.norm_sig_bounds hc0 hχ (hg.trans (norm_pm_ge τ g k))).1
    simp only [hσd] at h; rw [h, norm_zero] at this; linarith
  set Q : ℕ → ℂ := fun m => ∏ k ∈ Finset.range m, σk (k + 1) with hQd
  set R : ℕ → ℂ := fun m => pm τ g m * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H (pm τ g m) with hRd
  set U : ℕ → ℂ := fun m => R m * Q m with hUd
  set A : ℕ → ℂ := fun n => if n = 0 then 1 else aR χ (pm τ g n) / σk n with hAd
  set B : ℕ → ℂ := fun n => if n = 0 then 0 else bR c (pm τ g n) / (σk n * σk (n + 1)) with hBd
  -- the normalised recurrence
  have hrec : ∀ m, U m = A (m + 1) * U (m + 1) + B (m + 1) * U (m + 2) := by
    intro m
    have h := rec_lattice hH hode (τ := τ) hg0 m
    have h1 := hσ0 (m + 1)
    have h2 := hσ0 (m + 2)
    simp only [hUd, hAd, hBd, hRd, hQd, Nat.succ_ne_zero, if_false, Finset.prod_range_succ]
    rw [h]
    field_simp
  -- the limit
  set S := ∑' k : ℕ, Fq χ c (pm τ g (k + 1)) with hSd
  have hR : Tendsto R atTop (𝓝 (H 1)) := by
    have := Cvs.Prolate.Mellin.UnitCircleMellinSolution.tendsto_mul_circM hH (p₀ := pm τ g 0) (by rw [im_pm]; linarith)
    refine this.congr fun m => ?_
    simp only [hRd]; rw [← pm_eq]
  have hQe : ∀ m, Q m = Complex.exp (∑ k ∈ Finset.range m, Fq χ c (pm τ g (k + 1))) := fun m => by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (Complex.exp_log (hσ0 (k + 1))).symm
  have hQ : Tendsto Q atTop (𝓝 (Complex.exp S)) := by
    have hs := ((summable_Fq hc0 hχ hτ hg).of_norm).hasSum.tendsto_sum_nat
    have := (Complex.continuous_exp.tendsto S).comp hs
    exact this.congr fun m => (hQe m).symm
  have hlim : Tendsto U atTop (𝓝 (H 1 * Complex.exp S)) := hR.mul hQ
  -- the contraction
  have hβ : ∀ m, ‖B m‖ ≤ 3 / 25 := by
    intro m
    rcases m with _ | n
    · simp [hBd]; norm_num
    · simp only [hBd, Nat.succ_ne_zero, if_false, hσd]
      have hre : 1 ≤ (pm τ g (n + 1)).re := by
        rw [re_pm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hb := (Cvs.Prolate.Mellin.FrozenRootResidual.coeff_bounds hc hχ hre (hg.trans (norm_pm_ge τ g (n + 1)))).2
      rwa [← pm_succ] at hb
  -- the residual sum
  set f : ℕ → ℝ := fun n => if n = 0 then 0 else 8 * c ^ 2 / ‖pm τ g n‖ ^ 3 with hfd
  have hεf : ∀ n, ‖A n + B n - 1‖ ≤ f n := by
    intro n
    rcases n with _ | n
    · simp [hAd, hBd, hfd]
    · simp only [hAd, hBd, hfd, Nat.succ_ne_zero, if_false, hσd]
      have hre : 1 ≤ (pm τ g (n + 1)).re := by
        rw [re_pm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hb := (Cvs.Prolate.Mellin.FrozenRootResidual.coeff_bounds hc hχ hre (hg.trans (norm_pm_ge τ g (n + 1)))).1
      rwa [← pm_succ] at hb
  have hc16 := c_sq_div_le hc0 hg
  have hfsum : ∀ N, ∑ n ∈ Finset.range N, f n ≤ 3 * π / 16 := by
    intro N
    have hf0 : ∀ n, 0 ≤ f n := fun n => by simp only [hfd]; split_ifs <;> positivity
    calc ∑ n ∈ Finset.range N, f n ≤ ∑ n ∈ Finset.range (N + 1), f n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ N)) fun n _ _ => hf0 n
      _ = ∑ m ∈ Finset.range N, 8 * c ^ 2 * (1 / ‖pm τ g (m + 1)‖ ^ 3) := by
          rw [Finset.sum_range_succ']
          simp only [hfd, Nat.succ_ne_zero, if_false, if_true, add_zero, mul_one_div]
      _ = 8 * c ^ 2 * ∑ m ∈ Finset.range N, 1 / ‖pm τ g (m + 1)‖ ^ 3 := by rw [Finset.mul_sum]
      _ ≤ 8 * c ^ 2 * (3 * π / 8 / g ^ 2) :=
          mul_le_mul_of_nonneg_left (Cvs.Prolate.Mellin.FrozenRootResidual.sum_inv_norm_cube_le hτ hg1 N) (by positivity)
      _ = 3 * π * (c ^ 2 / g ^ 2) := by ring
      _ ≤ 3 * π * (1 / 16) := mul_le_mul_of_nonneg_left hc16 (by positivity)
      _ = 3 * π / 16 := by ring
  have hε0 : ∀ n, 0 ≤ ‖A n + B n - 1‖ := fun n => norm_nonneg _
  have hsum : Summable fun n => ‖A n + B n - 1‖ :=
    summable_of_sum_range_le hε0 fun N => (Finset.sum_le_sum fun n _ => hεf n).trans (hfsum N)
  have hE : ∑' n, ‖A n + B n - 1‖ ≤ 3 * π / 16 :=
    Real.tsum_le_of_sum_range_le hε0 fun N => (Finset.sum_le_sum fun n _ => hεf n).trans (hfsum N)
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hEβ : 3 * π / 16 < 1 - 3 / 25 := by linarith
  have key := Cvs.Upstream.DiscreteGronwallRecurrence.norm_le_of_recurrence hrec hlim hβ (by norm_num) hsum hE hEβ
  -- the constants
  have hU0 : U 0 = pm τ g 0 * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H (pm τ g 0) := by simp [hUd, hRd, hQd]
  rw [hU0] at key
  have hV : ‖H 1 * Complex.exp S‖ ≤ ‖H 1‖ * Real.exp 6 := by
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (re_tsum_Fq_le hc hχ hτ hτ' hg)) (norm_nonneg _)
  have hden : 1 / 4 ≤ 1 - 3 * π / 16 / (1 - 3 / 25) := by
    rw [show (1 : ℝ) - 3 / 25 = 22 / 25 by norm_num]; linarith
  calc ‖pm τ g 0 * Cvs.Prolate.Mellin.UnitCircleMellinSolution.circM H (pm τ g 0)‖ ≤ ‖H 1 * Complex.exp S‖ / (1 - 3 * π / 16 / (1 - 3 / 25)) := key
    _ ≤ ‖H 1‖ * Real.exp 6 / (1 / 4) := div_le_div₀ (by positivity) hV (by norm_num) hden
    _ = 4 * Real.exp 6 * ‖H 1‖ := by ring

end Cvs.Prolate.Mellin.UnitCircleMellinEdgeBound

end
