import Mathlib
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Mellin.HigherAliasesSummed
import Cvs.Prolate.Mellin.RayTransformEdgeSum
import Cvs.Prolate.Mellin.RungProfileOutsideCircle
import Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ray transforms of the aliases above the first

If `Σ_m |F_m(e^{−is})| ≤ Ωe^{κs}`, then `Σ_m |T_{F_m}(w)| ≤ Ω/(Im w − κ)`. With Cvs.Prolate.Mellin.HigherAliasesSummed and Cvs.Prolate.Mellin.RungProfileOutsideCircle at `ζ = e^{−is}`
(`|Im ζ| ≤ s`) this bounds the alias terms `m ≥ 1` of a single rung profile by `Ω_k/(g − c)`.
-/

noncomputable section

open Real Set MeasureTheory Filter Complex Topology
open Cvs.Prolate.Mellin.RayTransformEdgeSum (rayT)
open Cvs.Prolate.EntireRungProlateEquation (Hk)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev IsLevelIdx)

namespace Cvs.Prolate.Mellin.HigherAliasRayTransforms
open Cvs.ZeroCounting

/-- `‖T_F(w)‖ ≤ ∫_0^∞ ‖F(e^{−is})‖e^{−s Im w}`. -/
theorem norm_rayT_le_integral (F : ℂ → ℂ) (w : ℂ) :
    ‖rayT F w‖ ≤ ∫ s in Ioi (0 : ℝ), ‖F (Complex.exp (-(s * I)))‖ * Real.exp (-(w.im * s)) := by
  unfold rayT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact setIntegral_congr_fun measurableSet_Ioi fun s _ => Cvs.Prolate.Mellin.RayTransformEdgeSum.norm_integrand F w s

theorem integrableOn_norm {F : ℂ → ℂ} (hF : Continuous F) {w : ℂ} (hw : 0 < w.im) :
    IntegrableOn (fun s : ℝ => ‖F (Complex.exp (-(s * I)))‖ * Real.exp (-(w.im * s))) (Ioi 0) := by
  have := (Cvs.Prolate.Mellin.RayTransformEdgeSum.integrableOn_integrand hF hw).norm
  exact IntegrableOn.congr_fun this (fun s _ => Cvs.Prolate.Mellin.RayTransformEdgeSum.norm_integrand F w s) measurableSet_Ioi

/-- **Summed ray transforms** from an exponential bound on the circle. -/
theorem sum_norm_rayT_le {F : ℕ → ℂ → ℂ} (hF : ∀ m, Continuous (F m)) {w : ℂ} {κ Ω : ℝ} (hw : 0 < w.im)
    (hκ : κ < w.im) (N : ℕ)
    (hb : ∀ s : ℝ, 0 < s → ∑ m ∈ Finset.range N, ‖F m (Complex.exp (-(s * I)))‖ ≤ Ω * Real.exp (κ * s)) :
    ∑ m ∈ Finset.range N, ‖rayT (F m) w‖ ≤ Ω / (w.im - κ) := by
  have hi : ∀ m ∈ Finset.range N, Integrable (fun s : ℝ => ‖F m (Complex.exp (-(s * I)))‖
      * Real.exp (-(w.im * s))) (volume.restrict (Ioi 0)) := fun m _ => integrableOn_norm (hF m) hw
  have hdom : IntegrableOn (fun s : ℝ => Ω * Real.exp ((κ - w.im) * s)) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 (sub_pos.2 hκ)).const_mul Ω
    exact IntegrableOn.congr_fun this (fun s _ => by ring_nf) measurableSet_Ioi
  calc ∑ m ∈ Finset.range N, ‖rayT (F m) w‖
      ≤ ∑ m ∈ Finset.range N, ∫ s in Ioi (0 : ℝ), ‖F m (Complex.exp (-(s * I)))‖ * Real.exp (-(w.im * s)) :=
        Finset.sum_le_sum fun m _ => norm_rayT_le_integral (F m) w
    _ = ∫ s in Ioi (0 : ℝ), ∑ m ∈ Finset.range N, ‖F m (Complex.exp (-(s * I)))‖ * Real.exp (-(w.im * s)) :=
        (integral_finsetSum _ hi).symm
    _ ≤ ∫ s in Ioi (0 : ℝ), Ω * Real.exp ((κ - w.im) * s) := by
        refine setIntegral_mono_on (integrable_finsetSum _ hi) hdom measurableSet_Ioi fun s hs => ?_
        rw [← Finset.sum_mul]
        calc (∑ m ∈ Finset.range N, ‖F m (Complex.exp (-(s * I)))‖) * Real.exp (-(w.im * s))
            ≤ Ω * Real.exp (κ * s) * Real.exp (-(w.im * s)) := by gcongr; exact hb s hs
          _ = Ω * Real.exp ((κ - w.im) * s) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ = Ω / (w.im - κ) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
        simp only [mul_zero, Real.exp_zero]
        rw [show w.im - κ = -(κ - w.im) by ring, div_neg]
        field_simp

/-- On the unit circle `|Im e^{−is}| ≤ s` for `s ≥ 0`. -/
theorem abs_im_circle_le {s : ℝ} (hs : 0 ≤ s) : |(Complex.exp (-(s * I))).im| ≤ s := by
  rw [show -((s : ℂ) * I) = ((-s : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_im]
  have := Real.abs_sin_le_abs (x := -s)
  rwa [abs_neg, abs_of_nonneg hs] at this

theorem norm_circle (s : ℝ) : ‖Complex.exp (-(s * I))‖ = 1 := by
  rw [show -((s : ℂ) * I) = ((-s : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `e^{2πixn} = 1`. -/
theorem exp_two_pi_nat (x n : ℕ) : Complex.exp (I * ((2 * π * x) * n : ℝ)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨(x * n : ℕ), by push_cast; ring⟩

/-- The alias constant `Ω = 2Pe^{−c}/(1 − e^{−c}) + 6P′y₀/c + (2P/c) log(1/y₀)`. -/
def omega (c P P' y₀ : ℝ) : ℝ :=
  2 * P * Real.exp (-c) / (1 - Real.exp (-c)) + 6 * P' * y₀ / c + 2 * P / c * Real.log (1 / y₀)

theorem omega_nonneg {c P P' y₀ : ℝ} (hc : 0 < c) (hP : 0 ≤ P) (hP' : 0 ≤ P') (hy₀ : 0 < y₀) (hy₁ : y₀ ≤ 1) :
    0 ≤ omega c P P' y₀ := by
  unfold omega
  have h1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h2 : 0 ≤ Real.log (1 / y₀) := Real.log_nonneg (by rw [le_div_iff₀ hy₀]; linarith)
  have : 0 < 1 - Real.exp (-c) := by linarith
  positivity

/-- The `m`-th alias above the first of `H_k` at scale `c = 2πx`. -/
def tailF (x k m : ℕ) (ζ : ℂ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, Hk (2 * π * x) k (t * ζ) * Complex.cos (((2 * π * x) * (m + 2) : ℝ) * t)

theorem continuous_tailF {x k : ℕ} (h : ∃ χ, IsLevelIdx (2 * π * x) k χ) (m : ℕ) : Continuous (tailF x k m) := by
  unfold tailF
  have hH := (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h).continuous
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  fun_prop

/-- **The aliases above the first of one rung profile**: for `g > c = 2πx` and `y₀ ∈ (0, 1]`,
`Σ_{m < N} |T_{W_{m+2}}(σ + ig)| ≤ Ω_k/(g − c)`. -/
theorem sum_norm_rayT_tail_le {x k : ℕ} (hc : 0 < 2 * π * x) (h : ∃ χ, IsLevelIdx (2 * π * x) k χ)
    (hχ : lev (2 * π * x) k < (2 * π * x) ^ 2) (hχ' : |lev (2 * π * x) k| ≤ (2 * π * x) ^ 2)
    (hμ : muR (2 * π * x) k ≠ 0) {w : ℂ} (hw : 2 * π * x < w.im) {y₀ : ℝ} (hy₀ : 0 < y₀) (hy₁ : y₀ ≤ 1) (N : ℕ) :
    ∑ m ∈ Finset.range N, ‖rayT (tailF x k m) w‖
      ≤ omega (2 * π * x) (√(|rung (2 * π * x) k 1| * (Real.exp 1 * (Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk (2 * π * x) k
          + |rung (2 * π * x) k 1|))))
        (√((2 * π * x) ^ 2 * |rung (2 * π * x) k 1| * (Real.exp 1 * ((2 * π * x) * Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk (2 * π * x) k
          + (2 * π * x) ^ 2 * |rung (2 * π * x) k 1|)))) y₀ / (w.im - 2 * π * x) := by
  set c := 2 * π * (x : ℝ) with hcd
  set P := √(|rung c k 1| * (Real.exp 1 * (Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk c k + |rung c k 1|)))
  set P' := √(c ^ 2 * |rung c k 1| * (Real.exp 1 * (c * Cvs.Prolate.Mellin.RungProfileOutsideCircle.Mk c k + c ^ 2 * |rung c k 1|)))
  have hw0 : 0 < w.im := hc.trans hw
  have hO := omega_nonneg hc (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hy₀ hy₁ (P := P) (P' := P')
  refine sum_norm_rayT_le (fun m => continuous_tailF h m) hw0 hw N fun s hs => ?_
  have hζ := norm_circle s
  have hsum := Cvs.Prolate.Mellin.HigherAliasesSummed.sum_norm_alias_le (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk h) (Cvs.Prolate.Mellin.TrapezoidErrorAliasSeries.Hk_neg c k)
    (fun v hv => Cvs.Prolate.Mellin.RungProfileOutsideCircle.norm_Hk_outside hc.le h hχ hμ hv)
    (fun v hv => Cvs.Prolate.Mellin.RungProfileOutsideCircle.norm_deriv_Hk_outside hc h hχ hχ' hμ hv) hc (fun n => exp_two_pi_nat x n)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hζ hy₀ hy₁ N
  have hle : Real.exp (c * |(Complex.exp (-(s * I))).im|) ≤ Real.exp (c * s) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (abs_im_circle_le hs.le) hc.le)
  calc ∑ m ∈ Finset.range N, ‖tailF x k m (Complex.exp (-(s * I)))‖
      ≤ Real.exp (c * |(Complex.exp (-(s * I))).im|) * omega c P P' y₀ := by
        unfold tailF omega; exact hsum
    _ ≤ Real.exp (c * s) * omega c P P' y₀ := by gcongr
    _ = omega c P P' y₀ * Real.exp (c * s) := by ring

end Cvs.Prolate.Mellin.HigherAliasRayTransforms

end
