import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Digamma.WeierstrassGammaSeq

/-
Toward Hadamard: the Weierstrass elementary factor of genus 1.

`Cvs.Zeta.Bridge` reduces LAYER2 to a single hypothesis, `GuinandWeilOddGramPSD`
— the Guinand–Weil identity compressed to the Galerkin band.  That is the
explicit formula, and pinned Mathlib cannot express its proof: it has
`riemannZeta`, the functional equation (`riemannZeta_one_sub`), `ZetaZeros`
(zeros closed, discrete, finite in compacts), and the Dirichlet series
`−ζ'/ζ(s) = Σ Λ(n)n^{−s}` for `Re s > 1`
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`), but **no Hadamard/Weierstrass
factorization, no order theory for entire functions, and no residue theorem**.

The ladder to the explicit formula is therefore:

1. **Weierstrass elementary factors and product convergence**  ← this file
2. Order-1 growth bound for `ξ`
3. Hadamard factorization
4. Zero counting `N(T)` and `Σ_ρ |ρ|^{−2} < ∞`
5. Contour shift / argument principle
6. Guinand–Weil

This file is rung 1.  The genus-1 factor is

    `E₁(z) = (1 − z)·e^z`,

chosen so that `E₁(z) − 1` vanishes to second order at the origin — which is
what makes `Π E₁(z/ρ)` converge when `Σ|ρ|^{−2} < ∞`, the exact convergence `ξ`
has.  The classical estimate is `|E₁(z) − 1| ≤ |z|²` for `|z| ≤ 1`; proved here
in the slightly weaker but fully sufficient form

    `‖E₁(z) − 1‖ ≤ ‖z‖²·e^{‖z‖}`,

obtained from `E₁'(w) = −w e^w` by the mean value inequality along `[0,z]`,
with no series manipulation.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex

/-- The Weierstrass elementary factor of genus 1, `E₁(z) = (1 − z)e^z`. -/
noncomputable def weierstrassE1 (z : ℂ) : ℂ := (1 - z) * Complex.exp z

@[simp] theorem weierstrassE1_zero : weierstrassE1 0 = 1 := by
  simp [weierstrassE1]

/-- `E₁` vanishes exactly at `z = 1` — a simple zero, which is why
`E₁(z/ρ)` contributes exactly the zero `ρ`. -/
theorem weierstrassE1_eq_zero_iff {z : ℂ} : weierstrassE1 z = 0 ↔ z = 1 := by
  rw [weierstrassE1, mul_eq_zero]
  constructor
  · rintro (h | h)
    · linear_combination -h
    · exact absurd h (Complex.exp_ne_zero z)
  · rintro rfl; simp

/-- **The defining property**: `E₁' (w) = −w e^w`, vanishing to first order at
the origin.  This is why `E₁(z) − 1` vanishes to *second* order. -/
theorem hasDerivAt_weierstrassE1 (w : ℂ) :
    HasDerivAt weierstrassE1 (-(w * Complex.exp w)) w := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h2 : HasDerivAt Complex.exp (Complex.exp w) w := Complex.hasDerivAt_exp w
  have h := h1.mul h2
  refine h.congr_deriv ?_
  ring

/-- **The genus-1 estimate.** `‖E₁(z) − 1‖ ≤ ‖z‖²·e^{‖z‖}`. -/
theorem norm_weierstrassE1_sub_one_le (z : ℂ) :
    ‖weierstrassE1 z - 1‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  -- parametrise the segment `t ↦ E₁(t·z)` for `t ∈ [0,1]`
  set g : ℝ → ℂ := fun t => weierstrassE1 ((t : ℂ) * z) with hg
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g (-((t : ℂ) * z * Complex.exp ((t : ℂ) * z)) * z)
        (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z)
    exact ((hasDerivAt_weierstrassE1 ((t : ℂ) * z)).comp t hlin).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖-((t : ℂ) * z * Complex.exp ((t : ℂ) * z)) * z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hnt : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hz : ‖(t : ℂ) * z‖ ≤ ‖z‖ := by
      rw [norm_mul, hnt]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := by
            exact mul_le_mul_of_nonneg_right ht1 (norm_nonneg z)
        _ = ‖z‖ := one_mul _
    have hexp : ‖Complex.exp ((t : ℂ) * z)‖ ≤ Real.exp ‖z‖ := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) hz)
    rw [norm_mul, norm_neg, norm_mul]
    calc ‖(t : ℂ) * z‖ * ‖Complex.exp ((t : ℂ) * z)‖ * ‖z‖
        ≤ ‖z‖ * Real.exp ‖z‖ * ‖z‖ := by gcongr
      _ = ‖z‖ ^ 2 * Real.exp ‖z‖ := by ring
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.mpr zero_le_one)
    (Set.right_mem_Icc.mpr zero_le_one)
  simpa [hg, weierstrassE1_zero] using hmvt

/-- On the unit disc the bound is `e‖z‖²` — second order, uniformly. -/
theorem norm_weierstrassE1_sub_one_le_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖weierstrassE1 z - 1‖ ≤ Real.exp 1 * ‖z‖ ^ 2 := by
  refine le_trans (norm_weierstrassE1_sub_one_le z) ?_
  have h : Real.exp ‖z‖ ≤ Real.exp 1 := Real.exp_le_exp.mpr hz
  calc ‖z‖ ^ 2 * Real.exp ‖z‖ ≤ ‖z‖ ^ 2 * Real.exp 1 := by gcongr
    _ = Real.exp 1 * ‖z‖ ^ 2 := by ring

/-!
### The genus-1 canonical product

The point of the second-order estimate: when `Σ ‖aₙ‖⁻²` converges, the product `Π E₁(z/aₙ)`
converges for every `z`, and vanishes exactly at the `aₙ`.
-/

variable {ι : Type*} {a : ι → ℂ}

/-- Summability of `‖aₙ‖⁻²` forces `‖z/aₙ‖ ≤ 1` off a finite set. -/
theorem eventually_norm_div_le_one (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (z : ℂ) :
    ∀ᶠ n in Filter.cofinite, ‖z / a n‖ ≤ 1 := by
  have hz0 : Filter.Tendsto (fun n => ‖a n‖⁻¹ ^ 2) Filter.cofinite (nhds 0) :=
    ha.tendsto_cofinite_zero
  have ht : (0 : ℝ) < ((‖z‖ + 1)⁻¹) ^ 2 := by positivity
  filter_upwards [hz0.eventually (gt_mem_nhds ht)] with n hn
  have h0 : (0 : ℝ) ≤ ‖a n‖⁻¹ := by positivity
  have hp : (0 : ℝ) < (‖z‖ + 1)⁻¹ := by positivity
  have h1 : ‖a n‖⁻¹ < (‖z‖ + 1)⁻¹ := by nlinarith
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have h2 : ‖z‖ * ‖a n‖⁻¹ ≤ ‖z‖ * (‖z‖ + 1)⁻¹ :=
    mul_le_mul_of_nonneg_left h1.le hzn
  have h3 : ‖z‖ * (‖z‖ + 1)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    linarith
  rw [norm_div, div_eq_mul_inv]
  linarith

/-- The genus-1 factors differ from `1` by a summable amount. -/
theorem summable_norm_weierstrassE1_div_sub_one
    (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (z : ℂ) :
    Summable fun n => ‖weierstrassE1 (z / a n) - 1‖ := by
  refine Summable.of_norm_bounded_eventually
    (g := fun n => Real.exp 1 * ‖z‖ ^ 2 * ‖a n‖⁻¹ ^ 2) (ha.mul_left _) ?_
  filter_upwards [eventually_norm_div_le_one ha z] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc ‖weierstrassE1 (z / a n) - 1‖
      ≤ Real.exp 1 * ‖z / a n‖ ^ 2 := norm_weierstrassE1_sub_one_le_of_norm_le_one hn
    _ = Real.exp 1 * ‖z‖ ^ 2 * ‖a n‖⁻¹ ^ 2 := by
        rw [norm_div, div_pow, inv_pow, div_eq_mul_inv]; ring

/-- **Convergence of the genus-1 canonical product.**  If `Σ ‖aₙ‖⁻²` converges
then `Π E₁(z/aₙ)` converges for every `z`. -/
theorem multipliable_weierstrassE1_div
    (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (z : ℂ) :
    Multipliable fun n => weierstrassE1 (z / a n) :=
  (multipliable_one_add_of_summable
    (f := fun n => weierstrassE1 (z / a n) - 1)
    (summable_norm_weierstrassE1_div_sub_one ha z)).congr fun n => by ring

/-- **The canonical product vanishes only at the `aₙ`.** Together with
`multipliable_weierstrassE1_div` this says `Π E₁(z/aₙ)` is an entire function whose zero set
is exactly `{aₙ}` — the half of Hadamard that does not need a growth bound. -/
theorem tprod_weierstrassE1_div_ne_zero
    (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) {z : ℂ} (hz : ∀ n, z ≠ a n) :
    ∏' n, weierstrassE1 (z / a n) ≠ 0 := by
  have hne : ∀ n, (1 : ℂ) + (weierstrassE1 (z / a n) - 1) ≠ 0 := by
    intro n
    have hrw : (1 : ℂ) + (weierstrassE1 (z / a n) - 1) = weierstrassE1 (z / a n) := by ring
    rw [hrw, Ne, weierstrassE1_eq_zero_iff]
    rcases eq_or_ne (a n) 0 with h0 | h0
    · rw [h0, div_zero]
      exact zero_ne_one
    · rw [div_eq_one_iff_eq h0]
      exact hz n
  have heq : ∏' n, weierstrassE1 (z / a n)
      = ∏' n, ((1 : ℂ) + (weierstrassE1 (z / a n) - 1)) :=
    tprod_congr fun n => by ring
  rw [heq]
  exact tprod_one_add_ne_zero_of_summable hne
    (summable_norm_weierstrassE1_div_sub_one ha z)

/-!
### Local uniform convergence, and entirety

`multipliable_weierstrassE1_div` gives convergence pointwise.
-/

theorem continuous_weierstrassE1 : Continuous weierstrassE1 :=
  (continuous_const.sub continuous_id).mul Complex.continuous_exp

/-- On a ball of radius `R`, `‖z/aₙ‖ ≤ 1` for all but finitely many `n`,
*uniformly in `z`*. -/
theorem eventually_forall_ball_norm_div_le_one
    (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (R : ℝ) :
    ∀ᶠ n in Filter.cofinite, ∀ z ∈ Metric.ball (0 : ℂ) R, ‖z / a n‖ ≤ 1 := by
  have hz0 : Filter.Tendsto (fun n => ‖a n‖⁻¹ ^ 2) Filter.cofinite (nhds 0) :=
    ha.tendsto_cofinite_zero
  have ht : (0 : ℝ) < ((|R| + 1)⁻¹) ^ 2 := by positivity
  filter_upwards [hz0.eventually (gt_mem_nhds ht)] with n hn z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have h0 : (0 : ℝ) ≤ ‖a n‖⁻¹ := by positivity
  have hp : (0 : ℝ) < (|R| + 1)⁻¹ := by positivity
  have h1 : ‖a n‖⁻¹ < (|R| + 1)⁻¹ := by nlinarith
  have hzR : ‖z‖ ≤ |R| := le_trans hz.le (le_abs_self R)
  have h3 : |R| * (|R| + 1)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    linarith [abs_nonneg R]
  have h4 : ‖z‖ * ‖a n‖⁻¹ ≤ |R| * (|R| + 1)⁻¹ :=
    mul_le_mul hzR h1.le h0 (abs_nonneg R)
  rw [norm_div, div_eq_mul_inv]
  linarith

/-- **Local uniform convergence of the genus-1 canonical product.** With
`multipliable_weierstrassE1_div` and `tprod_weierstrassE1_div_ne_zero` this completes rung 1:
`Π E₁(z/aₙ)` is a locally uniform limit of polynomials-times- exponentials, hence entire, with … -/
theorem hasProdLocallyUniformlyOn_weierstrassE1_div
    (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (R : ℝ) :
    HasProdLocallyUniformlyOn (fun n (z : ℂ) => weierstrassE1 (z / a n))
      (fun z => ∏' n, weierstrassE1 (z / a n)) (Metric.ball (0 : ℂ) R) := by
  have hcts : ∀ n, ContinuousOn (fun z : ℂ => weierstrassE1 (z / a n) - 1)
      (Metric.ball (0 : ℂ) R) := fun n =>
    ((continuous_weierstrassE1.comp (continuous_id.div_const (a n))).sub
      continuous_const).continuousOn
  have hbd : ∀ᶠ n in Filter.cofinite, ∀ z ∈ Metric.ball (0 : ℂ) R,
      ‖weierstrassE1 (z / a n) - 1‖ ≤ Real.exp 1 * R ^ 2 * ‖a n‖⁻¹ ^ 2 := by
    filter_upwards [eventually_forall_ball_norm_div_le_one ha R] with n hn z hz
    have h1 := norm_weierstrassE1_sub_one_le_of_norm_le_one (hn z hz)
    rw [Metric.mem_ball, dist_zero_right] at hz
    have h0 : (0 : ℝ) ≤ ‖a n‖⁻¹ := by positivity
    have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have heq : ‖z / a n‖ ^ 2 = ‖z‖ ^ 2 * ‖a n‖⁻¹ ^ 2 := by
      rw [norm_div, div_pow, inv_pow, div_eq_mul_inv]
    have hle : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith
    calc ‖weierstrassE1 (z / a n) - 1‖
        ≤ Real.exp 1 * ‖z / a n‖ ^ 2 := h1
      _ = Real.exp 1 * (‖z‖ ^ 2 * ‖a n‖⁻¹ ^ 2) := by rw [heq]
      _ ≤ Real.exp 1 * (R ^ 2 * ‖a n‖⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (Real.exp_pos 1).le
      _ = Real.exp 1 * R ^ 2 * ‖a n‖⁻¹ ^ 2 := by ring
  have key := Summable.hasProdLocallyUniformlyOn_one_add
    (f := fun n (z : ℂ) => weierstrassE1 (z / a n) - 1)
    (u := fun n => Real.exp 1 * R ^ 2 * ‖a n‖⁻¹ ^ 2)
    Metric.isOpen_ball (ha.mul_left _) hbd hcts
  have h1 : (fun n (z : ℂ) => (1 : ℂ) + (weierstrassE1 (z / a n) - 1))
      = fun n (z : ℂ) => weierstrassE1 (z / a n) := by funext n z; ring
  have h2 : (fun z : ℂ => ∏' n, ((1 : ℂ) + (weierstrassE1 (z / a n) - 1)))
      = fun z : ℂ => ∏' n, weierstrassE1 (z / a n) := by
    funext z; exact tprod_congr fun n => by ring
  rw [← h1, ← h2]
  exact key

/-!
### The Euler–Gauss sequence as a Weierstrass product

This is the payoff of the estimate above, and the route to LAYERS' Mathlib request #2.
-/

/-- **`GammaSeq` in Weierstrass form.** `1/GammaSeq(s,n) = s · e^{s(H_n − log n)} · Π_{j<n}
E₁(−s/(j+1))`. -/
theorem inv_GammaSeq_eq_weierstrass (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (Complex.GammaSeq s n)⁻¹
      = s * Complex.exp (s * ((∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1))
            - (Real.log n : ℂ)))
        * ∏ j ∈ Finset.range n, weierstrassE1 (-(s / ((j : ℂ) + 1))) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hjne : ∀ j : ℕ, ((j : ℂ) + 1) ≠ 0 := by
    intro j
    have h : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    exact_mod_cast ne_of_gt h
  have hcne : ((n : ℂ) ^ s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
  have hPne : (∏ j ∈ Finset.range n, ((j : ℂ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hjne j
  have hlog : ((Real.log (n : ℝ) : ℝ) : ℂ) = Complex.log ((n : ℕ) : ℂ) := by
    simp
  have hcpow : Complex.exp (-((Real.log n : ℂ) * s)) = ((n : ℂ) ^ s)⁻¹ := by
    rw [hlog, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_neg]
  have hE : ∀ j : ℕ, weierstrassE1 (-(s / ((j : ℂ) + 1)))
      = (1 + s / ((j : ℂ) + 1)) * Complex.exp (-(s / ((j : ℂ) + 1))) := by
    intro j; rw [weierstrassE1]; ring
  have hsum : ∑ j ∈ Finset.range n, -(s / ((j : ℂ) + 1))
      = -(s * ∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hprod : ∏ j ∈ Finset.range n, weierstrassE1 (-(s / ((j : ℂ) + 1)))
      = (∏ j ∈ Finset.range n, (1 + s / ((j : ℂ) + 1)))
        * Complex.exp (-(s * ∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1))) := by
    rw [Finset.prod_congr rfl (fun j _ => hE j), Finset.prod_mul_distrib,
      ← Complex.exp_sum, hsum]
  have hden : ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))
      = s * ∏ j ∈ Finset.range n, (s + ((j : ℂ) + 1)) := by
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_zero, add_zero]
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by push_cast; ring
  have hfac : ((Nat.factorial n : ℕ) : ℂ) = ∏ j ∈ Finset.range n, ((j : ℂ) + 1) := by
    rw [← Finset.prod_range_add_one_eq_factorial n, Nat.cast_prod]
    exact Finset.prod_congr rfl fun j _ => by push_cast; ring
  have hratio : (∏ j ∈ Finset.range n, (1 + s / ((j : ℂ) + 1)))
      = (∏ j ∈ Finset.range n, (s + ((j : ℂ) + 1)))
        / ∏ j ∈ Finset.range n, ((j : ℂ) + 1) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have h := hjne j
    field_simp
    ring
  -- name the pieces so the exponentials can be combined
  set H : ℂ := ∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1) with hH
  set P : ℂ := ∏ j ∈ Finset.range n, (s + ((j : ℂ) + 1)) with hP
  set Q : ℂ := ∏ j ∈ Finset.range n, ((j : ℂ) + 1) with hQ
  have hexp : Complex.exp (s * (H - (Real.log n : ℂ))) * Complex.exp (-(s * H))
      = ((n : ℂ) ^ s)⁻¹ := by
    rw [← Complex.exp_add,
      show s * (H - (Real.log n : ℂ)) + -(s * H) = -((Real.log n : ℂ) * s) by ring,
      hcpow]
  simp only [Complex.GammaSeq, hden, hfac]
  rw [inv_div, hprod, hratio]
  have hrearr : s * Complex.exp (s * (H - (Real.log n : ℂ)))
        * (P / Q * Complex.exp (-(s * H)))
      = s * (P / Q) * (Complex.exp (s * (H - (Real.log n : ℂ)))
        * Complex.exp (-(s * H))) := by ring
  rw [hrearr, hexp]
  field_simp

/-!
### Locally uniform convergence of the canonical product

The M-test.
-/

/-- The elementary factors are uniformly `O(1/n²)` on a ball. -/
theorem norm_weierstrassE1_shift_sub_one_le {R : ℝ} {s : ℂ}
    (hs : s ∈ Metric.ball (0 : ℂ) R) (n : ℕ) :
    ‖weierstrassE1 (-(s / ((n : ℂ) + 1))) - 1‖
      ≤ (R ^ 2 * Real.exp R) / ((n : ℝ) + 1) ^ 2 := by
  have hsR : ‖s‖ < R := by simpa using hs
  have hR : (0 : ℝ) < R := lt_of_le_of_lt (norm_nonneg s) hsR
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) by push_cast; ring,
      Complex.norm_natCast]
    push_cast; ring
  have hz : ‖-(s / ((n : ℂ) + 1))‖ = ‖s‖ / ((n : ℝ) + 1) := by
    rw [norm_neg, norm_div, hnorm]
  have hzR : ‖-(s / ((n : ℂ) + 1))‖ ≤ R / ((n : ℝ) + 1) := by
    rw [hz]; gcongr
  have hzle : ‖-(s / ((n : ℂ) + 1))‖ ≤ R := by
    refine le_trans hzR ?_
    rw [div_le_iff₀ hn1]
    nlinarith
  refine le_trans (norm_weierstrassE1_sub_one_le _) ?_
  have h1 : ‖-(s / ((n : ℂ) + 1))‖ ^ 2 ≤ (R / ((n : ℝ) + 1)) ^ 2 := by
    gcongr
  have h2 : Real.exp ‖-(s / ((n : ℂ) + 1))‖ ≤ Real.exp R := Real.exp_le_exp.mpr hzle
  calc ‖-(s / ((n : ℂ) + 1))‖ ^ 2 * Real.exp ‖-(s / ((n : ℂ) + 1))‖
      ≤ (R / ((n : ℝ) + 1)) ^ 2 * Real.exp R := by gcongr
    _ = (R ^ 2 * Real.exp R) / ((n : ℝ) + 1) ^ 2 := by
        rw [div_pow]; ring

theorem summable_weierstrass_bound (R : ℝ) :
    Summable (fun n : ℕ => (R ^ 2 * Real.exp R) / ((n : ℝ) + 1) ^ 2) := by
  have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hshift := (summable_nat_add_iff 1).mpr h2
  have h : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    refine hshift.congr fun n => ?_
    push_cast
    ring
  exact (h.mul_left (R ^ 2 * Real.exp R)).congr fun n => by ring

/-- **The canonical product converges locally uniformly.** -/
theorem hasProdLocallyUniformlyOn_weierstrass (R : ℝ) :
    HasProdLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ => weierstrassE1 (-(s / ((n : ℂ) + 1))))
      (fun s : ℂ => ∏' n : ℕ, weierstrassE1 (-(s / ((n : ℂ) + 1))))
      (Metric.ball (0 : ℂ) R) := by
  have hcts : ∀ n : ℕ, ContinuousOn
      (fun s : ℂ => weierstrassE1 (-(s / ((n : ℂ) + 1))) - 1) (Metric.ball (0 : ℂ) R) := by
    intro n
    have hne : ((n : ℂ) + 1) ≠ 0 := by
      have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact_mod_cast ne_of_gt h
    unfold weierstrassE1
    fun_prop (disch := assumption)
  have h := Summable.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun n : ℕ => fun s : ℂ => weierstrassE1 (-(s / ((n : ℂ) + 1))) - 1)
    Metric.isOpen_ball (summable_weierstrass_bound R)
    (Filter.Eventually.of_forall fun n s hs =>
      norm_weierstrassE1_shift_sub_one_le hs n)
    hcts
  simpa using h

/-!
### The exponential factor

The other half of `inv_GammaSeq_eq_weierstrass`: `H_n − log n → γ`
(`Real.tendsto_harmonic_sub_log`), so the scalar factor `e^{s(H_n − log n)}` converges to
`e^{γs}`.
-/

theorem harmonic_cast_complex (n : ℕ) :
    (((harmonic n : ℚ) : ℝ) : ℂ) = ∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1) := by
  rw [harmonic]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [one_div]

/-- **The exponential factor converges**: `e^{s(H_n − log n)} → e^{γs}`. -/
theorem tendsto_weierstrass_exp_factor (s : ℂ) :
    Filter.Tendsto
      (fun n : ℕ => Complex.exp (s * ((∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1))
        - (Real.log n : ℂ))))
      Filter.atTop
      (nhds (Complex.exp (s * (Real.eulerMascheroniConstant : ℂ)))) := by
  have h1 : Filter.Tendsto
      (fun n : ℕ => (∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1)) - (Real.log n : ℂ))
      Filter.atTop (nhds ((Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
    refine h.congr fun n => ?_
    rw [Function.comp_apply, ← harmonic_cast_complex n]
    push_cast
    ring
  exact (h1.const_mul s).cexp

/-! ### The Weierstrass product for `1/Γ`

The three pieces combine.  `GammaSeq_tendsto_Gamma` is pointwise, which is all
that is needed here; the *locally uniform* statement above is what the digamma
step will use. -/

theorem multipliable_weierstrass (s : ℂ) :
    Multipliable (fun n : ℕ => weierstrassE1 (-(s / ((n : ℂ) + 1)))) := by
  set R : ℝ := ‖s‖ + 1 with hR
  have hmem : s ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right, hR]
    linarith
  have hsum : Summable (fun n : ℕ => ‖weierstrassE1 (-(s / ((n : ℂ) + 1))) - 1‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_weierstrassE1_shift_sub_one_le hmem n)
      (summable_weierstrass_bound R)
  have h := multipliable_one_add_of_summable hsum
  simpa using h

/-- **The Weierstrass product for `1/Γ`.** `1/Γ(s) = s·e^{γs}·Π_{n≥0} E₁(−s/(n+1))`. -/
theorem one_div_Gamma_eq_weierstrass_prod {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    (Complex.Gamma s)⁻¹
      = s * Complex.exp (s * (Real.eulerMascheroniConstant : ℂ))
        * ∏' n : ℕ, weierstrassE1 (-(s / ((n : ℂ) + 1))) := by
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have h1 : Filter.Tendsto (fun n : ℕ => (Complex.GammaSeq s n)⁻¹)
      Filter.atTop (nhds (Complex.Gamma s)⁻¹) :=
    (Complex.GammaSeq_tendsto_Gamma s).inv₀ hΓ
  have hprod : Filter.Tendsto
      (fun n : ℕ => ∏ j ∈ Finset.range n, weierstrassE1 (-(s / ((j : ℂ) + 1))))
      Filter.atTop (nhds (∏' n : ℕ, weierstrassE1 (-(s / ((n : ℂ) + 1))))) :=
    (multipliable_weierstrass s).hasProd.tendsto_prod_nat
  have h2 := ((tendsto_weierstrass_exp_factor s).const_mul s).mul hprod
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  exact (inv_GammaSeq_eq_weierstrass s hn).symm

/-!
### The Euler limit, locally uniformly

`Complex.logDeriv_tendsto` converts a *locally uniform* limit of nonvanishing holomorphic
functions into a limit of logarithmic derivatives.
-/

/-- The region carrying the locally uniform Euler limit. -/
noncomputable def gammaRegion (R : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) R ∩ {s : ℂ | 0 < s.re}

theorem isOpen_gammaRegion (R : ℝ) : IsOpen (gammaRegion R) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem gammaRegion_subset_ball (R : ℝ) : gammaRegion R ⊆ Metric.ball (0 : ℂ) R :=
  Set.inter_subset_left

/-- Points of `gammaRegion` are not poles of `Γ`. -/
theorem gammaRegion_ne_neg_nat {R : ℝ} {s : ℂ} (hs : s ∈ gammaRegion R) (m : ℕ) :
    s ≠ -m := by
  intro h
  have hre : 0 < s.re := hs.2
  rw [h] at hre
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- **The exponential factor converges uniformly on balls.**
`e^{s(H_n − log n)} → e^{γ s}`, uniformly for `‖s‖ < R`. -/
theorem tendstoUniformlyOn_weierstrass_exp {R : ℝ} (hR : 0 < R) :
    TendstoUniformlyOn
      (fun (n : ℕ) (s : ℂ) => Complex.exp (s * ((∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1))
        - (Real.log n : ℂ))))
      (fun s : ℂ => Complex.exp (s * (Real.eulerMascheroniConstant : ℂ)))
      Filter.atTop (Metric.ball (0 : ℂ) R) := by
  have hb : Filter.Tendsto
      (fun n : ℕ => (∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1)) - (Real.log n : ℂ))
      Filter.atTop (nhds ((Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
    refine h.congr fun n => ?_
    rw [Function.comp_apply, ← harmonic_cast_complex n]
    push_cast
    ring
  set g : ℂ := ((Real.eulerMascheroniConstant : ℝ) : ℂ) with hg
  set C : ℝ := Real.exp (R * ‖g‖) with hC
  have hCpos : 0 < C := Real.exp_pos _
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ‖((∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1))
        - (Real.log n : ℂ)) - g‖) Filter.atTop (nhds 0) := by
    have h0 : ‖g - g‖ = 0 := by simp
    rw [← h0]
    exact (hb.sub_const g).norm
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := min (1 / R) (ε / (4 * R * C)) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  filter_upwards [hnorm.eventually (eventually_lt_nhds hδpos)] with n hn x hx
  set d : ℂ := (∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1)) - (Real.log n : ℂ) with hd
  have hxR : ‖x‖ < R := by simpa [Complex.dist_eq] using hx
  have hsplit : Complex.exp (x * g) - Complex.exp (x * d)
      = -(Complex.exp (x * g) * (Complex.exp (x * (d - g)) - 1)) := by
    have hadd : x * g + x * (d - g) = x * d := by ring
    have hkey : Complex.exp (x * g) * (Complex.exp (x * (d - g)) - 1)
        = Complex.exp (x * d) - Complex.exp (x * g) := by
      rw [mul_sub, mul_one, ← Complex.exp_add, hadd]
    rw [hkey]
    ring
  have hprod : ‖x‖ * ‖d - g‖ ≤ R * δ :=
    mul_le_mul hxR.le hn.le (norm_nonneg _) (by positivity)
  have hsmall : ‖x * (d - g)‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖x‖ * ‖d - g‖ ≤ R * δ := hprod
      _ ≤ R * (1 / R) := by gcongr; exact min_le_left _ _
      _ = 1 := by field_simp
  have h1 : ‖Complex.exp (x * (d - g)) - 1‖ ≤ 2 * ‖x * (d - g)‖ :=
    Complex.norm_exp_sub_one_le hsmall
  have h2 : ‖Complex.exp (x * g)‖ ≤ C := by
    rw [Complex.norm_exp, hC]
    refine Real.exp_le_exp.mpr ?_
    calc (x * g).re ≤ ‖x * g‖ := Complex.re_le_norm _
      _ = ‖x‖ * ‖g‖ := norm_mul _ _
      _ ≤ R * ‖g‖ := by gcongr
  rw [Complex.dist_eq, hsplit, norm_neg, norm_mul]
  calc ‖Complex.exp (x * g)‖ * ‖Complex.exp (x * (d - g)) - 1‖
      ≤ C * (2 * (R * δ)) := by
        refine mul_le_mul h2 ?_ (norm_nonneg _) hCpos.le
        calc ‖Complex.exp (x * (d - g)) - 1‖ ≤ 2 * ‖x * (d - g)‖ := h1
          _ = 2 * (‖x‖ * ‖d - g‖) := by rw [norm_mul]
          _ ≤ 2 * (R * δ) := by gcongr
    _ ≤ C * (2 * (R * (ε / (4 * R * C)))) := by
        gcongr
        exact min_le_right _ _
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

/-- **The Euler limit `GammaSeq → Γ`, locally uniformly** (in inverted form). -/
theorem tendstoLocallyUniformlyOn_inv_GammaSeq {R : ℝ} (hR : 0 < R) :
    TendstoLocallyUniformlyOn (fun (n : ℕ) (s : ℂ) => (Complex.GammaSeq s n)⁻¹)
      (fun s : ℂ => (Complex.Gamma s)⁻¹) Filter.atTop (gammaRegion R) := by
  have h1 : TendstoLocallyUniformlyOn (fun (_ : ℕ) (s : ℂ) => s) (fun s : ℂ => s)
      Filter.atTop (gammaRegion R) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards with n x _
    simpa using hε
  have h2 : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (s : ℂ) => Complex.exp (s * ((∑ j ∈ Finset.range n, (1 : ℂ) / ((j : ℂ) + 1))
        - (Real.log n : ℂ))))
      (fun s : ℂ => Complex.exp (s * (Real.eulerMascheroniConstant : ℂ)))
      Filter.atTop (gammaRegion R) :=
    ((tendstoUniformlyOn_weierstrass_exp hR).tendstoLocallyUniformlyOn).mono
      (gammaRegion_subset_ball R)
  have h3 : TendstoLocallyUniformlyOn
      (fun (N : ℕ) (s : ℂ) => ∏ j ∈ Finset.range N, weierstrassE1 (-(s / ((j : ℂ) + 1))))
      (fun s : ℂ => ∏' n : ℕ, weierstrassE1 (-(s / ((n : ℂ) + 1))))
      Filter.atTop (gammaRegion R) :=
    ((hasProdLocallyUniformlyOn_weierstrass R).tendstoLocallyUniformlyOn_finsetRange).mono
      (gammaRegion_subset_ball R)
  -- continuity of the three limits
  have c1 : ContinuousOn (fun s : ℂ => s) (gammaRegion R) := continuousOn_id
  have c2 : ContinuousOn (fun s : ℂ => Complex.exp (s * (Real.eulerMascheroniConstant : ℂ)))
      (gammaRegion R) :=
    (Complex.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn
  have c3 : ContinuousOn (fun s : ℂ => ∏' n : ℕ, weierstrassE1 (-(s / ((n : ℂ) + 1))))
      (gammaRegion R) := by
    refine h3.continuousOn (.of_forall fun N => ?_)
    exact continuousOn_finsetProd _ fun j _ =>
      ((continuous_weierstrassE1.comp
        ((continuous_id.div_const ((j : ℂ) + 1)).neg))).continuousOn
  -- multiply
  have hall := (h1.mul₀ h2 c1 c2).mul₀ h3 (c1.mul c2) c3
  -- identify the sequence with `1/GammaSeq(·, n)`
  refine (hall.congr_inseparable ?_).congr_right ?_
  · filter_upwards [Filter.eventually_ne_atTop 0] with n hn x _
    exact Inseparable.of_eq (inv_GammaSeq_eq_weierstrass x hn).symm
  · intro x hx
    exact (one_div_Gamma_eq_weierstrass_prod (gammaRegion_ne_neg_nat hx)).symm

/-!
### From the Euler limit to the digamma series

`Complex.logDeriv_tendsto` now applies.
-/

/-- The logarithmic derivative of a reciprocal. -/
theorem logDeriv_inv_fun {f : ℂ → ℂ} {x : ℂ} (hf : f x ≠ 0)
    (hdf : DifferentiableAt ℂ f x) :
    logDeriv (fun s => (f s)⁻¹) x = -logDeriv f x := by
  have h : (fun s : ℂ => (f s)⁻¹) = fun s => (1 : ℂ) / f s := by
    funext s; rw [one_div]
  rw [h]
  refine (logDeriv_div (f := fun _ => (1 : ℂ)) (g := f) x one_ne_zero hf
    (differentiableAt_const 1) hdf).trans ?_
  simp

/-- **The logarithmic derivative of `1/GammaSeq(·, n)` is a finite Euler sum.** -/
theorem logDeriv_inv_GammaSeq {n : ℕ} (hn : n ≠ 0) {x : ℂ} (hx : 0 < x.re) :
    logDeriv (fun s : ℂ => (Complex.GammaSeq s n)⁻¹) x
      = (∑ j ∈ Finset.range (n + 1), (x + (j : ℂ))⁻¹) - (Real.log n : ℂ) := by
  have hnC : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpow : (n : ℂ) ^ x ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnC]; exact Complex.exp_ne_zero _
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hne : ∀ j ∈ Finset.range (n + 1), x + (j : ℂ) ≠ 0 := by
    intro j _ hj
    have hre : (x + (j : ℂ)).re = 0 := by rw [hj]; simp
    simp only [Complex.add_re, Complex.natCast_re] at hre
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hfun : (fun s : ℂ => (Complex.GammaSeq s n)⁻¹)
      = fun s : ℂ => (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ)))
          / ((n : ℂ) ^ s * ((Nat.factorial n : ℕ) : ℂ)) := by
    funext s; rw [Complex.GammaSeq, inv_div]
  have hprodne : (∏ j ∈ Finset.range (n + 1), (x + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hne
  have hdprod : DifferentiableAt ℂ
      (fun s : ℂ => ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) x :=
    DifferentiableAt.fun_finsetProd fun j _ => (differentiableAt_id.add_const _)
  have hdcpow : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ s) x :=
    (Complex.hasStrictDerivAt_const_cpow (Or.inl hnC)).hasDerivAt.differentiableAt
  have hdden : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ s * ((Nat.factorial n : ℕ) : ℂ)) x :=
    hdcpow.mul_const _
  rw [hfun]
  refine (logDeriv_div x hprodne (by exact mul_ne_zero hpow hfac) hdprod hdden).trans ?_
  congr 1
  · -- the product
    have hlin : ∀ j : ℕ, logDeriv (fun s : ℂ => s + (j : ℂ)) x = (x + (j : ℂ))⁻¹ := by
      intro j
      rw [logDeriv_apply, deriv_add_const]
      simp
    rw [logDeriv_fun_prod (f := fun (j : ℕ) (s : ℂ) => s + (j : ℂ)) hne
      fun j _ => differentiableAt_id.add_const _]
    exact Finset.sum_congr rfl fun j _ => hlin j
  · -- the denominator
    rw [logDeriv_mul_const x _ hfac, logDeriv_apply,
      (Complex.hasStrictDerivAt_const_cpow (Or.inl hnC)).hasDerivAt.deriv]
    have hdiv : (n : ℂ) ^ x * Complex.log (n : ℂ) / (n : ℂ) ^ x = Complex.log (n : ℂ) := by
      field_simp
    have hlogcast : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [hdiv, hlogcast]

/-- `1/GammaSeq(·, n)` is entire: the denominator `n^s · n!` never vanishes. -/
theorem differentiable_inv_GammaSeq {n : ℕ} (hn : n ≠ 0) :
    Differentiable ℂ (fun s : ℂ => (Complex.GammaSeq s n)⁻¹) := by
  have hnC : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfun : (fun s : ℂ => (Complex.GammaSeq s n)⁻¹)
      = fun s : ℂ => (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ)))
          / ((n : ℂ) ^ s * ((Nat.factorial n : ℕ) : ℂ)) := by
    funext s; rw [Complex.GammaSeq, inv_div]
  rw [hfun]
  intro s
  have hpow : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnC]; exact Complex.exp_ne_zero _
  have hdprod : DifferentiableAt ℂ
      (fun s : ℂ => ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) s :=
    DifferentiableAt.fun_finsetProd fun j _ => (differentiableAt_id.add_const _)
  have hdden : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ s * ((Nat.factorial n : ℕ) : ℂ)) s :=
    ((Complex.hasStrictDerivAt_const_cpow (Or.inl hnC)).hasDerivAt.differentiableAt).mul_const _
  exact hdprod.fun_div hdden (mul_ne_zero hpow hfac)

/-- **Euler's limit for the digamma function.** For `Re s > 0`, `log n − Σ_{j<n} 1/(s+j) → ψ(s)`.
 -/
theorem tendsto_euler_digamma {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto
      (fun n : ℕ => (Real.log n : ℂ) - ∑ j ∈ Finset.range n, (x + (j : ℂ))⁻¹)
      Filter.atTop (nhds (Complex.digamma x)) := by
  set R : ℝ := ‖x‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  have hxball : x ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right, hR]; linarith
  have hxmem : x ∈ gammaRegion R := Set.mem_inter hxball hx
  have hnepole : ∀ m : ℕ, x ≠ -m := gammaRegion_ne_neg_nat hxmem
  have hΓ : Complex.Gamma x ≠ 0 := Complex.Gamma_ne_zero hnepole
  have hdiff : ∀ᶠ n : ℕ in Filter.atTop,
      DifferentiableOn ℂ (fun s : ℂ => (Complex.GammaSeq s n)⁻¹) (gammaRegion R) := by
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    exact (differentiable_inv_GammaSeq hn).differentiableOn
  have hmain := Complex.logDeriv_tendsto (isOpen_gammaRegion R) hxmem
    (tendstoLocallyUniformlyOn_inv_GammaSeq hRpos) hdiff (inv_ne_zero hΓ)
  -- the limit is `−ψ(x)`
  have hrhs : logDeriv (fun s : ℂ => (Complex.Gamma s)⁻¹) x = -Complex.digamma x :=
    logDeriv_inv_fun hΓ (Complex.differentiableAt_Gamma x hnepole)
  rw [hrhs] at hmain
  -- the sequence is the finite Euler sum
  have hseq : ∀ᶠ n : ℕ in Filter.atTop,
      logDeriv (fun s : ℂ => (Complex.GammaSeq s n)⁻¹) x
        = ((∑ j ∈ Finset.range n, (x + (j : ℂ))⁻¹) + (x + (n : ℂ))⁻¹)
          - (Real.log n : ℂ) := by
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    rw [logDeriv_inv_GammaSeq hn hx, Finset.sum_range_succ]
  rw [Filter.tendsto_congr' hseq] at hmain
  -- the extra term vanishes
  have hterm : Filter.Tendsto (fun n : ℕ => (x + (n : ℂ))⁻¹) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Filter.Tendsto (fun n : ℕ => x.re + (n : ℝ)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb.inv_tendsto_atTop
    have hpos : (0 : ℝ) < x.re + (n : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hle : x.re + (n : ℝ) ≤ ‖x + (n : ℂ)‖ := by
      have h := Complex.re_le_norm (x + (n : ℂ))
      simpa using h
    rw [norm_inv]
    have h1 := one_div_le_one_div_of_le hpos hle
    simpa [one_div] using h1
  have hfinal := hmain.sub hterm
  simp only [sub_zero] at hfinal
  have hneg := hfinal.neg
  rw [neg_neg] at hneg
  refine hneg.congr fun n => ?_
  ring

end Cvs.Zeta
