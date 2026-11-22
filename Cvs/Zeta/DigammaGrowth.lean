import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Weierstrass

/-!
# `‖ψ(w)‖ = O(log |Im w|)` on a vertical strip

The digamma growth bound the `ξ` transfer needs, on a vertical strip.
-/

open Complex Real Finset

namespace Cvs.Zeta

/-- The Gauss-series term, in closed form. -/
theorem gauss_term_eq (x : ℂ) (j : ℕ) (h2 : x + (j : ℂ) ≠ 0) :
    ((1 : ℂ) + j)⁻¹ - (x + j)⁻¹ = (x - 1) / (((1 : ℂ) + j) * (x + j)) := by
  have h1 : ((1 : ℂ) + j) ≠ 0 := by
    intro hc
    have : ((1 : ℂ) + j).re = 0 := by rw [hc]; simp
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) j]
  field_simp
  ring

theorem norm_one_add_nat (j : ℕ) : ‖(1 : ℂ) + j‖ = 1 + j := by
  rw [show (1 : ℂ) + j = ((1 + j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem gauss_term_norm (x : ℂ) (j : ℕ) (hj : x + (j : ℂ) ≠ 0) :
    ‖((1 : ℂ) + j)⁻¹ - (x + j)⁻¹‖ = ‖x - 1‖ / ((1 + j) * ‖x + j‖) := by
  rw [gauss_term_eq x j hj, norm_div, norm_mul, norm_one_add_nat]

theorem abs_im_le_norm_add_nat (x : ℂ) (j : ℕ) : |x.im| ≤ ‖x + j‖ := by
  refine le_trans ?_ (Complex.abs_im_le_norm (x + j))
  simp

theorem nat_le_norm_add_nat {x : ℂ} (hx : 0 ≤ x.re) (j : ℕ) : (j : ℝ) ≤ ‖x + j‖ := by
  refine le_trans ?_ (Complex.abs_re_le_norm (x + j))
  have hre : (x + (j : ℂ)).re = x.re + j := by simp
  rw [hre, abs_of_nonneg (by positivity)]
  linarith

/-- **The head of the Gauss series**, bounded by the harmonic number. -/
theorem sum_head_le {x : ℂ} (h3 : 1 ≤ |x.im|) (N : ℕ) :
    ∑ j ∈ range N, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖)
      ≤ ‖x - 1‖ / |x.im| * (1 + Real.log N) := by
  have hx0 : (0 : ℝ) < |x.im| := by linarith
  have hstep : ∀ j ∈ range N, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖)
      ≤ ‖x - 1‖ / |x.im| * (1 / (1 + (j : ℝ))) := by
    intro j _
    have hj0 : (0 : ℝ) < 1 + (j : ℝ) := by positivity
    have hge : (1 + (j : ℝ)) * |x.im| ≤ (1 + (j : ℝ)) * ‖x + j‖ :=
      mul_le_mul_of_nonneg_left (abs_im_le_norm_add_nat x j) hj0.le
    have hrw : ‖x - 1‖ / |x.im| * (1 / (1 + (j : ℝ)))
        = ‖x - 1‖ / ((1 + (j : ℝ)) * |x.im|) := by
      field_simp
    rw [hrw]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hge
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have hre : ∀ M : ℕ, ∑ j ∈ range M, (1 / (1 + (j : ℝ))) = (harmonic M : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih, harmonic_succ]
        push_cast
        ring
  rw [hre N]
  exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)

/-- **The tail of the Gauss series**, telescoping.  `1/((1+j)j) = 1/j − 1/(j+1)` exactly. -/
theorem sum_tail_le {x : ℂ} (hx : 0 ≤ x.re) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ j ∈ Finset.Ico N M, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖) ≤ ‖x - 1‖ / N := by
  have hstep : ∀ j ∈ Finset.Ico N M, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖)
      ≤ ‖x - 1‖ / (j : ℝ) - ‖x - 1‖ / ((j : ℝ) + 1) := by
    intro j hj
    have hj1 : 1 ≤ j := le_trans hN (Finset.mem_Ico.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hge : (1 + (j : ℝ)) * (j : ℝ) ≤ (1 + (j : ℝ)) * ‖x + j‖ :=
      mul_le_mul_of_nonneg_left (nat_le_norm_add_nat hx j) (by positivity)
    have hrw : ‖x - 1‖ / (j : ℝ) - ‖x - 1‖ / ((j : ℝ) + 1)
        = ‖x - 1‖ / ((1 + (j : ℝ)) * (j : ℝ)) := by
      field_simp
      ring
    rw [hrw]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hge
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_Ico_eq_sum_range]
  calc ∑ i ∈ range (M - N), (‖x - 1‖ / ((N + i : ℕ) : ℝ)
        - ‖x - 1‖ / (((N + i : ℕ) : ℝ) + 1))
      = ∑ i ∈ range (M - N), (‖x - 1‖ / ((N : ℝ) + i)
        - ‖x - 1‖ / ((N : ℝ) + ((i + 1 : ℕ) : ℝ))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring_nf
    _ = ‖x - 1‖ / ((N : ℝ) + ((0 : ℕ) : ℝ))
        - ‖x - 1‖ / ((N : ℝ) + ((M - N : ℕ) : ℝ)) :=
        Finset.sum_range_sub' (fun i : ℕ => ‖x - 1‖ / ((N : ℝ) + i)) (M - N)
    _ ≤ ‖x - 1‖ / N := by
        have h0 : (0 : ℝ) ≤ ‖x - 1‖ / ((N : ℝ) + ((M - N : ℕ) : ℝ)) := by positivity
        simp only [Nat.cast_zero, add_zero]
        linarith

/-- The partial sums of the Gauss series are bounded by `O(log|Im x|)`, uniformly in `n`. -/
theorem norm_sum_gauss_le {B : ℝ} (hB : 1 ≤ B) {x : ℂ} (h1 : 0 < x.re)
    (h2 : x.re ≤ B) (h3 : 1 ≤ |x.im|) (n : ℕ) :
    ‖∑ j ∈ range n, (((1 : ℂ) + j)⁻¹ - (x + j)⁻¹)‖
      ≤ (B + 2) * (2 + Real.log (2 + |x.im|)) := by
  have hxre : (0 : ℝ) ≤ x.re := le_of_lt h1
  have ht : (0 : ℝ) < |x.im| := by linarith
  set N : ℕ := ⌈|x.im|⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNt : |x.im| ≤ (N : ℝ) := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil |x.im|]
  have hNt2 : (N : ℝ) ≤ |x.im| + 2 := by
    rw [hNdef]; push_cast; linarith [Nat.ceil_lt_add_one ht.le]
  set M : ℕ := max n N with hMdef
  have hnM : n ≤ M := le_max_left _ _
  have hNM : N ≤ M := le_max_right _ _
  have hxj : ∀ j : ℕ, x + (j : ℂ) ≠ 0 := by
    intro j hc
    have : (x + (j : ℂ)).re = 0 := by rw [hc]; simp
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) j]
  -- pass to absolute values and enlarge the range
  have hstep1 : ‖∑ j ∈ range n, (((1 : ℂ) + j)⁻¹ - (x + j)⁻¹)‖
      ≤ ∑ j ∈ range M, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖) := by
    refine (norm_sum_le _ _).trans ?_
    have hcongr : ∑ j ∈ range n, ‖((1 : ℂ) + j)⁻¹ - (x + j)⁻¹‖
        = ∑ j ∈ range n, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖) :=
      Finset.sum_congr rfl fun j _ => gauss_term_norm x j (hxj j)
    rw [hcongr]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hj) hnM)) fun j _ _ => by positivity
  -- split
  have hsplit : ∑ j ∈ range M, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖)
      = (∑ j ∈ range N, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖))
        + ∑ j ∈ Finset.Ico N M, ‖x - 1‖ / ((1 + (j : ℝ)) * ‖x + j‖) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNM]
  rw [hsplit] at hstep1
  have hhead := sum_head_le h3 N
  have htail := sum_tail_le hxre hN1 hNM
  have htail' : ‖x - 1‖ / (N : ℝ) ≤ ‖x - 1‖ / |x.im| :=
    div_le_div_of_nonneg_left (norm_nonneg _) ht hNt
  -- the numerator
  have hnum : ‖x - 1‖ ≤ (B + 2) * |x.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hr : (x - 1).re = x.re - 1 := by simp
    have hi : (x - 1).im = x.im := by simp
    rw [hr, hi]
    have : |x.re - 1| ≤ B + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith
  have hlogN : Real.log N ≤ Real.log (2 + |x.im|) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (2 + |x.im|) :=
    Real.log_nonneg (by linarith)
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hquot : ‖x - 1‖ / |x.im| ≤ B + 2 := by
    rw [div_le_iff₀ ht]; linarith
  have hq0 : (0 : ℝ) ≤ ‖x - 1‖ / |x.im| := by positivity
  calc ‖∑ j ∈ range n, (((1 : ℂ) + j)⁻¹ - (x + j)⁻¹)‖
      ≤ ‖x - 1‖ / |x.im| * (1 + Real.log N) + ‖x - 1‖ / |x.im| := by linarith
    _ = ‖x - 1‖ / |x.im| * (2 + Real.log N) := by ring
    _ ≤ (B + 2) * (2 + Real.log (2 + |x.im|)) := by
        refine mul_le_mul hquot (by linarith) (by linarith) (by linarith)

/-- **`ψ(x) − ψ(1)` is `O(log|Im x|)` on any vertical strip in the right half-plane.** -/
theorem norm_digamma_sub_le {B : ℝ} (hB : 1 ≤ B) {x : ℂ} (h1 : 0 < x.re)
    (h2 : x.re ≤ B) (h3 : 1 ≤ |x.im|) :
    ‖Complex.digamma x - Complex.digamma 1‖
      ≤ (B + 2) * (2 + Real.log (2 + |x.im|)) := by
  have hA := tendsto_euler_digamma h1
  have hA1 := tendsto_euler_digamma (x := (1 : ℂ)) (by norm_num)
  have hdiff : Filter.Tendsto
      (fun n : ℕ => ∑ j ∈ range n, (((1 : ℂ) + j)⁻¹ - (x + j)⁻¹))
      Filter.atTop (nhds (Complex.digamma x - Complex.digamma 1)) := by
    refine (hA.sub hA1).congr fun n => ?_
    rw [Finset.sum_sub_distrib]
    ring
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ‖∑ j ∈ range n, (((1 : ℂ) + j)⁻¹ - (x + j)⁻¹)‖)
      Filter.atTop (nhds ‖Complex.digamma x - Complex.digamma 1‖) :=
    (continuous_norm.tendsto _).comp hdiff
  exact le_of_tendsto hnorm
    (Filter.Eventually.of_forall fun n => norm_sum_gauss_le hB h1 h2 h3 n)

/-- **`‖ψ(x)‖ = O(log|Im x|)` on any vertical strip in the right half-plane.** This is the bound
the `ξ` transfer needs and that neither Mathlib nor this repo had. -/
theorem exists_norm_digamma_le (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 < x.re → x.re ≤ B → 1 ≤ |x.im| →
      ‖Complex.digamma x‖ ≤ C * (1 + Real.log (2 + |x.im|)) := by
  refine ⟨2 * (B + 2) + ‖Complex.digamma 1‖, by positivity, fun x h1 h2 h3 => ?_⟩
  have hlog0 : 0 ≤ Real.log (2 + |x.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg x.im])
  have hd := norm_digamma_sub_le hB h1 h2 h3
  have hsplit : ‖Complex.digamma x‖
      ≤ ‖Complex.digamma x - Complex.digamma 1‖ + ‖Complex.digamma 1‖ := by
    simpa using norm_add_le (Complex.digamma x - Complex.digamma 1) (Complex.digamma 1)
  nlinarith [norm_nonneg (Complex.digamma 1)]

end Cvs.Zeta
