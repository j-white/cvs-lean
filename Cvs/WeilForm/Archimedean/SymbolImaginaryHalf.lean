import Mathlib
import Cvs.Upstream.GammaEulerLimit
import Cvs.Zeta.Digamma

/-!
# The archimedean symbol's imaginary half, and its series

    archSymbolIm t = Im ψ(¼ + it/2) = ∑ₖ (t/2)/((¼+k)² + (t/2)²)

`Cvs.WeilForm.Archimedean.ArchimedeanUnbounded`'s `archSymbol` is the real part of the same digamma value less `log π`. The upstream
Euler–Gauss limit is complex, so the series comes from taking `.im` where `Cvs.Zeta.DigammaLimitDischarged` took `.re`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real Filter Topology Cvs.Zeta

namespace Cvs.WeilForm.Archimedean.SymbolImaginaryHalf

/-- **The archimedean symbol's imaginary half.** -/
def archSymbolIm (t : ℝ) : ℝ := (Complex.digamma (digammaArg t 0)).im

/-- The `k`-th term of its series. -/
def imTerm (t : ℝ) (k : ℕ) : ℝ := (t / 2) / ((1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2)

theorem denom_pos (t : ℝ) (k : ℕ) : (0:ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2 := by
  have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have : (0:ℝ) < 1 / 4 + (k : ℝ) := by linarith
  positivity

/-- **The inverse's imaginary part is minus the term.** -/
theorem inv_im (t : ℝ) (k : ℕ) : ((digammaArg t k)⁻¹).im = -imTerm t k := by
  rw [Complex.inv_im, Complex.normSq_apply, digammaArg_re, digammaArg_im, imTerm]
  ring

/-- The series converges: the terms are `O(k⁻²)`. -/
theorem summable_imTerm (t : ℝ) : Summable (imTerm t) := by
  have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa using (summable_nat_add_iff 1).mpr h
  refine Summable.of_norm_bounded ((hbase.mul_left (8 * |t|))) (fun k => ?_)
  have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpos : (0:ℝ) < 1 / 4 + (k : ℝ) := by linarith
  have hden : (0:ℝ) < (1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2 := denom_pos t k
  have hlow : ((k : ℝ) + 1) ^ 2 / 16 ≤ (1 / 4 + (k : ℝ)) ^ 2 := by nlinarith
  have hkp : (0:ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  rw [Real.norm_eq_abs, imTerm, abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  have habs : |t / 2| = |t| / 2 := by rw [abs_div]; norm_num
  rw [habs]
  have hfac : (0:ℝ) ≤ 8 * |t| * (1 / ((k : ℝ) + 1) ^ 2) := by positivity
  have hge : ((k : ℝ) + 1) ^ 2 / 16 ≤ (1 / 4 + (k : ℝ)) ^ 2 + (t / 2) ^ 2 := by
    nlinarith [sq_nonneg (t / 2), hlow]
  have hmul := mul_le_mul_of_nonneg_left hge hfac
  have hval : 8 * |t| * (1 / ((k : ℝ) + 1) ^ 2) * (((k : ℝ) + 1) ^ 2 / 16) = |t| / 2 := by
    field_simp
    ring
  linarith [hmul, hval]

/-- **The series sums to the imaginary half**, by taking `.im` of the Euler–Gauss limit. -/
theorem hasSum_imTerm (t : ℝ) : HasSum (imTerm t) (archSymbolIm t) := by
  have hre : 0 < (digammaArg t 0).re := digammaArg_re_pos t
  have hlim := (Complex.continuous_im.tendsto _).comp
    (Cvs.Upstream.GammaEulerLimit.tendsto_digamma hre)
  have hcongr : ∀ n : ℕ,
      (Complex.im ∘ fun n : ℕ => (Real.log n : ℂ) -
        ∑ k ∈ Finset.range n, (digammaArg t 0 + (k : ℂ))⁻¹) n
        = ∑ k ∈ Finset.range n, imTerm t k := by
    intro n
    simp only [Function.comp_apply, Complex.sub_im, Complex.ofReal_im, Complex.im_sum, zero_sub]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← digammaArg_eq_add, inv_im, neg_neg]
  have hS : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, imTerm t k) atTop
      (𝓝 (archSymbolIm t)) := by
    refine hlim.congr fun n => hcongr n
  have hsum := summable_imTerm t
  have := hsum.hasSum
  rwa [tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hS] at this

end Cvs.WeilForm.Archimedean.SymbolImaginaryHalf
