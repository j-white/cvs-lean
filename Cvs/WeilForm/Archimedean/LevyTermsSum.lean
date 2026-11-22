import Mathlib
import Cvs.WeilForm.Archimedean.ElementaryLevyIntegral
import Cvs.Zeta.Digamma

/-!
# The archimedean symbol is a positive sum of Lévy terms

    Re ψ(¼ + it/2) − Re ψ(¼)  =  ∑ₖ digammaDeficit t k,   each term ≥ 0

each term being `∫₀^∞ (1 − cos((t/2)u)) e^{−(¼+k)u} du`, so the symbol is a positive
combination of `1 − cos`.  `log π` cancels in the difference.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set Filter Topology Cvs.Zeta

namespace Cvs.WeilForm.Archimedean.LevyTermsSum

/-- **Each deficit term is a Lévy integral.**  `Laplace`'s closed form at `ω = t/2`,
`c = ¼ + k`, matching `digammaDeficit_eq` on the nose. -/
theorem digammaDeficit_eq_integral (t : ℝ) (k : ℕ) :
    digammaDeficit t k
      = ∫ u in Ioi (0:ℝ),
          (1 - Real.cos (t / 2 * u)) * Real.exp (-((1 / 4 + (k : ℝ)) * u)) := by
  have hc : (0:ℝ) < 1 / 4 + (k : ℝ) := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  rw [Cvs.WeilForm.Archimedean.ElementaryLevyIntegral.integral_one_sub_cos_mul_exp hc (t / 2), digammaDeficit_eq]

/-- The deficit vanishes identically at `t = 0`. -/
theorem digammaDeficit_zero (k : ℕ) : digammaDeficit 0 k = 0 := by
  rw [digammaDeficit_eq]; norm_num

/-- The partial sums of the deficit are exactly the difference of the two Euler–Gauss
approximants — the `log n` and the harmonic terms cancel. -/
theorem sum_deficit_eq_sub (t : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, digammaDeficit t k
      = (Real.log n - ∑ k ∈ Finset.range n, (digammaArg t k)⁻¹.re)
        - (Real.log n - ∑ k ∈ Finset.range n, (digammaArg 0 k)⁻¹.re) := by
  have h : ∀ k ∈ Finset.range n, digammaDeficit t k
      = (digammaArg 0 k)⁻¹.re - (digammaArg t k)⁻¹.re := by
    intro k _
    have h0 : (digammaArg 0 k)⁻¹.re = 1 / (1 / 4 + (k : ℝ)) := by
      have := digammaDeficit_zero k
      rw [digammaDeficit] at this
      linarith
    rw [digammaDeficit, h0]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib]
  ring

/-- **The identification.**  The symbol's increment from `t = 0` is the sum of the
deficits — a series of nonnegative terms, each a Lévy integral. -/
theorem hasSum_digammaDeficit (t : ℝ) [ht : DigammaEulerLimitRe t]
    [h0 : DigammaEulerLimitRe 0] :
    HasSum (digammaDeficit t)
      ((Complex.digamma (digammaArg t 0)).re - (Complex.digamma (digammaArg 0 0)).re) := by
  have hS : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, digammaDeficit t k) atTop
      (𝓝 ((Complex.digamma (digammaArg t 0)).re
            - (Complex.digamma (digammaArg 0 0)).re)) := by
    simp only [sum_deficit_eq_sub t]
    exact ht.tendsto.sub h0.tendsto
  have hmono : Monotone (fun n : ℕ => ∑ k ∈ Finset.range n, digammaDeficit t k) := by
    refine monotone_nat_of_le_succ fun n => ?_
    rw [Finset.sum_range_succ]
    linarith [digammaDeficit_nonneg t n]
  have hle := hmono.ge_of_tendsto hS
  have hsum : Summable (digammaDeficit t) :=
    summable_of_sum_range_le (fun k => digammaDeficit_nonneg t k) hle
  have := hsum.hasSum
  rwa [tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hS] at this

/-- The same, as a `tsum`. -/
theorem tsum_digammaDeficit (t : ℝ) [DigammaEulerLimitRe t] [DigammaEulerLimitRe 0] :
    ∑' k, digammaDeficit t k
      = (Complex.digamma (digammaArg t 0)).re - (Complex.digamma (digammaArg 0 0)).re :=
  (hasSum_digammaDeficit t).tsum_eq

/-- **And the increment is nonnegative** — the symbol is smallest at `t = 0`. -/
theorem sub_nonneg_of_limit (t : ℝ) [DigammaEulerLimitRe t] [DigammaEulerLimitRe 0] :
    0 ≤ (Complex.digamma (digammaArg t 0)).re - (Complex.digamma (digammaArg 0 0)).re := by
  rw [← tsum_digammaDeficit t]
  exact tsum_nonneg fun k => digammaDeficit_nonneg t k

end Cvs.WeilForm.Archimedean.LevyTermsSum
