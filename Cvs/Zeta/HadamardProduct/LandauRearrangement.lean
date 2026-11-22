import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.HadamardProduct.FarZeroTail
import Cvs.Zeta.HadamardProduct.GenusOneSummable
import Cvs.Zeta.HadamardProduct.GenusOneTermwiseDeriv

/-!
# The Landau/Hadamard rearrangement
-/

noncomputable section

open Complex Filter Topology Metric

namespace Cvs.ZeroFree

variable {ι : Type*} {a : ι → ℂ}

/-- The genus-1 series over the zeros **outside** a finite set. -/
def farSum (a : ι → ℂ) (N : Finset ι) (z : ℂ) : ℂ :=
  ∑' n : {n : ι // n ∉ N}, (1 / (z - a (n : ι)) + 1 / a (n : ι))

/-- The genus-1 normalisation of the zeros **inside** the finite set — a constant. -/
def nearConst (a : ι → ℂ) (N : Finset ι) : ℂ := ∑ n ∈ N, 1 / a n

/-- **The rearrangement.**  Landau's difference is `h'` plus the far series plus a constant. -/
theorem landau_rearrange (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (h1 : ∀ n, 1 ≤ ‖a n‖)
    {N : Finset ι} {z D u : ℂ} (hz : ∀ n, z ≠ a n)
    (hHad : D = (∑' n, (1 / (z - a n) + 1 / a n)) + u) :
    D - ∑ n ∈ N, 1 / (z - a n) = u + (farSum a N z + nearConst a N) := by
  have hsum := Cvs.ZeroFree.summable_genus_one ha h1 hz
  have hsplit : ∑ n ∈ N, (1 / (z - a n) + 1 / a n)
      + ∑' n : {x : ι // x ∉ N}, (1 / (z - a (n : ι)) + 1 / a (n : ι))
      = ∑' n, (1 / (z - a n) + 1 / a n) := hsum.sum_add_tsum_subtype_compl N
  have hdist : ∑ n ∈ N, (1 / (z - a n) + 1 / a n)
      = (∑ n ∈ N, 1 / (z - a n)) + nearConst a N := Finset.sum_add_distrib
  rw [hHad, ← hsplit, hdist, farSum]
  ring

/-- The bound Landau supplies, moved onto the holomorphic part `G`. -/
theorem norm_le_of_landau (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) (h1 : ∀ n, 1 ≤ ‖a n‖)
    {N : Finset ι} {z D u : ℂ} {B : ℝ} (hz : ∀ n, z ≠ a n)
    (hHad : D = (∑' n, (1 / (z - a n) + 1 / a n)) + u)
    (hL : ‖D - ∑ n ∈ N, 1 / (z - a n)‖ ≤ B) :
    ‖u + (farSum a N z + nearConst a N)‖ ≤ B := by
  rwa [landau_rearrange ha h1 hz hHad] at hL

/-! ### `G_r` is holomorphic, and its derivative is the far tail -/

/-- The far family is uniformly far: `n ∉ N` gives `4·(r/4) ≤ ‖aₙ‖`. -/
theorem farSum_hasDerivAt (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) {r : ℝ} (hr : 0 < r)
    {N : Finset ι} (hN : ∀ n, n ∉ N → r < ‖a n‖) {z : ℂ} (hz : ‖z‖ < r / 4) :
    HasDerivAt (fun w : ℂ => farSum a N w + nearConst a N)
      (∑' n : {x : ι // x ∉ N}, -(1 / (z - a (n : ι)) ^ 2)) z := by
  have hsub : Summable fun n : {x : ι // x ∉ N} => ‖a (n : ι)‖⁻¹ ^ 2 := ha.subtype _
  have hfar : ∀ n : {x : ι // x ∉ N}, 4 * (r / 4) ≤ ‖a (n : ι)‖ := by
    intro n
    have := hN (n : ι) n.2
    linarith
  have h := Cvs.ZeroFree.hasDerivAt_tsum_genus_one hsub (by linarith : (0:ℝ) < r / 4) hfar hz
  exact h.add_const _

/-- **`G_r` is holomorphic on the ball.** -/
theorem differentiableOn_farSum (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) {r : ℝ} (hr : 0 < r)
    {N : Finset ι} (hN : ∀ n, n ∉ N → r < ‖a n‖) :
    DifferentiableOn ℂ (fun w : ℂ => farSum a N w + nearConst a N) (ball (0 : ℂ) (r / 4)) := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz
  exact (farSum_hasDerivAt ha hr hN hz).differentiableAt.differentiableWithinAt

/-- **`G_r'` is bounded by the far tail**, on the ball of radius `r/4`. -/
theorem norm_deriv_farSum_le (ha : Summable fun n => ‖a n‖⁻¹ ^ 2) {r : ℝ} (hr : 0 < r)
    {N : Finset ι} (hN : ∀ n, n ∉ N → r < ‖a n‖) {z : ℂ} (hz : ‖z‖ < r / 4) :
    ‖deriv (fun w : ℂ => farSum a N w + nearConst a N) z‖
      ≤ ∑' n : {x : ι // x ∉ N}, 4 * ‖a (n : ι)‖⁻¹ ^ 2 := by
  have hsub : Summable fun n : {x : ι // x ∉ N} => ‖a (n : ι)‖⁻¹ ^ 2 := ha.subtype _
  have hfar : ∀ n : {x : ι // x ∉ N}, 4 * (r / 4) ≤ ‖a (n : ι)‖ := by
    intro n
    have := hN (n : ι) n.2
    linarith
  rw [(farSum_hasDerivAt ha hr hN hz).deriv]
  exact Cvs.ZeroFree.norm_tsum_far_le hsub (by linarith : (0:ℝ) < r / 4) hfar hz

end Cvs.ZeroFree
