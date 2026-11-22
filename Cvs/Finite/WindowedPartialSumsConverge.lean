import Mathlib
import Cvs.Finite.CosineCoefficientCompleteness
import Cvs.Finite.ModePairingTable
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.SelfConvolutionL2Continuous
import Cvs.Zeta.WeilPositivityStatement

/-!
# The windowed partial sums converge to the target on the line

    ∫_ℝ (F_N − g)² → 0,  hence the Lévy integrand converges at every displacement

for `g` continuous and supported in the window, `F_N` its windowed cosine partial sum.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.Finite.WindowedPartialSumsConverge

variable {L : ℝ}

/-- **The `L²` distance on the line is the distance on the window.** -/
theorem integral_sub_eq (hL : 0 < L) {g : ℝ → ℝ}
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ x : ℝ, (Cvs.Finite.WindowedModeSumDomain.windowMode L s a x - g x) ^ 2)
      = ∫ x in (0:ℝ)..L, (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x - g x) ^ 2 := by
  have hfun : (fun x : ℝ => (Cvs.Finite.WindowedModeSumDomain.windowMode L s a x - g x) ^ 2)
      = Set.indicator (Set.Ioc (0:ℝ) L)
        (fun x => (Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a x - g x) ^ 2) := by
    funext x
    rw [Cvs.Finite.WindowedModeSumDomain.windowMode]
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, hgs x hx]
      norm_num
  rw [hfun, integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le hL.le]

/-- **The windowed partial sums converge in `L²` on the line.** -/
theorem tendsto_integral_sub (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) (hsymm : ∀ x : ℝ, g (L - x) = g x) :
    Filter.Tendsto (fun N : ℕ => ∫ x : ℝ,
        (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
          (Cvs.Finite.WindowCosineBessel.coef L g) x - g x) ^ 2)
      Filter.atTop (nhds 0) := by
  have h := Cvs.Finite.CosineCoefficientCompleteness.tendsto_integral_sub_modeSum hL hgc hsymm
  refine h.congr (fun N => ?_)
  rw [integral_sub_eq hL hgs (Finset.range N) (Cvs.Finite.WindowCosineBessel.coef L g)]
  exact intervalIntegral.integral_congr (fun x _ => by ring)

/-- **The line integral of a window function is the window integral.** -/
theorem integral_sq_eq (hL : 0 < L) {g : ℝ → ℝ}
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) :
    (∫ x : ℝ, g x ^ 2) = ∫ x in (0:ℝ)..L, g x ^ 2 := by
  have hfun : (fun x : ℝ => g x ^ 2)
      = Set.indicator (Set.Ioc (0:ℝ) L) (fun x => g x ^ 2) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0:ℝ) L
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hgs x hx]; norm_num
  calc (∫ x : ℝ, g x ^ 2)
      = ∫ x : ℝ, Set.indicator (Set.Ioc (0:ℝ) L) (fun x => g x ^ 2) x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hfun x)
    _ = ∫ x in Set.Ioc (0:ℝ) L, g x ^ 2 := integral_indicator measurableSet_Ioc
    _ = ∫ x in (0:ℝ)..L, g x ^ 2 := (intervalIntegral.integral_of_le hL.le).symm

/-- **The partial sums keep no more energy than the target.** -/
theorem integral_windowMode_sq_le (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) (N : ℕ) :
    (∫ x : ℝ, Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
        (Cvs.Finite.WindowCosineBessel.coef L g) x ^ 2)
      ≤ ∫ x : ℝ, g x ^ 2 := by
  have hind : (∫ x : ℝ, Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
      (Cvs.Finite.WindowCosineBessel.coef L g) x ^ 2)
      = ∫ x in (0:ℝ)..L, Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (Finset.range N)
        (Cvs.Finite.WindowCosineBessel.coef L g) x ^ 2 := by
    have hfun : (fun x : ℝ => Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
        (Cvs.Finite.WindowCosineBessel.coef L g) x ^ 2)
        = Set.indicator (Set.Ioc (0:ℝ) L)
          (fun x => Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (Finset.range N)
            (Cvs.Finite.WindowCosineBessel.coef L g) x ^ 2) := by
      funext x
      rw [Cvs.Finite.WindowedModeSumDomain.windowMode]
      by_cases hx : x ∈ Set.Ioc (0:ℝ) L
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; norm_num
    rw [hfun, integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hL.le]
  rw [hind, Cvs.Finite.ModePairingTable.integral_modeSum_sq hL, integral_sq_eq hL hgs]
  exact Cvs.Finite.WindowCosineBessel.bessel hL hgc (Finset.range N)

/-- **The self-convolutions converge.** -/
theorem tendsto_selfConvolution (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) (hsymm : ∀ x : ℝ, g (L - x) = g x)
    (hgmem : MemLp g 2 (volume : Measure ℝ)) (v : ℝ) :
    Filter.Tendsto (fun N : ℕ => selfConvolution
        (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
          (Cvs.Finite.WindowCosineBessel.coef L g)) v)
      Filter.atTop (nhds (selfConvolution g v)) := by
  have hconv := tendsto_integral_sub hL hgc hgs hsymm
  set E : ℝ := Real.sqrt (∫ x : ℝ, g x ^ 2) with hE
  have hEnn : 0 ≤ E := Real.sqrt_nonneg _
  set s : ℕ → ℝ := fun N => Real.sqrt (∫ x : ℝ,
    (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
      (Cvs.Finite.WindowCosineBessel.coef L g) x - g x) ^ 2) with hs
  have hstend : Filter.Tendsto s Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hconv
    simpa [hs, Real.sqrt_zero, Function.comp_def] using this
  have hprod : Filter.Tendsto (fun N : ℕ => s N * (2 * E)) Filter.atTop (nhds 0) := by
    have := hstend.mul_const (2 * E)
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hprod ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hkey := Cvs.WeilForm.SelfConvolutionL2Continuous.abs_selfConvolution_sub_le
    (f := Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) (Cvs.Finite.WindowCosineBessel.coef L g))
    (h := g) v (Cvs.Finite.WindowedModeSumDomain.memLp_windowMode L (Finset.range N) _) hgmem
  have hle : Real.sqrt (∫ x : ℝ, Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
      (Cvs.Finite.WindowCosineBessel.coef L g) x ^ 2) ≤ E :=
    Real.sqrt_le_sqrt (integral_windowMode_sq_le hL hgc hgs N)
  have hd := hN₀ N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ s N * (2 * E))] at hd
  rw [Real.dist_eq]
  have hsnn : 0 ≤ s N := Real.sqrt_nonneg _
  nlinarith [hkey, hle, hd, hsnn, hEnn]

/-- **So the Lévy integrand converges at every displacement.** -/
theorem tendsto_levy (hL : 0 < L) {g : ℝ → ℝ} (hgc : Continuous g)
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) (hsymm : ∀ x : ℝ, g (L - x) = g x)
    (hgmem : MemLp g 2 (volume : Measure ℝ)) (u : ℝ) :
    Filter.Tendsto (fun N : ℕ => Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy
        (Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N)
          (Cvs.Finite.WindowCosineBessel.coef L g)) u)
      Filter.atTop (nhds (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g u)) := by
  have h0 := tendsto_selfConvolution hL hgc hgs hsymm hgmem 0
  have h1 := tendsto_selfConvolution hL hgc hgs hsymm hgmem (u / 2)
  have := (h0.sub h1).const_mul (Cvs.WeilForm.Archimedean.LevyDensity.densityU u)
  exact this

end Cvs.Finite.WindowedPartialSumsConverge
