import Mathlib
import Cvs.Finite.SymmetricWindowNoSine
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.Finite.WindowedPartialSumsConverge
import Cvs.Upstream.L2TranslationContinuity
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.EvenBottomAttained
import Cvs.WeilForm.Mollify.WindowNormalisation
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WeilFormSurvivesTruncation
import Cvs.WeilForm.WindowConstraintSet

/-!
# The mode sums are form-dense in the even sector

    ∃ coefficients `A N` with `windowMode L (range N) (A N) ∈ evenWindowSet L`,
    converging to `g` in `L²` and in form

the normalising factor absorbed into the coefficients, so the approximants are mode sums.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.ModeSumsFormDenseEven

variable {L : ℝ}

/-- **Scaling a mode sum scales its coefficients.** -/
theorem windowMode_smul (L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (c : ℝ) :
    (fun x => c * Cvs.Finite.WindowedModeSumDomain.windowMode L s a x)
      = Cvs.Finite.WindowedModeSumDomain.windowMode L s (fun n => c * a n) := by
  funext x
  rw [Cvs.Finite.WindowedModeSumDomain.windowMode, Cvs.Finite.WindowedModeSumDomain.windowMode]
  by_cases hx : x ∈ Set.Ioc (0:ℝ) L
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    show c * (∑ n ∈ s, a n * Real.cos (2 * π * n / L * x))
      = ∑ n ∈ s, c * a n * Real.cos (2 * π * n / L * x)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- **A windowed mode sum is symmetric off the two endpoints.** -/
theorem windowMode_symm_ae (hL : L ≠ 0) (s : Finset ℕ) (a : ℕ → ℝ) :
    (fun x => Cvs.Finite.WindowedModeSumDomain.windowMode L s a (L - x))
      =ᵐ[(volume : Measure ℝ)] Cvs.Finite.WindowedModeSumDomain.windowMode L s a := by
  have hnull : (volume : Measure ℝ) ({(0:ℝ)} ∪ {L}) = 0 := by
    refine measure_union_null ?_ ?_ <;> exact Real.volume_singleton
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
  intro x hx
  by_contra hmem
  refine hx ?_
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hmem
  obtain ⟨hx0, hxL⟩ := hmem
  simp only [Cvs.Finite.WindowedModeSumDomain.windowMode]
  by_cases hin : x ∈ Set.Ioc (0:ℝ) L
  · have hin' : L - x ∈ Set.Ioc (0:ℝ) L := by
      simp only [Set.mem_Ioc] at hin ⊢
      constructor
      · rcases lt_or_eq_of_le hin.2 with h | h
        · linarith
        · exact absurd h hxL
      · linarith [hin.1]
    rw [Set.indicator_of_mem hin', Set.indicator_of_mem hin]
    exact Cvs.Finite.SymmetricWindowNoSine.modeSum_symm hL s a x
  · have hout : L - x ∉ Set.Ioc (0:ℝ) L := by
      simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hin ⊢
      rcases hin with h | h
      · have hlt : x < 0 := lt_of_le_of_ne h hx0
        exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    rw [Set.indicator_of_notMem hout, Set.indicator_of_notMem hin]

/-- **The mode sums are form-dense in the even sector.** -/
theorem exists_modeApprox (hL : 0 < L) (P R : ℕ) {g g' : ℝ → ℝ}
    (hgd : ∀ x : ℝ, HasDerivAt g (g' x) x) (hg'c : Continuous g')
    (hgs : ∀ x ∉ Set.Ioc (0:ℝ) L, g x = 0) (hsymm : ∀ x : ℝ, g (L - x) = g x)
    (hgnorm : (∫ x : ℝ, g x ^ 2) = 1)
    (hglevy : IntegrableOn (Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous.levy g) (Set.Ioi 0) (volume : Measure ℝ)) :
    ∃ (S : ℕ → Finset ℕ) (A : ℕ → ℕ → ℝ),
      (∀ k, Cvs.Finite.WindowedModeSumDomain.windowMode L (S k) (A k)
        ∈ Cvs.WeilForm.EvenBottomAttained.evenWindowSet L) ∧
      Filter.Tendsto (fun k : ℕ => ∫ x : ℝ,
          (Cvs.Finite.WindowedModeSumDomain.windowMode L (S k) (A k) x - g x) ^ 2)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R
          (Cvs.Finite.WindowedModeSumDomain.windowMode L (S k) (A k)))
        Filter.atTop (nhds (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g)) := by
  classical
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt
  have hgmem : MemLp g 2 (volume : Measure ℝ) :=
    Cvs.WeilForm.WeilFormSurvivesTruncation.memLp_of_support hL hgc hgs
  set a : ℕ → ℝ := Cvs.Finite.WindowCosineBessel.coef L g with ha
  set F : ℕ → ℝ → ℝ := fun N => Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range N) a with hFdef
  have hFmem : ∀ N, MemLp (F N) 2 (volume : Measure ℝ) := fun N =>
    Cvs.Finite.WindowedModeSumDomain.memLp_windowMode L (Finset.range N) a
  have hbdd : ∀ N, (∫ x : ℝ, F N x ^ 2) ≤ 1 := by
    intro N
    have h := Cvs.Finite.WindowedPartialSumsConverge.integral_windowMode_sq_le hL hgc hgs N
    rw [hgnorm] at h
    exact h
  have hconv := Cvs.Finite.WindowedPartialSumsConverge.tendsto_integral_sub hL hgc hgs hsymm
  have hform := Cvs.WeilForm.WeilFormSurvivesTruncation.tendsto_weilForm_modeSum hL P R hgd hg'c hgs hsymm
  have hE := Cvs.WeilForm.Mollify.WindowNormalisation.tendsto_integral_sq (C := 1) hgmem hFmem hconv hbdd
  rw [hgnorm] at hE
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hE (1 / 2) (by norm_num)
  have hEpos : ∀ k : ℕ, 0 < ∫ x : ℝ, F (k + N₀) x ^ 2 := by
    intro k
    have h := hN₀ (k + N₀) (Nat.le_add_left N₀ k)
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  refine ⟨fun k => Finset.range (k + N₀),
    fun k => fun n => (Real.sqrt (∫ y : ℝ, F (k + N₀) y ^ 2))⁻¹ * a n, ?_, ?_, ?_⟩
  · intro k
    have hsm := windowMode_smul L (Finset.range (k + N₀)) a
      (Real.sqrt (∫ y : ℝ, F (k + N₀) y ^ 2))⁻¹
    refine ⟨?_, ?_⟩
    · have hmem := Cvs.WeilForm.Mollify.WindowNormalisation.mem_windowSet_normalised (hFmem (k + N₀))
        (Cvs.Finite.WindowedModeSumDomain.support_windowMode L (Finset.range (k + N₀)) a)
        (Cvs.Finite.WindowedModeSumDomain.integrableOn_levy_windowMode hL (Finset.range (k + N₀)) a)
        (hEpos k)
      rwa [hsm] at hmem
    · exact windowMode_symm_ae hL.ne' _ _
  · -- the `L²` distance
    set c : ℕ → ℝ := fun k => (Real.sqrt (∫ y : ℝ, F (k + N₀) y ^ 2))⁻¹ with hc
    set e : ℕ → ℝ := fun k => Real.sqrt (∫ y : ℝ, F (k + N₀) y ^ 2) with he
    have hEshift : Filter.Tendsto (fun k : ℕ => ∫ y : ℝ, F (k + N₀) y ^ 2)
        Filter.atTop (nhds 1) := (Filter.tendsto_add_atTop_iff_nat N₀).mpr hE
    have hetend : Filter.Tendsto e Filter.atTop (nhds 1) := by
      have := (Real.continuous_sqrt.tendsto 1).comp hEshift
      simpa [he, Function.comp_def] using this
    have hctend : Filter.Tendsto c Filter.atTop (nhds 1) := by
      have := hetend.inv₀ one_ne_zero
      rw [inv_one] at this
      exact this
    set d : ℕ → ℝ := fun k => Real.sqrt (∫ x : ℝ, (F (k + N₀) x - g x) ^ 2) with hd
    have hdtend : Filter.Tendsto d Filter.atTop (nhds 0) := by
      have hshift : Filter.Tendsto (fun k : ℕ => ∫ x : ℝ, (F (k + N₀) x - g x) ^ 2)
          Filter.atTop (nhds 0) := (Filter.tendsto_add_atTop_iff_nat N₀).mpr hconv
      have := (Real.continuous_sqrt.tendsto 0).comp hshift
      simpa [hd, Real.sqrt_zero, Function.comp_def] using this
    have hbtot : Filter.Tendsto (fun k : ℕ => (|c k - 1| * e k + d k) ^ 2)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k : ℕ => |c k - 1|) Filter.atTop (nhds 0) := by
        have hs : Filter.Tendsto (fun k : ℕ => c k - 1) Filter.atTop (nhds 0) := by
          have h0 := hctend.sub_const 1
          rw [sub_self] at h0
          exact h0
        have := (continuous_abs.tendsto (0:ℝ)).comp hs
        simpa [Function.comp_def] using this
      have h2 := (h1.mul hetend).add hdtend
      have h3 := h2.pow 2
      simpa using h3
    refine squeeze_zero (fun k => integral_nonneg fun x => sq_nonneg _) (fun k => ?_) hbtot
    have hsm := windowMode_smul L (Finset.range (k + N₀)) a (c k)
    rw [← hsm]
    have hcF : MemLp (fun x : ℝ => c k * F (k + N₀) x) 2 (volume : Measure ℝ) :=
      (hFmem _).const_mul _
    have htri := Cvs.Upstream.L2TranslationContinuity.sqrt_integral_sub_sq_triangle hcF
      (hFmem (k + N₀)) hgmem
    have hfirst : (∫ x : ℝ, (c k * F (k + N₀) x - F (k + N₀) x) ^ 2)
        = (c k - 1) ^ 2 * ∫ y : ℝ, F (k + N₀) y ^ 2 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have hsqrt1 : Real.sqrt (∫ x : ℝ, (c k * F (k + N₀) x - F (k + N₀) x) ^ 2)
        = |c k - 1| * e k := by
      rw [hfirst, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, he]
    rw [hsqrt1] at htri
    have hnn : 0 ≤ ∫ x : ℝ, (c k * F (k + N₀) x - g x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    nlinarith [Real.sq_sqrt hnn, htri,
      Real.sqrt_nonneg (∫ x : ℝ, (c k * F (k + N₀) x - g x) ^ 2),
      abs_nonneg (c k - 1), Real.sqrt_nonneg (∫ y : ℝ, F (k + N₀) y ^ 2), hdtend]
  · -- the form
    have hEshift : Filter.Tendsto (fun k : ℕ => ∫ y : ℝ, F (k + N₀) y ^ 2)
        Filter.atTop (nhds 1) := (Filter.tendsto_add_atTop_iff_nat N₀).mpr hE
    have hinv : Filter.Tendsto (fun k : ℕ => (∫ y : ℝ, F (k + N₀) y ^ 2)⁻¹)
        Filter.atTop (nhds 1) := by
      have := hEshift.inv₀ one_ne_zero
      rw [inv_one] at this
      exact this
    have hWshift : Filter.Tendsto
        (fun k : ℕ => Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (F (k + N₀))) Filter.atTop
        (nhds (Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R g)) :=
      (Filter.tendsto_add_atTop_iff_nat N₀).mpr hform
    have hprod := hinv.mul hWshift
    rw [one_mul] at hprod
    refine hprod.congr (fun k => ?_)
    have hsm := windowMode_smul L (Finset.range (k + N₀)) a
      (Real.sqrt (∫ y : ℝ, F (k + N₀) y ^ 2))⁻¹
    rw [← hsm, Cvs.WeilForm.Mollify.WindowNormalisation.weilForm_normalised P R (hEpos k)]

end Cvs.WeilForm.ModeSumsFormDenseEven
