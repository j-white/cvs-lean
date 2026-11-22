import Mathlib
import Cvs.Finite.ModePairingTable
import Cvs.Finite.RecentredTransform
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowedModeSumDomain
import Cvs.Limit.CriticalStripOffAxes
import Cvs.Limit.MovingWindowComparison
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.SpineWithoutSimplicity
import Cvs.Limit.TransformStripLipschitz
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Route.JointGapStripLimit
import Cvs.Upstream.CauchySchwarzLine
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.Archimedean.LevyChannelSumSquares
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.TransformNowhereLocallyZero

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The ground route, conditional on a joint gap

An even mode sum has energy `L‖ξ‖²`, so the recentred transform has type `L e^{|Im z| L/2}`. A sign
of the ground state within squared distance `ε` of even `v`, `L e^{aL/2}√ε → 0` for `a < 1/2`,
carries `v`'s convergence to `Ξ` on `criticalOffAxes` to the ground state; the joint gap
`K(v⬝Mv − λ₁) ≤ μ − λ₁` gives `ε = 2/K`, `K = √x log x` meets the budget, and Cvs.Limit.CriticalStripOffAxes gives RH.
-/

noncomputable section

open Filter Topology MeasureTheory Matrix
open scoped InnerProductSpace

namespace Cvs.Route.GroundRouteJointGap
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI negI_involutive mode_negI mode_injective)
open Cvs.Limit.SpineWithoutSimplicity (ground groundLam ground_spec)
open Cvs.Limit.CriticalStripOffAxes (criticalOffAxes isOpen_criticalOffAxes)

/-! ### The energy of an even mode sum -/

/-- The cosine coefficients of an even vector on `Idx N`, indexed by frequency. -/
def freqCoeff (N : ℕ) (ξ : Idx N → ℝ) : ℕ → ℝ := fun n =>
  if n = 0 then ξ none else if h : n - 1 < N then 2 * ξ (some (⟨n - 1, h⟩, true)) else 0

theorem coeff_freqCoeff (N : ℕ) {ξ : Idx N → ℝ} (hξ : ∀ i, ξ (negI N i) = ξ i) :
    Cvs.Finite.SymmetricModeSet.coeff N (Finset.range (N + 1)) (freqCoeff N ξ) = ξ := by
  funext i
  rcases i with _ | ⟨k, b⟩
  · simp [Cvs.Finite.SymmetricModeSet.coeff, freqCoeff]
  · have hk : (k : ℕ) + 1 ∈ Finset.range (N + 1) := by simp [k.isLt]
    simp only [Cvs.Finite.SymmetricModeSet.coeff, if_pos hk, freqCoeff, Nat.add_sub_cancel, dif_pos k.isLt]
    simp only [Nat.add_one_ne_zero, if_false, Fin.eta]
    cases b
    · have := hξ (some (k, true))
      simp only [negI, Bool.not_true] at this
      rw [this]; ring
    · ring

/-- **An even mode sum has energy `L‖ξ‖²`.** -/
theorem integral_modeSum_sq {L : ℝ} (hL : 0 < L) (N : ℕ) {ξ : Idx N → ℝ}
    (hξ : ∀ i, ξ (negI N i) = ξ i) :
    ∫ t : ℝ, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) ξ t ^ 2 = L * (ξ ⬝ᵥ ξ) := by
  have hw := Cvs.Finite.SymmetricModeSet.windowMode_eq_modeSum L N (Finset.range (N + 1)) (freqCoeff N ξ) subset_rfl
  rw [coeff_freqCoeff N hξ] at hw
  rw [← hw]
  have hsq : (fun t => Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range (N + 1)) (freqCoeff N ξ) t ^ 2)
      = Set.indicator (Set.Ioc (0 : ℝ) L)
          (fun t => Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L (Finset.range (N + 1)) (freqCoeff N ξ) t ^ 2) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) L
    · simp [Cvs.Finite.WindowedModeSumDomain.windowMode, Set.indicator_of_mem ht]
    · simp [Cvs.Finite.WindowedModeSumDomain.windowMode, Set.indicator_of_notMem ht]
  rw [hsq, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hL.le,
    Cvs.Finite.ModePairingTable.integral_modeSum_sq hL, Finset.sum_range_succ',
    ← Fin.sum_univ_eq_sum_range (fun k => (if k + 1 = 0 then (2 : ℝ) else 1)
      * freqCoeff N ξ (k + 1) ^ 2) N]
  rw [dotProduct, Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hf : ∀ k : Fin N, freqCoeff N ξ ((k : ℕ) + 1) = 2 * ξ (some (k, true)) := by
    intro k
    simp only [freqCoeff, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, dif_pos k.isLt,
      Fin.eta]
  have he : ∀ k : Fin N, ξ (some (k, false)) = ξ (some (k, true)) := fun k => by
    simpa [negI] using hξ (some (k, true))
  have hf0 : freqCoeff N ξ 0 = ξ none := by simp [freqCoeff]
  simp only [hf, he, hf0, Nat.add_one_ne_zero, if_false, if_true]
  have h1 : ∑ k : Fin N, 1 * (2 * ξ (some (k, true))) ^ 2
      = 4 * ∑ k : Fin N, ξ (some (k, true)) * ξ (some (k, true)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ k : Fin N, (ξ (some (k, true)) * ξ (some (k, true))
        + ξ (some (k, true)) * ξ (some (k, true)))
      = 2 * ∑ k : Fin N, ξ (some (k, true)) * ξ (some (k, true)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h1, h2]
  ring

/-! ### The recentred transform of a coefficient vector -/

/-- The recentred transform of the mode sum of `ξ` on `Idx N`. -/
def ctransform (L : ℝ) (N : ℕ) (ξ : Idx N → ℝ) : ℂ → ℂ := fun z =>
  Cvs.Finite.RecentredTransform.phase L z * FourierLaplace.fourierLaplace
    (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) ξ)) z

theorem cgtransform_eq (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Cvs.Finite.RecentredTransform.cgtransform P R hL N = ctransform L N (ground P R L hL N) := rfl

theorem modeSum_smul {ι : Type*} [Fintype ι] (L : ℝ) (md : ι → ℤ) (c : ℝ) (ξ : ι → ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L md (c • ξ) = c • Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L md ξ := by
  funext t
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  · ring

theorem modeSum_sub {ι : Type*} [Fintype ι] (L : ℝ) (md : ι → ℤ) (ξ η : ι → ℝ) :
    Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L md (ξ - η)
      = Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L md ξ - Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L md η := by
  funext t
  simp only [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, Pi.sub_apply]
  split_ifs
  · rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  · ring

theorem ctransform_smul (L : ℝ) (N : ℕ) (c : ℝ) (ξ : Idx N → ℝ) (z : ℂ) :
    ctransform L N (c • ξ) z = c * ctransform L N ξ z := by
  simp only [ctransform, modeSum_smul, FourierLaplace.fourierLaplace]
  rw [mul_left_comm, ← integral_const_mul (c : ℂ)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Pi.smul_apply, smul_eq_mul]
  push_cast; ring

/-- **The recentred transform has type `L/2` in `L²`:** for `f, h` in `L²` supported in `(0, L]`,
`‖φ_L(z)(𝓛f(z) − 𝓛h(z))‖ ≤ √(∫(f − h)²)·√L·e^{|Im z| L/2}`. -/
theorem norm_phase_mul_sub_le {L : ℝ} (hL : 0 ≤ L) {f h : ℝ → ℝ}
    (hf : MemLp f 2 (volume : Measure ℝ)) (hh : MemLp h 2 (volume : Measure ℝ))
    (hfs : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) (hhs : ∀ s ∉ Set.Ioc (0:ℝ) L, h s = 0) (z : ℂ) :
    ‖Cvs.Finite.RecentredTransform.phase L z * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
        - Cvs.Finite.RecentredTransform.phase L z
          * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z‖
      ≤ √(∫ t : ℝ, (f t - h t) ^ 2) * √L * Real.exp (|z.im| * L / 2) := by
  have hfint : Integrable f (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hf hfs
  have hhint : Integrable h (volume : Measure ℝ) :=
    Cvs.WeilForm.CentredWindowTranslate.integrable_of_support hL hh hhs
  have hcf : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf f) (volume : Measure ℝ) := hfint.ofReal
  have hch : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf h) (volume : Measure ℝ) := hhint.ofReal
  have hkf := FourierLaplace.integrable_mul_kernel hcf
    (Cvs.WeilForm.TransformNowhereLocallyZero.hasCompactSupport_cf hfs) z
  have hkh := FourierLaplace.integrable_mul_kernel hch
    (Cvs.WeilForm.TransformNowhereLocallyZero.hasCompactSupport_cf hhs) z
  have hsub : Cvs.Finite.RecentredTransform.phase L z
        * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf f) z
      - Cvs.Finite.RecentredTransform.phase L z
        * FourierLaplace.fourierLaplace (Cvs.WeilForm.SelfConvolutionTransform.cf h) z
      = ∫ t : ℝ, Cvs.Finite.RecentredTransform.phase L z
          * (((f t - h t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))) := by
    rw [← mul_sub, FourierLaplace.fourierLaplace, FourierLaplace.fourierLaplace,
      ← integral_sub hkf hkh, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Cvs.WeilForm.SelfConvolutionTransform.cf]
    push_cast
    ring
  rw [hsub]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  set c := Real.exp (|z.im| * L / 2) with hc
  have hpt : ∀ t : ℝ, ‖Cvs.Finite.RecentredTransform.phase L z
      * (((f t - h t : ℝ) : ℂ) * Complex.exp (Complex.I * z * (t : ℂ)))‖
      ≤ c * (|f t - h t| * Cvs.Limit.TransformStripLipschitz.stripWeight L 0 t) := by
    intro t
    rw [norm_mul, norm_mul, Cvs.Limit.MovingWindowComparison.norm_phase, FourierLaplace.norm_exp_I_mul,
      Complex.norm_real, Real.norm_eq_abs]
    by_cases ht : t ∈ Set.Ioc (0:ℝ) L
    · rw [Cvs.Limit.TransformStripLipschitz.stripWeight, Set.indicator_of_mem ht]
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      have hexp : Real.exp (z.im * L / 2) * Real.exp (-(t * z.im)) ≤ c := by
        rw [← Real.exp_add, hc]
        refine Real.exp_le_exp.mpr ?_
        have h1 : z.im * L / 2 + -(t * z.im) = z.im * (L / 2 - t) := by ring
        rw [h1]
        refine le_trans (le_abs_self _) ?_
        rw [abs_mul]
        have h2 : |L / 2 - t| ≤ L / 2 := by
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        have := mul_le_mul_of_nonneg_left h2 (abs_nonneg z.im)
        linarith
      calc Real.exp (z.im * L / 2) * (|f t - h t| * Real.exp (-(t * z.im)))
          = |f t - h t| * (Real.exp (z.im * L / 2) * Real.exp (-(t * z.im))) := by ring
        _ ≤ |f t - h t| * c := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        _ = c * |f t - h t| := by ring
    · rw [hfs t ht, hhs t ht]
      simp
  have hW := Cvs.Limit.TransformStripLipschitz.memLp_stripWeight L 0
  have habs : MemLp (fun t : ℝ => |f t - h t|) 2 (volume : Measure ℝ) := (hf.sub hh).abs
  have hint : Integrable (fun t => c * (|f t - h t| * Cvs.Limit.TransformStripLipschitz.stripWeight L 0 t))
      (volume : Measure ℝ) := by
    refine Integrable.const_mul ?_ c
    have hb : ∀ t, ‖|f t - h t| * Cvs.Limit.TransformStripLipschitz.stripWeight L 0 t‖ ≤ ‖f t - h t‖ := by
      intro t
      by_cases ht : t ∈ Set.Ioc (0:ℝ) L
      · rw [Cvs.Limit.TransformStripLipschitz.stripWeight, Set.indicator_of_mem ht]
        simp
      · rw [Cvs.Limit.TransformStripLipschitz.stripWeight, Set.indicator_of_notMem ht]
        simp
    exact (hfint.sub hhint).mono (habs.aestronglyMeasurable.mul hW.aestronglyMeasurable)
      (Eventually.of_forall hb)
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hint
    (Eventually.of_forall hpt)) ?_
  rw [integral_const_mul]
  have hcs := Cvs.Upstream.CauchySchwarzLine.abs_integral_mul_le habs hW
  have hsq : (∫ x : ℝ, |f x - h x| ^ 2) = ∫ x : ℝ, (f x - h x) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun x => sq_abs _)
  rw [hsq] at hcs
  have hWL : √(∫ t : ℝ, Cvs.Limit.TransformStripLipschitz.stripWeight L 0 t ^ 2) ≤ √L := by
    refine Real.sqrt_le_sqrt (le_trans (Cvs.Limit.TransformStripLipschitz.integral_stripWeight_sq_le hL 0) ?_)
    simp
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  calc c * ∫ t : ℝ, |f t - h t| * Cvs.Limit.TransformStripLipschitz.stripWeight L 0 t
      ≤ c * (√(∫ t : ℝ, (f t - h t) ^ 2) * √L) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        refine le_trans (le_abs_self _) (le_trans hcs ?_)
        exact mul_le_mul_of_nonneg_left hWL (Real.sqrt_nonneg _)
    _ = √(∫ t : ℝ, (f t - h t) ^ 2) * √L * c := by ring

/-- **The type bound on coefficient vectors.** For even `ξ, η` on `Idx N`,
`‖ĝ_ξ(z) − ĝ_η(z)‖ ≤ L·√((ξ − η)⬝(ξ − η))·e^{|Im z| L/2}`. -/
theorem norm_ctransform_sub_le {L : ℝ} (hL : 0 < L) (N : ℕ) {ξ η : Idx N → ℝ}
    (hξ : ∀ i, ξ (negI N i) = ξ i) (hη : ∀ i, η (negI N i) = η i) (z : ℂ) :
    ‖ctransform L N ξ z - ctransform L N η z‖
      ≤ L * √((ξ - η) ⬝ᵥ (ξ - η)) * Real.exp (|z.im| * L / 2) := by
  have hsupp : ∀ (θ : Idx N → ℝ), ∀ s ∉ Set.Ioc (0:ℝ) L,
      Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) θ s = 0 := by
    intro θ s hs
    simp [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, hs]
  have h := norm_phase_mul_sub_le hL.le (Cvs.WeilForm.Archimedean.LevyChannelSumSquares.memLp_modeSum L (mode N) ξ)
    (Cvs.WeilForm.Archimedean.LevyChannelSumSquares.memLp_modeSum L (mode N) η) (hsupp ξ) (hsupp η) z
  have hdiff : (∫ t : ℝ, (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) ξ t
      - Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) η t) ^ 2) = L * ((ξ - η) ⬝ᵥ (ξ - η)) := by
    rw [← integral_modeSum_sq hL N (ξ := ξ - η) (fun i => by simp [hξ i, hη i])]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [modeSum_sub]; rfl
  rw [hdiff, Real.sqrt_mul hL.le] at h
  have hLL : √L * √((ξ - η) ⬝ᵥ (ξ - η)) * √L = L * √((ξ - η) ⬝ᵥ (ξ - η)) := by
    have := Real.mul_self_sqrt hL.le
    calc √L * √((ξ - η) ⬝ᵥ (ξ - η)) * √L = (√L * √L) * √((ξ - η) ⬝ᵥ (ξ - η)) := by ring
      _ = L * √((ξ - η) ⬝ᵥ (ξ - η)) := by rw [this]
  rw [hLL] at h
  exact h

/-! ### Closeness of the ground state carries the convergence -/

/-- **Closeness carries convergence to the ground state**: a sign of the ground state within squared
distance `ε` of even `v`, `L e^{aL/2}√ε → 0` for `a < 1/2`, and `s·ĝ_v → Ξ` on `criticalOffAxes`
with `0 < |s| ≤ S` make nonzero rescalings of the centred ground transforms converge to `Ξ` there. -/
theorem tendsto_ground_of_close_strip {L : ℕ → ℝ} (hL : ∀ n, 0 < L n) (P R N : ℕ → ℕ)
    (v : ∀ n, Idx (N n) → ℝ) (hv : ∀ n i, v n (negI (N n) i) = v n i)
    (s : ℕ → ℝ) (hs : ∀ n, s n ≠ 0) {S : ℝ} (hS : ∀ n, |s n| ≤ S) (ε : ℕ → ℝ)
    (hclose : ∀ n, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (σ • ground (P n) (R n) (L n) (hL n) (N n) - v n)
        ⬝ᵥ (σ • ground (P n) (R n) (L n) (hL n) (N n) - v n) ≤ ε n)
    (hbudget : ∀ a < 1 / 2,
      Tendsto (fun n => L n * Real.exp (a * L n / 2) * √(ε n)) atTop (𝓝 0))
    (hconv : TendstoLocallyUniformlyOn (fun n z => (s n : ℂ) * ctransform (L n) (N n) (v n) z)
      Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop criticalOffAxes) :
    ∃ c : ℕ → ℂ, (∀ n, c n ≠ 0) ∧ TendstoLocallyUniformlyOn
      (fun n z => c n * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z)
      Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop criticalOffAxes := by
  choose σ hσ hd using hclose
  have hσ0 : ∀ n, σ n ≠ 0 := fun n => by rcases hσ n with h | h <;> rw [h] <;> norm_num
  refine ⟨fun n => ((s n * σ n : ℝ) : ℂ),
    fun n => Complex.ofReal_ne_zero.mpr (mul_ne_zero (hs n) (hσ0 n)), ?_⟩
  refine Cvs.Route.JointGapStripLimit.tendstoLocallyUniformlyOn_of_sub isOpen_criticalOffAxes
    (fun A hAs hA => ?_) hconv
  obtain ⟨a, -, ha, hAa⟩ := Cvs.Route.JointGapStripLimit.exists_abs_im_le_of_isCompact hA hAs
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hlim : Tendsto (fun n => S * (L n * Real.exp (a * L n / 2) * √(ε n))) atTop (𝓝 0) := by
    simpa using (hbudget a ha).const_mul S
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn z hz
  rw [Pi.zero_apply, dist_zero_left]
  have hg := (ground_spec (P n) (R n) (hL n) (N n)).1
  have hge : ∀ i, (σ n • ground (P n) (R n) (L n) (hL n) (N n)) (negI (N n) i)
      = (σ n • ground (P n) (R n) (L n) (hL n) (N n)) i := fun i => by simp [hg i]
  have heq : ((s n * σ n : ℝ) : ℂ) * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n) (hL n) (N n) z
        - (s n : ℂ) * ctransform (L n) (N n) (v n) z
      = (s n : ℂ) * (ctransform (L n) (N n) (σ n • ground (P n) (R n) (L n) (hL n) (N n)) z
        - ctransform (L n) (N n) (v n) z) := by
    rw [ctransform_smul, cgtransform_eq]; push_cast; ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb := norm_ctransform_sub_le (hL n) (N n) hge (hv n) z
  have hexp : Real.exp (|z.im| * L n / 2) ≤ Real.exp (a * L n / 2) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_right (hAa z hz) (hL n).le
    linarith
  have hsq := Real.sqrt_le_sqrt (hd n)
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hS n)
  calc |s n| * ‖ctransform (L n) (N n) (σ n • ground (P n) (R n) (L n) (hL n) (N n)) z
        - ctransform (L n) (N n) (v n) z‖
      ≤ S * (L n * Real.exp (a * L n / 2) * √(ε n)) := by
        refine mul_le_mul (hS n) (le_trans hb ?_) (norm_nonneg _) hS0
        calc L n * √((σ n • ground (P n) (R n) (L n) (hL n) (N n) - v n)
              ⬝ᵥ (σ n • ground (P n) (R n) (L n) (hL n) (N n) - v n))
              * Real.exp (|z.im| * L n / 2)
            ≤ L n * √(ε n) * Real.exp (a * L n / 2) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hsq (hL n).le) hexp
                (Real.exp_pos _).le (mul_nonneg (hL n).le (Real.sqrt_nonneg _))
          _ = L n * Real.exp (a * L n / 2) * √(ε n) := by ring
    _ < δ := hn

/-! ### The even sector -/

/-- The even vectors on `Idx N`, with the Euclidean inner product. -/
def evenSub (N : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Idx N)) where
  carrier := {x | ∀ i, x (negI N i) = x i}
  add_mem' := fun {x y} hx hy i => by simp [hx i, hy i]
  zero_mem' := fun i => by simp
  smul_mem' := fun c x hx i => by simp [hx i]

theorem inner_evenSub {N : ℕ} (f g : evenSub N) :
    ⟪f, g⟫_ℝ = WithLp.ofLp (f : EuclideanSpace ℝ (Idx N))
      ⬝ᵥ WithLp.ofLp (g : EuclideanSpace ℝ (Idx N)) := by
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

theorem norm_sq_evenSub {N : ℕ} (f : evenSub N) :
    ‖f‖ ^ 2 = WithLp.ofLp (f : EuclideanSpace ℝ (Idx N))
      ⬝ᵥ WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) := by
  rw [← real_inner_self_eq_norm_sq, inner_evenSub]

/-- A matrix commuting with the involution maps even vectors to even vectors. -/
theorem mulVec_even {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} {neg : ι → ι}
    (hinv : Function.Involutive neg) (hA : ∀ i j, A (neg i) (neg j) = A i j) {v : ι → ℝ}
    (hv : ∀ i, v (neg i) = v i) (i : ι) : (A *ᵥ v) (neg i) = (A *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (Function.Involutive.toPerm neg hinv)]
  simp only [Function.Involutive.coe_toPerm, hA, hv]

/-- Against an even vector, a vector pairs as its even part does. -/
theorem evenPart_dotProduct {ι : Type*} [Fintype ι] {neg : ι → ι}
    (hinv : Function.Involutive neg) (k : ι → ℝ) {f : ι → ℝ} (hf : ∀ i, f (neg i) = f i) :
    Cvs.Finite.TruncationQuadraticForm.evenPart neg k ⬝ᵥ f = k ⬝ᵥ f := by
  classical
  have h0 := Cvs.Finite.TruncationQuadraticForm.dotProduct_mulVec_eq_zero (A := (1 : Matrix ι ι ℝ)) hinv
    (fun i j => by simp [Matrix.one_apply, hinv.injective.eq_iff]) hf
    (Cvs.Finite.TruncationQuadraticForm.oddPart_odd hinv k)
  rw [Matrix.one_mulVec] at h0
  conv_rhs => rw [← Cvs.Finite.TruncationQuadraticForm.evenPart_add_oddPart neg k]
  rw [add_dotProduct, dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.oddPart neg k), h0, add_zero]

/-- The CvS matrix on the even sector. -/
def Meven (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) : evenSub N →ₗ[ℝ] evenSub N :=
  (Matrix.toEuclideanLin (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N))).restrict fun _ hv i =>
    mulVec_even (negI_involutive N)
      (Cvs.Finite.TruncationQuadraticForm.M_neg_neg hL P R (mode_injective N) (mode_negI N)) hv i

theorem ofLp_Meven (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) (f : evenSub N) :
    WithLp.ofLp ((Meven P R hL N f : evenSub N) : EuclideanSpace ℝ (Idx N))
      = Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) :=
  rfl

theorem isSymmetric_Meven (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (Meven P R hL N).IsSymmetric :=
  LinearMap.IsSymmetric.restrict_invariant
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.IsHermitian.ext fun i j => by
      simp [Cvs.Finite.TruncationQuadraticForm.M_symm hL P R (mode_injective N) j i])) _

/-! ### The joint gap -/

/-- **The joint gap** at scale `L` for the approximant `v`: a floor `μ > λ₁` of the even form on even
vectors orthogonal to some `k̃`, with `K(v⬝Mv − λ₁) ≤ μ − λ₁`, `λ₁` the ground level. -/
def JointGap (P R : ℕ) (L : ℝ) (N : ℕ) (K : ℝ) (v : Idx N → ℝ) : Prop :=
  ∃ hL : 0 < L, ∃ (μ : ℝ) (kt : Idx N → ℝ), groundLam P R L hL N < μ ∧
    (∀ f : Idx N → ℝ, (∀ i, f (negI N i) = f i) → kt ⬝ᵥ f = 0 →
      μ * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ f)) ∧
    K * (v ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ v) - groundLam P R L hL N)
      ≤ μ - groundLam P R L hL N

/-- **The joint gap puts a sign of the ground state within squared distance `2/K` of the
approximant.** -/
theorem exists_sign_close_of_jointGap {P R N : ℕ} {L K : ℝ} (hL : 0 < L) (hK : 0 < K)
    {v : Idx N → ℝ} (hve : ∀ i, v (negI N i) = v i) (hv1 : v ⬝ᵥ v = 1)
    (hgap : JointGap P R L N K v) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (σ • ground P R L hL N - v) ⬝ᵥ (σ • ground P R L hL N - v) ≤ 2 / K := by
  obtain ⟨_, μ, kt, hlt, hfloor, hj⟩ := hgap
  obtain ⟨hge, hg1, -, hgeig, -⟩ := ground_spec P R hL N
  have hunit : ∀ f : evenSub N, WithLp.ofLp (f : EuclideanSpace ℝ (Idx N))
      ⬝ᵥ WithLp.ofLp (f : EuclideanSpace ℝ (Idx N)) = 1 → ‖f‖ = 1 := by
    intro f hf
    have h := norm_sq_evenSub f
    rw [hf] at h
    exact (pow_left_inj₀ (norm_nonneg f) zero_le_one two_ne_zero).mp (by rw [h, one_pow])
  let θ' : evenSub N := ⟨WithLp.toLp 2 (ground P R L hL N), hge⟩
  let v' : evenSub N := ⟨WithLp.toLp 2 v, hve⟩
  let k' : evenSub N := ⟨WithLp.toLp 2 (Cvs.Finite.TruncationQuadraticForm.evenPart (negI N) kt),
    Cvs.Finite.TruncationQuadraticForm.evenPart_even (negI_involutive N) kt⟩
  have hθeig : Meven P R hL N θ' = groundLam P R L hL N • θ' := by
    refine Subtype.ext (WithLp.ofLp_injective 2 ?_)
    rw [ofLp_Meven]
    exact hgeig
  have hperp : ∀ f : evenSub N, ⟪k', f⟫_ℝ = 0 →
      μ * ‖f‖ ^ 2 ≤ ⟪Meven P R hL N f, f⟫_ℝ := by
    intro f hf
    rw [inner_evenSub] at hf
    rw [norm_sq_evenSub, inner_evenSub, ofLp_Meven, dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ _)]
    refine hfloor _ f.2 ?_
    rw [← evenPart_dotProduct (negI_involutive N) kt f.2]
    exact hf
  have hjoint : K * (⟪Meven P R hL N v', v'⟫_ℝ - groundLam P R L hL N)
      ≤ μ - groundLam P R L hL N := by
    rw [inner_evenSub, ofLp_Meven, dotProduct_comm (Cvs.Finite.TruncationQuadraticForm.M P R L (mode N) *ᵥ _)]
    exact hj
  obtain ⟨σ, hσ, hd⟩ := Cvs.Route.JointGapStripLimit.exists_sign_norm_sub_sq_le
    (isSymmetric_Meven P R hL N) (hunit θ' hg1) hθeig hlt hperp (hunit v' hv1) hK hjoint
  refine ⟨σ, hσ, ?_⟩
  rw [norm_sq_evenSub] at hd
  simpa [θ', v'] using hd

/-! ### The joint gap gives RH -/

/-- **The joint gap carries convergence to the ground state** along scales `x n → ∞`: the gap at
`K = √x log x` for unit even `v` and `s·ĝ_v → Ξ` on `criticalOffAxes` with `0 < |s| ≤ S` make
nonzero rescalings of the centred ground transforms converge to `Ξ` there. -/
theorem tendsto_ground_of_jointGap (x : ℕ → ℝ) (hx1 : ∀ n, 1 < x n)
    (hx : Tendsto x atTop atTop) (P R N : ℕ → ℕ) (v : ∀ n, Idx (N n) → ℝ)
    (hve : ∀ n i, v n (negI (N n) i) = v n i) (hv1 : ∀ n, v n ⬝ᵥ v n = 1)
    (s : ℕ → ℝ) (hs : ∀ n, s n ≠ 0) {S : ℝ} (hS : ∀ n, |s n| ≤ S)
    (hgap : ∀ n, JointGap (P n) (R n) (Real.log (x n)) (N n) (√(x n) * Real.log (x n)) (v n))
    (hconv : TendstoLocallyUniformlyOn
      (fun n z => (s n : ℂ) * ctransform (Real.log (x n)) (N n) (v n) z)
      Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop criticalOffAxes) :
    ∃ c : ℕ → ℂ, (∀ n, c n ≠ 0) ∧ TendstoLocallyUniformlyOn
      (fun n z => c n * Cvs.Finite.RecentredTransform.cgtransform (P n) (R n)
        (Real.log_pos (hx1 n)) (N n) z)
      Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop criticalOffAxes := by
  have hL : ∀ n, 0 < Real.log (x n) := fun n => Real.log_pos (hx1 n)
  have hK : ∀ n, √(x n) * Real.log (x n) = Real.log (x n) * Real.exp (Real.log (x n) / 2) := by
    intro n
    rw [Real.exp_half, Real.exp_log (by linarith [hx1 n]), mul_comm]
  refine tendsto_ground_of_close_strip hL P R N v hve s hs hS
    (fun n => 2 / (√(x n) * Real.log (x n))) (fun n => ?_) (fun a ha => ?_) hconv
  · exact exists_sign_close_of_jointGap (hL n)
      (mul_pos (Real.sqrt_pos.mpr (by linarith [hx1 n])) (hL n)) (hve n) (hv1 n) (hgap n)
  · refine (Cvs.Route.JointGapStripLimit.tendsto_scale (Real.tendsto_log_atTop.comp hx) ha).congr
      fun n => ?_
    simp only [Function.comp_apply, hK]

/-- **Strip approximability** of unit even vectors `v x`: a bounded nonzero rescaling of their centred
transforms converges to `Ξ` locally uniformly on `criticalOffAxes` as `x → ∞`. -/
def StripApproximable (N : ℝ → ℕ) (v : ∀ x, Idx (N x) → ℝ) : Prop :=
  (∀ x i, v x (negI (N x) i) = v x i) ∧ (∀ x, v x ⬝ᵥ v x = 1) ∧
    ∃ (s : ℝ → ℝ) (S : ℝ), (∀ x, s x ≠ 0) ∧ (∀ x, |s x| ≤ S) ∧
      TendstoLocallyUniformlyOn (fun x z => (s x : ℂ) * ctransform (Real.log x) (N x) (v x) z)
        Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop criticalOffAxes

/-- **The ground route on the joint gap at infinitely many scales.** Strip-approximable `v`, and the
joint gap at `K = √x log x` against `v x` for arbitrarily large `x`, give RH. -/
theorem riemannHypothesis_of_frequently_jointGap (P R N : ℝ → ℕ) (v : ∀ x, Idx (N x) → ℝ)
    (hA : StripApproximable N v)
    (hgap : ∃ᶠ x in atTop,
      JointGap (P x) (R x) (Real.log x) (N x) (√x * Real.log x) (v x)) :
    RiemannHypothesis := by
  obtain ⟨hve, hv1, s, S, hs, hS, hconvA⟩ := hA
  have hex : ∀ n : ℕ, ∃ x : ℝ, max (n : ℝ) 2 ≤ x ∧
      JointGap (P x) (R x) (Real.log x) (N x) (√x * Real.log x) (v x) :=
    fun n => frequently_atTop.mp hgap (max n 2)
  choose y hy hgy using hex
  have hy1 : ∀ n, 1 < y n := fun n => by linarith [le_max_right (n : ℝ) 2, hy n]
  have hyt : Tendsto y atTop atTop :=
    tendsto_atTop_mono (fun n => le_trans (le_max_left _ _) (hy n)) tendsto_natCast_atTop_atTop
  have hconv : TendstoLocallyUniformlyOn
      (fun n z => (s (y n) : ℂ) * ctransform (Real.log (y n)) (N (y n)) (v (y n)) z)
      Cvs.Limit.ZeroFreeApproximantsRH.Xi atTop criticalOffAxes := by
    intro u hu z hz
    obtain ⟨t, ht, hev⟩ := hconvA u hu z hz
    exact ⟨t, ht, hyt.eventually hev⟩
  obtain ⟨c, hc, hcg⟩ := tendsto_ground_of_jointGap y hy1 hyt (fun n => P (y n))
    (fun n => R (y n)) (fun n => N (y n)) (fun n => v (y n)) (fun n => hve (y n))
    (fun n => hv1 (y n)) (fun n => s (y n)) (fun n => hs (y n)) (fun n => hS (y n)) hgy hconv
  exact Cvs.Limit.CriticalStripOffAxes.riemannHypothesis_of_ground_centred_strip
    (fun n => Real.log_pos (hy1 n)) (fun n => P (y n)) (fun n => R (y n)) (fun n => N (y n))
    c hc hcg

end Cvs.Route.GroundRouteJointGap
