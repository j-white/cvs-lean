import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.ModePairingTable
import Cvs.Finite.RecentredTransform
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.Finite.WindowCosineBessel
import Cvs.Finite.WindowedModeSumDomain
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.GroundRouteJointGap
import Cvs.Upstream.FourierLaplace
import Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition
import Cvs.WeilForm.Archimedean.LevyChannelSumSquares
import Cvs.WeilForm.CentredWindowTranslate
import Cvs.WeilForm.EImageRadical
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.Xi.EImageMellin
import Cvs.Xi.EImageWindowPoisson
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Connes' vector at real `x`, and the transform of a truncated cosine series

`k_x = logScale(window(1/x) G)(· − log x)`, `G` the spine profile of `{1}` at `c = 2πx`; its cosine
coefficients on `(0, log x]`, truncated to `Idx N` and normalised, give `connesVec`. The energy of
`k_x` is at most `H_⌊x⌋ ∫_{[0,1]} G²`, Bessel holds for square-integrable `g`, and a truncated
cosine series of `g` has transform at most `√L ‖g‖_{L²(0,L)} e^{|Im z| L/2}`.
-/

noncomputable section

open Real Set Filter MeasureTheory Matrix

namespace Cvs.Approximant.ConnesVectorRealScale
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI coeff coeff_even)
open Cvs.L2a.TailLogScaleTest (logScale)

/-! ### Linearity of the cosine coefficients -/

/-- The cosine coefficients are homogeneous. -/
theorem coef_smul (L c : ℝ) (g : ℝ → ℝ) :
    Cvs.Finite.WindowCosineBessel.coef L (fun t => c * g t) = fun n => c * Cvs.Finite.WindowCosineBessel.coef L g n := by
  funext n
  unfold Cvs.Finite.WindowCosineBessel.coef
  split_ifs
  · rw [intervalIntegral.integral_const_mul]; ring
  · simp_rw [mul_assoc c]
    rw [intervalIntegral.integral_const_mul]; ring

/-- The cosine coefficients are additive on integrable functions. -/
theorem coef_add {L : ℝ} {g h : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 L)
    (hh : IntervalIntegrable h volume 0 L) :
    Cvs.Finite.WindowCosineBessel.coef L (fun t => g t + h t) = fun n => Cvs.Finite.WindowCosineBessel.coef L g n + Cvs.Finite.WindowCosineBessel.coef L h n := by
  funext n
  unfold Cvs.Finite.WindowCosineBessel.coef
  split_ifs
  · rw [intervalIntegral.integral_add hg hh]; ring
  · have hc : ContinuousOn (fun t => Real.cos (2 * π * n / L * t)) (uIcc 0 L) :=
      (by fun_prop : Continuous fun t => Real.cos (2 * π * n / L * t)).continuousOn
    simp_rw [add_mul]
    rw [intervalIntegral.integral_add (hg.mul_continuousOn hc) (hh.mul_continuousOn hc)]; ring

/-- The cosine coefficients are subtractive on integrable functions. -/
theorem coef_sub {L : ℝ} {g h : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 L)
    (hh : IntervalIntegrable h volume 0 L) :
    Cvs.Finite.WindowCosineBessel.coef L (fun t => g t - h t) = fun n => Cvs.Finite.WindowCosineBessel.coef L g n - Cvs.Finite.WindowCosineBessel.coef L h n := by
  have e : (fun t => g t - h t) = fun t => g t + (-1) * h t := by funext t; ring
  have hh' : IntervalIntegrable (fun t => (-1) * h t) volume 0 L := hh.const_mul (-1)
  rw [e, coef_add hg hh', coef_smul]
  funext n; ring

/-- The even coefficient vector is subtractive in the frequency coefficients. -/
theorem coeff_sub (N : ℕ) (s : Finset ℕ) (a b : ℕ → ℝ) :
    coeff N s (fun n => a n - b n) = coeff N s a - coeff N s b := by
  funext i
  rcases i with _ | ⟨k, _⟩ <;> simp only [coeff, Pi.sub_apply] <;> split_ifs <;> ring

/-! ### Bessel without continuity -/

/-- A function square integrable on `(0, L]` is interval integrable there, and so is its square. -/
theorem intervalIntegrable_of_memLp {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) :
    IntervalIntegrable g volume 0 L ∧ IntervalIntegrable (fun x => g x ^ 2) volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL,
    intervalIntegrable_iff_integrableOn_Ioc_of_le hL]
  exact ⟨hg.integrable one_le_two, hg.integrable_sq⟩

/-- **Bessel's identity on the window** for `g` square integrable on `(0, L]`. -/
theorem integral_sub_modeSum_sq {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) (s : Finset ℕ) :
    (∫ x in (0:ℝ)..L, (g x - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s (Cvs.Finite.WindowCosineBessel.coef L g) x) ^ 2)
      = (∫ x in (0:ℝ)..L, g x ^ 2)
        - L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * Cvs.Finite.WindowCosineBessel.coef L g n ^ 2 := by
  classical
  obtain ⟨hg1, hg2⟩ := intervalIntegrable_of_memLp hL.le hg
  set a : ℕ → ℝ := Cvs.Finite.WindowCosineBessel.coef L g with ha
  set S : ℝ → ℝ := Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s a with hS
  have hSc : Continuous S := Cvs.Finite.WindowedModeSumDomain.continuous_modeSum L s a
  have hexp : ∀ x : ℝ, (g x - S x) ^ 2 = g x ^ 2 - 2 * (g x * S x) + S x ^ 2 := by
    intro x; ring
  have hi2 : IntervalIntegrable (fun x : ℝ => 2 * (g x * S x)) volume 0 L :=
    (hg1.mul_continuousOn hSc.continuousOn).const_mul 2
  have hi3 : IntervalIntegrable (fun x : ℝ => S x ^ 2) volume 0 L :=
    (hSc.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun x _ => hexp x),
    intervalIntegral.integral_add (hg2.sub hi2) hi3,
    intervalIntegral.integral_sub hg2 hi2, intervalIntegral.integral_const_mul,
    Cvs.Finite.ModePairingTable.integral_modeSum_sq hL s a]
  have hcross : (∫ x in (0:ℝ)..L, g x * S x)
      = L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * a n ^ 2 := by
    have hpt : ∀ x : ℝ, g x * S x
        = ∑ n ∈ s, a n * (g x * Real.cos (2 * π * n / L * x)) := by
      intro x
      rw [hS]
      show g x * (∑ n ∈ s, a n * Real.cos (2 * π * n / L * x)) = _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    have hint : ∀ n : ℕ, IntervalIntegrable
        (fun x : ℝ => a n * (g x * Real.cos (2 * π * n / L * x))) volume 0 L := fun n =>
      (hg1.mul_continuousOn
        (by fun_prop : Continuous fun x => Real.cos (2 * π * n / L * x)).continuousOn).const_mul _
    rw [intervalIntegral.integral_congr (fun x _ => hpt x),
      intervalIntegral.integral_finsetSum (fun n _ => hint n), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul, ha, Cvs.Finite.WindowCosineBessel.integral_mul_cos hL g n, ← ha]
    ring
  rw [hcross]
  ring

/-- **Bessel's inequality on the window** for `g` square integrable on `(0, L]`. -/
theorem bessel {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (Ioc 0 L)))
    (s : Finset ℕ) :
    L / 2 * ∑ n ∈ s, (if n = 0 then 2 else 1) * Cvs.Finite.WindowCosineBessel.coef L g n ^ 2
      ≤ ∫ x in (0:ℝ)..L, g x ^ 2 := by
  have hnn : 0 ≤ ∫ x in (0:ℝ)..L,
      (g x - Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L s (Cvs.Finite.WindowCosineBessel.coef L g) x) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun x _ => sq_nonneg _)
  rw [integral_sub_modeSum_sq hL hg s] at hnn
  linarith

/-- **A truncated cosine series keeps no more energy than its target.** -/
theorem integral_modeSum_coeff_sq_le {L : ℝ} (hL : 0 < L) (N : ℕ) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) :
    ∫ t : ℝ, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N)
        (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L g)) t ^ 2
      ≤ ∫ t in (0:ℝ)..L, g t ^ 2 := by
  rw [← Cvs.Finite.SymmetricModeSet.windowMode_eq_modeSum L N _ _ subset_rfl]
  have hfun : (fun t : ℝ => Cvs.Finite.WindowedModeSumDomain.windowMode L (Finset.range (N + 1))
      (Cvs.Finite.WindowCosineBessel.coef L g) t ^ 2)
      = Set.indicator (Ioc (0:ℝ) L) (fun t => Cvs.WeilForm.Archimedean.ArchDirichletEnergyPosition.modeSum L
          (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L g) t ^ 2) := by
    funext t
    rw [Cvs.Finite.WindowedModeSumDomain.windowMode]
    by_cases ht : t ∈ Ioc (0:ℝ) L
    · rw [indicator_of_mem ht, indicator_of_mem ht]
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]; norm_num
  rw [hfun, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hL.le,
    Cvs.Finite.ModePairingTable.integral_modeSum_sq hL]
  exact bessel hL hg _

/-! ### The transform of a truncated cosine series -/

/-- **The transform of truncated cosine series has type `L/2`**: for `g, h` square integrable on
`(0, L]`, `‖ĝ_N(z) − ĥ_N(z)‖ ≤ √L ‖g − h‖_{L²(0,L)} e^{|Im z| L/2}`. -/
theorem norm_ctransform_coef_sub_le {L : ℝ} (hL : 0 < L) (N : ℕ) {g h : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) (hh : MemLp h 2 (volume.restrict (Ioc 0 L)))
    (z : ℂ) :
    ‖Cvs.Route.GroundRouteJointGap.ctransform L N (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L g)) z
        - Cvs.Route.GroundRouteJointGap.ctransform L N (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L h)) z‖
      ≤ √L * √(∫ t in (0:ℝ)..L, (g t - h t) ^ 2) * Real.exp (|z.im| * L / 2) := by
  set ξ := coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L g)
  set η := coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L h)
  have hsupp : ∀ (θ : Idx N → ℝ), ∀ s ∉ Ioc (0:ℝ) L,
      Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) θ s = 0 := by
    intro θ s hs
    simp [Cvs.Finite.TruncationZeroFreeOffAxes.modeSum, hs]
  have hb := Cvs.Route.GroundRouteJointGap.norm_phase_mul_sub_le hL.le
    (Cvs.WeilForm.Archimedean.LevyChannelSumSquares.memLp_modeSum L (mode N) ξ)
    (Cvs.WeilForm.Archimedean.LevyChannelSumSquares.memLp_modeSum L (mode N) η) (hsupp ξ) (hsupp η) z
  have hd : ξ - η = coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L fun t => g t - h t) := by
    obtain ⟨hg1, -⟩ := intervalIntegrable_of_memLp hL.le hg
    obtain ⟨hh1, -⟩ := intervalIntegrable_of_memLp hL.le hh
    rw [coef_sub hg1 hh1, coeff_sub]
  have hE : (∫ t : ℝ, (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) ξ t
      - Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) η t) ^ 2)
      ≤ ∫ t in (0:ℝ)..L, (g t - h t) ^ 2 := by
    have e : (fun t => (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) ξ t
        - Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) η t) ^ 2)
        = fun t => Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) (ξ - η) t ^ 2 := by
      funext t; rw [Cvs.Route.GroundRouteJointGap.modeSum_sub]; rfl
    rw [e, hd]
    exact integral_modeSum_coeff_sq_le hL N (g := fun t => g t - h t) (hg.sub hh)
  calc _ ≤ √(∫ t : ℝ, (Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) ξ t
          - Cvs.Finite.TruncationZeroFreeOffAxes.modeSum L (mode N) η t) ^ 2) * √L
          * Real.exp (|z.im| * L / 2) := hb
    _ ≤ √(∫ t in (0:ℝ)..L, (g t - h t) ^ 2) * √L * Real.exp (|z.im| * L / 2) := by
        gcongr
    _ = √L * √(∫ t in (0:ℝ)..L, (g t - h t) ^ 2) * Real.exp (|z.im| * L / 2) := by ring

/-- The transform of the zero vector vanishes. -/
theorem ctransform_zero (L : ℝ) (N : ℕ) (z : ℂ) : Cvs.Route.GroundRouteJointGap.ctransform L N 0 z = 0 := by
  have h := Cvs.Route.GroundRouteJointGap.ctransform_smul L N 0 0 z
  rw [zero_smul] at h
  rw [h]; simp

/-- **The transform of a truncated cosine series**: for `g` square integrable on `(0, L]`,
`‖ĝ_N(z)‖ ≤ √L ‖g‖_{L²(0,L)} e^{|Im z| L/2}`. -/
theorem norm_ctransform_coef_le {L : ℝ} (hL : 0 < L) (N : ℕ) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 L))) (z : ℂ) :
    ‖Cvs.Route.GroundRouteJointGap.ctransform L N (coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L g)) z‖
      ≤ √L * √(∫ t in (0:ℝ)..L, g t ^ 2) * Real.exp (|z.im| * L / 2) := by
  have h := norm_ctransform_coef_sub_le hL N hg (h := fun _ => 0) MemLp.zero' z
  have h0 : coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef L fun _ => 0) = 0 := by
    funext i
    rcases i with _ | ⟨k, _⟩ <;> simp [coeff, Cvs.Finite.WindowCosineBessel.coef]
  rw [h0, ctransform_zero, sub_zero] at h
  simpa using h

/-! ### The energy of a log-scaled window -/

/-- **The window energy in the log variable**: any translate of `logScale (window (1/x) F)` has
energy at most `H_⌊x⌋ ∫_{[0,1]} F²`. -/
theorem integral_logScale_window_sq_le {x : ℝ} (hx : 0 < x) {F : ℝ → ℝ}
    (hF : IntegrableOn (fun u => F u ^ 2) (Icc 0 1)) (L : ℝ) :
    ∫ s, logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x) F) (s - L) ^ 2
      ≤ (harmonic ⌊x⌋₊ : ℝ) * ∫ u in Icc (0 : ℝ) 1, F u ^ 2 := by
  set W := Cvs.Xi.EImageWindowPoisson.window (1 / x) F with hW
  have ha : 0 < 1 / x := one_div_pos.mpr hx
  rw [integral_sub_right_eq_self (fun s => logScale W s ^ 2) L]
  have h1 : ∫ s, logScale W s ^ 2 = ∫ θ in Ioi (0:ℝ), W θ ^ 2 := by
    have h := Cvs.WeilForm.ThetaFormWindowIdentification.selfConvolution_logScale_log W (k := 1) one_pos
    simp only [Cvs.Zeta.Explicit.Weil.selfConvolution, Real.log_one, add_zero, Real.sqrt_one,
      one_mul] at h
    simpa [sq] using h
  have h2 : ∫ θ in Ioi (0:ℝ), W θ ^ 2 = ∫ θ, W θ ^ 2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun θ hθ => ?_
    have hn : θ ∉ Icc (1 / x) 1 := fun h => hθ (ha.trans_le h.1)
    rw [hW, Cvs.Xi.EImageWindowPoisson.window_of_notMem F hn]; ring
  rw [h1, h2]
  have h := Cvs.Xi.EImageWindowPoisson.integral_window_sq_le ha hF
  rwa [one_div_one_div] at h

/-- The window image is bounded by any bound of `G` on `(0, 1]`. -/
theorem abs_window_le {a : ℝ} (ha : 0 < a) {G : ℝ → ℝ} {M : ℝ}
    (hM : ∀ u ∈ Ioc (0:ℝ) 1, |G u| ≤ M) (θ : ℝ) : |Cvs.Xi.EImageWindowPoisson.window a G θ| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 ⟨one_pos, le_rfl⟩)
  unfold Cvs.Xi.EImageWindowPoisson.window
  by_cases h : θ ∈ Icc a 1
  · rw [indicator_of_mem h]
    have hθ : 0 < θ := ha.trans_le h.1
    unfold Cvs.Xi.EImageWindowPoisson.eimage
    have hs : |∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)| ≤ ⌊θ / a⌋₊ * M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_card_nsmul (Finset.Icc 1 ⌊θ / a⌋₊) (fun n : ℕ => |G (n * a / θ)|) M
        (fun n hn => hM _ (Cvs.Xi.EImageWindowPoisson.mem_Ioc_of_mem ha hn).2)
      simpa using this
    have hfl : (⌊θ / a⌋₊ : ℝ) ≤ θ / a := Nat.floor_le (by positivity)
    rw [abs_mul, abs_of_pos (by positivity : 0 < a / θ)]
    calc a / θ * |∑ n ∈ Finset.Icc 1 ⌊θ / a⌋₊, G (n * a / θ)|
        ≤ a / θ * (⌊θ / a⌋₊ * M) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ a / θ * (θ / a * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfl hM0) (by positivity)
      _ = M := by field_simp
  · rw [indicator_of_notMem h, abs_zero]; exact hM0

/-- The spine profile is continuous on `[−1, 1]`. -/
theorem continuousOn_spineG (c : ℝ) {S : Finset ℕ} (a : S → ℝ) :
    ContinuousOn (Cvs.Approximant.DeepIndexSpineSpan.spineG c a) (Icc (-1) 1) := by
  have hr : ∀ k, ContinuousOn (Cvs.Prolate.EvenRungsByIndex.rung c k) (Icc (-1) 1) := fun k =>
    (Cvs.Approximant.DeepIndexSpineSpan.continuousOn_rawRung c (Cvs.Prolate.EvenRungsByIndex.lev c k)).div_const _
  unfold Cvs.Approximant.DeepIndexSpineSpan.spineG
  exact continuousOn_finsetSum _ fun j _ =>
    continuousOn_const.mul ((hr _).sub (continuousOn_const.mul (hr 0)))

/-! ### Connes' vector at real `x` -/

/-- Connes' test at real `x`: the window of the spine profile of `{1}` at `c = 2πx`, log-scaled
and moved into `(0, log x]`. -/
def connesK (x : ℝ) : ℝ → ℝ := fun s =>
  logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1))
    (s - Real.log x)

/-- The cosine coefficients of Connes' test on `(0, log x]`, as an even vector on `Idx N`. -/
def connesCoef (x : ℝ) (N : ℕ) : Idx N → ℝ :=
  coeff N (Finset.range (N + 1)) (Cvs.Finite.WindowCosineBessel.coef (Real.log x) (connesK x))

/-- Connes' vector: the normalised coefficient vector, or the zero mode when it vanishes. -/
def connesVec (N : ℝ → ℕ) (x : ℝ) : Idx (N x) → ℝ :=
  let ξ := connesCoef x (N x)
  if ξ ⬝ᵥ ξ = 0 then Pi.single none 1 else (√(ξ ⬝ᵥ ξ))⁻¹ • ξ

/-- **At integer `x`, Connes' test is the spine test** `k_G` of `{1}` with unit coefficient. -/
theorem connesK_natCast (n : ℕ) :
    connesK n = Cvs.Approximant.SpineSubspace.kG n (S := {1}) fun _ => 1 := by
  funext s
  unfold connesK Cvs.Approximant.SpineSubspace.kG
  rw [div_mul_eq_div_div, div_self (by positivity : (2 * π : ℝ) ≠ 0)]

/-- Connes' test vanishes off `[0, log x]`. -/
theorem connesK_supp {x : ℝ} (hx : 0 < x) : ∀ s ∉ Icc (0:ℝ) (Real.log x), connesK x s = 0 := by
  intro s hs
  unfold connesK logScale
  rw [Cvs.Xi.EImageWindowPoisson.window_of_notMem _ ?_, zero_mul]
  rintro ⟨h1, h2⟩
  apply hs
  have he : Real.exp (s - Real.log x) = Real.exp s / x := by rw [Real.exp_sub, Real.exp_log hx]
  rw [he] at h1 h2
  refine ⟨?_, ?_⟩
  · have h : 1 ≤ Real.exp s := by rwa [div_le_div_iff_of_pos_right hx] at h1
    exact Real.one_le_exp_iff.mp h
  · rw [div_le_one hx] at h2
    exact (Real.le_log_iff_exp_le hx).mpr h2

/-- Connes' test vanishes a.e. off `(0, log x]`. -/
theorem connesK_ae_supp {x : ℝ} (hx : 0 < x) :
    ∀ᵐ s ∂volume, s ∉ Ioc (0:ℝ) (Real.log x) → connesK x s = 0 := by
  filter_upwards [(Set.countable_singleton (0:ℝ)).ae_notMem volume] with s hs0 hs
  refine connesK_supp hx s fun h => hs ⟨lt_of_le_of_ne h.1 (fun e => hs0 (by simp [← e])), h.2⟩

/-- Connes' test is square integrable. -/
theorem connesK_memLp {x : ℝ} (hx : 0 < x) : MemLp (connesK x) 2 volume := by
  set G := Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) fun _ => 1 with hG
  have hGc : ContinuousOn G (Icc 0 1) :=
    (continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hGc
  have ha : 0 < 1 / x := one_div_pos.mpr hx
  have hmeas : Measurable (Cvs.Xi.EImageWindowPoisson.window (1 / x) G) :=
    (Cvs.Xi.EImageMellin.measurable_eimage_of_continuousOn ha hGc).indicator measurableSet_Icc
  have hb : ∀ θ, |Cvs.Xi.EImageWindowPoisson.window (1 / x) G θ| ≤ M :=
    abs_window_le ha fun u hu => by simpa using hM u (Ioc_subset_Icc_self hu)
  have hL := (Cvs.WeilForm.EImageRadical.integrable_logScale_of_support hmeas hb ha
    (fun θ hθ => Cvs.Xi.EImageWindowPoisson.window_of_notMem G hθ)).2
  have e : connesK x = fun s => logScale (Cvs.Xi.EImageWindowPoisson.window (1 / x) G) (s + -Real.log x) := by
    funext s; simp only [connesK, hG, sub_eq_add_neg]
  rw [e]
  exact Cvs.WeilForm.CentredWindowTranslate.memLp_translate (-Real.log x) hL

/-- **The energy of Connes' test** is at most `H_⌊x⌋ ∫_{[0,1]} G²`. -/
theorem integral_connesK_sq_le {x : ℝ} (hx : 0 < x) :
    ∫ s, connesK x s ^ 2 ≤ (harmonic ⌊x⌋₊ : ℝ)
      * ∫ u in Icc (0 : ℝ) 1, Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) (S := {1}) (fun _ => 1) u ^ 2 :=
  integral_logScale_window_sq_le hx
    (((continuousOn_spineG _ _).mono (Icc_subset_Icc (by norm_num) le_rfl)).pow 2).integrableOn_Icc
    _

/-- Connes' coefficient vector is even. -/
theorem connesCoef_even (x : ℝ) (N : ℕ) (i : Idx N) :
    connesCoef x N (negI N i) = connesCoef x N i :=
  coeff_even N _ _ i

/-- Connes' vector is even. -/
theorem connesVec_even (N : ℝ → ℕ) (x : ℝ) (i : Idx (N x)) :
    connesVec N x (negI (N x) i) = connesVec N x i := by
  unfold connesVec
  split_ifs
  · rcases i with _ | ⟨k, b⟩ <;> simp [negI]
  · simp only [Pi.smul_apply, connesCoef_even]

/-- Connes' vector is a unit vector. -/
theorem connesVec_dotProduct_self (N : ℝ → ℕ) (x : ℝ) :
    connesVec N x ⬝ᵥ connesVec N x = 1 := by
  unfold connesVec
  dsimp only
  split_ifs with h
  · simp
  · set ξ := connesCoef x (N x)
    have hq : 0 ≤ ξ ⬝ᵥ ξ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← mul_inv,
      Real.mul_self_sqrt hq, inv_mul_cancel₀ h]

/-- **The transform of Connes' coefficient vector** at `L = log x`, `x > 1`:
`‖ĝ(z)‖ ≤ √L ‖k_x‖_{L²(0,L)} e^{|Im z| L/2}`. -/
theorem norm_ctransform_connesCoef_le {x : ℝ} (hx : 1 < x) (N : ℕ) (z : ℂ) :
    ‖Cvs.Route.GroundRouteJointGap.ctransform (Real.log x) N (connesCoef x N) z‖
      ≤ √(Real.log x) * √(∫ t in (0:ℝ)..Real.log x, connesK x t ^ 2)
        * Real.exp (|z.im| * Real.log x / 2) :=
  norm_ctransform_coef_le (Real.log_pos hx) N ((connesK_memLp (by linarith)).restrict _) z

end Cvs.Approximant.ConnesVectorRealScale
