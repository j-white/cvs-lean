import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.RungOrthogonalityAtInfinity
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Route.Visibility.ExteriorTransformPointBound
import Cvs.Route.Visibility.ProjectionShareSawtooth
import Cvs.Route.Visibility.ReflectedRemainderMellin
import Cvs.Route.Visibility.SawtoothPlancherelBounds
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The exterior image in sawtooth–Poisson form, and its weighted norm

For `G` even and `C¹` with `∫₀¹ G = 0`, `c = 2π/a` and `ρ_G(ξ) = ψ_G(ξ) − (G(1) + G(−1))sin(cξ)/(cξ)`:
`S_{G'}(nθ/a)/(πn) = −(θ/a)ρ_G(nθ)` by parts, so `SawtoothPlancherelBounds`'s mode sum and Cvs.Route.Visibility.ReflectedRemainderMellin give `r_G(θ) = Σ_{n≥1} ρ_G(nθ)`.
Minkowski over the modes then bounds `Ext_G(σ)` for `σ < 1` by `a(|G(1)| + |G(0)|)/(2√(2(1 − σ)))
+ ζ(3/2)‖ξρ_G‖_{L²(1,∞)}`, squared.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.RungOrthogonalityAtInfinity (ampl)
open Cvs.Route.Visibility.ProjectionShareSawtooth (saw reflRem)
open Cvs.Route.Visibility.ReflectedRemainderMellin (sawT)
open Cvs.Route.Visibility.SawtoothPlancherelBounds (sawC sinT zeta32)

namespace Cvs.Route.Visibility.ExteriorImageSawtoothPoisson
open Cvs.ZeroCounting

/-- The Poisson remainder `ρ_G(ξ) = ψ_G(ξ) − (G(1) + G(−1))sin(cξ)/(cξ)`. -/
def rhoG (c : ℝ) (G : ℝ → ℝ) (ξ : ℝ) : ℝ := psi c G ξ - ampl G * Real.sin (c * ξ) / (c * ξ)

variable {G G₁ : ℝ → ℝ}

/-- **The even fold of the transform**: `ψ_G(w) = 2∫₀¹ G(t)cos(cwt) dt` for `G` even and continuous. -/
theorem psi_fold (hGc : ContinuousOn G (Icc (-1) 1)) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s) (c w : ℝ) :
    psi c G w = 2 * ∫ t in (0 : ℝ)..1, G t * Real.cos (c * w * t) := by
  have h := Cvs.Prolate.SlepianEvenOrdering.integral_even_fold (F := fun s => G s * Real.cos (c * w * s))
    (hGc.mul (by fun_prop)) (fun s hs => by
      simp only [heven s ⟨by linarith [hs.1], hs.2⟩, mul_neg, Real.cos_neg])
  exact h

/-- `ρ_G(0) = 0` for `G` even and continuous with `∫₀¹ G = 0`. -/
theorem rhoG_zero (hGc : ContinuousOn G (Icc (-1) 1)) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s)
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) (c : ℝ) : rhoG c G 0 = 0 := by
  unfold rhoG
  rw [psi_fold hGc heven]
  simp [hGi]

/-- **The mode by parts**: for `G` even, `C¹` on `[0, 1]`, `∫₀¹ G = 0`, `a, θ > 0` and `c = 2π/a`,
`S_{G'}(n θ/a)/(πn) = −(θ/a)ρ_G(nθ)`. -/
theorem sawC_mul_sinT (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGc : ContinuousOn G (Icc (-1) 1)) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s)
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (n : ℕ) :
    sawC n * sinT G₁ (n * (θ / a)) = -(θ / a) * rhoG (2 * π / a) G (n * θ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul]
    rw [rhoG_zero hGc heven hGi]
    simp [sawC]
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set ω := 2 * π / a * (n * θ) with hω
  have hω0 : 0 < ω := by positivity
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hparts : ∫ t in (0 : ℝ)..1, Real.sin (ω * t) * G₁ t
      = Real.sin (ω * 1) * G 1 - Real.sin (ω * 0) * G 0 - ∫ t in (0 : ℝ)..1, ω * Real.cos (ω * t) * G t := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun t => Real.sin (ω * t))
      (u' := fun t => ω * Real.cos (ω * t)) (fun t _ => ?_) (fun t ht => hG t (by rwa [hI] at ht)) ?_ ?_
    · have := ((hasDerivAt_id' t).const_mul ω).sin
      simpa [mul_comm] using this
    · exact (by fun_prop : Continuous fun t => ω * Real.cos (ω * t)).intervalIntegrable _ _
    · exact (hG₁.mono (by rw [hI])).intervalIntegrable
  have hS : sinT G₁ (n * (θ / a)) = Real.sin ω * G 1 - ω * ∫ t in (0 : ℝ)..1, G t * Real.cos (ω * t) := by
    unfold sinT
    have e1 : ∫ t in (0 : ℝ)..1, G₁ t * Real.sin (2 * π * (n * (θ / a)) * t)
        = ∫ t in (0 : ℝ)..1, Real.sin (ω * t) * G₁ t := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hω]; ring_nf
    rw [e1, hparts, mul_one, mul_zero, Real.sin_zero, zero_mul, sub_zero, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hρ : rhoG (2 * π / a) G (n * θ)
      = 2 * (∫ t in (0 : ℝ)..1, G t * Real.cos (ω * t)) - 2 * G 1 * Real.sin ω / ω := by
    unfold rhoG ampl
    rw [psi_fold hGc heven, heven 1 ⟨by norm_num, le_rfl⟩, ← hω]
    ring
  rw [hS, hρ, sawC]
  have hθa : θ / a = ω / (2 * π * n) := by rw [hω]; field_simp
  rw [hθa]
  field_simp
  ring

/-- **The sawtooth–Poisson form of the reflected remainder**: for `G` even, `C¹` on `[0, 1]`, `∫₀¹ G = 0`,
`a, θ > 0` and `c = 2π/a`, `Σ_{n<N} ρ_G(nθ) → r_G(θ)`. -/
theorem tendsto_sum_rhoG (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGc : ContinuousOn G (Icc (-1) 1)) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s)
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, rhoG (2 * π / a) G (n * θ)) atTop (𝓝 (reflRem a G θ)) := by
  set g : ℝ → ℝ := fun t => G₁ (max 0 (min t 1)) with hgdef
  have hmem : ∀ t, max 0 (min t 1) ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hgc : Continuous g := hG₁.comp_continuous (by fun_prop) hmem
  have hgeq : ∀ t ∈ uIcc (0 : ℝ) 1, g t = G₁ t := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    simp only [hgdef, min_eq_left ht.2, max_eq_right ht.1]
  have hsin : ∀ ξ, sinT g ξ = sinT G₁ ξ := fun ξ =>
    intervalIntegral.integral_congr fun t ht => by simp only [hgeq t ht]
  have hsaw : sawT g (θ / a) = sawT G₁ (θ / a) :=
    intervalIntegral.integral_congr fun t ht => by simp only [hgeq t ht]
  have hy : 0 < θ / a := div_pos hθ ha
  have h := Cvs.Route.Visibility.SawtoothPlancherelBounds.tendsto_sum_sinT hgc hy
  simp only [hsin, hsaw] at h
  have hterm : ∀ N, ∑ n ∈ Finset.range N, sawC n * sinT G₁ (n * (θ / a))
      = -(θ / a) * ∑ n ∈ Finset.range N, rhoG (2 * π / a) G (n * θ) := fun N => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => sawC_mul_sinT hG hG₁ hGc heven hGi ha hθ n
  simp only [hterm] at h
  have h2 := h.const_mul (-(a / θ))
  have hr := Cvs.Route.Visibility.ReflectedRemainderMellin.mul_reflRem_eq hG hG₁ hGi ha hθ
  have hval : -(a / θ) * sawT G₁ (θ / a) = reflRem a G θ := by
    field_simp; linarith [hr]
  rw [hval] at h2
  refine h2.congr fun N => ?_
  field_simp

/-! ### The weighted norm -/

/-- `ρ_G` is measurable for `G` continuous on `[−1, 1]`. -/
theorem measurable_rhoG (hGc : ContinuousOn G (Icc (-1) 1)) (c : ℝ) : Measurable (rhoG c G) := by
  have hψ : Continuous (psi c G) :=
    Cvs.Prolate.RungSpanBernsteinNikolskii.continuous_psi (by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])
  unfold rhoG
  exact hψ.measurable.sub (((measurable_const.mul (Real.continuous_sin.measurable.comp
    (measurable_const.mul measurable_id)))).div (measurable_const.mul measurable_id))

/-- `(θ^{σ−½})² = θ^{2σ−1}` for `θ ≥ 0`. -/
theorem rpow_half_sq {θ : ℝ} (hθ : 0 ≤ θ) (σ : ℝ) : (θ ^ (σ - 1 / 2)) ^ 2 = θ ^ (2 * σ - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hθ]; norm_num; ring_nf

/-- **One mode in the weighted norm**: for `σ ≤ 3/2`, `n ≥ 1` and `∫⁻₁^∞ u²ρ(u)² ≤ M`,
`∫⁻₁^∞ (ρ(nθ)θ^{σ−½})² ≤ M/n³`. -/
theorem lintegral_mode_le (hGc : ContinuousOn G (Icc (-1) 1)) {c σ M : ℝ} (hσ : σ ≤ 3 / 2) {n : ℕ} (hn : 0 < n)
    (hM : ∫⁻ u in Ioi 1, ENNReal.ofReal (u ^ 2 * rhoG c G u ^ 2) ≤ ENNReal.ofReal M) :
    ∫⁻ θ in Ioi 1, ENNReal.ofReal ((rhoG c G (n * θ) * θ ^ (σ - 1 / 2)) ^ 2) ≤ ENNReal.ofReal (M / n ^ 3) := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hρm := measurable_rhoG hGc c
  -- the weight is at most `θ²`
  have h1 : ∫⁻ θ in Ioi 1, ENNReal.ofReal ((rhoG c G (n * θ) * θ ^ (σ - 1 / 2)) ^ 2)
      ≤ ∫⁻ θ in Ioi 1, ENNReal.ofReal (1 / n ^ 2) * ENNReal.ofReal ((n * θ) ^ 2 * rhoG c G (n * θ) ^ 2) := by
    refine setLIntegral_mono' measurableSet_Ioi fun θ hθ => ?_
    have hθ1 : (1 : ℝ) < θ := hθ
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_pow, rpow_half_sq (by linarith)]
    have hw : θ ^ (2 * σ - 1) ≤ θ ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hθ1.le (by linarith)
    rw [Real.rpow_two] at hw
    have e : 1 / (n : ℝ) ^ 2 * ((n * θ) ^ 2 * rhoG c G (n * θ) ^ 2) = rhoG c G (n * θ) ^ 2 * θ ^ 2 := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hw (sq_nonneg _)
  -- the dilation `u = nθ`
  set F : ℝ → ℝ≥0∞ := (Ioi (n : ℝ)).indicator fun u => ENNReal.ofReal (u ^ 2 * rhoG c G u ^ 2) with hF
  have hFm : Measurable F :=
    (ENNReal.measurable_ofReal.comp ((measurable_id.pow_const 2).mul (hρm.pow_const 2))).indicator
      measurableSet_Ioi
  have hdil := Cvs.Route.Visibility.SawtoothPlancherelBounds.lintegral_comp_mul_left hFm hnr
  have hleft : ∫⁻ θ in Ioi 1, ENNReal.ofReal ((n * θ) ^ 2 * rhoG c G (n * θ) ^ 2) = ∫⁻ θ, F (n * θ) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    congr 1; funext θ
    simp only [hF, Set.indicator, mem_Ioi]
    by_cases h : (1 : ℝ) < θ
    · rw [ite_eq_left h, ite_eq_left (by nlinarith)]
    · rw [ite_eq_right h, ite_eq_right (by push Not at h ⊢; nlinarith)]
  have hright : ∫⁻ u, F u ≤ ENNReal.ofReal M := by
    rw [hF, lintegral_indicator measurableSet_Ioi]
    refine le_trans (lintegral_mono_set (Ioi_subset_Ioi (by exact_mod_cast hn))) hM
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  rw [hleft, hdil] at h1
  refine h1.trans ?_
  calc ENNReal.ofReal (1 / n ^ 2) * (ENNReal.ofReal (n : ℝ)⁻¹ * ∫⁻ u, F u)
      ≤ ENNReal.ofReal (1 / n ^ 2) * (ENNReal.ofReal (n : ℝ)⁻¹ * ENNReal.ofReal M) := by gcongr
    _ = ENNReal.ofReal (M / n ^ 3) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp

/-- **The exterior energy in Poisson form**: for `G` even, `C¹` on `[0, 1]`, `∫₀¹ G = 0`, `a > 0`, `σ < 1`,
`c = 2π/a` and `∫⁻₁^∞ ξ²ρ_G(ξ)² ≤ M`, `Ext_G(σ) ≤ (a(|G(1)| + |G(0)|)/(2√(2(1 − σ))) + ζ(3/2)√M)²`. -/
theorem extInt_le (hG : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt G (G₁ u) u) (hG₁ : ContinuousOn G₁ (Icc 0 1))
    (hGc : ContinuousOn G (Icc (-1) 1)) (heven : ∀ s ∈ Icc (-1 : ℝ) 1, G (-s) = G s)
    (hGi : ∫ u in (0 : ℝ)..1, G u = 0) {a σ M : ℝ} (ha : 0 < a) (hσ : σ < 1) (hM0 : 0 ≤ M)
    (hM : ∫⁻ u in Ioi 1, ENNReal.ofReal (u ^ 2 * rhoG (2 * π / a) G u ^ 2) ≤ ENNReal.ofReal M) :
    Cvs.Route.Visibility.ExteriorTransformPointBound.extInt a G σ
      ≤ (a * (|G 1| + |G 0|) / (2 * √(2 * (1 - σ))) + zeta32 * √M) ^ 2 := by
  set c := 2 * π / a with hc
  set μ := volume.restrict (Ioi (1 : ℝ)) with hμ
  set w : ℝ → ℝ := fun θ => θ ^ (σ - 1 / 2) with hw
  set S : ℝ → ℝ := fun θ => a / θ * (G 1 * saw (θ / a) - G 0 / 2) with hS
  set r := reflRem a G with hr
  set K := (a * (|G 1| + |G 0|) / 2) ^ 2 with hK
  set BS := a * (|G 1| + |G 0|) / (2 * √(2 * (1 - σ))) with hBS
  have h1σ : 0 < 1 - σ := by linarith
  have hBS0 : 0 ≤ BS := by positivity
  have hwm : Measurable w := measurable_id.pow_const _
  have hSm : Measurable S :=
    (measurable_const.div measurable_id).mul ((measurable_const.mul
      (Cvs.Route.Visibility.ProjectionShareSawtooth.measurable_saw.comp (measurable_id.div_const a))).sub measurable_const)
  have hGc01 : ContinuousOn G (Icc 0 1) := hGc.mono (Icc_subset_Icc (by norm_num) le_rfl)
  have hrm : Measurable r := Cvs.Route.Visibility.ProjectionShareSawtooth.measurable_reflRem ha hGc01
  -- the sawtooth part
  have hSw : eLpNorm (fun θ => S θ * w θ) 2 μ ≤ ENNReal.ofReal BS := by
    rw [Cvs.Route.Visibility.SawtoothPlancherelBounds.eLpNorm_two_le_iff (fun θ => S θ * w θ) hBS0 (hSm.mul hwm).aestronglyMeasurable]
    have hint : IntegrableOn (fun θ : ℝ => K * θ ^ (2 * σ - 3)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul K
    calc ∫⁻ θ, ENNReal.ofReal ((S θ * w θ) ^ 2) ∂μ ≤ ∫⁻ θ in Ioi 1, ENNReal.ofReal (K * θ ^ (2 * σ - 3)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun θ hθ => ENNReal.ofReal_le_ofReal ?_
          have hθ1 : (1 : ℝ) < θ := hθ
          have hθ0 : (0 : ℝ) < θ := by linarith
          have hsaw := Cvs.Route.Visibility.ProjectionShareSawtooth.abs_saw_le (θ / a)
          have hSb : |S θ| ≤ a * (|G 1| + |G 0|) / 2 / θ := by
            simp only [hS]
            rw [abs_mul, abs_div, abs_of_pos ha, abs_of_pos hθ0]
            have : |G 1 * saw (θ / a) - G 0 / 2| ≤ (|G 1| + |G 0|) / 2 := by
              calc |G 1 * saw (θ / a) - G 0 / 2| ≤ |G 1 * saw (θ / a)| + |G 0 / 2| := abs_sub _ _
                _ = |G 1| * |saw (θ / a)| + |G 0| / 2 := by rw [abs_mul, abs_div, abs_two]
                _ ≤ |G 1| * (1 / 2) + |G 0| / 2 := by gcongr
                _ = (|G 1| + |G 0|) / 2 := by ring
            calc a / θ * |G 1 * saw (θ / a) - G 0 / 2| ≤ a / θ * ((|G 1| + |G 0|) / 2) :=
                  mul_le_mul_of_nonneg_left this (by positivity)
              _ = a * (|G 1| + |G 0|) / 2 / θ := by ring
          have hS2 : S θ ^ 2 ≤ K / θ ^ 2 := by
            have := pow_le_pow_left₀ (abs_nonneg _) hSb 2
            rw [sq_abs, div_pow] at this; rw [hK]; exact this
          rw [mul_pow, hw, rpow_half_sq hθ0.le]
          have e : K * θ ^ (2 * σ - 3) = K / θ ^ 2 * θ ^ (2 * σ - 1) := by
            rw [show 2 * σ - 3 = 2 * σ - 1 - 2 by ring, Real.rpow_sub hθ0, Real.rpow_two]; ring
          rw [e]
          exact mul_le_mul_of_nonneg_right hS2 (by positivity)
      _ = ENNReal.ofReal (∫ θ in Ioi 1, K * θ ^ (2 * σ - 3)) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (ae_restrict_of_forall_mem measurableSet_Ioi fun θ hθ => by
              have : (0 : ℝ) < θ := lt_trans one_pos hθ
              positivity)).symm
      _ = ENNReal.ofReal (BS ^ 2) := by
          congr 1
          have hs : √(2 * (1 - σ)) ^ 2 = 2 * (1 - σ) := Real.sq_sqrt (by linarith)
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, hBS, div_pow,
            mul_pow (2 : ℝ), hs, hK, div_pow]
          have h2 : 2 * σ - 3 + 1 ≠ 0 := by linarith
          field_simp; ring
  -- the Poisson part
  set cn : ℕ → ℝ := fun n => √M * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) with hcn
  have hrw : eLpNorm (fun θ => r θ * w θ) 2 μ ≤ ENNReal.ofReal (∑' n, cn n) := by
    refine Cvs.Route.Visibility.SawtoothPlancherelBounds.eLpNorm_le_of_tendsto_sum (ψ := fun n θ => rhoG c G (n * θ) * w θ)
      (fun n => (((measurable_rhoG hGc c).comp (measurable_const.mul measurable_id)).mul hwm).aestronglyMeasurable)
      (fun n => ?_) (fun n => mul_nonneg (Real.sqrt_nonneg _)
        (div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
      (Cvs.Route.Visibility.SawtoothPlancherelBounds.summable_zeta32.mul_left _) ?_
    · rw [Cvs.Route.Visibility.SawtoothPlancherelBounds.eLpNorm_two_le_iff (fun θ => rhoG c G (n * θ) * w θ) (by positivity)
        (((measurable_rhoG hGc c).comp (measurable_const.mul measurable_id)).mul hwm).aestronglyMeasurable]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [rhoG_zero hGc heven hGi]
      · refine (lintegral_mode_le hGc (by linarith) hn hM).trans (le_of_eq ?_)
        congr 1
        rw [hcn, mul_pow, Real.sq_sqrt hM0, div_pow, Cvs.Route.Visibility.SawtoothPlancherelBounds.rpow_three_halves_sq]; ring
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun θ hθ => ?_
      have hθ0 : (0 : ℝ) < θ := lt_trans one_pos hθ
      have h := (tendsto_sum_rhoG hG hG₁ hGc heven hGi ha hθ0).mul_const (w θ)
      simpa only [Finset.sum_mul] using h
  have htsum : ∑' n, cn n = √M * zeta32 := tsum_mul_left
  -- Minkowski
  have hz0 : 0 ≤ zeta32 :=
    tsum_nonneg fun n => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hf : eLpNorm (fun θ => S θ * w θ + r θ * w θ) 2 μ ≤ ENNReal.ofReal (BS + zeta32 * √M) := by
    refine (eLpNorm_add_le one_le_two).trans ?_
    rw [ENNReal.ofReal_add hBS0 (mul_nonneg hz0 (Real.sqrt_nonneg _)), mul_comm zeta32, ← htsum]
    exact add_le_add hSw hrw
  have hB0 : 0 ≤ BS + zeta32 * √M := add_nonneg hBS0 (mul_nonneg hz0 (Real.sqrt_nonneg _))
  rw [Cvs.Route.Visibility.SawtoothPlancherelBounds.eLpNorm_two_le_iff (fun θ => S θ * w θ + r θ * w θ) hB0
    ((hSm.mul hwm).add (hrm.mul hwm)).aestronglyMeasurable] at hf
  -- back to `Ext`
  have heq : Cvs.Route.Visibility.ExteriorTransformPointBound.extInt a G σ = ∫ θ, (S θ * w θ + r θ * w θ) ^ 2 ∂μ := by
    unfold Cvs.Route.Visibility.ExteriorTransformPointBound.extInt
    refine setIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
    have hθ0 : (0 : ℝ) < θ := lt_trans one_pos hθ
    simp only [hS, hr, hw]
    rw [Cvs.Route.Visibility.ProjectionShareSawtooth.eimage_eq_saw_add_reflRem, ← add_mul, mul_pow, rpow_half_sq hθ0.le]
  have hfm : Measurable fun θ => (S θ * w θ + r θ * w θ) ^ 2 :=
    ((hSm.mul hwm).add (hrm.mul hwm)).pow_const 2
  rw [heq, integral_eq_lintegral_of_nonneg_ae (f := fun θ => (S θ * w θ + r θ * w θ) ^ 2)
    (ae_of_all _ fun _ => sq_nonneg _) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hf

end Cvs.Route.Visibility.ExteriorImageSawtoothPoisson
