import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.LowRungHighSpectralMass
import Cvs.L2a.LowRungTruncationRate
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTailEdgeRow
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.EdgeLayerDerivativeMass
import Cvs.Prolate.Envelope.FarRadialDerivative
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.SincTopIsRung
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.TruncatedTailAboveOrbit
import Cvs.Prolate.TruncatedTailEdgeIntegral
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.SelfConvolutionTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The truncation rate and the high mass on a finite span of prolate rungs

For `Φ = Σᵢ bᵢ ψᵢ` with low rungs `ψᵢ` (`c ≥ 100`, `0 ≤ χᵢ ≤ (2/5)c²`) and `M = (Σᵢ |bᵢ||ψᵢ(1)|)²`, for `k > 1`:
`∫_{θ>1} (posTail Φ k − F_∞)² ≤ Krate(c)·M·k^{-1/2}` and `∫_{θ>1} F_k² − specMass F_k (2ck) ≤ Khigh(c)·M·k^{-1/2}`.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology
open scoped FourierTransform

namespace Cvs.L2a.FiniteSpanRateHighMass

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.SlepianCommutingRelation (kint)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.L2a.SpectralMassLevelLeak (specMass)
open Cvs.L2a.LowRungTruncationRate (Krate)
open Cvs.L2a.LowRungHighSpectralMass (Khigh)

/-- The position-truncated tail is linear in the profile. -/
theorem posTail_sum {ι : Type*} [Fintype ι] (b : ι → ℝ) (f : ι → ℝ → ℝ) (X θ : ℝ) :
    posTail (fun ξ => ∑ i, b i * f i ξ) X θ = ∑ i, b i * posTail (f i) X θ := by
  simp only [Cvs.L2a.PositionTruncatedTail.posTail_eq_sum, Set.indicator_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

/-- **Minkowski for a finite sum**: `∫_S (Σ bᵢ xᵢ)² ≤ (Σ |bᵢ| √(∫_S xᵢ²))²`. -/
theorem integral_sum_sq_le {ι : Type*} [Fintype ι] (b : ι → ℝ) {x : ι → ℝ → ℝ} {S : Set ℝ}
    (hx : ∀ i, IntegrableOn (fun θ => x i θ ^ 2) S) (hxy : ∀ i j, IntegrableOn (fun θ => x i θ * x j θ) S) :
    ∫ θ in S, (∑ i, b i * x i θ) ^ 2 ≤ (∑ i, |b i| * √(∫ θ in S, x i θ ^ 2)) ^ 2 := by
  have e : ∀ θ, (∑ i, b i * x i θ) ^ 2 = ∑ i, ∑ j, b i * b j * (x i θ * x j θ) := fun θ => by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hxy i j).const_mul _]
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hxy i j).const_mul _]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [integral_const_mul]
  have h := Cvs.L2a.FullTailConvergence.abs_setIntegral_mul_le (hx i) (hx j) (hxy i j)
  calc b i * b j * ∫ θ in S, x i θ * x j θ ≤ |b i * b j * ∫ θ in S, x i θ * x j θ| := le_abs_self _
    _ = |b i| * |b j| * |∫ θ in S, x i θ * x j θ| := by rw [abs_mul, abs_mul]
    _ ≤ |b i| * |b j| * (√(∫ θ in S, x i θ ^ 2) * √(∫ θ in S, x j θ ^ 2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- The truncation-rate constant is nonnegative. -/
theorem Krate_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ Krate c := by
  unfold Krate Cvs.L2a.PositionTailEdgeRow.rowC; positivity

/-- **The truncation rate on a span**: `∫_{θ>1} (posTail Φ k − F_∞)² ≤ Krate(c)·(Σ|bᵢ||ψᵢ(1)|)²·k^{-1/2}`. -/
theorem integral_posTail_sub_fullTail_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 100 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i, χ i ≤ 2 / 5 * c ^ 2) {k : ℝ} (hk : 1 < k) :
    ∫ θ in Ioi 1, (posTail (psi c (fun s => ∑ i, b i * g i s)) k θ
        - fullTail (psi c (fun s => ∑ i, b i * g i s)) θ) ^ 2
      ≤ Krate c * (∑ i, |b i| * |psi c (g i) 1|) ^ 2 * k ^ (-(1 / 2) : ℝ) := by
  have hc0 : 0 < c := by linarith
  set ψ : ι → ℝ → ℝ := fun i => psi c (g i) with hψd
  set x : ι → ℝ → ℝ := fun i θ => posTail (ψ i) k θ - fullTail (ψ i) θ with hxd
  -- the full tail is linear in the profile
  have hfull : ∀ θ, 1 < θ → fullTail (psi c (fun s => ∑ i, b i * g i s)) θ = ∑ i, b i * fullTail (ψ i) θ :=
    fun θ hθ => by
    have h1 := Cvs.L2a.FullTailConvergence.tendsto_partial (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b hg)
      (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b hg₁) (Cvs.L2a.FullTailFloorLimit.continuousOn_span b hg₂c) hc0 hθ
    have h2 : Tendsto (fun M : ℕ => ∑ i, b i * ∑ m ∈ Finset.Icc 1 M, ψ i (m * θ)) atTop
        (𝓝 (∑ i, b i * fullTail (ψ i) θ)) :=
      tendsto_finsetSum _ fun i _ =>
        (Cvs.L2a.FullTailConvergence.tendsto_partial (hg i) (hg₁ i) (hg₂c i) hc0 hθ).const_mul (b i)
    refine tendsto_nhds_unique h1 (h2.congr fun M => ?_)
    rw [← Cvs.L2a.FullTailFloorLimit.span_eq b hg c]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hpt : ∀ θ ∈ Ioi (1 : ℝ), (posTail (psi c (fun s => ∑ i, b i * g i s)) k θ
      - fullTail (psi c (fun s => ∑ i, b i * g i s)) θ) ^ 2 = (∑ i, b i * x i θ) ^ 2 := fun θ hθ => by
    rw [hfull θ hθ, ← Cvs.L2a.FullTailFloorLimit.span_eq b hg c, posTail_sum, ← Finset.sum_sub_distrib]
    simp only [hxd, hψd, mul_sub]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  -- each rung's difference is bounded by `2B/θ`
  have hmeas : ∀ i, Measurable (x i) := fun i =>
    (Cvs.L2a.FullTailConvergence.measurable_posTail_psi (hg i) c k).sub
      (Cvs.L2a.FullTailConvergence.measurable_fullTail (hg i) (hg₁ i) (hg₂c i) hc0)
  have hbd := fun i θ (hθ : 0 < θ) =>
    Cvs.L2a.FullTailConvergence.abs_posTail_sub_le (hg i) (hg₁ i) (hg₂c i) hc0 k hθ
  have hx : ∀ i, IntegrableOn (fun θ => x i θ ^ 2) (Ioi 1) := fun i =>
    Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le (hmeas i) (hbd i)
  have hxy : ∀ i j, IntegrableOn (fun θ => x i θ * x j θ) (Ioi 1) := fun i j =>
    Cvs.L2a.FullTailConvergence.integrableOn_mul_of_le (hmeas i) (hmeas j) (hbd i) (hbd j)
  refine (integral_sum_sq_le b hx hxy).trans ?_
  -- each rung's rate
  set q := Krate c * k ^ (-(1 / 2) : ℝ) with hq
  have hq0 : 0 ≤ q := mul_nonneg (Krate_nonneg hc0) (by positivity)
  have hi : ∀ i, √(∫ θ in Ioi 1, x i θ ^ 2) ≤ √q * |ψ i 1| := fun i => by
    have h := Cvs.L2a.LowRungTruncationRate.integral_posTail_sub_fullTail_le (hg i) (hg₁ i) (hg₂c i) (hang i) hc
      (hχ0 i) (hχ i) hk
    have e : Krate c * psi c (g i) 1 ^ 2 * k ^ (-(1 / 2) : ℝ) = q * ψ i 1 ^ 2 := by rw [hq]; ring
    rw [e] at h
    calc √(∫ θ in Ioi 1, x i θ ^ 2) ≤ √(q * ψ i 1 ^ 2) := Real.sqrt_le_sqrt h
      _ = √q * |ψ i 1| := by rw [Real.sqrt_mul hq0, Real.sqrt_sq_eq_abs]
  have hsum : ∑ i, |b i| * √(∫ θ in Ioi 1, x i θ ^ 2) ≤ √q * ∑ i, |b i| * |ψ i 1| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc |b i| * √(∫ θ in Ioi 1, x i θ ^ 2) ≤ |b i| * (√q * |ψ i 1|) :=
          mul_le_mul_of_nonneg_left (hi i) (abs_nonneg _)
      _ = _ := by ring
  have h0 : 0 ≤ ∑ i, |b i| * √(∫ θ in Ioi 1, x i θ ^ 2) := Finset.sum_nonneg fun i _ => by positivity
  calc (∑ i, |b i| * √(∫ θ in Ioi 1, x i θ ^ 2)) ^ 2 ≤ (√q * ∑ i, |b i| * |ψ i 1|) ^ 2 :=
        pow_le_pow_left₀ h0 hsum 2
    _ = q * (∑ i, |b i| * |ψ i 1|) ^ 2 := by rw [mul_pow, Real.sq_sqrt hq0]
    _ = _ := by rw [hq]; ring

/-- The Fourier amplitude of a low rung's truncated tail at unit edge value. -/
def amp (c k : ℝ) : ℝ :=
  6 + 4 * (4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c))) + 74 * √(48 * exp 1 / c) * (1 + Real.log k)

/-- **The far Fourier decay of a rung's truncated tail**: `‖𝓕 F_k(t/2π)‖ ≤ |ψ(1)|·amp(c,k)/|t|` for `|t| ≥ 2ck`. -/
theorem norm_fourier_le {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 100 ≤ c) (hχ0 : 0 ≤ χ) (hχ : χ ≤ 2 / 5 * c ^ 2) {k : ℝ} (hk : 1 < k) {t : ℝ} (ht : k * (2 * c) ≤ |t|) :
    ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c g) k))) (t / (2 * π))‖
      ≤ |psi c g 1| * amp c k / |t| := by
  have hχc : χ < c ^ 2 := by nlinarith
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  obtain ⟨hψs, hvs, hode⟩ := Cvs.L2a.AngularProlateTailPositive.psi_system hg hg₁ hg₂c hang
  obtain ⟨hψ, hu, hψc, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  set ψ := psi c g with hψdef
  set a := |ψ 1| with ha
  set a₁ := 4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)) with ha₁
  set e := √(48 * exp 1 / c) with he
  have ha2 : a ^ 2 = ψ 1 ^ 2 := sq_abs _
  have hP₀ : ∀ θ ∈ Icc (1 : ℝ) 2, |ψ θ| ≤ a := fun θ hθ => by
    have hs : ψ θ ^ 2 ≤ ψ 1 ^ 2 :=
      Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge (ξ₁ := 2) hχc hθ (fun r _ => hψs r) (fun r _ => hvs r)
        (fun r _ => hode r)
    simpa using sq_le_sq.mp hs
  have hA₁ : ∫ θ in (1 : ℝ)..2, |kint g (fun ξ s => -(c * s * sin (c * ξ * s))) θ| ≤ a * a₁ := by
    have h := Cvs.Prolate.EdgeLayerDerivativeMass.integral_abs_deriv_le hg hg₁ hg₂c hang hc hχ0 hχ
    calc _ ≤ _ := h
      _ = a * a₁ := by rw [ha, ha₁]; ring
  have hψ₁ := fun ξ (_ : ξ ∈ Icc (1 : ℝ) 2) => Cvs.Prolate.SincTopIsRung.hasDerivAt_psi (c := c) hgc ξ
  have hψ₁c : ContinuousOn (kint g (fun ξ s => -(c * s * sin (c * ξ * s)))) (Icc 1 2) :=
    fun ξ _ => (Cvs.Prolate.SincTopIsRung.hasDerivAt_psi₁ (c := c) hgc ξ).continuousAt.continuousWithinAt
  have hE : ∀ ξ ∈ Icc 2 k, Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact.energy (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.aP c χ) ψ
      (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c g) ξ ≤ 48 * exp 1 * ψ 1 ^ 2 := fun ξ hξ =>
    Cvs.Prolate.Envelope.FarRadialDerivative.energy_far_le hg hg₁ hg₂c hang hc hχ0 hχ hξ.1
  have hsq : √(48 * exp 1 * ψ 1 ^ 2 / c) = a * e := by
    have h0 : a = √(a ^ 2) := (Real.sqrt_sq (abs_nonneg _)).symm
    rw [he, h0, ← Real.sqrt_mul (sq_nonneg _), ha2]
    congr 1; ring
  have h2' : (2 * c * k) ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h := Cvs.Prolate.TruncatedTailEdgeIntegral.norm_fourier_posTail_le_hi' (Ebar := 48 * exp 1 * ψ 1 ^ 2) (P₀ := a)
    (A₁ := a * a₁) (t := t) (by linarith) hχ0 hχc.le hk.le (by nlinarith [sq_nonneg (c * k)]) hψc.continuousOn
    (fun ξ hξ => hψ ξ (by linarith [hξ.1])) (fun ξ _ => hu ξ) hE hψ₁ hψ₁c hP₀ hA₁
  refine h.trans (le_of_eq ?_)
  rw [hsq, amp, ← ha₁, ← he]; ring

/-- **The high mass on a span**: `∫_{θ>1} F_k² − specMass F_k (2ck) ≤ Khigh(c)·(Σ|bᵢ||ψᵢ(1)|)²·k^{-1/2}`. -/
theorem highMass_le {ι : Type*} [Fintype ι] {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ}
    (b : ι → ℝ) (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 100 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχ : ∀ i, χ i ≤ 2 / 5 * c ^ 2) {k : ℝ} (hk : 1 < k) :
    (∫ θ in Ioi 1, posTail (psi c (fun s => ∑ i, b i * g i s)) k θ ^ 2)
        - specMass (posTail (psi c (fun s => ∑ i, b i * g i s)) k) (k * (2 * c))
      ≤ Khigh c * (∑ i, |b i| * |psi c (g i) 1|) ^ 2 * k ^ (-(1 / 2) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  set G := fun s => ∑ i, b i * g i s with hGd
  set S := ∑ i, |b i| * |psi c (g i) 1| with hSd
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hGc : ContinuousOn G (uIcc (-1) 1) := fun s hs =>
    (Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b hg s hs).continuousAt.continuousWithinAt
  set a₁ := 4 * (2 ^ (-(3/4) : ℝ) * √(96 * exp 1 * c)) with ha₁
  set e := √(48 * exp 1 / c) with he
  have ha₁0 : 0 ≤ a₁ := by positivity
  have he2 : e ^ 2 = 48 * exp 1 / c := Real.sq_sqrt (by positivity)
  set A := S * (6 + 4 * a₁) + 74 * (S * e) * (1 + Real.log k) with hAd
  -- the Fourier transform is linear over the rungs
  have hadm := fun i => Cvs.L2a.PositionTailAdmissible.admissible_posTail hk.le
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg i s hs).continuousAt.continuousWithinAt) c).contDiffOn
      (Φ := psi c (g i))
  have hfour : ∀ t, k * (2 * c) ≤ |t| →
      ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c G) k))) (t / (2 * π))‖
        ≤ A / |t| := by
    intro t ht
    have ecf : Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c G) k))
        = fun v => ∑ i, (b i : ℂ) • Cvs.WeilForm.SelfConvolutionTransform.cf
          (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c (g i)) k)) v := by
      funext v
      simp only [Cvs.WeilForm.SelfConvolutionTransform.cf, Cvs.L2a.TailLogScaleTest.logScale, hGd,
        ← Cvs.L2a.FullTailFloorLimit.span_eq b hg c, posTail_sum, Finset.sum_mul]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul]; ring
    have hint : ∀ i, Integrable (fun v => 𝐞 (-(v * (t / (2 * π)))) •
        (b i : ℂ) • Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c (g i)) k)) v) := by
      intro i
      have h1 : Integrable (Cvs.WeilForm.SelfConvolutionTransform.cf
          (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c (g i)) k))) := (hadm i).2.1.ofReal
      have h2 := (h1.const_mul (b i : ℂ))
      have := (Real.fourierIntegral_convergent_iff (μ := volume) (t / (2 * π))).2 h2
      simpa [real_inner_eq_re_inner, mul_comm, smul_eq_mul] using this
    have elin : 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c G) k))) (t / (2 * π))
        = ∑ i, (b i : ℂ) • 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf
          (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c (g i)) k))) (t / (2 * π)) := by
      rw [ecf, Real.fourier_real_eq]
      simp_rw [Finset.smul_sum]
      rw [integral_finsetSum _ fun i _ => hint i]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.fourier_real_eq, ← integral_smul]
      congr 1; funext v; rw [smul_comm]
    rw [elin]
    have ht0 : 0 < |t| := lt_of_lt_of_le (by positivity) ht
    calc _ ≤ ∑ i, ‖(b i : ℂ) • 𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf
          (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c (g i)) k))) (t / (2 * π))‖ := norm_sum_le _ _
      _ ≤ ∑ i, |b i| * (|psi c (g i) 1| * amp c k / |t|) := Finset.sum_le_sum fun i _ => by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (norm_fourier_le (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχ i) hk ht) (abs_nonneg _)
      _ = S * amp c k / |t| := by
          rw [hSd, Finset.sum_mul, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = A / |t| := by rw [hAd, ha₁, he, amp]; ring
  obtain ⟨h2, h1, -⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hk.le
    (Cvs.L2a.FullTailConvergence.contDiff_psi hGc c).contDiffOn
  have hmain := Cvs.Prolate.TruncatedTailAboveOrbit.highMass_le
    (fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero _ k hθ) h2 h1 (by positivity) hfour
  refine hmain.trans ?_
  -- `A²/(2ck) ≤ Khigh·S²·k^{-1/2}`
  have hL := Cvs.L2a.L1FullTailWinfBound.one_add_log_sq_le hk.le
  have hsk : k ^ (1 / 2 : ℝ) * k ^ (1 / 2 : ℝ) = k := by
    rw [← rpow_add hk0]; norm_num
  have hs1 : 1 ≤ k ^ (1 / 2 : ℝ) := one_le_rpow hk.le (by norm_num)
  have hA2 : A ^ 2 ≤ 2 * (S * (6 + 4 * a₁)) ^ 2 + 2 * (74 * (S * e) * (1 + Real.log k)) ^ 2 := by
    nlinarith [sq_nonneg (S * (6 + 4 * a₁) - 74 * (S * e) * (1 + Real.log k))]
  have hA2' : A ^ 2 ≤ 2 * S ^ 2 * ((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25 * k ^ (1 / 2 : ℝ)) := by
    refine hA2.trans ?_
    have : (74 * (S * e) * (1 + Real.log k)) ^ 2 ≤ 74 ^ 2 * S ^ 2 * e ^ 2 * (25 * k ^ (1 / 2 : ℝ)) := by
      rw [show (74 * (S * e) * (1 + Real.log k)) ^ 2 = 74 ^ 2 * S ^ 2 * e ^ 2 * (1 + Real.log k) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left hL (by positivity)
    nlinarith
  have hkey : (6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25 * k ^ (1 / 2 : ℝ)
      ≤ ((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25) * k ^ (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg (6 + 4 * a₁)]
  rw [Khigh, ← ha₁, ← he2, div_le_iff₀ (by positivity)]
  calc A ^ 2 ≤ 2 * S ^ 2 * ((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25 * k ^ (1 / 2 : ℝ)) := hA2'
    _ ≤ 2 * S ^ 2 * (((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25) * k ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((6 + 4 * a₁) ^ 2 + 74 ^ 2 * e ^ 2 * 25) / c * S ^ 2 * k ^ (-(1 / 2) : ℝ) * (k * (2 * c)) := by
        have hS0 : 0 < k ^ (1 / 2 : ℝ) := by linarith
        rw [show k ^ (-(1 / 2) : ℝ) = 1 / k ^ (1 / 2 : ℝ) by rw [rpow_neg hk0.le, inv_eq_one_div]]
        generalize k ^ (1 / 2 : ℝ) = R at hS0 hsk ⊢
        rw [← hsk]
        field_simp

end Cvs.L2a.FiniteSpanRateHighMass
