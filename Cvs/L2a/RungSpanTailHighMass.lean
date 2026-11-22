import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FarPartDirichletSplit
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.ProlateWindowMassIdentity
import Cvs.Prolate.RungTailIntegralMass
import Cvs.Prolate.SincTopIsRung
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Prolate.TruncatedTailAboveOrbit
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
# The rung span's truncated tails: their high mass and their norm

For `Φ = Σ aᵢψᵢ` on rungs at `c ≥ 80`: `|ψᵢ| ≤ ∫|gᵢ|`, `|ψᵢ′| ≤ c∫|gᵢ|`, and the energy `≤ 6cMᵢ` put Cvs.Prolate.TruncatedTailAboveOrbit at
`P₀ = ∫|gᵢ|`, `P₁ = c∫|gᵢ|`, `Ē = 6cMᵢ`; the span's truncated tail has mass at most `(α + β(1 + log k))²/(kT)` above
`kT`, `T ≥ 2c`. Mode by mode, with `RungCountEnvelope`'s envelope, `∫ F_k² ≤ (1 + log k) J (1 + 8 log k) P`, `P = Σ aᵢ²Mᵢ`.
-/

namespace Cvs.L2a.RungSpanTailHighMass

open Real Set intervalIntegral MeasureTheory Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.PositionTruncatedTail
open scoped FourierTransform

/-! ### Crude pointwise bounds on a cosine transform -/

theorem abs_kint_le {g : ℝ → ℝ} {k : ℝ → ℝ → ℝ} {C ξ : ℝ}
    (hi : IntervalIntegrable (fun s => g s * k ξ s) volume (-1) 1) (hgi : IntervalIntegrable g volume (-1) 1)
    (hk : ∀ s ∈ Icc (-1 : ℝ) 1, |k ξ s| ≤ C) :
    |Cvs.Prolate.SlepianCommutingRelation.kint g k ξ| ≤ C * ∫ s in (-1 : ℝ)..1, |g s| := by
  unfold Cvs.Prolate.SlepianCommutingRelation.kint
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (by norm_num) hi.abs (hgi.abs.const_mul C) fun s hs => ?_
  rw [abs_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hk s hs) (abs_nonneg _)

theorem abs_psi_le_L1 {c ξ : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1)) :
    |psi c g ξ| ≤ 1 * ∫ s in (-1 : ℝ)..1, |g s| := by
  unfold psi
  refine abs_kint_le ?_ hg.intervalIntegrable fun s _ => abs_cos_le_one _
  exact (hg.mul (Continuous.continuousOn (by fun_prop))).intervalIntegrable

theorem abs_psi₁_le_L1 {c ξ : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (uIcc (-1) 1)) :
    |Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ| ≤ |c| * ∫ s in (-1 : ℝ)..1, |g s| := by
  refine abs_kint_le ?_ hg.intervalIntegrable fun s hs => ?_
  · exact (hg.mul (Continuous.continuousOn (by fun_prop))).intervalIntegrable
  · have hs' : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
    rw [abs_neg, abs_mul, abs_mul]
    calc |c| * |s| * |sin (c * ξ * s)| ≤ |c| * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hs' (abs_nonneg c)) (abs_sin_le_one _) (abs_nonneg _) (by positivity)
      _ = |c| := by ring

/-! ### One rung -/

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- `A(k) = 2(3P₀ + 2P₁) + 74√(6M)(1 + log k)` with `P₀ = ∫|g|`, `P₁ = c∫|g|`, `M = ∫₁^∞ ψ²`. -/
noncomputable def rungA (c : ℝ) (g : ℝ → ℝ) (k : ℝ) : ℝ :=
  2 * (3 * (∫ s in (-1 : ℝ)..1, |g s|) + 2 * (c * ∫ s in (-1 : ℝ)..1, |g s|))
    + 74 * √(6 * ∫ t in Ioi 1, psi c g t ^ 2) * (1 + Real.log k)

/-- **One rung's truncated tail above the orbit frequency**: `‖𝓕(posTail ψ k)(t)‖ ≤ A(k)/|t|` for `t² ≥ 2c²k²`. -/
theorem norm_fourier_posTail_rung_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 80 ≤ c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) {k t : ℝ} (hk : 1 ≤ k) (ht : 2 * c ^ 2 * k ^ 2 ≤ t ^ 2) :
    ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c g) k))) (t / (2 * π))‖
      ≤ rungA c g k / |t| := by
  have hc0 : 0 < c := by linarith
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  obtain ⟨hψ, hu, hψc, -⟩ := Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system hg hg₁ hg₂c hang
  set M := ∫ t in Ioi 1, psi c g t ^ 2 with hMd
  have hE : ∀ ξ ∈ Icc 2 k, energy (aP c χ) (psi c g) (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c g) ξ ≤ 6 * c * M := by
    intro ξ hξ
    have hk2 : 2 ≤ k := hξ.1.trans hξ.2
    have h := Cvs.Prolate.ProlateWindowMassIdentity.far_energy_le_rung hg hg₁ hg₂c hang hc hχ0 hχc hk2 ξ ⟨by linarith [hξ.1], hξ.2⟩
    exact h.trans (mul_le_mul_of_nonneg_left (Cvs.Prolate.RungTailIntegralMass.integral_sq_le_mass hg hg₁ hg₂c hang hc0
      (by linarith)) (by positivity))
  have hψ₁ := fun ξ (_ : ξ ∈ Icc (1 : ℝ) 2) => Cvs.Prolate.SincTopIsRung.hasDerivAt_psi (c := c) hgc ξ
  have hψ₁c : ContinuousOn (Cvs.Prolate.SlepianCommutingRelation.kint g (fun ξ s => -(c * s * sin (c * ξ * s)))) (Icc 1 2) :=
    fun ξ _ => (Cvs.Prolate.SincTopIsRung.hasDerivAt_psi₁ (c := c) hgc ξ).continuousAt.continuousWithinAt
  have h := Cvs.Prolate.TruncatedTailAboveOrbit.norm_fourier_posTail_le_hi (Ebar := 6 * c * M)
    (P₀ := 1 * ∫ s in (-1 : ℝ)..1, |g s|) (P₁ := |c| * ∫ s in (-1 : ℝ)..1, |g s|) (by linarith) hχ0 hχc.le hk ht
    hψc.continuousOn (fun ξ hξ => hψ ξ (by linarith [hξ.1])) (fun ξ _ => hu ξ) hE hψ₁ hψ₁c
    (fun ξ _ => abs_psi_le_L1 hgc) (fun ξ _ => abs_psi₁_le_L1 hgc)
  refine h.trans (le_of_eq ?_)
  unfold rungA
  rw [abs_of_pos hc0, one_mul, ← hMd, show 6 * c * M / c = 6 * M by field_simp]

/-! ### The span -/

variable {ι : Type} [Fintype ι]

theorem posTail_span (a : ι → ℝ) (ψ : ι → ℝ → ℝ) (k θ : ℝ) :
    posTail (fun ξ => ∑ i, a i * ψ i ξ) k θ = ∑ i, a i * posTail (ψ i) k θ := by
  simp only [posTail_eq_sum, Set.indicator_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

theorem contDiff_span (a : ι → ℝ) {g g₁ : ι → ℝ → ℝ} (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (c : ℝ) : ContDiff ℝ 1 (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
  ContDiff.sum fun i _ => contDiff_const.mul
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg i s hs).continuousAt.continuousWithinAt) c)

/-- **The span's truncated tail above the orbit frequency**: `‖𝓕(posTail Φ k)(t)‖ ≤ (Σ|aᵢ|Aᵢ(k))/|t|`. -/
theorem norm_fourier_posTail_span_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) {k t : ℝ} (hk : 1 ≤ k)
    (ht : 2 * c ^ 2 * k ^ 2 ≤ t ^ 2) :
    ‖𝓕 (Cvs.WeilForm.SelfConvolutionTransform.cf (Cvs.L2a.TailLogScaleTest.logScale
        (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k))) (t / (2 * π))‖
      ≤ (∑ i, |a i| * rungA c (g i) k) / |t| := by
  have he : posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k = fun θ => ∑ i, a i * posTail (psi c (g i)) k θ :=
    funext fun θ => posTail_span a (fun i => psi c (g i)) k θ
  have hint : ∀ i, Integrable (Cvs.L2a.TailLogScaleTest.logScale (posTail (psi c (g i)) k)) := fun i =>
    (Cvs.L2a.PositionTailAdmissible.admissible_posTail hk
      ((Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg i s hs).continuousAt.continuousWithinAt) c).contDiffOn)).2.1
  rw [he, Cvs.L2a.FarPartDirichletSplit.logScale_sum, Cvs.L2a.FarPartDirichletSplit.fourier_cf_sum Finset.univ a hint]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (norm_fourier_posTail_rung_le (hg i) (hg₁ i) (hg₂c i) (hang i) hc (hχ0 i) (hχc i) hk ht) (abs_nonneg _)

/-- **The span's truncated tail is nearly band-limited**: for `T ≥ 2c`, the mass of `posTail Φ k` above `kT` is at
most `(Σ|aᵢ|Aᵢ(k))²/(kT)`. -/
theorem highMass_posTail_span_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) {k T : ℝ} (hk : 1 ≤ k) (hT : 2 * c ≤ T) :
    (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k θ ^ 2)
        - Cvs.L2a.SpectralMassLevelLeak.specMass (posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k) (k * T)
      ≤ (∑ i, |a i| * rungA c (g i) k) ^ 2 / (k * T) := by
  have hc0 : 0 < c := by linarith
  have hT0 : 0 < T := by linarith
  have hk0 : 0 < k := by linarith
  obtain ⟨h2, h1, -⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hk (contDiff_span a hg c).contDiffOn
  refine Cvs.Prolate.TruncatedTailAboveOrbit.highMass_le (fun θ hθ => posTail_zero _ k hθ) h2 h1 (by positivity) fun t ht => ?_
  refine norm_fourier_posTail_span_le a hg hg₁ hg₂c hang hc hχ0 hχc hk ?_
  have h1' : 2 * c * k ≤ |t| := le_trans (by nlinarith) ht
  have h2' : (2 * c * k) ^ 2 ≤ t ^ 2 := by rw [← sq_abs t]; exact pow_le_pow_left₀ (by positivity) h1' 2
  nlinarith [sq_nonneg (c * k)]

/-! ### The norm of a truncated tail, mode by mode -/

/-- **The span envelope**: `Φ(ξ)² ≤ 8J P/ξ²` on `[2, X]`, `P = Σ aᵢ² ∫₁^∞ ψᵢ²`. -/
theorem span_sq_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) {X ξ : ℝ} (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hξ : ξ ∈ Icc 2 X) :
    (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ 8 * (Fintype.card ι : ℝ) * (∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) / ξ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hξ1 : 1 < ξ := by linarith [hξ.1]
  have hξ0 : 0 < ξ := by linarith
  have hp : 0 < ξ ^ 2 - 1 := by nlinarith [hξ.1]
  have hξ' : ξ ∈ Icc (6 / 5 : ℝ) X := ⟨by linarith [hξ.1], hξ.2⟩
  have htp := Cvs.Prolate.Envelope.RungCountEnvelope.two_point_le a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hξ' hξ'
  rw [Real.sqrt_mul_self hp.le] at htp
  have habs : |∑ i, a i * psi c (g i) ξ| ≤ ∑ i, |a i| * Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ i) (g i) ξ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Cvs.Prolate.Envelope.RungCountEnvelope.abs_psi_le_rungAmp hξ1 hc0 (hχc i)) (abs_nonneg _)
  have h0 : 0 ≤ ∑ i, |a i| * Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ i) (g i) ξ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (∑ i, a i * psi c (g i) ξ) ^ 2 ≤ (∑ i, |a i| * Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ i) (g i) ξ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hPX : ∑ i, a i ^ 2 * (∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
      ≤ ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Cvs.Prolate.RungTailIntegralMass.integral_sq_le_mass (hg i) (hg₁ i) (hg₂c i) (hang i) hc0 (by linarith)) (sq_nonneg _)
  have hJ : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hP0 : 0 ≤ ∑ i, a i ^ 2 * (∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have h6 : 6 * (Fintype.card ι : ℝ) / (ξ ^ 2 - 1) ≤ 8 * (Fintype.card ι : ℝ) / ξ ^ 2 := by
    rw [div_le_div_iff₀ hp (by positivity)]
    have : ξ ^ 2 ≥ 4 := by nlinarith [hξ.1]
    nlinarith
  calc (∑ i, a i * psi c (g i) ξ) ^ 2 ≤ (∑ i, |a i| * Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ i) (g i) ξ) ^ 2 := hsq
    _ = (∑ i, |a i| * Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ i) (g i) ξ)
          * (∑ j, |a j| * Cvs.Prolate.Envelope.RungCountEnvelope.rungAmp c (χ j) (g j) ξ) := sq _
    _ ≤ 6 * (Fintype.card ι : ℝ) / (ξ ^ 2 - 1) * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 := htp
    _ ≤ 8 * (Fintype.card ι : ℝ) / ξ ^ 2 * ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 :=
        mul_le_mul h6 hPX hP0 (by positivity)
    _ = _ := by ring

/-- `∫_1^k Φ² ≤ J Σ aᵢ² ∫₁^∞ ψᵢ²`. -/
theorem integral_span_sq_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) {k : ℝ} (hk : 1 ≤ k) :
    ∫ ξ in (1 : ℝ)..k, (∑ i, a i * psi c (g i) ξ) ^ 2
      ≤ (Fintype.card ι : ℝ) * ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 := by
  have hcont : ∀ i, Continuous (psi c (g i)) := fun i =>
    (Cvs.L2a.FullTailConvergence.contDiff_psi (fun s hs => (hg i s hs).continuousAt.continuousWithinAt) c).continuous
  have hpt : ∀ ξ, (∑ i, a i * psi c (g i) ξ) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (a i * psi c (g i) ξ) ^ 2 := by
    intro ξ
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => a i * psi c (g i) ξ)
    simpa [Finset.card_univ] using this
  have hi1 : IntervalIntegrable (fun ξ => (∑ i, a i * psi c (g i) ξ) ^ 2) volume 1 k :=
    (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  have hi2 : ∀ i, IntervalIntegrable (fun ξ => (a i * psi c (g i) ξ) ^ 2) volume 1 k := fun i =>
    (Continuous.continuousOn (by have := hcont i; fun_prop)).intervalIntegrable
  have hi3 : IntervalIntegrable (fun ξ => (Fintype.card ι : ℝ) * ∑ i, (a i * psi c (g i) ξ) ^ 2) volume 1 k :=
    (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  refine (intervalIntegral.integral_mono_on hk hi1 hi3 fun ξ _ => hpt ξ).trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun i _ => hi2 i]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (Cvs.Prolate.RungTailIntegralMass.integral_sq_le_mass (hg i) (hg₁ i) (hg₂c i) (hang i) hc hk)
    (sq_nonneg _)

/-- `∫_m^k dξ/ξ² ≤ 1/m` for `0 < m ≤ k`. -/
theorem integral_inv_sq_le {m k : ℝ} (hm : 0 < m) (hmk : m ≤ k) : ∫ ξ in m..k, 1 / ξ ^ 2 ≤ 1 / m := by
  have hpos : ∀ x ∈ uIcc m k, 0 < x := fun x hx => by rw [uIcc_of_le hmk] at hx; linarith [hx.1]
  have hd : ∀ x ∈ uIcc m k, HasDerivAt (fun x => -(1 / x)) (1 / x ^ 2) x := fun x hx => by
    have h := (hasDerivAt_inv (hpos x hx).ne').neg
    refine (h.congr_deriv (by field_simp)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [one_div]
  have hc : ContinuousOn (fun ξ : ℝ => 1 / ξ ^ 2) (uIcc m k) :=
    continuousOn_const.div (continuousOn_pow 2) fun x hx => pow_ne_zero 2 (hpos x hx).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  have : 0 < k := lt_of_lt_of_le hm hmk
  have : 0 ≤ 1 / k := by positivity
  linarith

/-- **The norm of a truncated tail**: for `k ≥ 1`, `∫_{θ>1} F_k² ≤ (1 + log k) J (1 + 8 log k) P`. Cauchy–Schwarz
over the modes with weights `1/m` gives `∫ F_k² ≤ H_k Σ_m ∫_m^k Φ²`; the first mode is at most `JP`, the others `8JP/m`. -/
theorem integral_posTail_sq_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hM : ∀ i, ∀ X : ℝ, 2 ≤ X → 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) {k : ℝ} (hk : 1 ≤ k) :
    ∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k θ ^ 2
      ≤ (1 + Real.log k) * ((Fintype.card ι : ℝ) * (1 + 8 * Real.log k)
          * ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦd
  set J : ℝ := (Fintype.card ι : ℝ) with hJd
  set P := ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 with hPd
  set n := ⌊k⌋₊ with hnd
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  have hΦc : Continuous Φ := (contDiff_span a hg c).continuous
  set f : ℕ → ℝ → ℝ := fun m => Set.indicator (Ioc 1 (k / m)) (fun θ => Φ (m * θ)) with hfd
  have hsum : ∀ θ, posTail Φ k θ = ∑ m ∈ Finset.Icc 1 n, f m θ := fun θ => posTail_eq_sum Φ k θ
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by have := Nat.floor_pos.mpr hk; omega)
  have hm0 : ∀ m ∈ Finset.Icc 1 n, (0 : ℝ) < m := fun m hm => by
    have := (Finset.mem_Icc.mp hm).1; exact_mod_cast this
  have hmk : ∀ m ∈ Finset.Icc 1 n, (m : ℝ) ≤ k := fun m hm =>
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans (Nat.floor_le hk0.le)
  -- each mode is square integrable on `(1, ∞)`
  have hfi : ∀ m ∈ Finset.Icc 1 n, IntegrableOn (fun θ => f m θ ^ 2) (Ioi 1) := by
    intro m _
    have e : (fun θ => f m θ ^ 2) = Set.indicator (Ioc 1 (k / m)) (fun θ => Φ (m * θ) ^ 2) := by
      funext θ; simp only [hfd, Set.indicator_apply]; split_ifs <;> simp
    rw [e]
    refine (integrable_indicator_iff measurableSet_Ioc).2 ?_ |>.integrableOn
    exact (Continuous.continuousOn (by fun_prop)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- the mode masses
  have hmode : ∀ m ∈ Finset.Icc 1 n, (m : ℝ) * ∫ θ in Ioi 1, f m θ ^ 2 = ∫ ξ in (m : ℝ)..k, Φ ξ ^ 2 := by
    intro m hm
    have hm0' := hm0 m hm
    have hkm : 1 ≤ k / m := by rw [le_div_iff₀ hm0']; linarith [hmk m hm]
    have e : (fun θ => f m θ ^ 2) = Set.indicator (Ioc 1 (k / m)) (fun θ => Φ (m * θ) ^ 2) := by
      funext θ; simp only [hfd, Set.indicator_apply]; split_ifs <;> simp
    rw [e, setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self,
      ← intervalIntegral.integral_of_le hkm,
      intervalIntegral.integral_comp_mul_left (fun ξ => Φ ξ ^ 2) hm0'.ne', mul_one,
      mul_div_cancel₀ k hm0'.ne', smul_eq_mul]
    field_simp
  -- the bound on each mode
  have hbd : ∀ m ∈ Finset.Icc 1 n,
      ∫ ξ in (m : ℝ)..k, Φ ξ ^ 2 ≤ (if m = 1 then J * P else 0) + (if m = 1 then 0 else 8 * J * P / m) := by
    intro m hm
    by_cases h1 : m = 1
    · subst h1
      simp only [if_true, add_zero, Nat.cast_one]
      exact integral_span_sq_le a hg hg₁ hg₂c hang hc0 hk
    · simp only [h1, if_false, zero_add]
      have hm2 : (2 : ℝ) ≤ m := by
        have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (show 2 ≤ m by omega)
      have hk2 : 2 ≤ k := hm2.trans (hmk m hm)
      have hpt : ∀ ξ ∈ Icc (m : ℝ) k, Φ ξ ^ 2 ≤ 8 * J * P * (1 / ξ ^ 2) := fun ξ hξ => by
        have := span_sq_le a hg hg₁ hg₂c hang hc hχ0 hχc hk2 (fun i => hM i k hk2) ⟨hm2.trans hξ.1, hξ.2⟩
        rw [mul_one_div]; exact this
      have hi1 : IntervalIntegrable (fun ξ => Φ ξ ^ 2) volume m k :=
        (Continuous.continuousOn (by fun_prop)).intervalIntegrable
      have hi2 : IntervalIntegrable (fun ξ => 8 * J * P * (1 / ξ ^ 2)) volume m k := by
        refine (continuousOn_const.mul (continuousOn_const.div (continuousOn_pow 2) fun x hx => ?_)).intervalIntegrable
        rw [uIcc_of_le (hmk m hm)] at hx
        exact pow_ne_zero 2 (by linarith [hx.1])
      refine (intervalIntegral.integral_mono_on (hmk m hm) hi1 hi2 hpt).trans ?_
      rw [intervalIntegral.integral_const_mul]
      calc 8 * J * P * ∫ ξ in (m : ℝ)..k, 1 / ξ ^ 2 ≤ 8 * J * P * (1 / m) :=
            mul_le_mul_of_nonneg_left (integral_inv_sq_le (hm0 m hm) (hmk m hm)) (by positivity)
        _ = 8 * J * P / m := by ring
  -- pointwise Cauchy–Schwarz
  set H := ∑ m ∈ Finset.Icc 1 n, ((m : ℝ))⁻¹ with hHd
  have hH : H ≤ 1 + Real.log k := Cvs.Prolate.TruncatedTailAboveOrbit.sum_inv_Icc_le hk
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun m hm => inv_nonneg.mpr (hm0 m hm).le
  have hcs : ∀ θ, posTail Φ k θ ^ 2 ≤ H * ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * f m θ ^ 2 := by
    intro θ
    rw [hsum θ]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun m hm => inv_nonneg.mpr (hm0 m hm).le)
      (fun m hm => mul_nonneg (hm0 m hm).le (sq_nonneg _)) fun m hm => ?_
    rw [← mul_assoc, inv_mul_cancel₀ (hm0 m hm).ne', one_mul]
  have hRi : IntegrableOn (fun θ => H * ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * f m θ ^ 2) (Ioi 1) :=
    (integrable_finsetSum _ fun m hm => (hfi m hm).const_mul _).const_mul H
  have hLi : IntegrableOn (fun θ => posTail Φ k θ ^ 2) (Ioi 1) := by
    have h := integrableOn_posTail_mul_dilate Φ (X := k) hΦc.continuousOn (k := 1) le_rfl
    simp only [Nat.cast_one, one_mul] at h
    exact h.congr_fun (fun θ _ => by ring) measurableSet_Ioi
  have hint := setIntegral_mono_on hLi hRi measurableSet_Ioi fun θ _ => hcs θ
  rw [MeasureTheory.integral_const_mul, integral_finsetSum _ fun m hm => (hfi m hm).const_mul _] at hint
  simp_rw [MeasureTheory.integral_const_mul] at hint
  have hsum2 : ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * ∫ θ in Ioi 1, f m θ ^ 2 ≤ J * (1 + 8 * Real.log k) * P := by
    rw [Finset.sum_congr rfl hmode]
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.Icc 1 n) 1 (fun _ => J * P)]
    have h1mem : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, hn1⟩
    simp only [h1mem, if_true]
    have hrest : ∑ m ∈ Finset.Icc 1 n, (if m = 1 then (0 : ℝ) else 8 * J * P / m)
        = 8 * J * P * (H - 1) := by
      have e : ∀ m ∈ Finset.Icc 1 n, (if m = 1 then (0 : ℝ) else 8 * J * P / m)
          = 8 * J * P * ((m : ℝ))⁻¹ - (if m = 1 then 8 * J * P else 0) := by
        intro m _
        by_cases h : m = 1
        · subst h; simp
        · simp [h, div_eq_mul_inv]
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.Icc 1 n) 1 (fun _ => 8 * J * P),
        ← Finset.mul_sum, ← hHd]
      simp only [h1mem, if_true]
      ring
    rw [hrest]
    have : 8 * J * P * (H - 1) ≤ 8 * J * P * Real.log k := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  calc ∫ θ in Ioi 1, posTail Φ k θ ^ 2 ≤ H * ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * ∫ θ in Ioi 1, f m θ ^ 2 := hint
    _ ≤ (1 + Real.log k) * (J * (1 + 8 * Real.log k) * P) := by
        have h0 : 0 ≤ ∑ m ∈ Finset.Icc 1 n, (m : ℝ) * ∫ θ in Ioi 1, f m θ ^ 2 :=
          Finset.sum_nonneg fun m hm => mul_nonneg (hm0 m hm).le
            (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
        exact mul_le_mul hH hsum2 h0 (by linarith [Real.log_nonneg hk])

end Cvs.L2a.RungSpanTailHighMass
