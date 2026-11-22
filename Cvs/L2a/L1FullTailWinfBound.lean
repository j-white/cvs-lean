import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.RungSpanTailHighMass
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WinfPositionLevels
import Cvs.Prolate.RungTailIntegralMass
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L1 on the full tail: `W_∞ ≤ B̄ N` on the rung span

Below a level `K` the level gap is at most `N_k ≤ 8JP(1 + log K)²` (Cvs.L2a.RungSpanTailHighMass); above it `WinfPositionLevels`'s per-level lemma with
`‖F_k − F‖² ≤ K1b/√k` and `RungSpanTailHighMass`'s high mass give `a₁/k + a₂k^{−1/2} + a₃k^{−1/4}`. With the pole `|Π₊| ≤ C_π√P`, a
floor `κP ≤ N` and the position log split at `Θ`, `W_∞ ≤ B̄N`, where `log K` and `log Θ` are logarithms of crude
constants over `N`.
-/

namespace Cvs.L2a.L1FullTailWinfBound

open Real Set MeasureTheory Filter
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.FullTailConvergence (fullTail BG K1b K1 C1_nonneg BG_nonneg)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.SpectralMassLevelLeak (specMass)

/-! ### The level integral, split at `K` -/

/-- `∫_K^∞ k^{−1−q} = K^{−q}/q` for `q > 0`, `K > 0`, with integrability. -/
theorem integral_Ioi_rpow_neg {K q : ℝ} (hK : 0 < K) (hq : 0 < q) :
    IntegrableOn (fun k : ℝ => k ^ (-1 - q)) (Ioi K) ∧ ∫ k in Ioi K, k ^ (-1 - q) = K ^ (-q) / q := by
  have hlt : -1 - q < -1 := by linarith
  refine ⟨integrableOn_Ioi_rpow_of_lt hlt hK, ?_⟩
  rw [integral_Ioi_rpow_of_lt hlt hK, show -1 - q + 1 = -q by ring]
  field_simp

/-- **The level integral of the majorant**: for `K ≥ 1` and `C₁, a₁, a₂, a₃ ≥ 0`, the function
`λ = C₁ 1_{(1,K]} + (a₁/k + a₂k^{−1/2} + a₃k^{−1/4}) 1_{(K,∞)}` has `λ/k` integrable on `(1, ∞)` and
`∫ λ/k = C₁ log K + a₁/K + 2a₂K^{−1/2} + 4a₃K^{−1/4}`. -/
theorem levels_majorant {K C₁ a₁ a₂ a₃ : ℝ} (hK : 1 ≤ K) :
    IntegrableOn (fun k => ((Ioc 1 K).indicator (fun _ => C₁) k
        + (Ioi K).indicator (fun k => a₁ * k ^ (-1 : ℝ) + a₂ * k ^ (-(1 / 2) : ℝ) + a₃ * k ^ (-(1 / 4) : ℝ)) k) / k)
        (Ioi 1)
      ∧ ∫ k in Ioi 1, ((Ioc 1 K).indicator (fun _ => C₁) k
        + (Ioi K).indicator (fun k => a₁ * k ^ (-1 : ℝ) + a₂ * k ^ (-(1 / 2) : ℝ) + a₃ * k ^ (-(1 / 4) : ℝ)) k) / k
        = C₁ * Real.log K + (a₁ / K + 2 * a₂ * K ^ (-(1 / 2) : ℝ) + 4 * a₃ * K ^ (-(1 / 4) : ℝ)) := by
  have hK0 : 0 < K := by linarith
  set u : ℝ → ℝ := fun k => C₁ * k⁻¹ with hud
  set v : ℝ → ℝ := fun k => a₁ * k ^ (-1 - 1 : ℝ) + a₂ * k ^ (-1 - 1 / 2 : ℝ) + a₃ * k ^ (-1 - 1 / 4 : ℝ) with hvd
  have heq : EqOn (fun k => ((Ioc 1 K).indicator (fun _ => C₁) k
        + (Ioi K).indicator (fun k => a₁ * k ^ (-1 : ℝ) + a₂ * k ^ (-(1 / 2) : ℝ) + a₃ * k ^ (-(1 / 4) : ℝ)) k) / k)
      (fun k => (Ioc 1 K).indicator u k + (Ioi K).indicator v k) (Ioi 1) := by
    intro k hk
    have hk0 : 0 < k := lt_trans one_pos hk
    simp only [Set.indicator_apply, hud, hvd]
    by_cases h1 : k ∈ Ioc 1 K
    · have h2 : k ∉ Ioi K := fun h => not_lt.mpr h1.2 h
      simp only [h1, h2, ite_true, ite_false, add_zero]; field_simp
    · by_cases h2 : k ∈ Ioi K
      · simp only [h1, h2, ite_true, ite_false, zero_add]
        have r : ∀ p : ℝ, k ^ (-1 - p) = k ^ (-p) / k := fun p => by
          rw [show -1 - p = -p + -1 by ring, rpow_add hk0, rpow_neg_one, div_eq_mul_inv]
        rw [r 1, r (1 / 2), r (1 / 4), rpow_neg_one]
        field_simp
      · simp only [h1, h2, ite_false, add_zero, zero_div]
  have hu : IntegrableOn u (Ioc 1 K) :=
    ((continuousOn_const.mul (continuousOn_inv₀.mono fun x (hx : x ∈ Icc 1 K) => (lt_of_lt_of_le one_pos hx.1).ne')).integrableOn_Icc
      (μ := volume) |>.mono_set Ioc_subset_Icc_self) |>.congr_fun (fun _ _ => rfl) measurableSet_Ioc
  obtain ⟨i1, e1⟩ := integral_Ioi_rpow_neg hK0 (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨i2, e2⟩ := integral_Ioi_rpow_neg hK0 (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨i3, e3⟩ := integral_Ioi_rpow_neg hK0 (show (0 : ℝ) < 1 / 4 by norm_num)
  have hv : IntegrableOn v (Ioi K) := ((i1.const_mul a₁).add (i2.const_mul a₂)).add (i3.const_mul a₃)
  have hui : Integrable ((Ioc 1 K).indicator u) := (integrable_indicator_iff measurableSet_Ioc).2 hu
  have hvi : Integrable ((Ioi K).indicator v) := (integrable_indicator_iff measurableSet_Ioi).2 hv
  refine ⟨IntegrableOn.congr_fun (show IntegrableOn (fun k => (Ioc 1 K).indicator u k + (Ioi K).indicator v k)
    (Ioi 1) volume from (hui.add hvi).integrableOn) heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_add hui.integrableOn hvi.integrableOn,
    setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr Ioc_subset_Ioi_self, Set.inter_eq_right.mpr (Ioi_subset_Ioi hK)]
  have hlog : ∫ k in Ioc 1 K, u k = C₁ * Real.log K := by
    rw [← intervalIntegral.integral_of_le hK, hud, intervalIntegral.integral_const_mul,
      integral_inv_of_pos one_pos hK0, div_one]
  have hvv : ∫ k in Ioi K, v k = a₁ / K + 2 * a₂ * K ^ (-(1 / 2) : ℝ) + 4 * a₃ * K ^ (-(1 / 4) : ℝ) := by
    have h12 : IntegrableOn (fun k : ℝ => a₁ * k ^ (-1 - 1 : ℝ) + a₂ * k ^ (-1 - 1 / 2 : ℝ)) (Ioi K) :=
      (i1.const_mul a₁).add (i2.const_mul a₂)
    calc ∫ k in Ioi K, v k
        = (∫ k in Ioi K, (a₁ * k ^ (-1 - 1 : ℝ) + a₂ * k ^ (-1 - 1 / 2 : ℝ)))
          + ∫ k in Ioi K, a₃ * k ^ (-1 - 1 / 4 : ℝ) := integral_add h12 (i3.const_mul a₃)
      _ = a₁ * (∫ k in Ioi K, k ^ (-1 - 1 : ℝ)) + a₂ * (∫ k in Ioi K, k ^ (-1 - 1 / 2 : ℝ))
          + a₃ * ∫ k in Ioi K, k ^ (-1 - 1 / 4 : ℝ) := by
            rw [integral_add (i1.const_mul a₁) (i2.const_mul a₂), MeasureTheory.integral_const_mul,
              MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ = _ := by rw [e1, e2, e3, rpow_neg_one]; field_simp
  rw [hlog, hvv]

/-! ### The two level bounds on the rung span -/

/-- `(1 + log k)² ≤ 25√k` for `k ≥ 1`. -/
theorem one_add_log_sq_le {k : ℝ} (hk : 1 ≤ k) : (1 + Real.log k) ^ 2 ≤ 25 * k ^ (1 / 2 : ℝ) := by
  have hk0 : 0 < k := by linarith
  have hl := Real.log_le_rpow_div hk0.le (show (0 : ℝ) < 1 / 4 by norm_num)
  have hl0 := Real.log_nonneg hk
  have h4 : 1 ≤ k ^ (1 / 4 : ℝ) := one_le_rpow hk (by norm_num)
  have h1 : 1 + Real.log k ≤ 5 * k ^ (1 / 4 : ℝ) := by
    have : Real.log k ≤ 4 * k ^ (1 / 4 : ℝ) := by
      calc Real.log k ≤ k ^ (1 / 4 : ℝ) / (1 / 4) := hl
        _ = 4 * k ^ (1 / 4 : ℝ) := by ring
    linarith
  have h2 : (k ^ (1 / 4 : ℝ)) ^ 2 = k ^ (1 / 2 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hk0.le]; norm_num
  calc (1 + Real.log k) ^ 2 ≤ (5 * k ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    _ = 25 * k ^ (1 / 2 : ℝ) := by rw [mul_pow, h2]; norm_num

variable {ι : Type} [Fintype ι]

/-- `α = Σ|aᵢ|·2(3∫|gᵢ| + 2c∫|gᵢ|)`, the crude edge part of `RungSpanTailHighMass`'s `Σ|aᵢ|Aᵢ(k)`. -/
noncomputable def alphaS (c : ℝ) (a : ι → ℝ) (g : ι → ℝ → ℝ) : ℝ :=
  ∑ i, |a i| * (2 * (3 * (∫ s in (-1 : ℝ)..1, |g i s|) + 2 * (c * ∫ s in (-1 : ℝ)..1, |g i s|)))

/-- `β = 74 Σ|aᵢ|√(6Mᵢ)`, the energy part. -/
noncomputable def betaS (c : ℝ) (a : ι → ℝ) (g : ι → ℝ → ℝ) : ℝ :=
  ∑ i, |a i| * (74 * √(6 * ∫ t in Ioi 1, psi c (g i) t ^ 2))

theorem sum_rungA_eq (c : ℝ) (a : ι → ℝ) (g : ι → ℝ → ℝ) (k : ℝ) :
    ∑ i, |a i| * Cvs.L2a.RungSpanTailHighMass.rungA c (g i) k = alphaS c a g + betaS c a g * (1 + Real.log k) := by
  unfold alphaS betaS Cvs.L2a.RungSpanTailHighMass.rungA
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem alphaS_nonneg {c : ℝ} (hc : 0 ≤ c) (a : ι → ℝ) (g : ι → ℝ → ℝ) : 0 ≤ alphaS c a g :=
  Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by
    have := intervalIntegral.integral_nonneg (μ := volume) (show (-1 : ℝ) ≤ 1 by norm_num)
      fun s _ => abs_nonneg (g i s)
    positivity)

theorem betaS_nonneg (c : ℝ) (a : ι → ℝ) (g : ι → ℝ → ℝ) : 0 ≤ betaS c a g :=
  Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by positivity)

/-- `K1b` of the span profile. -/
noncomputable def K1bS (c : ℝ) (a : ι → ℝ) (g g₁ g₂ : ι → ℝ → ℝ) : ℝ :=
  K1b c ((fun t => ∑ i, a i * g i t) 1 + (fun t => ∑ i, a i * g i t) (-1))
    (|(fun t => ∑ i, a i * g₁ i t) 1 - (fun t => ∑ i, a i * g₁ i t) (-1)|
      + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, a i * g₂ i t) s|)

/-- **Above `K`**: for `k ≥ 1`, at `T = 2c`,
`N_k − specMass F (kT) ≤ (2α²/T)k⁻¹ + (50β²/T + K1b)k^{−1/2} + 2√(N K1b)k^{−1/4}`. -/
theorem level_high_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ} {c : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) {k : ℝ} (hk : 1 ≤ k)
    (hN : 0 < ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2) :
    (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k θ ^ 2)
        - specMass (fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ)) (k * (2 * c))
      ≤ 2 * alphaS c a g ^ 2 / (2 * c) * k ^ (-1 : ℝ)
        + (50 * betaS c a g ^ 2 / (2 * c) + K1bS c a g g₁ g₂) * k ^ (-(1 / 2) : ℝ)
        + 2 * √((∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2) * K1bS c a g g₁ g₂)
          * k ^ (-(1 / 4) : ℝ) := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦd
  set N := ∫ θ in Ioi 1, fullTail Φ θ ^ 2 with hNd
  set Kb := K1bS c a g g₁ g₂ with hKbd
  set α := alphaS c a g
  set β := betaS c a g
  have hc0 : 0 < c := by linarith
  have hk0 : 0 < k := by linarith
  have hspan : Φ = psi c (fun t => ∑ i, a i * g i t) := Cvs.L2a.FullTailFloorLimit.span_eq a hg c
  have hG := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span a hg
  have hG₁ := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span a hg₁
  have hG₂ := Cvs.L2a.FullTailFloorLimit.continuousOn_span a hg₂c
  -- admissibility of the two tails
  obtain ⟨h2, h1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hG hG₁ hG₂ hc0
  rw [← hspan] at h2 h1
  obtain ⟨h2k, h1k, -⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hk
    (Cvs.L2a.RungSpanTailHighMass.contDiff_span a hg c).contDiffOn
  have hF0 : ∀ θ ≤ 1, fullTail Φ θ = 0 := fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ
  have hFk0 : ∀ θ ≤ 1, posTail Φ k θ = 0 := fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero _ k hθ
  -- the far part is small in `L²`
  have hKb0 : 0 ≤ Kb := by
    have h := (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hG hG₁ hG₂ hc0 (le_refl (1 : ℝ))).trans
      (Cvs.L2a.FullTailConvergence.K1_le hc0 _ _ (le_refl (1 : ℝ)))
    have h0 : 0 ≤ ∫ θ in Ioi 1, (posTail (psi c fun t => ∑ i, a i * g i t) 1 θ
        - fullTail (psi c fun t => ∑ i, a i * g i t) θ) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
    rw [Real.sqrt_one, div_one] at h
    exact h0.trans h
  have hgap : ∫ θ in Ioi 1, (posTail Φ k θ - fullTail Φ θ) ^ 2 ≤ Kb * k ^ (-(1 / 2) : ℝ) := by
    rw [hspan]
    refine (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hG hG₁ hG₂ hc0 hk).trans
      ((Cvs.L2a.FullTailConvergence.K1_le hc0 _ _ hk).trans (le_of_eq ?_))
    rw [rpow_neg hk0.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    rfl
  have hD0 : ∀ θ ≤ 1, (posTail Φ k - fullTail Φ) θ = 0 := fun θ hθ => by
    simp [hFk0 θ hθ, hF0 θ hθ]
  have hfar : specMass (posTail Φ k - fullTail Φ) (k * (2 * c)) ≤ (Kb * k ^ (-(1 / 2) : ℝ) / N) * N := by
    rw [div_mul_cancel₀ _ hN.ne']
    refine (Cvs.L2a.SpectralMassLevelLeak.specMass_le hD0 ?_ ?_ _).trans ?_
    · rw [Cvs.L2a.SpectralMassLevelLeak.logScale_sub]; exact h2k.sub h2
    · rw [Cvs.L2a.SpectralMassLevelLeak.logScale_sub]; exact h1k.sub h1
    · simpa only [Pi.sub_apply] using hgap
  have he : 0 ≤ Kb * k ^ (-(1 / 2) : ℝ) / N := by positivity
  have hlg := Cvs.L2a.WinfPositionLevels.level_gap_le hF0 h2 h1 h2k h1k he hfar
  have hhi := Cvs.L2a.RungSpanTailHighMass.highMass_posTail_span_le a hg hg₁ hg₂c hang hc hχ0 hχc hk (le_refl (2 * c))
  rw [sum_rungA_eq] at hhi
  -- the high mass, in powers of `k`
  have hα := alphaS_nonneg hc0.le a g
  have hβ := betaS_nonneg c a g
  have hhi' : (α + β * (1 + Real.log k)) ^ 2 / (k * (2 * c))
      ≤ 2 * α ^ 2 / (2 * c) * k ^ (-1 : ℝ) + 50 * β ^ 2 / (2 * c) * k ^ (-(1 / 2) : ℝ) := by
    have hsq : (α + β * (1 + Real.log k)) ^ 2 ≤ 2 * α ^ 2 + 2 * β ^ 2 * (25 * k ^ (1 / 2 : ℝ)) := by
      have h1' := one_add_log_sq_le hk
      have : (α + β * (1 + Real.log k)) ^ 2 ≤ 2 * α ^ 2 + 2 * (β * (1 + Real.log k)) ^ 2 := by
        nlinarith [sq_nonneg (α - β * (1 + Real.log k))]
      rw [mul_pow] at this
      nlinarith [sq_nonneg β]
    have hr1 : k ^ (-1 : ℝ) = 1 / k := by rw [rpow_neg_one, one_div]
    have hr2 : k ^ (-(1 / 2) : ℝ) = k ^ (1 / 2 : ℝ) / k := by
      rw [show -(1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, rpow_sub hk0, rpow_one]
    rw [hr1, hr2, div_le_iff₀ (by positivity)]
    have e : (2 * α ^ 2 / (2 * c) * (1 / k) + 50 * β ^ 2 / (2 * c) * (k ^ (1 / 2 : ℝ) / k)) * (k * (2 * c))
        = 2 * α ^ 2 + 2 * β ^ 2 * (25 * k ^ (1 / 2 : ℝ)) := by field_simp; ring
    rw [e]; exact hsq
  -- the leak term
  have hleak : (2 * √(Kb * k ^ (-(1 / 2) : ℝ) / N) + Kb * k ^ (-(1 / 2) : ℝ) / N) * N
      = 2 * √(N * Kb) * k ^ (-(1 / 4) : ℝ) + Kb * k ^ (-(1 / 2) : ℝ) := by
    set x := Kb * k ^ (-(1 / 2) : ℝ) with hxd
    have hx0 : 0 ≤ x := by positivity
    have hsN : 0 < √N := Real.sqrt_pos.mpr hN
    have hNN : √N * √N = N := Real.mul_self_sqrt hN.le
    have h4 : √(k ^ (-(1 / 2) : ℝ)) = k ^ (-(1 / 4) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← rpow_mul hk0.le]; norm_num
    have hs : √(x / N) * N = √(N * Kb) * k ^ (-(1 / 4) : ℝ) := by
      rw [Real.sqrt_div hx0, Real.sqrt_mul hN.le, hxd, Real.sqrt_mul hKb0, h4]
      nth_rewrite 2 [← hNN]
      field_simp
    rw [add_mul, mul_assoc, hs, div_mul_cancel₀ x hN.ne']
    ring
  rw [hleak] at hlg
  linarith

/-- **Below `K`**: for `1 < k ≤ K`, `N_k − specMass F (kT) ≤ 8JP(1 + log K)²`. -/
theorem level_low_le (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ} {c : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2)
    (hM : ∀ i, ∀ X : ℝ, 2 ≤ X → 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) {k K T : ℝ} (hk : 1 ≤ k) (hkK : k ≤ K) :
    (∫ θ in Ioi 1, posTail (fun ξ => ∑ i, a i * psi c (g i) ξ) k θ ^ 2)
        - specMass (fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ)) (k * T)
      ≤ 8 * (Fintype.card ι : ℝ) * (∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) * (1 + Real.log K) ^ 2 := by
  have h := Cvs.L2a.RungSpanTailHighMass.integral_posTail_sq_le a hg hg₁ hg₂c hang hc hχ0 hχc hM hk
  have hS := Cvs.L2a.SpectralMassLevelLeak.specMass_nonneg (fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ)) (k * T)
  have hL := Real.log_nonneg hk
  have hLK : Real.log k ≤ Real.log K := Real.log_le_log (by linarith) hkK
  have hJP : 0 ≤ (Fintype.card ι : ℝ) * ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
      (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _))
  have hpoly : (1 + Real.log k) * (1 + 8 * Real.log k) ≤ 8 * (1 + Real.log K) ^ 2 := by nlinarith
  have e : (1 + Real.log k) * ((Fintype.card ι : ℝ) * (1 + 8 * Real.log k)
        * ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2)
      = ((1 + Real.log k) * (1 + 8 * Real.log k))
        * ((Fintype.card ι : ℝ) * ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2) := by ring
  rw [e] at h
  have := mul_le_mul_of_nonneg_right hpoly hJP
  nlinarith

/-! ### L1 on the full tail -/

/-- The level cut `K = max(1, (D/N)²)`. -/
noncomputable def cutK (D N : ℝ) : ℝ := max 1 ((D / N) ^ 2)

/-- The position cut `Θ = max(1, B²/N)`. -/
noncomputable def cutΘ (B N : ℝ) : ℝ := max 1 (B ^ 2 / N)

/-- `K^{−1/2} ≤ N/D` and `K^{−1/4} ≤ √(N/D)` at `K = cutK D N`, `D, N > 0`. -/
theorem cutK_rpow_le {D N : ℝ} (hD : 0 < D) (hN : 0 < N) :
    cutK D N ^ (-(1 / 2) : ℝ) ≤ N / D ∧ cutK D N ^ (-(1 / 4) : ℝ) ≤ √(N / D) := by
  have hK1 : 1 ≤ cutK D N := le_max_left _ _
  have hK0 : 0 < cutK D N := by linarith
  have h2 : (D / N) ^ 2 ≤ cutK D N := le_max_right _ _
  have hs : D / N ≤ cutK D N ^ (1 / 2 : ℝ) := by
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow] at this
  have h12 : cutK D N ^ (-(1 / 2) : ℝ) ≤ N / D := by
    rw [rpow_neg hK0.le, ← one_div, div_le_div_iff₀ (by positivity) hD]
    have := mul_le_mul_of_nonneg_left hs hN.le
    rw [mul_div_cancel₀ D hN.ne'] at this
    linarith
  refine ⟨h12, ?_⟩
  have e : cutK D N ^ (-(1 / 4) : ℝ) = √(cutK D N ^ (-(1 / 2) : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← rpow_mul hK0.le]; norm_num
  rw [e]; exact Real.sqrt_le_sqrt h12

/-- **The `L1` constant** `B̄ = 2C_π/√κ + a(2c) + 57/c + 8J(1 + log K)³/κ + 10 + 2 log Θ`. -/
noncomputable def L1const (c κ J K Θ : ℝ) : ℝ :=
  2 * Cvs.Prolate.RungTailIntegralMass.piConst J c / √κ + archSymbol (2 * c) + 57 / c + 8 * J * (1 + Real.log K) ^ 3 / κ + 10
    + 2 * Real.log Θ

set_option maxHeartbeats 800000 in
/-- **L1 on the full tail**: for the rung span `Φ = Σ aᵢψᵢ` at `c ≥ 80` with a floor `κP ≤ N`, `N > 0`:
`W_∞(Φ) ≤ B̄·N` with `B̄ = L1const c κ J K Θ`, `K = cutK D N`, `Θ = cutΘ B_G N`, where `D` and `B_G` are crude
constants of the profiles. -/
theorem L1_Winf (a : ι → ℝ) {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ} {c κ : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hχ : Function.Injective χ)
    (hM : ∀ i, ∀ X : ℝ, 2 ≤ X → 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2) (hκ : 0 < κ)
    (hN : 0 < ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)
    (hfloor : κ * (∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2)
      ≤ ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2) :
    Cvs.L2a.FullTailWeilFormLimit.Winf (fun ξ => ∑ i, a i * psi c (g i) ξ)
      ≤ L1const c κ (Fintype.card ι)
          (cutK (2 * alphaS c a g ^ 2 / (2 * c) + 2 * (50 * betaS c a g ^ 2 / (2 * c) + K1bS c a g g₁ g₂)
              + K1bS c a g g₁ g₂ + ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2)
            (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2))
          (cutΘ (BG c ((fun t => ∑ i, a i * g i t) 1 + (fun t => ∑ i, a i * g i t) (-1))
              (|(fun t => ∑ i, a i * g₁ i t) 1 - (fun t => ∑ i, a i * g₁ i t) (-1)|
                + ∫ s in (-1 : ℝ)..1, |(fun t => ∑ i, a i * g₂ i t) s|))
            (∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2))
        * ∫ θ in Ioi 1, fullTail (fun ξ => ∑ i, a i * psi c (g i) ξ) θ ^ 2 := by
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦd
  set N := ∫ θ in Ioi 1, fullTail Φ θ ^ 2 with hNd
  set J : ℝ := (Fintype.card ι : ℝ) with hJd
  set P := ∑ i, a i ^ 2 * ∫ t in Ioi 1, psi c (g i) t ^ 2 with hPd
  set Kb := K1bS c a g g₁ g₂ with hKbd
  set a₁ := 2 * alphaS c a g ^ 2 / (2 * c) with ha₁
  set a₂ := 50 * betaS c a g ^ 2 / (2 * c) + Kb with ha₂
  set a₃ := 2 * √(N * Kb) with ha₃
  set D := a₁ + 2 * a₂ + Kb + N with hDd
  set K := cutK D N with hKd
  set G : ℝ → ℝ := fun t => ∑ i, a i * g i t with hGd
  set G₁ : ℝ → ℝ := fun t => ∑ i, a i * g₁ i t with hG₁d
  set G₂ : ℝ → ℝ := fun t => ∑ i, a i * g₂ i t with hG₂d
  set B := BG c (G 1 + G (-1)) (|G₁ 1 - G₁ (-1)| + ∫ s in (-1 : ℝ)..1, |G₂ s|) with hBd
  set Θ := cutΘ B N with hΘd
  have hc0 : 0 < c := by linarith
  have hspan : Φ = psi c G := Cvs.L2a.FullTailFloorLimit.span_eq a hg c
  have hG := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span a hg
  have hG₁ := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span a hg₁
  have hG₂ := Cvs.L2a.FullTailFloorLimit.continuousOn_span a hg₂c
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
    (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  have hKb0 : 0 ≤ Kb := by
    have h := (Cvs.L2a.FullTailConvergence.integral_sub_sq_le hG hG₁ hG₂ hc0 (le_refl (1 : ℝ))).trans
      (Cvs.L2a.FullTailConvergence.K1_le hc0 _ _ (le_refl (1 : ℝ)))
    have h0 : 0 ≤ ∫ θ in Ioi 1, (posTail (psi c G) 1 θ - fullTail (psi c G) θ) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
    rw [Real.sqrt_one, div_one] at h
    exact h0.trans h
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by have := betaS_nonneg c a g; positivity
  have hD : 0 < D := by positivity
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hPN : P ≤ N / κ := by rw [le_div_iff₀ hκ]; linarith
  -- the level majorant
  set C₁ := 8 * J * P * (1 + Real.log K) ^ 2 with hC₁
  obtain ⟨hlam, hlamv⟩ := levels_majorant (C₁ := C₁) (a₁ := a₁) (a₂ := a₂) (a₃ := a₃) hK1
  have hlev : ∀ k, 1 < k → (∫ θ in Ioi 1, posTail (psi c G) k θ ^ 2) - specMass (fullTail (psi c G)) (k * (2 * c))
      ≤ (Ioc 1 K).indicator (fun _ => C₁) k
        + (Ioi K).indicator (fun k => a₁ * k ^ (-1 : ℝ) + a₂ * k ^ (-(1 / 2) : ℝ) + a₃ * k ^ (-(1 / 4) : ℝ)) k := by
    intro k hk
    rw [← hspan]
    by_cases hkK : k ≤ K
    · rw [Set.indicator_of_mem (show k ∈ Ioc 1 K from ⟨hk, hkK⟩),
        Set.indicator_of_notMem (show k ∉ Ioi K from fun h => not_lt.mpr hkK h), add_zero]
      exact level_low_le a hg hg₁ hg₂c hang hc hχ0 hχc hM hk.le hkK
    · rw [Set.indicator_of_notMem (show k ∉ Ioc 1 K from fun h => hkK h.2),
        Set.indicator_of_mem (show k ∈ Ioi K from not_le.mp hkK), zero_add]
      exact level_high_le a hg hg₁ hg₂c hang hc hχ0 hχc hk.le hN
  have hT : 2 ≤ 2 * c := by linarith
  have hbr := Cvs.L2a.WinfPositionLevels.Winf_le_bracket hG hG₁ hG₂ hc0 hT _ hlam hlev
  rw [← hspan, hlamv] at hbr
  -- the level terms
  have hlow : C₁ * Real.log K ≤ 8 * J * (1 + Real.log K) ^ 3 / κ * N := by
    have hL := Real.log_nonneg hK1
    have h8 : 0 ≤ 8 * J * P := by positivity
    have h8J : 0 ≤ 8 * J := by positivity
    have h3 : 0 ≤ (1 + Real.log K) ^ 3 := by positivity
    calc C₁ * Real.log K = 8 * J * P * ((1 + Real.log K) ^ 2 * Real.log K) := by rw [hC₁]; ring
      _ ≤ 8 * J * P * ((1 + Real.log K) ^ 2 * (1 + Real.log K)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)) h8
      _ = 8 * J * P * (1 + Real.log K) ^ 3 := by ring
      _ ≤ 8 * J * (N / κ) * (1 + Real.log K) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPN h8J) h3
      _ = 8 * J * (1 + Real.log K) ^ 3 / κ * N := by ring
  obtain ⟨hK12, hK14⟩ := cutK_rpow_le hD hN
  have htail : a₁ / K + 2 * a₂ * K ^ (-(1 / 2) : ℝ) + 4 * a₃ * K ^ (-(1 / 4) : ℝ) ≤ 9 * N := by
    have hinv : 1 / K ≤ K ^ (-(1 / 2) : ℝ) := by
      rw [rpow_neg hK0.le, one_div]
      exact inv_anti₀ (by positivity) (rpow_le_self_of_one_le hK1 (by norm_num))
    have h1 : a₁ / K ≤ a₁ * (N / D) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left (hinv.trans hK12) ha₁0
    have h2 : 2 * a₂ * K ^ (-(1 / 2) : ℝ) ≤ 2 * a₂ * (N / D) := mul_le_mul_of_nonneg_left hK12 (by positivity)
    have h3 : 4 * a₃ * K ^ (-(1 / 4) : ℝ) ≤ 4 * a₃ * √(N / D) := mul_le_mul_of_nonneg_left hK14 (by positivity)
    have h4 : (a₁ + 2 * a₂) * (N / D) ≤ N := by
      rw [mul_div_assoc']; rw [div_le_iff₀ hD]; nlinarith
    have h5 : 4 * a₃ * √(N / D) ≤ 8 * N := by
      rw [ha₃, Real.sqrt_mul hN.le, Real.sqrt_div hN.le]
      have hsD : 0 < √D := Real.sqrt_pos.mpr hD
      have hsN : √N * √N = N := Real.mul_self_sqrt hN.le
      have hKbD : √Kb ≤ √D := Real.sqrt_le_sqrt (by linarith)
      rw [show 4 * (2 * (√N * √Kb)) * (√N / √D) = 8 * (√N * √N) * (√Kb / √D) by ring, hsN]
      have : √Kb / √D ≤ 1 := by rw [div_le_one hsD]; exact hKbD
      nlinarith
    nlinarith
  -- the pole
  have hpole : 2 * Cvs.L2a.FullTailPoleChannel.piPlus Φ * (∫ θ in Ioi 1, fullTail Φ θ / θ)
      ≤ 2 * Cvs.Prolate.RungTailIntegralMass.piConst J c / √κ * N := by
    have hpi := Cvs.Prolate.RungTailIntegralMass.abs_piPlus_span_le a hg hg₁ hg₂c hang hc hχ0 hχc hχ
    have hFm : Measurable (fullTail Φ) := by
      rw [hspan]; exact Cvs.L2a.FullTailConvergence.measurable_fullTail hG hG₁ hG₂ hc0
    have hFB : ∀ θ, 0 < θ → |fullTail Φ θ| ≤ B / θ := fun θ hθ => by
      rw [hspan]; exact Cvs.L2a.FullTailConvergence.abs_fullTail_le hG hG₁ hG₂ hc0 hθ
    have hw : ∀ θ, 0 < θ → |(1 / θ : ℝ)| ≤ 1 / θ := fun θ hθ => by rw [abs_of_pos (by positivity)]
    have hcs := Cvs.L2a.FullTailConvergence.abs_setIntegral_mul_le (f := fullTail Φ) (w := fun θ => 1 / θ)
      (Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hFm hFB)
      (Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le (measurable_const.div measurable_id) hw)
      (Cvs.L2a.FullTailConvergence.integrableOn_mul_of_le hFm (measurable_const.div measurable_id) hFB hw)
    have hw2 : ∫ θ in Ioi (1 : ℝ), (1 / θ) ^ 2 = 1 := by
      have h := Cvs.L2a.FullTailConvergence.integral_one_div_sq (a := (1 : ℝ)) one_pos
      rw [div_one] at h
      calc ∫ θ in Ioi (1 : ℝ), (1 / θ) ^ 2 = ∫ θ in Ioi (1 : ℝ), 1 / θ ^ 2 := by
            congr 1; funext θ; rw [div_pow, one_pow]
        _ = 1 := h
    rw [hw2, Real.sqrt_one, mul_one] at hcs
    have he : ∫ θ in Ioi 1, fullTail Φ θ / θ = ∫ θ in Ioi 1, fullTail Φ θ * (1 / θ) :=
      setIntegral_congr_fun measurableSet_Ioi fun θ _ => by ring
    rw [he]
    have hsP : √P ≤ √N / √κ := by rw [← Real.sqrt_div' _ hκ.le]; exact Real.sqrt_le_sqrt hPN
    have hπ0 : 0 ≤ Cvs.Prolate.RungTailIntegralMass.piConst J c := by unfold Cvs.Prolate.RungTailIntegralMass.piConst; positivity
    have hsN : √N * √N = N := Real.mul_self_sqrt hN.le
    calc 2 * Cvs.L2a.FullTailPoleChannel.piPlus Φ * (∫ θ in Ioi 1, fullTail Φ θ * (1 / θ))
        ≤ 2 * (|Cvs.L2a.FullTailPoleChannel.piPlus Φ| * |∫ θ in Ioi 1, fullTail Φ θ * (1 / θ)|) := by
          rw [← abs_mul]; nlinarith [le_abs_self (Cvs.L2a.FullTailPoleChannel.piPlus Φ * ∫ θ in Ioi 1, fullTail Φ θ * (1 / θ)),
            mul_assoc (2 : ℝ) (Cvs.L2a.FullTailPoleChannel.piPlus Φ) (∫ θ in Ioi 1, fullTail Φ θ * (1 / θ))]
      _ ≤ 2 * ((Cvs.Prolate.RungTailIntegralMass.piConst J c * (√N / √κ)) * √N) := by
          gcongr
          exact hpi.trans (mul_le_mul_of_nonneg_left hsP hπ0)
      _ = 2 * Cvs.Prolate.RungTailIntegralMass.piConst J c / √κ * (√N * √N) := by ring
      _ = _ := by rw [hsN]
  -- the position log
  have hlog : ∫ θ in Ioi 1, Real.log θ * fullTail Φ θ ^ 2 ≤ (2 * Real.log Θ + 1) * N := by
    have hFm : Measurable (fullTail Φ) := by
      rw [hspan]; exact Cvs.L2a.FullTailConvergence.measurable_fullTail hG hG₁ hG₂ hc0
    have hFB : ∀ θ, 0 < θ → |fullTail Φ θ| ≤ B / θ := fun θ hθ => by
      rw [hspan]; exact Cvs.L2a.FullTailConvergence.abs_fullTail_le hG hG₁ hG₂ hc0 hθ
    have hΘ1 : 1 ≤ Θ := le_max_left _ _
    have h := Cvs.L2a.WinfPositionLevels.integral_log_mul_sq_le hFm hFB hΘ1
    have hBΘ : B ^ 2 / Θ ≤ N := by
      rcases le_or_gt 1 (B ^ 2 / N) with h1 | h1
      · have : Θ = B ^ 2 / N := max_eq_right h1
        rw [this, div_div_cancel₀]
        intro hB; rw [hB, zero_div] at h1; linarith
      · have : Θ = 1 := max_eq_left h1.le
        rw [this, div_one]; rw [div_lt_one hN] at h1; exact h1.le
    have hlΘ := Real.log_nonneg hΘ1
    have : B ^ 2 * ((1 + Real.log Θ) / Θ) ≤ N * (1 + Real.log Θ) := by
      rw [show B ^ 2 * ((1 + Real.log Θ) / Θ) = B ^ 2 / Θ * (1 + Real.log Θ) by ring]
      exact mul_le_mul_of_nonneg_right hBΘ (by linarith)
    nlinarith
  -- the arch bracket at `T = 2c`
  have harch : (archSymbol (2 * c) + 114 / (2 * c)) * N = (archSymbol (2 * c) + 57 / c) * N := by
    congr 2; field_simp; norm_num
  have hfinal : L1const c κ J K Θ * N
      = 2 * Cvs.Prolate.RungTailIntegralMass.piConst J c / √κ * N + (archSymbol (2 * c) + 57 / c) * N
        + 8 * J * (1 + Real.log K) ^ 3 / κ * N + 9 * N + (2 * Real.log Θ + 1) * N := by
    unfold L1const; ring
  rw [hfinal]
  linarith [hbr, hpole, hlow, htail, hlog, harch]

end Cvs.L2a.L1FullTailWinfBound
