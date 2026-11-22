import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.PositionTailAdmissible
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.SpectralMassLevelLeak
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WinfPositionLevels
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
# `W_∞` with a high mass decaying like `k^{−1/2}`

an earlier result with the high-mass hypothesis `N_k − specMass F_k (kT) ≤ hNk^{−1/2}`: the level majorant is
`(hk^{−1/2} + 2√r k^{−1/4} + rk^{−1/2})N`, so `W_∞ ≤ 2Π₊∫F/θ + (a(2c) + 114/(2c) + 2h + 8√r + 4r)N`; and against a
scale `M ≥ 0` with `N > 0`, `W_∞ ≤ 2Π₊∫F/θ + (a(2c) + 114/(2c))N + 2hM + 4√r(M + N) + 4rM`.
-/

noncomputable section

namespace Cvs.L2a.WinfHighMassDecay

open Real Set MeasureTheory Filter
open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.L2a.PositionTruncatedTail (posTail)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.SpectralMassLevelLeak (specMass)

/-- **`W_∞ ≤ (a(2c) + O(1))N` from an `N`-relative rate and a `k^{−1/2}` high mass.** -/
theorem Winf_le_rel {g g₁ g₂ : ℝ → ℝ} {c r h : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 1 ≤ c) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (hrate : ∀ k, 1 < k → ∫ θ in Ioi 1, (posTail (psi c g) k θ - fullTail (psi c g) θ) ^ 2
      ≤ r * (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) * k ^ (-(1 / 2) : ℝ))
    (hhigh : ∀ k, 1 < k → (∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass (posTail (psi c g) k) (k * (2 * c))
      ≤ h * (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) * k ^ (-(1 / 2) : ℝ)) :
    Cvs.L2a.FullTailWeilFormLimit.Winf (psi c g)
      ≤ 2 * Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) * (∫ θ in Ioi 1, fullTail (psi c g) θ / θ)
        + (archSymbol (2 * c) + 114 / (2 * c) + 2 * h + 8 * √r + 4 * r) * (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) := by
  have hc0 : 0 < c := by linarith
  set Φ := psi c g with hΦ
  set F := fullTail Φ with hF
  set N := ∫ θ in Ioi 1, F θ ^ 2 with hN
  have hN0 : 0 ≤ N := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  obtain ⟨h2, h1⟩ := Cvs.L2a.FullTailConvergence.memLp_logScale_fullTail hg hg₁ hg₂c hc0
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hΦd : ContDiff ℝ 1 Φ := Cvs.L2a.FullTailConvergence.contDiff_psi hgc c
  have hF0 : ∀ θ ≤ 1, F θ = 0 := fun θ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ
  -- the level majorant
  set lam : ℝ → ℝ := fun k => (h * k ^ (-(1 / 2) : ℝ) + 2 * √r * k ^ (-(1 / 4) : ℝ) + r * k ^ (-(1 / 2) : ℝ)) * N
    with hlamd
  have hlev : ∀ k, 1 < k → (∫ θ in Ioi 1, posTail Φ k θ ^ 2) - specMass F (k * (2 * c)) ≤ lam k := fun k hk => by
    have hk0 : 0 < k := by linarith
    obtain ⟨h2k, h1k, -⟩ := Cvs.L2a.PositionTailAdmissible.admissible_posTail hk.le hΦd.contDiffOn
    have hFk0 : ∀ θ ≤ 1, posTail Φ k θ = 0 := fun θ hθ => Cvs.L2a.PositionTruncatedTail.posTail_zero _ k hθ
    have hD0 : ∀ θ ≤ 1, (posTail Φ k - F) θ = 0 := fun θ hθ => by simp [hFk0 θ hθ, hF0 θ hθ]
    have he : 0 ≤ r * k ^ (-(1 / 2) : ℝ) := by positivity
    have hfar : specMass (posTail Φ k - F) (k * (2 * c)) ≤ r * k ^ (-(1 / 2) : ℝ) * N := by
      refine (Cvs.L2a.SpectralMassLevelLeak.specMass_le hD0 ?_ ?_ _).trans ?_
      · rw [Cvs.L2a.SpectralMassLevelLeak.logScale_sub]; exact h2k.sub h2
      · rw [Cvs.L2a.SpectralMassLevelLeak.logScale_sub]; exact h1k.sub h1
      · have := hrate k hk
        simp only [Pi.sub_apply]
        calc _ ≤ r * N * k ^ (-(1 / 2) : ℝ) := this
          _ = r * k ^ (-(1 / 2) : ℝ) * N := by ring
    have hlg := Cvs.L2a.WinfPositionLevels.level_gap_le hF0 h2 h1 h2k h1k he hfar
    have hhi := hhigh k hk
    have h4 : √(r * k ^ (-(1 / 2) : ℝ)) = √r * k ^ (-(1 / 4) : ℝ) := by
      rw [Real.sqrt_mul hr, Real.sqrt_eq_rpow (k ^ _), ← rpow_mul hk0.le]; norm_num
    have hk1 : h * N * k ^ (-(1 / 2) : ℝ) = h * k ^ (-(1 / 2) : ℝ) * N := by ring
    rw [h4] at hlg
    simp only [hlamd]
    nlinarith [hlg, hhi, hk1]
  -- its level integral
  have hI1 := (Cvs.L2a.L1FullTailWinfBound.integral_Ioi_rpow_neg (K := 1) one_pos (q := 1) one_pos)
  have hI2 := (Cvs.L2a.L1FullTailWinfBound.integral_Ioi_rpow_neg (K := 1) one_pos (q := 1 / 4) (by norm_num))
  have hI3 := (Cvs.L2a.L1FullTailWinfBound.integral_Ioi_rpow_neg (K := 1) one_pos (q := 1 / 2) (by norm_num))
  have hdiv : EqOn (fun k => lam k / k)
      (fun k => (h * k ^ (-1 - 1 / 2 : ℝ) + 2 * √r * k ^ (-1 - 1 / 4 : ℝ) + r * k ^ (-1 - 1 / 2 : ℝ)) * N) (Ioi 1) :=
    fun k hk => by
      have hk0 : (0 : ℝ) < k := lt_trans one_pos hk
      simp only [hlamd]
      have e2 : k ^ (-1 - 1 / 4 : ℝ) = k ^ (-(1 / 4) : ℝ) / k := by
        rw [show (-1 - 1 / 4 : ℝ) = -(1 / 4) - 1 by ring, rpow_sub hk0, rpow_one]
      have e3 : k ^ (-1 - 1 / 2 : ℝ) = k ^ (-(1 / 2) : ℝ) / k := by
        rw [show (-1 - 1 / 2 : ℝ) = -(1 / 2) - 1 by ring, rpow_sub hk0, rpow_one]
      rw [e2, e3]; field_simp
  have hint : IntegrableOn
      (fun k => (h * k ^ (-1 - 1 / 2 : ℝ) + 2 * √r * k ^ (-1 - 1 / 4 : ℝ) + r * k ^ (-1 - 1 / 2 : ℝ)) * N) (Ioi 1) :=
    (((hI3.1.const_mul h).add (hI2.1.const_mul (2 * √r))).add (hI3.1.const_mul r)).mul_const N
  have hlam : IntegrableOn (fun k => lam k / k) (Ioi 1) := hint.congr_fun hdiv.symm measurableSet_Ioi
  have hlamI : ∫ k in Ioi 1, lam k / k = (2 * h + 8 * √r + 2 * r) * N := by
    have i1 : IntegrableOn (fun a : ℝ => h * a ^ (-1 - 1 / 2 : ℝ)) (Ioi 1) := hI3.1.const_mul h
    have i2 : IntegrableOn (fun a : ℝ => 2 * √r * a ^ (-1 - 1 / 4 : ℝ)) (Ioi 1) := hI2.1.const_mul _
    have i3 : IntegrableOn (fun a : ℝ => r * a ^ (-1 - 1 / 2 : ℝ)) (Ioi 1) := hI3.1.const_mul r
    have i12 : IntegrableOn (fun a : ℝ => h * a ^ (-1 - 1 / 2 : ℝ) + 2 * √r * a ^ (-1 - 1 / 4 : ℝ)) (Ioi 1) := i1.add i2
    rw [setIntegral_congr_fun measurableSet_Ioi hdiv, integral_mul_const, integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul, hI2.2, hI3.2]
    simp only [one_rpow]; ring
  -- the position log
  have hlog : ∫ θ in Ioi 1, Real.log θ * F θ ^ 2 ≤ 2 * r * N := by
    refine (Cvs.L2a.WinfPositionLevels.integral_log_le_gaps hg hg₁ hg₂c hc0).trans ?_
    have hgi := Cvs.L2a.WinfPositionLevels.integrableOn_gap hg hg₁ hg₂c hc0
    have hmaj : IntegrableOn (fun k : ℝ => r * N * k ^ (-1 - 1 / 2 : ℝ)) (Ioi 1) := hI3.1.const_mul (r * N)
    calc _ ≤ ∫ k in Ioi 1, r * N * k ^ (-1 - 1 / 2 : ℝ) := by
          refine setIntegral_mono_on hgi hmaj measurableSet_Ioi fun k (hk : 1 < k) => ?_
          have hk0 : (0 : ℝ) < k := lt_trans one_pos hk
          have e : (∫ θ in Ioi 1, (F θ - posTail Φ k θ) ^ 2)
              = ∫ θ in Ioi 1, (posTail Φ k θ - F θ) ^ 2 := by congr 1; funext θ; ring
          rw [e, div_le_iff₀ hk0]
          have e3 : k ^ (-1 - 1 / 2 : ℝ) * k = k ^ (-(1 / 2) : ℝ) := by
            rw [show (-1 - 1 / 2 : ℝ) = -(1 / 2) - 1 by ring, rpow_sub hk0, rpow_one]; field_simp
          calc _ ≤ r * N * k ^ (-(1 / 2) : ℝ) := hrate k hk
            _ = r * N * k ^ (-1 - 1 / 2 : ℝ) * k := by rw [mul_assoc (r * N) _ k, e3]
      _ = 2 * r * N := by rw [integral_const_mul, hI3.2]; norm_num; ring
  have hB := Cvs.L2a.WinfPositionLevels.Winf_le_bracket hg hg₁ hg₂c hc0 (T := 2 * c) (by linarith) lam hlam hlev
  rw [hlamI] at hB
  nlinarith [hB, hlog]

/-- **`W_∞` from a rate and a `k^{−1/2}` high mass relative to a scale `M`.** -/
theorem Winf_le_relM {g g₁ g₂ : ℝ → ℝ} {c r h M : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 1 ≤ c) (hr : 0 ≤ r) (hh : 0 ≤ h) (hM : 0 ≤ M)
    (hN : 0 < ∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)
    (hrate : ∀ k, 1 < k → ∫ θ in Ioi 1, (posTail (psi c g) k θ - fullTail (psi c g) θ) ^ 2
      ≤ r * M * k ^ (-(1 / 2) : ℝ))
    (hhigh : ∀ k, 1 < k → (∫ θ in Ioi 1, posTail (psi c g) k θ ^ 2) - specMass (posTail (psi c g) k) (k * (2 * c))
      ≤ h * M * k ^ (-(1 / 2) : ℝ)) :
    Cvs.L2a.FullTailWeilFormLimit.Winf (psi c g)
      ≤ 2 * Cvs.L2a.FullTailPoleChannel.piPlus (psi c g) * (∫ θ in Ioi 1, fullTail (psi c g) θ / θ)
        + (archSymbol (2 * c) + 114 / (2 * c)) * (∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2)
        + 2 * h * M + 4 * √r * (M + ∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2) + 4 * r * M := by
  set N := ∫ θ in Ioi 1, fullTail (psi c g) θ ^ 2 with hNd
  have hB := Winf_le_rel hg hg₁ hg₂c hc (r := r * M / N) (h := h * M / N)
    (by positivity) (by positivity)
    (fun k hk => by
      have := hrate k hk
      calc _ ≤ r * M * k ^ (-(1 / 2) : ℝ) := this
        _ = r * M / N * N * k ^ (-(1 / 2) : ℝ) := by field_simp)
    (fun k hk => by
      have := hhigh k hk
      calc _ ≤ h * M * k ^ (-(1 / 2) : ℝ) := this
        _ = h * M / N * N * k ^ (-(1 / 2) : ℝ) := by field_simp)
  -- `8√(rM/N)·N = 8√(rMN) ≤ 4√r(M + N)`
  have hs : √(r * M / N) * N = √r * √(M * N) := by
    have h1 : (√(r * M / N) * N) ^ 2 = (√r * √(M * N)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hr, Real.sq_sqrt (by positivity)]
      field_simp
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h1
  have hAMGM : √(M * N) ≤ (M + N) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg (M - N)]
  have hk : (archSymbol (2 * c) + 114 / (2 * c) + 2 * (h * M / N) + 8 * √(r * M / N) + 4 * (r * M / N)) * N
      = (archSymbol (2 * c) + 114 / (2 * c)) * N + 2 * h * M + 8 * (√(r * M / N) * N) + 4 * r * M := by
    field_simp
  have hsr : 0 ≤ √r := Real.sqrt_nonneg r
  have h8 : 8 * (√(r * M / N) * N) ≤ 4 * √r * (M + N) := by
    rw [hs]; nlinarith [mul_le_mul_of_nonneg_left hAMGM hsr]
  rw [hk] at hB
  linarith

end Cvs.L2a.WinfHighMassDecay
