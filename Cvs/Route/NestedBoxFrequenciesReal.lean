import Mathlib
import Cvs.Finite.ZeroSideGramMatrix
import Cvs.Route.NestedBoxLevyStep
import Cvs.Route.OneCellLaplaceTransform
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.LogEnvelopeSquareSummable
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The induction's missing piece is the reality of the frequencies
`ZeroSideG`: `G(L) = ∑_ρ m_ρ Re[4 sin²(z_ρ L/2)/z_ρ²]`, `z_ρ = zPoint ρ`. `FrequenciesReal`: every `z_ρ` is real.
Given both, the zeros themselves index a Lévy representation (weights `2 m_ρ/γ²`), so RH (Cvs.Route.NestedBoxLevyStep). RH gives
`FrequenciesReal`; so relative to `ZeroSideG` the step of Cvs.Route.NestedBoxInduction is exactly the reality of the frequencies.
-/

noncomputable section

open Real

namespace Cvs.Route.NestedBoxFrequenciesReal
open Cvs.ZeroCounting

open Cvs.Route.OneCellLaplaceTransform (G)

/-- The zero side of the one-cell function (measured to `1e-6` with 8000 zeros at four `L`). -/
def ZeroSideG : Prop :=
  ∀ L, 0 ≤ L → G L = ∑' ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.Criterion.divisorWeight ρ : ℝ)
    * (4 * (Complex.sin (Cvs.ZeroCounting.zPoint ρ * L / 2) ^ 2 / Cvs.ZeroCounting.zPoint ρ ^ 2)).re

/-- Every zero's frequency is real. -/
def FrequenciesReal : Prop := ∀ ρ : Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet, (Cvs.ZeroCounting.zPoint ρ).im = 0

/-- `(2/γ²)(1 − cos γL) ≤ (8 + 2L²)/(1 + γ²)` for every real `γ` (both sides vanish-safe at `γ = 0`). -/
theorem term_le (g L : ℝ) : 2 / g ^ 2 * (1 - Real.cos (g * L)) ≤ (8 + 2 * L ^ 2) / (1 + g ^ 2) := by
  have hc1 := Real.cos_le_one (g * L)
  have hcq := Real.one_sub_sq_div_two_le_cos (x := g * L)
  have hc2 := Real.neg_one_le_cos (g * L)
  rcases eq_or_ne g 0 with hg | hg
  · subst hg; simp; positivity
  · have hg2 : 0 < g ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hg2 (by positivity)]
    rcases le_total 1 (g ^ 2) with h | h
    · nlinarith [sq_nonneg L]
    · nlinarith [sq_nonneg L, sq_nonneg (g * L), mul_nonneg hg2.le (sq_nonneg L)]

theorem one_div_le_two_phi_sq (g : ℝ) :
    1 / (1 + g ^ 2) ≤ 2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |g| ^ 2 := by
  have h1 := Cvs.Zeta.LogEnvelopeSquareSummable.one_div_le_phi (abs_nonneg g)
  have h0 : 0 < 1 + |g| := by positivity
  have hsq : (1 / (1 + |g|)) ^ 2 ≤ Cvs.Zeta.LogEnvelopeSquareSummable.phi |g| ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have hab : (1 + |g|) ^ 2 ≤ 2 * (1 + g ^ 2) := by nlinarith [sq_abs g, sq_nonneg (|g| - 1)]
  calc 1 / (1 + g ^ 2) ≤ 2 / (1 + |g|) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    _ = 2 * (1 / (1 + |g|)) ^ 2 := by field_simp
    _ ≤ _ := by linarith

/-- With real frequencies, one zero's term is `(2/γ²)(1 − cos γL)`, `γ = Re z = Im ρ`. -/
theorem term_real {z : ℂ} (hz : z.im = 0) (L : ℝ) :
    (4 * (Complex.sin (z * L / 2) ^ 2 / z ^ 2)).re = 2 / z.re ^ 2 * (1 - Real.cos (z.re * L)) := by
  have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz])
  rw [hzr]
  have : (z.re : ℂ) * (L : ℂ) / 2 = ((z.re * L / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_sin, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re, Real.sin_sq_eq_half_sub]
  have : 2 * (z.re * L / 2) = z.re * L := by ring
  rw [this]; ring

/-- **[C], proved**: the zero side with real frequencies is a Lévy representation indexed by the zeros. -/
def levyRep (hA : ZeroSideG) (hB : FrequenciesReal) : Cvs.Route.NestedBoxLevyStep.LevyRep Cvs.Zeta.GaussKernel.AdmissibleKernel.nonTrivialZeroSet where
  w ρ := (Cvs.Criterion.divisorWeight ρ : ℝ) * (2 / (Cvs.ZeroCounting.zPoint ρ).re ^ 2)
  γ ρ := (Cvs.ZeroCounting.zPoint ρ).re
  w_nonneg ρ := mul_nonneg (Nat.cast_nonneg _) (by positivity)
  summable_term L _ := by
    refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
      (by linarith [Real.cos_le_one ((Cvs.ZeroCounting.zPoint ρ).re * L)])) (fun ρ => ?_)
      (Cvs.Zeta.LogEnvelopeSquareSummable.summable_divisorWeight_phi_sq.mul_left (2 * (8 + 2 * L ^ 2)))
    have hre : (Cvs.ZeroCounting.zPoint ρ).re = ((ρ : ℂ)).im := Cvs.Finite.ZeroSideGramMatrix.zPoint_re ρ
    have h1 := term_le (Cvs.ZeroCounting.zPoint ρ).re L
    have h2 := one_div_le_two_phi_sq (Cvs.ZeroCounting.zPoint ρ).re
    have hm : (0:ℝ) ≤ Cvs.Criterion.divisorWeight ρ := Nat.cast_nonneg _
    have h3 : (8 + 2 * L ^ 2) / (1 + (Cvs.ZeroCounting.zPoint ρ).re ^ 2)
        ≤ (8 + 2 * L ^ 2) * (2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |(Cvs.ZeroCounting.zPoint ρ).re| ^ 2) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [hre] at h1 h3
    rw [hre, mul_assoc]
    calc (Cvs.Criterion.divisorWeight ρ : ℝ) * (2 / ((ρ : ℂ)).im ^ 2 * (1 - Real.cos (((ρ : ℂ)).im * L)))
        ≤ (Cvs.Criterion.divisorWeight ρ : ℝ) * ((8 + 2 * L ^ 2) * (2 * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((ρ : ℂ)).im| ^ 2)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) hm
      _ = 2 * (8 + 2 * L ^ 2) * ((Cvs.Criterion.divisorWeight ρ : ℝ) * Cvs.Zeta.LogEnvelopeSquareSummable.phi |((ρ : ℂ)).im| ^ 2) := by
          ring
  eq L hL := by
    rw [hA L hL]
    refine tsum_congr fun ρ => ?_
    rw [term_real (hB ρ) L]; ring

/-- RH from the zero side and real frequencies. -/
theorem rh_of_real (hA : ZeroSideG) (hB : FrequenciesReal) : RiemannHypothesis :=
  Cvs.Route.NestedBoxLevyStep.rh_of_levyRep (levyRep hA hB)

/-- RH gives real frequencies. -/
theorem frequenciesReal_of_rh (h : RiemannHypothesis) : FrequenciesReal := by
  intro ρ
  obtain ⟨hz, h0, h1⟩ := ρ.2
  have hre : (ρ : ℂ).re = 1 / 2 := by
    refine h (ρ : ℂ) hz ?_ ?_
    · rintro ⟨n, hn⟩
      have : (ρ : ℂ).re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h1'; rw [h1'] at h1; simp at h1
  unfold Cvs.ZeroCounting.zPoint
  simp [hre]

/-- **Relative to the zero side, RH is the reality of the frequencies**, and the induction step of Cvs.Route.NestedBoxInduction holds
at every `N` exactly when they are real. -/
theorem rh_iff_frequenciesReal (hA : ZeroSideG) : RiemannHypothesis ↔ FrequenciesReal :=
  ⟨frequenciesReal_of_rh, rh_of_real hA⟩

end Cvs.Route.NestedBoxFrequenciesReal
