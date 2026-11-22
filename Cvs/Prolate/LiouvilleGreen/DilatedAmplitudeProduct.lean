import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation
import Cvs.Prolate.LiouvilleGreen.RateSecondDerivativeIntegral
import Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The amplitude product of a dilated rung mode against a profile

The pairing of the mode `ψ(m·)` of a rung with the profile `cos(cm′t)/(m′t)^{n+1}` carries the amplitude
`A(mt)/(2(m′t)^{n+1})`; on `[p, q]` with `mp ≥ ξ₀ > 1` it is differentiable, bounded by
`√(E(ξ₀)fac(ξ₀)/a(mp))/(2(m′p)^{n+1})`, and its derivative by that bound times
`2m(mp/√((mp)² − 1))(mp/((mp)² − 1)) + (n + 1)/p`: the data `A`, `V` of the tests for the dilated modes of an earlier result.
-/

namespace Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeProduct

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge

/-- The amplitude product of the mode `m` against the profile `(m′, n)`: `A(mt)/(2(m′t)^{n+1})`. -/
noncomputable def profAmpM (c χ : ℝ) (ψ u : ℝ → ℝ) (m m' n : ℕ) (t : ℝ) : ℝ :=
  ampl (aP c χ) ψ u ((m : ℝ) * t) / (2 * ((m' : ℝ) * t) ^ (n + 1))

/-- Its derivative: `m A'(mt)/(2(m′t)^{n+1}) − (n+1) m′ A(mt)/(2(m′t)^{n+2})`. -/
noncomputable def profAmpM' (c χ : ℝ) (ψ u : ℝ → ℝ) (m m' n : ℕ) (t : ℝ) : ℝ :=
  m * ampl' (aP c χ) (wP c χ) (qP c χ) ψ u ((m : ℝ) * t) / (2 * ((m' : ℝ) * t) ^ (n + 1))
    - (n + 1) * m' * ampl (aP c χ) ψ u ((m : ℝ) * t) / (2 * ((m' : ℝ) * t) ^ (n + 2))

/-- **The amplitude product of a dilated mode is differentiable.** -/
theorem hasDerivAt_profAmpM {c χ t : ℝ} {ψ u : ℝ → ℝ} {m m' n : ℕ} (hm : 1 ≤ m) (ht : 1 < (m : ℝ) * t)
    (ht0 : 0 < t) (hc : 0 < c) (hχc : χ < c ^ 2) (hm' : 1 ≤ m')
    (hE : 0 < energy (aP c χ) ψ u ((m : ℝ) * t))
    (hψ : HasDerivAt ψ (u ((m : ℝ) * t) / pP ((m : ℝ) * t)) ((m : ℝ) * t))
    (hu : HasDerivAt u (-(qP c χ ((m : ℝ) * t) * ψ ((m : ℝ) * t))) ((m : ℝ) * t)) :
    HasDerivAt (profAmpM c χ ψ u m m' n) (profAmpM' c χ ψ u m m' n t) t := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha : 0 < aP c χ ((m : ℝ) * t) := aP_pos ht hc2 hχc
  have hp : pP ((m : ℝ) * t) ≠ 0 := (pP_pos ht).ne'
  have hA := hasDerivAt_ampl (p := pP) (w := wP c χ) (q := qP c χ) ha hp (aP_sq ht hc2 hχc) hE hψ hu
    (hasDerivAt_aP ht hc2 hχc)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlin : HasDerivAt (fun t => (m : ℝ) * t) (m : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (m : ℝ)
  have hAm : HasDerivAt (fun t => ampl (aP c χ) ψ u ((m : ℝ) * t))
      (ampl' (aP c χ) (wP c χ) (qP c χ) ψ u ((m : ℝ) * t) * m) t := hA.comp t hlin
  have hm'0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hx : 0 < (m' : ℝ) * t := by positivity
  have hpow : HasDerivAt (fun t => 2 * ((m' : ℝ) * t) ^ (n + 1))
      (2 * ((n + 1 : ℕ) * ((m' : ℝ) * t) ^ n * m')) t := by
    have h1 : HasDerivAt (fun t => (m' : ℝ) * t) (m' : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (m' : ℝ)
    exact (h1.pow (n + 1)).const_mul 2
  have hden : 2 * ((m' : ℝ) * t) ^ (n + 1) ≠ 0 := by positivity
  have := hAm.div hpow hden
  unfold profAmpM profAmpM'
  refine this.congr_deriv ?_
  have hx1 : ((m' : ℝ) * t) ^ (n + 1) ≠ 0 := by positivity
  have hx2 : ((m' : ℝ) * t) ^ (n + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The amplitude product of a dilated mode is bounded** on `[p, q]` with `[mp, mq] ⊆ [ξ₀, ξ₁]` by
`√(E(ξ₀)fac(ξ₀)/a(mp))/(2(m′p)^{n+1})`. -/
theorem profAmpM_le {c χ ξ₀ ξ₁ p q t : ℝ} {ψ u : ℝ → ℝ} {m m' n : ℕ} (h1 : 1 < ξ₀) (hm : 1 ≤ m)
    (hp : ξ₀ ≤ m * p) (hpt : p ≤ t) (htq : t ≤ q) (hq : (m : ℝ) * q ≤ ξ₁) (hc : 0 < c) (hχ : 0 ≤ χ)
    (hχc : χ < c ^ 2) (hm' : 1 ≤ m')
    (hψ : ∀ s ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u s / pP s) s)
    (hu : ∀ s ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ s * ψ s)) s) (hW : wP c χ ξ₀ < 2) :
    |profAmpM c χ ψ u m m' n t|
      ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ ((m : ℝ) * p)) / (2 * ((m' : ℝ) * p) ^ (n + 1)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmpt : (m : ℝ) * p ≤ m * t := mul_le_mul_of_nonneg_left hpt hm0.le
  have hmtq : (m : ℝ) * t ≤ m * q := mul_le_mul_of_nonneg_left htq hm0.le
  have hmp1 : 1 < (m : ℝ) * p := lt_of_lt_of_le h1 hp
  have hp0 : 0 < p := by
    by_contra h; push Not at h
    have : (m : ℝ) * p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0.le h
    linarith
  -- the amplitude window of Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge at `mt`, and `a(mp) ≤ a(mt)`
  have hA0 : 0 ≤ ampl (aP c χ) ψ u ((m : ℝ) * t) := Real.sqrt_nonneg _
  have hc2 : 0 < c ^ 2 := by positivity
  obtain ⟨-, hup⟩ := prolate_ampl_sq_bounds (ψ := ψ) (u := u) h1 (hp.trans hmpt) (hmtq.trans hq) hc hχ hχc hψ hu hW
  have hamono := Cvs.Prolate.LiouvilleGreen.RateSecondDerivativeIntegral.aP_mono (χ := χ) hmp1 hmpt hc hχ hχc
  have hap : 0 < aP c χ ((m : ℝ) * p) := aP_pos hmp1 hc2 hχc
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ₀ := by
    have ha0 := aP_pos h1 hc2 hχc
    unfold energy; positivity
  have hw0 : 0 < wP c χ ξ₀ := wP_pos h1 hc2 hχc
  have hfac : 0 ≤ fac c χ ξ₀ := by
    unfold fac
    have : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
    positivity
  have hAle : ampl (aP c χ) ψ u ((m : ℝ) * t) ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ ((m : ℝ) * p)) := by
    apply Real.le_sqrt_of_sq_le
    exact hup.trans (div_le_div_of_nonneg_left (by positivity) hap hamono)
  have hm'0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hpowle : ((m' : ℝ) * p) ^ (n + 1) ≤ ((m' : ℝ) * t) ^ (n + 1) :=
    pow_le_pow_left₀ (mul_nonneg hm'0.le hp0.le) (mul_le_mul_of_nonneg_left hpt hm'0.le) _
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hp0 hpt
  unfold profAmpM
  rw [abs_of_nonneg (div_nonneg hA0 (by positivity))]
  calc ampl (aP c χ) ψ u ((m : ℝ) * t) / (2 * ((m' : ℝ) * t) ^ (n + 1))
      ≤ ampl (aP c χ) ψ u ((m : ℝ) * t) / (2 * ((m' : ℝ) * p) ^ (n + 1)) :=
        div_le_div_of_nonneg_left hA0 (by positivity) (by linarith)
    _ ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ ((m : ℝ) * p)) / (2 * ((m' : ℝ) * p) ^ (n + 1)) :=
        div_le_div_of_nonneg_right hAle (by positivity)

end Cvs.Prolate.LiouvilleGreen.DilatedAmplitudeProduct
