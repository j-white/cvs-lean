import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation
import Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The amplitude product of a rung against a profile

The pairing of a rung's first mode with the profile `cos(cm′t)/(m′t)^{n+1}` carries the amplitude
`B(t) = A(t)/(2(m′t)^{n+1})`, `A = √(E/a)` the Prüfer amplitude. On `[p, q]` beyond `ξ₀` it is differentiable, bounded
by `√(E(ξ₀)fac(ξ₀)/a(p))/(2(m′p)^{n+1})`, and its derivative by that bound times
`2(p/√(p² − 1))(p/(p² − 1)) + (n + 1)/p`: the data `A` and `V = (q − p)·D` of the tests of Cvs.Upstream.SecondDerivativeWindowTest and Cvs.Upstream.FirstDerivativeTestVariation.
-/

namespace Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge

/-- The amplitude product against the profile of order `n` and mode `m′`: `A(t)/(2(m′t)^{n+1})`. -/
noncomputable def profAmp (c χ : ℝ) (ψ u : ℝ → ℝ) (m' n : ℕ) (t : ℝ) : ℝ :=
  ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))

/-- Its derivative: `A'/(2(m′t)^{n+1}) − (n+1) m′ A/(2 (m′t)^{n+2})`. -/
noncomputable def profAmp' (c χ : ℝ) (ψ u : ℝ → ℝ) (m' n : ℕ) (t : ℝ) : ℝ :=
  ampl' (aP c χ) (wP c χ) (qP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))
    - (n + 1) * m' * ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 2))

/-- **The amplitude product is differentiable** for `t > 1`, `m′ ≥ 1` and positive energy. -/
theorem hasDerivAt_profAmp {c χ t : ℝ} {ψ u : ℝ → ℝ} {m' n : ℕ} (ht : 1 < t) (hc : 0 < c) (_hχ0 : 0 ≤ χ)
    (hχc : χ < c ^ 2) (hm' : 1 ≤ m') (hE : 0 < energy (aP c χ) ψ u t)
    (hψ : HasDerivAt ψ (u t / pP t) t) (hu : HasDerivAt u (-(qP c χ t * ψ t)) t) :
    HasDerivAt (profAmp c χ ψ u m' n) (profAmp' c χ ψ u m' n t) t := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha : 0 < aP c χ t := aP_pos ht hc2 hχc
  have hp : pP t ≠ 0 := (pP_pos ht).ne'
  have hA := hasDerivAt_ampl (p := pP) (w := wP c χ) (q := qP c χ) ha hp (aP_sq ht hc2 hχc) hE hψ hu
    (hasDerivAt_aP ht hc2 hχc)
  have hm0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hx : 0 < (m' : ℝ) * t := by positivity
  -- the power `(m′t)^{n+1}` and its derivative `(n+1) m′ (m′t)^n`
  have hpow : HasDerivAt (fun t => 2 * ((m' : ℝ) * t) ^ (n + 1))
      (2 * ((n + 1 : ℕ) * ((m' : ℝ) * t) ^ n * m')) t := by
    have h1 : HasDerivAt (fun t => (m' : ℝ) * t) (m' : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (m' : ℝ)
    have h2 := h1.pow (n + 1)
    exact h2.const_mul 2
  have hden : 2 * ((m' : ℝ) * t) ^ (n + 1) ≠ 0 := by positivity
  have := hA.div hpow hden
  unfold profAmp profAmp'
  refine this.congr_deriv ?_
  have hx1 : ((m' : ℝ) * t) ^ (n + 1) ≠ 0 := by positivity
  have hx2 : ((m' : ℝ) * t) ^ (n + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **The amplitude product is bounded** on `[p, q] ⊆ [ξ₀, ξ₁]` by `√(E(ξ₀)fac(ξ₀)/a(p))/(2(m′p)^{n+1})`. -/
theorem profAmp_le {c χ ξ₀ ξ₁ p q t : ℝ} {ψ u : ℝ → ℝ} {m' n : ℕ} (h1 : 1 < ξ₀) (hp : ξ₀ ≤ p) (hpt : p ≤ t)
    (htq : t ≤ q) (hq : q ≤ ξ₁) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hm' : 1 ≤ m')
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2) :
    |profAmp c χ ψ u m' n t| ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ p) / (2 * ((m' : ℝ) * p) ^ (n + 1)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp1 : 1 < p := lt_of_lt_of_le h1 hp
  have ht1 : 1 < t := lt_of_lt_of_le hp1 hpt
  have hp0 : (0 : ℝ) < p := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hap : 0 < aP c χ p := aP_pos hp1 hc2 hχc
  have hat : 0 < aP c χ t := aP_pos ht1 hc2 hχc
  -- `a` increases: `a(p) ≤ a(t)`
  have hamono : aP c χ p ≤ aP c χ t := by
    unfold aP pP qP
    apply Real.sqrt_le_sqrt
    have hp2 : (1 : ℝ) ≤ p ^ 2 := by nlinarith
    have hpt2 : p ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by linarith) hpt 2
    have h0 : (0 : ℝ) ≤ c ^ 2 * p ^ 2 - χ := by
      nlinarith [mul_le_mul_of_nonneg_left hp2 hc2.le]
    have h1' : (0 : ℝ) ≤ p ^ 2 - 1 := by linarith
    have h2' : c ^ 2 * p ^ 2 - χ ≤ c ^ 2 * t ^ 2 - χ := by
      nlinarith [mul_le_mul_of_nonneg_left hpt2 hc2.le]
    exact mul_le_mul (by linarith) h2' h0 (by linarith)
  obtain ⟨-, hup⟩ := prolate_ampl_sq_bounds (ψ := ψ) (u := u) h1 (hp.trans hpt) (htq.trans hq) hc hχ hχc hψ hu hW
  have hA0 : 0 ≤ ampl (aP c χ) ψ u t := Real.sqrt_nonneg _
  have hE0 : 0 ≤ energy (aP c χ) ψ u ξ₀ := by
    have ha0 := aP_pos h1 hc2 hχc
    unfold energy; positivity
  have hw0 : 0 < wP c χ ξ₀ := wP_pos h1 hc2 hχc
  have hfac : 0 ≤ fac c χ ξ₀ := by
    unfold fac
    have : 0 < 1 - wP c χ ξ₀ / 2 := by linarith
    positivity
  have hAle : ampl (aP c χ) ψ u t ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ p) := by
    apply Real.le_sqrt_of_sq_le
    calc ampl (aP c χ) ψ u t ^ 2 ≤ energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ t := hup
      _ ≤ energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ p :=
        div_le_div_of_nonneg_left (by positivity) hap hamono
  have hm0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hpowle : ((m' : ℝ) * p) ^ (n + 1) ≤ ((m' : ℝ) * t) ^ (n + 1) :=
    pow_le_pow_left₀ (mul_nonneg hm0.le (by linarith)) (mul_le_mul_of_nonneg_left hpt hm0.le) _
  unfold profAmp
  rw [abs_of_nonneg (div_nonneg hA0 (by positivity))]
  calc ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))
      ≤ ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * p) ^ (n + 1)) :=
        div_le_div_of_nonneg_left hA0 (by positivity) (by linarith)
    _ ≤ √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ p) / (2 * ((m' : ℝ) * p) ^ (n + 1)) :=
        div_le_div_of_nonneg_right hAle (by positivity)

end Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct
