import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow
import Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay
import Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The variation of the amplitude product

The derivative of the amplitude product `B = A/(2(m′t)^{n+1})` of Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct is bounded on `[p, q]` beyond `ξ₀` by the
amplitude bound times `2(p/√(p² − 1))(p/(p² − 1)) + (n + 1)/p`: the first term is the rung's relative rate `|w|(a/p)`
of Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation through the correction bound of Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow, the second the profile's own decay. The variation `∫_p^q |B'|` is
therefore at most `(q − p)` times that: the datum `V` of the tests of Cvs.Upstream.SecondDerivativeWindowTest and Cvs.Upstream.FirstDerivativeTestVariation.
-/

namespace Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeVariation

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.ProlateLeakageArcsinDecay Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.PruferAmplitudeVariation Cvs.Prolate.LiouvilleGreen.RungAmplitudeBeyondEdge Cvs.Prolate.LiouvilleGreen.MismatchOutsideWindow Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct

/-- The amplitude bound of Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeProduct: `√(E(ξ₀)fac(ξ₀)/a(p))/(2(m′p)^{n+1})`. -/
noncomputable def ampBound (c χ : ℝ) (ψ u : ℝ → ℝ) (ξ₀ p : ℝ) (m' n : ℕ) : ℝ :=
  √(energy (aP c χ) ψ u ξ₀ * fac c χ ξ₀ / aP c χ p) / (2 * ((m' : ℝ) * p) ^ (n + 1))

/-- The derivative bound: `ampBound · (2(p/√(p² − 1))(p/(p² − 1)) + (n + 1)/p)`. -/
noncomputable def derivBound (c χ : ℝ) (ψ u : ℝ → ℝ) (ξ₀ p : ℝ) (m' n : ℕ) : ℝ :=
  ampBound c χ ψ u ξ₀ p m' n * (2 * (p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))) + (n + 1) / p)

/-- **The derivative of the amplitude product is bounded** on `[p, q] ⊆ [ξ₀, ξ₁]` by `derivBound`. -/
theorem abs_profAmp'_le {c χ ξ₀ ξ₁ p q t : ℝ} {ψ u : ℝ → ℝ} {m' n : ℕ} (h1 : 1 < ξ₀) (hp : ξ₀ ≤ p)
    (hpt : p ≤ t) (htq : t ≤ q) (hq : q ≤ ξ₁) (hc : 0 < c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2) (hm' : 1 ≤ m')
    (hψ : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt ψ (u t / pP t) t)
    (hu : ∀ t ∈ Icc ξ₀ ξ₁, HasDerivAt u (-(qP c χ t * ψ t)) t) (hW : wP c χ ξ₀ < 2)
    (hE : 0 < energy (aP c χ) ψ u t) :
    |profAmp' c χ ψ u m' n t| ≤ derivBound c χ ψ u ξ₀ p m' n := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp1 : 1 < p := lt_of_lt_of_le h1 hp
  have ht1 : 1 < t := lt_of_lt_of_le hp1 hpt
  have hp0 : (0 : ℝ) < p := by linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hm0 : (0 : ℝ) < m' := by exact_mod_cast hm'
  have hat : 0 < aP c χ t := aP_pos ht1 hc2 hχc
  have hpP : 0 < pP t := pP_pos ht1
  -- the amplitude and its bound
  have hAb := profAmp_le (ψ := ψ) (u := u) (m' := m') (n := n) h1 hp hpt htq hq hc hχ hχc hm' hψ hu hW
  have hA0 : 0 ≤ ampl (aP c χ) ψ u t := Real.sqrt_nonneg _
  have hAle : ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1)) ≤ ampBound c χ ψ u ξ₀ p m' n := by
    have := hAb
    unfold profAmp at this
    rw [abs_of_nonneg (div_nonneg hA0 (by positivity))] at this
    exact this
  -- the amplitude's derivative: `|A'| ≤ |w|(a/p) A ≤ 2 (p/√(p²−1))(p/(p²−1)) A`
  have hA' := abs_ampl'_le (p := pP) (w := wP c χ) (q := qP c χ) (ψ := ψ) (u := u) hat hpP
    (aP_sq ht1 hc2 hχc) hE
  have hcorr := correction_le (χ := χ) hp1 hpt hc hχ hχc
  have hA'le : |ampl' (aP c χ) (wP c χ) (qP c χ) ψ u t|
      ≤ 2 * (p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))) * ampl (aP c χ) ψ u t := by
    calc |ampl' (aP c χ) (wP c χ) (qP c χ) ψ u t| ≤ |wP c χ t| * (aP c χ t / pP t) * ampl (aP c χ) ψ u t := hA'
      _ = 2 * (|wP c χ t| * (aP c χ t / pP t) / 2) * ampl (aP c χ) ψ u t := by ring
      _ ≤ 2 * (p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))) * ampl (aP c χ) ψ u t := by gcongr
  -- assemble
  unfold profAmp' derivBound
  have hpow : 0 < ((m' : ℝ) * t) ^ (n + 1) := by positivity
  have hpow2 : 0 < ((m' : ℝ) * t) ^ (n + 2) := by positivity
  have hterm2 : (n + 1) * m' * ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 2))
      = (n + 1) / t * (ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))) := by
    field_simp
    ring
  have hpt' : (n + 1 : ℝ) / t ≤ (n + 1) / p := div_le_div_of_nonneg_left (by positivity) hp0 hpt
  calc |ampl' (aP c χ) (wP c χ) (qP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))
        - (n + 1) * m' * ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 2))|
      ≤ |ampl' (aP c χ) (wP c χ) (qP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))|
        + |(n + 1) * m' * ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 2))| := abs_sub _ _
    _ = |ampl' (aP c χ) (wP c χ) (qP c χ) ψ u t| / (2 * ((m' : ℝ) * t) ^ (n + 1))
        + (n + 1) / t * (ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))) := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ((m' : ℝ) * t) ^ (n + 1)), hterm2,
          abs_of_nonneg (mul_nonneg (by positivity) (div_nonneg hA0 (by positivity)))]
    _ ≤ 2 * (p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))) * ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))
        + (n + 1) / p * (ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))) := by
        gcongr
    _ = (2 * (p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))) + (n + 1) / p)
        * (ampl (aP c χ) ψ u t / (2 * ((m' : ℝ) * t) ^ (n + 1))) := by ring
    _ ≤ (2 * (p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))) + (n + 1) / p) * ampBound c χ ψ u ξ₀ p m' n := by
        apply mul_le_mul_of_nonneg_left hAle
        have : (0 : ℝ) < p ^ 2 - 1 := by nlinarith
        positivity
    _ = ampBound c χ ψ u ξ₀ p m' n * (2 * (p / √(p ^ 2 - 1) * (p / (p ^ 2 - 1))) + (n + 1) / p) := by ring

end Cvs.Prolate.LiouvilleGreen.ProfileAmplitudeVariation
