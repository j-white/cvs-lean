import Mathlib
import Cvs.L2a.ResonantChannelModeMasses

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The harmonic gain of the Poisson sum on the far mass

Every mode `m ≤ k` of the tail counts the far mass of `Φ` beyond `k`: `modeMass(m) = (1/m) ∫_m^{mb} Φ² ≥ (1/m) ∫_k^b Φ²`.
So with the tail norm at least `(1 − δ)` times the mode masses, `∫_k^b Φ² ≤ ∫F² / ((1 − δ) H_k)`, `H_k` the harmonic
number: the far mass beyond `k` is at most the tail norm over `(1 − δ) H_k`.
-/

namespace Cvs.L2a.PoissonFarMassHarmonicGain

open Real Set MeasureTheory
open Cvs.L2a.TailOfModes Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses

/-- A mode `m ≤ k` counts the far mass beyond `k`: `modeMass(m) ≥ (1/m) ∫_k^b Φ²`. -/
theorem modeMass_ge_far {Φ : ℝ → ℝ} {b : ℝ} {m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hkb : (k : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (k * b))) :
    (1 / (m : ℝ)) * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 ≤ modeMass Φ b m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hb1 : (1 : ℝ) ≤ b := le_trans (by exact_mod_cast (hm.trans hmk)) hkb
  unfold modeMass
  rw [intervalIntegral.integral_comp_mul_left (fun ξ => Φ ξ ^ 2) hm0.ne', smul_eq_mul, mul_one, one_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 : (m : ℝ) ≤ k := hmk'
  have h2 : (k : ℝ) ≤ b := hkb
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h3 : b ≤ m * b := by
    have h := mul_le_mul_of_nonneg_right hm1 (show (0 : ℝ) ≤ b by linarith)
    rw [one_mul] at h
    exact h
  have hsub : Icc (m : ℝ) (m * b) ⊆ Icc 1 (k * b) :=
    Icc_subset_Icc (by exact_mod_cast hm) (mul_le_mul_of_nonneg_right hmk' (by linarith))
  exact intervalIntegral.integral_mono_interval h1 h2 h3 (Filter.Eventually.of_forall fun ξ => sq_nonneg (Φ ξ))
    (((hcont.mono hsub).pow 2).intervalIntegrable_of_Icc (h1.trans (h2.trans h3)))

end Cvs.L2a.PoissonFarMassHarmonicGain
