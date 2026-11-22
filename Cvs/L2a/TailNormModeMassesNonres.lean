import Mathlib
import Cvs.L2a.PrimePairingResonantSplit
import Cvs.L2a.ResonantChannelModeMasses
import Cvs.L2a.TailOfModes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail norm is the mode masses plus the non-resonant pairs at `k = 1`

The pairing at `k = 1` is the tail's norm, its resonant pairs are the diagonal `(n, n)`, and each resonant tail
energy at `k = 1` is the mode mass `∫_1^b Φ(nθ)² dθ` itself: so `∫F² = Σ_{n ≤ M} modeMass(n) + nonresPart(1)`.
The comparison of the norm with the mode masses is therefore the same object as the non-resonant channel.
-/

namespace Cvs.L2a.TailNormModeMassesNonres

open Real Set MeasureTheory
open Cvs.L2a.TailOfModes Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses

/-- The resonant part at `k = 1` is the sum of the mode masses. -/
theorem resPart_one (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) :
    resPart Φ M b 1 = ∑ n ∈ Finset.Icc 1 M, modeMass Φ b n := by
  unfold resPart
  rw [resPairs_eq_image M le_rfl, Finset.sum_image (fun n _ n' _ h => ((Prod.mk.injEq _ _ _ _).mp h).1)]
  have hfilter : (Finset.Icc 1 M).filter (fun n => 1 ∣ n) = Finset.Icc 1 M := by
    ext n; simp
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn1 : 1 ≤ n := hn.1
  have := resonant_integral Φ (b := b) le_rfl hn1
  simp only [Nat.cast_one, one_mul, Nat.div_one, div_one] at this ⊢
  rw [← this]
  unfold modeMass
  exact (intervalIntegral.integral_congr (fun θ _ => by ring)).symm

/-- **The tail norm is the mode masses plus the non-resonant pairs at `k = 1`.** -/
theorem norm_eq_modeMasses_add_nonres (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (hb : 1 ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 = (∑ n ∈ Finset.Icc 1 M, modeMass Φ b n) + nonresPart Φ M b 1 := by
  have h := pairing_eq_res_add_nonres Φ M (k := 1) le_rfl (by simpa using hb) hcont
  rw [resPart_one] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro θ _
  simp only [Nat.cast_one, one_mul]
  ring

end Cvs.L2a.TailNormModeMassesNonres
