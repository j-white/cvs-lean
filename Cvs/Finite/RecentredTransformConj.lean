import Mathlib
import Cvs.Finite.RecentredTransform
import Cvs.Finite.RecentredTransformClosed
import Cvs.Finite.RecentredTransformEven
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.UniversalFunctionPairing
import Cvs.Limit.OffAxesLimit
import Cvs.Limit.OffAxisWitnessSymmetry
import Cvs.Limit.SpineWithoutSimplicity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The recentred transform conjugates off the axes

Off both coordinate axes the recentred ground-state transform at a conjugate point is the conjugate
of its value, since in the closed form of `Cvs.Finite.RecentredTransformClosed` the window length and the frequencies are real,
so the sine conjugates with its argument and the rational factor of `Cvs.Finite.UniversalFunctionPairing` conjugates termwise.
-/

noncomputable section

open Complex

namespace Cvs.Finite.RecentredTransformConj
open Cvs.ZeroCounting

open Cvs.Limit.OffAxesLimit

variable {ι : Type*} [Fintype ι]

/-- The rational factor conjugates with its argument, its coefficients and frequencies being
real. -/
theorem S_conj (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (ξ : ℂ) :
    Cvs.Finite.UniversalFunctionPairing.S L mode xi ((starRingEnd ℂ) ξ)
      = (starRingEnd ℂ) (Cvs.Finite.UniversalFunctionPairing.S L mode xi ξ) := by
  unfold Cvs.Finite.UniversalFunctionPairing.S
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_div₀, map_sub, map_pow, map_pow, Complex.conj_ofReal, Complex.conj_ofReal]

/-- **The recentred ground-state transform conjugates with its argument off the axes.** -/
theorem cgtransform_conj (P R : ℕ) {L : ℝ} (hL : 0 < L) (N : ℕ) {z : ℂ} (hz : z ∈ offAxes) :
    Cvs.Finite.RecentredTransform.cgtransform P R hL N ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (Cvs.Finite.RecentredTransform.cgtransform P R hL N z) := by
  rw [Cvs.Finite.RecentredTransformClosed.cgtransform_eq_sin P R hL N
      (fun i => Cvs.Finite.RecentredTransformEven.omega_add_ne_zero
        (Cvs.Limit.OffAxisWitnessSymmetry.conj_mem_offAxes hz) i),
    Cvs.Finite.RecentredTransformClosed.cgtransform_eq_sin P R hL N
      (fun i => Cvs.Finite.RecentredTransformEven.omega_add_ne_zero hz i)]
  -- conjugation fixes the numerals, which `norm_num` does not know on its own
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_eq_iff_im.mpr (by norm_num)
  have h2' : (starRingEnd ℂ) (-2 : ℂ) = -2 := Complex.conj_eq_iff_im.mpr (by norm_num)
  have harg : (starRingEnd ℂ) z * (L : ℂ) / 2 = (starRingEnd ℂ) (z * (L : ℂ) / 2) := by
    rw [map_div₀, map_mul, Complex.conj_ofReal, h2]
  rw [harg, Complex.sin_conj, S_conj, map_mul, map_mul, map_mul, h2']

end Cvs.Finite.RecentredTransformConj
