import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.Convexity.CompletedZetaStripBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Mellin integral, split at one

The modified function's Mellin transform converges at every exponent, so its integrand is
integrable on each half of the half line separately. The half line is the disjoint union of the
part below one and the part from one, and the integral splits accordingly.
-/

noncomputable section

open Set MeasureTheory

namespace Cvs.Xi.MellinSplitAtOne

theorem integrableOn_Ioo (P : WeakFEPair ℂ) (w : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • P.f_modif t) (Ioo (0 : ℝ) 1) :=
  (Cvs.ZetaGrowth.mellinConvergent_f_modif P w).mono_set Ioo_subset_Ioi_self

theorem integrableOn_Ici (P : WeakFEPair ℂ) (w : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • P.f_modif t) (Ici (1 : ℝ)) :=
  (Cvs.ZetaGrowth.mellinConvergent_f_modif P w).mono_set
    (fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp hx)))

theorem disjoint_Ioo_Ici : Disjoint (Ioo (0 : ℝ) 1) (Ici (1 : ℝ)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact absurd hx' (not_le.mpr hx.2)

/-- **The Mellin integral splits at one.** -/
theorem Λ₀_split (P : WeakFEPair ℂ) (w : ℂ) :
    P.Λ₀ w = (∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (w - 1) • P.f_modif t)
      + ∫ t in Ici (1 : ℝ), (t : ℂ) ^ (w - 1) • P.f_modif t := by
  rw [WeakFEPair.Λ₀, mellin, ← Set.Ioo_union_Ici_eq_Ioi (zero_lt_one : (0 : ℝ) < 1),
    setIntegral_union disjoint_Ioo_Ici measurableSet_Ici
      (integrableOn_Ioo P w) (integrableOn_Ici P w)]

end Cvs.Xi.MellinSplitAtOne
