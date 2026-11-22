import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SlepianEvenOrdering

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung family on `Finset.range x` at `c = 2πx`, with partners one count up

The span rungs are `g_j = rung c (2j)`, `j < x`, and the partners `h_j = rung c (2j + 1)`. Levels of count `2j` come
from `FullSpanIndexFloor`'s index floor and levels of count `2j + 1 ≤ 2x − 1` from Landau's lower pivot at `2x − 1`. Counts separate
the levels: the `g`-levels are injective, the `h`-levels are injective, and no `g`-level is an `h`-level.
-/

noncomputable section

open Real Set Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.RungFamilyRangePartners

/-! ### Levels from the pivot -/

/-- **Landau's lower pivot at `k` gives the level of count `k`.** -/
theorem exists_isLevelIdx_of_landauLower {c : ℝ} {k : ℕ} (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower c k) :
    ∃ χ, IsLevelIdx c k χ := by
  obtain ⟨χL, -, g, g₁, g₂, hg, hg₁, -, hang, heven, hg0, -, hkL, -⟩ := hL
  have hmem : χL ∈ evenSpec (sqC c) := mem_evenSpec_of_angular hg hg₁ hang heven hg0
  exact exists_isLevelIdx_of_le (⟨hmem, rfl⟩ : IsLevelIdx c _ χL) hkL

/-- **The level of count `2j` exists** for `j < x` at `c = 2πx ≥ 80`. -/
theorem exists_main {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Finset.range x) :
    ∃ χ, IsLevelIdx (2 * π * x) (2 * (j : ℕ)) χ :=
  (Cvs.L2a.FullSpanIndexFloor.full_index x hx (Finset.mem_range.mp j.2)).1

/-- **The level of count `2j + 1` exists** for `j < x`, from the pivot at `2x − 1`. -/
theorem exists_partner {x : ℕ} (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1))
    (j : Finset.range x) : ∃ χ, IsLevelIdx (2 * π * x) (2 * (j : ℕ) + 1) χ := by
  have hj := Finset.mem_range.mp j.2
  obtain ⟨χ, hχ⟩ := exists_isLevelIdx_of_landauLower hL
  exact exists_isLevelIdx_of_le hχ (by omega)

/-! ### Counts, order and separation -/

/-- The count below the `g`-level is `2j`. -/
theorem ncard_main {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Finset.range x) :
    (evenSpec (sqC (2 * π * x)) ∩ Iio (lev (2 * π * x) (2 * (j : ℕ)))).ncard = 2 * (j : ℕ) :=
  (lev_spec (exists_main hx j)).2

/-- The count below the `h`-level is `2j + 1`. -/
theorem ncard_partner {x : ℕ} (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1))
    (j : Finset.range x) :
    (evenSpec (sqC (2 * π * x)) ∩ Iio (lev (2 * π * x) (2 * (j : ℕ) + 1))).ncard = 2 * (j : ℕ) + 1 :=
  (lev_spec (exists_partner hL j)).2

/-- **The `g`-counts are even.** -/
theorem even_ncard_main {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Finset.range x) :
    Even (evenSpec (sqC (2 * π * x)) ∩ Iio (lev (2 * π * x) (2 * (j : ℕ)))).ncard := by
  rw [ncard_main hx j]
  exact ⟨j, by ring⟩

/-- **The `g`-counts are at most `2x − 1`.** -/
theorem ncard_main_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Finset.range x) :
    (evenSpec (sqC (2 * π * x)) ∩ Iio (lev (2 * π * x) (2 * (j : ℕ)))).ncard ≤ 2 * x - 1 := by
  have hj := Finset.mem_range.mp j.2
  rw [ncard_main hx j]
  omega

/-- **The `h`-counts are at most `2x − 1`.** -/
theorem ncard_partner_le {x : ℕ} (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1))
    (j : Finset.range x) :
    (evenSpec (sqC (2 * π * x)) ∩ Iio (lev (2 * π * x) (2 * (j : ℕ) + 1))).ncard ≤ 2 * x - 1 := by
  have hj := Finset.mem_range.mp j.2
  rw [ncard_partner hL j]
  omega

/-- **Each partner sits above its rung**: `χ_j ≤ χ'_j`. -/
theorem lev_le_partner {x : ℕ} (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1))
    (j : Finset.range x) : lev (2 * π * x) (2 * (j : ℕ)) ≤ lev (2 * π * x) (2 * (j : ℕ) + 1) :=
  lev_le (exists_partner hL j) (by omega)

/-- **The `g`-levels are injective.** -/
theorem lev_main_injective {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Function.Injective fun j : Finset.range x => lev (2 * π * x) (2 * (j : ℕ)) := by
  intro i j he
  have h1 := ncard_main hx i
  have h2 := ncard_main hx j
  simp only at he
  rw [he] at h1
  exact Subtype.ext (by omega)

/-- **The `h`-levels are injective.** -/
theorem lev_partner_injective {x : ℕ} (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1)) :
    Function.Injective fun j : Finset.range x => lev (2 * π * x) (2 * (j : ℕ) + 1) := by
  intro i j he
  have h1 := ncard_partner hL i
  have h2 := ncard_partner hL j
  simp only at he
  rw [he] at h1
  exact Subtype.ext (by omega)

/-- **No `g`-level is an `h`-level**: the counts differ in parity. -/
theorem lev_main_ne_partner {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1)) (i j : Finset.range x) :
    lev (2 * π * x) (2 * (i : ℕ)) ≠ lev (2 * π * x) (2 * (j : ℕ) + 1) := by
  intro he
  have h1 := ncard_main hx i
  have h2 := ncard_partner hL j
  rw [he] at h1
  omega

/-- The `g`-levels are nonnegative. -/
theorem lev_main_nonneg {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Finset.range x) :
    0 ≤ lev (2 * π * x) (2 * (j : ℕ)) :=
  nonneg_of_mem_evenSpec _ (lev_spec (exists_main hx j)).1

/-! ### The index floor, the size, the mass and the partners' half -/

/-- **(I) at the index floor**: `4c/log c ≤ c² − χ_j` on every `g`-level. -/
theorem sigmaLow_le_main {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Finset.range x) :
    Cvs.Prolate.EvenLevelIndexLemma.sigmaLow (2 * π * x) ≤ (2 * π * x) ^ 2 - lev (2 * π * x) (2 * (j : ℕ)) :=
  (Cvs.L2a.FullSpanIndexFloor.full_index x hx (Finset.mem_range.mp j.2)).2

/-- **The span has `x ≤ c/4 + 1` rungs.** -/
theorem card_range_le (x : ℕ) : (Fintype.card (Finset.range x) : ℝ) ≤ 2 * π * x / 4 + 1 := by
  rw [Fintype.card_coe, Finset.card_range]
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  nlinarith [Real.pi_gt_three]

/-- **Every `g`-rung has positive mass on `(1, 3)`.** -/
theorem mass_main {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Finset.range x) :
    0 < ∫ t in (1 : ℝ)..3, psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) t ^ 2 := by
  have hc0 : 0 < 2 * π * (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
  have hspec := fun j => rung_spec (exists_main hx j)
  exact Cvs.Prolate.AngularBesselInequality.hM_of_angular (g := fun j : Finset.range x => rung (2 * π * x) (2 * (j : ℕ)))
    (g₁ := fun j => rung₁ (2 * π * x) (2 * (j : ℕ))) (g₂ := fun j => rung₂ (2 * π * x) (2 * (j : ℕ)))
    (χ := fun j => lev (2 * π * x) (2 * (j : ℕ))) (X := 3) (fun j => (hspec j).1) (fun j => (hspec j).2.1)
    (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1) (fun j => (hspec j).2.2.2.2.1)
    (fun j => rung_ne_zero (exists_main hx j)) hc0 (lev_main_nonneg hx) (by norm_num) j

/-- **The partners have `λ'_j ≥ ½`**, from the pivot at `2x − 1`. -/
theorem half_le_lam_partner {x : ℕ} (hx : 80 ≤ 2 * π * x)
    (hL : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1)) (j : Finset.range x) :
    1 / 2 ≤ (muR (2 * π * x) (2 * (j : ℕ) + 1) * √(2 * π * x / (2 * π))) ^ 2 := by
  have hc0 : 0 < 2 * π * (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
  have hex := exists_partner hL j
  obtain ⟨hh, hh₁, hh₂c, hang, heven, -⟩ := rung_spec hex
  exact Cvs.Prolate.LandauHalfEvenSpectrum.half_le_lam_of_lower hc0 hL hh hh₁ hh₂c hang heven (rung_ne_zero hex)
    (psi_rung hex) (ncard_partner_le hL j)

end Cvs.Prolate.RungFamilyRangePartners
