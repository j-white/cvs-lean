import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.AddCircle.Defs

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

namespace Cvs.Operator

open Set

/-!
# The masks compose

`Cvs.Operator.IsCoherent` asks for `S a ∘ S b = S (a + b)`, and `Cvs.Operator.isCoherent_zero` shows the axiom
alone is vacuous.
-/

/-- The canonical representative of `z ∈ 𝕋` in `[0,1)`. -/
noncomputable def rep (z : AddCircle (1 : ℝ)) : ℝ :=
  ((AddCircle.equivIco (1 : ℝ) 0 z : Set.Ico (0:ℝ) (0+1)) : ℝ)

theorem rep_nonneg (z : AddCircle (1 : ℝ)) : 0 ≤ rep z :=
  (Set.mem_Ico.mp (AddCircle.equivIco (1 : ℝ) 0 z).2).1

theorem rep_lt_one (z : AddCircle (1 : ℝ)) : rep z < 1 := by
  have h := (Set.mem_Ico.mp (AddCircle.equivIco (1 : ℝ) 0 z).2).2
  unfold rep
  linarith

theorem coe_rep (z : AddCircle (1 : ℝ)) : ((rep z : ℝ) : AddCircle (1 : ℝ)) = z :=
  AddCircle.coe_equivIco

theorem rep_coe (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    rep ((y : AddCircle (1 : ℝ))) = y := by
  unfold rep
  rw [AddCircle.equivIco_coe_of_mem (Set.mem_Ico.mpr ⟨hy0, by linarith⟩)]

/-- **No wraparound**: below the cut, the representative advances by `β`. -/
theorem rep_add_step (β : ℝ) (z : AddCircle (1 : ℝ)) (hβ : 0 ≤ β)
    (h : rep z + β < 1) :
    rep (z + (β : AddCircle (1 : ℝ))) = rep z + β := by
  have hz : z + (β : AddCircle (1 : ℝ)) = ((rep z + β : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add, coe_rep z]
  rw [hz, rep_coe _ (by linarith [rep_nonneg z]) h]

/-- Wraparound: subtracting `β` from a point below `β` lands `1 - β` higher. -/
theorem rep_sub_wrap (β : ℝ) (z : AddCircle (1 : ℝ)) (hβ1 : β ≤ 1)
    (h : rep z < β) :
    rep (z - (β : AddCircle (1 : ℝ))) = rep z - β + 1 := by
  have hz : z - (β : AddCircle (1 : ℝ))
      = ((rep z - β + 1 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add_period, AddCircle.coe_sub, coe_rep z]
  rw [hz, rep_coe _ (by linarith [rep_nonneg z]) (by linarith [rep_lt_one z])]

/-- No wraparound in the backward direction. -/
theorem rep_sub_step (β : ℝ) (z : AddCircle (1 : ℝ)) (hβ : 0 ≤ β)
    (h : β ≤ rep z) :
    rep (z - (β : AddCircle (1 : ℝ))) = rep z - β := by
  have hz : z - (β : AddCircle (1 : ℝ)) = ((rep z - β : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub, coe_rep z]
  rw [hz, rep_coe _ (by linarith) (by linarith [rep_lt_one z])]

/-- Wraparound forward: past the cut the representative drops by one. -/
theorem rep_add_wrap (β : ℝ) (z : AddCircle (1 : ℝ)) (hβ1 : β ≤ 1)
    (h : 1 ≤ rep z + β) :
    rep (z + (β : AddCircle (1 : ℝ))) = rep z + β - 1 := by
  have hz : z + (β : AddCircle (1 : ℝ))
      = ((rep z + β - 1 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_add_period 1 (rep z + β - 1),
      show (rep z + β - 1 + 1 : ℝ) = rep z + β by ring,
      AddCircle.coe_add, coe_rep z]
  rw [hz, rep_coe _ (by linarith) (by linarith [rep_lt_one z])]

/-- The forward mask: the hop `z ↦ z + β` stays inside the chain. -/
def maskFwd (β : ℝ) : Set (AddCircle (1 : ℝ)) := {z | rep z + β < 1}

/-- **The masks compose.** This is the whole content of coherence: `z ∈ maskFwd a` and `z + a ∈
maskFwd b` ⟺ `z ∈ maskFwd (a + b)`. -/
theorem maskFwd_comp {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : AddCircle (1 : ℝ)) :
    (z ∈ maskFwd a ∧ z + (a : AddCircle (1 : ℝ)) ∈ maskFwd b)
      ↔ z ∈ maskFwd (a + b) := by
  simp only [maskFwd, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [rep_add_step a z ha h1] at h2
    linarith
  · intro h
    have h1 : rep z + a < 1 := by linarith
    refine ⟨h1, ?_⟩
    rw [rep_add_step a z ha h1]
    linarith

/-- **The pulled-back forward mask is the backward mask.** `z - β ∈ maskFwd β` exactly when `β ≤
rep z`: below the cut the step backward wraps, above it lands at `rep z - β`. -/
theorem mem_maskFwd_sub_iff {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (z : AddCircle (1 : ℝ)) :
    z - (β : AddCircle (1 : ℝ)) ∈ maskFwd β ↔ β ≤ rep z := by
  simp only [maskFwd, Set.mem_ofPred_eq]
  by_cases h : β ≤ rep z
  · rw [rep_sub_step β z hβ h]
    constructor
    · intro _; exact h
    · intro _; linarith [rep_lt_one z]
  · push Not at h
    rw [rep_sub_wrap β z hβ1 h]
    constructor
    · intro hc; linarith [rep_nonneg z]
    · intro hc; linarith

end Cvs.Operator
