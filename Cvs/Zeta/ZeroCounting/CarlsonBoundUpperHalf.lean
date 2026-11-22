import Mathlib
import Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `CarlsonBound` from Carlson's theorem in the upper half-plane, for fixed `½ < α < 1`

Carlson's density theorem is stated for the zeros with `α ≤ Re ρ` and `0 ≤ Im ρ ≤ T` at a fixed `α ∈ (½, 1)`.
Conjugation `ζ(s̄) = conj ζ(s)` doubles it to the rectangle `|Im ρ| ≤ T`; at `σ = ½` the exponent is `1 + ε` and
the `O(T log T)` count of Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint suffices; at `σ = 1` the count is zero.
-/

noncomputable section

open Complex Filter Asymptotics Set
open Cvs.Zeta.ZeroCounting.ZeroDensityBlueprint (zeroBox N_zero zeroBox_finite N_zero_isBigO carlson_density_one CarlsonBound)

namespace Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf

/-- The zeros of `ζ` with `α ≤ Re s ≤ 1` and `0 ≤ Im s ≤ T`. -/
def upperBox (α T : ℝ) : Set ℂ := zeroBox α T ∩ {s | 0 ≤ s.im}

/-- The number of distinct zeros of `ζ` with `α ≤ Re s ≤ 1` and `0 ≤ Im s ≤ T`. -/
def upperCount (α T : ℝ) : ℕ := (upperBox α T).ncard

/-- Carlson's density theorem `N(α, T) = O(T^{4α(1−α)+ε})` for fixed `½ < α < 1` and `ε > 0`. -/
def CarlsonDensity : Prop :=
  ∀ α ε : ℝ, 1 / 2 < α → α < 1 → 0 < ε →
    (fun T : ℝ ↦ (upperCount α T : ℝ)) =O[atTop] (fun T : ℝ ↦ T ^ (4 * α * (1 - α) + ε))

/-- **Conjugation doubles the upper count**: `N(σ, T) ≤ 2·#{zeros with Im ≥ 0}`. -/
theorem N_zero_le_two_mul_upperCount {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    N_zero σ T ≤ 2 * upperCount σ T := by
  have hfin : (upperBox σ T).Finite := (zeroBox_finite hσ T).subset inter_subset_left
  have hsub : zeroBox σ T ⊆ upperBox σ T ∪ (starRingEnd ℂ) '' upperBox σ T := by
    intro s hs
    rcases le_or_gt 0 s.im with him | him
    · exact Or.inl ⟨hs, him⟩
    · refine Or.inr ⟨(starRingEnd ℂ) s, ⟨?_, ?_⟩, by simp⟩
      · obtain ⟨⟨h1, h2, h3, h4⟩, hz⟩ := hs
        refine ⟨⟨by simpa using h1, by simpa using h2, by simp; linarith, by simp; linarith⟩, ?_⟩
        show riemannZeta ((starRingEnd ℂ) s) = 0
        rw [riemannZeta_conj, show riemannZeta s = 0 from hz, map_zero]
      · show 0 ≤ ((starRingEnd ℂ) s).im
        simp only [conj_im]; linarith
  calc N_zero σ T ≤ (upperBox σ T ∪ (starRingEnd ℂ) '' upperBox σ T).ncard :=
        Set.ncard_le_ncard hsub (hfin.union (hfin.image _))
    _ ≤ (upperBox σ T).ncard + ((starRingEnd ℂ) '' upperBox σ T).ncard :=
        Set.ncard_union_le _ _
    _ ≤ (upperBox σ T).ncard + (upperBox σ T).ncard :=
        Nat.add_le_add_left (Set.ncard_image_le hfin) _
    _ = 2 * upperCount σ T := by rw [upperCount]; ring

/-- `T log T = O(T^{1+ε})` for every `ε > 0`. -/
theorem mul_log_isBigO_rpow {ε : ℝ} (hε : 0 < ε) :
    (fun T : ℝ ↦ T * Real.log T) =O[atTop] (fun T : ℝ ↦ T ^ (1 + ε)) := by
  have h := ((isBigO_refl (fun T : ℝ ↦ T) atTop).mul (isLittleO_log_rpow_atTop hε).isBigO)
  refine h.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [Real.rpow_add hT, Real.rpow_one]

/-- **Carlson's bound on `[½, 1]` from Carlson's density theorem on `(½, 1)`.** -/
theorem carlsonBound_of_carlsonDensity (h : CarlsonDensity) : CarlsonBound := by
  intro σ ε hσ hσ1 hε
  rcases eq_or_lt_of_le hσ with he | hlt
  · subst he
    refine (N_zero_isBigO (by norm_num)).trans ?_
    have e : 4 * (1 / 2 : ℝ) * (1 - 1 / 2) + ε = 1 + ε := by ring
    rw [e]
    exact mul_log_isBigO_rpow hε
  rcases eq_or_lt_of_le hσ1 with he1 | hlt1
  · subst he1; exact carlson_density_one ε
  refine IsBigO.trans ?_ (h σ ε hlt hlt1 hε)
  refine IsBigO.of_bound 2 (Eventually.of_forall fun T => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast N_zero_le_two_mul_upperCount (by linarith) T

end Cvs.Zeta.ZeroCounting.CarlsonBoundUpperHalf

end
