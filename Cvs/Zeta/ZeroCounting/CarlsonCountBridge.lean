import Mathlib
import Cvs.Zeta.GaussKernel.AdmissibleKernel
import Cvs.Zeta.GaussKernel.RealSegmentClosed
import Cvs.Zeta.GaussKernel.RiemannHypothesisTarget
import Cvs.Zeta.GaussKernel.ZetaZeroStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real

/-!
# The counting-convention bridge

`Cvs.Zeta.GaussKernel.AdmissibleKernel.ZeroDensity` is stated over `offLineCount d T` — zeros with `|re - 1/2| ≥ d` and `|im|
≤ T`, counting both sides of the line and both signs of the ordinate.
-/

namespace Cvs.GaussKernel

open Cvs.Zeta.GaussKernel.AdmissibleKernel

/-! ### The orbit stays in the zero set -/

/-- Conjugation preserves the non-trivial zeros; `re` is unchanged. -/
theorem conj_mem {ρ : ℂ} (h : ρ ∈ nonTrivialZeroSet) :
    (starRingEnd ℂ) ρ ∈ nonTrivialZeroSet := by
  obtain ⟨hz, h0, h1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_conj, hz, map_zero]
  · simpa using h0
  · simpa using h1

/-- **Reflection across the line.** In the strip both `Gammaℝ s` and `Gammaℝ (1-s)` are non-zero,
so `ζ s = 0` forces `Λ s = 0`, hence `Λ (1-s) = 0`, hence `ζ (1-s) = 0`. -/
theorem one_sub_mem {ρ : ℂ} (h : ρ ∈ nonTrivialZeroSet) :
    1 - ρ ∈ nonTrivialZeroSet := by
  obtain ⟨hz, h0, h1⟩ := h
  have hre : (1 - ρ).re = 1 - ρ.re := by simp
  have hG : Complex.Gammaℝ ρ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hρ0 : ρ ≠ 0 := fun hc => by rw [hc] at h0; simp at h0
  have hL : completedRiemannZeta ρ = 0 := by
    have hdef := riemannZeta_def_of_ne_zero hρ0
    rw [hz] at hdef
    rcases div_eq_zero_iff.mp hdef.symm with h' | h'
    · exact h'
    · exact absurd h' hG
  have hre1 : (0 : ℝ) < (1 - ρ).re := by rw [hre]; linarith
  have hG1 : Complex.Gammaℝ (1 - ρ) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre1
  have hs1 : (1 : ℂ) - ρ ≠ 0 := fun hc => by rw [hc] at hre1; simp at hre1
  refine ⟨?_, hre1, by rw [hre]; linarith⟩
  rw [riemannZeta_def_of_ne_zero hs1, completedRiemannZeta_one_sub, hL, zero_div]

/-- Conjugation, on the subtype. -/
noncomputable def conjZ (ρ : nonTrivialZeroSet) : nonTrivialZeroSet :=
  ⟨(starRingEnd ℂ) (ρ : ℂ), conj_mem ρ.2⟩

/-- Reflection, on the subtype. -/
noncomputable def oneSubZ (ρ : nonTrivialZeroSet) : nonTrivialZeroSet :=
  ⟨1 - (ρ : ℂ), one_sub_mem ρ.2⟩

@[simp] theorem conjZ_re (ρ : nonTrivialZeroSet) : ((conjZ ρ : ℂ)).re = ((ρ : ℂ)).re := by
  simp [conjZ]

@[simp] theorem conjZ_im (ρ : nonTrivialZeroSet) : ((conjZ ρ : ℂ)).im = -((ρ : ℂ)).im := by
  simp [conjZ]

@[simp] theorem oneSubZ_re (ρ : nonTrivialZeroSet) :
    ((oneSubZ ρ : ℂ)).re = 1 - ((ρ : ℂ)).re := by simp [oneSubZ]

@[simp] theorem oneSubZ_im (ρ : nonTrivialZeroSet) :
    ((oneSubZ ρ : ℂ)).im = -((ρ : ℂ)).im := by simp [oneSubZ]

/-! ### The textbook counting function -/

/-- `N(σ, T)`'s index set: `re ≥ σ`, `0 < im ≤ T`. -/
def carlsonSet (σ T : ℝ) : Set nonTrivialZeroSet :=
  {ρ | σ ≤ ((ρ : ℂ)).re ∧ 0 < ((ρ : ℂ)).im ∧ ((ρ : ℂ)).im ≤ T}

theorem carlsonSet_finite (σ T : ℝ) : (carlsonSet σ T).Finite := by
  refine (finite_window_of_summable (fun ρ : nonTrivialZeroSet => ((ρ : ℂ)).im)
    summable_zeta_quartic T).subset ?_
  rintro ρ ⟨-, hpos, hle⟩
  exact abs_le.mpr ⟨by linarith, hle⟩

/-- `N(σ, T)`, in the convention density theorems are stated in. -/
noncomputable def carlsonCount (σ T : ℝ) : ℕ := (carlsonSet_finite σ T).toFinset.card

/-! ### The orbit representative -/

/-- The member of `ρ`'s orbit that sits in `N(1/2 + d, T)`'s region: push `re`
to the right of the line with `1 - ·` if needed, then `im` above the axis with
conjugation if needed. -/
noncomputable def pick (ρ : nonTrivialZeroSet) : nonTrivialZeroSet :=
  if 1 / 2 ≤ ((ρ : ℂ)).re then
    (if 0 < ((ρ : ℂ)).im then ρ else conjZ ρ)
  else
    (if 0 < ((ρ : ℂ)).im then oneSubZ (conjZ ρ) else oneSubZ ρ)

theorem pick_re {d : ℝ} {ρ : nonTrivialZeroSet} (hd : d ≤ |((ρ : ℂ)).re - 1 / 2|) :
    1 / 2 + d ≤ ((pick ρ : ℂ)).re := by
  rw [pick]
  split_ifs with h1 h2 h2
  · have h := hd; rw [abs_of_nonneg (by linarith)] at h; linarith
  · have h := hd; rw [abs_of_nonneg (by linarith)] at h; rw [conjZ_re]; linarith
  · have h := hd; rw [abs_of_nonpos (by linarith [not_le.mp h1])] at h
    rw [oneSubZ_re, conjZ_re]; linarith
  · have h := hd; rw [abs_of_nonpos (by linarith [not_le.mp h1])] at h
    rw [oneSubZ_re]; linarith

theorem pick_im_pos {ρ : nonTrivialZeroSet} (h : ((ρ : ℂ)).im ≠ 0) :
    0 < ((pick ρ : ℂ)).im := by
  rw [pick]
  split_ifs with h1 h2 h2
  · exact h2
  · rw [conjZ_im]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · linarith
    · exact absurd hgt h2
  · rw [oneSubZ_im, conjZ_im]; linarith
  · rw [oneSubZ_im]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · linarith
    · exact absurd hgt h2

theorem pick_im_le {T : ℝ} {ρ : nonTrivialZeroSet} (h : |((ρ : ℂ)).im| ≤ T) :
    ((pick ρ : ℂ)).im ≤ T := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  rw [pick]
  split_ifs
  · exact h2
  · rw [conjZ_im]; linarith
  · rw [oneSubZ_im, conjZ_im]; linarith
  · rw [oneSubZ_im]; linarith

/-- **`ρ` is recoverable from `pick ρ`**, as one of four orbit members.  This is
what makes the map at most four-to-one. -/
theorem mem_orbit_pick (ρ : nonTrivialZeroSet) :
    ((ρ : ℂ)) ∈ ({((pick ρ : ℂ)), 1 - ((pick ρ : ℂ)),
      (starRingEnd ℂ) ((pick ρ : ℂ)),
      1 - (starRingEnd ℂ) ((pick ρ : ℂ))} : Finset ℂ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, pick]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl (by simp [conjZ])))
  · exact Or.inr (Or.inr (Or.inr (by simp [conjZ, oneSubZ])))
  · exact Or.inr (Or.inl (by simp [oneSubZ]))

/-! ### The bridge -/

private theorem card_quad_le (a b c e : ℂ) : ({a, b, c, e} : Finset ℂ).card ≤ 4 := by
  calc ({a, b, c, e} : Finset ℂ).card ≤ ({b, c, e} : Finset ℂ).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (({c, e} : Finset ℂ).card + 1) + 1 := by
        have := Finset.card_insert_le b ({c, e} : Finset ℂ); omega
    _ ≤ ((({e} : Finset ℂ).card + 1) + 1) + 1 := by
        have := Finset.card_insert_le c ({e} : Finset ℂ); omega
    _ = 4 := by simp

/-- **The counting-convention bridge.**  Every zero counted by `offLineCount`
has an orbit member counted by `N(1/2 + d, T)`, and at most four zeros share
one.  So a density theorem in the textbook convention transfers. -/
theorem offLineCount_le_four_mul_carlsonCount {d : ℝ} (hd : 0 < d) (T : ℝ) :
    offLineCount d T ≤ 4 * carlsonCount (1 / 2 + d) T := by
  classical
  rw [offLineCount, carlsonCount]
  refine Finset.card_le_mul_card_image_of_maps_to (f := pick) (fun ρ hρ => ?_) 4
    (fun σ _ => ?_)
  · rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨him, hre⟩ := hρ
    have hne : ((ρ : ℂ)).re ≠ 1 / 2 := by
      intro hc
      rw [hc] at hre
      simp at hre
      linarith
    exact ⟨pick_re hre, pick_im_pos (Cvs.GaussKernel.noRealOffLineZero ρ hne), pick_im_le him⟩
  · refine le_trans (Finset.card_le_card_of_injOn (fun ρ => ((ρ : ℂ)))
      (t := ({((σ : ℂ)), 1 - ((σ : ℂ)), (starRingEnd ℂ) ((σ : ℂ)),
        1 - (starRingEnd ℂ) ((σ : ℂ))} : Finset ℂ)) (fun ρ hρ => ?_) ?_)
      (card_quad_le _ _ _ _)
    · have hpick : pick ρ = σ := (Finset.mem_filter.mp hρ).2
      have h := mem_orbit_pick ρ
      rwa [hpick] at h
    · intro a _ b _ hab
      exact Subtype.ext hab

/-- **The density estimate in the textbook convention suffices.**  If
`N(σ, T) = o(T)` for every `σ > 1/2`, then `Cvs.Zeta.GaussKernel.AdmissibleKernel.ZeroDensity` holds, hence
`WindowRecordStalls`, and the last hypothesis of `Cvs.Zeta.GaussKernel.AdmissibleKernel` is discharged. -/
theorem zeroDensity_of_carlson
    (h : ∀ d : ℝ, 0 < d →
      Filter.Tendsto (fun T : ℝ => (carlsonCount (1 / 2 + d) T : ℝ) / T)
        Filter.atTop (nhds 0)) :
    ZeroDensity := by
  intro d hd
  have hsq : Filter.Tendsto
      (fun T : ℝ => 4 * ((carlsonCount (1 / 2 + d) T : ℝ) / T))
      Filter.atTop (nhds 0) := by
    simpa using (h d hd).const_mul (4 : ℝ)
  refine squeeze_zero' ?_ ?_ hsq
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hT.le
    exact_mod_cast offLineCount_le_four_mul_carlsonCount hd T

end Cvs.GaussKernel
