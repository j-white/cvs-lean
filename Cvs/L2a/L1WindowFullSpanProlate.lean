import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.FullSpanFromScale
import Cvs.L2a.FullSpanProlateFamily
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFullSpanProlate
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# SPINE-L1 on the full span of the prolate family at `c = 2πx`

The spine profile `Σ_j a_j(h_{4j} − α_jh₀)`, `j ∈ S ⊆ [1, x)`, is the span over `Option S` of Cvs.L2a.WindowFullSpanProlate; `WindowChainInputsProlate`'s floor
`κ_F = kapFX x`, Landau's `λ_min = ½` and Cvs.L2a.L1WindowFromFloor give `QW(k_G) ≤ L1bound·N` at every `x` with `c₀^W ≤ 2πx`: the upper
companion of `WindowFullSpanProlate`'s floor on the same vectors.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.L1WindowFullSpanProlate

open Cvs.L2a.ProlateFamilySpine (kOf bOf sum_option_eq_spineG sum_option_pole)
open Cvs.L2a.WindowChainInputsProlate (c0W kapFX)
open Cvs.L2a.WindowFullSpanProlate (extN sum_extN)

/-- **SPINE-L1 on the full span**: for `c₀^W ≤ 2πx`, `S ⊆ [1, x)` and `a ≠ 0`, at `c = 2πx`,
`QW(k_G) ≤ L1bound c κ_F ½ b μ h h₁ h₂ · N` with `b = bOf c a`, `h = rung c (kOf ·)`, `μ = muR c (kOf ·)`,
`κ_F = kapFX x`, `N = tailN c b h`. -/
theorem L1_window_full (x : ℕ) (hx : c0W ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, 1 ≤ j ∧ j < x)
    (a : S → ℝ) (ha : ∃ j, a j ≠ 0) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
        (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a)))
      ≤ Cvs.L2a.L1WindowFromFloor.L1bound (2 * π * x) (kapFX x) (1 / 2) (bOf (2 * π * x) a)
          (fun i => muR (2 * π * x) (kOf i)) (fun i => rung (2 * π * x) (kOf i))
          (fun i => rung₁ (2 * π * x) (kOf i)) (fun i => rung₂ (2 * π * x) (kOf i))
        * Cvs.L2a.L1WindowFromFloor.tailN (2 * π * x) (bOf (2 * π * x) a) (fun i => rung (2 * π * x) (kOf i)) := by
  set c : ℝ := 2 * π * x with hcdef
  have hxF : Cvs.L2a.FullSpanThreshold.c0F ≤ c := le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx
  obtain ⟨-, hc80⟩ := Cvs.L2a.BandInputsFromCutMultipliers.scale_ge hxF
  have hc0 : 0 < c := by linarith
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp [hcdef] at hc80; linarith
    · exact h
  -- the levels
  have hex : ∀ i : Option S, ∃ χ, IsLevelIdx c (kOf i) χ := by
    rintro (_ | j)
    · exact exists_isLevelIdx_zero c
    · exact Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 ⟨j, Finset.mem_range.2 (hS j j.2).2⟩
  have hcnt : ∀ i : Option S, (evenSpec (sqC c) ∩ Iio (lev c (kOf i))).ncard = kOf i := fun i =>
    (lev_spec (hex i)).2
  have hkpos : ∀ j : S, 2 ≤ kOf (some j) := fun j => by
    simp only [kOf, Option.elim]; have := (hS j j.2).1; omega
  have hJ : (Fintype.card (Option S) : ℝ) ≤ c / 4 + 1 := by
    have h0S : 0 ∉ S := fun h => by have := (hS 0 h).1; omega
    have hsub : S ⊆ Finset.range x := fun j hj => Finset.mem_range.2 (hS j hj).2
    have hlt : S.card < (Finset.range x).card :=
      Finset.card_lt_card ⟨hsub, fun hsub' => h0S (hsub' (Finset.mem_range.2 hx1))⟩
    have hle : ((Fintype.card (Option S) : ℕ) : ℝ) ≤ x := by
      rw [Fintype.card_option, Fintype.card_coe]
      rw [Finset.card_range] at hlt
      exact_mod_cast hlt
    exact hle.trans (Cvs.L2a.FullSpanProlateFamily.x_le x)
  obtain ⟨hP, hR⟩ := sizes_PR hx1
  have hspec := fun i => rung_spec (hex i)
  have hχc : ∀ i : Option S, lev c (kOf i) < c ^ 2 := by
    rintro (_ | j)
    · show lev c 0 < c ^ 2
      rw [lev_zero]
      have := groundLevel_le c
      nlinarith
    · exact (Cvs.L2a.FullSpanFromScale.span_data hc80).2.1 ⟨j, Finset.mem_range.2 (hS j j.2).2⟩
  have hlam : ∀ i : Option S, i ≠ none → 1 / 2 ≤ (muR c (kOf i) * √(c / (2 * π))) ^ 2 := by
    rintro (_ | j) hne
    · exact absurd rfl hne
    · exact Cvs.L2a.WindowChainInputsProlate.half_le_lamR hc80 (hS j j.2).2
  -- the floor, from `Finset.range x`
  set b := bOf c a with hbd
  have hΦ : (fun ξ => ∑ j : Finset.range x, extN b j * psi c (rung c (2 * (j : ℕ))) ξ)
      = fun ξ => ∑ i : Option S, b i * psi c (rung c (kOf i)) ξ := by
    funext ξ
    exact sum_extN hx1 hS b (fun t n => t * psi c (rung c n) ξ) fun _ => zero_mul _
  have hPm : ∑ j : Finset.range x, extN b j ^ 2 * (∫ ξ in Ioi 1, psi c (rung c (2 * (j : ℕ))) ξ ^ 2)
      = ∑ i : Option S, b i ^ 2 * (∫ ξ in Ioi 1, psi c (rung c (kOf i)) ξ ^ 2) :=
    sum_extN hx1 hS b (fun t n => t ^ 2 * ∫ ξ in Ioi 1, psi c (rung c n) ξ ^ 2) fun _ => by simp
  obtain ⟨h38, hfl⟩ := Cvs.L2a.WindowChainInputsProlate.floor_full_span x hxF fun j => extN b j
  rw [hΦ, hPm] at hfl
  have hκF : 0 < kapFX x := lt_of_lt_of_le (by norm_num) h38
  have hb : ∃ i, b i ≠ 0 := by
    obtain ⟨j, hj⟩ := ha
    exact ⟨some j, by simpa [hbd, bOf] using hj⟩
  rw [← sum_option_eq_spineG]
  refine Cvs.L2a.L1WindowFromFloor.L1_window_of (ι := Option S) none
    (h := fun i => rung c (kOf i)) (h₁ := fun i => rung₁ c (kOf i)) (h₂ := fun i => rung₂ c (kOf i))
    (χ := fun i => lev c (kOf i)) (μ := fun i => muR c (kOf i)) b
    (fun i => (hspec i).1) (fun i => (hspec i).2.1) (fun i => (hspec i).2.2.1) (fun i => (hspec i).2.2.2.1) hc80
    (fun i => nonneg_of_mem_evenSpec c (lev_spec (hex i)).1) hχc ?_ (fun i => (hspec i).2.2.2.2.1)
    (fun i => (hspec i).2.2.2.2.2) (fun i => psi_rung (hex i)) (hcnt none) ?_ hJ
    (by norm_num : (0 : ℝ) < 1 / 2) hlam hκF hfl (sum_option_pole hc0 a) hP hR hb
  · -- distinct levels
    intro i i' he
    have hk' : kOf i = kOf i' := by
      have h1 := hcnt i
      have h2 := hcnt i'
      simp only at he
      rw [he] at h1
      omega
    rcases i with _ | j <;> rcases i' with _ | j'
    · rfl
    · have := hkpos j'; simp only [kOf, Option.elim] at hk' this; omega
    · have := hkpos j; simp only [kOf, Option.elim] at hk' this; omega
    · simp only [kOf, Option.elim] at hk'
      exact congrArg some (Subtype.ext (by omega))
  · -- even counts
    intro i
    rw [hcnt i]
    rcases i with _ | j
    · exact ⟨0, rfl⟩
    · exact ⟨j, by simp only [kOf, Option.elim]; ring⟩

end Cvs.L2a.L1WindowFullSpanProlate
