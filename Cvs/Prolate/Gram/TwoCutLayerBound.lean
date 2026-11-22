import Mathlib
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.Upstream.PencilLayerBound
import Cvs.Upstream.SchurLayerFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two-cut layer bound and (WF₂)

Cutting Theorem A at a bulk rung `k₀` and a plunge rung `k_p ≥ k₀`:
`λ_max(diag μ, C) ≤ m/F_{k₀} + μ_t/F_{k_p} + Σ_{k < k₀} δ_k/F_k` with `m ≥ Σ_{k₀ ≤ k < k_p} δ_k`.
(WF₂) asks for a bulk floor `φ₀` and a plunge floor `φ_p` with `C₀∞(m/φ₀ + μ*/φ_p) < 2`; with (EF′) it gives (B).
(WF′) is the case `k_p = k₀`, `m = 0`.
-/

noncomputable section

open Real Set Matrix Finset Filter Topology

namespace Cvs.Prolate.Gram.TwoCutLayerBound
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram mu muInc levT)
open Cvs.Route.Visibility.LayerFloorDeepRemainderB (cE floorC C0 C0inf muStar CondB WFprime EFprime)

/-- **The two-cut layer bound**: for `k₀ ≤ k_p` and `Σ_{k₀ ≤ k < k_p} δ_k ≤ m`,
`c_E^C ≤ m/F_{k₀} + μ_t/F_{k_p} + Σ_{k < k₀} δ_k/F_k`. -/
theorem cE_le_twoCut {x : ℕ} (hx : 80 ≤ 2 * π * x) {k₀ kp : Fin x} (hk : k₀ ≤ kp) {m : ℝ}
    (hm : ∑ k ∈ univ.filter (fun k : Fin x => k₀ ≤ k ∧ k < kp), muInc x k ≤ m) :
    cE x ≤ m / floorC x k₀ + mu x (x - 1) / floorC x kp
      + ∑ k ∈ univ.filter (· < k₀), muInc x k / floorC x k := by
  have hM := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_posDef hx
  have hδ : ∀ k : Fin x, 0 ≤ muInc x k := fun k => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.muInc_nonneg hx k.2
  have hA := Cvs.Upstream.PencilLayerBound.pencilTop_le_layer hM (μ := fun n : Fin x => mu x n) (δ := fun k : Fin x => muInc x k) hδ
    (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_eq_sum x)
  have hF : ∀ k, floorC x k = Cvs.Upstream.PencilLayerBound.layerFloor hM k := Cvs.Route.Visibility.LayerFloorDeepRemainderB.floorC_eq hx
  have hFpos : ∀ k, 0 < floorC x k := fun k => (hF k) ▸ Cvs.Upstream.PencilLayerBound.layerFloor_pos hM k
  have hmono : ∀ {a b : Fin x}, a ≤ b → floorC x a ≤ floorC x b := fun hab => by
    rw [hF, hF]; exact Cvs.Upstream.SchurLayerFloors.layerFloor_mono hM hab
  change cE x ≤ _ at hA
  simp only [← hF] at hA
  set f : Fin x → ℝ := fun k => muInc x k / floorC x k
  have hsplit : ∑ k, f k = ∑ k ∈ univ.filter (· < k₀), f k
      + ∑ k ∈ univ.filter (fun k : Fin x => k₀ ≤ k ∧ k < kp), f k + ∑ k ∈ univ.filter (kp ≤ ·), f k := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (· < k₀)]
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter fun k : Fin x => ¬ k < k₀) (· < kp)]
    rw [Finset.filter_filter, Finset.filter_filter, add_assoc]
    congr 2
    · congr 1; ext k; simp [not_lt]
    · congr 1; ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hk.trans h, h⟩
  have hmid : ∑ k ∈ univ.filter (fun k : Fin x => k₀ ≤ k ∧ k < kp), f k ≤ m / floorC x k₀ := by
    calc _ ≤ ∑ k ∈ univ.filter (fun k : Fin x => k₀ ≤ k ∧ k < kp), muInc x k / floorC x k₀ := by
          refine Finset.sum_le_sum fun k hk' => ?_
          simp only [Finset.mem_filter] at hk'
          exact div_le_div_of_nonneg_left (hδ k) (hFpos k₀) (hmono hk'.2.1)
      _ = (∑ k ∈ univ.filter (fun k : Fin x => k₀ ≤ k ∧ k < kp), muInc x k) / floorC x k₀ := by
          rw [Finset.sum_div]
      _ ≤ m / floorC x k₀ := div_le_div_of_nonneg_right hm (hFpos k₀).le
  have htop : ∑ k ∈ univ.filter (kp ≤ ·), f k ≤ mu x (x - 1) / floorC x kp := by
    have h2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx
    have hsum : ∑ k ∈ univ.filter (kp ≤ ·), muInc x k ≤ mu x (x - 1) := by
      have e := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_eq_sum x (Cvs.Route.Visibility.LayerFloorDeepRemainderB.top hx)
      have hall : univ.filter (· ≤ Cvs.Route.Visibility.LayerFloorDeepRemainderB.top hx) = (univ : Finset (Fin x)) := by
        ext k; simp [Cvs.Route.Visibility.LayerFloorDeepRemainderB.le_top hx k]
      rw [hall] at e
      simp only [Cvs.Route.Visibility.LayerFloorDeepRemainderB.top] at e
      rw [e]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => hδ k
    calc _ ≤ ∑ k ∈ univ.filter (kp ≤ ·), muInc x k / floorC x kp := by
          refine Finset.sum_le_sum fun k hk' => ?_
          simp only [Finset.mem_filter] at hk'
          exact div_le_div_of_nonneg_left (hδ k) (hFpos kp) (hmono hk'.2)
      _ = (∑ k ∈ univ.filter (kp ≤ ·), muInc x k) / floorC x kp := by rw [Finset.sum_div]
      _ ≤ mu x (x - 1) / floorC x kp := div_le_div_of_nonneg_right hsum (hFpos kp).le
  calc cE x ≤ ∑ k, f k := hA
    _ ≤ _ := by rw [hsplit]; linarith

/-- **(WF₂)** at the cut `T₀`: a bulk floor `φ₀` at the first rung `k₀` of `{T ≥ T₀}`, a plunge floor `φ_p` at a rung
`k_p ≥ k₀` with `Σ_{k₀ ≤ k < k_p} δ_k ≤ m`, and `C₀∞(m/φ₀ + μ*/φ_p) < 2`. -/
def WFtwo (Wt T₀ : ℝ) : Prop :=
  ∃ m φ₀ φp : ℝ, 0 ≤ m ∧ 0 < φ₀ ∧ 0 < φp ∧ C0inf Wt * (m / φ₀ + muStar / φp) < 2 ∧
    ∀ᶠ x : ℕ in atTop, ∃ k₀ kp : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀) ∧ k₀ ≤ kp ∧
      ∑ k ∈ univ.filter (fun k : Fin x => k₀ ≤ k ∧ k < kp), muInc x k ≤ m ∧ φ₀ ≤ floorC x k₀ ∧ φp ≤ floorC x kp

/-- (WF′) is the case `k_p = k₀`, `m = 0` of (WF₂). -/
theorem wfTwo_of_wfprime {Wt T₀ : ℝ} (h : WFprime Wt T₀) : WFtwo Wt T₀ := by
  obtain ⟨ε, hε, hev⟩ := h
  have hthr : 0 < muStar * C0inf Wt / 2 := by
    have := Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos; have := Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0inf_pos Wt; positivity
  set φ := muStar * C0inf Wt / 2 + ε
  have hφ : 0 < φ := by simp only [φ]; linarith
  refine ⟨0, φ, φ, le_rfl, hφ, hφ, ?_, ?_⟩
  · have : C0inf Wt * (0 / φ + muStar / φ) = 2 * ((muStar * C0inf Wt / 2) / φ) := by
      field_simp; ring
    rw [this]
    have : (muStar * C0inf Wt / 2) / φ < 1 := (div_lt_one hφ).2 (by simp only [φ]; linarith)
    linarith
  · filter_upwards [hev] with x ⟨k₀, h1, h2, h3⟩
    refine ⟨k₀, k₀, h1, h2, le_rfl, ?_, h3, h3⟩
    have : univ.filter (fun k : Fin x => k₀ ≤ k ∧ k < k₀) = ∅ := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun ⟨a, b⟩ => absurd (lt_of_le_of_lt a b) (lt_irrefl _)
    rw [this, Finset.sum_empty]

/-- **Theorem B₂**: (WF₂) and (EF′) at one cut `T₀` give (B), for every `C₁`. -/
theorem condB_of_wfTwo_ef {Wt C₁ T₀ : ℝ} (hW : WFtwo Wt T₀) (hE : EFprime T₀) : CondB Wt C₁ := by
  obtain ⟨m, φ₀, φp, hm0, hφ₀, hφp, hlt, hev⟩ := hW
  set L := C0inf Wt * (m / φ₀ + muStar / φp)
  set κ := (L + 2) / 2
  refine ⟨κ, by simp only [κ]; linarith, ?_⟩
  have hlim : Tendsto (fun x : ℕ => C0 Wt C₁ x * (m / φ₀ + muStar / φp
      + ∑ k ∈ univ.filter (fun k : Fin x => levT x k < T₀), muInc x k / floorC x k)) atTop (𝓝 L) := by
    have := (Cvs.Route.Visibility.LayerFloorDeepRemainderB.tendsto_C0 Wt C₁).mul ((tendsto_const_nhds (x := m / φ₀ + muStar / φp)).add hE)
    simpa [L] using this
  filter_upwards [hev, Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale, hlim.eventually (gt_mem_nhds (show L < κ by simp only [κ]; linarith))]
    with x ⟨k₀, kp, h1, h2, hk, hm, h3, h4⟩ hx hlt'
  have hF0 : 0 < floorC x k₀ := lt_of_lt_of_le hφ₀ h3
  have hFp : 0 < floorC x kp := lt_of_lt_of_le hφp h4
  have hw := cE_le_twoCut hx hk hm
  rw [Cvs.Route.Visibility.LayerFloorDeepRemainderB.filter_lt_eq hx h1 h2] at hw
  have hm1 : m / floorC x k₀ ≤ m / φ₀ := div_le_div_of_nonneg_left hm0 hφ₀ h3
  have hmu : mu x (x - 1) / floorC x kp ≤ muStar / φp := by
    have hm0' : 0 ≤ mu x (x - 1) := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_nonneg hx (by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega)
    calc mu x (x - 1) / floorC x kp ≤ muStar / floorC x kp :=
          div_le_div_of_nonneg_right (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.mu_top_le hx) hFp.le
      _ ≤ muStar / φp := div_le_div_of_nonneg_left Cvs.Route.Visibility.LayerFloorDeepRemainderB.muStar_pos.le hφp h4
  calc C0 Wt C₁ x * cE x
      ≤ C0 Wt C₁ x * (m / φ₀ + muStar / φp
          + ∑ k ∈ univ.filter (fun k : Fin x => levT x k < T₀), muInc x k / floorC x k) :=
        mul_le_mul_of_nonneg_left (hw.trans (by linarith)) (Cvs.Route.Visibility.LayerFloorDeepRemainderB.C0_nonneg _ _ _)
    _ ≤ κ := hlt'.le

end Cvs.Prolate.Gram.TwoCutLayerBound
