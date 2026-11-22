import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.FullSpanFromScale
import Cvs.L2a.FullSpanProlateFamily
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullSpanWiring
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainFromInputs
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFormDeepSpan
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.WindowFormBoundedBelow
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# SPINE-L2a(5) on the full span of the prolate family at `c = 2πx`

The spine profile `Σ_j a_j(h_{4j} − α_jh₀)`, `j ∈ S ⊆ [k, x)`, is `ProlateFamilySpine`'s span over `Option S`; its zero extension
to `Finset.range x` carries `WindowChainInputsProlate`'s floor and `FullSpanFromScale`'s full-tail bound to it, Landau's half gives `λ_min = ½`, and
`WindowChainFromInputs`'s window chain gives `ProlateFamilySpine`'s statement with `Finset.range x` for `deepSet x` and `c₀^W` for `c₀`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.WindowFullSpanProlate

open Cvs.L2a.ProlateFamilySpine (kOf bOf sum_option_eq_spineG sum_option_pole window_zero)
open Cvs.L2a.WindowFormDeepSpan (Hx)
open Cvs.L2a.WindowChainInputsProlate (c0W kapFX)

/-! ### The zero extension to `Finset.range x` -/

/-- The coefficient of `h_{4n}` in a span over `Option S`: `b_none` at `n = 0`, `b_n` for `n ∈ S`, `0` otherwise. -/
def extN {S : Finset ℕ} (b : Option S → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then b none else if h : n ∈ S then b (some ⟨n, h⟩) else 0

/-- **Re-indexing**: for `S ⊆ [1, x)` and `F(0, ·) = 0`, `Σ_{j<x} F(extN b j, 2j) = Σ_{i : Option S} F(bᵢ, k(i))`. -/
theorem sum_extN {x : ℕ} (hx : 1 ≤ x) {S : Finset ℕ} (hS : ∀ j ∈ S, 1 ≤ j ∧ j < x) (b : Option S → ℝ)
    (F : ℝ → ℕ → ℝ) (hF : ∀ k, F 0 k = 0) :
    ∑ j : Finset.range x, F (extN b j) (2 * (j : ℕ)) = ∑ i : Option S, F (b i) (kOf i) := by
  rw [Fintype.sum_option, Finset.sum_coe_sort (Finset.range x) (fun n => F (extN b n) (2 * n)),
    ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hx)]
  have h0 : F (extN b 0) (2 * 0) = F (b none) (kOf (none : Option S)) := by simp [extN, kOf]
  rw [h0]
  congr 1
  have hsub : S ⊆ (Finset.range x).erase 0 := fun j hj =>
    Finset.mem_erase.2 ⟨by have := (hS j hj).1; omega, Finset.mem_range.2 (hS j hj).2⟩
  rw [← Finset.sum_subset hsub fun n hn hnS => by
    have hn0 : n ≠ 0 := (Finset.mem_erase.1 hn).1
    simp [extN, hn0, hnS, hF]]
  rw [← Finset.sum_coe_sort S (fun n => F (extN b n) (2 * n))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj0 : (j : ℕ) ≠ 0 := by have := (hS j j.2).1; omega
  simp [extN, hj0, kOf]

/-! ### SPINE-L2a(5) on the full span -/

private theorem spineG_harmonic_energy {c : ℝ} (hc : 0 < c) {S : Finset ℕ} (a : S → ℝ) :
    ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / c) (spineG c a) θ ^ 2
      ≤ Hx c / 2 * ∫ s in (-1 : ℝ)..1, spineG c a s ^ 2 := by
  have hr : ∀ k, ContinuousOn (rung c k) (Icc (-1 : ℝ) 1) := fun k =>
    (Cvs.Approximant.DeepIndexSpineSpan.continuousOn_rawRung c (lev c k)).div_const _
  have hGc : ContinuousOn (spineG c a) (Icc (-1 : ℝ) 1) :=
    continuousOn_finsetSum _ fun j _ =>
      continuousOn_const.mul ((hr _).sub (continuousOn_const.mul (hr 0)))
  have hraw (χ s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      (rawRung c χ).1 (-s) = (rawRung c χ).1 s := by
    by_cases hχ : χ ∈ evenSpec (sqC c)
    · exact (rawRung_spec hχ).2.2.2.2.1 s hs
    · simp [rawRung, hχ]
  have he (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) : rung c k (-s) = rung c k s := by
    unfold rung
    rw [hraw (lev c k) s hs]
  have hGeven : ∀ s ∈ Icc (-1 : ℝ) 1, spineG c a (-s) = spineG c a s := by
    intro s hs
    unfold spineG
    exact Finset.sum_congr rfl fun j _ => by rw [he _ s hs, he 0 s hs]
  exact Cvs.Xi.EImageWindowPoisson.integral_window_sq_le_half (by positivity) hGc hGeven

/-- A proved window-energy budget gives the full-span floor at each actual scale. -/
theorem L2a_window_full_budget_of (x : ℕ) (hx : c0W ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j < x) {k : ℕ}
    (hk : 1 ≤ k) (hSk : ∀ j ∈ S, k ≤ j) (a : S → ℝ) {H : ℝ}
    (hH : 0 < H)
    (hwindow : ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ H / 2 * ∫ s in (-1 : ℝ)..1, spineG (2 * π * x) a s ^ 2) :
    π / (8 * (2 * π * x) * H * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) (2 * k))
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) := by
  set c : ℝ := 2 * π * x with hcdef
  have hxF : Cvs.L2a.FullSpanThreshold.c0F ≤ c := le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx
  obtain ⟨-, hc80⟩ := Cvs.L2a.BandInputsFromCutMultipliers.scale_ge hxF
  have hc0 : 0 < c := by linarith
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp at hc80; linarith
    · exact h
  rcases S.eq_empty_or_nonempty with hSe | ⟨j₀, hj₀⟩
  · -- the empty span: both sides vanish
    subst hSe
    have hG : spineG c a = fun _ => 0 := by
      funext s
      simp [spineG]
    have hL : Cvs.L2a.TailLogScaleTest.logScale (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
      funext s
      simp [Cvs.L2a.TailLogScaleTest.logScale]
    rw [hG, window_zero, hL, Cvs.WeilForm.WindowFormBoundedBelow.weilForm_zero]
    simp
  -- the levels
  have hS' : ∀ j ∈ S, 1 ≤ j ∧ j < x := fun j hj => ⟨le_trans hk (hSk j hj), hS j hj⟩
  have hex : ∀ i : Option S, ∃ χ, IsLevelIdx c (kOf i) χ := by
    rintro (_ | j)
    · exact exists_isLevelIdx_zero c
    · exact Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 ⟨j, Finset.mem_range.2 (hS j j.2)⟩
  have hexk : ∃ χ, IsLevelIdx c (2 * k) χ := by
    obtain ⟨χ, hχ⟩ := hex (some ⟨j₀, hj₀⟩)
    exact exists_isLevelIdx_of_le hχ (by simp only [kOf, Option.elim]; have := hSk j₀ hj₀; omega)
  have hcnt : ∀ i : Option S, (evenSpec (sqC c) ∩ Iio (lev c (kOf i))).ncard = kOf i := fun i =>
    (lev_spec (hex i)).2
  have hkpos : ∀ j : S, 2 * k ≤ kOf (some j) := fun j => by
    simp only [kOf, Option.elim]
    have := hSk j j.2
    omega
  -- the size
  have hJ : (Fintype.card (Option S) : ℝ) ≤ c / 4 + 1 := by
    have h0S : 0 ∉ S := fun h => by have := (hS' 0 h).1; omega
    have hsub : S ⊆ Finset.range x := fun j hj => Finset.mem_range.2 (hS j hj)
    have hlt : S.card < (Finset.range x).card :=
      Finset.card_lt_card ⟨hsub, fun hsub' => h0S (hsub' (Finset.mem_range.2 hx1))⟩
    have hle : ((Fintype.card (Option S) : ℕ) : ℝ) ≤ x := by
      rw [Fintype.card_option, Fintype.card_coe]
      rw [Finset.card_range] at hlt
      exact_mod_cast hlt
    exact hle.trans (Cvs.L2a.FullSpanProlateFamily.x_le x)
  obtain ⟨hP, hR⟩ := sizes_PR hx1
  have hspec := fun i => rung_spec (hex i)
  obtain ⟨hgd, hgd₁, hgd₂c, hgang, hgeven, hgnorm⟩ := rung_spec hexk
  -- the levels lie below `c²`
  have hχc : ∀ i : Option S, lev c (kOf i) < c ^ 2 := by
    rintro (_ | j)
    · show lev c 0 < c ^ 2
      rw [lev_zero]
      have := groundLevel_le c
      nlinarith
    · exact (Cvs.L2a.FullSpanFromScale.span_data hc80).2.1 ⟨j, Finset.mem_range.2 (hS j j.2)⟩
  -- Landau's half on the span
  have hlam : ∀ i : Option S, i ≠ none → 1 / 2 ≤ (muR c (kOf i) * √(c / (2 * π))) ^ 2 := by
    rintro (_ | j) hne
    · exact absurd rfl hne
    · exact Cvs.L2a.WindowChainInputsProlate.half_le_lamR hc80 (hS j j.2)
  -- the floor and the full-tail bound, from `Finset.range x`
  set b := bOf c a with hbd
  have hΦ : (fun ξ => ∑ j : Finset.range x, extN b j * psi c (rung c (2 * (j : ℕ))) ξ)
      = fun ξ => ∑ i : Option S, b i * psi c (rung c (kOf i)) ξ := by
    funext ξ
    exact sum_extN hx1 hS' b (fun t n => t * psi c (rung c n) ξ) fun _ => zero_mul _
  have hPm : ∑ j : Finset.range x, extN b j ^ 2 * (∫ ξ in Ioi 1, psi c (rung c (2 * (j : ℕ))) ξ ^ 2)
      = ∑ i : Option S, b i ^ 2 * (∫ ξ in Ioi 1, psi c (rung c (kOf i)) ξ ^ 2) :=
    sum_extN hx1 hS' b (fun t n => t ^ 2 * ∫ ξ in Ioi 1, psi c (rung c n) ξ ^ 2) fun _ => by simp
  obtain ⟨h38, hfl⟩ := Cvs.L2a.WindowChainInputsProlate.floor_full_span x hxF fun j => extN b j
  have hW := Cvs.L2a.WindowChainInputsProlate.fulltail_full_span x hxF fun j => extN b j
  rw [hΦ] at hfl hW
  rw [hPm] at hfl
  have hκF : 0 < kapFX x := lt_of_lt_of_le (by norm_num) h38
  have hbk := Cvs.L2a.WindowChainInputsProlate.margin_W hx (Nat.cast_nonneg x) (Cvs.L2a.FullSpanProlateFamily.x_le x) h38
  have hwindow' := hwindow
  rw [← sum_option_eq_spineG] at hwindow'
  rw [← sum_option_eq_spineG]
  refine Cvs.L2a.WindowChainFromInputs.L2a_window_deep_budget_of (ι := Option S) none
    (h := fun i => rung c (kOf i)) (h₁ := fun i => rung₁ c (kOf i)) (h₂ := fun i => rung₂ c (kOf i))
    (χ := fun i => lev c (kOf i)) (μ := fun i => muR c (kOf i)) (m := 2 * k) b
    (fun i => (hspec i).1) (fun i => (hspec i).2.1) (fun i => (hspec i).2.2.1) (fun i => (hspec i).2.2.2.1) hc80
    (fun i => nonneg_of_mem_evenSpec c (lev_spec (hex i)).1) hχc ?_ (fun i => (hspec i).2.2.2.2.1)
    (fun i => (hspec i).2.2.2.2.2) (fun i => psi_rung (hex i)) (hcnt none) ?_ hJ (by omega) ?_
    hgd hgd₁ hgd₂c hgang hgeven hgnorm (psi_rung hexk) (lev_spec hexk).2
    (by norm_num : (0 : ℝ) < 1 / 2) hlam hκF hfl hW hbk (sum_option_pole hc0 a) hP hR hH hwindow'
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
  · -- counts past the ground
    rintro (_ | j) hne
    · exact absurd rfl hne
    · rw [hcnt]
      exact hkpos j

/-- The harmonic-number window-energy budget gives the original full-span floor. -/
theorem L2a_window_full_of (x : ℕ) (hx : c0W ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j < x) {k : ℕ}
    (hk : 1 ≤ k) (hSk : ∀ j ∈ S, k ≤ j) (a : S → ℝ) :
    π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) (2 * k))
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) := by
  have hxF := le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx
  obtain ⟨-, hc80⟩ := Cvs.L2a.BandInputsFromCutMultipliers.scale_ge hxF
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hc2π : 2 * π ≤ 2 * π * (x : ℝ) := by linarith [Real.pi_lt_four]
  exact L2a_window_full_budget_of (H := Hx (2 * π * x)) x hx hS hk hSk a
    (Cvs.L2a.WindowFormDeepSpan.Hx_pos hc2π) (spineG_harmonic_energy hc0 a)

/-- **SPINE-L2a(5) on `D₀` of the full span**: indices `2 ≤ j < x`, factor `1 − λ₈`. -/
theorem L2a_window_full_D0 (x : ℕ) (hx : c0W ≤ 2 * π * x) (a : ((Finset.range x).filter (2 ≤ ·)) → ℝ) :
    π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 4)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) :=
  L2a_window_full_of x hx (fun _ hj => Finset.mem_range.1 (Finset.mem_filter.1 hj).1) (k := 2) (by norm_num)
    (fun _ hj => (Finset.mem_filter.1 hj).2) a

/-- **SPINE-L2a(5) on `R_D` of the full span**: indices `1 ≤ j < x`, factor `1 − λ₄`. -/
theorem L2a_window_full_RD (x : ℕ) (hx : c0W ≤ 2 * π * x) (a : ((Finset.range x).filter (1 ≤ ·)) → ℝ) :
    π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 2)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) :=
  L2a_window_full_of x hx (fun _ hj => Finset.mem_range.1 (Finset.mem_filter.1 hj).1) (k := 1) le_rfl
    (fun _ hj => (Finset.mem_filter.1 hj).2) a

/-- **SPINE-L2a(5) on the full span of the prolate family at `c = 2πx`**: the `D₀` bound with `1 − λ₈` and the
`R_D` bound with `1 − λ₄`, on the rungs `h_{4j}`, `0 ≤ j < x`, for every `x` with `c₀^W ≤ 2πx`. -/
theorem L2a_window_full_instance (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    (∀ a : ((Finset.range x).filter (2 ≤ ·)) → ℝ,
      π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
          * (1 - lamR (2 * π * x) 4)
          * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
        ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
            (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a)))) ∧
    (∀ a : ((Finset.range x).filter (1 ≤ ·)) → ℝ,
      π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
          * (1 - lamR (2 * π * x) 2)
          * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
        ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
            (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a)))) :=
  ⟨L2a_window_full_D0 x hx, L2a_window_full_RD x hx⟩

/-- **The full-span factors are positive** past `c₀^W`: `λ₀ > 0`, `λ₄, λ₈ < 1` and `H_x > 0` at `c = 2πx`. -/
theorem full_factors_pos (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    0 < π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 4) ∧
      0 < π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 2) := by
  have hxF := le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx
  obtain ⟨hcE, hc80⟩ := Cvs.L2a.BandInputsFromCutMultipliers.scale_ge hxF
  have hc0 : 0 < 2 * π * (x : ℝ) := by linarith
  have hx3 : 3 ≤ x := by
    have h80 : (10 : ℝ) ^ 80 ≤ 2 * π * x := Cvs.L2a.FullSpanProlateFamily.c80_le_exp.trans hcE
    by_contra h
    push Not at h
    have : (x : ℝ) ≤ 2 := by exact_mod_cast (by omega : x ≤ 2)
    have h16 : 2 * π * (x : ℝ) ≤ 16 := by
      clear * - this
      have hp := Real.pi_lt_four
      have hp0 := Real.pi_pos
      have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
      nlinarith
    have h' : (10 : ℝ) ^ 80 ≤ 16 := h80.trans h16
    clear * - h'
    norm_num at h'
  have h4 : ∃ χ, IsLevelIdx (2 * π * x) 4 χ :=
    Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 ⟨2, Finset.mem_range.2 (by omega)⟩
  have h2 : ∃ χ, IsLevelIdx (2 * π * x) 2 χ :=
    Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 ⟨1, Finset.mem_range.2 (by omega)⟩
  have hH := Cvs.L2a.WindowFormDeepSpan.Hx_pos (c := 2 * π * x) (by nlinarith [Real.pi_lt_four])
  have hl0 := lamR_zero_pos hc0
  have hl4 := lamR_lt_one hc0 h4 (by norm_num)
  have hl2 := lamR_lt_one hc0 h2 (by norm_num)
  constructor
  · have : 0 < 1 - lamR (2 * π * x) 4 := by linarith
    positivity
  · have : 0 < 1 - lamR (2 * π * x) 2 := by linarith
    positivity

end Cvs.L2a.WindowFullSpanProlate
