import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FrameFloorIntegerM
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailDeepSpan
import Cvs.L2a.FullTailDeepSpanClosed
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.LowConstantUniform
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowDeepSpanStructural
import Cvs.L2a.WindowFormDeepSpan
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.RegularSolutionEdge
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
# SPINE-L2a(5) on the rungs of the prolate family at `c = 2πx`

The spine profile `Σ_j a_j (h_{4j} − α_j h₀)` over the deep indices `j ≥ k` is the span `Σ_i b_i h_i` over
`Option S` with the ground rung at `none`; every hypothesis of `WindowDeepSpanStructural`'s deep window bound is then a property of the
rungs of Cvs.Prolate.EvenRungsByIndex and the deep set of Cvs.Approximant.DeepIndexSpineSpan. The full-tail bound of Cvs.L2a.FullTailDeepSpanClosed is instantiated on the same rungs.
-/

noncomputable section

open Real Set MeasureTheory Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.ProlateFamilySpine

open Cvs.L2a.WindowFormDeepSpan (c0 Hx kapStar Kpol bPrime_ge_one Kpol_nonneg)

/-! ### The span over `Option S` -/

/-- The even index of a member of `Option S`: the ground `none` has index `0`, `some j` has index `2j`. -/
def kOf {S : Finset ℕ} (i : Option S) : ℕ := Option.elim i 0 fun j => 2 * (j : ℕ)

/-- The coefficients of the spine profile on `Option S`: `b_none = −Σ_j a_j α_j` and `b_j = a_j`. -/
def bOf (c : ℝ) {S : Finset ℕ} (a : S → ℝ) (i : Option S) : ℝ :=
  Option.elim i (-∑ j, a j * alpha c j) a

/-- **The spine profile is the span over `Option S`.** -/
theorem sum_option_eq_spineG (c : ℝ) {S : Finset ℕ} (a : S → ℝ) :
    (fun s => ∑ i : Option S, bOf c a i * rung c (kOf i) s) = spineG c a := by
  funext s
  rw [Fintype.sum_option]
  simp only [bOf, kOf, Option.elim, spineG, mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_mul]
  have : ∀ j : S, a j * (alpha c j * rung c 0 s) = a j * alpha c j * rung c 0 s := fun j => by ring
  simp only [this]
  ring

/-- **The pole condition on `Option S`**: `Σ_i b_i ∫h_i = 0`. -/
theorem sum_option_pole {c : ℝ} (hc : 0 < c) {S : Finset ℕ} (a : S → ℝ) :
    ∑ i : Option S, bOf c a i * ∫ s in (-1 : ℝ)..1, rung c (kOf i) s = 0 := by
  have hI0 := integral_rung_zero_ne hc
  rw [Fintype.sum_option]
  simp only [bOf, kOf, Option.elim, neg_mul, Finset.sum_mul]
  have : ∀ j : S, a j * alpha c j * ∫ s in (-1 : ℝ)..1, rung c 0 s =
      a j * ∫ s in (-1 : ℝ)..1, rung c (2 * (j : ℕ)) s := fun j => by
    rw [mul_assoc, alpha, div_mul_cancel₀ _ hI0]
  simp only [this]
  ring

/-- The window of the zero profile is zero. -/
theorem window_zero (w : ℝ) : Cvs.Xi.EImageWindowPoisson.window w (fun _ => 0) = fun _ => 0 := by
  funext θ
  simp [Cvs.Xi.EImageWindowPoisson.window, Cvs.Xi.EImageWindowPoisson.eimage]

/-! ### The instance hypotheses -/

/-- `c0 ≤ 2πx` forces `1 ≤ x`. -/
theorem one_le_of_c0 {x : ℕ} (hx : c0 ≤ 2 * π * x) : 1 ≤ x := by
  have hc : (10 : ℝ) ^ 16 ≤ 2 * π * x := c0_ge.trans hx
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h
    norm_num at hc
  · exact h

/-- **SPINE-L2a(5) on deep indices `j ≥ k ≥ 1`**: factor `1 − λ_{4k}`, `λ_{4k} = lamR c (2k)`, at `c = 2πx`. -/
theorem L2a_spine_of (x : ℕ) (hx : c0 ≤ 2 * π * x) {S : Finset ℕ} (hS : ∀ j ∈ S, j ∈ deepSet x) {k : ℕ}
    (hk : 1 ≤ k) (hSk : ∀ j ∈ S, k ≤ j) (a : S → ℝ) :
    π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) (2 * k))
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) := by
  set c : ℝ := 2 * π * x with hcdef
  have hc16 : (10 : ℝ) ^ 16 ≤ c := c0_ge.trans hx
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hx1 := one_le_of_c0 hx
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
  have hex : ∀ i : Option S, ∃ χ, IsLevelIdx c (kOf i) χ := by
    rintro (_ | j)
    · exact exists_isLevelIdx_zero c
    · exact (mem_deepSet.mp (hS j j.2)).2.1
  have hexk : ∃ χ, IsLevelIdx c (2 * k) χ := by
    obtain ⟨χ, hχ⟩ := hex (some ⟨j₀, hj₀⟩)
    exact exists_isLevelIdx_of_le hχ (by simp only [kOf, Option.elim]; have := hSk j₀ hj₀; omega)
  have hcnt : ∀ i : Option S, (evenSpec (sqC c) ∩ Iio (lev c (kOf i))).ncard = kOf i := fun i =>
    (lev_spec (hex i)).2
  have hkpos : ∀ j : S, 2 * k ≤ kOf (some j) := fun j => by
    simp only [kOf, Option.elim]
    have := hSk j j.2
    omega
  -- the cardinality
  have hJ : (Fintype.card (Option S) : ℝ) ≤ c / 4 + 1 := by
    have h0S : 0 ∉ S := fun h => by have := hSk 0 h; omega
    have hlt : S.card < (deepSet x).card :=
      Finset.card_lt_card ⟨hS, fun hsub => h0S (hsub (zero_mem_deepSet hx))⟩
    have hle : ((Fintype.card (Option S) : ℕ) : ℝ) ≤ (deepSet x).card := by
      rw [Fintype.card_option, Fintype.card_coe]
      exact_mod_cast hlt
    exact hle.trans (card_deepSet_le x)
  obtain ⟨hP, hR⟩ := sizes_PR hx1
  have hspec := fun i => rung_spec (hex i)
  obtain ⟨hgd, hgd₁, -, hgang, hgeven, hgnorm⟩ := rung_spec hexk
  rw [← sum_option_eq_spineG]
  refine Cvs.L2a.WindowDeepSpanStructural.L2a_window_deep_closed (ι := Option S) none
    (h := fun i => rung c (kOf i)) (h₁ := fun i => rung₁ c (kOf i)) (h₂ := fun i => rung₂ c (kOf i))
    (χ := fun i => lev c (kOf i)) (μ := fun i => muR c (kOf i)) (m := 2 * k) (bOf c a)
    (fun i => (hspec i).1) (fun i => (hspec i).2.1) (fun i => (hspec i).2.2.2.1) hx
    (fun i => nonneg_of_mem_evenSpec c (lev_spec (hex i)).1) ?_ ?_ (fun i => (hspec i).2.2.2.2.1)
    (fun i => (hspec i).2.2.2.2.2) (fun i => psi_rung (hex i)) (hcnt none) ?_ hJ (by omega) ?_
    hgd hgd₁ hgang hgeven hgnorm (psi_rung hexk) (lev_spec hexk).2 (sum_option_pole hc0 a) hP hR
  · -- depth
    rintro (_ | j)
    · show 5 * c ≤ c ^ 2 - lev c 0
      rw [lev_zero]
      exact five_mul_le_sub_groundLevel (by linarith)
    · exact (mem_deepSet.mp (hS j j.2)).2.2
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

/-- **SPINE-L2a(5) on `D₀` for the prolate family**: deep indices `j ≥ 2`, factor `1 − λ₈`. -/
theorem L2a_spine_instance_D0 (x : ℕ) (hx : c0 ≤ 2 * π * x) (a : ((deepSet x).filter (2 ≤ ·)) → ℝ) :
    π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 4)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) :=
  L2a_spine_of x hx (fun _ hj => (Finset.mem_filter.mp hj).1) (k := 2) (by norm_num)
    (fun _ hj => (Finset.mem_filter.mp hj).2) a

/-- **SPINE-L2a(5) on `R_D` for the prolate family**: deep indices `j ≥ 1`, factor `1 − λ₄`. -/
theorem L2a_spine_instance_RD (x : ℕ) (hx : c0 ≤ 2 * π * x) (a : ((deepSet x).filter (1 ≤ ·)) → ℝ) :
    π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
        * (1 - lamR (2 * π * x) 2)
        * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
          (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a))) :=
  L2a_spine_of x hx (fun _ hj => (Finset.mem_filter.mp hj).1) (k := 1) le_rfl
    (fun _ hj => (Finset.mem_filter.mp hj).2) a

/-- **SPINE-L2a(5) for the prolate family at `c = 2πx`**: the `D₀` bound with `1 − λ₈` and the `R_D` bound with
`1 − λ₄`, for every `x` with `c₀ ≤ 2πx`. -/
theorem L2a_spine_instance (x : ℕ) (hx : c0 ≤ 2 * π * x) :
    (∀ a : ((deepSet x).filter (2 ≤ ·)) → ℝ,
      π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
          * (1 - lamR (2 * π * x) 4)
          * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
        ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
            (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a)))) ∧
    (∀ a : ((deepSet x).filter (1 ≤ ·)) → ℝ,
      π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
          * (1 - lamR (2 * π * x) 2)
          * ∫ θ, Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a) θ ^ 2
        ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
            (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) a)))) :=
  ⟨L2a_spine_instance_D0 x hx, L2a_spine_instance_RD x hx⟩

/-- **The spine factor is positive** once the level of index `4` exists. -/
theorem spine_factor_pos (x : ℕ) (hx : c0 ≤ 2 * π * x) (h4 : ∃ χ, IsLevelIdx (2 * π * x) 4 χ) :
    0 < π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
      * (1 - lamR (2 * π * x) 4) := by
  have hc16 : (10 : ℝ) ^ 16 ≤ 2 * π * x := c0_ge.trans hx
  have hc0 : 0 < 2 * π * (x : ℝ) := lt_of_lt_of_le (by norm_num) hc16
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast one_le_of_c0 hx
  have hH := Cvs.L2a.WindowFormDeepSpan.Hx_pos (c := 2 * π * x) (by nlinarith [Real.pi_pos])
  have hl0 := lamR_zero_pos hc0
  have hl4 := lamR_lt_one hc0 h4 (by norm_num)
  have h1 : 0 < 1 - lamR (2 * π * x) 4 := by linarith
  positivity

/-- **The `R_D` spine factor is positive** once the level of index `2` exists. -/
theorem spine_factor_pos_RD (x : ℕ) (hx : c0 ≤ 2 * π * x) (h2 : ∃ χ, IsLevelIdx (2 * π * x) 2 χ) :
    0 < π / (8 * (2 * π * x) * Hx (2 * π * x) * (1 + 2 * (2 * π * x) / (π * lamR (2 * π * x) 0)))
      * (1 - lamR (2 * π * x) 2) := by
  have hc16 : (10 : ℝ) ^ 16 ≤ 2 * π * x := c0_ge.trans hx
  have hc0 : 0 < 2 * π * (x : ℝ) := lt_of_lt_of_le (by norm_num) hc16
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast one_le_of_c0 hx
  have hH := Cvs.L2a.WindowFormDeepSpan.Hx_pos (c := 2 * π * x) (by nlinarith [Real.pi_pos])
  have hl0 := lamR_zero_pos hc0
  have hl2 := lamR_lt_one hc0 h2 (by norm_num)
  have h1 : 0 < 1 - lamR (2 * π * x) 2 := by linarith
  positivity

/-! ### The full-tail bound on the rungs -/

/-- **The full-tail L2a on the deep rungs at `c = 2πx`**: `FullTailDeepSpanClosed`'s three conclusions for `h_j = rung (2πx) (2j)`,
`j ∈ deepSet x`, with `κ = κ⋆`, together with `b̄ ≥ 1 + K_pol(κ_F)`. -/
theorem L2a_fulltail_spine (x : ℕ) (hx : c0 ≤ 2 * π * x) (a : deepSet x → ℝ) :
    0 < Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) (2 * π * x) (deepSet x).card (7 / 100)
      ∧ 1 + Kpol (Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) (2 * π * x) (deepSet x).card (7 / 100))
        ≤ Cvs.L2a.FullTailDeepSpan.bBar (2 * π * x) kapStar (deepSet x).card
            (Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) (2 * π * x) (deepSet x).card (7 / 100))
      ∧ (∀ M : ℕ, 3 ≤ M →
        Cvs.L2a.FullTailDeepSpan.bBar (2 * π * x) kapStar (deepSet x).card
              (Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) (2 * π * x) (deepSet x).card (7 / 100))
            * (∫ θ in Ioi 1, Cvs.L2a.PositionTruncatedTail.posTail
                (fun ξ => ∑ j, a j * psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ) M θ ^ 2)
          ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm ⌊(M : ℝ)⌋₊ ⌊(M : ℝ)⌋₊
              (Cvs.L2a.TailLogScaleTest.logScale (Cvs.L2a.PositionTruncatedTail.posTail
                (fun ξ => ∑ j, a j * psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ) M)))
      ∧ Cvs.L2a.FullTailDeepSpan.bBar (2 * π * x) kapStar (deepSet x).card
            (Cvs.L2a.FrameFloorIntegerM.kappaF (10 ^ 16) (2 * π * x) (deepSet x).card (7 / 100))
          * (∫ θ in Ioi 1, Cvs.L2a.FullTailConvergence.fullTail
              (fun ξ => ∑ j, a j * psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ) θ ^ 2)
        ≤ Cvs.L2a.FullTailWeilFormLimit.Winf
            (fun ξ => ∑ j, a j * psi (2 * π * x) (rung (2 * π * x) (2 * (j : ℕ))) ξ) := by
  set c : ℝ := 2 * π * x with hcdef
  have hc16 : (10 : ℝ) ^ 16 ≤ c := c0_ge.trans hx
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc16
  have hex : ∀ j : deepSet x, ∃ χ, IsLevelIdx c (2 * (j : ℕ)) χ := fun j => (mem_deepSet.mp j.2).2.1
  have hspec := fun j => rung_spec (hex j)
  have hcnt : ∀ j : deepSet x, (evenSpec (sqC c) ∩ Iio (lev c (2 * (j : ℕ)))).ncard = 2 * (j : ℕ) :=
    fun j => (lev_spec (hex j)).2
  have hJd : ((deepSet x).card : ℝ) ≤ c / 4 + 1 := card_deepSet_le x
  have hJ : (Fintype.card (deepSet x) : ℝ) ≤ c / 4 + 1 := by
    rw [Fintype.card_coe]
    exact hJd
  have hχ0 : ∀ j : deepSet x, 0 ≤ lev c (2 * (j : ℕ)) := fun j =>
    nonneg_of_mem_evenSpec c (lev_spec (hex j)).1
  have hg0 : ∀ j : deepSet x, ∃ s ∈ Icc (-1 : ℝ) 1, rung c (2 * (j : ℕ)) s ≠ 0 := fun j =>
    rung_ne_zero (hex j)
  have hmass := Cvs.Prolate.AngularBesselInequality.hM_of_angular (g := fun j : deepSet x => rung c (2 * (j : ℕ)))
    (g₁ := fun j => rung₁ c (2 * (j : ℕ))) (g₂ := fun j => rung₂ c (2 * (j : ℕ)))
    (χ := fun j => lev c (2 * (j : ℕ))) (X := 3) (fun j => (hspec j).1) (fun j => (hspec j).2.1)
    (fun j => (hspec j).2.2.1) (fun j => (hspec j).2.2.2.1) (fun j => (hspec j).2.2.2.2.1) hg0 hc0 hχ0
    (by norm_num)
  obtain ⟨hT, hb⟩ := bPrime_ge_one (J := ((deepSet x).card : ℝ)) hx (Nat.cast_nonneg _) hJd
  have hκ1 : (1 : ℝ) ≤ kapStar := le_trans (by norm_num) (le_max_left _ _)
  have H := Cvs.L2a.FullTailDeepSpanClosed.L2a_fulltail_span_closed (ι := deepSet x)
    (g := fun j => rung c (2 * (j : ℕ))) (g₁ := fun j => rung₁ c (2 * (j : ℕ)))
    (g₂ := fun j => rung₂ c (2 * (j : ℕ))) (χ := fun j => lev c (2 * (j : ℕ)))
    (μ := fun j => muR c (2 * (j : ℕ))) a (κ := kapStar)
    (fun j => (hspec j).1) (fun j => (hspec j).2.1) (fun j => (hspec j).2.2.1)
    (fun j => (hspec j).2.2.2.1) hc16 hχ0 (fun j => (mem_deepSet.mp j.2).2.2) ?_
    (fun j => (hspec j).2.2.2.2.1) hg0 (fun j => psi_rung (hex j))
    (fun j => ⟨j, by rw [hcnt j]; ring⟩) hJ hκ1 hT hmass
  · rw [Fintype.card_coe] at H
    refine ⟨H.1, ?_, H.2⟩
    unfold Cvs.L2a.WindowFormDeepSpan.bPrime Cvs.L2a.WindowFormDeepSpan.kapF at hb
    linarith
  · intro j j' he
    have h1 := hcnt j
    have h2 := hcnt j'
    simp only at he
    rw [he] at h1
    exact Subtype.ext (by omega)

end Cvs.L2a.ProlateFamilySpine
