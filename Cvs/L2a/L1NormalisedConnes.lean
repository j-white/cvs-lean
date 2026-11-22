import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.EvenConnesPartLower
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.FullSpanFromScale
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailUpperFrame
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.PolarParameterBessel
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.L1GapConnesRH
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.XiValueAtOrigin

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# L1 normalised at Connes' vector: `L1/‖e‖² ≤ C₁(x)(1 − λ₄)`

For `G = h₄ − αh₀`, Cvs.L2a.FullTailUpperFrame gives `N ≤ C(ℓ)(π/c)(α²(1 − λ₀) + (1 − λ₄)) ≤ C(ℓ)(4 + π/c)(1 − λ₄)` (`λ` antitone,
`α² ≤ 2c/(πλ₀)`, Landau's `½`), and Cvs.Approximant.EvenConnesPartLower gives `‖e‖² ≥ (4/25)‖Ξ(0)‖²/(x log x)`. So the joint gap's `q`-side is
`(1 − λ₄)` times an explicit factor; RH follows from the gap condition at that factor (Cvs.Route.L1GapConnesRH).
-/

noncomputable section

open MeasureTheory Set Real Filter Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan
open scoped InnerProductSpace

namespace Cvs.L2a.L1NormalisedConnes
open Cvs.ZeroCounting

open Cvs.L2a.ProlateFamilySpine (kOf bOf)
open Cvs.L2a.WindowChainInputsProlate (c0W kapFX)
open Cvs.Route.JointGapConnesFromL1 (one₁ connesL1 connesEven connesOdd)

/-- The frame level of Connes' profile, `max(0, 3πc + 2 log((K₁ᵦ + P)/V))` at `c = 2πx`. -/
def connesLevel (x : ℕ) : ℝ :=
  max 0 (3 * π * (2 * π * x) + 2 * Real.log ((Cvs.L2a.L1FullTailWinfBound.K1bS (2 * π * x) (bOf (2 * π * x) one₁)
      (fun i => rung (2 * π * x) (kOf i)) (fun i => rung₁ (2 * π * x) (kOf i)) (fun i => rung₂ (2 * π * x) (kOf i))
    + ∑ i, bOf (2 * π * x) one₁ i ^ 2 * ∫ t in Ioi 1, psi (2 * π * x) (rung (2 * π * x) (kOf i)) t ^ 2)
    / Cvs.L2a.L1WindowFromFloor.endV (2 * π * x) 1 (bOf (2 * π * x) one₁) (fun i => muR (2 * π * x) (kOf i))))

/-- The normalised L1 factor `C₁(x) = L1⁺ · C(ℓ) · (4 + π/c) · 25x log x/(4‖Ξ(0)‖²)`. -/
def C1conn (x : ℕ) : ℝ :=
  max 0 (Cvs.L2a.L1WindowFromFloor.L1bound (2 * π * x) (kapFX x) (1 / 2) (bOf (2 * π * x) one₁)
      (fun i => muR (2 * π * x) (kOf i)) (fun i => rung (2 * π * x) (kOf i))
      (fun i => rung₁ (2 * π * x) (kOf i)) (fun i => rung₂ (2 * π * x) (kOf i)))
    * Cvs.L2a.FullTailUpperFrame.frameC (Fintype.card (Option ({1} : Finset ℕ))) (connesLevel x)
    * (4 + π / (2 * π * x)) * (25 * x * Real.log x / (4 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2))

private theorem sum_one (f : ℕ → ℝ) : ∑ j : ({1} : Finset ℕ), f j = f 1 := by
  rw [Finset.sum_coe_sort ({1} : Finset ℕ) f, Finset.sum_singleton]

/-- **The full tail of Connes' profile is `(1 − λ₄)`-small**:
`N ≤ C(ℓ)·(4 + π/c)(1 − λ₄)` at `c = 2πx`, `c₀^W ≤ 2πx`. -/
theorem connes_tailN_le (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    Cvs.L2a.L1WindowFromFloor.tailN (2 * π * x) (bOf (2 * π * x) one₁) (fun i => rung (2 * π * x) (kOf i))
      ≤ Cvs.L2a.FullTailUpperFrame.frameC (Fintype.card (Option ({1} : Finset ℕ))) (connesLevel x)
        * ((4 + π / (2 * π * x)) * (1 - lamR (2 * π * x) 2)) := by
  set c : ℝ := 2 * π * x with hcdef
  have hc80 : 80 ≤ c := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hc0 : 0 < c := by linarith
  have hx1 : 1 < x := by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hc80
  have hex : ∀ i : Option ({1} : Finset ℕ), ∃ χ, IsLevelIdx c (kOf i) χ := by
    rintro (_ | j)
    · exact exists_isLevelIdx_zero c
    · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
      have := Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 ⟨1, Finset.mem_range.2 hx1⟩
      simpa [kOf, hj] using this
  have hspec := fun i => rung_spec (hex i)
  have hcnt : ∀ i : Option ({1} : Finset ℕ), (evenSpec (sqC c) ∩ Iio (lev c (kOf i))).ncard = kOf i := fun i =>
    (lev_spec (hex i)).2
  have hχc : ∀ i : Option ({1} : Finset ℕ), lev c (kOf i) < c ^ 2 := by
    rintro (_ | j)
    · show lev c 0 < c ^ 2
      rw [lev_zero]
      have := groundLevel_le c
      nlinarith
    · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
      exact (Cvs.L2a.FullSpanFromScale.span_data hc80).2.1 ⟨j, Finset.mem_range.2 (by rw [hj]; exact hx1)⟩
  have hg0 := fun i => Cvs.L2a.PolarParameterBessel.exists_ne_zero_of_norm (hspec i).2.2.2.2.2
  have hμpos : ∀ i : Option ({1} : Finset ℕ), 0 < muR c (kOf i) := fun i =>
    mu_pos_of_even_index hc0 (hspec i).1 (hspec i).2.1 (hspec i).2.2.1 (hspec i).2.2.2.1 (hspec i).2.2.2.2.1
      (hg0 i) (psi_rung (hex i)) (by
        rw [hcnt i]
        rcases i with _ | j
        · exact ⟨0, rfl⟩
        · exact ⟨j, by simp only [kOf, Option.elim]; ring⟩)
  have hχ0 := fun i => nonneg_of_mem_evenSpec c (lev_spec (hex i)).1
  have hF := Cvs.L2a.FullTailUpperFrame.tailN_le_frame (bOf c one₁) (fun i => (hspec i).1) (fun i => (hspec i).2.1)
    (fun i => (hspec i).2.2.1) (fun i => (hspec i).2.2.2.1) hc80 hχ0 hχc (fun i => (hspec i).2.2.2.2.1)
    (fun i => (hspec i).2.2.2.2.2) (fun i => (hμpos i).ne') (fun i => psi_rung (hex i))
    (fun i X hX => Cvs.Prolate.AngularBesselInequality.hM_of_angular (fun i => (hspec i).1) (fun i => (hspec i).2.1)
      (fun i => (hspec i).2.2.1) (fun i => (hspec i).2.2.2.1) (fun i => (hspec i).2.2.2.2.1) hg0 hc0 hχ0
      (by linarith) i)
    ⟨some ⟨1, Finset.mem_singleton_self 1⟩, by simp [bOf, one₁]⟩
  refine hF.trans (mul_le_mul_of_nonneg_left ?_ (Cvs.L2a.FullTailUpperFrame.frameC_nonneg (Nat.cast_nonneg _)
    (le_max_left _ _)))
  -- the `(1 − λ)` sum over `{h₀, h₄}`
  have hex2 : ∃ χ, IsLevelIdx c 2 χ := by simpa [kOf] using hex (some ⟨1, Finset.mem_singleton_self 1⟩)
  have hanti : lamR c 2 ≤ lamR c 0 := lamR_anti hc0 hex2 (by norm_num)
  have hhalf : 1 / 2 ≤ lamR c 2 := by
    simpa using Cvs.L2a.WindowChainInputsProlate.half_le_lamR hc80 hx1
  obtain ⟨g2, g2₁, g2₂c, hang2, heven2, hnorm2⟩ := rung_spec hex2
  have hm2 := Cvs.Prolate.AngularBesselInequality.mass_eq hc0
    (fun s hs => (g2 s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt)
    heven2 (psi_rung hex2) hnorm2
  have hd2 : 0 ≤ 1 - lamR c 2 := by
    have h0 : 0 ≤ ∫ ξ in Ioi 1, psi c (rung c 2) ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
    rw [hm2] at h0
    have : 0 ≤ π / c := by positivity
    by_contra hneg
    push Not at hneg
    have : π / c * (1 - (muR c 2 * √(c / (2 * π))) ^ 2) < 0 := mul_neg_of_pos_of_neg (by positivity) (by
      simpa [lamR] using hneg)
    linarith
  -- `α² ≤ 2c/(πλ₀) ≤ 4c/π`
  obtain ⟨g0, g0₁, g0₂c, hang0, heven0, hnorm0⟩ := rung_spec (exists_isLevelIdx_zero c)
  have hα := Cvs.Xi.EImageWindowPoisson.sum_alpha_sq_le (Finset.univ : Finset Unit) (fun _ => rung c 2)
    (fun _ _ s hs => (g2 s hs).continuousAt.continuousWithinAt)
    (fun _ _ _ _ => by simpa [sq] using hnorm2) hc0 g0 g0₁ hang0 heven0 (by simpa [kOf] using hcnt none) hnorm0
    (psi_rung (exists_isLevelIdx_zero c))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul] at hα
  have hlam0 : 1 / 2 ≤ lamR c 0 := hhalf.trans hanti
  have hα' : alpha c 1 ^ 2 ≤ 4 * c / π := by
    have e : alpha c 1 = (∫ s in (-1 : ℝ)..1, rung c 2 s) / ∫ s in (-1 : ℝ)..1, rung c 0 s := by
      simp [alpha]
    rw [e]
    refine hα.trans ?_
    change 2 * c / (π * lamR c 0) ≤ 4 * c / π
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hlam0 (show 0 ≤ 4 * c * π by positivity)]
  -- evaluate the sum
  rw [Fintype.sum_option]
  have hb0 : bOf c one₁ none = -alpha c 1 := by
    simp only [bOf, Option.elim, one₁, one_mul]
    rw [sum_one (fun j => alpha c j)]
  have hb1 : ∀ j : ({1} : Finset ℕ), bOf c one₁ (some j) = 1 := fun j => rfl
  have hk1 : ∀ j : ({1} : Finset ℕ), kOf (some j) = 2 := fun j => by
    have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
    simp [kOf, hj]
  simp only [hb1, hk1, one_pow, one_mul]
  rw [sum_one (fun _ => π / c * (1 - (muR c 2 * √(c / (2 * π))) ^ 2)), hb0]
  change (-alpha c 1) ^ 2 * (π / c * (1 - lamR c 0)) + π / c * (1 - lamR c 2)
    ≤ (4 + π / c) * (1 - lamR c 2)
  have hpc : 0 ≤ π / c := by positivity
  have h1 : (-alpha c 1) ^ 2 * (π / c * (1 - lamR c 0)) ≤ (4 * c / π) * (π / c * (1 - lamR c 2)) := by
    rw [neg_sq]
    have hd0 : 1 - lamR c 0 ≤ 1 - lamR c 2 := by linarith
    calc alpha c 1 ^ 2 * (π / c * (1 - lamR c 0)) ≤ alpha c 1 ^ 2 * (π / c * (1 - lamR c 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd0 hpc) (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hα' (mul_nonneg hpc hd2)
  have e2 : (4 * c / π) * (π / c * (1 - lamR c 2)) = 4 * (1 - lamR c 2) := by
    field_simp
  rw [e2] at h1
  nlinarith

/-- **L1 normalised at Connes' vector**: eventually, at every `x` with `c₀^W ≤ 2πx`,
`L1/‖e‖² ≤ C₁(x)(1 − λ₄)`. -/
theorem eventually_connesL1_div_le :
    ∀ᶠ x : ℕ in atTop, ∀ hx : c0W ≤ 2 * π * x,
      connesL1 x / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2 ≤ C1conn x * (1 - lamR (2 * π * x) 2) := by
  filter_upwards [Cvs.Approximant.EvenConnesPartLower.eventually_norm_connesEven_sq_ge, eventually_ge_atTop 3] with x he hx3 hx
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hL : 0 < Real.log x := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80)
  have hXi : 0 < ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ := norm_pos_iff.mpr fun h => by
    have hp := Cvs.Xi.XiValueAtOrigin.Xi_zero_re_pos
    rw [h, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  set m := 4 / 25 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2 / (x * Real.log x) with hm
  have hm0 : 0 < m := by positivity
  have hme := he h80
  set E := ‖connesEven h80‖ ^ 2
  have hE : 0 < E := lt_of_lt_of_le hm0 hme
  set Lb := Cvs.L2a.L1WindowFromFloor.L1bound (2 * π * x) (kapFX x) (1 / 2) (bOf (2 * π * x) one₁)
      (fun i => muR (2 * π * x) (kOf i)) (fun i => rung (2 * π * x) (kOf i))
      (fun i => rung₁ (2 * π * x) (kOf i)) (fun i => rung₂ (2 * π * x) (kOf i)) with hLb
  set T := Cvs.L2a.L1WindowFromFloor.tailN (2 * π * x) (bOf (2 * π * x) one₁) (fun i => rung (2 * π * x) (kOf i))
  set U := Cvs.L2a.FullTailUpperFrame.frameC (Fintype.card (Option ({1} : Finset ℕ))) (connesLevel x)
        * ((4 + π / (2 * π * x)) * (1 - lamR (2 * π * x) 2)) with hU
  have hT0 : 0 ≤ T := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  have hTU : T ≤ U := connes_tailN_le x hx
  have hnum : connesL1 x ≤ max 0 Lb * U := by
    change Lb * T ≤ _
    calc Lb * T ≤ max 0 Lb * T := mul_le_mul_of_nonneg_right (le_max_right _ _) hT0
      _ ≤ max 0 Lb * U := mul_le_mul_of_nonneg_left hTU (le_max_left _ _)
  have hU0 : 0 ≤ max 0 Lb * U := (mul_nonneg (le_max_left _ _) hT0).trans
    (mul_le_mul_of_nonneg_left hTU (le_max_left _ _))
  calc connesL1 x / E ≤ max 0 Lb * U / E := div_le_div_of_nonneg_right hnum hE.le
    _ ≤ max 0 Lb * U / m := div_le_div_of_nonneg_left hU0 hm0 hme
    _ = C1conn x * (1 - lamR (2 * π * x) 2) := by
        rw [hm, hU, C1conn, ← hLb]
        field_simp

/-- **L1's normalised gap at scale `x`**: near-positivity `s` on the whole domain, a continuous even-hyperplane floor
`μ`, and `K(C₁(1 − λ₄) + s‖o‖²/‖e‖²) + (K − 1)s < μ` at `K = √x log x`. -/
def L1GapN (x : ℕ) : Prop :=
  ∃ (hx : c0W ≤ 2 * π * x) (s μ : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)),
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    √(x : ℝ) * Real.log x * (C1conn x * (1 - lamR (2 * π * x) 2)
        + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2 / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
      + (√(x : ℝ) * Real.log x - 1) * s < μ

/-- **RH from L1's normalised gap**: `L1GapN x` at infinitely many integers `x` gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_L1GapN (h : ∃ᶠ x : ℕ in atTop, L1GapN x) : RiemannHypothesis := by
  refine Cvs.Route.L1GapConnesRH.riemannHypothesis_of_L1Gap ((h.and_eventually (eventually_connesL1_div_le.and
    (eventually_ge_atTop 2))).mono fun x ⟨⟨hx, s, μ, η, hneg, hfloor, hlt⟩, hdiv, hx2⟩ => ?_)
  refine ⟨hx, s, μ, η, hneg, hfloor, lt_of_le_of_lt ?_ hlt⟩
  have hK : 0 ≤ √(x : ℝ) * Real.log x :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega)))
  have h := hdiv hx
  have : (connesL1 x + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
      / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2
      ≤ C1conn x * (1 - lamR (2 * π * x) 2)
        + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2 / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2 := by
    rw [add_div]; linarith
  have := mul_le_mul_of_nonneg_left this hK
  linarith

end Cvs.L2a.L1NormalisedConnes
