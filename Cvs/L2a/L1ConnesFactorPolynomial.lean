import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandECouplingCollar
import Cvs.L2a.FullSpanFromScale
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullTailBilinearBound
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailUpperFrame
import Cvs.L2a.L1CutLevelExponent
import Cvs.L2a.L1FullTailWinfBound
import Cvs.L2a.L1NormalisedConnes
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.PolarParameterBessel
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.RungSpanProfilePowers
import Cvs.L2a.WindowChainFromInputs
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowThresholdExplicit
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Prolate.AngularBesselInequality
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Prolate.RungTailIntegralMass
import Cvs.Prolate.SlepianEvenOrdering
import Cvs.Route.JointGapConnesFromL1
import Cvs.WeilForm.Archimedean.ArchFormIntegrable
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Connes' normalised L1 factor is polynomial: `C₁(x) ≤ C1poly(x)`

On Connes' profile `μ ≥ 1/c` (Landau) and `Σ|bᵢ| = 1 + |α| ≤ c`, so Cvs.L2a.RungSpanProfilePowers applies: the L1 levels are at most
`3πc + 28 log c` and `3πc/2 + 12 log c`, the frame level at most `3πc + 26 log c`, and with `κ_F ≥ 1/38`,
`C₁(x) ≤ L1poly(c) · C(3πc + 26 log c) · (4 + π/c) · 25x log x/(4‖Ξ(0)‖²)`, `L1poly(c) = O(c³)`.
-/

noncomputable section

open MeasureTheory Set Real Filter Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.L1ConnesFactorPolynomial
open Cvs.ZeroCounting

open Cvs.L2a.ProlateFamilySpine (kOf bOf)
open Cvs.L2a.WindowChainInputsProlate (c0W kapFX)
open Cvs.Route.JointGapConnesFromL1 (one₁)
open Cvs.L2a.L1NormalisedConnes (connesLevel C1conn)

/-- The polynomial L1 constant at `c`: `O(c³)`. -/
def L1poly (c : ℝ) : ℝ :=
  28 + (|Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + Cvs.WeilForm.Archimedean.ArchFormIntegrable.growth * (2 * c) ^ 2) + 1
    + 608 * (1 + (3 * π * c + 28 * Real.log c)) ^ 3 + 10 + 2 * (3 * π * c / 2 + 12 * Real.log c) + 6650

/-- **The polynomial normalised factor** `C1poly(x)`. -/
def C1poly (x : ℕ) : ℝ :=
  L1poly (2 * π * x) * Cvs.L2a.FullTailUpperFrame.frameC 2 (3 * π * (2 * π * x) + 26 * Real.log (2 * π * x))
    * (4 + π / (2 * π * x)) * (25 * x * Real.log x / (4 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2))

private theorem sum_one (f : ℕ → ℝ) : ∑ j : ({1} : Finset ℕ), f j = f 1 := by
  rw [Finset.sum_coe_sort ({1} : Finset ℕ) f, Finset.sum_singleton]

private theorem card_eq : (Fintype.card (Option ({1} : Finset ℕ)) : ℝ) = 2 := by
  simp [Fintype.card_option]

/-- `log r ≤ n log c` for `0 ≤ r ≤ cⁿ`, `c ≥ 1`. -/
private theorem log_le_pow {r c : ℝ} {n : ℕ} (hr : 0 ≤ r) (hc : 1 ≤ c) (h : r ≤ c ^ n) :
    Real.log r ≤ n * Real.log c := by
  rcases hr.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hc)
  · rw [← Real.log_pow]; exact Real.log_le_log h0 h

/-- **Connes' profile satisfies `RungSpanProfilePowers`'s span hypotheses** at `c = 2πx`, `c₀^W ≤ 2πx`. -/
theorem connes_spanHyp (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    Cvs.L2a.RungSpanProfilePowers.SpanHyp (2 * π * x) (bOf (2 * π * x) one₁) (fun i => rung (2 * π * x) (kOf i))
      (fun i => rung₁ (2 * π * x) (kOf i)) (fun i => rung₂ (2 * π * x) (kOf i))
      (fun i => lev (2 * π * x) (kOf i)) (fun i => muR (2 * π * x) (kOf i)) := by
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
  have hex2 : ∃ χ, IsLevelIdx c 2 χ := by simpa [kOf] using hex (some ⟨1, Finset.mem_singleton_self 1⟩)
  have hanti : lamR c 2 ≤ lamR c 0 := lamR_anti hc0 hex2 (by norm_num)
  have hhalf : 1 / 2 ≤ lamR c 2 := by simpa using Cvs.L2a.WindowChainInputsProlate.half_le_lamR hc80 hx1
  have hlam : ∀ i : Option ({1} : Finset ℕ), 1 / 2 ≤ lamR c (kOf i) := by
    rintro (_ | j)
    · exact hhalf.trans hanti
    · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
      simpa [kOf, hj] using hhalf
  -- `μ ≥ 1/c` from `λ ≥ ½`
  have hμc : ∀ i : Option ({1} : Finset ℕ), 1 / c ≤ muR c (kOf i) := fun i => by
    have hl := hlam i
    have hμ0 := hμpos i
    have e : lamR c (kOf i) = muR c (kOf i) ^ 2 * (c / (2 * π)) := by
      unfold lamR; rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [e] at hl
    have hsq : (1 / c) ^ 2 ≤ muR c (kOf i) ^ 2 := by
      have h1 : π / c ≤ muR c (kOf i) ^ 2 := by
        have : 1 / 2 * (2 * π / c) ≤ muR c (kOf i) ^ 2 * (c / (2 * π)) * (2 * π / c) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
        have e1 : muR c (kOf i) ^ 2 * (c / (2 * π)) * (2 * π / c) = muR c (kOf i) ^ 2 := by field_simp
        have e2 : 1 / 2 * (2 * π / c) = π / c := by ring
        linarith
      have h2 : (1 / c) ^ 2 ≤ π / c := by
        rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) hc0]
        nlinarith [Real.pi_gt_three]
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hμ0.le (by norm_num)).mp hsq
  -- `Σ|bᵢ| = 1 + |α| ≤ c`
  obtain ⟨g2, g2₁, g2₂c, hang2, heven2, hnorm2⟩ := rung_spec hex2
  obtain ⟨g0, g0₁, g0₂c, hang0, heven0, hnorm0⟩ := rung_spec (exists_isLevelIdx_zero c)
  have hα := Cvs.Xi.EImageWindowPoisson.sum_alpha_sq_le (Finset.univ : Finset Unit) (fun _ => rung c 2)
    (fun _ _ s hs => (g2 s hs).continuousAt.continuousWithinAt)
    (fun _ _ _ _ => by simpa [sq] using hnorm2) hc0 g0 g0₁ hang0 heven0 (by simpa [kOf] using hcnt none) hnorm0
    (psi_rung (exists_isLevelIdx_zero c))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul] at hα
  have hα' : alpha c 1 ^ 2 ≤ 2 * c := by
    have e : alpha c 1 = (∫ s in (-1 : ℝ)..1, rung c 2 s) / ∫ s in (-1 : ℝ)..1, rung c 0 s := by
      simp [alpha]
    rw [e]
    refine hα.trans ?_
    change 2 * c / (π * lamR c 0) ≤ 2 * c
    have hl0 := hhalf.trans hanti
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ π * lamR c 0 := by nlinarith [Real.pi_gt_three]
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * c by linarith)]
  have hS : ∑ i, |bOf c one₁ i| ≤ c := by
    rw [Fintype.sum_option]
    have hb0 : bOf c one₁ none = -alpha c 1 := by
      simp only [bOf, Option.elim, one₁, one_mul]
      rw [sum_one (fun j => alpha c j)]
    have hb1 : ∀ j : ({1} : Finset ℕ), bOf c one₁ (some j) = 1 := fun j => rfl
    simp only [hb1, abs_one]
    rw [sum_one (fun _ => (1 : ℝ)), hb0, abs_neg]
    have ha0 := abs_nonneg (alpha c 1)
    have ha2 : |alpha c 1| ^ 2 ≤ 2 * c := by rw [sq_abs]; exact hα'
    have key : |alpha c 1| ≤ c - 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : (c - 1) ^ 2 < |alpha c 1| ^ 2 := pow_lt_pow_left₀ hcon (by linarith) two_ne_zero
      nlinarith
    linarith
  exact ⟨fun i => (hspec i).1, fun i => (hspec i).2.1, fun i => (hspec i).2.2.1, fun i => (hspec i).2.2.2.1,
    fun i => (hspec i).2.2.2.2.1, fun i => (hspec i).2.2.2.2.2, fun i => psi_rung (hex i), hc80,
    fun i => nonneg_of_mem_evenSpec c (lev_spec (hex i)).1, hχc, hμc, hS⟩

set_option maxHeartbeats 1600000 in
/-- **Connes' normalised L1 factor is polynomial**: `C₁(x) ≤ C1poly(x)` at every `x` with `c₀^W ≤ 2πx`. -/
theorem C1conn_le (x : ℕ) (hx : c0W ≤ 2 * π * x) : C1conn x ≤ C1poly x := by
  have H := connes_spanHyp x hx
  set c : ℝ := 2 * π * x with hcdef
  have hc80 : 80 ≤ c := H.hc
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc1
  set b := bOf c one₁
  set h := fun i : Option ({1} : Finset ℕ) => rung c (kOf i)
  set h₁ := fun i : Option ({1} : Finset ℕ) => rung₁ c (kOf i)
  set h₂ := fun i : Option ({1} : Finset ℕ) => rung₂ c (kOf i)
  set μ := fun i : Option ({1} : Finset ℕ) => muR c (kOf i)
  have hb1 : (1 : ℝ) ≤ |b (some ⟨1, Finset.mem_singleton_self 1⟩)| := by simp [b, bOf, one₁]
  -- the floor
  have hκ38 : 1 / 38 ≤ kapFX x :=
    (Cvs.L2a.WindowChainInputsProlate.floor_full_span x (le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx) fun _ => 0).1
  have hκ0 : 0 < kapFX x := lt_of_lt_of_le (by norm_num) hκ38
  have hc2 : (2432 : ℝ) ≤ c ^ 2 := by nlinarith
  have hc4 : 0 < c ^ 4 := by positivity
  -- the endpoint scales
  have hVκ := H.endV_ge hκ0.le hb1
  have hV1 := H.endV_ge zero_le_one hb1
  have hVκ0 : 0 < Cvs.L2a.L1WindowFromFloor.endV c (kapFX x) b μ := lt_of_lt_of_le (by positivity) hVκ
  have hV10 : 0 < Cvs.L2a.L1WindowFromFloor.endV c 1 b μ := lt_of_lt_of_le (by positivity) hV1
  have hinvκ : 1 / Cvs.L2a.L1WindowFromFloor.endV c (kapFX x) b μ ≤ c ^ 6 := by
    rw [div_le_iff₀ hVκ0]
    calc (1 : ℝ) ≤ c ^ 6 * (kapFX x / (64 * c ^ 4)) := by
          rw [mul_div_assoc', le_div_iff₀ (by positivity)]
          have : c ^ 6 * (1 / 38) ≤ c ^ 6 * kapFX x := mul_le_mul_of_nonneg_left hκ38 (by positivity)
          nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 80) hc80 2]
      _ ≤ _ := mul_le_mul_of_nonneg_left hVκ (by positivity)
  have hinv1 : 1 / Cvs.L2a.L1WindowFromFloor.endV c 1 b μ ≤ c ^ 5 := by
    rw [div_le_iff₀ hV10]
    calc (1 : ℝ) ≤ c ^ 5 * (1 / (64 * c ^ 4)) := by
          rw [mul_one_div, le_div_iff₀ (by positivity)]
          nlinarith [pow_pos hc0 4]
      _ ≤ _ := mul_le_mul_of_nonneg_left hV1 (by positivity)
  -- the three levels
  have hD := H.levD_le
  have hD0 : 0 ≤ Cvs.L2a.L1WindowFromFloor.levD c b h h₁ h₂ := by
    have := Cvs.L2a.L1FullTailWinfBound.betaS_nonneg c b h
    have := Cvs.L2a.L1FullTailWinfBound.alphaS_nonneg hc0.le b h
    have := Cvs.L2a.FullTailUpperFrame.K1bS_nonneg b H.hg H.hg₁ H.hg₂c hc0
    have : 0 ≤ Cvs.L2a.L1WindowFromFloor.tailN c b h := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
    unfold Cvs.L2a.L1WindowFromFloor.levD; positivity
  have hlK : 3 * π * c + 2 * Real.log (Cvs.L2a.L1WindowFromFloor.levD c b h h₁ h₂
      / Cvs.L2a.L1WindowFromFloor.endV c (kapFX x) b μ) ≤ 3 * π * c + 28 * Real.log c := by
    have hr : Cvs.L2a.L1WindowFromFloor.levD c b h h₁ h₂ / Cvs.L2a.L1WindowFromFloor.endV c (kapFX x) b μ ≤ c ^ 14 := by
      rw [div_eq_mul_one_div]
      calc _ ≤ c ^ 8 * c ^ 6 := mul_le_mul hD hinvκ (by positivity) (by positivity)
        _ = c ^ 14 := by ring
    have := log_le_pow (div_nonneg hD0 hVκ0.le) hc1 hr
    push_cast at this; linarith
  have hB := H.BG_le
  have hlΘ : 3 * π * c / 2 + Real.log (max 1 (Cvs.L2a.L1WindowFromFloor.posB c b h h₁ h₂ ^ 2
      / Cvs.L2a.L1WindowFromFloor.endV c (kapFX x) b μ)) ≤ 3 * π * c / 2 + 12 * Real.log c := by
    have hB0 : 0 ≤ Cvs.L2a.L1WindowFromFloor.posB c b h h₁ h₂ := by
      unfold Cvs.L2a.L1WindowFromFloor.posB
      exact Cvs.L2a.FullTailConvergence.BG_nonneg hc0 _
        (Cvs.L2a.FullTailConvergence.C1_nonneg (fun t => ∑ i, b i * h₁ i t) (fun t => ∑ i, b i * h₂ i t))
    have hr : max 1 (Cvs.L2a.L1WindowFromFloor.posB c b h h₁ h₂ ^ 2 / Cvs.L2a.L1WindowFromFloor.endV c (kapFX x) b μ)
        ≤ c ^ 12 := by
      refine max_le (one_le_pow₀ hc1) ?_
      rw [div_eq_mul_one_div]
      calc _ ≤ (c ^ 3) ^ 2 * c ^ 6 :=
            mul_le_mul (pow_le_pow_left₀ hB0 hB 2) hinvκ (by positivity) (by positivity)
        _ = c ^ 12 := by ring
    have := log_le_pow (by positivity) hc1 hr
    push_cast at this; linarith
  have hKb := H.K1bS_le
  have hP := H.P_le
  have hlev : connesLevel x ≤ 3 * π * c + 26 * Real.log c := by
    unfold connesLevel
    refine max_le (by positivity) ?_
    have hKb0 := Cvs.L2a.FullTailUpperFrame.K1bS_nonneg b H.hg H.hg₁ H.hg₂c hc0
    have hP0 : 0 ≤ ∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (h i) t ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _)
    have hr : (Cvs.L2a.L1FullTailWinfBound.K1bS c b h h₁ h₂ + ∑ i, b i ^ 2 * ∫ t in Ioi 1, psi c (h i) t ^ 2)
        / Cvs.L2a.L1WindowFromFloor.endV c 1 b μ ≤ c ^ 13 := by
      rw [div_eq_mul_one_div]
      have h8 : c ^ 7 + c ^ 2 ≤ c ^ 8 := by
        have := mul_le_mul_of_nonneg_right hc80 (pow_pos hc0 7).le
        have := pow_le_pow_right₀ hc1 (show 2 ≤ 7 by norm_num)
        nlinarith [pow_pos hc0 7]
      calc _ ≤ c ^ 8 * c ^ 5 := mul_le_mul (by linarith) hinv1 (by positivity) (by positivity)
        _ = c ^ 13 := by ring
    have := log_le_pow (div_nonneg (by linarith) hV10.le) hc1 hr
    push_cast at this; linarith
  -- `L1bound ≤ L1poly`
  have hL1 : Cvs.L2a.L1WindowFromFloor.L1bound c (kapFX x) (1 / 2) b μ h h₁ h₂ ≤ L1poly c := by
    unfold Cvs.L2a.L1WindowFromFloor.L1bound Cvs.L2a.L1CutLevelExponent.L1sym L1poly
    rw [card_eq]
    have hsκ : 1 / √(kapFX x) ≤ 7 := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr hκ0)]
      have : √(1 / 38 : ℝ) ≤ √(kapFX x) := Real.sqrt_le_sqrt hκ38
      have h38 : (1 : ℝ) / 7 ≤ √(1 / 38) := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      linarith
    have hpi : Cvs.Prolate.RungTailIntegralMass.piConst 2 c ≤ 2 := by
      unfold Cvs.Prolate.RungTailIntegralMass.piConst
      have h5 : 1 / √5 ≤ 1 := by rw [div_le_one (by positivity)]; exact Real.one_le_sqrt.mpr (by norm_num)
      have h12 : √(6 * 2 : ℝ) ≤ 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have : 3 * √(6 * 2 : ℝ) / c * (30 / 11 + 3 / 4) ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one hc0]
        have : 3 * √(6 * 2 : ℝ) * (30 / 11 + 3 / 4) ≤ 3 * 4 * (30 / 11 + 3 / 4) := by gcongr
        linarith
      linarith
    have hpi0 := Cvs.L2a.FullTailBilinearBound.piConst_nonneg (J := 2) hc0
    have t1 : 2 * Cvs.Prolate.RungTailIntegralMass.piConst 2 c / √(kapFX x) ≤ 28 := by
      rw [div_eq_mul_one_div]
      nlinarith [mul_le_mul hpi hsκ (by positivity) (by norm_num)]
    have t2 : Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol (2 * c)
        ≤ |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + Cvs.WeilForm.Archimedean.ArchFormIntegrable.growth * (2 * c) ^ 2 :=
      (le_abs_self _).trans (Cvs.WeilForm.Archimedean.ArchFormIntegrable.abs_archSymbol_le _)
    have t3 : 57 / c ≤ 1 := by rw [div_le_one hc0]; linarith
    have hcube : (1 + (3 * π * c + 2 * Real.log (Cvs.L2a.L1WindowFromFloor.levD c b h h₁ h₂
        / Cvs.L2a.L1WindowFromFloor.endV c (kapFX x) b μ))) ^ 3
        ≤ (1 + (3 * π * c + 28 * Real.log c)) ^ 3 :=
      (Odd.strictMono_pow (by decide : Odd 3)).monotone (by linarith)
    have hcube0 : 0 ≤ (1 + (3 * π * c + 28 * Real.log c)) ^ 3 := by positivity
    have t4 : 8 * 2 * (1 + (3 * π * c + 2 * Real.log (Cvs.L2a.L1WindowFromFloor.levD c b h h₁ h₂
        / Cvs.L2a.L1WindowFromFloor.endV c (kapFX x) b μ))) ^ 3 / kapFX x
        ≤ 608 * (1 + (3 * π * c + 28 * Real.log c)) ^ 3 := by
      rw [div_le_iff₀ hκ0]
      nlinarith [mul_le_mul_of_nonneg_left hκ38 hcube0]
    have t5 := Cvs.L2a.WindowChainFromInputs.KpolL_anti (l := 1 / 2) (by norm_num) (by norm_num) hκ38
    have t6 := Cvs.L2a.WindowThresholdExplicit.KpolL_half_le
    linarith
  -- assemble
  have hL1p : 0 ≤ L1poly c := by
    have := (abs_nonneg (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0))
    have := Cvs.WeilForm.Archimedean.ArchFormIntegrable.growth_nonneg
    unfold L1poly; positivity
  have hfr : Cvs.L2a.FullTailUpperFrame.frameC (Fintype.card (Option ({1} : Finset ℕ))) (connesLevel x)
      ≤ Cvs.L2a.FullTailUpperFrame.frameC 2 (3 * π * c + 26 * Real.log c) := by
    rw [card_eq]; unfold Cvs.L2a.FullTailUpperFrame.frameC
    have h0 : 0 ≤ connesLevel x := le_max_left _ _
    have := mul_le_mul (show 1 + connesLevel x ≤ 1 + (3 * π * c + 26 * Real.log c) by linarith)
      (show 2 * (1 + 8 * connesLevel x) ≤ 2 * (1 + 8 * (3 * π * c + 26 * Real.log c)) by linarith)
      (by positivity) (by positivity)
    nlinarith
  have hfr0 : 0 ≤ Cvs.L2a.FullTailUpperFrame.frameC (Fintype.card (Option ({1} : Finset ℕ))) (connesLevel x) :=
    Cvs.L2a.FullTailUpperFrame.frameC_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
  have hQ : 0 ≤ 25 * (x : ℝ) * Real.log x / (4 * ‖Cvs.Limit.ZeroFreeApproximantsRH.Xi 0‖ ^ 2) := by
    have : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by
      have := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hc80; exact_mod_cast this.le))
    positivity
  have h4 : 0 ≤ 4 + π / c := by positivity
  have hm : max 0 (Cvs.L2a.L1WindowFromFloor.L1bound c (kapFX x) (1 / 2) b μ h h₁ h₂) ≤ L1poly c :=
    max_le hL1p hL1
  have hF := mul_le_mul hm hfr hfr0 hL1p
  have hF2 := mul_le_mul hF (le_refl (4 + π / c)) h4 (mul_nonneg hL1p (Cvs.L2a.FullTailUpperFrame.frameC_nonneg
    (by norm_num) (by positivity)))
  exact mul_le_mul hF2 (le_refl _) hQ (mul_nonneg (mul_nonneg hL1p (Cvs.L2a.FullTailUpperFrame.frameC_nonneg
    (by norm_num) (by positivity))) h4)

/-- `λ₄ ≤ 1` at the spine scale. -/
theorem one_sub_lamR_nonneg (x : ℕ) (hx : c0W ≤ 2 * π * x) : 0 ≤ 1 - lamR (2 * π * x) 2 := by
  have H := connes_spanHyp x hx
  set c : ℝ := 2 * π * x
  have hc0 : 0 < c := by linarith [H.hc]
  set i : Option ({1} : Finset ℕ) := some ⟨1, Finset.mem_singleton_self 1⟩
  have hk : kOf i = 2 := rfl
  have hgc : ContinuousOn (rung c 2) (Icc (-1) 1) := fun s hs =>
    (H.hg i s (by rw [uIcc_of_le (by norm_num)]; exact hs)).continuousAt.continuousWithinAt
  have hm := Cvs.Prolate.AngularBesselInequality.mass_eq hc0 hgc (H.heven i) (H.hμ i) (H.hnorm i)
  have h0 : 0 ≤ ∫ ξ in Ioi 1, psi c (rung c 2) ξ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun _ _ => sq_nonneg _
  change 0 ≤ ∫ ξ in Ioi 1, psi c (rung c 2) ξ ^ 2 at h0
  rw [hm, hk] at h0
  have hpc : 0 < π / c := by positivity
  change 0 ≤ 1 - (muR c 2 * √(c / (2 * π))) ^ 2
  by_contra hneg
  push Not at hneg
  nlinarith [mul_neg_of_pos_of_neg hpc hneg]

open Cvs.Route.JointGapConnesFromL1 (connesEven connesOdd) in
/-- **L1's polynomial gap at scale `x`**: `L1GapN` with `C₁` replaced by the explicit polynomial `C1poly`. -/
def L1GapP (x : ℕ) : Prop :=
  ∃ (hx : c0W ≤ 2 * π * x) (s μ : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)),
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → inner ℝ η φ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    √(x : ℝ) * Real.log x * (C1poly x * (1 - lamR (2 * π * x) 2)
        + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2 / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
      + (√(x : ℝ) * Real.log x - 1) * s < μ

/-- **RH from L1's polynomial gap**: `L1GapP x` at infinitely many integers `x` gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_L1GapP (h : ∃ᶠ x : ℕ in atTop, L1GapP x) : RiemannHypothesis := by
  refine Cvs.L2a.L1NormalisedConnes.riemannHypothesis_of_L1GapN (h.mono fun x ⟨hx, s, μ, η, hneg, hfloor, hlt⟩ => ?_)
  refine ⟨hx, s, μ, η, hneg, hfloor, lt_of_le_of_lt ?_ hlt⟩
  have hK : 0 ≤ √(x : ℝ) * Real.log x := by
    have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80).le)
  have hC := mul_le_mul_of_nonneg_right (C1conn_le x hx) (one_sub_lamR_nonneg x hx)
  have := mul_le_mul_of_nonneg_left (add_le_add_right hC
    (s * ‖Cvs.Route.JointGapConnesFromL1.connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2
      / ‖Cvs.Route.JointGapConnesFromL1.connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)) hK
  linarith

end Cvs.L2a.L1ConnesFactorPolynomial
