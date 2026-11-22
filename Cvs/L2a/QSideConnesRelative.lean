import Mathlib
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandInputsFromCutMultipliers
import Cvs.L2a.FiniteSpanRateHighMass
import Cvs.L2a.FullSpanThreshold
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailFloorLimit
import Cvs.L2a.FullTailPoleChannel
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.L1ConnesFactorPolynomial
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.L1WindowFromWinf
import Cvs.L2a.LowRungHighSpectralMass
import Cvs.L2a.LowRungTruncationRate
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.RungSpanProfilePowers
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainFromInputs
import Cvs.L2a.WindowChainInputsProlate
import Cvs.L2a.WindowFullSpanProlate
import Cvs.L2a.WinfHighMassDecay
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.LowLevelsTwoFifths
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFamilyRangePartners
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.L1GapParametricRH
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.InfimumAttainedSphere
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
# The q-side at Connes' vector from the relative `W_∞` bound

At `c = 2πx`, `c₀^W ≤ 2πx`, with `Φ = Σᵢ bᵢψᵢ` Connes' span, `N = ∫F²`, `M = (Σᵢ|bᵢ||ψᵢ(1)|)²`:
`Q(k) ≤ 2Π₊∫F/θ + (a(2c) + 114/(2c))N + 2Khigh M + 4√Krate (M + N) + 4Krate M + K_pol(½, κ_F)N`;
`L1GapL` against this bound at infinitely many `x` gives RH.
-/

noncomputable section

open MeasureTheory Set Real Filter Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan

namespace Cvs.L2a.QSideConnesRelative
open Cvs.ZeroCounting

open Cvs.L2a.ProlateFamilySpine (kOf bOf sum_option_eq_spineG sum_option_pole)
open Cvs.L2a.WindowChainInputsProlate (c0W kapFX)
open Cvs.L2a.WindowFullSpanProlate (extN sum_extN)
open Cvs.Route.JointGapConnesFromL1 (one₁)
open Cvs.L2a.FullTailConvergence (fullTail)
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.LowRungTruncationRate (Krate)
open Cvs.L2a.LowRungHighSpectralMass (Khigh)

/-- Connes' span profile `Φ = Σᵢ bᵢψᵢ` at `c = 2πx`. -/
def connesPhi (x : ℕ) : ℝ → ℝ :=
  fun ξ => ∑ i, bOf (2 * π * x) one₁ i * psi (2 * π * x) (rung (2 * π * x) (kOf i)) ξ

/-- Connes' tail norm `N = ∫_{θ>1} F²` at `c = 2πx`. -/
def connesN (x : ℕ) : ℝ :=
  Cvs.L2a.L1WindowFromFloor.tailN (2 * π * x) (bOf (2 * π * x) one₁) (fun i => rung (2 * π * x) (kOf i))

/-- Connes' edge scale `M = (Σᵢ |bᵢ||ψᵢ(1)|)²` at `c = 2πx`. -/
def connesM (x : ℕ) : ℝ :=
  (∑ i, |bOf (2 * π * x) one₁ i| * |psi (2 * π * x) (rung (2 * π * x) (kOf i)) 1|) ^ 2

/-- **The relative q-side bound** on Connes' class at `c = 2πx`. -/
def connesLrel (x : ℕ) : ℝ :=
  2 * Cvs.L2a.FullTailPoleChannel.piPlus (connesPhi x) * (∫ θ in Ioi 1, fullTail (connesPhi x) θ / θ)
    + (archSymbol (2 * (2 * π * x)) + 114 / (2 * (2 * π * x))) * connesN x
    + 2 * Khigh (2 * π * x) * connesM x + 4 * √(Krate (2 * π * x)) * (connesM x + connesN x)
    + 4 * Krate (2 * π * x) * connesM x
    + Cvs.L2a.WindowChainFromInputs.KpolL (1 / 2) (kapFX x) * connesN x

/-- `c₀^W ≤ 2πx` gives `100 ≤ 2πx`. -/
theorem hundred_le {x : ℕ} (hx : c0W ≤ 2 * π * x) : 100 ≤ 2 * π * (x : ℝ) := by
  have h := (Cvs.L2a.BandInputsFromCutMultipliers.scale_ge (le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx)).1
  have := Real.add_one_le_exp (1360 : ℝ)
  linarith

/-- **The window form of Connes' profile** is at most `connesLrel x`. -/
theorem window_le_rel (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    Cvs.WeilForm.SelfConvolutionFunctional.weilForm x (Nat.clog 2 x) (Cvs.L2a.TailLogScaleTest.logScale
        (Cvs.Xi.EImageWindowPoisson.window (2 * π / (2 * π * x)) (spineG (2 * π * x) one₁)))
      ≤ connesLrel x := by
  have H := Cvs.L2a.L1ConnesFactorPolynomial.connes_spanHyp x hx
  set c : ℝ := 2 * π * x with hcdef
  have hxF : Cvs.L2a.FullSpanThreshold.c0F ≤ c := le_trans Cvs.L2a.WindowChainInputsProlate.c0F_le_c0W hx
  have hc80 : 80 ≤ c := H.hc
  have hc100 : 100 ≤ c := hundred_le hx
  have hc0 : 0 < c := by linarith
  have hx1' : 1 < x := by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)
  have hx1 : 1 ≤ x := hx1'.le
  have hS : ∀ j ∈ ({1} : Finset ℕ), 1 ≤ j ∧ j < x := fun j hj => by
    rw [Finset.mem_singleton.mp hj]; exact ⟨le_rfl, hx1'⟩
  have hex : ∀ i : Option ({1} : Finset ℕ), ∃ χ, IsLevelIdx c (kOf i) χ := by
    rintro (_ | j)
    · exact exists_isLevelIdx_zero c
    · exact Cvs.Prolate.RungFamilyRangePartners.exists_main hc80 ⟨j, Finset.mem_range.2 (hS j j.2).2⟩
  have hcnt : ∀ i : Option ({1} : Finset ℕ), (evenSpec (sqC c) ∩ Iio (lev c (kOf i))).ncard = kOf i :=
    fun i => (lev_spec (hex i)).2
  have hkpos : ∀ j : ({1} : Finset ℕ), 2 ≤ kOf (some j) := fun j => by
    simp only [kOf, Option.elim]; have := (hS j j.2).1; omega
  have hJ : (Fintype.card (Option ({1} : Finset ℕ)) : ℝ) ≤ c / 4 + 1 := by
    have : (Fintype.card (Option ({1} : Finset ℕ)) : ℝ) = 2 := by simp [Fintype.card_option]
    rw [this]; linarith
  obtain ⟨hP, hR⟩ := sizes_PR hx1
  have hlam : ∀ i : Option ({1} : Finset ℕ), i ≠ none → 1 / 2 ≤ (muR c (kOf i) * √(c / (2 * π))) ^ 2 := by
    rintro (_ | j) hne
    · exact absurd rfl hne
    · exact Cvs.L2a.WindowChainInputsProlate.half_le_lamR hc80 (hS j j.2).2
  -- the levels are at most `(2/5)c²`
  have hχ25 : ∀ i : Option ({1} : Finset ℕ), lev c (kOf i) ≤ 2 / 5 * c ^ 2 := by
    rintro (_ | j)
    · show lev c 0 ≤ 2 / 5 * c ^ 2
      rw [lev_zero]
      have := groundLevel_le c
      nlinarith
    · have hj : (j : ℕ) = 1 := Finset.mem_singleton.mp j.2
      have hk : kOf (some j) = 2 := by simp only [kOf, Option.elim, hj]
      rw [hk]
      exact (Cvs.Prolate.LowLevelsTwoFifths.lev_two_lt (c := c) (by nlinarith [Real.pi_lt_four])).1.le
  -- the floor
  set b := bOf c one₁ with hbd
  set h : Option ({1} : Finset ℕ) → ℝ → ℝ := fun i => rung c (kOf i) with hhd
  have hΦ : (fun ξ => ∑ j : Finset.range x, extN b j * psi c (rung c (2 * (j : ℕ))) ξ)
      = fun ξ => ∑ i : Option ({1} : Finset ℕ), b i * psi c (rung c (kOf i)) ξ := by
    funext ξ
    exact sum_extN hx1 hS b (fun t n => t * psi c (rung c n) ξ) fun _ => zero_mul _
  have hPm : ∑ j : Finset.range x, extN b j ^ 2 * (∫ ξ in Ioi 1, psi c (rung c (2 * (j : ℕ))) ξ ^ 2)
      = ∑ i : Option ({1} : Finset ℕ), b i ^ 2 * (∫ ξ in Ioi 1, psi c (rung c (kOf i)) ξ ^ 2) :=
    sum_extN hx1 hS b (fun t n => t ^ 2 * ∫ ξ in Ioi 1, psi c (rung c n) ξ ^ 2) fun _ => by simp
  obtain ⟨h38, hfl⟩ := Cvs.L2a.WindowChainInputsProlate.floor_full_span x hxF fun j => extN b j
  rw [hΦ, hPm] at hfl
  have hκF : 0 < kapFX x := lt_of_lt_of_le (by norm_num) h38
  have hb : ∃ i, b i ≠ 0 := ⟨some ⟨1, Finset.mem_singleton_self 1⟩, by simp [hbd, bOf, one₁]⟩
  have hidx : ∀ i : Option ({1} : Finset ℕ), Even (evenSpec (sqC c) ∩ Iio (lev c (kOf i))).ncard := by
    intro i
    rw [hcnt i]
    rcases i with _ | j
    · exact ⟨0, rfl⟩
    · exact ⟨j, by simp only [kOf, Option.elim]; ring⟩
  -- the `W_∞` bound
  set G : ℝ → ℝ := fun s => ∑ i, b i * h i s with hGd
  have hGd' := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b H.hg
  have hGd₁ := Cvs.L2a.FullTailFloorLimit.hasDerivAt_span b H.hg₁
  have hGc₂ := Cvs.L2a.FullTailFloorLimit.continuousOn_span b H.hg₂c
  have hspan : (fun ξ => ∑ i, b i * psi c (h i) ξ) = psi c G := Cvs.L2a.FullTailFloorLimit.span_eq b H.hg c
  have hNpos : 0 < Cvs.L2a.L1WindowFromFloor.tailN c b h :=
    Cvs.L2a.L1WindowFromWinf.tailN_pos b H.hg H.hg₁ H.hg₂c H.hang (by linarith) H.hχ0 (fun i => (H.hχc i).le)
      H.heven H.hnorm H.hμ hidx hκF hfl hb
  have hN : 0 < ∫ θ in Ioi 1, fullTail (psi c G) θ ^ 2 := by
    rw [← hspan]; exact hNpos
  have hW := Cvs.L2a.WinfHighMassDecay.Winf_le_relM hGd' hGd₁ hGc₂ (by linarith)
    (Cvs.L2a.FiniteSpanRateHighMass.Krate_nonneg hc0) (by unfold Khigh; positivity)
    (M := (∑ i, |b i| * |psi c (h i) 1|) ^ 2) (by positivity) hN
    (fun k hk => Cvs.L2a.FiniteSpanRateHighMass.integral_posTail_sub_fullTail_le b H.hg H.hg₁ H.hg₂c H.hang hc100
      H.hχ0 hχ25 hk)
    (fun k hk => Cvs.L2a.FiniteSpanRateHighMass.highMass_le b H.hg H.hg₁ H.hg₂c H.hang hc100 H.hχ0 hχ25 hk)
  rw [← hspan] at hW
  rw [← sum_option_eq_spineG]
  refine (Cvs.L2a.L1WindowFromWinf.L1_window_of_Winf (ι := Option ({1} : Finset ℕ)) none
    (h := h) (h₁ := fun i => rung₁ c (kOf i)) (h₂ := fun i => rung₂ c (kOf i))
    (χ := fun i => lev c (kOf i)) (μ := fun i => muR c (kOf i)) b
    H.hg H.hg₁ H.hg₂c H.hang hc80 H.hχ0 H.hχc ?_ H.heven H.hnorm H.hμ (hcnt none) hidx hJ
    (by norm_num : (0 : ℝ) < 1 / 2) hlam hκF hfl (sum_option_pole hc0 one₁) hP hR hb hW).trans (le_of_eq ?_)
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
  · rfl

/-- **The q-side at Connes' vector from the relative `W_∞` bound**: `Q(k) ≤ connesLrel x` for `c₀^W ≤ 2πx`. -/
theorem Q_connesClass_le_rel (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.CosineColumnTailPairing.connesClass (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx))
      ≤ connesLrel x := by
  unfold Cvs.Approximant.CosineColumnTailPairing.connesClass
  rw [Cvs.Approximant.SpineSubspace.Q_ofFun, Cvs.Approximant.SpineSubspace.weilForm_kG]
  exact window_le_rel x hx

/-- **RH from L1's gap against the relative bound** at infinitely many integers `x`. -/
theorem riemannHypothesis_of_L1GapRel (h : ∃ᶠ x : ℕ in atTop, Cvs.Route.L1GapParametricRH.L1GapL connesLrel x) :
    RiemannHypothesis :=
  Cvs.Route.L1GapParametricRH.riemannHypothesis_of_L1GapL (fun x hx => Q_connesClass_le_rel x hx) h

end Cvs.L2a.QSideConnesRelative
