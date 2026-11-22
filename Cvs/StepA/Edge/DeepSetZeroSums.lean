import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.CorrectedPairingUSums
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FiniteTopTieTerm
import Cvs.StepA.Edge.OffTopPairingBound
import Cvs.StepA.RestEnvelopeSmall
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.QuadraticWeightSummable
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge
import Cvs.Zeta.ZeroTailInverseSquare

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The zero sums off a deep set: the pairing part and the low shallow part

`D = deepSet δ_D H` holds the zeros with `|γ| ≤ H` and `|δ| ≥ δ_D`. Off `D`, a zero is shallow or above `H`, so
`Σ_{ρ ∉ D} m_ρ⟪V_σ, U_ρ⟫² ≤ x^{|δ_σ| + δ_D}(L² n_σ + 16 Z) + 16 x^{|δ_σ| + Θ} tailBound(H)` with `Z = Σ m/γ²`,
`n_σ` the weight below `2|γ_σ| + 1`, and `Θ` any bound on `|δ|` (caseinf-attack §6.2). The `U`-Gram entries are
summable in `ρ`, `‖U_ρ‖² ≤ L x^{|δ_ρ|}`, and the weight below `H'` is at most `(1 + H'²)Σ m/(1 + γ²)` (§6.3 (S3a)).
-/

noncomputable section

open Real MeasureTheory Filter Set
open scoped InnerProductSpace
open Cvs.StepA.Edge.FiniteTopGap (mult mult_nonneg)
open Cvs.StepA.Edge.FiniteTopTieTerm (pairUe)
open Cvs.StepA.Edge.CorrectedPairingUSums (ueUe)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.StepA.Edge.DeepSetZeroSums
open Cvs.ZeroCounting

/-! ### The deep set -/

/-- The deep set at height `H`: the zeros with `|γ| ≤ H` and `|δ| ≥ δ_D`. -/
def deepSet (δD H : ℝ) : Finset nonTrivialZeroSet :=
  (Cvs.GaussKernel.finite_window H).toFinset.filter fun ρ => δD ≤ |Cvs.GaussKernel.del ρ|

theorem mem_deepSet {δD H : ℝ} {ρ : nonTrivialZeroSet} :
    ρ ∈ deepSet δD H ↔ |(ρ : ℂ).im| ≤ H ∧ δD ≤ |Cvs.GaussKernel.del ρ| := by
  simp [deepSet, Cvs.GaussKernel.gam]

/-! ### Near and far bounds for the Gram entries, at any pair of zeros -/

/-- `pairUe(L, z_σ, z_ρ)² ≤ L² e^{(|δ_σ| + |δ_ρ|)L}`. -/
theorem pairUe_sq_near (σ ρ : nonTrivialZeroSet) {L : ℝ} (hL : 0 ≤ L) :
    pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2
      ≤ L ^ 2 * exp ((|Cvs.GaussKernel.del σ| + |Cvs.GaussKernel.del ρ|) * L) :=
  Cvs.StepA.Edge.OffTopPairingBound.pairUe_sq_le fun a b _ hb => (Cvs.StepA.Edge.OffTopPairingBound.sinSinhC_sq_le_mul a b hL).trans (mul_le_mul_of_nonneg_left
    (exp_le_exp.2 (mul_le_mul_of_nonneg_right (Cvs.StepA.Edge.OffTopPairingBound.abs_im_pm_le rfl hb) hL)) (sq_nonneg L))

/-- `pairUe(L, z_σ, z_ρ)² ≤ 16γ_ρ⁻² e^{(|δ_σ| + |δ_ρ|)L}` for `|γ_ρ| ≥ 2|γ_σ| + 1`. -/
theorem pairUe_sq_far (σ ρ : nonTrivialZeroSet) {L : ℝ} (hL : 0 ≤ L)
    (hR : 2 * |(σ : ℂ).im| + 1 ≤ |(ρ : ℂ).im|) :
    pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2
      ≤ 16 * (1 / ((ρ : ℂ).im) ^ 2) * exp ((|Cvs.GaussKernel.del σ| + |Cvs.GaussKernel.del ρ|) * L) :=
  Cvs.StepA.Edge.OffTopPairingBound.pairUe_sq_le fun a b ha hb => by
    rw [Cvs.ZeroCounting.zPoint_re, Cvs.ZeroCounting.zPoint_re] at ha
    obtain ⟨ha0, hc⟩ := Cvs.StepA.Edge.OffTopPairingBound.far_coef hR ha
    exact (Cvs.StepA.Edge.OffTopPairingBound.sinSinhC_sq_le_div ha0 b hL).trans (mul_le_mul hc
      (exp_le_exp.2 (mul_le_mul_of_nonneg_right (Cvs.StepA.Edge.OffTopPairingBound.abs_im_pm_le rfl hb) hL)) (exp_pos _).le (by positivity))

/-- `ueUe(L, z_r, z_ρ)² ≤ L² e^{(|δ_r| + |δ_ρ|)L}`. -/
theorem ueUe_sq_near (r ρ : nonTrivialZeroSet) {L : ℝ} (hL : 0 ≤ L) :
    ueUe L (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) ^ 2
      ≤ L ^ 2 * exp ((|Cvs.GaussKernel.del r| + |Cvs.GaussKernel.del ρ|) * L) :=
  Cvs.StepA.Edge.CorrectedPairingUSums.ueUe_sq_le fun a b _ hb => (Cvs.StepA.Edge.OffTopPairingBound.cosCoshC_sq_le_mul a b hL).trans (mul_le_mul_of_nonneg_left
    (exp_le_exp.2 (mul_le_mul_of_nonneg_right (Cvs.StepA.Edge.OffTopPairingBound.abs_im_pm_le rfl hb) hL)) (sq_nonneg L))

/-- `ueUe(L, z_r, z_ρ)² ≤ 16γ_ρ⁻² e^{(|δ_r| + |δ_ρ|)L}` for `|γ_ρ| ≥ 2|γ_r| + 1`. -/
theorem ueUe_sq_far (r ρ : nonTrivialZeroSet) {L : ℝ} (hL : 0 ≤ L) (hR : 2 * |(r : ℂ).im| + 1 ≤ |(ρ : ℂ).im|) :
    ueUe L (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) ^ 2
      ≤ 16 * (1 / ((ρ : ℂ).im) ^ 2) * exp ((|Cvs.GaussKernel.del r| + |Cvs.GaussKernel.del ρ|) * L) :=
  Cvs.StepA.Edge.CorrectedPairingUSums.ueUe_sq_le fun a b ha hb => by
    rw [Cvs.ZeroCounting.zPoint_re, Cvs.ZeroCounting.zPoint_re] at ha
    obtain ⟨ha0, hc⟩ := Cvs.StepA.Edge.OffTopPairingBound.far_coef hR ha
    exact (Cvs.StepA.Edge.OffTopPairingBound.cosCoshC_sq_le_div ha0 b hL).trans (mul_le_mul hc
      (exp_le_exp.2 (mul_le_mul_of_nonneg_right (Cvs.StepA.Edge.OffTopPairingBound.abs_im_pm_le rfl hb) hL)) (exp_pos _).le (by positivity))

/-! ### Summability -/

/-- The weight below height `R` is finitely supported. -/
theorem summable_mul_ite_lt (R c : ℝ) :
    Summable fun ρ : nonTrivialZeroSet => mult ρ * (if |(ρ : ℂ).im| < R then c else 0) := by
  refine summable_of_hasFiniteSupport ((Cvs.GaussKernel.finite_window R).subset fun ρ hρ => ?_)
  rw [Function.mem_support] at hρ
  simp only [Set.mem_ofPred_eq, Cvs.GaussKernel.gam]
  by_contra h
  exact hρ (by rw [if_neg fun h' => h h'.le, mul_zero])

/-- **A near/far family is summable**: `0 ≤ f ≤ A` everywhere and `f ≤ B/γ²` for `|γ| ≥ R` give `Σ m f < ∞`. -/
theorem summable_mul_of_near_far {f : nonTrivialZeroSet → ℝ} (hf0 : ∀ ρ, 0 ≤ f ρ) {R A B : ℝ} (hB : 0 ≤ B)
    (hnear : ∀ ρ : nonTrivialZeroSet, f ρ ≤ A)
    (hfar : ∀ ρ : nonTrivialZeroSet, R ≤ |(ρ : ℂ).im| → f ρ ≤ B * (1 / ((ρ : ℂ).im) ^ 2)) :
    Summable fun ρ => mult ρ * f ρ := by
  have hg := (summable_mul_ite_lt R A).add (Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq.mul_left B)
  refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (mult_nonneg ρ) (hf0 ρ)) (fun ρ => ?_) hg
  have hm := mult_nonneg ρ
  have hz : 0 ≤ B * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2)) := mul_nonneg hB (mul_nonneg hm (by positivity))
  show mult ρ * f ρ ≤ mult ρ * (if |(ρ : ℂ).im| < R then A else 0)
    + B * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / ((ρ : ℂ).im) ^ 2))
  split_ifs with h
  · nlinarith [mul_le_mul_of_nonneg_left (hnear ρ) hm]
  · have := mul_le_mul_of_nonneg_left (hfar ρ (not_lt.1 h)) hm
    simp only [mult] at this hz ⊢
    nlinarith

/-- **The `V`–`U` Gram row of a zero is summable** at every `L ≥ 0`. -/
theorem summable_mul_pairUe_sq (σ : nonTrivialZeroSet) {L : ℝ} (hL : 0 ≤ L) :
    Summable fun ρ => mult ρ * pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2 := by
  have he : ∀ ρ : nonTrivialZeroSet, exp ((|Cvs.GaussKernel.del σ| + |Cvs.GaussKernel.del ρ|) * L)
      ≤ exp ((|Cvs.GaussKernel.del σ| + 1 / 2) * L) := fun ρ =>
    exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith [Cvs.GaussKernel.del_bdd ρ]) hL)
  refine summable_mul_of_near_far (fun _ => sq_nonneg _) (R := 2 * |(σ : ℂ).im| + 1)
    (B := 16 * exp ((|Cvs.GaussKernel.del σ| + 1 / 2) * L)) (by positivity)
    (fun ρ => (pairUe_sq_near σ ρ hL).trans (mul_le_mul_of_nonneg_left (he ρ) (sq_nonneg L)))
    (fun ρ hR => ?_)
  refine (pairUe_sq_far σ ρ hL hR).trans ?_
  have := mul_le_mul_of_nonneg_left (he ρ) (by positivity : (0 : ℝ) ≤ 16 * (1 / ((ρ : ℂ).im) ^ 2))
  nlinarith

/-- **The `U`–`U` Gram row of a zero is summable** at every `L ≥ 0`. -/
theorem summable_mul_ueUe_sq (r : nonTrivialZeroSet) {L : ℝ} (hL : 0 ≤ L) :
    Summable fun ρ => mult ρ * ueUe L (Cvs.ZeroCounting.zPoint r) (Cvs.ZeroCounting.zPoint ρ) ^ 2 := by
  have he : ∀ ρ : nonTrivialZeroSet, exp ((|Cvs.GaussKernel.del r| + |Cvs.GaussKernel.del ρ|) * L)
      ≤ exp ((|Cvs.GaussKernel.del r| + 1 / 2) * L) := fun ρ =>
    exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith [Cvs.GaussKernel.del_bdd ρ]) hL)
  refine summable_mul_of_near_far (fun _ => sq_nonneg _) (R := 2 * |(r : ℂ).im| + 1)
    (B := 16 * exp ((|Cvs.GaussKernel.del r| + 1 / 2) * L)) (by positivity)
    (fun ρ => (ueUe_sq_near r ρ hL).trans (mul_le_mul_of_nonneg_left (he ρ) (sq_nonneg L)))
    (fun ρ hR => ?_)
  refine (ueUe_sq_far r ρ hL hR).trans ?_
  have := mul_le_mul_of_nonneg_left (he ρ) (by positivity : (0 : ℝ) ≤ 16 * (1 / ((ρ : ℂ).im) ^ 2))
  nlinarith

/-! ### The pairing part off the deep set -/

/-- The weight of the zeros below `2|γ_σ| + 1`. -/
def nearWeight (σ : nonTrivialZeroSet) : ℝ :=
  ∑' ρ : nonTrivialZeroSet, mult ρ * (if |(ρ : ℂ).im| < 2 * |(σ : ℂ).im| + 1 then 1 else 0)

/-- `Z = Σ_ρ m_ρ/γ_ρ²`. -/
def invSqSum : ℝ := ∑' ρ : nonTrivialZeroSet, mult ρ * (1 / ((ρ : ℂ).im) ^ 2)

/-- **The pairing part off the deep set** (§6.2): with `|δ| ≤ Θ` for every zero, `2|γ_σ| + 1 ≤ H` and
`9 + e ≤ 2H`, `Σ_{ρ ∉ D} m_ρ pairUe² ≤ e^{(|δ_σ| + δ_D)L}(L² n_σ + 16Z) + 16e^{(|δ_σ| + Θ)L} tailBound(H)`. -/
theorem tsum_compl_pairUe_le (σ : nonTrivialZeroSet) {δD H Θ L : ℝ} (hL : 0 ≤ L)
    (hΘ : ∀ ρ : nonTrivialZeroSet, |Cvs.GaussKernel.del ρ| ≤ Θ) (hR : 2 * |(σ : ℂ).im| + 1 ≤ H)
    (hH : 9 + Real.exp 1 ≤ 2 * H) :
    ∑' ρ : ↥((deepSet δD H : Set nonTrivialZeroSet)ᶜ),
        mult (ρ : nonTrivialZeroSet) * pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2
      ≤ exp ((|Cvs.GaussKernel.del σ| + δD) * L) * (L ^ 2 * nearWeight σ + 16 * invSqSum)
        + 16 * exp ((|Cvs.GaussKernel.del σ| + Θ) * L) * Cvs.Zeta.ZeroTailInverseSquare.tailBound H := by
  set δ := |Cvs.GaussKernel.del σ|
  set R := 2 * |(σ : ℂ).im| + 1
  set f : nonTrivialZeroSet → ℝ := fun ρ =>
    mult ρ * pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2 with hf
  set g₁ : nonTrivialZeroSet → ℝ := fun ρ => exp ((δ + δD) * L)
    * (L ^ 2 * (mult ρ * (if |(ρ : ℂ).im| < R then 1 else 0)) + 16 * (mult ρ * (1 / ((ρ : ℂ).im) ^ 2)))
    with hg₁
  set t : nonTrivialZeroSet → ℝ := fun ρ =>
    if H < |(ρ : ℂ).im| then (Cvs.Criterion.divisorWeight ρ : ℝ) / ((ρ : ℂ).im) ^ 2 else 0 with ht
  set g₂ : nonTrivialZeroSet → ℝ := fun ρ => 16 * exp ((δ + Θ) * L) * t ρ with hg₂
  have hE0 := exp_pos ((δ + δD) * L)
  have hE1 := exp_pos ((δ + Θ) * L)
  have ht0 : ∀ ρ, 0 ≤ t ρ := fun ρ => by
    simp only [ht]; split_ifs
    · exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    · exact le_rfl
  have hg₁0 : ∀ ρ, 0 ≤ g₁ ρ := fun ρ => by
    have := mult_nonneg ρ
    simp only [hg₁]
    refine mul_nonneg hE0.le (add_nonneg (mul_nonneg (sq_nonneg L) (mul_nonneg this ?_))
      (mul_nonneg (by norm_num) (mul_nonneg this (by positivity))))
    split_ifs <;> norm_num
  have hg₂0 : ∀ ρ, 0 ≤ g₂ ρ := fun ρ => mul_nonneg (by positivity) (ht0 ρ)
  -- the tail sum through Cvs.Zeta.ZeroTailInverseSquare
  obtain ⟨hTs, hTle⟩ := Cvs.Zeta.ZeroTailInverseSquare.tsum_le_tailBound hH
  have htsub : ∑' ρ, t ρ = ∑' ρ : {ρ : nonTrivialZeroSet // H < |(ρ : ℂ).im|},
      (Cvs.Criterion.divisorWeight (ρ : nonTrivialZeroSet) : ℝ) / (((ρ : nonTrivialZeroSet) : ℂ)).im ^ 2 := by
    rw [← tsum_subtype_eq_of_support_subset (s := {ρ : nonTrivialZeroSet | H < |(ρ : ℂ).im|})]
    · exact tsum_congr fun ρ => by simp only [ht]; exact if_pos ρ.2
    · intro ρ hρ
      by_contra h
      exact hρ (by simp only [ht]; exact if_neg h)
  have hts : Summable t := by
    refine (summable_subtype_and_compl (s := {ρ : nonTrivialZeroSet | H < |(ρ : ℂ).im|})).1 ⟨?_, ?_⟩
    · refine hTs.congr fun ρ => ?_
      simp only [ht]; exact (if_pos ρ.2).symm
    · refine (summable_zero).congr fun ρ => ?_
      simp only [ht]; exact (if_neg ρ.2).symm
  have hs₁ : Summable g₁ :=
    (((summable_mul_ite_lt R 1).mul_left (L ^ 2)).add (Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq.mul_left 16)).mul_left _
  have hs₂ : Summable g₂ := hts.mul_left _
  -- pointwise domination off the deep set
  have hpt : ∀ ρ : ↥((deepSet δD H : Set nonTrivialZeroSet)ᶜ), f ρ ≤ g₁ ρ + g₂ ρ := by
    rintro ⟨ρ, hρ⟩
    have hnot : ¬ (|(ρ : ℂ).im| ≤ H ∧ δD ≤ |Cvs.GaussKernel.del ρ|) := fun h => hρ (mem_deepSet.2 h)
    have hm := mult_nonneg ρ
    simp only [hf]
    by_cases hd : δD ≤ |Cvs.GaussKernel.del ρ|
    · have hHγ : H < |(ρ : ℂ).im| := lt_of_not_ge fun h => hnot ⟨h, hd⟩
      have hfar := pairUe_sq_far σ ρ hL (hR.trans hHγ.le)
      have hexp : exp ((δ + |Cvs.GaussKernel.del ρ|) * L) ≤ exp ((δ + Θ) * L) :=
        exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith [hΘ ρ]) hL)
      have htρ : t ρ = (Cvs.Criterion.divisorWeight ρ : ℝ) / ((ρ : ℂ).im) ^ 2 := by
        simp only [ht]; rw [if_pos hHγ]
      have h2 : mult ρ * pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2 ≤ g₂ ρ := by
        simp only [hg₂, htρ]
        have := mul_le_mul_of_nonneg_left (hfar.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) hm
        calc _ ≤ mult ρ * (16 * (1 / ((ρ : ℂ).im) ^ 2) * exp ((δ + Θ) * L)) := this
          _ = 16 * exp ((δ + Θ) * L) * ((Cvs.Criterion.divisorWeight ρ : ℝ) / ((ρ : ℂ).im) ^ 2) := by
            simp only [mult]; ring
      linarith [hg₁0 ρ]
    · have hd' : |Cvs.GaussKernel.del ρ| ≤ δD := (not_le.1 hd).le
      have hexp : exp ((δ + |Cvs.GaussKernel.del ρ|) * L) ≤ exp ((δ + δD) * L) :=
        exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hL)
      have hb : pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2
          ≤ exp ((δ + δD) * L) * (L ^ 2 * (if |(ρ : ℂ).im| < R then 1 else 0) + 16 * (1 / ((ρ : ℂ).im) ^ 2)) := by
        have hiv : (0 : ℝ) ≤ 1 / ((ρ : ℂ).im) ^ 2 := by positivity
        split_ifs with hγ
        · have := (pairUe_sq_near σ ρ hL).trans (mul_le_mul_of_nonneg_left hexp (sq_nonneg L))
          nlinarith [mul_nonneg hE0.le hiv]
        · have := (pairUe_sq_far σ ρ hL (not_lt.1 hγ)).trans
            (mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 16 * (1 / ((ρ : ℂ).im) ^ 2)))
          nlinarith
      have h1 : mult ρ * pairUe L (Cvs.ZeroCounting.zPoint σ) (Cvs.ZeroCounting.zPoint ρ) ^ 2 ≤ g₁ ρ := by
        simp only [hg₁]
        have := mul_le_mul_of_nonneg_left hb hm
        calc _ ≤ mult ρ * (exp ((δ + δD) * L)
              * (L ^ 2 * (if |(ρ : ℂ).im| < R then 1 else 0) + 16 * (1 / ((ρ : ℂ).im) ^ 2))) := this
          _ = _ := by ring
      linarith [hg₂0 ρ]
  have hfs : Summable fun ρ : ↥((deepSet δD H : Set nonTrivialZeroSet)ᶜ) => f ρ :=
    (summable_mul_pairUe_sq σ hL).subtype _
  have hgs : Summable fun ρ : ↥((deepSet δD H : Set nonTrivialZeroSet)ᶜ) => g₁ ρ + g₂ ρ :=
    (hs₁.add hs₂).subtype _
  calc ∑' ρ : ↥((deepSet δD H : Set nonTrivialZeroSet)ᶜ), f ρ
      ≤ ∑' ρ : ↥((deepSet δD H : Set nonTrivialZeroSet)ᶜ), (g₁ ρ + g₂ ρ) := Summable.tsum_le_tsum hpt hfs hgs
    _ ≤ ∑' ρ, (g₁ ρ + g₂ ρ) :=
        Summable.tsum_subtype_le (fun ρ => g₁ ρ + g₂ ρ) _ (fun ρ => add_nonneg (hg₁0 ρ) (hg₂0 ρ)) (hs₁.add hs₂)
    _ = ∑' ρ, g₁ ρ + ∑' ρ, g₂ ρ := Summable.tsum_add hs₁ hs₂
    _ ≤ _ := by
        have e1 : ∑' ρ, g₁ ρ = exp ((δ + δD) * L) * (L ^ 2 * nearWeight σ + 16 * invSqSum) := by
          simp only [hg₁]
          rw [tsum_mul_left, Summable.tsum_add ((summable_mul_ite_lt R 1).mul_left _)
            (Cvs.StepA.RestEnvelopeSmall.summable_divisorWeight_div_sq.mul_left 16), tsum_mul_left, tsum_mul_left]
          rfl
        have e2 : ∑' ρ, g₂ ρ = 16 * exp ((δ + Θ) * L) * ∑' ρ, t ρ := by simp only [hg₂]; rw [tsum_mul_left]
        rw [e1, e2, htsub]
        have := mul_le_mul_of_nonneg_left hTle (by positivity : (0 : ℝ) ≤ 16 * exp ((δ + Θ) * L))
        linarith

/-! ### The low shallow part -/

/-- **`‖U_ρ‖² ≤ L e^{|δ_ρ|L}`**, `L = log x`. -/
theorem norm_sq_ueVec_le {x : ℕ} (hx0 : (0 : ℝ) < x) (ρ : nonTrivialZeroSet) :
    ‖ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)‖ ^ 2 ≤ Real.log x * exp (|Cvs.GaussKernel.del ρ| * Real.log x) := by
  have hL := Real.log_natCast_nonneg x
  rw [(real_inner_self_eq_norm_sq (ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))).symm, Cvs.StepA.Edge.CorrectedPairingUSums.inner_ueVec_ueVec]
  have h := ueUe_sq_near ρ ρ hL
  have e : exp ((|Cvs.GaussKernel.del ρ| + |Cvs.GaussKernel.del ρ|) * Real.log x)
      = exp (|Cvs.GaussKernel.del ρ| * Real.log x) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← mul_pow] at h
  exact (abs_le_of_sq_le_sq' h (by positivity)).2

/-- `Σ m/(1 + γ²)`. -/
def invOneSqSum : ℝ := ∑' ρ : nonTrivialZeroSet, mult ρ * (1 / (1 + ((ρ : ℂ).im) ^ 2))

/-- **The weight below a height**: `Σ_{|γ| ≤ H'} m_ρ c ≤ c(1 + H'²)Σ m/(1 + γ²)` for `c ≥ 0`, and the family is
summable. -/
theorem tsum_mul_ite_le_le (H' : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (Summable fun ρ : nonTrivialZeroSet => if |(ρ : ℂ).im| ≤ H' then mult ρ * c else 0)
      ∧ ∑' ρ : nonTrivialZeroSet, (if |(ρ : ℂ).im| ≤ H' then mult ρ * c else 0)
          ≤ c * (1 + H' ^ 2) * invOneSqSum := by
  have hs := (Cvs.Zeta.QuadraticWeightSummable.summable_divisorWeight_sq.mul_left (c * (1 + H' ^ 2)))
  have hpt : ∀ ρ : nonTrivialZeroSet, (if |(ρ : ℂ).im| ≤ H' then mult ρ * c else 0)
      ≤ c * (1 + H' ^ 2) * ((Cvs.Criterion.divisorWeight ρ : ℝ) * (1 / (1 + ((ρ : ℂ).im) ^ 2))) := by
    intro ρ
    have hm := mult_nonneg ρ
    have hpos : (0 : ℝ) < 1 + ((ρ : ℂ).im) ^ 2 := by positivity
    split_ifs with h
    · have hsq : ((ρ : ℂ).im) ^ 2 ≤ H' ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have : 1 ≤ (1 + H' ^ 2) * (1 / (1 + ((ρ : ℂ).im) ^ 2)) := by
        rw [mul_one_div, le_div_iff₀ hpos]; linarith
      simp only [mult] at hm ⊢
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hm hc)]
    · exact mul_nonneg (mul_nonneg hc (by positivity)) (mul_nonneg hm (by positivity))
  have hs' : Summable fun ρ : nonTrivialZeroSet => if |(ρ : ℂ).im| ≤ H' then mult ρ * c else 0 := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) hpt hs
    split_ifs
    · exact mul_nonneg (mult_nonneg ρ) hc
    · exact le_rfl
  refine ⟨hs', (Summable.tsum_le_tsum hpt hs' hs).trans (le_of_eq ?_)⟩
  rw [tsum_mul_left]; rfl

end Cvs.StepA.Edge.DeepSetZeroSums

end
