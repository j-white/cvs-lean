import Mathlib
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SingletonRegularisationColumn
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.Prolate.Envelope.RungCentreBound
import Cvs.Prolate.Envelope.RungExteriorLaw
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.RungExactOrthogonality
import Cvs.Prolate.RungSpanBernsteinNikolskii
import Cvs.Route.Visibility.AliasRemainderCentreBound
import Cvs.Route.Visibility.AliasRemainderSplit
import Cvs.Route.Visibility.LayerFloorDeepRemainderB
import Cvs.WeilForm.PoleTermCauchySchwarz

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The centre term of a spine class: `G_b(0)² ≤ 2E(b)/(π²λ_t(1 + √λ_t)²)`, which is `Cvs.Route.Visibility.AliasRemainderCentreBound.ZBound`

At `c = 2πx`, `∫_{−1}^{1} G_b = 0` and `∫h_n = μ_n h_n(0)` give `G_b(0) = Σ_n b̃_n(1 − √λ_n)h_n(0)`.  The test
function `φ = Σ_n b̃_n h_n/(μ_n(1 + √λ_n))` has exterior pairing `∫_{|ξ|>1} ψ_φψ_1 = (2π/c)G_b(0)` and, the
exterior parts of the rungs being orthogonal, exterior energy `Σ_n (1 − λ_n)b̃_n²/(λ_n(1 + √λ_n)²)`.
Cauchy–Schwarz against `∫_{|ξ|>1}ψ_1² ≤ 8/c²` and `λ_n ≥ λ_t` give the bound.
-/

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Cvs.Route.Visibility.SpineCentreTermBound
open Cvs.ZeroCounting

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.EvenRungsByIndex (rung muR lamR lev rung_spec)
open Cvs.Approximant.DeepIndexSpineSpan (spineG)
open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (coefH energyE lam lamTop)
open Cvs.Prolate.Envelope.RungCentreBound (extSet)

/-! ### Even integrands on the exterior -/

/-- An even integrable `f` has `∫_{|ξ|>1} f = 2∫_{(1,∞)} f`. -/
theorem setIntegral_extSet_of_even {f : ℝ → ℝ} (hf : ∀ ξ, f (-ξ) = f ξ) (hi : Integrable f) :
    ∫ ξ in extSet, f ξ = 2 * ∫ ξ in Ioi 1, f ξ := by
  have hset : extSet = Iio (-1) ∪ Ioi 1 := by
    ext ξ; simp only [extSet, mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
  have hdisj : Disjoint (Iio (-1 : ℝ)) (Ioi 1) :=
    Set.disjoint_left.2 fun ξ h1 h2 => by simp only [mem_Iio, mem_Ioi] at h1 h2; linarith
  rw [hset, setIntegral_union hdisj measurableSet_Ioi hi.integrableOn hi.integrableOn,
    ← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
  simp only [hf]
  ring

/-! ### The spine profile at the centre -/

section spine

variable {x : ℕ}

/-- The rungs of `Fin x` are continuous on `[−1, 1]`. -/
theorem continuousOn_rung_uIcc (x : ℕ) (n : Fin x) :
    ContinuousOn (rung (2 * π * x) (2 * (n : ℕ))) (uIcc (-1) 1) := by
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact Cvs.Prolate.Gram.ProlateCellGramHalfUnit.continuousOn_rung _ _

/-- `Σ_n b̃_n μ_n h_n(0) = 0`, from `∫_{−1}^{1} G_b = 0`. -/
theorem sum_coefH_mu_rung_zero (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∑ n : Fin x, coefH x b n * (muR (2 * π * x) (2 * (n : ℕ)) * rung (2 * π * x) (2 * (n : ℕ)) 0) = 0 := by
  have hx1 : 1 ≤ x := by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega
  have h0 := Cvs.Approximant.DeepIndexSpineSpan.integral_spineG (by linarith : (0 : ℝ) < 2 * π * x) b
  rw [show spineG (2 * π * x) b = fun s => ∑ n : Fin x, coefH x b n * rung (2 * π * x) (2 * (n : ℕ)) s from
    funext (Cvs.Route.Visibility.AliasRemainderSplit.spineG_eq_sum hx1 b), intervalIntegral.integral_finsetSum fun n _ =>
      (Cvs.Approximant.DeepIndexSpineSpan.intervalIntegrable_rung _ _).const_mul _] at h0
  refine Eq.trans (Finset.sum_congr rfl fun n _ => ?_) h0
  rw [intervalIntegral.integral_const_mul, Cvs.Prolate.Envelope.RungCentreBound.integral_rung_eq (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)]

/-- `√λ_n = μ_n√(c/2π)` on the rungs `n < x`. -/
theorem sqrt_lam_eq (hx : 80 ≤ 2 * π * x) (n : Fin x) :
    √(lam x n) = muR (2 * π * x) (2 * (n : ℕ)) * √(2 * π * x / (2 * π)) := by
  have hμ := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even (by linarith) (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n) (⟨n, by ring⟩ : Even (2 * (n : ℕ)))
  rw [lam, lamR, Real.sqrt_sq (by positivity)]

/-- The test coefficients `a_n = b̃_n/(μ_n(1 + √λ_n))`. -/
def testCoef (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (n : Fin x) : ℝ :=
  coefH x b n / (muR (2 * π * x) (2 * (n : ℕ)) * (1 + √(lam x n)))

/-- The test function `φ = Σ_n a_n h_n`. -/
def testFun (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.univ, testCoef x b n * rung (2 * π * x) (2 * (n : ℕ)) s

/-- The test function is continuous on `[−1, 1]`. -/
theorem continuousOn_testFun (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ContinuousOn (testFun x b) (uIcc (-1) 1) :=
  continuousOn_finsetSum _ fun n _ => (continuousOn_rung_uIcc x n).const_smul (testCoef x b n)

/-- `ψ_φ = Σ_n a_n ψ_{h_n}`. -/
theorem psi_testFun (x : ℕ) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) (ξ : ℝ) :
    psi (2 * π * x) (testFun x b) ξ
      = ∑ n : Fin x, testCoef x b n * psi (2 * π * x) (rung (2 * π * x) (2 * (n : ℕ))) ξ :=
  Cvs.L2a.FullTailConvergence.psi_sum _ _ _ (fun _ _ => Cvs.Approximant.DeepIndexSpineSpan.intervalIntegrable_rung _ _) _ _

/-- **The exterior pairing of the test function**: `∫_{|ξ|>1} ψ_φψ_1 = (2π/c)G_b(0)`. -/
theorem integral_ext_psi_testFun_mul_psi_one (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∫ ξ in extSet, psi (2 * π * x) (testFun x b) ξ * psi (2 * π * x) (fun _ => 1) ξ
      = 2 * π / (2 * π * x) * spineG (2 * π * x) b 0 := by
  have hx1 : 1 ≤ x := by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  simp only [psi_testFun, Finset.sum_mul]
  set c := 2 * π * (x : ℝ)
  rw [integral_finsetSum _ fun n _ => ((Cvs.Prolate.Envelope.RungCentreBound.integrable_psi_mul hc (continuousOn_rung_uIcc x n)
    continuousOn_const).const_mul (testCoef x b n)).integrableOn.congr_fun (fun ξ _ => by ring) measurableSet_Icc.compl]
  have e : ∀ n : Fin x, ∫ ξ in extSet, testCoef x b n * psi c (rung c (2 * (n : ℕ))) ξ * psi c (fun _ => 1) ξ
      = 2 * π / c * (coefH x b n * rung c (2 * (n : ℕ)) 0
        - √(c / (2 * π)) * (coefH x b n * (muR c (2 * (n : ℕ)) * rung c (2 * (n : ℕ)) 0))) := fun n => by
    have hl := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n
    have hμ := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc hl (⟨n, by ring⟩ : Even (2 * (n : ℕ)))
    have hs : √(lam x n) = muR c (2 * (n : ℕ)) * √(c / (2 * π)) := sqrt_lam_eq hx n
    have ht0 : 0 < √(c / (2 * π)) := Real.sqrt_pos.2 (by positivity)
    have h2 : 2 * π / c = 1 / √(c / (2 * π)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]; field_simp
    simp only [mul_assoc]
    rw [integral_const_mul, ← mul_assoc, Cvs.Prolate.Envelope.RungCentreBound.integral_ext_psi_mul_psi_one hc hl, testCoef, hs, h2]
    generalize √(c / (2 * π)) = t at ht0 ⊢
    generalize muR c (2 * (n : ℕ)) = m at hμ ⊢
    have h1 : 0 < 1 + m * t := by positivity
    field_simp
    ring
  simp only [e]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_coefH_mu_rung_zero hx b, mul_zero, sub_zero,
    Cvs.Route.Visibility.AliasRemainderSplit.spineG_eq_sum hx1 b 0]

/-- **The exterior energy of the test function**: `∫_{|ξ|>1} ψ_φ² = Σ_n (1 − λ_n)b̃_n²/(λ_n(1 + √λ_n)²)`. -/
theorem integral_ext_psi_testFun_sq (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    ∫ ξ in extSet, psi (2 * π * x) (testFun x b) ξ ^ 2
      = ∑ n : Fin x, (1 - lam x n) * coefH x b n ^ 2 / (lam x n * (1 + √(lam x n)) ^ 2) := by
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  rw [setIntegral_extSet_of_even (fun ξ => by rw [Cvs.Prolate.RungSpanBernsteinNikolskii.psi_neg]) (Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc
    (continuousOn_testFun x b))]
  simp only [psi_testFun]
  set c := 2 * π * (x : ℝ)
  have hspec := fun n : Fin x => rung_spec (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n)
  have hinj : Function.Injective fun n : Fin x => lev c (2 * (n : ℕ)) := (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lev_strictMono hx).injective
  rw [Cvs.Prolate.RungExactOrthogonality.integral_span_sq (testCoef x b) (fun n => (hspec n).1) (fun n => (hspec n).2.1)
    (fun n => (hspec n).2.2.1) (fun n => (hspec n).2.2.2.1) hc hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hl := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.exists_level hx n
  have hμ := Cvs.Prolate.EvenRungsByIndex.muR_pos_of_even hc hl (⟨n, by ring⟩ : Even (2 * (n : ℕ)))
  have hlam : lam x n = muR c (2 * (n : ℕ)) ^ 2 * (c / (2 * π)) := Cvs.Prolate.Envelope.RungExteriorLaw.lamR_eq hc
  rw [Cvs.Prolate.Envelope.RungExteriorLaw.mass_eq hc hl, testCoef]
  have hd : (0 : ℝ) < 1 + √(lam x n) := by positivity
  change 2 * ((coefH x b n / (muR c (2 * (n : ℕ)) * (1 + √(lam x n)))) ^ 2 * (π / c * (1 - lam x n))) = _
  rw [hlam]
  field_simp

/-- **The centre bound**: `G_b(0)² ≤ 2E(b)/(π²λ_t(1 + √λ_t)²)` at `c = 2πx ≥ 80`. -/
theorem spineG_zero_sq_le (hx : 80 ≤ 2 * π * x) (b : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    spineG (2 * π * x) b 0 ^ 2 ≤ 2 / (π ^ 2 * (lamTop x * (1 + √(lamTop x)) ^ 2)) * energyE x b := by
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  have hx2 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx
  set c := 2 * π * (x : ℝ)
  set K := lamTop x * (1 + √(lamTop x)) ^ 2
  have ht := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
  have hK : 0 < K := by positivity
  -- the exterior energy is at most `E/K`
  have hen : ∫ ξ in extSet, psi c (testFun x b) ξ ^ 2 ≤ energyE x b / K := by
    rw [integral_ext_psi_testFun_sq hx, energyE, Finset.sum_div]
    refine Finset.sum_le_sum fun n _ => ?_
    have hn := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_anti hx (by omega : x - 1 < x) (by omega : (n : ℕ) ≤ x - 1)
    have h1 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_le_one hx n.2
    have hKn : K ≤ lam x n * (1 + √(lam x n)) ^ 2 := by
      have := Real.sqrt_le_sqrt hn
      simp only [K, lamTop]
      exact mul_le_mul hn (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by positivity)
        (Cvs.Prolate.Gram.ProlateCellGramHalfUnit.lam_nonneg x n)
    exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (sq_nonneg _)) hK hKn
  -- Cauchy–Schwarz on the exterior
  have hφ := continuousOn_testFun x b
  set f := extSet.indicator (psi c (testFun x b))
  set g := extSet.indicator (psi c (fun _ => 1))
  have hm : MeasurableSet extSet := measurableSet_Icc.compl
  have hf2 : (fun ξ => f ξ ^ 2) = extSet.indicator fun ξ => psi c (testFun x b) ξ ^ 2 := by
    funext ξ; by_cases hξ : ξ ∈ extSet <;> simp [f, hξ]
  have hg2 : (fun ξ => g ξ ^ 2) = extSet.indicator fun ξ => psi c (fun _ => 1) ξ ^ 2 := by
    funext ξ; by_cases hξ : ξ ∈ extSet <;> simp [g, hξ]
  have hfg : (fun ξ => f ξ * g ξ) = extSet.indicator fun ξ => psi c (testFun x b) ξ * psi c (fun _ => 1) ξ := by
    funext ξ; by_cases hξ : ξ ∈ extSet <;> simp [f, g, hξ]
  have hcs := Cvs.WeilForm.PoleTermCauchySchwarz.sq_integral_mul_le (f := f) (h := g)
    (by rw [hf2]; exact (Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc hφ).indicator hm)
    (by rw [hg2]; exact (Cvs.Prolate.RungSpanBernsteinNikolskii.integrable_psi_sq hc (continuousOn_const (c := (1 : ℝ)))).indicator hm)
    (by rw [hfg]; exact (Cvs.Prolate.Envelope.RungCentreBound.integrable_psi_mul hc hφ (continuousOn_const (c := (1 : ℝ)))).indicator hm)
  rw [hf2, hg2, hfg, integral_indicator hm, integral_indicator hm, integral_indicator hm,
    integral_ext_psi_testFun_mul_psi_one hx] at hcs
  have hP := Cvs.Prolate.Envelope.RungCentreBound.integral_ext_psi_one_sq_le hc
  have hP0 : 0 ≤ ∫ ξ in extSet, psi c (fun _ => 1) ξ ^ 2 := setIntegral_nonneg hm fun _ _ => sq_nonneg _
  have hE0 := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.energyE_nonneg hx b
  have key : (2 * π / c * spineG c b 0) ^ 2 ≤ energyE x b / K * (8 / c ^ 2) :=
    hcs.trans (mul_le_mul hen hP hP0 (by positivity))
  have e1 : (2 * π / c * spineG c b 0) ^ 2 = (4 * π ^ 2 / c ^ 2) * spineG c b 0 ^ 2 := by ring
  have e2 : energyE x b / K * (8 / c ^ 2) = (4 * π ^ 2 / c ^ 2) * (2 / (π ^ 2 * K) * energyE x b) := by
    field_simp; ring
  rw [e1, e2] at key
  exact le_of_mul_le_mul_left key (by positivity)

end spine

/-! ### P5 -/

/-- **P5**: `Cvs.Route.Visibility.AliasRemainderCentreBound.ZBound`. -/
theorem zBound : Cvs.Route.Visibility.AliasRemainderCentreBound.ZBound := by
  filter_upwards [Cvs.Route.Visibility.LayerFloorDeepRemainderB.eventually_scale] with x hx b
  have hc : (0 : ℝ) < 2 * π * x := by linarith
  have hx0 : (0 : ℝ) < x := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have ht := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
  have hE := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.energyE_nonneg hx b
  have h := spineG_zero_sq_le hx b
  have h1 : 1 ≤ (1 + √(lamTop x)) ^ 2 := by nlinarith [Real.sqrt_nonneg (lamTop x)]
  have hle : 2 / (π ^ 2 * (lamTop x * (1 + √(lamTop x)) ^ 2)) * energyE x b
      ≤ 2 / (π ^ 2 * lamTop x) * energyE x b := by
    gcongr
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  calc spineG (2 * π * x) b 0 ^ 2 ≤ 2 / (π ^ 2 * lamTop x) * energyE x b := h.trans hle
    _ = energyE x b / (π * (2 * π * x) * lamTop x) * (4 * x) := by field_simp; ring

end Cvs.Route.Visibility.SpineCentreTermBound

end
