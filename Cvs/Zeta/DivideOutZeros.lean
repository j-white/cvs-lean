import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Cvs.Zeta.Hadamard

/-!
# Dividing out a divisor that `f` dominates

The last construction route B needs: given `f` and a product `φ` of some of its zeros, produce
`g` with `f = g·φ`, analytic everywhere and zero-free exactly where `f` and `φ` have the same
order.
-/

open Complex Set Metric Finset

namespace Cvs.Zeta

/-- **Dividing out a divisor that `f` dominates.**
`Hadamard.analyticOnNhd_and_ne_zero_of_divisor_eq` needs the divisors to be *equal*, which
gives a quotient that is zero-free everywhere. -/
theorem analyticOnNhd_toMeromorphicNFOn_of_order_le {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    (hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤)
    (hle : ∀ z : ℂ, meromorphicOrderAt φ z ≤ meromorphicOrderAt f z) :
    AnalyticOnNhd ℂ (toMeromorphicNFOn (φ⁻¹ • f) Set.univ) Set.univ := by
  set g : ℂ → ℂ := toMeromorphicNFOn (φ⁻¹ • f) Set.univ with hgdef
  have hgNF : MeromorphicNFOn g Set.univ := meromorphicNFOn_toMeromorphicNFOn _ _
  rw [← hgNF.divisor_nonneg_iff_analyticOnNhd]
  intro z
  have hord : meromorphicOrderAt g z = -meromorphicOrderAt φ z + meromorphicOrderAt f z :=
    meromorphicOrderAt_toMeromorphicNFOn_inv_smul hf hφ z
  have hne : meromorphicOrderAt g z ≠ ⊤ :=
    meromorphicOrderAt_toMeromorphicNFOn_inv_smul_ne_top hf hφ hfinf hfinφ z
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (hfinf z)
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp (hfinφ z)
  have hab : b ≤ a := by
    have h := hle z
    rw [← ha, ← hb] at h
    exact_mod_cast h
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
  rw [MeromorphicOn.divisor_apply hgNF.meromorphicOn (Set.mem_univ z), hord, ← ha, ← hb]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
    WithTop.untop₀_coe]
  omega

/-- The factorisation holds pointwise, including at the zeros of `φ`. -/
theorem eq_mul_toMeromorphicNFOn_of_order_le {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    (hle : ∀ z : ℂ, meromorphicOrderAt φ z ≤ meromorphicOrderAt f z) (z : ℂ) :
    f z = toMeromorphicNFOn (φ⁻¹ • f) Set.univ z * φ z := by
  have hfa : AnalyticAt ℂ f z := hf z (Set.mem_univ z)
  have hφa : AnalyticAt ℂ φ z := hφ z (Set.mem_univ z)
  by_cases hz : φ z = 0
  · -- `φ` vanishes, so its order is positive, so `f`'s is too and `f z = 0`
    have hφ0 : meromorphicOrderAt φ z ≠ 0 := fun hc =>
      hφa.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hc hz
    have hfz : f z = 0 := by
      by_contra hc
      have hf0 : meromorphicOrderAt f z = 0 :=
        hfa.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hc
      have hnn : 0 ≤ meromorphicOrderAt φ z :=
        hφa.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hφa
      have hcmp := hle z
      rw [hf0] at hcmp
      exact hφ0 (le_antisymm hcmp hnn)
    rw [hz, hfz, mul_zero]
  · rw [toMeromorphicNFOn_inv_smul_apply hf hφ hz]
    field_simp

/-- The quotient is nonzero exactly where the two orders agree. -/
theorem toMeromorphicNFOn_ne_zero_of_order_eq {f φ : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hfinf : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    (hfinφ : ∀ z : ℂ, meromorphicOrderAt φ z ≠ ⊤)
    {z : ℂ} (heq : meromorphicOrderAt φ z = meromorphicOrderAt f z) :
    toMeromorphicNFOn (φ⁻¹ • f) Set.univ z ≠ 0 := by
  set g : ℂ → ℂ := toMeromorphicNFOn (φ⁻¹ • f) Set.univ with hgdef
  have hgNF : MeromorphicNFOn g Set.univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hord : meromorphicOrderAt g z = -meromorphicOrderAt φ z + meromorphicOrderAt f z :=
    meromorphicOrderAt_toMeromorphicNFOn_inv_smul hf hφ z
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (hfinf z)
  have hz0 : meromorphicOrderAt g z = 0 := by
    rw [hord, heq, ← ha]
    simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    norm_num
  exact (hgNF (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff.mp hz0

end Cvs.Zeta
