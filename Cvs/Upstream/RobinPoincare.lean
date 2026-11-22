import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Upstream.RiccatiIntegrationByParts
import Cvs.Upstream.RiccatiTangentWitness

/-!
# Robin–Poincaré, assembled

    `φ ℓ = 0`  and the witness pole-free on `[0, ℓ]`   ⟹   `t²∫φ² ≤ ∫φ'² + b·φ 0²`

the witness contributing `w' = t² + w²` and `w 0 = −b`, and nothing else entering.
-/

noncomputable section

open MeasureTheory

namespace Cvs.Upstream.RobinPoincare

/-- **The Robin–Poincaré inequality.**  `w` is `Cvs.Upstream.RiccatiTangentWitness`'s tangent witness at `c = arctan(b/t)/t`;
the hypotheses are that it is regular on the interval, that `φ` vanishes at `ℓ`, and the
integrability the expansion of `∫(φ' + wφ)²` needs. -/
theorem robin_poincare {t b ℓ : ℝ} {φ dφ : ℝ → ℝ} (ht : 0 < t)
    (hφ : ∀ x ∈ Set.uIcc (0:ℝ) ℓ, HasDerivAt φ (dφ x) x)
    (hw : ∀ x ∈ Set.uIcc (0:ℝ) ℓ,
      Real.cos (t * (x - Real.arctan (b / t) / t)) ≠ 0)
    (hzero : φ ℓ = 0)
    (hiA : IntervalIntegrable (fun x => φ x ^ 2) volume 0 ℓ)
    (hiW2 : IntervalIntegrable
      (fun x => Cvs.Upstream.RiccatiTangentWitness.wit t (Real.arctan (b / t) / t) x ^ 2 * φ x ^ 2)
      volume 0 ℓ)
    (hi1 : IntervalIntegrable
      (fun x => (t ^ 2 + Cvs.Upstream.RiccatiTangentWitness.wit t (Real.arctan (b / t) / t) x ^ 2)
        * φ x ^ 2) volume 0 ℓ)
    (hi2 : IntervalIntegrable
      (fun x => Cvs.Upstream.RiccatiTangentWitness.wit t (Real.arctan (b / t) / t) x * (φ x * dφ x))
      volume 0 ℓ)
    (hsq : 0 ≤ (∫ x in (0:ℝ)..ℓ, dφ x ^ 2)
      + 2 * (∫ x in (0:ℝ)..ℓ,
          Cvs.Upstream.RiccatiTangentWitness.wit t (Real.arctan (b / t) / t) x * (φ x * dφ x))
      + ∫ x in (0:ℝ)..ℓ,
          Cvs.Upstream.RiccatiTangentWitness.wit t (Real.arctan (b / t) / t) x ^ 2 * φ x ^ 2) :
    t ^ 2 * (∫ x in (0:ℝ)..ℓ, φ x ^ 2)
      ≤ (∫ x in (0:ℝ)..ℓ, dφ x ^ 2) + b * φ 0 ^ 2 := by
  set c := Real.arctan (b / t) / t with hc
  set w := Cvs.Upstream.RiccatiTangentWitness.wit t c with hwdef
  -- the witness solves the Riccati equation on the interval
  have hder : ∀ x ∈ Set.uIcc (0:ℝ) ℓ, HasDerivAt w (t ^ 2 + w x ^ 2) x :=
    fun x hx => Cvs.Upstream.RiccatiTangentWitness.hasDerivAt_wit (hw x hx)
  -- integration by parts
  have hibp := Cvs.Upstream.RiccatiIntegrationByParts.ibp_identity hder hφ hi1 hi2
  -- the left-hand integral splits
  have hsplit : (∫ x in (0:ℝ)..ℓ, (t ^ 2 + w x ^ 2) * φ x ^ 2)
      = t ^ 2 * (∫ x in (0:ℝ)..ℓ, φ x ^ 2)
        + ∫ x in (0:ℝ)..ℓ, w x ^ 2 * φ x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (hiA.const_mul _) hiW2]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  have hw0 : w 0 = -b := Cvs.Upstream.RiccatiTangentWitness.wit_zero ht
  rw [hsplit, hzero, hw0] at hibp
  refine Cvs.Upstream.RiccatiIntegrationByParts.poincare_of_parts (t := t) (b := b) (wl := w ℓ)
    (gl2 := 0) ?_ rfl hsq
  simpa using hibp

end Cvs.Upstream.RobinPoincare
