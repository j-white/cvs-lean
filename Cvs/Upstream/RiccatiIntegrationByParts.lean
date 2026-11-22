import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The integration by parts behind the Riccati comparison

    ∫ w' g² + 2 ∫ w g g'  =  [w g²]₀^ℓ

which is the fundamental theorem applied to `x ↦ w x · g x ²`.
-/

noncomputable section

namespace Cvs.Upstream.RiccatiIntegrationByParts

/-- **Integration by parts, in the form the Riccati comparison consumes.**  With `w' = t² + w²`
and `g ℓ = 0` this is what turns `0 ≤ ∫(g' + w g)²` into the Poincaré bound. -/
theorem ibp_identity {ℓ : ℝ} {w g dw dg : ℝ → ℝ}
    (hw : ∀ x ∈ Set.uIcc (0:ℝ) ℓ, HasDerivAt w (dw x) x)
    (hg : ∀ x ∈ Set.uIcc (0:ℝ) ℓ, HasDerivAt g (dg x) x)
    (hi1 : IntervalIntegrable (fun x => dw x * g x ^ 2) MeasureTheory.volume 0 ℓ)
    (hi2 : IntervalIntegrable (fun x => w x * (g x * dg x)) MeasureTheory.volume 0 ℓ) :
    (∫ x in (0:ℝ)..ℓ, dw x * g x ^ 2) + 2 * ∫ x in (0:ℝ)..ℓ, w x * (g x * dg x)
      = w ℓ * g ℓ ^ 2 - w 0 * g 0 ^ 2 := by
  have hder : ∀ x ∈ Set.uIcc (0:ℝ) ℓ,
      HasDerivAt (fun y => w y * g y ^ 2)
        (dw x * g x ^ 2 + 2 * (w x * (g x * dg x))) x := by
    intro x hx
    have h := (hw x hx).mul ((hg x hx).mul (hg x hx))
    have heqf : (fun y => w y * g y ^ 2) = fun y => w y * (g y * g y) := by
      funext y; ring
    have heqv : dw x * g x ^ 2 + 2 * (w x * (g x * dg x))
        = dw x * (g x * g x) + w x * (dg x * g x + g x * dg x) := by ring
    rw [heqf, heqv]
    exact h
  have hint : IntervalIntegrable
      (fun x => dw x * g x ^ 2 + 2 * (w x * (g x * dg x))) MeasureTheory.volume 0 ℓ :=
    hi1.add (hi2.const_mul 2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  rw [intervalIntegral.integral_add hi1 (hi2.const_mul 2),
    intervalIntegral.integral_const_mul] at hFTC
  exact hFTC

/-- **The comparison, assembled.**  `0 ≤ ∫(g' + w g)²` expanded, with the parts by name:
`B = ∫g'²`, `CR = ∫ w g g'`, `W2 = ∫ w² g²`, and `∫ w' g² = t²A + W2` from the Riccati
equation.  With `g ℓ = 0` and `w 0 = −b` this is the Robin–Poincaré bound. -/
theorem poincare_of_parts {t b A B W2 CR gl2 wl g0sq : ℝ}
    (hibp : (t ^ 2 * A + W2) + 2 * CR = wl * gl2 - (-b) * g0sq)
    (hgl : gl2 = 0)
    (hsq : 0 ≤ B + 2 * CR + W2) :
    t ^ 2 * A ≤ B + b * g0sq := by
  subst hgl
  simp only [mul_zero, zero_sub] at hibp
  linarith

end Cvs.Upstream.RiccatiIntegrationByParts
