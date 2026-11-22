import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Cvs.Zeta.RiemannXi

/-
The bridge from `ξ` to `ζ`.

`Cvs.Zeta.logDeriv_riemannXi_eq` expresses `ξ'/ξ` as a sum over the zeros.  The
explicit formula needs the *other* side of the same quantity: `ξ'/ξ` in terms of
`ζ'/ζ` and an archimedean term.  The link is the classical factorisation

    `ξ(s) = ½·s·(s−1)·Λ(s)`,     `Λ(s) = Γ_ℝ(s)·ζ(s)`,   `Γ_ℝ(s) = π^{−s/2}Γ(s/2)`.

`Cvs.Zeta.riemannXi` is defined through the entire `Λ₀` (so that entirety is
definitional), and Mathlib's `completedRiemannZeta_eq` relates `Λ₀` to `Λ` by
`Λ = Λ₀ − 1/s − 1/(1−s)`.  Those pole terms cancel the `+ ½` in the definition
exactly — which is why `ξ` is entire while `Λ` is not.

No `sorry`; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

namespace Cvs.Zeta

open Complex

/-- **`ξ(s) = ½·s·(s−1)·Λ(s)`** — the classical form. -/
theorem riemannXi_eq_completed {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp
  ring

/-- **`ξ(s) = ½·s·(s−1)·Γ_ℝ(s)·ζ(s)`.** `Γ_ℝ(s) = π^{−s/2}Γ(s/2)` is the archimedean factor; this
is where the `log π` and the digamma of the explicit formula come from. -/
theorem riemannXi_eq_gammaR_mul_zeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) :
    riemannXi s = s * (s - 1) * (Gammaℝ s * riemannZeta s) / 2 := by
  rw [riemannXi_eq_completed h0 h1]
  congr 2
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp

/-- The same on the right half-plane, where `Γ_ℝ` cannot vanish. -/
theorem riemannXi_eq_gammaR_mul_zeta_of_re_pos {s : ℂ} (h1 : s ≠ 1) (hs : 0 < s.re) :
    riemannXi s = s * (s - 1) * (Gammaℝ s * riemannZeta s) / 2 :=
  riemannXi_eq_gammaR_mul_zeta
    (fun hcon => by rw [hcon] at hs; simp at hs) h1 (Gammaℝ_ne_zero_of_re_pos hs)

/-!
### The log-derivative form

What the explicit formula consumes.
-/

/-- `Γ_ℝ` is differentiable wherever it is nonzero. -/
theorem differentiableAt_gammaR {s : ℂ} (hG : Gammaℝ s ≠ 0) :
    DifferentiableAt ℂ Gammaℝ s := by
  have h : DifferentiableAt ℂ (fun w : ℂ => ((Gammaℝ w)⁻¹)⁻¹) s :=
    (differentiable_Gammaℝ_inv s).fun_inv (by simpa using hG)
  simpa [inv_inv] using h

/-- **`ξ'/ξ = 1/s + 1/(s−1) + Γ_ℝ'/Γ_ℝ + ζ'/ζ`.** The archimedean term `Γ_ℝ'/Γ_ℝ` is `−½log π +
½ψ(s/2)`; it is exactly the archimedean block of the Guinand–Weil formula. -/
theorem logDeriv_riemannXi_eq_zeta {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s
      = 1 / s + 1 / (s - 1) + logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  have h0 : s ≠ 0 := fun hcon => by rw [hcon] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  -- the factorisation, on an open neighbourhood
  have hUopen : IsOpen ({w : ℂ | 0 < w.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hev : riemannXi =ᶠ[nhds s]
      fun w => w * (w - 1) * (Gammaℝ w * riemannZeta w) / 2 := by
    filter_upwards [hUopen.mem_nhds ⟨hs, h1⟩] with w hw
    exact riemannXi_eq_gammaR_mul_zeta_of_re_pos hw.2 hw.1
  rw [(logDeriv_congr_nhds hev).eq_of_nhds]
  -- differentiability and non-vanishing of each factor at `s`
  have hd1 : DifferentiableAt ℂ (fun w : ℂ => w) s := differentiableAt_id
  have hd2 : DifferentiableAt ℂ (fun w : ℂ => w - 1) s := differentiableAt_id.sub_const 1
  have hd3 : DifferentiableAt ℂ Gammaℝ s := differentiableAt_gammaR hG
  have hd4 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta h1
  have e1 : logDeriv (fun w : ℂ => w) s = 1 / s := by
    rw [logDeriv_apply, deriv_id'']
  have e2 : logDeriv (fun w : ℂ => w - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  -- the constant factor drops out of a logarithmic derivative
  have hdiv : logDeriv (fun w : ℂ => w * (w - 1) * (Gammaℝ w * riemannZeta w) / 2) s
      = logDeriv (fun w : ℂ => w * (w - 1) * (Gammaℝ w * riemannZeta w)) s := by
    have hre : (fun w : ℂ => w * (w - 1) * (Gammaℝ w * riemannZeta w) / 2)
        = fun w : ℂ => (w * (w - 1) * (Gammaℝ w * riemannZeta w)) * (2 : ℂ)⁻¹ := by
      funext w; ring
    rw [hre, logDeriv_mul_const s ((2 : ℂ)⁻¹) (by norm_num)]
  have m1 := logDeriv_mul (f := fun w : ℂ => w * (w - 1))
      (g := fun w : ℂ => Gammaℝ w * riemannZeta w) s
      (mul_ne_zero h0 hsub) (mul_ne_zero hG hz) (hd1.fun_mul hd2) (hd3.fun_mul hd4)
  have m2 := logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) s h0 hsub hd1 hd2
  have m3 := logDeriv_mul (f := Gammaℝ) (g := riemannZeta) s hG hz hd3 hd4
  simp only [Pi.mul_def] at m1 m2 m3
  rw [hdiv, m1, m2, m3, e1, e2]
  ring

end Cvs.Zeta
