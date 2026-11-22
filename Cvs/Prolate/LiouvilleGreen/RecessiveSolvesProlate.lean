import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Cvs.Prolate.LiouvilleGreen.ComplexSymbols
import Cvs.Prolate.LiouvilleGreen.HalfStripPhase
import Cvs.Prolate.LiouvilleGreen.RecessiveVolterra
import Cvs.Upstream.HalfStripRayIntegrals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The recessive Liouville–Green solution solves the prolate equation

For the Volterra solution `ε` of Cvs.Prolate.LiouvilleGreen.RecessiveVolterra, `H₊ = Λe^{icΦ_T}(1 + ε)` and `H₊¹ = PH₊′` satisfy `H₊′ = H₊¹/P` and
`(H₊¹)′ = −c²QH₊` on `U_a`: `(PH′)′ + c²(T − z²)H = 0`, the prolate equation at `χ = c²T`.
-/

noncomputable section

open Real Set
open Complex (I)
open Cvs.Upstream.HalfStripRayIntegrals (strip)
open Cvs.Prolate.LiouvilleGreen.ComplexSymbols
open Cvs.Prolate.LiouvilleGreen.HalfStripPhase
open Cvs.Prolate.LiouvilleGreen.RecessiveVolterra

namespace Cvs.Prolate.LiouvilleGreen.RecessiveSolvesProlate

/-- `f` with flux `f₁ = Pf′` solves `(Pf′)′ + c²Qf = 0` on `S`. -/
def IsSolOn (c T : ℝ) (S : Set ℂ) (f f₁ : ℂ → ℂ) : Prop :=
  ∀ z ∈ S, HasDerivAt f (f₁ z / pP z) z ∧ HasDerivAt f₁ (-((c : ℂ) ^ 2 * pQ T z) * f z) z

/-- The recessive solution `H₊ = Λe^{icΦ_T}(1 + ε)`. -/
def hP (c T : ℝ) (ε : ℂ → ℂ) (z : ℂ) : ℂ := lam T z * Complex.exp (I * c * Phi T z) * (1 + ε z)

/-- Its flux `H₊¹ = PΛe^{icΦ_T}((ℓ + icΦ′)(1 + ε) + Φ′e^{−2icΦ_T}J)`. -/
def hP1 (c T : ℝ) (ε : ℂ → ℂ) (z : ℂ) : ℂ :=
  pP z * lam T z * Complex.exp (I * c * Phi T z) *
    ((ell T z + I * c * phiD T z) * (1 + ε z) + phiD T z * emph c T z * flux c T ε z)

variable {a T c : ℝ}

/-- The flux part of the residual cancels: `(−2z + Pℓ + icPΦ′)Φ′ + P(ℓ + icΦ′)Φ′ + PΦ″ − 2icPΦ′² = 0`. -/
theorem flux_cancel (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) (φ : ℂ) :
    (-(2 * z) + pP z * ell T z + I * c * pP z * φ) * φ + pP z * (ell T z + I * c * φ) * φ +
      pP z * (φ * (z / pP z - z / pQ T z)) - 2 * I * c * pP z * φ ^ 2 = 0 := by
  have hP := pP_ne hT hT1 hz
  have hQ := pQ_ne hT hz
  unfold ell
  field_simp
  unfold pP pQ
  ring

/-- The rate identity `P·Φ′(z/P − z/Q) = Φ′(2z − 2Pℓ)`. -/
theorem rate_eq (hT : a ^ 2 < T) (hT1 : T ≤ 1) {z : ℂ} (hz : z ∈ strip a) (φ : ℂ) :
    pP z * (φ * (z / pP z - z / pQ T z)) = φ * (2 * z - 2 * pP z * ell T z) := by
  have hP := pP_ne hT hT1 hz
  have hQ := pQ_ne hT hz
  unfold ell
  field_simp
  unfold pP pQ
  ring

/-- **The recessive solution solves the prolate equation** on `U_a`. -/
theorem isSolOn_hP (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {ε : ℂ → ℂ} {B : ℝ} (hε : Good a ε B)
    (hfix : ∀ z ∈ strip a, ε z = vop c T ε z) : IsSolOn c T (strip a) (hP c T ε) (hP1 c T ε) := by
  intro z hz
  have hPne := pP_ne hT hT1 hz
  have hlam := hasDerivAt_lam hT hT1 hz
  have he := ((hasDerivAt_Phi hT hT1 hz).const_mul (I * c)).cexp
  have hεd := hasDerivAt_eps hT hT1 hc hε hfix hz
  have hJ := hasDerivAt_flux hT hT1 hc hε hz
  have hφ := hasDerivAt_phiD hT hT1 hz
  have hell := hasDerivAt_ell hT hT1 hz
  have hE := hasDerivAt_emph (c := c) hT hT1 hz
  have hPd := hasDerivAt_pP z
  have hsq := phiD_sq (pp_ne hT hT1 hz)
  have hl2 := lam_sq_mul (T := T) hPne
  have hee := eph_mul_emph c T z
  have hsig := sig_eq hT hT1 hz
  have hfc := flux_cancel (c := c) hT hT1 hz (phiD T z)
  have hre := rate_eq hT hT1 hz (phiD T z)
  have hφ2 : pP z * phiD T z ^ 2 = pQ T z := by rw [hsq, pp]; field_simp
  refine ⟨?_, ?_⟩
  · refine ((hlam.mul he).mul (hεd.const_add 1)).congr_deriv ?_
    unfold hP1
    simp only [Pi.mul_apply]
    field_simp
  · have hA := ((hell.add (hφ.const_mul (I * c))).mul (hεd.const_add 1)).add ((hφ.mul hE).mul hJ)
    refine (((hPd.mul hlam).mul he).mul hA).congr_deriv ?_
    unfold hP resid rr
    simp only [Pi.mul_apply, Pi.add_apply]
    set φ := phiD T z
    set L := lam T z
    set e := Complex.exp (I * c * Phi T z)
    set E := emph c T z
    set ep := eph c T z
    set J := flux c T ε z
    set P := pP z
    set Q := pQ T z
    set ℓ := ell T z
    set ℓ' := ellD T z
    set σ := sig T z
    set w := ε z
    have hcomb : P * φ * E * ep * L ^ 2 = 1 := by
      calc P * φ * E * ep * L ^ 2 = (L ^ 2 * P * φ) * (ep * E) := by ring
        _ = 1 := by rw [hl2, hee, one_mul]
    linear_combination (L * e * (1 + w)) * (-(1 : ℂ)) * hsig + (L * e * (1 + w)) * (I * c) * hre +
      (L * e * (1 + w)) * (-((c : ℂ) ^ 2)) * hφ2 + (L * e * E * J) * hfc +
      (L * e * σ * (1 + w)) * (-(1 : ℂ)) * hcomb + (L * P * e * (c : ℂ) ^ 2 * φ ^ 2 * (1 + w)) * Complex.I_sq

end Cvs.Prolate.LiouvilleGreen.RecessiveSolvesProlate

end
