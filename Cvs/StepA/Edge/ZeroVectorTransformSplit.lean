import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.StepA.OneZeroParitySectors
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The transform of `U_ρ`, split into the four data terms

For `|Im ζ| < |γ_ρ|`, `e^{−ζT}F_{U_ρ}(ζ) = ¼(E_α(ζ) + E_ᾱ(ζ))`, `α = w_ρ`, `T = log x/2`, with
`E_c(ζ) = (e^{cT} − e^{−cT}e^{−2ζT})/(ζ + c) + (e^{−cT} − e^{cT}e^{−2ζT})/(ζ − c)`, the four terms `D₁ … D₄` of
caseinf-W Theorem C (iii). `E_c` is even in `c`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Interval ComplexConjugate
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.WindowCoshTransformDuality (wR coshT emb)
open Cvs.StepA.Edge.TransplantAngleHighZeros (shc ueClosed)

namespace Cvs.StepA.Edge.ZeroVectorTransformSplit
open Cvs.ZeroCounting

/-- `E_c(ζ) = (e^{cT} − e^{−cT}e^{−2ζT})/(ζ + c) + (e^{−cT} − e^{cT}e^{−2ζT})/(ζ − c)`. -/
def E (T : ℝ) (c ζ : ℂ) : ℂ :=
  (cexp (c * T) - cexp (-(c * T)) * cexp (-(2 * ζ * T))) / (ζ + c)
    + (cexp (-(c * T)) - cexp (c * T) * cexp (-(2 * ζ * T))) / (ζ - c)

theorem E_neg (T : ℝ) (c ζ : ℂ) : E T (-c) ζ = E T c ζ := by
  unfold E
  rw [show ζ + -c = ζ - c by ring, show ζ - -c = ζ + c by ring, neg_mul, neg_neg]
  ring

/-- `e^{−ζT}(shc(c + ζ) + shc(c − ζ)) = E_c(ζ)` for `c ± ζ ≠ 0`, `T = L/2`. -/
theorem exp_mul_shc_add (L : ℝ) {c ζ : ℂ} (h1 : c + ζ ≠ 0) (h2 : c - ζ ≠ 0) :
    cexp (-(ζ * (L / 2 : ℝ))) * (shc L (c + ζ) + shc L (c - ζ)) = E (L / 2) c ζ := by
  unfold shc E
  set T : ℂ := ((L / 2 : ℝ) : ℂ)
  have h1' : ζ + c ≠ 0 := by rwa [add_comm]
  have h2' : ζ - c ≠ 0 := fun h => h2 (by rw [← neg_sub, h, neg_zero])
  rw [Complex.sinh, Complex.sinh]
  have e1 : cexp ((c + ζ) * T) = cexp (c * T) * cexp (ζ * T) := by rw [← Complex.exp_add]; ring_nf
  have e2 : cexp (-((c + ζ) * T)) = cexp (-(c * T)) * cexp (-(ζ * T)) := by rw [← Complex.exp_add]; ring_nf
  have e3 : cexp ((c - ζ) * T) = cexp (c * T) * cexp (-(ζ * T)) := by rw [← Complex.exp_add]; ring_nf
  have e4 : cexp (-((c - ζ) * T)) = cexp (-(c * T)) * cexp (ζ * T) := by rw [← Complex.exp_add]; ring_nf
  have e5 : cexp (-(2 * ζ * T)) = cexp (-(ζ * T)) * cexp (-(ζ * T)) := by rw [← Complex.exp_add]; ring_nf
  have e6 : cexp (-(ζ * T)) * cexp (ζ * T) = 1 := by rw [← Complex.exp_add]; simp
  rw [e1, e2, e3, e4, e5, Complex.exp_neg (ζ * T), Complex.exp_neg (c * T)]
  have hP : cexp (ζ * T) ≠ 0 := Complex.exp_ne_zero _
  have hQ : cexp (c * T) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

/-- `E` at `±c` and `±c̄` agree with `E` at `w_ρ` and `w̄_ρ`. -/
theorem E_I_mul_zPoint (T : ℝ) (ρ : nonTrivialZeroSet) (ζ : ℂ) :
    E T (I * Cvs.ZeroCounting.zPoint ρ) ζ = E T (wR ρ) ζ := by
  rw [Cvs.StepA.Edge.WindowCoshTransformDuality.I_mul_zPoint]
  unfold wR
  split_ifs
  · rfl
  · rw [← E_neg]; congr 1; ring

theorem E_I_mul_conj_zPoint (T : ℝ) (ρ : nonTrivialZeroSet) (ζ : ℂ) :
    E T (I * conj (Cvs.ZeroCounting.zPoint ρ)) ζ = E T (conj (wR ρ)) ζ := by
  have h : I * conj (Cvs.ZeroCounting.zPoint ρ) = -conj (I * Cvs.ZeroCounting.zPoint ρ) := by
    rw [map_mul, Complex.conj_I]; ring
  rw [h, E_neg, Cvs.StepA.Edge.WindowCoshTransformDuality.I_mul_zPoint]
  unfold wR
  split_ifs
  · rfl
  · rw [← E_neg]; congr 1; simp [map_sub, map_div₀, map_ofNat]

/-- **The data of `U_ρ`**: `e^{−ζT}F_{U_ρ}(ζ) = ¼(E_{w_ρ}(ζ) + E_{w̄_ρ}(ζ))` for `|Im ζ| < |γ_ρ|`. -/
theorem exp_mul_coshT_ueVec {x : ℕ} (hx0 : (0 : ℝ) < x) (ρ : nonTrivialZeroSet) {ζ : ℂ}
    (hζ : |ζ.im| < |(ρ : ℂ).im|) :
    cexp (-(ζ * (Real.log x / 2 : ℝ))) * coshT x (emb x (Cvs.Route.Visibility.VisibilityClosingStep.ueVec hx0 (Cvs.ZeroCounting.zPoint ρ))) ζ
      = (E (Real.log x / 2) (wR ρ) ζ + E (Real.log x / 2) (conj (wR ρ)) ζ) / 4 := by
  set z := Cvs.ZeroCounting.zPoint ρ
  have hz : |ζ.im| < |z.re| := by rw [Cvs.ZeroCounting.zPoint_re]; exact hζ
  obtain ⟨h1, h2, h3, h4⟩ := Cvs.StepA.Edge.TransplantAngleHighZeros.ne_zero_of_im_lt hz
  rw [Cvs.StepA.Edge.TransplantAngleHighZeros.coshT_emb_ueVec, Cvs.StepA.Edge.TransplantAngleHighZeros.integral_ue_mul_cosh _ hz, ueClosed]
  rw [← E_I_mul_zPoint, ← E_I_mul_conj_zPoint, ← exp_mul_shc_add _ h1 h2, ← exp_mul_shc_add _ h3 h4]
  ring

end Cvs.StepA.Edge.ZeroVectorTransformSplit

end
