import Mathlib
import Cvs.Finite.EvenSectorZeroSide
import Cvs.WeilForm.SelfConvolutionTransform
import Cvs.Zeta.ExplicitFormula.HannWindowShifts
import Cvs.Zeta.ExplicitFormula.WindowTransformEntire

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The centred cosine transform of the even window modes, its Nyquist samples and its zeros

For `Φ_f(ξ) = ∫₀^L f(s) cos(ξ(s − L/2)) ds` and `ω_m = 2πm/L`, the cosine mode has `Φ(z) = 2z sin(zL/2)/(z² − ω_m²)`
off the nodes, with exact node samples. For reflection-even `f`, `CompactTestAdmissibility.sqTransform = Φ_f²` at every complex `ξ`, so
with `Cvs.Finite.ZeroSideGramMatrix.zeroSide_eq_ddMatrix`, `L·ξᵀ Cvs.Finite.TruncationQuadraticForm.M ξ = ∑_ρ m_ρ Re Φ(z_ρ)²` over all nontrivial zeros. In the coordinates
`f_v` on `Cvs.Finite.SymmetricModeSet`'s even vectors, `∑_{m ∈ ℤ} Φ_v(ω_m)² = L ∑ v_m² = L ∫₀^L f_v²`.
-/

noncomputable section

open Real

namespace Cvs.Finite.CentredCosineNyquist
open Cvs.ZeroCounting

/-- The centred cosine transform of a function on the window `[0, L]`. -/
def Phi (L : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..L, f s * cos (z * (s - L / 2))

/-- The mode frequency `ω_m = 2πm/L`. -/
def om (L : ℝ) (m : ℤ) : ℝ := 2 * π * m / L

/-! ### One cosine mode -/

/-! ### Cosine polynomials -/

variable {ι : Type*} [Fintype ι]

/-- `Cvs.Finite.EvenSectorZeroSide.cosPoly` unfolds to `∑ ξ_i cos(ω_{mode i} s)`. -/
theorem cosPoly_eq (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) :
    Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi = fun s => ∑ i, xi i * cos (om L (mode i) * s) := rfl

/-! ### Normalised coordinates: `f_v = ∑ v_k nrm_k cos(ω_k s)` -/

/-! ### The bridge to the window transform -/

/-- The complex cast of an interval-integrable real function is interval-integrable. -/
theorem intervalIntegrable_ofReal {f : ℝ → ℝ} {a b : ℝ} (h : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => (f x : ℂ)) MeasureTheory.volume a b :=
  ⟨MeasureTheory.Integrable.ofReal h.1, MeasureTheory.Integrable.ofReal h.2⟩

/-- A cosine polynomial on the mode lattice is reflection-even on the window. -/
theorem cosPoly_reflect (L : ℝ) (mode : ι → ℤ) (xi : ι → ℝ) (s : ℝ) :
    Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi (L - s) = Cvs.Finite.EvenSectorZeroSide.cosPoly L mode xi s := by
  rcases eq_or_ne L 0 with hL | hL
  · subst hL; simp [cosPoly_eq, om]
  rw [cosPoly_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : om L (mode i) * (L - s) = -(om L (mode i) * s - (mode i : ℝ) * (2 * π)) := by
    unfold om; field_simp; ring
  rw [this, cos_neg, cos_sub_int_mul_two_pi]

/-! ### The complex amplitude and the zero side -/

/-- The centred cosine transform at a complex argument, `Φ_f(ξ) = ∫₀^L f(s) cos(ξ(s − L/2)) ds`. -/
def PhiC (L : ℝ) (f : ℝ → ℝ) (ξ : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..L, (f s : ℂ) * Complex.cos (ξ * ((s : ℂ) - (L : ℂ) / 2))

/-- On the real line the complex amplitude is `Φ`. -/
theorem PhiC_ofReal (L : ℝ) (f : ℝ → ℝ) (z : ℝ) : PhiC L f z = ((Phi L f z : ℝ) : ℂ) := by
  unfold PhiC Phi
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s _ => ?_
  push_cast
  try rfl

/-- The complex amplitude is even. -/
theorem PhiC_neg (L : ℝ) (f : ℝ → ℝ) (ξ : ℂ) : PhiC L f (-ξ) = PhiC L f ξ := by
  unfold PhiC
  simp_rw [neg_mul, Complex.cos_neg]

/-- A reflection-even integrand has vanishing complex sine moment about the window centre. -/
theorem integral_sinC_center_eq_zero {L : ℝ} {f : ℝ → ℝ} (hf : ∀ s, f (L - s) = f s) (ξ : ℂ) :
    ∫ s in (0 : ℝ)..L, (f s : ℂ) * Complex.sin (ξ * ((s : ℂ) - (L : ℂ) / 2)) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := L)
    (fun s : ℝ => (f s : ℂ) * Complex.sin (ξ * ((s : ℂ) - (L : ℂ) / 2))) L
  simp only [sub_self, sub_zero] at h
  have hneg : ∀ s : ℝ, (f (L - s) : ℂ) * Complex.sin (ξ * (((L - s : ℝ) : ℂ) - (L : ℂ) / 2))
      = -((f s : ℂ) * Complex.sin (ξ * ((s : ℂ) - (L : ℂ) / 2))) := by
    intro s
    rw [hf s, show ξ * (((L - s : ℝ) : ℂ) - (L : ℂ) / 2) = -(ξ * ((s : ℂ) - (L : ℂ) / 2)) by
      push_cast; ring, Complex.sin_neg]
    ring
  simp_rw [hneg, intervalIntegral.integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- **The complex amplitude is the recentred window transform**: for reflection-even integrable `f` and every
`ξ : ℂ`, `Φ_f(ξ) = e^{iξL/2}·`HannWindowShifts.windowTransform` L f ξ`. -/
theorem PhiC_eq_windowTransform {L : ℝ} {f : ℝ → ℝ} (hf : ∀ s, f (L - s) = f s)
    (hint : IntervalIntegrable f MeasureTheory.volume 0 L) (ξ : ℂ) :
    PhiC L f ξ = Complex.exp (ξ * ((L : ℂ) / 2) * Complex.I)
      * Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ := by
  unfold Cvs.Detection.windowTransform Cvs.WeilForm.SelfConvolutionTransform.cf
  rw [← intervalIntegral.integral_const_mul]
  have hpt : ∀ s : ℝ, Complex.exp (ξ * ((L : ℂ) / 2) * Complex.I)
        * (Complex.exp (-((s : ℂ) * ξ) * Complex.I) * (f s : ℂ))
      = (f s : ℂ) * Complex.cos (ξ * ((s : ℂ) - (L : ℂ) / 2))
        - Complex.I * ((f s : ℂ) * Complex.sin (ξ * ((s : ℂ) - (L : ℂ) / 2))) := by
    intro s
    rw [← mul_assoc, ← Complex.exp_add]
    have e : ξ * ((L : ℂ) / 2) * Complex.I + -((s : ℂ) * ξ) * Complex.I
        = (-(ξ * ((s : ℂ) - (L : ℂ) / 2))) * Complex.I := by ring
    rw [e, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  simp_rw [hpt]
  have hc : IntervalIntegrable (fun s : ℝ => (f s : ℂ) * Complex.cos (ξ * ((s : ℂ) - (L : ℂ) / 2)))
      MeasureTheory.volume 0 L :=
    (intervalIntegrable_ofReal hint).mul_continuousOn (by fun_prop)
  have hs : IntervalIntegrable (fun s : ℝ => (f s : ℂ) * Complex.sin (ξ * ((s : ℂ) - (L : ℂ) / 2)))
      MeasureTheory.volume 0 L :=
    (intervalIntegrable_ofReal hint).mul_continuousOn (by fun_prop)
  rw [intervalIntegral.integral_sub hc (hs.const_mul _), intervalIntegral.integral_const_mul,
    integral_sinC_center_eq_zero hf ξ, mul_zero, sub_zero]
  rfl

/-- **The complex amplitude is entire** for a continuous reflection-even `f` on a window of length `L ≥ 0`. -/
theorem differentiable_PhiC {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : ∀ s, f (L - s) = f s)
    (hc : Continuous f) : Differentiable ℂ (PhiC L f) := by
  have hfun : PhiC L f = fun ξ => Complex.exp (ξ * ((L : ℂ) / 2) * Complex.I)
      * Cvs.Detection.windowTransform L (Cvs.WeilForm.SelfConvolutionTransform.cf f) ξ :=
    funext (PhiC_eq_windowTransform hf (hc.intervalIntegrable 0 L))
  rw [hfun]
  have hcf : Continuous (Cvs.WeilForm.SelfConvolutionTransform.cf f) := by
    unfold Cvs.WeilForm.SelfConvolutionTransform.cf; fun_prop
  exact (((differentiable_id.mul_const _).mul_const _).cexp).mul
    (Cvs.Detection.differentiable_windowTransform hL hcf)

/-- **`Φ` is smooth on the real line** for a continuous reflection-even `f`, `L ≥ 0`. -/
theorem contDiff_Phi {L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ} (hf : ∀ s, f (L - s) = f s)
    (hc : Continuous f) {n : WithTop ℕ∞} : ContDiff ℝ n (Phi L f) := by
  have h1 : ContDiff ℝ n (PhiC L f) := ((differentiable_PhiC hL hf hc).contDiff).restrict_scalars ℝ
  have hfun : Phi L f = fun τ : ℝ => Complex.reCLM (PhiC L f (Complex.ofRealCLM τ)) := by
    funext τ
    simp [PhiC_ofReal]
  rw [hfun]
  exact Complex.reCLM.contDiff.comp (h1.comp Complex.ofRealCLM.contDiff)

/-! ### The normalised coordinates on the symmetric mode set -/

end Cvs.Finite.CentredCosineNyquist
