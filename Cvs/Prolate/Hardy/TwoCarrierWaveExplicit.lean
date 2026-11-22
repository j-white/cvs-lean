import Mathlib
import Cvs.Prolate.Hardy.CarrierBoundaryValues
import Cvs.Prolate.Hardy.CarrierNegativeFrequencies
import Cvs.Prolate.Hardy.CarrierUpperHalfPlane
import Cvs.Prolate.Hardy.ColumnTwoCarrierWave
import Cvs.Prolate.Hardy.ColumnWaveErrorBound
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral
import Cvs.Prolate.Hardy.ExteriorSincColumns
import Cvs.Prolate.Hardy.HardyExtensionOperator
import Cvs.Prolate.Hardy.LipSymmetricPieces
import Cvs.Prolate.Hardy.ReflectedWaveSplit
import Cvs.Prolate.Hardy.SpectrumCosineHighpass
import Cvs.Prolate.Hardy.TraceLimitHighpassOperator
import Cvs.Upstream.FourierLpConjReflect
import Cvs.Upstream.HardyProjectionReal

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two-carrier wave `V_u` is explicit

With `W(θ) = (u sin(cu) cos θ − x cos(cu) sin θ)/(π(u² − x²)) = Re[A_u(x)e^{iθ}]`, `V_u = W(cx)` on `I`,
`V_u = W(cx) − W(c(x − S(x)))` on `½ < |x| ≤ ℓ`, and `0` elsewhere, so `‖V_u‖² = ∫ V_u²`.
-/

noncomputable section

open Real Set MeasureTheory
open Complex (I)

namespace Cvs.Prolate.Hardy.TwoCarrierWaveExplicit
open Cvs.ZeroCounting

open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R)
open Cvs.Prolate.Hardy.HardyExtensionOperator (L2C mulOp reLp wR)
open Cvs.Upstream.FourierLpConjReflect (conjLp)
open Cvs.Prolate.Hardy.CarrierBoundaryValues (sR)
open Cvs.Prolate.Hardy.CarrierNegativeFrequencies (carH)
open Cvs.Prolate.Hardy.LipSymmetricPieces (symS)
open Cvs.Prolate.Hardy.ColumnTwoCarrierWave (toL2 hI piece waveV)
open Cvs.Prolate.Hardy.ColumnWaveErrorBound (ell)

/-- The real column wave `W(θ) = (u sin(cu) cos θ − x cos(cu) sin θ)/(π(u² − x²))`. -/
def colWave (c u x θ : ℝ) : ℝ := (u * Real.sin (c * u) * Real.cos θ - x * Real.cos (c * u) * Real.sin θ) /
  (π * (u ^ 2 - x ^ 2))

/-- `Re[A_u(x)e^{iθ}] = W(θ)`. -/
theorem re_amp_mul_exp (c u x θ : ℝ) :
    (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u x * Complex.exp (I * θ)).re = colWave c u x θ := by
  have e : Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u x = ((u * Real.sin (c * u) / (π * (u ^ 2 - x ^ 2)) : ℝ) : ℂ) +
      ((x * Real.cos (c * u) / (π * (u ^ 2 - x ^ 2)) : ℝ) : ℂ) * I := by
    unfold Cvs.Prolate.Hardy.ExteriorSincColumns.amp
    push_cast
    ring
  rw [e, show I * (θ : ℂ) = (θ : ℂ) * I by ring, Complex.exp_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_im, Complex.mul_im]
  unfold colWave
  ring

/-- The explicit two-carrier wave. -/
def vfun (c u x : ℝ) : ℝ :=
  cI.indicator (fun x => colWave c u x (c * x)) x +
    (symS (1 / 2) ell).indicator (fun x => colWave c u x (c * x) - colWave c u x (c * (x - sR x))) x

theorem mem_symS_not_cI {x : ℝ} (hx : x ∈ symS (1 / 2) ell) (hx' : x ≠ -(1 / 2)) : x ∉ cI := by
  intro h
  rcases hx with hx | hx
  · linarith [hx.1, h.2]
  · exact hx' (le_antisymm hx.2 (by linarith [h.1]))

theorem half_le_abs_of_mem {x : ℝ} (hx : x ∈ symS (1 / 2) ell) : 1 / 2 ≤ |x| :=
  Cvs.Prolate.Hardy.LipSymmetricPieces.half_le_abs_of_mem_symS le_rfl hx

/-- `Re(w · H) = W(cx)` wherever `H = Ae^{icx}/w`. -/
theorem re_w_carH (c u x : ℝ) : (wR (c / 2) x * carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) x).re = colWave c u x (c * x) := by
  unfold carH
  rw [show wR (c / 2) x * (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u x * Complex.exp (I * c * x) * (wR (c / 2) x)⁻¹) =
      Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u x * Complex.exp (I * ((c * x : ℝ) : ℂ)) by
    field_simp [Cvs.Prolate.Hardy.CarrierUpperHalfPlane.wR_ne_zero]; push_cast; ring_nf]
  exact re_amp_mul_exp c u x (c * x)

/-- Off `I`, `Re(w · conj H) = W(c(x − S(x)))`. -/
theorem re_w_conj_carH (c u : ℝ) {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    (wR (c / 2) x * (starRingEnd ℂ) (carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) x)).re = colWave c u x (c * (x - sR x)) := by
  have hw := Cvs.Prolate.Hardy.CarrierBoundaryValues.wR_of_half_le_abs (c / 2) hx
  set E := Complex.exp (I * ((c / 2 : ℝ) * (sR x : ℂ)))
  have hcE : (starRingEnd ℂ) E = E⁻¹ := by
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    ring
  set z := Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u x * Complex.exp (I * c * x)
  have hcar : carH c (Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u) x = z * E⁻¹ := by unfold carH; rw [hw]
  rw [hcar, hw, map_mul, map_inv₀, hcE, inv_inv]
  have e1 : (E * ((starRingEnd ℂ) z * E)).re = (z * (E⁻¹ * E⁻¹)).re := by
    rw [← Complex.conj_re]
    congr 1
    simp only [map_mul, Complex.conj_conj, hcE]
    ring
  rw [e1]
  have e2 : z * (E⁻¹ * E⁻¹) = Cvs.Prolate.Hardy.ExteriorSincColumns.amp c u x * Complex.exp (I * ((c * (x - sR x) : ℝ) : ℂ)) := by
    simp only [z, E]
    rw [← Complex.exp_neg, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e2, re_amp_mul_exp]

/-- **`V_u` is explicit**: `V_u = vfun c u` a.e. -/
theorem coeFn_waveV {c : ℝ} (hc : 0 ≤ c) {u : ℝ} (hu : 1 < u) :
    (waveV c u ell : ℝ → ℝ) =ᵐ[volume] vfun c u := by
  have hm := Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_symS c hu (a := 1 / 2) (b := ell) (by norm_num) (by
    unfold ell; rw [div_le_iff₀ (by positivity)]
    have : (5 / 3 : ℝ) ≤ √3 := by
      rw [show (5 / 3 : ℝ) = √((5 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)] ]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith)
  set m := piece c u (1 / 2) ell
  set h := hI c u
  have hwmem : MemLp (wR (c / 2)) ⊤ (volume : Measure ℝ) := Cvs.Prolate.Hardy.CarrierUpperHalfPlane.memLp_wR (by positivity)
  unfold waveV
  filter_upwards [Cvs.Prolate.Hardy.ReflectedWaveSplit.coeFn_reLp (mulOp (wR (c / 2)) (h + m - conjLp m)),
    Cvs.Upstream.HardyProjectionReal.coeFn_mulOp hwmem (h + m - conjLp m), Lp.coeFn_sub (h + m) (conjLp m), Lp.coeFn_add h m,
    Cvs.Upstream.FourierLpConjReflect.coeFn_conjLp m, Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 (Cvs.Prolate.Hardy.ColumnTwoCarrierWave.memLp_cI c hu), Cvs.Prolate.Hardy.ColumnTwoCarrierWave.coeFn_toL2 hm, Cvs.Prolate.Hardy.SpectrumCosineHighpass.ae_ne (-(1 / 2))]
    with x h1 h2 h3 h4 h5 h6 h7 hx
  simp only [h, m, hI, piece] at h1 h2 h3 h4 h5 h6 h7 ⊢
  rw [h1, h2, h3, Pi.sub_apply, h4, Pi.add_apply, h5, h6, h7]
  unfold vfun
  by_cases hI' : x ∈ cI
  · have hS : x ∉ symS (1 / 2) ell := fun hs => mem_symS_not_cI hs hx hI'
    rw [indicator_of_mem hI', indicator_of_mem hI', indicator_of_notMem hS, indicator_of_notMem hS, map_zero,
      add_zero, sub_zero, add_zero, re_w_carH]
  · by_cases hS : x ∈ symS (1 / 2) ell
    · rw [indicator_of_notMem hI', indicator_of_notMem hI', indicator_of_mem hS, indicator_of_mem hS, zero_add,
        zero_add, mul_sub, Complex.sub_re, re_w_carH, re_w_conj_carH c u (half_le_abs_of_mem hS)]
    · rw [indicator_of_notMem hI', indicator_of_notMem hI', indicator_of_notMem hS, indicator_of_notMem hS]
      simp

/-- `‖V_u‖² = ∫ V_u²`. -/
theorem norm_waveV_sq {c : ℝ} (hc : 0 ≤ c) {u : ℝ} (hu : 1 < u) : ‖waveV c u ell‖ ^ 2 = ∫ x, vfun c u x ^ 2 := by
  rw [← Cvs.Prolate.Hardy.TraceLimitHighpassOperator.integral_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_waveV hc hu] with x hx
  rw [hx]

end Cvs.Prolate.Hardy.TwoCarrierWaveExplicit

end
