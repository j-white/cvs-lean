import Mathlib
import Cvs.Prolate.Gram.CentralResolventTrace
import Cvs.Prolate.Hardy.CosineSynthesisPlancherel
import Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Hardy extension operator `J_c f = 2 Re[w P₊(1_I f / w)]`

`P₊` is the orthogonal projection of `L²(ℝ, ℂ)` onto the functions whose `L²` Fourier transform vanishes on `(−∞, 0)`,
`w = e^{ibS}` with `S(z) = i√(−i(z − a))√(−i(z + a))`, `a = 1/2`, `b = c/2`, and `J_c : L²(I) →L[ℝ] L²(ℝ)`.
-/

noncomputable section

open Real Set MeasureTheory FourierTransform
open Complex (I)

namespace Cvs.Prolate.Hardy.HardyExtensionOperator
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.CentralResolventTrace (L2I)
open Cvs.Prolate.Hardy.ExtensionTraceColumnIntegral (L2R)
open Cvs.Prolate.Hardy.CosineSynthesisPlancherel (cI)

/-- Complex `L²(ℝ)`. -/
abbrev L2C : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- The `L²` Fourier transform as a continuous linear map. -/
def fourierL : L2C →L[ℂ] L2C := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap

/-- The functions whose `L²` Fourier transform vanishes a.e. on `(−∞, β)`. -/
def specGe (β : ℝ) : Submodule ℂ L2C :=
  LinearMap.ker (((LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Iio β)).comp fourierL :
    L2C →L[ℂ] Lp ℂ 2 (volume.restrict (Iio β))) : L2C →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Iio β)))

theorem isClosed_specGe (β : ℝ) : IsClosed (specGe β : Set L2C) :=
  ContinuousLinearMap.isClosed_ker _

instance (β : ℝ) : (specGe β).HasOrthogonalProjection := by
  have : CompleteSpace (specGe β) := (isClosed_specGe β).completeSpace_coe
  infer_instance

/-- The positive-frequency Hardy projection `P₊`. -/
def posProj : L2C →L[ℂ] L2C := (specGe 0).starProjection

/-- `S(z) = i√(−i(z − a))√(−i(z + a))`, `a = 1/2`: the branch of `√(z² − a²)` with `Im S ≥ 0` for `Im z ≥ 0`. -/
def sS (z : ℂ) : ℂ := I * Complex.sqrt (-I * (z - 1 / 2)) * Complex.sqrt (-I * (z + 1 / 2))

/-- The carrier `w(z) = e^{ibS(z)}`. -/
def wC (b : ℝ) (z : ℂ) : ℂ := Complex.exp (I * b * sS z)

/-- The boundary values of `w` on `ℝ`. -/
def wR (b : ℝ) (x : ℝ) : ℂ := wC b x

/-- The weight `1_I / w`. -/
def wInvI (b : ℝ) : ℝ → ℂ := cI.indicator fun x => (wR b x)⁻¹

open scoped Classical in
/-- Multiplication by an essentially bounded `m` on `L²(ℝ, ℂ)` (zero if `m ∉ L^∞`). -/
def mulOp (m : ℝ → ℂ) : L2C →L[ℂ] L2C :=
  if h : MemLp m ⊤ (volume : Measure ℝ) then
    (ContinuousLinearMap.lsmul ℂ ℂ).holderL (volume : Measure ℝ) ⊤ 2 2 (h.toLp m)
  else 0

theorem memLp_indicator_L2I (f : L2I) : MemLp (cI.indicator (f : ℝ → ℝ)) 2 (volume : Measure ℝ) :=
  (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (Lp.memLp f)

/-- Zero extension `L²(I) → L²(ℝ)` as a linear map. -/
def ext0ₗ : L2I →ₗ[ℝ] L2R where
  toFun f := (memLp_indicator_L2I f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    rw [← indicator_add']
    exact (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1 (Lp.coeFn_add f g)
  map_smul' r f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    have e : r • cI.indicator (f : ℝ → ℝ) = cI.indicator (fun x => r • (f : ℝ → ℝ) x) :=
      (indicator_const_smul cI r (f : ℝ → ℝ)).symm
    rw [e]
    exact (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc).1 (Lp.coeFn_smul r f)

theorem norm_ext0ₗ (f : L2I) : ‖ext0ₗ f‖ = ‖f‖ := by
  change ‖(memLp_indicator_L2I f).toLp _‖ = _
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet, Lp.norm_def]

/-- Zero extension `L²(I) →L[ℝ] L²(ℝ)`. -/
def ext0 : L2I →L[ℝ] L2R := LinearMap.mkContinuous ext0ₗ 1 fun f => by rw [norm_ext0ₗ, one_mul]

/-- `L²(ℝ, ℝ) → L²(ℝ, ℂ)`. -/
def ofRealLp : L2R →L[ℝ] L2C := Complex.ofRealCLM.compLpL 2 (volume : Measure ℝ)

/-- `Re : L²(ℝ, ℂ) → L²(ℝ, ℝ)`. -/
def reLp : L2C →L[ℝ] L2R := Complex.reCLM.compLpL 2 (volume : Measure ℝ)

/-- **The Hardy extension operator** `J_c f = 2 Re[w P₊(1_I f / w)]` with `b = c/2`. -/
def hardyJ (c : ℝ) : L2I →L[ℝ] L2R :=
  (2 : ℝ) • (reLp ∘L ((mulOp (wR (c / 2))).restrictScalars ℝ ∘L (posProj.restrictScalars ℝ ∘L
    ((mulOp (wInvI (c / 2))).restrictScalars ℝ ∘L (ofRealLp ∘L ext0)))))

end Cvs.Prolate.Hardy.HardyExtensionOperator

end
