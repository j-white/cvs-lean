import Mathlib
import Cvs.Approximant.D0FloorEvenRungShare
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCoefficientMatrix
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineFormOwnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.L2a.ReflectedSpineTame
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.BulkSchurIdentity
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.Xi.EImageWindowPoisson
import Cvs.Xi.PhysicalReciprocalReflection

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The low-eigenvalue count on the spine and on its even part

On the spine (`u_s = uA x s`) the count of eigenvalues above `ε` is at most `2N_dist(T)`. The even part of the
spine class of `a` is the class of `(W_a + R_{1/x}W_a)/2`, whose window transform is
`u^E_s(a) = (u_s(a) + x^{½−s} u_{1−s}(a))/2`, with `u^E_{1−s} = x^{s−½} u^E_s`; so on the even rung matrix
the count is at most `N_dist(T)`, for `80 ≤ 2πx` and any `ε`, `M` with far sum `≤ ε aᵀMa`.
-/

noncomputable section

open Real Set MeasureTheory Matrix Module ComplexConjugate

namespace Cvs.StepA.LowEigenvalueCountSpine
open Cvs.ZeroCounting

open Cvs.Approximant.SpineCoefficientMatrix (uA spineGram)
open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.Xi.EImageWindowPoisson (window)
open Cvs.Xi.PhysicalReciprocalReflection (reciprocal)

/-! ### The spine -/

/-! ### Averages of tame tests -/

/-- **A tame test is Mellin-convergent everywhere.** -/
theorem tame_mellinConvergent {v : ℝ → ℝ} {α β : ℝ} (h : Tame v α β) (s : ℂ) :
    MellinConvergent (fun θ => (v θ : ℂ)) s := by
  obtain ⟨M, hM⟩ := h.bdd
  have hIcc : IntegrableOn (fun θ : ℝ => (θ : ℂ) ^ (s - 1) * (v θ : ℂ)) (Icc α β) := by
    refine IntegrableOn.continuousOn_mul ?_ ?_ isCompact_Icc
    · exact Complex.continuous_ofReal.continuousOn.cpow_const fun θ hθ =>
        Complex.ofReal_mem_slitPlane.2 (h.pos.trans_le hθ.1)
    · refine IntegrableOn.of_bound measure_Icc_lt_top
        (Complex.continuous_ofReal.measurable.comp h.meas).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun θ => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hM θ
  unfold MellinConvergent
  simp only [smul_eq_mul]
  refine hIcc.of_forall_sdiff_eq_zero measurableSet_Ioi fun θ hθ => ?_
  rw [h.supp θ hθ.2, Complex.ofReal_zero, mul_zero]

/-- The average `(v + w)/2`. -/
def avg (v w : ℝ → ℝ) : ℝ → ℝ := fun θ => (v θ + w θ) / 2

/-- **The Mellin transform of an average of tame tests is the average of their transforms.** -/
theorem mellinR_avg {v w : ℝ → ℝ} {α β α' β' : ℝ} (hv : Tame v α β) (hw : Tame w α' β') (s : ℂ) :
    mellinR (avg v w) s = (mellinR v s + mellinR w s) / 2 := by
  have h := Cvs.Approximant.SpineCoefficientMatrix.mellinR_finsetSum (Finset.univ : Finset (Fin 2)) ![1 / 2, 1 / 2] ![v, w] (s := s)
    fun i _ => by fin_cases i <;> simp [tame_mellinConvergent hv, tame_mellinConvergent hw]
  have e : avg v w = fun θ => ∑ i ∈ (Finset.univ : Finset (Fin 2)), (![1 / 2, 1 / 2] : Fin 2 → ℝ) i
      * (![v, w] : Fin 2 → ℝ → ℝ) i θ := by
    funext θ; simp [avg, Fin.sum_univ_two]; ring
  rw [e, h, Fin.sum_univ_two]
  simp; ring

/-- **An average of tame tests on `[α, β]` is tame on `[α, β]`.** -/
theorem tame_avg {v w : ℝ → ℝ} {α β : ℝ} (hv : Tame v α β) (hw : Tame w α β) : Tame (avg v w) α β where
  pos := hv.pos
  supp θ hθ := by simp [avg, hv.supp θ hθ, hw.supp θ hθ]
  meas := (hv.meas.add hw.meas).div_const 2
  bdd := by
    obtain ⟨M, hM⟩ := hv.bdd
    obtain ⟨N, hN⟩ := hw.bdd
    refine ⟨(M + N) / 2, fun θ => ?_⟩
    rw [avg, abs_div, abs_two]
    exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add (hM θ) (hN θ))) zero_le_two
  dec := by
    obtain ⟨C, hC⟩ := hv.dec
    obtain ⟨D, hD⟩ := hw.dec
    refine ⟨(C + D) / 2, fun s h1 h2 h3 => ?_⟩
    rw [mellinR_avg hv hw, norm_div, Complex.norm_two]
    have := (norm_add_le _ _).trans (add_le_add (hC s h1 h2 h3) (hD s h1 h2 h3))
    calc ‖mellinR v s + mellinR w s‖ / 2 ≤ (C / |s.im| + D / |s.im|) / 2 :=
          div_le_div_of_nonneg_right this zero_le_two
      _ = (C + D) / 2 / |s.im| := by ring

/-! ### The even part of a spine class -/

theorem two_le {x : ℕ} (hx : 80 ≤ 2 * π * x) : 2 ≤ x := by
  by_contra h
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast (by omega : x ≤ 1)
  nlinarith [Real.pi_le_four, Real.pi_pos]

/-- The even spine window `(W_a + R_{1/x}W_a)/2`. -/
def evenWin (x : ℕ) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : ℝ → ℝ :=
  avg (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a))
    (reciprocal (1 / x) (window (1 / x) (Cvs.Approximant.DeepIndexSpineSpan.spineG (2 * π * x) a)))

theorem tame_evenWin {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) : Tame (evenWin x a) (1 / x) 1 :=
  tame_avg (Cvs.Approximant.SpineFormOwnTailPairing.tame_spineWindow hx a) (Cvs.L2a.ReflectedSpineTame.tame_reciprocal_spineWindow hx a)

/-- **The even part of a spine class is the class of the even spine window.** -/
theorem evenPart_spineMap_eq_wv {x : ℕ} (hx : 80 ≤ 2 * π * x) (a : Cvs.Approximant.SpineSubspace.SF x → ℝ) :
    Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.SpineSubspace.spineMap x a)
      = Cvs.Approximant.SpineCouplingTailPairing.wv (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) (tame_evenWin hx a) := by
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  unfold Cvs.WeilForm.EvenOddSplitForm.evenPart
  rw [Cvs.L2a.ReflectedSpineTame.reflD_spineMap hx a, Cvs.Approximant.SpineFormOwnTailPairing.spineMap_eq_wv hx a]
  set φ := Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.Approximant.SpineFormOwnTailPairing.tame_spineWindow hx a)
  set ψ := Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.L2a.ReflectedSpineTame.tame_reciprocal_spineWindow hx a)
  apply Subtype.ext; apply Subtype.ext; apply Lp.ext
  simp only [Submodule.coe_smul, Submodule.coe_add]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) ((φ : Lp ℝ 2 volume) + (ψ : Lp ℝ 2 volume)),
    Lp.coeFn_add (φ : Lp ℝ 2 volume) (ψ : Lp ℝ 2 volume),
    Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.Approximant.SpineFormOwnTailPairing.tame_spineWindow hx a),
    Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (Cvs.L2a.ReflectedSpineTame.tame_reciprocal_spineWindow hx a),
    Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 (tame_evenWin hx a)] with θ h1 h2 h3 h4 h5
  rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, h5]
  simp only [Cvs.Approximant.SpineCouplingTailPairing.fv, Cvs.L2a.TailLogScaleTest.logScale, evenWin, avg, smul_eq_mul]
  ring

/-- The even spine form is symmetric. -/
theorem evenForm_isSymm (x : ℕ) : (Cvs.L2a.EvenSectorReflectionBound.evenForm x).IsSymm :=
  ⟨fun _ _ => (Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm (Real.log_natCast_nonneg x) x (Nat.clog 2 x)).eq _ _⟩

theorem evenGram_isHermitian (x : ℕ) : (Cvs.L2a.EvenSectorReflectionBound.evenGram x).IsHermitian :=
  Cvs.WeilForm.BulkSchurIdentity.gram_isHermitian (evenForm_isSymm x) _

/-! ### The constraints as window-transform zeros -/

end Cvs.StepA.LowEigenvalueCountSpine
