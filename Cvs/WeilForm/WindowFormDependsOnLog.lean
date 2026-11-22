import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.LevyDensity
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.NestedWindowsMonotoneBottom
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.VonMangoldtMultiplier
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.PrimePowerSideTruncated
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window form at `x` depends on `x` only through `L = log x`

On the form domain at `L`, the truncated form `Cvs.WeilForm.InfimumAttainedSphere.Q hL P R` takes one value for every complete truncation
`(P, R)`, `e^L ≤ P` and `L ≤ R log 2`. Hence `Q_x = Cvs.WeilForm.InfimumAttainedSphere.Q (log x) P R` for every complete `(P, R)`; in particular
the cutoff `Nat.clog 2 x` may be replaced by any `R` with `x ≤ 2^R`, and `x` by any `P ≥ x`.
-/

noncomputable section

open Real MeasureTheory

namespace Cvs.WeilForm.WindowFormDependsOnLog
open Cvs.ZeroCounting

open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.Route.WindowPositivityBulkCoupling (Qx)

/-- **Enlarging a complete truncation leaves `Cvs.WeilForm.InfimumAttainedSphere.Q` unchanged.** -/
theorem Q_eq_of_le_of_complete {L : ℝ} (hL : 0 ≤ L) {P R P' R' : ℕ} (hPP : P ≤ P') (hRR : R ≤ R')
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (φ : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P' R' φ = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ := by
  show Cvs.WeilForm.WindowRepresentative.weilQW P' R' (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L) = Cvs.WeilForm.WindowRepresentative.weilQW P R (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)
  unfold Cvs.WeilForm.WindowRepresentative.weilQW
  rw [Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (Cvs.WeilForm.WindowRepresentative.ae_eq_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L)),
    Cvs.WeilForm.WeilFormOnWindowL2.weilQ_eq (Cvs.WeilForm.WindowRepresentative.ae_eq_rep (φ : Cvs.WeilForm.WeilFormOnWindowL2.window L))]
  unfold Cvs.WeilForm.SelfConvolutionFunctional.weilForm
  rw [Cvs.WeilForm.NestedWindowsMonotoneBottom.primeSide_eq_of_complete hPP hRR hP hR]

/-- **Any two complete truncations give the same form**: `Cvs.WeilForm.InfimumAttainedSphere.Q hL P R = Cvs.WeilForm.InfimumAttainedSphere.Q hL P' R'`. -/
theorem Q_eq_of_complete {L : ℝ} (hL : 0 ≤ L) {P R P' R' : ℕ}
    (hP : Real.exp L ≤ P) (hR : L ≤ R * Real.log 2) (hP' : Real.exp L ≤ P') (hR' : L ≤ R' * Real.log 2)
    (φ : Cvs.WeilForm.FormDomain.formDomain hL) : Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ = Cvs.WeilForm.InfimumAttainedSphere.Q hL P' R' φ := by
  have hm : Real.exp L ≤ (min P P' : ℕ) := by
    rcases min_choice P P' with h | h <;> rw [h] <;> assumption
  have hr : L ≤ (min R R' : ℕ) * Real.log 2 := by
    rcases min_choice R R' with h | h <;> rw [h] <;> assumption
  rw [Q_eq_of_le_of_complete hL (min_le_left P P') (min_le_left R R') hm hr,
    Q_eq_of_le_of_complete hL (min_le_right P P') (min_le_right R R') hm hr]

/-- **`Q_x` is the form at `L = log x` with any complete truncation**: `Q_x = Cvs.WeilForm.InfimumAttainedSphere.Q (log x) P R` whenever
`e^{log x} ≤ P` and `log x ≤ R log 2`. -/
theorem Qx_eq_Q_of_complete {x : ℕ} (hx : 1 ≤ x) {P R : ℕ} (hP : Real.exp (Real.log x) ≤ P)
    (hR : Real.log x ≤ R * Real.log 2) (φ : Dom x) :
    Qx x φ = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R φ := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  exact Q_eq_of_complete (Real.log_natCast_nonneg x) (Real.exp_log hx0).le
    (Cvs.WeilForm.VonMangoldtMultiplier.log_le_clog_mul_log_two x) hP hR φ

/-- **The cutoff `Nat.clog 2 x` is invisible**: `Q_x = Cvs.WeilForm.InfimumAttainedSphere.Q (log x) x R` for every `R` with `x ≤ 2^R`. -/
theorem Qx_eq_Q_of_le_two_pow {x : ℕ} (hx : 1 ≤ x) {R : ℕ} (hR : x ≤ 2 ^ R) (φ : Dom x) :
    Qx x φ = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x R φ := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  refine Qx_eq_Q_of_complete hx (Real.exp_log hx0).le ?_ φ
  have h2 : (x : ℝ) ≤ (2 : ℝ) ^ R := by exact_mod_cast hR
  calc Real.log x ≤ Real.log ((2 : ℝ) ^ R) := Real.log_le_log hx0 h2
    _ = R * Real.log 2 := Real.log_pow 2 R

/-- **The prime range is invisible above `x`**: `Q_x = Cvs.WeilForm.InfimumAttainedSphere.Q (log x) P (Nat.clog 2 x)` for every `P ≥ x`. -/
theorem Qx_eq_Q_of_le {x : ℕ} (hx : 1 ≤ x) {P : ℕ} (hP : x ≤ P) (φ : Dom x) :
    Qx x φ = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P (Nat.clog 2 x) φ := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  refine Qx_eq_Q_of_complete hx ?_ (Cvs.WeilForm.VonMangoldtMultiplier.log_le_clog_mul_log_two x) φ
  rw [Real.exp_log hx0]
  exact_mod_cast hP

end Cvs.WeilForm.WindowFormDependsOnLog
