import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.StepA.OffLineHyperbolicMellin
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.InsideFunctionTame
import Cvs.WeilForm.MellinZeroSum
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The zero side of the window form, polarized

For `2 ≤ x` and `v, u` tame on `[1/x, 1]`, at `P = x`, `R = ⌈log₂ x⌉`:
`Q(w_v, w_u) = Σ_ρ (m_ρ/2) Re(M[v](1 − ρ) M[u](ρ) + M[u](1 − ρ) M[v](ρ))`, the family summable, by
`Q(a, b) = (Q(a) + Q(b) − Q(a − b))/2` and `w_{v−u} = w_v − w_u`. On the line the term is
`m_ρ Re(M[v](ρ) conj M[u](ρ))`; for a spine vector `v` is the spine window `W_a`.
-/

noncomputable section

open MeasureTheory Real Set Complex ComplexConjugate

namespace Cvs.WeilForm.ZeroSidePolarized
open Cvs.ZeroCounting

open Cvs.L2a.WindowFormTailLimit (Tame)
open Cvs.WeilForm.ThetaSpaceParseval (mellinR)
open Cvs.WeilForm.MellinZeroSum (Z zeroTerm)

/-- Left subtraction for `QWbil`, stated with the subtraction the form domain elaborates to. -/
private theorem QWbil_sub_left {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (a b c : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R (a - b) c
      = Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R a c
        - Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R b c :=
  LinearMap.map_sub₂ _ a b c

/-- Right subtraction for `QWbil`, stated with the subtraction the form domain elaborates to. -/
private theorem QWbil_sub_right {L : ℝ} (hL : 0 ≤ L) (P R : ℕ)
    (a b c : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R c (a - b)
      = Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R c a
        - Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R c b :=
  LinearMap.map_sub _ a b

/-- **The class of a difference is the difference of the classes**: `w_{v−u} = w_v − w_u`. -/
theorem wv_sub {x : ℕ} (hx0 : (0 : ℝ) < x) {v u : ℝ → ℝ} (hv : Tame v (1 / x) 1) (hu : Tame u (1 / x) 1) :
    Cvs.Approximant.SpineCouplingTailPairing.wv hx0 (Cvs.WeilForm.InsideFunctionTame.tame_sub hv hu) = Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv - Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu := by
  apply Subtype.ext; apply Subtype.ext; apply Lp.ext
  refine (Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 _).trans ?_
  simp only [Submodule.coe_sub]
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_sub _ _).symm
  filter_upwards [Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hv, Cvs.Approximant.SpineCouplingTailPairing.coe_wv_ae hx0 hu] with s h1 h2
  rw [Pi.sub_apply, h1, h2]
  simp only [Cvs.Approximant.SpineCouplingTailPairing.fv, Cvs.L2a.TailLogScaleTest.logScale]
  ring

/-- The polarized zero-side term `(m_ρ/2) Re(M[v](1 − ρ) M[u](ρ) + M[u](1 − ρ) M[v](ρ))`. -/
def crossTerm (v u : ℝ → ℝ) (rho : Z) : ℝ :=
  (Cvs.Criterion.divisorWeight rho : ℝ)
    * (mellinR v (1 - rho) * mellinR u rho + mellinR u (1 - rho) * mellinR v rho).re / 2

/-- **The zero-side term of a difference**: `z(v − u) = z(v) + z(u) − 2c(v, u)`. -/
theorem zeroTerm_sub {v u : ℝ → ℝ} {a : ℝ} (hv : Tame v a 1) (hu : Tame u a 1) (rho : Z) :
    zeroTerm (fun θ => v θ - u θ) rho = zeroTerm v rho + zeroTerm u rho - 2 * crossTerm v u rho := by
  rw [zeroTerm, zeroTerm, zeroTerm, crossTerm,
    Cvs.WeilForm.InsideFunctionTame.mellinR_sub (Cvs.StepA.OffLineHyperbolicMellin.win_of_tame hv) (Cvs.StepA.OffLineHyperbolicMellin.win_of_tame hu),
    Cvs.WeilForm.InsideFunctionTame.mellinR_sub (Cvs.StepA.OffLineHyperbolicMellin.win_of_tame hv) (Cvs.StepA.OffLineHyperbolicMellin.win_of_tame hu)]
  simp only [mul_re, sub_re, sub_im, add_re]
  ring

/-- The polarized term is half the defect of the difference: `c(v, u) = (z(v) + z(u) − z(v − u))/2`. -/
theorem crossTerm_eq {v u : ℝ → ℝ} {a : ℝ} (hv : Tame v a 1) (hu : Tame u a 1) (rho : Z) :
    crossTerm v u rho = (zeroTerm v rho + zeroTerm u rho - zeroTerm (fun θ => v θ - u θ) rho) / 2 := by
  rw [zeroTerm_sub hv hu]; ring

/-- **The class pairing of two tame tests is their polarized zero sum**: for `2 ≤ x` and `v, u` tame on
`[1/x, 1]`, `Q(w_v, w_u) = Σ_ρ (m_ρ/2) Re(M[v](1 − ρ) M[u](ρ) + M[u](1 − ρ) M[v](ρ))`, the family summable. -/
theorem QWbil_wv_eq_zeroSum {x : ℕ} (hx : 2 ≤ x) {v u : ℝ → ℝ} (hv : Tame v (1 / x) 1)
    (hu : Tame u (1 / x) 1) :
    Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.Approximant.SpineCouplingTailPairing.wv (Nat.cast_pos.mpr (by omega)) hv) (Cvs.Approximant.SpineCouplingTailPairing.wv (Nat.cast_pos.mpr (by omega)) hu)
      = ∑' rho : Z, crossTerm v u rho
    ∧ Summable (crossTerm v u) := by
  have hx0 : (0 : ℝ) < x := Nat.cast_pos.mpr (by omega)
  have hvu := Cvs.WeilForm.InsideFunctionTame.tame_sub hv hu
  obtain ⟨qv, sv⟩ := Cvs.WeilForm.MellinZeroSum.Q_wv_eq_zeroSum hx hv
  obtain ⟨qu, su⟩ := Cvs.WeilForm.MellinZeroSum.Q_wv_eq_zeroSum hx hu
  obtain ⟨qd, sd⟩ := Cvs.WeilForm.MellinZeroSum.Q_wv_eq_zeroSum hx hvu
  have hfun : crossTerm v u = fun rho => (zeroTerm v rho + zeroTerm u rho
      - zeroTerm (fun θ => v θ - u θ) rho) / 2 := funext (crossTerm_eq hv hu)
  have hs : Summable fun rho => zeroTerm v rho + zeroTerm u rho - zeroTerm (fun θ => v θ - u θ) rho :=
    (sv.add su).sub sd
  refine ⟨?_, by rw [hfun]; exact hs.div_const 2⟩
  set B := Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
  have hB := Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
  have hpol : B (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv - Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv - Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)
      = B (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv) - 2 * B (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)
        + B (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) := by
    rw [QWbil_sub_left, QWbil_sub_right, QWbil_sub_right,
      hB.eq (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv)]
    ring
  rw [← wv_sub hx0 hv hu, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, Cvs.WeilForm.SymmetricBilinearForm.QWbil_self] at hpol
  rw [hfun, tsum_div_const, (sv.add su).tsum_sub sd, sv.tsum_add su]
  have e1 : Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv)
      = ∑' rho : Z, zeroTerm v rho := qv
  have e2 : Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu)
      = ∑' rho : Z, zeroTerm u rho := qu
  have e3 : Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hvu)
      = ∑' rho : Z, zeroTerm (fun θ => v θ - u θ) rho := qd
  rw [e1, e2, e3] at hpol
  show B (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hv) (Cvs.Approximant.SpineCouplingTailPairing.wv hx0 hu) = _
  linarith

end Cvs.WeilForm.ZeroSidePolarized
