import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.CouplingAngle
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MellinZeroSum
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowTestOperators
import Cvs.WeilForm.WindowTestSelfAdjoint
import Cvs.WeilForm.WindowWeilCriterion
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.ZeroSidePairingEigenvalues

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Weil form on window test functions: Parseval under RH, and the zero samples
For `2 ≤ x`, `W(f, f) = Σ_ρ m_ρ Re(f̂(1 − ρ) f̂(ρ))`, and the samples `f ↦ Σ_{ρ ∈ S} f̂(ρ) δ_ρ` carry `T` to
`ZeroSidePairingEigenvalues`'s multiplication by `ρ(1 − ρ)`. Under RH every term is `m_ρ |f̂(ρ)|²`, so `W ≥ 0` and each zero's
evaluation is `W`-bounded, `m_ρ |f̂(ρ)|² ≤ W(f, f)`; RH is `Q ≥ 0` on the form domain at every large `x`.
-/

noncomputable section

open scoped Distributions
open Set MeasureTheory Complex

namespace Cvs.WeilForm.WindowTestParseval
open Cvs.ZeroCounting

open Cvs.WeilForm.WindowTestOperators Cvs.WeilForm.WindowTestSelfAdjoint
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)
open Cvs.WeilForm.MellinZeroSum (Z)

/-! ### The diagonal -/

/-- `W(f, f) = Q(w_f)`. -/
theorem weil_self {x : ℕ} (hx0 : (0 : ℝ) < x) (f : 𝓓(win (Real.log x), ℝ)) :
    weil hx0 f f = Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (toDom hx0 f) :=
  Cvs.WeilForm.SymmetricBilinearForm.QWbil_self _ _ _ _

/-- The diagonal zero-side term `m_ρ Re(f̂(1 − ρ) f̂(ρ))`. -/
def diagTerm (L : ℝ) (f : ℝ → ℝ) (ρ : Z) : ℝ :=
  (Cvs.Criterion.divisorWeight ρ : ℝ) * (hat L f (1 - ρ) * hat L f ρ).re

theorem term_self (L : ℝ) (f : ℝ → ℝ) (ρ : Z) : term L f f ρ = diagTerm L f ρ := by
  unfold term diagTerm
  rw [Complex.add_re]
  ring

/-- **The explicit formula on the diagonal**: for `2 ≤ x`, `W(f, f) = Σ_ρ m_ρ Re(f̂(1 − ρ) f̂(ρ))`. -/
theorem hasSum_weil_self {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 2 ≤ x) (f : 𝓓(win (Real.log x), ℝ)) :
    HasSum (diagTerm (Real.log x) f) (weil hx0 f f) := by
  have h := hasSum_weil hx0 hx f f
  rwa [show term (Real.log x) f f = diagTerm (Real.log x) f from funext (term_self _ _)] at h

/-- On the critical line the diagonal term is `m_ρ |f̂(ρ)|²`. -/
theorem diagTerm_of_re (L : ℝ) (f : ℝ → ℝ) {ρ : Z} (h : (ρ : ℂ).re = 1 / 2) :
    diagTerm L f ρ = (Cvs.Criterion.divisorWeight ρ : ℝ) * ‖hat L f ρ‖ ^ 2 := by
  have h1 : 1 - (ρ : ℂ) = (starRingEnd ℂ) ρ := by
    apply Complex.ext <;> simp [h]
    norm_num
  rw [diagTerm, h1, hat_conj, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-! ### Under RH: Parseval and bounded evaluations -/

/-- **Parseval under RH**: for `2 ≤ x`, `W(f, f) = Σ_ρ m_ρ |f̂(ρ)|²`. -/
theorem hasSum_weil_self_of_rh (hRH : RiemannHypothesis) {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 2 ≤ x)
    (f : 𝓓(win (Real.log x), ℝ)) :
    HasSum (fun ρ : Z => (Cvs.Criterion.divisorWeight ρ : ℝ) * ‖hat (Real.log x) f ρ‖ ^ 2)
      (weil hx0 f f) := by
  have h := hasSum_weil_self hx0 hx f
  rwa [show diagTerm (Real.log x) f = fun ρ : Z =>
      (Cvs.Criterion.divisorWeight ρ : ℝ) * ‖hat (Real.log x) f ρ‖ ^ 2 from
    funext fun ρ => diagTerm_of_re _ _ (Cvs.WeilForm.CouplingAngle.re_eq_half_of_rh hRH ρ)] at h

/-- Under RH the Weil form is nonnegative on the window's test functions. -/
theorem weil_self_nonneg_of_rh (hRH : RiemannHypothesis) {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 2 ≤ x)
    (f : 𝓓(win (Real.log x), ℝ)) : 0 ≤ weil hx0 f f :=
  (hasSum_weil_self_of_rh hRH hx0 hx f).nonneg fun _ => by positivity

/-- **Under RH every zero's evaluation is `W`-bounded**: `m_ρ |f̂(ρ)|² ≤ W(f, f)`. -/
theorem sq_norm_hat_le_weil_of_rh (hRH : RiemannHypothesis) {x : ℕ} (hx0 : (0 : ℝ) < x) (hx : 2 ≤ x)
    (f : 𝓓(win (Real.log x), ℝ)) (ρ : Z) :
    (Cvs.Criterion.divisorWeight ρ : ℝ) * ‖hat (Real.log x) f ρ‖ ^ 2 ≤ weil hx0 f f :=
  le_hasSum (hasSum_weil_self_of_rh hRH hx0 hx f) ρ fun _ _ => by positivity

/-! ### The zero samples and the zero-side `T` -/

/-- The samples on a finite set `S`: `f ↦ Σ_{ρ ∈ S} f̂(ρ) δ_ρ`. -/
def samples (L : ℝ) (S : Finset ℂ) : 𝓓(win L, ℝ) →ₗ[ℝ] ℂ →₀ ℂ :=
  ∑ ρ ∈ S, ((Finsupp.lsingle ρ : ℂ →ₗ[ℂ] ℂ →₀ ℂ).restrictScalars ℝ).comp (ev L ρ)

theorem samples_apply (L : ℝ) (S : Finset ℂ) (f : 𝓓(win L, ℝ)) :
    samples L S f = ∑ ρ ∈ S, Finsupp.single ρ (hat L f ρ) := by
  simp [samples, ev_apply]

/-- **The samples carry `T` to multiplication by `ρ(1 − ρ)`**: `zeroSideT (samples f) = samples (T f)`. -/
theorem zeroSideT_samples (L : ℝ) (S : Finset ℂ) (f : 𝓓(win L, ℝ)) :
    Cvs.Zeta.ZeroSidePairingEigenvalues.zeroSideT (samples L S f) = samples L S (opT L f) := by
  rw [samples_apply, samples_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Cvs.Zeta.ZeroSidePairingEigenvalues.zeroSideT_single, hat_opT, Finsupp.smul_single, smul_eq_mul]

/-! ### RH -/

/-- **RH is `0 ≤ W(φ, φ)` on the form domain at every `x ≥ x₀`**, for any `x₀ ≥ 2`. -/
theorem rh_iff_forall_Bx_nonneg (x₀ : ℕ) (hx₀ : 2 ≤ x₀) :
    RiemannHypothesis ↔ ∀ x : ℕ, x₀ ≤ x → ∀ φ : Dom x, 0 ≤ Bx x φ φ := by
  rw [Cvs.WeilForm.WindowWeilCriterion.rh_iff_windowPos x₀ hx₀]
  refine forall₂_congr fun x _ => forall_congr' fun φ => ?_
  rw [show Bx x φ φ = _ from Cvs.WeilForm.SymmetricBilinearForm.QWbil_self _ _ _ φ]

end Cvs.WeilForm.WindowTestParseval
