import Mathlib
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ExteriorFactorMTwo
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.WindowLaplaceUPairing
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.ZeroSideMoments

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# (M1′) at every top depth from the window transform

The window transform `F_u` of Cvs.Route.Visibility.WindowLaplaceUPairing is entire, so the sub-mean value on discs of radius `r₀` about `±(½ − ρ̄)` and
the local zero count bound the `U` sum by `A(δ + r₀)/r₀²` times the log-weighted line energy of `F_u` on
`|Re w| ≤ δ + r₀` (`WinBesselDisc`), with no condition `δ + r₀ < ½`. A log-weighted energy rate `x^{|σ|+ν}` on `R₁`
(`WinLogReg ν`) then gives `M1Prime m` for every `m > ν` at every value of `Θ'`, in particular at `Θ' = ½`.
-/

noncomputable section

open Real MeasureTheory Filter Set
open scoped InnerProductSpace
open Cvs.Route.L1FloorFromBulkD0 (Dom)
open Cvs.L2a.EvenSectorReflectionBound (R1)
open Cvs.Route.Visibility.VisibilityClosingStep (ueVec)
open Cvs.StepA.Edge.FiniteTopGap (mult)
open Cvs.Route.Visibility.ExtPairingRatesSubpoly (SubPoly)
open Cvs.StepA.Edge.CaseInfinityJointRates (M1Prime topDepth)
open Cvs.Route.Visibility.WindowLaplaceUPairing (winLaplace)
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)

namespace Cvs.Route.Visibility.MOnePrimeTopDepth
open Cvs.ZeroCounting

/-! ### The top depth at `½` -/

/-- `Θ' ≥ 0`. -/
theorem topDepth_nonneg : 0 ≤ topDepth :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- `Θ' ≤ ½`. -/
theorem topDepth_le_half' : topDepth ≤ 1 / 2 :=
  Real.iSup_le (fun ρ => Cvs.GaussKernel.del_bdd ρ) (by norm_num)

/-! ### The named inputs -/

/-- The log-weighted line energy `∫ ‖F_u(σ + ig)‖² log(|g| + 7/2) dg` of the window transform. -/
def winLogEnergy {x : ℕ} (u : Dom x) (σ : ℝ) : ℝ :=
  ∫ g : ℝ, ‖winLaplace u (σ + g * Complex.I)‖ ^ 2 * Real.log (|g| + 7 / 2)

/-- **The window Bessel disc bound** with constant `A`: for zeros with `|δ_ρ| ≤ δ` and `0 < r₀ < ½`, a bound `M` on
the log-weighted line energies of `F_u` for `|σ| ≤ δ + r₀` gives a summable `U` sum at most `A(δ + r₀)/r₀² · M`. -/
def WinBesselDisc (A : ℝ) : Prop :=
  ∀ (x : ℕ) (hx0 : (0 : ℝ) < x) (u : Dom x) (δ r₀ : ℝ), 0 ≤ δ → 0 < r₀ → r₀ < 1 / 2 →
    (∀ ρ : nonTrivialZeroSet, |Cvs.GaussKernel.del ρ| ≤ δ) → ∀ M : ℝ,
    (∀ σ ∈ Icc (-(δ + r₀)) (δ + r₀),
      Integrable (fun g : ℝ => ‖winLaplace u (σ + g * Complex.I)‖ ^ 2 * Real.log (|g| + 7 / 2))
        ∧ winLogEnergy u σ ≤ M) →
    (Summable fun ρ : nonTrivialZeroSet => mult ρ * ⟪u, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2)
      ∧ ∑' ρ : nonTrivialZeroSet, mult ρ * ⟪u, ueVec hx0 (Cvs.ZeroCounting.zPoint ρ)⟫_ℝ ^ 2
        ≤ A * (δ + r₀) / r₀ ^ 2 * M

/-- **The log-weighted energy rate on `R₁` with loss `ν`**: `∫ ‖F_r(σ + ig)‖² log(|g| + 7/2) dg ≤
Q(x)x^{|σ| + ν}‖r‖²` for `r ∈ R₁` and `|σ| ≤ 1` at all large `x`, `Q` subpolynomial. -/
def WinLogReg (ν : ℝ) : Prop :=
  ∃ Q : ℕ → ℝ, SubPoly Q ∧ ∀ᶠ x : ℕ in atTop, ∀ r ∈ R1 x, ∀ σ : ℝ, |σ| ≤ 1 →
    Integrable (fun g : ℝ => ‖winLaplace r (σ + g * Complex.I)‖ ^ 2 * Real.log (|g| + 7 / 2))
      ∧ winLogEnergy r σ ≤ Q x * (x : ℝ) ^ (|σ| + ν) * ‖r‖ ^ 2

/-! ### (M1′) -/

/-- **(M1′) from the window transform**: the window Bessel disc bound and the log-weighted energy rate with loss
`ν < m` give `M1Prime m`, at every top depth. -/
theorem m1Prime_of_win {A ν m : ℝ} (hA : 0 ≤ A) (hB : WinBesselDisc A) (hR : WinLogReg ν) (hνm : ν < m) :
    M1Prime m := by
  obtain ⟨Q, hQ, hR⟩ := hR
  set δ := topDepth
  have hδ0 : 0 ≤ δ := topDepth_nonneg
  have hδ1 : δ ≤ 1 / 2 := topDepth_le_half'
  set r₀ := min ((m - ν) / 2) (1 / 4)
  have hr₀ : 0 < r₀ := lt_min (by linarith) (by norm_num)
  have hr₁ : r₀ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hr₂ : r₀ ≤ (m - ν) / 2 := min_le_left _ _
  set C := A * (δ + r₀) / r₀ ^ 2
  have hC : 0 ≤ C := by have : 0 ≤ δ + r₀ := by linarith
                        positivity
  refine ⟨m - ν - r₀, by linarith, fun x => C * max (Q x) 0,
    (Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const C).mul (Cvs.Route.Visibility.ExteriorFactorMTwo.subPoly_max_zero hQ) (Eventually.of_forall fun _ => hC)
      (Eventually.of_forall fun _ => le_max_right _ _), ?_⟩
  filter_upwards [hR, eventually_ge_atTop 1] with x hx hx1 hx0 r hr
  have hx1' : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hM : ∀ σ ∈ Icc (-(δ + r₀)) (δ + r₀),
      Integrable (fun g : ℝ => ‖winLaplace r (σ + g * Complex.I)‖ ^ 2 * Real.log (|g| + 7 / 2))
        ∧ winLogEnergy r σ ≤ max (Q x) 0 * (x : ℝ) ^ (δ + r₀ + ν) * ‖r‖ ^ 2 := by
    intro σ hσ
    have hσ' : |σ| ≤ δ + r₀ := abs_le.2 hσ
    obtain ⟨h1, h2⟩ := hx r hr σ (by linarith)
    refine ⟨h1, h2.trans ?_⟩
    have hp : (x : ℝ) ^ (|σ| + ν) ≤ (x : ℝ) ^ (δ + r₀ + ν) :=
      Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
    have hp0 : 0 ≤ (x : ℝ) ^ (|σ| + ν) := Real.rpow_nonneg (by linarith) _
    gcongr
    · exact le_max_left _ _
  obtain ⟨h1, h2⟩ := hB x hx0 r δ r₀ hδ0 hr₀ hr₁ Cvs.StepA.Edge.CaseInfinityJointRates.abs_del_le_topDepth _ hM
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [show δ + m - (m - ν - r₀) = δ + r₀ + ν by ring]
  simp only [C]
  ring

end Cvs.Route.Visibility.MOnePrimeTopDepth

end
