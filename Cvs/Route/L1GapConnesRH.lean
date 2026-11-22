import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesResidualFixedScale
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Route.JointGapConnesFromL1
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# RH from L1's gap at Connes' vectors

`L1Gap x`: a lower bound `Q ≥ −s‖·‖²` on the whole form domain, a floor `μ` on a continuous even hyperplane, and
`K(L1 + s‖o‖²)/‖e‖² + (K − 1)s < μ` at `K = √x log x`. At infinitely many integer `x` it gives RH (Cvs.Route.JointGapConnesFromL1, Cvs.Route.JointGapAtConnesVectors).
-/

noncomputable section

open Real Filter Matrix Topology
open scoped InnerProductSpace

namespace Cvs.Route.L1GapConnesRH
open Cvs.ZeroCounting

open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.JointGapConnesFromL1 (connesL1 connesEven connesOdd)

/-- **L1's gap at scale `x`**, the joint-gap condition with the Rayleigh value replaced by L1. -/
def L1Gap (x : ℕ) : Prop :=
  ∃ (hx : c0W ≤ 2 * π * x) (s μ : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)),
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    √(x : ℝ) * Real.log x * ((connesL1 x + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
        / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2) + (√(x : ℝ) * Real.log x - 1) * s < μ

/-- `1 ≤ √x log x` for `x ≥ 3`. -/
theorem one_le_K {x : ℕ} (hx : 3 ≤ x) : 1 ≤ √(x : ℝ) * Real.log x := by
  have hx3 : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hs : 1 ≤ √(x : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hl : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  nlinarith

/-- **L1's gap gives the joint gap at every large mode order**, at large `x`. -/
theorem eventually_jointGap_of_L1Gap :
    ∀ᶠ x : ℕ in atTop, L1Gap x → ∀ᶠ N in atTop,
      Cvs.Route.GroundRouteJointGap.JointGap x (Nat.clog 2 x) (Real.log x) N (√(x : ℝ) * Real.log x)
        (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) := by
  filter_upwards [Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_coefficientMass_pos, eventually_ge_atTop 3] with x hm hx3 hgap
  obtain ⟨hx, s, μ, η, hneg, hfloor, hlt⟩ := hgap
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have he : 0 < ‖connesEven h80‖ := by
    have h2 := Cvs.Route.JointGapConnesFromL1.norm_connesEven_sq h80
    have hL := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80)
    have : 0 < ‖connesEven h80‖ ^ 2 := by rw [h2]; positivity
    exact lt_of_le_of_ne (norm_nonneg (connesEven h80)) fun h0 => by rw [← h0] at this; simp at this
  exact Cvs.Route.JointGapConnesFromL1.eventually_jointGap x hx (one_le_K hx3) hneg η hfloor he hlt

open Classical in
/-- The mode order chosen at a real scale: one past which the joint gap holds, when there is one. -/
def Nsel (y : ℝ) : ℕ :=
  if h : ∃ N₀ : ℕ, ∀ N ≥ N₀, Cvs.Route.GroundRouteJointGap.JointGap ⌊y⌋₊ (Nat.clog 2 ⌊y⌋₊) (Real.log y) N (√y * Real.log y)
      (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) y) then Classical.choose h else 0

/-- The truncation: at least Connes' threshold and the chosen order. -/
def Nf (y : ℝ) : ℕ := max (Cvs.Route.JointGapAtConnesVectors.connesThreshold y) (Nsel y)

/-- **RH from L1's gap**: `L1Gap x` at infinitely many integers `x` gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_L1Gap (h : ∃ᶠ x : ℕ in atTop, L1Gap x) : RiemannHypothesis := by
  refine Cvs.Route.JointGapAtConnesVectors.riemannHypothesis_of_jointGap_connes (fun y => ⌊y⌋₊) (fun y => Nat.clog 2 ⌊y⌋₊)
    ⟨Nf, Eventually.of_forall fun y => le_max_left _ _, ?_⟩
  have hn : ∃ᶠ n : ℕ in atTop, Cvs.Route.GroundRouteJointGap.JointGap ⌊(n : ℝ)⌋₊ (Nat.clog 2 ⌊(n : ℝ)⌋₊) (Real.log n) (Nf n)
      (√(n : ℝ) * Real.log n) (Cvs.Approximant.ConnesVectorRealScale.connesVec Nf n) := by
    refine (h.and_eventually eventually_jointGap_of_L1Gap).mono fun n ⟨hg, himp⟩ => ?_
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (himp hg)
    have hfl : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
    have hex : ∃ N₀ : ℕ, ∀ N ≥ N₀, Cvs.Route.GroundRouteJointGap.JointGap ⌊(n : ℝ)⌋₊ (Nat.clog 2 ⌊(n : ℝ)⌋₊) (Real.log n) N
        (√(n : ℝ) * Real.log n) (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) n) := by
      rw [hfl]; exact ⟨N₀, hN₀⟩
    have hsel : Nsel n = Classical.choose hex := by unfold Nsel; rw [dite_eq_left hex]
    exact Classical.choose_spec hex (Nf n) (hsel ▸ le_max_right _ _)
  exact tendsto_natCast_atTop_atTop.frequently hn

end Cvs.Route.L1GapConnesRH
