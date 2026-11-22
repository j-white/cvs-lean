import Mathlib
import Cvs.Approximant.ConnesCoefficientsNonvanishing
import Cvs.Approximant.ConnesResidualFixedScale
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Route.EvenHyperplaneFloorCompress
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapAtConnesVectors
import Cvs.Route.JointGapConnesFromL1
import Cvs.Route.JointGapFloorNearPositivity
import Cvs.Route.L1GapConnesRH
import Cvs.WeilForm.EvenOddSplitForm
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
# RH from L1's gap, parametric in the bound on Connes' class

`L1GapL L x` is `L1GapConnesRH`'s `L1Gap x` with `connesL1 x` replaced by any `L x` bounding `Q(k)` on Connes' class `k`.
At infinitely many integer `x` it gives RH.
-/

noncomputable section

open MeasureTheory Set Real Filter Matrix Topology
open scoped InnerProductSpace

namespace Cvs.Route.L1GapParametricRH
open Cvs.ZeroCounting

open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.JointGapConnesFromL1 (connesEven connesOdd)

/-- **L1's gap at scale `x` against a bound `L x`**, `L1GapConnesRH`'s `L1Gap` with `connesL1 x` replaced by `L x`. -/
def L1GapL (L : ℕ → ℝ) (x : ℕ) : Prop :=
  ∃ (hx : c0W ≤ 2 * π * x) (s μ : ℝ) (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)),
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    (∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) ∧
    √(x : ℝ) * Real.log x * ((L x + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
        / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2) + (√(x : ℝ) * Real.log x - 1) * s < μ

/-- **The joint gap at Connes' vector from any bound `B ≥ Q(k)`**, `JointGapConnesFromL1`'s `eventually_jointGap` with `B` for L1. -/
theorem eventually_jointGap (x : ℕ) (hx : c0W ≤ 2 * π * x) {B K s μ : ℝ} (hK : 1 ≤ K)
    (hB : Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
      (Cvs.Approximant.CosineColumnTailPairing.connesClass (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)) ≤ B)
    (hneg : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ)
    (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x))
    (hfloor : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ)
    (he : 0 < ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖)
    (hgap : K * ((B + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
        / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2) + (K - 1) * s < μ) :
    ∀ᶠ N in atTop, Cvs.Route.GroundRouteJointGap.JointGap x (Nat.clog 2 x) (Real.log x) N K (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) := by
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale h80
  have hL := Real.log_pos hx1
  set e := connesEven h80 with hed
  set C₀ := (B + s * ‖connesOdd h80‖ ^ 2) / ‖e‖ ^ 2 with hC₀
  set q := Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) e / ‖e‖ ^ 2 with hqd
  have he2 : 0 < ‖e‖ ^ 2 := by positivity
  have hQe : Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) e ≤ B + s * ‖connesOdd h80‖ ^ 2 :=
    (Cvs.Route.JointGapConnesFromL1.Q_evenPart_le _ _ _ hneg _).trans (by unfold connesOdd; linarith)
  have hqC : q ≤ C₀ := div_le_div_of_nonneg_right hQe he2.le
  have hqs : -s ≤ q := by
    rw [hqd, le_div_iff₀ he2]; exact hneg e
  set δ := (μ - (K * C₀ + (K - 1) * s)) / (2 * K) with hδ
  have hK0 : 0 < K := by linarith
  have hδ0 : 0 < δ := div_pos (by linarith) (by linarith)
  set C := C₀ + δ with hCd
  have hKC : K * C + (K - 1) * s < μ := by
    have : K * δ = (μ - (K * C₀ + (K - 1) * s)) / 2 := by rw [hδ]; field_simp
    nlinarith
  have hCμ : C < μ := by
    have hCs : 0 ≤ C + s := by linarith
    nlinarith [mul_nonneg (show 0 ≤ K - 1 by linarith) hCs]
  filter_upwards [(Cvs.Route.JointGapConnesFromL1.tendsto_rayleigh h80 he).eventually (gt_mem_nhds (show q < C by linarith))] with N hN
  refine Cvs.Route.EvenHyperplaneFloorCompress.jointGap_of_continuous_even_hyperplane hL hK η hfloor _
    (Cvs.Approximant.ConnesVectorRealScale.connesVec_even (fun _ => N) x) (Cvs.Approximant.ConnesVectorRealScale.connesVec_dotProduct_self (fun _ => N) x) hN.le ?_ hCμ hKC.le
  exact Cvs.Route.JointGapFloorNearPositivity.neg_le_groundLam hL fun f hf => Cvs.Route.JointGapConnesFromL1.matrix_neg_le hx0 hx1 x (Nat.clog 2 x) N hneg f hf

/-- **`L1GapL` gives the joint gap at every large mode order**, at large `x`. -/
theorem eventually_jointGap_of_L1GapL {L : ℕ → ℝ}
    (hL : ∀ x : ℕ, ∀ hx : c0W ≤ 2 * π * x,
      Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.CosineColumnTailPairing.connesClass (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)) ≤ L x) :
    ∀ᶠ x : ℕ in atTop, L1GapL L x → ∀ᶠ N in atTop,
      Cvs.Route.GroundRouteJointGap.JointGap x (Nat.clog 2 x) (Real.log x) N (√(x : ℝ) * Real.log x)
        (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) := by
  filter_upwards [Cvs.Approximant.ConnesCoefficientsNonvanishing.eventually_coefficientMass_pos, eventually_ge_atTop 3] with x hm hx3 hgap
  obtain ⟨hx, s, μ, η, hneg, hfloor, hlt⟩ := hgap
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have he : 0 < ‖connesEven h80‖ := by
    have h2 := Cvs.Route.JointGapConnesFromL1.norm_connesEven_sq h80
    have hl := Real.log_pos (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80)
    have : 0 < ‖connesEven h80‖ ^ 2 := by rw [h2]; positivity
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg (connesEven h80)) (by simpa using this)
  exact eventually_jointGap x hx (Cvs.Route.L1GapConnesRH.one_le_K hx3) (hL x hx) hneg η hfloor he hlt

/-- **RH from `L1GapL`**: with `L` bounding `Q` on Connes' class, `L1GapL L x` at infinitely many integers `x` gives
the Riemann hypothesis. -/
theorem riemannHypothesis_of_L1GapL {L : ℕ → ℝ}
    (hL : ∀ x : ℕ, ∀ hx : c0W ≤ 2 * π * x,
      Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.CosineColumnTailPairing.connesClass (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)) ≤ L x)
    (h : ∃ᶠ x : ℕ in atTop, L1GapL L x) : RiemannHypothesis := by
  refine Cvs.Route.JointGapAtConnesVectors.riemannHypothesis_of_jointGap_connes (fun y => ⌊y⌋₊) (fun y => Nat.clog 2 ⌊y⌋₊)
    ⟨Cvs.Route.L1GapConnesRH.Nf, Eventually.of_forall fun y => le_max_left _ _, ?_⟩
  have hn : ∃ᶠ n : ℕ in atTop, Cvs.Route.GroundRouteJointGap.JointGap ⌊(n : ℝ)⌋₊ (Nat.clog 2 ⌊(n : ℝ)⌋₊) (Real.log n) (Cvs.Route.L1GapConnesRH.Nf n)
      (√(n : ℝ) * Real.log n) (Cvs.Approximant.ConnesVectorRealScale.connesVec Cvs.Route.L1GapConnesRH.Nf n) := by
    refine (h.and_eventually (eventually_jointGap_of_L1GapL hL)).mono fun n ⟨hg, himp⟩ => ?_
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (himp hg)
    have hfl : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
    have hex : ∃ N₀ : ℕ, ∀ N ≥ N₀, Cvs.Route.GroundRouteJointGap.JointGap ⌊(n : ℝ)⌋₊ (Nat.clog 2 ⌊(n : ℝ)⌋₊) (Real.log n) N
        (√(n : ℝ) * Real.log n) (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) n) := by
      rw [hfl]; exact ⟨N₀, hN₀⟩
    have hsel : Cvs.Route.L1GapConnesRH.Nsel n = Classical.choose hex := by unfold Cvs.Route.L1GapConnesRH.Nsel; rw [dite_eq_left hex]
    exact Classical.choose_spec hex (Cvs.Route.L1GapConnesRH.Nf n) (hsel ▸ le_max_right _ _)
  exact tendsto_natCast_atTop_atTop.frequently hn

/-- `L1GapConnesRH`'s `L1Gap` is `L1GapL connesL1`. -/
theorem l1Gap_iff (x : ℕ) : Cvs.Route.L1GapConnesRH.L1Gap x ↔ L1GapL Cvs.Route.JointGapConnesFromL1.connesL1 x := Iff.rfl

end Cvs.Route.L1GapParametricRH
