import Mathlib
import Cvs.Approximant.ConnesFormTruncation
import Cvs.Approximant.ConnesResidualFixedScale
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Approximant.SpineSubspace
import Cvs.Finite.DiscreteTwoGap
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationQuadraticForm
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.L2a.L1WindowFromFloor
import Cvs.L2a.L1WindowFullSpanProlate
import Cvs.L2a.ProlateFamilySpine
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Route.EvenHyperplaneFloorCompress
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapFloorNearPositivity
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Xi.EImageWindowPoisson

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The joint gap at Connes' vector from L1, without the Rayleigh value

`connesVec` truncates the even part `e` of Connes' class `k`; L1 (Cvs.L2a.L1WindowFullSpanProlate) bounds `Q(k) = Q(e) + Q(o)`, so `Q ≥ −s‖·‖²`
on the whole domain gives `Q(e) ≤ L1 + s‖o‖²`. The truncated Rayleigh values tend to `Q(e)/‖e‖²`, so a continuous
even-hyperplane floor `μ > K(L1 + s‖o‖²)/‖e‖² + (K − 1)s` gives `JointGap` at every large mode order (Cvs.Route.EvenHyperplaneFloorCompress).
-/

noncomputable section

open MeasureTheory Set Real Filter Matrix Topology Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.SlepianEvenOrdering Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex Cvs.Approximant.DeepIndexSpineSpan
open scoped InnerProductSpace

namespace Cvs.Route.JointGapConnesFromL1
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx mode negI)
open Cvs.L2a.ProlateFamilySpine (kOf bOf)
open Cvs.L2a.WindowChainInputsProlate (c0W kapFX)

/-- Connes' singleton coefficient on `S = {1}`. -/
def one₁ : ({1} : Finset ℕ) → ℝ := fun _ => 1

/-- **L1 for Connes' profile**: `L1WindowFullSpanProlate`'s `L1bound · N` at `c = 2πx` for `S = {1}`, `a = 1`. -/
def connesL1 (x : ℕ) : ℝ :=
  Cvs.L2a.L1WindowFromFloor.L1bound (2 * π * x) (kapFX x) (1 / 2) (bOf (2 * π * x) one₁)
      (fun i => muR (2 * π * x) (kOf i)) (fun i => rung (2 * π * x) (kOf i))
      (fun i => rung₁ (2 * π * x) (kOf i)) (fun i => rung₂ (2 * π * x) (kOf i))
    * Cvs.L2a.L1WindowFromFloor.tailN (2 * π * x) (bOf (2 * π * x) one₁) (fun i => rung (2 * π * x) (kOf i))

/-- The even part of Connes' class. -/
def connesEven {x : ℕ} (hx : 80 ≤ 2 * π * x) : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  Cvs.WeilForm.EvenOddSplitForm.evenPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)

/-- The odd part of Connes' class. -/
def connesOdd {x : ℕ} (hx : 80 ≤ 2 * π * x) : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x) :=
  Cvs.WeilForm.EvenOddSplitForm.oddPart (Real.log_natCast_nonneg x) (Cvs.Approximant.CosineColumnTailPairing.connesClass hx)

/-- **L1 on Connes' class**: `Q(k) ≤ L1bound · N` at every `x` with `c₀^W ≤ 2πx`. -/
theorem Q_connesClass_le (x : ℕ) (hx : c0W ≤ 2 * π * x) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (Cvs.Approximant.CosineColumnTailPairing.connesClass (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx))
      ≤ connesL1 x := by
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have h1 : ∀ j ∈ ({1} : Finset ℕ), 1 ≤ j ∧ j < x := fun j hj => by
    rw [Finset.mem_singleton.mp hj]
    exact ⟨le_rfl, by exact_mod_cast Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80⟩
  unfold Cvs.Approximant.CosineColumnTailPairing.connesClass
  rw [Cvs.Approximant.SpineSubspace.Q_ofFun, Cvs.Approximant.SpineSubspace.weilForm_kG]
  exact Cvs.L2a.L1WindowFullSpanProlate.L1_window_full x hx h1 one₁ ⟨⟨1, Finset.mem_singleton_self 1⟩, one_ne_zero⟩

/-- **The even part's form from a lower bound on the whole domain**: `Q(e) ≤ Q(k) + s‖o‖²`. -/
theorem Q_evenPart_le {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) {s : ℝ}
    (hneg : ∀ φ : Cvs.WeilForm.FormDomain.formDomain hL, -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL P R φ) (k : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (Cvs.WeilForm.EvenOddSplitForm.evenPart hL k) ≤ Cvs.WeilForm.InfimumAttainedSphere.Q hL P R k + s * ‖Cvs.WeilForm.EvenOddSplitForm.oddPart hL k‖ ^ 2 := by
  have h := Cvs.WeilForm.EvenOddSplitForm.weilQW_split hL P R k
  have ho := hneg (Cvs.WeilForm.EvenOddSplitForm.oddPart hL k)
  change Cvs.WeilForm.InfimumAttainedSphere.Q hL P R k = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (Cvs.WeilForm.EvenOddSplitForm.evenPart hL k) + Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (Cvs.WeilForm.EvenOddSplitForm.oddPart hL k) at h
  linarith

/-- **The even Connes part's Rayleigh value** is below `(L1 + s‖o‖²)/‖e‖²`. -/
theorem Q_connesEven_le (x : ℕ) (hx : c0W ≤ 2 * π * x) {s : ℝ}
    (hneg : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ) :
    Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx))
      ≤ connesL1 x + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2 :=
  (Q_evenPart_le _ _ _ hneg _).trans (by
    have := Q_connesClass_le x hx
    unfold connesOdd
    linarith)

/-! ### The truncated Rayleigh values -/

/-- **Parseval for cosine classes**: `‖modeMap f‖² = log x · f⬝f` for even `f`. -/
theorem norm_modeMap_sq {x : ℕ} (hx0 : (0 : ℝ) < x) (hx1 : (1 : ℝ) < x) (N : ℕ) (f : Idx N → ℝ)
    (hfe : ∀ i, f (negI N i) = f i) :
    ‖Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f‖ ^ 2 = Real.log x * (f ⬝ᵥ f) := by
  change ‖((Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x))
    : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))‖ ^ 2 = _
  rw [Cvs.WeilForm.OddCapTransfer.sq_norm_eq_integral_rep]
  have hae := (Cvs.WeilForm.WindowRepresentative.ae_eq_rep _).symm.trans (Cvs.Approximant.CosineColumnTailPairing.coe_modeClass_ae hx0 N f)
  refine (integral_congr_ae (hae.mono fun s hs => congrArg (fun z : ℝ => z ^ 2) hs)).trans ?_
  exact Cvs.Route.GroundRouteJointGap.integral_modeSum_sq (Real.log_pos hx1) N hfe

/-- The Weil form of a difference of classes. -/
private theorem Q_sub {L : ℝ} (hL : 0 ≤ L) (P R : ℕ) (u v : Cvs.WeilForm.FormDomain.formDomain hL) :
    Cvs.WeilForm.InfimumAttainedSphere.Q hL P R (u - v)
      = Cvs.WeilForm.InfimumAttainedSphere.Q hL P R u - 2 * Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R v u + Cvs.WeilForm.InfimumAttainedSphere.Q hL P R v := by
  rw [← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self, ← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self hL P R u, ← Cvs.WeilForm.SymmetricBilinearForm.QWbil_self hL P R v]
  have h1 := LinearMap.BilinForm.sub_left (B₁ := Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R) u v (u - v)
  have h2 := LinearMap.BilinForm.sub_right (B₁ := Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R) u u v
  have h3 := LinearMap.BilinForm.sub_right (B₁ := Cvs.WeilForm.SymmetricBilinearForm.QWbil hL P R) v u v
  rw [h1, h2, h3]
  rw [(Cvs.WeilForm.SymmetricBilinearForm.QWbil_isSymm hL P R).eq u v]
  ring

/-- **The truncated Connes classes converge in form and norm** to the even part. -/
theorem tendsto_trunc {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Tendsto (fun N => Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x)
        (Cvs.Approximant.ConnesFormTruncation.connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N)) atTop
        (𝓝 (Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (connesEven hx))) ∧
      Tendsto (fun N => ‖Cvs.Approximant.ConnesFormTruncation.connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N‖ ^ 2) atTop (𝓝 (‖connesEven hx‖ ^ 2)) := by
  have hT : ∀ N, Cvs.Approximant.ConnesFormTruncation.connesTrunc (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N = connesEven hx - Cvs.Approximant.ConnesFormTruncation.connesError hx N := by
    intro N; exact (sub_sub_cancel (connesEven hx) _).symm
  have herr : Tendsto (fun N => Cvs.Approximant.ConnesFormTruncation.connesError hx N) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero (E := Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x))
      (f := fun N => Cvs.Approximant.ConnesFormTruncation.connesError hx N)).mpr (Cvs.Approximant.ConnesFormTruncation.tendsto_connesError_norm hx)
  refine ⟨?_, ?_⟩
  · have h := ((tendsto_const_nhds (x := Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (connesEven hx))).sub
      ((Cvs.Approximant.ConnesFormTruncation.tendsto_QWbil_connesError_zero hx (connesEven hx)).const_mul 2)).add
      (Cvs.Approximant.ConnesFormTruncation.tendsto_Q_connesError_zero hx)
    simp only [mul_zero, sub_zero, add_zero] at h
    exact h.congr fun N => by rw [hT N, Q_sub]
  · have hr := Cvs.Approximant.ConnesFormTruncation.tendsto_connesError_norm hx
    have hlo : Tendsto (fun N => ‖connesEven hx‖ - ‖Cvs.Approximant.ConnesFormTruncation.connesError hx N‖) atTop
        (𝓝 ‖connesEven hx‖) := by simpa using (tendsto_const_nhds (x := ‖connesEven hx‖)).sub hr
    have hhi : Tendsto (fun N => ‖connesEven hx‖ + ‖Cvs.Approximant.ConnesFormTruncation.connesError hx N‖) atTop
        (𝓝 ‖connesEven hx‖) := by simpa using (tendsto_const_nhds (x := ‖connesEven hx‖)).add hr
    have h2 : Tendsto (fun N => ‖connesEven hx - Cvs.Approximant.ConnesFormTruncation.connesError hx N‖) atTop
        (𝓝 ‖connesEven hx‖) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
        (fun N => norm_sub_norm_le (E := Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) _ _)
        (fun N => norm_sub_le (E := Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)) _ _)
    have h := h2.pow 2
    exact h.congr fun N => congrArg (fun z => ‖z‖ ^ 2) (hT N).symm

/-- **The even part's norm is the complete coefficient mass**: `‖e‖² = log x · coefficientMass x`. -/
theorem norm_connesEven_sq {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    ‖connesEven hx‖ ^ 2 = Real.log x * Cvs.Approximant.ConnesResidualFixedScale.coefficientMass x := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have h := (Cvs.Approximant.ConnesResidualFixedScale.tendsto_coefficientMass hx).const_mul (Real.log x)
  refine tendsto_nhds_unique (tendsto_trunc hx).2 (h.congr fun N => ?_)
  unfold Cvs.Approximant.ConnesFormTruncation.connesTrunc
  rw [norm_modeMap_sq _ hx1 N _ (Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N)]

/-- **The truncated Rayleigh values tend to `Q(e)/‖e‖²`**, when `e ≠ 0`. -/
theorem tendsto_rayleigh {x : ℕ} (hx : 80 ≤ 2 * π * x) (he : 0 < ‖connesEven hx‖) :
    Tendsto (fun N => Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x ⬝ᵥ
        (Cvs.Finite.TruncationQuadraticForm.M x (Nat.clog 2 x) (Real.log x) (mode N) *ᵥ Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x)) atTop
      (𝓝 (Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) (connesEven hx) / ‖connesEven hx‖ ^ 2)) := by
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  have hL := Real.log_pos hx1
  obtain ⟨hQ, hn⟩ := tendsto_trunc hx
  have he2 : ‖connesEven hx‖ ^ 2 ≠ 0 := by positivity
  refine (hQ.div hn he2).congr' ?_
  filter_upwards [hn.eventually (lt_mem_nhds (by positivity : (0 : ℝ) < ‖connesEven hx‖ ^ 2))] with N hN
  have hξe := Cvs.Approximant.ConnesVectorRealScale.connesCoef_even x N
  simp only [Pi.div_apply]
  unfold Cvs.Approximant.ConnesFormTruncation.connesTrunc at hN ⊢
  rw [norm_modeMap_sq hx0 hx1 N _ hξe] at hN ⊢
  rw [Cvs.Approximant.CosineColumnTailPairing.Q_modeMap hx0 hx1 x (Nat.clog 2 x) N _ hξe]
  set ξ := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N with hξ
  have hξ0 : ξ ⬝ᵥ ξ ≠ 0 := fun h0 => by rw [h0, mul_zero] at hN; exact lt_irrefl _ hN
  have hv : Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x = (√(ξ ⬝ᵥ ξ))⁻¹ • ξ := by
    unfold Cvs.Approximant.ConnesVectorRealScale.connesVec
    simp only
    rw [ite_eq_right hξ0]
  rw [hv, Cvs.Finite.DiscreteTwoGap.quad_smul, inv_pow, Real.sq_sqrt (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' ξ)]
  field_simp

/-! ### The joint gap -/

/-- A lower bound on the whole form domain bounds the even mode matrix below. -/
theorem matrix_neg_le {x : ℕ} (hx0 : (0 : ℝ) < x) (hx1 : (1 : ℝ) < x) (P R N : ℕ) {s : ℝ}
    (hneg : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) P R φ)
    (f : Idx N → ℝ) (hfe : ∀ i, f (negI N i) = f i) :
    -s * (f ⬝ᵥ f) ≤ f ⬝ᵥ (Cvs.Finite.TruncationQuadraticForm.M P R (Real.log x) (mode N) *ᵥ f) := by
  have h := hneg (Cvs.Approximant.CosineColumnTailPairing.modeMap hx0 N f)
  rw [norm_modeMap_sq hx0 hx1 N f hfe, Cvs.Approximant.CosineColumnTailPairing.Q_modeMap hx0 hx1 P R N f hfe] at h
  have hL := Real.log_pos hx1
  nlinarith

/-- **The joint gap at Connes' vector from L1**: with `Q ≥ −s‖·‖²` on the whole form domain and a floor `μ` on a
continuous even hyperplane, `K(L1 + s‖o‖²)/‖e‖² + (K − 1)s < μ` gives `JointGap` at `K` against Connes' vector at
every large mode order. -/
theorem eventually_jointGap (x : ℕ) (hx : c0W ≤ 2 * π * x) {K s μ : ℝ} (hK : 1 ≤ K)
    (hneg : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      -s * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ)
    (η : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x))
    (hfloor : ∀ φ : Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x),
      Cvs.WeilForm.WindowReflectionSymmetry.reflD (Real.log_natCast_nonneg x) φ = φ → ⟪η, φ⟫_ℝ = 0 →
        μ * ‖φ‖ ^ 2 ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ)
    (he : 0 < ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖)
    (hgap : K * ((connesL1 x + s * ‖connesOdd (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2)
        / ‖connesEven (Cvs.Approximant.SpineSubspace.scale80_of_c0W hx)‖ ^ 2) + (K - 1) * s < μ) :
    ∀ᶠ N in atTop, Cvs.Route.GroundRouteJointGap.JointGap x (Nat.clog 2 x) (Real.log x) N K (Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x) := by
  have h80 := Cvs.Approximant.SpineSubspace.scale80_of_c0W hx
  have hx1 := Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale h80
  have hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale h80
  have hL := Real.log_pos hx1
  set e := connesEven h80 with hed
  set C₀ := (connesL1 x + s * ‖connesOdd h80‖ ^ 2) / ‖e‖ ^ 2 with hC₀
  set q := Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) e / ‖e‖ ^ 2 with hqd
  have he2 : 0 < ‖e‖ ^ 2 := by positivity
  have hqC : q ≤ C₀ := div_le_div_of_nonneg_right (Q_connesEven_le x hx hneg) he2.le
  have hqs : -s ≤ q := by
    rw [hqd, le_div_iff₀ he2]; exact hneg e
  -- a ceiling strictly between
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
  filter_upwards [(tendsto_rayleigh h80 he).eventually (gt_mem_nhds (show q < C by linarith))] with N hN
  refine Cvs.Route.EvenHyperplaneFloorCompress.jointGap_of_continuous_even_hyperplane hL hK η hfloor _
    (Cvs.Approximant.ConnesVectorRealScale.connesVec_even (fun _ => N) x) (Cvs.Approximant.ConnesVectorRealScale.connesVec_dotProduct_self (fun _ => N) x) hN.le ?_ hCμ hKC.le
  exact Cvs.Route.JointGapFloorNearPositivity.neg_le_groundLam hL fun f hf => matrix_neg_le hx0 hx1 x (Nat.clog 2 x) N hneg f hf

end Cvs.Route.JointGapConnesFromL1
