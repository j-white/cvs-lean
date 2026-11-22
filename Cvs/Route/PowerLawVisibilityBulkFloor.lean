import Mathlib
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.L2a.EvenSectorReflectionBound
import Cvs.Route.EvenWindowBulkCoupling
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.SpectralChainThreeCut
import Cvs.Route.Visibility.ExtPairingRatesSubpoly
import Cvs.Route.Visibility.ShareBesselFromExtPairing
import Cvs.Route.Visibility.VisibilityClosingStep
import Cvs.Route.Visibility.VisibilityUnconditional
import Cvs.Route.Visibility.ZeroPairingVector
import Cvs.Route.WindowPositivityBulkCoupling
import Cvs.StepA.Edge.CaseInfinityJointRates
import Cvs.StepA.Edge.DbarTransplantHolds
import Cvs.StepA.Edge.DeepJointShare
import Cvs.StepA.Edge.DeepSetZeroSums
import Cvs.StepA.Edge.FiniteTopCorrectedClosing
import Cvs.StepA.Edge.FiniteTopGap
import Cvs.StepA.Edge.FreeInterpHolds
import Cvs.StepA.Edge.TransplantAngleHighZeros
import Cvs.StepA.Edge.WindowCoshTransformDuality
import Cvs.StepA.LowEigenvalueCountZeros
import Cvs.StepA.TopQuadruple
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin
import Cvs.WeilForm.CentredHodgeIndexWindow
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget
import Cvs.WeilForm.OrganisingIdentityGreen
import Cvs.WeilForm.PoleArchPrimeProblem
import Cvs.WeilForm.PrimeOperatorPathLawDeficit
import Cvs.WeilForm.ReflectionEvenPositivityRH
import Cvs.WeilForm.SelfConvolutionCosine
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WholeDomainUnification
import Cvs.WeilForm.WindowCircleIsometry
import Cvs.WeilForm.WindowRepresentative
import Cvs.Zeta.GaussKernel.DivisorWeightCoordinates
import Cvs.Zeta.GaussKernel.ZeroChain
import Cvs.Zeta.GaussKernel.ZetaZeroStatement
import Cvs.Zeta.WindowBudgetFactorTwo
import Cvs.Zeta.ZeroSideMoments
import Cvs.Zeta.ZeroSideMomentsConverge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Quantitative power-law `hV` up to `topDepth` and loss-tolerant bulk-floor equivalences

Off `RiemannHypothesis`, `EvenBulkFloor x (-C * (x : ℝ) ^ κ)` fails eventually for every `κ < topDepth`, yielding
zero-free strips from power-loss floors and two-sided equivalences with subpolynomial and mean-free-prime bulk bounds.
-/

noncomputable section

open Complex Real MeasureTheory Set Filter Topology Finset
open scoped InnerProductSpace
open Cvs.Zeta.GaussKernel.AdmissibleKernel (nonTrivialZeroSet)
open Cvs.StepA.Edge.DeepSetZeroSums (deepSet)

namespace Cvs.Route.PowerLawVisibilityBulkFloor
open Cvs.ZeroCounting

/-! ### 1. Monotonicity, witness form, unconditional Path-Law baseline, and `topDepth = 0 ↔ RiemannHypothesis` -/

/-- **Monotonicity of `EvenBulkFloor`** in the floor parameter. -/
theorem evenBulkFloor_mono {x : ℕ} {b₁ b₂ : ℝ} (hb : b₁ ≤ b₂)
    (h : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b₂) : Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x b₁ :=
  fun w hwE hwR => (mul_le_mul_of_nonneg_right hb (sq_nonneg ‖w‖)).trans (h w hwE hwR)

/-- **Unconditional Path-Law baseline floor on `Ev x ∩ (R₁ x)ᗮ`**: for every `x > 1`,
`EvenBulkFloor x (archSymbol 0 − atomBudget x x ⌈log₂ x⌉)` holds unconditionally. -/
theorem evenBulkFloor_archSymbol_sub_atomBudget {x : ℕ} (hx : 1 < x) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x
      (Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 - Cvs.PrimeOperator.atomBudget x x (Nat.clog 2 x)) := by
  intro w hwE _
  have hempty : {t : ℝ | |t| < 0} = ∅ := by
    ext t
    simp [not_lt_of_ge (abs_nonneg t)]
  have hlow : (∫ t in {t : ℝ | |t| < 0},
      Cvs.WeilForm.SelfConvolutionCosine.specDensity (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) t) ≤ 0 * ‖w‖ ^ 2 := by
    rw [hempty, setIntegral_empty, zero_mul]
  have h := Cvs.WeilForm.WindowCircleIsometry.Qx_even_ge_highBand_floor hx le_rfl
    (fun t _ => Cvs.WeilForm.Archimedean.SymbolMinimumAtOrigin.archSymbol_min_at_zero t) hwE hlow
  linarith

/-- **Unconditional Chebyshev upper bound on `partialSumHalf Λ N`**:
`partialSumHalf Λ N ≤ 2 (log 4 + 4) N^(1/2)` for every `N : ℕ`. -/
theorem partialSumHalf_vonMangoldt_le_rpow_half (N : ℕ) :
    Cvs.WeilForm.WholeDomainUnification.partialSumHalf ArithmeticFunction.vonMangoldt N
      ≤ 2 * (Real.log 4 + 4) * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hlog4 : 0 ≤ Real.log 4 + 4 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : Cvs.WeilForm.WholeDomainUnification.partialSumHalf ArithmeticFunction.vonMangoldt 0 = 0 := by
      simp [Cvs.WeilForm.WholeDomainUnification.partialSumHalf]
    rw [h0]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) _)
  · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbud := Cvs.Deficit.budget_le hN1
    rw [Nat.floor_natCast, Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons,
      ArithmeticFunction.map_zero, mul_zero, zero_add] at hbud
    have hsum : Cvs.WeilForm.WholeDomainUnification.partialSumHalf ArithmeticFunction.vonMangoldt N
        = ∑ k ∈ Finset.Ioc 0 N, (k : ℝ) ^ (-(1 : ℝ) / 2) * ArithmeticFunction.vonMangoldt k := by
      unfold Cvs.WeilForm.WholeDomainUnification.partialSumHalf
      have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        omega
      rw [hset]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (-(1 / 2 : ℝ)) = -(1 : ℝ) / 2 by ring, mul_comm]
    have hexp : ((1 : ℝ) / 2) = (1 / 2 : ℝ) := by ring
    rw [hexp] at hbud
    rw [hsum]
    linarith

/-- **Unconditional `O(x^(1/2))` bound on `atomBudget`**: for every `x > 1`,
`atomBudget x x ⌈log₂ x⌉ ≤ 4 (log 4 + 4) x^(1/2)`. -/
theorem atomBudget_le_rpow_half {x : ℕ} (hx : 1 < x) :
    Cvs.PrimeOperator.atomBudget x x (Nat.clog 2 x)
      ≤ 4 * (Real.log 4 + 4) * (x : ℝ) ^ (1 / 2 : ℝ) := by
  have hbud := Cvs.Route.SpectralChainThreeCut.atomBudget_le_chebPrimeBound hx (Nat.le_succ x) (Nat.le_succ _)
  unfold Cvs.Route.SpectralChainThreeCut.chebPrimeBound at hbud
  have h1 := partialSumHalf_vonMangoldt_le_rpow_half (x - 1)
  have h2 := partialSumHalf_vonMangoldt_le_rpow_half (Nat.sqrt (x - 1))
  have hlog4 : 0 ≤ Real.log 4 + 4 := by
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hx1 : ((x - 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le x 1) (by positivity)
  have hx2 : ((Nat.sqrt (x - 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast (Nat.sqrt_le_self (x - 1)).trans (Nat.sub_le x 1)) (by positivity)
  nlinarith

/-- **Unconditional `θ = 1/2` power-loss bulk floor**: for every `x > 1`,
`EvenBulkFloor x (-(|archSymbol 0| + 4 (log 4 + 4)) · x^(1/2))` holds unconditionally. -/
theorem evenBulkFloor_neg_rpow_half {x : ℕ} (hx : 1 < x) :
    Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x
      (-(|Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| + 4 * (Real.log 4 + 4)) * (x : ℝ) ^ (1 / 2 : ℝ)) := by
  refine evenBulkFloor_mono ?_ (evenBulkFloor_archSymbol_sub_atomBudget hx)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hx.le) (by positivity)
  have ha : -|Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| ≤ Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0 := neg_abs_le _
  have h0 : 0 ≤ |Cvs.WeilForm.Archimedean.ArchimedeanUnbounded.archSymbol 0| := abs_nonneg _
  have hbud := atomBudget_le_rpow_half hx
  nlinarith

/-- Under `RiemannHypothesis`, every nontrivial zero has `del ρ = 0`. -/
theorem del_eq_zero_of_rh (hRH : RiemannHypothesis) (ρ : nonTrivialZeroSet) :
    Cvs.GaussKernel.del ρ = 0 := by
  obtain ⟨hz, hre0, hre1⟩ := ρ.2
  have hre : (ρ : ℂ).re = 1 / 2 :=
    hRH (ρ : ℂ) hz
      (fun ⟨n, hn⟩ => by
        have hlt : ((ρ : ℂ)).re < 0 := by
          rw [hn]
          simp
          linarith
        linarith)
      (fun h1 => by
        rw [h1] at hre1
        norm_num at hre1)
  simp [Cvs.GaussKernel.del, hre]

/-- Under `RiemannHypothesis`, `topDepth = 0`. -/
theorem topDepth_eq_zero_of_rh (hRH : RiemannHypothesis) : Cvs.StepA.Edge.CaseInfinityJointRates.topDepth = 0 := by
  unfold Cvs.StepA.Edge.CaseInfinityJointRates.topDepth
  have h0 : (fun ρ : nonTrivialZeroSet => |Cvs.GaussKernel.del ρ|) = fun _ => 0 := by
    ext ρ
    rw [del_eq_zero_of_rh hRH ρ, abs_zero]
  rw [h0]
  by_cases hne : Nonempty nonTrivialZeroSet
  · exact ciSup_const
  · have : IsEmpty nonTrivialZeroSet := not_nonempty_iff.mp hne
    simp

/-! ### 2. Quantitative `hV`: power-law Rayleigh divergence up to `topDepth` -/

/-- **Power-law bulk-floor failure from `DeepJointShare` and `ShallowRate`**: an off-line zero `σ` with
`DeepJointShare σ D` and `ShallowRate σ D` forces `¬ EvenBulkFloor x (-c · x^{|del σ|})` at all large `x`. -/
theorem eventually_not_evenBulkFloor_rpow_of_joint {σ : nonTrivialZeroSet}
    (hσ : Cvs.GaussKernel.del σ ≠ 0) {D : ℕ → Finset nonTrivialZeroSet}
    (hJ : Cvs.StepA.Edge.DeepJointShare.DeepJointShare σ D) (hS : Cvs.StepA.Edge.DeepJointShare.ShallowRate σ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-c * (x : ℝ) ^ |Cvs.GaussKernel.del σ|) := by
  obtain ⟨s₀, hs₀, hJe⟩ := hJ
  have hre : (Cvs.ZeroCounting.zPoint σ).re ≠ 0 := by
    rw [Cvs.ZeroCounting.zPoint_re]
    exact Cvs.StepA.LowEigenvalueCountZeros.im_ne_zero σ
  have him : (Cvs.ZeroCounting.zPoint σ).im ≠ 0 := by
    rw [Cvs.ZeroCounting.zPoint_im]
    exact neg_ne_zero.2 hσ
  have habs : |(Cvs.ZeroCounting.zPoint σ).im| = |Cvs.GaussKernel.del σ| := by
    rw [Cvs.ZeroCounting.zPoint_im, abs_neg]
    rfl
  obtain ⟨β, hβ, hVlo⟩ := Cvs.StepA.Edge.DeepJointShare.exists_norm_sq_pairVec_ge hre him
  refine ⟨s₀ * β / 4, by positivity, ?_⟩
  filter_upwards [hJe, hS (s₀ ^ 2 / 2) (by positivity), hVlo, eventually_ge_atTop 14]
    with x h1 h2 h3 h14
  have hx := Cvs.Route.Visibility.VisibilityClosingStep.scale_of_ge h14
  set hx0 := Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx
  obtain ⟨hsum, hoff⟩ := h2 hx0
  have hQ := Cvs.StepA.Edge.DeepJointShare.Qx_wJoint_le hx (D x) σ hsum
  set w := Cvs.StepA.Edge.DeepJointShare.wJoint hx0 (D x) σ
  obtain ⟨hwE, hwR⟩ := Cvs.StepA.Edge.DeepJointShare.wJoint_mem hx0 (D x) σ
  have hV : β * (x : ℝ) ^ |Cvs.GaussKernel.del σ| ≤ ‖Cvs.StepA.Edge.DeepJointShare.Vσ hx0 σ‖ ^ 2 := by
    simpa only [habs] using h3 hx0
  have hw2 : s₀ * ‖Cvs.StepA.Edge.DeepJointShare.Vσ hx0 σ‖ ^ 2 ≤ ‖w‖ ^ 2 := h1 hx0
  have hlo : s₀ * β * (x : ℝ) ^ |Cvs.GaussKernel.del σ| ≤ ‖w‖ ^ 2 :=
    calc s₀ * β * (x : ℝ) ^ |Cvs.GaussKernel.del σ|
        = s₀ * (β * (x : ℝ) ^ |Cvs.GaussKernel.del σ|) := by ring
      _ ≤ s₀ * ‖Cvs.StepA.Edge.DeepJointShare.Vσ hx0 σ‖ ^ 2 := mul_le_mul_of_nonneg_left hV hs₀.le
      _ ≤ ‖w‖ ^ 2 := hw2
  have hxpow : 0 < (x : ℝ) ^ |Cvs.GaussKernel.del σ| := Real.rpow_pos_of_pos hx0 _
  have hw_pos : 0 < ‖w‖ ^ 2 := lt_of_lt_of_le (by positivity) hlo
  have hsq : s₀ ^ 2 * ‖Cvs.StepA.Edge.DeepJointShare.Vσ hx0 σ‖ ^ 4 ≤ ‖w‖ ^ 4 := by
    have hpow := pow_le_pow_left₀ (by positivity) hw2 2
    calc s₀ ^ 2 * ‖Cvs.StepA.Edge.DeepJointShare.Vσ hx0 σ‖ ^ 4 = (s₀ * ‖Cvs.StepA.Edge.DeepJointShare.Vσ hx0 σ‖ ^ 2) ^ 2 := by ring
      _ ≤ (‖w‖ ^ 2) ^ 2 := hpow
      _ = ‖w‖ ^ 4 := by ring
  have hW : ‖w‖ ^ 4 ≤ Cvs.StepA.TopQuadruple.quadWeight σ * ‖w‖ ^ 4 :=
    le_mul_of_one_le_left (by positivity) (Cvs.StepA.TopQuadruple.one_le_quadWeight σ)
  have hQle : Cvs.Route.WindowPositivityBulkCoupling.Qx x w ≤ -(1 / 2) * ‖w‖ ^ 4 := by linarith
  have hstrict : (s₀ * β / 4 * (x : ℝ) ^ |Cvs.GaussKernel.del σ|) * ‖w‖ ^ 2 < 1 / 2 * ‖w‖ ^ 4 := by
    have hlt1 : s₀ * β / 4 * (x : ℝ) ^ |Cvs.GaussKernel.del σ| < 1 / 2 * ‖w‖ ^ 2 := by linarith
    calc (s₀ * β / 4 * (x : ℝ) ^ |Cvs.GaussKernel.del σ|) * ‖w‖ ^ 2
        < (1 / 2 * ‖w‖ ^ 2) * ‖w‖ ^ 2 := mul_lt_mul_of_pos_right hlt1 hw_pos
      _ = 1 / 2 * ‖w‖ ^ 4 := by ring
  intro hfl
  have hge := hfl w hwE hwR
  linarith

set_option maxHeartbeats 1000000 in
/-- **Uniform top-band joint rates off `RiemannHypothesis`**: there is a band width `η₀ > 0` such that every zero `σ`
with `topDepth − η₀ < |del σ|` satisfies `DeepJointShare σ D` and `ShallowRate σ D` for a deep family `D`. -/
theorem exists_topBand_joint_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ σ : nonTrivialZeroSet,
      Cvs.StepA.Edge.CaseInfinityJointRates.topDepth - η₀ < |Cvs.GaussKernel.del σ| →
        Cvs.GaussKernel.del σ ≠ 0 ∧
          ∃ D : ℕ → Finset nonTrivialZeroSet,
            Cvs.StepA.Edge.DeepJointShare.DeepJointShare σ D ∧ Cvs.StepA.Edge.DeepJointShare.ShallowRate σ D := by
  have hm : (0 : ℝ) < 1 := one_pos
  have hX := Cvs.Route.Visibility.VisibilityUnconditional.sepData_one
  have hM := Cvs.Route.Visibility.VisibilityUnconditional.m1Prime_one_of_not_rh hRH
  have hT := Cvs.StepA.Edge.DbarTransplantHolds.dbarTransplant
  have hF := Cvs.StepA.Edge.FreeInterpHolds.freeInterp
  have hC := Cvs.Route.Visibility.VisibilityUnconditional.lemmaC
  set Θ := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth
  have hΘ0 := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_pos hRH
  have hΘh := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_le_half hRH
  set δD := Θ / 2
  have hδD0 : 0 < δD := by positivity
  have hδDh : δD < 1 / 2 := by simp only [δD]; linarith
  obtain ⟨ε₁, hε₁, Q₁, hQ₁, hMe⟩ := hM
  obtain ⟨αT, hαT, hT'⟩ := hT
  obtain ⟨αF, hαF, hF'⟩ := hF
  obtain ⟨αC, hαC, hC'⟩ := hC
  obtain ⟨κ, hκ, hCδ⟩ := hC' δD hδD0 hδDh
  set α := max αT (max αF αC)
  have hα : 0 < α := lt_max_of_lt_left hαT
  have hαT' : αT ≤ α := le_max_left _ _
  have hαF' : αF ≤ α := (le_max_left _ _).trans (le_max_right _ _)
  have hαC' : αC ≤ α := (le_max_right _ _).trans (le_max_right _ _)
  set ε₂ := min (min (δD / (16 * α)) (ε₁ / (8 * α))) (min (min (1 / (4 * α)) (Θ / 16)) (1 / 2))
  have hε₂0 : 0 < ε₂ := by positivity
  have he1 : ε₂ ≤ δD / (16 * α) := (min_le_left _ _).trans (min_le_left _ _)
  have he2 : ε₂ ≤ ε₁ / (8 * α) := (min_le_left _ _).trans (min_le_right _ _)
  have he3 : ε₂ ≤ 1 / (4 * α) := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have he4 : ε₂ ≤ Θ / 16 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have he5 : ε₂ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hαe1 : α * ε₂ ≤ δD / 16 :=
    (mul_le_mul_of_nonneg_left he1 hα.le).trans_eq (by field_simp)
  have hαe2 : α * ε₂ ≤ ε₁ / 8 :=
    (mul_le_mul_of_nonneg_left he2 hα.le).trans_eq (by field_simp)
  have hαe3 : α * ε₂ ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left he3 hα.le).trans_eq (by field_simp)
  have hTε : αT * ε₂ ≤ α * ε₂ := mul_le_mul_of_nonneg_right hαT' hε₂0.le
  have hFε : αF * ε₂ ≤ α * ε₂ := mul_le_mul_of_nonneg_right hαF' hε₂0.le
  have hCε : αC * ε₂ ≤ α * ε₂ := mul_le_mul_of_nonneg_right hαC' hε₂0.le
  obtain ⟨H, hH, Qc, hQc, hCe⟩ := hCδ ε₂ hε₂0 (by linarith)
  obtain ⟨C, hC0, hTe⟩ := hT' δD hδD0 hδDh ε₂ hε₂0 (by linarith) H hH
  set η₀ := min (min (ε₂ / 2) (ε₁ / 4)) (min (κ * ε₂ / 2) (Θ / 4))
  have hη₀ : 0 < η₀ := by positivity
  have hη1 : η₀ ≤ ε₂ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η₀ ≤ ε₁ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η₀ ≤ κ * ε₂ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη4 : η₀ ≤ Θ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η₀, hη₀, fun σ hσgt => ?_⟩
  set δ := |Cvs.GaussKernel.del σ|
  have hδ0 : 0 < δ := by linarith
  have hσ : Cvs.GaussKernel.del σ ≠ 0 := abs_pos.1 hδ0
  have hδD : δD ≤ δ := by simp only [δD]; linarith
  obtain ⟨β, hβ, hPI⟩ := hF' δD hδD0 hδDh ε₂ hε₂0 (by linarith) H hH σ hδD
  set g := δ / ‖Cvs.StepA.Edge.WindowCoshTransformDuality.wR σ‖
  have hg : g < 1 :=
    (div_lt_one (hδ0.trans (Cvs.StepA.Edge.CaseInfinityJointRates.abs_del_lt_norm_wR σ))).2 (Cvs.StepA.Edge.CaseInfinityJointRates.abs_del_lt_norm_wR σ)
  set r := (1 - g) ^ 2 * β ^ 2 / 8
  have hr : 0 < r := by
    have : 0 < 1 - g := by linarith
    positivity
  obtain ⟨K, hK, -⟩ := Cvs.StepA.Edge.CaseInfinityJointRates.extPairingRate_of hm hX σ
  have hm' : 2 * αT * ε₂ < 1 := by linarith
  have hShare := Cvs.StepA.Edge.CaseInfinityJointRates.freeShare_of_pointInterp hσ hβ hPI
  have hPair := Cvs.StepA.Edge.DeepJointShare.pairingRate_of_extPairingRate_offLine hσ (Finset.mem_singleton_self σ) hK
  have hAng := Cvs.StepA.Edge.CaseInfinityJointRates.angleBound_of hαT.le hC0 hε₂0 (by linarith) hm' hδD0 hH hX hTe
    (by linarith : 0 < r / 2)
  have hDeep := Cvs.StepA.Edge.DeepJointShare.deepJointShare_of_rates hShare hPair hAng
    (by dsimp only [r, g, δ] at hr ⊢; linarith)
  have hSh := Cvs.StepA.Edge.CaseInfinityJointRates.shallowRate_of hσ hαT.le hC0 hε₂0 (by linarith) hm' hδD0
    (by simp only [δD]; linarith) (by simp only [δD]; linarith) (by linarith) (by linarith)
    (by nlinarith) hH hX ⟨Q₁, hQ₁, hMe⟩ hTe ⟨Qc, hQc, hCe⟩
  exact ⟨hσ, fun x => deepSet δD (H x), hDeep, hSh⟩

/-- **Arbitrarily deep power-law `hV` off `RiemannHypothesis`**: for every `η > 0`, some off-line zero `σ` has
`topDepth − η < |del σ|` and forces `¬ EvenBulkFloor x (-c · x^{|del σ|})` at all large `x`. -/
theorem hV_rpow_exists_zero (hRH : ¬ RiemannHypothesis) {η : ℝ} (hη : 0 < η) :
    ∃ (σ : nonTrivialZeroSet) (c : ℝ), Cvs.GaussKernel.del σ ≠ 0 ∧
      Cvs.StepA.Edge.CaseInfinityJointRates.topDepth - η < |Cvs.GaussKernel.del σ| ∧ 0 < c ∧
        ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-c * (x : ℝ) ^ |Cvs.GaussKernel.del σ|) := by
  obtain ⟨η₀, hη₀, hband⟩ := exists_topBand_joint_of_not_rh hRH
  obtain ⟨σ, hgt⟩ := Cvs.StepA.Edge.CaseInfinityJointRates.exists_abs_del_gt hRH (lt_min hη hη₀)
  have h1 : Cvs.StepA.Edge.CaseInfinityJointRates.topDepth - η < |Cvs.GaussKernel.del σ| := by
    linarith [min_le_left η η₀]
  have h2 : Cvs.StepA.Edge.CaseInfinityJointRates.topDepth - η₀ < |Cvs.GaussKernel.del σ| := by
    linarith [min_le_right η η₀]
  obtain ⟨hdel, D, hJ, hS⟩ := hband σ h2
  obtain ⟨c, hc, hev⟩ := eventually_not_evenBulkFloor_rpow_of_joint hdel hJ hS
  exact ⟨σ, c, hdel, h1, hc, hev⟩

/-- **Quantitative `hV` up to `topDepth`**: off `RiemannHypothesis`, for every `κ < topDepth` and `C : ℝ`,
`EvenBulkFloor x (-C · x^κ)` fails at all sufficiently large `x`. -/
theorem hV_lt_topDepth (hRH : ¬ RiemannHypothesis) {κ : ℝ} (hκ : κ < Cvs.StepA.Edge.CaseInfinityJointRates.topDepth) (C : ℝ) :
    ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-C * (x : ℝ) ^ κ) := by
  obtain ⟨σ, c, -, hgt, hc, hev⟩ :=
    hV_rpow_exists_zero hRH (show 0 < (Cvs.StepA.Edge.CaseInfinityJointRates.topDepth - κ) / 2 by linarith)
  set δ := |Cvs.GaussKernel.del σ|
  have hκδ : 0 < δ - κ := by dsimp only [δ]; linarith
  have hgrow := (Cvs.Route.Visibility.ExtPairingRatesSubpoly.tendsto_natCast_rpow hκδ).eventually_ge_atTop (max C 0 / c)
  filter_upwards [hev, hgrow, eventually_ge_atTop 1] with x hnot hbig hx1 hfl
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
  have h1 : max C 0 ≤ c * (x : ℝ) ^ (δ - κ) := by
    rwa [div_le_iff₀ hc, mul_comm] at hbig
  have h2 : C * (x : ℝ) ^ κ ≤ c * (x : ℝ) ^ δ :=
    calc C * (x : ℝ) ^ κ ≤ max C 0 * (x : ℝ) ^ κ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
      _ ≤ c * (x : ℝ) ^ (δ - κ) * (x : ℝ) ^ κ :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _)
      _ = c * ((x : ℝ) ^ (δ - κ) * (x : ℝ) ^ κ) := by ring
      _ = c * (x : ℝ) ^ δ := by
          rw [← Real.rpow_add hx0]
          ring_nf
  exact hnot (evenBulkFloor_mono (by linarith) hfl)

/-! ### 3. Zero-free strips and two-sided loss-tolerant `↔ RiemannHypothesis` equivalences -/

/-- **Power-loss bulk floor bounds `topDepth`**: if `EvenBulkFloor x (-C · x^θ)` (`θ ≥ 0`) holds at infinitely
many `x`, then `topDepth ≤ θ`. -/
theorem topDepth_le_of_frequently_evenBulkFloor_neg_rpow {θ C : ℝ} (hθ : 0 ≤ θ)
    (hF : ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-C * (x : ℝ) ^ θ)) :
    Cvs.StepA.Edge.CaseInfinityJointRates.topDepth ≤ θ := by
  by_cases hRH : RiemannHypothesis
  · rw [topDepth_eq_zero_of_rh hRH]
    exact hθ
  · by_contra hge
    exact hF (hV_lt_topDepth hRH (lt_of_not_ge hge) C)

/-- **Quasi-RH zero-free strip from a power-loss bulk floor**: if `EvenBulkFloor x (-C · x^θ)` (`θ ≥ 0`) holds
at infinitely many `x`, every nontrivial zero satisfies `1/2 − θ ≤ Re ρ ≤ 1/2 + θ`. -/
theorem zeroFreeStrip_of_frequently_evenBulkFloor_neg_rpow {θ C : ℝ} (hθ : 0 ≤ θ)
    (hF : ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-C * (x : ℝ) ^ θ))
    (ρ : nonTrivialZeroSet) :
    1 / 2 - θ ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ 1 / 2 + θ := by
  have hle : |Cvs.GaussKernel.del ρ| ≤ θ :=
    (Cvs.StepA.Edge.CaseInfinityJointRates.abs_del_le_topDepth ρ).trans (topDepth_le_of_frequently_evenBulkFloor_neg_rpow hθ hF)
  rw [Cvs.GaussKernel.del, abs_le] at hle
  exact ⟨by linarith [hle.1], by linarith [hle.2]⟩

/-- **`RiemannHypothesis` ↔ `EvenBulkFloor x (-Q x)` frequently for some `SubPoly Q`**. -/
theorem rh_iff_exists_subPoly_evenBulkFloor :
    RiemannHypothesis ↔
      ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-Q x) := by
  constructor
  · intro hRH
    refine ⟨fun _ => 0, Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 0, ?_⟩
    exact (Cvs.Route.Visibility.VisibilityUnconditional.rh_iff_frequently_evenBulkFloor.mp hRH).mono fun x h => by simpa using h
  · rintro ⟨Q, hQ, hF⟩
    by_contra hRH
    have hΘ := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_pos hRH
    set ε := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth / 2
    have hε : 0 < ε := by positivity
    have hnot : ∀ᶠ x : ℕ in atTop, ¬ Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-Q x) := by
      filter_upwards [hQ ε hε,
        hV_lt_topDepth hRH (show ε < Cvs.StepA.Edge.CaseInfinityJointRates.topDepth by dsimp only [ε]; linarith) 1]
        with x hQx hVx hfl
      exact hVx (evenBulkFloor_mono (by linarith) hfl)
    exact hF hnot

/-- **`RiemannHypothesis` ↔ `EvenBulkFloor x (-x^ε)` frequently for every `ε > 0`**. -/
theorem rh_iff_subpoly_evenBulkFloor :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-(x : ℝ) ^ ε) := by
  constructor
  · intro hRH ε _
    exact (Cvs.Route.Visibility.VisibilityUnconditional.rh_iff_frequently_evenBulkFloor.mp hRH).mono fun x h =>
      evenBulkFloor_mono (by linarith [Real.rpow_nonneg (Nat.cast_nonneg x) ε]) h
  · intro h
    by_contra hRH
    have hΘ := Cvs.StepA.Edge.CaseInfinityJointRates.topDepth_pos hRH
    have hf := h (Cvs.StepA.Edge.CaseInfinityJointRates.topDepth / 2) (by positivity)
    have hev := hV_lt_topDepth hRH (show Cvs.StepA.Edge.CaseInfinityJointRates.topDepth / 2 < Cvs.StepA.Edge.CaseInfinityJointRates.topDepth by linarith) 1
    exact hf (hev.mono fun x hx => by simpa using hx)

/-- **`RiemannHypothesis` ↔ `EvenBulkFloor x (-C)` frequently for some constant `C : ℝ`**. -/
theorem rh_iff_bdd_evenBulkFloor :
    RiemannHypothesis ↔ ∃ C : ℝ, ∃ᶠ x : ℕ in atTop, Cvs.Route.EvenWindowBulkCoupling.EvenBulkFloor x (-C) := by
  constructor
  · intro hRH
    exact ⟨0, (Cvs.Route.Visibility.VisibilityUnconditional.rh_iff_frequently_evenBulkFloor.mp hRH).mono fun x h => by simpa using h⟩
  · rintro ⟨C, hF⟩
    exact rh_iff_exists_subPoly_evenBulkFloor.mpr ⟨fun _ => C, Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const C, hF⟩

/-! ### 4. Two-sided Green-energy sandwich and mean-free-prime / Path-Law SOS bulk equivalences -/

/-- **Upper half of the `[0, 4]` Green-energy sandwich on `Dom x`**:
`Qx x w ≤ archTerm (rep w) − meanFreePrimeTerm x ⌈log₂ x⌉ (rep w) + 4 ‖w‖²`. -/
theorem Qx_le_arch_sub_meanFreePrime_add_four (x : ℕ) (w : Cvs.Route.L1FloorFromBulkD0.Dom x) :
    Cvs.Route.WindowPositivityBulkCoupling.Qx x w
      ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - Cvs.WeilForm.OrganisingIdentityGreen.meanFreePrimeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + 4 * ‖w‖ ^ 2 := by
  rw [Cvs.WeilForm.OrganisingIdentityGreen.Qx_eq_green_add_arch_sub_meanFreePrime x w]
  linarith [Cvs.WeilForm.OrganisingIdentityGreen.windowGreenEnergy_rep_le_four_mul_norm_sq w]

/-- Under `RiemannHypothesis`, `meanFreePrimeTerm ≤ archTerm + 4 ‖w‖²` on `Ev x ∩ (R₁ x)ᗮ` at all `x ≥ 2`. -/
theorem meanFreePrime_le_arch_add_four_of_rh (hRH : RiemannHypothesis) {x : ℕ} (hx : 2 ≤ x)
    {w : Cvs.Route.L1FloorFromBulkD0.Dom x} (hwE : w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x) (hwR : w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ) :
    Cvs.WeilForm.OrganisingIdentityGreen.meanFreePrimeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) + 4 * ‖w‖ ^ 2 := by
  have h0 := (Cvs.Route.EvenWindowBulkCoupling.even_floor_coupling_zero_of_rh hRH hx).2.1 w hwE hwR
  have hup := Qx_le_arch_sub_meanFreePrime_add_four x w
  linarith

/-- **`RiemannHypothesis` ↔ subpolynomial-loss control of `meanFreePrimeTerm` by `archTerm` on `Ev x ∩ (R₁ x)ᗮ`**. -/
theorem rh_iff_meanFreePrime_le_arch_add_subPoly :
    RiemannHypothesis ↔
      ∃ Q : ℕ → ℝ, Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q ∧ ∃ᶠ x : ℕ in atTop, ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
        Cvs.WeilForm.OrganisingIdentityGreen.meanFreePrimeTerm x (Nat.clog 2 x) (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
          ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))) + Q x * ‖w‖ ^ 2 := by
  constructor
  · intro hRH
    refine ⟨fun _ => 4, Cvs.Route.Visibility.ExtPairingRatesSubpoly.subPoly_const 4,
      ((eventually_ge_atTop 2).mono fun x hx w hwE hwR => ?_).frequently⟩
    exact meanFreePrime_le_arch_add_four_of_rh hRH hx hwE hwR
  · rintro ⟨Q, hQ, hF⟩
    refine rh_iff_exists_subPoly_evenBulkFloor.mpr ⟨Q, hQ, hF.mono fun x hx => ?_⟩
    refine Cvs.WeilForm.OrganisingIdentityGreen.evenBulkFloor_of_meanFreePrime_le_arch fun w hwE hwR => ?_
    linarith [hx w hwE hwR]

/-- **Reflection-even Path-Law sum-of-squares lower bound on `Qx`**: on `Ev x` (`1 < x`),
`archTerm (rep w) − atomBudget · ‖w‖² + (atomSchurDiffForm + atomShortChainForm) ≤ Qx x w`. -/
theorem Qx_even_ge_arch_sub_atomBudget_add_pathLaw {x : ℕ} (hx : 1 < x)
    {w : Cvs.Route.L1FloorFromBulkD0.Dom x} (hwE : w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x) :
    Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        - Cvs.PrimeOperator.atomBudget x x (Nat.clog 2 x) * ‖w‖ ^ 2
        + (Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm x x (Nat.clog 2 x)
            (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm x x (Nat.clog 2 x)
            (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))))
      ≤ Cvs.Route.WindowPositivityBulkCoupling.Qx x w := by
  have hQ := Cvs.WeilForm.WindowCircleIsometry.Q_eq_pathLaw_schur hx x (Nat.clog 2 x) w
  have hpole := Cvs.WeilForm.WindowCircleIsometry.poleTerm_rep_nonneg_of_Uc_eq_zero (Real.log_natCast_nonneg x)
    (Cvs.WeilForm.CentredHodgeIndexWindow.Uc_eq_zero_of_mem_evenSub (Real.log_natCast_nonneg x) hwE)
  change Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
      - Cvs.PrimeOperator.atomBudget x x (Nat.clog 2 x) * ‖w‖ ^ 2
      + (Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm x x (Nat.clog 2 x)
          (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
        + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm x x (Nat.clog 2 x)
          (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x))))
    ≤ Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) w
  linarith

/-- **`RiemannHypothesis` from Path-Law SOS + `archTerm` covering `atomBudget` up to subpolynomial loss**
on `Ev x ∩ (R₁ x)ᗮ`. -/
theorem rh_of_pathLaw_schur_subPoly {Q : ℕ → ℝ} (hQ : Cvs.Route.Visibility.ExtPairingRatesSubpoly.SubPoly Q)
    (hF : ∃ᶠ x : ℕ in atTop, ∃ hx : 1 < x, ∀ w ∈ Cvs.WeilForm.ReflectionEvenPositivityRH.Ev x, w ∈ (Cvs.L2a.EvenSectorReflectionBound.R1 x)ᗮ →
      (Cvs.PrimeOperator.atomBudget x x (Nat.clog 2 x) - Q x) * ‖w‖ ^ 2
        ≤ Cvs.WeilForm.PoleArchPrimeProblem.archTerm (Cvs.WeilForm.WindowRepresentative.rep (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomSchurDiffForm x x (Nat.clog 2 x)
              (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))
          + Cvs.WeilForm.PrimeOperatorPathLawDeficit.atomShortChainForm x x (Nat.clog 2 x)
              (Cvs.WeilForm.WindowCircleIsometry.windowCircle hx (w : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log x)))) :
    RiemannHypothesis := by
  refine rh_iff_exists_subPoly_evenBulkFloor.mpr ⟨Q, hQ, hF.mono fun x ⟨hx, h⟩ w hwE hwR => ?_⟩
  have hlow := Qx_even_ge_arch_sub_atomBudget_add_pathLaw hx hwE
  have h1 := h w hwE hwR
  linarith

end Cvs.Route.PowerLawVisibilityBulkFloor

end
