import Mathlib
import Cvs.Approximant.ConnesErrorColumn
import Cvs.Approximant.ConnesVectorRealScale
import Cvs.Approximant.CosineColumnTailPairing
import Cvs.Approximant.DeepIndexSpineSpan
import Cvs.Approximant.SpineCouplingTailPairing
import Cvs.Finite.SymmetricModeSet
import Cvs.Finite.TruncationZeroFreeOffAxes
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullTailConvergence
import Cvs.L2a.FullTailWeilFormLimit
import Cvs.L2a.PlaneCorrelationL2
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.WindowFormTailLimit
import Cvs.Route.GroundRouteJointGap
import Cvs.Route.JointGapFromResidual
import Cvs.Upstream.SymmetricMatrixBottom
import Cvs.WeilForm.CubicTailSeparatedKernel
import Cvs.WeilForm.EImageRadical
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.PoleTermDilationMean
import Cvs.WeilForm.SeparatedArchDilationPairing
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.ThetaFormWindowIdentification
import Cvs.WeilForm.ThetaSpaceParseval
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The whole physical cubic correction column

Physical cosine tests have exactly the logarithmic coefficient energy.
A uniform bound on even unit tests controls the entire even coefficient column
and its orthogonally centered projection.
-/

noncomputable section

open Real Set MeasureTheory Matrix Finset

namespace Cvs.WeilForm.PhysicalCubicCorrectionColumn
open Cvs.ZeroCounting

open Cvs.Finite.SymmetricModeSet (Idx negI)

/-- A tame theta test belongs to physical L² on the line. -/
theorem memLp_of_tame {F : ℝ → ℝ} {a b : ℝ} (hF : Cvs.L2a.WindowFormTailLimit.Tame F a b) :
    MemLp F 2 volume := by
  obtain ⟨M, hM⟩ := hF.bdd
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hM 0)
  refine (memLp_two_iff_integrable_sq hF.meas.aestronglyMeasurable).mpr ?_
  apply Cvs.WeilForm.EImageRadical.integrable_of_bound_support (hF.meas.pow_const 2)
    (K := M ^ 2) (p := a) (q := b)
  · intro θ
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (F θ)) hM0).mpr (hM θ)
  · intro θ hθ
    simp only [hF.supp θ hθ, zero_pow (by omega : 2 ≠ 0)]

/-- The physical cosine test is square integrable. -/
theorem memLp_modeTest {x : ℕ} (hx0 : (0 : ℝ) < x) (N : ℕ) (f : Idx N → ℝ) :
    MemLp (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) 2 volume :=
  memLp_of_tame (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N f)

/-- Log scaling preserves the energy of a positive-supported physical test. -/
theorem integral_logScale_sq {F : ℝ → ℝ} (hF : ∀ θ ≤ 0, F θ = 0) :
    ∫ s, Cvs.L2a.TailLogScaleTest.logScale F s ^ 2 = ∫ θ, F θ ^ 2 := by
  have h := Cvs.WeilForm.ThetaFormWindowIdentification.selfConvolution_logScale_log F (k := 1) one_pos
  simp only [Cvs.Zeta.Explicit.Weil.selfConvolution, Real.log_one, add_zero,
    Real.sqrt_one, one_mul] at h
  have he : ∫ θ in Ioi (0 : ℝ), F θ ^ 2 = ∫ θ, F θ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    simp only [Set.mem_Ioi, not_lt] at hθ
    simp only [hF θ hθ, zero_pow (by omega : 2 ≠ 0)]
  simpa only [← sq, he] using h

/-- An even physical cosine test has energy `log x` times its coefficient mass. -/
theorem integral_modeTest_sq {x : ℕ} (hx1 : (1 : ℝ) < x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i) :
    ∫ θ, Cvs.Approximant.CosineColumnTailPairing.modeTest x N f θ ^ 2 = Real.log x * (f ⬝ᵥ f) := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have ht := Cvs.Approximant.CosineColumnTailPairing.tame_modeTest hx0 N f
  have hs : ∀ θ ≤ 0, Cvs.Approximant.CosineColumnTailPairing.modeTest x N f θ = 0 := by
    intro θ hθ
    exact ht.supp θ (fun h => (one_div_pos.mpr hx0).not_ge (h.1.trans hθ))
  rw [← integral_logScale_sq hs,
    ← integral_sub_right_eq_self (fun s => Cvs.L2a.TailLogScaleTest.logScale (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) s ^ 2)
      (Real.log x)]
  calc
    ∫ s, Cvs.L2a.TailLogScaleTest.logScale (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) (s - Real.log x) ^ 2
        = ∫ s, Cvs.Finite.TruncationZeroFreeOffAxes.modeSum (Real.log x) (Cvs.Finite.SymmetricModeSet.mode N) f s ^ 2 := by
          apply integral_congr_ae
          filter_upwards [Cvs.Approximant.CosineColumnTailPairing.fv_modeTest_ae N f] with s hs
          exact congrArg (fun t : ℝ => t ^ 2) hs
    _ = _ := Cvs.Route.GroundRouteJointGap.integral_modeSum_sq (Real.log_pos hx1) N hf

/-- The physical L² norm of an even cosine test is its exact coefficient energy. -/
theorem norm_modeTest_toLp {x : ℕ} (hx1 : (1 : ℝ) < x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i) :
    ‖(memLp_modeTest (lt_trans zero_lt_one hx1) N f).toLp (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)‖
      = √(Real.log x * (f ⬝ᵥ f)) := by
  let hF := memLp_modeTest (lt_trans zero_lt_one hx1) N f
  have he : ‖hF.toLp (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)‖ ^ 2 = Real.log x * (f ⬝ᵥ f) := by
    rw [Cvs.L2a.PlaneCorrelationL2.norm_sq_eq_integral]
    calc
      ∫ θ, (hF.toLp (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f)) θ ^ 2
          = ∫ θ, Cvs.Approximant.CosineColumnTailPairing.modeTest x N f θ ^ 2 := by
            apply integral_congr_ae
            filter_upwards [hF.coeFn_toLp] with θ hθ
            rw [hθ]
      _ = _ := integral_modeTest_sq hx1 N f hf
  rw [← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Even unit-test bounds control the squared mass of the whole even column. -/
theorem column_sq_le_of_unit_pairing {ι : Type*} [Fintype ι]
    (σ : ι → ι) (u : ι → ℝ) (hu : ∀ i, u (σ i) = u i) (C : ℝ)
    (hC : ∀ f : ι → ℝ, (∀ i, f (σ i) = f i) → (∑ i, f i ^ 2 = 1) →
      |u ⬝ᵥ f| ≤ C) : ∑ i, u i ^ 2 ≤ C ^ 2 := by
  let m := u ⬝ᵥ u
  have hm0 : 0 ≤ m := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' u
  have hsum : ∑ i, u i ^ 2 = m := by simp only [m, dotProduct, sq]
  rw [hsum]
  by_cases hm : m = 0
  · rw [hm]
    exact sq_nonneg _
  · have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
    let t := (Real.sqrt m)⁻¹
    let f := t • u
    have ht : t ^ 2 * m = 1 := by
      dsimp [t]
      rw [inv_pow, Real.sq_sqrt hm0, inv_mul_cancel₀ hm]
    have hf : ∀ i, f (σ i) = f i := by
      intro i
      simp only [f, Pi.smul_apply, smul_eq_mul, hu]
    have hunit : ∑ i, f i ^ 2 = 1 := by
      simp only [f, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [hsum, ht]
    have hb := hC f hf hunit
    have he : u ⬝ᵥ f = Real.sqrt m := by
      change u ⬝ᵥ (t • u) = _
      rw [dotProduct_smul, smul_eq_mul]
      change t * m = _
      dsimp [t]
      field_simp [(Real.sqrt_pos.mpr hmpos).ne']
      nlinarith [Real.sq_sqrt hm0]
    rw [he, abs_of_nonneg (Real.sqrt_nonneg m)] at hb
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg m) hb 2
    rwa [Real.sq_sqrt hm0] at hsq

/-- Orthogonal centering preserves any whole-column unit-test budget. -/
theorem centered_column_sq_le_of_unit_pairing {ι : Type*} [Fintype ι]
    (σ : ι → ι) (u α : ι → ℝ) (hu : ∀ i, u (σ i) = u i) (C : ℝ)
    (hC : ∀ f : ι → ℝ, (∀ i, f (σ i) = f i) → (∑ i, f i ^ 2 = 1) →
      |u ⬝ᵥ f| ≤ C) :
    ∑ i, Cvs.Approximant.ConnesErrorColumn.center u α i ^ 2 ≤ C ^ 2 := by
  have hc : ∑ i, Cvs.Approximant.ConnesErrorColumn.center u α i ^ 2 ≤ ∑ i, u i ^ 2 := by
    simpa only [dotProduct, sq] using Cvs.Approximant.ConnesErrorColumn.center_sq_le u α
  exact hc.trans (column_sq_le_of_unit_pairing σ u hu C hC)

/-- A measurable right tail bounded by `K/θ` belongs to physical L². -/
theorem memLp_of_right_tail_bound {F : ℝ → ℝ} (hm : Measurable F)
    (hs : ∀ θ ≤ 1, F θ = 0) {K : ℝ}
    (hK : ∀ θ, 0 < θ → |F θ| ≤ K / θ) : MemLp F 2 volume := by
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr ?_
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
    (Cvs.L2a.FullTailConvergence.integrableOn_sq_of_le hm hK)
  intro θ hθ
  by_contra h
  have ht : θ ≤ 1 := not_lt.mp h
  exact hθ (by simp only [hs θ ht, zero_pow (by omega : 2 ≠ 0)])

/-- A twice differentiable profile gives a physically square-integrable full Poisson tail. -/
theorem memLp_fullTail {g g₁ g₂ : ℝ → ℝ} {c : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1)) (hc : 0 < c) :
    MemLp (Cvs.L2a.FullTailConvergence.fullTail (Cvs.L2a.AngularProlateTailPositive.psi c g)) 2 volume :=
  memLp_of_right_tail_bound (Cvs.L2a.FullTailConvergence.measurable_fullTail hg hg₁ hg₂c hc)
    (fun _ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ)
    (fun _ hθ => Cvs.L2a.FullTailConvergence.abs_fullTail_le hg hg₁ hg₂c hc hθ)

/-- The actual regularized Connes tail is measurable. -/
theorem measurable_connesTail {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    Measurable (Cvs.Approximant.CosineColumnTailPairing.connesTail x) := by
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, _, _⟩ :=
    Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx) (fun _ => 1)
  obtain ⟨H₁, H₂, hH, hH₁, hH₂c⟩ := Cvs.WeilForm.SeparatedArchDilationPairing.regProfile_derivative_data hg hg₁ hg₂c
  exact Cvs.L2a.FullTailConvergence.measurable_fullTail hH hH₁ hH₂c (by linarith)

/-- The actual regularized Connes tail belongs to physical L². -/
theorem memLp_connesTail {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    MemLp (Cvs.Approximant.CosineColumnTailPairing.connesTail x) 2 volume := by
  obtain ⟨G₁, G₂, hg, hg₁, hg₂c, _, _⟩ :=
    Cvs.Approximant.SpineCouplingTailPairing.spine_profile_data hx (Cvs.Approximant.CosineColumnTailPairing.singleton_lt_of_scale hx) (fun _ => 1)
  obtain ⟨H₁, H₂, hH, hH₁, hH₂c⟩ := Cvs.WeilForm.SeparatedArchDilationPairing.regProfile_derivative_data hg hg₁ hg₂c
  exact memLp_fullTail hH hH₁ hH₂c (by linarith)

/-- Finite coefficients map linearly to their actual physical cosine tests. -/
def modeTestMap (x N : ℕ) : (Idx N → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun := Cvs.Approximant.CosineColumnTailPairing.modeTest x N
  map_add' f g := by
    funext θ
    simp only [Cvs.Approximant.CosineColumnTailPairing.modeTest, Cvs.Approximant.CosineColumnTailPairing.pullTest, Cvs.Approximant.CosineColumnTailPairing.cosineSum]
    by_cases hθ : θ ∈ Icc (Real.exp (-Real.log x)) 1
    · simp only [indicator_of_mem hθ, Pi.add_apply, add_mul,
        Finset.sum_add_distrib, mul_add]
    · simp only [indicator_of_notMem hθ, Pi.add_apply, zero_add]
  map_smul' c f := by
    funext θ
    simp only [Cvs.Approximant.CosineColumnTailPairing.modeTest, Cvs.Approximant.CosineColumnTailPairing.pullTest, Cvs.Approximant.CosineColumnTailPairing.cosineSum]
    by_cases hθ : θ ∈ Icc (Real.exp (-Real.log x)) 1
    · simp only [indicator_of_mem hθ, Pi.smul_apply, smul_eq_mul, mul_assoc,
        ← Finset.mul_sum, RingHom.id_apply]
      ring
    · simp only [indicator_of_notMem hθ, Pi.smul_apply, smul_eq_mul, mul_zero]

/-- An even physical cosine test is the sum of its actual signed coordinate tests. -/
theorem modeTest_eq_sum_rows (x N : ℕ) (f : Idx N → ℝ)
    (hf : ∀ i, f (negI N i) = f i) :
    Cvs.Approximant.CosineColumnTailPairing.modeTest x N f = ∑ i, f i • Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i) := by
  change modeTestMap x N f = _
  calc
    modeTestMap x N f = modeTestMap x N (∑ i, f i • Cvs.Approximant.CosineColumnTailPairing.cosineRow N i) := by
      rw [Cvs.Approximant.ConnesErrorColumn.sum_smul_cosineRow N f hf]
    _ = _ := by simp only [map_sum, map_smul]; rfl

/-- The cubic correction paired with an actual physical cosine test. -/
def cubicPairing (x N : ℕ) (f : Idx N → ℝ) : ℝ :=
  ∫ p, Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair (Cvs.Approximant.CosineColumnTailPairing.connesTail x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) p
    ∂Cvs.WeilForm.CubicTailSeparatedKernel.leftVolume.prod Cvs.WeilForm.CubicTailSeparatedKernel.rightVolume

/-- The complete cubic correction column in the actual signed cosine coordinates. -/
def cubicColumn (x N : ℕ) (i : Idx N) : ℝ :=
  cubicPairing x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)

/-- The cubic correction column is even. -/
theorem cubicColumn_even (x N : ℕ) (i : Idx N) :
    cubicColumn x N (negI N i) = cubicColumn x N i := by
  rw [cubicColumn, Cvs.Approximant.ConnesErrorColumn.cosineRow_neg]
  rfl

/-- Each actual cubic pairing has the same dimension-independent physical budget. -/
theorem abs_cubicPairing_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i) :
    |cubicPairing x N f| ≤ π / 2 *
      ‖(memLp_connesTail hx).toLp (Cvs.Approximant.CosineColumnTailPairing.connesTail x)‖ *
      √(Real.log x * (f ⬝ᵥ f)) := by
  have h := Cvs.WeilForm.CubicTailSeparatedKernel.abs_integral_kernelPair_le (measurable_connesTail hx)
    (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f).meas
    (memLp_connesTail hx) (memLp_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
  change |cubicPairing x N f| ≤ _ at h
  rwa [norm_modeTest_toLp (Cvs.Approximant.CosineColumnTailPairing.one_lt_of_scale hx) N f hf] at h

/-- The actual cubic correction pairing is the dot product with its entire even column. -/
theorem cubicPairing_eq_dot {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (f : Idx N → ℝ) (hf : ∀ i, f (negI N i) = f i) :
    cubicPairing x N f = cubicColumn x N ⬝ᵥ f := by
  have hi (i : Idx N) : Integrable
      (Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair (Cvs.Approximant.CosineColumnTailPairing.connesTail x) (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)))
      (Cvs.WeilForm.CubicTailSeparatedKernel.leftVolume.prod Cvs.WeilForm.CubicTailSeparatedKernel.rightVolume) :=
    Cvs.WeilForm.CubicTailSeparatedKernel.integrable_kernelPair (measurable_connesTail hx)
      (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N _).meas
      (memLp_connesTail hx) (memLp_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N _)
  unfold cubicPairing
  calc
    _ = ∫ p, ∑ i, f i * Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair (Cvs.Approximant.CosineColumnTailPairing.connesTail x)
        (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)) p
          ∂Cvs.WeilForm.CubicTailSeparatedKernel.leftVolume.prod Cvs.WeilForm.CubicTailSeparatedKernel.rightVolume := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [Cvs.WeilForm.CubicTailSeparatedKernel.kernelPair, modeTest_eq_sum_rows x N f hf, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    _ = ∑ i, f i * cubicColumn x N i := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hi i).const_mul (f i))]
      simp only [integral_const_mul, cubicColumn, cubicPairing]
    _ = _ := by
      unfold dotProduct
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The whole cubic column has a fixed-scale budget independent of mode order. -/
theorem cubicColumn_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    ∑ i, cubicColumn x N i ^ 2 ≤
      (π / 2 * ‖(memLp_connesTail hx).toLp (Cvs.Approximant.CosineColumnTailPairing.connesTail x)‖ * √(Real.log x)) ^ 2 := by
  apply column_sq_le_of_unit_pairing (negI N) (cubicColumn x N)
    (cubicColumn_even x N)
  intro f hf hunit
  rw [← cubicPairing_eq_dot hx N f hf]
  have hm : f ⬝ᵥ f = 1 := by simpa only [dotProduct, sq] using hunit
  simpa only [hm, mul_one] using abs_cubicPairing_le hx N f hf

/-- The centered cubic column obeys the same dimension-independent budget. -/
theorem centered_cubicColumn_sq_le {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (α : Idx N → ℝ) :
    ∑ i, Cvs.Approximant.ConnesErrorColumn.center (cubicColumn x N) α i ^ 2 ≤
      (π / 2 * ‖(memLp_connesTail hx).toLp (Cvs.Approximant.CosineColumnTailPairing.connesTail x)‖ * √(Real.log x)) ^ 2 := by
  have hc : ∑ i, Cvs.Approximant.ConnesErrorColumn.center (cubicColumn x N) α i ^ 2 ≤ ∑ i, cubicColumn x N i ^ 2 := by
    simpa only [dotProduct, sq] using Cvs.Approximant.ConnesErrorColumn.center_sq_le (cubicColumn x N) α
  exact hc.trans (cubicColumn_sq_le hx N)

/-- The physical kernel pairing is exactly the original actual cubic dilation correction. -/
theorem cubicPairing_eq_integral {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (f : Idx N → ℝ) :
    cubicPairing x N f = ∫ r in Ioi (1 : ℝ),
      Cvs.WeilForm.PoleTermDilationMean.dilR (Cvs.Approximant.CosineColumnTailPairing.modeTest x N f) (Cvs.Approximant.CosineColumnTailPairing.connesTail x) r / (r * (r ^ 2 - 1)) := by
  unfold cubicPairing
  symm
  apply Cvs.WeilForm.CubicTailSeparatedKernel.integral_cubic_eq_kernelPair (measurable_connesTail hx)
    (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f).meas
    (memLp_connesTail hx) (memLp_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f)
  · exact fun _ hθ => Cvs.L2a.FullTailWeilFormLimit.fullTail_of_le_one _ hθ
  · intro θ hθ
    exact (Cvs.Approximant.CosineColumnTailPairing.tame_modeTest (Cvs.Approximant.SpineCouplingTailPairing.hx0_of_scale hx) N f).supp θ
      (fun hm => hθ.not_ge hm.2)

/-- The actual prime-sampling column after its full continuous mean is removed. -/
def discrepancyColumn (x N : ℕ) (i : Idx N) : ℝ :=
  (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
    Cvs.WeilForm.ThetaSpaceParseval.dil (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)) (Cvs.Approximant.CosineColumnTailPairing.connesTail x) n)
    - Cvs.WeilForm.ThetaSpaceParseval.poleP (Cvs.Approximant.CosineColumnTailPairing.connesTail x) *
      Cvs.WeilForm.ThetaSpaceParseval.poleM (Cvs.Approximant.CosineColumnTailPairing.modeTest x N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i))

/-- The actual prime-minus-mean column is even. -/
theorem discrepancyColumn_even (x N : ℕ) (i : Idx N) :
    discrepancyColumn x N (negI N i) = discrepancyColumn x N i := by
  rw [discrepancyColumn, Cvs.Approximant.ConnesErrorColumn.cosineRow_neg]
  rfl

/-- The complete actual tail column is its arithmetic discrepancy plus the bounded cubic column. -/
theorem tailColumn_eq_discrepancy_add_cubic {x : ℕ} (hx : 80 ≤ 2 * π * x) (N : ℕ) :
    Cvs.Approximant.ConnesErrorColumn.tailColumn x N = discrepancyColumn x N + cubicColumn x N := by
  funext i
  have h := Cvs.WeilForm.SeparatedArchDilationPairing.QWbil_connesClass_modeMap_eq_cubic hx N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)
  rw [Cvs.Approximant.CosineColumnTailPairing.QWbil_connesClass_modeMap hx N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i),
    ← cubicPairing_eq_integral hx N (Cvs.Approximant.CosineColumnTailPairing.cosineRow N i)] at h
  exact h

/-- Orthogonal centering is additive in the column. -/
theorem center_add {ι : Type*} [Fintype ι] (u v α : ι → ℝ) :
    Cvs.Approximant.ConnesErrorColumn.center (u + v) α = Cvs.Approximant.ConnesErrorColumn.center u α + Cvs.Approximant.ConnesErrorColumn.center v α := by
  funext i
  simp only [Cvs.Approximant.ConnesErrorColumn.center, add_dotProduct, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, add_div]
  ring

/-- The actual matrix residual separates exactly into centered discrepancy, bounded cubic correction,
and its vanishing truncation column. -/
theorem connes_residual_eq_discrepancy_cubic_error {x : ℕ}
    (hx : 80 ≤ 2 * π * x) (N : ℕ)
    (hs : Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ⬝ᵥ Cvs.Approximant.ConnesVectorRealScale.connesCoef x N ≠ 0) :
    let α := Cvs.Approximant.ConnesVectorRealScale.connesCoef x N
    let v := Cvs.Approximant.ConnesVectorRealScale.connesVec (fun _ => N) x
    Real.log x ^ 2 * (α ⬝ᵥ α) * Cvs.Route.JointGapFromResidual.residualSq x (Nat.clog 2 x) (Real.log x) N v
      = (Cvs.Approximant.ConnesErrorColumn.center (discrepancyColumn x N) α + Cvs.Approximant.ConnesErrorColumn.center (cubicColumn x N) α
          - Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N) ⬝ᵥ
        (Cvs.Approximant.ConnesErrorColumn.center (discrepancyColumn x N) α + Cvs.Approximant.ConnesErrorColumn.center (cubicColumn x N) α
          - Cvs.Approximant.ConnesErrorColumn.centeredErrorColumn hx N) := by
  dsimp only
  rw [Cvs.Approximant.ConnesErrorColumn.connes_residual_eq_tail_error hx N hs,
    tailColumn_eq_discrepancy_add_cubic hx N, center_add]

end Cvs.WeilForm.PhysicalCubicCorrectionColumn
