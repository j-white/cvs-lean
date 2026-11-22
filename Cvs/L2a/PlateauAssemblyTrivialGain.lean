import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.FarMassPlateau
import Cvs.L2a.FirstSecondPairNoGram
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanFirstSecondPair
import Cvs.L2a.RungSpanFromPlateau
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailEdgeFarSplit
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailOfModes
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.PrimePowerIndexed
import Cvs.WeilForm.SelfConvolutionFunctional

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trivial gain below `k₀`, and the assembly without integrability hypotheses

Products of two masked Poisson sums of a continuous `Φ` are integrable on `(1, ∞)`, so the squares of the tail, edge
and far sums and the edge–far product are; the trivial gain `(1 − δ_k) ∫_k^b Φ² ≤ ∫F²` follows from the far–far cross
terms on `[k, b]`, where the tail is its far sum; and L2a on the span from the plateau beyond `k₀` is restated with
only the correlation, the far cross constants and the cross terms below `k₀` as hypotheses.
-/

namespace Cvs.L2a.PlateauAssemblyTrivialGain

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.TailNormModeMassesNonres Cvs.L2a.ResonantPartBeyondEdge Cvs.L2a.RungSpanTailFractions Cvs.L2a.RungSpanFirstSecondPair Cvs.L2a.FirstSecondPairFarMass Cvs.L2a.FirstSecondPairNoGram Cvs.L2a.RungSpanClosedForm Cvs.L2a.PoissonFarMassHarmonicGain Cvs.L2a.TailFractionsPairRatio Cvs.L2a.FarMassPlateau Cvs.L2a.TailEdgeFarSplit Cvs.L2a.RungSpanFromPlateau
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A masked Poisson sum on `(1, b]`: the modes `Φ(m·)` restricted to measurable sets `S m`. -/
noncomputable def maskedF (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (S : ℕ → Set ℝ) (θ : ℝ) : ℝ :=
  Set.indicator (Ioc 1 b) (fun θ => ∑ m ∈ Finset.Icc 1 M, Set.indicator (S m) (fun θ => Φ (m * θ)) θ) θ

/-- **The product of two masked Poisson sums is integrable on `(1, ∞)`** for `Φ` continuous on `[1, Mb]`. -/
theorem integrableOn_maskedF_mul (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (_hb : 1 ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) (S T : ℕ → Set ℝ)
    (hS : ∀ m, MeasurableSet (S m)) (hT : ∀ m, MeasurableSet (T m)) :
    IntegrableOn (fun θ => maskedF Φ M b S θ * maskedF Φ M b T θ) (Ioi 1) := by
  have hpt : ∀ θ, maskedF Φ M b S θ * maskedF Φ M b T θ
      = ∑ m ∈ Finset.Icc 1 M, ∑ m' ∈ Finset.Icc 1 M,
          Set.indicator (Ioc 1 b ∩ S m ∩ T m') (fun θ => Φ (m * θ) * Φ (m' * θ)) θ := by
    intro θ
    unfold maskedF
    by_cases hθ : θ ∈ Ioc 1 b
    · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro m' _
      by_cases h1 : θ ∈ S m <;> by_cases h2 : θ ∈ T m'
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_mem (show θ ∈ Ioc 1 b ∩ S m ∩ T m' from ⟨⟨hθ, h1⟩, h2⟩)]
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, mul_zero,
          Set.indicator_of_notMem (fun (h : θ ∈ Ioc 1 b ∩ S m ∩ T m') => h2 h.2)]
      · rw [Set.indicator_of_notMem h1, zero_mul, Set.indicator_of_notMem (fun (h : θ ∈ Ioc 1 b ∩ S m ∩ T m') => h1 h.1.2)]
      · rw [Set.indicator_of_notMem h1, zero_mul, Set.indicator_of_notMem (fun (h : θ ∈ Ioc 1 b ∩ S m ∩ T m') => h1 h.1.2)]
    · rw [Set.indicator_of_notMem hθ, zero_mul]
      symm
      apply Finset.sum_eq_zero; intro m _; apply Finset.sum_eq_zero; intro m' _
      exact Set.indicator_of_notMem (fun (h : θ ∈ Ioc 1 b ∩ S m ∩ T m') => hθ h.1.1) _
  have hint : ∀ m ∈ Finset.Icc 1 M, ∀ m' ∈ Finset.Icc 1 M,
      IntegrableOn (Set.indicator (Ioc 1 b ∩ S m ∩ T m') (fun θ => Φ (m * θ) * Φ (m' * θ))) (Ioi 1) := by
    intro m hm m' hm'
    rw [Finset.mem_Icc] at hm hm'
    have hmeas : MeasurableSet (Ioc 1 b ∩ S m ∩ T m') := (measurableSet_Ioc.inter (hS m)).inter (hT m')
    have hc : ContinuousOn (fun θ => Φ (m * θ) * Φ (m' * θ)) (Icc 1 b) := by
      refine ContinuousOn.mul ?_ ?_
      · refine hcont.comp (continuousOn_const.mul continuousOn_id) ?_
        intro θ hθ
        show (m : ℝ) * θ ∈ Icc 1 (M * b)
        have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
        have h2 : (m : ℝ) ≤ M := by exact_mod_cast hm.2
        exact ⟨by nlinarith [hθ.1], mul_le_mul h2 hθ.2 (by linarith [hθ.1]) (by linarith)⟩
      · refine hcont.comp (continuousOn_const.mul continuousOn_id) ?_
        intro θ hθ
        show (m' : ℝ) * θ ∈ Icc 1 (M * b)
        have h1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'.1
        have h2 : (m' : ℝ) ≤ M := by exact_mod_cast hm'.2
        exact ⟨by nlinarith [hθ.1], mul_le_mul h2 hθ.2 (by linarith [hθ.1]) (by linarith)⟩
    have hI : IntegrableOn (fun θ => Φ (m * θ) * Φ (m' * θ)) (Ioc 1 b ∩ S m ∩ T m') :=
      (hc.integrableOn_Icc.mono_set (fun θ hθ => ⟨hθ.1.1.1.le, hθ.1.1.2⟩))
    exact (integrable_indicator_iff hmeas).mpr hI |>.integrableOn
  simp_rw [hpt]
  exact integrable_finsetSum _ (fun m hm => integrable_finsetSum _ (fun m' hm' => hint m hm m' hm'))

/-- The tail is the masked sum with no mask. -/
theorem tailF_eq_maskedF (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) :
    tailF Φ M b = maskedF Φ M b (fun _ => univ) := by
  funext θ; simp [tailF, maskedF]

/-- The edge sum is the masked sum with the masks `mθ < k`. -/
theorem edgeF_eq_maskedF (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) :
    edgeF Φ M b k = maskedF Φ M b (fun m => {θ | θ < (k : ℝ) / m}) := rfl

/-- The far sum is the masked sum with the masks `mθ ≥ k`. -/
theorem farF_eq_maskedF (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) (k : ℕ) :
    farF Φ M b k = maskedF Φ M b (fun m => {θ | (k : ℝ) / m ≤ θ}) := rfl

/-- **The square of the tail is integrable on `(1, ∞)`.** -/
theorem integrableOn_tailF_sq (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (hb : 1 ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    IntegrableOn (fun θ => tailF Φ M b θ ^ 2) (Ioi 1) := by
  have := integrableOn_maskedF_mul Φ M hb hcont (fun _ => univ) (fun _ => univ)
    (fun _ => MeasurableSet.univ) (fun _ => MeasurableSet.univ)
  rw [tailF_eq_maskedF]
  simpa only [sq] using this

/-- **The square of the edge sum is integrable on `(1, ∞)`.** -/
theorem integrableOn_edgeF_sq (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (k : ℕ) (hb : 1 ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    IntegrableOn (fun θ => edgeF Φ M b k θ ^ 2) (Ioi 1) := by
  have := integrableOn_maskedF_mul Φ M hb hcont (fun m => {θ | θ < (k : ℝ) / m}) (fun m => {θ | θ < (k : ℝ) / m})
    (fun _ => measurableSet_Iio) (fun _ => measurableSet_Iio)
  rw [edgeF_eq_maskedF]
  simpa only [sq] using this

/-- **The square of the far sum is integrable on `(1, ∞)`.** -/
theorem integrableOn_farF_sq (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (k : ℕ) (hb : 1 ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    IntegrableOn (fun θ => farF Φ M b k θ ^ 2) (Ioi 1) := by
  have := integrableOn_maskedF_mul Φ M hb hcont (fun m => {θ | (k : ℝ) / m ≤ θ}) (fun m => {θ | (k : ℝ) / m ≤ θ})
    (fun _ => measurableSet_Ici) (fun _ => measurableSet_Ici)
  rw [farF_eq_maskedF]
  simpa only [sq] using this

/-- **The edge–far product is integrable on `(1, ∞)`.** -/
theorem integrableOn_edgeF_mul_farF (Φ : ℝ → ℝ) (M : ℕ) {b : ℝ} (k : ℕ) (hb : 1 ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    IntegrableOn (fun θ => edgeF Φ M b k θ * farF Φ M b k θ) (Ioi 1) := by
  rw [edgeF_eq_maskedF, farF_eq_maskedF]
  exact integrableOn_maskedF_mul Φ M hb hcont _ _ (fun _ => measurableSet_Iio) (fun _ => measurableSet_Ici)

/-- **The trivial gain**: on `[k, b]` the tail is its far sum, so `(1 − δ) Σ_m ∫_k^b Φ(mθ)² ≤ ∫_k^b F²` gives
`(1 − δ) ∫_k^b Φ² ≤ ∫F²`. -/
theorem trivial_gain {Φ : ℝ → ℝ} {M k : ℕ} {b δ : ℝ} (hk : 1 ≤ k) (hkM : k ≤ M) (hkb : (k : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) (hδ : δ ≤ 1)
    (hcross : (1 - δ) * ∑ m ∈ Finset.Icc 1 M, ∫ θ in (k : ℝ)..b, Φ (m * θ) ^ 2
      ≤ ∫ θ in (k : ℝ)..b, tailF Φ M b θ ^ 2) :
    (1 - δ) * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb1 : (1 : ℝ) ≤ b := hk1.trans hkb
  have hM1 : 1 ≤ M := hk.trans hkM
  -- the first mode's mass is one term of the sum
  have h1 : ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 ≤ ∑ m ∈ Finset.Icc 1 M, ∫ θ in (k : ℝ)..b, Φ (m * θ) ^ 2 := by
    have hterm : ∫ θ in (k : ℝ)..b, Φ ((1 : ℕ) * θ) ^ 2 = ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 := by
      simp only [Nat.cast_one, one_mul]
    rw [← hterm]
    refine Finset.single_le_sum (f := fun m : ℕ => ∫ θ in (k : ℝ)..b, Φ (m * θ) ^ 2) (fun m _ => ?_)
      (Finset.mem_Icc.mpr ⟨le_rfl, hM1⟩)
    exact intervalIntegral.integral_nonneg hkb (fun θ _ => sq_nonneg _)
  have h2 : ∫ θ in (k : ℝ)..b, tailF Φ M b θ ^ 2 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    rw [intervalIntegral.integral_of_le hkb]
    exact setIntegral_mono_set (integrableOn_tailF_sq Φ M hb1 hcont)
      (Filter.Eventually.of_forall (fun θ => sq_nonneg _))
      (Filter.Eventually.of_forall (fun θ hθ => lt_of_le_of_lt hk1 hθ.1))
  calc (1 - δ) * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2
      ≤ (1 - δ) * ∑ m ∈ Finset.Icc 1 M, ∫ θ in (k : ℝ)..b, Φ (m * θ) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := hcross.trans h2

/-- **L2a on the prolate rung span from the plateau beyond `k₀`, with only the constants as hypotheses**: the
edge–far correlation `r_j ≤ w_j` and far cross constant `ε_j` for `k₀ ≤ j ≤ M`, the far–far cross terms `δ_j` on
`[j, b]` below `k₀`, and `ρ₁`, `ρ`, `ε₃`. -/
theorem L2a_span_of_plateau' {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β ρ ρ₁ ε₃ : ℝ} {M k₀ : ℕ} (N P R Kf : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ) (rs ws εs δs : ℕ → ℝ)
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hinj : Function.Injective χ)
    (hM : 2 ≤ M) (hc₀ : 1 ≤ c₀) (hc : c₀ ≤ c) (hc8 : 8 ≤ c) (hs : 0 < s) (hsmax : max s (5 / (6 * s)) ≤ 1)
    (hh : 0 < h) (hh' : h ≤ 1 / 5)
    (hh₂ : 0 < h₂) (hh₂' : h₂ ≤ 1 / 20) (hη0 : 0 < hη) (hη' : 4 / 3 + hη ≤ 3 / 2 - h₂) (hb : 4 ≤ b)
    (hbM : 3 * M / 2 ≤ b)
    (hε : 0 < ε) (hε2 : ε < 2) (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (hMpos : ∀ i, 0 < ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2)
    (hN₀ : 0 < ∑ i, a i ^ 2 * massB c (χ i) (g i) b)
    (hD : 0 < D) (hgap : ∀ i j, i ≠ j → D ≤ |χ i - χ j|)
    (hξ₀ : 1 < ξ₀) (hξ₀b : ξ₀ ≤ b) (hw' : wbar c ξ₀ < 2) (hden : 0 < massCoeff c b ξ₀)
    (hκ : 0 < (1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b))
    (hx : 0 < x') (hKf : 1 ≤ Kf) (hfl : archSymbol 0 ≤ floorK x' Kf)
    (hB : ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ B
      ∧ |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ B)
    (hβ : B ^ 2 ≤ β * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) (hβ0 : 0 ≤ β)
    (hMb : (M : ℝ) ≤ b) (hε₃ : 0 ≤ ε₃)
    (hbeyond : ∫ ξ in b..(M * b), (fun ξ => ∑ i, a i * psi c (g i) ξ) ξ ^ 2
      ≤ ε₃ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hε0 : ∀ j, 0 ≤ εs j) (hε1 : ∀ j, εs j < 1)
    (hfar : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      (1 - εs j) * ∑ m ∈ Finset.Icc 1 M, farMode (fun ξ => ∑ i, a i * psi c (g i) ξ) b j m
        ≤ ∫ θ in Ioi 1, farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2)
    (hw : ∀ j, 0 < ws j) (hr : ∀ j, 0 ≤ rs j) (hrw : ∀ j, rs j ≤ ws j) (hrw1 : ∀ j, rs j * ws j < 1)
    (hcorr : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      -(rs j * ((∫ θ in Ioi 1, edgeF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2) / ws j
          + ws j * ∫ θ in Ioi 1, farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2))
        ≤ 2 * ∫ θ in Ioi 1, edgeF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ
          * farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ)
    (hδ1 : ∀ j, δs j < 1)
    (hcross : ∀ j ∈ Finset.Icc 1 M, j < k₀ →
      (1 - δs j) * ∑ m ∈ Finset.Icc 1 M, ∫ θ in (j : ℝ)..b, (fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) ^ 2
        ≤ ∫ θ in (j : ℝ)..b, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (h2 : 2 ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b))
    (hρ₁ : 0 ≤ ρ₁)
    (hrest1 : 2 * |pairPiece (fun ξ => ∑ i, a i * psi c (g i) ξ) b|
        + |rest1 (fun ξ => ∑ i, a i * psi c (g i) ξ) M b|
      ≤ ρ₁ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hrest : nonresRestTotal (fun ξ => ∑ i, a i * psi c (g i) ξ) M b
          ((Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b))
      ≤ ρ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hpole : -(q * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ / θ)) :
    (floorK x' Kf
        - (floorK x' Kf - archSymbol 0)
          * (4 * x' * β / ((1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
            - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
                + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b)))
        - ((∑ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
              2 * Λ k * tauG (gainP k₀ rs ws εs δs) ε₃ M k / k)
            + (2 * Λ 2 * √((1 + ρ₁) * tauG (gainP k₀ rs ws εs δs) ε₃ M 2 / 2) + ρ)) - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hconts : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcψ i)
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hcont := hconts.continuousOn (s := Icc 1 (M * b))
  refine L2a_span_of_plateau N P R Kf g g₁ g₂ χ a rs ws εs δs hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax
    hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw' hden hκ hx hKf hfl hB hβ hβ0
    hMb hε₃ hbeyond (fun j _ _ => integrableOn_edgeF_sq _ M j hb1 hcont)
    (fun j _ _ => integrableOn_farF_sq _ M j hb1 hcont)
    (fun j _ _ => integrableOn_edgeF_mul_farF _ M j hb1 hcont) hε0 hε1 hfar hw hr hrw hrw1 hcorr hδ1 ?_ h2 hρ₁
    hrest1 hrest hpole
  intro j hj hjk
  have hj' := Finset.mem_Icc.mp hj
  exact trivial_gain hj'.1 hj'.2 (le_trans (by exact_mod_cast hj'.2) hMb) hcont (hδ1 j).le (hcross j hj hjk)

end Cvs.L2a.PlateauAssemblyTrivialGain
