import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.PrimePairingResonantSplit
import Cvs.L2a.ResonantChannelModeMasses
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanFirstSecondPair
import Cvs.L2a.RungSpanTailFractions
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailLogScaleTest
import Cvs.L2a.TailNormModeMassesNonres
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
# The `(1, 2)` pair from the first-mode mass and the far mass beyond `2`

For every `s > 0`, `2 ∫_1^{b/2} Φ(θ)Φ(2θ) ≤ s ∫_1^{b/2} Φ² + (1/s) ∫_1^{b/2} Φ(2θ)²`; the first is at most the mode-`1`
mass, hence `∫F²/(1 − δ)` with the tail norm at least `(1 − δ)` times the mode masses (Cvs.L2a.TailNormModeMassesNonres), and the second is
half the far mass beyond `2`, at most `τ₂ ∫F²/2`. So L2a on the span holds with the `(1, 2)` pair paid by
`Λ(2)(s/(1 − δ) + τ₂/(2s))`: the spectral hypothesis of Cvs.L2a.RungSpanFirstSecondPair becomes the two named constants `δ` and `τ₂`.
-/

namespace Cvs.L2a.FirstSecondPairFarMass

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.TailNormModeMassesNonres Cvs.L2a.ResonantPartBeyondEdge Cvs.L2a.RungSpanTailFractions Cvs.L2a.RungSpanFirstSecondPair
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The `(1, 2)` pair by the arithmetic–geometric mean**: for `s > 0`,
`2 ∫_1^{b/2} Φ(θ)Φ(2θ) ≤ s ∫_1^{b/2} Φ² + (1/s) ∫_1^{b/2} Φ(2θ)²`. -/
theorem two_pair11_le {Φ : ℝ → ℝ} {b s : ℝ} (hb : 2 ≤ b) (hs : 0 < s) (hcont : ContinuousOn Φ (Icc 1 b)) :
    2 * pair11 Φ b 2 ≤ s * (∫ θ in (1 : ℝ)..b / 2, Φ θ ^ 2) + (1 / s) * ∫ θ in (1 : ℝ)..b / 2, Φ (2 * θ) ^ 2 := by
  have hb2 : (1 : ℝ) ≤ b / 2 := by linarith
  have hc1 : ContinuousOn Φ (Icc 1 (b / 2)) := hcont.mono (Icc_subset_Icc le_rfl (by linarith))
  have hc2 : ContinuousOn (fun θ => Φ (2 * θ)) (Icc 1 (b / 2)) := by
    refine hcont.comp (continuousOn_const.mul continuousOn_id) ?_
    intro θ hθ
    show 2 * θ ∈ Icc 1 b
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hI1 : IntervalIntegrable (fun θ => Φ θ ^ 2) volume 1 (b / 2) := (hc1.pow 2).intervalIntegrable_of_Icc hb2
  have hI2 : IntervalIntegrable (fun θ => Φ (2 * θ) ^ 2) volume 1 (b / 2) :=
    (hc2.pow 2).intervalIntegrable_of_Icc hb2
  have hI12 : IntervalIntegrable (fun θ => Φ θ * Φ (2 * θ)) volume 1 (b / 2) :=
    (hc1.mul hc2).intervalIntegrable_of_Icc hb2
  -- `∫ (√s Φ − Φ(2·)/√s)² ≥ 0`, then the goal's integrals assembled into that one
  have hsq : 0 ≤ ∫ θ in (1 : ℝ)..b / 2, (s * Φ θ ^ 2 - 2 * (Φ θ * Φ (2 * θ)) + (1 / s) * Φ (2 * θ) ^ 2) := by
    apply integral_nonneg hb2
    intro θ _
    have : s * Φ θ ^ 2 - 2 * (Φ θ * Φ (2 * θ)) + (1 / s) * Φ (2 * θ) ^ 2
        = (√s * Φ θ - Φ (2 * θ) / √s) ^ 2 := by
      have hs' : √s ^ 2 = s := sq_sqrt hs.le
      have hs0 : √s ≠ 0 := (sqrt_pos.mpr hs).ne'
      rw [sub_sq, mul_pow, div_pow, hs']
      field_simp
    rw [this]
    exact sq_nonneg _
  have e : pair11 Φ b 2 = ∫ θ in (1 : ℝ)..b / 2, Φ θ * Φ (2 * θ) := by
    unfold pair11; norm_num
  rw [intervalIntegral.integral_add (hI1.const_mul s |>.sub (hI12.const_mul 2)) (hI2.const_mul _),
    intervalIntegral.integral_sub (hI1.const_mul s) (hI12.const_mul 2), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hsq
  rw [e]
  linarith

/-- The far mass beyond `2` is the mode-`1` term of the masses beyond the edge: `2 ∫_1^{b/2} Φ(2θ)² ≤ modesBeyond(2)`. -/
theorem two_far_le_modesBeyond (Φ : ℝ → ℝ) {M : ℕ} {b : ℝ} (hM : 2 ≤ M) (hb : 2 ≤ b)
    (_hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    2 * ∫ θ in (1 : ℝ)..b / 2, Φ (2 * θ) ^ 2 ≤ modesBeyond Φ M b 2 := by
  unfold modesBeyond
  have h1 : (1 : ℕ) ∈ (Finset.Icc 1 M).filter (fun m' => 2 * m' ≤ M) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have hnn : ∀ m' ∈ (Finset.Icc 1 M).filter (fun m' => 2 * m' ≤ M), 0 ≤ ∫ ξ in (2 : ℝ)..b, Φ (m' * ξ) ^ 2 :=
    fun m' _ => integral_nonneg hb (fun ξ _ => sq_nonneg _)
  have e : 2 * ∫ θ in (1 : ℝ)..b / 2, Φ (2 * θ) ^ 2 = ∫ ξ in (2 : ℝ)..b, Φ (((1 : ℕ) : ℝ) * ξ) ^ 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun ξ => Φ ξ ^ 2) two_ne_zero, smul_eq_mul]
    simp only [Nat.cast_one, one_mul, mul_one]
    rw [show (2 : ℝ) * (b / 2) = b by ring]
    field_simp
  rw [e]
  exact Finset.single_le_sum hnn h1

/-- The first-mode mass on `[1, b/2]` is at most `∫F²/(1 − δ)` when the tail norm is at least `(1 − δ)` times the
mode masses. -/
theorem first_mass_le {Φ : ℝ → ℝ} {M : ℕ} {b δ : ℝ} (hM : 1 ≤ M) (hb : 2 ≤ b) (hδ : δ < 1)
    (hcont : ContinuousOn Φ (Icc 1 (M * b)))
    (hnr : -(δ * ∑ n ∈ Finset.Icc 1 M, modeMass Φ b n) ≤ nonresPart Φ M b 1) :
    (1 - δ) * ∫ θ in (1 : ℝ)..b / 2, Φ θ ^ 2 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc1 : ContinuousOn Φ (Icc 1 b) := hcont.mono (Icc_subset_Icc le_rfl (by nlinarith))
  have hmm : ∀ n ∈ Finset.Icc 1 M, 0 ≤ modeMass Φ b n := fun n _ =>
    integral_nonneg hb1 (fun θ _ => sq_nonneg _)
  have h1 : ∫ θ in (1 : ℝ)..b / 2, Φ θ ^ 2 ≤ modeMass Φ b 1 := by
    unfold modeMass
    simp only [Nat.cast_one, one_mul]
    exact integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun θ => sq_nonneg (Φ θ)) ((hc1.pow 2).intervalIntegrable_of_Icc hb1)
  have h2 : modeMass Φ b 1 ≤ ∑ n ∈ Finset.Icc 1 M, modeMass Φ b n :=
    Finset.single_le_sum hmm (by simp only [Finset.mem_Icc]; omega)
  rw [norm_eq_modeMasses_add_nonres Φ M hb1 hcont]
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 M, modeMass Φ b n := Finset.sum_nonneg hmm
  have h1δ : 0 ≤ 1 - δ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) h1δ]

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span from the tail fractions, the mode-Gram constant `δ₁` and the rest**: the `(1, 2)`
pair is paid by `Λ(2)(s/(1 − δ₁) + τ₂/(2s))` for any `s > 0`. -/
theorem L2a_span_of_fractions_delta {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β δ₁ ρ s₂ : ℝ} {M : ℕ} (N P R Kf : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ) (τ : ℕ → ℝ)
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
    (hξ₀ : 1 < ξ₀) (hξ₀b : ξ₀ ≤ b) (hw : wbar c ξ₀ < 2) (hden : 0 < massCoeff c b ξ₀)
    (hκ : 0 < (1 - max s (5 / (6 * s))) * (1 - θH c D b ξ₀)
        - (Kpair s (1 / 2) 1 (1 / 2) h h₂ hη b ε δ μ₁ μ₂ c₀ M N / c
            + Λpair s 1 b (Qpsi c g g₁ g₂ χ b / c) (Qu c g g₁ g₂ χ b / c ^ 3) M N) * (1 + τtail c b))
    (hx : 0 < x') (hKf : 1 ≤ Kf) (hfl : archSymbol 0 ≤ floorK x' Kf)
    (hB : ∀ t : ℝ, |t| < 2 * π * x' →
      |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.ky t θ| ≤ B
      ∧ |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ * Cvs.Prolate.Mellin.MellinKernelSturmLiouville.kys t θ| ≤ B)
    (hβ : B ^ 2 ≤ β * ∑ i, a i ^ 2 * ∫ ξ in (1 : ℝ)..b, psi c (g i) ξ ^ 2) (hβ0 : 0 ≤ β)
    (hτ : ∀ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
      modesBeyond (fun ξ => ∑ i, a i * psi c (g i) ξ) M b k
        ≤ τ k * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (h2 : 2 ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b))
    (hs₂ : 0 < s₂) (hδ₁ : δ₁ < 1)
    (hnr1 : -(δ₁ * ∑ n ∈ Finset.Icc 1 M, modeMass (fun ξ => ∑ i, a i * psi c (g i) ξ) b n)
      ≤ nonresPart (fun ξ => ∑ i, a i * psi c (g i) ξ) M b 1)
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
              2 * Λ k * τ k / k) + (2 * Λ 2 * ((s₂ / (1 - δ₁) + τ 2 / (2 * s₂)) / 2) + ρ)) - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hconts : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcψ i)
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hb2 : (2 : ℝ) ≤ b := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦ
  have hM1 : 1 ≤ M := by omega
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hcb : ContinuousOn Φ (Icc 1 b) := hconts.continuousOn
  have hNn : 0 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hτ2 := hτ 2 h2
  have hfirst := first_mass_le hM1 hb2 hδ₁ hconts.continuousOn hnr1
  have hfar := two_far_le_modesBeyond Φ hM hb2 hconts.continuousOn
  have hamgm := two_pair11_le (Φ := Φ) hb2 hs₂ hcb
  have h1δ : 0 < 1 - δ₁ := by linarith
  have hP2 : pair11 Φ b 2 ≤ (s₂ / (1 - δ₁) + τ 2 / (2 * s₂)) / 2 * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    have hA : s₂ * ∫ θ in (1 : ℝ)..b / 2, Φ θ ^ 2 ≤ s₂ / (1 - δ₁) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h1δ]
      nlinarith [hfirst]
    have hB : (1 / s₂) * ∫ θ in (1 : ℝ)..b / 2, Φ (2 * θ) ^ 2
        ≤ τ 2 / (2 * s₂) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
      have : ∫ θ in (1 : ℝ)..b / 2, Φ (2 * θ) ^ 2 ≤ τ 2 / 2 * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
        linarith [hfar, hτ2]
      calc (1 / s₂) * ∫ θ in (1 : ℝ)..b / 2, Φ (2 * θ) ^ 2
          ≤ (1 / s₂) * (τ 2 / 2 * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = τ 2 / (2 * s₂) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by field_simp
    have h2p : 2 * pair11 Φ b 2 ≤ s₂ / (1 - δ₁) * (∫ θ in Ioi 1, tailF Φ M b θ ^ 2)
        + τ 2 / (2 * s₂) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 :=
      hamgm.trans (add_le_add hA hB)
    have e : s₂ / (1 - δ₁) * (∫ θ in Ioi 1, tailF Φ M b θ ^ 2) + τ 2 / (2 * s₂) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2
        = 2 * ((s₂ / (1 - δ₁) + τ 2 / (2 * s₂)) / 2 * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) := by ring
    rw [e] at h2p
    linarith
  exact L2a_span_of_P2 N P R Kf g g₁ g₂ χ a τ hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax hh hh'
    hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden hκ hx hKf hfl hB hβ hβ0 hτ h2 hP2
    hrest hpole

end Cvs.L2a.FirstSecondPairFarMass
