import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.FirstSecondPairFarMass
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
# The `(1, 2)` pair without the mode-Gram constant

The non-resonant pairs at `k = 1` are twice the `(1, 2)` pair `∫_1^b Φ(θ)Φ(2θ)` plus the rest, so on a tail whose
`(1, 2)` pair is nonnegative the first-mode mass is at most `∫F²` plus the rest and the piece of the pair on
`[b/2, b]`: the bound of Cvs.L2a.FirstSecondPairFarMass then needs no `1/(1 − δ)`, and L2a on the span holds with the prime constant
`Σ 2Λ(k) τ_k/k + Λ(2)(s(1 + ρ₁) + τ₂/(2s)) + ρ`, `ρ₁` the rest of the `k = 1` pairs against the tail norm.
-/

namespace Cvs.L2a.FirstSecondPairNoGram

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.TailNormModeMassesNonres Cvs.L2a.ResonantPartBeyondEdge Cvs.L2a.RungSpanTailFractions Cvs.L2a.RungSpanFirstSecondPair Cvs.L2a.FirstSecondPairFarMass
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The `(1, 2)` pair on the whole tail, `∫_1^b Φ(θ)Φ(2θ) dθ`. -/
noncomputable def pairFull (Φ : ℝ → ℝ) (b : ℝ) : ℝ := ∫ θ in (1 : ℝ)..b, Φ θ * Φ (2 * θ)

/-- The non-resonant pairs at `k = 1` other than `(1, 2)` and `(2, 1)`. -/
noncomputable def rest1 (Φ : ℝ → ℝ) (M : ℕ) (b : ℝ) : ℝ :=
  ∑ p ∈ ((nonresPairs M 1).erase (1, 2)).erase (2, 1), ∫ θ in (1 : ℝ)..b / 1, Φ (p.1 * θ) * Φ (p.2 * (1 * θ))

/-- **The non-resonant pairs at `k = 1` are twice the `(1, 2)` pair plus the rest.** -/
theorem nonresPart_one_eq (Φ : ℝ → ℝ) {M : ℕ} (b : ℝ) (hM : 2 ≤ M) :
    nonresPart Φ M b 1 = 2 * pairFull Φ b + rest1 Φ M b := by
  unfold nonresPart rest1 pairFull
  have h12 : ((1 : ℕ), (2 : ℕ)) ∈ nonresPairs M 1 := by
    simp only [nonresPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]; omega
  have h21 : ((2 : ℕ), (1 : ℕ)) ∈ (nonresPairs M 1).erase (1, 2) := by
    rw [Finset.mem_erase]
    refine ⟨by simp, ?_⟩
    simp only [nonresPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]; omega
  rw [← Finset.add_sum_erase _ _ h12, ← Finset.add_sum_erase _ _ h21]
  simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, div_one]
  have e : ∫ θ in (1 : ℝ)..b, Φ (2 * θ) * Φ θ = ∫ θ in (1 : ℝ)..b, Φ θ * Φ (2 * θ) :=
    integral_congr fun θ _ => by ring
  rw [e]; ring

/-- The piece of the `(1, 2)` pair on `[b/2, b]`. -/
noncomputable def pairPiece (Φ : ℝ → ℝ) (b : ℝ) : ℝ := ∫ θ in (b / 2)..b, Φ θ * Φ (2 * θ)

/-- `pairFull = pair11(2) + pairPiece`. -/
theorem pairFull_eq (Φ : ℝ → ℝ) {b : ℝ} (hb : 2 ≤ b) (hcont : ContinuousOn Φ (Icc 1 (2 * b))) :
    pairFull Φ b = pair11 Φ b 2 + pairPiece Φ b := by
  unfold pairFull pair11 pairPiece
  have hc : ContinuousOn (fun θ => Φ θ * Φ (2 * θ)) (Icc 1 b) := by
    refine (hcont.mono (Icc_subset_Icc le_rfl (by linarith))).mul
      (hcont.comp (continuousOn_const.mul continuousOn_id) ?_)
    intro θ hθ
    show 2 * θ ∈ Icc 1 (2 * b)
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hb2 : (1 : ℝ) ≤ b / 2 := by linarith
  have hbb : b / 2 ≤ b := by linarith
  rw [Nat.cast_ofNat, ← integral_add_adjacent_intervals
    ((hc.mono (Icc_subset_Icc le_rfl hbb)).intervalIntegrable_of_Icc hb2)
    ((hc.mono (Icc_subset_Icc hb2 le_rfl)).intervalIntegrable_of_Icc hbb)]

/-- **The first-mode mass on a tail whose `(1, 2)` pair is nonnegative** is at most the tail norm plus the rest:
`modeMass(1) ≤ ∫F² + 2|pairPiece| + |rest1|`. -/
theorem first_mass_le_of_pair_nonneg (Φ : ℝ → ℝ) {M : ℕ} {b : ℝ} (hM : 2 ≤ M) (hb : 2 ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) (hpos : 0 ≤ pair11 Φ b 2) :
    modeMass Φ b 1 ≤ (∫ θ in Ioi 1, tailF Φ M b θ ^ 2) + 2 * |pairPiece Φ b| + |rest1 Φ M b| := by
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hc2 : ContinuousOn Φ (Icc 1 (2 * b)) :=
    hcont.mono (Icc_subset_Icc le_rfl (mul_le_mul_of_nonneg_right hM' (by linarith)))
  have hmm : ∀ n ∈ Finset.Icc 1 M, 0 ≤ modeMass Φ b n := fun n _ =>
    integral_nonneg hb1 (fun θ _ => sq_nonneg _)
  have h1 : modeMass Φ b 1 ≤ ∑ n ∈ Finset.Icc 1 M, modeMass Φ b n :=
    Finset.single_le_sum hmm (by simp only [Finset.mem_Icc]; omega)
  rw [norm_eq_modeMasses_add_nonres Φ M hb1 hcont, nonresPart_one_eq Φ b hM, pairFull_eq Φ hb hc2]
  have h2 := le_abs_self (pairPiece Φ b)
  have h3 := neg_abs_le (pairPiece Φ b)
  have h4 := neg_abs_le (rest1 Φ M b)
  linarith

/-- **The `(1, 2)` pair from the tail norm alone**: with `2|pairPiece| + |rest1| ≤ ρ₁ ∫F²` and
`modesBeyond(2) ≤ τ₂ ∫F²`, for every `s > 0`, `pair11(2) ≤ ((s(1 + ρ₁) + τ₂/(2s))/2) ∫F²`. -/
theorem pair11_le_of_rest (Φ : ℝ → ℝ) {M : ℕ} {b s ρ₁ τ₂ : ℝ} (hM : 2 ≤ M) (hb : 2 ≤ b) (hs : 0 < s)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) (hρ₁ : 0 ≤ ρ₁) (hτ₂ : 0 ≤ τ₂)
    (hrest : 2 * |pairPiece Φ b| + |rest1 Φ M b| ≤ ρ₁ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2)
    (hfar : modesBeyond Φ M b 2 ≤ τ₂ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) :
    pair11 Φ b 2 ≤ (s * (1 + ρ₁) + τ₂ / (2 * s)) / 2 * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hN : 0 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hcoef : 0 ≤ (s * (1 + ρ₁) + τ₂ / (2 * s)) / 2 := by positivity
  rcases le_or_gt (pair11 Φ b 2) 0 with hneg | hpos
  · exact hneg.trans (mul_nonneg hcoef hN)
  · have hcb : ContinuousOn Φ (Icc 1 b) :=
      hcont.mono (Icc_subset_Icc le_rfl (by nlinarith))
    have hamgm := two_pair11_le (Φ := Φ) hb hs hcb
    have hfirst := first_mass_le_of_pair_nonneg Φ hM hb hcont hpos.le
    have hfar2 := two_far_le_modesBeyond Φ hM hb hcont
    have hm1 : ∫ θ in (1 : ℝ)..b / 2, Φ θ ^ 2 ≤ modeMass Φ b 1 := by
      unfold modeMass
      simp only [Nat.cast_one, one_mul]
      exact integral_mono_interval le_rfl (by linarith) (by linarith)
        (Filter.Eventually.of_forall fun θ => sq_nonneg (Φ θ)) ((hcb.pow 2).intervalIntegrable_of_Icc hb1)
    have hA : s * ∫ θ in (1 : ℝ)..b / 2, Φ θ ^ 2 ≤ s * ((1 + ρ₁) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      linarith
    have hB : (1 / s) * ∫ θ in (1 : ℝ)..b / 2, Φ (2 * θ) ^ 2
        ≤ (1 / s) * (τ₂ / 2 * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have := hamgm.trans (add_le_add hA hB)
    have e : s * ((1 + ρ₁) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) + (1 / s) * (τ₂ / 2 * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2)
        = 2 * ((s * (1 + ρ₁) + τ₂ / (2 * s)) / 2 * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) := by
      field_simp
    rw [e] at this
    linarith

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span from the tail fractions and the rest of the `k = 1` pairs**: the `(1, 2)`
pair is paid by `Λ(2)(s(1 + ρ₁) + τ₂/(2s))` with no mode-Gram constant. -/
theorem L2a_span_of_fractions_rest {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β ρ ρ₁ s₂ : ℝ} {M : ℕ} (N P R Kf : ℕ)
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
    (hs₂ : 0 < s₂) (hρ₁ : 0 ≤ ρ₁) (hτ₂ : 0 ≤ τ 2)
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
              2 * Λ k * τ k / k) + (2 * Λ 2 * ((s₂ * (1 + ρ₁) + τ 2 / (2 * s₂)) / 2) + ρ)) - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hconts : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcψ i)
  have hb2 : (2 : ℝ) ≤ b := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦ
  have hP2 := pair11_le_of_rest Φ hM hb2 hs₂ hconts.continuousOn hρ₁ hτ₂ hrest1 (hτ 2 h2)
  exact L2a_span_of_P2 N P R Kf g g₁ g₂ χ a τ hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax hh hh'
    hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw hden hκ hx hKf hfl hB hβ hβ0 hτ h2 hP2
    hrest hpole

end Cvs.L2a.FirstSecondPairNoGram
