import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.FirstSecondPairNoGram
import Cvs.L2a.PoissonFarMassHarmonicGain
import Cvs.L2a.PrimePairingResonantSplit
import Cvs.L2a.ResonantChannelModeMasses
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanClosedForm
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
# The tail fractions from the `(1, 2)` pair's Cauchy–Schwarz ratio

The tail norm is the mode masses plus twice the `(1, 2)` pair plus the rest (Cvs.L2a.FirstSecondPairNoGram), the modes `m ≤ k` each count
the far mass beyond `k` (Cvs.L2a.PoissonFarMassHarmonicGain), and the pair is at least `−r(m₁/w + w m₂)` with `m₂ ≤ (1 + ε)m₁/2`: when
`r/w + rw(1 + ε)/2 ≤ 1` the pair costs at most `m₁`, so `(H_k − 1) ∫_k^b Φ² ≤ (1 + ρ′) ∫F²`. The tail fractions are
then explicit, `τ_k = Σ_{k m′ ≤ M} (1/m′)((1 + ρ′)/(H_{k m′} − 1) + ε₃)`, and L2a on the span follows from `r`, `ρ′`, `ρ₁`, `ρ`.
-/

namespace Cvs.L2a.TailFractionsPairRatio

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.TailNormModeMassesNonres Cvs.L2a.ResonantPartBeyondEdge Cvs.L2a.RungSpanTailFractions Cvs.L2a.RungSpanFirstSecondPair Cvs.L2a.FirstSecondPairFarMass Cvs.L2a.FirstSecondPairNoGram Cvs.L2a.RungSpanClosedForm Cvs.L2a.PoissonFarMassHarmonicGain
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `H_k − 1 = Σ_{m = 2}^{k} 1/m`. -/
noncomputable def harm2 (k : ℕ) : ℝ := ∑ m ∈ Finset.Icc 2 k, 1 / (m : ℝ)

/-- The explicit tail fraction `τ_k = Σ_{k m′ ≤ M} (1/m′)((1 + ρ′)/(H_{k m′} − 1) + ε₃)`, `ε₃` the mass beyond `b`. -/
noncomputable def tauR (ρ' ε₃ : ℝ) (M k : ℕ) : ℝ :=
  ∑ m' ∈ (Finset.Icc 1 M).filter (fun m' => k * m' ≤ M), (1 / (m' : ℝ)) * ((1 + ρ') / harm2 (k * m') + ε₃)

theorem harm2_pos {k : ℕ} (hk : 2 ≤ k) : 0 < harm2 k := by
  unfold harm2
  apply Finset.sum_pos
  · intro m hm
    rw [Finset.mem_Icc] at hm
    have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  · exact ⟨2, by simp only [Finset.mem_Icc]; omega⟩

/-- **The far mass beyond `k` from the pair ratio**: `(H_k − 1) ∫_k^b Φ² ≤ (1 + ρ′) ∫F²`. -/
theorem far_mass_le_of_pair_ratio {Φ : ℝ → ℝ} {M k : ℕ} {b r w ρ' ε : ℝ} (hM : 2 ≤ M) (hk : 2 ≤ k)
    (hkM : k ≤ M) (hkb : (k : ℝ) ≤ b) (hcont : ContinuousOn Φ (Icc 1 (M * b)))
    (hw : 0 < w) (hr : 0 ≤ r) (hε : 0 ≤ ε) (hρ' : 0 ≤ ρ')
    (hpair : -(r * (modeMass Φ b 1 / w + w * modeMass Φ b 2)) ≤ 2 * pairFull Φ b)
    (hrest : -(ρ' * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) ≤ rest1 Φ M b)
    (htail : modeMass Φ b 2 ≤ (1 + ε) / 2 * modeMass Φ b 1)
    (hcoef : r / w + r * w * (1 + ε) / 2 ≤ 1) :
    harm2 k * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 ≤ (1 + ρ') * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  have hb1 : (1 : ℝ) ≤ b := le_trans (by exact_mod_cast (show 1 ≤ k by omega)) hkb
  have hM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hcont' : ContinuousOn Φ (Icc 1 (k * b)) :=
    hcont.mono (Icc_subset_Icc le_rfl (mul_le_mul_of_nonneg_right hM' (by linarith)))
  have hfar : 0 ≤ ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 := intervalIntegral.integral_nonneg hkb (fun ξ _ => sq_nonneg _)
  have hmm : ∀ n ∈ Finset.Icc 1 M, 0 ≤ modeMass Φ b n := fun n _ =>
    intervalIntegral.integral_nonneg hb1 (fun θ _ => sq_nonneg _)
  have hm1 : 0 ≤ modeMass Φ b 1 := hmm 1 (by simp only [Finset.mem_Icc]; omega)
  -- the modes `2 ≤ m ≤ k` count the far mass, and mode `1` is kept whole
  have hsub : Finset.Icc 2 k ⊆ Finset.Icc 1 M := Finset.Icc_subset_Icc (by omega) hkM
  have h1 : harm2 k * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 ≤ ∑ m ∈ Finset.Icc 2 k, modeMass Φ b m := by
    unfold harm2
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact modeMass_ge_far (by omega) hm.2 hkb hcont'
  have h2 : modeMass Φ b 1 + ∑ m ∈ Finset.Icc 2 k, modeMass Φ b m ≤ ∑ n ∈ Finset.Icc 1 M, modeMass Φ b n := by
    have hsplit : Finset.Icc 1 M = insert 1 ((Finset.Icc 1 M).erase 1) :=
      (Finset.insert_erase (by simp only [Finset.mem_Icc]; omega)).symm
    rw [hsplit, Finset.sum_insert (Finset.notMem_erase _ _)]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_erase, Finset.mem_Icc]
      omega
    · intro n hn _
      exact hmm n (Finset.mem_of_mem_erase hn)
  -- the pair costs at most the first-mode mass
  have hpair' : -(modeMass Φ b 1) ≤ 2 * pairFull Φ b := by
    refine le_trans ?_ hpair
    have : r * (modeMass Φ b 1 / w + w * modeMass Φ b 2)
        ≤ (r / w + r * w * (1 + ε) / 2) * modeMass Φ b 1 := by
      have := mul_le_mul_of_nonneg_left htail (mul_nonneg hr hw.le)
      calc r * (modeMass Φ b 1 / w + w * modeMass Φ b 2)
          = r / w * modeMass Φ b 1 + (r * w) * modeMass Φ b 2 := by field_simp
        _ ≤ r / w * modeMass Φ b 1 + (r * w) * ((1 + ε) / 2 * modeMass Φ b 1) := by linarith
        _ = (r / w + r * w * (1 + ε) / 2) * modeMass Φ b 1 := by ring
    have h3 := mul_le_mul_of_nonneg_right hcoef hm1
    linarith
  rw [norm_eq_modeMasses_add_nonres Φ M hb1 hcont, nonresPart_one_eq Φ b hM] at hrest ⊢
  linarith

/-- **The masses beyond the edge from the pair ratio**: `modesBeyond(k) ≤ τ_k ∫F²` with `τ_k` explicit, the mass
of `Φ` beyond `b` at most `ε₃ ∫F²`. -/
theorem modesBeyond_le_of_pair_ratio {Φ : ℝ → ℝ} {M k : ℕ} {b r w ρ' ε ε₃ : ℝ} (hM : 2 ≤ M) (hk : 2 ≤ k)
    (hMb : (M : ℝ) ≤ b) (hb : 2 ≤ b) (hcont : ContinuousOn Φ (Icc 1 (M * b)))
    (hw : 0 < w) (hr : 0 ≤ r) (hε : 0 ≤ ε) (hρ' : 0 ≤ ρ') (hε₃ : 0 ≤ ε₃)
    (hpair : -(r * (modeMass Φ b 1 / w + w * modeMass Φ b 2)) ≤ 2 * pairFull Φ b)
    (hrest : -(ρ' * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) ≤ rest1 Φ M b)
    (htail : modeMass Φ b 2 ≤ (1 + ε) / 2 * modeMass Φ b 1)
    (hcoef : r / w + r * w * (1 + ε) / 2 ≤ 1)
    (hbeyond : ∫ ξ in b..(M * b), Φ ξ ^ 2 ≤ ε₃ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) :
    modesBeyond Φ M b k ≤ tauR ρ' ε₃ M k * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  unfold modesBeyond tauR
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m' hm'
  rw [Finset.mem_filter, Finset.mem_Icc] at hm'
  obtain ⟨⟨hm'1, hm'M⟩, hkm'⟩ := hm'
  have hm'0 : (0 : ℝ) < m' := by exact_mod_cast hm'1
  have hm'1' : (1 : ℝ) ≤ m' := by exact_mod_cast hm'1
  have hm'M' : (m' : ℝ) ≤ M := by exact_mod_cast hm'M
  have hkm'2 : 2 ≤ k * m' := by nlinarith
  have hkm'b : ((k * m' : ℕ) : ℝ) ≤ b := le_trans (by exact_mod_cast hkm') hMb
  have hN : 0 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hcM : ContinuousOn (fun ξ => Φ ξ ^ 2) (Icc 1 (M * b)) := hcont.pow 2
  -- the mode `m′` on `[k, b]` is `(1/m′)` times the mass of `Φ` on `[k m′, m′ b]`, split at `b`
  have e : ∫ ξ in (k : ℝ)..b, Φ (m' * ξ) ^ 2
      = (1 / (m' : ℝ)) * ((∫ ξ in ((k * m' : ℕ) : ℝ)..b, Φ ξ ^ 2) + ∫ ξ in b..(m' * b), Φ ξ ^ 2) := by
    rw [intervalIntegral.integral_comp_mul_left (fun ξ => Φ ξ ^ 2) hm'0.ne', smul_eq_mul, one_div]
    congr 1
    have h1 : ((k * m' : ℕ) : ℝ) = m' * k := by push_cast; ring
    rw [h1]
    have hb' : b ≤ m' * b := by nlinarith
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hmk1 : (1 : ℝ) ≤ m' * k := by
      have := mul_le_mul hm'1' hk1' (by norm_num) (by linarith)
      linarith
    have hsub1 : Icc ((m' : ℝ) * k) b ⊆ Icc 1 (M * b) := Icc_subset_Icc hmk1 (by nlinarith)
    have hsub2 : Icc b ((m' : ℝ) * b) ⊆ Icc 1 (M * b) := Icc_subset_Icc (by linarith) (by nlinarith)
    rw [intervalIntegral.integral_add_adjacent_intervals
      ((hcM.mono hsub1).intervalIntegrable_of_Icc (by rw [← h1]; exact hkm'b))
      ((hcM.mono hsub2).intervalIntegrable_of_Icc hb')]
  have hfar := far_mass_le_of_pair_ratio (k := k * m') hM hkm'2 hkm' hkm'b hcont hw hr hε hρ' hpair hrest htail hcoef
  have hH := harm2_pos hkm'2
  have hbey : ∫ ξ in b..(m' * b), Φ ξ ^ 2 ≤ ε₃ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    refine le_trans ?_ hbeyond
    have hsub : Icc b ((M : ℝ) * b) ⊆ Icc 1 (M * b) := Icc_subset_Icc (by linarith) le_rfl
    have hbm : b ≤ (m' : ℝ) * b := by nlinarith
    have hmM : (m' : ℝ) * b ≤ M * b := mul_le_mul_of_nonneg_right hm'M' hb0
    have hbM : b ≤ (M : ℝ) * b := hbm.trans hmM
    exact intervalIntegral.integral_mono_interval le_rfl hbm hmM
      (Filter.Eventually.of_forall fun ξ => sq_nonneg (Φ ξ))
      ((hcM.mono hsub).intervalIntegrable_of_Icc hbM)
  rw [e]
  have h1 : ∫ ξ in ((k * m' : ℕ) : ℝ)..b, Φ ξ ^ 2 ≤ (1 + ρ') / harm2 (k * m') * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hH]
    linarith
  calc (1 / (m' : ℝ)) * ((∫ ξ in ((k * m' : ℕ) : ℝ)..b, Φ ξ ^ 2) + ∫ ξ in b..(m' * b), Φ ξ ^ 2)
      ≤ (1 / (m' : ℝ)) * (((1 + ρ') / harm2 (k * m') * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2)
          + ε₃ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 hbey) (by positivity)
    _ = (1 / (m' : ℝ)) * ((1 + ρ') / harm2 (k * m') + ε₃) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by ring

/-- Every prime power of the index is at least `2`. -/
theorem two_le_of_mem_primePowIndex {P R k : ℕ} (hk : k ∈ Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R) : 2 ≤ k := by
  unfold Cvs.WeilForm.PrimePowerIndexed.primePowIndex at hk
  rw [Finset.mem_image] at hk
  obtain ⟨⟨p, r⟩, hpr, rfl⟩ := hk
  rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hpr
  have hp := hpr.1.2.two_le
  have hr := hpr.2.1
  calc 2 ≤ p := hp
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ r := Nat.pow_le_pow_right (by omega) hr

set_option maxHeartbeats 1600000 in
/-- **L2a on the prolate rung span from the `(1, 2)` pair's Cauchy–Schwarz ratio**: with the pair at least
`−r(m₁/w + w m₂)` and `r/w + rw(1 + ε)/2 ≤ 1`, the tail fractions are `τ_k = Σ_{k m′ ≤ M} (1/m′)((1 + ρ′)/(H_{k m′} − 1) + ε₃)`
and the prime constant is `Σ_{k ≤ b} 2Λ(k) τ_k/k + 2Λ(2) √((1 + ρ₁) τ₂/2) + ρ`. -/
theorem L2a_span_of_ratio {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β ρ ρ₁ r w ε₂ ρ' ε₃ : ℝ} {M : ℕ} (N P R Kf : ℕ)
    (g g₁ g₂ : ι → ℝ → ℝ) (χ : ι → ℝ) (a : ι → ℝ)
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
    (hMb : (M : ℝ) ≤ b) (hw : 0 < w) (hr : 0 ≤ r) (hε₂ : 0 ≤ ε₂) (hρ' : 0 ≤ ρ')
    (hpair : -(r * (modeMass (fun ξ => ∑ i, a i * psi c (g i) ξ) b 1 / w
        + w * modeMass (fun ξ => ∑ i, a i * psi c (g i) ξ) b 2))
      ≤ 2 * pairFull (fun ξ => ∑ i, a i * psi c (g i) ξ) b)
    (hrest' : -(ρ' * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ rest1 (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)
    (htail : modeMass (fun ξ => ∑ i, a i * psi c (g i) ξ) b 2
      ≤ (1 + ε₂) / 2 * modeMass (fun ξ => ∑ i, a i * psi c (g i) ξ) b 1)
    (hcoef : r / w + r * w * (1 + ε₂) / 2 ≤ 1) (hε₃ : 0 ≤ ε₃)
    (hbeyond : ∫ ξ in b..(M * b), (fun ξ => ∑ i, a i * psi c (g i) ξ) ξ ^ 2
      ≤ ε₃ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
    (hτ₂ : 0 < tauR ρ' ε₃ M 2)
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
              2 * Λ k * tauR ρ' ε₃ M k / k) + (2 * Λ 2 * √((1 + ρ₁) * tauR ρ' ε₃ M 2 / 2) + ρ)) - q)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
      ≤ Cvs.WeilForm.SelfConvolutionFunctional.weilForm P R (logScale (tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b)) := by
  have hcψ : ∀ i, Continuous (psi c (g i)) := fun i => (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hconts : Continuous fun ξ => ∑ i, a i * psi c (g i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hcψ i)
  have hb2 : (2 : ℝ) ≤ b := by linarith
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦ
  have hτ : ∀ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
      modesBeyond Φ M b k ≤ tauR ρ' ε₃ M k * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    intro k hk
    have hk2 : 2 ≤ k := two_le_of_mem_primePowIndex (Finset.mem_filter.mp hk).1
    exact modesBeyond_le_of_pair_ratio hM hk2 hMb hb2 hconts.continuousOn hw hr hε₂ hρ' hε₃ hpair hrest' htail
      hcoef hbeyond
  exact L2a_span_closed_form N P R Kf g g₁ g₂ χ a (tauR ρ' ε₃ M) hg hg₁ hg₂c hang hχ0 hχc hinj hM hc₀ hc hc8 hs hsmax
    hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw' hden hκ hx hKf hfl hB hβ hβ0
    hτ h2 hρ₁ hτ₂ hrest1 hrest hpole

end Cvs.L2a.TailFractionsPairRatio
