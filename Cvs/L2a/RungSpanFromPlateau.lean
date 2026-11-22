import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.L2a.FarMassPlateau
import Cvs.L2a.FirstSecondPairNoGram
import Cvs.L2a.RungHilbertLossMass
import Cvs.L2a.RungSpanClosedForm
import Cvs.L2a.RungSpanFirstSecondPair
import Cvs.L2a.RungSpanTailFractions
import Cvs.L2a.SpanFloorPairSums
import Cvs.L2a.SpanTailFloorLargeC
import Cvs.L2a.SpanTailFloorProlateLargeC
import Cvs.L2a.SpanTailFloorProlateRungs
import Cvs.L2a.TailEdgeFarSplit
import Cvs.L2a.TailFractionsPairRatio
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
# L2a on the rung span from the plateau beyond `k₀`

Any gain sequence `γ_j ∫_j^b Φ² ≤ ∫F²` gives the explicit tail fractions `τ_k = Σ_{k m′ ≤ M} (1/m′)(1/γ_{k m′} + ε₃)`;
the plateau of Cvs.L2a.FarMassPlateau supplies `γ_j = (1 − r_j w_j)(1 − ε_j) H_j` from the edge–far correlation `r_j` and the far cross
constant `ε_j` for `j ≥ k₀`, the trivial `γ_j = 1 − δ_j` serving below `k₀`, and L2a on the span follows with the
resonant constant `Σ_k 2Λ(k) τ_k / k`, whose terms decay like `1/H_k` from `k₀` on.
-/

namespace Cvs.L2a.RungSpanFromPlateau

open Real Set Finset MeasureTheory intervalIntegral ArithmeticFunction Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
open Cvs.L2a.RungSpanFromLowMass Cvs.L2a.PrimePairingResonantSplit Cvs.L2a.ResonantChannelModeMasses Cvs.L2a.SpanTailPrimeResonant Cvs.L2a.TailLogScaleTest Cvs.L2a.TailOfModes Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.RungOrthogonalityAtInfinity Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.RungChiHierarchy Cvs.L2a.SpanTailFloorProlateRungs Cvs.L2a.SpanFloorPairSums Cvs.L2a.SpanTailFloorLargeC Cvs.L2a.SpanTailFloorProlateLargeC Cvs.L2a.RungHilbertLossMass Cvs.L2a.RungSpanResonantForm Cvs.L2a.TailNormModeMassesNonres Cvs.L2a.ResonantPartBeyondEdge Cvs.L2a.RungSpanTailFractions Cvs.L2a.RungSpanFirstSecondPair Cvs.L2a.FirstSecondPairFarMass Cvs.L2a.FirstSecondPairNoGram Cvs.L2a.RungSpanClosedForm Cvs.L2a.PoissonFarMassHarmonicGain Cvs.L2a.TailFractionsPairRatio Cvs.L2a.FarMassPlateau Cvs.L2a.TailEdgeFarSplit
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The tail fraction from a gain sequence: `τ_k = Σ_{k m′ ≤ M} (1/m′)(1/γ(k m′) + ε₃)`. -/
noncomputable def tauG (γ : ℕ → ℝ) (ε₃ : ℝ) (M k : ℕ) : ℝ :=
  ∑ m' ∈ (Finset.Icc 1 M).filter (fun m' => k * m' ≤ M), (1 / (m' : ℝ)) * (1 / γ (k * m') + ε₃)

/-- **The masses beyond the edge from a gain sequence**: `γ_j ∫_j^b Φ² ≤ ∫F²` for `j ≤ M` gives
`modesBeyond(k) ≤ τ_k ∫F²`, the mass of `Φ` beyond `b` at most `ε₃ ∫F²`. -/
theorem modesBeyond_le_of_gain {Φ : ℝ → ℝ} {M k : ℕ} {b ε₃ : ℝ} (γ : ℕ → ℝ) (hk : 1 ≤ k)
    (hMb : (M : ℝ) ≤ b) (hb : 1 ≤ b) (hcont : ContinuousOn Φ (Icc 1 (M * b))) (_hε₃ : 0 ≤ ε₃)
    (hγ : ∀ j ∈ Finset.Icc 1 M, 0 < γ j)
    (hgain : ∀ j ∈ Finset.Icc 1 M, γ j * ∫ ξ in (j : ℝ)..b, Φ ξ ^ 2 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2)
    (hbeyond : ∫ ξ in b..(M * b), Φ ξ ^ 2 ≤ ε₃ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) :
    modesBeyond Φ M b k ≤ tauG γ ε₃ M k * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  unfold modesBeyond tauG
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m' hm'
  rw [Finset.mem_filter, Finset.mem_Icc] at hm'
  obtain ⟨⟨hm'1, hm'M⟩, hkm'⟩ := hm'
  have hm'0 : (0 : ℝ) < m' := by exact_mod_cast hm'1
  have hm'1' : (1 : ℝ) ≤ m' := by exact_mod_cast hm'1
  have hm'M' : (m' : ℝ) ≤ M := by exact_mod_cast hm'M
  have hkm'1 : 1 ≤ k * m' := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
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
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hmk1 : (1 : ℝ) ≤ m' * k := by
      have := mul_le_mul hm'1' hk1' (by norm_num) (by linarith)
      linarith
    have hsub1 : Icc ((m' : ℝ) * k) b ⊆ Icc 1 (M * b) := Icc_subset_Icc hmk1 (by nlinarith)
    have hsub2 : Icc b ((m' : ℝ) * b) ⊆ Icc 1 (M * b) := Icc_subset_Icc (by linarith) (by nlinarith)
    rw [intervalIntegral.integral_add_adjacent_intervals
      ((hcM.mono hsub1).intervalIntegrable_of_Icc (by rw [← h1]; exact hkm'b))
      ((hcM.mono hsub2).intervalIntegrable_of_Icc hb')]
  have hmem : k * m' ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hkm'1, hkm'⟩
  have hγpos := hγ _ hmem
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
  have h1 : ∫ ξ in ((k * m' : ℕ) : ℝ)..b, Φ ξ ^ 2 ≤ 1 / γ (k * m') * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hγpos, mul_comm]
    exact hgain _ hmem
  calc (1 / (m' : ℝ)) * ((∫ ξ in ((k * m' : ℕ) : ℝ)..b, Φ ξ ^ 2) + ∫ ξ in b..(m' * b), Φ ξ ^ 2)
      ≤ (1 / (m' : ℝ)) * ((1 / γ (k * m') * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2)
          + ε₃ * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 hbey) (by positivity)
    _ = (1 / (m' : ℝ)) * (1 / γ (k * m') + ε₃) * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by ring

/-- The gain sequence: the plateau's `(1 − r_j w_j)(1 − ε_j) H_j` from `k₀` on, the trivial `1 − δ_j` below. -/
noncomputable def gainP (k₀ : ℕ) (rs ws εs δs : ℕ → ℝ) (j : ℕ) : ℝ :=
  if k₀ ≤ j then (1 - rs j * ws j) * (1 - εs j) * harm j else 1 - δs j

/-- `H_j > 0` for `j ≥ 1`. -/
theorem harm_pos {j : ℕ} (hj : 1 ≤ j) : 0 < harm j := by
  unfold harm
  refine Finset.sum_pos (fun m hm => ?_) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hj⟩⟩
  have h1 := (Finset.mem_Icc.mp hm).1
  exact one_div_pos.mpr (Nat.cast_pos.mpr (by omega))

/-- The gain sequence is positive when `r_j w_j < 1`, `ε_j < 1` and `δ_j < 1`. -/
theorem gainP_pos {k₀ : ℕ} {rs ws εs δs : ℕ → ℝ} (hrw : ∀ j, rs j * ws j < 1) (hε : ∀ j, εs j < 1)
    (hδ : ∀ j, δs j < 1) {j : ℕ} (hj : 1 ≤ j) : 0 < gainP k₀ rs ws εs δs j := by
  unfold gainP
  split_ifs
  · have := harm_pos hj
    have h1 := hrw j
    have h2 := hε j
    positivity
  · linarith [hδ j]

/-- **The gain sequence is realised**: the plateau of Cvs.L2a.FarMassPlateau for `j ≥ k₀` and the trivial bound below. -/
theorem gainP_mul_far_le {Φ : ℝ → ℝ} {M k₀ : ℕ} {b : ℝ} (rs ws εs δs : ℕ → ℝ) (hMb : (M : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b)))
    (hFe : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j → IntegrableOn (fun θ => edgeF Φ M b j θ ^ 2) (Ioi 1))
    (hFf : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j → IntegrableOn (fun θ => farF Φ M b j θ ^ 2) (Ioi 1))
    (hFef : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      IntegrableOn (fun θ => edgeF Φ M b j θ * farF Φ M b j θ) (Ioi 1))
    (hε0 : ∀ j, 0 ≤ εs j) (hε1 : ∀ j, εs j ≤ 1)
    (hfar : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      (1 - εs j) * ∑ m ∈ Finset.Icc 1 M, farMode Φ b j m ≤ ∫ θ in Ioi 1, farF Φ M b j θ ^ 2)
    (hw : ∀ j, 0 < ws j) (hr : ∀ j, 0 ≤ rs j) (hrw : ∀ j, rs j ≤ ws j) (hrw1 : ∀ j, rs j * ws j ≤ 1)
    (hcorr : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      -(rs j * ((∫ θ in Ioi 1, edgeF Φ M b j θ ^ 2) / ws j + ws j * ∫ θ in Ioi 1, farF Φ M b j θ ^ 2))
        ≤ 2 * ∫ θ in Ioi 1, edgeF Φ M b j θ * farF Φ M b j θ)
    (htriv : ∀ j ∈ Finset.Icc 1 M, j < k₀ →
      (1 - δs j) * ∫ ξ in (j : ℝ)..b, Φ ξ ^ 2 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2) :
    ∀ j ∈ Finset.Icc 1 M, gainP k₀ rs ws εs δs j * ∫ ξ in (j : ℝ)..b, Φ ξ ^ 2
      ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hjb : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj'.2) hMb
  unfold gainP
  split_ifs with h
  · exact plateau hj'.1 hj'.2 hjb hcont (tailF_eq_edge_add_far Φ M b j) (hFe j hj h) (hFf j hj h) (hFef j hj h)
      (hε0 j) (hε1 j) (hfar j hj h) (hw j) (hr j) (hrw j) (hrw1 j) (hcorr j hj h)
  · exact htriv j hj (not_le.mp h)

/-- **L2a on the prolate rung span from the plateau beyond `k₀`**: with the edge–far correlation `r_j ≤ w_j` and
the far cross constant `ε_j` for `k₀ ≤ j ≤ M`, the trivial gain `1 − δ_j` below `k₀`, and the constants `ρ₁`, `ρ`,
`ε₃`, the resonant constant is `Σ_{k ≤ b} 2Λ(k) τ_k / k` with `τ_k = Σ_{k m′ ≤ M} (1/m′)(1/γ_{k m′} + ε₃)`. -/
theorem L2a_span_of_plateau {c c₀ h h₂ hη b s ε δ μ₁ μ₂ D ξ₀ x' B q β ρ ρ₁ ε₃ : ℝ} {M k₀ : ℕ} (N P R Kf : ℕ)
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
    (hFe : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      IntegrableOn (fun θ => edgeF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2) (Ioi 1))
    (hFf : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      IntegrableOn (fun θ => farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ ^ 2) (Ioi 1))
    (hFef : ∀ j ∈ Finset.Icc 1 M, k₀ ≤ j →
      IntegrableOn (fun θ => edgeF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ
        * farF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b j θ) (Ioi 1))
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
    (htriv : ∀ j ∈ Finset.Icc 1 M, j < k₀ →
      (1 - δs j) * ∫ ξ in (j : ℝ)..b, (fun ξ => ∑ i, a i * psi c (g i) ξ) ξ ^ 2
        ≤ ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * psi c (g i) ξ) M b θ ^ 2)
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
  set Φ : ℝ → ℝ := fun ξ => ∑ i, a i * psi c (g i) ξ with hΦ
  have hγ : ∀ j ∈ Finset.Icc 1 M, 0 < gainP k₀ rs ws εs δs j :=
    fun j hj => gainP_pos hrw1 hε1 hδ1 (Finset.mem_Icc.mp hj).1
  have hgain := gainP_mul_far_le (Φ := Φ) (M := M) (k₀ := k₀) rs ws εs δs hMb hconts.continuousOn hFe hFf hFef
    hε0 (fun j => (hε1 j).le) hfar hw hr hrw (fun j => (hrw1 j).le) hcorr htriv
  have hτ : ∀ k ∈ (Cvs.WeilForm.PrimePowerIndexed.primePowIndex P R).filter (fun k : ℕ => (k : ℝ) ≤ b),
      modesBeyond Φ M b k ≤ tauG (gainP k₀ rs ws εs δs) ε₃ M k * ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
    intro k hk
    have hk2 : 2 ≤ k := two_le_of_mem_primePowIndex (Finset.mem_filter.mp hk).1
    exact modesBeyond_le_of_gain _ (by omega) hMb hb1 hconts.continuousOn hε₃ hγ hgain hbeyond
  have hτ₂ : 0 < tauG (gainP k₀ rs ws εs δs) ε₃ M 2 := by
    unfold tauG
    refine Finset.sum_pos (fun m' hm' => ?_) ⟨1, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc] at hm'
      have hm'0 : (0 : ℝ) < m' := by exact_mod_cast hm'.1.1
      have hmem : 2 * m' ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨by omega, hm'.2⟩
      have := hγ _ hmem
      positivity
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, by omega⟩, by omega⟩
  exact L2a_span_closed_form N P R Kf g g₁ g₂ χ a (tauG (gainP k₀ rs ws εs δs) ε₃ M) hg hg₁ hg₂c hang hχ0 hχc hinj hM
    hc₀ hc hc8 hs hsmax hh hh' hh₂ hh₂' hη0 hη' hb hbM hε hε2 hδ hμ₁ hμ₂ hMpos hN₀ hD hgap hξ₀ hξ₀b hw' hden hκ hx
    hKf hfl hB hβ hβ0 hτ h2 hρ₁ hτ₂ hrest1 hrest hpole

end Cvs.L2a.RungSpanFromPlateau
