import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.BandRungOutgoingWave
import Cvs.L2a.BandTransferBandForm
import Cvs.L2a.BernsteinRieszSymbolBounds
import Cvs.L2a.CutMultiplierBand
import Cvs.L2a.CutSymbolWavenumber
import Cvs.L2a.FarIntegrationByParts
import Cvs.L2a.OrbitGapIntegerM
import Cvs.Prolate.CosineChristoffelDarboux
import Cvs.Prolate.RungOrthogonalityAtInfinity
import Cvs.Prolate.RungStieltjesDecay
import Cvs.Prolate.RungStieltjesTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-! The top multiplier `ν_top(cη) = Σ_{2 ≤ m < M} ν_cut(m; M)` is a band multiplier on
`bandRg(1/4, Ymax M)`: its value is bounded by `(200|A| + 32F + 18‖g‖₁)/c²`, uniformly in `M`,
and its `k`-th derivative by `k!·8^k·(8 H_M F/c + 97‖g‖₁/c²)` for `k = 1, 2, 3`.
Far cuts use the Stieltjes decay of Cvs.Prolate.RungStieltjesDecay, near cuts the Stieltjes bound of Cvs.L2a.BernsteinRieszSymbolBounds. -/

noncomputable section
open Real Set Filter Topology MeasureTheory Complex Metric
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.L2a.FarIntegrationByParts
open Cvs.Prolate.RungStieltjesTransform Cvs.Prolate.RungStieltjesDecay
open Cvs.L2a.CutMultiplierBand Cvs.L2a.CutSymbolWavenumber
open scoped Interval

namespace Cvs.L2a.TopCutBandMultiplier

/-- The `si` part at any `x₀`: `|ν_si(ζ)| ≤ F/(c(|mζ| − 1))` for `|mζ| > 1`. -/
theorem norm_nuSiC_le_gen {c m x₀ F : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ t : ℝ, |psi c g t| ≤ F)
    (hc : 0 < c) (hm : 0 < m) {ζ : ℂ} (hζ : 1 < ‖(m : ℂ) * ζ‖) :
    ‖nuSiC c g m x₀ ζ‖ ≤ F / (c * (‖(m : ℂ) * ζ‖ - 1)) := by
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm.ne'
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have hS := Cvs.L2a.BernsteinRieszSymbolBounds.norm_integral_stieltjesC_le (g := fun s => (g s : ℂ))
    (Complex.continuous_ofReal.comp_continuousOn hg) hc.ne' (Cvs.L2a.BernsteinRieszSymbolBounds.hF_of_psi hg heven hpsi)
    hζ (x₀ / m)
  have e : nuSiC c g m x₀ ζ = -I / (c : ℂ) * ∫ s in (-1 : ℝ)..1,
      (g s : ℂ) / ((m : ℂ) * ζ + s) * Cvs.L2a.BernsteinRieszSymbolBounds.ek c (x₀ / m) s := by
    unfold nuSiC
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have he : eF c (s / m) x₀ = Cvs.L2a.BernsteinRieszSymbolBounds.ek c (x₀ / m) s := by
      unfold eF Cvs.L2a.BernsteinRieszSymbolBounds.ek
      congr 3
      ring
    have hd : (c : ℂ) * (((s / m : ℝ) : ℂ) + ζ) = (c / m : ℂ) * ((m : ℂ) * ζ + s) := by
      push_cast; field_simp; ring
    have hX : (m : ℂ) * ζ + s ≠ 0 := by
      intro h0
      have h1 : (m : ℂ) * ζ = -(s : ℂ) := by linear_combination h0
      rw [h1, norm_neg, Complex.norm_real, Real.norm_eq_abs] at hζ
      rw [uIcc_of_le (by norm_num)] at *
      have := abs_le.2 ⟨‹s ∈ Icc (-1 : ℝ) 1›.1, ‹s ∈ Icc (-1 : ℝ) 1›.2⟩
      linarith
    rw [he, hd]
    push_cast
    field_simp
  rw [e, norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have h0 : 0 < ‖(m : ℂ) * ζ‖ - 1 := by linarith
  calc 1 / c * ‖∫ s in (-1 : ℝ)..1, (g s : ℂ) / ((m : ℂ) * ζ + s) * Cvs.L2a.BernsteinRieszSymbolBounds.ek c (x₀ / m) s‖
      ≤ 1 / c * (F / (‖(m : ℂ) * ζ‖ - 1)) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = F / (c * (‖(m : ℂ) * ζ‖ - 1)) := by field_simp

/-- **The real `si` part is the z-Stieltjes transform**: `ν_si(η) = −(i/c)·Fs(mη; x₀/m)` for `|mη| > 1`. -/
theorem nuSiC_ofReal_eq {c m x₀ : ℝ} (hc : 0 < c) (hm : 0 < m) (g : ℝ → ℝ) {η : ℝ} (hη : 1 < |m * η|) :
    nuSiC c g m x₀ (η : ℂ) = -I / (c : ℂ) * fsZ c g (m * η) (x₀ / m) := by
  have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm.ne'
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  unfold nuSiC
  rw [fsZ_eq, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (by norm_num)] at hs
  have hX : (m : ℂ) * η + s ≠ 0 := by
    have : m * η + s ≠ 0 := by
      intro h0
      have h1 : |m * η| = |s| := by rw [show m * η = -s by linarith, abs_neg]
      have := abs_le.2 ⟨hs.1, hs.2⟩
      linarith
    exact_mod_cast this
  have he : eF c (s / m) x₀ = ph c (x₀ / m) s := by
    unfold eF ph; congr 3; ring
  rw [he]
  push_cast
  field_simp
  have hw : ((m : ℂ) * η + s) * ((m : ℂ) * η + s)⁻¹ = 1 := mul_inv_cancel₀ hX
  linear_combination (-((g s : ℂ) * ph c (x₀ / m) s)) * hw

/-- **A far cut** (`c((M/m)² − 1) ≥ 16`): `|ν_si(η)| ≤ 100|A|/(c²√(M² − m²))` at `|η| ≥ 3/4`. -/
theorem norm_nuSiC_far {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hσ : c ^ 2 - χ ≤ 10 * c) {m M η : ℝ} (hm : 2 ≤ m) (hmM : m < M) (hη : 3 / 4 ≤ |η|)
    (hfar : 16 ≤ c * ((M / m) ^ 2 - 1)) :
    ‖nuSiC c g m M (η : ℂ)‖ ≤ 100 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / (c ^ 2 * √(M ^ 2 - m ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hm0 : 0 < m := by linarith
  have hmη : 3 / 2 ≤ m * |η| := by nlinarith
  have h1 : 1 < |m * η| := by rw [abs_mul, abs_of_pos hm0]; linarith
  rw [nuSiC_ofReal_eq hc0 hm0 g h1]
  have hz : 1 < M / m := by rw [lt_div_iff₀ hm0]; linarith
  have hF := norm_fsZ_le hg hg₁ hg₂c hang heven hc hχ hχc hσ hmη hz hfar
  have hneg : ‖fsZ c g (m * η) (M / m)‖ = ‖fsZ c g (m * |η|) (M / m)‖ := by
    rcases le_or_gt 0 η with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, mul_neg, norm_fsZ_neg heven]
  rw [norm_mul, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, hneg]
  have hMm : 0 < M ^ 2 - m ^ 2 := by nlinarith
  have hsq : √((M / m) ^ 2 - 1) = √(M ^ 2 - m ^ 2) / m := by
    rw [show (M / m) ^ 2 - 1 = (M ^ 2 - m ^ 2) / m ^ 2 by field_simp, Real.sqrt_div' _ (sq_nonneg m),
      Real.sqrt_sq hm0.le]
  rw [hsq] at hF
  have hs0 : 0 < √(M ^ 2 - m ^ 2) := Real.sqrt_pos.2 hMm
  have hA : 0 ≤ |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| := abs_nonneg _
  have hmη1 : 0 < m * |η| - 1 := by linarith
  calc 1 / c * ‖fsZ c g (m * |η|) (M / m)‖
      ≤ 1 / c * (25 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / (c * (m * |η| - 1) * (√(M ^ 2 - m ^ 2) / m))) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
    _ = 25 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| * (m / (m * |η| - 1)) / (c ^ 2 * √(M ^ 2 - m ^ 2)) := by
        field_simp
    _ ≤ 25 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| * 4 / (c ^ 2 * √(M ^ 2 - m ^ 2)) := by
        gcongr
        rw [div_le_iff₀ hmη1]; nlinarith
    _ = 100 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / (c ^ 2 * √(M ^ 2 - m ^ 2)) := by ring

/-- **A near cut**: `|ν_si(η)| ≤ 4F/(cm)` at `|η| ≥ 3/4`. -/
theorem norm_nuSiC_real_le {c m x₀ F : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ t : ℝ, |psi c g t| ≤ F)
    (hc : 0 < c) (hm : 2 ≤ m) {η : ℝ} (hη : 3 / 4 ≤ |η|) :
    ‖nuSiC c g m x₀ (η : ℂ)‖ ≤ 4 * F / (c * m) := by
  have hm0 : 0 < m := by linarith
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  have hn : ‖(m : ℂ) * (η : ℂ)‖ = m * |η| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hm0]
  have h1 : 1 < ‖(m : ℂ) * (η : ℂ)‖ := by rw [hn]; nlinarith
  refine (norm_nuSiC_le_gen hg heven hpsi hc hm0 h1).trans ?_
  rw [hn, div_le_div_iff₀ (by nlinarith) (by positivity)]
  have h4 : m ≤ 4 * (m * |η| - 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hF0 hc.le)]

/-- **The co part at `x₀ = M` on the real collar**. -/
theorem norm_nuCoC_top_real {c m M η : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) (hc : 0 < c)
    (hm : 2 ≤ m) (hM : 1 < M) (hη : 3 / 4 ≤ |η|) :
    ‖nuCoC c g m M (η : ℂ)‖ ≤ Cvs.L2a.BandRungOutgoingWave.gL1 g * ((34 * M / (M ^ 2 - 1) + 11 / (c * (M ^ 2 - 1))) / c ^ 2) / m :=
  norm_nuCoC_le hg (by linarith) fun s hs => norm_hcoC_le_real hc hM (abs_le_half_of_mem (div_mem_half hm hs)) hη

/-- **The cut at `x₀ = M` on the strip**. -/
theorem norm_nuCutC_top_strip {c m M F : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ t : ℝ, |psi c g t| ≤ F)
    (hc : 0 < c) (hm : 2 ≤ m) (hM : 1 < M) {ζ : ℂ} (hζ : ζ ∈ stripC) :
    ‖nuCutC c g m M ζ‖ ≤ 8 * F / (c * m)
      + Cvs.L2a.BandRungOutgoingWave.gL1 g * ((192 * M / (M ^ 2 - 1) + 64 / (c * (M ^ 2 - 1))) / c ^ 2) / m := by
  have hm0 : 0 < m := by linarith
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  have hmz : 5 * m / 8 ≤ ‖(m : ℂ) * ζ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
    have := Complex.abs_re_le_norm ζ
    nlinarith [hζ.1]
  have hsi := norm_nuSiC_le_gen (x₀ := M) hg heven hpsi hc hm0 (by linarith : 1 < ‖(m : ℂ) * ζ‖)
  have hsi' : F / (c * (‖(m : ℂ) * ζ‖ - 1)) ≤ 8 * F / (c * m) := by
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith [mul_nonneg hF0 hc.le]
  have hco := norm_nuCoC_le (x₀ := M) (H := (192 * M / (M ^ 2 - 1) + 64 / (c * (M ^ 2 - 1))) / c ^ 2) hg hm0
    (ζ := ζ) fun s hs => norm_hcoC_le_strip hc hM (abs_le_half_of_mem (div_mem_half hm hs)) hζ
  rw [nuCutC_eq_add hc hm hM hg (stripC_subset_omegaC hζ)]
  exact (norm_add_le _ _).trans (add_le_add (hsi.trans hsi') hco)

/-- `Σ_{k<n} 1/√(k+1) ≤ 2√n`. -/
theorem sum_inv_sqrt_le (n : ℕ) : ∑ k ∈ Finset.range n, 1 / √((k : ℝ) + 1) ≤ 2 * √(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
    have hstep : 1 / √((n : ℝ) + 1) ≤ 2 * √((n : ℝ) + 1) - 2 * √(n : ℝ) := by
      rw [div_le_iff₀ h1]
      have hs : √(n : ℝ) * √((n : ℝ) + 1) ≤ ((n : ℝ) + ((n : ℝ) + 1)) / 2 := by
        rw [← Real.sqrt_mul hn]
        have := Real.sqrt_le_sqrt (show (n : ℝ) * ((n : ℝ) + 1) ≤ (((n : ℝ) + ((n : ℝ) + 1)) / 2) ^ 2 by nlinarith)
        rwa [Real.sqrt_sq (by linarith)] at this
      have e : (2 * √((n : ℝ) + 1) - 2 * √(n : ℝ)) * √((n : ℝ) + 1)
          = 2 * ((n : ℝ) + 1) - 2 * (√(n : ℝ) * √((n : ℝ) + 1)) := by
        rw [sub_mul, mul_assoc, Real.mul_self_sqrt (by linarith)]; ring
      rw [e]; linarith
    push_cast
    linarith

/-- **The far sum**: `Σ_{2 ≤ m < M} 1/√(M² − m²) ≤ 2`. -/
theorem sum_inv_sqrt_sq_sub_le (M : ℕ) :
    ∑ m ∈ Finset.Ico 2 M, 1 / √((M : ℝ) ^ 2 - (m : ℝ) ^ 2) ≤ 2 := by
  rcases Nat.lt_or_ge M 3 with hM | hM
  · interval_cases M <;> simp
  have hM0 : (0 : ℝ) < M := by positivity
  have hpt : ∀ m ∈ Finset.Ico 2 M, 1 / √((M : ℝ) ^ 2 - (m : ℝ) ^ 2) ≤ 1 / √(M : ℝ) * (1 / √(((M - m : ℕ) : ℝ))) := by
    intro m hm
    have hmM : m < M := (Finset.mem_Ico.1 hm).2
    have hk : (0 : ℝ) < ((M - m : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hmM
    have hcast : ((M - m : ℕ) : ℝ) = (M : ℝ) - m := by rw [Nat.cast_sub hmM.le]
    rw [one_div_mul_one_div, ← Real.sqrt_mul hM0.le]
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
    apply Real.sqrt_le_sqrt
    rw [hcast]
    have : (m : ℝ) ≤ M := by exact_mod_cast hmM.le
    nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  have hre : ∑ m ∈ Finset.Ico 2 M, 1 / √(((M - m : ℕ) : ℝ)) = ∑ k ∈ Finset.range (M - 2), 1 / √((k : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < M - 2 := Finset.mem_range.1 hk
    congr 2
    have : M - (2 + (M - 2 - 1 - k)) = k + 1 := by omega
    rw [this]; push_cast; ring
  rw [hre]
  have hs := sum_inv_sqrt_le (M - 2)
  have hsM : √(((M - 2 : ℕ) : ℝ)) ≤ √(M : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le M 2)
  have hsM0 : 0 < √(M : ℝ) := Real.sqrt_pos.2 hM0
  calc 1 / √(M : ℝ) * ∑ k ∈ Finset.range (M - 2), 1 / √((k : ℝ) + 1) ≤ 1 / √(M : ℝ) * (2 * √(M : ℝ)) := by
        gcongr; exact hs.trans (by linarith)
    _ = 2 := by field_simp

/-- **The near cuts**: if every `m` in `S ⊆ [2, M)` has `M < z·m` with `z ≥ 1`,
then `Σ_{m ∈ S} 1/m ≤ z − 1`. -/
theorem sum_near_le {M : ℕ} {z : ℝ} (hz : 1 ≤ z) (hM : 0 < M) (S : Finset ℕ) (hS : S ⊆ Finset.Ico 2 M)
    (hnear : ∀ m ∈ S, (M : ℝ) < z * m) : ∑ m ∈ S, 1 / (m : ℝ) ≤ z - 1 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set K := ⌈(M : ℝ) / z⌉₊ with hK
  have hsub : S ⊆ Finset.Ico K M := by
    intro m hm
    have h1 := hnear m hm
    have h2 := Finset.mem_Ico.1 (hS hm)
    refine Finset.mem_Ico.2 ⟨?_, h2.2⟩
    rw [hK, Nat.ceil_le, div_le_iff₀ (by linarith)]
    linarith
  have hMz : (M : ℝ) / z ≤ M := div_le_self hM0.le hz
  have hcard : (S.card : ℝ) ≤ M - M / z := by
    rcases le_or_gt K M with h | h
    · have h1 : S.card ≤ (Finset.Ico K M).card := Finset.card_le_card hsub
      rw [Nat.card_Ico] at h1
      have h2 : (M : ℝ) / z ≤ K := Nat.le_ceil _
      have : (S.card : ℝ) ≤ ((M - K : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub h] at this
      linarith
    · have : S = ∅ := by
        rw [← Finset.subset_empty]
        exact hsub.trans (by rw [Finset.Ico_eq_empty (by omega)])
      rw [this, Finset.card_empty]; push_cast; linarith
  have hpt : ∀ m ∈ S, 1 / (m : ℝ) ≤ z / M := by
    intro m hm
    have h1 := hnear m hm
    have hm0 : (0 : ℝ) < m := by
      have := (Finset.mem_Ico.1 (hS hm)).1
      exact_mod_cast (show 0 < m by omega)
    rw [div_le_div_iff₀ hm0 hM0]
    linarith
  calc ∑ m ∈ S, 1 / (m : ℝ) ≤ ∑ m ∈ S, z / M := Finset.sum_le_sum hpt
    _ = S.card * (z / M) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M - M / z) * (z / M) := by gcongr
    _ = z - 1 := by field_simp

/-- `Σ_{2 ≤ m < M} 1/m ≤ (M − 2)/2`. -/
theorem harm_le {M : ℕ} (hM : 2 ≤ M) : ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ≤ ((M : ℝ) - 2) / 2 := by
  calc ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ≤ ∑ m ∈ Finset.Ico 2 M, (1 / 2 : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ico.1 hm).1
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    _ = ((M : ℝ) - 2) / 2 := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hM]; push_cast; ring

/-- The top multiplier at complex `ζ`. -/
def nuTopC (c : ℝ) (g : ℝ → ℝ) (M : ℕ) (ζ : ℂ) : ℂ := ∑ m ∈ Finset.Ico 2 M, nuCutC c g m M ζ

/-- `H_M = Σ_{2 ≤ m < M} 1/m`. -/
def harmM (M : ℕ) : ℝ := ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ)

/-- `N_top,0` (M-uniform). -/
def N0top (c : ℝ) (g : ℝ → ℝ) (F : ℝ) : ℝ :=
  200 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / c ^ 2 + 32 * F / c ^ 2 + 18 * Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2

/-- The strip bound `U = 8H_M F/c + 97‖g‖₁/c²`. -/
def Utop (c : ℝ) (g : ℝ → ℝ) (F : ℝ) (M : ℕ) : ℝ := 8 * harmM M * F / c + 97 * Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2

/-- The norms `N_top,k`. -/
def Ntop (c : ℝ) (g : ℝ → ℝ) (F : ℝ) (M : ℕ) (k : ℕ) : ℝ :=
  if k = 0 then N0top c g F else (k.factorial : ℝ) * 8 ^ k * Utop c g F M

/-- The top multiplier at real `η` is the cut sum `nuTop` at `cη`. -/
theorem nuTopC_ofReal (c : ℝ) (g : ℝ → ℝ) (M : ℕ) (η : ℝ) :
    nuTopC c g M (η : ℂ) = Cvs.L2a.BandRungOutgoingWave.nuTop c g M (c * η) := by
  unfold nuTopC Cvs.L2a.BandRungOutgoingWave.nuTop
  exact Finset.sum_congr rfl fun m _ => nuCutC_ofReal c g m M η

/-- The top multiplier is holomorphic on `omegaC`. -/
theorem differentiableOn_nuTopC {c : ℝ} {g : ℝ → ℝ} {M : ℕ} (hc : 0 < c) (hM : 2 ≤ M)
    (hg : ContinuousOn g (Icc (-1) 1)) : DifferentiableOn ℂ (nuTopC c g M) omegaC := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
  have : nuTopC c g M = fun ζ => ∑ m ∈ Finset.Ico 2 M, nuCutC c g m M ζ := rfl
  rw [this]
  exact DifferentiableOn.fun_sum fun m hm =>
    differentiableOn_nuCutC hc (by exact_mod_cast (Finset.mem_Ico.1 hm).1) hM1 hg

/-- `H_M ≤ (M − 2)/2`. -/
theorem harmM_le {M : ℕ} (hM : 2 ≤ M) : harmM M ≤ ((M : ℝ) - 2) / 2 := harm_le hM

/-- `H_M ≥ 0`. -/
theorem harmM_nonneg (M : ℕ) : 0 ≤ harmM M := Finset.sum_nonneg fun m _ => by positivity

/-- **`N_top,0`**: on the real collar, `|ν_top(cη)| ≤ 200|A|/c² + 32F/c² + 18‖g‖₁/c²`, uniformly in `M`. -/
theorem norm_nuTop_le_N0 {g g₁ g₂ : ℝ → ℝ} {c χ F : ℝ} {M : ℕ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hσ : c ^ 2 - χ ≤ 10 * c) (hpsi : ∀ t : ℝ, |psi c g t| ≤ F) (hM : 3 ≤ M) {η : ℝ} (hη : 3 / 4 ≤ |η|) :
    ‖Cvs.L2a.BandRungOutgoingWave.nuTop c g M (c * η)‖ ≤ N0top c g F := by
  have hc0 : 0 < c := by linarith
  have hgc : ContinuousOn g (Icc (-1) 1) := Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt hg
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  have hM0 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hG0 := Cvs.L2a.BandRungOutgoingWave.gL1_nonneg (g := g)
  have hA0 : 0 ≤ |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| := abs_nonneg _
  set far := (Finset.Ico 2 M).filter (fun m : ℕ => 16 ≤ c * (((M : ℝ) / m) ^ 2 - 1)) with hfar
  set near := (Finset.Ico 2 M).filter (fun m : ℕ => ¬ 16 ≤ c * (((M : ℝ) / m) ^ 2 - 1)) with hnear
  have hm2 : ∀ m ∈ Finset.Ico 2 M, (2 : ℝ) ≤ m := fun m hm => by exact_mod_cast (Finset.mem_Ico.1 hm).1
  have hmM : ∀ m ∈ Finset.Ico 2 M, (m : ℝ) < M := fun m hm => by exact_mod_cast (Finset.mem_Ico.1 hm).2
  rw [← nuTopC_ofReal]
  unfold nuTopC
  have hsplit : ∀ m ∈ Finset.Ico 2 M, ‖nuCutC c g m M (η : ℂ)‖ ≤ ‖nuSiC c g m M (η : ℂ)‖ + ‖nuCoC c g m M (η : ℂ)‖ :=
    fun m hm => by
      rw [nuCutC_eq_add hc0 (hm2 m hm) hM1 hgc (ofReal_mem_omegaC hη)]; exact norm_add_le _ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hsplit).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter_add_sum_filter_not (Finset.Ico 2 M) (fun m : ℕ => 16 ≤ c * (((M : ℝ) / m) ^ 2 - 1))]
  rw [← hfar, ← hnear]
  -- far cuts
  have hF1 : ∑ m ∈ far, ‖nuSiC c g m M (η : ℂ)‖ ≤ 200 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / c ^ 2 := by
    have h1 : ∀ m ∈ far, ‖nuSiC c g m M (η : ℂ)‖
        ≤ 100 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / c ^ 2 * (1 / √((M : ℝ) ^ 2 - (m : ℝ) ^ 2)) := by
      intro m hm
      rw [hfar, Finset.mem_filter] at hm
      refine (norm_nuSiC_far hg hg₁ hg₂c hang heven hc hχ hχc hσ (hm2 m hm.1) (hmM m hm.1) hη hm.2).trans
        (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    have h2 : ∑ m ∈ far, 1 / √((M : ℝ) ^ 2 - (m : ℝ) ^ 2) ≤ 2 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity).trans
        (sum_inv_sqrt_sq_sub_le M)
    calc 100 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / c ^ 2 * ∑ m ∈ far, 1 / √((M : ℝ) ^ 2 - (m : ℝ) ^ 2)
        ≤ 100 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / c ^ 2 * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 200 * |Cvs.Prolate.RungOrthogonalityAtInfinity.ampl g| / c ^ 2 := by ring
  -- near cuts
  have hN1 : ∑ m ∈ near, ‖nuSiC c g m M (η : ℂ)‖ ≤ 32 * F / c ^ 2 := by
    set z₁ := √(1 + 16 / c) with hz₁
    have hz1 : 1 ≤ z₁ := by
      rw [hz₁, Real.le_sqrt (by norm_num) (by positivity)]
      have : 0 ≤ 16 / c := by positivity
      linarith
    have hz8 : z₁ - 1 ≤ 8 / c := by
      have : z₁ ≤ 1 + 8 / c := by
        rw [hz₁, Real.sqrt_le_left (by positivity)]
        have : 0 ≤ 64 / c ^ 2 := by positivity
        nlinarith [show (1 + 8 / c) ^ 2 = 1 + 16 / c + 64 / c ^ 2 by field_simp; ring]
      linarith
    have hnz : ∀ m ∈ near, (M : ℝ) < z₁ * m := by
      intro m hm
      rw [hnear, Finset.mem_filter] at hm
      have hm0 : (0 : ℝ) < m := by linarith [hm2 m hm.1]
      have h1 : ((M : ℝ) / m) ^ 2 < 1 + 16 / c := by
        have h0 := not_le.1 hm.2
        have h16c : ((M : ℝ) / m) ^ 2 - 1 < 16 / c := by
          rw [lt_div_iff₀ hc0]; nlinarith
        linarith
      have h2 : (M : ℝ) / m < z₁ := by
        rw [hz₁]
        exact (Real.lt_sqrt (by positivity)).2 h1
      rwa [div_lt_iff₀ hm0] at h2
    have hsum := sum_near_le hz1 (by omega) near (Finset.filter_subset _ _) hnz
    have h1 : ∀ m ∈ near, ‖nuSiC c g m M (η : ℂ)‖ ≤ 4 * F / c * (1 / (m : ℝ)) := fun m hm => by
      rw [hnear, Finset.mem_filter] at hm
      refine (norm_nuSiC_real_le hgc heven hpsi hc0 (hm2 m hm.1) hη).trans (le_of_eq ?_)
      field_simp
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    calc 4 * F / c * ∑ m ∈ near, 1 / (m : ℝ) ≤ 4 * F / c * (8 / c) :=
          mul_le_mul_of_nonneg_left (hsum.trans hz8) (by positivity)
      _ = 32 * F / c ^ 2 := by field_simp; ring
  -- co part
  have hC1 : ∑ m ∈ Finset.Ico 2 M, ‖nuCoC c g m M (η : ℂ)‖ ≤ 18 * Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2 := by
    have h1 : ∀ m ∈ Finset.Ico 2 M, ‖nuCoC c g m M (η : ℂ)‖
        ≤ Cvs.L2a.BandRungOutgoingWave.gL1 g * ((34 * M / ((M : ℝ) ^ 2 - 1) + 11 / (c * ((M : ℝ) ^ 2 - 1))) / c ^ 2)
          * (1 / (m : ℝ)) := fun m hm => by
      refine (norm_nuCoC_top_real hgc hc0 (hm2 m hm) hM1 hη).trans (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum]
    have hH := harmM_le (by omega : 2 ≤ M)
    unfold harmM at hH
    have hp : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
    have hK0 : 0 ≤ Cvs.L2a.BandRungOutgoingWave.gL1 g * ((34 * M / ((M : ℝ) ^ 2 - 1) + 11 / (c * ((M : ℝ) ^ 2 - 1))) / c ^ 2) := by
      positivity
    refine (mul_le_mul_of_nonneg_left hH hK0).trans ?_
    rw [show Cvs.L2a.BandRungOutgoingWave.gL1 g * ((34 * M / ((M : ℝ) ^ 2 - 1) + 11 / (c * ((M : ℝ) ^ 2 - 1))) / c ^ 2)
        * (((M : ℝ) - 2) / 2) = Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2
          * ((34 * M * c + 11) * ((M : ℝ) - 2) / (2 * c * ((M : ℝ) ^ 2 - 1))) by field_simp]
    rw [show 18 * Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2 = Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2 * 18 by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hfn : ∑ m ∈ far, ‖nuSiC c g m M (η : ℂ)‖ + ∑ m ∈ near, ‖nuSiC c g m M (η : ℂ)‖
      + ∑ m ∈ Finset.Ico 2 M, ‖nuCoC c g m M (η : ℂ)‖ ≤ N0top c g F := by
    unfold N0top; linarith
  exact hfn

/-- **The strip bound**: `|ν_top,C(ζ)| ≤ 8H_M F/c + 97‖g‖₁/c²` on the strip. -/
theorem norm_nuTopC_strip {c F : ℝ} {g : ℝ → ℝ} {M : ℕ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ t : ℝ, |psi c g t| ≤ F)
    (hc : 80 ≤ c) (hM : 3 ≤ M) {ζ : ℂ} (hζ : ζ ∈ stripC) : ‖nuTopC c g M ζ‖ ≤ Utop c g F M := by
  have hc0 : 0 < c := by linarith
  have hM0 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) < M := by linarith
  have hG0 := Cvs.L2a.BandRungOutgoingWave.gL1_nonneg (g := g)
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hpsi 0)
  unfold nuTopC Utop
  have h1 : ∀ m ∈ Finset.Ico 2 M, ‖nuCutC c g m M ζ‖ ≤ 8 * F / c * (1 / (m : ℝ))
      + Cvs.L2a.BandRungOutgoingWave.gL1 g * ((192 * M / ((M : ℝ) ^ 2 - 1) + 64 / (c * ((M : ℝ) ^ 2 - 1))) / c ^ 2)
        * (1 / (m : ℝ)) := fun m hm => by
    refine (norm_nuCutC_top_strip hg heven hpsi hc0 (by exact_mod_cast (Finset.mem_Ico.1 hm).1) hM1 hζ).trans
      (le_of_eq ?_)
    ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h1).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hH := harmM_le (by omega : 2 ≤ M)
  have hH0 := harmM_nonneg M
  unfold harmM at hH hH0 ⊢
  have hp : 0 < (M : ℝ) ^ 2 - 1 := by nlinarith
  have hK0 : 0 ≤ Cvs.L2a.BandRungOutgoingWave.gL1 g * ((192 * M / ((M : ℝ) ^ 2 - 1) + 64 / (c * ((M : ℝ) ^ 2 - 1))) / c ^ 2) := by
    positivity
  have h2 : Cvs.L2a.BandRungOutgoingWave.gL1 g * ((192 * M / ((M : ℝ) ^ 2 - 1) + 64 / (c * ((M : ℝ) ^ 2 - 1))) / c ^ 2)
      * ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) ≤ 97 * Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2 := by
    refine (mul_le_mul_of_nonneg_left hH hK0).trans ?_
    rw [show Cvs.L2a.BandRungOutgoingWave.gL1 g * ((192 * M / ((M : ℝ) ^ 2 - 1) + 64 / (c * ((M : ℝ) ^ 2 - 1))) / c ^ 2)
        * (((M : ℝ) - 2) / 2) = Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2
          * ((192 * M * c + 64) * ((M : ℝ) - 2) / (2 * c * ((M : ℝ) ^ 2 - 1))) by field_simp]
    rw [show 97 * Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2 = Cvs.L2a.BandRungOutgoingWave.gL1 g / c ^ 2 * 97 by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e : 8 * F / c * ∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ) = 8 * (∑ m ∈ Finset.Ico 2 M, 1 / (m : ℝ)) * F / c := by ring
  linarith

/-- **Cauchy at radius `1/8`**: `|ν_top^{(k)}(η)| ≤ k!8^k U` at real `|η| ≥ 3/4`. -/
theorem norm_iteratedDeriv_nuTopC_le {c F : ℝ} {g : ℝ → ℝ} {M : ℕ} (hg : ContinuousOn g (Icc (-1) 1))
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hpsi : ∀ t : ℝ, |psi c g t| ≤ F)
    (hc : 80 ≤ c) (hM : 3 ≤ M) (k : ℕ) {η : ℝ} (hη : 3 / 4 ≤ |η|) :
    ‖iteratedDeriv k (nuTopC c g M) (η : ℂ)‖ ≤ (k.factorial : ℝ) * 8 ^ k * Utop c g F M := by
  have hc0 : 0 < c := by linarith
  have hball := closedBall_subset_stripC hη
  have hd := (differentiableOn_nuTopC (M := M) hc0 (by omega) hg).diffContOnCl_ball (hball.trans stripC_subset_omegaC)
  have hC : ∀ z ∈ sphere (η : ℂ) (1 / 8), ‖nuTopC c g M z‖ ≤ Utop c g F M := fun z hz =>
    norm_nuTopC_strip hg heven hpsi hc hM (hball (sphere_subset_closedBall hz))
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num) hd hC
  refine h.trans (le_of_eq ?_)
  rw [one_div, inv_pow, div_inv_eq_mul]
  ring

/-- **The top multiplier is a band multiplier** on `bandRg(1/4, Ymax M)` with norms `Ntop`,
for an even rung with `c ≥ 80`, `0 ≤ χ < c²`, `c² − χ ≤ 10c` and `|ψ| ≤ F`. -/
theorem nuTop_isBandMult {g g₁ g₂ : ℝ → ℝ} {c χ F : ℝ} {M : ℕ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (heven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hc : 80 ≤ c) (hχ : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hσ : c ^ 2 - χ ≤ 10 * c) (hpsi : ∀ t : ℝ, |psi c g t| ≤ F) (hM : 3 ≤ M) :
    Cvs.L2a.BandTransferBandForm.IsBandMult (fun η => Cvs.L2a.BandRungOutgoingWave.nuTop c g M (c * η))
      (fun η => iteratedDeriv 1 (nuTopC c g M) (η : ℂ)) (fun η => iteratedDeriv 2 (nuTopC c g M) (η : ℂ))
      (fun η => iteratedDeriv 3 (nuTopC c g M) (η : ℂ)) (1 / 4) (Cvs.L2a.OrbitGapIntegerM.Ymax M) (Ntop c g F M) := by
  have hc0 : 0 < c := by linarith
  have hgc : ContinuousOn g (Icc (-1) 1) := Cvs.Prolate.CosineChristoffelDarboux.continuousOn_of_hasDerivAt hg
  have hD := differentiableOn_nuTopC hc0 (by omega : 2 ≤ M) hgc
  have hmem : ∀ η ∈ Cvs.L2a.BandTransferBandForm.bandRg (1 / 4) (Cvs.L2a.OrbitGapIntegerM.Ymax M), 3 / 4 ≤ |η| :=
    fun η hη => by have := hη.1; linarith
  have hΩ : ∀ η ∈ Cvs.L2a.BandTransferBandForm.bandRg (1 / 4) (Cvs.L2a.OrbitGapIntegerM.Ymax M), (η : ℂ) ∈ omegaC :=
    fun η hη => ofReal_mem_omegaC (hmem η hη)
  have hfun : (fun η : ℝ => Cvs.L2a.BandRungOutgoingWave.nuTop c g M (c * η))
      = fun t : ℝ => iteratedDeriv 0 (nuTopC c g M) (t : ℂ) := by
    funext t; rw [iteratedDeriv_zero, nuTopC_ofReal]
  have hdk := fun k η hη => hasDerivAt_iteratedDeriv_ofReal isOpen_omegaC hD k (hΩ η hη)
  refine ⟨fun η hη => by rw [hfun]; exact hdk 0 η hη, fun η hη => hdk 1 η hη, fun η hη => hdk 2 η hη,
    fun η hη => (hdk 3 η hη).continuousAt.continuousWithinAt, fun η hη => ?_⟩
  have hk : ∀ k, 1 ≤ k → ‖iteratedDeriv k (nuTopC c g M) (η : ℂ)‖ ≤ Ntop c g F M k := by
    intro k hk1
    simp only [Ntop, ite_eq_right (by omega : k ≠ 0)]
    exact norm_iteratedDeriv_nuTopC_le hgc heven hpsi hc hM k (hmem η hη)
  refine ⟨?_, hk 1 le_rfl, hk 2 (by norm_num), hk 3 (by norm_num)⟩
  simp only [Ntop, ite_eq_left]
  exact norm_nuTop_le_N0 hg hg₁ hg₂c hang heven hc hχ hχc hσ hpsi hM (hmem η hη)

end Cvs.L2a.TopCutBandMultiplier

end
