import Mathlib
import Cvs.L2a.TailOfModes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far-mass plateau from the edge–far split of the tail

Split the tail `F = F_e + F_f` into the Poisson sums of the edge part of `Φ` (below `k`) and of its far part. Each
mode `m ≤ k` of the far part carries `(1/m) ∫_k^b Φ²`, so the far modes sum to at least `H_k ∫_k^b Φ²`; with the far
cross terms at least `−ε` times those masses and the edge–far pairing at least `−r(‖F_e‖²/w + w‖F_f‖²)`, `rw ≤ 1`,
the tail norm is at least `(1 − rw)(1 − ε) H_k ∫_k^b Φ²`: the plateau `τ_k ≤ 1/((1 − rw)(1 − ε)H_k)`, jointly in the direction.
-/

namespace Cvs.L2a.FarMassPlateau

open Real Set MeasureTheory
open Cvs.L2a.TailOfModes

/-- The mass of mode `m` of the far part of `Φ` beyond `k`: `∫_{max 1 (k/m)}^b Φ(mθ)² dθ`. -/
noncomputable def farMode (Φ : ℝ → ℝ) (b : ℝ) (k m : ℕ) : ℝ :=
  ∫ θ in (max 1 ((k : ℝ) / m))..b, Φ (m * θ) ^ 2

/-- The harmonic number `H_k = Σ_{m ≤ k} 1/m`. -/
noncomputable def harm (k : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 k, 1 / (m : ℝ)

/-- **A far mode `m ≤ k` carries the far mass over `m`**: `farMode(m) ≥ (1/m) ∫_k^b Φ²`. -/
theorem farMode_ge {Φ : ℝ → ℝ} {b : ℝ} {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) (hkb : (k : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (k * b))) :
    (1 / (m : ℝ)) * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 ≤ farMode Φ b k m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hb1 : (1 : ℝ) ≤ b := le_trans (le_trans hm1 hmk') hkb
  have hkm1 : (1 : ℝ) ≤ k / m := by rw [le_div_iff₀ hm0]; linarith
  unfold farMode
  rw [max_eq_right hkm1, intervalIntegral.integral_comp_mul_left (fun ξ => Φ ξ ^ 2) hm0.ne', smul_eq_mul, one_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have e : (m : ℝ) * (k / m) = k := by field_simp
  rw [e]
  have hb' : b ≤ m * b := by
    have h := mul_le_mul_of_nonneg_right hm1 (show (0 : ℝ) ≤ b by linarith)
    rw [one_mul] at h
    exact h
  have hsub : Icc (k : ℝ) (m * b) ⊆ Icc 1 (k * b) :=
    Icc_subset_Icc (le_trans hm1 hmk') (mul_le_mul_of_nonneg_right hmk' (by linarith))
  exact intervalIntegral.integral_mono_interval le_rfl hkb hb'
    (Filter.Eventually.of_forall fun ξ => sq_nonneg (Φ ξ))
    (((hcont.mono hsub).pow 2).intervalIntegrable_of_Icc (hkb.trans hb'))

/-- **The far modes sum to at least `H_k` times the far mass.** -/
theorem farSum_ge_harmonic {Φ : ℝ → ℝ} {M k : ℕ} {b : ℝ} (hk : 1 ≤ k) (hkM : k ≤ M) (hkb : (k : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b))) :
    harm k * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 ≤ ∑ m ∈ Finset.Icc 1 M, farMode Φ b k m := by
  have hb1 : (1 : ℝ) ≤ b := le_trans (by exact_mod_cast hk) hkb
  have hM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hcont' : ContinuousOn Φ (Icc 1 (k * b)) :=
    hcont.mono (Icc_subset_Icc le_rfl (mul_le_mul_of_nonneg_right hM' (by linarith)))
  have hnn : ∀ m ∈ Finset.Icc 1 M, 0 ≤ farMode Φ b k m := fun m hm => by
    rw [Finset.mem_Icc] at hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
    have hm0 : (0 : ℝ) < m := by linarith
    unfold farMode
    apply intervalIntegral.integral_nonneg _ (fun θ _ => sq_nonneg _)
    apply max_le hb1
    rw [div_le_iff₀ hm0]
    nlinarith
  calc harm k * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2
      = ∑ m ∈ Finset.Icc 1 k, (1 / (m : ℝ)) * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 := by
        unfold harm; rw [Finset.sum_mul]
    _ ≤ ∑ m ∈ Finset.Icc 1 k, farMode Φ b k m := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Icc] at hm
        exact farMode_ge hm.1 hm.2 hkb hcont'
    _ ≤ ∑ m ∈ Finset.Icc 1 M, farMode Φ b k m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hkM) (fun m hm _ => hnn m hm)

/-- **The norm of a sum from a correlation bound**: with `N = A + 2C + B`, `−r(A/w + wB) ≤ 2C` and `r ≤ w`,
`(1 − rw) B ≤ N`. -/
theorem norm_ge_of_corr {N A B C r w : ℝ} (hN : N = A + 2 * C + B) (hA : 0 ≤ A) (hB : 0 ≤ B) (hw : 0 < w)
    (hr : 0 ≤ r) (hrw : r ≤ w) (hcorr : -(r * (A / w + w * B)) ≤ 2 * C) : (1 - r * w) * B ≤ N := by
  have h1 : r / w ≤ 1 := by rw [div_le_one hw]; exact hrw
  have h2 : r * (A / w) ≤ A := by
    calc r * (A / w) = (r / w) * A := by field_simp
      _ ≤ 1 * A := mul_le_mul_of_nonneg_right h1 hA
      _ = A := one_mul A
  have h3 : r * (A / w + w * B) = r * (A / w) + (r * w) * B := by ring
  nlinarith

/-- **The far-mass plateau, jointly in the direction**: for a tail split `F = F_e + F_f` whose far part's mode masses
are `farMode`, with the far cross terms at least `−ε` times those masses, the edge–far pairing at least
`−r(‖F_e‖²/w + w‖F_f‖²)`, `r ≤ w` and `rw ≤ 1`: `(1 − rw)(1 − ε) H_k ∫_k^b Φ² ≤ ∫F²`. -/
theorem plateau {Φ Fe Ff : ℝ → ℝ} {M k : ℕ} {b r w ε : ℝ} (hk : 1 ≤ k) (hkM : k ≤ M) (hkb : (k : ℝ) ≤ b)
    (hcont : ContinuousOn Φ (Icc 1 (M * b)))
    (hsplit : ∀ θ, tailF Φ M b θ = Fe θ + Ff θ)
    (hFe : IntegrableOn (fun θ => Fe θ ^ 2) (Ioi 1)) (hFf : IntegrableOn (fun θ => Ff θ ^ 2) (Ioi 1))
    (hFef : IntegrableOn (fun θ => Fe θ * Ff θ) (Ioi 1))
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hfar : (1 - ε) * ∑ m ∈ Finset.Icc 1 M, farMode Φ b k m ≤ ∫ θ in Ioi 1, Ff θ ^ 2)
    (hw : 0 < w) (hr : 0 ≤ r) (hrw : r ≤ w) (hrw1 : r * w ≤ 1)
    (hcorr : -(r * ((∫ θ in Ioi 1, Fe θ ^ 2) / w + w * ∫ θ in Ioi 1, Ff θ ^ 2))
      ≤ 2 * ∫ θ in Ioi 1, Fe θ * Ff θ) :
    (1 - r * w) * (1 - ε) * harm k * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := by
  have hb1 : (1 : ℝ) ≤ b := le_trans (by exact_mod_cast hk) hkb
  -- the norm expands over the split
  have hN : ∫ θ in Ioi 1, tailF Φ M b θ ^ 2
      = (∫ θ in Ioi 1, Fe θ ^ 2) + 2 * (∫ θ in Ioi 1, Fe θ * Ff θ) + ∫ θ in Ioi 1, Ff θ ^ 2 := by
    have e : (fun θ => tailF Φ M b θ ^ 2) = fun θ => Fe θ ^ 2 + 2 * (Fe θ * Ff θ) + Ff θ ^ 2 := by
      funext θ; rw [hsplit θ]; ring
    have h12 : ∫ θ in Ioi 1, (Fe θ ^ 2 + 2 * (Fe θ * Ff θ))
        = (∫ θ in Ioi 1, Fe θ ^ 2) + ∫ θ in Ioi 1, 2 * (Fe θ * Ff θ) :=
      integral_add hFe (hFef.const_mul 2)
    have h123 : ∫ θ in Ioi 1, (Fe θ ^ 2 + 2 * (Fe θ * Ff θ) + Ff θ ^ 2)
        = (∫ θ in Ioi 1, (Fe θ ^ 2 + 2 * (Fe θ * Ff θ))) + ∫ θ in Ioi 1, Ff θ ^ 2 :=
      integral_add (hFe.add (hFef.const_mul 2)) hFf
    rw [e, h123, h12, integral_const_mul]
  have hA : 0 ≤ ∫ θ in Ioi 1, Fe θ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have hB : 0 ≤ ∫ θ in Ioi 1, Ff θ ^ 2 := setIntegral_nonneg measurableSet_Ioi fun θ _ => sq_nonneg _
  have h1 := norm_ge_of_corr hN hA hB hw hr hrw hcorr
  have h2 := farSum_ge_harmonic hk hkM hkb hcont
  have hrw1 : 0 ≤ 1 - r * w := by linarith
  have hε' : 0 ≤ 1 - ε := by linarith
  have hfarm : 0 ≤ ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2 := intervalIntegral.integral_nonneg hkb (fun ξ _ => sq_nonneg _)
  have hharm : 0 ≤ harm k := by
    unfold harm; apply Finset.sum_nonneg; intro m _; positivity
  calc (1 - r * w) * (1 - ε) * harm k * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2
      = (1 - r * w) * ((1 - ε) * (harm k * ∫ ξ in (k : ℝ)..b, Φ ξ ^ 2)) := by ring
    _ ≤ (1 - r * w) * ((1 - ε) * ∑ m ∈ Finset.Icc 1 M, farMode Φ b k m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hε') hrw1
    _ ≤ (1 - r * w) * ∫ θ in Ioi 1, Ff θ ^ 2 := mul_le_mul_of_nonneg_left hfar hrw1
    _ ≤ ∫ θ in Ioi 1, tailF Φ M b θ ^ 2 := h1

end Cvs.L2a.FarMassPlateau
