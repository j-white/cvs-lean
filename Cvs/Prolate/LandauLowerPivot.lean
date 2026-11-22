import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.AngularEdgeValueNonzero
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LandauHalfCosineSpan
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.PlungeMassTrace
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SincTopIsRung

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Landau's lower pivot: an even rung with `n − 1` even levels below it and `λ ≥ ½` at `c = πn`

The rungs of index `< n − 1` span at most `n − 1` dimensions, so some `f = Σ_{k<n} a_k cos(πkt)` is orthogonal to all
of them; Cvs.Prolate.LandauHalfCosineSpan gives `⟨Kf, f⟩ ≥ ½‖f‖²`, Cvs.Prolate.SincTopIsRung a rung `g` orthogonal to them with `λ ≥ ½`, and orthogonality forces the
level of `g` to have index at least `n − 1`.
-/

noncomputable section

open Real Set MeasureTheory
open scoped Interval

namespace Cvs.Prolate.LandauLowerPivot

open Cvs.Prolate.EvenRungsByIndex Cvs.Prolate.EdgeCentreSign Cvs.Prolate.RegularSolutionEdge

/-- **Two even angular solutions at one level pair to a nonzero multiple**: `∫ g · w ≠ 0` for `w` normalised. -/
theorem integral_mul_ne_zero_of_level {c χ : ℝ} {g g₁ g₂ w w₁ w₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hgang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hgeven : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s) (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0)
    (hw : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt w (w₁ s) s) (hw₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt w₁ (w₂ s) s)
    (hwang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * w₂ s - 2 * s * w₁ s - c ^ 2 * s ^ 2 * w s + χ * w s = 0)
    (hweven : ∀ s ∈ Icc (-1 : ℝ) 1, w (-s) = w s) (hwnorm : ∫ s in (-1 : ℝ)..1, w s ^ 2 = 1) :
    ∫ s in (-1 : ℝ)..1, g s * w s ≠ 0 := by
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg0
  have hg1 : g 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hg hg₁ hgang hs₀ hgs₀
  have hw0 : ∃ s ∈ Icc (-1 : ℝ) 1, w s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : ∫ s in (-1 : ℝ)..1, w s ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => by
        rw [uIcc_of_le (by norm_num)] at hs
        simp [hcon s hs])]
      simp
    rw [hwnorm] at this
    exact one_ne_zero this
  obtain ⟨t₀, ht₀, hwt₀⟩ := hw0
  have hw1 : w 1 ≠ 0 := Cvs.Prolate.AngularEdgeValueNonzero.edge_ne_zero hw hw₁ hwang ht₀ hwt₀
  have hrg := angular_eq_mul_regSol hg hg₁ hgang
  have hrw := angular_eq_mul_regSol hw hw₁ hwang
  have hprop : ∀ s ∈ Icc (-1 : ℝ) 1, g s = g 1 / w 1 * w s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · have hs' : (1 : ℝ) ∈ Ioc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
      have e1 := hgeven 1 ⟨by norm_num, le_rfl⟩
      have e2 := hweven 1 ⟨by norm_num, le_rfl⟩
      rw [← h1, e1, e2]
      field_simp
    · rw [hrg s ⟨h1, hs.2⟩, hrw s ⟨h1, hs.2⟩]
      field_simp
  have hint : ∫ s in (-1 : ℝ)..1, g s * w s = g 1 / w 1 * ∫ s in (-1 : ℝ)..1, w s ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    simp only [hprop s hs]
    ring
  rw [hint, hwnorm, mul_one]
  exact div_ne_zero hg1 hw1

/-- **Landau's lower pivot at `c = πn`**: some even angular rung has at least `n − 1` even levels below it and
concentration `(μ√(c/2π))² ≥ ½`. -/
theorem landau_lower_pi (n : ℕ) (hn : 1 ≤ n) : Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (π * n) (n - 1) := by
  classical
  set c := π * (n : ℝ) with hcdef
  have hc : 0 < c := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  -- the rungs of index `< n − 1`
  let ι := {k : Fin (n - 1) // ∃ χ, IsLevelIdx c (k : ℕ) χ}
  have hex : ∀ i : ι, ∃ χ, IsLevelIdx c ((i : Fin (n - 1)) : ℕ) χ := fun i => i.2
  let w : ι → ℝ → ℝ := fun i => rung c ((i : Fin (n - 1)) : ℕ)
  -- a test function orthogonal to them
  let Φ : (Fin n → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun a i => ∫ s in (-1 : ℝ)..1, Cvs.Prolate.LandauHalfCosineSpan.cosPoly a s * w i s
      map_add' := fun a b => by
        funext i
        simp only [Pi.add_apply]
        rw [← intervalIntegral.integral_add]
        · refine intervalIntegral.integral_congr fun s _ => ?_
          unfold Cvs.Prolate.LandauHalfCosineSpan.cosPoly
          simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        · exact ((Cvs.Prolate.LandauHalfCosineSpan.continuous_cosPoly a).continuousOn.mul
            (continuousOn_rung (hex i))).intervalIntegrable_of_Icc (by norm_num)
        · exact ((Cvs.Prolate.LandauHalfCosineSpan.continuous_cosPoly b).continuousOn.mul
            (continuousOn_rung (hex i))).intervalIntegrable_of_Icc (by norm_num)
      map_smul' := fun t a => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun s _ => ?_
        unfold Cvs.Prolate.LandauHalfCosineSpan.cosPoly
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring }
  have hdim : Module.finrank ℝ (ι → ℝ) < Module.finrank ℝ (Fin n → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]
    have : Fintype.card ι ≤ n - 1 := (Fintype.card_subtype_le _).trans (by simp)
    omega
  obtain ⟨a, haK, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hdim)
  have hΦ : ∀ i : ι, ∫ s in (-1 : ℝ)..1, Cvs.Prolate.LandauHalfCosineSpan.cosPoly a s * w i s = 0 := by
    intro i
    have := congrFun (LinearMap.mem_ker.1 haK) i
    exact this
  set f := Cvs.Prolate.LandauHalfCosineSpan.cosPoly a with hfdef
  have hf : Continuous f := Cvs.Prolate.LandauHalfCosineSpan.continuous_cosPoly a
  have hfeven : ∀ s, f (-s) = f s := Cvs.Prolate.LandauHalfCosineSpan.cosPoly_neg a
  have hf0 : 0 < ∫ s in (-1 : ℝ)..1, f s ^ 2 := by
    have h1 := Cvs.Prolate.LandauHalfCosineSpan.sum_sq_le_integral_cosPoly_sq a
    have h2 : 0 < ∑ k : Fin n, a k ^ 2 := by
      obtain ⟨k, hk⟩ := Function.ne_iff.1 ha0
      exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk)))
        (Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ k))
    linarith
  have hK : 1 / 2 * ∫ s in (-1 : ℝ)..1, f s ^ 2
      ≤ c / π * ∫ ξ in (0 : ℝ)..1, Cvs.L2a.AngularProlateTailPositive.psi c f ξ ^ 2 := by
    have h1 := Cvs.Prolate.LandauHalfCosineSpan.sincForm_ge_half hn a
    rw [Cvs.Prolate.LandauHalfCosineSpan.sincForm_eq hc hf hfeven] at h1
    exact h1
  -- the rung
  obtain ⟨χ, μ, g, g₁, g₂, hg, hg₁, hg₂c, hang, heven, hg0, hμ, horth, hhalf⟩ :=
    Cvs.Prolate.SincTopIsRung.exists_rung_of_test (ι := ι) hc (w := w)
      (w₁ := fun i => rung₁ c ((i : Fin (n - 1)) : ℕ)) (w₂ := fun i => rung₂ c ((i : Fin (n - 1)) : ℕ))
      (χw := fun i => lev c ((i : Fin (n - 1)) : ℕ)) (μw := fun i => muR c ((i : Fin (n - 1)) : ℕ))
      (fun i => (rung_spec (hex i)).1) (fun i => (rung_spec (hex i)).2.1) (fun i => (rung_spec (hex i)).2.2.1)
      (fun i => (rung_spec (hex i)).2.2.2.1) (fun i => (rung_spec (hex i)).2.2.2.2.1) (fun i => psi_rung (hex i))
      hf hfeven hf0 hΦ hK
  refine ⟨χ, μ, g, g₁, g₂, hg, hg₁, hg₂c, hang, heven, hg0, hμ, ?_, hhalf⟩
  -- the count of the level of `g`
  by_contra hlt
  push Not at hlt
  set m := (evenSpec (sqC c) ∩ Iio χ).ncard with hm
  have hχmem : χ ∈ evenSpec (sqC c) := mem_evenSpec_of_angular hg hg₁ hang heven hg0
  have hidx : IsLevelIdx c m χ := ⟨hχmem, rfl⟩
  let i : ι := ⟨⟨m, hlt⟩, ⟨χ, hidx⟩⟩
  have hlev : lev c m = χ := lev_eq hidx
  obtain ⟨hr, hr₁, -, hrang, hreven, hrnorm⟩ := rung_spec (hex i)
  have hrang' : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * rung₂ c m s - 2 * s * rung₁ c m s
      - c ^ 2 * s ^ 2 * rung c m s + χ * rung c m s = 0 := by
    intro s hs
    have := hrang s hs
    rwa [show ((i : Fin (n - 1)) : ℕ) = m from rfl, hlev] at this
  exact integral_mul_ne_zero_of_level hg hg₁ hang heven hg0 hr hr₁ hrang' hreven hrnorm (horth i)

/-- **Landau's lower pivot at `c = 2πx`**: `LandauLower (2πx) (2x − 1)`. -/
theorem landau_lower_pivot (x : ℕ) (hx : 80 ≤ 2 * π * x) :
    Cvs.Prolate.LandauHalfEvenSpectrum.LandauLower (2 * π * x) (2 * x - 1) := by
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hx; simp at hx; linarith
    · exact h
  have h := landau_lower_pi (2 * x) (by omega)
  have hcn : π * ((2 * x : ℕ) : ℝ) = 2 * π * x := by push_cast; ring
  rwa [hcn] at h

end Cvs.Prolate.LandauLowerPivot
