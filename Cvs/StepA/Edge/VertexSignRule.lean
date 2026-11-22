import Mathlib
import Cvs.StepA.Edge.ComplexWeightDiscriminant
import Cvs.StepA.Edge.EdgePencil
import Cvs.StepA.Edge.EdgePencilOperators
import Cvs.StepA.Edge.EdgeSpace
import Cvs.StepA.Edge.InteractionFrame
import Cvs.StepA.Edge.VertexChains
import Cvs.StepA.Edge.VertexEigenvalues
import Cvs.Upstream.RayleighQuotientExtremes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The sign rule at a vertex and the classification of touching vertices

Along the orbit through a vertex the edge discriminant is positive just after it when `κ` does not
vanish on `E₊` (the forward rule), and positive just before a top-start vertex (odd-chains
Theorem B). By the chain theorem these exhaust every type but bottom start, so a vertex with `s ≤ 0`
on a two-sided orbit interval is bottom-start (merged §4, Lemma C).
-/

noncomputable section

open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : EdgeData ι} {z : ι → ℂ}

/-- `e^{δx} s > 0` gives `s > 0`. -/
theorem edgeDiscZ_pos_of_scaled {x : ℝ} {w : ι → ℂ} [Nonempty ι]
    (h : 0 < Real.exp (P.δ * x) * lamMax (opA P w) + Real.exp (P.δ * x) * lamMin (opA P w)) :
    0 < edgeDiscZ P.δ P.g w := by
  rw [edgeDiscZ_eq]
  by_contra hc
  push Not at hc
  have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (P.δ * x)).le hc
  linarith

variable [Nonempty ι]

-- merged §1 S, forward
/-- **The forward rule**: at a vertex where `κ` does not vanish on `E₊`,
`s(t) > 0` for all small `t > 0` along the orbit. -/
theorem IsVertex.sign_forward (hv : IsVertex P z) (hk : ∃ w ∈ Eplus P z, ⟪kap P, w⟫ ≠ 0) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε, 0 < edgeDiscZ P.δ P.g (flow P.g t 0 z) := by
  have hσ := hv.sig_pos
  obtain ⟨w₀, hw₀, hk₀⟩ := hk
  have hw₀0 : w₀ ≠ 0 := by rintro rfl; simp at hk₀
  have hn : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀0
  set w := ‖w₀‖⁻¹ • w₀ with hwdef
  have hw : w ∈ Eplus P z := Submodule.smul_mem _ _ hw₀
  have hw1 : ‖w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  set k := ⟪kap P, w⟫ with hkdef
  have hk : k ≠ 0 := by
    rw [hkdef, real_inner_smul_right]; exact mul_ne_zero (inv_ne_zero hn.ne') hk₀
  have hk2 : 0 < k ^ 2 := by positivity
  have hEm : ∀ v ∈ Eminus P z, ⟪kap P, v⟫ = 0 := fun v hv' =>
    (mul_eq_zero.mp (hv.kap_mul_eq_zero hw₀ hv')).resolve_left hk₀
  obtain ⟨ct, htop⟩ := top_trial P z
  obtain ⟨cb, rb, hrb, hbot⟩ := bottom_bound P z hv
  obtain ⟨Cc, hCc⟩ := fInt_le_cube P
  obtain ⟨Cl, hCl⟩ := fInt_ge_linear P
  set σ := sig P z with hσdef
  set K := |ct| + |cb| with hKdef
  set C₃ := |Cc| with hC₃
  set C₂ := |Cl| with hC₂
  have hK0 : 0 ≤ K := by positivity
  have hctK : ct ≤ K := (le_abs_self ct).trans (by linarith [abs_nonneg cb])
  have hcbK : cb ≤ K := (le_abs_self cb).trans (by linarith [abs_nonneg ct])
  set A := σ / 4 * C₂ + (σ / 2 + K) * C₃ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨min (min 1 rb) (min (σ / (4 * (K + 1))) (σ * k ^ 2 / (4 * (A + 1)))),
    lt_min (lt_min one_pos hrb) (lt_min (by positivity) (by positivity)), fun t ht => ?_⟩
  obtain ⟨ht0, htr⟩ := ht
  simp only [lt_min_iff] at htr
  obtain ⟨⟨ht1, htb⟩, hta, htc⟩ := htr
  have hat : |t| = t := abs_of_pos ht0
  obtain ⟨v, hv', hv1, hB⟩ := hbot t 0 (by rw [hat]; exact htb) (by simpa using hrb)
  have hT := htop t 0 (by rw [hat]; exact ht1.le) (by simp) w hw hw1
  simp only [zero_mul, abs_zero, mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at hB hT
  set Fw := fInt P w t with hFw
  set Fv := fInt P v t with hFv
  have hFw0 : 0 ≤ Fw := fInt_nonneg P w ht0.le
  have hFv0 : 0 ≤ Fv := fInt_nonneg P v ht0.le
  rw [hat, abs_of_nonneg hFw0] at hT
  rw [hat, abs_of_nonneg hFv0] at hB
  have hFvc : Fv ≤ C₃ * t ^ 3 := by
    have h := hCc v (hEm v hv') t (by rw [hat]; exact ht1.le)
    rw [hv1, abs_of_nonneg hFv0, hat, one_pow, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self Cc) (by positivity))
  have hFwl : k ^ 2 * t - C₂ * t ^ 2 ≤ Fw := by
    have h := hCl w t ht0.le ht1.le
    rw [hw1, one_pow, mul_one] at h
    have : Cl * t ^ 2 ≤ C₂ * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self Cl) (by positivity)
    linarith
  have hKt : K * t ≤ σ / 4 := by
    calc K * t ≤ K * (σ / (4 * (K + 1))) := mul_le_mul_of_nonneg_left hta.le hK0
      _ ≤ σ / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        have : σ * (4 * (K + 1)) = K * σ * 4 + 4 * σ := by ring
        linarith
  have hw' : σ / 4 * Fw ≤ σ / 2 * Fw - ct * t * Fw := by
    have : ct * t ≤ σ / 4 := (mul_le_mul_of_nonneg_right hctK ht0.le).trans hKt
    have := mul_le_mul_of_nonneg_right this hFw0
    linarith
  have hv'' : σ / 2 * Fv + cb * t * Fv ≤ (σ / 2 + K) * C₃ * t ^ 3 := by
    have h1 : cb * t ≤ K := by
      calc cb * t ≤ K * t := mul_le_mul_of_nonneg_right hcbK ht0.le
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left ht1.le hK0
        _ = K := mul_one K
    have h2 := mul_le_mul_of_nonneg_right h1 hFv0
    have h3 : (σ / 2 + K) * Fv ≤ (σ / 2 + K) * (C₃ * t ^ 3) :=
      mul_le_mul_of_nonneg_left hFvc (by positivity)
    linarith
  have hlin : σ / 4 * (k ^ 2 * t - C₂ * t ^ 2) ≤ σ / 4 * Fw :=
    mul_le_mul_of_nonneg_left hFwl (by positivity)
  have habs : σ / 4 * C₂ * t ^ 2 + (σ / 2 + K) * C₃ * t ^ 3 < σ / 4 * k ^ 2 * t := by
    have ht2 : t ^ 2 ≤ t := by rw [sq]; exact mul_le_of_le_one_right ht0.le ht1.le
    have ht3 : t ^ 3 ≤ t ^ 2 := by
      rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) ht1.le
    have h1 : σ / 4 * C₂ * t ^ 2 + (σ / 2 + K) * C₃ * t ^ 3 ≤ A * t ^ 2 := by
      have := mul_le_mul_of_nonneg_left ht3 (show 0 ≤ (σ / 2 + K) * C₃ by positivity)
      rw [hA]
      linarith
    have h5 : t * (4 * (A + 1)) < σ * k ^ 2 := by
      have := htc
      rwa [lt_div_iff₀ (by positivity)] at this
    have h6 : A * t < σ / 4 * k ^ 2 := by linarith
    calc σ / 4 * C₂ * t ^ 2 + (σ / 2 + K) * C₃ * t ^ 3 ≤ A * t ^ 2 := h1
      _ = A * t * t := by ring
      _ < σ / 4 * k ^ 2 * t := mul_lt_mul_of_pos_right h6 ht0
  refine edgeDiscZ_pos_of_scaled (x := t) ?_
  linarith

-- odd-chains, the backward rule at a top-start vertex
/-- **Theorem B**: `s(−t) > 0` for all small
`t > 0` along the orbit. -/
theorem TopStart.sign_backward (ht : TopStart P z) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo 0 ε, 0 < edgeDiscZ P.δ P.g (flow P.g (-t) 0 z) := by
  have hv := ht.1
  have hσ := hv.sig_pos
  obtain ⟨ct, htop⟩ := top_trial P z
  obtain ⟨cb, rb, hrb, hbot⟩ := bottom_bound P z hv
  obtain ⟨c1, hc1, hc1w⟩ := exists_opDinv_lower P
  set σ := sig P z with hσdef
  set K := |ct| + |cb| with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hctK : ct ≤ K := (le_abs_self ct).trans (by linarith [abs_nonneg cb])
  have hcbK : cb ≤ K := (le_abs_self cb).trans (by linarith [abs_nonneg ct])
  refine ⟨min (min 1 rb) (min (σ / (8 * (K + 1))) (σ * c1 / (σ + 2 * K + 2))),
    lt_min (lt_min one_pos hrb) (lt_min (by positivity) (by positivity)), fun t htt => ?_⟩
  obtain ⟨ht0, htr⟩ := htt
  simp only [lt_min_iff] at htr
  obtain ⟨⟨ht1, htb⟩, hta, htc⟩ := htr
  have hat : |-t| = t := by rw [abs_neg, abs_of_pos ht0]
  obtain ⟨v, hvm, hv1, hB⟩ := hbot (-t) 0 (by rw [hat]; exact htb) (by simpa using hrb)
  simp only [zero_mul, abs_zero, mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at hB
  obtain ⟨hDm, hDk⟩ := ht.opDinv_mem hvm
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv1
  have ha : 0 < ‖opDinv P v‖ := by
    refine norm_pos_iff.mpr fun h0 => hv0 ?_
    have := opD_opDinv P v
    rw [h0, map_zero] at this
    exact this.symm
  set a := ‖opDinv P v‖ with hadef
  set w := a⁻¹ • opDinv P v with hwdef
  have hw : w ∈ Eplus P z := Submodule.smul_mem _ _ hDm
  have hw1 : ‖w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ha.ne']
  have hT := htop (-t) 0 (by rw [hat]; exact ht1.le) (by simp) w hw hw1
  simp only [zero_mul, abs_zero, mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at hT
  set Fv := fInt P v (-t) with hFv
  set Fw := fInt P w (-t) with hFw
  have hFv0 : Fv ≤ 0 := fInt_nonpos P v (by linarith)
  have hFw0 : Fw ≤ 0 := fInt_nonpos P w (by linarith)
  rw [hat, abs_of_nonpos hFw0] at hT
  rw [hat, abs_of_nonpos hFv0] at hB
  have hca : c1 ≤ a ^ 2 := hc1w v hv1
  have hFwb : -Fw ≤ t ^ 2 / (8 * c1) * -Fv := by
    have hH := hardy P hDk (-t)
    rw [neg_sq, abs_of_nonpos hFv0] at hH
    have e : Fw = fInt P (opDinv P v) (-t) / a ^ 2 := by
      rw [hFw, hwdef, fInt_smul, inv_pow, div_eq_inv_mul]
    have hD0 : fInt P (opDinv P v) (-t) ≤ 0 := fInt_nonpos P _ (by linarith)
    rw [abs_of_nonpos hD0] at hH
    rw [e, ← neg_div, div_le_iff₀ (by positivity)]
    calc -fInt P (opDinv P v) (-t) ≤ t ^ 2 / 8 * -Fv := hH
      _ = t ^ 2 / (8 * c1) * -Fv * c1 := by field_simp
      _ ≤ t ^ 2 / (8 * c1) * -Fv * a ^ 2 :=
          mul_le_mul_of_nonneg_left hca
            (mul_nonneg (by positivity) (by linarith))
  have hKt : K * t ≤ σ / 8 := by
    calc K * t ≤ K * (σ / (8 * (K + 1))) := mul_le_mul_of_nonneg_left hta.le hK0
      _ ≤ σ / 8 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        have : σ * (8 * (K + 1)) = K * σ * 8 + 8 * σ := by ring
        linarith
  have ht2 : t ^ 2 ≤ σ * c1 / (σ + 2 * K + 2) := by
    have : t ^ 2 ≤ t := by rw [sq]; exact mul_le_of_le_one_right ht0.le ht1.le
    linarith
  have hB1 : cb * t * -Fv ≤ σ / 8 * -Fv := by
    have : cb * t ≤ σ / 8 := (mul_le_mul_of_nonneg_right hcbK ht0.le).trans hKt
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hB2 : σ / 2 * -Fw + ct * t * -Fw ≤ σ / 8 * -Fv := by
    have h1 : ct * t ≤ K := by
      calc ct * t ≤ K * t := mul_le_mul_of_nonneg_right hctK ht0.le
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left ht1.le hK0
        _ = K := mul_one K
    have h2 : (σ / 2 + K) * (t ^ 2 / (8 * c1)) ≤ σ / 8 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      have h3 : (σ / 2 + K) * t ^ 2 ≤ (σ / 2 + K) * (σ * c1 / (σ + 2 * K + 2)) :=
        mul_le_mul_of_nonneg_left ht2 (by positivity)
      have h4 : (σ / 2 + K) * (σ * c1 / (σ + 2 * K + 2)) ≤ σ * c1 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        calc (σ / 2 + K) * (σ * c1) ≤ (σ + 2 * K + 2) * (σ * c1) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = σ * c1 * (σ + 2 * K + 2) := by ring
      linarith
    have hFw' : 0 ≤ -Fw := by linarith
    calc σ / 2 * -Fw + ct * t * -Fw ≤ (σ / 2 + K) * -Fw := by
          have := mul_le_mul_of_nonneg_right h1 hFw'
          linarith
      _ ≤ (σ / 2 + K) * (t ^ 2 / (8 * c1) * -Fv) :=
          mul_le_mul_of_nonneg_left hFwb (by positivity)
      _ = (σ / 2 + K) * (t ^ 2 / (8 * c1)) * -Fv := by ring
      _ ≤ σ / 8 * -Fv := mul_le_mul_of_nonneg_right h2 (by linarith)
  have hFvn : Fv < 0 := lt_of_le_of_ne hFv0 (fInt_ne_zero P hv0 (by linarith))
  have hpos : 0 < σ / 4 * -Fv := mul_pos (by positivity) (by linarith)
  refine edgeDiscZ_pos_of_scaled (x := -t) ?_
  linarith

-- merged §4
/-- **Lemma C**: a vertex with `s ≤ 0` on a two-sided interval of its orbit line is
bottom-start. -/
theorem IsVertex.bottomStart_of_le (hv : IsVertex P z)
    (hle : ∃ ε > 0, ∀ x, |x| < ε → edgeDiscZ P.δ P.g (flow P.g x 0 z) ≤ 0) :
    BottomStart P z := by
  obtain ⟨ε, hε, hle⟩ := hle
  -- forward rule: `κ = 0` on `E₊`
  have hkp : ∀ w ∈ Eplus P z, ⟪kap P, w⟫ = 0 := by
    by_contra h
    push Not at h
    obtain ⟨ε', hε', hpos⟩ := hv.sign_forward h
    have ht : min ε ε' / 2 ∈ Set.Ioo 0 ε' :=
      ⟨by positivity, by linarith [min_le_right ε ε', lt_min hε hε']⟩
    have h1 := hpos _ ht
    have h2 := hle (min ε ε' / 2) (by
      rw [abs_of_pos (by positivity)]; linarith [min_le_left ε ε', lt_min hε hε'])
    linarith
  obtain ⟨H, l, hc⟩ := hv.exists_chain
  have hl : l - 1 < l := by have := hc.1; omega
  have htail : (opD P ^ (l - 1)) H ∈ Eminus P z := by
    have hk : ⟪kap P, (opD P ^ (l - 1)) H⟫ ≠ 0 := hc.2.2.2.2.1
    have hmem := hc.mem hl
    rcases hc.2.2.1 with hH | hH
    · have := hmem.1 hH
      split_ifs at this with he
      · exact absurd (hkp _ this) hk
      · exact this
    · have := hmem.2 hH
      split_ifs at this with he
      · exact this
      · exact absurd (hkp _ this) hk
  rcases hc.2.2.1 with hH | hH
  · -- a top-start vertex is positive just before it
    obtain ⟨ε', hε', hpos⟩ := (hc.topStart hv hH htail).sign_backward
    have ht : min ε ε' / 2 ∈ Set.Ioo 0 ε' :=
      ⟨by positivity, by linarith [min_le_right ε ε', lt_min hε hε']⟩
    have h1 := hpos _ ht
    have h2 := hle (-(min ε ε' / 2)) (by
      rw [abs_neg, abs_of_pos (by positivity)]; linarith [min_le_left ε ε', lt_min hε hε'])
    linarith
  · exact hc.bottomStart hv hH htail

end Cvs.StepA.Edge.PlanarBoxLemma
