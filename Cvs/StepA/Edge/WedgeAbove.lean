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
# The wedge above a bottom-start vertex

At a bottom-start vertex `(q, q+1)` the edge discriminant is negative on a punctured closed upper
half-disc of the orbit-heat plane, from the top eigenvector `w ∈ E₊` paired with the trial
`D⁻¹w ∈ K₋` (Hardy transfer, strict Cauchy–Schwarz) and, where `y` is small against `x³`, a bottom
eigenvector with `v(0) ≠ 0`.
-/

set_option maxHeartbeats 400000

noncomputable section

open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : EdgeData ι} {z : ι → ℂ}

-- Step 5
/-- **The strict Cauchy–Schwarz margin** at a bottom-start vertex: for some `c₀ > 0`
every unit `w ∈ E₊` has `c₀ + 1/‖D⁻¹w‖² ≤ ‖Dw‖²`. -/
theorem BottomStart.exists_strictCS (hb : BottomStart P z) :
    ∃ c₀ > 0, ∀ w ∈ Eplus P z, ‖w‖ = 1 → c₀ + 1 / ‖opDinv P w‖ ^ 2 ≤ ‖opD P w‖ ^ 2 := by
  have hne : ∀ w ∈ {w | w ∈ Eplus P z ∧ ‖w‖ = 1}, ‖opDinv P w‖ ^ 2 ≠ 0 := by
    rintro w ⟨-, hw1⟩ h
    have h0 : opDinv P w = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
    have := opD_opDinv P w
    rw [h0, map_zero] at this
    rw [← this, norm_zero] at hw1
    exact zero_ne_one hw1
  have h1 : Continuous (fun w : EdgeV P => ‖opD P w‖ ^ 2) := by fun_prop
  have h2 : Continuous (fun w : EdgeV P => ‖opDinv P w‖ ^ 2) := by fun_prop
  have h3 : ContinuousOn (fun w : EdgeV P => ‖opD P w‖ ^ 2 - 1 / ‖opDinv P w‖ ^ 2)
      {w | w ∈ Eplus P z ∧ ‖w‖ = 1} :=
    h1.continuousOn.sub (continuousOn_const.div₀ (f := fun _ : EdgeV P => (1 : ℝ))
      (g := fun w : EdgeV P => ‖opDinv P w‖ ^ 2) h2.continuousOn hne)
  obtain ⟨c, hc, hle⟩ := exists_pos_le_on_sphere (W := Eplus P z)
    (f := fun w => ‖opD P w‖ ^ 2 - 1 / ‖opDinv P w‖ ^ 2) h3
    (fun w hw hw1 => by
      have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
      have h := sq_norm_lt_opDinv_mul_opD P hw0 (by rw [hb.kap_Eplus hw, zero_mul])
      rw [hw1, one_pow] at h
      have hpos : 0 < ‖opDinv P w‖ := by
        rcases (norm_nonneg (opDinv P w)).lt_or_eq with h' | h'
        · exact h'
        · rw [← h', zero_mul] at h; linarith
      have : 1 / ‖opDinv P w‖ ^ 2 < ‖opD P w‖ ^ 2 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (opD P w)]
      show 0 < ‖opD P w‖ ^ 2 - 1 / ‖opDinv P w‖ ^ 2
      linarith)
  exact ⟨c, hc, fun w hw hw1 => by linarith [hle w hw hw1]⟩

variable [Nonempty ι]

/-- At a bottom-start vertex some unit `φ ∈ E₋` has `φ(0) ≠ 0`. -/
theorem BottomStart.exists_Eminus_kap_ne (hb : BottomStart P z) :
    ∃ φ ∈ Eminus P z, ‖φ‖ = 1 ∧ ⟪kap P, φ⟫ ≠ 0 := by
  have hp : Eplus P z ≤ (ℝ ∙ kap P)ᗮ := fun x hx =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hb.kap_Eplus hx)
  have hm : ¬ Eminus P z ≤ (ℝ ∙ kap P)ᗮ := fun hm => not_kap_zero_both P z ⟨hp, hm⟩
  obtain ⟨φ, hφ, hk⟩ := Set.not_subset.mp hm
  rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right] at hk
  have hφ0 : φ ≠ 0 := by rintro rfl; simp at hk
  have hn : 0 < ‖φ‖ := norm_pos_iff.mpr hφ0
  refine ⟨‖φ‖⁻¹ • φ, Submodule.smul_mem _ _ hφ, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · rw [real_inner_smul_right]
    exact mul_ne_zero (inv_ne_zero hn.ne') hk

/-! ### The trial `v_w = D⁻¹w/‖D⁻¹w‖` -/

/-- At a bottom-start vertex, `w ∈ E₊` unit gives the unit trial `v = D⁻¹w/‖D⁻¹w‖ ∈ E₋` with
`v(0) = 0`, `‖Dv‖² = 1/‖D⁻¹w‖²` and `F_v = F_{D⁻¹w}/‖D⁻¹w‖²`. -/
theorem BottomStart.trial (hb : BottomStart P z) {w : EdgeV P} (hw : w ∈ Eplus P z)
    (hw1 : ‖w‖ = 1) :
    0 < ‖opDinv P w‖ ∧ ⟪kap P, opDinv P w⟫ = 0 ∧
      (‖opDinv P w‖⁻¹ • opDinv P w) ∈ Eminus P z ∧ ⟪kap P, ‖opDinv P w‖⁻¹ • opDinv P w⟫ = 0 ∧
      ‖‖opDinv P w‖⁻¹ • opDinv P w‖ = 1 ∧
      ‖opD P (‖opDinv P w‖⁻¹ • opDinv P w)‖ ^ 2 = 1 / ‖opDinv P w‖ ^ 2 ∧
      ∀ x, fInt P (‖opDinv P w‖⁻¹ • opDinv P w) x
        = fInt P (opDinv P w) x / ‖opDinv P w‖ ^ 2 := by
  have hK := hb.opDinv_mem_Kminus hw
  rw [Kminus, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right] at hK
  have hpos : 0 < ‖opDinv P w‖ := by
    refine norm_pos_iff.mpr fun h0 => ?_
    have := opD_opDinv P w
    rw [h0, map_zero] at this
    rw [← this, norm_zero] at hw1
    exact zero_ne_one hw1
  refine ⟨hpos, hK.2, Submodule.smul_mem _ _ hK.1, ?_, ?_, ?_, fun x => ?_⟩
  · rw [real_inner_smul_right, hK.2, mul_zero]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
  · rw [map_smul, opD_opDinv, norm_smul, norm_inv, norm_norm, hw1, mul_one, inv_pow, one_div]
  · rw [fInt_smul, inv_pow, div_eq_inv_mul]

/-! ### The two halves of the wedge -/

/-- `e^{δx} s < 0` gives `s < 0`. -/
theorem edgeDiscZ_neg_of_scaled {x : ℝ} {w : ι → ℂ}
    (h : Real.exp (P.δ * x) * lamMax (opA P w) + Real.exp (P.δ * x) * lamMin (opA P w) < 0) :
    edgeDiscZ P.δ P.g w < 0 := by
  rw [edgeDiscZ_eq]
  by_contra hc
  push Not at hc
  have := mul_nonneg (Real.exp_pos (P.δ * x)).le hc
  linarith

-- odd-chains Theorem A Step 7
/-- **The wedge above, `x ≤ 0`**: at a bottom-start vertex
`s(x, y) < 0` for small `x ≤ 0 ≤ y`, `(x, y) ≠ 0`. -/
theorem BottomStart.wedgeAbove_left (hb : BottomStart P z) :
    ∃ r > 0, ∀ x y : ℝ, x ≤ 0 → 0 ≤ y → |x| < r → y < r → (x ≠ 0 ∨ y ≠ 0) →
      edgeDiscZ P.δ P.g (flow P.g x y z) < 0 := by
  have hσ := hb.1.sig_pos
  obtain ⟨ct, rt, hrt, htop⟩ := top_bound P z
  obtain ⟨cb, hbot⟩ := bottom_trial P z
  obtain ⟨c0, hc0, hcs⟩ := hb.exists_strictCS
  obtain ⟨c1, hc1, hc1w⟩ := exists_opDinv_lower P
  set σ := sig P z with hσdef
  set K := |ct| + |cb| with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hctK : ct ≤ K := (le_abs_self ct).trans (by linarith [abs_nonneg cb])
  have hcbK : cb ≤ K := (le_abs_self cb).trans (by linarith [abs_nonneg ct])
  refine ⟨min (min 1 rt) (min (σ / (8 * (K + 1)))
    (min (σ * c1 / (σ + 2 * K + 2)) (σ * c0 / (4 * (K + 1))))),
    lt_min (lt_min one_pos hrt) (lt_min (by positivity) (lt_min (by positivity) (by positivity))),
    fun x y hx0 hy0 hxr hyr hne => ?_⟩
  simp only [lt_min_iff] at hxr hyr
  obtain ⟨⟨hx1, hxt⟩, hxa, hxb, hxc⟩ := hxr
  obtain ⟨⟨hy1, hyt⟩, -, -, hyc⟩ := hyr
  have hay : |y| = y := abs_of_nonneg hy0
  have hax : |x| = -x := abs_of_nonpos hx0
  obtain ⟨w, hw, hw1, hL⟩ := htop x y hxt (by rw [hay]; exact hyt)
  obtain ⟨ha, hDk, hvm, hvk, hv1, hDv, hFv⟩ := hb.trial hw hw1
  set a := ‖opDinv P w‖ with hadef
  set v := a⁻¹ • opDinv P w with hvdef
  have hM := hbot x y hx1.le (by rw [hay]; exact hy1.le) v hvm hv1
  have czw : ⟪opAzeta P z w, w⟫ = -σ * (‖opD P w‖ ^ 2 - P.δ ^ 2) := by
    rw [inner_opAzeta_of_eig P (mem_Eplus.mp hw) (hb.kap_Eplus hw), hw1]; ring
  have czv : ⟪opAzeta P z v, v⟫ = σ * (1 / a ^ 2 - P.δ ^ 2) := by
    rw [inner_opAzeta_of_eig P (mem_Eminus.mp hvm) hvk, hv1, hDv]; ring
  have hcsw := hcs w hw hw1
  set F := fInt P w x with hFdef
  have hF0 : F ≤ 0 := fInt_nonpos P w hx0
  have hFv0 : fInt P v x ≤ 0 := fInt_nonpos P v hx0
  have hH := hardy P hDk x
  have hca : c1 ≤ a ^ 2 := hc1w w hw1
  -- `|F_v| ≤ x²/(8c₁) |F|`
  have hFvb : |fInt P v x| ≤ x ^ 2 / (8 * c1) * |F| := by
    rw [hFv x, abs_div, abs_of_pos (by positivity : 0 < a ^ 2), div_le_iff₀ (by positivity)]
    calc |fInt P (opDinv P w) x| ≤ x ^ 2 / 8 * |F| := hH
      _ = x ^ 2 / (8 * c1) * |F| * c1 := by field_simp
      _ ≤ x ^ 2 / (8 * c1) * |F| * a ^ 2 := mul_le_mul_of_nonneg_left hca (by positivity)
  -- the radius conditions
  have hKx : K * |x| ≤ σ / 8 := by
    calc K * |x| ≤ K * (σ / (8 * (K + 1))) := mul_le_mul_of_nonneg_left hxa.le hK0
      _ ≤ σ / 8 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        have : σ * (8 * (K + 1)) = K * σ * 8 + 8 * σ := by ring
        linarith
  have hx2 : x ^ 2 ≤ σ * c1 / (σ + 2 * K + 2) := by
    have : x ^ 2 ≤ |x| := by
      rw [← sq_abs, sq]
      calc |x| * |x| ≤ |x| * 1 := mul_le_mul_of_nonneg_left hx1.le (abs_nonneg x)
        _ = |x| := mul_one _
    linarith
  have hB1 : ct * |x| * |F| ≤ σ / 8 * |F| := by
    have : ct * |x| ≤ σ / 8 := (mul_le_mul_of_nonneg_right hctK (abs_nonneg x)).trans hKx
    exact mul_le_mul_of_nonneg_right this (abs_nonneg F)
  have hB2 : σ / 2 * |fInt P v x| + cb * |x| * |fInt P v x| ≤ σ / 8 * |F| := by
    have h1 : cb * |x| ≤ K := by
      calc cb * |x| ≤ K * |x| := mul_le_mul_of_nonneg_right hcbK (abs_nonneg x)
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left hx1.le hK0
        _ = K := mul_one K
    have h2 : (σ / 2 + K) * (x ^ 2 / (8 * c1)) ≤ σ / 8 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      have h3 : (σ / 2 + K) * x ^ 2 ≤ (σ / 2 + K) * (σ * c1 / (σ + 2 * K + 2)) :=
        mul_le_mul_of_nonneg_left hx2 (by positivity)
      have h4 : (σ / 2 + K) * (σ * c1 / (σ + 2 * K + 2)) ≤ σ * c1 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        calc (σ / 2 + K) * (σ * c1) ≤ (σ + 2 * K + 2) * (σ * c1) :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = σ * c1 * (σ + 2 * K + 2) := by ring
      linarith
    calc σ / 2 * |fInt P v x| + cb * |x| * |fInt P v x|
        ≤ (σ / 2 + K) * |fInt P v x| := by
          have := mul_le_mul_of_nonneg_right h1 (abs_nonneg (fInt P v x))
          linarith
      _ ≤ (σ / 2 + K) * (x ^ 2 / (8 * c1) * |F|) :=
          mul_le_mul_of_nonneg_left hFvb (by positivity)
      _ = (σ / 2 + K) * (x ^ 2 / (8 * c1)) * |F| := by ring
      _ ≤ σ / 8 * |F| := mul_le_mul_of_nonneg_right h2 (abs_nonneg F)
  have hB3 : y * (-σ * (‖opD P w‖ ^ 2 - P.δ ^ 2)) + y * (σ * (1 / a ^ 2 - P.δ ^ 2))
      ≤ -(y * σ * c0) := by
    have h1 : σ * (1 / a ^ 2 - ‖opD P w‖ ^ 2) ≤ σ * (-c0) :=
      mul_le_mul_of_nonneg_left (by linarith) hσ.le
    have h2 := mul_le_mul_of_nonneg_left h1 hy0
    linarith
  have hB4 : ct * (y ^ 2 + y * |x|) + cb * (y ^ 2 + y * |x|) ≤ y * σ * c0 / 2 := by
    have hyx : y + |x| ≤ σ * c0 / (2 * (K + 1)) := by
      have : σ * c0 / (4 * (K + 1)) + σ * c0 / (4 * (K + 1)) = σ * c0 / (2 * (K + 1)) := by
        field_simp; ring
      linarith
    have h1 : (ct + cb) * (y * (y + |x|)) ≤ K * (y * (y + |x|)) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self ct, le_abs_self cb])
        (by positivity)
    have h2 : K * (y * (y + |x|)) ≤ K * (y * (σ * c0 / (2 * (K + 1)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyx hy0) hK0
    have h3 : K * (y * (σ * c0 / (2 * (K + 1)))) ≤ y * σ * c0 / 2 := by
      rw [show K * (y * (σ * c0 / (2 * (K + 1)))) = y * σ * c0 / 2 * (K / (K + 1)) by
        field_simp]
      have h5 : K / (K + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      exact mul_le_of_le_one_right (by positivity) h5
    linarith
  rw [hay, czw, abs_of_nonpos hF0] at hL
  rw [hay, czv, abs_of_nonpos hFv0] at hM
  rw [abs_of_nonpos hF0] at hB1 hB2
  rw [abs_of_nonpos hFv0] at hB2
  have hsum : Real.exp (P.δ * x) * lamMax (opA P (flow P.g x y z))
      + Real.exp (P.δ * x) * lamMin (opA P (flow P.g x y z)) ≤ σ / 4 * F - y * σ * c0 / 2 := by
    linarith
  refine edgeDiscZ_neg_of_scaled (hsum.trans_lt ?_)
  rcases hne with hx | hy
  · have hFn : F ≠ 0 := fInt_ne_zero P (by rintro rfl; simp at hw1) hx
    have hFneg : F < 0 := lt_of_le_of_ne hF0 hFn
    have h1 : 0 ≤ y * σ * c0 / 2 := by positivity
    have h2 : σ / 4 * F < 0 := mul_neg_of_pos_of_neg (by positivity) hFneg
    linarith
  · have hy' : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
    have h1 : 0 < y * σ * c0 / 2 := by positivity
    have h2 : σ / 4 * F ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hF0
    linarith

-- odd-chains Theorem A Step 8
/-- **The wedge above, `x ≥ 0`**: at a bottom-start vertex
`s(x, y) < 0` for small `x, y ≥ 0`, `(x, y) ≠ 0`. -/
theorem BottomStart.wedgeAbove_right (hb : BottomStart P z) :
    ∃ r > 0, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x < r → y < r → (x ≠ 0 ∨ y ≠ 0) →
      edgeDiscZ P.δ P.g (flow P.g x y z) < 0 := by
  have hσ := hb.1.sig_pos
  obtain ⟨ct, rt, hrt, htop⟩ := top_bound P z
  obtain ⟨cb, hbot⟩ := bottom_trial P z
  obtain ⟨c0, hc0, hcs⟩ := hb.exists_strictCS
  obtain ⟨Cc, hCc⟩ := fInt_le_cube P
  obtain ⟨Cl, hCl⟩ := fInt_ge_linear P
  obtain ⟨φ, hφ, hφ1, hφk⟩ := hb.exists_Eminus_kap_ne
  set σ := sig P z with hσdef
  set k := ⟪kap P, φ⟫ with hkdef
  have hk2 : 0 < k ^ 2 := by positivity
  set K := |ct| + |cb| with hKdef
  set N := ‖opAzeta P z‖ with hNdef
  set C₃ := |Cc| with hC₃
  set C₂ := |Cl| with hC₂
  have hK0 : 0 ≤ K := by positivity
  have hN0 : 0 ≤ N := norm_nonneg _
  have hctK : ct ≤ K := (le_abs_self ct).trans (by linarith [abs_nonneg cb])
  have hcbK : cb ≤ K := (le_abs_self cb).trans (by linarith [abs_nonneg ct])
  set τ := 2 * ((σ / 2 + K) * C₃) / (σ * c0) with hτ
  have hτ0 : 0 ≤ τ := by positivity
  set B := 2 * N + 2 * K with hB
  have hB0 : 0 ≤ B := by positivity
  set A₃ := (σ / 2 + K) * C₃ + σ / 4 * C₂ with hA₃
  have hA₃0 : 0 ≤ A₃ := by positivity
  refine ⟨min (min 1 rt) (min (σ / (4 * (K + 1)))
    (min (σ * c0 / (4 * (K + 1))) (min (σ * k ^ 2 / (8 * (A₃ + 1)))
      (σ * k ^ 2 / (8 * (B * τ + 1)))))),
    lt_min (lt_min one_pos hrt) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity)))),
    fun x y hx0 hy0 hxr hyr hne => ?_⟩
  simp only [lt_min_iff] at hxr hyr
  obtain ⟨⟨hx1, hxt⟩, hxa, hxc, hxd, hxe⟩ := hxr
  obtain ⟨⟨hy1, hyt⟩, -, hyc, -, -⟩ := hyr
  have hay : |y| = y := abs_of_nonneg hy0
  have hax : |x| = x := abs_of_nonneg hx0
  obtain ⟨w, hw, hw1, hL⟩ := htop x y (by rw [hax]; exact hxt) (by rw [hay]; exact hyt)
  obtain ⟨ha, hDk, hvm, hvk, hv1, hDv, -⟩ := hb.trial hw hw1
  set a := ‖opDinv P w‖ with hadef
  set v := a⁻¹ • opDinv P w with hvdef
  have hMv := hbot x y (by rw [hax]; exact hx1.le) (by rw [hay]; exact hy1.le) v hvm hv1
  have hMφ := hbot x y (by rw [hax]; exact hx1.le) (by rw [hay]; exact hy1.le) φ hφ hφ1
  have czw : ⟪opAzeta P z w, w⟫ = -σ * (‖opD P w‖ ^ 2 - P.δ ^ 2) := by
    rw [inner_opAzeta_of_eig P (mem_Eplus.mp hw) (hb.kap_Eplus hw), hw1]; ring
  have czv : ⟪opAzeta P z v, v⟫ = σ * (1 / a ^ 2 - P.δ ^ 2) := by
    rw [inner_opAzeta_of_eig P (mem_Eminus.mp hvm) hvk, hv1, hDv]; ring
  have hcsw := hcs w hw hw1
  have hNφ : ⟪opAzeta P z φ, φ⟫ ≤ N := by
    refine (real_inner_le_norm _ _).trans ?_
    have := (opAzeta P z).le_opNorm φ
    rw [hφ1] at this ⊢
    linarith
  set F := fInt P w x with hFdef
  set Fv := fInt P v x with hFvdef
  set Fφ := fInt P φ x with hFφdef
  have hF0 : 0 ≤ F := fInt_nonneg P w hx0
  have hFv0 : 0 ≤ Fv := fInt_nonneg P v hx0
  have hFφ0 : 0 ≤ Fφ := fInt_nonneg P φ hx0
  have hFc : F ≤ C₃ * x ^ 3 := by
    have h := hCc w (hb.kap_Eplus hw) x (by rw [hax]; exact hx1.le)
    rw [hw1, abs_of_nonneg hF0, hax, one_pow, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self Cc) (by positivity))
  have hFl : k ^ 2 * x - C₂ * x ^ 2 ≤ Fφ := by
    have h := hCl φ x hx0 hx1.le
    rw [hφ1, one_pow, mul_one] at h
    have : Cl * x ^ 2 ≤ C₂ * x ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self Cl) (by positivity)
    linarith
  rw [hax, hay, abs_of_nonneg hF0] at hL
  rw [hax, hay, abs_of_nonneg hFv0, czv] at hMv
  rw [hax, hay, abs_of_nonneg hFφ0] at hMφ
  -- common bounds
  have hKx : K * x ≤ σ / 4 := by
    calc K * x ≤ K * (σ / (4 * (K + 1))) := mul_le_mul_of_nonneg_left hxa.le hK0
      _ ≤ σ / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        have : σ * (4 * (K + 1)) = K * σ * 4 + 4 * σ := by ring
        linarith
  have hx2 : x ^ 2 ≤ x := by
    rw [sq]; exact mul_le_of_le_one_right hx0 hx1.le
  have hx3 : x ^ 3 ≤ x ^ 2 := by
    rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hx1.le
  have hTop : σ * (1 + F / 2) + ct * x * F ≤ σ + (σ / 2 + K) * C₃ * x ^ 3 := by
    have h1 : ct * x * F ≤ K * F := by
      have : ct * x ≤ K := by
        calc ct * x ≤ K * x := mul_le_mul_of_nonneg_right hctK hx0
          _ ≤ K * 1 := mul_le_mul_of_nonneg_left hx1.le hK0
          _ = K := mul_one K
      exact mul_le_mul_of_nonneg_right this hF0
    have h2 : (σ / 2 + K) * F ≤ (σ / 2 + K) * (C₃ * x ^ 3) :=
      mul_le_mul_of_nonneg_left hFc (by positivity)
    linarith
  have hyy : ct * (y ^ 2 + y * x) + cb * (y ^ 2 + y * x) ≤ K * (y ^ 2 + y * x) := by
    have hcK : ct + cb ≤ K := by linarith [le_abs_self ct, le_abs_self cb]
    have := mul_le_mul_of_nonneg_right hcK (show 0 ≤ y ^ 2 + y * x by positivity)
    linarith
  -- bound (i): the trial `v_w`
  have hI : Real.exp (P.δ * x) * lamMax (opA P (flow P.g x y z))
      + Real.exp (P.δ * x) * lamMin (opA P (flow P.g x y z))
        ≤ (σ / 2 + K) * C₃ * x ^ 3 - y * σ * c0 / 2 := by
    have hB3 : y * (-σ * (‖opD P w‖ ^ 2 - P.δ ^ 2)) + y * (σ * (1 / a ^ 2 - P.δ ^ 2))
        ≤ -(y * σ * c0) := by
      have h1 : σ * (1 / a ^ 2 - ‖opD P w‖ ^ 2) ≤ σ * (-c0) :=
        mul_le_mul_of_nonneg_left (by linarith) hσ.le
      have h2 := mul_le_mul_of_nonneg_left h1 hy0
      linarith
    have hv' : cb * x * Fv ≤ σ / 2 * Fv := by
      have : cb * x ≤ σ / 2 := by
        calc cb * x ≤ K * x := mul_le_mul_of_nonneg_right hcbK hx0
          _ ≤ σ / 2 := by linarith
      exact mul_le_mul_of_nonneg_right this hFv0
    have hB4 : K * (y ^ 2 + y * x) ≤ y * σ * c0 / 2 := by
      have hyx : y + x ≤ σ * c0 / (2 * (K + 1)) := by
        have : σ * c0 / (4 * (K + 1)) + σ * c0 / (4 * (K + 1)) = σ * c0 / (2 * (K + 1)) := by
          field_simp; ring
        linarith
      have h2 : K * (y * (y + x)) ≤ K * (y * (σ * c0 / (2 * (K + 1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyx hy0) hK0
      have h3 : K * (y * (σ * c0 / (2 * (K + 1)))) ≤ y * σ * c0 / 2 := by
        rw [show K * (y * (σ * c0 / (2 * (K + 1)))) = y * σ * c0 / 2 * (K / (K + 1)) by
          field_simp]
        have h5 : K / (K + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        exact mul_le_of_le_one_right (by positivity) h5
      have e : K * (y ^ 2 + y * x) = K * (y * (y + x)) := by ring
      linarith
    rw [czw] at hL
    linarith
  -- bound (ii): the trial `φ` with `φ(0) ≠ 0`
  have hII : Real.exp (P.δ * x) * lamMax (opA P (flow P.g x y z))
      + Real.exp (P.δ * x) * lamMin (opA P (flow P.g x y z))
        ≤ -(σ / 8 * k ^ 2 * x) + B * y := by
    have hNw : y * ⟪opAzeta P z w, w⟫ ≤ y * N := by
      refine mul_le_mul_of_nonneg_left ((real_inner_le_norm _ _).trans ?_) hy0
      have := (opAzeta P z).le_opNorm w
      rw [hw1] at this ⊢
      linarith
    have hNφ' : y * ⟪opAzeta P z φ, φ⟫ ≤ y * N := mul_le_mul_of_nonneg_left hNφ hy0
    have hφ' : -(σ * (1 + Fφ / 2)) + cb * x * Fφ ≤ -σ - σ / 4 * Fφ := by
      have : cb * x ≤ σ / 4 := by
        calc cb * x ≤ K * x := mul_le_mul_of_nonneg_right hcbK hx0
          _ ≤ σ / 4 := hKx
      have := mul_le_mul_of_nonneg_right this hFφ0
      linarith
    have hFl' : σ / 4 * (k ^ 2 * x - C₂ * x ^ 2) ≤ σ / 4 * Fφ :=
      mul_le_mul_of_nonneg_left hFl (by positivity)
    have hKy : K * (y ^ 2 + y * x) ≤ 2 * K * y := by
      have h1 : y ^ 2 ≤ y := by rw [sq]; exact mul_le_of_le_one_right hy0 hy1.le
      have h2 : y * x ≤ y := mul_le_of_le_one_right hy0 hx1.le
      have h3 : y ^ 2 + y * x ≤ 2 * y := by linarith
      have := mul_le_mul_of_nonneg_left h3 hK0
      linarith
    have hab : (σ / 2 + K) * C₃ * x ^ 3 + σ / 4 * C₂ * x ^ 2 ≤ σ / 8 * k ^ 2 * x := by
      have h1 : (σ / 2 + K) * C₃ * x ^ 3 + σ / 4 * C₂ * x ^ 2 ≤ A₃ * x ^ 2 := by
        have h2 : (σ / 2 + K) * C₃ * x ^ 3 ≤ (σ / 2 + K) * C₃ * x ^ 2 :=
          mul_le_mul_of_nonneg_left hx3 (by positivity)
        rw [hA₃]
        linarith
      have h5 : x * (8 * (A₃ + 1)) < σ * k ^ 2 := by
        have := hxd
        rwa [lt_div_iff₀ (by positivity)] at this
      have h6 : A₃ * x ≤ σ / 8 * k ^ 2 := by linarith
      calc (σ / 2 + K) * C₃ * x ^ 3 + σ / 4 * C₂ * x ^ 2 ≤ A₃ * x ^ 2 := h1
        _ = A₃ * x * x := by ring
        _ ≤ σ / 8 * k ^ 2 * x := mul_le_mul_of_nonneg_right h6 hx0
    linarith
  by_cases hcase : τ * x ^ 3 < y
  · refine edgeDiscZ_neg_of_scaled (hI.trans_lt ?_)
    have hτe : τ * (σ * c0) = 2 * ((σ / 2 + K) * C₃) := by
      rw [hτ]; field_simp
    have h1 : τ * x ^ 3 * (σ * c0) < y * (σ * c0) :=
      mul_lt_mul_of_pos_right hcase (by positivity)
    have h2 : τ * x ^ 3 * (σ * c0) = 2 * ((σ / 2 + K) * C₃ * x ^ 3) := by
      rw [show τ * x ^ 3 * (σ * c0) = τ * (σ * c0) * x ^ 3 by ring, hτe]; ring
    linarith
  · push Not at hcase
    have hxpos : 0 < x := by
      rcases hne with h | h
      · exact lt_of_le_of_ne hx0 (Ne.symm h)
      · by_contra hx
        have hx' : x = 0 := le_antisymm (not_lt.mp hx) hx0
        rw [hx'] at hcase
        simp at hcase
        exact h (le_antisymm hcase hy0)
    refine edgeDiscZ_neg_of_scaled (hII.trans_lt ?_)
    have h5 : x * (8 * (B * τ + 1)) < σ * k ^ 2 := by
      have := hxe
      rwa [lt_div_iff₀ (by positivity)] at this
    have h6 : B * τ * x ^ 2 < σ / 8 * k ^ 2 := by
      have h7 : B * τ * x ^ 2 ≤ B * τ * x := mul_le_mul_of_nonneg_left hx2 (mul_nonneg hB0 hτ0)
      linarith only [h5, h7, hx0]
    have h8 : B * y ≤ B * (τ * x ^ 3) := mul_le_mul_of_nonneg_left hcase hB0
    have h9 : B * (τ * x ^ 3) < σ / 8 * k ^ 2 * x := by
      calc B * (τ * x ^ 3) = B * τ * x ^ 2 * x := by ring
        _ < σ / 8 * k ^ 2 * x := mul_lt_mul_of_pos_right h6 hxpos
    linarith

-- odd-chains Theorem A, merged §1 WA
/-- **The wedge above**: at a bottom-start vertex the edge
discriminant is negative on a punctured closed upper half-disc of the orbit-heat plane. -/
theorem BottomStart.wedgeAbove (hb : BottomStart P z) :
    ∃ r > 0, ∀ x y : ℝ, 0 ≤ y → 0 < x ^ 2 + y ^ 2 → x ^ 2 + y ^ 2 < r ^ 2 →
      edgeDiscZ P.δ P.g (flow P.g x y z) < 0 := by
  obtain ⟨r₁, hr₁, h₁⟩ := hb.wedgeAbove_left
  obtain ⟨r₂, hr₂, h₂⟩ := hb.wedgeAbove_right
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun x y hy hpos hlt => ?_⟩
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hx : |x| < min r₁ r₂ :=
    abs_lt_of_sq_lt_sq (by linarith [sq_nonneg y]) hr.le
  have hy' : y < min r₁ r₂ :=
    lt_of_le_of_lt (le_abs_self y) (abs_lt_of_sq_lt_sq (by linarith [sq_nonneg x]) hr.le)
  have hne : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    rw [h.1, h.2] at hpos
    norm_num at hpos
  rcases le_total x 0 with hx0 | hx0
  · exact h₁ x y hx0 hy (lt_of_lt_of_le hx (min_le_left _ _))
      (lt_of_lt_of_le hy' (min_le_left _ _)) hne
  · exact h₂ x y hx0 hy (lt_of_le_of_lt (le_abs_self x) (lt_of_lt_of_le hx (min_le_right _ _)))
      (lt_of_lt_of_le hy' (min_le_right _ _)) hne

end Cvs.StepA.Edge.PlanarBoxLemma
