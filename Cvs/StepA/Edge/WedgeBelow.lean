import Mathlib
import Cvs.StepA.Edge.ComplexWeightDiscriminant
import Cvs.StepA.Edge.EdgePencil
import Cvs.StepA.Edge.EdgePencilOperators
import Cvs.StepA.Edge.EdgeSpace
import Cvs.StepA.Edge.VertexChains
import Cvs.Upstream.RayleighQuotientExtremes

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The wedge below a vertex

At a vertex with `κ = 0` on `E₊` and `dim E₋ ≥ 2` the edge discriminant along `(−λη, −η)` is
`η c(λ) + O(η²)`, and the rank-one penalty `λ(σ/2)κκ*` on `E₋` drives `c(λ)` to the strict margin
`σ(ρ(f)² − max_{K₋} ρ²) > 0`, so `s > 0` just below the vertex.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace Cvs.StepA.Edge.PlanarBoxLemma
open Cvs.ZeroCounting
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : EdgeData ι} {z : ι → ℂ}

variable (P z) in
/-- The first-order direction of the pencil along the ray `(ξ, ζ) = (−λη, −η)`:
`T_λ = −λ A_ξ − A_ζ`. -/
def opT (lam : ℝ) : EdgeV P →L[ℝ] EdgeV P := -(lam • opAxi P z) - opAzeta P z

variable [Nonempty ι]

/-! ### First order along the ray (merged §2(a)-(d)) -/

-- merged §2(a)-(d)
/-- **The expansion along the ray**: at a vertex, for `λ ≥ 0`, a unit
`f ∈ E₊` and `⟪T_λ u, u⟫ ≥ m ‖u‖²` on `E₋`, `s(−λη, −η) ≥ η(⟪T_λ f, f⟫ + m) − Cη²` for small
`η > 0`. -/
theorem IsVertex.wb_expansion (hv : IsVertex P z) {lam : ℝ} (hlam : 0 ≤ lam) {f : EdgeV P}
    (hf : f ∈ Eplus P z) (hf1 : ‖f‖ = 1) {m : ℝ}
    (hm : ∀ u ∈ Eminus P z, m * ‖u‖ ^ 2 ≤ ⟪opT P z lam u, u⟫) :
    ∃ C η₁ : ℝ, 0 < η₁ ∧ ∀ η ∈ Set.Ioo 0 η₁,
      η * (⟪opT P z lam f, f⟫ + m) - C * η ^ 2
        ≤ edgeDiscZ P.δ P.g (flow P.g (-(lam * η)) (-η) z) := by
  have hσ := hv.sig_pos
  obtain ⟨CT, hT⟩ := taylor_flow P z
  obtain ⟨g, hg, hgap⟩ := hv.gap_bottom
  set σ := sig P z with hσdef
  set C' := |CT| * (lam ^ 2 + 1) with hC'
  set NT := ‖opT P z lam‖ with hNT
  have hC'0 : 0 ≤ C' := by positivity
  have hNT0 : 0 ≤ NT := norm_nonneg _
  refine ⟨2 * C' + 2 * (NT + C') ^ 2 / g, min (min 1 (1 / (lam + 1))) (g / (4 * (NT + C' + 1))),
    lt_min (lt_min one_pos (by positivity)) (by positivity), fun η hη => ?_⟩
  obtain ⟨hη0, hηr⟩ := hη
  simp only [lt_min_iff] at hηr
  obtain ⟨⟨hη1, hηl⟩, hηg⟩ := hηr
  have hlη : lam * η ≤ 1 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < lam + 1)).mp hηl
    linarith
  have hη2 : η ^ 2 ≤ η := by rw [sq]; exact mul_le_of_le_one_right hη0.le hη1.le
  set A₀ := opA P z with hA₀
  set Aη := opA P (flow P.g (-(lam * η)) (-η) z) with hAη
  set T := opT P z lam with hTdef
  -- the Taylor remainder
  have hR : ∀ x, ‖(Aη - A₀ - η • T) x‖ ≤ C' * η ^ 2 * ‖x‖ := by
    intro x
    have h := hT (-(lam * η)) (-η) (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact hlη)
      (by rw [abs_neg, abs_of_pos hη0]; exact hη1.le) x
    have e : (Aη - A₀ - η • T) x
        = (opA P (flow P.g (-(lam * η)) (-η) z) - opA P z - (-(lam * η)) • opAxi P z
          - (-η) • opAzeta P z) x := by
      simp only [hTdef, opT, sub_apply, smul_apply,
        neg_apply, hAη, hA₀]
      module
    rw [e]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg x))
    have : (-(lam * η)) ^ 2 + (-η) ^ 2 = (lam ^ 2 + 1) * η ^ 2 := by ring
    rw [this, hC', mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self CT) (by positivity)
  have hRi : ∀ x, |⟪(Aη - A₀ - η • T) x, x⟫| ≤ C' * η ^ 2 * ‖x‖ ^ 2 := fun x => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := mul_le_mul_of_nonneg_right (hR x) (norm_nonneg x)
    rw [sq]
    linarith
  have hsplit : ∀ x, ⟪Aη x, x⟫ = ⟪A₀ x, x⟫ + η * ⟪T x, x⟫ + ⟪(Aη - A₀ - η • T) x, x⟫ :=
    fun x => by
      simp only [sub_apply, smul_apply, inner_sub_left,
        real_inner_smul_left]
      ring
  -- top: the test vector `f`
  have htop : σ + η * ⟪T f, f⟫ - C' * η ^ 2 ≤ lamMax Aη := by
    have hf0 : f ≠ 0 := by rintro rfl; simp at hf1
    refine le_lamMax_of hf0 ?_
    rw [hf1, one_pow, mul_one, hsplit, mem_Eplus.mp hf, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hf1]
    have := (abs_le.mp (hRi f)).1
    rw [hf1] at this
    linarith
  -- bottom: the Schur bound
  have hEp : ∀ x, ‖(Aη - A₀) x‖ ≤ η * (NT + C') * ‖x‖ := fun x => by
    have e : (Aη - A₀) x = η • T x + (Aη - A₀ - η • T) x := by
      simp only [sub_apply, smul_apply]
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη0]
    have h1 := T.le_opNorm x
    have h2 := hR x
    have h3 : C' * η ^ 2 * ‖x‖ ≤ C' * η * ‖x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη2 hC'0) (norm_nonneg x)
    nlinarith [norm_nonneg x]
  have hm' : ∀ u ∈ Eminus P z, (η * m - C' * η ^ 2) * ‖u‖ ^ 2 ≤ ⟪(Aη - A₀) u, u⟫ := by
    intro u hu
    have h1 := mul_le_mul_of_nonneg_left (hm u hu) hη0.le
    have h2 := (abs_le.mp (hRi u)).1
    have e : ⟪(Aη - A₀) u, u⟫ = η * ⟪T u, u⟫ + ⟪(Aη - A₀ - η • T) u, u⟫ := by
      simp only [sub_apply, smul_apply, inner_sub_left,
        real_inner_smul_left]
      ring
    rw [e]
    nlinarith
  have hmε : η * m - C' * η ^ 2 ≤ η * (NT + C') := by
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hv.Eminus_ne_bot
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have h1 := hm' u hu
    have h2 : ⟪(Aη - A₀) u, u⟫ ≤ η * (NT + C') * ‖u‖ ^ 2 := by
      refine (real_inner_le_norm _ _).trans ?_
      have := mul_le_mul_of_nonneg_right (hEp u) (norm_nonneg u)
      rw [sq]
      linarith
    have := le_trans h1 h2
    exact le_of_mul_le_mul_right this (by positivity)
  have hεg : 4 * (η * (NT + C')) ≤ g := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (NT + C' + 1))).mp hηg
    nlinarith
  have hlow := schur_lower (A₀ := A₀) (Ep := Aη - A₀) (opA_isSelfAdjoint P z)
    (W := Eminus P z) (σ := σ) (g := g)
    (ε := η * (NT + C')) (m := η * m - C' * η ^ 2) (fun u hu => mem_Eminus.mp hu) hgap hg hEp
    hεg hm' hmε
  have hbot : -σ + (η * m - C' * η ^ 2) - 2 * (η * (NT + C')) ^ 2 / g ≤ lamMin Aη := by
    refine le_lamMin fun x => ?_
    have := hlow x
    rwa [show A₀ + (Aη - A₀) = Aη by abel] at this
  rw [edgeDiscZ_eq]
  have e : 2 * (η * (NT + C')) ^ 2 / g = 2 * (NT + C') ^ 2 / g * η ^ 2 := by ring
  rw [e] at hbot
  have hσ' : lamMax A₀ = σ := rfl
  linarith

/-! ### The positive first-order slope (merged §2(e)-(g)) -/

variable (P z) in
-- merged §2(g): `g*` maximising `ρ` on `K₋`, `f = Dg*/‖Dg*‖ ∈ E₊` (reflection), strict
-- Cauchy–Schwarz (`eq_zero_of_opD_opD`), compactness of the unit sphere of `K₋`
/-- **The strict margin `c_∞ > 0`**: some unit `f ∈ E₊` and `μ > 0` have
`‖Dg‖² + μ‖g‖² ≤ ‖Df‖² ‖g‖²` for every `g ∈ K₋`. -/
theorem exists_margin :
    ∃ f ∈ Eplus P z, ‖f‖ = 1 ∧ ∃ μ > 0, ∀ g ∈ Kminus P z,
      ‖opD P g‖ ^ 2 + μ * ‖g‖ ^ 2 ≤ ‖opD P f‖ ^ 2 * ‖g‖ ^ 2 := by
  by_cases hK : Kminus P z = ⊥
  · -- `K₋ = 0`: any unit `f ∈ E₊`
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (Eplus_ne_bot P z)
    refine ⟨‖x‖⁻¹ • x, (Eplus P z).smul_mem _ hx, ?_, 1, one_pos, fun g hg => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
    · rw [hK, Submodule.mem_bot] at hg
      subst hg
      simp
  -- the maximiser `g*` of `‖Dg‖` on the unit sphere of `K₋`
  set S : Set (EdgeV P) := {w | w ∈ Kminus P z ∧ ‖w‖ = 1} with hS
  have hSc : IsCompact S := by
    have e : S = (Kminus P z : Set (EdgeV P)) ∩ Metric.sphere 0 1 := by
      ext w
      simp [hS]
    rw [e]
    exact (isCompact_sphere 0 1).inter_left (Submodule.closed_of_finiteDimensional _)
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hK
  have hSne : S.Nonempty := ⟨‖u‖⁻¹ • u, (Kminus P z).smul_mem _ hu, by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)]⟩
  obtain ⟨gs, ⟨hgsK, hgs1⟩, hmax⟩ := hSc.exists_isMaxOn hSne
    (f := fun w => ‖opD P w‖) (continuous_norm.comp (opD P).continuous).continuousOn
  set a := ‖opD P gs‖ with ha
  set b := ‖opD P (opD P gs)‖ with hb
  have hgs0 : gs ≠ 0 := by
    rintro rfl
    simp at hgs1
  have hDgs0 : opD P gs ≠ 0 := fun h => hgs0 (opD_injective P (by rw [h, map_zero]))
  have ha0 : 0 < a := norm_pos_iff.mpr hDgs0
  -- `‖Dg‖ ≤ a ‖g‖` on `K₋`
  have hbound : ∀ g ∈ Kminus P z, ‖opD P g‖ ≤ a * ‖g‖ := by
    intro g hg
    by_cases hg0 : g = 0
    · simp [hg0]
    have hn : 0 < ‖g‖ := norm_pos_iff.mpr hg0
    have hmem : ‖g‖⁻¹ • g ∈ S := ⟨(Kminus P z).smul_mem _ hg, by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩
    have h := isMaxOn_iff.mp hmax _ hmem
    simp only [map_smul, norm_smul, norm_inv, norm_norm] at h
    rw [inv_mul_le_iff₀ hn] at h
    linarith [mul_comm a ‖g‖]
  -- the reflection `Dg* ∈ E₊`
  have hgsE : gs ∈ Eminus P z := (Submodule.mem_inf.mp hgsK).1
  have hgsk : ⟪kap P, gs⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (Submodule.mem_inf.mp hgsK).2
  have hDE : opD P gs ∈ Eplus P z := by
    rw [mem_Eplus, opA_opD_of_eig P (mem_Eminus.mp hgsE) hgsk, neg_neg]
  -- strict Cauchy–Schwarz: `a² < b`
  have hcs := sq_norm_lt_opDinv_mul_opD P hDgs0 (by rw [opDinv_opD, hgsk, mul_zero])
  rw [opDinv_opD, hgs1, one_mul] at hcs
  have hDf : ‖opD P (a⁻¹ • opD P gs)‖ ^ 2 = b ^ 2 / a ^ 2 := by
    rw [map_smul, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha0, ← hb, mul_pow,
      inv_pow]
    ring
  refine ⟨a⁻¹ • opD P gs, (Eplus P z).smul_mem _ hDE, ?_, b ^ 2 / a ^ 2 - a ^ 2, ?_,
    fun g hg => ?_⟩
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha0, inv_mul_cancel₀ ha0.ne']
  · have h4 : a ^ 2 * a ^ 2 < b ^ 2 := by nlinarith
    rw [gt_iff_lt, sub_pos, lt_div_iff₀ (by positivity)]
    linarith
  · have h2 : ‖opD P g‖ ^ 2 ≤ a ^ 2 * ‖g‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound g hg) 2
    rw [hDf]
    have e : (b ^ 2 / a ^ 2 - a ^ 2) * ‖g‖ ^ 2 = b ^ 2 / a ^ 2 * ‖g‖ ^ 2 - a ^ 2 * ‖g‖ ^ 2 := by
      ring
    rw [e]
    linarith

-- `K₋ = E₋ ∩ ker κ` has codimension at most `1` in `E₋`
/-- `dim E₋ ≥ 2` gives `K₋ ≠ 0`. -/
theorem Kminus_ne_bot (hd : 2 ≤ Module.finrank ℝ (Eminus P z)) : Kminus P z ≠ ⊥ := by
  intro h
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Eminus P z) (ℝ ∙ kap P)ᗮ
  have h2 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ kap P)
  have h3 : Module.finrank ℝ (ℝ ∙ kap P) ≤ 1 := by
    have := finrank_span_le_card (R := ℝ) ({kap P} : Set (EdgeV P))
    simpa using this
  have h4 := Submodule.finrank_le (Eminus P z ⊔ (ℝ ∙ kap P)ᗮ)
  have h5 : Eminus P z ⊓ (ℝ ∙ kap P)ᗮ = ⊥ := h
  rw [h5, finrank_bot] at h1
  omega

-- merged §2(e)-(g)
/-- **A positive first-order slope**: at a vertex with `κ = 0` on `E₊` and
`dim E₋ ≥ 2` there are `λ > 0`, a unit `f ∈ E₊` and a lower bound `m` of `T_λ` on `E₋` with
`⟪T_λ f, f⟫ + m > 0`. -/
theorem IsVertex.exists_slope_pos (hv : IsVertex P z) (hk : ∀ w ∈ Eplus P z, ⟪kap P, w⟫ = 0)
    (hd : 2 ≤ Module.finrank ℝ (Eminus P z)) :
    ∃ lam > 0, ∃ f ∈ Eplus P z, ‖f‖ = 1 ∧ ∃ m : ℝ,
      (∀ u ∈ Eminus P z, m * ‖u‖ ^ 2 ≤ ⟪opT P z lam u, u⟫) ∧ 0 < ⟪opT P z lam f, f⟫ + m := by
  have hσ := hv.sig_pos
  set σ := sig P z with hσdef
  obtain ⟨f, hf, hf1, μ, hμ, hmar⟩ := exists_margin P z
  set W := Eminus P z with hW
  set p := W.starProjection (kap P) with hp
  have hpW : p ∈ W := W.starProjection_apply_mem _
  have hpk : ∀ u ∈ W, ⟪p, u⟫ = ⟪kap P, u⟫ := fun u hu => by
    have := W.starProjection_inner_eq_zero (kap P) u hu
    rw [inner_sub_left] at this
    linarith
  -- `p ≠ 0`, since `κ` does not vanish on `E₋`
  have hp0 : p ≠ 0 := by
    intro h0
    apply not_kap_zero_both P z
    refine ⟨fun x hx => Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hk x hx),
      fun x hx => Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ?_⟩
    rw [← hpk x hx, h0, inner_zero_left]
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  -- the penalty data: `Q = −A_ζ`, `q = ‖A_ζ‖`, `μ_K = σ(δ² − ‖Df‖² + μ)`
  set q := ‖opAzeta P z‖ with hq
  set μK := σ * (P.δ ^ 2 - ‖opD P f‖ ^ 2 + μ) with hμK
  have hQn : ∀ x, ‖(-opAzeta P z) x‖ ≤ q * ‖x‖ := fun x => by
    rw [neg_apply, norm_neg]; exact (opAzeta P z).le_opNorm x
  have hQK : ∀ u ∈ W, ⟪p, u⟫ = 0 → μK * ‖u‖ ^ 2 ≤ ⟪(-opAzeta P z) u, u⟫ := by
    intro u hu hpu
    have hku : ⟪kap P, u⟫ = 0 := by rw [← hpk u hu]; exact hpu
    have hKu : u ∈ Kminus P z := Submodule.mem_inf.mpr
      ⟨hu, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hku⟩
    have h1 := hmar u hKu
    rw [neg_apply, inner_neg_left,
      inner_opAzeta_of_eig P (mem_Eminus.mp hu) hku]
    have h2 : σ * (‖opD P u‖ ^ 2 + μ * ‖u‖ ^ 2) ≤ σ * (‖opD P f‖ ^ 2 * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 hσ.le
    rw [hμK]
    nlinarith
  have hμKq : μK ≤ q := by
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (Kminus_ne_bot (P := P) (z := z) hd)
    have huW : u ∈ W := (Submodule.mem_inf.mp hu).1
    have hku : ⟪kap P, u⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (Submodule.mem_inf.mp hu).2
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have h1 := hQK u huW (by rw [hpk u huW]; exact hku)
    have h2 : ⟪(-opAzeta P z) u, u⟫ ≤ q * ‖u‖ ^ 2 := by
      refine (real_inner_le_norm _ _).trans ?_
      have := mul_le_mul_of_nonneg_right (hQn u) (norm_nonneg u)
      rw [sq]; linarith
    exact le_of_mul_le_mul_right (h1.trans h2) (by positivity)
  have hq0 : 0 ≤ q := norm_nonneg _
  -- choose `λ` with `λ(σ/2)‖p‖² − 2q > q²/(σμ)`
  set L := (2 * q + q ^ 2 / (σ * μ) + 1) * 2 / (σ * ‖p‖ ^ 2) with hL
  have hL0 : 0 < L := by positivity
  have hLc : 2 * q < L * σ / 2 * ‖p‖ ^ 2 := by
    have : L * σ / 2 * ‖p‖ ^ 2 = 2 * q + q ^ 2 / (σ * μ) + 1 := by
      rw [hL]; field_simp
    rw [this]; have : 0 ≤ q ^ 2 / (σ * μ) := by positivity
    linarith
  have hLd : q ^ 2 / (L * σ / 2 * ‖p‖ ^ 2 - 2 * q) < σ * μ := by
    have hden : L * σ / 2 * ‖p‖ ^ 2 - 2 * q = q ^ 2 / (σ * μ) + 1 := by
      rw [hL]; field_simp; ring
    rw [hden, div_lt_iff₀ (by positivity)]
    have : q ^ 2 / (σ * μ) * (σ * μ) = q ^ 2 := by field_simp
    nlinarith [mul_pos hσ hμ]
  refine ⟨L, hL0, f, hf, hf1, -(L * σ * P.δ) + (μK - q ^ 2 / (L * σ / 2 * ‖p‖ ^ 2 - 2 * q)),
    fun u hu => ?_, ?_⟩
  · have hpen := penalty_lower hpW hp0 hQn hQK hμKq hLc hu
    have hxi := inner_opAxi_of_eig P (mem_Eminus.mp hu)
    rw [hpk u hu] at hpen
    simp only [opT, sub_apply, neg_apply,
      smul_apply, inner_sub_left, inner_neg_left, real_inner_smul_left]
    rw [hxi]
    simp only [neg_apply, inner_neg_left] at hpen
    nlinarith
  · have hxi := inner_opAxi_of_eig P (mem_Eplus.mp hf)
    have hze := inner_opAzeta_of_eig P (mem_Eplus.mp hf) (hk f hf)
    simp only [opT, sub_apply, neg_apply,
      smul_apply, inner_sub_left, inner_neg_left, real_inner_smul_left]
    rw [hxi, hze, hk f hf, hf1, hμK]
    nlinarith

-- merged §2
/-- **The wedge below**: at a vertex with `κ = 0` on `E₊` and `dim E₋ ≥ 2`,
`s(−λη, −η) > 0` for some `λ > 0` and all small `η > 0`. -/
theorem IsVertex.wedgeBelow (hv : IsVertex P z) (hk : ∀ w ∈ Eplus P z, ⟪kap P, w⟫ = 0)
    (hd : 2 ≤ Module.finrank ℝ (Eminus P z)) :
    ∃ lam > 0, ∃ η₀ > 0, ∀ η ∈ Set.Ioo 0 η₀,
      0 < edgeDiscZ P.δ P.g (flow P.g (-(lam * η)) (-η) z) := by
  obtain ⟨lam, hlam, f, hf, hf1, m, hm, hpos⟩ := hv.exists_slope_pos hk hd
  obtain ⟨C, η₁, hη₁, hexp⟩ := hv.wb_expansion hlam.le hf hf1 hm
  set c := ⟪opT P z lam f, f⟫ + m with hc
  refine ⟨lam, hlam, min η₁ (c / (|C| + 1)), lt_min hη₁ (by positivity), fun η hη => ?_⟩
  obtain ⟨hη0, hηr⟩ := hη
  have h1 := hexp η ⟨hη0, lt_of_lt_of_le hηr (min_le_left _ _)⟩
  have h2 : η * (|C| + 1) < c :=
    (lt_div_iff₀ (by positivity)).mp (lt_of_lt_of_le hηr (min_le_right _ _))
  have h3 : C * η ^ 2 ≤ |C| * η ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have h4 : 0 < η * (c - |C| * η) := mul_pos hη0 (by nlinarith)
  nlinarith

/-- **The wedge below at a bottom-start vertex.** -/
theorem BottomStart.wedgeBelow (hb : BottomStart P z) :
    ∃ lam > 0, ∃ η₀ > 0, ∀ η ∈ Set.Ioo 0 η₀,
      0 < edgeDiscZ P.δ P.g (flow P.g (-(lam * η)) (-η) z) :=
  hb.1.wedgeBelow (fun _ hw => hb.kap_Eplus hw) hb.two_le_finrank

end Cvs.StepA.Edge.PlanarBoxLemma
