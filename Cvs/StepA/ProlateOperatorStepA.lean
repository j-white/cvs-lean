import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.EvenSpectrumGroundLevel
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.VolterraResolventEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Step A for the prolate operator

The prolate operator `−((1−s²)g')' + c²s²g` on `[−1, 1]` (zero flux at `±1`) has simple levels
`evenSpec (sqC c) ∪ oddSpec (sqC c)`; the least is `groundLevel c`, below every odd level, with even
eigenfunction `rung c 0`. Its energy on `C¹[−1, 1]` has that bottom, attained exactly on the line of
`rung c 0`, and so does Connes' `PW_ℓ = −∂ₓ((ℓ²−x²)∂ₓ) + (2πℓx)²` on `[−ℓ, ℓ]`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenSpectrumGroundLevel Cvs.Prolate.EvenRungsByIndex

namespace Cvs.StepA.ProlateOperatorStepA

/-! ### Regular solutions -/

/-- `g` solves `((1−s²)g')' = (c²s² − χ)g` on `(−1, 1)` with flux `w = (1−s²)g'`; `g` and `w` are
continuous on `[−1, 1]` and the flux vanishes at `±1`. -/
structure IsRegSol (c χ : ℝ) (g w : ℝ → ℝ) : Prop where
  cont : ContinuousOn g (Icc (-1) 1)
  contFlux : ContinuousOn w (Icc (-1) 1)
  deriv : ∀ s ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (w s / (1 - s ^ 2)) s
  derivFlux : ∀ s ∈ Ioo (-1 : ℝ) 1, HasDerivAt w ((c ^ 2 * s ^ 2 - χ) * g s) s
  flux_neg_one : w (-1) = 0
  flux_one : w 1 = 0

/-- A solution of the angular equation with two derivatives on `[−1, 1]` is regular, with flux
`(1−s²)g₁`. -/
theorem isRegSol_of_angular {c χ : ℝ} {g g₁ g₂ : ℝ → ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0) :
    IsRegSol c χ g (fun s => (1 - s ^ 2) * g₁ s) := by
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  rw [hI] at hg hg₁ hang
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := fun s => by
    simpa using (hasDerivAt_pow 2 s).const_sub 1
  refine ⟨fun s hs => (hg s hs).continuousAt.continuousWithinAt,
    fun s hs => ((hp s).mul (hg₁ s hs)).continuousAt.continuousWithinAt, fun s hs => ?_, fun s hs => ?_,
    by norm_num, by norm_num⟩
  · have h1 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    exact (hg s (Ioo_subset_Icc_self hs)).congr_deriv (by field_simp)
  · have := hang s (Ioo_subset_Icc_self hs)
    exact ((hp s).mul (hg₁ s (Ioo_subset_Icc_self hs))).congr_deriv (by linear_combination this)

/-- The reflection `s ↦ g(−s)` of a regular solution is regular, with flux `s ↦ −w(−s)`. -/
theorem IsRegSol.reflect {c χ : ℝ} {g w : ℝ → ℝ} (h : IsRegSol c χ g w) :
    IsRegSol c χ (fun s => g (-s)) (fun s => -w (-s)) := by
  have hneg : MapsTo (fun s : ℝ => -s) (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hnego : ∀ s ∈ Ioo (-1 : ℝ) 1, -s ∈ Ioo (-1 : ℝ) 1 := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨h.cont.comp continuousOn_neg hneg, (h.contFlux.comp continuousOn_neg hneg).neg, fun s hs => ?_,
    fun s hs => ?_, by simp [h.flux_one], by simp [h.flux_neg_one]⟩
  · exact (HasDerivAt.comp_of_eq s (h.deriv (-s) (hnego s hs)) (hasDerivAt_neg' s) rfl).congr_deriv
      (by ring)
  · exact (HasDerivAt.comp_of_eq s (h.derivFlux (-s) (hnego s hs)) (hasDerivAt_neg' s) rfl).neg.congr_deriv
      (by ring)

/-- **A regular solution is `g(1)` times the regular solution `regSol` on `(−1, 1]`.** -/
theorem IsRegSol.eq_mul_regSol {c χ : ℝ} {g w : ℝ → ℝ} (h : IsRegSol c χ g w) :
    ∀ s ∈ Ioc (-1 : ℝ) 1, g s = g 1 * regSol (sqC c) χ s := by
  intro s hs
  have hsub : Icc s 1 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc hs.1.le le_rfl
  have hsubo : Ioo s 1 ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo hs.1.le le_rfl
  refine (Cvs.Prolate.RegularSolutionEdge.eq_mul_regSol (sqC c) χ (a := s) (b := 1) ⟨hs.1, hs.2, le_rfl⟩ (ψ := g)
    (u := fun t => -w t) (h.cont.mono hsub) (h.contFlux.mono hsub).neg ?_ ?_ (by simp [h.flux_one]) s
    ⟨le_rfl, hs.2⟩).1
  · intro t ht _
    refine (h.deriv t (hsubo ht)).congr_deriv ?_
    simp only [pP]
    rw [show t ^ 2 - 1 = -(1 - t ^ 2) by ring, neg_div_neg_eq]
  · intro t ht
    exact (h.derivFlux t (hsubo ht)).neg.congr_deriv rfl

/-- Two functions continuous on `[−1, 1]` that agree on `(−1, 1]` agree on `[−1, 1]`. -/
theorem eq_on_Icc_of_Ioc {f f' : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hf' : ContinuousOn f' (Icc (-1) 1)) (h : ∀ s ∈ Ioc (-1 : ℝ) 1, f s = f' s) :
    ∀ s ∈ Icc (-1 : ℝ) 1, f s = f' s :=
  Set.EqOn.of_subset_closure h hf hf' Ioc_subset_Icc_self (by rw [closure_Ioc (by norm_num)])

/-- **Every level is simple**: a regular solution is `g(1)/h(1)` times any regular solution `h` at the
same level with `h(1) ≠ 0`. -/
theorem IsRegSol.eq_mul {c χ : ℝ} {g w h v : ℝ → ℝ} (hg : IsRegSol c χ g w) (hh : IsRegSol c χ h v)
    (h1 : h 1 ≠ 0) : ∀ s ∈ Icc (-1 : ℝ) 1, g s = g 1 / h 1 * h s :=
  eq_on_Icc_of_Ioc hg.cont (continuousOn_const.mul hh.cont) fun s hs => by
    rw [hg.eq_mul_regSol s hs, hh.eq_mul_regSol s hs]; field_simp

/-- A nonzero regular solution is nonzero at the edge `1`. -/
theorem IsRegSol.edge_ne_zero {c χ : ℝ} {g w : ℝ → ℝ} (h : IsRegSol c χ g w)
    (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) : g 1 ≠ 0 := by
  intro h1
  obtain ⟨s, hs, hne⟩ := hg0
  exact hne (eq_on_Icc_of_Ioc h.cont continuousOn_const
    (fun t ht => by rw [h.eq_mul_regSol t ht, h1, zero_mul]) s hs)

/-- The centre value and flux of a regular solution against `regSol`, from either edge. -/
theorem IsRegSol.centre {c χ : ℝ} {g w : ℝ → ℝ} (h : IsRegSol c χ g w) :
    g 0 = g 1 * regSol (sqC c) χ 0 ∧ g 0 = g (-1) * regSol (sqC c) χ 0 ∧
      w 0 = g 1 * regV (sqC c) χ 0 ∧ -w 0 = g (-1) * regV (sqC c) χ 0 := by
  have h0 : (0 : ℝ) ∈ Ioc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h0o : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hnb : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hr := h.reflect
  have hd : HasDerivAt g (g 1 * regV (sqC c) χ 0) 0 :=
    ((hasDerivAt_regSol (sqC c) χ (by norm_num)).const_mul (g 1)).congr_of_eventuallyEq
      (by filter_upwards [hnb] with s hs using h.eq_mul_regSol s ⟨hs.1, hs.2.le⟩)
  have hdr : HasDerivAt (fun s => g (-s)) (g (-1) * regV (sqC c) χ 0) 0 :=
    ((hasDerivAt_regSol (sqC c) χ (by norm_num)).const_mul (g (-1))).congr_of_eventuallyEq
      (by filter_upwards [hnb] with s hs using hr.eq_mul_regSol s ⟨hs.1, hs.2.le⟩)
  refine ⟨h.eq_mul_regSol 0 h0, by simpa using hr.eq_mul_regSol 0 h0, ?_, ?_⟩
  · simpa using (h.deriv 0 h0o).unique hd
  · simpa using (hr.deriv 0 h0o).unique hdr

/-- **Every level of a nonzero regular solution is even or odd.** -/
theorem IsRegSol.mem_evenSpec_or_oddSpec {c χ : ℝ} {g w : ℝ → ℝ} (h : IsRegSol c χ g w)
    (hg0 : ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0) : χ ∈ evenSpec (sqC c) ∨ χ ∈ oddSpec (sqC c) := by
  have hg1 := h.edge_ne_zero hg0
  obtain ⟨e1, e2, e3, e4⟩ := h.centre
  by_cases hr : regSol (sqC c) χ 0 = 0
  · exact Or.inr hr
  · left
    have h1 : g 1 = g (-1) := mul_right_cancel₀ hr (e1.symm.trans e2)
    have hV : regV (sqC c) χ 0 = 0 := by
      have : g 1 * regV (sqC c) χ 0 = 0 := by rw [← h1] at e4; linarith
      exact (mul_eq_zero.mp this).resolve_left hg1
    show regU (sqC c) χ 0 = 0
    rw [← pP_mul_regV (sqC c) χ (by norm_num), hV, mul_zero]

/-- At an even level every regular solution is even. -/
theorem IsRegSol.even_of_mem_evenSpec {c χ : ℝ} {g w : ℝ → ℝ} (h : IsRegSol c χ g w)
    (hχ : χ ∈ evenSpec (sqC c)) : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = g s := by
  obtain ⟨e1, e2, -, -⟩ := h.centre
  have hr : regSol (sqC c) χ 0 ≠ 0 := fun h0 =>
    regU_ne_zero_of_regSol_eq_zero (sqC c) χ (by norm_num) (by norm_num) h0 hχ
  have h1 : g (-1) = g 1 := mul_right_cancel₀ hr (e2.symm.trans e1)
  refine eq_on_Icc_of_Ioc h.reflect.cont h.cont fun s hs => ?_
  rw [h.reflect.eq_mul_regSol s hs, h.eq_mul_regSol s hs]
  simp only [h1]

/-- At an odd level every regular solution is odd. -/
theorem IsRegSol.odd_of_mem_oddSpec {c χ : ℝ} {g w : ℝ → ℝ} (h : IsRegSol c χ g w)
    (hχ : χ ∈ oddSpec (sqC c)) : ∀ s ∈ Icc (-1 : ℝ) 1, g (-s) = -g s := by
  obtain ⟨-, -, e3, e4⟩ := h.centre
  have hV : regV (sqC c) χ 0 ≠ 0 := regV_ne_zero_of_regSol_eq_zero (sqC c) χ (by norm_num) (by norm_num) hχ
  have h1 : g (-1) = -g 1 := mul_right_cancel₀ hV (by rw [← e4, e3]; ring)
  refine eq_on_Icc_of_Ioc h.reflect.cont h.cont.neg fun s hs => ?_
  rw [h.reflect.eq_mul_regSol s hs, h.eq_mul_regSol s hs]
  simp only [h1]; ring

/-! ### The odd regular solutions -/

/-- The odd extension `sign(s)·regSol(|s|)` of the regular solution. -/
def oddExt (c χ s : ℝ) : ℝ := if 0 ≤ s then regSol (sqC c) χ s else -regSol (sqC c) χ (-s)

/-- Gluing a derivative at `0` from the two sides. -/
theorem hasDerivAt_zero_of_sides {f fl fr : ℝ → ℝ} {d : ℝ} (hl : HasDerivAt fl d 0) (hr : HasDerivAt fr d 0)
    (hfl : ∀ t ≤ 0, f t = fl t) (hfr : ∀ t, 0 ≤ t → f t = fr t) : HasDerivAt f d 0 := by
  have h := (hl.hasDerivWithinAt (s := Iic 0)).congr (fun t ht => hfl t ht) (hfl 0 le_rfl) |>.union
    ((hr.hasDerivWithinAt (s := Ici 0)).congr (fun t ht => hfr t ht) (hfr 0 le_rfl))
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h

/-- At an odd level the odd extension has derivative `regV(|s|)` everywhere. -/
theorem hasDerivAt_oddExt {c χ : ℝ} (hχ : χ ∈ oddSpec (sqC c)) (s : ℝ) :
    HasDerivAt (oddExt c χ) (regV (sqC c) χ |s|) s := by
  have h0 : regSol (sqC c) χ 0 = 0 := hχ
  have hR : ∀ t : ℝ, -1 < t → HasDerivAt (regSol (sqC c) χ) (regV (sqC c) χ t) t :=
    fun t ht => hasDerivAt_regSol (sqC c) χ ht
  have hL : ∀ t : ℝ, t < 1 → HasDerivAt (fun x => -regSol (sqC c) χ (-x)) (regV (sqC c) χ (-t)) t :=
    fun t ht => (HasDerivAt.comp_of_eq t (hR (-t) (by linarith)) (hasDerivAt_neg' t) rfl).neg.congr_deriv
      (by ring)
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · rw [abs_of_neg hs]
    refine (hL s (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hs] with t ht
    simp [oddExt, not_le.2 (show t < 0 from ht)]
  · rw [abs_zero]
    refine hasDerivAt_zero_of_sides ((hL 0 (by norm_num)).congr_deriv (by simp)) (hR 0 (by norm_num))
      (fun t ht => ?_) (fun t ht => by simp [oddExt, ht])
    rcases eq_or_lt_of_le ht with h | h
    · subst h; simp [oddExt, h0]
    · simp [oddExt, not_le.2 h]
  · rw [abs_of_pos hs]
    refine (hR s (by linarith)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp [oddExt, (show 0 < t from ht).le]

/-- At an odd level the flux `−regU(|s|)` of the odd extension has derivative `(c²s² − χ)·oddExt`. -/
theorem hasDerivAt_oddFlux {c χ : ℝ} (hχ : χ ∈ oddSpec (sqC c)) (s : ℝ) :
    HasDerivAt (fun t => -regU (sqC c) χ |t|) ((c ^ 2 * s ^ 2 - χ) * oddExt c χ s) s := by
  have h0 : regSol (sqC c) χ 0 = 0 := hχ
  have hR : ∀ t : ℝ, -1 < t → HasDerivAt (fun x => -regU (sqC c) χ x)
      ((c ^ 2 * t ^ 2 - χ) * regSol (sqC c) χ t) t :=
    fun t ht => (hasDerivAt_regU (sqC c) χ ht).neg.congr_deriv (by simp [sqC])
  have hL : ∀ t : ℝ, t < 1 → HasDerivAt (fun x => -regU (sqC c) χ (-x))
      ((c ^ 2 * t ^ 2 - χ) * -regSol (sqC c) χ (-t)) t :=
    fun t ht => (HasDerivAt.comp_of_eq t (hasDerivAt_regU (sqC c) χ (show -1 < -t by linarith))
      (hasDerivAt_neg' t) rfl).neg.congr_deriv (by simp [sqC])
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · refine ((hL s (by linarith)).congr_deriv (by simp [oddExt, not_le.2 hs])).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hs] with t ht
    simp [abs_of_neg (show t < 0 from ht)]
  · refine hasDerivAt_zero_of_sides ((hL 0 (by norm_num)).congr_deriv (by simp [oddExt, h0]))
      ((hR 0 (by norm_num)).congr_deriv (by simp [oddExt, h0])) (fun t ht => by simp [abs_of_nonpos ht])
      (fun t ht => by simp [abs_of_nonneg ht])
  · refine ((hR s (by linarith)).congr_deriv (by simp [oddExt, hs.le])).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp [abs_of_pos (show 0 < t from ht)]

/-- At an odd level the odd extension is a regular solution, with flux `−regU(|s|)`. -/
theorem isRegSol_oddExt {c χ : ℝ} (hχ : χ ∈ oddSpec (sqC c)) :
    IsRegSol c χ (oddExt c χ) (fun t => -regU (sqC c) χ |t|) := by
  have hU1 : regU (sqC c) χ 1 = 0 := (regSol_system (sqC c) χ).2.2.1
  refine ⟨fun s _ => (hasDerivAt_oddExt hχ s).continuousAt.continuousWithinAt,
    fun s _ => (hasDerivAt_oddFlux hχ s).continuousAt.continuousWithinAt, fun s hs => ?_,
    fun s _ => hasDerivAt_oddFlux hχ s, by simp [hU1], by simp [hU1]⟩
  refine (hasDerivAt_oddExt hχ s).congr_deriv ?_
  have h1 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have hp := pP_mul_regV (sqC c) χ (show (-1 : ℝ) < |s| by linarith [abs_nonneg s])
  rw [← hp]
  simp only [pP, sq_abs]
  field_simp
  ring

/-! ### The levels of the prolate operator -/

/-- The levels of the prolate operator: the `χ` carrying a nonzero regular solution. -/
def prolSpec (c : ℝ) : Set ℝ :=
  {χ | ∃ g w : ℝ → ℝ, IsRegSol c χ g w ∧ ∃ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0}

/-- **The levels are exactly the even and the odd spectrum.** -/
theorem prolSpec_eq (c : ℝ) : prolSpec c = evenSpec (sqC c) ∪ oddSpec (sqC c) := by
  ext χ
  constructor
  · rintro ⟨g, w, h, hg0⟩
    exact h.mem_evenSpec_or_oddSpec hg0
  · rintro (he | ho)
    · obtain ⟨g, g₁, g₂, hg, hg₁, hang, -, hg0⟩ := (isEvenLevel_iff c χ).2 he
      exact ⟨g, _, isRegSol_of_angular hg hg₁ hang, hg0⟩
    · exact ⟨oddExt c χ, _, isRegSol_oddExt ho, 1, ⟨by norm_num, le_rfl⟩, by simp [oddExt, regSol_one]⟩

/-- No level is both even and odd. -/
theorem disjoint_evenSpec_oddSpec (Q : C(ℝ, ℝ)) : Disjoint (evenSpec Q) (oddSpec Q) :=
  Set.disjoint_left.2 fun χ he ho =>
    regU_ne_zero_of_regSol_eq_zero Q χ (by norm_num) (by norm_num) ho he

/-- **The ground level lies strictly below every odd level.** -/
theorem groundLevel_lt_of_mem_oddSpec {c o : ℝ} (ho : o ∈ oddSpec (sqC c)) : groundLevel c < o := by
  have h := (odd_interlace (sqC c) _ o ho rfl).1
  obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (s := evenSpec (sqC c) ∩ Iio o) (by omega)
  exact lt_of_le_of_lt (groundLevel_le_of_mem he.1) he.2

/-- **The least of the even and odd levels is `groundLevel c`.** -/
theorem isLeast_evenSpec_union_oddSpec (c : ℝ) :
    IsLeast (evenSpec (sqC c) ∪ oddSpec (sqC c)) (groundLevel c) := by
  refine ⟨Or.inl (groundLevel_mem c), ?_⟩
  rintro χ (h | h)
  · exact groundLevel_le_of_mem h
  · exact (groundLevel_lt_of_mem_oddSpec h).le

/-- **The least level of the prolate operator is `groundLevel c`.** -/
theorem isLeast_prolSpec (c : ℝ) : IsLeast (prolSpec c) (groundLevel c) := by
  rw [prolSpec_eq]; exact isLeast_evenSpec_union_oddSpec c

/-! ### The ground state -/

/-- The ground rung is a regular solution at `groundLevel c`, with flux `(1−s²)·rung₁ c 0`. -/
theorem isRegSol_rung_zero (c : ℝ) :
    IsRegSol c (groundLevel c) (rung c 0) (fun s => (1 - s ^ 2) * rung₁ c 0 s) := by
  obtain ⟨hg, hg₁, -, hang, -, -⟩ := rung_spec (exists_isLevelIdx_zero c)
  rw [lev_zero] at hang
  exact isRegSol_of_angular hg hg₁ hang

/-- **The ground level is simple**: every regular solution at `groundLevel c` is
`g(1)/rung c 0 1` times `rung c 0` on `[−1, 1]`. -/
theorem eq_mul_rung_zero {c : ℝ} {g w : ℝ → ℝ} (h : IsRegSol c (groundLevel c) g w) :
    ∀ s ∈ Icc (-1 : ℝ) 1, g s = g 1 / rung c 0 1 * rung c 0 s :=
  h.eq_mul (isRegSol_rung_zero c) (rung_one_ne_zero (exists_isLevelIdx_zero c))

/-- The ground rung is even. -/
theorem rung_zero_even (c : ℝ) : ∀ s ∈ Icc (-1 : ℝ) 1, rung c 0 (-s) = rung c 0 s :=
  (rung_spec (exists_isLevelIdx_zero c)).2.2.2.2.1

/-- The ground rung has no zero on `[−1, 1]`. -/
theorem rung_zero_ne_zero (c : ℝ) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) : rung c 0 s ≠ 0 := by
  obtain ⟨hg, hg₁, -, hang, heven, -⟩ := rung_spec (exists_isLevelIdx_zero c)
  have h0 : (evenSpec (sqC c) ∩ Iio (lev c 0)).ncard = 0 := (lev_spec (exists_isLevelIdx_zero c)).2
  have := ground_pos hg hg₁ hang heven (rung_ne_zero (exists_isLevelIdx_zero c)) h0 s hs
  intro h
  rw [h, zero_mul] at this
  exact lt_irrefl 0 this

/-- **Step A for the prolate operator**: `χ₀` is its least level, attained by the even regular solution
`g₀ ≢ 0`, and every regular solution at `χ₀` is a multiple of `g₀`. -/
structure OpStepA (c χ₀ : ℝ) (g₀ w₀ : ℝ → ℝ) : Prop where
  least : IsLeast (prolSpec c) χ₀
  eigen : IsRegSol c χ₀ g₀ w₀
  nonzero : ∃ s ∈ Icc (-1 : ℝ) 1, g₀ s ≠ 0
  simple : ∀ g w : ℝ → ℝ, IsRegSol c χ₀ g w → ∃ a : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, g s = a * g₀ s
  even : ∀ s ∈ Icc (-1 : ℝ) 1, g₀ (-s) = g₀ s

/-- **The prolate operator satisfies Step A** at `groundLevel c` with the ground rung, for every `c`. -/
theorem opStepA (c : ℝ) :
    OpStepA c (groundLevel c) (rung c 0) (fun s => (1 - s ^ 2) * rung₁ c 0 s) :=
  ⟨isLeast_prolSpec c, isRegSol_rung_zero c, rung_ne_zero (exists_isLevelIdx_zero c),
    fun _ _ h => ⟨_, eq_mul_rung_zero h⟩, rung_zero_even c⟩

/-! ### The quadratic form -/

/-- The prolate energy `∫_{−1}^{1} (1−s²)F₁² + c²s²F²` of `F` with derivative `F₁`. -/
def prolQ (c : ℝ) (F F₁ : ℝ → ℝ) : ℝ :=
  ∫ s in (-1 : ℝ)..1, ((1 - s ^ 2) * F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2)

/-- **Picone's identity for the prolate energy**: the excess over `groundLevel c · ∫F²` is
`∫(1−s²)(F₁ − F·g₀'/g₀)²` with `g₀ = rung c 0`. -/
theorem prolQ_sub_eq (c : ℝ) {F F₁ : ℝ → ℝ} (hF : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt F (F₁ s) s)
    (hF₁ : ContinuousOn F₁ (uIcc (-1) 1)) :
    prolQ c F F₁ - groundLevel c * ∫ s in (-1 : ℝ)..1, F s ^ 2 =
      ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) * (F₁ s - F s * rung₁ c 0 s / rung c 0 s) ^ 2 := by
  obtain ⟨hg, hg₁, hg₂c, hang, -, -⟩ := rung_spec (exists_isLevelIdx_zero c)
  rw [← lev_zero]
  set g := rung c 0
  set g₁ := rung₁ c 0
  set g₂ := rung₂ c 0
  set χ := lev c 0
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgne : ∀ s ∈ uIcc (-1 : ℝ) 1, g s ≠ 0 := fun s hs => rung_zero_ne_zero c (hI ▸ hs)
  have hFc : ContinuousOn F (uIcc (-1) 1) := fun s hs => (hF s hs).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (uIcc (-1) 1) := fun s hs => (hg s hs).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (uIcc (-1) 1) := fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  set B : ℝ → ℝ := fun s => (1 - s ^ 2) * F s ^ 2 * g₁ s / g s
  set B' : ℝ → ℝ := fun s => -(2 * s) * F s ^ 2 * g₁ s / g s
      + (1 - s ^ 2) * ((2 * F s * F₁ s * g₁ s + F s ^ 2 * g₂ s) * g s - F s ^ 2 * g₁ s * g₁ s) / g s ^ 2
  have hB : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt B (B' s) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => 1 - s ^ 2) (-(2 * s)) s := by
      simpa using ((hasDerivAt_pow 2 s).const_sub 1)
    have h2 : HasDerivAt (fun s => F s ^ 2 * g₁ s) (2 * F s * F₁ s * g₁ s + F s ^ 2 * g₂ s) s :=
      (((hF s hs).pow 2).mul (hg₁ s hs)).congr_deriv (by simp only [Pi.pow_apply]; ring)
    have h4 := h1.mul (h2.div (hg s hs) (hgne s hs))
    have e : B = fun y => (1 - y ^ 2) * ((fun s => F s ^ 2 * g₁ s) / g) y := by
      funext y; simp only [B, Pi.div_apply]; ring
    rw [e]
    exact h4.congr_deriv (by simp only [B', Pi.div_apply]; ring)
  have hB'c : ContinuousOn B' (uIcc (-1) 1) := by
    have hg2 : ∀ s ∈ uIcc (-1 : ℝ) 1, g s ^ 2 ≠ 0 := fun s hs => pow_ne_zero 2 (hgne s hs)
    have hg₂c' : ContinuousOn g₂ (uIcc (-1) 1) := hg₂c
    have hp : ContinuousOn (fun s : ℝ => 1 - s ^ 2) (uIcc (-1) 1) := by fun_prop
    have hm : ContinuousOn (fun s : ℝ => -(2 * s)) (uIcc (-1) 1) := by fun_prop
    have hFF₁ := hF₁
    have hA : ContinuousOn (fun s => -(2 * s) * F s ^ 2 * g₁ s) (uIcc (-1) 1) :=
      (hm.mul (hFc.pow 2)).mul hg₁c
    have hN : ContinuousOn (fun s => (2 * F s * F₁ s * g₁ s + F s ^ 2 * g₂ s) * g s
        - F s ^ 2 * g₁ s * g₁ s) (uIcc (-1) 1) :=
      ((((continuousOn_const.mul hFc).mul hFF₁).mul hg₁c).add ((hFc.pow 2).mul hg₂c')).mul hgc
        |>.sub (((hFc.pow 2).mul hg₁c).mul hg₁c)
    have hgsq : ContinuousOn (fun s => g s ^ 2) (uIcc (-1) 1) := hgc.pow 2
    exact (hA.div₀ hgc hgne).add ((hp.mul hN).div₀ hgsq hg2)
  have hBint : ∫ s in (-1 : ℝ)..1, B' s = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hB (hB'c.intervalIntegrable)]
    simp [B]
  have hpt : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2 - χ * F s ^ 2 =
      (1 - s ^ 2) * (F₁ s - F s * g₁ s / g s) ^ 2 + B' s := by
    intro s hs
    have hgs := hgne s hs
    have he := hang s hs
    simp only [B']
    field_simp
    linear_combination (-(F s ^ 2) * g s) * he
  have iP : IntervalIntegrable (fun s => (1 - s ^ 2) * (F₁ s - F s * g₁ s / g s) ^ 2) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable ((continuousOn_const.sub (continuous_pow 2).continuousOn).mul
      ((hF₁.sub ((hFc.mul hg₁c).div₀ hgc hgne)).pow 2))
  have cE : ContinuousOn (fun s => (1 - s ^ 2) * F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2) (uIcc (-1) 1) :=
    ((continuousOn_const.sub (continuous_pow 2).continuousOn).mul (hF₁.pow 2)).add
      ((continuousOn_const.mul (continuous_pow 2).continuousOn).mul (hFc.pow 2))
  have iE : IntervalIntegrable (fun s => (1 - s ^ 2) * F₁ s ^ 2 + c ^ 2 * s ^ 2 * F s ^ 2) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable cE
  have cF : ContinuousOn (fun s => F s ^ 2) (uIcc (-1) 1) := hFc.pow 2
  have iF : IntervalIntegrable (fun s => F s ^ 2) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable cF
  unfold prolQ
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub iE (iF.const_mul χ)]
  rw [show (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) * (F₁ s - F s * g₁ s / g s) ^ 2)
      = (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) * (F₁ s - F s * g₁ s / g s) ^ 2) + ∫ s in (-1 : ℝ)..1, B' s by
    rw [hBint, add_zero]]
  rw [← intervalIntegral.integral_add iP hB'c.intervalIntegrable]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have := hpt s hs
  linarith

/-- The energy bottom: `groundLevel c · ∫F² ≤ ∫(1−s²)F'² + c²s²F²` for `F ∈ C¹[−1, 1]`. -/
theorem groundLevel_mul_le (c : ℝ) {F F₁ : ℝ → ℝ} (hF : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt F (F₁ s) s)
    (hF₁ : ContinuousOn F₁ (uIcc (-1) 1)) :
    groundLevel c * ∫ s in (-1 : ℝ)..1, F s ^ 2 ≤ prolQ c F F₁ := by
  have h := prolQ_sub_eq c hF hF₁
  have : 0 ≤ ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) * (F₁ s - F s * rung₁ c 0 s / rung c 0 s) ^ 2 := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun s hs => ?_
    have : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    positivity
  linarith

/-- The ground rung has energy `groundLevel c`. -/
theorem prolQ_rung_zero (c : ℝ) : prolQ c (rung c 0) (rung₁ c 0) = groundLevel c := by
  obtain ⟨hg, hg₁, -, -, -, hsq⟩ := rung_spec (exists_isLevelIdx_zero c)
  have hg₁c : ContinuousOn (rung₁ c 0) (uIcc (-1) 1) :=
    fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt
  have h := prolQ_sub_eq c hg hg₁c
  have hz : ∫ s in (-1 : ℝ)..1,
      (1 - s ^ 2) * (rung₁ c 0 s - rung c 0 s * rung₁ c 0 s / rung c 0 s) ^ 2 = 0 := by
    refine (intervalIntegral.integral_congr fun s hs => ?_).trans intervalIntegral.integral_zero
    have hne := rung_zero_ne_zero c (s := s) (by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs)
    rw [mul_div_cancel_left₀ _ hne, sub_self]; ring
  rw [hz, hsq, mul_one] at h
  linarith

/-- Equality `∫(1−s²)F'² + c²s²F² = groundLevel c · ∫F²` forces `F = a · rung c 0` on `[−1, 1]`. -/
theorem eq_mul_rung_zero_of_eq (c : ℝ) {F F₁ : ℝ → ℝ} (hF : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt F (F₁ s) s)
    (hF₁ : ContinuousOn F₁ (uIcc (-1) 1))
    (heq : prolQ c F F₁ = groundLevel c * ∫ s in (-1 : ℝ)..1, F s ^ 2) :
    ∃ a : ℝ, ∀ s ∈ Icc (-1 : ℝ) 1, F s = a * rung c 0 s := by
  obtain ⟨hg, hg₁, -, -, -, -⟩ := rung_spec (exists_isLevelIdx_zero c)
  set g := rung c 0
  set g₁ := rung₁ c 0
  have hI : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgne : ∀ s ∈ Icc (-1 : ℝ) 1, g s ≠ 0 := fun s hs => rung_zero_ne_zero c hs
  have hFc : ContinuousOn F (Icc (-1) 1) := fun s hs => (hF s (hI ▸ hs)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc (-1) 1) := fun s hs => (hg s (hI ▸ hs)).continuousAt.continuousWithinAt
  have hg₁c : ContinuousOn g₁ (Icc (-1) 1) :=
    fun s hs => (hg₁ s (hI ▸ hs)).continuousAt.continuousWithinAt
  have hP0 := prolQ_sub_eq c hF hF₁
  rw [heq, sub_self] at hP0
  rw [hI] at hF₁
  set P : ℝ → ℝ := fun s => (1 - s ^ 2) * (F₁ s - F s * g₁ s / g s) ^ 2
  have hPc : ContinuousOn P (Icc (-1) 1) :=
    (continuousOn_const.sub (continuous_pow 2).continuousOn).mul
      ((hF₁.sub ((hFc.mul hg₁c).div hgc hgne)).pow 2)
  have hPnn : ∀ s ∈ Icc (-1 : ℝ) 1, 0 ≤ P s := fun s hs => by
    have : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    simp only [P]; positivity
  have hPz : ∀ s ∈ Ioo (-1 : ℝ) 1, P s = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₀, hs₀, hne⟩ := hcon
    have hpos : 0 < P s₀ := lt_of_le_of_ne (hPnn s₀ (Ioo_subset_Icc_self hs₀)) (Ne.symm hne)
    have hU : IsOpen (Ioo (-1 : ℝ) 1 ∩ P ⁻¹' Ioi 0) :=
      (hPc.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_Ioi
    have hmeas : 0 < volume (Ioo (-1 : ℝ) 1 ∩ P ⁻¹' Ioi 0) := hU.measure_pos volume ⟨s₀, hs₀, hpos⟩
    have hint : 0 < ∫ s in (-1 : ℝ)..1, P s := by
      rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae']
      · refine ⟨by norm_num, lt_of_lt_of_le hmeas (measure_mono ?_)⟩
        rintro s ⟨hs, hps⟩
        exact ⟨ne_of_gt hps, Ioo_subset_Ioc_self hs⟩
      · rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
        exact hPnn s (Ioc_subset_Icc_self hs)
      · exact (hPc.mono (by rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])).intervalIntegrable
    have : ∫ s in (-1 : ℝ)..1, P s = 0 := hP0.symm
    linarith
  set q : ℝ → ℝ := fun s => F s / g s
  have hqd : ∀ s ∈ Ioo (-1 : ℝ) 1, HasDerivAt q 0 s := by
    intro s hs
    have hsI := Ioo_subset_Icc_self hs
    have hd : HasDerivAt q ((F₁ s * g s - F s * g₁ s) / g s ^ 2) s :=
      (hF s (hI ▸ hsI)).div (hg s (hI ▸ hsI)) (hgne s hsI)
    refine hd.congr_deriv ?_
    have h1 : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have hz := hPz s hs
    simp only [P] at hz
    have hsq : F₁ s - F s * g₁ s / g s = 0 := by
      rcases mul_eq_zero.1 hz with h | h
      · linarith
      · exact pow_eq_zero_iff two_ne_zero |>.1 h
    have hgs := hgne s hsI
    rw [sub_eq_zero.1 hsq]
    field_simp
    ring
  have hqc : ContinuousOn q (Icc (-1) 1) := hFc.div hgc hgne
  refine ⟨q (-1), fun s hs => ?_⟩
  have hqs : q s = q (-1) := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]
    obtain ⟨t, -, hslope⟩ := exists_hasDerivAt_eq_slope q (fun _ => (0 : ℝ)) h
      (hqc.mono (Icc_subset_Icc le_rfl hs.2))
      (fun t ht => hqd t ⟨ht.1, lt_of_lt_of_le ht.2 hs.2⟩)
    have hne : s - (-1) ≠ 0 := by linarith
    have := hslope.symm
    rw [div_eq_zero_iff] at this
    rcases this with h' | h'
    · linarith
    · exact absurd h' hne
  have hgs := hgne s hs
  calc F s = q s * g s := by simp only [q]; field_simp
    _ = q (-1) * g s := by rw [hqs]

/-- **Step A for an energy `E` on `C¹[−r, r]`**: the bottom `lam` of `E` against `∫F²` is attained at
the nonzero `C¹` function `η`, every function attaining it is a multiple of `η`, and `η` is even. -/
structure FormStepA (r : ℝ) (E : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (lam : ℝ) (η η₁ : ℝ → ℝ) : Prop where
  bottom : ∀ F F₁ : ℝ → ℝ, (∀ s ∈ uIcc (-r) r, HasDerivAt F (F₁ s) s) → ContinuousOn F₁ (uIcc (-r) r) →
    lam * ∫ s in -r..r, F s ^ 2 ≤ E F F₁
  smooth : (∀ s ∈ uIcc (-r) r, HasDerivAt η (η₁ s) s) ∧ ContinuousOn η₁ (uIcc (-r) r)
  attains : E η η₁ = lam * ∫ s in -r..r, η s ^ 2
  nonzero : ∃ s ∈ Icc (-r) r, η s ≠ 0
  simple : ∀ F F₁ : ℝ → ℝ, (∀ s ∈ uIcc (-r) r, HasDerivAt F (F₁ s) s) → ContinuousOn F₁ (uIcc (-r) r) →
    E F F₁ = lam * ∫ s in -r..r, F s ^ 2 → ∃ a : ℝ, ∀ s ∈ Icc (-r) r, F s = a * η s
  even : ∀ s ∈ Icc (-r) r, η (-s) = η s

/-- **The prolate energy satisfies Step A** at `groundLevel c` with the ground rung, for every `c`. -/
theorem prolateStepA (c : ℝ) : FormStepA 1 (prolQ c) (groundLevel c) (rung c 0) (rung₁ c 0) := by
  obtain ⟨hg, hg₁, -, -, -, hsq⟩ := rung_spec (exists_isLevelIdx_zero c)
  refine ⟨fun F F₁ hF hF₁ => groundLevel_mul_le c hF hF₁,
    ⟨hg, fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt⟩, ?_,
    rung_ne_zero (exists_isLevelIdx_zero c), fun F F₁ hF hF₁ heq => eq_mul_rung_zero_of_eq c hF hF₁ heq,
    rung_zero_even c⟩
  rw [prolQ_rung_zero, hsq, mul_one]

/-- **The bottom of the prolate energy on the unit sphere of `C¹[−1, 1]` is `groundLevel c`.** -/
theorem isLeast_prolQ (c : ℝ) :
    IsLeast {q | ∃ F F₁ : ℝ → ℝ, (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt F (F₁ s) s) ∧
      ContinuousOn F₁ (uIcc (-1) 1) ∧ ∫ s in (-1 : ℝ)..1, F s ^ 2 = 1 ∧ prolQ c F F₁ = q} (groundLevel c) := by
  obtain ⟨hg, hg₁, -, -, -, hsq⟩ := rung_spec (exists_isLevelIdx_zero c)
  refine ⟨⟨rung c 0, rung₁ c 0, hg, fun s hs => (hg₁ s hs).continuousAt.continuousWithinAt, hsq,
    prolQ_rung_zero c⟩, ?_⟩
  rintro q ⟨F, F₁, hF, hF₁, h1, rfl⟩
  simpa [h1] using groundLevel_mul_le c hF hF₁

/-! ### Connes' `PW_ℓ` on `[−ℓ, ℓ]` -/

/-- Connes' prolate energy `∫_{−ℓ}^{ℓ} (ℓ²−x²)f₁² + (2πℓx)²f²` of `f` with derivative `f₁`. -/
def pwQ (ℓ : ℝ) (f f₁ : ℝ → ℝ) : ℝ :=
  ∫ x in -ℓ..ℓ, ((ℓ ^ 2 - x ^ 2) * f₁ x ^ 2 + (2 * π * ℓ * x) ^ 2 * f x ^ 2)

/-- Rescaling `x = ℓs` carries Connes' energy to the prolate energy at `c = 2πℓ²`. -/
theorem prolQ_comp_mul {ℓ : ℝ} (hℓ : ℓ ≠ 0) (f f₁ : ℝ → ℝ) :
    prolQ (2 * π * ℓ ^ 2) (fun s => f (ℓ * s)) (fun s => ℓ * f₁ (ℓ * s)) = ℓ⁻¹ * pwQ ℓ f f₁ := by
  have h := intervalIntegral.integral_comp_mul_left (a := -1) (b := 1)
    (fun x => (ℓ ^ 2 - x ^ 2) * f₁ x ^ 2 + (2 * π * ℓ * x) ^ 2 * f x ^ 2) hℓ
  simp only [mul_neg, mul_one, smul_eq_mul] at h
  unfold prolQ pwQ
  rw [← h]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only []
  ring

/-- Rescaling `x = ℓs` in `∫f²`. -/
theorem integral_sq_comp_mul {ℓ : ℝ} (hℓ : ℓ ≠ 0) (f : ℝ → ℝ) :
    ∫ s in (-1 : ℝ)..1, f (ℓ * s) ^ 2 = ℓ⁻¹ * ∫ x in -ℓ..ℓ, f x ^ 2 := by
  have h := intervalIntegral.integral_comp_mul_left (a := -1) (b := 1) (fun x => f x ^ 2) hℓ
  simpa only [mul_neg, mul_one, smul_eq_mul] using h

/-- **Step A transfers from the prolate energy at `c = 2πℓ²` to Connes' `PW_ℓ` energy on `[−ℓ, ℓ]`**,
with minimiser `x ↦ η(x/ℓ)`. -/
theorem FormStepA.pw {ℓ lam : ℝ} (hℓ : 0 < ℓ) {η η₁ : ℝ → ℝ}
    (h : FormStepA 1 (prolQ (2 * π * ℓ ^ 2)) lam η η₁) :
    FormStepA ℓ (pwQ ℓ) lam (fun x => η (x / ℓ)) (fun x => η₁ (x / ℓ) / ℓ) := by
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  have hI1 : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hIℓ : uIcc (-ℓ) ℓ = Icc (-ℓ) ℓ := uIcc_of_le (by linarith)
  -- `s ↦ ℓs` maps `[−1, 1]` to `[−ℓ, ℓ]`, and `x ↦ x/ℓ` maps back
  have hmul : ∀ s ∈ Icc (-1 : ℝ) 1, ℓ * s ∈ Icc (-ℓ) ℓ := fun s hs =>
    ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have hdiv : ∀ x ∈ Icc (-ℓ) ℓ, x / ℓ ∈ Icc (-1 : ℝ) 1 := fun x hx =>
    ⟨by rw [le_div_iff₀ hℓ]; linarith [hx.1], by rw [div_le_iff₀ hℓ]; linarith [hx.2]⟩
  -- pulling a `C¹` function on `[−ℓ, ℓ]` back to `[−1, 1]`
  have hpull : ∀ f f₁ : ℝ → ℝ, (∀ x ∈ uIcc (-ℓ) ℓ, HasDerivAt f (f₁ x) x) → ContinuousOn f₁ (uIcc (-ℓ) ℓ) →
      (∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun s => f (ℓ * s)) (ℓ * f₁ (ℓ * s)) s) ∧
        ContinuousOn (fun s => ℓ * f₁ (ℓ * s)) (uIcc (-1) 1) := by
    intro f f₁ hf hf₁
    rw [hIℓ] at hf hf₁
    rw [hI1]
    refine ⟨fun s hs => ?_, ?_⟩
    · exact ((hf (ℓ * s) (hmul s hs)).comp s ((hasDerivAt_id s).const_mul ℓ)).congr_deriv (by simp; ring)
    · exact continuousOn_const.mul (hf₁.comp (continuousOn_const.mul continuousOn_id) fun s hs => hmul s hs)
  have hQ : ∀ f f₁ : ℝ → ℝ, pwQ ℓ f f₁ = ℓ * prolQ (2 * π * ℓ ^ 2) (fun s => f (ℓ * s))
      (fun s => ℓ * f₁ (ℓ * s)) := fun f f₁ => by
    rw [prolQ_comp_mul hℓ0, ← mul_assoc, mul_inv_cancel₀ hℓ0, one_mul]
  have hN : ∀ f : ℝ → ℝ, ∫ x in -ℓ..ℓ, f x ^ 2 = ℓ * ∫ s in (-1 : ℝ)..1, f (ℓ * s) ^ 2 := fun f => by
    rw [integral_sq_comp_mul hℓ0, ← mul_assoc, mul_inv_cancel₀ hℓ0, one_mul]
  obtain ⟨hη, hη₁⟩ := h.smooth
  rw [hI1] at hη hη₁
  refine ⟨fun f f₁ hf hf₁ => ?_, ⟨fun x hx => ?_, ?_⟩, ?_, ?_, fun f f₁ hf hf₁ heq => ?_, fun x hx => ?_⟩
  · obtain ⟨hF, hF₁⟩ := hpull f f₁ hf hf₁
    have := h.bottom _ _ hF hF₁
    rw [hQ, hN]
    calc lam * (ℓ * ∫ s in (-1 : ℝ)..1, f (ℓ * s) ^ 2) = ℓ * (lam * ∫ s in (-1 : ℝ)..1, f (ℓ * s) ^ 2) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hℓ.le
  · rw [hIℓ] at hx
    exact (hη (x / ℓ) (hdiv x hx)).comp x ((hasDerivAt_id x).div_const ℓ) |>.congr_deriv (by simp; ring)
  · rw [hIℓ]
    exact (hη₁.comp (continuousOn_id.div_const ℓ) fun x hx => hdiv x hx).div_const ℓ
  · rw [hQ, hN]
    simp only [mul_div_cancel_left₀ _ hℓ0, mul_div_cancel₀ _ hℓ0]
    rw [h.attains]
    ring
  · obtain ⟨s, hs, hne⟩ := h.nonzero
    refine ⟨ℓ * s, hmul s hs, ?_⟩
    simpa [mul_div_cancel_left₀ _ hℓ0] using hne
  · obtain ⟨hF, hF₁⟩ := hpull f f₁ hf hf₁
    have heq' : prolQ (2 * π * ℓ ^ 2) (fun s => f (ℓ * s)) (fun s => ℓ * f₁ (ℓ * s)) =
        lam * ∫ s in (-1 : ℝ)..1, f (ℓ * s) ^ 2 := by
      rw [hQ, hN] at heq
      refine mul_left_cancel₀ hℓ0 ?_
      rw [heq]
      ring
    obtain ⟨a, ha⟩ := h.simple _ _ hF hF₁ heq'
    refine ⟨a, fun x hx => ?_⟩
    have := ha (x / ℓ) (hdiv x hx)
    simpa [mul_div_cancel₀ _ hℓ0] using this
  · have hx' := hdiv x hx
    simp only [neg_div]
    exact h.even _ hx'

/-- **Connes' `PW_ℓ` satisfies Step A on `[−ℓ, ℓ]`** at `groundLevel (2πℓ²)`, with the even minimiser
`x ↦ rung (2πℓ²) 0 (x/ℓ)`. -/
theorem pwStepA {ℓ : ℝ} (hℓ : 0 < ℓ) :
    FormStepA ℓ (pwQ ℓ) (groundLevel (2 * π * ℓ ^ 2)) (fun x => rung (2 * π * ℓ ^ 2) 0 (x / ℓ))
      (fun x => rung₁ (2 * π * ℓ ^ 2) 0 (x / ℓ) / ℓ) :=
  (prolateStepA _).pw hℓ

/-! ### Summary -/

/-- **The prolate analogue of Connes' Step A**: the levels of the prolate operator are the even and odd
spectra, the least is `groundLevel c` below every odd level, simple with the even eigenfunction `rung c 0`,
which also spans the minimisers of the prolate energy, and the same holds for `PW_ℓ` at `c = 2πℓ²`. -/
theorem prolate_stepA (c : ℝ) :
    prolSpec c = evenSpec (sqC c) ∪ oddSpec (sqC c) ∧ (∀ o ∈ oddSpec (sqC c), groundLevel c < o) ∧
      OpStepA c (groundLevel c) (rung c 0) (fun s => (1 - s ^ 2) * rung₁ c 0 s) ∧
      FormStepA 1 (prolQ c) (groundLevel c) (rung c 0) (rung₁ c 0) ∧
      ∀ ℓ : ℝ, 0 < ℓ → c = 2 * π * ℓ ^ 2 →
        FormStepA ℓ (pwQ ℓ) (groundLevel c) (fun x => rung c 0 (x / ℓ)) (fun x => rung₁ c 0 (x / ℓ) / ℓ) :=
  ⟨prolSpec_eq c, fun _ ho => groundLevel_lt_of_mem_oddSpec ho, opStepA c, prolateStepA c,
    fun ℓ hℓ hc => by subst hc; exact pwStepA hℓ⟩

end Cvs.StepA.ProlateOperatorStepA
