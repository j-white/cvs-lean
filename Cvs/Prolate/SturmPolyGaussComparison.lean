import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
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
# Polynomial–Gaussian Sturm comparison: no zero of the prolate below `3γ² + 2`

A smaller potential keeps every zero count of the regular solution in `(0, 1)`. A solution `z` of
`((1 − ξ²)z')' = (Q − χ)z` on `[0, 1]` is `z(1) · regSol Q χ`, so at most `m` zeros of `z` and
`Q − χ < c²ξ² − Λ` forbid `m + 1` zeros of `regSol (sqC c) Λ`. For `z = ξe^{−γ²ξ²/2}` with
`γ⁴ + 5γ² = c²` this rules out any zero of `regSol (sqC c) Λ` in `(0, 1)` for `Λ ≤ 3γ² + 2`.
-/

noncomputable section

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.VolterraResolventEdge Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.EvenLevelIndexLemma

namespace Cvs.Prolate.SturmPolyGaussComparison

/-! ### Zeros of the more oscillatory solution -/

/-- Between two zeros `a < b` in `(−1, 1)` of `regSol Q χ`, a smaller `Q' − χ'` forces a zero. -/
theorem exists_zero_Ioo_of_lt {Q Q' : C(ℝ, ℝ)} {χ χ' a b : ℝ} (ha : -1 < a) (hab : a < b)
    (hb : b < 1) (hlt : ∀ t ∈ Ioo a b, Q' t - χ' < Q t - χ) (ha0 : regSol Q χ a = 0)
    (hb0 : regSol Q χ b = 0) : ∃ t ∈ Ioo a b, regSol Q' χ' t = 0 := by
  have hV := regV_ne_zero_of_regSol_eq_zero Q χ ha (hab.trans hb) ha0
  have hev := eventually_mul_deriv_pos (hasDerivAt_regSol Q χ ha) ha0 hV
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hne1 : ∀ t ∈ Ioo a u, regSol Q χ t ≠ 0 := fun t ht h => by
    have := hsub ht
    simp only [mem_ofPred_eq, h, zero_mul, lt_irrefl] at this
  have hub : u ≤ b := by
    by_contra hcon
    exact hne1 b ⟨hab, lt_of_not_ge hcon⟩ hb0
  have hu' : a < (a + u) / 2 := by linarith [mem_Ioi.mp hu]
  have hu'' : (a + u) / 2 < u := by linarith [mem_Ioi.mp hu]
  set K := Icc ((a + u) / 2) b ∩ regSol Q χ ⁻¹' {0} with hK
  have hKc : IsCompact K :=
    isCompact_Icc.of_isClosed_subset
      ((continuousOn_regSol_Icc Q χ (by linarith)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton) inter_subset_left
  have hbK : b ∈ K := ⟨⟨by linarith, le_rfl⟩, hb0⟩
  obtain ⟨b', ⟨hb'I, hb'0⟩, hmin⟩ := hKc.exists_isLeast ⟨b, hbK⟩
  have hne : ∀ t ∈ Ioo a b', regSol Q χ t ≠ 0 := by
    intro t ht h0
    rcases lt_or_ge t u with htu | htu
    · exact hne1 t ⟨ht.1, htu⟩ h0
    · have : b' ≤ t := hmin ⟨⟨by linarith, ht.2.le.trans hb'I.2⟩, h0⟩
      linarith [ht.2]
  obtain ⟨t, ht, ht0⟩ := sturm_between ha (by linarith [hb'I.1]) (lt_of_le_of_lt hb'I.2 hb)
    (fun t ht => hlt t ⟨ht.1, lt_of_lt_of_le ht.2 hb'I.2⟩) ha0 hb'0 hne
  exact ⟨t, ⟨ht.1, lt_of_lt_of_le ht.2 hb'I.2⟩, ht0⟩

/-- Past a zero `a ∈ (−1, 1)` of `regSol Q χ`, a smaller `Q' − χ'` forces a zero in `(a, 1)`. -/
theorem exists_zero_Ioo_one {Q Q' : C(ℝ, ℝ)} {χ χ' a : ℝ} (ha : -1 < a) (ha1 : a < 1)
    (hlt : ∀ t ∈ Ioo a 1, Q' t - χ' < Q t - χ) (ha0 : regSol Q χ a = 0) :
    ∃ t ∈ Ioo a 1, regSol Q' χ' t = 0 := by
  have hc1 : ContinuousAt (regSol Q χ) 1 := (hasDerivAt_regSol Q χ (by norm_num)).continuousAt
  have hev : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < regSol Q χ t :=
    hc1.eventually (eventually_gt_nhds (by rw [regSol_one]; exact one_pos))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set v := max a (1 - ε / 2) with hv
  have hv1 : v < 1 := max_lt ha1 (by linarith)
  set K := Icc a v ∩ regSol Q χ ⁻¹' {0} with hK
  have hKc : IsCompact K :=
    isCompact_Icc.of_isClosed_subset
      ((continuousOn_regSol_Icc Q χ ha).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton) inter_subset_left
  have haK : a ∈ K := ⟨⟨le_rfl, le_max_left _ _⟩, ha0⟩
  obtain ⟨a', ⟨ha'I, ha'0⟩, hmax⟩ := hKc.exists_isGreatest ⟨a, haK⟩
  have hne : ∀ t ∈ Ioo a' 1, regSol Q χ t ≠ 0 := by
    intro t ht h0
    rcases le_or_gt t v with htv | htv
    · have : t ≤ a' := hmax ⟨⟨ha'I.1.trans ht.1.le, htv⟩, h0⟩
      linarith [ht.1]
    · have hd : dist t 1 < ε := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [le_max_right a (1 - ε / 2), ht.2]
      exact (hball hd).ne' h0
  obtain ⟨t, ht, ht0⟩ := sturm_edge (lt_of_lt_of_le ha ha'I.1) (lt_of_le_of_lt ha'I.2 hv1)
    (fun t ht => hlt t ⟨lt_of_le_of_lt ha'I.1 ht.1, ht.2⟩) ha'0 hne
  exact ⟨t, ⟨lt_of_le_of_lt ha'I.1 ht.1, ht.2⟩, ht0⟩

/-- **Sturm count transfer**: `k` zeros in `(0, 1)` persist when `Q − χ` decreases on `(0, 1)`. -/
theorem hasZeros_of_lt {Q Q' : C(ℝ, ℝ)} {χ χ' : ℝ} {k : ℕ} (h : HasZeros Q χ k)
    (hlt : ∀ t ∈ Ioo (0 : ℝ) 1, Q' t - χ' < Q t - χ) : HasZeros Q' χ' k := by
  obtain ⟨w, hw, hw01, hw0⟩ := h
  set nx : Fin k → ℝ := fun i => if hi : i.val + 1 < k then w ⟨i.val + 1, hi⟩ else 1 with hnx
  have hnx1 : ∀ i, nx i ≤ 1 := fun i => by
    simp only [hnx]
    split_ifs
    · exact (hw01 _).2.le
    · exact le_rfl
  have key : ∀ i, ∃ t ∈ Ioo (w i) (nx i), regSol Q' χ' t = 0 := by
    intro i
    have hwi := hw01 i
    by_cases hi : i.val + 1 < k
    · simp only [hnx, dite_eq_left hi]
      have hlt' : w i < w ⟨i.val + 1, hi⟩ := hw (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _))
      exact exists_zero_Ioo_of_lt (by linarith) hlt' (hw01 _).2
        (fun t ht => hlt t ⟨hwi.1.trans ht.1, ht.2.trans (hw01 _).2⟩) (hw0 i) (hw0 _)
    · simp only [hnx, dite_eq_right hi]
      exact exists_zero_Ioo_one (by linarith) hwi.2
        (fun t ht => hlt t ⟨hwi.1.trans ht.1, ht.2⟩) (hw0 i)
  choose w' hw' hw'0 using key
  refine ⟨w', fun i j hij => ?_, fun i => ⟨(hw01 i).1.trans (hw' i).1,
    (hw' i).2.trans_le (hnx1 i)⟩, hw'0⟩
  have hi : i.val + 1 < k := lt_of_le_of_lt (Nat.succ_le_of_lt hij) j.isLt
  have h1 : nx i = w ⟨i.val + 1, hi⟩ := by simp only [hnx, dite_eq_left hi]
  have h2 : w ⟨i.val + 1, hi⟩ ≤ w j := hw.monotone (Fin.mk_le_mk.mpr (Nat.succ_le_of_lt hij))
  linarith [(hw' i).2, (hw' j).1]

/-! ### A solution of the equation is a multiple of the regular solution -/

/-- A solution of `((1 − ξ²)z')' = (Q − χ)z` on `[0, 1]` is `z(1) · regSol Q χ` there. -/
theorem eq_mul_regSol_of_ode {Q : C(ℝ, ℝ)} {χ : ℝ} {z z₁ z₂ : ℝ → ℝ}
    (hz : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt z (z₁ s) s)
    (hz₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt z₁ (z₂ s) s)
    (hode : ∀ s ∈ Icc (0 : ℝ) 1, (1 - s ^ 2) * z₂ s - 2 * s * z₁ s = (Q s - χ) * z s) :
    ∀ s ∈ Icc (0 : ℝ) 1, z s = z 1 * regSol Q χ s := by
  intro s hs
  have h : Adm 0 1 := ⟨by norm_num, by norm_num, le_rfl⟩
  have hpd : ∀ t : ℝ, HasDerivAt pP (2 * t) t := fun t => by
    have := (hasDerivAt_pow 2 t).sub_const 1; unfold pP; simpa using this
  refine (eq_mul_regSol Q χ h (ψ := z) (u := fun t => pP t * z₁ t)
    (fun t ht => (hz t ht).continuousAt.continuousWithinAt)
    (fun t ht => ((hpd t).mul (hz₁ t ht)).continuousAt.continuousWithinAt) ?_ ?_ ?_ s hs).1
  · intro t ht ht1
    have hp := pP_ne_zero (by linarith [ht.1]) ht1
    refine (hz t (Ioo_subset_Icc_self ht)).congr_deriv ?_
    rw [mul_div_cancel_left₀ _ hp]
  · intro t ht
    refine ((hpd t).mul (hz₁ t (Ioo_subset_Icc_self ht))).congr_deriv ?_
    have := hode t (Ioo_subset_Icc_self ht)
    simp only [pP]
    linear_combination -this
  · simp [pP]

/-- **Comparison by a solution**: if a solution `z` of `((1 − ξ²)z')' = (Q − χ)z` on `[0, 1]` has
at most `m` zeros in `(0, 1)` and `Q − χ < Q' − χ'` there, `regSol Q' χ'` has no `m + 1`. -/
theorem not_hasZeros_of_ode {Q Q' : C(ℝ, ℝ)} {χ χ' : ℝ} {z z₁ z₂ : ℝ → ℝ} {m : ℕ}
    (hz : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt z (z₁ s) s)
    (hz₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt z₁ (z₂ s) s)
    (hode : ∀ s ∈ Icc (0 : ℝ) 1, (1 - s ^ 2) * z₂ s - 2 * s * z₁ s = (Q s - χ) * z s)
    (hlt : ∀ t ∈ Ioo (0 : ℝ) 1, Q t - χ < Q' t - χ')
    (hm : {t | t ∈ Ioo (0 : ℝ) 1 ∧ z t = 0}.encard ≤ m) : ¬HasZeros Q' χ' (m + 1) := by
  intro h
  obtain ⟨w, hw, hw01, hw0⟩ := hasZeros_of_lt h hlt
  have hsub : range w ⊆ {t | t ∈ Ioo (0 : ℝ) 1 ∧ z t = 0} := by
    rintro _ ⟨i, rfl⟩
    refine ⟨hw01 i, ?_⟩
    rw [eq_mul_regSol_of_ode hz hz₁ hode (w i) ⟨(hw01 i).1.le, (hw01 i).2.le⟩, hw0 i, mul_zero]
  have hcard := (hw.injective.encard_range.symm.trans_le (Set.encard_le_encard hsub)).trans hm
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at hcard
  norm_cast at hcard
  omega

/-! ### Polynomial–Gaussian comparison functions -/

/-- **Polynomial–Gaussian comparison**: `z = P e^{−Gξ²/2}` with `((1 − ξ²)z')' = (Q − χ)z` on
`[0, 1]`, at most `m` zeros of `P` in `(0, 1)` and `Q − χ < Q' − χ'` there forbid `m + 1` zeros. -/
theorem not_hasZeros_of_polyGauss {Q Q' : C(ℝ, ℝ)} {χ χ' G : ℝ} {P P₁ P₂ : ℝ → ℝ} {m : ℕ}
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt P (P₁ s) s)
    (hP₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt P₁ (P₂ s) s)
    (hode : ∀ s ∈ Icc (0 : ℝ) 1, (1 - s ^ 2) * (P₂ s - 2 * G * s * P₁ s - G * P s
      + G ^ 2 * s ^ 2 * P s) - 2 * s * (P₁ s - G * s * P s) = (Q s - χ) * P s)
    (hlt : ∀ t ∈ Ioo (0 : ℝ) 1, Q t - χ < Q' t - χ')
    (hm : {t | t ∈ Ioo (0 : ℝ) 1 ∧ P t = 0}.encard ≤ m) : ¬HasZeros Q' χ' (m + 1) := by
  set e : ℝ → ℝ := fun s => Real.exp (-(G * s ^ 2 / 2)) with he
  have hepos : ∀ s, 0 < e s := fun s => Real.exp_pos _
  have hde : ∀ s, HasDerivAt e (-(G * s) * e s) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => -(G * s ^ 2 / 2)) (-(G * s)) s := by
      have := (((hasDerivAt_pow 2 s).const_mul G).div_const 2).neg
      refine this.congr_deriv ?_
      norm_num
      ring
    exact ((Real.hasDerivAt_exp _).comp s h1).congr_deriv (by simp only [he]; ring)
  refine not_hasZeros_of_ode (z := fun s => P s * e s) (z₁ := fun s => (P₁ s - G * s * P s) * e s)
    (z₂ := fun s => (P₂ s - 2 * G * s * P₁ s - G * P s + G ^ 2 * s ^ 2 * P s) * e s)
    (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_) hlt ?_
  · exact ((hP s hs).mul (hde s)).congr_deriv (by ring)
  · have hGs : HasDerivAt (fun s => G * s * P s) (G * P s + G * s * P₁ s) s :=
      (((hasDerivAt_id s).const_mul G).mul (hP s hs)).congr_deriv (by simp)
    exact (((hP₁ s hs).sub hGs).mul (hde s)).congr_deriv (by simp only [Pi.sub_apply]; ring)
  · have := hode s hs
    linear_combination e s * this
  · refine le_of_eq_of_le (congrArg Set.encard ?_) hm
    ext t
    simp only [mem_ofPred_eq, mul_eq_zero, (hepos t).ne', or_false]

/-! ### The first odd comparison: `z = ξe^{−Gξ²/2}` with `G² + 5G = c²` -/

/-- The potential `(G² + 5G)ξ² − G²ξ⁴ − 3G − 2` of `ξe^{−Gξ²/2}`. -/
def potOne (G : ℝ) : C(ℝ, ℝ) :=
  ⟨fun s => (G ^ 2 + 5 * G) * s ^ 2 - G ^ 2 * s ^ 4 - (3 * G + 2), by fun_prop⟩

/-- For `G ≠ 0` with `G² + 5G = c²` and `Λ ≤ 3G + 2`, `regSol (sqC c) Λ` has no zero in `(0, 1)`. -/
theorem not_hasZeros_one_of_sq {c G Λ : ℝ} (hG : G ≠ 0) (hc : G ^ 2 + 5 * G = c ^ 2)
    (hΛ : Λ ≤ 3 * G + 2) : ¬HasZeros (sqC c) Λ 1 := by
  refine not_hasZeros_of_polyGauss (m := 0) (Q := potOne G) (χ := 0) (G := G) (P := fun s => s)
    (P₁ := fun _ => 1) (P₂ := fun _ => 0) (fun s _ => hasDerivAt_id s)
    (fun s _ => hasDerivAt_const s 1) (fun s _ => ?_) (fun t ht => ?_) ?_
  · simp only [potOne, ContinuousMap.coe_mk]; ring
  · have h4 : 0 < G ^ 2 * t ^ 4 := by have := ht.1; positivity
    have hct : c ^ 2 * t ^ 2 = (G ^ 2 + 5 * G) * t ^ 2 := by rw [hc]
    simp only [potOne, sqC, ContinuousMap.coe_mk]
    linarith
  · have : {t : ℝ | t ∈ Ioo (0 : ℝ) 1 ∧ t = 0} = ∅ := by
      ext t; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro ht h0; exact ht.1.ne' h0
    rw [this, Set.encard_empty]; rfl

/-- The positive root `G = (√(25 + 4c²) − 5)/2` of `G² + 5G = c²`. -/
def gOne (c : ℝ) : ℝ := (√(25 + 4 * c ^ 2) - 5) / 2

/-- `gOne c` solves `G² + 5G = c²`. -/
theorem gOne_sq_add (c : ℝ) : gOne c ^ 2 + 5 * gOne c = c ^ 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 25 + 4 * c ^ 2 by positivity)
  unfold gOne
  linear_combination h / 4

/-- `gOne c` is positive for `c ≠ 0`. -/
theorem gOne_pos {c : ℝ} (hc : c ≠ 0) : 0 < gOne c := by
  have h5 : (5 : ℝ) < √(25 + 4 * c ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    have := pow_pos (abs_pos.mpr hc) 2
    rw [sq_abs] at this
    linarith
  unfold gOne
  linarith

/-- `gOne c ≥ |c| − 5/2`. -/
theorem abs_sub_le_gOne (c : ℝ) : |c| - 5 / 2 ≤ gOne c := by
  have h : 2 * |c| ≤ √(25 + 4 * c ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity), mul_pow, sq_abs]
    linarith
  unfold gOne
  linarith

/-- **No zero below `3γ² + 2`**: for `c ≠ 0` and `Λ ≤ 3 gOne c + 2`, `regSol (sqC c) Λ` has no
zero in `(0, 1)`. -/
theorem not_hasZeros_one {c Λ : ℝ} (hc : c ≠ 0) (hΛ : Λ ≤ 3 * gOne c + 2) :
    ¬HasZeros (sqC c) Λ 1 :=
  not_hasZeros_one_of_sq (gOne_pos hc).ne' (gOne_sq_add c) hΛ

end Cvs.Prolate.SturmPolyGaussComparison
