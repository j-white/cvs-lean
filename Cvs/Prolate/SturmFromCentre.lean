import Mathlib
import Cvs.Prolate.ConverseLevelCount
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LandauHalfEvenSpectrum
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.SturmPolyGaussComparison

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Sturm comparison from the centre: even comparison functions count even levels

If `z` and `y` have zero flux at the centre, `z` vanishes first at `β ∈ (0, 1)` and `y` has the smaller `Q − χ`,
then `y` vanishes in `(0, β)`. So a solution `y` of `((1 − ξ²)y')' = (Q' − χ')y` on `[0, 1]` with `y'(0) = 0`,
at most `k + 1` zeros in `(0, 1)` and `Q' − χ' ≤ c²ξ² − Λ` puts every even level of index `≥ k + 1` at or above `Λ`.
-/

noncomputable section

open Real Set Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge Cvs.Prolate.EdgeCentreSign Cvs.Prolate.EvenLevelIndexLemma Cvs.Prolate.EvenRungsByIndex

namespace Cvs.Prolate.SturmFromCentre

/-! ### Sturm comparison from the centre -/

/-- **Sturm comparison from the centre** for `y' = U/pP`, `U' = −(Q − χ)y` against `z' = Z/pP`, `Z' = −Rz` on
`[0, β] ⊂ [0, 1)`: if `U(0) = Z(0) = 0`, `z` vanishes at `β` and not on `(0, β)`, and `Q − χ < R` on `(0, β)`,
then `y` vanishes in `(0, β)`. -/
theorem exists_zero_of_centre {Q R y U z Z : ℝ → ℝ} {χ β : ℝ} (hβ0 : 0 < β) (hβ : β < 1)
    (hy : ∀ ξ ∈ Icc 0 β, HasDerivAt y (U ξ / pP ξ) ξ)
    (hU : ∀ ξ ∈ Icc 0 β, HasDerivAt U (-((Q ξ - χ) * y ξ)) ξ)
    (hz : ∀ ξ ∈ Icc 0 β, HasDerivAt z (Z ξ / pP ξ) ξ)
    (hZ : ∀ ξ ∈ Icc 0 β, HasDerivAt Z (-(R ξ * z ξ)) ξ)
    (hU0 : U 0 = 0) (hZ0 : Z 0 = 0) (hzβ : z β = 0) (hz0 : ∀ ξ ∈ Ioo 0 β, z ξ ≠ 0)
    (hR : ∀ ξ ∈ Ioo 0 β, Q ξ - χ < R ξ) : ∃ ξ ∈ Ioo 0 β, y ξ = 0 := by
  by_contra hcon
  push Not at hcon
  set μ := β / 2 with hμdef
  have hμ : μ ∈ Ioo 0 β := ⟨by rw [hμdef]; linarith, by rw [hμdef]; linarith⟩
  have hβI : β ∈ Icc 0 β := ⟨hβ0.le, le_rfl⟩
  have h0I : (0 : ℝ) ∈ Icc 0 β := ⟨le_rfl, hβ0.le⟩
  have hpP : ∀ ξ ∈ Icc 0 β, pP ξ < 0 := fun ξ hξ => by
    unfold pP; nlinarith [hξ.1, hξ.2]
  have hsgn : ∀ f : ℝ → ℝ, (∀ ξ ∈ Icc 0 β, ContinuousAt f ξ) → (∀ ξ ∈ Ioo 0 β, f ξ ≠ 0) →
      ∀ ξ ∈ Ioo 0 β, 0 < f μ * f ξ := by
    intro f hf hne ξ hξ
    have hcf : ∀ a b, 0 < a → b < β → ContinuousOn f (Icc a b) := fun a b ha hb s hs =>
      (hf s ⟨by linarith [hs.1], by linarith [hs.2]⟩).continuousWithinAt
    rcases le_total μ ξ with h | h
    · exact mul_pos_of_ne_zero (hcf μ ξ hμ.1 hξ.2)
        (fun s hs => hne s ⟨by linarith [hs.1, hμ.1], by linarith [hs.2, hξ.2]⟩) ξ ⟨h, le_rfl⟩
    · have := mul_pos_of_ne_zero (hcf ξ μ hξ.1 hμ.2)
        (fun s hs => hne s ⟨by linarith [hs.1, hξ.1], by linarith [hs.2, hμ.2]⟩) μ ⟨h, le_rfl⟩
      rwa [mul_comm] at this
  have hyc : ∀ ξ ∈ Icc 0 β, ContinuousAt y ξ := fun ξ hξ => (hy ξ hξ).continuousAt
  have hzc : ∀ ξ ∈ Icc 0 β, ContinuousAt z ξ := fun ξ hξ => (hz ξ hξ).continuousAt
  have hys := hsgn y hyc hcon
  have hzs := hsgn z hzc hz0
  have hyβ : 0 ≤ y μ * y β :=
    ge_of_tendsto (((hyc β hβI).const_mul (y μ)).tendsto.mono_left nhdsWithin_le_nhds)
      (by filter_upwards [Ioo_mem_nhdsLT hβ0] with ξ hξ using (hys ξ hξ).le)
  have hZβ : 0 ≤ z μ * Z β := by
    have hd := deriv_nonpos_of_left ((hz β hβI).const_mul (z μ)) (by
      filter_upwards [Ioo_mem_nhdsLT hβ0] with ξ hξ
      rw [hzβ, mul_zero]; exact (hzs ξ hξ).le)
    have hp := hpP β hβI
    have hp' := hp.ne
    have e : z μ * Z β = z μ * (Z β / pP β) * pP β := by field_simp
    rw [e]
    exact mul_nonneg_of_nonpos_of_nonpos hd hp.le
  set ε := y μ * z μ with hεdef
  set F : ℝ → ℝ := fun ξ => ε * (y ξ * Z ξ - U ξ * z ξ) with hFdef
  have hF : ∀ ξ ∈ Icc 0 β, HasDerivAt F (ε * (((Q ξ - χ) - R ξ) * (y ξ * z ξ))) ξ := by
    intro ξ hξ
    have d := (((hy ξ hξ).mul (hZ ξ hξ)).sub ((hU ξ hξ).mul (hz ξ hξ))).const_mul ε
    refine d.congr_deriv ?_
    have hp := (hpP ξ hξ).ne
    field_simp
    ring
  obtain ⟨c0, hc0, hslope⟩ := exists_hasDerivAt_eq_slope F
    (fun ξ => ε * (((Q ξ - χ) - R ξ) * (y ξ * z ξ))) hβ0
    (fun ξ hξ => (hF ξ hξ).continuousAt.continuousWithinAt)
    (fun ξ hξ => hF ξ (Ioo_subset_Icc_self hξ))
  have hneg : ε * (((Q c0 - χ) - R c0) * (y c0 * z c0)) < 0 := by
    have h1 : 0 < ε * (y c0 * z c0) := by
      have e : ε * (y c0 * z c0) = (y μ * y c0) * (z μ * z c0) := by rw [hεdef]; ring
      rw [e]; exact mul_pos (hys c0 hc0) (hzs c0 hc0)
    have h2 : (Q c0 - χ) - R c0 < 0 := by linarith [hR c0 hc0]
    have e : ε * (((Q c0 - χ) - R c0) * (y c0 * z c0)) =
        ((Q c0 - χ) - R c0) * (ε * (y c0 * z c0)) := by ring
    rw [e]; exact mul_neg_of_neg_of_pos h2 h1
  have hF0 : F 0 = 0 := by simp only [hFdef, hU0, hZ0]; ring
  have hFβ : 0 ≤ F β := by
    have e : F β = (y μ * y β) * (z μ * Z β) := by simp only [hFdef, hεdef, hzβ]; ring
    rw [e]; exact mul_nonneg hyβ hZβ
  have : (F β - F 0) / (β - 0) < 0 := by rw [← hslope]; exact hneg
  have : F β - F 0 < 0 := by
    by_contra hc
    push Not at hc
    exact absurd this (not_lt.mpr (div_nonneg hc (by linarith)))
  linarith

/-! ### Even comparison functions -/

/-- **An even level against an even comparison solution**: if `χ` is an even level of `Q`, `regSol Q χ` has
`k + 1` zeros in `(0, 1)`, `y` solves `((1 − ξ²)y')' = (Q' − χ')y` on `[0, 1]` with `y'(0) = 0`,
`Q' − χ' < Q − χ` on `(0, 1)` and `y` has at most `m` zeros in `(0, 1)`, then `k + 2 ≤ m`. -/
theorem add_two_le_of_even {Q Q' : C(ℝ, ℝ)} {χ χ' : ℝ} {y y₁ y₂ : ℝ → ℝ} {k m : ℕ}
    (hy : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt y (y₁ s) s)
    (hy₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt y₁ (y₂ s) s)
    (hode : ∀ s ∈ Icc (0 : ℝ) 1, (1 - s ^ 2) * y₂ s - 2 * s * y₁ s = (Q' s - χ') * y s)
    (hy0 : y₁ 0 = 0) (hlt : ∀ t ∈ Ioo (0 : ℝ) 1, Q' t - χ' < Q t - χ)
    (hm : {t | t ∈ Ioo (0 : ℝ) 1 ∧ y t = 0}.encard ≤ m)
    (hχ : χ ∈ evenSpec Q) (h : HasZeros Q χ (k + 1)) : k + 2 ≤ m := by
  obtain ⟨w, hw, hw01, hw0⟩ := h
  have hz0 : regSol Q χ 0 ≠ 0 := fun h0 =>
    regU_ne_zero_of_regSol_eq_zero Q χ (by norm_num) (by norm_num) h0 hχ
  -- the first zero `β` of `regSol Q χ` in `(0, 1)`
  set K := Icc 0 (w 0) ∩ regSol Q χ ⁻¹' {0} with hK
  have hKc : IsCompact K :=
    isCompact_Icc.of_isClosed_subset
      ((continuousOn_regSol_Icc Q χ (by norm_num)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton) inter_subset_left
  have hwK : w 0 ∈ K := ⟨⟨(hw01 0).1.le, le_rfl⟩, hw0 0⟩
  obtain ⟨β, ⟨hβI, hβ0⟩, hmin⟩ := hKc.exists_isLeast ⟨w 0, hwK⟩
  have hβpos : 0 < β := lt_of_le_of_ne hβI.1 (fun h => hz0 (h ▸ hβ0))
  have hβ1 : β < 1 := lt_of_le_of_lt hβI.2 (hw01 0).2
  have hne : ∀ t ∈ Ioo 0 β, regSol Q χ t ≠ 0 := fun t ht h0 => by
    have := hmin ⟨⟨ht.1.le, ht.2.le.trans hβI.2⟩, h0⟩
    linarith [ht.2]
  -- a zero of `y` before `β`
  have hpP : ∀ ξ ∈ Icc (0 : ℝ) β, pP ξ ≠ 0 := fun ξ hξ => by
    unfold pP; nlinarith [hξ.1, hξ.2]
  have hIcc : ∀ ξ ∈ Icc (0 : ℝ) β, ξ ∈ Icc (0 : ℝ) 1 := fun ξ hξ => ⟨hξ.1, hξ.2.trans hβ1.le⟩
  obtain ⟨t₀, ht₀, hyt₀⟩ := exists_zero_of_centre (Q := fun s => Q' s) (R := fun s => Q s - χ)
    (U := fun s => pP s * y₁ s) (Z := regU Q χ) (z := regSol Q χ) (χ := χ') hβpos hβ1
    (fun ξ hξ => (hy ξ (hIcc ξ hξ)).congr_deriv (by field_simp [hpP ξ hξ]))
    (fun ξ hξ => by
      have hpd : HasDerivAt pP (2 * ξ) ξ := by
        have := (hasDerivAt_pow 2 ξ).sub_const 1; unfold pP; simpa using this
      refine (hpd.mul (hy₁ ξ (hIcc ξ hξ))).congr_deriv ?_
      have := hode ξ (hIcc ξ hξ)
      simp only [pP]
      linear_combination -this)
    (fun ξ hξ => by
      have hξ1 : (-1 : ℝ) < ξ := by linarith [hξ.1]
      refine (hasDerivAt_regSol Q χ hξ1).congr_deriv ?_
      rw [← pP_mul_regV Q χ hξ1, mul_div_cancel_left₀ _ (hpP ξ hξ)])
    (fun ξ hξ => hasDerivAt_regU Q χ (by linarith [hξ.1]))
    (by simp [hy0]) hχ hβ0 hne (fun ξ hξ => hlt ξ ⟨hξ.1, hξ.2.trans hβ1⟩)
  -- the zeros past each `w i`
  obtain ⟨w', hw', hw'I, hw'0⟩ := Cvs.Prolate.ConverseLevelCount.exists_zeros_of_lt (Q := Q) (Q' := Q') (χ := χ) (χ' := χ')
    hw (fun i => ⟨by linarith [(hw01 i).1], (hw01 i).2⟩) hw0
    (fun i t ht => hlt t ⟨(hw01 i).1.trans ht.1, ht.2⟩)
  have hyeq := Cvs.Prolate.SturmPolyGaussComparison.eq_mul_regSol_of_ode hy hy₁ hode
  have hyw : ∀ i, y (w' i) = 0 := fun i => by
    rw [hyeq (w' i) ⟨((hw01 i).1.trans (hw'I i).1).le, (hw'I i).2.le⟩, hw'0 i, mul_zero]
  set v : Fin (k + 2) → ℝ := Fin.cons t₀ w' with hvdef
  have hv : StrictMono v := Fin.strictMono_cons.2 ⟨fun i => by
    have h1 : w 0 ≤ w i := hw.monotone (Fin.zero_le i)
    linarith [ht₀.2, hβI.2, (hw'I i).1], hw'⟩
  have hsub : range v ⊆ {t | t ∈ Ioo (0 : ℝ) 1 ∧ y t = 0} := by
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [hvdef, Fin.cons_zero]
      exact ⟨⟨ht₀.1, ht₀.2.trans hβ1⟩, hyt₀⟩
    · simp only [hvdef, Fin.cons_succ]
      exact ⟨⟨(hw01 j).1.trans (hw'I j).1, (hw'I j).2⟩, hyw j⟩
  have hcard := (hv.injective.encard_range.symm.trans_le (Set.encard_le_encard hsub)).trans hm
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at hcard
  exact_mod_cast hcard

/-- **Even levels below an even comparison**: if `y` solves `((1 − ξ²)y')' = (Q' − χ')y` on `[0, 1]` with
`y'(0) = 0`, has at most `k + 1` zeros in `(0, 1)`, and `Q' − χ' ≤ Q − Λ` on `(0, 1)`, then at most `k + 1`
even levels of `Q` lie below `Λ`. -/
theorem ncard_evenSpec_le_of_even {Q Q' : C(ℝ, ℝ)} {χ' Λ : ℝ} {y y₁ y₂ : ℝ → ℝ} {k : ℕ}
    (hy : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt y (y₁ s) s)
    (hy₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt y₁ (y₂ s) s)
    (hode : ∀ s ∈ Icc (0 : ℝ) 1, (1 - s ^ 2) * y₂ s - 2 * s * y₁ s = (Q' s - χ') * y s)
    (hy0 : y₁ 0 = 0) (hle : ∀ t ∈ Ioo (0 : ℝ) 1, Q' t - χ' ≤ Q t - Λ)
    (hm : {t | t ∈ Ioo (0 : ℝ) 1 ∧ y t = 0}.encard ≤ k + 1) :
    (evenSpec Q ∩ Iio Λ).ncard ≤ k + 1 := by
  by_contra hcon
  push Not at hcon
  have hne : (evenSpec Q ∩ Iio Λ).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨e, he, heΛ, -, hcard⟩ := Cvs.Prolate.ConverseLevelCount.exists_max_Iio (finite_evenSpec_Iio Q Λ) hne
  have hodd := Cvs.Prolate.ConverseLevelCount.le_ncard_odd_of_even Q _ e he rfl
  have hz : HasZeros Q e (k + 1) :=
    Cvs.Prolate.ConverseLevelCount.hasZeros_of_le (Cvs.Prolate.ConverseLevelCount.hasZeros_ncard_oddSpec Q e) (by omega)
  have := add_two_le_of_even hy hy₁ hode hy0 (fun t ht => by linarith [hle t ht]) hm he hz
  simp only at this
  omega

/-- **Levels above an even comparison**: under the hypotheses of `ncard_evenSpec_le_of_even` with
`Q = c²ξ²`, every even level of index at least `k + 1` lies at or above `Λ`. -/
theorem le_of_even {c Λ χ χ' : ℝ} {Q' : C(ℝ, ℝ)} {y y₁ y₂ : ℝ → ℝ} {j k : ℕ}
    (hy : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt y (y₁ s) s)
    (hy₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt y₁ (y₂ s) s)
    (hode : ∀ s ∈ Icc (0 : ℝ) 1, (1 - s ^ 2) * y₂ s - 2 * s * y₁ s = (Q' s - χ') * y s)
    (hy0 : y₁ 0 = 0) (hle : ∀ t ∈ Ioo (0 : ℝ) 1, Q' t - χ' ≤ c ^ 2 * t ^ 2 - Λ)
    (hm : {t | t ∈ Ioo (0 : ℝ) 1 ∧ y t = 0}.encard ≤ k + 1)
    (hχ : IsLevelIdx c j χ) (hj : k + 1 ≤ j) : Λ ≤ χ :=
  Cvs.Prolate.LandauHalfEvenSpectrum.le_of_ncard_le hχ.1 ((ncard_evenSpec_le_of_even (Q := sqC c) hy hy₁ hode hy0
    (fun t ht => by simpa [sqC] using hle t ht) hm).trans (hχ.2 ▸ hj))

/-- **Polynomial–Gaussian even comparison**: `y = P e^{−Gξ²/2}` with `((1 − ξ²)y')' = (Q' − χ')y` on `[0, 1]`,
`P'(0) = 0`, at most `k + 1` zeros of `P` in `(0, 1)` and `Q' − χ' ≤ c²ξ² − Λ` there put every even level of
index at least `k + 1` at or above `Λ`. -/
theorem le_of_polyGauss_even {c Λ χ χ' G : ℝ} {Q' : C(ℝ, ℝ)} {P P₁ P₂ : ℝ → ℝ} {j k : ℕ}
    (hP : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt P (P₁ s) s)
    (hP₁ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt P₁ (P₂ s) s)
    (hode : ∀ s ∈ Icc (0 : ℝ) 1, (1 - s ^ 2) * (P₂ s - 2 * G * s * P₁ s - G * P s
      + G ^ 2 * s ^ 2 * P s) - 2 * s * (P₁ s - G * s * P s) = (Q' s - χ') * P s)
    (hP0 : P₁ 0 = 0) (hle : ∀ t ∈ Ioo (0 : ℝ) 1, Q' t - χ' ≤ c ^ 2 * t ^ 2 - Λ)
    (hm : {t | t ∈ Ioo (0 : ℝ) 1 ∧ P t = 0}.encard ≤ k + 1)
    (hχ : IsLevelIdx c j χ) (hj : k + 1 ≤ j) : Λ ≤ χ := by
  set e : ℝ → ℝ := fun s => Real.exp (-(G * s ^ 2 / 2)) with he
  have hepos : ∀ s, 0 < e s := fun s => Real.exp_pos _
  have hde : ∀ s, HasDerivAt e (-(G * s) * e s) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => -(G * s ^ 2 / 2)) (-(G * s)) s := by
      have := (((hasDerivAt_pow 2 s).const_mul G).div_const 2).neg
      refine this.congr_deriv ?_
      norm_num
      ring
    exact ((Real.hasDerivAt_exp _).comp s h1).congr_deriv (by simp only [he]; ring)
  refine le_of_even (y := fun s => P s * e s) (y₁ := fun s => (P₁ s - G * s * P s) * e s)
    (y₂ := fun s => (P₂ s - 2 * G * s * P₁ s - G * P s + G ^ 2 * s ^ 2 * P s) * e s)
    (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_) ?_ hle ?_ hχ hj
  · exact ((hP s hs).mul (hde s)).congr_deriv (by ring)
  · have hGs : HasDerivAt (fun s => G * s * P s) (G * P s + G * s * P₁ s) s :=
      (((hasDerivAt_id s).const_mul G).mul (hP s hs)).congr_deriv (by simp)
    exact (((hP₁ s hs).sub hGs).mul (hde s)).congr_deriv (by simp only [Pi.sub_apply]; ring)
  · have := hode s hs
    linear_combination e s * this
  · simp [hP0]
  · refine le_of_eq_of_le (congrArg Set.encard ?_) hm
    ext t
    simp only [mem_ofPred_eq, mul_eq_zero, (hepos t).ne', or_false]

end Cvs.Prolate.SturmFromCentre
