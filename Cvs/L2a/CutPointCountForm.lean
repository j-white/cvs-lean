import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutGap
import Cvs.L2a.CutPointReduction
import Cvs.Prolate.Envelope.RungCountEnvelope
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut-point terms in count form

`|B_X| ≤ (6J/c)Λ°(X)·Σ aᵢ²∫₁^X ψᵢ²` with `Λ°(X) = Σ_{m<n} 2Σ_{θ ∈ {lo, hi}} |log m − ω(θ)|(mK_m + nK_n)/(Γ√(p_m p_n))`,
`K_m = mθ/√(m²θ² − 1)`, `p_m = m²θ² − 1`: `CutGap`'s gap and `RungCountEnvelope`'s envelope at both cut points.
-/

namespace Cvs.L2a.CutPointCountForm

open Real Set Cvs.L2a.AngularProlateTailPositive Cvs.L2a.CutGap Cvs.L2a.CutPointReduction Cvs.Prolate.Envelope.RungCountEnvelope

/-- `K_m(θ) = mθ/√(m²θ² − 1)`. -/
noncomputable def cutK (m θ : ℝ) : ℝ := m * θ / √(m ^ 2 * θ ^ 2 - 1)

/-- The count weight of one cut point, `|log m − ω θ|(m K_m + n K_n)/(Γ √((m²θ² − 1)(n²θ² − 1)))`. -/
noncomputable def cutCount (ω : ℝ → ℝ) (m n θ : ℝ) : ℝ :=
  |Real.log m - ω θ| * (m * cutK m θ + n * cutK n θ)
    / (cutGamma m n θ * √((m ^ 2 * θ ^ 2 - 1) * (n ^ 2 * θ ^ 2 - 1)))

/-- `Λ°(X)`: twice the count weights at both cuts of every pair `m < n ≤ ⌊X⌋`. -/
noncomputable def lamCount (ω : ℝ → ℝ) (t₁ X : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n),
    2 * (cutCount ω m n (cutHi t₁ X m n) + cutCount ω m n (cutLo t₁ m))

variable {ι : Type} [Fintype ι]

theorem abs_cutBdryAt_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {ω : ℝ → ℝ} {X θ : ℝ}
    {m n : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (hm : 1 ≤ m) (hmn : m < n) (hmθ : 6 / 5 ≤ (m : ℝ) * θ) (hnθ : (n : ℝ) * θ ≤ X)
    (hΓ : 0 < cutGamma m n θ) :
    |cutBdryAt c χ g a ω m n θ|
      ≤ 6 * (Fintype.card ι : ℝ) / c * cutCount ω m n θ * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have hθ0 : 0 < θ := by
    by_contra h
    have : (m : ℝ) * θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp h)
    linarith
  set ξ : ℝ := (m : ℝ) * θ with hξdef
  set η : ℝ := (n : ℝ) * θ with hηdef
  have hξη : ξ < η := mul_lt_mul_of_pos_right hmn' hθ0
  have hξ1 : 1 < ξ := by linarith
  have hη1 : 1 < η := by linarith
  have hξI : ξ ∈ Icc (6 / 5 : ℝ) X := ⟨hmθ, by linarith⟩
  have hηI : η ∈ Icc (6 / 5 : ℝ) X := ⟨by linarith, hnθ⟩
  have hpξ : 0 < ξ ^ 2 - 1 := by nlinarith
  have hpη : 0 < η ^ 2 - 1 := by nlinarith
  have eξ : ξ ^ 2 = (m : ℝ) ^ 2 * θ ^ 2 := by rw [hξdef, mul_pow]
  have eη : η ^ 2 = (n : ℝ) ^ 2 * θ ^ 2 := by rw [hηdef, mul_pow]
  have hKm : ξ / √(ξ ^ 2 - 1) = cutK m θ := by unfold cutK; rw [eξ]
  have hKn : η / √(η ^ 2 - 1) = cutK n θ := by unfold cutK; rw [eη]
  have hKm0 : 0 ≤ cutK m θ := by rw [← hKm]; positivity
  have hKn0 : 0 ≤ cutK n θ := by rw [← hKn]; positivity
  set W : ℝ := ((m : ℝ) * cutK m θ + (n : ℝ) * cutK n θ) / (c * cutGamma m n θ) with hW
  have hW0 : 0 ≤ W := by positivity
  set R : ι → ℝ → ℝ := fun i ζ => rungAmp c (χ i) (g i) ζ with hR
  have hR0 : ∀ i ζ, 0 ≤ R i ζ := fun _ _ => Real.sqrt_nonneg _
  -- one rung pair
  have hpair : ∀ i j, |pairBdry c (χ i) (χ j) (g i) (g j) m n θ| ≤ W * (R i ξ * R j η) := by
    intro i j
    have hδ : cutGamma m n θ ≤ cutDelta m n θ (χ i / c ^ 2) (χ j / c ^ 2) :=
      cutGamma_le_cutDelta (by rw [← eξ]; exact hpξ) (by rw [← eη]; exact hpη)
        (div_nonneg (hχ0 i) (sq_nonneg c)) ((div_le_one (by positivity)).2 (hχc j).le)
    have hD : 0 < c ^ 2 * cutGamma m n θ := by positivity
    have hD' : c ^ 2 * cutGamma m n θ ≤ c ^ 2 * cutDelta m n θ (χ i / c ^ 2) (χ j / c ^ 2) :=
      mul_le_mul_of_nonneg_left hδ (sq_nonneg c)
    have hPξ : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP ξ = ξ ^ 2 - 1 := rfl
    have hPη : Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP η = η ^ 2 - 1 := rfl
    have hψi := abs_psi_le_rungAmp (g := g i) hξ1 hc0 (hχc i)
    have hψj := abs_psi_le_rungAmp (g := g j) hη1 hc0 (hχc j)
    have hui := abs_rungU_div_le_rungAmp (g := g i) hξ1 hc0 (hχ0 i) (hχc i)
    have huj := abs_rungU_div_le_rungAmp (g := g j) hη1 hc0 (hχ0 j) (hχc j)
    rw [hKm] at hui
    rw [hKn] at huj
    have hnum : |(m : ℝ) * Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g i) ξ * psi c (g j) η / Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP ξ
        - (n : ℝ) * psi c (g i) ξ * Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g j) η / Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP η|
        ≤ c * ((m : ℝ) * cutK m θ + (n : ℝ) * cutK n θ) * (R i ξ * R j η) := by
      have e1 : |(m : ℝ) * Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g i) ξ * psi c (g j) η / Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP ξ|
          = (m : ℝ) * (|Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g i) ξ| / Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP ξ)
            * |psi c (g j) η| := by
        rw [hPξ, abs_div, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ m),
          abs_of_pos hpξ]
        ring
      have e2 : |(n : ℝ) * psi c (g i) ξ * Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g j) η / Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP η|
          = (n : ℝ) * |psi c (g i) ξ|
            * (|Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g j) η| / Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP η) := by
        rw [hPη, abs_div, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n),
          abs_of_pos hpη]
        ring
      have b1 : (m : ℝ) * (|Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g i) ξ| / Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP ξ)
            * |psi c (g j) η| ≤ (m : ℝ) * (c * cutK m θ * R i ξ) * R j η := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hui (by linarith)) hψj (abs_nonneg _)
        exact mul_nonneg (by linarith) (mul_nonneg (mul_nonneg hc0.le hKm0) (hR0 i ξ))
      have b2 : (n : ℝ) * |psi c (g i) ξ|
            * (|Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g j) η| / Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP η)
            ≤ (n : ℝ) * R i ξ * (c * cutK n θ * R j η) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hψi (by linarith)) huj
        · rw [hPη]; positivity
        · exact mul_nonneg (by linarith) (hR0 i ξ)
      calc _ ≤ _ := abs_sub _ _
        _ ≤ (m : ℝ) * (c * cutK m θ * R i ξ) * R j η + (n : ℝ) * R i ξ * (c * cutK n θ * R j η) := by
          rw [e1, e2]; exact add_le_add b1 b2
        _ = _ := by ring
    have hnum0 : 0 ≤ c * ((m : ℝ) * cutK m θ + (n : ℝ) * cutK n θ) * (R i ξ * R j η) := by
      have := hR0 i ξ; have := hR0 j η; positivity
    unfold pairBdry
    rw [← hξdef, ← hηdef, abs_div, abs_of_pos (lt_of_lt_of_le hD hD')]
    calc _ ≤ c * ((m : ℝ) * cutK m θ + (n : ℝ) * cutK n θ) * (R i ξ * R j η)
          / (c ^ 2 * cutDelta m n θ (χ i / c ^ 2) (χ j / c ^ 2)) :=
          div_le_div_of_nonneg_right hnum (hD.trans_le hD').le
      _ ≤ c * ((m : ℝ) * cutK m θ + (n : ℝ) * cutK n θ) * (R i ξ * R j η) / (c ^ 2 * cutGamma m n θ) :=
          div_le_div_of_nonneg_left hnum0 hD hD'
      _ = W * (R i ξ * R j η) := by rw [hW]; field_simp
  -- the double sum
  have hsum : |∑ i, ∑ j, a i * a j * pairBdry c (χ i) (χ j) (g i) (g j) m n θ|
      ≤ W * ((∑ i, |a i| * R i ξ) * (∑ j, |a j| * R j η)) := by
    calc _ ≤ ∑ i, |∑ j, a i * a j * pairBdry c (χ i) (χ j) (g i) (g j) m n θ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |a i * a j * pairBdry c (χ i) (χ j) (g i) (g j) m n θ| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, W * ((|a i| * R i ξ) * (|a j| * R j η)) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          calc |a i| * |a j| * |pairBdry c (χ i) (χ j) (g i) (g j) m n θ|
              ≤ |a i| * |a j| * (W * (R i ξ * R j η)) :=
                mul_le_mul_of_nonneg_left (hpair i j) (by positivity)
            _ = _ := by ring
      _ = _ := by rw [Finset.sum_mul_sum, Finset.mul_sum]; simp_rw [Finset.mul_sum]
  have htwo := two_point_le a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hξI hηI
  have hP0 : 0 ≤ ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  unfold cutBdryAt
  rw [abs_mul]
  calc |Real.log m - ω θ| * |∑ i, ∑ j, a i * a j * pairBdry c (χ i) (χ j) (g i) (g j) m n θ|
      ≤ |Real.log m - ω θ| * (W * ((∑ i, |a i| * R i ξ) * (∑ j, |a j| * R j η))) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ |Real.log m - ω θ| * (W * (6 * (Fintype.card ι : ℝ) / √((ξ ^ 2 - 1) * (η ^ 2 - 1))
          * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htwo hW0) (abs_nonneg _)
    _ = _ := by
        rw [eξ, eη, hW]
        unfold cutCount
        have : 0 < √(((m : ℝ) ^ 2 * θ ^ 2 - 1) * ((n : ℝ) ^ 2 * θ ^ 2 - 1)) := by
          rw [← eξ, ← eη]; positivity
        field_simp

theorem lamCount_nonneg {ω : ℝ → ℝ} {t₁ X : ℝ} (ht₁ : 6 / 5 ≤ t₁) : 0 ≤ lamCount ω t₁ X := by
  have hsd : 4 < 3 * t₁ ^ 2 := by nlinarith
  have ht1 : (1 : ℝ) ≤ t₁ := by linarith
  unfold lamCount
  refine Finset.sum_nonneg fun m hm => Finset.sum_nonneg fun n hn => ?_
  obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
  obtain ⟨-, hmn⟩ := Finset.mem_filter.mp hn
  have hlo1 : 1 ≤ cutLo t₁ m := by unfold cutLo; split_ifs <;> linarith
  have hc : ∀ θ, cutLo t₁ m ≤ θ → 0 ≤ cutCount ω m n θ := by
    intro θ hθ
    have hΓ := cutGamma_pos_of_cutLo_le hm1 hmn ht1 hsd hθ
    have hθ0 : 0 ≤ θ := by linarith
    have hK : ∀ k : ℝ, 0 ≤ k → 0 ≤ k * cutK k θ := fun k hk => by unfold cutK; positivity
    unfold cutCount
    exact div_nonneg (mul_nonneg (abs_nonneg _) (add_nonneg (hK _ (Nat.cast_nonneg _))
      (hK _ (Nat.cast_nonneg _)))) (mul_nonneg hΓ.le (Real.sqrt_nonneg _))
  exact mul_nonneg (by norm_num) (add_nonneg (hc _ (le_max_left _ _)) (hc _ le_rfl))

/-- **The cut-point terms in count form**: `|B_X| ≤ (6J/c)Λ°(X) Σ aᵢ²∫₁^X ψᵢ²`. -/
theorem bdry_le_count {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {ω : ℝ → ℝ} {t₁ X : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (ht₁ : 6 / 5 ≤ t₁) (hω0 : ∀ θ ∈ Icc 1 t₁, ω θ = 0) :
    |cutB c χ g a ω t₁ X|
      ≤ 6 * (Fintype.card ι : ℝ) / c * lamCount ω t₁ X * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 := by
  have hsd : 4 < 3 * t₁ ^ 2 := by nlinarith
  have ht1 : (1 : ℝ) ≤ t₁ := by linarith
  set P := ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 with hP
  set K := 6 * (Fintype.card ι : ℝ) / c with hK
  have hX0 : 0 ≤ X := by linarith
  have key : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, ∀ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n), ∀ θ,
      cutLo t₁ m ≤ θ → (m = 1 ∧ θ = t₁) ∨ (n : ℝ) * θ ≤ X →
      |cutBdryAt c χ g a ω m n θ| ≤ K * cutCount ω m n θ * P := by
    intro m hm n hn θ hθ hcase
    obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
    obtain ⟨-, hmn⟩ := Finset.mem_filter.mp hn
    rcases hcase with ⟨h1, h2⟩ | hnθ
    · subst h1; rw [h2]
      have hz : Real.log ((1 : ℕ) : ℝ) - ω t₁ = 0 := by
        rw [hω0 t₁ ⟨ht1, le_rfl⟩]; simp
      have hL : cutBdryAt c χ g a ω 1 n t₁ = 0 := by unfold cutBdryAt; rw [hz, zero_mul]
      have hC : cutCount ω ((1 : ℕ) : ℝ) n t₁ = 0 := by unfold cutCount; rw [hz]; simp
      rw [hL, hC]; simp
    · have hmθ : 6 / 5 ≤ (m : ℝ) * θ := by
        unfold cutLo at hθ
        split_ifs at hθ with h
        · subst h; simp; linarith
        · have : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
          nlinarith
      exact abs_cutBdryAt_le a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hm1 hmn hmθ hnθ
        (cutGamma_pos_of_cutLo_le hm1 hmn ht1 hsd hθ)
  clear_value P K
  unfold cutB lamCount
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨hnI, hmn⟩ := Finset.mem_filter.mp hn
  obtain ⟨-, hnX⟩ := Finset.mem_Icc.mp hnI
  have hnle : (n : ℝ) ≤ X := (Nat.cast_le.mpr hnX).trans (Nat.floor_le hX0)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlo : (m = 1 ∧ cutLo t₁ m = t₁) ∨ (n : ℝ) * cutLo t₁ m ≤ X := by
    unfold cutLo
    split_ifs with h
    · exact Or.inl ⟨h, rfl⟩
    · right; simpa using hnle
  have hhi : (m = 1 ∧ cutHi t₁ X m n = t₁) ∨ (n : ℝ) * cutHi t₁ X m n ≤ X := by
    unfold cutHi
    rcases le_total (X / n) (cutLo t₁ m) with h | h
    · rw [max_eq_left h]; exact hlo
    · rw [max_eq_right h]; right; rw [mul_div_cancel₀ _ hnpos.ne']
  have bhi := key m hm n hn _ (le_max_left _ _) hhi
  have blo := key m hm n hn _ le_rfl hlo
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc 2 * |cutBdryAt c χ g a ω m n (cutHi t₁ X m n) - cutBdryAt c χ g a ω m n (cutLo t₁ m)|
      ≤ 2 * (|cutBdryAt c χ g a ω m n (cutHi t₁ X m n)| + |cutBdryAt c χ g a ω m n (cutLo t₁ m)|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ ≤ 2 * (K * cutCount ω m n (cutHi t₁ X m n) * P + K * cutCount ω m n (cutLo t₁ m) * P) :=
        mul_le_mul_of_nonneg_left (add_le_add bhi blo) (by norm_num)
    _ = _ := by ring

end Cvs.L2a.CutPointCountForm
