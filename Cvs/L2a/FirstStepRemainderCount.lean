import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutGap
import Cvs.L2a.CutPointReduction
import Cvs.L2a.NonresonantCrossIntegral
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
# The first-step remainder in count form

`|R_X| ≤ (6J/c)κ(X)·Σ aᵢ²∫₁^X ψᵢ²` with `κ(X) = Σ_{m<n} 2∫_{lo}^{hi} ρ_mn` and `ρ_mn` the `c`-free density built from
`|ω|`, `|ω'|`, `Γ`, `p_m`, `p_n` and `|δ'| ≤ 2n⁴θ/p_n² + 2m⁴θ/p_m²`: `CutGap`'s gap and `RungCountEnvelope`'s envelope inside the integrals.
-/

namespace Cvs.L2a.FirstStepRemainderCount

open Real Set Cvs.L2a.NonresonantCrossIntegral Cvs.L2a.AngularProlateTailPositive Cvs.L2a.CutGap Cvs.L2a.CutPointReduction Cvs.Prolate.Envelope.RungCountEnvelope

/-- The remainder density of one cut pair (`c`-free, rung-free). -/
noncomputable def remDensity (ω ω₁ : ℝ → ℝ) (m n θ : ℝ) : ℝ :=
  ((n ^ 2 * θ / √(n ^ 2 * θ ^ 2 - 1)) * (|ω₁ θ| / cutGamma m n θ + |Real.log m - ω θ|
        * (cutDeltaBound m n θ / cutGamma m n θ ^ 2 + 2 * n ^ 2 * θ / (cutGamma m n θ * (n ^ 2 * θ ^ 2 - 1))))
    + (m ^ 2 * θ / √(m ^ 2 * θ ^ 2 - 1)) * (|ω₁ θ| / cutGamma m n θ + |Real.log m - ω θ|
        * (cutDeltaBound m n θ / cutGamma m n θ ^ 2 + 2 * m ^ 2 * θ / (cutGamma m n θ * (m ^ 2 * θ ^ 2 - 1)))))
    / √((m ^ 2 * θ ^ 2 - 1) * (n ^ 2 * θ ^ 2 - 1))

/-- `κ(X)`: twice the remainder density integrated over `[lo, hi]` for every pair `m < n ≤ ⌊X⌋`. -/
noncomputable def kapCount (ω ω₁ : ℝ → ℝ) (t₁ X : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n),
    2 * ∫ θ in cutLo t₁ m..cutHi t₁ X m n, remDensity ω ω₁ m n θ

theorem abs_coefA_le {c χi χj m n θ : ℝ} (hc : 0 < c) (hn : 0 < n) (hpm : 0 < m ^ 2 * θ ^ 2 - 1)
    (hpn : 0 < n ^ 2 * θ ^ 2 - 1) (hχi : 0 ≤ χi) (hχj : χj ≤ c ^ 2) (hΓ : 0 < cutGamma m n θ) :
    |coefA c χi χj m n θ| ≤ n ^ 2 / (c ^ 2 * cutGamma m n θ * (n ^ 2 * θ ^ 2 - 1)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hδ : cutGamma m n θ ≤ cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) :=
    cutGamma_le_cutDelta hpm hpn (div_nonneg hχi hc2.le) ((div_le_one hc2).mpr hχj)
  have hδ0 : 0 < cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) := lt_of_lt_of_le hΓ hδ
  have hP : pm n θ = (n ^ 2 * θ ^ 2 - 1) / n ^ 2 := rfl
  have hP0 : 0 < pm n θ := by rw [hP]; positivity
  unfold coefA
  rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity), hP]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : c ^ 2 * cutGamma m n θ * (n ^ 2 * θ ^ 2 - 1)
      ≤ c ^ 2 * cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * (n ^ 2 * θ ^ 2 - 1) := by gcongr
  have hn2 : 0 < n ^ 2 := by positivity
  field_simp
  nlinarith

theorem abs_coefA'_le {c χi χj m n θ : ℝ} (hc : 0 < c) (hn : 0 < n) (hθ : 0 ≤ θ)
    (hpm : 0 < m ^ 2 * θ ^ 2 - 1) (hpn : 0 < n ^ 2 * θ ^ 2 - 1) (hχi0 : 0 ≤ χi) (hχi : χi ≤ c ^ 2)
    (hχj0 : 0 ≤ χj) (hχj : χj ≤ c ^ 2) (hΓ : 0 < cutGamma m n θ) :
    |coefA' c χi χj m n θ|
      ≤ (n ^ 2 * cutDeltaBound m n θ / (cutGamma m n θ ^ 2 * (n ^ 2 * θ ^ 2 - 1))
          + 2 * n ^ 4 * θ / (cutGamma m n θ * (n ^ 2 * θ ^ 2 - 1) ^ 2)) / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  set x := χi / c ^ 2
  set x' := χj / c ^ 2
  have hx0 : 0 ≤ x := div_nonneg hχi0 hc2.le
  have hx1 : x ≤ 1 := (div_le_one hc2).mpr hχi
  have hx0' : 0 ≤ x' := div_nonneg hχj0 hc2.le
  have hx1' : x' ≤ 1 := (div_le_one hc2).mpr hχj
  set δ := cutDelta m n θ x x'
  set Γ := cutGamma m n θ
  have hδ : Γ ≤ δ := cutGamma_le_cutDelta hpm hpn hx0 hx1'
  have hδ0 : 0 < δ := lt_of_lt_of_le hΓ hδ
  have hd := abs_cutDelta'_le (m := m) (n := n) hθ hx0 hx1 hx0' hx1'
  set d := cutDelta' m n θ x x'
  set B := cutDeltaBound m n θ
  set pn := n ^ 2 * θ ^ 2 - 1
  have hP : pm n θ = pn / n ^ 2 := rfl
  have hn2 : 0 < n ^ 2 := by positivity
  have hP0 : 0 < pm n θ := by rw [hP]; positivity
  unfold coefA'
  rw [hP]
  have hnum : |d * (pn / n ^ 2) + δ * (2 * θ)| ≤ |d| * (pn / n ^ 2) + δ * (2 * θ) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : 0 < pn / n ^ 2), abs_of_nonneg (by positivity : 0 ≤ δ * (2 * θ))]
  have hden : 0 < c ^ 2 * (δ * (pn / n ^ 2)) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden]
  calc |d * (pn / n ^ 2) + δ * (2 * θ)| / (c ^ 2 * (δ * (pn / n ^ 2)) ^ 2)
      ≤ (|d| * (pn / n ^ 2) + δ * (2 * θ)) / (c ^ 2 * (δ * (pn / n ^ 2)) ^ 2) :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = (|d| * n ^ 2 / (δ ^ 2 * pn) + 2 * n ^ 4 * θ / (δ * pn ^ 2)) / c ^ 2 := by
        field_simp
    _ ≤ (n ^ 2 * B / (Γ ^ 2 * pn) + 2 * n ^ 4 * θ / (Γ * pn ^ 2)) / c ^ 2 := by
        apply div_le_div_of_nonneg_right _ hc2.le
        apply add_le_add
        · rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : |d| * n ^ 2 ≤ n ^ 2 * B := by nlinarith [abs_nonneg d]
          have h2 : Γ ^ 2 * pn ≤ δ ^ 2 * pn := by
            apply mul_le_mul_of_nonneg_right _ hpn.le
            exact pow_le_pow_left₀ hΓ.le hδ 2
          have h3 : 0 ≤ n ^ 2 * B := by
            have : 0 ≤ B := le_trans (abs_nonneg d) hd
            positivity
          calc |d| * n ^ 2 * (Γ ^ 2 * pn) ≤ n ^ 2 * B * (Γ ^ 2 * pn) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ n ^ 2 * B * (δ ^ 2 * pn) := mul_le_mul_of_nonneg_left h2 h3
        · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hδ (by positivity)

theorem abs_coefB_le {c χi χj m n θ : ℝ} (hc : 0 < c) (hm : 0 < m) (hpm : 0 < m ^ 2 * θ ^ 2 - 1)
    (hpn : 0 < n ^ 2 * θ ^ 2 - 1) (hχi : 0 ≤ χi) (hχj : χj ≤ c ^ 2) (hΓ : 0 < cutGamma m n θ) :
    |coefB c χi χj m n θ| ≤ m ^ 2 / (c ^ 2 * cutGamma m n θ * (m ^ 2 * θ ^ 2 - 1)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hδ : cutGamma m n θ ≤ cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) :=
    cutGamma_le_cutDelta hpm hpn (div_nonneg hχi hc2.le) ((div_le_one hc2).mpr hχj)
  have hδ0 : 0 < cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) := lt_of_lt_of_le hΓ hδ
  have hP : pm m θ = (m ^ 2 * θ ^ 2 - 1) / m ^ 2 := rfl
  have hP0 : 0 < pm m θ := by rw [hP]; positivity
  unfold coefB
  rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity), hP]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : c ^ 2 * cutGamma m n θ * (m ^ 2 * θ ^ 2 - 1)
      ≤ c ^ 2 * cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * (m ^ 2 * θ ^ 2 - 1) := by gcongr
  have hm2 : 0 < m ^ 2 := by positivity
  field_simp
  nlinarith

theorem abs_coefB'_le {c χi χj m n θ : ℝ} (hc : 0 < c) (hm : 0 < m) (hθ : 0 ≤ θ)
    (hpm : 0 < m ^ 2 * θ ^ 2 - 1) (hpn : 0 < n ^ 2 * θ ^ 2 - 1) (hχi0 : 0 ≤ χi) (hχi : χi ≤ c ^ 2)
    (hχj0 : 0 ≤ χj) (hχj : χj ≤ c ^ 2) (hΓ : 0 < cutGamma m n θ) :
    |coefB' c χi χj m n θ|
      ≤ (m ^ 2 * cutDeltaBound m n θ / (cutGamma m n θ ^ 2 * (m ^ 2 * θ ^ 2 - 1))
          + 2 * m ^ 4 * θ / (cutGamma m n θ * (m ^ 2 * θ ^ 2 - 1) ^ 2)) / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  set x := χi / c ^ 2
  set x' := χj / c ^ 2
  have hx0 : 0 ≤ x := div_nonneg hχi0 hc2.le
  have hx1 : x ≤ 1 := (div_le_one hc2).mpr hχi
  have hx0' : 0 ≤ x' := div_nonneg hχj0 hc2.le
  have hx1' : x' ≤ 1 := (div_le_one hc2).mpr hχj
  set δ := cutDelta m n θ x x'
  set Γ := cutGamma m n θ
  have hδ : Γ ≤ δ := cutGamma_le_cutDelta hpm hpn hx0 hx1'
  have hδ0 : 0 < δ := lt_of_lt_of_le hΓ hδ
  have hd := abs_cutDelta'_le (m := m) (n := n) hθ hx0 hx1 hx0' hx1'
  set d := cutDelta' m n θ x x'
  set B := cutDeltaBound m n θ
  set pq := m ^ 2 * θ ^ 2 - 1
  have hP : pm m θ = pq / m ^ 2 := rfl
  have hm2 : 0 < m ^ 2 := by positivity
  have hP0 : 0 < pm m θ := by rw [hP]; positivity
  unfold coefB'
  rw [hP]
  have hnum : |d * (pq / m ^ 2) + δ * (2 * θ)| ≤ |d| * (pq / m ^ 2) + δ * (2 * θ) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : 0 < pq / m ^ 2), abs_of_nonneg (by positivity : 0 ≤ δ * (2 * θ))]
  have hden : 0 < c ^ 2 * (δ * (pq / m ^ 2)) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hden]
  calc |d * (pq / m ^ 2) + δ * (2 * θ)| / (c ^ 2 * (δ * (pq / m ^ 2)) ^ 2)
      ≤ (|d| * (pq / m ^ 2) + δ * (2 * θ)) / (c ^ 2 * (δ * (pq / m ^ 2)) ^ 2) :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = (|d| * m ^ 2 / (δ ^ 2 * pq) + 2 * m ^ 4 * θ / (δ * pq ^ 2)) / c ^ 2 := by
        field_simp
    _ ≤ (m ^ 2 * B / (Γ ^ 2 * pq) + 2 * m ^ 4 * θ / (Γ * pq ^ 2)) / c ^ 2 := by
        apply div_le_div_of_nonneg_right _ hc2.le
        apply add_le_add
        · rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : |d| * m ^ 2 ≤ m ^ 2 * B := by nlinarith [abs_nonneg d]
          have h2 : Γ ^ 2 * pq ≤ δ ^ 2 * pq := by
            apply mul_le_mul_of_nonneg_right _ hpm.le
            exact pow_le_pow_left₀ hΓ.le hδ 2
          have h3 : 0 ≤ m ^ 2 * B := by
            have : 0 ≤ B := le_trans (abs_nonneg d) hd
            positivity
          calc |d| * m ^ 2 * (Γ ^ 2 * pq) ≤ m ^ 2 * B * (Γ ^ 2 * pq) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ ≤ m ^ 2 * B * (δ ^ 2 * pq) := mul_le_mul_of_nonneg_left h2 h3
        · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hδ (by positivity)

/-- `remDensity ≥ 0` past the lower cut. -/
theorem remDensity_nonneg {ω ω₁ : ℝ → ℝ} {m n θ : ℝ} (hθ : 0 ≤ θ) (hpm : 0 < m ^ 2 * θ ^ 2 - 1)
    (hpn : 0 < n ^ 2 * θ ^ 2 - 1) (hΓ : 0 < cutGamma m n θ) : 0 ≤ remDensity ω ω₁ m n θ := by
  have hB : 0 ≤ cutDeltaBound m n θ := by unfold cutDeltaBound; positivity
  unfold remDensity
  generalize cutDeltaBound m n θ = B at hB ⊢
  generalize cutGamma m n θ = Γ at hΓ ⊢
  generalize m ^ 2 * θ ^ 2 - 1 = pm at hpm ⊢
  generalize n ^ 2 * θ ^ 2 - 1 = pn at hpn ⊢
  positivity

theorem kapCount_nonneg {ω ω₁ : ℝ → ℝ} {t₁ X : ℝ} (ht₁ : 6 / 5 ≤ t₁) : 0 ≤ kapCount ω ω₁ t₁ X := by
  have hsd : 4 < 3 * t₁ ^ 2 := by nlinarith
  have ht1 : (1 : ℝ) ≤ t₁ := by linarith
  have ht1' : (1 : ℝ) < t₁ := by linarith
  unfold kapCount
  refine Finset.sum_nonneg fun m hm => Finset.sum_nonneg fun n hn => ?_
  obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
  obtain ⟨-, hmn⟩ := Finset.mem_filter.mp hn
  have hlo1 : 1 ≤ cutLo t₁ m := by unfold cutLo; split_ifs <;> linarith
  refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg (le_max_left _ _) fun θ hθ => ?_)
  have hpm := one_lt_sq_mul_of_cutLo_le hm1 le_rfl ht1' hθ.1
  have hpn := one_lt_sq_mul_of_cutLo_le hm1 hmn.le ht1' hθ.1
  exact remDensity_nonneg (by linarith [hθ.1]) (by linarith) (by linarith)
    (cutGamma_pos_of_cutLo_le hm1 hmn ht1 hsd hθ.1)

/-- The `A`-integrand of one rung pair against `R_i(mθ)R_j(nθ)`, with weight `s` and derivative `s'`. -/
theorem abs_remA_le {gi gj : ℝ → ℝ} {c χi χj m n θ s s' : ℝ} (hc : 0 < c) (hn : 0 < n) (hθ : 0 ≤ θ)
    (hmθ : 1 < m * θ) (hnθ : 1 < n * θ) (hχi0 : 0 ≤ χi) (hχi : χi < c ^ 2) (hχj0 : 0 ≤ χj)
    (hχj : χj < c ^ 2) (hΓ : 0 < cutGamma m n θ) :
    |(s' * coefA c χi χj m n θ + s * coefA' c χi χj m n θ)
        * (psi c gi (m * θ) * (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c gj (n * θ) / n))|
      ≤ 1 / c * ((n ^ 2 * θ / √(n ^ 2 * θ ^ 2 - 1)) * (|s'| / cutGamma m n θ + |s|
          * (cutDeltaBound m n θ / cutGamma m n θ ^ 2 + 2 * n ^ 2 * θ / (cutGamma m n θ * (n ^ 2 * θ ^ 2 - 1)))))
        * (rungAmp c χi gi (m * θ) * rungAmp c χj gj (n * θ)) := by
  have hpm : 0 < m ^ 2 * θ ^ 2 - 1 := by rw [← mul_pow]; nlinarith
  have hpn : 0 < n ^ 2 * θ ^ 2 - 1 := by rw [← mul_pow]; nlinarith
  have hA := abs_coefA_le (χj := χj) hc hn hpm hpn hχi0 hχj.le hΓ
  have hA' := abs_coefA'_le hc hn hθ hpm hpn hχi0 hχi.le hχj0 hχj.le hΓ
  have hψ := abs_psi_le_rungAmp (g := gi) hmθ hc hχi
  have hu := abs_rungU_le_rungAmp (g := gj) hnθ hc hχj0 hχj
  rw [mul_pow] at hu
  have hRi : 0 ≤ rungAmp c χi gi (m * θ) := Real.sqrt_nonneg _
  have hRj : 0 ≤ rungAmp c χj gj (n * θ) := Real.sqrt_nonneg _
  have hB : 0 ≤ cutDeltaBound m n θ := by unfold cutDeltaBound; positivity
  generalize coefA c χi χj m n θ = A at hA ⊢
  generalize coefA' c χi χj m n θ = A' at hA' ⊢
  generalize psi c gi (m * θ) = ψ at hψ ⊢
  generalize Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c gj (n * θ) = u at hu ⊢
  generalize rungAmp c χi gi (m * θ) = Ri at hψ hRi ⊢
  generalize rungAmp c χj gj (n * θ) = Rj at hu hRj ⊢
  generalize cutDeltaBound m n θ = B at hA' hB ⊢
  generalize cutGamma m n θ = Γ at hA hA' hΓ ⊢
  generalize n ^ 2 * θ ^ 2 - 1 = p at hA hA' hu hpn ⊢
  have hsp : 0 < √p := Real.sqrt_pos.mpr hpn
  set Q := |s'| / Γ + |s| * (B / Γ ^ 2 + 2 * n ^ 2 * θ / (Γ * p)) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hα : |s' * A + s * A'| ≤ n ^ 2 / (c ^ 2 * p) * Q := by
    calc |s' * A + s * A'| ≤ |s'| * |A| + |s| * |A'| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ |s'| * (n ^ 2 / (c ^ 2 * Γ * p))
          + |s| * ((n ^ 2 * B / (Γ ^ 2 * p) + 2 * n ^ 4 * θ / (Γ * p ^ 2)) / c ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _)) (mul_le_mul_of_nonneg_left hA' (abs_nonneg _))
      _ = n ^ 2 / (c ^ 2 * p) * Q := by rw [hQ]; field_simp
  have hu' : |u / n| ≤ c * θ * √p * Rj := by
    rw [abs_div, abs_of_pos hn, div_le_iff₀ hn]
    calc |u| ≤ c * (n * θ) * √p * Rj := hu
      _ = c * θ * √p * Rj * n := by ring
  rw [abs_mul, abs_mul]
  calc |s' * A + s * A'| * (|ψ| * |u / n|)
      ≤ n ^ 2 / (c ^ 2 * p) * Q * (Ri * (c * θ * √p * Rj)) :=
        mul_le_mul hα (mul_le_mul hψ hu' (abs_nonneg _) hRi) (by positivity) (by positivity)
    _ = 1 / c * (n ^ 2 * θ / √p * Q) * (Ri * Rj) := by
        field_simp
        rw [Real.sq_sqrt hpn.le]
        ring

/-- The `B`-integrand of one rung pair against `R_i(mθ)R_j(nθ)`, the mirror of `abs_remA_le`. -/
theorem abs_remB_le {gi gj : ℝ → ℝ} {c χi χj m n θ s s' : ℝ} (hc : 0 < c) (hm : 0 < m) (hθ : 0 ≤ θ)
    (hmθ : 1 < m * θ) (hnθ : 1 < n * θ) (hχi0 : 0 ≤ χi) (hχi : χi < c ^ 2) (hχj0 : 0 ≤ χj)
    (hχj : χj < c ^ 2) (hΓ : 0 < cutGamma m n θ) :
    |(s' * coefB c χi χj m n θ + s * coefB' c χi χj m n θ)
        * (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c gi (m * θ) / m * psi c gj (n * θ))|
      ≤ 1 / c * ((m ^ 2 * θ / √(m ^ 2 * θ ^ 2 - 1)) * (|s'| / cutGamma m n θ + |s|
          * (cutDeltaBound m n θ / cutGamma m n θ ^ 2 + 2 * m ^ 2 * θ / (cutGamma m n θ * (m ^ 2 * θ ^ 2 - 1)))))
        * (rungAmp c χi gi (m * θ) * rungAmp c χj gj (n * θ)) := by
  have hpm : 0 < m ^ 2 * θ ^ 2 - 1 := by rw [← mul_pow]; nlinarith
  have hpn : 0 < n ^ 2 * θ ^ 2 - 1 := by rw [← mul_pow]; nlinarith
  have hA := abs_coefB_le (χj := χj) hc hm hpm hpn hχi0 hχj.le hΓ
  have hA' := abs_coefB'_le hc hm hθ hpm hpn hχi0 hχi.le hχj0 hχj.le hΓ
  have hψ := abs_psi_le_rungAmp (g := gj) hnθ hc hχj
  have hu := abs_rungU_le_rungAmp (g := gi) hmθ hc hχi0 hχi
  rw [mul_pow] at hu
  have hRi : 0 ≤ rungAmp c χi gi (m * θ) := Real.sqrt_nonneg _
  have hRj : 0 ≤ rungAmp c χj gj (n * θ) := Real.sqrt_nonneg _
  have hB : 0 ≤ cutDeltaBound m n θ := by unfold cutDeltaBound; positivity
  generalize coefB c χi χj m n θ = A at hA ⊢
  generalize coefB' c χi χj m n θ = A' at hA' ⊢
  generalize psi c gj (n * θ) = ψ at hψ ⊢
  generalize Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c gi (m * θ) = u at hu ⊢
  generalize rungAmp c χi gi (m * θ) = Ri at hu hRi ⊢
  generalize rungAmp c χj gj (n * θ) = Rj at hψ hRj ⊢
  generalize cutDeltaBound m n θ = B at hA' hB ⊢
  generalize cutGamma m n θ = Γ at hA hA' hΓ ⊢
  generalize m ^ 2 * θ ^ 2 - 1 = p at hA hA' hu hpm ⊢
  have hsp : 0 < √p := Real.sqrt_pos.mpr hpm
  set Q := |s'| / Γ + |s| * (B / Γ ^ 2 + 2 * m ^ 2 * θ / (Γ * p)) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hα : |s' * A + s * A'| ≤ m ^ 2 / (c ^ 2 * p) * Q := by
    calc |s' * A + s * A'| ≤ |s'| * |A| + |s| * |A'| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ |s'| * (m ^ 2 / (c ^ 2 * Γ * p))
          + |s| * ((m ^ 2 * B / (Γ ^ 2 * p) + 2 * m ^ 4 * θ / (Γ * p ^ 2)) / c ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _)) (mul_le_mul_of_nonneg_left hA' (abs_nonneg _))
      _ = m ^ 2 / (c ^ 2 * p) * Q := by rw [hQ]; field_simp
  have hu' : |u / m| ≤ c * θ * √p * Ri := by
    rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
    calc |u| ≤ c * (m * θ) * √p * Ri := hu
      _ = c * θ * √p * Ri * m := by ring
  rw [abs_mul, abs_mul]
  calc |s' * A + s * A'| * (|u / m| * |ψ|)
      ≤ m ^ 2 / (c ^ 2 * p) * Q * ((c * θ * √p * Ri) * Rj) :=
        mul_le_mul hα (mul_le_mul hu' hψ (abs_nonneg _) (by positivity)) (by positivity) (by positivity)
    _ = 1 / c * (m ^ 2 * θ / √p * Q) * (Ri * Rj) := by
        field_simp
        rw [Real.sq_sqrt hpm.le]
        ring

variable {ι : Type} [Fintype ι]

/-- One cut pair: `|Σᵢⱼ aᵢaⱼ R_ij| ≤ (6J/c)·∫_{lo}^{hi} ρ_mn·Σ aᵢ²∫₁^X ψᵢ²`. -/
theorem abs_sum_pairRem_le {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {ω ω₁ : ℝ → ℝ}
    {t₁ X : ℝ} {m n : ℕ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (ht₁ : 6 / 5 ≤ t₁) (hωd : ∀ θ ∈ Icc 1 X, HasDerivAt ω (ω₁ θ) θ) (hω₁ : ContinuousOn ω₁ (Icc 1 X))
    (hm : 1 ≤ m) (hmn : m < n) :
    |∑ i, ∑ j, a i * a j * pairRem c (χ i) (χ j) (g i) (g j) (fun θ => Real.log m - ω θ)
        (fun θ => -ω₁ θ) m n (cutLo t₁ m) (cutHi t₁ X m n)|
      ≤ 6 * (Fintype.card ι : ℝ) / c * (∫ θ in cutLo t₁ m..cutHi t₁ X m n, remDensity ω ω₁ m n θ)
        * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hsd : 4 < 3 * t₁ ^ 2 := by nlinarith
  have ht1 : (1 : ℝ) ≤ t₁ := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
  have hlo1 : 1 ≤ cutLo t₁ m := by unfold cutLo; split_ifs <;> linarith
  have hXn : X / n ≤ X := div_le_self hX0 (by exact_mod_cast (show 1 ≤ n by omega))
  set P := ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 with hP
  set K := 6 * (Fintype.card ι : ℝ) / c with hK
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i).le
  have hK0 : 0 ≤ K := by positivity
  rcases le_total (X / n) (cutLo t₁ m) with h | h
  · rw [show cutHi t₁ X m n = cutLo t₁ m from max_eq_left h]
    simp [pairRem]
  rw [show cutHi t₁ X m n = X / n from max_eq_right h]
  -- the cut range
  have hfacts : ∀ θ ∈ Icc (cutLo t₁ m) (X / n), θ ∈ Icc 1 X ∧ 0 < cutGamma m n θ ∧ 0 ≤ θ
      ∧ 1 < (m : ℝ) * θ ∧ 1 < (n : ℝ) * θ ∧ (m : ℝ) * θ ∈ Icc (6 / 5 : ℝ) X ∧ (n : ℝ) * θ ∈ Icc (6 / 5 : ℝ) X
      ∧ 0 < (m : ℝ) ^ 2 * θ ^ 2 - 1 ∧ 0 < (n : ℝ) ^ 2 * θ ^ 2 - 1 := by
    intro θ hθ
    have hθ1 : 1 ≤ θ := hlo1.trans hθ.1
    have hmθ : 6 / 5 ≤ (m : ℝ) * θ := by
      have h1 := hθ.1
      unfold cutLo at h1
      split_ifs at h1 with hm1
      · subst hm1; simp; linarith
      · have : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
        nlinarith
    have hmnθ : (m : ℝ) * θ ≤ n * θ := mul_le_mul_of_nonneg_right hmn' (by linarith)
    have hnθX : (n : ℝ) * θ ≤ X := by
      have := (le_div_iff₀ hnpos).1 hθ.2
      linarith
    refine ⟨⟨hθ1, hθ.2.trans hXn⟩, cutGamma_pos_of_cutLo_le hm hmn ht1 hsd hθ.1, by linarith,
      by linarith, by linarith, ⟨hmθ, by linarith⟩, ⟨by linarith, hnθX⟩, ?_, ?_⟩
    · rw [← mul_pow]; nlinarith
    · rw [← mul_pow]; nlinarith
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have huc : ∀ i, Continuous (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g i)) := fun i =>
    (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.2
  have hω₁c : ContinuousOn ω₁ (Icc (cutLo t₁ m) (X / n)) := hω₁.mono (Icc_subset_Icc hlo1 hXn)
  have hσc : ContinuousOn (fun θ => Real.log m - ω θ) (Icc (cutLo t₁ m) (X / n)) :=
    continuousOn_const.sub fun θ hθ => (hωd θ (hfacts θ hθ).1).continuousAt.continuousWithinAt
  have hδ : ∀ i j, ∀ θ ∈ Icc (cutLo t₁ m) (X / n), cutDelta m n θ (χ i / c ^ 2) (χ j / c ^ 2) ≠ 0 := by
    intro i j θ hθ
    obtain ⟨-, hΓ, -, -, -, -, -, hpm, hpn⟩ := hfacts θ hθ
    exact (lt_of_lt_of_le hΓ (cutGamma_le_cutDelta hpm hpn (div_nonneg (hχ0 i) (sq_nonneg c))
      ((div_le_one (by positivity)).2 (hχc j).le))).ne'
  set fA : ι → ι → ℝ → ℝ := fun i j θ =>
    (-ω₁ θ * coefA c (χ i) (χ j) m n θ + (Real.log m - ω θ) * coefA' c (χ i) (χ j) m n θ)
      * (psi c (g i) (m * θ) * (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g j) (n * θ) / n)) with hfA
  set fB : ι → ι → ℝ → ℝ := fun i j θ =>
    (-ω₁ θ * coefB c (χ i) (χ j) m n θ + (Real.log m - ω θ) * coefB' c (χ i) (χ j) m n θ)
      * (Cvs.Prolate.Gram.RungGramFloorAtInfinity.rungU c (g i) (m * θ) / m * psi c (g j) (n * θ)) with hfB
  have hAc : ∀ i j, ContinuousOn (fA i j) (Icc (cutLo t₁ m) (X / n)) := by
    intro i j
    have h1 : ContinuousOn (fun θ => coefA c (χ i) (χ j) m n θ) (Icc (cutLo t₁ m) (X / n)) :=
      fun θ hθ => by
        obtain ⟨-, -, -, -, -, -, -, hpm, hpn⟩ := hfacts θ hθ
        exact (hasDerivAt_coefA hc0.ne' hnpos.ne' hpm.ne' hpn.ne' (hδ i j θ hθ)).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (fun θ => coefA' c (χ i) (χ j) m n θ) (Icc (cutLo t₁ m) (X / n)) :=
      fun θ hθ => by
        obtain ⟨-, -, -, -, -, -, -, hpm, hpn⟩ := hfacts θ hθ
        exact (continuousAt_coefA' hc0.ne' hnpos.ne' hpm.ne' hpn.ne' (hδ i j θ hθ)).continuousWithinAt
    exact ((hω₁c.neg.mul h1).add (hσc.mul h2)).mul (((hψc i).comp (continuous_const.mul continuous_id)).mul
      (((huc j).comp (continuous_const.mul continuous_id)).div_const _)).continuousOn
  have hBc : ∀ i j, ContinuousOn (fB i j) (Icc (cutLo t₁ m) (X / n)) := by
    intro i j
    have h1 : ContinuousOn (fun θ => coefB c (χ i) (χ j) m n θ) (Icc (cutLo t₁ m) (X / n)) :=
      fun θ hθ => by
        obtain ⟨-, -, -, -, -, -, -, hpm, hpn⟩ := hfacts θ hθ
        exact (hasDerivAt_coefB hc0.ne' hmpos.ne' hpm.ne' hpn.ne' (hδ i j θ hθ)).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (fun θ => coefB' c (χ i) (χ j) m n θ) (Icc (cutLo t₁ m) (X / n)) :=
      fun θ hθ => by
        obtain ⟨-, -, -, -, -, -, -, hpm, hpn⟩ := hfacts θ hθ
        exact (continuousAt_coefB' hc0.ne' hmpos.ne' hpm.ne' hpn.ne' (hδ i j θ hθ)).continuousWithinAt
    exact ((hω₁c.neg.mul h1).add (hσc.mul h2)).mul
      ((((huc i).comp (continuous_const.mul continuous_id)).div_const _).mul
        ((hψc j).comp (continuous_const.mul continuous_id))).continuousOn
  have hsplit : ∑ i, ∑ j, a i * a j * pairRem c (χ i) (χ j) (g i) (g j) (fun θ => Real.log m - ω θ)
        (fun θ => -ω₁ θ) m n (cutLo t₁ m) (X / n)
      = ∫ θ in cutLo t₁ m..X / n, ∑ i, ∑ j, a i * a j * (-fA i j θ + fB i j θ) := by
    have hI : ∀ i j, IntervalIntegrable (fun θ => a i * a j * (-fA i j θ + fB i j θ)) MeasureTheory.volume
        (cutLo t₁ m) (X / n) := fun i j =>
      ContinuousOn.intervalIntegrable_of_Icc h (continuousOn_const.mul ((hAc i j).neg.add (hBc i j)))
    rw [intervalIntegral.integral_finsetSum (f := fun i θ => ∑ j, a i * a j * (-fA i j θ + fB i j θ))
      fun i _ => ContinuousOn.intervalIntegrable_of_Icc h
        (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hAc i j).neg.add (hBc i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum (f := fun j θ => a i * a j * (-fA i j θ + fB i j θ))
      fun j _ => hI i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (f := fun θ => -fA i j θ)
      (g := fun θ => fB i j θ) (ContinuousOn.intervalIntegrable_of_Icc h (hAc i j)).neg
      (ContinuousOn.intervalIntegrable_of_Icc h (hBc i j)), intervalIntegral.integral_neg]
    rfl
  rw [hsplit]
  have hRc : ContinuousOn (fun θ => remDensity ω ω₁ m n θ) (Icc (cutLo t₁ m) (X / n)) := by
    intro θ hθ
    obtain ⟨-, hΓ, -, -, -, -, -, hpm, hpn⟩ := hfacts θ hθ
    have hw : ContinuousWithinAt (fun θ => |Real.log m - ω θ|) (Icc (cutLo t₁ m) (X / n)) θ :=
      (hσc θ hθ).abs
    have hw₁ : ContinuousWithinAt (fun θ => |ω₁ θ|) (Icc (cutLo t₁ m) (X / n)) θ := (hω₁c θ hθ).abs
    have hpmc : ContinuousAt (fun θ => (m : ℝ) ^ 2 * θ ^ 2 - 1) θ := by fun_prop
    have hpnc : ContinuousAt (fun θ => (n : ℝ) ^ 2 * θ ^ 2 - 1) θ := by fun_prop
    have hΓc : ContinuousAt (fun θ => cutGamma m n θ) θ := by
      unfold cutGamma
      exact continuousAt_const.sub ((by fun_prop : ContinuousAt (fun t => (m : ℝ) ^ 4 * t ^ 2) θ).div hpmc hpm.ne')
    have hBc : ContinuousAt (fun θ => cutDeltaBound m n θ) θ := by
      unfold cutDeltaBound
      exact ((by fun_prop : ContinuousAt (fun t => 2 * (n : ℝ) ^ 4 * t) θ).div (hpnc.pow 2)
        (pow_ne_zero 2 hpn.ne')).add ((by fun_prop : ContinuousAt (fun t => 2 * (m : ℝ) ^ 4 * t) θ).div
        (hpmc.pow 2) (pow_ne_zero 2 hpm.ne'))
    have hQ : ∀ k : ℝ, 0 < k ^ 2 * θ ^ 2 - 1 → ContinuousAt (fun θ => k ^ 2 * θ ^ 2 - 1) θ →
        ContinuousWithinAt (fun θ => (k ^ 2 * θ / √(k ^ 2 * θ ^ 2 - 1)) * (|ω₁ θ| / cutGamma m n θ
          + |Real.log m - ω θ| * (cutDeltaBound m n θ / cutGamma m n θ ^ 2
            + 2 * k ^ 2 * θ / (cutGamma m n θ * (k ^ 2 * θ ^ 2 - 1))))) (Icc (cutLo t₁ m) (X / n)) θ := by
      intro k hk hkc
      exact (((by fun_prop : ContinuousAt (fun t => k ^ 2 * t) θ).div hkc.sqrt
        (Real.sqrt_ne_zero'.2 hk)).continuousWithinAt).mul ((hw₁.div hΓc.continuousWithinAt hΓ.ne').add
        (hw.mul (((hBc.div (hΓc.pow 2) (pow_ne_zero 2 hΓ.ne')).add
          ((by fun_prop : ContinuousAt (fun t => 2 * k ^ 2 * t) θ).div (hΓc.mul hkc)
            (mul_ne_zero hΓ.ne' hk.ne'))).continuousWithinAt)))
    unfold remDensity
    exact ((hQ n hpn hpnc).add (hQ m hpm hpmc)).div (hpmc.mul hpnc).sqrt.continuousWithinAt
      (Real.sqrt_ne_zero'.2 (mul_pos hpm hpn))
  have hpt : ∀ θ ∈ Icc (cutLo t₁ m) (X / n),
      |∑ i, ∑ j, a i * a j * (-fA i j θ + fB i j θ)| ≤ K * P * remDensity ω ω₁ m n θ := by
    intro θ hθ
    obtain ⟨-, hΓ, hθ0, hmθ, hnθ, hξ, hη, hpm, hpn⟩ := hfacts θ hθ
    have hR0 : ∀ i ζ, 0 ≤ rungAmp c (χ i) (g i) ζ := fun _ _ => Real.sqrt_nonneg _
    set DA := ((n : ℝ) ^ 2 * θ / √((n : ℝ) ^ 2 * θ ^ 2 - 1)) * (|ω₁ θ| / cutGamma m n θ
      + |Real.log m - ω θ| * (cutDeltaBound m n θ / cutGamma m n θ ^ 2
        + 2 * (n : ℝ) ^ 2 * θ / (cutGamma m n θ * ((n : ℝ) ^ 2 * θ ^ 2 - 1)))) with hDA
    set DB := ((m : ℝ) ^ 2 * θ / √((m : ℝ) ^ 2 * θ ^ 2 - 1)) * (|ω₁ θ| / cutGamma m n θ
      + |Real.log m - ω θ| * (cutDeltaBound m n θ / cutGamma m n θ ^ 2
        + 2 * (m : ℝ) ^ 2 * θ / (cutGamma m n θ * ((m : ℝ) ^ 2 * θ ^ 2 - 1)))) with hDB
    have hrem : remDensity ω ω₁ m n θ = (DA + DB) / √(((m : ℝ) ^ 2 * θ ^ 2 - 1) * ((n : ℝ) ^ 2 * θ ^ 2 - 1)) :=
      rfl
    have hsq : 0 < √(((m : ℝ) ^ 2 * θ ^ 2 - 1) * ((n : ℝ) ^ 2 * θ ^ 2 - 1)) :=
      Real.sqrt_pos.2 (mul_pos hpm hpn)
    have hD0 : 0 ≤ DA + DB := by
      have h0 := remDensity_nonneg (ω := ω) (ω₁ := ω₁) hθ0 hpm hpn hΓ
      rw [hrem] at h0
      exact (div_nonneg_iff.1 h0).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hsq)
    have hA : ∀ i j, |fA i j θ| ≤ 1 / c * DA * (rungAmp c (χ i) (g i) (m * θ) * rungAmp c (χ j) (g j) (n * θ)) :=
      fun i j => by
        have := abs_remA_le (gi := g i) (gj := g j) (s := Real.log m - ω θ) (s' := -ω₁ θ) hc0 hnpos hθ0 hmθ
          hnθ (hχ0 i) (hχc i) (hχ0 j) (hχc j) hΓ
        rwa [abs_neg] at this
    have hB : ∀ i j, |fB i j θ| ≤ 1 / c * DB * (rungAmp c (χ i) (g i) (m * θ) * rungAmp c (χ j) (g j) (n * θ)) :=
      fun i j => by
        have := abs_remB_le (gi := g i) (gj := g j) (s := Real.log m - ω θ) (s' := -ω₁ θ) hc0 hmpos hθ0 hmθ
          hnθ (hχ0 i) (hχc i) (hχ0 j) (hχc j) hΓ
        rwa [abs_neg] at this
    have htwo := two_point_le a hg hg₁ hg₂c hang hc hχ0 hχc hX hM hξ hη
    rw [mul_pow, mul_pow] at htwo
    calc |∑ i, ∑ j, a i * a j * (-fA i j θ + fB i j θ)|
        ≤ ∑ i, ∑ j, |a i * a j * (-fA i j θ + fB i j θ)| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, 1 / c * (DA + DB) * ((|a i| * rungAmp c (χ i) (g i) (m * θ))
            * (|a j| * rungAmp c (χ j) (g j) (n * θ))) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have hs := abs_add_le (-fA i j θ) (fB i j θ)
          rw [abs_neg] at hs
          rw [abs_mul, abs_mul]
          calc |a i| * |a j| * |-fA i j θ + fB i j θ|
              ≤ |a i| * |a j| * (1 / c * DA * (rungAmp c (χ i) (g i) (m * θ) * rungAmp c (χ j) (g j) (n * θ))
                + 1 / c * DB * (rungAmp c (χ i) (g i) (m * θ) * rungAmp c (χ j) (g j) (n * θ))) :=
                mul_le_mul_of_nonneg_left (hs.trans (add_le_add (hA i j) (hB i j))) (by positivity)
            _ = _ := by ring
      _ = 1 / c * (DA + DB) * ((∑ i, |a i| * rungAmp c (χ i) (g i) (m * θ))
            * (∑ j, |a j| * rungAmp c (χ j) (g j) (n * θ))) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ 1 / c * (DA + DB) * (6 * (Fintype.card ι : ℝ)
            / √(((m : ℝ) ^ 2 * θ ^ 2 - 1) * ((n : ℝ) ^ 2 * θ ^ 2 - 1)) * P) :=
          mul_le_mul_of_nonneg_left htwo (by positivity)
      _ = K * P * remDensity ω ω₁ m n θ := by
          rw [hrem, hK]; field_simp
  have hRint : IntervalIntegrable (fun θ => K * P * remDensity ω ω₁ m n θ) MeasureTheory.volume
      (cutLo t₁ m) (X / n) :=
    ContinuousOn.intervalIntegrable_of_Icc h (continuousOn_const.mul hRc)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le h
    (MeasureTheory.ae_of_all _ fun θ hθ => by rw [Real.norm_eq_abs]; exact hpt θ (Ioc_subset_Icc_self hθ)) hRint
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hnorm
  calc _ ≤ _ := hnorm
    _ = _ := by ring

/-- **The first-step remainder in count form**: `|R_X| ≤ (6J/c)κ(X) Σ aᵢ²∫₁^X ψᵢ²`. -/
theorem rem_le_count {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {ω ω₁ : ℝ → ℝ} {t₁ X : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 80 ≤ c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i < c ^ 2) (hX : 2 ≤ X)
    (hM : ∀ i, 0 < ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2)
    (ht₁ : 6 / 5 ≤ t₁) (hωd : ∀ θ ∈ Icc 1 X, HasDerivAt ω (ω₁ θ) θ) (hω₁ : ContinuousOn ω₁ (Icc 1 X)) :
    |cutR c χ g a ω ω₁ t₁ X|
      ≤ 6 * (Fintype.card ι : ℝ) / c * kapCount ω ω₁ t₁ X * ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 := by
  set P := ∑ i, a i ^ 2 * ∫ t in (1 : ℝ)..X, psi c (g i) t ^ 2 with hP
  set K := 6 * (Fintype.card ι : ℝ) / c with hK
  have key : ∀ m ∈ Finset.Icc 1 ⌊X⌋₊, ∀ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n),
      |∑ i, ∑ j, a i * a j * pairRem c (χ i) (χ j) (g i) (g j) (fun θ => Real.log m - ω θ)
        (fun θ => -ω₁ θ) m n (cutLo t₁ m) (cutHi t₁ X m n)|
        ≤ K * (∫ θ in cutLo t₁ m..cutHi t₁ X m n, remDensity ω ω₁ m n θ) * P := fun m hm n hn =>
    abs_sum_pairRem_le a hg hg₁ hg₂c hang hc hχ0 hχc hX hM ht₁ hωd hω₁ (Finset.mem_Icc.mp hm).1
      (Finset.mem_filter.mp hn).2
  clear_value P K
  unfold cutR kapCount
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have h := key m hm n hn
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc 2 * |∑ i, ∑ j, a i * a j * pairRem c (χ i) (χ j) (g i) (g j) (fun θ => Real.log m - ω θ)
        (fun θ => -ω₁ θ) m n (cutLo t₁ m) (cutHi t₁ X m n)|
      ≤ 2 * (K * (∫ θ in cutLo t₁ m..cutHi t₁ X m n, remDensity ω ω₁ m n θ) * P) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

end Cvs.L2a.FirstStepRemainderCount
