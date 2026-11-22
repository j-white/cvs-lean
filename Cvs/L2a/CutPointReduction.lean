import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.CutGap
import Cvs.L2a.CutWeightResidual
import Cvs.L2a.NonresonantCrossIntegral
import Cvs.L2a.NonstationaryCrossPairClosed
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SturmProductByParts

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cut-point reduction of `cutNS` (Theorem A)

On a rung span, `cutNS ω Φ X = B_X + R_X` exactly: one Cvs.Prolate.LiouvilleGreen.SturmProductByParts integration by parts per dilate pair `m < n` and rung pair
on `[lo_m, max(lo_m, X/n)]`, `lo_1 = t₁`, `lo_m = 1`, with `ω = 0` on `[1, t₁]` and `t₁` past `2/√3`. `B_X` is the cut-point
samples over `c²δ`; `R_X` the first-step integrals against `(σ·coefA)'` and `(σ·coefB)'`.
-/

namespace Cvs.L2a.CutPointReduction

open Real Set Finset intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.NonresonantCrossIntegral Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.L2a.CutWeightResidual Cvs.L2a.CutGap

/-- `A/σ = −1/(c²δ·pm n)`: `SturmProductByParts`'s first coefficient over the weight. -/
noncomputable def coefA (c χi χj m n θ : ℝ) : ℝ :=
  -1 / (c ^ 2 * cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * pm n θ)

/-- Its derivative `(δ'·pm n + δ·2θ)/(c²(δ·pm n)²)`. -/
noncomputable def coefA' (c χi χj m n θ : ℝ) : ℝ :=
  (cutDelta' m n θ (χi / c ^ 2) (χj / c ^ 2) * pm n θ + cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * (2 * θ))
    / (c ^ 2 * (cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * pm n θ) ^ 2)

/-- `B/σ = −1/(c²δ·pm m)`. -/
noncomputable def coefB (c χi χj m n θ : ℝ) : ℝ :=
  -1 / (c ^ 2 * cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * pm m θ)

/-- Its derivative `(δ'·pm m + δ·2θ)/(c²(δ·pm m)²)`. -/
noncomputable def coefB' (c χi χj m n θ : ℝ) : ℝ :=
  (cutDelta' m n θ (χi / c ^ 2) (χj / c ^ 2) * pm m θ + cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * (2 * θ))
    / (c ^ 2 * (cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * pm m θ) ^ 2)

/-- The cut sample of one rung pair, `(m u_i(mθ) ψ_j(nθ)/p(mθ) − n ψ_i(mθ) u_j(nθ)/p(nθ))/(c²δ)`. -/
noncomputable def pairBdry (c χi χj : ℝ) (gi gj : ℝ → ℝ) (m n θ : ℝ) : ℝ :=
  (m * rungU c gi (m * θ) * psi c gj (n * θ) / pP (m * θ)
      - n * psi c gi (m * θ) * rungU c gj (n * θ) / pP (n * θ))
    / (c ^ 2 * cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2))

/-- The first-step remainder of one rung pair on `[lo, hi]` for a weight `σ` with derivative `σ'`. -/
noncomputable def pairRem (c χi χj : ℝ) (gi gj σ σ' : ℝ → ℝ) (m n lo hi : ℝ) : ℝ :=
  -(∫ θ in lo..hi, (σ' θ * coefA c χi χj m n θ + σ θ * coefA' c χi χj m n θ)
      * (psi c gi (m * θ) * (rungU c gj (n * θ) / n)))
    + ∫ θ in lo..hi, (σ' θ * coefB c χi χj m n θ + σ θ * coefB' c χi χj m n θ)
      * (rungU c gi (m * θ) / m * psi c gj (n * θ))

variable {ι : Type} [Fintype ι]

/-- The cut-point term `(log m − ω θ) Σᵢⱼ aᵢaⱼ pairBdry`. -/
noncomputable def cutBdryAt (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (ω : ℝ → ℝ) (m n : ℕ)
    (θ : ℝ) : ℝ :=
  (Real.log m - ω θ) * ∑ i, ∑ j, a i * a j * pairBdry c (χ i) (χ j) (g i) (g j) m n θ

/-- `B_X`: the cut-point terms. -/
noncomputable def cutB (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (ω : ℝ → ℝ) (t₁ X : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n),
    2 * (cutBdryAt c χ g a ω m n (cutHi t₁ X m n) - cutBdryAt c χ g a ω m n (cutLo t₁ m))

/-- `R_X`: the first-step remainders. -/
noncomputable def cutR (c : ℝ) (χ : ι → ℝ) (g : ι → ℝ → ℝ) (a : ι → ℝ) (ω ω₁ : ℝ → ℝ) (t₁ X : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n),
    2 * ∑ i, ∑ j, a i * a j * pairRem c (χ i) (χ j) (g i) (g j) (fun θ => Real.log m - ω θ)
      (fun θ => -ω₁ θ) m n (cutLo t₁ m) (cutHi t₁ X m n)

theorem hasDerivAt_coefA {c χi χj m n θ : ℝ} (hc : c ≠ 0) (hn : n ≠ 0) (hpm : m ^ 2 * θ ^ 2 - 1 ≠ 0)
    (hpn : n ^ 2 * θ ^ 2 - 1 ≠ 0) (hδ : cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) ≠ 0) :
    HasDerivAt (fun t => coefA c χi χj m n t) (coefA' c χi χj m n θ) θ := by
  have hP : pm n θ ≠ 0 := by unfold pm; exact div_ne_zero hpn (pow_ne_zero 2 hn)
  have hD := hasDerivAt_cutDelta (x := χi / c ^ 2) (x' := χj / c ^ 2) hpm hpn
  have hF : HasDerivAt (fun t => c ^ 2 * (cutDelta m n t (χi / c ^ 2) (χj / c ^ 2) * pm n t))
      (c ^ 2 * (cutDelta' m n θ (χi / c ^ 2) (χj / c ^ 2) * pm n θ
        + cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * (2 * θ))) θ :=
    (hD.fun_mul (hasDerivAt_pm hn θ)).const_mul (c ^ 2)
  have hF0 : c ^ 2 * (cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * pm n θ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hc) (mul_ne_zero hδ hP)
  have h := (hasDerivAt_const θ (-1 : ℝ)).fun_div hF hF0
  have e : (fun t => coefA c χi χj m n t)
      = fun t => (-1 : ℝ) / (c ^ 2 * (cutDelta m n t (χi / c ^ 2) (χj / c ^ 2) * pm n t)) := by
    funext t; unfold coefA; rw [mul_assoc]
  rw [e]
  refine h.congr_deriv ?_
  unfold coefA'
  field_simp
  ring

theorem hasDerivAt_coefB {c χi χj m n θ : ℝ} (hc : c ≠ 0) (hm : m ≠ 0) (hpm : m ^ 2 * θ ^ 2 - 1 ≠ 0)
    (hpn : n ^ 2 * θ ^ 2 - 1 ≠ 0) (hδ : cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) ≠ 0) :
    HasDerivAt (fun t => coefB c χi χj m n t) (coefB' c χi χj m n θ) θ := by
  have hP : pm m θ ≠ 0 := by unfold pm; exact div_ne_zero hpm (pow_ne_zero 2 hm)
  have hD := hasDerivAt_cutDelta (x := χi / c ^ 2) (x' := χj / c ^ 2) hpm hpn
  have hF : HasDerivAt (fun t => c ^ 2 * (cutDelta m n t (χi / c ^ 2) (χj / c ^ 2) * pm m t))
      (c ^ 2 * (cutDelta' m n θ (χi / c ^ 2) (χj / c ^ 2) * pm m θ
        + cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * (2 * θ))) θ :=
    (hD.fun_mul (hasDerivAt_pm hm θ)).const_mul (c ^ 2)
  have hF0 : c ^ 2 * (cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) * pm m θ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hc) (mul_ne_zero hδ hP)
  have h := (hasDerivAt_const θ (-1 : ℝ)).fun_div hF hF0
  have e : (fun t => coefB c χi χj m n t)
      = fun t => (-1 : ℝ) / (c ^ 2 * (cutDelta m n t (χi / c ^ 2) (χj / c ^ 2) * pm m t)) := by
    funext t; unfold coefB; rw [mul_assoc]
  rw [e]
  refine h.congr_deriv ?_
  unfold coefB'
  field_simp
  ring

theorem continuousAt_cutDelta' {m n θ x x' : ℝ} (hpm : m ^ 2 * θ ^ 2 - 1 ≠ 0) (hpn : n ^ 2 * θ ^ 2 - 1 ≠ 0) :
    ContinuousAt (fun t => cutDelta' m n t x x') θ := by
  unfold cutDelta'
  have dm : ContinuousAt (fun t => (m ^ 2 * t ^ 2 - 1) ^ 2) θ := by fun_prop
  have dn : ContinuousAt (fun t => (n ^ 2 * t ^ 2 - 1) ^ 2) θ := by fun_prop
  exact ((by fun_prop : ContinuousAt (fun t => 2 * m ^ 4 * t * (1 - x)) θ).div dm
    (pow_ne_zero 2 hpm)).sub ((by fun_prop : ContinuousAt (fun t => 2 * n ^ 4 * t * (1 - x')) θ).div
    dn (pow_ne_zero 2 hpn))

theorem continuousAt_coefA' {c χi χj m n θ : ℝ} (hc : c ≠ 0) (hn : n ≠ 0) (hpm : m ^ 2 * θ ^ 2 - 1 ≠ 0)
    (hpn : n ^ 2 * θ ^ 2 - 1 ≠ 0) (hδ : cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) ≠ 0) :
    ContinuousAt (fun t => coefA' c χi χj m n t) θ := by
  have hP : pm n θ ≠ 0 := by unfold pm; exact div_ne_zero hpn (pow_ne_zero 2 hn)
  have hD := (hasDerivAt_cutDelta (x := χi / c ^ 2) (x' := χj / c ^ 2) hpm hpn).continuousAt
  have hD' := continuousAt_cutDelta' (x := χi / c ^ 2) (x' := χj / c ^ 2) hpm hpn
  have hp : ContinuousAt (pm n) θ := (hasDerivAt_pm hn θ).continuousAt
  unfold coefA'
  exact ((hD'.mul hp).add (hD.mul (continuousAt_const.mul continuousAt_id))).div
    (continuousAt_const.mul ((hD.mul hp).pow 2)) (mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 (mul_ne_zero hδ hP)))

theorem continuousAt_coefB' {c χi χj m n θ : ℝ} (hc : c ≠ 0) (hm : m ≠ 0) (hpm : m ^ 2 * θ ^ 2 - 1 ≠ 0)
    (hpn : n ^ 2 * θ ^ 2 - 1 ≠ 0) (hδ : cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) ≠ 0) :
    ContinuousAt (fun t => coefB' c χi χj m n t) θ := by
  have hP : pm m θ ≠ 0 := by unfold pm; exact div_ne_zero hpm (pow_ne_zero 2 hm)
  have hD := (hasDerivAt_cutDelta (x := χi / c ^ 2) (x' := χj / c ^ 2) hpm hpn).continuousAt
  have hD' := continuousAt_cutDelta' (x := χi / c ^ 2) (x' := χj / c ^ 2) hpm hpn
  have hp : ContinuousAt (pm m) θ := (hasDerivAt_pm hm θ).continuousAt
  unfold coefB'
  exact ((hD'.mul hp).add (hD.mul (continuousAt_const.mul continuousAt_id))).div
    (continuousAt_const.mul ((hD.mul hp).pow 2)) (mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 (mul_ne_zero hδ hP)))

theorem pair_integral_eq {gi gi₁ gi₂ gj gj₁ gj₂ σ σ' : ℝ → ℝ} {c χi χj m n lo hi : ℝ}
    (hgi : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi (gi₁ s) s)
    (hgi₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gi₁ (gi₂ s) s) (hgi₂c : ContinuousOn gi₂ (uIcc (-1) 1))
    (hangi : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gi₂ s - 2 * s * gi₁ s - c ^ 2 * s ^ 2 * gi s + χi * gi s = 0)
    (hgj : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj (gj₁ s) s)
    (hgj₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt gj₁ (gj₂ s) s) (hgj₂c : ContinuousOn gj₂ (uIcc (-1) 1))
    (hangj : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * gj₂ s - 2 * s * gj₁ s - c ^ 2 * s ^ 2 * gj s + χj * gj s = 0)
    (hc : 0 < c) (hχi : 0 ≤ χi) (hχj : χj ≤ c ^ 2) (hm : 0 < m) (hmn : m ≤ n) (hlohi : lo ≤ hi)
    (hlo : 1 < m * lo) (hΓ : ∀ θ ∈ Icc lo hi, 0 < cutGamma m n θ)
    (hσ : ∀ θ ∈ Icc lo hi, HasDerivAt σ (σ' θ) θ) (hσ' : ContinuousOn σ' (Icc lo hi)) :
    ∫ θ in lo..hi, σ θ * (psi c gi (m * θ) * psi c gj (n * θ))
      = σ hi * pairBdry c χi χj gi gj m n hi - σ lo * pairBdry c χi χj gi gj m n lo
        + pairRem c χi χj gi gj σ σ' m n lo hi := by
  have hc0 : c ≠ 0 := hc.ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := (lt_of_lt_of_le hm hmn).ne'
  have hlo0 : 0 < lo := by
    by_contra h; have := not_lt.mp h; nlinarith
  have hmθ : ∀ θ ∈ Icc lo hi, 1 < m * θ := fun θ hθ =>
    lt_of_lt_of_le hlo (mul_le_mul_of_nonneg_left hθ.1 hm.le)
  have hnθ : ∀ θ ∈ Icc lo hi, 1 < n * θ := fun θ hθ =>
    lt_of_lt_of_le (hmθ θ hθ) (mul_le_mul_of_nonneg_right hmn (by linarith [hθ.1]))
  have hpos : ∀ θ ∈ Icc lo hi, 0 < m ^ 2 * θ ^ 2 - 1 ∧ 0 < n ^ 2 * θ ^ 2 - 1 := by
    intro θ hθ
    have h1 := hmθ θ hθ
    have h2 := hnθ θ hθ
    constructor <;> nlinarith
  have hδ : ∀ θ ∈ Icc lo hi, 0 < cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) := fun θ hθ =>
    lt_of_lt_of_le (hΓ θ hθ) (cutGamma_le_cutDelta (hpos θ hθ).1 (hpos θ hθ).2
      (div_nonneg hχi (sq_nonneg c)) ((div_le_one (by positivity)).2 hχj))
  have hPm : ∀ θ ∈ Icc lo hi, pm m θ ≠ 0 := fun θ hθ => by
    unfold pm; exact div_ne_zero (hpos θ hθ).1.ne' (pow_ne_zero 2 hm0)
  have hPn : ∀ θ ∈ Icc lo hi, pm n θ ≠ 0 := fun θ hθ => by
    unfold pm; exact div_ne_zero (hpos θ hθ).2.ne' (pow_ne_zero 2 hn0)
  obtain ⟨hψi, hui, hψic, -⟩ := rung_system hgi hgi₁ hgi₂c hangi
  obtain ⟨hψj, huj, hψjc, -⟩ := rung_system hgj hgj₁ hgj₂c hangj
  have hσc : ContinuousOn σ (Icc lo hi) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
  have hAeq : ∀ θ, m ^ 2 * θ ^ 2 - 1 ≠ 0 → n ^ 2 * θ ^ 2 - 1 ≠ 0 →
      σ θ * pm m θ / (pm n θ * qm c χi m θ - pm m θ * qm c χj n θ) = σ θ * coefA c χi χj m n θ := by
    intro θ h1 h2
    rw [show pm n θ * qm c χi m θ - pm m θ * qm c χj n θ = crossD c χi χj m n θ from rfl,
      crossD_eq hc0 hm0 hn0 h1 h2]
    have h1' : pm m θ ≠ 0 := by unfold pm; exact div_ne_zero h1 (pow_ne_zero 2 hm0)
    have h2' : pm n θ ≠ 0 := by unfold pm; exact div_ne_zero h2 (pow_ne_zero 2 hn0)
    unfold coefA
    by_cases hd : cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) = 0
    · simp [hd]
    · field_simp
  have hBeq : ∀ θ, m ^ 2 * θ ^ 2 - 1 ≠ 0 → n ^ 2 * θ ^ 2 - 1 ≠ 0 →
      σ θ * pm n θ / (pm n θ * qm c χi m θ - pm m θ * qm c χj n θ) = σ θ * coefB c χi χj m n θ := by
    intro θ h1 h2
    rw [show pm n θ * qm c χi m θ - pm m θ * qm c χj n θ = crossD c χi χj m n θ from rfl,
      crossD_eq hc0 hm0 hn0 h1 h2]
    have h1' : pm m θ ≠ 0 := by unfold pm; exact div_ne_zero h1 (pow_ne_zero 2 hm0)
    have h2' : pm n θ ≠ 0 := by unfold pm; exact div_ne_zero h2 (pow_ne_zero 2 hn0)
    unfold coefB
    by_cases hd : cutDelta m n θ (χi / c ^ 2) (χj / c ^ 2) = 0
    · simp [hd]
    · field_simp
  have hev : ∀ θ ∈ Icc lo hi, ∀ᶠ t in nhds θ, m ^ 2 * t ^ 2 - 1 ≠ 0 ∧ n ^ 2 * t ^ 2 - 1 ≠ 0 := by
    intro θ hθ
    have c1 : ContinuousAt (fun t => m ^ 2 * t ^ 2 - 1) θ := by fun_prop
    have c2 : ContinuousAt (fun t => n ^ 2 * t ^ 2 - 1) θ := by fun_prop
    exact (c1.eventually_ne (hpos θ hθ).1.ne').and (c2.eventually_ne (hpos θ hθ).2.ne')
  have hA : ∀ θ ∈ Icc lo hi, HasDerivAt (fun r => σ r * pm m r / (pm n r * qm c χi m r - pm m r * qm c χj n r))
      (σ' θ * coefA c χi χj m n θ + σ θ * coefA' c χi χj m n θ) θ := by
    intro θ hθ
    refine ((hσ θ hθ).mul (hasDerivAt_coefA hc0 hn0 (hpos θ hθ).1.ne' (hpos θ hθ).2.ne'
      (hδ θ hθ).ne')).congr_of_eventuallyEq ?_
    filter_upwards [hev θ hθ] with t ht
    exact hAeq t ht.1 ht.2
  have hB : ∀ θ ∈ Icc lo hi, HasDerivAt (fun r => σ r * pm n r / (pm n r * qm c χi m r - pm m r * qm c χj n r))
      (σ' θ * coefB c χi χj m n θ + σ θ * coefB' c χi χj m n θ) θ := by
    intro θ hθ
    refine ((hσ θ hθ).mul (hasDerivAt_coefB hc0 hm0 (hpos θ hθ).1.ne' (hpos θ hθ).2.ne'
      (hδ θ hθ).ne')).congr_of_eventuallyEq ?_
    filter_upwards [hev θ hθ] with t ht
    exact hBeq t ht.1 ht.2
  have hαc : ContinuousOn (fun θ => σ' θ * coefA c χi χj m n θ + σ θ * coefA' c χi χj m n θ) (Icc lo hi) := by
    refine (hσ'.mul fun θ hθ => ?_).add (hσc.mul fun θ hθ => ?_)
    · exact (hasDerivAt_coefA hc0 hn0 (hpos θ hθ).1.ne' (hpos θ hθ).2.ne'
        (hδ θ hθ).ne').continuousAt.continuousWithinAt
    · exact (continuousAt_coefA' hc0 hn0 (hpos θ hθ).1.ne' (hpos θ hθ).2.ne'
        (hδ θ hθ).ne').continuousWithinAt
  have hβc : ContinuousOn (fun θ => σ' θ * coefB c χi χj m n θ + σ θ * coefB' c χi χj m n θ) (Icc lo hi) := by
    refine (hσ'.mul fun θ hθ => ?_).add (hσc.mul fun θ hθ => ?_)
    · exact (hasDerivAt_coefB hc0 hm0 (hpos θ hθ).1.ne' (hpos θ hθ).2.ne'
        (hδ θ hθ).ne').continuousAt.continuousWithinAt
    · exact (continuousAt_coefB' hc0 hm0 (hpos θ hθ).1.ne' (hpos θ hθ).2.ne'
        (hδ θ hθ).ne').continuousWithinAt
  have hcont : ContinuousOn (fun r => σ r * (psi c gi (m * r) * psi c gj (n * r))) (Icc lo hi) :=
    hσc.mul ((hψic.comp (continuous_const.mul continuous_id)).mul
      (hψjc.comp (continuous_const.mul continuous_id))).continuousOn
  have hf₁ : ∀ θ ∈ Icc lo hi, HasDerivAt (fun s => psi c gi (m * s)) ((rungU c gi (m * θ) / m) / pm m θ) θ :=
    fun θ hθ => (Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm (hψi _ (hmθ θ hθ)) (hui (m * θ))).1
  have hu₁ : ∀ θ ∈ Icc lo hi, HasDerivAt (fun s => rungU c gi (m * s) / m)
      (-(qm c χi m θ * psi c gi (m * θ))) θ :=
    fun θ hθ => (Cvs.L2a.NonstationaryCrossPairClosed.scale_system hm (hψi _ (hmθ θ hθ)) (hui (m * θ))).2
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hf₂ : ∀ θ ∈ Icc lo hi, HasDerivAt (fun s => psi c gj (n * s)) ((rungU c gj (n * θ) / n) / pm n θ) θ :=
    fun θ hθ => (Cvs.L2a.NonstationaryCrossPairClosed.scale_system hn (hψj _ (hnθ θ hθ)) (huj (n * θ))).1
  have hu₂ : ∀ θ ∈ Icc lo hi, HasDerivAt (fun s => rungU c gj (n * s) / n)
      (-(qm c χj n θ * psi c gj (n * θ))) θ :=
    fun θ hθ => (Cvs.L2a.NonstationaryCrossPairClosed.scale_system hn (hψj _ (hnθ θ hθ)) (huj (n * θ))).2
  have hD : ∀ θ ∈ Icc lo hi, pm n θ * qm c χi m θ - pm m θ * qm c χj n θ ≠ 0 := by
    intro θ hθ
    rw [show pm n θ * qm c χi m θ - pm m θ * qm c χj n θ = crossD c χi χj m n θ from rfl,
      crossD_eq hc0 hm0 hn0 (hpos θ hθ).1.ne' (hpos θ hθ).2.ne']
    exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc0) (hδ θ hθ).ne')
      (mul_ne_zero (hPm θ hθ) (hPn θ hθ)))
  have hqc : ∀ (χ k : ℝ), ContinuousOn (qm c χ k) (Icc lo hi) := fun χ k => by
    unfold qm; fun_prop
  have hpc : ∀ k : ℝ, ContinuousOn (pm k) (Icc lo hi) := fun k => by
    unfold pm; fun_prop
  have key := Cvs.Prolate.LiouvilleGreen.SturmProductByParts.integral_cross (σ := σ) (p₁ := pm m) (q₁ := qm c χi m)
    (f₁ := fun θ => psi c gi (m * θ)) (u₁ := fun θ => rungU c gi (m * θ) / m) (p₂ := pm n)
    (q₂ := qm c χj n) (f₂ := fun θ => psi c gj (n * θ)) (u₂ := fun θ => rungU c gj (n * θ) / n)
    hlohi hPm hPn hD hf₁ hu₁ hf₂ hu₂ hA hB hαc hβc hcont (hqc _ _) (hqc _ _) (hpc _) (hpc _)
  have hbd : ∀ θ ∈ Icc lo hi,
      σ θ * pm m θ / (pm n θ * qm c χi m θ - pm m θ * qm c χj n θ)
          * (psi c gi (m * θ) * (rungU c gj (n * θ) / n))
        - σ θ * pm n θ / (pm n θ * qm c χi m θ - pm m θ * qm c χj n θ)
          * (rungU c gi (m * θ) / m * psi c gj (n * θ))
        = σ θ * pairBdry c χi χj gi gj m n θ := by
    intro θ hθ
    rw [show pm n θ * qm c χi m θ - pm m θ * qm c χj n θ = crossD c χi χj m n θ from rfl,
      crossD_eq hc0 hm0 hn0 (hpos θ hθ).1.ne' (hpos θ hθ).2.ne']
    have e1 : pP (m * θ) = m ^ 2 * pm m θ := by unfold pP pm; field_simp
    have e2 : pP (n * θ) = n ^ 2 * pm n θ := by unfold pP pm; field_simp
    unfold pairBdry
    rw [e1, e2]
    have := hPm θ hθ
    have := hPn θ hθ
    have := (hδ θ hθ).ne'
    field_simp
    ring
  rw [key, hbd hi ⟨hlohi, le_rfl⟩, hbd lo ⟨le_rfl, hlohi⟩]
  unfold pairRem
  ring

/-- One rung span: `∫_lo^hi σ Φ(m·)Φ(n·)` is the cut samples plus the first-step remainders, summed over rung pairs. -/
theorem span_integral_eq {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ) {σ σ' : ℝ → ℝ}
    {m n lo hi : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2) (hm : 0 < m) (hmn : m ≤ n)
    (hlohi : lo ≤ hi) (hlo : 1 < m * lo) (hΓ : ∀ θ ∈ Icc lo hi, 0 < cutGamma m n θ)
    (hσ : ∀ θ ∈ Icc lo hi, HasDerivAt σ (σ' θ) θ) (hσ' : ContinuousOn σ' (Icc lo hi)) :
    ∫ θ in lo..hi, σ θ * ((∑ i, a i * psi c (g i) (m * θ)) * ∑ i, a i * psi c (g i) (n * θ))
      = σ hi * ∑ i, ∑ j, a i * a j * pairBdry c (χ i) (χ j) (g i) (g j) m n hi
        - σ lo * ∑ i, ∑ j, a i * a j * pairBdry c (χ i) (χ j) (g i) (g j) m n lo
        + ∑ i, ∑ j, a i * a j * pairRem c (χ i) (χ j) (g i) (g j) σ σ' m n lo hi := by
  have hσc : ContinuousOn σ (Icc lo hi) := fun θ hθ => (hσ θ hθ).continuousAt.continuousWithinAt
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hcont : ∀ i j, ContinuousOn
      (fun θ => a i * a j * (σ θ * (psi c (g i) (m * θ) * psi c (g j) (n * θ)))) (uIcc lo hi) := by
    intro i j
    rw [uIcc_of_le hlohi]
    exact continuousOn_const.mul (hσc.mul ((((hψc i).comp (continuous_const.mul continuous_id)).mul
      ((hψc j).comp (continuous_const.mul continuous_id))).continuousOn))
  have e : (fun θ => σ θ * ((∑ i, a i * psi c (g i) (m * θ)) * ∑ i, a i * psi c (g i) (n * θ)))
      = fun θ => ∑ i, ∑ j, a i * a j * (σ θ * (psi c (g i) (m * θ) * psi c (g j) (n * θ))) := by
    funext θ
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hrow : ∀ i, ∫ θ in lo..hi, ∑ j, a i * a j * (σ θ * (psi c (g i) (m * θ) * psi c (g j) (n * θ)))
      = ∑ j, a i * a j * (σ hi * pairBdry c (χ i) (χ j) (g i) (g j) m n hi
          - σ lo * pairBdry c (χ i) (χ j) (g i) (g j) m n lo
          + pairRem c (χ i) (χ j) (g i) (g j) σ σ' m n lo hi) := by
    intro i
    rw [intervalIntegral.integral_finsetSum fun j _ => (hcont i j).intervalIntegrable]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, pair_integral_eq (hg i) (hg₁ i) (hg₂c i) (hang i) (hg j)
      (hg₁ j) (hg₂c j) (hang j) hc (hχ0 i) (hχc j) hm hmn hlohi hlo hΓ hσ hσ']
  rw [e, intervalIntegral.integral_finsetSum fun i _ =>
    (continuousOn_finsetSum _ fun j _ => hcont i j).intervalIntegrable,
    Finset.sum_congr rfl fun i _ => hrow i]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) rfl <;>
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cutNS_eq_sum_lt (ω Φ : ℝ → ℝ) (X : ℝ) :
    cutNS ω Φ X = ∑ m ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => m < n),
      2 * ∫ θ in (1 : ℝ)..(X / n), (Real.log m - ω θ) * (Φ (m * θ) * Φ (n * θ)) := by
  set S := Finset.Icc 1 ⌊X⌋₊ with hS
  set F : ℕ → ℕ → ℝ := fun m n =>
    ∫ θ in (1 : ℝ)..(X / n), (Real.log m - ω θ) * (Φ (m * θ) * Φ (n * θ)) with hF
  have hterm : ∀ a ∈ S, ∀ n ∈ S.erase a,
      (∫ θ in (1 : ℝ)..(X / (max a n : ℕ)), (Real.log (min a n : ℕ) - ω θ) * (Φ (a * θ) * Φ (n * θ)))
        = (if a < n then F a n else 0) + (if n < a then F n a else 0) := by
    intro a _ n hn
    have hne : n ≠ a := (Finset.mem_erase.mp hn).1
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add, max_eq_left h.le, min_eq_right h.le]
      exact intervalIntegral.integral_congr fun θ _ => by ring
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero, max_eq_right h.le, min_eq_left h.le]
  have e1 : cutNS ω Φ X = ∑ a ∈ S, ∑ n ∈ S, ((if a < n then F a n else 0) + (if n < a then F n a else 0)) := by
    unfold cutNS
    rw [← hS]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_congr rfl (hterm a ha)]
    rw [← Finset.add_sum_erase S _ ha]
    simp
  have e2 : ∑ a ∈ S, ∑ n ∈ S, (if n < a then F n a else 0) = ∑ a ∈ S, ∑ n ∈ S, (if a < n then F a n else 0) :=
    Finset.sum_comm
  rw [e1]
  simp only [Finset.sum_add_distrib, e2]
  rw [← two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp [hF]

/-- **Theorem A**: on a rung span, `cutNS = B_X + R_X` exactly, for any `C¹` weight vanishing on `[1, t₁]`,
`t₁ > 2/√3`. -/
theorem cutNS_eq_bdry_add_rem {g g₁ g₂ : ι → ℝ → ℝ} {c : ℝ} {χ : ι → ℝ} (a : ι → ℝ)
    {ω ω₁ : ℝ → ℝ} {t₁ X : ℝ}
    (hg : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g i) (g₁ i s) s)
    (hg₁ : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt (g₁ i) (g₂ i s) s)
    (hg₂c : ∀ i, ContinuousOn (g₂ i) (uIcc (-1) 1))
    (hang : ∀ i, ∀ s ∈ uIcc (-1 : ℝ) 1,
      (1 - s ^ 2) * g₂ i s - 2 * s * g₁ i s - c ^ 2 * s ^ 2 * g i s + χ i * g i s = 0)
    (hc : 0 < c) (hχ0 : ∀ i, 0 ≤ χ i) (hχc : ∀ i, χ i ≤ c ^ 2)
    (ht₁ : 1 ≤ t₁) (hsd : 4 < 3 * t₁ ^ 2) (hω0 : ∀ θ ∈ Icc 1 t₁, ω θ = 0)
    (hωd : ∀ θ ∈ Icc 1 X, HasDerivAt ω (ω₁ θ) θ) (hω₁ : ContinuousOn ω₁ (Icc 1 X)) :
    cutNS ω (fun ξ => ∑ i, a i * psi c (g i) ξ) X = cutB c χ g a ω t₁ X + cutR c χ g a ω ω₁ t₁ X := by
  have ht₁' : 1 < t₁ := by nlinarith
  have hψc : ∀ i, Continuous (psi c (g i)) := fun i =>
    (rung_system (hg i) (hg₁ i) (hg₂c i) (hang i)).2.2.1
  have hΦc : Continuous (fun ξ => ∑ i, a i * psi c (g i) ξ) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i)
  rw [cutNS_eq_sum_lt]
  unfold cutB cutR
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hm1, -⟩ := Finset.mem_Icc.mp hm
  obtain ⟨hnI, hmn⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hnI
  have hX0 : 0 ≤ X := by
    by_contra h
    have := Nat.floor_eq_zero.mpr (by linarith : X < 1)
    omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn.le
  have hX : (n : ℝ) ≤ X := (Nat.cast_le.mpr hnX).trans (Nat.floor_le hX0)
  have h1n : 1 ≤ X / n := (one_le_div hnpos).2 hX
  have hXn : X / n ≤ X := div_le_self hX0 (by exact_mod_cast hn1)
  have hσc : ContinuousOn (fun θ => Real.log m - ω θ) (Icc 1 X) :=
    continuousOn_const.sub fun θ hθ => (hωd θ hθ).continuousAt.continuousWithinAt
  have hFc : ContinuousOn (fun θ => (Real.log m - ω θ)
      * ((fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) * (fun ξ => ∑ i, a i * psi c (g i) ξ) (n * θ)))
      (Icc 1 X) :=
    hσc.mul (((hΦc.comp (continuous_const.mul continuous_id)).mul
      (hΦc.comp (continuous_const.mul continuous_id))).continuousOn)
  have hlo1 : 1 ≤ cutLo t₁ m := by unfold cutLo; split_ifs <;> linarith
  have hmlo : 1 < (m : ℝ) * cutLo t₁ m := by
    unfold cutLo
    split_ifs with h
    · simp [h, ht₁']
    · have : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
      linarith
  have hzero : m = 1 → ∀ θ ∈ Icc 1 t₁, Real.log m - ω θ = 0 := fun h θ hθ => by
    simp [h, hω0 θ hθ]
  rcases le_total (X / n) (cutLo t₁ m) with h | h
  · have hhi : cutHi t₁ X m n = cutLo t₁ m := max_eq_left h
    have hL : ∫ θ in (1 : ℝ)..(X / n), (Real.log m - ω θ)
        * ((fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) * (fun ξ => ∑ i, a i * psi c (g i) ξ) (n * θ))
        = 0 := by
      by_cases hm1' : m = 1
      · have hlo : cutLo t₁ m = t₁ := if_pos hm1'
        rw [hlo] at h
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun θ hθ => ?_]
        · simp
        · rw [uIcc_of_le h1n] at hθ
          simp only
          rw [hzero hm1' θ ⟨hθ.1, hθ.2.trans h⟩, zero_mul]
      · have hlo : cutLo t₁ m = 1 := if_neg hm1'
        rw [hlo] at h
        rw [show X / n = 1 by linarith, intervalIntegral.integral_same]
    rw [hL, hhi]
    simp [pairRem]
  · have hhi : cutHi t₁ X m n = X / n := max_eq_right h
    have hred : ∫ θ in (1 : ℝ)..(X / n), (Real.log m - ω θ)
        * ((fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) * (fun ξ => ∑ i, a i * psi c (g i) ξ) (n * θ))
        = ∫ θ in (cutLo t₁ m)..(X / n), (Real.log m - ω θ)
          * ((fun ξ => ∑ i, a i * psi c (g i) ξ) (m * θ) * (fun ξ => ∑ i, a i * psi c (g i) ξ) (n * θ)) := by
      by_cases hm1' : m = 1
      · have hlo : cutLo t₁ m = t₁ := if_pos hm1'
        rw [hlo] at h ⊢
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := t₁)
          ((hFc.mono (by rw [uIcc_of_le ht₁]; exact Icc_subset_Icc le_rfl (h.trans hXn))).intervalIntegrable)
          ((hFc.mono (by rw [uIcc_of_le h]; exact Icc_subset_Icc ht₁ hXn)).intervalIntegrable)]
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (a := 1) (b := t₁) fun θ hθ => ?_]
        · simp
        · rw [uIcc_of_le ht₁] at hθ
          simp only
          rw [hzero hm1' θ hθ, zero_mul]
      · rw [show cutLo t₁ m = 1 from if_neg hm1']
    have hspan := span_integral_eq a (σ := fun θ => Real.log m - ω θ) (σ' := fun θ => -ω₁ θ)
      (m := m) (n := n) (lo := cutLo t₁ m) (hi := X / n) hg hg₁ hg₂c hang hc hχ0 hχc hmpos hmn' h hmlo
      (fun θ hθ => cutGamma_pos_of_cutLo_le hm1 hmn ht₁ hsd hθ.1)
      (fun θ hθ => by
        have := (hasDerivAt_const θ (Real.log m)).fun_sub (hωd θ ⟨hlo1.trans hθ.1, hθ.2.trans hXn⟩)
        simpa using this)
      ((hω₁.mono (Icc_subset_Icc hlo1 hXn)).neg)
    rw [hred, hhi]
    beta_reduce at hspan ⊢
    rw [hspan]
    unfold cutBdryAt
    ring

end Cvs.L2a.CutPointReduction
