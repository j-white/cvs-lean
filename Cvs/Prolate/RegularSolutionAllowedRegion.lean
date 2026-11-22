import Mathlib
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.RegularSolutionDepthBound
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RegularSolutionEnergyComparability
import Cvs.Prolate.RegularSolutionForbiddenRegion
import Cvs.Prolate.TopRungDepthBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The regular solution in the allowed region: `E/(pq)` increases and a short layer costs a factor `e`

With `E = U² + pqy²`, `p = 1 − t²`, `q = σ − c²t²`, `(E/pq)' = −(pq)'U²/(pq)² ≥ 0` on the allowed region, so
`y(t)² ≤ E(t₂)/(pq)(t₂)` for `t ≤ t₂` and `E(t) ≥ pq(t)y(0)²` at an even level; `S = y² + U²` has `|S'| ≤ (1/p + |q|)S`.
Together with Cvs.Prolate.RegularSolutionForbiddenRegion these bound `∫_0^1 y² ≤ 50(1 + c²)²y(θ)²` at the turning point `θ`.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory
open Cvs.Prolate.RegularSolutionEdge (regSol regU sqC hasDerivAt_regSol hasDerivAt_regU)

namespace Cvs.Prolate.RegularSolutionAllowedRegion
open Cvs.ZeroCounting

variable {c σ : ℝ}

/-- `pq = (1 − t²)(σ − c²t²)`. -/
def pq (c σ t : ℝ) : ℝ := (1 - t ^ 2) * (σ - c ^ 2 * t ^ 2)

theorem hasDerivAt_pq (c σ t : ℝ) :
    HasDerivAt (pq c σ) (-(2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_sub 1)
  have h2 : HasDerivAt (fun t : ℝ => σ - c ^ 2 * t ^ 2) (-(c ^ 2 * (2 * t))) t := by
    simpa using (((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_sub σ)
  exact (h1.mul h2).congr_deriv (by ring)

theorem energy_eq (t : ℝ) : Cvs.Prolate.RegularSolutionEnergyComparability.energy c σ t = regU (sqC c) σ t ^ 2 + pq c σ t * regSol (sqC c) σ t ^ 2 := rfl

/-- **The energy ratio increases** on the allowed region: for `0 ≤ t₁ ≤ t₂ < 1` with `c²t₂² < σ`,
`E(t₁)/pq(t₁) ≤ E(t₂)/pq(t₂)`. -/
theorem ratio_mono {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h1 : t₂ < 1) (hq : c ^ 2 * t₂ ^ 2 < σ) :
    Cvs.Prolate.RegularSolutionEnergyComparability.energy c σ t₁ / pq c σ t₁ ≤ Cvs.Prolate.RegularSolutionEnergyComparability.energy c σ t₂ / pq c σ t₂ := by
  have hpos : ∀ t ∈ Icc t₁ t₂, 0 < pq c σ t := fun t ht => by
    unfold pq
    have : c ^ 2 * t ^ 2 ≤ c ^ 2 * t₂ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h0.trans ht.1) ht.2 2) (sq_nonneg c)
    exact mul_pos (by nlinarith [ht.1, ht.2]) (by linarith)
  have hd : ∀ t ∈ Icc t₁ t₂, HasDerivAt (fun t => Cvs.Prolate.RegularSolutionEnergyComparability.energy c σ t / pq c σ t)
      (-(2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2)) * -(regU (sqC c) σ t ^ 2) / pq c σ t ^ 2) t := by
    intro t ht
    have hE := Cvs.Prolate.RegularSolutionEnergyComparability.hasDerivAt_energy (c := c) (σ := σ) (show -1 < t by linarith [h0.trans ht.1])
    refine (hE.div (hasDerivAt_pq c σ t) (hpos t ht).ne').congr_deriv ?_
    rw [energy_eq]
    have := (hpos t ht).ne'
    field_simp
    ring
  have hm := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv hd fun t ht => by
    have ht0 := h0.trans ht.1
    have : 0 ≤ σ + c ^ 2 - 2 * c ^ 2 * t ^ 2 := by
      have h2 : c ^ 2 * t ^ 2 ≤ c ^ 2 * t₂ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht.2 2) (sq_nonneg c)
      have h3 : c ^ 2 * t ^ 2 ≤ c ^ 2 := by
        have : t ^ 2 ≤ 1 := by nlinarith [ht.2]
        nlinarith [sq_nonneg c]
      linarith
    have : 0 ≤ -(2 * t * (σ + c ^ 2 - 2 * c ^ 2 * t ^ 2)) * -(regU (sqC c) σ t ^ 2) := by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht0) this
      nlinarith [sq_nonneg (regU (sqC c) σ t)]
    positivity
  exact hm ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12

/-- `y² ≤ E/pq` where `pq > 0`. -/
theorem sq_le_ratio {t : ℝ} (h : 0 < pq c σ t) : regSol (sqC c) σ t ^ 2 ≤ Cvs.Prolate.RegularSolutionEnergyComparability.energy c σ t / pq c σ t := by
  rw [le_div_iff₀ h, energy_eq]; nlinarith [sq_nonneg (regU (sqC c) σ t)]

/-- **The layer bound**: on `[t₂, θ] ⊆ [0, 1)` with `1/(1 − t²) + |σ − c²t²| ≤ L`,
`y(t)² + U(t)² ≤ (y(θ)² + U(θ)²)e^{L(θ − t)}`. -/
theorem layer_le {t₂ θ L : ℝ} (h0 : 0 ≤ t₂) (h1 : θ < 1)
    (hL : ∀ t ∈ Icc t₂ θ, 1 / (1 - t ^ 2) + |σ - c ^ 2 * t ^ 2| ≤ L) {t : ℝ} (ht : t ∈ Icc t₂ θ) :
    regSol (sqC c) σ t ^ 2 + regU (sqC c) σ t ^ 2 ≤
      (regSol (sqC c) σ θ ^ 2 + regU (sqC c) σ θ ^ 2) * Real.exp (L * (θ - t)) := by
  set S : ℝ → ℝ := fun t => regSol (sqC c) σ t ^ 2 + regU (sqC c) σ t ^ 2 with hS
  have hd : ∀ s ∈ Icc t₂ θ, HasDerivAt (fun s => S s * Real.exp (L * s))
      ((2 * regSol (sqC c) σ s * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s + 2 * regU (sqC c) σ s *
        (-((c ^ 2 * s ^ 2 - σ) * regSol (sqC c) σ s))) * Real.exp (L * s) + S s * (Real.exp (L * s) * L)) s := by
    intro s hs
    have hs1 : -1 < s := by linarith [h0.trans hs.1]
    have dS : HasDerivAt S (2 * regSol (sqC c) σ s * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s + 2 * regU (sqC c) σ s *
        (-((c ^ 2 * s ^ 2 - σ) * regSol (sqC c) σ s))) s := by
      have h1 := (hasDerivAt_regSol (sqC c) σ hs1).pow 2
      have h2 := (hasDerivAt_regU (sqC c) σ hs1).pow 2
      refine (h1.add h2).congr_deriv ?_
      rw [Cvs.Prolate.TopRungDepthBound.sqC_apply]; push_cast; ring
    have dE : HasDerivAt (fun s => Real.exp (L * s)) (Real.exp (L * s) * L) s := by
      simpa using ((hasDerivAt_id s).const_mul L).exp
    exact dS.mul dE
  have hm := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv hd fun s hs => by
    have hp : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2, h0.trans hs.1]
    have hpd := Cvs.Prolate.RegularSolutionEnergyComparability.p_mul_deriv (c := c) (σ := σ) (t := s) (by linarith [h0.trans hs.1])
    have hv : Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s = -regU (sqC c) σ s / (1 - s ^ 2) := by
      rw [eq_div_iff hp.ne', mul_comm]; exact hpd
    set y := regSol (sqC c) σ s
    set U := regU (sqC c) σ s
    have hLs := hL s hs
    have hkey : |2 * y * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s + 2 * U * (-((c ^ 2 * s ^ 2 - σ) * y))| ≤ L * (y ^ 2 + U ^ 2) := by
      rw [hv]
      have e : 2 * y * (-U / (1 - s ^ 2)) + 2 * U * (-((c ^ 2 * s ^ 2 - σ) * y)) =
          2 * y * U * (-(1 / (1 - s ^ 2)) + (σ - c ^ 2 * s ^ 2)) := by field_simp; ring
      rw [e, abs_mul]
      have h2 : |2 * y * U| ≤ y ^ 2 + U ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y - U), sq_nonneg (y + U)]
      have h3 : |-(1 / (1 - s ^ 2)) + (σ - c ^ 2 * s ^ 2)| ≤ L := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (1 - s ^ 2))]
        exact hLs
      calc |2 * y * U| * |-(1 / (1 - s ^ 2)) + (σ - c ^ 2 * s ^ 2)| ≤ (y ^ 2 + U ^ 2) * L :=
            mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hex := Real.exp_pos (L * s)
    have := neg_abs_le (2 * y * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s + 2 * U * (-((c ^ 2 * s ^ 2 - σ) * y)))
    have hS' : S s = y ^ 2 + U ^ 2 := rfl
    rw [hS']
    have hlow : -(L * (y ^ 2 + U ^ 2)) ≤
        2 * y * Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ s + 2 * U * (-((c ^ 2 * s ^ 2 - σ) * y)) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hlow hex.le]
  have := hm ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2
  simp only at this
  have e : Real.exp (L * (θ - t)) = Real.exp (L * θ) / Real.exp (L * t) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e, mul_div_assoc', le_div_iff₀ (Real.exp_pos _)]
  exact this

/-! ### The mass up to the turning point -/

theorem intervalIntegrable_sq (c σ : ℝ) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    IntervalIntegrable (fun t => regSol (sqC c) σ t ^ 2) volume α β :=
  (((Cvs.Prolate.RegularSolutionEdge.continuousOn_regSol (sqC c) σ).pow 2).mono fun t ht => by
    rw [uIcc_of_le hαβ] at ht; exact show (-1 : ℝ) < t by linarith [ht.1]).intervalIntegrable

/-- The layer below the turning point costs a factor `e`: for `c ≥ 4`, `σ = c²θ²`, `θ² ≤ ¾` and
`θ − t ≤ min(θ, 1/(2c))`, `y(t)² + U(t)² ≤ (y(θ)² + U(θ)²)e`. -/
theorem layer_le_exp_one {θ t : ℝ} (hc : 4 ≤ c) (hθ3 : θ ^ 2 ≤ 3 / 4) (hσ : σ = c ^ 2 * θ ^ 2)
    (ht0 : 0 ≤ θ - min θ (1 / (2 * c))) (ht : t ∈ Icc (θ - min θ (1 / (2 * c))) θ) :
    regSol (sqC c) σ t ^ 2 + regU (sqC c) σ t ^ 2 ≤
      (regSol (sqC c) σ θ ^ 2 + regU (sqC c) σ θ ^ 2) * Real.exp 1 := by
  have hc0 : 0 < c := by linarith
  have hθ1 : θ < 1 := by nlinarith
  set h := min θ (1 / (2 * c)) with hh
  have hhc : h ≤ 1 / (2 * c) := min_le_right _ _
  have hL : ∀ s ∈ Icc (θ - h) θ, 1 / (1 - s ^ 2) + |σ - c ^ 2 * s ^ 2| ≤ 4 + c := by
    intro s hs
    have hs0 : 0 ≤ s := ht0.trans hs.1
    have hp : 1 / 4 ≤ 1 - s ^ 2 := by nlinarith [hs.2]
    have h1 : 1 / (1 - s ^ 2) ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hss : s ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hs0 hs.2 2
    have h2 : |σ - c ^ 2 * s ^ 2| ≤ c := by
      have hnn : 0 ≤ σ - c ^ 2 * s ^ 2 := by
        rw [hσ]; have := mul_le_mul_of_nonneg_left hss (sq_nonneg c); linarith
      rw [abs_of_nonneg hnn, hσ]
      have hd : θ ^ 2 - s ^ 2 ≤ 2 * h := by nlinarith [hs.1, hs.2]
      have hch : c ^ 2 * (2 * h) ≤ c := by
        have := mul_le_mul_of_nonneg_left hhc (by positivity : (0 : ℝ) ≤ c ^ 2 * 2)
        have e : c ^ 2 * 2 * (1 / (2 * c)) = c := by field_simp
        linarith
      have := mul_le_mul_of_nonneg_left hd (sq_nonneg c)
      linarith
    linarith
  have h1 := layer_le (c := c) (σ := σ) ht0 hθ1 hL ht
  have hLh : (4 + c) * (θ - t) ≤ 1 := by
    have h2 : θ - t ≤ h := by linarith [ht.1]
    have h3 : (4 + c) * (θ - t) ≤ (4 + c) * (1 / (2 * c)) :=
      mul_le_mul_of_nonneg_left (h2.trans hhc) (by linarith)
    have e : (4 + c) * (1 / (2 * c)) ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hLh) (by positivity))

/-- Below the layer: for `0 < t₂ = θ − 1/(2c)`, every `t ∈ [0, t₂]` has `y(t)² ≤ 16(1 + c²)·S(θ)e`. -/
theorem below_layer_le {θ t : ℝ} (hc : 4 ≤ c) (hθ3 : θ ^ 2 ≤ 3 / 4) (hσ : σ = c ^ 2 * θ ^ 2)
    (h0 : 0 < θ - 1 / (2 * c)) (ht : t ∈ Icc 0 (θ - 1 / (2 * c))) :
    regSol (sqC c) σ t ^ 2 ≤ 16 * (1 + c ^ 2) *
      ((regSol (sqC c) σ θ ^ 2 + regU (sqC c) σ θ ^ 2) * Real.exp 1) := by
  have hc0 : 0 < c := by linarith
  have hpc : 0 < 1 / (2 * c) := by positivity
  have hθ0 : 0 ≤ θ := by linarith
  set t₂ := θ - 1 / (2 * c) with ht₂
  have hmin : min θ (1 / (2 * c)) = 1 / (2 * c) := min_eq_right (by linarith)
  have hS2 := layer_le_exp_one (c := c) (σ := σ) (t := t₂) hc hθ3 hσ (by rw [hmin]; linarith)
    (by rw [hmin]; exact ⟨le_rfl, by linarith⟩)
  set K := (regSol (sqC c) σ θ ^ 2 + regU (sqC c) σ θ ^ 2) * Real.exp 1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hq2 : c ^ 2 * t₂ ^ 2 < σ := by
    rw [hσ]
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ (by linarith) h0.le two_ne_zero) (by positivity)
  have hpq : 1 / 16 ≤ pq c σ t₂ := by
    unfold pq
    have hp : 1 / 4 ≤ 1 - t₂ ^ 2 := by nlinarith
    have hq : 1 / 4 ≤ σ - c ^ 2 * t₂ ^ 2 := by
      have e : σ - c ^ 2 * t₂ ^ 2 = c ^ 2 * (1 / (2 * c)) * (θ + t₂) := by rw [hσ, ht₂]; ring
      rw [e]
      have h1 : c ^ 2 * (1 / (2 * c)) * (1 / (2 * c)) ≤ c ^ 2 * (1 / (2 * c)) * (θ + t₂) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e2 : c ^ 2 * (1 / (2 * c)) * (1 / (2 * c)) = 1 / 4 := by field_simp; ring
      linarith
    have := mul_le_mul hp hq (by norm_num) (by linarith)
    linarith
  have hpq' : pq c σ t₂ ≤ c ^ 2 := by
    unfold pq
    have h1 : 0 ≤ σ - c ^ 2 * t₂ ^ 2 := by linarith
    have h2 : σ - c ^ 2 * t₂ ^ 2 ≤ c ^ 2 := by
      rw [hσ]; nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg t₂)]
    have h3 : 0 ≤ 1 - t₂ ^ 2 := by nlinarith
    have h4 : 1 - t₂ ^ 2 ≤ 1 := by nlinarith [sq_nonneg t₂]
    calc (1 - t₂ ^ 2) * (σ - c ^ 2 * t₂ ^ 2) ≤ 1 * c ^ 2 := mul_le_mul h4 h2 h1 (by norm_num)
      _ = c ^ 2 := one_mul _
  have hE : Cvs.Prolate.RegularSolutionEnergyComparability.energy c σ t₂ ≤ (1 + c ^ 2) * K := by
    rw [energy_eq]
    have hpq0 : 0 ≤ pq c σ t₂ := by linarith
    have a1 : pq c σ t₂ * regSol (sqC c) σ t₂ ^ 2 ≤ c ^ 2 * regSol (sqC c) σ t₂ ^ 2 :=
      mul_le_mul_of_nonneg_right hpq' (sq_nonneg _)
    have a2 : c ^ 2 * regSol (sqC c) σ t₂ ^ 2 ≤ c ^ 2 * K :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (regU (sqC c) σ t₂)]) (sq_nonneg c)
    nlinarith [sq_nonneg (regSol (sqC c) σ t₂)]
  have hpqt : 0 < pq c σ t := by
    unfold pq
    have h1 : t ^ 2 ≤ t₂ ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
    have h2 : c ^ 2 * t ^ 2 ≤ c ^ 2 * t₂ ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    exact mul_pos (by nlinarith) (by linarith)
  have h1 := sq_le_ratio hpqt
  have h2 := ratio_mono (c := c) (σ := σ) ht.1 ht.2 (by nlinarith) hq2
  have h3 : Cvs.Prolate.RegularSolutionEnergyComparability.energy c σ t₂ / pq c σ t₂ ≤ 16 * (1 + c ^ 2) * K := by
    rw [div_le_iff₀ (by linarith)]
    have : (1 + c ^ 2) * K ≤ 16 * (1 + c ^ 2) * K * pq c σ t₂ := by
      have := mul_le_mul_of_nonneg_left hpq (by positivity : (0 : ℝ) ≤ 16 * (1 + c ^ 2) * K)
      linarith
    linarith
  linarith

/-- **The mass is controlled at the turning point**: for `c ≥ 4`, `σ = c²θ²`, `0 ≤ θ`, `θ² ≤ ¾`,
`∫_0^1 y² ≤ 50(1 + c²)²y(θ)²`. -/
theorem integral_sq_le_turning {θ : ℝ} (hc : 4 ≤ c) (hθ : 0 ≤ θ) (hθ3 : θ ^ 2 ≤ 3 / 4) (hσ : σ = c ^ 2 * θ ^ 2) :
    ∫ t in (0 : ℝ)..1, regSol (sqC c) σ t ^ 2 ≤ 50 * (1 + c ^ 2) ^ 2 * regSol (sqC c) σ θ ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hθ1 : θ < 1 := by nlinarith
  have hτσ : σ ≤ c ^ 2 * θ ^ 2 := hσ.le
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hyθ : 1 ≤ regSol (sqC c) σ θ := Cvs.Prolate.RegularSolutionForbiddenRegion.one_le_forbidden hθ hτσ θ ⟨le_rfl, hθ1.le⟩
  have hU0 := Cvs.Prolate.RegularSolutionForbiddenRegion.regU_nonneg_forbidden (c := c) (σ := σ) hθ hτσ ⟨le_rfl, hθ1.le⟩
  have hU1 := Cvs.Prolate.RegularSolutionForbiddenRegion.regU_le_half hc0.le hσ0 hθ hτσ θ ⟨le_rfl, hθ1.le⟩
  set Y := regSol (sqC c) σ θ ^ 2 with hY
  set Sθ := regSol (sqC c) σ θ ^ 2 + regU (sqC c) σ θ ^ 2 with hSθ
  have hSθle : Sθ ≤ (1 + c ^ 2) * Y := by
    have : regU (sqC c) σ θ ^ 2 ≤ (c / 2 * regSol (sqC c) σ θ) ^ 2 := pow_le_pow_left₀ hU0 hU1 2
    have e : (c / 2 * regSol (sqC c) σ θ) ^ 2 = c ^ 2 / 4 * Y := by rw [hY]; ring
    have : 0 ≤ c ^ 2 * Y := by positivity
    linarith
  have hSθ0 : 0 ≤ Sθ := by positivity
  have he : Real.exp 1 < 2.72 := by have := Real.exp_one_lt_d9; linarith
  have hSe : Sθ * Real.exp 1 ≤ (1 + c ^ 2) * Y * 2.72 :=
    mul_le_mul hSθle he.le (Real.exp_pos 1).le (by positivity)
  set h := min θ (1 / (2 * c)) with hh
  have hh0 : 0 ≤ h := le_min hθ (by positivity)
  have hhθ : h ≤ θ := min_le_left _ _
  set t₂ := θ - h with ht₂
  have ht₂0 : 0 ≤ t₂ := by linarith
  -- the three pieces
  have hI2 : ∫ t in t₂..θ, regSol (sqC c) σ t ^ 2 ≤ Sθ * Real.exp 1 := by
    have := intervalIntegral.integral_mono_on (by linarith) (intervalIntegrable_sq c σ ht₂0 (by linarith))
      intervalIntegrable_const fun t ht => (le_add_of_nonneg_right (sq_nonneg _)).trans
        (layer_le_exp_one (c := c) (σ := σ) hc hθ3 hσ ht₂0 ht)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have h1 : θ - t₂ ≤ 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hSθ0 (Real.exp_pos 1).le)
    linarith
  have hI3 : ∫ t in θ..1, regSol (sqC c) σ t ^ 2 ≤ Y := by
    have hanti := Cvs.Prolate.RegularSolutionEnergyComparability.sq_anti_forbidden (c := c) (σ := σ) hθ hτσ
    have := intervalIntegral.integral_mono_on hθ1.le (intervalIntegrable_sq c σ hθ hθ1.le)
      intervalIntegrable_const fun t ht => hanti ⟨le_rfl, hθ1.le⟩ ht ht.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have h1 : 1 - θ ≤ 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (regSol (sqC c) σ θ))
    linarith
  have hI1 : ∫ t in (0 : ℝ)..t₂, regSol (sqC c) σ t ^ 2 ≤ 16 * (1 + c ^ 2) * (Sθ * Real.exp 1) := by
    rcases eq_or_lt_of_le ht₂0 with h0 | h0
    · rw [← h0, intervalIntegral.integral_same]; positivity
    · have hhv : h = 1 / (2 * c) := by
        rcases le_total θ (1 / (2 * c)) with h1 | h1
        · exfalso
          have : h = θ := min_eq_left h1
          linarith
        · exact min_eq_right h1
      have ht₂' : t₂ = θ - 1 / (2 * c) := by rw [ht₂, hhv]
      have hpt : ∀ t ∈ Icc (0 : ℝ) t₂, regSol (sqC c) σ t ^ 2 ≤ 16 * (1 + c ^ 2) * (Sθ * Real.exp 1) :=
        fun t ht => below_layer_le (c := c) (σ := σ) hc hθ3 hσ (by rw [← ht₂']; exact h0) (by rw [← ht₂']; exact ht)
      have := intervalIntegral.integral_mono_on ht₂0 (intervalIntegrable_sq c σ le_rfl ht₂0)
        intervalIntegrable_const hpt
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      have h1 : t₂ - 0 ≤ 1 := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1
        (mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * (1 + c ^ 2)) (mul_nonneg hSθ0 (Real.exp_pos 1).le))
      linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := t₂) (intervalIntegrable_sq c σ le_rfl ht₂0)
    (intervalIntegrable_sq c σ ht₂0 (by linarith : t₂ ≤ 1)),
    ← intervalIntegral.integral_add_adjacent_intervals (b := θ) (intervalIntegrable_sq c σ ht₂0 (by linarith))
    (intervalIntegrable_sq c σ hθ hθ1.le)]
  have hY0 : 0 ≤ Y := sq_nonneg _
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have k1 : 16 * (1 + c ^ 2) * (Sθ * Real.exp 1) ≤ 16 * (1 + c ^ 2) * ((1 + c ^ 2) * Y * 2.72) :=
    mul_le_mul_of_nonneg_left hSe (by positivity)
  have k2 : (1 + c ^ 2) * Y ≤ (1 + c ^ 2) ^ 2 * Y := by
    have : 1 + c ^ 2 ≤ (1 + c ^ 2) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hY0
  have k3 : Y ≤ (1 + c ^ 2) ^ 2 * Y := by
    have : 1 ≤ (1 + c ^ 2) ^ 2 := by nlinarith
    nlinarith
  have k4 : 16 * (1 + c ^ 2) * ((1 + c ^ 2) * Y * 2.72) = 43.52 * ((1 + c ^ 2) ^ 2 * Y) := by ring
  linarith

/-! ### A large value on an allowed window -/

/-- A continuous function bounded away from zero on `[α, β]` keeps one sign. -/
theorem sign_const {f : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β) (hf : ContinuousOn f (Icc α β))
    (hne : ∀ t ∈ Icc α β, f t ≠ 0) : (∀ t ∈ Icc α β, 0 < f t) ∨ ∀ t ∈ Icc α β, f t < 0 := by
  have hαI : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
  rcases lt_or_gt_of_ne (hne α hαI) with h | h
  · right
    intro t ht
    by_contra hc
    push Not at hc
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht.1 (hf.mono (Icc_subset_Icc le_rfl ht.2)) ⟨h.le, hc⟩
    exact hne s ⟨hs.1, hs.2.trans ht.2⟩ hs0
  · left
    intro t ht
    by_contra hc
    push Not at hc
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht.1 (hf.mono (Icc_subset_Icc le_rfl ht.2)) ⟨hc, h.le⟩
    exact hne s ⟨hs.1, hs.2.trans ht.2⟩ hs0

/-- **A large value on an allowed window** (eq-cpb Lemma 9(ii)): at an even level (`U(0) = 0`) with `σ > c²β²`,
if `pq ≥ m` on `[α, β] ⊆ [0, 1)` and `(β − α)²m ≥ 4`, then `y(t)² ≥ y(0)²/2` somewhere on `[α, β]`. -/
theorem exists_sq_ge {α β m : ℝ} (hσ : 0 < σ) (hU0 : regU (sqC c) σ 0 = 0) (hα : 0 ≤ α) (hαβ : α < β)
    (hβ1 : β < 1) (hq : c ^ 2 * β ^ 2 < σ) (hm : ∀ t ∈ Icc α β, m ≤ pq c σ t) (hbig : 4 ≤ (β - α) ^ 2 * m) :
    ∃ t ∈ Icc α β, regSol (sqC c) σ 0 ^ 2 / 2 ≤ regSol (sqC c) σ t ^ 2 := by
  by_contra H
  push Not at H
  set y0 := regSol (sqC c) σ 0
  have hy0 : y0 ≠ 0 := fun h => Cvs.Prolate.EdgeCentreSign.regU_ne_zero_of_regSol_eq_zero (sqC c) σ (by norm_num) (by norm_num) h hU0
  have hy02 : 0 < y0 ^ 2 := by positivity
  have hm0 : 0 < m := by
    by_contra h; push Not at h
    have : (β - α) ^ 2 * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h
    linarith
  have hR0 : Cvs.Prolate.RegularSolutionEnergyComparability.energy c σ 0 / pq c σ 0 = y0 ^ 2 := by
    rw [energy_eq, hU0]; unfold pq
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero, one_mul, zero_add]
    field_simp
    rfl
  have hp : ∀ t ∈ Icc α β, 0 < 1 - t ^ 2 := fun t ht => by nlinarith [ht.1, ht.2, hα.trans ht.1]
  have hqt : ∀ t ∈ Icc α β, c ^ 2 * t ^ 2 < σ := fun t ht =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hα.trans ht.1) ht.2 2) (sq_nonneg c)) hq
  -- the flux is large on the window
  have hU : ∀ t ∈ Icc α β, m * y0 ^ 2 / 2 ≤ regU (sqC c) σ t ^ 2 := by
    intro t ht
    have hpq : 0 < pq c σ t := mul_pos (hp t ht) (by linarith [hqt t ht])
    have h1 := ratio_mono (c := c) (σ := σ) le_rfl (hα.trans ht.1) (by linarith [ht.2]) (hqt t ht)
    rw [hR0, le_div_iff₀ hpq, energy_eq] at h1
    have h2 := H t ht
    have h3 := hm t ht
    nlinarith [mul_le_mul_of_nonneg_right h3 hy02.le, mul_le_mul_of_nonneg_left h2.le hpq.le]
  have hv : ∀ t ∈ Icc α β, Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t = -regU (sqC c) σ t / (1 - t ^ 2) := fun t ht => by
    rw [eq_div_iff (hp t ht).ne', mul_comm]
    exact Cvs.Prolate.RegularSolutionEnergyComparability.p_mul_deriv (by linarith [hα.trans ht.1])
  set M := m * y0 ^ 2 / 2 with hM
  have hM0 : 0 < M := by positivity
  have hV : ∀ t ∈ Icc α β, M ≤ Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t ^ 2 := by
    intro t ht
    have hp2 : 0 < (1 - t ^ 2) ^ 2 := by have := hp t ht; positivity
    rw [hv t ht, div_pow, neg_sq, le_div_iff₀ hp2]
    have h1 : (1 - t ^ 2) ^ 2 ≤ 1 := by nlinarith [hp t ht, ht.1, hα.trans ht.1]
    nlinarith [hU t ht, mul_le_mul_of_nonneg_left h1 hM0.le]
  have hcont : ContinuousOn (Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ) (Icc α β) := by
    have : ContinuousOn (fun t => -regU (sqC c) σ t / (1 - t ^ 2)) (Icc α β) :=
      have hnum : ContinuousOn (fun t => -regU (sqC c) σ t) (Icc α β) := fun t ht =>
        ((hasDerivAt_regU (sqC c) σ
          (by linarith [hα.trans ht.1] : (-1 : ℝ) < t)).continuousAt.neg).continuousWithinAt
      have hden : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Icc α β) :=
        (continuous_const.sub (continuous_pow 2)).continuousOn
      ContinuousOn.div (f := fun t => -regU (sqC c) σ t) (g := fun t : ℝ => 1 - t ^ 2) hnum hden
        fun t ht => (hp t ht).ne'
    exact this.congr fun t ht => hv t ht
  have hne : ∀ t ∈ Icc α β, Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t ≠ 0 := fun t ht h => by
    have := hV t ht; rw [h] at this; norm_num at this; linarith
  have hdiff : M * (β - α) ^ 2 ≤ (regSol (sqC c) σ β - regSol (sqC c) σ α) ^ 2 := by
    have hsq : √M * √M = M := Real.mul_self_sqrt hM0.le
    have hsM : 0 ≤ √M := Real.sqrt_nonneg M
    have hd : ∀ t ∈ Icc α β, HasDerivAt (regSol (sqC c) σ) (Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t) t := fun t ht =>
      hasDerivAt_regSol (sqC c) σ (by linarith [hα.trans ht.1])
    rcases sign_const hαβ.le hcont hne with hpos | hneg
    · have hge : ∀ t ∈ Icc α β, √M ≤ Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t := fun t ht => by
        rw [← Real.sqrt_sq (hpos t ht).le]; exact Real.sqrt_le_sqrt (hV t ht)
      have hmono := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv (f := fun t => regSol (sqC c) σ t - √M * t)
        (fun t ht => (hd t ht).sub ((hasDerivAt_id t).const_mul √M)) fun t ht => by
          simp only [mul_one]; linarith [hge t ht]
      have := hmono ⟨le_rfl, hαβ.le⟩ ⟨hαβ.le, le_rfl⟩ hαβ.le
      simp only at this
      have h1 : √M * (β - α) ≤ regSol (sqC c) σ β - regSol (sqC c) σ α := by linarith
      have h2 : 0 ≤ √M * (β - α) := mul_nonneg hsM (by linarith)
      have := mul_le_mul h1 h1 h2 (h2.trans h1)
      nlinarith
    · have hge : ∀ t ∈ Icc α β, √M ≤ -Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t := fun t ht => by
        rw [← Real.sqrt_sq (by linarith [hneg t ht] : 0 ≤ -Cvs.Prolate.RegularSolutionEdge.regV (sqC c) σ t), neg_sq]
        exact Real.sqrt_le_sqrt (hV t ht)
      have hmono := Cvs.Prolate.RegularSolutionDepthBound.monotoneOn_of_deriv (f := fun t => -regSol (sqC c) σ t - √M * t)
        (fun t ht => (hd t ht).neg.sub ((hasDerivAt_id t).const_mul √M)) fun t ht => by
          simp only [mul_one]; linarith [hge t ht]
      have := hmono ⟨le_rfl, hαβ.le⟩ ⟨hαβ.le, le_rfl⟩ hαβ.le
      simp only at this
      have h1 : √M * (β - α) ≤ regSol (sqC c) σ α - regSol (sqC c) σ β := by linarith
      have h2 : 0 ≤ √M * (β - α) := mul_nonneg hsM (by linarith)
      have := mul_le_mul h1 h1 h2 (h2.trans h1)
      nlinarith
  have hup : (regSol (sqC c) σ β - regSol (sqC c) σ α) ^ 2 < 2 * y0 ^ 2 := by
    have h1 := H β ⟨hαβ.le, le_rfl⟩
    have h2 := H α ⟨le_rfl, hαβ.le⟩
    nlinarith [sq_nonneg (regSol (sqC c) σ β + regSol (sqC c) σ α)]
  have : 2 * y0 ^ 2 ≤ M * (β - α) ^ 2 := by
    rw [hM]
    have := mul_le_mul_of_nonneg_right hbig hy02.le
    nlinarith
  linarith

end Cvs.Prolate.RegularSolutionAllowedRegion

end
