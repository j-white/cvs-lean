import Mathlib
import Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent
import Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier
import Cvs.Upstream.BackwardComparisonRiccati

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The far side of the turning point

For a positive solution of the angular equation on `[s₁, 1]` with `3χ ≤ c²`: `U ≤ √(pq)` on `[s_m, 1]` and
`U ≤ √(pq) + γ` on `[s₁, s_m]`, `s_m² = (c² + χ)/(2c²)`, so `g(s₁)e^{cΦ₂(s₁)}(pq(s₁)/pq(s_m))^{1/4} ≤ g(1)`.
-/

noncomputable section

open Real Set

namespace Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint

open Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier (pp qq Bb gam gamD)
open Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent (U)

/-- The point `s_m = √((c² + χ)/(2c²))` where `pq` is largest. -/
def sm (c χ : ℝ) : ℝ := √((c ^ 2 + χ) / (2 * c ^ 2))

theorem mem_uIcc {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : s ∈ uIcc (-1 : ℝ) 1 := by
  rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, h1⟩

theorem sm_pos {c χ : ℝ} (hc : 0 < c) (hχ : 0 < χ) : 0 < sm c χ := Real.sqrt_pos.2 (by positivity)

theorem sm_sq {c χ : ℝ} (hc : 0 < c) (hχ : 0 < χ) : sm c χ ^ 2 = (c ^ 2 + χ) / (2 * c ^ 2) :=
  Real.sq_sqrt (by positivity)

theorem sm_lt_one {c χ : ℝ} (hc : 0 < c) (_hχ : 0 < χ) (hχc : χ < c ^ 2) : sm c χ < 1 := by
  rw [sm, Real.sqrt_lt' one_pos, div_lt_iff₀ (by positivity)]; nlinarith

/-- Past `s_m`, `q > 0` and `2c²s² ≥ c² + χ`. -/
theorem qq_pos_of_ge {c χ s : ℝ} (hc : 0 < c) (hχ : 0 < χ) (hχc : χ < c ^ 2) (hs : sm c χ ≤ s) :
    0 < qq c χ s ∧ c ^ 2 + χ ≤ 2 * c ^ 2 * s ^ 2 := by
  have h1 : sm c χ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (sm_pos hc hχ).le hs 2
  rw [sm_sq hc hχ, div_le_iff₀ (by positivity)] at h1
  unfold qq
  constructor <;> nlinarith

/-- `U` is continuous where `g ≠ 0`. -/
theorem continuousOn_U {g g₁ g₂ : ℝ → ℝ} {a b : ℝ} (h0 : 0 ≤ a) (h1 : b ≤ 1)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hne : ∀ s ∈ Icc a b, g s ≠ 0) : ContinuousOn (U g g₁) (Icc a b) := by
  intro s hs
  have hm := mem_uIcc (h0.trans hs.1) (hs.2.trans h1)
  unfold U
  exact (((continuousAt_const.sub (continuousAt_id.pow 2)).mul (hg₁ s hm).continuousAt).neg.div
    (hg s hm).continuousAt (hne s hs)).continuousWithinAt

/-- **`U ≤ √(pq)` on `[s_m, 1]`.** -/
theorem U_le_Bb {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 < χ) (hχc : χ < c ^ 2) (hpos : ∀ s ∈ Icc (sm c χ) 1, 0 < g s) :
    ∀ s ∈ Icc (sm c χ) 1, U g g₁ s ≤ Bb c χ s := by
  have hsm0 := sm_pos hc hχ
  have hsm1 := sm_lt_one hc hχ hχc
  have key := Cvs.Upstream.BackwardComparisonRiccati.nonpos_of_deriv_pos (D := fun s => U g g₁ s - Bb c χ s)
    (D' := fun s => (U g g₁ s ^ 2 / (1 - s ^ 2) - (c ^ 2 * s ^ 2 - χ)) - 2 * Bb c χ s * gam c χ s / pp s)
    hsm1.le ?_ ?_ ?_ ?_
  · intro s hs; have := key s hs; linarith
  · refine (continuousOn_U hsm0.le le_rfl hg hg₁ fun s hs => (hpos s hs).ne').sub ?_
    unfold Bb pp qq
    fun_prop
  · intro x hx
    have hq := (qq_pos_of_ge hc hχ hχc hx.1.le).1
    have hp : 0 < pp x := by unfold pp; nlinarith [hx.2, hsm0, hx.1]
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.2, hsm0, hx.1]
    exact (Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent.hasDerivAt_U (hg x (mem_uIcc (hsm0.le.trans hx.1.le) hx.2.le))
      (hg₁ x (mem_uIcc (hsm0.le.trans hx.1.le) hx.2.le)) (hang x (mem_uIcc (hsm0.le.trans hx.1.le) hx.2.le))
      hx2 (hpos x ⟨hx.1.le, hx.2.le⟩).ne').sub (Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.hasDerivAt_Bb hp hq)
  · intro x hx hD
    obtain ⟨hq, h2⟩ := qq_pos_of_ge hc hχ hχc hx.1.le
    have hp : 0 < pp x := by unfold pp; nlinarith [hx.2, hsm0, hx.1]
    have hγ := Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.gam_nonpos hq (hsm0.trans hx.1) h2
    have hB0 : 0 ≤ Bb c χ x := Real.sqrt_nonneg _
    have hB2 : Bb c χ x ^ 2 = pp x * qq c χ x := Real.sq_sqrt (mul_pos hp hq).le
    have hUB : Bb c χ x < U g g₁ x := by linarith
    have hsq : Bb c χ x ^ 2 < U g g₁ x ^ 2 := by nlinarith
    have hpe : pp x = 1 - x ^ 2 := rfl
    have h1 : 0 < U g g₁ x ^ 2 / (1 - x ^ 2) - (c ^ 2 * x ^ 2 - χ) := by
      rw [← hpe, show c ^ 2 * x ^ 2 - χ = qq c χ x from rfl, sub_pos, lt_div_iff₀ hp]
      nlinarith
    have h2' : 2 * Bb c χ x * gam c χ x / pp x ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) hp.le
    linarith
  · simp only [U, Bb, pp, qq]; simp

/-- **`U ≤ √(pq) + γ` on `[s₁, s_m]`**, for `s₀ < s₁`. -/
theorem U_le_W {g g₁ g₂ : ℝ → ℝ} {c χ s₁ : ℝ}
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    (hc : 0 < c) (hχ : 0 < χ) (h3 : 3 * χ ≤ c ^ 2) (hs₁ : √χ / c < s₁) (hs₁m : s₁ ≤ sm c χ)
    (hpos : ∀ s ∈ Icc s₁ 1, 0 < g s) :
    ∀ s ∈ Icc s₁ (sm c χ), U g g₁ s ≤ Bb c χ s + gam c χ s := by
  have hχc : χ < c ^ 2 := by linarith
  have hsm0 := sm_pos hc hχ
  have hsm1 := sm_lt_one hc hχ hχc
  have hs₁0 : 0 < s₁ := lt_of_le_of_lt (by positivity) hs₁
  -- `q > 0` and `γ ≥ 0` on `[s₁, s_m]`
  have hqx : ∀ x, s₁ ≤ x → 0 < qq c χ x := fun x hx => by
    have h1 : √χ < c * x := by rw [div_lt_iff₀ hc] at hs₁; nlinarith
    have h2 : χ < (c * x) ^ 2 := by
      have := Real.sq_sqrt hχ.le
      nlinarith [Real.sqrt_nonneg χ]
    unfold qq; nlinarith
  have hγx : ∀ x, x ≤ sm c χ → 0 < x → 2 * c ^ 2 * x ^ 2 ≤ c ^ 2 + χ := fun x hx hx0 => by
    have h1 : x ^ 2 ≤ sm c χ ^ 2 := pow_le_pow_left₀ hx0.le hx 2
    rw [sm_sq hc hχ, le_div_iff₀ (by positivity)] at h1; nlinarith
  have hend := U_le_Bb hg hg₁ hang hc hχ hχc (fun s hs => hpos s ⟨hs₁m.trans hs.1, hs.2⟩) (sm c χ)
    ⟨le_rfl, hsm1.le⟩
  refine Cvs.Upstream.BackwardComparisonRiccati.le_of_riccati (p := pp) (q := qq c χ)
    (U' := fun s => U g g₁ s ^ 2 / pp s - qq c χ s)
    (W := fun s => Bb c χ s + gam c χ s) (W' := fun s => 2 * Bb c χ s * gam c χ s / pp s + gamD c χ s)
    hs₁m ?_ ?_ ?_ ?_ ?_ ?_ (fun _ _ => rfl) ?_ ?_
  · exact continuousOn_U hs₁0.le hsm1.le hg hg₁ fun s hs => (hpos s ⟨hs.1, hs.2.trans hsm1.le⟩).ne'
  · refine ContinuousOn.add (f := fun s => Bb c χ s) (g := fun s => gam c χ s)
      (by unfold Bb pp qq; fun_prop) ?_
    intro x hx
    have hq := hqx x hx.1
    have hq' : 2 * qq c χ x ≠ 0 := (mul_pos two_pos hq).ne'
    unfold qq at hq'
    refine ContinuousAt.continuousWithinAt ?_
    unfold gam pp qq
    fun_prop (disch := exact hq')
  · intro x hx
    have hm := mem_uIcc (hs₁0.le.trans hx.1.le) (hx.2.le.trans hsm1.le)
    have hx2 : x ^ 2 < 1 := by nlinarith [hx.2, hsm1, hx.1, hs₁0]
    have := Cvs.Prolate.LiouvilleGreen.RiccatiWkbExponent.hasDerivAt_U (hg x hm) (hg₁ x hm) (hang x hm) hx2
      (hpos x ⟨hx.1.le, hx.2.le.trans hsm1.le⟩).ne'
    exact this
  · intro x hx
    have hq := hqx x hx.1.le
    have hp : 0 < pp x := by unfold pp; nlinarith [hx.2, hsm1, hx.1, hs₁0]
    exact (Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.hasDerivAt_Bb hp hq).add (Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.hasDerivAt_gam hq.ne')
  · intro x hx; unfold pp; nlinarith [hx.2, hsm1, hx.1, hs₁0]
  · intro x hx
    have hq := hqx x hx.1.le
    exact add_nonneg (Real.sqrt_nonneg _)
      (Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.gam_nonneg hq (hs₁0.trans hx.1) (hγx x hx.2.le (hs₁0.trans hx.1)))
  · intro x hx
    have hq := hqx x hx.1.le
    exact Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.barrier_le (hs₁0.trans hx.1) (by linarith [hx.2, hsm1]) hq hχ.le h3 hc
  · have hq := hqx (sm c χ) hs₁m
    have := Cvs.Prolate.LiouvilleGreen.WkbRiccatiBarrier.gam_nonneg hq hsm0 (hγx _ le_rfl hsm0)
    linarith


/-- `g₁ = −Ug/p` where `g ≠ 0`, `p ≠ 0`. -/
theorem g₁_eq {g g₁ : ℝ → ℝ} {x : ℝ} (hg : g x ≠ 0) (hp : 1 - x ^ 2 ≠ 0) :
    g₁ x = -(U g g₁ x * g x) / (1 - x ^ 2) := by
  unfold U; field_simp

end Cvs.Prolate.LiouvilleGreen.FarSideTurningPoint
