import Mathlib
import Cvs.L2a.ProlateTailCombinationTerminal
import Cvs.L2a.TailOfModes
import Cvs.Prolate.Mellin.MellinKernelSturmLiouville

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole and Mellin values of a span tail from the rungs' own, weighted by mass

For `Φ = Σ aᵢψᵢ` with rung masses `mᵢ > 0`, `|Σ aᵢXᵢ| ≤ √(Σ aᵢ²mᵢ)·√(Σ vᵢ²/mᵢ)` whenever `|Xᵢ| ≤ vᵢ`. So rung pole
values `|∫Fᵢ| ≤ Pᵢ`, `|∫Fᵢ/θ| ≤ Qᵢ` and a floor `κΣ aᵢ²mᵢ ≤ ∫F²` give the pole with `q = 2√(ΣP²/m)√(ΣQ²/m)/κ`, and
rung Mellin bounds `Bᵢ` below `T` give the span's with `B² = (Σ aᵢ²mᵢ)·ΣB²/m`: no factor `(Σ|aᵢ|)²`.
-/

namespace Cvs.L2a.SpanPoleMellinFromRungs

open Real Set MeasureTheory Cvs.Prolate.Mellin.MellinKernelSturmLiouville Cvs.L2a.TailOfModes Cvs.L2a.ProlateTailCombinationTerminal

variable {ι : Type} [Fintype ι]

/-- The mass-weighted sum `Σ vᵢ²/mᵢ`. -/
noncomputable def massSum (v m : ι → ℝ) : ℝ := ∑ i, v i ^ 2 / m i

/-- **Cauchy–Schwarz against the masses**: `|Σ aᵢXᵢ| ≤ √(Σ aᵢ²mᵢ)·√(Σ vᵢ²/mᵢ)`. -/
theorem abs_sum_le_mass (a X v m : ι → ℝ) (hm : ∀ i, 0 < m i) (hX : ∀ i, |X i| ≤ v i) :
    |∑ i, a i * X i| ≤ √(∑ i, a i ^ 2 * m i) * √(massSum v m) := by
  have h1 : |∑ i, a i * X i| ≤ ∑ i, |a i| * v i := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hX i) (abs_nonneg _)
  have h2 : ∑ i, |a i| * v i = ∑ i, (|a i| * √(m i)) * (v i / √(m i)) := Finset.sum_congr rfl fun i _ => by
    have := Real.sqrt_pos.mpr (hm i)
    field_simp
  have h3 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |a i| * √(m i)) (fun i => v i / √(m i))
  have e1 : ∑ i, (|a i| * √(m i)) ^ 2 = ∑ i, a i ^ 2 * m i := Finset.sum_congr rfl fun i _ => by
    rw [mul_pow, sq_abs, Real.sq_sqrt (hm i).le]
  have e2 : ∑ i, (v i / √(m i)) ^ 2 = massSum v m := Finset.sum_congr rfl fun i _ => by
    rw [div_pow, Real.sq_sqrt (hm i).le]
  rw [e1, e2] at h3
  linarith

/-- `massSum ≥ 0`. -/
theorem massSum_nonneg (v : ι → ℝ) {m : ι → ℝ} (hm : ∀ i, 0 < m i) : 0 ≤ massSum v m :=
  Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hm i).le

/-- **The pole of a span tail from the rungs' pole values.** -/
theorem pole_of_rungs (ψ : ι → ℝ → ℝ) (a m P Q : ι → ℝ) (M : ℕ) {b κ : ℝ} (hb : 1 ≤ b)
    (hcont : ∀ i, Continuous (ψ i)) (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    (hN : κ * ∑ i, a i ^ 2 * m i ≤ ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ ^ 2)
    (hP : ∀ i, |∫ θ in Ioi 1, tailF (ψ i) M b θ| ≤ P i)
    (hQ : ∀ i, |∫ θ in Ioi 1, tailF (ψ i) M b θ / θ| ≤ Q i) :
    -(2 * √(massSum P m) * √(massSum Q m) / κ * ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ ^ 2)
      ≤ 2 * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ)
        * (∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ / θ) := by
  have hc1 : ∀ j ∈ Finset.univ, ∀ k ∈ Finset.Icc 1 M,
      ContinuousOn (fun θ => ψ j (k * θ) * (fun _ : ℝ => (1 : ℝ)) θ) (Icc 1 b) := fun j _ k _ =>
    ((hcont j).comp (continuous_const.mul continuous_id)).continuousOn.mul continuousOn_const
  have hcθ : ∀ j ∈ Finset.univ, ∀ k ∈ Finset.Icc 1 M,
      ContinuousOn (fun θ => ψ j (k * θ) * (fun θ : ℝ => 1 / θ) θ) (Icc 1 b) := fun j _ k _ =>
    ((hcont j).comp (continuous_const.mul continuous_id)).continuousOn.mul
      (continuousOn_const.div continuousOn_id fun θ hθ => (show (0 : ℝ) < θ by linarith [hθ.1]).ne')
  have eX := integral_tailF_sum_mul Finset.univ a ψ (fun _ => 1) M hb hc1
  have eY := integral_tailF_sum_mul Finset.univ a ψ (fun θ => 1 / θ) M hb hcθ
  simp only [mul_one, mul_one_div] at eX eY
  have hX := abs_sum_le_mass a _ P m hm hP
  have hY := abs_sum_le_mass a _ Q m hm hQ
  rw [← eX] at hX
  rw [← eY] at hY
  set X := ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ
  set Y := ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ / θ
  set N := ∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ ^ 2
  set S := ∑ i, a i ^ 2 * m i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hm i).le
  have hP0 := Real.sqrt_nonneg (massSum P m)
  have hQ0 := Real.sqrt_nonneg (massSum Q m)
  have hXY : |X| * |Y| ≤ S * (√(massSum P m) * √(massSum Q m)) := by
    have := mul_le_mul hX hY (abs_nonneg _) (by positivity)
    calc |X| * |Y| ≤ √S * √(massSum P m) * (√S * √(massSum Q m)) := this
      _ = (√S * √S) * (√(massSum P m) * √(massSum Q m)) := by ring
      _ = S * (√(massSum P m) * √(massSum Q m)) := by rw [Real.mul_self_sqrt hS0]
  have hSN : S ≤ N / κ := by rw [le_div_iff₀ hκ]; linarith
  have hlow : -(2 * (|X| * |Y|)) ≤ 2 * X * Y := by
    have := abs_mul X Y ▸ neg_abs_le (X * Y); linarith
  have hK : 2 * (|X| * |Y|) ≤ 2 * √(massSum P m) * √(massSum Q m) / κ * N := by
    have := mul_le_mul_of_nonneg_right hSN (mul_nonneg hP0 hQ0)
    have e : 2 * √(massSum P m) * √(massSum Q m) / κ * N = 2 * (N / κ * (√(massSum P m) * √(massSum Q m))) := by
      ring
    rw [e]; linarith
  linarith

/-- **The Mellin values of a span tail from the rungs' own below `T`.** -/
theorem mellin_of_rungs (ψ : ι → ℝ → ℝ) (a m Bm : ι → ℝ) (M : ℕ) {b T : ℝ} (hb : 1 ≤ b)
    (hcont : ∀ i, Continuous (ψ i)) (hm : ∀ i, 0 < m i)
    (hB : ∀ i, ∀ t : ℝ, |t| < T → |∫ θ in Ioi 1, tailF (ψ i) M b θ * ky t θ| ≤ Bm i
      ∧ |∫ θ in Ioi 1, tailF (ψ i) M b θ * kys t θ| ≤ Bm i) :
    ∀ t : ℝ, |t| < T →
      |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ * ky t θ| ≤ √(∑ i, a i ^ 2 * m i) * √(massSum Bm m)
      ∧ |∫ θ in Ioi 1, tailF (fun ξ => ∑ i, a i * ψ i ξ) M b θ * kys t θ|
        ≤ √(∑ i, a i ^ 2 * m i) * √(massSum Bm m) := by
  intro t ht
  have hlog : ContinuousOn Real.log (Icc 1 b) :=
    continuousOn_log.mono fun θ hθ => by have := hθ.1; simp only [mem_compl_iff, mem_singleton_iff]; linarith
  have hsq : ContinuousOn (fun θ : ℝ => √θ) (Icc 1 b) := Real.continuous_sqrt.continuousOn
  have hne : ∀ θ ∈ Icc (1 : ℝ) b, √θ ≠ 0 := fun θ hθ => (Real.sqrt_pos.mpr (by linarith [hθ.1])).ne'
  have hky : ContinuousOn (ky t) (Icc 1 b) :=
    (continuous_cos.comp_continuousOn (continuousOn_const.mul hlog)).div hsq hne
  have hkys : ContinuousOn (kys t) (Icc 1 b) :=
    (continuous_sin.comp_continuousOn (continuousOn_const.mul hlog)).div hsq hne
  have hψm : ∀ j k, ContinuousOn (fun θ => ψ j (k * θ)) (Icc 1 b) := fun j k =>
    ((hcont j).comp (continuous_const.mul continuous_id)).continuousOn
  have e1 := integral_tailF_sum_mul Finset.univ a ψ (ky t) M hb fun j _ k _ => (hψm j k).mul hky
  have e2 := integral_tailF_sum_mul Finset.univ a ψ (kys t) M hb fun j _ k _ => (hψm j k).mul hkys
  rw [e1, e2]
  exact ⟨abs_sum_le_mass a _ Bm m hm fun i => (hB i t ht).1, abs_sum_le_mass a _ Bm m hm fun i => (hB i t ht).2⟩

/-- The span Mellin bound's square is the mass times `Σ B²/m`. -/
theorem mellin_sq_eq (a m Bm : ι → ℝ) (hm : ∀ i, 0 < m i) :
    (√(∑ i, a i ^ 2 * m i) * √(massSum Bm m)) ^ 2 = massSum Bm m * ∑ i, a i ^ 2 * m i := by
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hm i).le),
    Real.sq_sqrt (massSum_nonneg Bm hm)]
  ring

end Cvs.L2a.SpanPoleMellinFromRungs
