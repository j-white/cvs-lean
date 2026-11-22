import Mathlib
import Cvs.Limit.CriticalStripOffAxes
import Cvs.Route.MergedBoundSimpleBottom
import Cvs.Upstream.DavisKahanRayleighRitz
import Cvs.Upstream.MergedLowerBoundPositivity

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A joint gap carries the approximant's limit to the ground state, on compacts of the strip

`K(⟪T v, v⟫ − l₁) ≤ μ − l₁`, with `μ` a floor of `T` on `k̃ᗮ`, puts one of `±θ` within squared
distance `2/K` of `v`. Compacts of `criticalOffAxes` sit below a height `a < 1/2`, where a transform
of type `C e^{|Im z| L/2}` moves by at most `C e^{aL/2}√(2/K)`, which tends to `0` as `L → ∞` at
`C = L`, `K = L e^{L/2}`.
-/

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace Cvs.Route.JointGapStripLimit
open Cvs.ZeroCounting

open Cvs.Limit.CriticalStripOffAxes (criticalOffAxes isOpen_criticalOffAxes)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The joint Rayleigh-quotient Davis–Kahan step -/

/-- **Joint Davis–Kahan.** For symmetric `T`, a unit eigenvector `θ` at `l₁ < μ`, a form at least
`μ‖f‖²` on `k̃ᗮ`, and a unit `v` with `K(⟪T v, v⟫ − l₁) ≤ μ − l₁`, `K > 0`, one has
`1 − ⟪v, θ⟫² ≤ 1/K`. -/
theorem one_sub_inner_sq_le {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {θ kt v : E} {l₁ μ K : ℝ}
    (hθ : ‖θ‖ = 1) (hθeig : T θ = l₁ • θ) (hlt : l₁ < μ)
    (hperp : ∀ f : E, ⟪kt, f⟫_ℝ = 0 → μ * ‖f‖ ^ 2 ≤ ⟪T f, f⟫_ℝ)
    (hv : ‖v‖ = 1) (hK : 0 < K) (hjoint : K * (⟪T v, v⟫_ℝ - l₁) ≤ μ - l₁) :
    1 - ⟪v, θ⟫_ℝ ^ 2 ≤ 1 / K := by
  have hθ0 : θ ≠ 0 := by
    intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
  have hgap := Cvs.Upstream.MergedLowerBoundPositivity.hgap_of_perp hT hθ0 hθeig hlt hperp
  have hDK := Cvs.Upstream.DavisKahanRayleighRitz.gap_mul_sin_sq_le hT hθ hθeig hgap hv
  have hpos : 0 < μ - l₁ := sub_pos.mpr hlt
  rw [le_div_iff₀ hK]
  have h1 : (μ - l₁) * ((1 - ⟪v, θ⟫_ℝ ^ 2) * K) ≤ (μ - l₁) * 1 := by
    have := mul_le_mul_of_nonneg_left hDK hK.le
    nlinarith
  exact le_of_mul_le_mul_left h1 hpos

/-- **Joint Davis–Kahan, signed.** Under the hypotheses of `one_sub_inner_sq_le`, some
`σ ∈ {1, −1}` has `‖σθ − v‖² ≤ 2/K`. -/
theorem exists_sign_norm_sub_sq_le {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {θ kt v : E}
    {l₁ μ K : ℝ} (hθ : ‖θ‖ = 1) (hθeig : T θ = l₁ • θ) (hlt : l₁ < μ)
    (hperp : ∀ f : E, ⟪kt, f⟫_ℝ = 0 → μ * ‖f‖ ^ 2 ≤ ⟪T f, f⟫_ℝ)
    (hv : ‖v‖ = 1) (hK : 0 < K) (hjoint : K * (⟪T v, v⟫_ℝ - l₁) ≤ μ - l₁) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ‖σ • θ - v‖ ^ 2 ≤ 2 / K := by
  have hsin := one_sub_inner_sq_le hT hθ hθeig hlt hperp hv hK hjoint
  obtain ⟨θ', hθ', -, hd⟩ := Cvs.Route.MergedBoundSimpleBottom.exists_sign_norm_sub_sq_le (T := T) (x := K)
    (L := 1) hv hθ hθeig (by rwa [mul_one])
  rw [mul_one] at hd
  rcases hθ' with rfl | rfl
  · exact ⟨1, Or.inl rfl, by rwa [one_smul]⟩
  · exact ⟨-1, Or.inr rfl, by rwa [neg_one_smul]⟩

/-! ### Compacts of the critical strip -/

/-- **A compact subset of `criticalOffAxes` lies below a height `a < 1/2`.** -/
theorem exists_abs_im_le_of_isCompact {A : Set ℂ} (hA : IsCompact A) (hAs : A ⊆ criticalOffAxes) :
    ∃ a : ℝ, 0 ≤ a ∧ a < 1 / 2 ∧ ∀ z ∈ A, |z.im| ≤ a := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, by norm_num, by simp⟩
  · obtain ⟨z₀, hz₀, hmax⟩ := hA.exists_isMaxOn hne
      (continuous_abs.comp Complex.continuous_im).continuousOn
    exact ⟨|z₀.im|, abs_nonneg _, (hAs hz₀).2.2, fun z hz => isMaxOn_iff.mp hmax z hz⟩

/-- **Comparison on compacts.** On an open set of a locally compact space, if `F i − G i → 0`
uniformly on every compact subset and `G i → g` locally uniformly, then `F i → g` locally
uniformly. -/
theorem tendstoLocallyUniformlyOn_of_sub {α β ι : Type*} [TopologicalSpace α]
    [LocallyCompactSpace α] [NormedAddCommGroup β] {p : Filter ι} {U : Set α} (hU : IsOpen U)
    {F G : ι → α → β} {g : α → β}
    (hsub : ∀ A ⊆ U, IsCompact A → TendstoUniformlyOn (fun i z => F i z - G i z) 0 p A)
    (hG : TendstoLocallyUniformlyOn G g p U) :
    TendstoLocallyUniformlyOn F g p U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at hG ⊢
  intro A hAU hA
  have h := (hsub A hAU hA).fun_add (hG A hAU hA)
  simpa using h

/-! ### The transfer -/

section Transfer

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The scales.** With `C = L` and `K = L e^{L/2}`, `C e^{aL/2}√(2/K) → 0` as `L → ∞` whenever
`a < 1/2`. -/
theorem tendsto_scale {l : Filter ι} {L : ι → ℝ} (hL : Tendsto L l atTop) {a : ℝ}
    (ha : a < 1 / 2) :
    Tendsto (fun i => L i * Real.exp (a * L i / 2) * √(2 / (L i * Real.exp (L i / 2)))) l
      (𝓝 0) := by
  have hb : 0 < (1 / 2 - a) / 2 := by linarith
  have key : ∀ y : ℝ, 0 < y → y * Real.exp (a * y / 2) * √(2 / (y * Real.exp (y / 2)))
      = √2 * (y ^ (1 / 2 : ℝ) * Real.exp (-((1 / 2 - a) / 2) * y)) := by
    intro y hy
    have he : Real.exp (y / 2) = Real.exp (y / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsq : √(2 / (y * Real.exp (y / 2))) = √2 / (√y * Real.exp (y / 4)) := by
      rw [Real.sqrt_div' 2 (by positivity), Real.sqrt_mul hy.le, he,
        Real.sqrt_sq (Real.exp_pos _).le]
    have hexp : Real.exp (a * y / 2)
        = Real.exp (-((1 / 2 - a) / 2) * y) * Real.exp (y / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    have hsy : 0 < √y := Real.sqrt_pos.mpr hy
    have hyy : y = √y * √y := (Real.mul_self_sqrt hy.le).symm
    rw [← Real.sqrt_eq_rpow, hsq, hexp]
    nth_rewrite 1 [hyy]
    field_simp
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) _ hb).comp hL).const_mul √2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with i hi
  exact (key (L i) hi).symm

end Transfer

/-! ### The joint gap reaches the strip -/

section Strip

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Strip

end Cvs.Route.JointGapStripLimit
