import Mathlib
import Cvs.L2a.MirrorSplitDefect
import Cvs.L2a.PositionTruncatedTail
import Cvs.L2a.ReflectionFloor
import Cvs.Upstream.CosineTransformDilation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The core/arm identity, the angle inequality and the swap form

`PositionTruncatedTail`'s tail splits as `F = 1_(1,X]Φ + E`, with `E = Σ_{2≤m≤X} D_m(1_(m,X]Φ)` supported in `(1, X/2]`. For a
self-adjoint involution `J`, `h = u + a_B + a_F` and `F = u + a_B + E`: the core/arm identity (E5), the angle inequality
(E6) and the swap form (E7), abstractly (from `MirrorSplitDefect`'s mirror split) and in `L²(0, ∞)` with `ReflectionFloor`'s `Uop`.
-/

noncomputable section

open MeasureTheory Set Real Cvs.L2a.PositionTruncatedTail Cvs.L2a.ReflectionFloor Cvs.L2a.MirrorSplitDefect

namespace Cvs.L2a.CoreArmIdentity

/-! ### The abstract identities -/

section Abstract

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **The core/arm identity (E5)**: for a self-adjoint involution `J`, `h = u + a`, `a = a_B + a_F`, `u ⊥ a_F` and
`F = u + a_B + e`: `‖F‖² − ‖h‖²/2 = Pos + re⟨a, Ja⟩ − re⟨Jh + h, a⟩ + 2re⟨u + a_B + Ja_B, e⟩`, where
`Pos = ½‖u + Ja‖² + 2re⟨u, a⟩ + ‖e − Ja_B‖²`. -/
theorem core_arm_identity (J : E →ₗ[𝕜] E) (hsa : ∀ v w, ⟪J v, w⟫ = ⟪v, J w⟫) (hJJ : ∀ v, J (J v) = v)
    (u aB aF e : E) (hort : RCLike.re ⟪u, aF⟫ = 0) :
    ‖u + aB + e‖ ^ 2 - ‖u + (aB + aF)‖ ^ 2 / 2
      = (‖u + J (aB + aF)‖ ^ 2 / 2 + 2 * RCLike.re ⟪u, aB + aF⟫ + ‖e - J aB‖ ^ 2)
        + RCLike.re ⟪aB + aF, J (aB + aF)⟫ - RCLike.re ⟪J (u + (aB + aF)) + (u + (aB + aF)), aB + aF⟫
        + 2 * RCLike.re ⟪u + aB + J aB, e⟫ := by
  have hm := mirror_split J hsa hJJ u (aB + aF)
  have hJ := norm_map_of_involution J hsa hJJ aB
  have h1 := norm_add_sq (𝕜 := 𝕜) (u + aB) e
  have h2 := norm_add_sq (𝕜 := 𝕜) u aB
  have h3 := norm_add_sq (𝕜 := 𝕜) u (aB + aF)
  have h4 := norm_sub_sq (𝕜 := 𝕜) e (J aB)
  have h5 : RCLike.re ⟪u, aB + aF⟫ = RCLike.re ⟪u, aB⟫ + RCLike.re ⟪u, aF⟫ := by
    rw [inner_add_right, map_add]
  have h6 : RCLike.re ⟪u + aB + J aB, e⟫ = RCLike.re ⟪u + aB, e⟫ + RCLike.re ⟪J aB, e⟫ := by
    rw [inner_add_left, map_add]
  have h7 : RCLike.re ⟪e, J aB⟫ = RCLike.re ⟪J aB, e⟫ := inner_re_symm _ _
  rw [hJ] at h4
  linarith

end Abstract

/-! ### The split of the tail -/

/-- The dilate part `E = Σ_{2 ≤ m ≤ ⌊X⌋} D_m(1_(m,X]Φ)` of `PositionTruncatedTail`'s tail: the sum of `Φ(mθ)` on `(1, X/m]`. -/
def dilSum (Φ : ℝ → ℝ) (X θ : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 ⌊X⌋₊, (Ioc 1 (X / m)).indicator (fun θ => Φ (m * θ)) θ

/-- **The tail split**: `posTail Φ X = 1_(1,X]Φ + E`. -/
theorem posTail_eq_add_dilSum (Φ : ℝ → ℝ) (X θ : ℝ) :
    posTail Φ X θ = (Ioc 1 X).indicator Φ θ + dilSum Φ X θ := by
  rw [posTail_eq_sum, dilSum]
  rcases Nat.eq_zero_or_pos ⌊X⌋₊ with h0 | h0
  · have hX : X < 1 := Nat.floor_eq_zero.1 h0
    have hn : (Ioc 1 X).indicator Φ θ = 0 :=
      indicator_of_notMem (fun h => by linarith [h.1, h.2]) _
    rw [h0, hn]
    simp
  · rw [← Finset.insert_Icc_add_one_left_eq_Icc h0, Finset.sum_insert (by simp)]
    simp

/-- **`E` is supported in `(1, X/2]`**. -/
theorem dilSum_of_notMem {Φ : ℝ → ℝ} {X θ : ℝ} (hθ : θ ∉ Ioc 1 (X / 2)) : dilSum Φ X θ = 0 := by
  refine Finset.sum_eq_zero fun m hm => indicator_of_notMem (fun (h : θ ∈ Ioc (1 : ℝ) (X / m)) => hθ ⟨h.1, ?_⟩) _
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
  have hX : 0 ≤ X := by
    have h1 : 1 < X / m := lt_of_lt_of_le h.1 h.2
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < m)).1 h1
    linarith
  exact h.2.trans (div_le_div_of_nonneg_left hX (by norm_num) hm2)

/-- `E` vanishes for `θ ≤ 1`. -/
theorem dilSum_of_le_one {Φ : ℝ → ℝ} {X θ : ℝ} (hθ : θ ≤ 1) : dilSum Φ X θ = 0 :=
  dilSum_of_notMem fun h => by linarith [h.1]

/-- `E` vanishes for `θ > X` when `X ≥ 0`. -/
theorem dilSum_of_gt {Φ : ℝ → ℝ} {X θ : ℝ} (hX : 0 ≤ X) (hθ : X < θ) : dilSum Φ X θ = 0 :=
  dilSum_of_notMem fun h => by linarith [h.2]

/-! ### The identities in `L²(0, ∞)` -/

local notation "μ₀" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H₀" => Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
local notation "μ₁" => (volume.restrict (Ioi (1 : ℝ)))

/-- An integral over `(0, ∞)` of a function vanishing on `(0, 1]` is the integral over `(1, ∞)`. -/
theorem integral_Ioi_zero_eq {φ : ℝ → ℝ} (hφ : ∀ x, x ≤ 1 → φ x = 0) :
    ∫ x in Ioi 0, φ x = ∫ x in Ioi 1, φ x := by
  have h : ∫ x in Ioi 0, φ x = ∫ x in Ioi 0, (Ioi (1 : ℝ)).indicator φ x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hφ x (not_lt.1 hx)]
  rw [h, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]

/-- For classes of real functions with `φ = 0` on `(0, 1]`: `re⟨f, g⟩ = ∫_{Ioi 1} φψ`. -/
theorem re_inner_of_ae {f g : H₀} {φ ψ : ℝ → ℝ} (hf : (f : ℝ → ℂ) =ᵐ[μ₀] fun x => (φ x : ℂ))
    (hg : (g : ℝ → ℂ) =ᵐ[μ₀] fun x => (ψ x : ℂ)) (hφ : ∀ x, x ≤ 1 → φ x = 0) :
    RCLike.re (inner ℂ f g) = ∫ x in Ioi 1, φ x * ψ x := by
  have h : inner ℂ f g = ((∫ x in Ioi 0, φ x * ψ x : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hf, hg] with x h1 h2
    rw [h1, h2, RCLike.inner_apply', Complex.conj_ofReal]
    push_cast; ring
  rw [h, RCLike.re_to_complex, Complex.ofReal_re]
  exact integral_Ioi_zero_eq fun x hx => by rw [hφ x hx, zero_mul]

/-- For the class of a real function with `φ = 0` on `(0, 1]`: `‖f‖² = ∫_{Ioi 1} φ²`. -/
theorem norm_sq_of_ae {f : H₀} {φ : ℝ → ℝ} (hf : (f : ℝ → ℂ) =ᵐ[μ₀] fun x => (φ x : ℂ))
    (hφ : ∀ x, x ≤ 1 → φ x = 0) : ‖f‖ ^ 2 = ∫ x in Ioi 1, φ x ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), re_inner_of_ae hf hf hφ]
  simp only [sq]

/-- With `χ = 1` beyond `X`: `1_(1,∞)(1 − χ)Φ + 1_(1,X]χΦ = 1_(1,X]Φ`. -/
theorem edge_split {Φ χ : ℝ → ℝ} {X : ℝ} (hχX : ∀ x, X < x → χ x = 1) (x : ℝ) :
    (Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x + (Ioc 1 X).indicator (fun x => χ x * Φ x) x
      = (Ioc 1 X).indicator Φ x := by
  by_cases h : x ∈ Ioc 1 X
  · rw [indicator_of_mem h, indicator_of_mem h, indicator_of_mem (show x ∈ Ioi (1 : ℝ) from h.1)]; ring
  · rw [indicator_of_notMem h, indicator_of_notMem h]
    by_cases h1 : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem h1, hχX x (not_le.1 fun h2 => h ⟨h1, h2⟩)]; ring
    · rw [indicator_of_notMem h1]; ring

/-- With `χ = 1` beyond `X ≥ 1`: `1_(1,X]χΦ + 1_(X,∞)Φ = 1_(1,∞)χΦ`. -/
theorem arm_split {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hχX : ∀ x, X < x → χ x = 1) (x : ℝ) :
    (Ioc 1 X).indicator (fun x => χ x * Φ x) x + (Ioi X).indicator Φ x
      = (Ioi 1).indicator (fun x => χ x * Φ x) x := by
  by_cases h : x ∈ Ioc 1 X
  · rw [indicator_of_mem h, indicator_of_mem (show x ∈ Ioi (1 : ℝ) from h.1),
      indicator_of_notMem (show x ∉ Ioi X from not_lt.2 h.2)]; ring
  · rw [indicator_of_notMem h]
    by_cases h1 : X < x
    · rw [indicator_of_mem (show x ∈ Ioi X from h1), indicator_of_mem (show x ∈ Ioi (1 : ℝ) by
        simp only [mem_Ioi]; linarith), hχX x h1]; ring
    · have hx1 : ¬ 1 < x := fun h2 => h ⟨h2, not_lt.1 h1⟩
      rw [indicator_of_notMem (show x ∉ Ioi X from h1), indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from hx1)]
      ring

/-- The classes of the core/arm pieces: `h = u + a_B + a_F` is `1_(1,∞)Φ`, `a_B + a_F` is `1_(1,∞)χΦ`, `u + a_B` is
`1_(1,X]Φ`, `F = u + a_B + e` is `posTail Φ X`, and `D = e − a_F` is `posTail Φ X − 1_(1,∞)Φ`. -/
theorem core_arm_ae {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hχX : ∀ x, X < x → χ x = 1) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    ((u + (aB + aF) : H₀) : ℝ → ℂ) =ᵐ[μ₀] (fun x => (((Ioi 1).indicator Φ x : ℝ) : ℂ))
      ∧ ((aB + aF : H₀) : ℝ → ℂ) =ᵐ[μ₀] (fun x => (((Ioi 1).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
      ∧ ((u + aB : H₀) : ℝ → ℂ) =ᵐ[μ₀] (fun x => (((Ioc 1 X).indicator Φ x : ℝ) : ℂ))
      ∧ ((u + aB + e : H₀) : ℝ → ℂ) =ᵐ[μ₀] (fun x => ((posTail Φ X x : ℝ) : ℂ))
      ∧ ((e - aF : H₀) : ℝ → ℂ) =ᵐ[μ₀] (fun x => ((posTail Φ X x - (Ioi 1).indicator Φ x : ℝ) : ℂ)) := by
  have hpt : ∀ x, (Ioc 1 X).indicator Φ x + (Ioi X).indicator Φ x = (Ioi 1).indicator Φ x := fun x => by
    have := arm_split (Φ := Φ) (χ := fun _ => 1) hX (fun _ _ => rfl) x
    simpa only [one_mul] using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add u (aB + aF), Lp.coeFn_add aB aF, hu, haB, haF] with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, ← add_assoc,← Complex.ofReal_add, ← Complex.ofReal_add, edge_split hχX, hpt]
  · filter_upwards [Lp.coeFn_add aB aF, haB, haF] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, ← Complex.ofReal_add, arm_split hX hχX]
  · filter_upwards [Lp.coeFn_add u aB, hu, haB] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, ← Complex.ofReal_add, edge_split hχX]
  · filter_upwards [Lp.coeFn_add (u + aB) e, Lp.coeFn_add u aB, hu, haB, he] with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, ← Complex.ofReal_add, ← Complex.ofReal_add,
      edge_split hχX, posTail_eq_add_dilSum]
  · filter_upwards [Lp.coeFn_sub e aF, he, haF] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, ← Complex.ofReal_sub, posTail_eq_add_dilSum, ← hpt x]
    ring_nf

/-- **The core/arm identity (E5) in `L²(0, ∞)`**: with `χ = 1` beyond `X ≥ 1`, `u = 1_(1,∞)(1 − χ)Φ`,
`a_B = 1_(1,X]χΦ`, `a_F = 1_(X,∞)Φ`, `e = E` and `J = Uop`: `N − P/2 = Pos + re⟨a, Ja⟩ − re⟨e₁, a⟩ + Dil`. -/
theorem core_arm_identity_L2 {c : ℝ} (hc : 0 < c) {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X)
    (hχX : ∀ x, X < x → χ x = 1) {u aB aF e : H₀}
    (hu : (u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
    (haB : (aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
    (haF : (aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
    (he : (e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) :
    (∫ θ in Ioi 1, posTail Φ X θ ^ 2) - (∫ θ in Ioi 1, Φ θ ^ 2) / 2
      = (‖u + Uop hc (aB + aF)‖ ^ 2 / 2 + 2 * (∫ x in Ioi 1, χ x * (1 - χ x) * Φ x ^ 2)
          + ‖e - Uop hc aB‖ ^ 2)
        + RCLike.re (inner ℂ (aB + aF) (Uop hc (aB + aF)))
        - RCLike.re (inner ℂ (Uop hc (u + (aB + aF)) + (u + (aB + aF))) (aB + aF))
        + 2 * RCLike.re (inner ℂ (u + aB + Uop hc aB) e) := by
  obtain ⟨hh, ha, -, hF, -⟩ := core_arm_ae hX hχX hu haB haF he
  have hu0 : ∀ x, x ≤ 1 → (Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x = 0 :=
    fun x hx => indicator_of_notMem (fun h => not_lt.2 hx h) _
  have hort : RCLike.re (inner ℂ u aF) = 0 := by
    rw [re_inner_of_ae hu haF hu0]
    refine (setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_).trans (integral_zero _ _)
    by_cases hx : X < x
    · rw [indicator_of_mem (show x ∈ Ioi (1 : ℝ) from show (1 : ℝ) < x by linarith), hχX x hx]; ring
    · rw [indicator_of_notMem (show x ∉ Ioi X from hx), mul_zero]
  have hN : ‖u + aB + e‖ ^ 2 = ∫ θ in Ioi 1, posTail Φ X θ ^ 2 :=
    norm_sq_of_ae hF fun x hx => posTail_zero Φ X hx
  have hP : ‖u + (aB + aF)‖ ^ 2 = ∫ θ in Ioi 1, Φ θ ^ 2 := by
    rw [norm_sq_of_ae hh fun x hx => indicator_of_notMem (fun h => not_lt.2 hx h) _]
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [indicator_of_mem hx]
  have hua : RCLike.re (inner ℂ u (aB + aF)) = ∫ x in Ioi 1, χ x * (1 - χ x) * Φ x ^ 2 := by
    rw [re_inner_of_ae hu ha hu0]
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      rw [indicator_of_mem hx, indicator_of_mem hx]; ring
  have h := core_arm_identity (Uop hc) (inner_Uop hc) (Uop_Uop hc) u aB aF e hort
  rw [hN, hP, hua] at h
  exact h

/-- **`Pos ≥ 0`**: for `0 ≤ χ ≤ 1` on `(1, ∞)`, `½‖q‖² + 2∫_{Ioi 1} χ(1 − χ)Φ² + ‖r‖² ≥ 0`. -/
theorem pos_nonneg {Φ χ : ℝ → ℝ} (hχ : ∀ x, 1 < x → 0 ≤ χ x ∧ χ x ≤ 1) (q r : H₀) :
    0 ≤ ‖q‖ ^ 2 / 2 + 2 * (∫ x in Ioi 1, χ x * (1 - χ x) * Φ x ^ 2) + ‖r‖ ^ 2 := by
  have h : 0 ≤ ∫ x in Ioi 1, χ x * (1 - χ x) * Φ x ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun x hx => by
      have := hχ x hx
      exact mul_nonneg (mul_nonneg this.1 (by linarith [this.2])) (sq_nonneg _)
  positivity

/-- **The core/arm pieces exist**: for `Φ ∈ L²(1, ∞)`, measurable `0 ≤ χ ≤ 1` and `X ≥ 1`, the classes `u`, `a_B`,
`a_F`, `e` of `1_(1,∞)(1 − χ)Φ`, `1_(1,X]χΦ`, `1_(X,∞)Φ` and `E` lie in `L²(0, ∞)`. -/
theorem exists_core_arm {Φ χ : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) (hΦ : MemLp Φ 2 μ₁) (hχm : Measurable χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) :
    ∃ u aB aF e : H₀,
      ((u : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi 1).indicator (fun x => (1 - χ x) * Φ x) x : ℝ) : ℂ))
      ∧ ((aB : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
      ∧ ((aF : ℝ → ℂ) =ᵐ[μ₀] fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
      ∧ ((e : ℝ → ℂ) =ᵐ[μ₀] fun x => ((dilSum Φ X x : ℝ) : ℂ)) := by
  have lift : ∀ {g : ℝ → ℝ}, MemLp g 2 μ₁ → MemLp ((Ioi (1 : ℝ)).indicator g) 2 μ₀ := fun hg =>
    ((memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hg).restrict _
  have hu1 : MemLp (fun x => (1 - χ x) * Φ x) 2 μ₁ :=
    hΦ.of_le (((hχm.const_sub 1).aestronglyMeasurable : AEStronglyMeasurable (fun x => 1 - χ x) μ₁).mul
      hΦ.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (abs_le.2 ⟨by linarith [hχ1 x], by linarith [hχ0 x]⟩))
  have ha1 : MemLp (fun x => χ x * Φ x) 2 μ₁ :=
    hΦ.of_le ((hχm.aestronglyMeasurable : AEStronglyMeasurable χ μ₁).mul hΦ.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨by linarith [hχ0 x], hχ1 x⟩))
  have hΦ0 := lift hΦ
  have hmu := (lift hu1).ofReal (K := ℂ)
  have hmaB : MemLp (fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ)) 2 μ₀ := by
    have h := ((lift ha1).indicator (measurableSet_Iic (a := X)).nullMeasurableSet).ofReal (K := ℂ)
    have e : (fun x => (((Ioc 1 X).indicator (fun x => χ x * Φ x) x : ℝ) : ℂ))
        = fun x => (((Iic X).indicator ((Ioi 1).indicator (fun x => χ x * Φ x)) x : ℝ) : ℂ) := by
      funext x
      rw [indicator_indicator, inter_comm, Ioi_inter_Iic]
    rw [e]; exact h
  have hmaF : MemLp (fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ)) 2 μ₀ := by
    have h := (hΦ0.indicator (measurableSet_Ioi (a := X)).nullMeasurableSet).ofReal (K := ℂ)
    have e : (fun x => (((Ioi X).indicator Φ x : ℝ) : ℂ))
        = fun x => (((Ioi X).indicator ((Ioi 1).indicator Φ) x : ℝ) : ℂ) := by
      funext x
      rw [indicator_indicator, Ioi_inter_Ioi, max_eq_left hX]
    rw [e]; exact h
  have hme : MemLp (fun x => ((dilSum Φ X x : ℝ) : ℂ)) 2 μ₀ := by
    have hterm : ∀ m ∈ Finset.Icc 2 ⌊X⌋₊,
        MemLp (fun x => (((Ioc 1 (X / m)).indicator (fun θ => Φ (m * θ)) x : ℝ) : ℂ)) 2 μ₀ := by
      intro m hm
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
      have h := (Cvs.Upstream.CosineTransformDilation.memLp_comp_mul_Ioi hΦ0.ofReal (m := m) (by linarith)).indicator
        (measurableSet_Ioc (a := 1) (b := X / m)).nullMeasurableSet
      have e : (fun x => (((Ioc 1 (X / m)).indicator (fun θ => Φ (m * θ)) x : ℝ) : ℂ))
          = (Ioc 1 (X / m)).indicator fun x => (((Ioi 1).indicator Φ (m * x) : ℝ) : ℂ) := by
        funext x
        by_cases hx : x ∈ Ioc 1 (X / m)
        · have hmx : m * x ∈ Ioi (1 : ℝ) := show (1 : ℝ) < m * x by nlinarith [hx.1]
          rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hmx]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, Complex.ofReal_zero]
      rw [e]; exact h
    have e : (fun x => ((dilSum Φ X x : ℝ) : ℂ))
        = fun x => ∑ m ∈ Finset.Icc 2 ⌊X⌋₊, (((Ioc 1 (X / m)).indicator (fun θ => Φ (m * θ)) x : ℝ) : ℂ) := by
      funext x
      rw [dilSum, Complex.ofReal_sum]
    rw [e]; exact memLp_finsetSum _ hterm
  exact ⟨hmu.toLp _, hmaB.toLp _, hmaF.toLp _, hme.toLp _, hmu.coeFn_toLp, hmaB.coeFn_toLp,
    hmaF.coeFn_toLp, hme.coeFn_toLp⟩

end Cvs.L2a.CoreArmIdentity
