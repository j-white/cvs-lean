import Mathlib
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Upstream.PencilLayerBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Theorem B′: the layer floor (WF′) and the deep remainder (EF′) give (B)

With `F_k = λ_min(S_k)` the Schur floors of the cell Gram and `A(T₀) = {T_j ≥ T₀}`: if eventually
`F_{min A(T₀)} ≥ μ*C₀∞/2 + ε` and `Σ_{T_k < T₀} δ_k/F_k → 0`, then `limsup C₀(x)·λ_max(diag μ, C) < 2`.
-/

noncomputable section

open Real Set Filter Matrix Finset Topology

namespace Cvs.Route.Visibility.LayerFloorDeepRemainderB
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram cellGram_posDef mu muInc lamTop levT)

/-! ### The constants -/

/-- `μ* = 12 − 8√2 = 2/(1 + √½)²`. -/
def muStar : ℝ := 12 - 8 * √2

/-- `μ* > 0`. -/
theorem muStar_pos : 0 < muStar := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have : √2 < 3 / 2 := by nlinarith [Real.sqrt_nonneg 2]
  unfold muStar; linarith

/-- The AL-R constant `C₀(x) = (½ + √(W̃/2 + C₁/(2c)) + (πcλ_t)^{−1/2})²` at `c = 2πx`. -/
def C0 (Wt C₁ : ℝ) (x : ℕ) : ℝ :=
  (1 / 2 + √(Wt / 2 + C₁ / (2 * (2 * π * x))) + 1 / √(π * (2 * π * x) * lamTop x)) ^ 2

/-- Its limit `C₀∞ = (½ + √(W̃/2))²`. -/
def C0inf (Wt : ℝ) : ℝ := (1 / 2 + √(Wt / 2)) ^ 2

/-- `C₀∞ > 0`. -/
theorem C0inf_pos (Wt : ℝ) : 0 < C0inf Wt := by unfold C0inf; positivity

/-- `80 ≤ 2πx` eventually. -/
theorem eventually_scale : ∀ᶠ x : ℕ in atTop, 80 ≤ 2 * π * x := by
  have h : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  exact h.eventually_ge_atTop 80

/-- **(c)**: `C₀(x) → C₀∞` (from `λ_t ≥ ½`). -/
theorem tendsto_C0 (Wt C₁ : ℝ) : Tendsto (C0 Wt C₁) atTop (𝓝 (C0inf Wt)) := by
  have hc : Tendsto (fun x : ℕ => 2 * π * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h1 : Tendsto (fun x : ℕ => C₁ / (2 * (2 * π * (x : ℝ)))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hc.const_mul_atTop (by norm_num))
  have hb : Tendsto (fun x : ℕ => 1 / √(π * (2 * π * (x : ℝ)) / 2)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℕ => √(π * (2 * π * (x : ℝ)) / 2)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp ((hc.const_mul_atTop Real.pi_pos).atTop_div_const (by norm_num))
    refine this.inv_tendsto_atTop.congr fun x => ?_
    simp only [Pi.inv_apply, one_div]
  have h2 : Tendsto (fun x : ℕ => 1 / √(π * (2 * π * (x : ℝ)) * lamTop x)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_ hb
    filter_upwards [eventually_scale] with x hx
    have hh := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.half_le_lamTop hx
    have hp : 0 < π * (2 * π * (x : ℝ)) / 2 := by positivity
    gcongr
    calc π * (2 * π * (x : ℝ)) / 2 = π * (2 * π * x) * (1 / 2) := by ring
      _ ≤ π * (2 * π * x) * lamTop x := by gcongr
  have h := (((tendsto_const_nhds (x := (1 / 2 : ℝ))).add
    ((h1.const_add (Wt / 2)).sqrt)).add h2).pow 2
  have e : (1 / 2 + √(Wt / 2 + 0) + 0) ^ 2 = C0inf Wt := by simp [C0inf]
  rw [e] at h
  exact h

/-- `C₀ ≥ 0`. -/
theorem C0_nonneg (Wt C₁ : ℝ) (x : ℕ) : 0 ≤ C0 Wt C₁ x := sq_nonneg _

/-! ### The pencil top and the layer floors of the real cell Gram -/

/-- `c_E^C = λ_max(diag μ, C)`, the pencil top of the weights `μ` against the cell Gram. -/
def cE (x : ℕ) : ℝ := Cvs.Upstream.PencilLayerBound.pencilTop (fun n : Fin x => mu x n) (cellGram x) Set.univ

open Classical in
/-- The Schur floor `F_k = λ_min(S_k)` of the layer `{j ≥ k}` of the cell Gram (`0` if `C` is not definite). -/
def floorC (x : ℕ) (k : Fin x) : ℝ :=
  if h : (cellGram x).PosDef then Cvs.Upstream.PencilLayerBound.layerFloor h k else 0

/-- At `80 ≤ 2πx`, `floorC` is `λ_min(S_k)`. -/
theorem floorC_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) (k : Fin x) :
    floorC x k = Cvs.Upstream.PencilLayerBound.layerFloor (cellGram_posDef hx) k := by
  rw [floorC, dif_pos (cellGram_posDef hx)]

/-- `F_k ≥ 0`. -/
theorem floorC_nonneg (x : ℕ) (k : Fin x) : 0 ≤ floorC x k := by
  unfold floorC; split_ifs with h
  · exact (Cvs.Upstream.PencilLayerBound.layerFloor_pos h k).le
  · exact le_rfl

/-- The top rung `t = x − 1`. -/
def top {x : ℕ} (hx : 80 ≤ 2 * π * x) : Fin x :=
  ⟨x - 1, by have := Cvs.Prolate.Gram.ProlateCellGramHalfUnit.two_le_of_scale hx; omega⟩

/-- Every rung lies below the top. -/
theorem le_top {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : j ≤ top hx :=
  Fin.le_iff_val_le_val.2 (by simp [top]; omega)

/-! ### (WF′), (EF′) and (B) -/

/-- **(WF′)** at the cut `T₀`: for some `ε > 0`, eventually the first rung `k₀` with `T_{k₀} ≥ T₀` exists and
its layer floor satisfies `F_{k₀} ≥ μ*C₀∞/2 + ε`. -/
def WFprime (Wt T₀ : ℝ) : Prop :=
  ∃ ε > 0, ∀ᶠ x : ℕ in atTop, ∃ k₀ : Fin x, T₀ ≤ levT x k₀ ∧ (∀ j < k₀, levT x j < T₀)
    ∧ muStar * C0inf Wt / 2 + ε ≤ floorC x k₀

/-- **(EF′)** at the cut `T₀`: `R_{T₀} = Σ_{T_k < T₀} δ_k/F_k → 0`. -/
def EFprime (T₀ : ℝ) : Prop :=
  Tendsto (fun x : ℕ => ∑ k ∈ univ.filter (fun k : Fin x => levT x k < T₀), muInc x k / floorC x k)
    atTop (𝓝 0)

/-- **(B)**: `limsup C₀(x)·λ_max(diag μ, C) < 2`. -/
def CondB (Wt C₁ : ℝ) : Prop := ∃ κ < 2, ∀ᶠ x : ℕ in atTop, C0 Wt C₁ x * cE x ≤ κ

/-- Below the first rung of `A(T₀)` are exactly the rungs with `T_k < T₀`. -/
theorem filter_lt_eq {x : ℕ} (hx : 80 ≤ 2 * π * x) {T₀ : ℝ} {k₀ : Fin x} (h1 : T₀ ≤ levT x k₀)
    (h2 : ∀ j < k₀, levT x j < T₀) :
    univ.filter (· < k₀) = univ.filter (fun k : Fin x => levT x k < T₀) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨h2 k, fun hk => lt_of_not_ge fun hge => ?_⟩
  exact absurd (h1.trans ((Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT_strictMono hx).monotone hge)) (not_le.2 hk)

/-! ### Corollary B′.1 -/

end Cvs.Route.Visibility.LayerFloorDeepRemainderB
