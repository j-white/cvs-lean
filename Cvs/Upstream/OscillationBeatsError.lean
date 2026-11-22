import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A growing oscillation beats its error along any scale map, and `γ log n` meets every phase
If `D ≤ −g·s + E`, `g > 0` and `E ≤ η·g` eventually, and `c ≤ s` frequently along a map `φ → ∞` with `η < c`,
then `D ∘ φ < 0` frequently; along `L = log n`, `n ∈ ℕ`, `sin(γ log n + θ)` comes within every `ε > 0` of every
value `sin φ` for arbitrarily large `n` when `γ ≠ 0`; and `e^{aL} = o(e^{bL})` for `a < b`.
-/

noncomputable section

open Filter Topology Asymptotics

namespace Cvs.Upstream.OscillationBeatsError

/-! ### The sign skeleton along a filter -/

/-! ### Along a scale map `φ → ∞` -/

/-! ### Integer scales `L = log n` -/

/-- The logarithm of `⌈y⌉₊` lies within `y⁻¹` of `log y` for every `y > 0`. -/
theorem abs_log_natCeil_sub_log_le {y : ℝ} (hy : 0 < y) :
    |Real.log (⌈y⌉₊ : ℝ) - Real.log y| ≤ y⁻¹ := by
  have hle : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hlt : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy.le
  have hpos : 0 < (⌈y⌉₊ : ℝ) := hy.trans_le hle
  have hq : 0 < (⌈y⌉₊ : ℝ) / y := div_pos hpos hy
  have hsub : Real.log (⌈y⌉₊ : ℝ) - Real.log y = Real.log ((⌈y⌉₊ : ℝ) / y) :=
    (Real.log_div hpos.ne' hy.ne').symm
  have h0 : 0 ≤ Real.log ((⌈y⌉₊ : ℝ) / y) := Real.log_nonneg ((one_le_div hy).2 hle)
  have h1 : Real.log ((⌈y⌉₊ : ℝ) / y) ≤ (⌈y⌉₊ : ℝ) / y - 1 := Real.log_le_sub_one_of_pos hq
  have h2 : (⌈y⌉₊ : ℝ) / y - 1 ≤ y⁻¹ := by
    rw [div_sub_one hy.ne', div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 hy.le) (by linarith)
  rw [hsub, abs_of_nonneg h0]
  linarith

/-! ### Exponential scales -/

/-- `e^{aL} = o(e^{bL})` as `L → ∞` whenever `a < b`. -/
theorem isLittleO_exp_exp {a b : ℝ} (h : a < b) :
    (fun L : ℝ => Real.exp (a * L)) =o[atTop] fun L => Real.exp (b * L) :=
  Real.isLittleO_exp_comp_exp_comp.2 <|
    (tendsto_id.const_mul_atTop (sub_pos.2 h)).congr fun L => sub_mul b a L

end Cvs.Upstream.OscillationBeatsError
