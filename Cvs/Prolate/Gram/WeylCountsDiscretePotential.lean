import Mathlib
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.RegularSolutionEdge

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two Weyl counts behind the discrete potential (eq-cpb Lemma 10)

The rungs `T_j ≤ u` number `x∫_0^1 √((min(u, 1) − t²)₊/(1 − t²)) dt`, and the Dirichlet nodes `σ ≤ c²v` at `a` number
`(c/π)∫_a^1 √((v − t²)₊/(1 − t²)) dt`, both up to `o(c/log c)`, `c = 2πx`.
-/

noncomputable section

open Real Set Filter Topology Finset
open Cvs.Prolate.RegularSolutionEdge (regSol sqC)

namespace Cvs.Prolate.Gram.WeylCountsDiscretePotential
open Cvs.ZeroCounting

/-- The rung Weyl integral `W(u) = ∫_0^1 √((min(u, 1) − t²)₊/(1 − t²)) dt`. -/
def rungWeyl (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, √((min u 1 - t ^ 2) / (1 - t ^ 2))

/-- The Dirichlet Weyl integral at `a`, `Λ_a(v) = (1/π)∫_a^1 √((v − t²)₊/(1 − t²)) dt`. -/
def dirWeyl (a v : ℝ) : ℝ := 1 / π * ∫ t in a..1, √((v - t ^ 2) / (1 - t ^ 2))

/-- The Dirichlet nodes `σ ≤ c²v` of `y_σ(a) = 0`. -/
def dirNodes (c a v : ℝ) : Set ℝ := {σ | regSol (sqC c) σ a = 0} ∩ Iic (c ^ 2 * v)

/-- **Rung counting**: for every `ε > 0`, eventually `|#{j : T_j ≤ u} − xW(u)| ≤ εc/log c` on `[0, 1]`. -/
def RungCount : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∀ u ∈ Icc (0 : ℝ) 1,
    |((univ.filter fun j : Fin x => Cvs.Prolate.Gram.ProlateCellGramHalfUnit.levT x j ≤ u).card : ℝ) - x * rungWeyl u| ≤
      ε * (2 * π * x) / log (2 * π * x)

/-- **Dirichlet node counting**: for every `ε > 0` and `V`, eventually for `a ∈ [½, 3/5]` and `v ∈ [0, V]` the nodes
`σ ≤ c²v` at `a` are finite and number `cΛ_a(v)` up to `εc/log c`. -/
def DirCount : Prop :=
  ∀ ε > 0, ∀ V : ℝ, ∀ᶠ x : ℕ in atTop, ∀ a ∈ Icc (1 / 2 : ℝ) (3 / 5), ∀ v ∈ Icc (0 : ℝ) V,
    (dirNodes (2 * π * x) a v).Finite ∧
      |((dirNodes (2 * π * x) a v).ncard : ℝ) - 2 * π * x * dirWeyl a v| ≤ ε * (2 * π * x) / log (2 * π * x)

end Cvs.Prolate.Gram.WeylCountsDiscretePotential

end
