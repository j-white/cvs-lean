import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rank-two form `B(u,·)² − B(v,·)²`: its bottom is the lower root of the Gram data
For `B ⪰ 0` symmetric, `lamMinus P Q c · B(f,f) ≤ B(u,f)² − B(v,f)² ≤ −lamMinus Q P c · B(f,f)`
(`P = B(u,u)`, `Q = B(v,v)`, `c = B(u,v)`), both bounds attained in `span {u, v}` when `c² < PQ`.
Over a nonnegative background, `k` rank-two terms leave a negative definite subspace of rank `≤ k`.
-/

noncomputable section

open Module

namespace Cvs.StepA.RankTwoBottom

/-! ### The lower root -/

/-- The lower root of `λ² − (P − Q)λ − (PQ − c²)`. -/
def lamMinus (P Q c : ℝ) : ℝ := ((P - Q) - √((P + Q) ^ 2 - 4 * c ^ 2)) / 2

/-! ### The two-sided bound for a positive semidefinite form -/

section Bilin

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {B : LinearMap.BilinForm ℝ E}

end Bilin

/-! ### In a real inner product space -/

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

end Inner

/-! ### At most `k` negative directions over a nonnegative background -/

section Inertia

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Inertia

end Cvs.StepA.RankTwoBottom
