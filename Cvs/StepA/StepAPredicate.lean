import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Connes–van Suijlekom's step (a), as one predicate

    `StepA Q Refl lam eta` : the bottom is attained at `eta`, its eigenspace is the line
    through `eta`, there is a gap above it on `eta`'s orthogonal complement, and `Refl` fixes it

`RH.md §3.23` carries what this is for.
-/

noncomputable section

namespace Cvs.StepA.StepAPredicate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Step (a).**  Simple, isolated, and even — the three things Connes–van Suijlekom assume of
the minimiser, stated on a quadratic functional rather than an operator, because the Weil
multiplier grows like `log|t|` and is not the form of a continuous map. -/
structure StepA (Q : E → ℝ) (Refl : E → E) (lam : ℝ) (eta : E) : Prop where
  /-- `lam` is a lower bound for the Rayleigh quotient. -/
  bottom : ∀ v : E, lam * ‖v‖ ^ 2 ≤ Q v
  /-- and it is attained at `eta`. -/
  attains : Q eta = lam * ‖eta‖ ^ 2
  /-- which is not the zero vector. -/
  nonzero : eta ≠ 0
  /-- Every minimiser lies on the line through `eta`. -/
  simple : ∀ v : E, Q v = lam * ‖v‖ ^ 2 → ∃ c : ℝ, v = c • eta
  /-- Off that line the form is bounded below by something strictly larger. -/
  isolated : ∃ mu : ℝ, lam < mu ∧
    ∀ v : E, (inner ℝ eta v : ℝ) = 0 → mu * ‖v‖ ^ 2 ≤ Q v
  /-- The reflection fixes the minimiser. -/
  even : Refl eta = eta

/-- **The decomposition, backwards.**  Each field of `StepA` is supplied by one named fact, so
what the route still owes is exactly the hypothesis list. -/
theorem stepA_of {Q : E → ℝ} {Refl : E → E} {lam mu : ℝ} {eta : E}
    (hbot : ∀ v : E, lam * ‖v‖ ^ 2 ≤ Q v)
    (hatt : Q eta = lam * ‖eta‖ ^ 2)
    (hne : eta ≠ 0)
    (hsimple : ∀ v : E, Q v = lam * ‖v‖ ^ 2 → ∃ c : ℝ, v = c • eta)
    (hgap : lam < mu)
    (hperp : ∀ v : E, (inner ℝ eta v : ℝ) = 0 → mu * ‖v‖ ^ 2 ≤ Q v)
    (heven : Refl eta = eta) :
    StepA Q Refl lam eta :=
  { bottom := hbot, attains := hatt, nonzero := hne, simple := hsimple,
    isolated := ⟨mu, hgap, hperp⟩, even := heven }

/-- **Simplicity from the gap, when the form is quadratic.**  With the parallelogram structure
available, a minimiser orthogonal to `eta` would have to vanish. -/
theorem simple_of_perp {Q : E → ℝ} {lam mu : ℝ} {eta : E}
    (hgap : lam < mu)
    (hperp : ∀ v : E, (inner ℝ eta v : ℝ) = 0 → mu * ‖v‖ ^ 2 ≤ Q v)
    {v : E} (hv : (inner ℝ eta v : ℝ) = 0) (hmin : Q v = lam * ‖v‖ ^ 2) : v = 0 := by
  by_contra hne
  have h1 := hperp v hv
  rw [hmin] at h1
  have hpos : 0 < ‖v‖ ^ 2 := by
    have : 0 < ‖v‖ := norm_pos_iff.mpr hne
    positivity
  nlinarith

end Cvs.StepA.StepAPredicate
