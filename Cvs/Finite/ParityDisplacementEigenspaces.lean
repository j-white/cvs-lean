import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Parity and displacement rank two bound a sector's eigenspaces

For symmetric `G` whose commutator with a parity-odd `Ω` is the rank two `e uᵀ − u eᵀ`, an even
eigenvector killed by both generators is carried by `Ω` to an odd eigenvector at the same value.
A repeated even eigenvalue therefore forces either `Ω`'s kernel vector to be an eigenvector or
an odd eigenvector alongside it, and neither branch can be dropped.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Matrix

namespace Cvs.Finite.ParityDisplacementEigenspaces

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The displacement hypothesis: `Ω G − G Ω = e uᵀ − u eᵀ`, entrywise. -/
def Displacement (om : ι → ℝ) (G : Matrix ι ι ℝ) (e u : ι → ℝ) : Prop :=
  ∀ i j, (om i - om j) * G i j = e i * u j - u i * e j

/-- **The cross-relation.**  An eigenvector's `Ω`-image is moved only along the generators. -/
theorem cross_relation {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u x : ι → ℝ} {lam : ℝ}
    (hd : Displacement om G e u) (hx : G *ᵥ x = lam • x) (i : ι) :
    (G *ᵥ (fun k => om k * x k)) i - lam * (om i * x i)
      = (e ⬝ᵥ x) * u i - (u ⬝ᵥ x) * e i := by
  have hxi : ∑ j, G i j * x j = lam * x i := by
    have h := congrFun hx i
    simpa [Matrix.mulVec, dotProduct] using h
  have hstep : ∑ j, G i j * (om j * x j)
      = om i * (∑ j, G i j * x j)
        - (e i * (∑ j, u j * x j) - u i * (∑ j, e j * x j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-(x j)) * (hd i j)
  simp only [Matrix.mulVec, dotProduct]
  rw [hstep, hxi]
  ring

/-- **The two generators pair with an eigenspace through a rank one map.**  This is what makes
a fatal vector exist in dimension two, where counting functionals does not. -/
theorem det_eq_zero_on_eigenspace {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u x y : ι → ℝ} {lam : ℝ}
    (hsymm : G.IsSymm) (hd : Displacement om G e u)
    (hx : G *ᵥ x = lam • x) (hy : G *ᵥ y = lam • y) :
    (e ⬝ᵥ x) * (u ⬝ᵥ y) - (u ⬝ᵥ x) * (e ⬝ᵥ y) = 0 := by
  have hsym2 : ∀ w : ι → ℝ, w ᵥ* G = G *ᵥ w := by
    intro w; rw [← Matrix.mulVec_transpose, hsymm.eq]
  set w : ι → ℝ := fun k => om k * x k with hwdef
  have hkey : (G *ᵥ w) ⬝ᵥ y = lam * (w ⬝ᵥ y) := by
    rw [← hsym2 w, ← Matrix.dotProduct_mulVec, hy]
    simp only [dotProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcr : ∀ i, (G *ᵥ w) i - lam * w i = (e ⬝ᵥ x) * u i - (u ⬝ᵥ x) * e i :=
    fun i => cross_relation hd hx i
  have hLHS : ∑ i, ((G *ᵥ w) i - lam * w i) * y i = 0 := by
    have hd2 : ∑ i, ((G *ᵥ w) i - lam * w i) * y i
        = (G *ᵥ w) ⬝ᵥ y - lam * (w ⬝ᵥ y) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hd2, hkey]; ring
  have hRHS : ∑ i, ((G *ᵥ w) i - lam * w i) * y i
      = (e ⬝ᵥ x) * (u ⬝ᵥ y) - (u ⬝ᵥ x) * (e ⬝ᵥ y) := by
    have hterm : ∀ i, ((G *ᵥ w) i - lam * w i) * y i
        = (e ⬝ᵥ x) * (u i * y i) - (u ⬝ᵥ x) * (e i * y i) :=
      fun i => by linear_combination (y i) * (hcr i)
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [← hRHS, hLHS]

/-- **The fatal vector's `Ω`-image is an odd eigenvector at the same eigenvalue.**  An even
eigenvector killed by both generators is carried by a parity-odd `Ω` into the odd part of its
own eigenspace. -/
theorem omega_odd_eigenvector {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u x : ι → ℝ} {lam : ℝ}
    {neg : ι → ι} (hodd : ∀ i, om (neg i) = -om i) (hd : Displacement om G e u)
    (hx : G *ᵥ x = lam • x) (heven : ∀ i, x (neg i) = x i)
    (he : e ⬝ᵥ x = 0) (hu : u ⬝ᵥ x = 0) :
    G *ᵥ (fun k => om k * x k) = lam • (fun k => om k * x k)
      ∧ ∀ i, om (neg i) * x (neg i) = -(om i * x i) := by
  refine ⟨funext fun i => ?_, fun i => ?_⟩
  · have h := cross_relation hd hx i
    rw [he, hu] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith [h]
  · rw [hodd i, heven i]; ring

/-- **A repeated even eigenvalue yields a fatal vector**: one killed by both generators. -/
theorem exists_fatal {om : ι → ℝ} {G : Matrix ι ι ℝ} {e u x y : ι → ℝ} {lam : ℝ}
    {neg : ι → ι} (hsymm : G.IsSymm) (hd : Displacement om G e u)
    (hx : G *ᵥ x = lam • x) (hy : G *ᵥ y = lam • y)
    (hxe : ∀ i, x (neg i) = x i) (hye : ∀ i, y (neg i) = y i)
    (hindep : ∀ c : ℝ, y ≠ c • x) (hxne : x ≠ 0) :
    ∃ z : ι → ℝ, z ≠ 0 ∧ G *ᵥ z = lam • z ∧ (∀ i, z (neg i) = z i)
      ∧ e ⬝ᵥ z = 0 ∧ u ⬝ᵥ z = 0 := by
  have hdet : (e ⬝ᵥ x) * (u ⬝ᵥ y) - (u ⬝ᵥ x) * (e ⬝ᵥ y) = 0 :=
    det_eq_zero_on_eigenspace hsymm hd hx hy
  have hcomb : ∀ p q : ℝ, G *ᵥ (p • x - q • y) = lam • (p • x - q • y) := by
    intro p q
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hy]
    rw [smul_sub, smul_comm p lam x, smul_comm q lam y]
  have hpar : ∀ p q : ℝ, ∀ i, (p • x - q • y) (neg i) = (p • x - q • y) i := by
    intro p q i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hxe i, hye i]
  have hdotx : ∀ (v : ι → ℝ) (p q : ℝ),
      v ⬝ᵥ (p • x - q • y) = p * (v ⬝ᵥ x) - q * (v ⬝ᵥ y) := by
    intro v p q
    simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hne : ∀ p q : ℝ, q ≠ 0 → p • x - q • y ≠ 0 := by
    intro p q hq hc
    refine hindep (p / q) ?_
    funext i
    have h := congrFun hc i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hq]
    linear_combination -h
  by_cases hab : e ⬝ᵥ x = 0 ∧ u ⬝ᵥ x = 0
  · exact ⟨x, hxne, hx, hxe, hab.1, hab.2⟩
  · by_cases ha : e ⬝ᵥ x = 0
    · have hb : u ⬝ᵥ x ≠ 0 := fun h => hab ⟨ha, h⟩
      have hc : e ⬝ᵥ y = 0 := by
        have h0 : (u ⬝ᵥ x) * (e ⬝ᵥ y) = 0 := by
          rw [ha] at hdet; linear_combination -hdet
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hb
        · exact h
      exact ⟨(u ⬝ᵥ y) • x - (u ⬝ᵥ x) • y, hne _ _ hb, hcomb _ _, hpar _ _,
        by rw [hdotx]; rw [ha, hc]; ring, by rw [hdotx]; ring⟩
    · exact ⟨(e ⬝ᵥ y) • x - (e ⬝ᵥ x) • y, hne _ _ ha, hcomb _ _, hpar _ _,
        by rw [hdotx]; ring, by rw [hdotx]; linear_combination -hdet⟩

end Cvs.Finite.ParityDisplacementEigenspaces
