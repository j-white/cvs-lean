import Mathlib
import Cvs.Upstream.SymmetricMatrixBottom

/-!
# A finite certificate for the two-gap of a symmetric matrix
An even trial vector `w` with `wᵀAw < t‖w‖²`, the odd sector bounded below by `t`, and the even
sector on `w⊥` bounded below by `t` give, for the bottom `lam` of `A`: `lam < t`, the strict odd
gap `lam‖o‖² < oᵀAo`, and a one-dimensional even eigenspace at `lam`. These are exactly the inputs
`Cvs.Upstream.SymmetricMatrixBottom`/`Cvs.Finite.DisplacementIdentity` take from continuous step (a), so step (a) at one scale and mode count becomes
three finite matrix inequalities.
-/

noncomputable section

open Matrix

namespace Cvs.Finite.TwoGapFiniteCertificate

variable {ι : Type*} [Fintype ι]

/-- **The trial level lies strictly above the bottom.** -/
theorem lam_lt_of_trial {A : Matrix ι ι ℝ} {lam t : ℝ}
    (hge : ∀ v, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) {w : ι → ℝ}
    (hw : w ⬝ᵥ (A *ᵥ w) < t * (w ⬝ᵥ w)) : lam < t := by
  have h1 := hge w
  have hww := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' w
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_le_mul_of_nonneg_right hcon hww]

/-- **The strict odd gap from the certificate.** -/
theorem odd_gap_of_cert {A : Matrix ι ι ℝ} {lam t : ℝ} {neg : ι → ι}
    (hge : ∀ v, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) {w : ι → ℝ}
    (hw : w ⬝ᵥ (A *ᵥ w) < t * (w ⬝ᵥ w))
    (hodd : ∀ o : ι → ℝ, (∀ i, o (neg i) = -o i) → t * (o ⬝ᵥ o) ≤ o ⬝ᵥ (A *ᵥ o)) :
    ∀ o : ι → ℝ, (∀ i, o (neg i) = -o i) → o ≠ 0 → lam * (o ⬝ᵥ o) < o ⬝ᵥ (A *ᵥ o) := by
  intro o ho hne
  have hlt := lam_lt_of_trial hge hw
  have hpos : 0 < o ⬝ᵥ o := lt_of_le_of_ne (Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' o)
    (fun h => hne (dotProduct_self_eq_zero.mp h.symm))
  calc lam * (o ⬝ᵥ o) < t * (o ⬝ᵥ o) := mul_lt_mul_of_pos_right hlt hpos
    _ ≤ o ⬝ᵥ (A *ᵥ o) := hodd o ho

/-- **The even eigenspace at the bottom is a line**, from the certificate on `w⊥`. -/
theorem evenline_of_cert {A : Matrix ι ι ℝ} {lam t : ℝ} {neg : ι → ι}
    (hge : ∀ v, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v)) {w : ι → ℝ}
    (hw : w ⬝ᵥ (A *ᵥ w) < t * (w ⬝ᵥ w))
    (hperp : ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → v ⬝ᵥ w = 0 → t * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v))
    {xi : ι → ℝ} (hxi0 : xi ≠ 0) (hxieven : ∀ i, xi (neg i) = xi i)
    (hxi : A *ᵥ xi = lam • xi) :
    ∀ v : ι → ℝ, (∀ i, v (neg i) = v i) → A *ᵥ v = lam • v → ∃ c : ℝ, v = c • xi := by
  have hlt := lam_lt_of_trial hge hw
  -- an even eigenvector orthogonal to `w` vanishes
  have hkill : ∀ u : ι → ℝ, (∀ i, u (neg i) = u i) → u ⬝ᵥ w = 0 → A *ᵥ u = lam • u → u = 0 := by
    intro u hu hperpu hAu
    have h1 := hperp u hu hperpu
    rw [hAu, dotProduct_smul, smul_eq_mul] at h1
    have hnn := Cvs.Upstream.SymmetricMatrixBottom.dotProduct_self_nonneg' u
    have h0 : u ⬝ᵥ u = 0 := by nlinarith
    exact dotProduct_self_eq_zero.mp h0
  have hxiw : xi ⬝ᵥ w ≠ 0 := fun h => hxi0 (hkill xi hxieven h hxi)
  intro v hv hAv
  refine ⟨(v ⬝ᵥ w) / (xi ⬝ᵥ w), ?_⟩
  set c : ℝ := (v ⬝ᵥ w) / (xi ⬝ᵥ w) with hc
  have hu : ∀ i, (v - c • xi) (neg i) = (v - c • xi) i := by
    intro i; simp [hv i, hxieven i]
  have hperpu : (v - c • xi) ⬝ᵥ w = 0 := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hc, div_mul_cancel₀ _ hxiw, sub_self]
  have hAu : A *ᵥ (v - c • xi) = lam • (v - c • xi) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hAv, hxi, smul_sub, smul_comm]
  have := hkill _ hu hperpu hAu
  exact sub_eq_zero.mp this

end Cvs.Finite.TwoGapFiniteCertificate
