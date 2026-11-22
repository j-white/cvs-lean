import Mathlib

/-!
# The prime-power index, reindexed

    (p, r) ↦ pʳ  is injective on primes with `r ≥ 1`

so the operator side's double sum over `(p, r)` is a sum over distinct naturals, which is the
shape `an earlier result` sums in.  RH.md §3.21 carries what is still missing.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Finset

namespace Cvs.WeilForm.PrimePowerReindex

/-- **Distinct prime powers are distinct.**  `p ∣ qˢ` forces `p = q`, and then the exponents
agree by injectivity of `p ^ ·`. -/
theorem primePow_inj {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (h : p ^ r = q ^ s) : p = q ∧ r = s := by
  have hdvd : p ∣ q ^ s := by
    rw [← h]
    exact dvd_pow_self p (by omega)
  have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)
  subst hpq
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

/-- The map, as an injection on the truncation's index set. -/
theorem primePow_injOn (P R : ℕ) :
    Set.InjOn (fun pr : ℕ × ℕ => pr.1 ^ pr.2)
      (((Finset.range (P + 1)).filter Nat.Prime ×ˢ Finset.Icc 1 R) : Finset (ℕ × ℕ)) := by
  intro x hx y hy hxy
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_Icc] at hx hy
  obtain ⟨heq, hreq⟩ := primePow_inj hx.1.2 hy.1.2 hx.2.1 hy.2.1 hxy
  exact Prod.ext heq hreq

/-- **The double sum is a sum over distinct prime powers.**  So the operator side's index set
and `an earlier result`'s differ by a reindexing and nothing else. -/
theorem sum_primePow_eq_image (P R : ℕ) (w : ℕ → ℝ) :
    ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, ∑ r ∈ Finset.Icc 1 R, w (p ^ r)
      = ∑ k ∈ (((Finset.range (P + 1)).filter Nat.Prime ×ˢ Finset.Icc 1 R).image
          (fun pr : ℕ × ℕ => pr.1 ^ pr.2)), w k := by
  classical
  rw [Finset.sum_image (fun x hx y hy hxy => primePow_injOn P R hx hy hxy),
    Finset.sum_product]

end Cvs.WeilForm.PrimePowerReindex
