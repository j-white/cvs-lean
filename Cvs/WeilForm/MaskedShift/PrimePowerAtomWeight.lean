import Mathlib
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.Zeta.PrimePowerSideTruncated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open Real ArithmeticFunction Cvs.Zeta.Explicit.Weil

namespace Cvs.PrimeOperator

open Cvs.WeilForm.MaskedShift.PrimeAtomRealisation

/-! # B41: the weight at a prime power

`Λ(pʳ)/√(pʳ) = log p · p^(−r/2)` — the development's `wt` agrees with the
venue's `primePowerWeight`.  Mathematically trivial; the work is the
`√` ↔ `rpow` bridge and the `ℕ`/`ℝ` casts.
-/

/-- `√((p:ℝ)^r) = p^(r/2)`. -/
theorem sqrt_pow_eq_rpow {p : ℕ} (r : ℕ) :
    Real.sqrt ((p : ℝ) ^ r) = (p : ℝ) ^ ((r : ℝ) / 2) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [show ((p : ℝ) ^ r) = (p : ℝ) ^ ((r : ℕ) : ℝ) from (Real.rpow_natCast _ _).symm,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hp0]
  ring_nf

/-- **N2.**  `wt (pʳ) = primePowerWeight p r`. -/
theorem wt_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    wt (p ^ r) = primePowerWeight p r := by
  have hp0 : 0 < p := hp.pos
  have hp0' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  -- the von Mangoldt value
  have hL : (vonMangoldt (p ^ r) : ℝ) = Real.log p := by
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
  unfold wt primePowerWeight
  rw [hL, Nat.cast_pow, sqrt_pow_eq_rpow r,
    show (-(r : ℝ) / 2) = -((r : ℝ) / 2) by ring, Real.rpow_neg hp0'.le]
  ring

end Cvs.PrimeOperator
