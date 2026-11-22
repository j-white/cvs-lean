import Mathlib
import Cvs.Zeta.CompletedXiOrderOneGrowth
import Cvs.Zeta.ThetaTailSquared

/-!
# Three constants in the Jensen chain, as numbers

`completedXiJensenGrowth_proved` builds its `C` from `Kr`, `B` and `‖completedXiCore 2‖`,
each behind an existential.  Two of the three do not need one.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex Real

namespace Cvs.Zeta.ZeroCounting.JensenChainConstants
open Cvs.ZeroFree

/-- **`Γ ≤ 1` on `[1,2]`.**  `Γ` is convex there and both endpoints are `1`, so the
endpoints are the maximum — no critical point is looked for. -/
theorem Gamma_le_one_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have hcvx := Real.convexOn_Gamma
  have hmem1 : (1:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have hmem2 : (2:ℝ) ∈ Set.Ioi (0:ℝ) := by norm_num
  have hab : (2 - x) + (x - 1) = 1 := by ring
  have hcomb := hcvx.2 hmem1 hmem2 (by linarith : (0:ℝ) ≤ 2 - x) (by linarith : (0:ℝ) ≤ x - 1)
    hab
  rw [Real.Gamma_one, Real.Gamma_two] at hcomb
  simp only [smul_eq_mul, mul_one] at hcomb
  rw [show 2 - x + (x - 1) * 2 = x by ring] at hcomb
  linarith

/-- **The Gamma growth constant is `1`.**  `exists_Real_Gamma_le_rpow_growth` takes
`C = max 1 (Γ y)` for `y` a maximiser on `[1,2]`; that maximum is `1`. -/
theorem Gamma_le_rpow_growth {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ (x + 1) ^ (x + 1) := by
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hbase : (1:ℝ) ≤ x + 1 := by linarith
  have hpow_one : (1:ℝ) ≤ (x + 1) ^ (x + 1) := Real.one_le_rpow hbase (by linarith)
  by_cases hx2 : x < 2
  · exact le_trans (Gamma_le_one_of_mem_Icc hx hx2.le) hpow_one
  · push_neg at hx2
    set n := Nat.ceil x with hn
    have hn_cast : x ≤ (n : ℝ) := Nat.le_ceil x
    have hn2 : 2 ≤ n := by exact_mod_cast hx2.trans hn_cast
    have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hceil_lt : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
    have hn_nonneg : (0 : ℝ) ≤ n := by positivity
    calc Real.Gamma x
        ≤ Real.Gamma (n : ℝ) :=
          Real.Gamma_strictMonoOn_Ici.monotoneOn (show x ∈ Set.Ici 2 from hx2)
            (show (n : ℝ) ∈ Set.Ici 2 from hn2r) hn_cast
      _ ≤ Real.Gamma ((n : ℝ) + 1) :=
          Real.Gamma_strictMonoOn_Ici.monotoneOn (show (n : ℝ) ∈ Set.Ici 2 from hn2r)
            (show (n : ℝ) + 1 ∈ Set.Ici 2 by change (2:ℝ) ≤ (n : ℝ) + 1; linarith)
            (by linarith)
      _ = (n.factorial : ℝ) := by simpa using Real.Gamma_nat_eq_factorial n
      _ ≤ (n : ℝ) ^ n := by exact_mod_cast n.factorial_le_pow
      _ = (n : ℝ) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (x + 1) ^ (n : ℝ) := Real.rpow_le_rpow hn_nonneg hceil_lt.le hn_nonneg
      _ ≤ (x + 1) ^ (x + 1) := Real.rpow_le_rpow_of_exponent_le hbase hceil_lt.le

/-- **The zeta majorant is `π²/6`.**  `zetaTwoMajorant` is Basel's series with the `n = 0`
term zero by convention. -/
theorem zetaTwoMajorant_eq : Cvs.Zeta.Explicit.Venue.zetaTwoMajorant = Real.pi ^ 2 / 6 := by
  have hsum : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2:ℝ)) (Real.pi ^ 2 / 6) := by
    have h := hasSum_zeta_two
    refine h.congr_fun ?_
    intro n
    rw [Real.rpow_two]
  rw [Cvs.Zeta.Explicit.Venue.zetaTwoMajorant, hsum.tsum_eq]

/-- **The strip constant is a number.**  `exists_norm_completedRiemannZeta₀_le_strip` asks
for a `B` on `−1 ≤ Re s ≤ 2`; `Cvs.Zeta.ThetaTailSquared` proves that statement with one. -/
theorem norm_completedRiemannZeta₀_le_strip_num {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ ≤ 1 / 36.3 :=
  le_of_lt (lt_of_le_of_lt (Cvs.Zeta.ThetaTailSquared.norm_completedRiemannZeta₀_le_sq h1 h2)
    Cvs.Zeta.ThetaTailSquared.const_lt_sq)

end Cvs.Zeta.ZeroCounting.JensenChainConstants
