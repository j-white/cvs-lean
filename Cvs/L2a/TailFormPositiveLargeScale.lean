import Mathlib
import Cvs.L2a.ArchChannelFloorAbove
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The tail form is positive at every large scale

The archimedean floor `floorK x K = log x + c_K − s_K/(πx)²` tends to `+∞`. So if, along `x → ∞`, the
prime channel stays below a fixed `p`, the pole above `−q` with `q` fixed, and the low-mass fraction `ε(x)`
satisfies `ε(x)(floorK x K − archSymbol 0) → 0`, then `LeakageTailThreeChannels`'s margin is eventually positive, and with it the
global form on the leakage tail.
-/

namespace Cvs.L2a.TailFormPositiveLargeScale

open Filter Real Topology MeasureTheory
open Cvs.WeilForm.Archimedean.ArchimedeanUnbounded (archSymbol)
open Cvs.L2a.ArchChannelFloorAbove (floorK)

/-- **The floor diverges**: `floorK x K → ∞` as `x → ∞`. -/
theorem tendsto_floorK (K : ℕ) : Tendsto (fun x => floorK x K) atTop atTop := by
  have hlog : Tendsto (fun x : ℝ => log x) atTop atTop := tendsto_log_atTop
  have hsq : Tendsto (fun x : ℝ => (∑ k ∈ Finset.range K, (1 / 4 + (k : ℝ))) / (π * x) ^ 2)
      atTop (𝓝 0) := by
    apply Tendsto.div_atTop tendsto_const_nhds
    have hpx : Tendsto (fun x : ℝ => π * x) atTop atTop := tendsto_id.const_mul_atTop pi_pos
    exact (tendsto_pow_atTop two_ne_zero).comp hpx
  have h := (hlog.atTop_add (tendsto_const_nhds (x := archSymbol 0
    + ∑ k ∈ Finset.range K, 1 / (1 / 4 + (k : ℝ)) + log (π / (K + 1 / 4))))).atTop_add
    (hsq.neg)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Cvs.L2a.ArchChannelFloorAbove.floorK_eq hx]
  ring

end Cvs.L2a.TailFormPositiveLargeScale
