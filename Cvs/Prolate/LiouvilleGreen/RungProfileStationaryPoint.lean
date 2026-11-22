import Mathlib
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The stationary point of a rung against a profile

The first mode of a rung meets the profile `cos(cm′θ)` where its frequency `a/p` equals `cm′`, and by the frequency
identity of Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow this is the explicit point `θ*² = 1 + (c² − χ)/(c²(m′² − 1))`:
`(a/p)² − (cm′)² = c²(m′² − 1)(θ*² − θ²)/(θ² − 1)`, positive below `θ*` and negative above, with the size of the
mismatch growing linearly in `θ*² − θ²`, the data the window test of Cvs.Upstream.SecondDerivativeWindowTest needs around the stationary point.
-/

namespace Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint

open Real Set Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow

/-- The stationary point squared of the first mode against the profile of order `m′`:
`θ*² = 1 + (c² − χ)/(c²(m′² − 1))`. -/
noncomputable def statSq (c χ : ℝ) (m' : ℕ) : ℝ := 1 + (c ^ 2 - χ) / (c ^ 2 * ((m' : ℝ) ^ 2 - 1))

/-- **The frequency mismatch against the profile**:
`(a/p)² − (cm′)² = c²(m′² − 1)(θ*² − θ²)/(θ² − 1)`. -/
theorem freq_sq_sub_profile {c χ θ : ℝ} {m' : ℕ} (hθ : 1 < θ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hm' : 2 ≤ m') :
    (aP c χ θ / pP θ) ^ 2 - (c * m') ^ 2
      = c ^ 2 * ((m' : ℝ) ^ 2 - 1) * (statSq c χ m' - θ ^ 2) / (θ ^ 2 - 1) := by
  rw [freq_sq hθ hc hχ0 hχc]
  unfold statSq
  have h1 : (0 : ℝ) < θ ^ 2 - 1 := by nlinarith
  have hm : (2 : ℝ) ≤ m' := by exact_mod_cast hm'
  have h2 : (0 : ℝ) < (m' : ℝ) ^ 2 - 1 := by nlinarith
  field_simp
  ring

end Cvs.Prolate.LiouvilleGreen.RungProfileStationaryPoint
