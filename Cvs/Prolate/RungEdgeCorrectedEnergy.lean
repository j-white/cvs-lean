import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.Envelope.EdgeValueSoninBound
import Cvs.Prolate.Envelope.EnergyFromReferencePoint
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.SoninFunction
import Cvs.Prolate.SlepianCommutingRelation
import Cvs.Upstream.OneSidedEdgeLimit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge-corrected energy of a rung

For a rung `ψ = ∫ g cos(cξs)`, `u = (ξ² − 1)ψ'`, `0 ≤ χ < c²`, `D = c² − χ` and `ξ₀ > 1`, the corrected energy
`H = E + wψu` satisfies `H(ξ₀) ≤ ψ(1)² [(1 + d₀) a(ξ₀) − w(ξ₀)(ξ₀ − 1) q(ξ₀)]`, `d₀ = 2c²ξ₀(ξ₀ − 1)/D`:
`H − Φ` decreases on `(1, ξ₀]` by Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact, Cvs.Prolate.LiouvilleGreen.SoninFunction and Cvs.Prolate.Envelope.EdgeValueSoninBound, and vanishes at the edge by Cvs.Prolate.Envelope.EnergyFromReferencePoint and Cvs.Upstream.OneSidedEdgeLimit.
-/

namespace Cvs.Prolate.RungEdgeCorrectedEnergy

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.Gram.RungGramFloorAtInfinity

variable {g g₁ g₂ : ℝ → ℝ} {c χ : ℝ}

/-- **The rung's edge bounds**: `ψ(ξ)² ≤ ψ(1)²` and `|u(ξ)| ≤ (ξ − 1) q(ξ) |ψ(1)|` for `ξ ≥ 1`. -/
theorem rung_edge_bounds (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ : ℝ} (hξ : 1 ≤ ξ) :
    psi c g ξ ^ 2 ≤ psi c g 1 ^ 2 ∧ |rungU c g ξ| ≤ (ξ - 1) * qP c χ ξ * |psi c g 1| := by
  obtain ⟨hψ, hv, hode⟩ := psi_system hg hg₁ hg₂c hang
  have hξ' : ξ ∈ Icc 1 ξ := ⟨hξ, le_rfl⟩
  refine ⟨Cvs.Prolate.LiouvilleGreen.SoninFunction.prolate_sq_le_edge hχc hξ' (fun r _ => hψ r) (fun r _ => hv r) (fun r _ => hode r), ?_⟩
  have h := Cvs.Prolate.Envelope.EdgeValueSoninBound.flux_le hχc (fun r _ => hψ r) (fun r _ => hv r) (fun r _ => hode r) hξ'
  unfold rungU pP qP
  exact h

/-- **The edge bound on `ψu`**: `|ψ(ξ) u(ξ)| ≤ ψ(1)² (ξ − 1) q(ξ)` for `ξ ≥ 1`. -/
theorem abs_mul_le_edge (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ : ℝ} (hξ : 1 ≤ ξ) :
    |psi c g ξ * rungU c g ξ| ≤ psi c g 1 ^ 2 * ((ξ - 1) * qP c χ ξ) := by
  obtain ⟨hs, hf⟩ := rung_edge_bounds hχc hg hg₁ hg₂c hang hξ
  have ha : |psi c g ξ| ≤ |psi c g 1| := sq_le_sq.mp hs
  rw [abs_mul]
  calc |psi c g ξ| * |rungU c g ξ| ≤ |psi c g 1| * ((ξ - 1) * qP c χ ξ * |psi c g 1|) :=
        mul_le_mul ha hf (abs_nonneg _) (abs_nonneg _)
    _ = psi c g 1 ^ 2 * ((ξ - 1) * qP c χ ξ) := by rw [← sq_abs (psi c g 1)]; ring

/-- **The small-`ξ` bound**: `E(ξ) ≤ a(ξ) ψ(1)²` for every `ξ > 1`. -/
theorem energy_le_edge (hc : 0 < c) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ : ℝ} (hξ : 1 < ξ) :
    energy (aP c χ) (psi c g) (rungU c g) ξ ≤ aP c χ ξ * psi c g 1 ^ 2 := by
  obtain ⟨hψ, hv, hode⟩ := psi_system hg hg₁ hg₂c hang
  exact Cvs.Prolate.Envelope.EnergyFromReferencePoint.energy_le_edge (Ξ := ξ) (by positivity) hχc ⟨hξ, le_rfl⟩ (fun r _ => hψ r) (fun r _ => hv r)
    (fun r _ => hode r)

/-- **The edge rate**: `w(x)(x − 1) q(x) = (pq)'(x) √(x − 1) / (2 √((x + 1) q(x)))` for `x > 1`. -/
theorem rate_edge_eq {x : ℝ} (hx : 1 < x) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    wP c χ x * (x - 1) * qP c χ x = dP c χ x * √(x - 1) / (2 * √((x + 1) * qP c χ x)) := by
  have hq := qP_pos hx hc2 hχc
  have h1 : 0 < x - 1 := by linarith
  have hR : 0 < (x + 1) * qP c χ x := mul_pos (by linarith) hq
  have ha : aP c χ x = √(x - 1) * √((x + 1) * qP c χ x) := by
    unfold aP pP; rw [← Real.sqrt_mul h1.le]; congr 1; ring
  have hs1 : 0 < √(x - 1) := Real.sqrt_pos.mpr h1
  have hs2 : 0 < √((x + 1) * qP c χ x) := Real.sqrt_pos.mpr hR
  have hsq : √(x - 1) ^ 2 = x - 1 := Real.sq_sqrt h1.le
  unfold wP
  rw [ha]
  set s := √(x - 1)
  set r := √((x + 1) * qP c χ x)
  rw [← hsq]
  field_simp

/-- **The edge term vanishes**: `K (a(x) + (pq)'(x) √(x − 1) / √((x + 1) q(x))) → 0` as `x → 1⁺`. -/
theorem tendsto_edge (hχc : χ < c ^ 2) (K : ℝ) :
    Tendsto (fun x => K * (aP c χ x + dP c χ x * √(x - 1) / √((x + 1) * qP c χ x))) (𝓝[>] 1) (𝓝 0) := by
  have hD : 0 < (1 + 1) * (c ^ 2 * 1 ^ 2 - χ) := by nlinarith
  have hcont : ContinuousAt
      (fun x => K * (aP c χ x + dP c χ x * √(x - 1) / √((x + 1) * qP c χ x))) 1 := by
    unfold aP pP qP dP
    have hA : ContinuousAt (fun x : ℝ => √((x ^ 2 - 1) * (c ^ 2 * x ^ 2 - χ))) 1 := by fun_prop
    have hN : ContinuousAt (fun x : ℝ => 2 * x * (2 * c ^ 2 * x ^ 2 - c ^ 2 - χ) * √(x - 1)) 1 := by
      fun_prop
    have hDen : ContinuousAt (fun x : ℝ => √((x + 1) * (c ^ 2 * x ^ 2 - χ))) 1 := by fun_prop
    exact continuousAt_const.mul (hA.add (hN.div hDen (Real.sqrt_pos.mpr hD).ne'))
  have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 1))
  convert h using 2
  simp [aP, pP]

/-- **The edge-corrected energy**: for a rung with `0 ≤ χ < c²` and `ξ₀ > 1`, with `d₀ = 2c²ξ₀(ξ₀ − 1)/(c² − χ)`,
`E(ξ₀) + w(ξ₀)ψ(ξ₀)u(ξ₀) ≤ ψ(1)² ((1 + d₀) a(ξ₀) − w(ξ₀)(ξ₀ − 1) q(ξ₀))`. -/
theorem edge_corrected_energy_le (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s) (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s)
    (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hang : ∀ s ∈ uIcc (-1 : ℝ) 1, (1 - s ^ 2) * g₂ s - 2 * s * g₁ s - c ^ 2 * s ^ 2 * g s + χ * g s = 0)
    {ξ₀ : ℝ} (h1 : 1 < ξ₀) :
    energy (aP c χ) (psi c g) (rungU c g) ξ₀ + wP c χ ξ₀ * (psi c g ξ₀ * rungU c g ξ₀)
      ≤ psi c g 1 ^ 2 * ((1 + 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ)) * aP c χ ξ₀
        - wP c χ ξ₀ * (ξ₀ - 1) * qP c χ ξ₀) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hD : 0 < c ^ 2 - χ := by linarith
  obtain ⟨hψ, hu, -, -⟩ := rung_system hg hg₁ hg₂c hang
  have hpu : ∀ t, 1 ≤ t → |psi c g t * rungU c g t| ≤ psi c g 1 ^ 2 * ((t - 1) * qP c χ t) :=
    fun t ht => abs_mul_le_edge hχc hg hg₁ hg₂c hang ht
  set ψ := psi c g
  set u := rungU c g
  set B := ψ 1 ^ 2 with hB
  set d₀ := 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) / (c ^ 2 - χ) with hd₀
  have hB0 : 0 ≤ B := sq_nonneg _
  have hd₀0 : 0 ≤ d₀ := by
    have : 0 ≤ ξ₀ - 1 := by linarith
    rw [hd₀]; positivity
  have hd₀D : d₀ * (c ^ 2 - χ) = 2 * c ^ 2 * ξ₀ * (ξ₀ - 1) := by rw [hd₀]; field_simp
  set H := fun t => energy (aP c χ) ψ u t + wP c χ t * (ψ t * u t) with hH
  set Φ := fun t => B * ((1 + d₀) * aP c χ t - wP c χ t * (t - 1) * qP c χ t) with hΦ
  set F' := fun t => wP' c χ t * (ψ t * u t) - B * ((1 + d₀) * (wP c χ t * qP c χ t)
      - (wP' c χ t * (t - 1) * qP c χ t + wP c χ t * qP c χ t + wP c χ t * (t - 1) * (2 * c ^ 2 * t)))
    with hF'
  have hd : ∀ t, 1 < t → HasDerivAt (fun t => H t - Φ t) (F' t) t := by
    intro t ht
    have hHd := hasDerivAt_energy_add (aP_pos ht hc2 hχc) (pP_pos ht).ne' (aP_sq ht hc2 hχc) (hψ t ht)
      (hu t) (hasDerivAt_aP ht hc2 hχc) (hasDerivAt_wP ht hc2 hχc)
    have hq : HasDerivAt (qP c χ) (2 * c ^ 2 * t) t := by
      have h := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).sub_const χ
      have e : qP c χ = fun s => c ^ 2 * s ^ 2 - χ := rfl
      rw [e]; refine h.congr_deriv ?_; ring
    have hΦd := ((((hasDerivAt_aP ht hc2 hχc).const_mul (1 + d₀)).fun_sub
      (((hasDerivAt_wP ht hc2 hχc).fun_mul ((hasDerivAt_id' t).sub_const 1)).fun_mul hq)).const_mul B)
    exact (hHd.fun_sub hΦd).congr_deriv (by simp only [hF']; ring)
  have hneg : ∀ t, 1 < t → t ≤ ξ₀ → F' t ≤ 0 := by
    intro t ht htξ
    have hw' := wP'_nonpos ht hc2 hχ0 hχc
    have hw := wP_pos ht hc2 hχc
    have hqt : c ^ 2 - χ ≤ qP c χ t := by
      unfold qP; have : 1 ≤ t ^ 2 := by nlinarith
      nlinarith
    have hX : 0 ≤ ψ t * u t + B * ((t - 1) * qP c χ t) := by
      have := neg_abs_le (ψ t * u t); have := hpu t ht.le; linarith
    have hY : 2 * c ^ 2 * t * (t - 1) ≤ d₀ * qP c χ t := by
      have h2 : t * (t - 1) ≤ ξ₀ * (ξ₀ - 1) := by nlinarith
      have h3 : d₀ * (c ^ 2 - χ) ≤ d₀ * qP c χ t := mul_le_mul_of_nonneg_left hqt hd₀0
      nlinarith
    have e : F' t = wP' c χ t * (ψ t * u t + B * ((t - 1) * qP c χ t))
        - B * wP c χ t * (d₀ * qP c χ t - 2 * c ^ 2 * t * (t - 1)) := by
      simp only [hF']; ring
    rw [e]
    have k1 : wP' c χ t * (ψ t * u t + B * ((t - 1) * qP c χ t)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hw' hX
    have k2 : 0 ≤ B * wP c χ t * (d₀ * qP c χ t - 2 * c ^ 2 * t * (t - 1)) :=
      mul_nonneg (mul_nonneg hB0 hw.le) (by linarith)
    linarith
  have hle : ∀ x ∈ Ioo 1 ξ₀, H ξ₀ ≤ B * (aP c χ x + dP c χ x * √(x - 1) / √((x + 1) * qP c χ x)) + Φ ξ₀ := by
    intro x hx
    have hanti : AntitoneOn (fun t => H t - Φ t) (Icc x ξ₀) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc x ξ₀)
        (fun t ht => (hd t (by linarith [hx.1, ht.1])).continuousAt.continuousWithinAt)
      · rw [interior_Icc]
        exact fun t ht => (hd t (by linarith [hx.1, ht.1])).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]; intro t ht
        rw [(hd t (by linarith [hx.1, ht.1])).deriv]
        exact hneg t (by linarith [hx.1, ht.1]) ht.2.le
    have hmono := hanti (left_mem_Icc.mpr hx.2.le) (right_mem_Icc.mpr hx.2.le) hx.2.le
    simp only at hmono
    have hx1 : 1 < x := hx.1
    have hE := energy_le_edge hc hχc hg hg₁ hg₂c hang hx1
    have hwx := wP_pos hx1 hc2 hχc
    have hax := aP_pos hx1 hc2 hχc
    have hpux := hpu x hx1.le
    have hr := rate_edge_eq hx1 hc2 hχc
    have k1 : wP c χ x * (ψ x * u x) ≤ wP c χ x * (B * ((x - 1) * qP c χ x)) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hpux) hwx.le
    have k2 : 0 ≤ B * ((1 + d₀) * aP c χ x) := mul_nonneg hB0 (mul_nonneg (by linarith) hax.le)
    have hHx : H x - Φ x ≤ B * (aP c χ x + dP c χ x * √(x - 1) / √((x + 1) * qP c χ x)) := by
      have e : dP c χ x * √(x - 1) / √((x + 1) * qP c χ x) = 2 * (wP c χ x * (x - 1) * qP c χ x) := by
        rw [hr]; field_simp
      rw [e]
      simp only [hH, hΦ]
      nlinarith
    linarith
  exact Cvs.Upstream.OneSidedEdgeLimit.le_of_edge_limit h1 hle (tendsto_edge hχc B)

end Cvs.Prolate.RungEdgeCorrectedEnergy
