import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.L2a.FullSpanIndexFloor
import Cvs.Prolate.ConverseLevelCount
import Cvs.Prolate.EdgeCentreSign
import Cvs.Prolate.EvenLevelIndexLemma
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.RegularSolutionEdge
import Cvs.Prolate.RungFarMassFloor
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The top-rung depth: an upper zero count gives `c² − lev c (2(x − 1)) ≤ 5c` for `x ≥ 31`

At `χ = c² − Kc` the regular solution has no zero on `[τ₁, 1]`, `τ₁² = 1 − (K + m)/c`, when `m(c(τ − τ₁))² < 2K`; on
`(0, τ₁)` its Prüfer angle with scale `a = √(pq)` obeys `Θ' = ω(1 − (w/2) sin 2Θ)`, `w = a'/q` antitone, so `k` zeros give
`(k − 1)π ≤ Ω̄(τ₁) − w(τ₁)/2` with `Ω̄` elementary. At `K = 5`, `m = 16/5`, `c = 2πx ≥ 62π` this forbids `2x − 2` zeros,
so the top rung has `S_t ≤ 5` and `RungFarMassFloor`'s edge mass `ψ(1)² ≤ 8c∫₁^∞ψ²` holds for it with no hypothesis.
-/

noncomputable section

namespace Cvs.Prolate.TopRungDepthBound

open Real Set Filter Topology MeasureTheory

/-! ### Rising phases -/

/-- A function whose derivative is positive wherever it equals `L` cannot fall back to `L` after leaving it. -/
theorem not_return {Θ : ℝ → ℝ} {α β L : ℝ} (hαβ : α < β) (hc : ContinuousOn Θ (Icc α β))
    (hα : Θ α = L) (hβ : Θ β ≤ L) (hd : ∀ t ∈ Icc α β, Θ t = L → ∃ d, 0 < d ∧ HasDerivAt Θ d t) : False := by
  obtain ⟨d, hd0, hdα⟩ := hd α ⟨le_rfl, hαβ.le⟩ hα
  have hev := Cvs.Prolate.EdgeCentreSign.eventually_mul_deriv_pos (hdα.sub_const L) (by simp [hα]) hd0.ne'
  obtain ⟨t₁, ht₁, ht₁I⟩ := (hev.and (Ioo_mem_nhdsGT hαβ)).exists
  have hL1 : L < Θ t₁ := by
    by_contra h; push Not at h
    have : (Θ t₁ - L) * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hd0.le
    linarith
  set S := Icc t₁ β ∩ Θ ⁻¹' Iic L with hS
  have hsub : Icc t₁ β ⊆ Icc α β := Icc_subset_Icc ht₁I.1.le le_rfl
  have hcl : IsClosed S := (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : S.Nonempty := ⟨β, ⟨ht₁I.2.le, le_rfl⟩, hβ⟩
  have hbdd : BddBelow S := ⟨t₁, fun t ht => ht.1.1⟩
  set s := sInf S with hsdef
  have hs : s ∈ S := hcl.csInf_mem hne hbdd
  have hmin : ∀ t ∈ S, s ≤ t := fun t ht => csInf_le hbdd ht
  obtain ⟨⟨hs1, hs2⟩, hs3⟩ := hs
  have hs3' : Θ s ≤ L := hs3
  obtain ⟨r, hrI, hr⟩ := intermediate_value_Icc' hs1 (hc.mono (Icc_subset_Icc ht₁I.1.le hs2))
    ⟨hs3', hL1.le⟩
  have hrS : r ∈ S := ⟨⟨hrI.1, hrI.2.trans hs2⟩, by simp [hr]⟩
  have hrs : r = s := le_antisymm hrI.2 (hmin r hrS)
  have hθs : Θ s = L := hrs ▸ hr
  have hts : t₁ < s := lt_of_le_of_ne hs1 (fun h => by rw [← h] at hθs; linarith)
  obtain ⟨d', hd'0, hd's⟩ := hd s ⟨ht₁I.1.le.trans hs1, hs2⟩ hθs
  have hev' := Cvs.Prolate.EdgeCentreSign.eventually_mul_deriv_neg (hd's.sub_const L) (by simp [hθs]) hd'0.ne'
  obtain ⟨t, ht, htI⟩ := (hev'.and (Ioo_mem_nhdsLT hts)).exists
  have htL : Θ t ≤ L := by
    by_contra h; push Not at h
    have : 0 < (Θ t - L) * d' := mul_pos (by linarith) hd'0
    linarith
  have := hmin t ⟨⟨htI.1.le, htI.2.le.trans hs2⟩, htL⟩
  linarith [htI.2]

/-- Two zeros of `cos Θ` with `Θ` rising through every zero of `cos Θ` are at least `π` apart in `Θ`. -/
theorem add_pi_le {Θ : ℝ → ℝ} {α β : ℝ} (hαβ : α < β) (hc : ContinuousOn Θ (Icc α β))
    (hα : cos (Θ α) = 0) (hβ : cos (Θ β) = 0)
    (hd : ∀ t ∈ Icc α β, cos (Θ t) = 0 → ∃ d, 0 < d ∧ HasDerivAt Θ d t) : Θ α + π ≤ Θ β := by
  obtain ⟨kα, hkα⟩ := Real.cos_eq_zero_iff.mp hα
  obtain ⟨kβ, hkβ⟩ := Real.cos_eq_zero_iff.mp hβ
  by_contra hlt
  push Not at hlt
  have hk : kβ ≤ kα := by
    by_contra h; push Not at h
    have h1 : (kα : ℝ) + 1 ≤ kβ := by exact_mod_cast h
    rw [hkα, hkβ] at hlt
    nlinarith [Real.pi_pos]
  have hle : Θ β ≤ Θ α := by
    have h1 : (kβ : ℝ) ≤ kα := by exact_mod_cast hk
    rw [hkα, hkβ]; nlinarith [Real.pi_pos]
  exact not_return hαβ hc rfl hle (fun t ht hθ => hd t ht (by rw [hθ]; exact hα))

/-- Along `k` increasing zeros of `cos Θ`, the phase gains at least `π` per step. -/
theorem phase_count {Θ : ℝ → ℝ} {k : ℕ} {w : Fin k → ℝ} (hw : StrictMono w) {α β : ℝ}
    (hc : ContinuousOn Θ (Icc α β)) (hwI : ∀ i, w i ∈ Icc α β) (hz : ∀ i, cos (Θ (w i)) = 0)
    (hd : ∀ t ∈ Icc α β, cos (Θ t) = 0 → ∃ d, 0 < d ∧ HasDerivAt Θ d t) :
    ∀ n (hn : n < k), Θ (w ⟨0, by omega⟩) + n * π ≤ Θ (w ⟨n, hn⟩) := by
  intro n
  induction n with
  | zero => intro hn; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have hlt : w ⟨n, by omega⟩ < w ⟨n + 1, hn⟩ := hw (by simp [Fin.lt_def])
    have hsub : Icc (w ⟨n, by omega⟩) (w ⟨n + 1, hn⟩) ⊆ Icc α β :=
      Icc_subset_Icc (hwI _).1 (hwI _).2
    have h2 := add_pi_le hlt (hc.mono hsub) (hz _) (hz _) (fun t ht => hd t (hsub ht))
    push_cast
    linarith

/-! ### The Prüfer angle -/

open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Upstream.SturmLiouvillePrufer in
/-- **The Prüfer angle**: with `Θ' = ` the rate on `[t₀, t₁]` and `(X, Y)(t₀) = (cos Θ, sin Θ)(t₀)`,
`(X, Y) = (cos Θ, sin Θ)` on `[t₀, t₁]`. -/
theorem prufer_XY {ψ u p q a w : ℝ → ℝ} {t₀ t₁ : ℝ} {Θ : ℝ → ℝ}
    (ha : ∀ t ∈ Icc t₀ t₁, 0 < a t) (hp : ∀ t ∈ Icc t₀ t₁, p t ≠ 0)
    (hapq : ∀ t ∈ Icc t₀ t₁, a t ^ 2 = p t * q t) (hE : ∀ t ∈ Icc t₀ t₁, 0 < energy a ψ u t)
    (hψ : ∀ t ∈ Icc t₀ t₁, HasDerivAt ψ (u t / p t) t) (hu : ∀ t ∈ Icc t₀ t₁, HasDerivAt u (-(q t * ψ t)) t)
    (haw : ∀ t ∈ Icc t₀ t₁, HasDerivAt a (w t * q t) t)
    (hΘ : ∀ t ∈ Icc t₀ t₁, HasDerivAt Θ (rate p a w q ψ u t) t)
    (h0 : X a ψ u t₀ = cos (Θ t₀)) (h0' : Y a ψ u t₀ = sin (Θ t₀)) :
    ∀ t ∈ Icc t₀ t₁, X a ψ u t = cos (Θ t) ∧ Y a ψ u t = sin (Θ t) := by
  set D : ℝ → ℝ := fun t => (X a ψ u t - cos (Θ t)) ^ 2 + (Y a ψ u t - sin (Θ t)) ^ 2 with hD
  have hD' : ∀ t ∈ Icc t₀ t₁, HasDerivAt D 0 t := fun t ht => by
    have hX := hasDerivAt_X (ha t ht) (hp t ht) (hapq t ht) (hE t ht) (hψ t ht) (hu t ht) (haw t ht)
    have hY := hasDerivAt_Y (ha t ht) (hp t ht) (hapq t ht) (hE t ht) (hψ t ht) (hu t ht) (haw t ht)
    have hC : HasDerivAt (fun t => cos (Θ t)) (-sin (Θ t) * rate p a w q ψ u t) t :=
      (Real.hasDerivAt_cos _).comp t (hΘ t ht)
    have hS : HasDerivAt (fun t => sin (Θ t)) (cos (Θ t) * rate p a w q ψ u t) t :=
      (Real.hasDerivAt_sin _).comp t (hΘ t ht)
    have h := ((hX.sub hC).pow 2).add ((hY.sub hS).pow 2)
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.sub_apply]
    ring
  intro t ht
  have hDt : D t = D t₀ := by
    have hsub : uIcc t₀ t ⊆ Icc t₀ t₁ := by
      rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hD' s (hsub hs))
      (intervalIntegrable_const : IntervalIntegrable (fun _ => (0 : ℝ)) MeasureTheory.volume t₀ t)
    rw [intervalIntegral.integral_zero] at this
    linarith
  have hD0 : D t₀ = 0 := by simp only [hD, h0, h0', sub_self]; ring
  rw [hD0] at hDt
  have h1 : 0 ≤ (X a ψ u t - cos (Θ t)) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (Y a ψ u t - sin (Θ t)) ^ 2 := sq_nonneg _
  have e1 : (X a ψ u t - cos (Θ t)) ^ 2 = 0 := by simp only [hD] at hDt; linarith
  have e2 : (Y a ψ u t - sin (Θ t)) ^ 2 = 0 := by simp only [hD] at hDt; linarith
  exact ⟨by linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1],
    by linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2]⟩

/-- **The integrated phase bound**: if `Θ' = ω(1 − (w/2) sin 2Θ)` with `0 ≤ ω ≤ ω̄ = Ω̄'` and `w' ≤ 0` on `[α, β]`, then
`Θ(β) − Θ(α) ≤ Ω̄(β) − Ω̄(α) + (w(β)/4)(cos 2Θ(β) − 1) − (w(α)/4)(cos 2Θ(α) − 1)`. -/
theorem phase_le {Θ ω ωb Ωb w w' : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hΘ : ∀ t ∈ Icc α β, HasDerivAt Θ (ω t * (1 - w t / 2 * sin (2 * Θ t))) t)
    (hw : ∀ t ∈ Icc α β, HasDerivAt w (w' t) t) (hw' : ∀ t ∈ Icc α β, w' t ≤ 0)
    (hΩ : ∀ t ∈ Icc α β, HasDerivAt Ωb (ωb t) t) (hω : ∀ t ∈ Icc α β, 0 ≤ ω t ∧ ω t ≤ ωb t) :
    Θ β - Θ α ≤ Ωb β - Ωb α + w β / 4 * (cos (2 * Θ β) - 1) - w α / 4 * (cos (2 * Θ α) - 1) := by
  set Φ : ℝ → ℝ := fun t => Θ t - Ωb t - w t / 4 * (cos (2 * Θ t) - 1) with hΦ
  set Φ' : ℝ → ℝ := fun t => ω t * (1 - w t / 2 * sin (2 * Θ t)) - ωb t -
    (w' t / 4 * (cos (2 * Θ t) - 1) + w t / 4 * (-sin (2 * Θ t) * (2 * (ω t * (1 - w t / 2 * sin (2 * Θ t))))))
  have hder : ∀ t ∈ Icc α β, HasDerivAt Φ (Φ' t) t := fun t ht => by
    have hc : HasDerivAt (fun t => cos (2 * Θ t)) (-sin (2 * Θ t) * (2 * (ω t * (1 - w t / 2 * sin (2 * Θ t))))) t :=
      (Real.hasDerivAt_cos _).comp t ((hΘ t ht).const_mul 2)
    exact ((hΘ t ht).sub (hΩ t ht)).sub (((hw t ht).div_const 4).mul (hc.sub_const 1))
  have hneg : ∀ t ∈ Icc α β, Φ' t ≤ 0 := fun t ht => by
    obtain ⟨h0, h1⟩ := hω t ht
    have hw't := hw' t ht
    have hcos := Real.cos_le_one (2 * Θ t)
    have e : Φ' t = ω t * (1 - (w t / 2 * sin (2 * Θ t)) ^ 2) - ωb t + w' t / 4 * (1 - cos (2 * Θ t)) := by
      simp only [Φ']; ring
    rw [e]
    have h2 : ω t * (1 - (w t / 2 * sin (2 * Θ t)) ^ 2) ≤ ω t := by
      nlinarith [sq_nonneg (w t / 2 * sin (2 * Θ t))]
    have h3 : w' t / 4 * (1 - cos (2 * Θ t)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  have hanti : AntitoneOn Φ (Icc α β) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := Φ') (convex_Icc α β)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
    · exact (hder t (interior_subset ht)).hasDerivWithinAt
    · exact hneg t (interior_subset ht)
  have := hanti ⟨le_rfl, hαβ⟩ ⟨hαβ, le_rfl⟩ hαβ
  simp only [Φ] at this
  linarith

/-! ### The prolate coefficients at `χ = c² − Kc` -/

/-- `q(s) = c²(1 − s²) − Kc = χ − c²s²` at `χ = c² − Kc`. -/
def qf (c K s : ℝ) : ℝ := c ^ 2 * (1 - s ^ 2) - K * c

/-- The Prüfer scale `a = √(pq)`, `p = 1 − s²`. -/
def af (c K s : ℝ) : ℝ := √((1 - s ^ 2) * qf c K s)

/-- `w = a'/q = −(s/a + c²s(1 − s²)/(aq))`. -/
def wf (c K s : ℝ) : ℝ := -(s / af c K s + c ^ 2 * s * (1 - s ^ 2) / (af c K s * qf c K s))

/-- The derivative of `w`. -/
def wd (c K s : ℝ) : ℝ :=
  -((af c K s - s * (wf c K s * qf c K s)) / af c K s ^ 2 +
    c ^ 2 * ((1 - 3 * s ^ 2) * (af c K s * qf c K s) -
      s * (1 - s ^ 2) * (wf c K s * qf c K s * qf c K s - 2 * c ^ 2 * s * af c K s)) / (af c K s * qf c K s) ^ 2)

/-- `L(s) = (log(1 + s) − log(1 − s))/2`, so `L' = 1/(1 − s²)`. -/
def Lf (s : ℝ) : ℝ := (Real.log (1 + s) - Real.log (1 - s)) / 2

/-- `M(s) = s/(2(1 − s²)) + L(s)/2`, so `M' = 1/(1 − s²)²`. -/
def Mf (s : ℝ) : ℝ := s / (2 * (1 - s ^ 2)) + Lf s / 2

/-- The frequency majorant `ω̄ = c(1 − u/2 − u²/8)`, `u = K/(c(1 − s²))`. -/
def omb (c K s : ℝ) : ℝ := c - K / (2 * (1 - s ^ 2)) - K ^ 2 / (8 * c * (1 - s ^ 2) ^ 2)

/-- `Ω̄ = cs − (K/2)L − (K²/8c)M`, an antiderivative of `ω̄`. -/
def Omb (c K s : ℝ) : ℝ := c * s - K / 2 * Lf s - K ^ 2 / (8 * c) * Mf s

variable {c K s : ℝ}

/-- `a > 0` where `s² < 1` and `q > 0`. -/
theorem af_pos (hs : s ^ 2 < 1) (hq : 0 < qf c K s) : 0 < af c K s :=
  Real.sqrt_pos.mpr (mul_pos (by linarith) hq)

/-- `a² = pq` where `s² < 1` and `q > 0`. -/
theorem af_sq (hs : s ^ 2 < 1) (hq : 0 < qf c K s) : af c K s ^ 2 = (1 - s ^ 2) * qf c K s :=
  Real.sq_sqrt (mul_pos (by linarith) hq).le

/-- `q' = −2c²s`. -/
theorem hasDerivAt_qf (c K s : ℝ) : HasDerivAt (qf c K) (-(2 * c ^ 2 * s)) s := by
  have h := (((hasDerivAt_pow 2 s).const_sub 1).const_mul (c ^ 2)).sub_const (K * c)
  unfold qf; refine h.congr_deriv ?_; simp; ring

/-- **`a' = wq`**. -/
theorem hasDerivAt_af (hs : s ^ 2 < 1) (hq : 0 < qf c K s) :
    HasDerivAt (af c K) (wf c K s * qf c K s) s := by
  have hp : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
    have := (hasDerivAt_pow 2 s).const_sub 1; refine this.congr_deriv ?_; simp
  have hg := hp.mul (hasDerivAt_qf c K s)
  have hpos : 0 < (1 - s ^ 2) * qf c K s := mul_pos (by linarith) hq
  have h := hg.sqrt hpos.ne'
  have ha := af_pos hs hq
  have ha2 := af_sq hs hq
  refine h.congr_deriv ?_
  unfold wf
  simp only [Pi.mul_apply]
  rw [show √((1 - s ^ 2) * qf c K s) = af c K s from rfl]
  field_simp
  unfold qf at ha2 ⊢
  ring

/-- `w ≤ 0` on `s ≥ 0`. -/
theorem wf_nonpos (hs0 : 0 ≤ s) (hs : s ^ 2 < 1) (hq : 0 < qf c K s) : wf c K s ≤ 0 := by
  have ha := af_pos hs hq
  have hp : 0 ≤ 1 - s ^ 2 := by linarith
  unfold wf
  have : 0 ≤ s / af c K s + c ^ 2 * s * (1 - s ^ 2) / (af c K s * qf c K s) := by positivity
  linarith

/-- **`w' = wd`**. -/
theorem hasDerivAt_wf (hs : s ^ 2 < 1) (hq : 0 < qf c K s) : HasDerivAt (wf c K) (wd c K s) s := by
  have ha := af_pos hs hq
  have haD := hasDerivAt_af hs hq
  have hqD := hasDerivAt_qf c K s
  have h1 := (hasDerivAt_id s).div haD ha.ne'
  have hN : HasDerivAt (fun s : ℝ => c ^ 2 * s * (1 - s ^ 2)) (c ^ 2 * (1 - 3 * s ^ 2)) s := by
    have := ((hasDerivAt_id s).const_mul (c ^ 2)).mul ((hasDerivAt_pow 2 s).const_sub 1)
    refine this.congr_deriv ?_; simp; ring
  have h2 := hN.div (haD.mul hqD) (mul_pos ha hq).ne'
  have h := (h1.add h2).neg
  unfold wf wd
  refine h.congr_deriv ?_
  simp only [id, Pi.mul_apply]
  ring

/-- **`w' ≤ 0`** on `s ≥ 0`, `K ≥ 0`. -/
theorem wd_nonpos (hK : 0 ≤ K) (hc : 0 ≤ c) (hs0 : 0 ≤ s) (hs : s ^ 2 < 1) (hq : 0 < qf c K s) :
    wd c K s ≤ 0 := by
  have ha := af_pos hs hq
  have hw := wf_nonpos hs0 hs hq
  set a := af c K s
  set q := qf c K s with hqdef
  set a1 := wf c K s * q
  have ha1 : a1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw hq.le
  have hp : 0 ≤ 1 - s ^ 2 := by linarith
  have hT1 : 0 ≤ (a - s * a1) / a ^ 2 := div_nonneg (by nlinarith) (by positivity)
  have hnum : 0 ≤ (1 - 3 * s ^ 2) * (a * q) - s * (1 - s ^ 2) * (a1 * q - 2 * c ^ 2 * s * a) := by
    have e : (1 - 3 * s ^ 2) * (a * q) - s * (1 - s ^ 2) * (a1 * q - 2 * c ^ 2 * s * a) =
        a * (q * (1 - s ^ 2) + 2 * s ^ 2 * (K * c)) + s * (1 - s ^ 2) * q * (-a1) := by
      rw [hqdef]; unfold qf; ring
    rw [e]
    have : 0 ≤ s * (1 - s ^ 2) * q := by positivity
    have : 0 ≤ q * (1 - s ^ 2) + 2 * s ^ 2 * (K * c) := by positivity
    nlinarith
  have hT2 : 0 ≤ c ^ 2 * ((1 - 3 * s ^ 2) * (a * q) - s * (1 - s ^ 2) * (a1 * q - 2 * c ^ 2 * s * a)) /
      (a * q) ^ 2 := by positivity
  unfold wd
  linarith

/-- `L' = 1/(1 − s²)`. -/
theorem hasDerivAt_Lf (hs : s ^ 2 < 1) : HasDerivAt Lf (1 / (1 - s ^ 2)) s := by
  have h1 : 0 < 1 + s := by nlinarith
  have h2 : 0 < 1 - s := by nlinarith
  have hl1 := ((hasDerivAt_id s).const_add 1).log h1.ne'
  have hl2 := ((hasDerivAt_id s).const_sub 1).log h2.ne'
  have h := (hl1.sub hl2).div_const 2
  unfold Lf
  refine h.congr_deriv ?_
  have hp : (1 : ℝ) - s ^ 2 ≠ 0 := by nlinarith
  have e : (1 : ℝ) - s ^ 2 = (1 + s) * (1 - s) := by ring
  simp only [id]
  rw [e]
  field_simp
  ring

/-- `M' = 1/(1 − s²)²`. -/
theorem hasDerivAt_Mf (hs : s ^ 2 < 1) : HasDerivAt Mf (1 / (1 - s ^ 2) ^ 2) s := by
  have hp : 0 < 1 - s ^ 2 := by linarith
  have hd : HasDerivAt (fun s : ℝ => 2 * (1 - s ^ 2)) (2 * (-(2 * s))) s := by
    have := ((hasDerivAt_pow 2 s).const_sub 1).const_mul 2
    refine this.congr_deriv ?_; simp
  have h := ((hasDerivAt_id' s).div hd (by positivity)).add ((hasDerivAt_Lf hs).div_const 2)
  unfold Mf
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **`Ω̄' = ω̄`**. -/
theorem hasDerivAt_Omb (hc : c ≠ 0) (hs : s ^ 2 < 1) : HasDerivAt (Omb c K) (omb c K s) s := by
  have hp : 0 < 1 - s ^ 2 := by linarith
  have h := (((hasDerivAt_id' s).const_mul c).sub ((hasDerivAt_Lf hs).const_mul (K / 2))).sub
    ((hasDerivAt_Mf hs).const_mul (K ^ 2 / (8 * c)))
  unfold Omb omb
  refine h.congr_deriv ?_
  field_simp
  try ring

/-- **The frequency majorant**: `0 ≤ a/(1 − s²) ≤ ω̄` where `q > 0`. -/
theorem omega_le_omb (hc : 0 < c) (hK : 0 ≤ K) (hs : s ^ 2 < 1) (hq : 0 < qf c K s) :
    0 ≤ af c K s / (1 - s ^ 2) ∧ af c K s / (1 - s ^ 2) ≤ omb c K s := by
  have hp : 0 < 1 - s ^ 2 := by linarith
  have ha := af_pos hs hq
  have ha2 := af_sq hs hq
  refine ⟨by positivity, ?_⟩
  set u := K / (c * (1 - s ^ 2)) with hu
  have hu0 : 0 ≤ u := by positivity
  have hq' : qf c K s = c ^ 2 * (1 - s ^ 2) * (1 - u) := by
    rw [hu]; unfold qf; field_simp
  have hu1 : u < 1 := by
    have : 0 < c ^ 2 * (1 - s ^ 2) * (1 - u) := hq' ▸ hq
    by_contra h; push Not at h
    have : c ^ 2 * (1 - s ^ 2) * (1 - u) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have hom : omb c K s = c * (1 - u / 2 - u ^ 2 / 8) := by
    rw [hu]; unfold omb; field_simp; try ring
  have hpos : 0 ≤ 1 - u / 2 - u ^ 2 / 8 := by nlinarith
  rw [hom, div_le_iff₀ hp]
  have hsq : af c K s ^ 2 ≤ (c * (1 - u / 2 - u ^ 2 / 8) * (1 - s ^ 2)) ^ 2 := by
    rw [ha2, hq']
    have : 1 - u ≤ (1 - u / 2 - u ^ 2 / 8) ^ 2 := by nlinarith [pow_nonneg hu0 3, pow_nonneg hu0 4]
    have hc2 : 0 ≤ c ^ 2 * (1 - s ^ 2) ^ 2 := by positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ ha.le (by positivity) two_ne_zero).mp hsq

/-! ### No zero beyond `τ₁`: the edge region -/

open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.RegularSolutionEdge

/-- `sqC c r = c²r²`. -/
theorem sqC_apply (c r : ℝ) : sqC c r = c ^ 2 * r ^ 2 := rfl

/-- `τ = √(1 − K/c)`, the turning point of `χ = c² − Kc`. -/
theorem tau_spec (hc : 0 < c) (hK : 0 < K) (hKc : K < c) :
    0 ≤ √(1 - K / c) ∧ √(1 - K / c) ^ 2 = 1 - K / c ∧ √(1 - K / c) < 1 := by
  have h0 : 0 ≤ 1 - K / c := by rw [sub_nonneg, div_le_one hc]; exact hKc.le
  have hsq := Real.sq_sqrt h0
  have hKc' : 0 < K / c := div_pos hK hc
  refine ⟨Real.sqrt_nonneg _, hsq, ?_⟩
  rw [Real.sqrt_lt' one_pos]; linarith

/-- **Beyond the turning point**: `regSol ≥ 1` on `[τ, 1]` and the flux `regU` is `≥ 0` at `τ`. -/
theorem edge_one (hc : 0 < c) (hK : 0 < K) (hKc : K < c) :
    (∀ s ∈ Icc (√(1 - K / c)) 1, 1 ≤ regSol (sqC c) (c ^ 2 - K * c) s) ∧
      0 ≤ regU (sqC c) (c ^ 2 - K * c) (√(1 - K / c)) := by
  obtain ⟨hτ0, hτ2, hτ1⟩ := tau_spec hc hK hKc
  set τ := √(1 - K / c)
  have hQ : ∀ s, τ < s → ∀ r ∈ Icc s 1, c ^ 2 - K * c < sqC c r := fun s hs r hr => by
    rw [sqC_apply]
    have hr2 : τ ^ 2 < r ^ 2 := by nlinarith [hr.1]
    have : c ^ 2 * τ ^ 2 < c ^ 2 * r ^ 2 := mul_lt_mul_of_pos_left hr2 (by positivity)
    rw [hτ2] at this
    have e : c ^ 2 * (1 - K / c) = c ^ 2 - K * c := by field_simp; try ring
    linarith
  have hgt : ∀ s ∈ Ioc τ 1, 1 ≤ regSol (sqC c) (c ^ 2 - K * c) s := fun s hs =>
    Cvs.Prolate.EdgeCentreSign.one_le_regSol_of_lt (sqC c) (by linarith [hs.1]) hs.2 (hQ s hs.1) s ⟨le_rfl, hs.2⟩
  have hτm : -1 < τ := by linarith
  have hev : ∀ᶠ s in 𝓝[>] τ, s ∈ Ioo τ 1 := Ioo_mem_nhdsGT hτ1
  refine ⟨fun s hs => ?_, ?_⟩
  · rcases eq_or_lt_of_le hs.1 with h | h
    · subst h
      have hca := (hasDerivAt_regSol (sqC c) (c ^ 2 - K * c) hτm).continuousAt
      refine ge_of_tendsto (hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi τ))) ?_
      filter_upwards [hev] with r hr using hgt r ⟨hr.1, hr.2.le⟩
    · exact hgt s ⟨h, hs.2⟩
  · have hca := (hasDerivAt_regU (sqC c) (c ^ 2 - K * c) hτm).continuousAt
    refine ge_of_tendsto (hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi τ))) ?_
    filter_upwards [hev] with r hr
    exact (Cvs.Prolate.EdgeCentreSign.regU_pos_of_lt (sqC c) (by linarith [hr.1]) hr.2 (hQ r hr.1)).le

/-- **The near-turning region**: with `τ₁ = √(1 − (K + m)/c)` and `m(c(τ − τ₁))² < 2K`, the regular solution at
`c² − Kc` has no zero on `[τ₁, τ]`. -/
theorem edge_two {m : ℝ} (hc : 0 < c) (hK : 0 < K) (hm : 0 < m) (hKm : K + m < c)
    (hstep : m * (c * (√(1 - K / c) - √(1 - (K + m) / c))) ^ 2 < 2 * K) :
    ∀ z ∈ Icc (√(1 - (K + m) / c)) (√(1 - K / c)), regSol (sqC c) (c ^ 2 - K * c) z ≠ 0 := by
  have hKc : K < c := by linarith
  obtain ⟨hτ0, hτ2, hτ1⟩ := tau_spec hc hK hKc
  obtain ⟨hy1, hU⟩ := edge_one hc hK hKc
  have hK' : 0 < K + m := by linarith
  obtain ⟨hσ0, hσ2, -⟩ := tau_spec hc hK' hKm
  set τ := √(1 - K / c)
  set τ₁ := √(1 - (K + m) / c)
  set y := regSol (sqC c) (c ^ 2 - K * c)
  set U := regU (sqC c) (c ^ 2 - K * c)
  intro z hz hyz
  have hyτ : 1 ≤ y τ := hy1 τ ⟨le_rfl, hτ1.le⟩
  have hzτ : z < τ := lt_of_le_of_ne hz.2 (fun h => by rw [h] at hyz; linarith)
  have hzm : -1 < z := by linarith [hz.1]
  have hcont : ContinuousOn y (Icc z τ) := Cvs.Prolate.EdgeCentreSign.continuousOn_regSol_Icc _ _ hzm
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hzτ.le) hcont
  set M := y s₀
  have hM1 : 1 ≤ M := le_trans hyτ (hmax ⟨hzτ.le, le_rfl⟩)
  have hyM : ∀ r ∈ Icc z τ, y r ≤ M := fun r hr => hmax hr
  set q₁ := m * c
  set ε := K / c
  have hε : 0 < ε := div_pos hK hc
  have hτ₁τ : τ ^ 2 - τ₁ ^ 2 = m / c := by rw [hτ2, hσ2]; ring
  -- facts on the region
  have hI : ∀ r ∈ Icc z τ, 0 ≤ r ∧ -1 < r ∧ r < 1 ∧ ε ≤ 1 - r ^ 2 ∧
      0 ≤ c ^ 2 - K * c - c ^ 2 * r ^ 2 ∧ c ^ 2 - K * c - c ^ 2 * r ^ 2 ≤ q₁ := fun r hr => by
    have hr0 : 0 ≤ r := le_trans hσ0 (le_trans hz.1 hr.1)
    have hrτ : r ^ 2 ≤ τ ^ 2 := by nlinarith [hr.2]
    have hrσ : τ₁ ^ 2 ≤ r ^ 2 := by nlinarith [hz.1, hr.1]
    have e : c ^ 2 - K * c - c ^ 2 * r ^ 2 = c ^ 2 * (τ ^ 2 - r ^ 2) := by rw [hτ2]; simp only [ε]; field_simp; try ring
    refine ⟨hr0, by linarith, by linarith [hr.2], by rw [hτ2] at hrτ; simp only [ε]; linarith, ?_, ?_⟩
    · rw [e]; have := sub_nonneg.mpr hrτ; positivity
    · rw [e]
      have : τ ^ 2 - r ^ 2 ≤ m / c := by linarith
      calc c ^ 2 * (τ ^ 2 - r ^ 2) ≤ c ^ 2 * (m / c) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = q₁ := by simp only [q₁]; field_simp; try ring
  -- the flux bound `−U(r) ≤ q₁ M (τ − r)`
  have hflux : ∀ r ∈ Icc z τ, -U r ≤ q₁ * M * (τ - r) := by
    set φ : ℝ → ℝ := fun r => -U r - q₁ * M * (τ - r)
    have hd : ∀ r ∈ Icc z τ, HasDerivAt φ (-(-((sqC c r - (c ^ 2 - K * c)) * y r)) - q₁ * M * (-1)) r :=
      fun r hr => by
        have h1 := (hasDerivAt_regU (sqC c) (c ^ 2 - K * c) (hI r hr).2.1).neg
        have h2 := ((hasDerivAt_id' r).const_sub τ).const_mul (q₁ * M)
        exact h1.sub h2
    have hmono : MonotoneOn φ (Icc z τ) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc z τ)
        (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
        (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt) (fun r hr => ?_)
      have hr := interior_subset hr
      obtain ⟨-, -, -, -, hq0, hq1⟩ := hI r hr
      rw [sqC_apply]
      have hyr := hyM r hr
      have hq1' : 0 ≤ q₁ := by positivity
      rcases le_or_gt 0 (y r) with h | h
      · have : (c ^ 2 - K * c - c ^ 2 * r ^ 2) * y r ≤ q₁ * M := by
          calc (c ^ 2 - K * c - c ^ 2 * r ^ 2) * y r ≤ q₁ * y r := mul_le_mul_of_nonneg_right hq1 h
            _ ≤ q₁ * M := mul_le_mul_of_nonneg_left hyr hq1'
        nlinarith
      · have : (c ^ 2 - K * c - c ^ 2 * r ^ 2) * y r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0 h.le
        nlinarith
    intro r hr
    have := hmono hr ⟨hzτ.le, le_rfl⟩ hr.2
    simp only [φ, sub_self, mul_zero, sub_zero] at this
    linarith
  -- `y + (q₁ M/2ε)(τ − s)²` is antitone
  set ψ : ℝ → ℝ := fun s => y s + q₁ * M / (2 * ε) * (τ - s) ^ 2
  have hd : ∀ s ∈ Icc z τ, HasDerivAt ψ (regV (sqC c) (c ^ 2 - K * c) s +
      q₁ * M / (2 * ε) * (2 * (τ - s) * (-1))) s := fun s hs => by
    have h1 := hasDerivAt_regSol (sqC c) (c ^ 2 - K * c) (hI s hs).2.1
    have h2 := (((hasDerivAt_id' s).const_sub τ).pow 2).const_mul (q₁ * M / (2 * ε))
    refine (h1.add h2).congr_deriv ?_
    simp
  have hanti : AntitoneOn ψ (Icc z τ) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc z τ)
      (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt) (fun r hr => ?_)
    have hr := interior_subset hr
    obtain ⟨-, hrm, hr1, hεr, -, -⟩ := hI r hr
    have hV := pP_mul_regV (sqC c) (c ^ 2 - K * c) hrm
    have hp : 0 < 1 - r ^ 2 := by linarith
    have hpP : pP r = -(1 - r ^ 2) := by unfold pP; ring
    have hVe : regV (sqC c) (c ^ 2 - K * c) r = -U r / (1 - r ^ 2) := by
      rw [eq_div_iff hp.ne']; rw [hpP] at hV; simp only [U]; linarith
    rw [hVe]
    have hf := hflux r hr
    have hτr : 0 ≤ τ - r := by linarith [hr.2]
    have h0 : 0 ≤ q₁ * M * (τ - r) := by positivity
    have h1 : -U r / (1 - r ^ 2) ≤ q₁ * M * (τ - r) / ε := by
      calc -U r / (1 - r ^ 2) ≤ q₁ * M * (τ - r) / (1 - r ^ 2) := div_le_div_of_nonneg_right hf hp.le
        _ ≤ q₁ * M * (τ - r) / ε := div_le_div_of_nonneg_left h0 hε hεr
    have e : q₁ * M / (2 * ε) * (2 * (τ - r) * (-1)) = -(q₁ * M * (τ - r) / ε) := by
      field_simp
    linarith
  have h := hanti ⟨le_rfl, hzτ.le⟩ hs₀ hs₀.1
  simp only [ψ, hyz, zero_add] at h
  have hsq : (τ - z) ^ 2 ≤ (τ - τ₁) ^ 2 := by nlinarith [hz.1, hz.2]
  have hcoef : q₁ * M / (2 * ε) * (τ - τ₁) ^ 2 = M * (m * (c * (τ - τ₁)) ^ 2 / (2 * K)) := by
    simp only [q₁, ε]; field_simp
  have hlt : m * (c * (τ - τ₁)) ^ 2 / (2 * K) < 1 := by rw [div_lt_one (by positivity)]; exact hstep
  have hq0 : 0 ≤ q₁ * M / (2 * ε) := by positivity
  have h3 : M ≤ q₁ * M / (2 * ε) * (τ - τ₁) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hq0, sq_nonneg (τ - s₀)]
  rw [hcoef] at h3
  nlinarith

/-! ### The zero count -/

/-- A point of the unit circle is `(cos θ, sin θ)`. -/
theorem exists_angle {X Y : ℝ} (h : X ^ 2 + Y ^ 2 = 1) : ∃ θ, cos θ = X ∧ sin θ = Y := by
  have h1 : -1 ≤ X := by nlinarith [sq_nonneg Y, sq_nonneg (X + 1)]
  have h2 : X ≤ 1 := by nlinarith [sq_nonneg Y, sq_nonneg (X - 1)]
  have hs : √(1 - X ^ 2) = |Y| := by rw [show 1 - X ^ 2 = Y ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  rcases le_or_gt 0 Y with hY | hY
  · exact ⟨arccos X, cos_arccos h1 h2, by rw [sin_arccos, hs, abs_of_nonneg hY]⟩
  · exact ⟨-arccos X, by rw [cos_neg, cos_arccos h1 h2], by rw [sin_neg, sin_arccos, hs, abs_of_neg hY]; ring⟩

open Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Upstream.SturmLiouvillePrufer in
/-- **The upper zero count**: with `τ₁ = √(1 − (K + m)/c)` and `m(c(τ − τ₁))² < 2K`, `k ≥ 1` zeros in `(0, 1)` of the
regular solution at `c² − Kc` satisfy `(k − 1)π ≤ Ω̄(τ₁) − w(τ₁)/2`. -/
theorem zero_count {m : ℝ} (hc : 0 < c) (hK : 0 < K) (hm : 0 < m) (hKm : K + m < c)
    (hstep : m * (c * (√(1 - K / c) - √(1 - (K + m) / c))) ^ 2 < 2 * K) {k : ℕ} (hk : 1 ≤ k)
    (hZ : Cvs.Prolate.EvenLevelIndexLemma.HasZeros (sqC c) (c ^ 2 - K * c) k) :
    ((k : ℝ) - 1) * π ≤ Omb c K (√(1 - (K + m) / c)) - wf c K (√(1 - (K + m) / c)) / 2 := by
  have hKc : K < c := by linarith
  obtain ⟨hτ0, hτ2, hτ1⟩ := tau_spec hc hK hKc
  obtain ⟨hy1, -⟩ := edge_one hc hK hKc
  have hK' : 0 < K + m := by linarith
  obtain ⟨hσ0, hσ2, hσ1⟩ := tau_spec hc hK' hKm
  have hnz := edge_two hc hK hm hKm hstep
  set τ := √(1 - K / c)
  set τ₁ := √(1 - (K + m) / c)
  set y := regSol (sqC c) (c ^ 2 - K * c) with hydef
  set U := regU (sqC c) (c ^ 2 - K * c) with hUdef
  obtain ⟨w, hmono, hw01, hz⟩ := hZ
  have hwτ : ∀ i, w i < τ₁ := fun i => by
    by_contra h; push Not at h
    rcases le_or_gt (w i) τ with h' | h'
    · exact hnz (w i) ⟨h, h'⟩ (hz i)
    · have := hy1 (w i) ⟨h'.le, (hw01 i).2.le⟩
      have h0 : y (w i) = 0 := hz i
      linarith
  have hreg : ∀ t ∈ Icc 0 τ₁, -1 < t ∧ t ^ 2 < 1 ∧ 0 < qf c K t := fun t ht => by
    have ht2 : t ^ 2 ≤ τ₁ ^ 2 := by nlinarith [ht.1, ht.2]
    rw [hσ2] at ht2
    have hKmc : 0 < (K + m) / c := div_pos hK' hc
    refine ⟨by linarith [ht.1], by linarith, ?_⟩
    unfold qf
    have h1 : c ^ 2 * ((K + m) / c) ≤ c ^ 2 * (1 - t ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : c ^ 2 * ((K + m) / c) = (K + m) * c := by field_simp
    nlinarith
  have hk0 : 0 < k := hk
  set α := w ⟨0, hk0⟩
  set β := w ⟨k - 1, by omega⟩
  have hwI : ∀ i, w i ∈ Icc α β := fun i =>
    ⟨hmono.monotone (Fin.mk_le_mk.2 (Nat.zero_le _)), hmono.monotone (Fin.mk_le_mk.2 (by omega))⟩
  have hαβ : α ≤ β := (hwI ⟨0, hk0⟩).2
  have hα0 : 0 < α := (hw01 _).1
  have hβ1 : β < τ₁ := hwτ _
  have hsubV : Icc α β ⊆ Ioo 0 τ₁ := fun t ht => ⟨hα0.trans_le ht.1, ht.2.trans_lt hβ1⟩
  have hVreg : ∀ t ∈ Ioo 0 τ₁, -1 < t ∧ t ^ 2 < 1 ∧ 0 < qf c K t := fun t ht => hreg t ⟨ht.1.le, ht.2.le⟩
  set p : ℝ → ℝ := fun t => 1 - t ^ 2 with hpdef
  set u : ℝ → ℝ := fun t => -U t with hudef
  have hψd : ∀ t, -1 < t → t ^ 2 < 1 → HasDerivAt y (u t / p t) t := fun t ht1 ht2 => by
    have h := hasDerivAt_regSol (sqC c) (c ^ 2 - K * c) ht1
    have hV := pP_mul_regV (sqC c) (c ^ 2 - K * c) ht1
    have hp : 0 < 1 - t ^ 2 := by linarith
    refine h.congr_deriv ?_
    simp only [u, p, U]
    rw [eq_div_iff hp.ne']
    unfold pP at hV
    linarith
  have hud : ∀ t, -1 < t → HasDerivAt u (-(qf c K t * y t)) t := fun t ht1 => by
    have h := (hasDerivAt_regU (sqC c) (c ^ 2 - K * c) ht1).neg
    refine h.congr_deriv ?_
    rw [sqC_apply]; unfold qf; ring
  have hE : ∀ t, -1 < t → t < 1 → 0 < af c K t → 0 < energy (af c K) y u t := fun t ht1 ht2 ha => by
    unfold energy
    rcases eq_or_ne (y t) 0 with h0 | h0
    · have hU0 := Cvs.Prolate.EdgeCentreSign.regU_ne_zero_of_regSol_eq_zero (sqC c) (c ^ 2 - K * c) ht1 ht2 h0
      have : 0 < u t ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (neg_ne_zero.mpr hU0)).symm
      rw [h0]; positivity
    · have : 0 < af c K t * y t ^ 2 := by positivity
      have : 0 ≤ u t ^ 2 / af c K t := by positivity
      linarith
  set rateF := rate p (af c K) (wf c K) (qf c K) y u with hrateF
  have hcont : ∀ t ∈ Ioo 0 τ₁, ContinuousAt rateF t := fun t ht => by
    obtain ⟨ht1, ht2, hq⟩ := hVreg t ht
    have ha := af_pos ht2 hq
    have haC := (hasDerivAt_af ht2 hq).continuousAt
    have hwC := (hasDerivAt_wf ht2 hq).continuousAt
    have hqC := (hasDerivAt_qf c K t).continuousAt
    have hyC := (hasDerivAt_regSol (sqC c) (c ^ 2 - K * c) ht1).continuousAt
    have huC := (hasDerivAt_regU (sqC c) (c ^ 2 - K * c) ht1).continuousAt.neg
    have hpC : ContinuousAt p t := by simp only [p]; fun_prop
    have hEt := hE t ht1 (by nlinarith) ha
    have hEC : ContinuousAt (energy (af c K) y u) t := by
      unfold energy
      exact (haC.mul (hyC.pow 2)).add ((huC.pow 2).div haC ha.ne')
    have hp0 : p t ≠ 0 := by simp only [p]; linarith
    rw [hrateF]; unfold rate
    exact (haC.div hpC hp0).add (((hwC.mul hqC).mul (huC.mul hyC)).div (haC.mul hEC) (mul_pos ha hEt).ne')
  have hcontOn : ContinuousOn rateF (Ioo 0 τ₁) := fun t ht => (hcont t ht).continuousWithinAt
  obtain ⟨hα1, hα2, hαq⟩ := hreg α ⟨hα0.le, hβ1.le.trans' hαβ⟩
  have haα := af_pos hα2 hαq
  obtain ⟨Θ₀, hc0, hs0⟩ := exists_angle (X_sq_add_Y_sq (a := af c K) (ψ := y) (u := u) haα
    (hE α hα1 (by nlinarith) haα))
  set Θ : ℝ → ℝ := fun t => Θ₀ + ∫ r in α..t, rateF r with hΘdef
  have hΘ : ∀ t ∈ Icc α β, HasDerivAt Θ (rateF t) t := fun t ht => by
    have hsub : uIcc α t ⊆ Ioo 0 τ₁ := by
      rw [uIcc_of_le ht.1]; exact (Icc_subset_Icc le_rfl ht.2).trans hsubV
    have h := intervalIntegral.integral_hasDerivAt_right ((hcontOn.mono hsub).intervalIntegrable)
      (hcontOn.stronglyMeasurableAtFilter isOpen_Ioo t (hsubV ht)) (hcont t (hsubV ht))
    exact h.const_add Θ₀
  have hΘα : Θ α = Θ₀ := by simp [hΘdef]
  have hfacts : ∀ t ∈ Icc α β, 0 < af c K t ∧ p t ≠ 0 ∧ af c K t ^ 2 = p t * qf c K t ∧
      0 < energy (af c K) y u t ∧ HasDerivAt y (u t / p t) t ∧ HasDerivAt u (-(qf c K t * y t)) t ∧
      HasDerivAt (af c K) (wf c K t * qf c K t) t := fun t ht => by
    obtain ⟨ht1, ht2, hq⟩ := hVreg t (hsubV ht)
    have ha := af_pos ht2 hq
    exact ⟨ha, by simp only [p]; linarith, af_sq ht2 hq, hE t ht1 (by nlinarith) ha, hψd t ht1 ht2, hud t ht1,
      hasDerivAt_af ht2 hq⟩
  have hXY := prufer_XY (fun t ht => (hfacts t ht).1) (fun t ht => (hfacts t ht).2.1)
    (fun t ht => (hfacts t ht).2.2.1) (fun t ht => (hfacts t ht).2.2.2.1) (fun t ht => (hfacts t ht).2.2.2.2.1)
    (fun t ht => (hfacts t ht).2.2.2.2.2.1) (fun t ht => (hfacts t ht).2.2.2.2.2.2) hΘ
    (by rw [hΘα, hc0]) (by rw [hΘα, hs0])
  -- the rate in angle form
  have hrate : ∀ t ∈ Icc α β, rateF t = af c K t / p t * (1 - wf c K t / 2 * sin (2 * Θ t)) := fun t ht => by
    obtain ⟨ha, hp, hapq, hEt, -, -, -⟩ := hfacts t ht
    obtain ⟨hX, hY⟩ := hXY t ht
    rw [Real.sin_two_mul, ← hX, ← hY]
    rw [hrateF]; unfold X Y rate
    have hsa := Real.sq_sqrt ha.le
    have hsE := Real.sq_sqrt hEt.le
    have hsa0 : 0 < √(af c K t) := Real.sqrt_pos.mpr ha
    have hsE0 : 0 < √(energy (af c K) y u t) := Real.sqrt_pos.mpr hEt
    have hq : qf c K t = af c K t ^ 2 / p t := by rw [hapq]; field_simp
    rw [hq]
    field_simp
    rw [hsE]
    ring
  have hpos : ∀ t ∈ Icc α β, cos (Θ t) = 0 → ∃ d, 0 < d ∧ HasDerivAt Θ d t := fun t ht h0 => by
    refine ⟨rateF t, ?_, hΘ t ht⟩
    rw [hrate t ht, Real.sin_two_mul, h0]
    obtain ⟨ha, hp, -⟩ := hfacts t ht
    have : 0 < p t := by simp only [p] at hp ⊢; obtain ⟨-, h2, -⟩ := hVreg t (hsubV ht); linarith
    simp only [mul_zero, sub_zero, mul_one]
    positivity
  have hzc : ∀ i, cos (Θ (w i)) = 0 := fun i => by
    rw [← (hXY (w i) (hwI i)).1]
    unfold X
    rw [show y (w i) = 0 from hz i]; simp
  have hΘc : ContinuousOn Θ (Icc α β) := fun t ht => (hΘ t ht).continuousAt.continuousWithinAt
  have hcount := phase_count hmono hΘc hwI hzc hpos (k - 1) (by omega)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk]; simp
  rw [hcast] at hcount
  -- the integrated bound
  have hle := phase_le (ω := fun t => af c K t / (1 - t ^ 2)) (ωb := omb c K) (Ωb := Omb c K)
    (w := wf c K) (w' := wd c K) hαβ (fun t ht => by rw [← hrate t ht]; exact hΘ t ht)
    (fun t ht => by obtain ⟨-, h2, hq⟩ := hVreg t (hsubV ht); exact hasDerivAt_wf h2 hq)
    (fun t ht => by
      obtain ⟨-, h2, hq⟩ := hVreg t (hsubV ht)
      exact wd_nonpos hK.le hc.le (hsubV ht).1.le h2 hq)
    (fun t ht => by obtain ⟨-, h2, -⟩ := hVreg t (hsubV ht); exact hasDerivAt_Omb hc.ne' h2)
    (fun t ht => by obtain ⟨-, h2, hq⟩ := hVreg t (hsubV ht); exact omega_le_omb hc hK.le h2 hq)
  have hcα : cos (2 * Θ α) = -1 := by rw [Real.cos_two_mul, hzc ⟨0, hk0⟩]; ring
  have hcβ : cos (2 * Θ β) = -1 := by rw [Real.cos_two_mul, hzc ⟨k - 1, by omega⟩]; ring
  rw [hcα, hcβ] at hle
  -- monotonicity on `[0, τ₁]`
  have hOmono : MonotoneOn (Omb c K) (Icc 0 τ₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := omb c K) (convex_Icc 0 τ₁)
      (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨-, h2, -⟩ := hreg t ht; exact (hasDerivAt_Omb hc.ne' h2).continuousAt.continuousWithinAt
    · obtain ⟨-, h2, -⟩ := hreg t (interior_subset ht); exact (hasDerivAt_Omb hc.ne' h2).hasDerivWithinAt
    · obtain ⟨-, h2, hq⟩ := hreg t (interior_subset ht)
      have := omega_le_omb hc hK.le h2 hq; linarith
  have hwanti : AntitoneOn (wf c K) (Icc 0 τ₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := wd c K) (convex_Icc 0 τ₁)
      (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨-, h2, hq⟩ := hreg t ht; exact (hasDerivAt_wf h2 hq).continuousAt.continuousWithinAt
    · obtain ⟨-, h2, hq⟩ := hreg t (interior_subset ht); exact (hasDerivAt_wf h2 hq).hasDerivWithinAt
    · have ht' := interior_subset ht
      obtain ⟨-, h2, hq⟩ := hreg t ht'
      exact wd_nonpos hK.le hc.le ht'.1 h2 hq
  have hI0 : (0 : ℝ) ∈ Icc 0 τ₁ := ⟨le_rfl, hσ0⟩
  have hIτ : τ₁ ∈ Icc 0 τ₁ := ⟨hσ0, le_rfl⟩
  have hIα : α ∈ Icc 0 τ₁ := ⟨hα0.le, hαβ.trans hβ1.le⟩
  have hIβ : β ∈ Icc 0 τ₁ := ⟨hα0.le.trans hαβ, hβ1.le⟩
  have hO0 : Omb c K 0 = 0 := by simp [Omb, Lf, Mf]
  have h1 := hOmono hI0 hIα hα0.le
  have h2 := hOmono hIβ hIτ hβ1.le
  have h3 := hwanti hIβ hIτ hβ1.le
  have h4 : wf c K α ≤ 0 := by
    obtain ⟨-, h2, hq⟩ := hreg α hIα; exact wf_nonpos hα0.le h2 hq
  rw [hO0] at h1
  nlinarith

/-! ### The bound in closed form -/

/-- **The count bound, opened**: `Ω̄(τ₁) − w(τ₁)/2 ≤ c − (K + m)/2 − (K/2)L(τ₁) − K²τ₁/(16(K + m)) +
τ₁(K + 2m)/(2m√(m(K + m)))`. -/
theorem bound_le {m : ℝ} (hc : 0 < c) (hK : 0 < K) (hm : 0 < m) (hKm : K + m < c) :
    Omb c K (√(1 - (K + m) / c)) - wf c K (√(1 - (K + m) / c)) / 2 ≤
      c - (K + m) / 2 - K / 2 * Lf (√(1 - (K + m) / c)) - K ^ 2 * √(1 - (K + m) / c) / (16 * (K + m)) +
        √(1 - (K + m) / c) * (K + 2 * m) / (2 * m * √(m * (K + m))) := by
  have hK' : 0 < K + m := by linarith
  obtain ⟨hσ0, hσ2, hσ1⟩ := tau_spec hc hK' hKm
  set τ₁ := √(1 - (K + m) / c)
  have hy : 0 < (K + m) / c := div_pos hK' hc
  have hy1 : (K + m) / c < 1 := by rw [div_lt_one hc]; exact hKm
  have hp : 1 - τ₁ ^ 2 = (K + m) / c := by rw [hσ2]; ring
  have hL : 0 ≤ Lf τ₁ := by
    unfold Lf
    have : Real.log (1 - τ₁) ≤ Real.log (1 + τ₁) := Real.log_le_log (by linarith) (by linarith)
    linarith
  -- `cτ₁ ≤ c − (K + m)/2`
  have hτ : τ₁ ≤ 1 - (K + m) / c / 2 := by
    have h0 : 0 ≤ 1 - (K + m) / c / 2 := by linarith
    rw [← Real.sqrt_sq h0]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hcτ : c * τ₁ ≤ c - (K + m) / 2 := by
    have := mul_le_mul_of_nonneg_left hτ hc.le
    have e : c * (1 - (K + m) / c / 2) = c - (K + m) / 2 := by field_simp
    linarith
  -- `M(τ₁) ≥ τ₁c/(2(K + m))`
  have hM : K ^ 2 * τ₁ / (16 * (K + m)) ≤ K ^ 2 / (8 * c) * Mf τ₁ := by
    unfold Mf
    rw [hp]
    have e : K ^ 2 / (8 * c) * (τ₁ / (2 * ((K + m) / c))) = K ^ 2 * τ₁ / (16 * (K + m)) := by
      field_simp; ring
    have : 0 ≤ K ^ 2 / (8 * c) * (Lf τ₁ / 2) := by positivity
    nlinarith
  -- `w(τ₁)` in closed form
  have hq : qf c K τ₁ = m * c := by
    unfold qf; rw [hp]; field_simp; ring
  have ha : af c K τ₁ = √(m * (K + m)) := by
    unfold af; rw [hq, hp]; congr 1; field_simp
  have hapos : 0 < √(m * (K + m)) := Real.sqrt_pos.mpr (by positivity)
  have hw : -(wf c K τ₁ / 2) = τ₁ * (K + 2 * m) / (2 * m * √(m * (K + m))) := by
    unfold wf; rw [ha, hq, hp]; field_simp; ring
  unfold Omb
  linarith

/-- `e^{9/2} < 91`. -/
theorem exp_nine_halves_lt : Real.exp (9 / 2) < 91 := by
  have h9 : Real.exp (9 / 2) ^ 2 = Real.exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 1 ^ 9 < (2.7182818286 : ℝ) ^ 9 := pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
  have h3 : Real.exp (9 / 2) ^ 2 < 91 ^ 2 := by rw [h9]; linarith [show (2.7182818286 : ℝ) ^ 9 < 91 ^ 2 by norm_num]
  exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) two_ne_zero).mp h3

/-- **The count at `K = 5`, `m = 16/5`**: for `c ≥ 62π`, `regSol (sqC c) (c² − 5c)` has no `k` zeros in `(0, 1)`
with `(k − 1)π ≥ c − 3π`. -/
theorem not_hasZeros_five {k : ℕ} (hc : 62 * π ≤ c) (hk : c - 3 * π ≤ ((k : ℝ) - 1) * π) (hk1 : 1 ≤ k) :
    ¬Cvs.Prolate.EvenLevelIndexLemma.HasZeros (sqC c) (c ^ 2 - 5 * c) k := by
  intro hZ
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hc0 : 194 < c := by nlinarith
  have hcp : 0 < c := by linarith
  have hKm : (5 : ℝ) + 16 / 5 < c := by linarith
  obtain ⟨hτ0, hτ2, hτ1⟩ := tau_spec (K := 5) hcp (by norm_num) (by linarith)
  obtain ⟨hσ0, hσ2, hσ1⟩ := tau_spec (K := 5 + 16 / 5) hcp (by norm_num) hKm
  set τ := √(1 - 5 / c)
  set τ₁ := √(1 - (5 + 16 / 5) / c)
  have hfrac : (5 + 16 / 5) / c ≤ 41 / 970 := by
    rw [div_le_iff₀ hcp]; nlinarith
  have hσ978 : 0.978 ≤ τ₁ := by nlinarith
  have hττ : τ₁ ≤ τ := by
    have : τ₁ ^ 2 ≤ τ ^ 2 := by
      rw [hσ2, hτ2]; have : 5 / c ≤ (5 + 16 / 5) / c := div_le_div_of_nonneg_right (by norm_num) hcp.le
      linarith
    nlinarith
  -- the near-turning condition
  have hstep : 16 / 5 * (c * (τ - τ₁)) ^ 2 < 2 * 5 := by
    have hd : c * (τ - τ₁) * (τ + τ₁) = 16 / 5 := by
      have : (τ - τ₁) * (τ + τ₁) = τ ^ 2 - τ₁ ^ 2 := by ring
      rw [mul_assoc, this, hτ2, hσ2]; field_simp; ring
    have hs : 1.956 ≤ τ + τ₁ := by linarith
    have hx0 : 0 ≤ c * (τ - τ₁) := mul_nonneg hcp.le (by linarith)
    have : c * (τ - τ₁) ≤ 16 / 5 / 1.956 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    have : (c * (τ - τ₁)) ^ 2 ≤ (16 / 5 / 1.956) ^ 2 := pow_le_pow_left₀ hx0 this 2
    nlinarith
  have hcount : ((k : ℝ) - 1) * π ≤ Omb c 5 τ₁ - wf c 5 τ₁ / 2 :=
    zero_count (m := 16 / 5) hcp (by norm_num) (by norm_num) hKm hstep hk1 hZ
  have hb : Omb c 5 τ₁ - wf c 5 τ₁ / 2 ≤ c - (5 + 16 / 5) / 2 - 5 / 2 * Lf τ₁ -
      5 ^ 2 * τ₁ / (16 * (5 + 16 / 5)) + τ₁ * (5 + 2 * (16 / 5)) / (2 * (16 / 5) * √((16 / 5 : ℝ) * (5 + 16 / 5))) :=
    bound_le (K := 5) (m := 16 / 5) hcp (by norm_num) (by norm_num) hKm
  -- `L(τ₁) ≥ 9/4`
  have hL : 9 / 4 ≤ Lf τ₁ := by
    have h1m : 0 < 1 - τ₁ := by linarith
    have hratio : 91 ≤ (1 + τ₁) / (1 - τ₁) := by
      have e : (1 + τ₁) / (1 - τ₁) = (1 + τ₁) ^ 2 * c / (5 + 16 / 5) := by
        have hp : 1 - τ₁ ^ 2 = (5 + 16 / 5) / c := by rw [hσ2]; ring
        rw [div_eq_div_iff h1m.ne' (by norm_num)]
        have h8 : c * (1 - τ₁ ^ 2) = 5 + 16 / 5 := by rw [hp]; field_simp
        linear_combination (-(1 + τ₁)) * h8
      rw [e, le_div_iff₀ (by norm_num)]
      nlinarith
    unfold Lf
    rw [← Real.log_div (by linarith) h1m.ne']
    have := Real.log_le_log (by positivity) (hratio.trans' exp_nine_halves_lt.le)
    rw [Real.log_exp] at this
    linarith
  have hsq : 5.12 ≤ √((16 / 5 : ℝ) * (5 + 16 / 5)) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  have hwb : τ₁ * (5 + 2 * (16 / 5)) / (2 * (16 / 5) * √((16 / 5 : ℝ) * (5 + 16 / 5))) ≤ 0.348 := by
    rw [div_le_iff₀ (by positivity)]
    have : τ₁ ≤ 1 := hσ1.le
    nlinarith
  have hK2 : 0.186 ≤ (5 : ℝ) ^ 2 * τ₁ / (16 * (5 + 16 / 5)) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  nlinarith

/-! ### Levels -/

/-- **The level floor**: if `m(c(τ − τ₁))² < 2K` and `Ω̄(τ₁) − w(τ₁)/2 < (j − 1)π`, every even level of index `j ≥ 1`
lies at or above `c² − Kc`, so `(c² − χ)/c ≤ K`. -/
theorem le_level {m χ : ℝ} {j : ℕ} (hc : 0 < c) (hK : 0 < K) (hm : 0 < m) (hKm : K + m < c)
    (hstep : m * (c * (√(1 - K / c) - √(1 - (K + m) / c))) ^ 2 < 2 * K)
    (hB : Omb c K (√(1 - (K + m) / c)) - wf c K (√(1 - (K + m) / c)) / 2 < ((j : ℝ) - 1) * π)
    (hj : 1 ≤ j) (hχ : Cvs.Prolate.EvenRungsByIndex.IsLevelIdx c j χ) : c ^ 2 - K * c ≤ χ := by
  refine Cvs.Prolate.ConverseLevelCount.le_of_not_hasZeros (k := j - 1) (fun hZ => ?_) hχ (by omega)
  have h := zero_count hc hK hm hKm hstep (k := j - 1 + 1) (by omega) hZ
  rw [show j - 1 + 1 = j by omega] at h
  linarith

open Cvs.Prolate.EvenRungsByIndex (lev) in
/-- **The top rung is shallow**: at `c = 2πx`, `x ≥ 31`, `S_t = (c² − lev c (2(x − 1)))/c ≤ 5`. -/
theorem top_depth_le_five {x : ℕ} (hx : 31 ≤ x) :
    (2 * π * x) ^ 2 - lev (2 * π * x) (2 * (x - 1)) ≤ 5 * (2 * π * x) := by
  have hpi1 := Real.pi_gt_d2
  have hx' : (31 : ℝ) ≤ x := by exact_mod_cast hx
  have hc : 62 * π ≤ 2 * π * x := by nlinarith
  have hx80 : 80 ≤ 2 * π * x := by nlinarith
  obtain ⟨hex, -⟩ := Cvs.L2a.FullSpanIndexFloor.full_index x hx80 (j := x - 1) (by omega)
  have hχ := Cvs.Prolate.EvenRungsByIndex.lev_spec hex
  have hnot : ¬Cvs.Prolate.EvenLevelIndexLemma.HasZeros (sqC (2 * π * x)) ((2 * π * x) ^ 2 - 5 * (2 * π * x))
      (2 * x - 3 + 1) := by
    refine not_hasZeros_five hc ?_ (by omega)
    have e : ((2 * x - 3 + 1 : ℕ) : ℝ) = 2 * x - 2 := by
      rw [show 2 * x - 3 + 1 = 2 * x - 2 by omega, Nat.cast_sub (by omega)]; push_cast; ring
    rw [e]; nlinarith
  have := Cvs.Prolate.ConverseLevelCount.le_of_not_hasZeros hnot hχ (by omega)
  linarith

open Cvs.Prolate.EvenRungsByIndex (lev rung) in
open Cvs.L2a.AngularProlateTailPositive (psi) in
/-- **The top-rung edge mass at `x ≥ 31`**: `ψ(1)² ≤ 8c∫₁^∞ψ²` for the rung of index `2(x − 1)` at `c = 2πx`. -/
theorem top_edge_mass {x : ℕ} (hx : 31 ≤ x) :
    psi (2 * π * x) (rung (2 * π * x) (2 * (x - 1))) 1 ^ 2 ≤
      8 * (2 * π * x) * ∫ ξ in Ioi 1, psi (2 * π * x) (rung (2 * π * x) (2 * (x - 1))) ξ ^ 2 := by
  have hpi1 := Real.pi_gt_d2
  have hx' : (31 : ℝ) ≤ x := by exact_mod_cast hx
  exact Cvs.Prolate.RungFarMassFloor.top_edge_mass (by nlinarith) (top_depth_le_five hx)

end Cvs.Prolate.TopRungDepthBound
