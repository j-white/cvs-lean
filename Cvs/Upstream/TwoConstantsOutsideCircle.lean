import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two-constants bound outside the unit circle

If `f` is analytic near the closed upper half-plane with `‖f z‖ ≤ M e^{c Im z}`, `‖f t‖ ≤ A` for real `|t| ≥ 1`
and `‖f t‖ ≤ B` for real `|t| ≤ 1`, `0 < A ≤ B`, then `‖f z‖ ≤ √(A·eB) e^{c Im z}` whenever `Im z ≥ 0`, `|z| ≥ 1`.
Phragmén–Lindelöf applies to `f e^{icz} r^{iL/π}`, `r = (z + iδ − 1)/(z + iδ + 1)`; outside the circle `arg r ≤ π/2`.
-/

noncomputable section

open Complex Real Set Filter Topology

namespace Cvs.Upstream.TwoConstantsOutsideCircle

/-- The Möbius quotient `(u − 1)/(u + 1)`. -/
def mob (u : ℂ) : ℂ := (u - 1) / (u + 1)

theorem mob_re (u : ℂ) : (mob u).re = (normSq u - 1) / normSq (u + 1) := by
  unfold mob
  rw [div_re, normSq_apply, normSq_apply]
  simp only [sub_re, one_re, add_re, sub_im, one_im, add_im, sub_zero, add_zero]
  ring

theorem mob_im (u : ℂ) : (mob u).im = 2 * u.im / normSq (u + 1) := by
  unfold mob
  rw [div_im]
  simp only [sub_re, one_re, add_re, sub_im, one_im, add_im, sub_zero, add_zero]
  ring

theorem normSq_add_one_pos {u : ℂ} (hu : 0 < u.im) : 0 < normSq (u + 1) := by
  rw [normSq_apply]; simp only [add_re, one_re, add_im, one_im, add_zero]; nlinarith

theorem mob_im_pos {u : ℂ} (hu : 0 < u.im) : 0 < (mob u).im := by
  rw [mob_im]; exact div_pos (by linarith) (normSq_add_one_pos hu)

/-- `‖exp(iκ log r)‖ = exp(−κ arg r)`. -/
theorem norm_exp_I_mul_log (κ : ℝ) (r : ℂ) : ‖Complex.exp (I * κ * Complex.log r)‖ = Real.exp (-(κ * arg r)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.log_im]

/-- `‖exp(icz)‖ = exp(−c Im z)`. -/
theorem norm_exp_I_mul (c : ℝ) (z : ℂ) : ‖Complex.exp (I * c * z)‖ = Real.exp (-(c * z.im)) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- Outside the unit circle `arg r ≤ π/2`. -/
theorem arg_mob_le {u : ℂ} (hu : 1 ≤ normSq u) : arg (mob u) ≤ π / 2 := by
  refine arg_le_pi_div_two_iff.2 (Or.inl ?_)
  rw [mob_re]; exact div_nonneg (by linarith) (normSq_nonneg _)

/-- Near `π`: if `Re r < 0 < Im r` and `Im r ≤ ε(−Re r)`, then `arg r ≥ π − (π/2)ε`. -/
theorem arg_ge_of_re_neg {r : ℂ} (hre : r.re < 0) (him : 0 < r.im) {ε : ℝ} (h : r.im ≤ ε * (-r.re)) :
    π - π / 2 * ε ≤ arg r := by
  rw [arg_of_re_neg_of_im_nonneg hre him.le]
  have hn : 0 < ‖r‖ := norm_pos_iff.2 fun h0 => by simp [h0] at hre
  set y := (-r).im / ‖r‖ with hy
  have hy0 : y ≤ 0 := by rw [hy, neg_im]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hn.le
  have hre' : -r.re ≤ ‖r‖ := by have := Complex.abs_re_le_norm r; rw [abs_of_neg hre] at this; exact this
  have hyabs : -y ≤ ε := by
    rw [hy, neg_im, neg_div, neg_neg, div_le_iff₀ hn]
    have hε0 : 0 ≤ ε := by
      by_contra hneg; nlinarith [not_le.1 hneg]
    nlinarith
  have hy1 : -y ≤ 1 := by
    rw [hy, neg_im, neg_div, neg_neg, div_le_one hn]
    exact (Complex.abs_im_le_norm r).trans' (le_abs_self _)
  -- `arcsin y ≥ −(π/2)(−y)` by Jordan's inequality
  set θ := π / 2 * (-y) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; have := Real.pi_pos; nlinarith
  have hθ1 : θ ≤ π / 2 := by rw [hθ]; have := Real.pi_pos; nlinarith
  have hs : 2 / π * θ ≤ Real.sin θ := Real.mul_le_sin hθ0 hθ1
  have hsy : 2 / π * θ = -y := by rw [hθ]; field_simp
  have hle : -θ ≤ Real.arcsin y := by
    rw [Real.le_arcsin_iff_sin_le ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩, Real.sin_neg]
    linarith
  have : θ ≤ π / 2 * ε := by rw [hθ]; exact mul_le_mul_of_nonneg_left hyabs (by positivity)
  linarith

/-- The analytic factor `G = f e^{icz} r^{iL/π}`, `r = mob(z + iδ)`. -/
def twoG (f : ℂ → ℂ) (c L δ : ℝ) (z : ℂ) : ℂ :=
  f z * Complex.exp (I * c * z) * Complex.exp (I * ((L / π : ℝ) : ℂ) * Complex.log (mob (z + I * δ)))

theorem im_shift_pos {δ : ℝ} {z : ℂ} (hz : -δ < z.im) : 0 < (z + I * δ).im := by
  simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]; linarith

theorem differentiableOn_twoG {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f {z | -1 < z.im}) (c L : ℝ) {δ : ℝ}
    (hδ1 : δ < 1) : DifferentiableOn ℂ (twoG f c L δ) {z | -δ < z.im} := by
  intro z hz
  have hz' : -δ < z.im := hz
  have hu := im_shift_pos hz'
  have hfz : DifferentiableAt ℂ f z :=
    hf.differentiableAt (isOpen_lt continuous_const continuous_im |>.mem_nhds (show -1 < z.im by linarith))
  have hne : z + I * δ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp only [add_im, one_im, add_zero, zero_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul,
      one_mul] at this
    linarith
  have hmob : DifferentiableAt ℂ (fun w => mob (w + I * δ)) z := by
    unfold mob
    exact ((differentiableAt_id.add_const _).sub_const _).fun_div ((differentiableAt_id.add_const _).add_const _) hne
  have hslit : mob (z + I * δ) ∈ slitPlane := Or.inr (mob_im_pos hu).ne'
  have hlog : DifferentiableAt ℂ (fun w => Complex.log (mob (w + I * δ))) z :=
    hmob.clog hslit
  unfold twoG
  exact ((hfz.mul ((differentiableAt_id.const_mul _).cexp)).mul ((hlog.const_mul _).cexp)).differentiableWithinAt

/-- **Phragmén–Lindelöf on the upper half-plane**: a bounded function analytic near the closed upper half-plane
and bounded by `C` on `ℝ` is bounded by `C` there. -/
theorem norm_le_of_upper {G : ℂ → ℂ} {δ M C : ℝ} (hδ : 0 < δ) (hGd : DifferentiableOn ℂ G {z | -δ < z.im})
    (hGM : ∀ w : ℂ, 0 ≤ w.im → ‖G w‖ ≤ M) (hGR : ∀ t : ℝ, ‖G t‖ ≤ C) {z : ℂ} (hz : 0 ≤ z.im) : ‖G z‖ ≤ C := by
  set g : ℂ → ℂ := fun w => G (I * w) with hg
  have hgd : DiffContOnCl ℂ g {w | 0 < w.re} := by
    refine DifferentiableOn.diffContOnCl ?_
    have hsub : closure {w : ℂ | 0 < w.re} ⊆ {w : ℂ | -δ < (I * w).im} := by
      refine (closure_minimal (s := {w : ℂ | 0 < w.re}) (t := {w : ℂ | 0 ≤ w.re})
        (fun w (hw : 0 < w.re) => le_of_lt hw)
        (isClosed_le continuous_const Complex.continuous_re)).trans fun w (hw : 0 ≤ w.re) => ?_
      show -δ < (I * w).im
      simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]; linarith
    exact (hGd.comp (differentiableOn_id.const_mul I) (fun w hw => hw)).mono hsub
  have hgB : ∀ w : ℂ, 0 ≤ w.re → ‖g w‖ ≤ M := fun w hw => hGM _ (by
    simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add]; exact hw)
  have hexp : ∃ c' < (2 : ℝ), ∃ B₀,
      g =O[Bornology.cobounded ℂ ⊓ 𝓟 {w | 0 < w.re}] fun w => Real.exp (B₀ * ‖w‖ ^ c') := by
    refine ⟨1, by norm_num, 0, Asymptotics.IsBigO.of_bound M ?_⟩
    refine eventually_inf_principal.2 (Eventually.of_forall fun w (hw : 0 < w.re) => ?_)
    simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
    exact hgB w hw.le
  have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖g x‖ :=
    ⟨M, eventually_map.2 ((eventually_ge_atTop 0).mono fun x hx => hgB _ (by simpa using hx))⟩
  have him : ∀ x : ℝ, ‖g (x * I)‖ ≤ C := fun x => by
    have : I * ((x : ℂ) * I) = ((-x : ℝ) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
    simp only [hg, this]; exact hGR _
  have hw : 0 ≤ (-I * z).re := by
    simp only [neg_mul, neg_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, neg_neg]; exact hz
  have hPL := PhragmenLindelof.right_half_plane_of_bounded_on_real hgd hexp hre him hw
  have : I * (-I * z) = z := by ring_nf; rw [I_sq]; ring
  simpa only [hg, this] using hPL

/-- The modulus of `G = f e^{icz} r^{iL/π}`. -/
theorem norm_twoG (f : ℂ → ℂ) (c L δ : ℝ) (w : ℂ) :
    ‖twoG f c L δ w‖ = ‖f w‖ * Real.exp (-(c * w.im)) * Real.exp (-(L / π * arg (mob (w + I * δ)))) := by
  unfold twoG; rw [norm_mul, norm_mul, norm_exp_I_mul, norm_exp_I_mul_log]

/-- On the closed upper half-plane `arg r ≥ 0`, so the phase factor has modulus at most `1`. -/
theorem exp_arg_le_one {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {w : ℂ} (hw : 0 ≤ w.im) :
    Real.exp (-(L / π * arg (mob (w + I * δ)))) ≤ 1 := by
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact mul_nonneg (by positivity) (arg_nonneg_iff.2 (mob_im_pos (im_shift_pos (by linarith))).le)

/-- On `|t| ≤ 1 − η` the phase factor is at most `e^{1 − L}` once `Lδ ≤ η`, `δ² ≤ η/2`. -/
theorem exp_arg_le_real {L δ η : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hδη : δ ≤ η / 2) (hLδ : L * δ ≤ η) {t : ℝ} (ht : |t| ≤ 1 - η) :
    Real.exp (-(L / π * arg (mob ((t : ℂ) + I * δ)))) ≤ Real.exp (1 - L) := by
  set u := (t : ℂ) + I * δ with hu
  have hure : u.re = t := by simp [hu]
  have huim : u.im = δ := by simp [hu]
  have hN := normSq_add_one_pos (show 0 < u.im by rw [huim]; exact hδ)
  have hnu : normSq u = t ^ 2 + δ ^ 2 := by rw [normSq_apply, hure, huim]; ring
  have ht2 : t ^ 2 ≤ (1 - η) ^ 2 := by
    have h0 := abs_nonneg t
    have : |t| ^ 2 ≤ (1 - η) ^ 2 := pow_le_pow_left₀ h0 ht 2
    rwa [sq_abs] at this
  have hδ2 : δ ^ 2 ≤ η / 2 := by nlinarith
  have hre : (mob u).re < 0 := by
    rw [mob_re]
    refine div_neg_of_neg_of_pos ?_ hN
    rw [hnu]; nlinarith
  have hreb : η / normSq (u + 1) ≤ -(mob u).re := by
    rw [mob_re, ← neg_div, div_le_div_iff_of_pos_right hN, hnu]; nlinarith
  have him : (mob u).im = 2 * δ / normSq (u + 1) := by rw [mob_im, huim]
  have hb : (mob u).im ≤ 2 * δ / η * (-(mob u).re) := by
    rw [him]
    calc 2 * δ / normSq (u + 1) = 2 * δ / η * (η / normSq (u + 1)) := by field_simp
      _ ≤ 2 * δ / η * (-(mob u).re) := by gcongr
  have hag := arg_ge_of_re_neg hre (mob_im_pos (by rw [huim]; exact hδ)) hb
  rw [Real.exp_le_exp]
  have hpi := Real.pi_pos
  have h4 : L / π * (π - π / 2 * (2 * δ / η)) = L - L * δ / η := by field_simp
  have h5 : L / π * (π - π / 2 * (2 * δ / η)) ≤ L / π * arg (mob u) :=
    mul_le_mul_of_nonneg_left hag (by positivity)
  have h6 : L * δ / η ≤ 1 := by rw [div_le_one hη]; exact hLδ
  linarith

/-- `A' e^{L/2} = √(A'B')` for `L = log(B'/A')`. -/
theorem mul_exp_half_log {A' B' : ℝ} (hA : 0 < A') (hB : 0 < B') :
    A' * Real.exp (Real.log (B' / A') / 2) = √(A' * B') := by
  have h1 : Real.exp (Real.log (B' / A') / 2) = √(B' / A') := by
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← Real.exp_add, add_halves,
      Real.exp_log (by positivity)]
  rw [h1, ← Real.sqrt_sq hA.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA.le]
  congr 1; field_simp

/-- The bound with `A' = A + ε`, `B' = e(B + ε)`. -/
theorem norm_le_sqrt_mul_eps {f : ℂ → ℂ} {c M A B : ℝ} (hf : DifferentiableOn ℂ f {z | -1 < z.im})
    (hM : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ M * Real.exp (c * z.im))
    (hA : ∀ t : ℝ, 1 ≤ |t| → ‖f t‖ ≤ A) (hB : ∀ t : ℝ, |t| ≤ 1 → ‖f t‖ ≤ B)
    (hA0 : 0 < A) (hAB : A ≤ B) {z : ℂ} (hz : 0 ≤ z.im) (hz1 : 1 ≤ ‖z‖) {ε : ℝ} (hε : 0 < ε) :
    ‖f z‖ ≤ √((A + ε) * (Real.exp 1 * (B + ε))) * Real.exp (c * z.im) := by
  -- continuity at `±1`
  have hc1 : ContinuousAt f (1 : ℂ) := (hf.differentiableAt
    (isOpen_lt continuous_const continuous_im |>.mem_nhds (by simp))).continuousAt
  have hc2 : ContinuousAt f (-1 : ℂ) := (hf.differentiableAt
    (isOpen_lt continuous_const continuous_im |>.mem_nhds (by simp))).continuousAt
  obtain ⟨η₁, hη₁, h₁⟩ := Metric.continuousAt_iff.1 hc1 ε hε
  obtain ⟨η₂, hη₂, h₂⟩ := Metric.continuousAt_iff.1 hc2 ε hε
  set η := min (min η₁ η₂) (1 / 2) with hηd
  have hη0 : 0 < η := lt_min (lt_min hη₁ hη₂) (by norm_num)
  have hη12 : η ≤ 1 / 2 := min_le_right _ _
  have hf1 : ‖f 1‖ ≤ A := by have := hA 1 (by simp); simpa using this
  have hf2 : ‖f (-1)‖ ≤ A := by have := hA (-1) (by simp); simpa using this
  have hnear : ∀ t : ℝ, 1 - η < |t| → ‖f t‖ ≤ A + ε := by
    intro t ht
    rcases le_total 1 |t| with h1 | h1
    · exact (hA t h1).trans (by linarith)
    rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht h1
      have hd : dist (t : ℂ) 1 < η₁ := by
        rw [dist_eq_norm, show (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        have : η ≤ η₁ := (min_le_left _ _).trans (min_le_left _ _)
        linarith
      have := h₁ hd
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le (f t) (f 1)
      linarith
    · rw [abs_of_nonpos h0] at ht h1
      have hd : dist (t : ℂ) (-1) < η₂ := by
        rw [dist_eq_norm, show (t : ℂ) - -1 = ((t + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        have : η ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
        linarith
      have := h₂ hd
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le (f t) (f (-1))
      linarith
  -- the constants
  have hA'0 : 0 < A + ε := by linarith
  have hB'0 : 0 < Real.exp 1 * (B + ε) := mul_pos (Real.exp_pos 1) (by linarith)
  have heB : Real.exp 1 * B ≤ Real.exp 1 * (B + ε) := by nlinarith [Real.exp_pos 1]
  set L := Real.log (Real.exp 1 * (B + ε) / (A + ε)) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hA'0]
    nlinarith [Real.exp_pos 1]
  have hL0 : 0 ≤ L := by linarith
  set δ := η / (L + 2) with hδd
  have hδ0 : 0 < δ := by positivity
  have hδη : δ ≤ η / 2 := by rw [hδd]; gcongr; linarith
  have hδ1 : δ < 1 := by linarith
  have hLδ : L * δ ≤ η := by
    rw [hδd, ← mul_div_assoc, div_le_iff₀ (by linarith)]; nlinarith
  have hGd := differentiableOn_twoG hf c L hδ1
  have hGM : ∀ w : ℂ, 0 ≤ w.im → ‖twoG f c L δ w‖ ≤ M := by
    intro w hw
    rw [norm_twoG]
    have h2 : ‖f w‖ * Real.exp (-(c * w.im)) ≤ M := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]; exact hM w hw
    have h3 := exp_arg_le_one hL0 hδ0 hw
    have h4 : 0 ≤ ‖f w‖ * Real.exp (-(c * w.im)) := by positivity
    calc ‖f w‖ * Real.exp (-(c * w.im)) * Real.exp (-(L / π * arg (mob (w + I * δ))))
        ≤ ‖f w‖ * Real.exp (-(c * w.im)) * 1 := mul_le_mul_of_nonneg_left h3 h4
      _ ≤ M := by rw [mul_one]; exact h2
  have hGR : ∀ t : ℝ, ‖twoG f c L δ t‖ ≤ A + ε := by
    intro t
    rw [norm_twoG]
    simp only [ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one]
    by_cases ht : 1 - η < |t|
    · have h3 := exp_arg_le_one hL0 hδ0 (w := (t : ℂ)) (by simp)
      calc ‖f t‖ * Real.exp (-(L / π * arg (mob (t + I * δ)))) ≤ ‖f t‖ * 1 :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ ≤ A + ε := by rw [mul_one]; exact hnear t ht
    · have ht' : |t| ≤ 1 - η := le_of_not_gt ht
      have hft := hB t (by linarith)
      have hE := exp_arg_le_real hL0 hδ0 hη0 hη12 hδη hLδ ht'
      have hE2 : Real.exp (1 - L) = Real.exp 1 * (A + ε) / (Real.exp 1 * (B + ε)) := by
        rw [Real.exp_sub, hL, Real.exp_log (by positivity)]; field_simp
      have hB0 : 0 ≤ B := by linarith
      calc ‖f t‖ * Real.exp (-(L / π * arg (mob (t + I * δ))))
          ≤ B * Real.exp (1 - L) := mul_le_mul hft hE (Real.exp_pos _).le hB0
        _ = (A + ε) * (Real.exp 1 * B / (Real.exp 1 * (B + ε))) := by rw [hE2]; ring
        _ ≤ (A + ε) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ hA'0.le
            rw [div_le_one hB'0]; exact heB
        _ = A + ε := mul_one _
  have hGz := norm_le_of_upper hδ0 hGd hGM hGR hz
  rw [norm_twoG] at hGz
  have hnz : 1 ≤ normSq (z + I * δ) := by
    have h1 : normSq (z + I * δ) = normSq z + 2 * δ * z.im + δ ^ 2 := by
      rw [normSq_apply, normSq_apply]
      simp only [add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]; ring
    have h2 : 1 ≤ normSq z := by rw [Complex.normSq_eq_norm_sq]; nlinarith
    rw [h1]; nlinarith
  have hag := arg_mob_le hnz
  have hE : Real.exp (-(L / 2)) ≤ Real.exp (-(L / π * arg (mob (z + I * δ)))) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    calc L / π * arg (mob (z + I * δ)) ≤ L / π * (π / 2) := by gcongr
      _ = L / 2 := by field_simp
  have hsq := mul_exp_half_log hA'0 hB'0
  rw [← hL] at hsq
  have hpos : 0 < Real.exp (-(c * z.im)) * Real.exp (-(L / 2)) := by positivity
  have h7 : ‖f z‖ * (Real.exp (-(c * z.im)) * Real.exp (-(L / 2))) ≤ A + ε := by
    calc ‖f z‖ * (Real.exp (-(c * z.im)) * Real.exp (-(L / 2)))
        ≤ ‖f z‖ * Real.exp (-(c * z.im)) * Real.exp (-(L / π * arg (mob (z + I * δ)))) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ A + ε := hGz
  rw [← le_div_iff₀ hpos] at h7
  refine h7.trans (le_of_eq ?_)
  rw [← hsq, Real.exp_neg, Real.exp_neg]
  field_simp

/-- **The two-constants bound outside the unit circle.** -/
theorem norm_le_sqrt_mul {f : ℂ → ℂ} {c M A B : ℝ} (hf : DifferentiableOn ℂ f {z | -1 < z.im})
    (hM : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ M * Real.exp (c * z.im))
    (hA : ∀ t : ℝ, 1 ≤ |t| → ‖f t‖ ≤ A) (hB : ∀ t : ℝ, |t| ≤ 1 → ‖f t‖ ≤ B)
    (hA0 : 0 < A) (hAB : A ≤ B) {z : ℂ} (hz : 0 ≤ z.im) (hz1 : 1 ≤ ‖z‖) :
    ‖f z‖ ≤ √(A * (Real.exp 1 * B)) * Real.exp (c * z.im) := by
  have hT : Tendsto (fun ε : ℝ => √((A + ε) * (Real.exp 1 * (B + ε))) * Real.exp (c * z.im)) (𝓝[>] 0)
      (𝓝 (√(A * (Real.exp 1 * B)) * Real.exp (c * z.im))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have : Continuous fun ε : ℝ => √((A + ε) * (Real.exp 1 * (B + ε))) * Real.exp (c * z.im) := by fun_prop
    simpa using this.tendsto 0
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε =>
    norm_le_sqrt_mul_eps hf hM hA hB hA0 hAB hz hz1 hε)

end Cvs.Upstream.TwoConstantsOutsideCircle

end
