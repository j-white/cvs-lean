import Mathlib
import Cvs.Prolate.EntireRungProlateEquation
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.LiouvilleGreen.ComplexSymbols
import Cvs.Prolate.LiouvilleGreen.HalfStripPhase
import Cvs.Prolate.LiouvilleGreen.RecessiveSolvesProlate
import Cvs.Prolate.LiouvilleGreen.RecessiveVolterra
import Cvs.Upstream.HalfStripRayIntegrals

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung is twice the real part of a multiple of the recessive solution

On the box `W_a = {|Re z| < a, |Im z| < 1}` the entire rung `H_k`, `H₊` and its reflection `H₋ = conj ∘ H₊ ∘ conj`
solve the prolate equation, so their Wronskians are constant; when `W(H₊, H₋) ≠ 0`, `h_k(t) = Re(2αH₊(t))` on `|t| < a`.
-/

noncomputable section

open Real Set Filter Topology
open Complex (I)
open ComplexConjugate
open Cvs.Upstream.HalfStripRayIntegrals (strip)
open Cvs.Prolate.LiouvilleGreen.ComplexSymbols
open Cvs.Prolate.LiouvilleGreen.HalfStripPhase
open Cvs.Prolate.LiouvilleGreen.RecessiveVolterra
open Cvs.Prolate.LiouvilleGreen.RecessiveSolvesProlate
open Cvs.Prolate.EvenRungsByIndex (rung rung₁ muR lev IsLevelIdx rung_spec)

namespace Cvs.Prolate.LiouvilleGreen.RungRecessiveRealPart
open Cvs.ZeroCounting

/-- The box `W_a = {|Re z| < a, |Im z| < 1}`. -/
def box (a : ℝ) : Set ℂ := {z | |z.re| < a ∧ |z.im| < 1}

theorem isOpen_box (a : ℝ) : IsOpen (box a) :=
  (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem convex_box (a : ℝ) : Convex ℝ (box a) := by
  have e : box a = Complex.re ⁻¹' Ioo (-a) a ∩ Complex.im ⁻¹' Ioo (-1) 1 := by
    ext z; simp [box, abs_lt]
  rw [e]
  exact ((convex_Ioo _ _).linear_preimage Complex.reLm).inter ((convex_Ioo _ _).linear_preimage Complex.imLm)

theorem box_subset_strip {a : ℝ} {z : ℂ} (hz : z ∈ box a) : z ∈ strip a :=
  ⟨hz.1, by linarith [neg_abs_le z.im, hz.2]⟩

theorem conj_mem_strip {a : ℝ} {z : ℂ} (hz : z ∈ box a) : conj z ∈ strip a :=
  ⟨by simpa using hz.1, by simp; linarith [le_abs_self z.im, hz.2]⟩

theorem zero_mem_box {a : ℝ} (ha : 0 < a) : (0 : ℂ) ∈ box a := ⟨by simpa using ha, by simp⟩

theorem ofReal_mem_box {a t : ℝ} (ht : |t| < a) : (t : ℂ) ∈ box a := ⟨by simpa using ht, by simp⟩

/-! ### Wronskians -/

/-- The Wronskian `W(f, g) = f g₁ − f₁ g` with fluxes `f₁ = Pf′`, `g₁ = Pg′`. -/
def wr (f f₁ g g₁ : ℂ → ℂ) (z : ℂ) : ℂ := f z * g₁ z - f₁ z * g z

variable {a T c : ℝ}

/-- **Abel's identity**: the Wronskian of two solutions is constant on a convex open set. -/
theorem wr_const {S : Set ℂ} (hS : IsOpen S) (hSc : Convex ℝ S) {f f₁ g g₁ : ℂ → ℂ}
    (hf : IsSolOn c T S f f₁) (hg : IsSolOn c T S g g₁) (hP : ∀ z ∈ S, pP z ≠ 0) {z w : ℂ} (hz : z ∈ S)
    (hw : w ∈ S) : wr f f₁ g g₁ z = wr f f₁ g g₁ w := by
  have hd : ∀ x ∈ S, HasDerivAt (wr f f₁ g g₁) 0 x := by
    intro x hx
    obtain ⟨hf0, hf1⟩ := hf x hx
    obtain ⟨hg0, hg1⟩ := hg x hx
    refine ((hf0.mul hg1).sub (hf1.mul hg0)).congr_deriv ?_
    have := hP x hx
    field_simp
    ring
  refine hS.is_const_of_deriv_eq_zero hSc.isPreconnected
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hd x hx).deriv) hz hw

/-- The pointwise Plücker identity `W(f, g)h = W(h, g)f + W(f, h)g`. -/
theorem plucker (f f₁ g g₁ h h₁ : ℂ → ℂ) (z : ℂ) :
    wr f f₁ g g₁ z * h z = wr h h₁ g g₁ z * f z + wr f f₁ h h₁ z * g z := by
  unfold wr; ring

/-- The reflection `conj ∘ f ∘ conj` of a solution on `conj S` is a solution on `S`. -/
theorem isSolOn_conj {S S' : Set ℂ} (hS : ∀ z ∈ S, conj z ∈ S') {f f₁ : ℂ → ℂ} (hf : IsSolOn c T S' f f₁) :
    IsSolOn c T S (fun z => conj (f (conj z))) (fun z => conj (f₁ (conj z))) := by
  intro z hz
  obtain ⟨h0, h1⟩ := hf (conj z) (hS z hz)
  have hP : conj (pP (conj z)) = pP z := by unfold pP; simp [map_sub, map_pow]
  have hQ : conj (pQ T (conj z)) = pQ T z := by unfold pQ; simp [map_sub, map_pow]
  refine ⟨?_, ?_⟩
  · have := h0.conj_conj
    rw [Complex.conj_conj] at this
    refine this.congr_deriv ?_
    rw [map_div₀, hP]
  · have := h1.conj_conj
    rw [Complex.conj_conj] at this
    refine this.congr_deriv ?_
    simp only [map_mul, map_neg, map_pow, Complex.conj_ofReal]
    rw [hQ]

/-! ### The rung as a solution -/

/-- The flux `PH_k′` of the entire rung. -/
def hk1 (c : ℝ) (k : ℕ) (z : ℂ) : ℂ := pP z * deriv (Cvs.Prolate.EntireRungProlateEquation.Hk c k) z

theorem isSolOn_Hk {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ) (hμ : muR c k ≠ 0) (hχ : lev c k = c ^ 2 * T) {S : Set ℂ}
    (hP : ∀ z ∈ S, pP z ≠ 0) : IsSolOn c T S (Cvs.Prolate.EntireRungProlateEquation.Hk c k) (hk1 c k) := by
  have hF := Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hk
  have hF' : Differentiable ℂ (deriv (Cvs.Prolate.EntireRungProlateEquation.Hk c k)) := fun w =>
    ((hF.differentiableOn.deriv isOpen_univ) w (mem_univ w)).differentiableAt (isOpen_univ.mem_nhds (mem_univ w))
  intro z hz
  refine ⟨((hF z).hasDerivAt).congr_deriv ?_, ?_⟩
  · unfold hk1; field_simp [hP z hz]
  · have h := (hasDerivAt_pP z).mul (hF' z).hasDerivAt
    refine h.congr_deriv ?_
    have hode := Cvs.Prolate.EntireRungProlateEquation.ode_Hk hk hμ z
    rw [hχ] at hode
    unfold pP pQ
    push_cast at hode ⊢
    linear_combination hode

/-! ### The Wronskian of `H₊` and `H₋` at the origin -/

/-- The reflected solution `H₋ = conj ∘ H₊ ∘ conj`. -/
def hM (c T : ℝ) (ε : ℂ → ℂ) (z : ℂ) : ℂ := conj (hP c T ε (conj z))

/-- Its flux. -/
def hM1 (c T : ℝ) (ε : ℂ → ℂ) (z : ℂ) : ℂ := conj (hP1 c T ε (conj z))

theorem phiD_zero (hT : a ^ 2 < T) (hT1 : T ≤ 1) (ha : 0 < a) : phiD T 0 = (√T : ℝ) := by
  have := phiD_ofReal (t := 0) hT hT1 (by simpa using ha)
  simpa using this

/-- **`W(H₊, H₋)(0) ≠ 0`** once `c(1 − B) > V(1 + B)`. -/
theorem wr_zero_ne (ha : 0 < a) (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {ε : ℂ → ℂ} {B : ℝ}
    (hε : Good a ε B) (hW : vV a T * (1 + B) < c * (1 - B)) :
    wr (hP c T ε) (hP1 c T ε) (hM c T ε) (hM1 c T ε) 0 ≠ 0 := by
  have h0s : (0 : ℂ) ∈ strip a := box_subset_strip (zero_mem_box ha)
  have hT0 : 0 < T := lt_of_le_of_lt (sq_nonneg a) hT
  set u := 1 + ε 0
  set L := lam T 0
  set J := flux c T ε 0
  set φ : ℝ := √T
  have hφ := phiD_zero hT hT1 ha
  have hE0 : emph c T 0 = 1 := by unfold emph; rw [Phi_zero]; simp
  have he0 : Complex.exp (I * c * Phi T 0) = 1 := by rw [Phi_zero]; simp
  have hell0 : ell T 0 = 0 := by unfold ell; simp
  have hP0 : pP 0 = 1 := by unfold pP; simp
  have hH : hP c T ε 0 = L * u := by unfold hP; rw [he0]; ring
  have hH1 : hP1 c T ε 0 = L * ((I * c * φ) * u + φ * J) := by
    unfold hP1; rw [he0, hell0, hP0, hE0, hφ]; ring
  have hw : wr (hP c T ε) (hP1 c T ε) (hM c T ε) (hM1 c T ε) 0 =
      (L * conj L) * (u * conj ((I * c * φ) * u + φ * J) - ((I * c * φ) * u + φ * J) * conj u) := by
    unfold wr hM hM1
    rw [map_zero, hH, hH1]
    simp only [map_mul]
    ring
  have hLne : L * conj L ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (by
    rw [Ne, map_eq_zero]; exact Complex.exp_ne_zero _)
  rw [hw]
  refine mul_ne_zero hLne fun h => ?_
  have him := congrArg Complex.im h
  have hu1 : 1 - B ≤ ‖u‖ := by
    have := hε.2 0 h0s
    have h2 : ‖(1 : ℂ)‖ ≤ ‖u‖ + ‖ε 0‖ := by
      calc ‖(1 : ℂ)‖ = ‖u - ε 0‖ := by simp [u]
        _ ≤ _ := norm_sub_le _ _
    rw [norm_one] at h2; linarith
  have hJ : ‖J‖ ≤ vV a T * (1 + B) := by
    have := norm_emph_flux_le hT hT1 hc hε h0s
    rwa [hE0, one_mul] at this
  have hB1 : B < 1 := by
    have := vV_nonneg hT hT1
    have hB0 := B_nonneg hε ha
    nlinarith
  have hφ0 : 0 < φ := Real.sqrt_pos.2 hT0
  -- the imaginary part is `2φ(−c|u|² + Im(u J̄))`
  have e : (u * conj ((I * c * φ) * u + φ * J) - ((I * c * φ) * u + φ * J) * conj u).im =
      2 * φ * (-(c * ‖u‖ ^ 2) + (u * conj J).im) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [e, Complex.zero_im] at him
  have hbd : |(u * conj J).im| ≤ ‖u‖ * ‖J‖ := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have hu0 : 0 < ‖u‖ := by linarith
  have h3 : ‖u‖ * ‖J‖ < c * ‖u‖ ^ 2 := by
    have h4 : ‖J‖ < c * ‖u‖ := by nlinarith
    nlinarith
  have h5 : (u * conj J).im = c * ‖u‖ ^ 2 := by
    have : 2 * φ ≠ 0 := by positivity
    have := (mul_eq_zero.1 him).resolve_left this
    linarith
  linarith [le_abs_self (u * conj J).im]

/-- **The rung is `Re(2αH₊)`** on `|t| < a`. -/
theorem exists_alpha (ha : 0 < a) (hT : a ^ 2 < T) (hT1 : T ≤ 1) (hc : 0 < c) {ε : ℂ → ℂ} {B : ℝ}
    (hε : Good a ε B) (hfix : ∀ z ∈ strip a, ε z = vop c T ε z) (hW : vV a T * (1 + B) < c * (1 - B))
    {k : ℕ} (hk : ∃ χ, IsLevelIdx c k χ) (hμ : muR c k ≠ 0) (hχ : lev c k = c ^ 2 * T) :
    ∃ α : ℂ, ∀ t : ℝ, |t| < a → rung c k t = (2 * α * hP c T ε t).re := by
  have ha1 : a < 1 := by
    have : a ^ 2 < 1 := lt_of_lt_of_le hT hT1
    nlinarith
  have hPb : ∀ z ∈ box a, pP z ≠ 0 := fun z hz => pP_ne hT hT1 (box_subset_strip hz)
  have hsp := (isSolOn_hP hT hT1 hc hε hfix)
  have hsP : IsSolOn c T (box a) (hP c T ε) (hP1 c T ε) := fun z hz => hsp z (box_subset_strip hz)
  have hsM : IsSolOn c T (box a) (hM c T ε) (hM1 c T ε) :=
    isSolOn_conj (fun z hz => conj_mem_strip hz) hsp
  have hsK := isSolOn_Hk (S := box a) hk hμ hχ hPb
  have h0 := zero_mem_box ha
  set W0 := wr (hP c T ε) (hP1 c T ε) (hM c T ε) (hM1 c T ε) 0
  have hW0 : W0 ≠ 0 := wr_zero_ne ha hT hT1 hc hε hW
  set α := wr (Cvs.Prolate.EntireRungProlateEquation.Hk c k) (hk1 c k) (hM c T ε) (hM1 c T ε) 0 / W0
  set β := wr (hP c T ε) (hP1 c T ε) (Cvs.Prolate.EntireRungProlateEquation.Hk c k) (hk1 c k) 0 / W0
  -- `β = conj α`
  obtain ⟨hg, -, -, -, -, -⟩ := rung_spec hk
  have hK0 : Cvs.Prolate.EntireRungProlateEquation.Hk c k 0 = (rung c k 0 : ℂ) := by
    simpa using Cvs.Prolate.EntireRungProlateEquation.Hk_ofReal hk hμ (s := 0) (by norm_num)
  have hK1 : hk1 c k 0 = (rung₁ c k 0 : ℂ) := by
    unfold hk1
    have hd := Cvs.Prolate.EntireRungProlateEquation.deriv_ofReal_eq (Cvs.Prolate.EntireRungProlateEquation.differentiable_Hk hk) (U := Ioo (-1) 1) (t := 0)
      (isOpen_Ioo.mem_nhds (by norm_num)) (fun y hy => Cvs.Prolate.EntireRungProlateEquation.Hk_ofReal hk hμ (Ioo_subset_Icc_self hy))
      (hg 0 (by rw [uIcc_of_le (by norm_num)]; norm_num))
    have hP0 : pP 0 = 1 := by unfold pP; simp
    simpa [hP0] using hd
  have hconj : conj α = β := by
    simp only [α, β, W0, wr, hM, hM1, map_zero, map_div₀, map_sub, map_mul, Complex.conj_conj, hK0, hK1,
      Complex.conj_ofReal]
    rw [show (rung c k 0 : ℂ) * hP1 c T ε 0 - (rung₁ c k 0 : ℂ) * hP c T ε 0 =
      -(hP c T ε 0 * (rung₁ c k 0 : ℂ) - hP1 c T ε 0 * (rung c k 0 : ℂ)) by ring,
      show conj (hP c T ε 0) * hP1 c T ε 0 - conj (hP1 c T ε 0) * hP c T ε 0 =
      -(hP c T ε 0 * conj (hP1 c T ε 0) - hP1 c T ε 0 * conj (hP c T ε 0)) by ring, neg_div_neg_eq]
  refine ⟨α, fun t ht => ?_⟩
  have htb := ofReal_mem_box ht
  have hrep : Cvs.Prolate.EntireRungProlateEquation.Hk c k t = α * hP c T ε t + β * hM c T ε t := by
    have hpl := plucker (hP c T ε) (hP1 c T ε) (hM c T ε) (hM1 c T ε) (Cvs.Prolate.EntireRungProlateEquation.Hk c k) (hk1 c k) t
    rw [wr_const (isOpen_box a) (convex_box a) hsP hsM hPb htb h0,
      wr_const (isOpen_box a) (convex_box a) hsK hsM hPb htb h0,
      wr_const (isOpen_box a) (convex_box a) hsP hsK hPb htb h0] at hpl
    simp only [α, β]
    field_simp
    linear_combination hpl
  have hMt : hM c T ε t = conj (hP c T ε t) := by unfold hM; rw [Complex.conj_ofReal]
  have hKt : Cvs.Prolate.EntireRungProlateEquation.Hk c k t = (rung c k t : ℂ) := Cvs.Prolate.EntireRungProlateEquation.Hk_ofReal hk hμ ⟨by linarith [neg_abs_le t],
    by linarith [le_abs_self t]⟩
  rw [hKt, hMt, ← hconj, ← map_mul] at hrep
  have := congrArg Complex.re hrep
  rw [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at this
  rw [this, mul_assoc, Complex.mul_re]
  simp
  ring

end Cvs.Prolate.LiouvilleGreen.RungRecessiveRealPart

end
