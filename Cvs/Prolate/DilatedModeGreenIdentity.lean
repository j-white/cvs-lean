import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.ExteriorSpanBernstein
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Route.Visibility.AliasPairThetaKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Green's identity for a pair of dilated prolate modes

`p(θ) = ψ_i(kθ)` solves `p″ = −2θβ_kp′ − A_kp` with `A_k = β_k(c²k²θ² − χ_i)`, so the Wronskian of `ψ_i(kθ)` and
`ψ_j(lθ)` has `W′ = −2θ(β_kp′q − β_lpq′) − (A_k − A_l)pq`; against a weight vanishing at both ends this gives
`∫wpq = ∫(w/D)′W − 2∫(w/D)θ(β_kp′q − β_lpq′)`, `D = A_k − A_l`, and summed over the span `h = Σ b_iψ_i`.
-/

noncomputable section

namespace Cvs.Prolate.DilatedModeGreenIdentity
open Cvs.ZeroCounting

open Real Set Filter Topology MeasureTheory intervalIntegral

/-- **Green's identity for two damped oscillators**: if `p″ = −2θap′ − Ap` and `q″ = −2θbq′ − Bq` on `[α, β]` and
`D = A − B ≠ 0`, then for a weight vanishing at both ends,
`∫wpq = ∫(w/D)′(p′q − pq′) − 2∫(w/D)θ(ap′q − bpq′)`. -/
theorem green_abstract {p pd q qd a b A B D D' w w' : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β) {E : Set ℝ}
    (hE : E.Countable)
    (hp : ∀ θ ∈ Icc α β, HasDerivAt p (pd θ) θ)
    (hpd : ∀ θ ∈ Icc α β, HasDerivAt pd (-2 * θ * a θ * pd θ - A θ * p θ) θ)
    (hq : ∀ θ ∈ Icc α β, HasDerivAt q (qd θ) θ)
    (hqd : ∀ θ ∈ Icc α β, HasDerivAt qd (-2 * θ * b θ * qd θ - B θ * q θ) θ)
    (ha : ContinuousOn a (Icc α β)) (hb : ContinuousOn b (Icc α β))
    (hD : ∀ θ ∈ Icc α β, D θ = A θ - B θ) (hD0 : ∀ θ ∈ Icc α β, D θ ≠ 0)
    (hDd : ∀ θ ∈ Icc α β, HasDerivAt D (D' θ) θ) (hD'c : ContinuousOn D' (Icc α β))
    (hwc : ContinuousOn w (Icc α β)) (hwd : ∀ θ ∈ Ioo α β \ E, HasDerivAt w (w' θ) θ)
    (hwi : IntervalIntegrable w' volume α β) (hwα : w α = 0) (hwβ : w β = 0) :
    IntervalIntegrable (fun θ => (w' θ / D θ - w θ * D' θ / D θ ^ 2) * (pd θ * q θ - p θ * qd θ)
          - 2 * (w θ / D θ) * θ * (a θ * pd θ * q θ - b θ * p θ * qd θ)) volume α β
      ∧ ∫ θ in α..β, w θ * (p θ * q θ)
      = ∫ θ in α..β, ((w' θ / D θ - w θ * D' θ / D θ ^ 2) * (pd θ * q θ - p θ * qd θ)
          - 2 * (w θ / D θ) * θ * (a θ * pd θ * q θ - b θ * p θ * qd θ)) := by
  have hpc : ContinuousOn p (Icc α β) := fun θ h => (hp θ h).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Icc α β) := fun θ h => (hq θ h).continuousAt.continuousWithinAt
  have hpdc : ContinuousOn pd (Icc α β) := fun θ h => (hpd θ h).continuousAt.continuousWithinAt
  have hqdc : ContinuousOn qd (Icc α β) := fun θ h => (hqd θ h).continuousAt.continuousWithinAt
  have hDc : ContinuousOn D (Icc α β) := fun θ h => (hDd θ h).continuousAt.continuousWithinAt
  set W : ℝ → ℝ := fun θ => pd θ * q θ - p θ * qd θ with hW
  have hWc : ContinuousOn W (Icc α β) := (hpdc.mul hqc).sub (hpc.mul hqdc)
  set F : ℝ → ℝ := fun θ => w θ / D θ * W θ with hFdef
  set G : ℝ → ℝ := fun θ => (w' θ / D θ - w θ * D' θ / D θ ^ 2) * W θ
      - 2 * (w θ / D θ) * θ * (a θ * pd θ * q θ - b θ * p θ * qd θ) with hGdef
  have hcR : ContinuousOn (fun θ => (- (w θ * D' θ / D θ ^ 2)) * W θ
      - 2 * (w θ / D θ) * θ * (a θ * pd θ * q θ - b θ * p θ * qd θ)) (Icc α β) := by
    refine ContinuousOn.sub (ContinuousOn.mul (ContinuousOn.neg ?_) hWc) ?_
    · exact (hwc.mul hD'c).div (hDc.pow 2) fun θ h => pow_ne_zero 2 (hD0 θ h)
    · refine ContinuousOn.mul (ContinuousOn.mul (continuousOn_const.mul (hwc.div hDc hD0)) continuousOn_id) ?_
      exact ((ha.mul hpdc).mul hqc).sub ((hb.mul hpc).mul hqdc)
  have hGi : IntervalIntegrable G volume α β := by
    have h1 : IntervalIntegrable (fun θ => w' θ * (W θ / D θ)) volume α β :=
      hwi.mul_continuousOn (by rw [uIcc_of_le hαβ]; exact hWc.div hDc hD0)
    have h2 : IntervalIntegrable (fun θ => (- (w θ * D' θ / D θ ^ 2)) * W θ
        - 2 * (w θ / D θ) * θ * (a θ * pd θ * q θ - b θ * p θ * qd θ)) volume α β :=
      hcR.intervalIntegrable_of_Icc hαβ
    have e : G = fun θ => w' θ * (W θ / D θ) + ((- (w θ * D' θ / D θ ^ 2)) * W θ
        - 2 * (w θ / D θ) * θ * (a θ * pd θ * q θ - b θ * p θ * qd θ)) := by
      funext θ; simp only [hGdef]; ring
    rw [e]; exact h1.add h2
  have hwpq : IntervalIntegrable (fun θ => w θ * (p θ * q θ)) volume α β :=
    (hwc.mul (hpc.mul hqc)).intervalIntegrable_of_Icc hαβ
  have hF'eq : ∀ θ ∈ Icc α β, G θ - w θ * (p θ * q θ)
      = (w' θ / D θ - w θ * D' θ / D θ ^ 2) * W θ
        + w θ / D θ * (-2 * θ * a θ * pd θ - A θ * p θ) * q θ + w θ / D θ * (pd θ * qd θ)
        - (w θ / D θ * (pd θ * qd θ) + w θ / D θ * p θ * (-2 * θ * b θ * qd θ - B θ * q θ)) := by
    intro θ h
    have h0 := hD0 θ h
    have hDA := hD θ h
    simp only [hGdef, hW]
    have : w θ * (p θ * q θ) = w θ / D θ * ((A θ - B θ) * p θ * q θ) := by
      rw [← hDA]; field_simp
    rw [this]
    ring
  have hftc : ∫ θ in α..β, (G θ - w θ * (p θ * q θ)) = F β - F α := by
    refine integral_eq_of_hasDerivAt_off_countable_of_le F _ hαβ hE ?_ ?_ (hGi.sub hwpq)
    · exact ((hwc.div hDc hD0).mul hWc)
    · intro θ hθ
      have hI : θ ∈ Icc α β := Ioo_subset_Icc_self hθ.1
      have hwD := (hwd θ hθ).div (hDd θ hI) (hD0 θ hI)
      have hWd := ((hpd θ hI).mul (hq θ hI)).sub ((hp θ hI).mul (hqd θ hI))
      refine (hwD.mul hWd).congr_deriv ?_
      rw [hF'eq θ hI]
      have h0 := hD0 θ hI
      simp only [hW, Pi.mul_apply, Pi.sub_apply, Pi.div_apply]
      field_simp
      ring
  have hFα : F α = 0 := by simp [hFdef, hwα]
  have hFβ : F β = 0 := by simp [hFdef, hwβ]
  rw [hFα, hFβ, sub_zero, intervalIntegral.integral_sub hGi hwpq, sub_eq_zero] at hftc
  exact ⟨hGi, hftc.symm⟩

open Cvs.L2a.AngularProlateTailPositive (psi)
open Cvs.Prolate.Gram.RungGramFloorAtInfinity (rungU)
open Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval (pP qP)
open Cvs.Prolate.ExteriorSpanBernstein (IsRungFamily)
open Cvs.Route.Visibility.AliasPairThetaKernel (bet Lam hasDerivAt_bet one_lt_of)

/-- The dilated mode `θ ↦ ψ(kθ)`. -/
def Pk (c : ℝ) (g : ℝ → ℝ) (k : ℕ) (θ : ℝ) : ℝ := psi c g (k * θ)

/-- The dilated slope `θ ↦ ψ′(kθ) = u(kθ)/((kθ)² − 1)`. -/
def Vk (c : ℝ) (g : ℝ → ℝ) (k : ℕ) (θ : ℝ) : ℝ := rungU c g (k * θ) / pP (k * θ)

/-- The `θ`-potential `A_k = β_k(c²k²θ² − χ)` of the dilated mode. -/
def Ak (c χ : ℝ) (k : ℕ) (θ : ℝ) : ℝ := bet k θ * (c ^ 2 * (k : ℝ) ^ 2 * θ ^ 2 - χ)

/-- Its derivative `A_k′ = −2θβ_k²(c² − χ)`. -/
def AkD (c χ : ℝ) (k : ℕ) (θ : ℝ) : ℝ := -2 * θ * bet k θ ^ 2 * (c ^ 2 - χ)

variable {ι : Type*} [Fintype ι] {c : ℝ} {g g₁ g₂ : ι → ℝ → ℝ} {χ : ι → ℝ}

/-- `pP(kθ) = k²θ² − 1`. -/
theorem pP_mul_eq (k : ℕ) (θ : ℝ) : pP (k * θ) = (k : ℝ) ^ 2 * θ ^ 2 - 1 := by unfold pP; ring

/-- `A_k = c²Λ_k + β_k(c²/2 − χ)`. -/
theorem Ak_eq {k : ℕ} {θ : ℝ} (χ' : ℝ) (h : (k : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0) :
    Ak c χ' k θ = c ^ 2 * Lam k θ + bet k θ * (c ^ 2 / 2 - χ') := by
  unfold Ak Lam bet
  field_simp
  ring

/-- `A_k′ = −2θβ_k²(c² − χ)`. -/
theorem hasDerivAt_Ak {k : ℕ} {θ : ℝ} (χ' : ℝ) (h : (k : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0) :
    HasDerivAt (Ak c χ' k) (AkD c χ' k θ) θ := by
  have h1 := hasDerivAt_bet (k := k) h
  have h2 : HasDerivAt (fun θ : ℝ => c ^ 2 * (k : ℝ) ^ 2 * θ ^ 2 - χ') (c ^ 2 * (k : ℝ) ^ 2 * (2 * θ)) θ := by
    simpa using ((hasDerivAt_pow 2 θ).const_mul (c ^ 2 * (k : ℝ) ^ 2)).sub_const χ'
  refine (h1.mul h2).congr_deriv ?_
  unfold AkD bet
  field_simp
  ring

/-- The dilated mode has slope `kψ′(kθ)`. -/
theorem hasDerivAt_Pk (hF : IsRungFamily c g g₁ g₂ χ) (i : ι) {k : ℕ} {θ : ℝ} (h : 1 < k * θ) :
    HasDerivAt (Pk c (g i) k) (k * Vk c (g i) k θ) θ := by
  have h1 := ((hF.system i).1 (k * θ) h).comp θ ((hasDerivAt_id θ).const_mul (k : ℝ))
  refine h1.congr_deriv ?_
  unfold Vk; ring

/-- **The dilated prolate equation**: `(kψ′(kθ))′ = −2θβ_k·kψ′(kθ) − A_kψ(kθ)`. -/
theorem hasDerivAt_kVk (hF : IsRungFamily c g g₁ g₂ χ) (i : ι) {k : ℕ} {θ : ℝ} (h : 1 < k * θ) :
    HasDerivAt (fun θ => (k : ℝ) * Vk c (g i) k θ)
      (-2 * θ * bet k θ * (k * Vk c (g i) k θ) - Ak c (χ i) k θ * Pk c (g i) k θ) θ := by
  have hp : (k : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := by rw [← pP_mul_eq]; exact (Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP_pos h).ne'
  have e : (fun θ => (k : ℝ) * Vk c (g i) k θ)
      = fun θ => (k : ℝ) * (rungU c (g i) (k * θ) / ((k : ℝ) ^ 2 * θ ^ 2 - 1)) :=
    funext fun θ => by unfold Vk; rw [pP_mul_eq]
  rw [e]
  have hu := ((hF.system i).2.1 (k * θ)).comp θ ((hasDerivAt_id θ).const_mul (k : ℝ))
  have hpp : HasDerivAt (fun θ : ℝ => (k : ℝ) ^ 2 * θ ^ 2 - 1) ((k : ℝ) ^ 2 * (2 * θ)) θ := by
    have := ((hasDerivAt_pow 2 θ).const_mul ((k : ℝ) ^ 2)).sub_const 1
    exact this.congr_deriv (by push_cast; ring)
  have := (hu.div hpp hp).const_mul (k : ℝ)
  refine this.congr_deriv ?_
  unfold Vk Ak bet Pk
  simp only [Function.comp, qP]
  rw [pP_mul_eq]
  field_simp
  ring

/-- On `θ ≥ 12/25` every dilation with `k ≥ 3` lands beyond `1`. -/
theorem one_lt_mul {k : ℕ} (hk : 3 ≤ k) {θ : ℝ} (hθ : 12 / 25 ≤ θ) : 1 < (k : ℝ) * θ := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- `β_k` is continuous on `θ ≥ 12/25`. -/
theorem continuousOn_bet {k : ℕ} (hk : 3 ≤ k) {s : Set ℝ} (hs : ∀ θ ∈ s, 12 / 25 ≤ θ) : ContinuousOn (bet k) s :=
  fun θ hθ => (hasDerivAt_bet (sub_ne_zero.mpr (one_lt_of hk (hs θ hθ)).ne')).continuousAt.continuousWithinAt

/-- The Green integrand of the pair `ψ_i(kθ)`, `ψ_j(lθ)` against `w`, with `D = A_k − A_l`. -/
def gI (c : ℝ) (gi gj : ℝ → ℝ) (χi χj : ℝ) (w w' : ℝ → ℝ) (k l : ℕ) (θ : ℝ) : ℝ :=
  (w' θ / (Ak c χi k θ - Ak c χj l θ) - w θ * (AkD c χi k θ - AkD c χj l θ) / (Ak c χi k θ - Ak c χj l θ) ^ 2)
      * (k * Vk c gi k θ * Pk c gj l θ - Pk c gi k θ * (l * Vk c gj l θ))
    - 2 * (w θ / (Ak c χi k θ - Ak c χj l θ)) * θ
      * (bet k θ * (k * Vk c gi k θ) * Pk c gj l θ - bet l θ * Pk c gi k θ * (l * Vk c gj l θ))

/-- **Green's identity for a pair of dilated modes** `ψ_i(kθ)`, `ψ_j(lθ)` against a weight vanishing at both ends. -/
theorem green_pair (hF : IsRungFamily c g g₁ g₂ χ) (i j : ι) {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) {α β : ℝ}
    (hα : 12 / 25 ≤ α) (hαβ : α ≤ β) {E : Set ℝ} (hE : E.Countable) {w w' : ℝ → ℝ}
    (hwc : ContinuousOn w (Icc α β)) (hwd : ∀ θ ∈ Ioo α β \ E, HasDerivAt w (w' θ) θ)
    (hwi : IntervalIntegrable w' volume α β) (hwα : w α = 0) (hwβ : w β = 0)
    (hD0 : ∀ θ ∈ Icc α β, Ak c (χ i) k θ - Ak c (χ j) l θ ≠ 0) :
    IntervalIntegrable (gI c (g i) (g j) (χ i) (χ j) w w' k l) volume α β ∧
    ∫ θ in α..β, w θ * (Pk c (g i) k θ * Pk c (g j) l θ) = ∫ θ in α..β, gI c (g i) (g j) (χ i) (χ j) w w' k l θ := by
  have hθ : ∀ θ ∈ Icc α β, 12 / 25 ≤ θ := fun θ h => hα.trans h.1
  have hkθ : ∀ θ ∈ Icc α β, 1 < (k : ℝ) * θ := fun θ h => one_lt_mul hk (hθ θ h)
  have hlθ : ∀ θ ∈ Icc α β, 1 < (l : ℝ) * θ := fun θ h => one_lt_mul hl (hθ θ h)
  have hbk : ∀ θ ∈ Icc α β, (k : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := fun θ h => by
    have := one_lt_of hk (hθ θ h); intro h'; linarith
  have hbl : ∀ θ ∈ Icc α β, (l : ℝ) ^ 2 * θ ^ 2 - 1 ≠ 0 := fun θ h => by
    have := one_lt_of hl (hθ θ h); intro h'; linarith
  have hAD : ContinuousOn (fun θ => AkD c (χ i) k θ - AkD c (χ j) l θ) (Icc α β) := by
    unfold AkD
    exact ((((continuousOn_const.mul continuousOn_id).mul ((continuousOn_bet hk hθ).pow 2)).mul continuousOn_const).sub
      (((continuousOn_const.mul continuousOn_id).mul ((continuousOn_bet hl hθ).pow 2)).mul continuousOn_const))
  exact green_abstract (a := bet k) (b := bet l) (A := Ak c (χ i) k) (B := Ak c (χ j) l) hαβ hE
    (fun θ h => hasDerivAt_Pk hF i (hkθ θ h)) (fun θ h => hasDerivAt_kVk hF i (hkθ θ h))
    (fun θ h => hasDerivAt_Pk hF j (hlθ θ h)) (fun θ h => hasDerivAt_kVk hF j (hlθ θ h))
    (continuousOn_bet hk hθ) (continuousOn_bet hl hθ) (fun _ _ => rfl) hD0
    (fun θ h => (hasDerivAt_Ak (χ i) (hbk θ h)).sub (hasDerivAt_Ak (χ j) (hbl θ h))) hAD hwc hwd hwi hwα hwβ

/-- **Green's identity summed over the span**: `∫w·h(kθ)h(lθ) = ∫Σ_{ij} b_ib_j·gI_{ij}` for `h = Σ b_iψ_i`. -/
theorem green_sum (hF : IsRungFamily c g g₁ g₂ χ) (b : ι → ℝ) {k l : ℕ} (hk : 3 ≤ k) (hl : 3 ≤ l) {α β : ℝ}
    (hα : 12 / 25 ≤ α) (hαβ : α ≤ β) {E : Set ℝ} (hE : E.Countable) {w w' : ℝ → ℝ}
    (hwc : ContinuousOn w (Icc α β)) (hwd : ∀ θ ∈ Ioo α β \ E, HasDerivAt w (w' θ) θ)
    (hwi : IntervalIntegrable w' volume α β) (hwα : w α = 0) (hwβ : w β = 0)
    (hD0 : ∀ i j, ∀ θ ∈ Icc α β, Ak c (χ i) k θ - Ak c (χ j) l θ ≠ 0) :
    IntervalIntegrable (fun θ => ∑ i, ∑ j, b i * b j * gI c (g i) (g j) (χ i) (χ j) w w' k l θ) volume α β ∧
    ∫ θ in α..β, w θ * (Cvs.Prolate.ExteriorSpanBernstein.spanH c g b (k * θ) * Cvs.Prolate.ExteriorSpanBernstein.spanH c g b (l * θ))
      = ∫ θ in α..β, ∑ i, ∑ j, b i * b j * gI c (g i) (g j) (χ i) (χ j) w w' k l θ := by
  have hG := fun i j => green_pair hF i j hk hl hα hαβ hE hwc hwd hwi hwα hwβ (hD0 i j)
  have hint : ∀ i j, IntervalIntegrable (fun θ => w θ * (Pk c (g i) k θ * Pk c (g j) l θ)) volume α β := by
    intro i j
    refine ContinuousOn.intervalIntegrable_of_Icc hαβ (hwc.mul (ContinuousOn.mul ?_ ?_))
    · exact ((hF.system i).2.2.1.comp (continuous_const.mul continuous_id)).continuousOn
    · exact ((hF.system j).2.2.1.comp (continuous_const.mul continuous_id)).continuousOn
  have hS : ∀ F : ι → ι → ℝ → ℝ, (∀ i j, IntervalIntegrable (F i j) volume α β) →
      IntervalIntegrable (fun θ => ∑ i, ∑ j, F i j θ) volume α β := by
    intro F hFi
    have := IntervalIntegrable.sum Finset.univ fun i _ => IntervalIntegrable.sum Finset.univ fun j _ => hFi i j
    exact this.congr fun θ _ => by simp [Finset.sum_apply]
  have hsum := hS (fun i j θ => b i * b j * gI c (g i) (g j) (χ i) (χ j) w w' k l θ)
    fun i j => (hG i j).1.const_mul (b i * b j)
  refine ⟨hsum, ?_⟩
  have e : ∀ θ, w θ * (Cvs.Prolate.ExteriorSpanBernstein.spanH c g b (k * θ) * Cvs.Prolate.ExteriorSpanBernstein.spanH c g b (l * θ))
      = ∑ i, ∑ j, b i * b j * (w θ * (Pk c (g i) k θ * Pk c (g j) l θ)) := by
    intro θ
    simp only [Cvs.Prolate.ExteriorSpanBernstein.spanH, Pk]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum fun i _ => ?_, intervalIntegral.integral_finsetSum fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => ?_, intervalIntegral.integral_finsetSum fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, (hG i j).2]
    · exact (hG i j).1.const_mul _
    · exact (hint i j).const_mul _
  · exact IntervalIntegrable.sum Finset.univ (fun j _ => (hG i j).1.const_mul (b i * b j)) |>.congr
      fun θ _ => by simp [Finset.sum_apply]
  · exact IntervalIntegrable.sum Finset.univ (fun j _ => (hint i j).const_mul (b i * b j)) |>.congr
      fun θ _ => by simp [Finset.sum_apply]

end Cvs.Prolate.DilatedModeGreenIdentity
