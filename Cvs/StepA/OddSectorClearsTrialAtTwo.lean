import Mathlib
import Cvs.StepA.OddChannelCertificatesLogTwo
import Cvs.StepA.OddSectorBaseBudget
import Cvs.StepA.StepAAtTwoAssembled
import Cvs.WeilForm.Archimedean.ArchimedeanUnbounded
import Cvs.WeilForm.Archimedean.OffWindowDefect
import Cvs.WeilForm.Archimedean.TruncatedSymbolConstant
import Cvs.WeilForm.ChannelFunctionalL2
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.LevyDomainSpectral
import Cvs.WeilForm.OddCapTransfer
import Cvs.WeilForm.OddPoleTermBound
import Cvs.WeilForm.SimplicityCriterionWindow
import Cvs.WeilForm.WeilFormOnWindowL2
import Cvs.WeilForm.WindowReflectionSymmetry
import Cvs.WeilForm.WindowRepresentative

/-!
# The odd sector clears the trial level at `x = 2`

For `L = log 2`, `N = 100`, `P = 2`, `R = 1`, every nonzero odd class of the form domain has
`weilQWTrunc` above `15/1000 · ‖·‖²`, so it beats any trial level `β < 15/1000`.
-/

noncomputable section

open MeasureTheory Finset

namespace Cvs.StepA.OddSectorClearsTrialAtTwo

/-- The 100 rational channel caps `r k = 2/bₖ − 2bₖ/(bₖ²+tₖ²)`, indexed by channel. -/
noncomputable def r : ℕ → ℝ := fun k => ([(3957491 / 1000000 : ℝ), (670979 / 1000000 : ℝ), (294009 / 1000000 : ℝ), (158976 / 1000000 : ℝ), (95803 / 1000000 : ℝ), (62004 / 1000000 : ℝ), (42288 / 1000000 : ℝ), (30044 / 1000000 : ℝ), (22061 / 1000000 : ℝ), (16646 / 1000000 : ℝ), (12852 / 1000000 : ℝ), (10119 / 1000000 : ℝ), (8102 / 1000000 : ℝ), (6584 / 1000000 : ℝ), (5420 / 1000000 : ℝ), (4513 / 1000000 : ℝ), (3797 / 1000000 : ℝ), (3223 / 1000000 : ℝ), (2759 / 1000000 : ℝ), (2380 / 1000000 : ℝ), (2066 / 1000000 : ℝ), (1805 / 1000000 : ℝ), (1587 / 1000000 : ℝ), (1401 / 1000000 : ℝ), (1244 / 1000000 : ℝ), (1109 / 1000000 : ℝ), (993 / 1000000 : ℝ), (893 / 1000000 : ℝ), (805 / 1000000 : ℝ), (729 / 1000000 : ℝ), (662 / 1000000 : ℝ), (603 / 1000000 : ℝ), (550 / 1000000 : ℝ), (504 / 1000000 : ℝ), (462 / 1000000 : ℝ), (426 / 1000000 : ℝ), (392 / 1000000 : ℝ), (363 / 1000000 : ℝ), (336 / 1000000 : ℝ), (311 / 1000000 : ℝ), (289 / 1000000 : ℝ), (269 / 1000000 : ℝ), (251 / 1000000 : ℝ), (235 / 1000000 : ℝ), (219 / 1000000 : ℝ), (206 / 1000000 : ℝ), (193 / 1000000 : ℝ), (181 / 1000000 : ℝ), (170 / 1000000 : ℝ), (160 / 1000000 : ℝ), (151 / 1000000 : ℝ), (143 / 1000000 : ℝ), (135 / 1000000 : ℝ), (127 / 1000000 : ℝ), (121 / 1000000 : ℝ), (114 / 1000000 : ℝ), (108 / 1000000 : ℝ), (103 / 1000000 : ℝ), (98 / 1000000 : ℝ), (93 / 1000000 : ℝ), (89 / 1000000 : ℝ), (84 / 1000000 : ℝ), (80 / 1000000 : ℝ), (77 / 1000000 : ℝ), (73 / 1000000 : ℝ), (70 / 1000000 : ℝ), (67 / 1000000 : ℝ), (64 / 1000000 : ℝ), (61 / 1000000 : ℝ), (59 / 1000000 : ℝ), (56 / 1000000 : ℝ), (54 / 1000000 : ℝ), (52 / 1000000 : ℝ), (50 / 1000000 : ℝ), (48 / 1000000 : ℝ), (46 / 1000000 : ℝ), (44 / 1000000 : ℝ), (42 / 1000000 : ℝ), (41 / 1000000 : ℝ), (39 / 1000000 : ℝ), (38 / 1000000 : ℝ), (36 / 1000000 : ℝ), (35 / 1000000 : ℝ), (34 / 1000000 : ℝ), (33 / 1000000 : ℝ), (31 / 1000000 : ℝ), (30 / 1000000 : ℝ), (29 / 1000000 : ℝ), (28 / 1000000 : ℝ), (27 / 1000000 : ℝ), (26 / 1000000 : ℝ), (26 / 1000000 : ℝ), (25 / 1000000 : ℝ), (24 / 1000000 : ℝ), (23 / 1000000 : ℝ), (22 / 1000000 : ℝ), (22 / 1000000 : ℝ), (21 / 1000000 : ℝ), (20 / 1000000 : ℝ), (20 / 1000000 : ℝ)]).getD k 0

/-- The per-channel Lévy weight minus its cap, the coefficient the budget sums. -/
noncomputable def lam : ℕ → ℝ := fun k => 2 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k - r k

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 8000 in
/-- **The odd sector clears the trial level.**  Every nonzero odd class of the form domain has
truncated Weil form strictly above `15/1000 · ‖·‖²`. -/
theorem odd_bottom {o : Cvs.WeilForm.FormDomain.formDomain Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le}
    (hodd : Cvs.WeilForm.WindowReflectionSymmetry.reflD Cvs.StepA.StepAAtTwoAssembled.log_two_pos.le o = -o) (ho : o ≠ 0) :
    (15 / 1000 : ℝ) * ‖o‖ ^ 2
      < Cvs.WeilForm.SimplicityCriterionWindow.weilQWTrunc 100 2 1 (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by
  have hoddW : Cvs.WeilForm.WindowReflectionSymmetry.reflW (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
      = -(o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by
    have h := congrArg (Subtype.val) hodd
    simpa [Cvs.WeilForm.WindowReflectionSymmetry.reflD] using h
  have hodd_ae : ∀ᵐ s ∂(volume : Measure ℝ),
      Cvs.WeilForm.WindowRepresentative.rep (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) (Real.log 2 - s)
        = - Cvs.WeilForm.WindowRepresentative.rep (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) s := by
    have h1 := Cvs.WeilForm.WindowReflectionSymmetry.rep_reflW_ae (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
    have h2 := Cvs.WeilForm.LevyDomainSpectral.rep_smul_ae (-1 : ℝ) (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))
    rw [hoddW] at h1
    have h3 : ((-1 : ℝ) • (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
        = -(o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) := by ext1; simp
    rw [h3] at h2
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← hx1, hx2]; ring
  have hcaps : ∀ k ∈ Finset.range 100,
      Cvs.WeilForm.ChannelFunctionalL2.chanInt (Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx k)
          (Cvs.WeilForm.WindowRepresentative.rep (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)))
        ≤ lam k * ‖(o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))‖ ^ 2 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    interval_cases k
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 0 = 1 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 0) (t := (48244 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_0)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_0_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 1 = 5 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 1) (t := (57012 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_1)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_1_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 2 = 9 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 2) (t := (62910 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_2)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_2_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 3 = 13 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 3) (t := (67205 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_3)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_3_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 4 = 17 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 4) (t := (70443 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_4)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_4_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 5 = 21 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 5) (t := (72945 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_5)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_5_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 6 = 25 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 6) (t := (74923 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_6)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_6_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 7 = 29 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 7) (t := (76519 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_7)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_7_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 8 = 33 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 8) (t := (77831 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_8)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_8_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 9 = 37 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 9) (t := (78925 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_9)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_9_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 10 = 41 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 10) (t := (79851 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_10)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_10_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 11 = 45 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 11) (t := (80645 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_11)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_11_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 12 = 49 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 12) (t := (81331 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_12)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_12_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 13 = 53 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 13) (t := (81931 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_13)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_13_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 14 = 57 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 14) (t := (82458 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_14)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_14_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 15 = 61 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 15) (t := (82927 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_15)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_15_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 16 = 65 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 16) (t := (83345 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_16)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_16_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 17 = 69 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 17) (t := (83720 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_17)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_17_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 18 = 73 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 18) (t := (84059 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_18)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_18_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 19 = 77 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 19) (t := (84366 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_19)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_19_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 20 = 81 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 20) (t := (84646 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_20)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_20_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 21 = 85 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 21) (t := (84902 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_21)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_21_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 22 = 89 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 22) (t := (85138 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_22)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_22_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 23 = 93 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 23) (t := (85354 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_23)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_23_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 24 = 97 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 24) (t := (85555 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_24)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_24_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 25 = 101 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 25) (t := (85740 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_25)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_25_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 26 = 105 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 26) (t := (85913 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_26)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_26_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 27 = 109 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 27) (t := (86074 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_27)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_27_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 28 = 113 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 28) (t := (86224 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_28)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_28_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 29 = 117 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 29) (t := (86365 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_29)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_29_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 30 = 121 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 30) (t := (86496 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_30)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_30_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 31 = 125 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 31) (t := (86620 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_31)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_31_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 32 = 129 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 32) (t := (86737 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_32)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_32_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 33 = 133 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 33) (t := (86847 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_33)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_33_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 34 = 137 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 34) (t := (86951 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_34)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_34_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 35 = 141 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 35) (t := (87050 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_35)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_35_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 36 = 145 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 36) (t := (87143 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_36)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_36_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 37 = 149 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 37) (t := (87231 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_37)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_37_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 38 = 153 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 38) (t := (87316 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_38)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_38_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 39 = 157 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 39) (t := (87396 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_39)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_39_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 40 = 161 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 40) (t := (87472 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_40)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_40_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 41 = 165 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 41) (t := (87544 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_41)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_41_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 42 = 169 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 42) (t := (87614 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_42)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_42_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 43 = 173 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 43) (t := (87680 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_43)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_43_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 44 = 177 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 44) (t := (87744 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_44)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_44_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 45 = 181 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 45) (t := (87804 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_45)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_45_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 46 = 185 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 46) (t := (87863 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_46)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_46_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 47 = 189 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 47) (t := (87918 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_47)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_47_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 48 = 193 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 48) (t := (87972 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_48)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_48_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 49 = 197 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 49) (t := (88024 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_49)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_49_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 50 = 201 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 50) (t := (88073 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_50)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_50_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 51 = 205 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 51) (t := (88121 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_51)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_51_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 52 = 209 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 52) (t := (88167 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_52)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_52_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 53 = 213 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 53) (t := (88211 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_53)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_53_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 54 = 217 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 54) (t := (88254 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_54)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_54_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 55 = 221 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 55) (t := (88295 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_55)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_55_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 56 = 225 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 56) (t := (88334 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_56)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_56_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 57 = 229 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 57) (t := (88373 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_57)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_57_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 58 = 233 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 58) (t := (88410 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_58)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_58_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 59 = 237 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 59) (t := (88446 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_59)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_59_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 60 = 241 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 60) (t := (88481 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_60)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_60_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 61 = 245 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 61) (t := (88514 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_61)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_61_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 62 = 249 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 62) (t := (88547 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_62)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_62_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 63 = 253 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 63) (t := (88578 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_63)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_63_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 64 = 257 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 64) (t := (88609 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_64)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_64_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 65 = 261 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 65) (t := (88639 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_65)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_65_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 66 = 265 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 66) (t := (88668 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_66)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_66_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 67 = 269 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 67) (t := (88696 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_67)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_67_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 68 = 273 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 68) (t := (88723 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_68)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_68_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 69 = 277 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 69) (t := (88749 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_69)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_69_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 70 = 281 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 70) (t := (88775 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_70)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_70_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 71 = 285 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 71) (t := (88800 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_71)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_71_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 72 = 289 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 72) (t := (88824 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_72)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_72_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 73 = 293 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 73) (t := (88848 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_73)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_73_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 74 = 297 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 74) (t := (88871 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_74)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_74_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 75 = 301 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 75) (t := (88893 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_75)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_75_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 76 = 305 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 76) (t := (88915 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_76)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_76_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 77 = 309 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 77) (t := (88937 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_77)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_77_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 78 = 313 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 78) (t := (88957 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_78)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_78_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 79 = 317 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 79) (t := (88978 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_79)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_79_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 80 = 321 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 80) (t := (88997 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_80)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_80_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 81 = 325 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 81) (t := (89017 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_81)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_81_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 82 = 329 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 82) (t := (89036 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_82)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_82_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 83 = 333 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 83) (t := (89054 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_83)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_83_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 84 = 337 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 84) (t := (89072 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_84)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_84_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 85 = 341 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 85) (t := (89090 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_85)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_85_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 86 = 345 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 86) (t := (89107 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_86)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_86_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 87 = 349 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 87) (t := (89123 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_87)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_87_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 88 = 353 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 88) (t := (89140 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_88)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_88_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 89 = 357 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 89) (t := (89156 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_89)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_89_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 90 = 361 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 90) (t := (89172 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_90)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_90_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 91 = 365 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 91) (t := (89187 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_91)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_91_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 92 = 369 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 92) (t := (89202 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_92)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_92_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 93 = 373 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 93) (t := (89217 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_93)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_93_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 94 = 377 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 94) (t := (89231 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_94)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_94_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 95 = 381 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 95) (t := (89245 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_95)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_95_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 96 = 385 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 96) (t := (89259 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_96)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_96_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 97 = 389 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 97) (t := (89273 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_97)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_97_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 98 = 393 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 98) (t := (89286 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_98)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_98_cap]
    · have hb : Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 99 = 397 / 2 := by unfold Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx; norm_num
      have hcap := Cvs.WeilForm.OddCapTransfer.odd_cap_L2 Cvs.StepA.StepAAtTwoAssembled.log_two_pos
          (b := Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx 99) (t := (89299 / 10000 : ℝ))
          (by rw [hb]; norm_num) (by norm_num) (by rw [hb]; exact Cvs.StepA.OddChannelCertificatesLogTwo.chan_99)
          (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) hodd_ae
      refine hcap.trans ?_
      simp only [lam, r, List.getD_cons_zero, List.getD_cons_succ]
      rw [hb]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      linarith [Cvs.StepA.OddChannelCertificatesLogTwo.chan_99_cap]
  have hlow := Cvs.StepA.OddSectorBaseBudget.odd_lower_of_caps 100 hoddW hcaps
  have hsum_r : ∑ k ∈ Finset.range 100, r k = 5432403 / 1000000 := by
    simp only [r, List.getD_cons_zero, List.getD_cons_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    norm_num
  have hpt : ∀ n ∈ Finset.range 100,
      2 / Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx n = (1 : ℝ) / ((n : ℝ) + 1 / 4) := by
    intro n _
    rw [Cvs.WeilForm.Archimedean.OffWindowDefect.bIdx_eq]
    have hn : (1 : ℝ) / 4 + (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hlamsum : ∑ k ∈ Finset.range 100, lam k
      = (∑ n ∈ Finset.range 100, (1 : ℝ) / ((n : ℝ) + 1 / 4)) - 5432403 / 1000000 := by
    simp only [lam, Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl hpt, hsum_r]
  have hcoef : (15 / 1000 : ℝ)
      < Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst 100 - (∑ k ∈ Finset.range 100, lam k)
          - (Real.exp (Real.log 2 / 2) - Real.exp (-(Real.log 2 / 2)) - Real.log 2) := by
    rw [Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.truncConst, hlamsum]
    have hA0 := Cvs.WeilForm.Archimedean.TruncatedSymbolConstant.archSymbol_zero_lower
    have hpole := Cvs.WeilForm.OddPoleTermBound.poleConst_log_two
    linarith
  have hne : (o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2)) ≠ 0 := by
    simpa using ho
  have hpos : 0 < ‖(o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))‖ ^ 2 := by positivity
  have hnorm : ‖(o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))‖ = ‖o‖ := rfl
  calc (15 / 1000 : ℝ) * ‖o‖ ^ 2
      = (15 / 1000 : ℝ) * ‖(o : Cvs.WeilForm.WeilFormOnWindowL2.window (Real.log 2))‖ ^ 2 := by rw [hnorm]
    _ < _ := by
        apply lt_of_lt_of_le _ hlow
        exact mul_lt_mul_of_pos_right hcoef hpos

end Cvs.StepA.OddSectorClearsTrialAtTwo
