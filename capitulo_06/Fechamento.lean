import Mathlib

set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Chapter06Closure

structure ColorModel (nm nw nu : ℕ) where
  prior : Fin nm → ℝ
  meaning : Fin nm → Fin nu → ℝ
  encoder : Fin nm → Fin nw → ℝ
  prior_nonneg : ∀ m, 0 ≤ prior m
  meaning_nonneg : ∀ m u, 0 ≤ meaning m u
  encoder_nonneg : ∀ m w, 0 ≤ encoder m w
  prior_sum : ∑ m, prior m = 1
  meaning_sum : ∀ m, ∑ u, meaning m u = 1
  encoder_sum : ∀ m, ∑ w, encoder m w = 1

namespace ColorModel

variable {nm nw nu : ℕ} (c : ColorModel nm nw nu)

noncomputable def triple (m : Fin nm) (w : Fin nw) (u : Fin nu) : ℝ :=
  c.prior m * c.encoder m w * c.meaning m u

noncomputable def marginalW (w : Fin nw) : ℝ := ∑ m, c.prior m * c.encoder m w

noncomputable def marginalU (u : Fin nu) : ℝ := ∑ m, c.prior m * c.meaning m u

noncomputable def jointWU (w : Fin nw) (u : Fin nu) : ℝ := ∑ m, c.triple m w u

noncomputable def decoder (w : Fin nw) (u : Fin nu) : ℝ := c.jointWU w u / c.marginalW w

noncomputable def distortion : ℝ :=
  ∑ m, ∑ w, ∑ u, c.triple m w u * Real.logb 2 (c.meaning m u / c.decoder w u)

noncomputable def sourceInformation : ℝ :=
  ∑ m, ∑ u, c.prior m * c.meaning m u * Real.logb 2 (c.meaning m u / c.marginalU u)

noncomputable def wordInformation : ℝ :=
  ∑ w, ∑ u, c.jointWU w u * Real.logb 2 (c.decoder w u / c.marginalU u)

noncomputable def expectedKL : ℝ :=
  ∑ m, ∑ w, if c.prior m * c.encoder m w = 0 then 0 else
    c.prior m * c.encoder m w *
      ∑ u, c.meaning m u * Real.logb 2 (c.meaning m u / c.decoder w u)

theorem triple_nonneg (m : Fin nm) (w : Fin nw) (u : Fin nu) : 0 ≤ c.triple m w u :=
  mul_nonneg (mul_nonneg (c.prior_nonneg m) (c.encoder_nonneg m w)) (c.meaning_nonneg m u)

theorem sum_encoder_triple (m : Fin nm) (u : Fin nu) :
    ∑ w, c.triple m w u = c.prior m * c.meaning m u := by
  calc
    ∑ w, c.triple m w u = (c.prior m * c.meaning m u) * ∑ w, c.encoder m w := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      unfold triple
      ring
    _ = c.prior m * c.meaning m u := by rw [c.encoder_sum]; ring

theorem sum_meaning_triple (m : Fin nm) (w : Fin nw) :
    ∑ u, c.triple m w u = c.prior m * c.encoder m w := by
  simp only [triple, ← Finset.mul_sum, c.meaning_sum, mul_one]

theorem joint_marginal_word (w : Fin nw) : ∑ u, c.jointWU w u = c.marginalW w := by
  unfold jointWU marginalW
  rw [Finset.sum_comm]
  simp_rw [c.sum_meaning_triple]

theorem joint_marginal_universe (u : Fin nu) : ∑ w, c.jointWU w u = c.marginalU u := by
  unfold jointWU marginalU
  rw [Finset.sum_comm]
  simp_rw [c.sum_encoder_triple]

theorem source_joint_marginal (m : Fin nm) :
    ∑ u, c.prior m * c.meaning m u = c.prior m := by
  rw [← Finset.mul_sum, c.meaning_sum, mul_one]

theorem word_marginal_normalized : ∑ w, c.marginalW w = 1 := by
  unfold marginalW
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, c.encoder_sum, mul_one]
  exact c.prior_sum

theorem source_joint_normalized : (∑ m, ∑ u, c.prior m * c.meaning m u) = 1 := by
  simp_rw [c.source_joint_marginal]
  exact c.prior_sum

theorem word_joint_normalized : (∑ w, ∑ u, c.jointWU w u) = 1 := by
  simp_rw [c.joint_marginal_word]
  exact c.word_marginal_normalized

theorem bayesian_decoder (w : Fin nw) (u : Fin nu) :
    c.decoder w u = ∑ m, (c.prior m * c.encoder m w / c.marginalW w) * c.meaning m u := by
  unfold decoder jointWU triple
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem joint_nonneg (w : Fin nw) (u : Fin nu) : 0 ≤ c.jointWU w u := by
  exact Finset.sum_nonneg fun m _ => c.triple_nonneg m w u

theorem decoder_normalized (w : Fin nw) (hw : 0 < c.marginalW w) :
    (∀ u, 0 ≤ c.decoder w u) ∧ ∑ u, c.decoder w u = 1 := by
  constructor
  · intro u
    exact div_nonneg (c.joint_nonneg w u) hw.le
  · simp only [decoder, ← Finset.sum_div, c.joint_marginal_word, div_self hw.ne']

theorem support_of_positive_triple (m : Fin nm) (w : Fin nw) (u : Fin nu)
    (ht : 0 < c.triple m w u) :
    0 < c.meaning m u ∧ 0 < c.decoder w u ∧ 0 < c.marginalU u := by
  have hpq : 0 < c.prior m * c.encoder m w :=
    pos_of_mul_pos_left ht (c.meaning_nonneg m u)
  have hp : 0 < c.prior m := pos_of_mul_pos_left hpq (c.encoder_nonneg m w)
  have hr : 0 < c.meaning m u :=
    pos_of_mul_pos_right ht (mul_nonneg (c.prior_nonneg m) (c.encoder_nonneg m w))
  have hj : 0 < c.jointWU w u := lt_of_lt_of_le ht
    (Finset.single_le_sum (fun i _ => c.triple_nonneg i w u) (Finset.mem_univ m))
  have hw : 0 < c.marginalW w := lt_of_lt_of_le hpq
    (Finset.single_le_sum (fun i _ => mul_nonneg (c.prior_nonneg i) (c.encoder_nonneg i w))
      (Finset.mem_univ m))
  have hu : 0 < c.marginalU u := lt_of_lt_of_le (mul_pos hp hr)
    (Finset.single_le_sum (fun i _ => mul_nonneg (c.prior_nonneg i) (c.meaning_nonneg i u))
      (Finset.mem_univ m))
  exact ⟨hr, div_pos hj hw, hu⟩

theorem active_KL_support (m : Fin nm) (w : Fin nw)
    (hpair : 0 < c.prior m * c.encoder m w) (u : Fin nu) (hu : 0 < c.meaning m u) :
    0 < c.decoder w u :=
  (c.support_of_positive_triple m w u (mul_pos hpair hu)).2.1

theorem weighted_log_split (m : Fin nm) (w : Fin nw) (u : Fin nu) :
    c.triple m w u * Real.logb 2 (c.meaning m u / c.decoder w u) =
      c.triple m w u * Real.logb 2 (c.meaning m u / c.marginalU u) -
      c.triple m w u * Real.logb 2 (c.decoder w u / c.marginalU u) := by
  by_cases ht : c.triple m w u = 0
  · simp [ht]
  · have hpos : 0 < c.triple m w u := lt_of_le_of_ne (c.triple_nonneg m w u) (Ne.symm ht)
    obtain ⟨hr, hd, hu⟩ := c.support_of_positive_triple m w u hpos
    rw [Real.logb_div hr.ne' hd.ne', Real.logb_div hr.ne' hu.ne',
      Real.logb_div hd.ne' hu.ne']
    ring

theorem aggregate_by_meaning (f : Fin nm → Fin nu → ℝ) :
    (∑ m, ∑ w, ∑ u, c.triple m w u * f m u) =
      ∑ m, ∑ u, c.prior m * c.meaning m u * f m u := by
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul, c.sum_encoder_triple]

theorem aggregate_by_word (f : Fin nw → Fin nu → ℝ) :
    (∑ m, ∑ w, ∑ u, c.triple m w u * f w u) =
      ∑ w, ∑ u, c.jointWU w u * f w u := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul]
  rfl

theorem expected_KL_equals_distortion : c.expectedKL = c.distortion := by
  unfold expectedKL distortion
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : c.prior m * c.encoder m w = 0
  · simp [h, triple]
  · simp only [if_neg h, Finset.mul_sum, triple, mul_assoc]

theorem distortion_equals_information_loss :
    c.distortion = c.sourceInformation - c.wordInformation := by
  unfold distortion sourceInformation wordInformation
  simp_rw [c.weighted_log_split, Finset.sum_sub_distrib]
  rw [c.aggregate_by_meaning, c.aggregate_by_word]

theorem expected_KL_equals_information_loss :
    c.expectedKL = c.sourceInformation - c.wordInformation := by
  rw [c.expected_KL_equals_distortion, c.distortion_equals_information_loss]

theorem source_information_is_mutual_information :
    c.sourceInformation = ∑ m, ∑ u, c.prior m * c.meaning m u *
      Real.logb 2 ((c.prior m * c.meaning m u) / (c.prior m * c.marginalU u)) := by
  unfold sourceInformation
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro u _
  by_cases hp : c.prior m = 0
  · simp [hp]
  · rw [mul_div_mul_left _ _ hp]

theorem word_information_is_mutual_information :
    c.wordInformation = ∑ w, ∑ u, c.jointWU w u *
      Real.logb 2 (c.jointWU w u / (c.marginalW w * c.marginalU u)) := by
  simp only [wordInformation, decoder, div_div]

theorem word_information_full_marginals :
    c.wordInformation = ∑ w, ∑ u, c.jointWU w u *
      Real.logb 2 (c.jointWU w u / ((∑ v, c.jointWU w v) * (∑ v, c.jointWU v u))) := by
  simp_rw [c.joint_marginal_word, c.joint_marginal_universe]
  exact c.word_information_is_mutual_information

theorem source_information_full_marginals :
    c.sourceInformation = ∑ m, ∑ u, c.prior m * c.meaning m u *
      Real.logb 2 ((c.prior m * c.meaning m u) /
        ((∑ v, c.prior m * c.meaning m v) * (∑ v, c.prior v * c.meaning v u))) := by
  simp_rw [c.source_joint_marginal]
  exact c.source_information_is_mutual_information

theorem source_information_fixed {nw' : ℕ} (d : ColorModel nm nw' nu)
    (hp : c.prior = d.prior) (hr : c.meaning = d.meaning) :
    c.sourceInformation = d.sourceInformation := by
  simp only [sourceInformation, marginalU, hp, hr]

theorem less_distortion_iff_more_information {nw' : ℕ} (d : ColorModel nm nw' nu)
    (hp : c.prior = d.prior) (hr : c.meaning = d.meaning) :
    c.expectedKL < d.expectedKL ↔ d.wordInformation < c.wordInformation := by
  rw [c.expected_KL_equals_information_loss, d.expected_KL_equals_information_loss,
    c.source_information_fixed d hp hr]
  constructor <;> intro h <;> linarith

theorem weak_distortion_order_iff_information_order {nw' : ℕ} (d : ColorModel nm nw' nu)
    (hp : c.prior = d.prior) (hr : c.meaning = d.meaning) :
    c.expectedKL ≤ d.expectedKL ↔ d.wordInformation ≤ c.wordInformation := by
  rw [c.expected_KL_equals_information_loss, d.expected_KL_equals_information_loss,
    c.source_information_fixed d hp hr]
  constructor <;> intro h <;> linarith

end ColorModel

end Chapter06Closure

#print axioms Chapter06Closure.ColorModel.expected_KL_equals_information_loss
#print axioms Chapter06Closure.ColorModel.less_distortion_iff_more_information
