import Mathlib

namespace Chapter08ReLULimits

noncomputable def relu (x : ℝ) : ℝ := max 0 x

theorem continuous_relu : Continuous relu := continuous_const.max continuous_id

theorem left_difference_quotient {h : ℝ} (hh : h < 0) :
    (relu h - relu 0) / h = 0 := by
  simp [relu, max_eq_left (le_of_lt hh)]

theorem right_difference_quotient {h : ℝ} (hh : 0 < h) :
    (relu h - relu 0) / h = 1 := by
  simp [relu, max_eq_right (le_of_lt hh), ne_of_gt hh]

theorem derivative_left : HasDerivWithinAt relu 0 (Set.Iic 0) 0 := by
  apply (hasDerivWithinAt_const (0 : ℝ) (Set.Iic 0) (0 : ℝ)).congr_of_mem
  · intro x hx
    exact max_eq_left hx
  · exact Set.self_mem_Iic

theorem derivative_right : HasDerivWithinAt relu 1 (Set.Ici 0) 0 := by
  apply (hasDerivWithinAt_id (0 : ℝ) (Set.Ici 0)).congr_of_mem
  · intro x hx
    exact max_eq_right hx
  · exact Set.self_mem_Ici

theorem not_differentiable_at_zero : ¬ DifferentiableAt ℝ relu 0 := by
  intro h
  have hl : deriv relu 0 = 0 :=
    (uniqueDiffOn_Iic _ _ Set.self_mem_Iic).eq_deriv _ h.hasDerivAt.hasDerivWithinAt derivative_left
  have hr : deriv relu 0 = 1 :=
    (uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt derivative_right
  linarith

end Chapter08ReLULimits
