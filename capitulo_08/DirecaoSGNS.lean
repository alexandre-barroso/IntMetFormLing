import Mathlib

open scoped BigOperators
namespace Chapter08SGNSDirection

theorem square_sum_positive {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) :
    0 < ∑ i, (v i)^2 := by
  have hn : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    exact h i
  obtain ⟨i,hi⟩ := hn
  have hb : (v i)^2 ≤ ∑ j, (v j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi) hb

theorem update_identity {d : ℕ} (u v : Fin d → ℝ) (α p y : ℝ) :
    (∑ i, (u i-α*(p-y)*v i)*v i) - (∑ i, u i*v i) =
      -α*(p-y)*(∑ i, (v i)^2) := by
  have ht : (∑ i, (u i-α*(p-y)*v i)*v i) =
      (∑ i, u i*v i) - α*(p-y)*(∑ i, (v i)^2) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [ht]
  ring

theorem sigmoid_interior (z : ℝ) : 0 < Real.exp z/(1+Real.exp z) ∧
    Real.exp z/(1+Real.exp z) < 1 := by
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).mpr
    linarith

theorem observed_pair_increases {d : ℕ} (u v : Fin d → ℝ) (α z : ℝ)
    (hα : 0 < α) (hv : v ≠ 0) :
    (∑ i, u i*v i) <
      ∑ i, (u i-α*(Real.exp z/(1+Real.exp z)-1)*v i)*v i := by
  have hs := square_sum_positive v hv
  have hp := (sigmoid_interior z).2
  have hpos := mul_pos (mul_pos hα (sub_pos.mpr hp)) hs
  have he := update_identity u v α (Real.exp z/(1+Real.exp z)) 1
  nlinarith

theorem negative_pair_decreases {d : ℕ} (u v : Fin d → ℝ) (α z : ℝ)
    (hα : 0 < α) (hv : v ≠ 0) :
    (∑ i, (u i-α*(Real.exp z/(1+Real.exp z)-0)*v i)*v i) <
      ∑ i, u i*v i := by
  have hs := square_sum_positive v hv
  have hp := (sigmoid_interior z).1
  have hpos := mul_pos (mul_pos hα hp) hs
  have he := update_identity u v α (Real.exp z/(1+Real.exp z)) 0
  nlinarith

end Chapter08SGNSDirection
