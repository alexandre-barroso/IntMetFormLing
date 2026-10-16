import Mathlib

open scoped BigOperators

namespace Chapter04Closure

def adjacency {α : Type*} [Fintype α] (R : α → α → Prop) [DecidableRel R] :
    Matrix α α ℝ := fun i j => if R i j then 1 else 0

theorem square_counts_intermediates {α : Type*} [Fintype α]
    (R : α → α → Prop) [DecidableRel R] (i j : α) :
    (adjacency R * adjacency R) i j =
      ((Finset.univ.filter (fun k => R i k ∧ R k j)).card : ℝ) := by
  classical
  rw [Matrix.mul_apply]
  calc
    (∑ k, adjacency R i k * adjacency R k j) =
        ∑ k, if R i k ∧ R k j then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : R i k <;> by_cases g : R k j <;> simp [adjacency, h, g]
    _ = _ := by simp

theorem antipodal_mean_zero {α : Type*} (u : α → ℝ) :
    (fun i => (u i + (-u i)) / 2) = 0 := by
  funext i
  simp

theorem unit_vectors_mean_need_not_unit :
    ∃ u v : Fin 1 → ℝ,
      Real.sqrt (∑ i, (u i)^2) = 1 ∧
      Real.sqrt (∑ i, (v i)^2) = 1 ∧
      Real.sqrt (∑ i, ((u i + v i) / 2)^2) = 0 := by
  refine ⟨fun _ => 1, fun _ => -1, ?_⟩
  norm_num

end Chapter04Closure

#print axioms Chapter04Closure.square_counts_intermediates
#print axioms Chapter04Closure.antipodal_mean_zero
#print axioms Chapter04Closure.unit_vectors_mean_need_not_unit
