import Mathlib

open scoped BigOperators
namespace Chapter07Closure

noncomputable def centered {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i - (∑ j, x j) / n

noncomputable def pearson {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (∑ i, centered x i * centered y i) /
    Real.sqrt ((∑ i, centered x i ^ 2) * (∑ i, centered y i ^ 2))

theorem normalized_dot_range {n : ℕ} (u v : Fin n → ℝ)
    (hu : 0 < ∑ i, u i ^ 2) (hv : 0 < ∑ i, v i ^ 2) :
    -1 ≤ (∑ i, u i * v i) / Real.sqrt ((∑ i, u i ^ 2) * (∑ i, v i ^ 2)) ∧
    (∑ i, u i * v i) / Real.sqrt ((∑ i, u i ^ 2) * (∑ i, v i ^ 2)) ≤ 1 := by
  have hp := mul_pos hu hv
  have hd := Real.sqrt_pos.mpr hp
  have hs := Real.sq_sqrt hp.le
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_one hd).mpr
    nlinarith

theorem pearson_range {n : ℕ} (x y : Fin n → ℝ)
    (hx : 0 < ∑ i, centered x i ^ 2) (hy : 0 < ∑ i, centered y i ^ 2) :
    -1 ≤ pearson x y ∧ pearson x y ≤ 1 :=
  normalized_dot_range (centered x) (centered y) hx hy

theorem centered_square_zero_iff {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, centered x i ^ 2) = 0 ↔ ∀ i, x i = (∑ j, x j) / n := by
  constructor
  · intro h i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (centered x j)) (Finset.mem_univ i)
    rw [h] at hi
    have hz : centered x i = 0 := by nlinarith [sq_nonneg (centered x i)]
    exact sub_eq_zero.mp hz
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    change (x i - (∑ j, x j) / n)^2 = 0
    rw [h i]
    ring

theorem centered_square_positive_iff_nonconstant {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    0 < (∑ i, centered x i ^ 2) ↔ ∃ i j, x i ≠ x j := by
  have hnonneg : 0 ≤ ∑ i, centered x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  constructor
  · intro h
    by_contra he
    push Not at he
    let k : Fin n := ⟨0, hn⟩
    have hx : x = fun _ => x k := by funext i; exact he i k
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hm : (∑ i, x i) / n = x k := by
      calc (∑ i, x i) / n = (∑ _i : Fin n, x k) / n := by rw [hx]
        _ = x k := by simp [hnr]
    have hz : (∑ i, centered x i ^ 2) = 0 := (centered_square_zero_iff x).mpr (fun i => (he i k).trans hm.symm)
    linarith
  · rintro ⟨i,j,hij⟩
    by_contra hp
    have hz : (∑ i, centered x i ^ 2) = 0 := le_antisymm (not_lt.mp hp) hnonneg
    have he := (centered_square_zero_iff x).mp hz
    exact hij ((he i).trans (he j).symm)

noncomputable def nonlinearX : Fin 3 → ℝ := ![-1, 0, 1]
noncomputable def nonlinearY : Fin 3 → ℝ := ![1, 0, 1]

theorem zero_correlation_nonlinear_relation :
    (∀ i, nonlinearY i = nonlinearX i ^ 2) ∧
    (∑ i, centered nonlinearX i ^ 2) = 2 ∧
    (∑ i, centered nonlinearY i ^ 2) = 2 / 3 ∧
    pearson nonlinearX nonlinearY = 0 ∧
    ¬ ∃ a b : ℝ, ∀ i, nonlinearY i = a + b * nonlinearX i := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [nonlinearX, nonlinearY]
  · norm_num [centered, nonlinearX, Fin.sum_univ_succ]
  · norm_num [centered, nonlinearY, Fin.sum_univ_succ]
  · norm_num [pearson, centered, nonlinearX, nonlinearY, Fin.sum_univ_succ]
  · rintro ⟨a, b, h⟩
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    norm_num [nonlinearX, nonlinearY] at h0 h1 h2
    change (1 : ℝ) = a + b * 1 at h2
    linarith

theorem zero_correlation_does_not_imply_empirical_independence :
    ((Finset.univ.filter (fun i : Fin 3 => nonlinearX i = 0 ∧ nonlinearY i = 0)).card : ℝ) / 3 ≠
    (((Finset.univ.filter (fun i : Fin 3 => nonlinearX i = 0)).card : ℝ) / 3) *
    (((Finset.univ.filter (fun i : Fin 3 => nonlinearY i = 0)).card : ℝ) / 3) := by
  have hx : (Finset.univ.filter (fun i : Fin 3 => nonlinearX i = 0)) = {1} := by
    ext i
    fin_cases i <;> norm_num [nonlinearX]
  have hy : (Finset.univ.filter (fun i : Fin 3 => nonlinearY i = 0)) = {1} := by
    ext i
    fin_cases i <;> norm_num [nonlinearY]
  have hxy : (Finset.univ.filter (fun i : Fin 3 => nonlinearX i = 0 ∧ nonlinearY i = 0)) = {1} := by
    ext i
    fin_cases i <;> norm_num [nonlinearX, nonlinearY]
  rw [hx, hy, hxy]
  norm_num

end Chapter07Closure

#print axioms Chapter07Closure.normalized_dot_range
#print axioms Chapter07Closure.pearson_range
#print axioms Chapter07Closure.centered_square_zero_iff
#print axioms Chapter07Closure.centered_square_positive_iff_nonconstant
#print axioms Chapter07Closure.zero_correlation_nonlinear_relation
#print axioms Chapter07Closure.zero_correlation_does_not_imply_empirical_independence
