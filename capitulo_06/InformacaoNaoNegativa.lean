import capitulo_06.Expressoes

open scoped BigOperators

namespace Chapter06InformationNonnegative

theorem log_ratio_lower (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsupport : 0 < p → 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  by_cases hzero : p = 0
  · simp [hzero, hq]
  · have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hzero)
    have hqq := hsupport hpp
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hqq hpp)) hp
    have reverse : p * Real.log (p / q) = -(p * Real.log (q / p)) := by
      rw [Real.log_div (ne_of_gt hpp) (ne_of_gt hqq),
        Real.log_div (ne_of_gt hqq) (ne_of_gt hpp)]
      ring
    have rhs : p * (q / p - 1) = q - p := by
      field_simp
    rw [rhs] at h
    rw [reverse]
    linarith

theorem independent_reference_total {m n : ℕ}
    (p : Matrix (Fin m) (Fin n) ℝ) (hn : ∑ i, ∑ j, p i j = 1) :
    (∑ i, ∑ j, (∑ k, p i k) * (∑ k, p k j)) = 1 := by
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => p i j), hn]
  simp [hn]

theorem mutual_information_nonnegative {m n : ℕ}
    (p : Matrix (Fin m) (Fin n) ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (hn : ∑ i, ∑ j, p i j = 1) :
    0 ≤ Chapter06Expressions.mutualInformation p := by
  have term : ∀ i j, p i j - (∑ k, p i k) * (∑ k, p k j) ≤
      p i j * Real.log (p i j / ((∑ k, p i k) * (∑ k, p k j))) := by
    intro i j
    apply log_ratio_lower _ _ (hp i j)
    · exact mul_nonneg (Finset.sum_nonneg (fun k _ => hp i k))
        (Finset.sum_nonneg (fun k _ => hp k j))
    · intro hij
      exact mul_pos (lt_of_lt_of_le hij (Chapter06Expressions.entry_le_row p hp i j))
        (lt_of_lt_of_le hij (Chapter06Expressions.entry_le_column p hp i j))
  have sumBound := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => term i j))
  have natural_nonnegative : 0 ≤ ∑ i, ∑ j,
      p i j * Real.log (p i j / ((∑ k, p i k) * (∑ k, p k j))) := by
    simp_rw [Finset.sum_sub_distrib] at sumBound
    rw [hn, independent_reference_total p hn] at sumBound
    simpa using sumBound
  have change_base : Chapter06Expressions.mutualInformation p =
      (∑ i, ∑ j, p i j * Real.log (p i j / ((∑ k, p i k) * (∑ k, p k j)))) /
        Real.log 2 := by
    unfold Chapter06Expressions.mutualInformation
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    unfold Real.logb
    ring
  rw [change_base]
  exact div_nonneg natural_nonnegative (Real.log_pos (by norm_num)).le

theorem conditioning_reduces_average_entropy {m n : ℕ}
    (p : Matrix (Fin m) (Fin n) ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (hn : ∑ i, ∑ j, p i j = 1) :
    Chapter06Expressions.conditionalEntropy p ≤
      Chapter06Expressions.entropy (fun j => ∑ i, p i j) := by
  have h := mutual_information_nonnegative p hp hn
  rw [Chapter06Expressions.information_entropy_identity_valid p hp] at h
  linarith

end Chapter06InformationNonnegative

#print axioms Chapter06InformationNonnegative.log_ratio_lower
#print axioms Chapter06InformationNonnegative.independent_reference_total
#print axioms Chapter06InformationNonnegative.mutual_information_nonnegative
#print axioms Chapter06InformationNonnegative.conditioning_reduces_average_entropy
