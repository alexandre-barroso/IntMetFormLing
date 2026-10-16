import Mathlib

open scoped BigOperators

namespace Chapter05Closure

theorem sum_squares_zero_iff {α : Type*} [Fintype α] (x : α → ℝ) (m : ℝ) :
    (∑ i, (x i - m)^2) = 0 ↔ ∀ i, x i = m := by
  constructor
  · intro h i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg (x j - m))).mp h i (Finset.mem_univ i)
    nlinarith [sq_nonneg (x i - m)]
  · intro h
    simp [h]

theorem normalized_variance_zero_iff {α : Type*} [Fintype α]
    (x : α → ℝ) (m d : ℝ) (hd : 0 < d) :
    (∑ i, (x i - m)^2) / d = 0 ↔ ∀ i, x i = m := by
  rw [div_eq_zero_iff, or_iff_left (ne_of_gt hd), sum_squares_zero_iff]

theorem sample_variance_zero_iff {n : ℕ} (x : Fin n → ℝ) (hn : 1 < n) :
    (∑ i, (x i - (∑ j, x j) / n)^2) / (n - 1 : ℝ) = 0 ↔
      ∀ i, x i = (∑ j, x j) / n := by
  apply normalized_variance_zero_iff
  have h : (1 : ℝ) < n := by exact_mod_cast hn
  linarith

theorem population_variance_zero_iff {n : ℕ} (x : Fin n → ℝ) (hn : 0 < n) :
    (∑ i, (x i - (∑ j, x j) / n)^2) / (n : ℝ) = 0 ↔
      ∀ i, x i = (∑ j, x j) / n := by
  apply normalized_variance_zero_iff
  exact_mod_cast hn

theorem dispersion_zero_iff {α : Type*} [Fintype α] (o s : α → ℝ) :
    (∑ i, |o i - s i|) / 2 = 0 ↔ o = s := by
  constructor
  · intro h
    have hsum : (∑ i, |o i - s i|) = 0 := by linarith
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => abs_nonneg (o j - s j))).mp hsum i (Finset.mem_univ i)
    exact sub_eq_zero.mp (abs_eq_zero.mp hi)
  · intro h
    subst s
    simp

theorem excess_deficit_balance {α : Type*} [Fintype α] (o s : α → ℝ)
    (hmass : ∑ i, o i = ∑ i, s i) :
    (∑ i, max (o i - s i) 0) = ∑ i, max (s i - o i) 0 := by
  have point : ∀ i, max (o i - s i) 0 - max (s i - o i) 0 = o i - s i := by
    intro i
    rcases le_total (o i) (s i) with h | h
    · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
      ring
  have h : (∑ i, max (o i - s i) 0) - (∑ i, max (s i - o i) 0) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [point]
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  exact sub_eq_zero.mp h

theorem half_absolute_sum_is_excess {α : Type*} [Fintype α] (o s : α → ℝ)
    (hmass : ∑ i, o i = ∑ i, s i) :
    (∑ i, |o i - s i|) / 2 = ∑ i, max (o i - s i) 0 := by
  have point : ∀ i, |o i - s i| = max (o i - s i) 0 + max (s i - o i) 0 := by
    intro i
    rcases le_total (o i) (s i) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h),
        max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h),
        max_eq_right (sub_nonpos.mpr h)]
      ring
  simp_rw [point]
  rw [Finset.sum_add_distrib, ← excess_deficit_balance o s hmass]
  ring

end Chapter05Closure

#print axioms Chapter05Closure.sum_squares_zero_iff
#print axioms Chapter05Closure.normalized_variance_zero_iff
#print axioms Chapter05Closure.sample_variance_zero_iff
#print axioms Chapter05Closure.population_variance_zero_iff
#print axioms Chapter05Closure.dispersion_zero_iff
#print axioms Chapter05Closure.excess_deficit_balance
#print axioms Chapter05Closure.half_absolute_sum_is_excess
