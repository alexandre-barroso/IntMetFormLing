import Mathlib

open scoped BigOperators

namespace Capitulo05Dispersao

theorem c05_d03_point_bound (o s m : ℝ)
    (ho : 0 ≤ o) (ho1 : o ≤ 1) (hm : 0 ≤ m)
    (hm1 : m ≤ 1) (hms : m ≤ s) :
    |o - s| ≤ o + s - 2 * m * o := by
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hm1) ho]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ho1) hm]

theorem c05_d03_total_bound {n : ℕ} (o s : Fin n → ℝ) (m : ℝ)
    (ho : ∀ i, 0 ≤ o i) (ho1 : ∀ i, o i ≤ 1)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hms : ∀ i, m ≤ s i)
    (hon : ∑ i, o i = 1) (hsn : ∑ i, s i = 1) :
    (∑ i, |o i - s i|) / 2 ≤ 1 - m := by
  have h : (∑ i, |o i - s i|) ≤ ∑ i, (o i + s i - 2*m*o i) :=
    Finset.sum_le_sum (fun i _ => c05_d03_point_bound (o i) (s i) m
      (ho i) (ho1 i) hm hm1 (hms i))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hon, hsn, mul_one] at h
  linarith

theorem c05_d03_bound_attained {n : ℕ} (s : Fin n → ℝ) (j : Fin n)
    (hs : ∀ i, 0 ≤ s i) (hsj : s j ≤ 1) (hsn : ∑ i, s i = 1) :
    (∑ i, |(if i = j then 1 else 0) - s i|) / 2 = 1 - s j := by
  classical
  have hi : ∀ i, |(if i = j then 1 else 0) - s i| =
      (if i = j then 1 - 2*s i else 0) + s i := by
    intro i
    by_cases h : i = j
    · subst i
      simp only [ite_true, abs_of_nonneg (sub_nonneg.mpr hsj)]
      ring
    · simp [h, abs_of_nonneg (hs i)]
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hsn]
  ring

theorem c05_r05_no_dispersion {n : ℕ} (s : Fin n → ℝ) :
    (∑ i, |s i - s i|) / 2 = 0 := by simp

end Capitulo05Dispersao

#print axioms Capitulo05Dispersao.c05_d03_point_bound
#print axioms Capitulo05Dispersao.c05_d03_total_bound
#print axioms Capitulo05Dispersao.c05_d03_bound_attained
#print axioms Capitulo05Dispersao.c05_r05_no_dispersion
