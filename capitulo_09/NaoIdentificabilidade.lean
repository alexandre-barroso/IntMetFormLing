import Mathlib

open scoped BigOperators

namespace Chapter09Nonidentifiability

noncomputable def f1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  2 * M i i / ((∑ j, M i j) + ∑ j, M j i)

theorem transpose_preserves_f1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    f1 M.transpose i = f1 M i := by
  simp [f1, Matrix.transpose_apply, add_comm]

theorem transpose_preserves_domain {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (h : 0 < (∑ j, M i j) + ∑ j, M j i) :
    0 < (∑ j, M.transpose i j) + ∑ j, M.transpose j i := by
  simpa [Matrix.transpose_apply, add_comm] using h

theorem transpose_preserves_macro_f1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, f1 M.transpose i) / n = (∑ i, f1 M i) / n := by
  simp only [transpose_preserves_f1]

noncomputable def confusion (t : ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => if i = j then 1 else if i = 0 ∧ j = 1 then t else 0

theorem confusion_nonnegative {t : ℝ} (ht : 0 < t) (i j : Fin 9) :
    0 ≤ confusion t i j := by
  simp only [confusion]
  split_ifs <;> linarith

theorem confusion_denominator_positive {t : ℝ} (ht : 0 < t) (i : Fin 9) :
    0 < (∑ j, confusion t i j) + ∑ j, confusion t j i := by
  have hr := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => confusion_nonnegative ht i j)
    (Finset.mem_univ i)
  have hc := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => confusion_nonnegative ht j i)
    (Finset.mem_univ i)
  have hd : confusion t i i = 1 := by simp [confusion]
  rw [hd] at hr hc
  linarith

theorem confusion_differs_from_transpose {t : ℝ} (ht : 0 < t) :
    confusion t ≠ (confusion t).transpose := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 9) (Fin 9) ℝ => M 0 1) h
  norm_num [confusion, Matrix.transpose_apply] at he
  linarith

theorem positive_integer_confusions_same_f1 (t : ℕ) (ht : 0 < t) :
    confusion (t : ℝ) ≠ (confusion (t : ℝ)).transpose ∧
    (∀ i, 0 < (∑ j, confusion (t : ℝ) i j) + ∑ j, confusion (t : ℝ) j i) ∧
    (∀ i, f1 (confusion (t : ℝ)).transpose i = f1 (confusion (t : ℝ)) i) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  exact ⟨confusion_differs_from_transpose ht', confusion_denominator_positive ht',
    transpose_preserves_f1 _⟩

end Chapter09Nonidentifiability
