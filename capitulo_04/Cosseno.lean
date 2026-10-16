import capitulo_04.Expressoes
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace Chapter04Cosine
open Chapter04Expressions

theorem length_nonnegative {n : ℕ} (v : Fin n → ℝ) : 0 ≤ length v := Real.sqrt_nonneg _

theorem length_squared {n : ℕ} (v : Fin n → ℝ) : length v ^ 2 = ∑ i, v i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem positive_scaling_length {n : ℕ} (v : Fin n → ℝ) (a : ℝ) (ha : 0 < a) :
    length (fun i => a * v i) = a * length v := by
  unfold length
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_pos ha]

theorem cosine_positive_scaling {n : ℕ} (v w : Fin n → ℝ) (a : ℝ) (ha : 0 < a) :
    cosine (fun i => a * v i) w = cosine v w := by
  unfold cosine
  rw [positive_scaling_length v a ha]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt ha)

theorem cosine_range {n : ℕ} (v w : Fin n → ℝ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hnv : ∀ i, 0 ≤ v i) (hnw : ∀ i, 0 ≤ w i) : 0 ≤ cosine v w ∧ cosine v w ≤ 1 := by
  have hp := mul_pos (length_positive v hv) (length_positive w hw)
  have hsum : 0 ≤ ∑ i, v i * w i := Finset.sum_nonneg (fun i _ => mul_nonneg (hnv i) (hnw i))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  have he : (length v * length w) ^ 2 = (∑ i, v i ^ 2) * (∑ i, w i ^ 2) := by
    rw [mul_pow, length_squared, length_squared]
  have hle : (∑ i, v i * w i) ≤ length v * length w := by nlinarith
  unfold cosine
  exact ⟨div_nonneg hsum hp.le, (div_le_one hp).mpr hle⟩

theorem cosine_normalized {n : ℕ} (v w : Fin n → ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    cosine (fun i => v i / length v) (fun i => w i / length w) = cosine v w := by
  unfold cosine
  rw [unit_normalization v hv, unit_normalization w hw]
  simp only [mul_one, div_one]
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div]

theorem normalization_chain {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) :
    length (fun i => v i / length v) = length v / length v ∧ length v / length v = 1 := by
  have h := ne_of_gt (length_positive v hv)
  rw [unit_normalization v hv, div_self h]
  exact ⟨rfl,rfl⟩

#print axioms cosine_positive_scaling
#print axioms cosine_range
#print axioms cosine_normalized
#print axioms normalization_chain
end Chapter04Cosine
