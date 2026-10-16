import Mathlib

open MeasureTheory
open scoped Interval

namespace Chapter02Exposition

theorem zipf_decreasing (C alpha x y : ℝ) (hC : 0 < C) (ha : 0 < alpha)
    (hx : 0 < x) (hxy : x < y) : C*y^(-alpha) < C*x^(-alpha) := by
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx hxy (neg_neg_of_pos ha)) hC

theorem heaps_increasing (D beta x y : ℝ) (hD : 0 < D) (hb : 0 < beta)
    (hx : 0 ≤ x) (hxy : x < y) : D*x^beta < D*y^beta := by
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx hxy hb) hD

theorem heaps_sublinear_scale (D beta x k : ℝ) (hD : 0 < D)
    (hb : beta < 1) (hx : 0 < x) (hk : 1 < k) :
    D*(k*x)^beta < k*(D*x^beta) := by
  rw [Real.mul_rpow (by linarith : 0 ≤ k) hx.le]
  have h : k^beta < k := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hk hb
  have hp : 0 < D*x^beta := mul_pos hD (Real.rpow_pos_of_pos hx beta)
  nlinarith [mul_lt_mul_of_pos_right h hp]

theorem fractional_power_unique (x z : ℝ) (hx : 0 < x) (hz : 0 < z)
    (he : z^(100:ℕ) = x^(63:ℕ)) : z = x^((63:ℝ)/100) := by
  have target : (x^((63:ℝ)/100))^(100:ℕ) = x^(63:ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  apply (pow_left_inj₀ hz.le (Real.rpow_pos_of_pos hx _).le (by norm_num : (100:ℕ) ≠ 0)).mp
  exact he.trans target.symm

theorem surprise_decreasing (p q : ℝ) (hp : 0 < p) (hpq : p < q) :
    -Real.log q/Real.log 2 < -Real.log p/Real.log 2 := by
  exact div_lt_div_of_pos_right (neg_lt_neg (Real.log_lt_log hp hpq)) (Real.log_pos (by norm_num))

theorem inverse_duration_order (y₁ y₂ : ℝ) (h₁ : 0 < y₁) (h : y₁ < y₂) :
    1/y₂ < 1/y₁ := by
  exact one_div_lt_one_div_of_lt h₁ h

theorem primitive_constant_cancels (F : ℝ → ℝ) (a b c : ℝ) :
    (F b+c)-(F a+c)=F b-F a := by ring

theorem fundamental_theorem (F f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hF : ContinuousOn F (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x) :
    (∫ x in a..b, f x) = F b-F a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hd
  exact hf.intervalIntegrable_of_Icc hab

theorem normalization_preserves_only_unit_magnitude (c : ℝ) (w : ℝ → ℝ) (T : ℝ)
    (hw : (∫ t in (0:ℝ)..T, (w t)^2)=1) :
    (∫ t in (0:ℝ)..T, (c*w t)^2)=1 ↔ c=1 ∨ c= -1 := by
  have he : (∫ t in (0:ℝ)..T, (c*w t)^2)=c^2 := by
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, hw, mul_one]
  rw [he]
  constructor
  · intro h
    rcases (sq_eq_one_iff).mp h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl) <;> norm_num

end Chapter02Exposition

#print axioms Chapter02Exposition.zipf_decreasing
#print axioms Chapter02Exposition.heaps_increasing
#print axioms Chapter02Exposition.heaps_sublinear_scale
#print axioms Chapter02Exposition.fractional_power_unique
#print axioms Chapter02Exposition.surprise_decreasing
#print axioms Chapter02Exposition.inverse_duration_order
#print axioms Chapter02Exposition.primitive_constant_cancels
#print axioms Chapter02Exposition.fundamental_theorem
#print axioms Chapter02Exposition.normalization_preserves_only_unit_magnitude
