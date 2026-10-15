import Mathlib

namespace Chapter02Conditions

noncomputable def finiteSlope (m L₁ L₂ : ℝ) : Option ℝ :=
  if L₂ = L₁ then none else some ((m*L₂-m*L₁)/(L₂-L₁))

noncomputable def linearIncrement (m L h : ℝ) : Option ℝ :=
  if h = 0 then none else some ((m*(L+h)-m*L)/h)

noncomputable def reciprocalIncrement (u h : ℝ) : Option ℝ :=
  if u = 0 ∨ h = 0 ∨ u+h = 0 then none else some ((1/(u+h)-1/u)/h)

theorem finite_slope_domain (m L₁ L₂ : ℝ) :
    finiteSlope m L₁ L₂ = none ↔ L₂=L₁ := by
  by_cases h : L₂=L₁ <;> simp [finiteSlope,h]

theorem finite_slope_valid (m L₁ L₂ : ℝ) (h : L₂≠L₁) :
    finiteSlope m L₁ L₂ = some m := by
  simp only [finiteSlope,if_neg h,Option.some.injEq]
  have hd : L₂-L₁≠0 := sub_ne_zero.mpr h
  field_simp

theorem linear_increment_domain (m L h : ℝ) :
    linearIncrement m L h = none ↔ h=0 := by
  by_cases hh : h=0 <;> simp [linearIncrement,hh]

theorem linear_increment_valid (m L h : ℝ) (hh : h≠0) :
    linearIncrement m L h = some m := by
  simp only [linearIncrement,if_neg hh,Option.some.injEq]
  field_simp
  ring

theorem reciprocal_increment_domain (u h : ℝ) :
    reciprocalIncrement u h = none ↔ u=0 ∨ h=0 ∨ u+h=0 := by
  by_cases hx : u=0 ∨ h=0 ∨ u+h=0 <;> simp [reciprocalIncrement,hx]

theorem reciprocal_increment_valid (u h : ℝ) (hu : u≠0) (hh : h≠0) (huh : u+h≠0) :
    reciprocalIncrement u h = some (-1/(u*(u+h))) := by
  simp only [reciprocalIncrement,if_neg (not_or.mpr ⟨hu,not_or.mpr ⟨hh,huh⟩⟩),Option.some.injEq]
  field_simp
  ring

theorem logarithm_inverse_domain (x : ℝ) (hx : 0<x) :
    Real.exp (Real.log x)=x := Real.exp_log hx

theorem logarithm_zero_outside_domain : ¬ (0 < (0:ℝ)) ∧ Real.exp (Real.log 0)≠0 := by norm_num

theorem reciprocal_derivative_domain (u : ℝ) (hu : u≠0) :
    HasDerivAt (fun x : ℝ=>1/x) (-1/u^2) u := by
  convert! (hasDerivAt_id u).inv hu using 1
  funext x
  simp only [Pi.inv_apply, id_eq, one_div]

theorem logarithm_mal_chain (a b c n : ℝ) (ha:0<a) (hn:0<n) :
    Real.log (a*n^b*Real.exp (-c*n)) = Real.log a+Real.log (n^b)+Real.log (Real.exp (-c*n)) ∧
    Real.log a+Real.log (n^b)+Real.log (Real.exp (-c*n)) = Real.log a+b*Real.log n-c*n := by
  constructor
  · rw [Real.log_mul (ne_of_gt (mul_pos ha (Real.rpow_pos_of_pos hn b))) (Real.exp_ne_zero _),
      Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.rpow_pos_of_pos hn b))]
  · rw [Real.log_rpow hn,Real.log_exp]
    ring

theorem logarithm_composition_chain (A C r alpha lambda ell : ℝ)
    (hA:0<A) (hC:0<C) (hr:0<r)
    (h:A*Real.exp (-lambda*ell)=C*r^(-alpha)) :
    Real.log (A*Real.exp (-lambda*ell))=Real.log (C*r^(-alpha)) ∧
    Real.log A+Real.log (Real.exp (-lambda*ell))=Real.log C+Real.log (r^(-alpha)) ∧
    Real.log A-lambda*ell=Real.log C-alpha*Real.log r := by
  have hlog := congrArg Real.log h
  refine ⟨hlog,?_,?_⟩
  · simpa [Real.log_mul (ne_of_gt hA) (Real.exp_ne_zero _),Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hr _))] using hlog
  · rw [Real.log_mul (ne_of_gt hA) (Real.exp_ne_zero _),Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hr _)),Real.log_exp,Real.log_rpow hr] at hlog
    nlinarith

#print axioms logarithm_mal_chain
#print axioms logarithm_composition_chain

theorem logarithm_powers_sum (u v:ℝ) :
    Real.logb 2 ((2:ℝ)^u*(2:ℝ)^v)=u+v ∧
    Real.logb 2 ((2:ℝ)^u)+Real.logb 2 ((2:ℝ)^v)=u+v := by
  have hu := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) u
  have hv := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) v
  rw [Real.logb_mul (ne_of_gt hu) (ne_of_gt hv)]
  simp [Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<2),Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]

theorem composition_rearrangement_steps (a c alpha r lam ell:ℝ) (hlam:lam≠0)
    (h:a-lam*ell=c-alpha*r) :
    -lam*ell=c-a-alpha*r ∧ lam*ell=alpha*r+a-c ∧
    ell=(alpha*r+a-c)/lam ∧ (alpha*r+a-c)/lam=(alpha/lam)*r+(a-c)/lam := by
  refine ⟨by linarith,by linarith,?_,?_⟩
  · apply (eq_div_iff hlam).mpr
    nlinarith
  · ring

#print axioms logarithm_powers_sum
#print axioms composition_rearrangement_steps

end Chapter02Conditions

#print axioms Chapter02Conditions.finite_slope_domain
#print axioms Chapter02Conditions.finite_slope_valid
#print axioms Chapter02Conditions.linear_increment_domain
#print axioms Chapter02Conditions.linear_increment_valid
#print axioms Chapter02Conditions.reciprocal_increment_domain
#print axioms Chapter02Conditions.reciprocal_increment_valid
#print axioms Chapter02Conditions.logarithm_inverse_domain
#print axioms Chapter02Conditions.logarithm_zero_outside_domain
#print axioms Chapter02Conditions.reciprocal_derivative_domain
