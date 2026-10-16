import Mathlib

namespace Chapter02IntegralReview

theorem equation_steps (n:ℝ) (h:(8/100:ℝ)*n=24/100) :
    100*((8/100:ℝ)*n)=100*(24/100:ℝ) ∧ 8*n=24 ∧ (8*n)/8=(24:ℝ)/8 ∧ n=3 := by
  constructor
  · exact congrArg (100*·) h
  constructor
  · linarith
  constructor <;> linarith

theorem negative_power (n b:ℝ) (hn:0<n) : n^b=1/n^(-b) := by
  rw [Real.rpow_neg (le_of_lt hn), one_div, inv_inv]

theorem derivative_identity (x:ℝ) : HasDerivAt (fun u:ℝ=>u) 1 x := hasDerivAt_id x

theorem derivative_log (x:ℝ) (hx:0<x) : HasDerivAt Real.log (1/x) x := by
  simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx)

theorem derivative_exp (x:ℝ) : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x

theorem derivative_log_composition (y:ℝ→ℝ) (n d:ℝ) (hy:0<y n) (h:HasDerivAt y d n) :
    HasDerivAt (fun u=>Real.log (y u)) (d/y n) n := by
  simpa [div_eq_mul_inv,mul_comm] using h.log (ne_of_gt hy)

theorem derivative_log_constant (a n:ℝ) : HasDerivAt (fun _:ℝ=>Real.log a) 0 n := hasDerivAt_const n (Real.log a)

theorem derivative_scaled_log (b n:ℝ) (hn:0<n) : HasDerivAt (fun u=>b*Real.log u) (b/n) n := by
  simpa [div_eq_mul_inv] using (Real.hasDerivAt_log (ne_of_gt hn)).const_mul b

theorem derivative_negative_linear (c n:ℝ) : HasDerivAt (fun u:ℝ=>-c*u) (-c) n := by
  simpa using (hasDerivAt_id n).const_mul (-c)

theorem derivative_affine (A b s:ℝ) : HasDerivAt (fun u:ℝ=>A+b*u) b s := by
  simpa using ((hasDerivAt_id s).const_mul b).const_add A

theorem numerator_rewrite (b c n:ℝ) (hn:n≠0) : b/n-c=(b-c*n)/n := by
  field_simp

theorem numerator_increasing (b c n₁ n₂:ℝ) (hc:c<0) (h:n₁<n₂) : b+(-c)*n₁<b+(-c)*n₂ := by
  nlinarith

theorem positive_square (u:ℝ) (hu:0<u) : 0<u^2 := sq_pos_of_pos hu

theorem negative_coefficient (c:ℝ) (hc:c<0) : 0< -c := neg_pos.mpr hc

theorem empirical_width (N:ℝ) : ((14/100:ℝ)-3/100)/N=(11/100:ℝ)/N := by ring

theorem surprise_base (p:ℝ) : -Real.logb 2 p = -Real.log p/Real.log 2 := by
  rw [Real.logb]
  ring

theorem constant_recovery (m L T:ℝ) (hm:m≠0) (h:T=m*L) : T/m=(m*L)/m ∧ (m*L)/m=L ∧ L=T/m := by
  subst T
  have hh:(m*L)/m=L := by field_simp
  exact ⟨rfl,hh,hh.symm⟩

theorem maximum_rounding :
    ((-227/1000:ℚ)/(-67/10000))=(227/1000:ℚ)/(67/10000) ∧
    (227/1000:ℚ)/(67/10000)=2270/67 ∧
    |(2270/67:ℚ)-(3388/100)|<1/200 := by norm_num

theorem positive_factors (a b c n:ℝ) (ha:0<a) (hn:0<n) :
    0<a ∧ 0<n^b ∧ 0<Real.exp (-c*n) ∧ 0<a*n^b*Real.exp (-c*n) := by
  exact ⟨ha,Real.rpow_pos_of_pos hn b,Real.exp_pos _,mul_pos (mul_pos ha (Real.rpow_pos_of_pos hn b)) (Real.exp_pos _)⟩

theorem surprise_nonnegative (p:ℝ) (hp:0<p) (hp1:p≤1) : 0≤ -Real.log p/Real.log 2 := by
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hp.le hp1)) (Real.log_nonneg (by norm_num))

theorem maximum_integer_rounding : |(2270/67:ℚ)-34|<1/2 := by norm_num

end Chapter02IntegralReview
