import Mathlib
namespace Chapter07Review
theorem indicator_numeric_cases (p q:ℝ) (hq:q=0 ∨ q=1) (h:q=1 → p=1) : p*q=q := by rcases hq with hq|hq; simp [hq]; simp [hq,h hq]
theorem fitted_line_substitution (a b x:ℝ) (ha:a=679/3) (hb:b= -295/3) : a+b*x=679/3-(295/3)*x := by rw [ha,hb]; ring
theorem minimum_coefficient_conditions (a b:ℝ) : (a=679/3 ∧ b= -295/3) ↔ (a=679/3 ∧ a+b=128) := by constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
theorem c07_e0241_integral (a b:ℝ) : HasDerivAt (fun t:ℝ=>6*t*b) (6*b) a ∧ HasDerivAt (fun t:ℝ=>6*a*t) (6*a) b := by constructor; simpa using (((hasDerivAt_id a).const_mul 6).mul_const b); simpa using ((hasDerivAt_id b).const_mul (6*a))
theorem c07_e0248_integral (a b:ℝ) : HasDerivAt (fun _:ℝ=>3*b^2) 0 a ∧ HasDerivAt (fun t:ℝ=>3*t^2) (6*b) b := by constructor; exact hasDerivAt_const a (3*b^2); exact ((hasDerivAt_pow 2 b).const_mul (3:ℝ)).congr_deriv (by ring)
theorem c07_e0251_integral (a b:ℝ) :
 ((12*a+6*b-2126=0 ∧ 6*a+6*b-768=0) ↔ (6*a+3*b=1063 ∧ 3*a+3*b=384)) ∧
 ((6*a+3*b=1063 ∧ 3*a+3*b=384) → (3*a=679 ∧ a=679/3 ∧ 679+3*b=384 ∧ 3*b= -295 ∧ b= -295/3)) := by
 constructor
 · constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
 · rintro ⟨h1,h2⟩
   refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith
theorem redundant_indicator_chain (p q b c:ℝ) (h:p*q=q) : b*q+c*p*q=b*q+c*q ∧ b*q+c*q=(b+c)*q := by
 constructor
 · calc b*q+c*p*q=b*q+c*(p*q):=by ring
        _=b*q+c*q:=by rw [h]
 · ring
def reviewDesign : Matrix (Fin 6) (Fin 2) ℝ := !![1,0;1,0;1,0;1,1;1,1;1,1]
theorem normal_matrix_arbitrary_coefficients (a b:ℝ) : (reviewDesign.transpose*reviewDesign).mulVec ![a,b] = ![6*a+3*b,3*a+3*b] := by
 ext i
 fin_cases i <;> norm_num [reviewDesign,Matrix.mulVec,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring
def reviewObserved : Fin 6 → ℚ := ![233,204,242,130,112,142]
def reviewPredicted : Fin 6 → ℚ := ![2263333333333/10000000000,2263333333333/10000000000,2263333333333/10000000000,128,128,128]
def reviewVertical (i:Fin 6) : (ℚ×ℚ)×(ℚ×ℚ) := (((i.val+1:ℕ),reviewObserved i),((i.val+1:ℕ),reviewPredicted i))
def reviewHorizontal : List ((ℚ×ℚ)×(ℚ×ℚ)) := [((1,reviewPredicted 0),(3,reviewPredicted 2)),((4,reviewPredicted 3),(6,reviewPredicted 5))]
theorem regression_plot_coordinates :
 (List.finRange 6).map reviewVertical = [((1,233),(1,2263333333333/10000000000)),((2,204),(2,2263333333333/10000000000)),((3,242),(3,2263333333333/10000000000)),((4,130),(4,128)),((5,112),(5,128)),((6,142),(6,128))] ∧
 reviewHorizontal = [((1,2263333333333/10000000000),(3,2263333333333/10000000000)),((4,128),(6,128))] := by
 decide +kernel
end Chapter07Review
