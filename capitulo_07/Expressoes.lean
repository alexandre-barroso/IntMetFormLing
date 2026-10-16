import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open scoped BigOperators

namespace Chapter07Expressions

def X : Matrix (Fin 6) (Fin 2) ℚ := !![1,0;1,0;1,0;1,1;1,1;1,1]
def y : Fin 6 → ℚ := ![233,204,242,130,112,142]
def beta : Fin 2 → ℚ := ![679/3,-295/3]
def fitted : Fin 6 → ℚ := X.mulVec beta
def residual : Fin 6 → ℚ := y-fitted

theorem predictions (a b : ℚ) : X.mulVec ![a,b]=![a,a,a,a+b,a+b,a+b] := by
  ext i; fin_cases i <;> simp [X,Matrix.mulVec, dotProduct,Fin.sum_univ_two]

theorem normal_matrix : X.transpose*X=!![6,3;3,3] := by
  ext i j;fin_cases i <;> fin_cases j <;> norm_num [X,Matrix.mul_apply,Fin.sum_univ_succ]

theorem normal_target : X.transpose.mulVec y=![1063,384] := by
  ext i;fin_cases i <;> norm_num [X,y,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem normal_equation : (X.transpose*X).mulVec beta=X.transpose.mulVec y := by
  rw [normal_matrix,normal_target]
  ext i;fin_cases i <;> norm_num [beta,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem residuals_from_matrix : residual=![20/3,-67/3,47/3,2,-16,14] := by
  unfold residual fitted beta
  rw [predictions]
  decide +kernel

theorem residual_orthogonality : X.transpose.mulVec residual=0 := by
  ext i;fin_cases i <;> norm_num [residuals_from_matrix,X,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem residual_loss : (∑ i,residual i*residual i)=3734/3 := by
  norm_num [residuals_from_matrix,Fin.sum_univ_succ]

theorem loss_from_matrix (a b : ℚ) :
    (∑ i,(y-X.mulVec ![a,b]) i*(y-X.mulVec ![a,b]) i)=6*a^2+6*a*b+3*b^2-2126*a-768*b+204077 := by
  rw [predictions]
  simp [y,Fin.sum_univ_succ]
  ring

theorem paired_mean_general {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i,(a i-b i))/(n:ℝ)=(∑ i,a i)/(n:ℝ)-(∑ i,b i)/(n:ℝ) := by
  rw [Finset.sum_sub_distrib,sub_div]

theorem swap_count (n : ℕ) : Fintype.card (Fin n → Bool)=2^n := by simp

noncomputable def totalSquares (ys : Fin 6 → ℝ) : ℝ := ∑ i,(ys i-(∑ j,ys j)/6)^2

theorem correlation_simplification :
    (-295/2:ℝ)/Real.sqrt ((3/2)*(94493/6))= -295/Real.sqrt 94493 := by
  have h : Real.sqrt ((3/2:ℝ)*(94493/6))=Real.sqrt 94493/2 := by
    norm_num [Real.sqrt_div]
  rw [h]
  ring

theorem indicator_product (p q : ℝ) (hq : q=0 ∨ q=1) (h : q=1 → p=1) : p*q=q := by
  rcases hq with hq | hq
  · rw [hq];ring
  · rw [h hq,hq];ring

theorem nonidentifiable_coefficients (b c h q : ℝ) :
    b*q+c*q=(b+c)*q ∧ (b+h)*q+(c-h)*q=(b+c)*q := by constructor <;> ring

def plottedFitted : Fin 6 → ℚ := ![2263333333333/10000000000,2263333333333/10000000000,2263333333333/10000000000,128,128,128]

theorem fitted_graph_rounding : ∀ i, |plottedFitted i-fitted i|<1/20000000000 := by
  intro i
  fin_cases i <;> norm_num [plottedFitted,fitted,X,beta,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem residual_segments : ∀ i, y i-(plottedFitted i)=residual i+(fitted i-plottedFitted i) := by
  intro i
  simp [residual]

#print axioms fitted_graph_rounding
#print axioms residual_segments

end Chapter07Expressions

#print axioms Chapter07Expressions.predictions
#print axioms Chapter07Expressions.normal_matrix
#print axioms Chapter07Expressions.normal_target
#print axioms Chapter07Expressions.normal_equation
#print axioms Chapter07Expressions.residuals_from_matrix
#print axioms Chapter07Expressions.residual_orthogonality
#print axioms Chapter07Expressions.residual_loss
#print axioms Chapter07Expressions.loss_from_matrix
#print axioms Chapter07Expressions.paired_mean_general
#print axioms Chapter07Expressions.swap_count
#print axioms Chapter07Expressions.correlation_simplification
#print axioms Chapter07Expressions.indicator_product
#print axioms Chapter07Expressions.nonidentifiable_coefficients
