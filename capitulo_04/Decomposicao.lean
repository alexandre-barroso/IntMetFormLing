import Mathlib
open scoped BigOperators
namespace Chapter04Decomposition

noncomputable def reconstruct {m n k:ℕ} (U:Matrix (Fin m) (Fin k) ℝ) (sigma:Fin k→ℝ) (V:Matrix (Fin n) (Fin k) ℝ) : Matrix (Fin m) (Fin n) ℝ := U*Matrix.diagonal sigma*V.transpose

theorem reconstruction_coordinate {m n k:ℕ} (U:Matrix (Fin m) (Fin k) ℝ) (sigma:Fin k→ℝ) (V:Matrix (Fin n) (Fin k) ℝ) (i:Fin m) (j:Fin n) :
    reconstruct U sigma V i j=∑ r,U i r*sigma r*V j r := by
  unfold reconstruct
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply]

theorem rank_two (U:Matrix (Fin 12) (Fin 2) ℝ) (V:Matrix (Fin 9) (Fin 2) ℝ)
    (S invS:Matrix (Fin 2) (Fin 2) ℝ) (hU:U.transpose*U=1) (hV:V.transpose*V=1) (hS:invS*S=1) :
    (U*S*V.transpose).rank=2 := by
  have hproduct : (invS*U.transpose)*(U*S*V.transpose)*V=(1:Matrix (Fin 2) (Fin 2) ℝ) := by
    calc
      (invS*U.transpose)*(U*S*V.transpose)*V=invS*(U.transpose*U)*S*(V.transpose*V) := by simp only [Matrix.mul_assoc]
      _=1 := by simp only [hU,hV,Matrix.mul_one,hS]
  have hlo : 2≤(U*S*V.transpose).rank := by
    have h:=(Matrix.rank_mul_le_left ((invS*U.transpose)*(U*S*V.transpose)) V).trans
      (Matrix.rank_mul_le_right (invS*U.transpose) (U*S*V.transpose))
    rw [hproduct,Matrix.rank_one,Fintype.card_fin] at h
    exact h
  have hhi : (U*S*V.transpose).rank≤2 :=
    (Matrix.rank_mul_le_left (U*S) V.transpose).trans ((Matrix.rank_mul_le_left U S).trans (Matrix.rank_le_width U))
  exact le_antisymm hhi hlo

theorem published_diagonal_inverse :
    (!![100/334,0;0,100/254]:Matrix (Fin 2) (Fin 2) ℝ)*!![334/100,0;0,254/100]=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]

#print axioms reconstruction_coordinate
#print axioms rank_two
#print axioms published_diagonal_inverse
end Chapter04Decomposition
