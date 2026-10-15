import Mathlib

open scoped BigOperators

namespace Chapter04Review

theorem rectangular_product_entry {m n p:ℕ} (A:Matrix (Fin m) (Fin n) ℝ)
    (B:Matrix (Fin n) (Fin p) ℝ) (i:Fin m) (j:Fin p) :
    (A*B) i j=∑ k,A i k*B k j := rfl

theorem transpose_product {m n p:ℕ} (A:Matrix (Fin m) (Fin n) ℝ)
    (B:Matrix (Fin n) (Fin p) ℝ) : (A*B).transpose=B.transpose*A.transpose :=
  Matrix.transpose_mul A B

theorem orthogonal_product_chain {d m n:ℕ} (U:Matrix (Fin m) (Fin d) ℝ)
    (V:Matrix (Fin n) (Fin d) ℝ) (Q:Matrix (Fin d) (Fin d) ℝ)
    (hQ:Q*Q.transpose=1) :
    (U*Q)*(V*Q).transpose=U*Q*Q.transpose*V.transpose ∧
    U*Q*Q.transpose*V.transpose=U*(1:Matrix (Fin d) (Fin d) ℝ)*V.transpose ∧
    U*(1:Matrix (Fin d) (Fin d) ℝ)*V.transpose=U*V.transpose := by
  constructor
  · rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  constructor
  · rw [Matrix.mul_assoc U Q Q.transpose,hQ]
  · rw [Matrix.mul_one]

theorem alignment_entry_general {n d:ℕ} (W1 W2:Matrix (Fin n) (Fin d) ℝ)
    (Q:Matrix (Fin d) (Fin d) ℝ) (i:Fin n) (j:Fin d) :
    (W1*Q) i j=(∑ k,W1 i k*Q k j) ∧
    (W1*Q-W2) i j=(W1*Q) i j-W2 i j := by constructor <;> rfl

end Chapter04Review
