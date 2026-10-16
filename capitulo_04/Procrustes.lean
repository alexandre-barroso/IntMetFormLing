import Mathlib

open scoped BigOperators Matrix
namespace Chapter04Procrustes

variable {N d : ℕ}

def Orthogonal (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Q.transpose * Q = 1 ∧ Q * Q.transpose = 1

noncomputable def frobSq (A : Matrix (Fin N) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j)^2

noncomputable def loss (A B : Matrix (Fin N) (Fin d) ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ := frobSq (A * Q - B)

theorem orthogonal_one : Orthogonal (1 : Matrix (Fin d) (Fin d) ℝ) := by
  simp [Orthogonal]

theorem orthogonal_transpose {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : Orthogonal Q) : Orthogonal Q.transpose := by
  simpa [Orthogonal] using And.intro hQ.2 hQ.1

theorem orthogonal_mul {U V : Matrix (Fin d) (Fin d) ℝ}
    (hU : Orthogonal U) (hV : Orthogonal V) : Orthogonal (U * V) := by
  constructor
  · calc
      (U * V).transpose * (U * V) = V.transpose * (U.transpose * U) * V := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hU.1]; simpa using hV.1
  · calc
      (U * V) * (U * V).transpose = U * (V * V.transpose) * U.transpose := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hV.2]; simpa using hU.2

theorem column_squares {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Orthogonal Q)
    (j : Fin d) : ∑ i, (Q i j)^2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M j j) hQ.1
  simpa [Matrix.mul_apply, pow_two] using h

theorem entry_bounds {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Orthogonal Q)
    (i j : Fin d) : -1 ≤ Q i j ∧ Q i j ≤ 1 := by
  have hs : (Q i j)^2 ≤ ∑ k, (Q k j)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (Q k j)) (Finset.mem_univ i)
  rw [column_squares hQ j] at hs
  constructor <;> nlinarith [sq_nonneg (Q i j + 1), sq_nonneg (Q i j - 1)]

theorem frobSq_trace (A : Matrix (Fin N) (Fin d) ℝ) :
    frobSq A = Matrix.trace (A.transpose * A) := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

theorem frobSq_nonnegative (A : Matrix (Fin N) (Fin d) ℝ) : 0 ≤ frobSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem frobSq_sub (A B : Matrix (Fin N) (Fin d) ℝ) :
    frobSq (A - B) = frobSq A + frobSq B - 2 * Matrix.trace (A.transpose * B) := by
  rw [frobSq_trace, frobSq_trace, frobSq_trace]
  simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  have h : Matrix.trace (B.transpose * A) = Matrix.trace (A.transpose * B) := by
    calc
      Matrix.trace (B.transpose * A) = Matrix.trace (B.transpose * A).transpose :=
        (Matrix.trace_transpose _).symm
      _ = Matrix.trace (A.transpose * B) := by simp [Matrix.transpose_mul]
  rw [h]
  ring

theorem right_orthogonal_frobSq (A : Matrix (Fin N) (Fin d) ℝ)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Orthogonal Q) :
    frobSq (A * Q) = frobSq A := by
  rw [frobSq_trace, frobSq_trace, Matrix.transpose_mul]
  calc
    Matrix.trace (Q.transpose * A.transpose * (A * Q)) =
        Matrix.trace (Q.transpose * (A.transpose * A) * Q) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (Q * Q.transpose * (A.transpose * A)) := by
      exact Matrix.trace_mul_cycle Q.transpose (A.transpose * A) Q
    _ = Matrix.trace (A.transpose * A) := by rw [hQ.2, Matrix.one_mul]

theorem loss_trace_identity (A B : Matrix (Fin N) (Fin d) ℝ)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Orthogonal Q) :
    loss A B Q = frobSq A + frobSq B - 2 * Matrix.trace (Q.transpose * (A.transpose * B)) := by
  rw [loss, frobSq_sub, right_orthogonal_frobSq A hQ, Matrix.transpose_mul,
    Matrix.mul_assoc]

theorem trace_diagonal (R : Matrix (Fin d) (Fin d) ℝ) (σ : Fin d → ℝ) :
    Matrix.trace (R.transpose * Matrix.diagonal σ) = ∑ i, σ i * R i i := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, mul_comm]

theorem rotated_trace (Q U V : Matrix (Fin d) (Fin d) ℝ) (σ : Fin d → ℝ) :
    Matrix.trace (Q.transpose * (U * Matrix.diagonal σ * V.transpose)) =
      ∑ i, σ i * (U.transpose * Q * V) i i := by
  rw [← trace_diagonal]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    Matrix.trace (Q.transpose * (U * Matrix.diagonal σ * V.transpose)) =
        Matrix.trace ((Q.transpose * U * Matrix.diagonal σ) * V.transpose) := by
      simp [Matrix.mul_assoc]
    _ = Matrix.trace (V.transpose * (Q.transpose * U * Matrix.diagonal σ)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (V.transpose * (Q.transpose * U) * Matrix.diagonal σ) := by
      simp [Matrix.mul_assoc]

theorem singular_trace_bound {Q U V : Matrix (Fin d) (Fin d) ℝ}
    (hQ : Orthogonal Q) (hU : Orthogonal U) (hV : Orthogonal V)
    (σ : Fin d → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    Matrix.trace (Q.transpose * (U * Matrix.diagonal σ * V.transpose)) ≤ ∑ i, σ i := by
  rw [rotated_trace]
  apply Finset.sum_le_sum
  intro i _
  have hR := orthogonal_mul (orthogonal_mul (orthogonal_transpose hU) hQ) hV
  have hb := (entry_bounds hR i i).2
  simpa using mul_le_mul_of_nonneg_left hb (hσ i)

theorem singular_trace_attained {U V : Matrix (Fin d) (Fin d) ℝ}
    (hU : Orthogonal U) (hV : Orthogonal V) (σ : Fin d → ℝ) :
    Matrix.trace ((U * V.transpose).transpose * (U * Matrix.diagonal σ * V.transpose)) =
      ∑ i, σ i := by
  rw [rotated_trace]
  have hR : U.transpose * (U * V.transpose) * V = 1 := by
    calc
      U.transpose * (U * V.transpose) * V = (U.transpose * U) * (V.transpose * V) := by
        simp [Matrix.mul_assoc]
      _ = 1 := by rw [hU.1, hV.1, Matrix.one_mul]
  rw [hR]
  simp

theorem procrustes_conditional_minimum (A B : Matrix (Fin N) (Fin d) ℝ)
    {U V : Matrix (Fin d) (Fin d) ℝ} (σ : Fin d → ℝ)
    (hU : Orthogonal U) (hV : Orthogonal V) (hσ : ∀ i, 0 ≤ σ i)
    (hC : A.transpose * B = U * Matrix.diagonal σ * V.transpose) :
    Orthogonal (U * V.transpose) ∧
      ∀ Q, Orthogonal Q → loss A B (U * V.transpose) ≤ loss A B Q := by
  have hstar := orthogonal_mul hU (orthogonal_transpose hV)
  refine ⟨hstar, ?_⟩
  intro Q hQ
  rw [loss_trace_identity A B hstar, loss_trace_identity A B hQ, hC,
    singular_trace_attained hU hV]
  linarith [singular_trace_bound hQ hU hV σ hσ]

theorem orthogonal_closed : IsClosed {Q : Matrix (Fin d) (Fin d) ℝ | Orthogonal Q} := by
  unfold Orthogonal
  exact (isClosed_eq (by fun_prop) continuous_const).inter
    (isClosed_eq (by fun_prop) continuous_const)

theorem orthogonal_compact : IsCompact {Q : Matrix (Fin d) (Fin d) ℝ | Orthogonal Q} := by
  apply (isCompact_Icc (a := (fun _ _ => (-1 : ℝ))) (b := (fun _ _ => (1 : ℝ)))).of_isClosed_subset
    orthogonal_closed
  intro Q hQ
  constructor
  · intro i j
    exact (entry_bounds hQ i j).1
  · intro i j
    exact (entry_bounds hQ i j).2

theorem loss_continuous (A B : Matrix (Fin N) (Fin d) ℝ) : Continuous (loss A B) := by
  unfold loss frobSq
  fun_prop

theorem procrustes_minimizer_exists (A B : Matrix (Fin N) (Fin d) ℝ) :
    ∃ Q, Orthogonal Q ∧ ∀ R, Orthogonal R → loss A B Q ≤ loss A B R := by
  exact orthogonal_compact.exists_isMinOn ⟨1, orthogonal_one⟩
    (loss_continuous A B).continuousOn


theorem orthogonal_iff_transpose_mul (Q : Matrix (Fin d) (Fin d) ℝ) :
    Orthogonal Q ↔ Q.transpose * Q = 1 := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, mul_eq_one_comm.mp h⟩

theorem procrustes_conditional_frobenius_minimum (A B : Matrix (Fin N) (Fin d) ℝ)
    {U V : Matrix (Fin d) (Fin d) ℝ} (σ : Fin d → ℝ)
    (hU : Orthogonal U) (hV : Orthogonal V) (hσ : ∀ i, 0 ≤ σ i)
    (hC : A.transpose * B = U * Matrix.diagonal σ * V.transpose) :
    (U * V.transpose).transpose * (U * V.transpose) = 1 ∧
      ∀ Q, Q.transpose * Q = 1 →
        Real.sqrt (loss A B (U * V.transpose)) ≤ Real.sqrt (loss A B Q) := by
  obtain ⟨ho, hm⟩ := procrustes_conditional_minimum A B σ hU hV hσ hC
  refine ⟨ho.1, ?_⟩
  intro Q hQ
  exact Real.sqrt_le_sqrt (hm Q ((orthogonal_iff_transpose_mul Q).mpr hQ))

theorem procrustes_frobenius_minimizer_exists (A B : Matrix (Fin N) (Fin d) ℝ) :
    ∃ Q, Q.transpose * Q = 1 ∧
      ∀ R, R.transpose * R = 1 → Real.sqrt (loss A B Q) ≤ Real.sqrt (loss A B R) := by
  obtain ⟨Q,ho,hm⟩ := procrustes_minimizer_exists A B
  refine ⟨Q,ho.1,?_⟩
  intro R hR
  exact Real.sqrt_le_sqrt (hm R ((orthogonal_iff_transpose_mul R).mpr hR))

#print axioms procrustes_conditional_frobenius_minimum
#print axioms procrustes_frobenius_minimizer_exists

#print axioms procrustes_conditional_minimum
#print axioms orthogonal_compact
#print axioms procrustes_minimizer_exists
end Chapter04Procrustes
