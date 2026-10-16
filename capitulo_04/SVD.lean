import Mathlib

set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

namespace Chapter04SVD

noncomputable def sourceMatrix : Matrix (Fin 12) (Fin 9) ℝ := !![
  1,0,0,1,0,0,0,0,0;
  1,0,1,0,0,0,0,0,0;
  1,1,0,0,0,0,0,0,0;
  0,1,1,0,1,0,0,0,0;
  0,1,1,2,0,0,0,0,0;
  0,1,0,0,1,0,0,0,0;
  0,1,0,0,1,0,0,0,0;
  0,0,1,1,0,0,0,0,0;
  0,1,0,0,0,0,0,0,1;
  0,0,0,0,0,1,1,1,0;
  0,0,0,0,0,0,1,1,1;
  0,0,0,0,0,0,0,1,1]


noncomputable def leftInverse : Matrix (Fin 9) (Fin 12) ℝ := !![1/2,1/4,1/4,0,-1/4,0,0,0,0,0,0,0;
-1/2,-1/4,3/4,0,1/4,0,0,0,0,0,0,0;
-1/2,3/4,-1/4,0,1/4,0,0,0,0,0,0,0;
1/2,-1/4,-1/4,0,1/4,0,0,0,0,0,0,0;
1,-1/2,-1/2,1,-1/2,0,0,0,0,0,0,0;
1/2,1/4,-3/4,0,-1/4,0,0,0,1,1,-1,0;
0,0,0,0,0,0,0,0,0,0,1,-1;
-1/2,-1/4,3/4,0,1/4,0,0,0,-1,0,0,1;
1/2,1/4,-3/4,0,-1/4,0,0,0,1,0,0,0]


theorem source_left_inverse : leftInverse*sourceMatrix=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [leftInverse,sourceMatrix,Matrix.mul_apply,Fin.sum_univ_succ]

theorem source_injective : Function.Injective sourceMatrix.mulVec := by
  intro x y h
  have e := congrArg leftInverse.mulVec h
  simpa only [Matrix.mulVec_mulVec,source_left_inverse,Matrix.one_mulVec] using e

noncomputable def gram : Matrix (Fin 9) (Fin 9) ℝ := sourceMatrix.transpose*sourceMatrix

theorem gram_positive : gram.PosDef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,gram] using
    Matrix.PosDef.conjTranspose_mul_self sourceMatrix source_injective

noncomputable def eigenvalue : Fin 9 → ℝ := gram_positive.1.eigenvalues
noncomputable def V : Matrix (Fin 9) (Fin 9) ℝ := gram_positive.1.eigenvectorUnitary
noncomputable def sigmaValue (i : Fin 9) : ℝ := Real.sqrt (eigenvalue i)
noncomputable def sigma : Matrix (Fin 9) (Fin 9) ℝ := Matrix.diagonal sigmaValue
noncomputable def inverseSigma : Matrix (Fin 9) (Fin 9) ℝ := Matrix.diagonal (fun i => (sigmaValue i)⁻¹)
noncomputable def U : Matrix (Fin 12) (Fin 9) ℝ := sourceMatrix*V*inverseSigma

theorem eigenvalue_positive (i : Fin 9) : 0<eigenvalue i := gram_positive.eigenvalues_pos i

theorem singular_value_positive (i : Fin 9) : 0<sigmaValue i := Real.sqrt_pos.mpr (eigenvalue_positive i)

theorem singular_value_square (i : Fin 9) : sigmaValue i*sigmaValue i=eigenvalue i := by
  exact Real.mul_self_sqrt (le_of_lt (eigenvalue_positive i))

theorem right_orthonormal : V.transpose*V=1 := by
  simpa only [V,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_star_mul_self gram_positive.1.eigenvectorUnitary

theorem right_complete : V*V.transpose=1 := by
  simpa only [V,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_mul_star_self gram_positive.1.eigenvectorUnitary

theorem gram_diagonalization : V.transpose*gram*V=Matrix.diagonal eigenvalue := by
  have h := gram_positive.1.conjStarAlgAut_star_eigenvectorUnitary
  simpa only [Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id,Function.id_def,V,eigenvalue] using h

theorem inverse_sigma_mul_sigma : inverseSigma*sigma=1 := by
  rw [inverseSigma,sigma,Matrix.diagonal_mul_diagonal]
  have h : (fun i => (sigmaValue i)⁻¹*sigmaValue i)=(fun _ : Fin 9 => (1:ℝ)) := by
    funext i
    exact inv_mul_cancel₀ (ne_of_gt (singular_value_positive i))
  rw [h,Matrix.diagonal_one]

theorem inverse_eigenvalue_inverse : inverseSigma*Matrix.diagonal eigenvalue*inverseSigma=1 := by
  rw [inverseSigma,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  have h : (fun i => (sigmaValue i)⁻¹*eigenvalue i*(sigmaValue i)⁻¹)=(fun _ : Fin 9 => (1:ℝ)) := by
    funext i
    rw [←singular_value_square i]
    field_simp [ne_of_gt (singular_value_positive i)]
  rw [h,Matrix.diagonal_one]

theorem left_orthonormal : U.transpose*U=1 := by
  unfold U
  rw [Matrix.transpose_mul,Matrix.transpose_mul]
  have ht : inverseSigma.transpose=inverseSigma := by simp only [inverseSigma,Matrix.diagonal_transpose]
  rw [ht]
  calc
    inverseSigma * (V.transpose*sourceMatrix.transpose) * (sourceMatrix*V*inverseSigma) =
      inverseSigma * (V.transpose*gram*V) * inverseSigma := by simp only [gram,Matrix.mul_assoc]
    _=1 := by rw [gram_diagonalization,inverse_eigenvalue_inverse]

theorem reconstructs_source : U*sigma*V.transpose=sourceMatrix := by
  unfold U
  calc
    sourceMatrix*V*inverseSigma*sigma*V.transpose=
      sourceMatrix*(V*(inverseSigma*sigma)*V.transpose) := by simp only [Matrix.mul_assoc]
    _=sourceMatrix := by rw [inverse_sigma_mul_sigma,Matrix.mul_one,right_complete,Matrix.mul_one]

theorem source_svd_exists :
    ∃ (U : Matrix (Fin 12) (Fin 9) ℝ) (s : Fin 9 → ℝ) (V : Matrix (Fin 9) (Fin 9) ℝ),
      (∀ i,0<s i) ∧ U.transpose*U=1 ∧ V.transpose*V=1 ∧
        U*Matrix.diagonal s*V.transpose=sourceMatrix := by
  exact ⟨U,sigmaValue,V,singular_value_positive,left_orthonormal,right_orthonormal,reconstructs_source⟩

#print axioms source_svd_exists

end Chapter04SVD
