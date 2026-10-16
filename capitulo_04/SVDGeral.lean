import Mathlib
import capitulo_04.Procrustes

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Chapter04SVDGeral

theorem real_square_svd_exists {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (U V : Matrix (Fin n) (Fin n) ℝ) (s : Fin n → ℝ),
      U.transpose*U=1 ∧ U*U.transpose=1 ∧
      V.transpose*V=1 ∧ V*V.transpose=1 ∧
      (∀ i,0 ≤ s i) ∧ U*Matrix.diagonal s*V.transpose=M := by
  classical
  let G := M.transpose*M
  have hg : G.PosSemidef := by
    simpa only [G,Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self M
  let V : Matrix (Fin n) (Fin n) ℝ := hg.1.eigenvectorUnitary
  let e : Fin n → ℝ := hg.1.eigenvalues
  let s : Fin n → ℝ := fun i => Real.sqrt (e i)
  let R := M*V
  let W := R*Matrix.diagonal (fun i => (s i)⁻¹)
  let w : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => W i j)
  let S : Set (Fin n) := {i | 0<e i}
  have he : ∀ i,0≤e i := hg.eigenvalues_nonneg
  have hs : ∀ i,0 ≤ s i := fun i => Real.sqrt_nonneg _
  have hs2 : ∀ i,s i*s i=e i := fun i => Real.mul_self_sqrt (he i)
  have hv : V.transpose*V=1 := by
    simpa only [V,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hg.1.eigenvectorUnitary
  have hvv : V*V.transpose=1 := by
    simpa only [V,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hg.1.eigenvectorUnitary
  have hdiag : V.transpose*G*V=Matrix.diagonal e := by
    simpa only [V,e,Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,RCLike.ofReal_real_eq_id,Function.comp_def,Function.id_def] using
      hg.1.conjStarAlgAut_star_eigenvectorUnitary
  have hR : R.transpose*R=Matrix.diagonal e := by
    change (M*V).transpose*(M*V)=_
    rw [Matrix.transpose_mul]
    simpa only [G,Matrix.mul_assoc] using hdiag
  have hW : W.transpose*W=Matrix.diagonal (fun i => if 0<e i then 1 else 0) := by
    change (R*Matrix.diagonal (fun i => (s i)⁻¹)).transpose*
      (R*Matrix.diagonal (fun i => (s i)⁻¹))=_
    rw [Matrix.transpose_mul,Matrix.diagonal_transpose]
    calc
      Matrix.diagonal (fun i => (s i)⁻¹)*R.transpose*(R*Matrix.diagonal (fun i => (s i)⁻¹))=
        Matrix.diagonal (fun i => (s i)⁻¹)*(R.transpose*R)*Matrix.diagonal (fun i => (s i)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _=Matrix.diagonal (fun i => if 0<e i then 1 else 0) := by
        rw [hR,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        by_cases hi : 0<e i
        · simp only [if_pos hi]
          have hz : s i≠0 := ne_of_gt (Real.sqrt_pos.mpr hi)
          rw [←hs2 i]
          field_simp
        · have hz : e i=0 := le_antisymm (le_of_not_gt hi) (he i)
          simp [hz]
  have hw : Orthonormal ℝ (S.restrict w) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i.1 j.1) hW
    change (∑ k,W k i.1*W k j.1)=(if i.1=j.1 then if 0<e i.1 then 1 else 0 else 0) at hij
    have hi : 0<e i.1 := i.2
    have hinner : inner ℝ (w i.1) (w j.1)=∑k,W k i.1*W k j.1 := by
      simp only [w,EuclideanSpace.inner_toLp_toLp,dotProduct,Pi.star_apply,star_trivial]
      apply Finset.sum_congr rfl
      intro k _
      ring
    change inner ℝ (w i.1) (w j.1)=_
    rw [hinner,hij]
    simp only [if_pos hi,Subtype.ext_iff]
  obtain ⟨b,hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=Fintype.card (Fin n))
  let U : Matrix (Fin n) (Fin n) ℝ := fun i j => b j i
  have hu : U.transpose*U=1 := by
    ext i j
    have h := b.inner_eq_ite i j
    have hinner : inner ℝ (b i) (b j)=∑k,U k i*U k j := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Pi.star_apply,star_trivial]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [U]
      ring
    rw [hinner] at h
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using h
  have huu : U*U.transpose=1 := mul_eq_one_comm.mp hu
  have hzero (j : Fin n) (hj : e j=0) : ∀i,R i j=0 := by
    intro i
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j) hR
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.diagonal_apply_eq,hj] at h
    have hle : R i j*R i j≤∑k,R k j*R k j :=
      Finset.single_le_sum (fun k _ => mul_self_nonneg (R k j)) (Finset.mem_univ i)
    rw [h] at hle
    nlinarith [mul_self_nonneg (R i j)]
  have hUS : U*Matrix.diagonal s=R := by
    ext i j
    rw [Matrix.mul_diagonal]
    by_cases hj : 0<e j
    · have hjS : j∈S := hj
      have hbj := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (hb j hjS)
      change U i j=W i j at hbj
      rw [hbj]
      change (R*Matrix.diagonal (fun k => (s k)⁻¹)) i j*s j=R i j
      rw [Matrix.mul_diagonal]
      have hz : s j≠0 := ne_of_gt (Real.sqrt_pos.mpr hj)
      field_simp
    · have hez : e j=0 := le_antisymm (le_of_not_gt hj) (he j)
      have hsz : s j=0 := by simp [s,hez]
      rw [hsz,mul_zero,hzero j hez i]
  refine ⟨U,V,s,hu,huu,hv,hvv,hs,?_⟩
  rw [hUS]
  change (M*V)*V.transpose=M
  rw [Matrix.mul_assoc,hvv,Matrix.mul_one]

theorem procrustes_solution_from_svd {N d : ℕ}
    (A B : Matrix (Fin N) (Fin d) ℝ) :
    ∃ (U V : Matrix (Fin d) (Fin d) ℝ) (s : Fin d → ℝ),
      Chapter04Procrustes.Orthogonal U ∧ Chapter04Procrustes.Orthogonal V ∧
      (∀i,0 ≤ s i) ∧ U*Matrix.diagonal s*V.transpose=A.transpose*B ∧
      (U*V.transpose).transpose*(U*V.transpose)=1 ∧
      ∀Q : Matrix (Fin d) (Fin d) ℝ,Q.transpose*Q=1 →
        Real.sqrt (Chapter04Procrustes.loss A B (U*V.transpose))≤
          Real.sqrt (Chapter04Procrustes.loss A B Q) := by
  obtain ⟨U,V,s,hu,huu,hv,hvv,hs,hM⟩ := real_square_svd_exists (A.transpose*B)
  have h := Chapter04Procrustes.procrustes_conditional_frobenius_minimum A B s ⟨hu,huu⟩ ⟨hv,hvv⟩ hs hM.symm
  exact ⟨U,V,s,⟨hu,huu⟩,⟨hv,hvv⟩,hs,hM,h⟩

#print axioms real_square_svd_exists
#print axioms procrustes_solution_from_svd

end Chapter04SVDGeral
