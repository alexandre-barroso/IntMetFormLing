import capitulo_06.Expressoes
import capitulo_06.Verificar
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace Chapter06Matlab
open Chapter06Expressions
theorem all_conditional_edges : (fun i j=>joint i j/px i)=!![1,0,0,0,0;0,1/2,1/2,0,0;0,0,1,0,0;2/3,0,0,0,1/3;0,0,0,1,0] := by decide +kernel
theorem all_group_memberships : (fun i : Fin 5 => Finset.univ.filter (fun k=>acc k=i))=![{0},{1,2},{3},{4,5,7},{6}] := by decide +kernel
theorem all_conditional_normalizations : ∀ i,0<px i ∧ (∑ j,joint i j/px i)=1 := by decide +kernel
noncomputable def groupEntropy (i : Fin 5) : ℝ := entropy (fun j=>((joint i j/px i : ℚ):ℝ))
theorem all_group_entropies : groupEntropy=![0,1,0,Real.logb 2 3-2/3,0] := by
  have loghalf : Real.logb 2 (1/2) = -1 := by
    have h:=Chapter06.c06_r07.basicSurprise.2.1
    linarith
  ext i
  simp only [groupEntropy,entropy,joint_from_classes,marginal_from_classes.1]
  fin_cases i <;> norm_num [Fin.sum_univ_succ,loghalf]
  have h:=Chapter06.c06_p02.groupEntropy
  linarith

theorem conditional_entropy_weighted : (∑ i,(px i : ℝ)*groupEntropy i)=3/8*Real.logb 2 3 := by
  rw [all_group_entropies]
  norm_num [marginal_from_classes.1,Fin.sum_univ_succ]
  ring
end Chapter06Matlab
#print axioms Chapter06Matlab.all_conditional_edges
#print axioms Chapter06Matlab.all_group_entropies
#print axioms Chapter06Matlab.conditional_entropy_weighted
