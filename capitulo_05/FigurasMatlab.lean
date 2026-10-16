import capitulo_05.Expressoes
import capitulo_05.Dispersao
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace Chapter05Matlab

def sizes : Fin 3 → ℚ := ![4/10,3/10,3/10]
def observed : Fin 3 → ℚ := ![6/10,2/10,2/10]
theorem complete_distributions : (∑ i,sizes i)=1 ∧ (∑ i,observed i)=1 ∧ (∀ i,0<sizes i ∧ 0<observed i) := by norm_num [sizes,observed,Fin.sum_univ_succ]; try decide +kernel
theorem all_differences : (fun i=>observed i-sizes i)=![1/5,-1/10,-1/10] := by norm_num [sizes,observed,Fin.sum_univ_succ]; try decide +kernel
theorem balanced_excess : (∑ i, (observed i - sizes i))=0 ∧ (observed 0-sizes 0)= -((observed 1-sizes 1)+(observed 2-sizes 2)) := by norm_num [sizes,observed,Fin.sum_univ_succ]; try decide +kernel
theorem dispersion_and_normalization : (∑ i,|observed i-sizes i|)/2=1/5 ∧ ((∑ i,|observed i-sizes i|)/2)/(1-sizes 1)=2/7 ∧ (∀ i,sizes 1 ≤ sizes i) := by norm_num [sizes,observed,Fin.sum_univ_succ]; try decide +kernel
theorem percentages : (fun i=>100*sizes i)=![40,30,30] ∧ (fun i=>100*observed i)=![60,20,20] := by norm_num [sizes,observed,Fin.sum_univ_succ]; try decide +kernel
theorem band_boundaries : sizes 0=2/5 ∧ sizes 0+sizes 1=7/10 ∧ observed 0=3/5 ∧ observed 0+observed 1=4/5 := by norm_num [sizes,observed,Fin.sum_univ_succ]; try decide +kernel
end Chapter05Matlab
#print axioms Chapter05Matlab.dispersion_and_normalization
