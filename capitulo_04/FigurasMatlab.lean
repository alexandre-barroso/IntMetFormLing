import capitulo_04.Expressoes
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace Chapter04Matlab

def own : Matrix (Fin 3) (Fin 3) ℚ := !![40,853/10,32/10;167/10,734/10,8;52/10,93/10,484/10]
def use : Matrix (Fin 3) (Fin 3) ℚ := !![821/10,448/10,33/10;695/10,519/10,101/10;7,47/10,536/10]
def tensor (i : Fin 3) (j : Fin 2) (k : Fin 3) : ℚ := if j=0 then own i k else use i k
def unfolded : Matrix (Fin 3) (Fin 6) ℚ := !![40,821/10,853/10,448/10,32/10,33/10;167/10,695/10,734/10,519/10,8,101/10;52/10,7,93/10,47/10,484/10,536/10]
def column (j : Fin 2) (k : Fin 3) : Fin 6 := ⟨2*k.val+j.val,by omega⟩
theorem full_tensor_unfolding : ∀ i j k, tensor i j k=unfolded i (column j k) := by decide +kernel
theorem unfolding_is_bijective : Function.Bijective (fun p : Fin 2 × Fin 3 => column p.1 p.2) := by decide +kernel
theorem highlighted_weight : tensor 2 1 2=536/10 ∧ unfolded 2 5=536/10 := by decide +kernel
theorem workshop_weight : tensor 0 1 1=448/10 ∧ unfolded 0 3=448/10 := by decide +kernel
theorem projection_orthonormal (a e : ℝ) :
  let P : Matrix (Fin 2) (Fin 3) ℝ := !![Real.cos a,-Real.sin a,0;Real.sin a*Real.sin e,Real.cos a*Real.sin e,Real.cos e]
  P*P.transpose=1 := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]
  all_goals nlinarith [Real.sin_sq_add_cos_sq a,Real.sin_sq_add_cos_sq e]
end Chapter04Matlab
#print axioms Chapter04Matlab.full_tensor_unfolding
#print axioms Chapter04Matlab.projection_orthonormal
