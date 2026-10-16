import Mathlib

namespace Capitulo03Cardinalidade

theorem c03_r01_inclusion_exclusion {α : Type*} [DecidableEq α]
    (A B : Finset α) :
    (A ∪ B).card = A.card + B.card - (A ∩ B).card := by
  have h := Finset.card_union_add_card_inter A B
  omega

theorem c03_r06_append_length (u v : String) :
    (u ++ v).length = u.length + v.length := by simp

end Capitulo03Cardinalidade

#print axioms Capitulo03Cardinalidade.c03_r01_inclusion_exclusion
#print axioms Capitulo03Cardinalidade.c03_r06_append_length
