import capitulo_04.Espectro
import capitulo_04.Raizes

namespace Chapter04Certificates
open Chapter04Spectrum Chapter04SpectralRoots

theorem source_characteristic : (sourceMatrix.transpose*sourceMatrix).charpoly=p := by
  rw [gram_from_source,characteristic_from_gram]
  rfl

theorem source_singular_values_covered (s : ℝ) (hs : IsSingularValue sourceMatrix s) :
    ∃ i,|s-published i|<1/200 :=
  singular_value_certificate sourceMatrix source_characteristic s hs

theorem source_each_published_value (i : Fin 9) :
    IsSingularValue sourceMatrix (Real.sqrt (root i)) ∧
    |Real.sqrt (root i)-published i|<1/200 := by
  refine ⟨⟨Real.sqrt_nonneg _,?_⟩,rounded_sqrt_root i⟩
  have hp : 0 < root i := lt_trans (intervals_ordered i).1 (root_spec i).1.1
  rw [Real.sq_sqrt hp.le]
  rw [←Matrix.eval_charpoly,source_characteristic]
  exact (root_spec i).2

theorem source_distinct_singular_values : Function.Injective (fun i : Fin 9=>Real.sqrt (root i)) := by
  intro i j hij
  apply root_injective
  have hi : 0 ≤ root i := le_of_lt (lt_trans (intervals_ordered i).1 (root_spec i).1.1)
  have hj : 0 ≤ root j := le_of_lt (lt_trans (intervals_ordered j).1 (root_spec j).1.1)
  have he := congrArg (fun x : ℝ=>x^2) hij
  simpa only [Real.sq_sqrt hi,Real.sq_sqrt hj] using he

#print axioms source_characteristic
#print axioms source_singular_values_covered
#print axioms source_each_published_value
#print axioms source_distinct_singular_values
end Chapter04Certificates
