import capitulo_08.OtEstrita

open scoped BigOperators
namespace Chapter08Closure

theorem context_mean_permutation {n d : ℕ} (hn : 0 < n)
    (v : Fin n → Fin d → ℝ) (p : Equiv.Perm (Fin n)) :
    0 < (n : ℝ) ∧ ∀ r, (∑ i, v (p i) r) / n = (∑ i, v i r) / n := by
  refine ⟨by exact_mod_cast hn, ?_⟩
  intro r
  rw [Equiv.sum_comp p (fun i => v i r)]

def pottsViolations (i : Fin 4) (j : Fin 2) : ℕ :=
  if i.val = 0 then (if j.val = 0 then 2 else 0)
  else if i.val = 3 then (if j.val = 0 then 0 else 2) else 1

noncomputable def pottsHarmony (w₁ w₂ : ℝ) (i : Fin 4) : ℝ :=
  -w₁ * pottsViolations i 0 - w₂ * pottsViolations i 1

theorem complete_deletion_hg (w₁ w₂ : ℝ) (h : w₂ < w₁) :
    ∀ i : Fin 4, i ≠ 3 → pottsHarmony w₁ w₂ i < pottsHarmony w₁ w₂ 3 := by
  intro i hi
  fin_cases i <;> norm_num [pottsHarmony, pottsViolations, Fin.ext_iff] at * <;> linarith

theorem complete_deletion_ot :
    ∀ i : Fin 4, i ≠ 3 →
      Chapter08StrictOT.prefers (pottsViolations 3) (pottsViolations i) := by
  intro i hi
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    exact False.elim (by omega)
  · fin_cases i <;> norm_num [pottsViolations, Fin.ext_iff] at *

noncomputable def squaredDistance (B : Matrix (Fin 1) (Fin 1) ℝ)
    (x y : Fin 1 → ℝ) : ℝ := ∑ i, (B.mulVec (x-y) i)^2

theorem squared_distance_triangle_counterexample :
    squaredDistance 1 ![0] ![2] >
      squaredDistance 1 ![0] ![1] + squaredDistance 1 ![1] ![2] := by
  norm_num [squaredDistance, Matrix.one_mulVec, Fin.sum_univ_succ]

theorem distinct_vectors_collapsed_by_projection :
    (![1, 0] : Fin 2 → ℝ) ≠ ![1, 1] ∧
    (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ).mulVec ![1, 0] =
      (!![1, 0] : Matrix (Fin 1) (Fin 2) ℝ).mulVec ![1, 1] := by
  constructor
  · intro h
    have h1 := congrFun h 1
    norm_num at h1
  · ext i
    fin_cases i
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def eraseBoundaries (xs : List Char) : List Char := xs.filter (fun c => c != '-')

inductive BoundaryInsertion : List Char → List Char → Prop where
  | nil : BoundaryInsertion [] []
  | keep (c : Char) {xs ys : List Char} : BoundaryInsertion xs ys → BoundaryInsertion (c::xs) (c::ys)
  | insert {xs ys : List Char} : BoundaryInsertion xs ys → BoundaryInsertion xs ('-'::ys)

theorem boundary_insertion_preserves_erasure {xs ys : List Char} (h : BoundaryInsertion xs ys) :
    eraseBoundaries ys = eraseBoundaries xs := by
  induction h with
  | nil => rfl
  | keep c h ih => simp only [eraseBoundaries, List.filter_cons]; split <;> simp_all [eraseBoundaries]
  | insert h ih => simpa [eraseBoundaries] using ih

theorem canonical_segmentation_requires_more_than_boundaries :
    ¬BoundaryInsertion "Cylindrically".toList "Cylinder-ical-ly".toList := by
  intro h
  have hi := boundary_insertion_preserves_erasure h
  have hn : eraseBoundaries "Cylinder-ical-ly".toList ≠ eraseBoundaries "Cylindrically".toList := by decide +kernel
  exact hn hi

noncomputable def shapleyA (v0 va vb vab : ℝ) : ℝ := ((va-v0)+(vab-vb))/2

theorem shapley_negative_despite_valid_performances :
    (∀ v ∈ ([1,0,1,0] : List ℝ), 0 ≤ v ∧ v ≤ 1) ∧
    shapleyA 1 0 1 0 = -1 ∧ shapleyA 1 0 1 0 < 0 := by
  norm_num [shapleyA]

end Chapter08Closure

#print axioms Chapter08Closure.context_mean_permutation
#print axioms Chapter08Closure.complete_deletion_hg
#print axioms Chapter08Closure.complete_deletion_ot
#print axioms Chapter08Closure.squared_distance_triangle_counterexample
#print axioms Chapter08Closure.distinct_vectors_collapsed_by_projection
#print axioms Chapter08Closure.boundary_insertion_preserves_erasure
#print axioms Chapter08Closure.canonical_segmentation_requires_more_than_boundaries
#print axioms Chapter08Closure.shapley_negative_despite_valid_performances
