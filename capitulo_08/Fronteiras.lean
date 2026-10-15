import Mathlib

namespace Chapter08Boundaries

inductive EditStep {α : Type} : List α → List α → ℕ → Prop
  | delete (pre post : List α) (a : α) : EditStep (pre ++ a :: post) (pre ++ post) 1
  | insert (pre post : List α) (a : α) : EditStep (pre ++ post) (pre ++ a :: post) 1
  | substitute (pre post : List α) (a b : α) : EditStep (pre ++ a :: post) (pre ++ b :: post) 2

inductive EditPath {α : Type} : List α → List α → ℕ → Prop
  | refl (word : List α) : EditPath word word 0
  | step {x y z : List α} {c k : ℕ} : EditStep x y c → EditPath y z k → EditPath x z (c+k)

theorem step_length_bounds {α : Type} {x y : List α} {c : ℕ} (h : EditStep x y c) :
    x.length ≤ y.length+c ∧ y.length ≤ x.length+c := by
  cases h <;> simp <;> omega

theorem path_length_bounds {α : Type} {x y : List α} {c : ℕ} (h : EditPath x y c) :
    x.length ≤ y.length+c ∧ y.length ≤ x.length+c := by
  induction h with
  | refl word => simp
  | step hstep hpath ih =>
    have hs := step_length_bounds hstep
    omega

theorem delete_all {α : Type} (word : List α) : EditPath word [] word.length := by
  induction word with
  | nil => exact EditPath.refl []
  | cons a tail ih =>
    simpa [Nat.add_comm] using EditPath.step (EditStep.delete [] tail a) ih

theorem insert_all {α : Type} (word : List α) : EditPath [] word word.length := by
  induction word using List.reverseRecOn with
  | nil => exact EditPath.refl []
  | append_singleton word a ih =>
    have append_path {α : Type} {x y z : List α} {c k : ℕ}
        (p : EditPath x y c) (q : EditPath y z k) : EditPath x z (c+k) := by
      induction p with
      | refl word => simpa using q
      | step hstep hpath ih => simpa [Nat.add_assoc] using EditPath.step hstep (ih q)
    have single := EditPath.step (EditStep.insert word [] a) (EditPath.refl (word ++ [a]))
    have result := append_path ih (by simpa using single)
    simpa using result

theorem empty_target_minimum {α : Type} (word : List α) :
    IsLeast {c : ℕ | EditPath word [] c} word.length := by
  refine ⟨delete_all word,?_⟩
  intro c hc
  have h := (path_length_bounds hc).1
  simpa using h

theorem empty_source_minimum {α : Type} (word : List α) :
    IsLeast {c : ℕ | EditPath [] word c} word.length := by
  refine ⟨insert_all word,?_⟩
  intro c hc
  have h := (path_length_bounds hc).2
  simpa using h

theorem prefix_to_empty_minimum {α : Type} (word : List α) (i : ℕ) (hi : i ≤ word.length) :
    IsLeast {c : ℕ | EditPath (word.take i) [] c} i := by
  simpa [List.length_take,Nat.min_eq_left hi] using empty_target_minimum (word.take i)

theorem empty_to_prefix_minimum {α : Type} (word : List α) (j : ℕ) (hj : j ≤ word.length) :
    IsLeast {c : ℕ | EditPath [] (word.take j) c} j := by
  simpa [List.length_take,Nat.min_eq_left hj] using empty_source_minimum (word.take j)

end Chapter08Boundaries
