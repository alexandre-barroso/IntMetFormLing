import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open scoped BigOperators

namespace Chapter09Expressions

def selected {n : ℕ} (S P : Finset (Fin n)) : Finset (Fin n) := S∩P
def relevant {n : ℕ} (S Q : Finset (Fin n)) : Finset (Fin n) := S∩Q
def correct {n : ℕ} (S P Q : Finset (Fin n)) : Finset (Fin n) := S∩P∩Q

theorem correct_subsets {n : ℕ} (S P Q : Finset (Fin n)) : correct S P Q⊆selected S P ∧ correct S P Q⊆relevant S Q := by
  constructor
  · exact Finset.inter_subset_left
  · intro x hx
    simp only [correct,selected,relevant,Finset.mem_inter] at *
    exact ⟨hx.1.1,hx.2⟩

def precision {n : ℕ} (S P Q : Finset (Fin n)) : Option ℚ :=
  if (selected S P).card=0 then none else some (((correct S P Q).card:ℚ)/(selected S P).card)
def coverage {n : ℕ} (S P Q : Finset (Fin n)) : Option ℚ :=
  if (relevant S Q).card=0 then none else some (((correct S P Q).card:ℚ)/(relevant S Q).card)

theorem precision_definition {n : ℕ} (S P Q : Finset (Fin n)) (h : (selected S P).card≠0) :
    precision S P Q=some (((correct S P Q).card:ℚ)/(selected S P).card) := by simp [precision,h]

theorem coverage_definition {n : ℕ} (S P Q : Finset (Fin n)) (h : (relevant S Q).card≠0) :
    coverage S P Q=some (((correct S P Q).card:ℚ)/(relevant S Q).card) := by simp [coverage,h]

def before : Matrix (Fin 2) (Fin 2) ℚ := !![85,15;4,105]
def after : Matrix (Fin 2) (Fin 2) ℚ := !![100,0;4,105]

theorem revision_rows : (fun i=>∑ j,before i j)=![100,109] ∧ (fun i=>∑ j,after i j)=![100,109] := by decide +kernel

theorem revision_columns : (fun j=>∑ i,before i j)=![89,120] ∧ (fun j=>∑ i,after i j)=![104,105] := by decide +kernel

theorem revision_conservation : (∑ i,∑ j,before i j)=209 ∧ (∑ i,∑ j,after i j)=209 ∧ after-before=!![15,-15;0,0] := by decide +kernel

theorem revision_proportion : (∑ i,after i 0)/(∑ i,∑ j,after i j)-(∑ i,before i 0)/(∑ i,∑ j,before i j)=15/209 := by decide +kernel

def transfer : Fin 9 → ℚ := ![997/1000,986/1000,918/1000,951/1000,966/1000,936/1000,813/1000,906/1000,985/1000]

theorem transfer_mean : (∑ i,transfer i)=8458/1000 ∧ (∑ i,transfer i)/9=4229/4500 := by decide +kernel

theorem nested_indicators {n : ℕ} (A B : Finset (Fin n)) (h : B⊆A) (i : Fin n) :
    (if i∈A then (1:ℚ) else 0)*(if i∈B then 1 else 0)=(if i∈B then 1 else 0) := by
  by_cases hi : i∈B
  · simp [hi,h hi]
  · simp [hi]

end Chapter09Expressions

#print axioms Chapter09Expressions.correct_subsets
#print axioms Chapter09Expressions.precision_definition
#print axioms Chapter09Expressions.coverage_definition
#print axioms Chapter09Expressions.revision_rows
#print axioms Chapter09Expressions.revision_columns
#print axioms Chapter09Expressions.revision_conservation
#print axioms Chapter09Expressions.revision_proportion
#print axioms Chapter09Expressions.transfer_mean
#print axioms Chapter09Expressions.nested_indicators
