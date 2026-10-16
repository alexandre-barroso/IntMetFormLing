import Mathlib

namespace Chapter03IntegralReview

def genitivePlural (_ : Fin 8) : String := "-on"

theorem genitive_plural_values : genitivePlural 0="-on" ∧ genitivePlural 1="-on" ∧ genitivePlural 0=genitivePlural 1 := by decide +kernel

theorem min_cardinalities : min (4:ℕ) 5=4 := by decide +kernel

theorem disjunction_without_negation : (True ∨ False) ∧ ¬ False := ⟨Or.inl trivial,not_false⟩

theorem modal_existential_countermodel :
    (∃ _x : Bool, True ∧ (fun _ : Prop => True) False) ∧
    ¬ (∃ _x : Bool, True ∧ False) := by
  constructor
  · exact ⟨false,trivial,trivial⟩
  · rintro ⟨x,_,hfalse⟩
    exact hfalse

theorem published_word_lengths :
    ("work" : String).length=4 ∧ ("ed" : String).length=2 ∧
    ("work" ++ "ed" : String).length=("work" : String).length+("ed" : String).length := by decide +kernel

noncomputable def possible (w : Bool) (P : Bool → Prop) : Prop := ∃ v, w ≠ v ∧ P v

theorem normal_modal_countermodel :
    (∃ _x : Unit, True ∧ possible false (fun w => w = true)) ∧
    ¬ (∃ _x : Unit, True ∧ (false : Bool) = true) := by
  constructor
  · exact ⟨(),trivial,true,by decide,rfl⟩
  · rintro ⟨x,_,h⟩
    cases h

theorem possible_false (w : Bool) : ¬ possible w (fun _ => False) := by
  rintro ⟨v,_,h⟩
  exact h

theorem published_overlap_steps :
    let a : Finset String := {"s","or","pr","endere"}
    let b : Finset String := {"s","or","pr","endere","bbe"}
    let c : Finset String := {"s","or","pr","end","iamo"}
    let d : Finset String := {"s","or","pre","se"}
    (a∩b).card=4 ∧ min a.card b.card=4 ∧
    ((a∩b).card:ℚ)/(min a.card b.card:ℕ)=1 ∧
    (a∩c).card=3 ∧ min a.card c.card=4 ∧
    ((a∩c).card:ℚ)/(min a.card c.card:ℕ)=3/4 ∧ (3/4:ℚ)=75/100 ∧
    (a∩d).card=2 ∧ min a.card d.card=4 ∧
    ((a∩d).card:ℚ)/(min a.card d.card:ℕ)=2/4 ∧ (2/4:ℚ)=5/10 := by decide +kernel

end Chapter03IntegralReview
