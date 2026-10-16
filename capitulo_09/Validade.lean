import Mathlib

open scoped BigOperators

namespace Chapter09Validity

def selected {α : Type*} [DecidableEq α] (S P : Finset α) := S ∩ P
def relevant {α : Type*} [DecidableEq α] (S Q : Finset α) := S ∩ Q
def correct {α : Type*} [DecidableEq α] (S P Q : Finset α) := S ∩ P ∩ Q

def precision {α : Type*} [DecidableEq α] (S P Q : Finset α) : Option ℚ :=
    if (selected S P).card = 0 then none else some ((correct S P Q).card / ((selected S P).card : ℚ))
def coverage {α : Type*} [DecidableEq α] (S P Q : Finset α) : Option ℚ :=
    if (relevant S Q).card = 0 then none else some ((correct S P Q).card / ((relevant S Q).card : ℚ))

theorem subset_counts {α : Type*} [DecidableEq α] (S P Q : Finset α) :
    (correct S P Q).card ≤ (selected S P).card ∧ (correct S P Q).card ≤ (relevant S Q).card := by
  constructor
  · apply Finset.card_le_card
    exact Finset.inter_subset_left
  · apply Finset.card_le_card
    intro x hx
    simp only [correct, relevant, Finset.mem_inter] at *
    exact ⟨hx.1.1,hx.2⟩

theorem precision_valid {α : Type*} [DecidableEq α] (S P Q : Finset α) (r : ℚ)
    (h : precision S P Q = some r) :
    0 < (selected S P).card ∧ r = (correct S P Q).card / ((selected S P).card : ℚ) ∧ 0 ≤ r ∧ r ≤ 1 := by
  unfold precision at h
  split_ifs at h with hn
  have he : ((correct S P Q).card : ℚ) / (selected S P).card = r := Option.some.inj h
  subst r
  have hpos : 0 < ((selected S P).card : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ⟨Nat.pos_of_ne_zero hn, rfl, div_nonneg (by positivity) hpos.le, ?_⟩
  apply (div_le_one hpos).2
  exact_mod_cast (subset_counts S P Q).1

theorem coverage_valid {α : Type*} [DecidableEq α] (S P Q : Finset α) (r : ℚ)
    (h : coverage S P Q = some r) :
    0 < (relevant S Q).card ∧ r = (correct S P Q).card / ((relevant S Q).card : ℚ) ∧ 0 ≤ r ∧ r ≤ 1 := by
  unfold coverage at h
  split_ifs at h with hn
  have he : ((correct S P Q).card : ℚ) / (relevant S Q).card = r := Option.some.inj h
  subst r
  have hpos : 0 < ((relevant S Q).card : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ⟨Nat.pos_of_ne_zero hn, rfl, div_nonneg (by positivity) hpos.le, ?_⟩
  apply (div_le_one hpos).2
  exact_mod_cast (subset_counts S P Q).2

theorem undefined_precisely {α : Type*} [DecidableEq α] (S P Q : Finset α) :
    (precision S P Q = none ↔ (selected S P).card = 0) ∧
    (coverage S P Q = none ↔ (relevant S Q).card = 0) := by
  constructor <;> simp [precision, coverage]

theorem nested_sets {α : Type*} [DecidableEq α] (A B : Finset α) (h : B ⊆ A) : A ∩ B = B :=
  Finset.inter_eq_right.mpr h

def opportunities : Fin 3 → ℚ := ![5509,395,209]
def preposed : Fin 3 → ℚ := ![601,292,89]
def displayedPrecision : Fin 3 → ℚ := ![109/10,739/10,426/10]
def displayedCoverage : Fin 3 → ℚ := ![768/10,373/10,114/10]

theorem source_domains : ∀ i, 0 < opportunities i ∧ 0 ≤ preposed i ∧ preposed i ≤ opportunities i ∧ preposed i ≤ 783 := by
  intro i
  fin_cases i <;> norm_num [opportunities,preposed]

theorem precision_plot_rounding : ∀ i, |100 * preposed i / opportunities i - displayedPrecision i| < 1/20 := by
  intro i
  fin_cases i <;> norm_num [opportunities,preposed,displayedPrecision]

theorem coverage_plot_rounding : ∀ i, |100 * preposed i / 783 - displayedCoverage i| < 1/20 := by
  intro i
  fin_cases i <;> norm_num [preposed,displayedCoverage]

#print axioms subset_counts
#print axioms precision_valid
#print axioms coverage_valid
#print axioms undefined_precisely
#print axioms nested_sets
#print axioms source_domains
#print axioms precision_plot_rounding
#print axioms coverage_plot_rounding

end Chapter09Validity
