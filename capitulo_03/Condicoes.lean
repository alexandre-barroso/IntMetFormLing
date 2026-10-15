import Mathlib

namespace Chapter03Conditions

noncomputable def overlap {α : Type*} [DecidableEq α] (X Y : Finset α) : Option ℚ :=
  if X.Nonempty ∧ Y.Nonempty then some (((X ∩ Y).card : ℚ) / (min X.card Y.card : ℕ)) else none

theorem overlap_domain {α : Type*} [DecidableEq α] (X Y : Finset α) :
    overlap X Y = none ↔ X = ∅ ∨ Y = ∅ := by
  classical
  simp [overlap,Finset.nonempty_iff_ne_empty]
  tauto

theorem overlap_valid {α : Type*} [DecidableEq α] (X Y : Finset α)
    (hx : X.Nonempty) (hy : Y.Nonempty) :
    overlap X Y = some (((X ∩ Y).card : ℚ) / (min X.card Y.card : ℕ)) := by
  simp [overlap,hx,hy]

theorem overlap_bounds {α : Type*} [DecidableEq α] (X Y : Finset α)
    (hx : X.Nonempty) (hy : Y.Nonempty) :
    0 ≤ ((X ∩ Y).card : ℚ) / (min X.card Y.card : ℕ) ∧
    ((X ∩ Y).card : ℚ) / (min X.card Y.card : ℕ) ≤ 1 := by
  have hd : (0:ℚ) < (min X.card Y.card : ℕ) := by
    exact_mod_cast lt_min (Finset.card_pos.mpr hx) (Finset.card_pos.mpr hy)
  constructor
  · positivity
  · apply (div_le_iff₀ hd).mpr
    simp only [one_mul]
    exact_mod_cast le_min (Finset.card_le_card Finset.inter_subset_left) (Finset.card_le_card Finset.inter_subset_right)

theorem overlap_zero_iff {α : Type*} [DecidableEq α] (X Y : Finset α)
    (hx : X.Nonempty) (hy : Y.Nonempty) :
    ((X ∩ Y).card : ℚ) / (min X.card Y.card : ℕ) = 0 ↔ Disjoint X Y := by
  have hd : (min X.card Y.card : ℕ) ≠ 0 := ne_of_gt (lt_min (Finset.card_pos.mpr hx) (Finset.card_pos.mpr hy))
  have hdq : ((min X.card Y.card : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [div_eq_zero_iff,or_iff_left hdq,Nat.cast_eq_zero,Finset.card_eq_zero,Finset.disjoint_iff_inter_eq_empty]

theorem overlap_one_iff {α : Type*} [DecidableEq α] (X Y : Finset α)
    (hx : X.Nonempty) (hy : Y.Nonempty) :
    ((X ∩ Y).card : ℚ) / (min X.card Y.card : ℕ) = 1 ↔ X ⊆ Y ∨ Y ⊆ X := by
  have hd : (min X.card Y.card : ℕ) ≠ 0 := ne_of_gt (lt_min (Finset.card_pos.mpr hx) (Finset.card_pos.mpr hy))
  have hdq : ((min X.card Y.card : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [div_eq_one_iff_eq hdq]
  constructor
  · intro h
    have hn : (X ∩ Y).card = min X.card Y.card := by exact_mod_cast h
    rcases le_total X.card Y.card with hl | hr
    · rw [min_eq_left hl] at hn
      have heq := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hn.ge
      exact Or.inl (Finset.inter_eq_left.mp heq)
    · rw [min_eq_right hr] at hn
      have heq := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hn.ge
      exact Or.inr (Finset.inter_eq_right.mp heq)
  · rintro (hl | hr)
    · rw [Finset.inter_eq_left.mpr hl,min_eq_left (Finset.card_le_card hl)]
    · rw [Finset.inter_eq_right.mpr hr,min_eq_right (Finset.card_le_card hr)]

def surface {E : Type*} (F D : E → Prop) (R : E → E → Prop) : Prop :=
  ∀ y, F y → ∃ x, D x ∧ R y x

def inverse {E : Type*} (F D : E → Prop) (R : E → E → Prop) : Prop :=
  ∃ x, D x ∧ ∀ y, F y → R y x

theorem inverse_implies_surface {E : Type*} (F D : E → Prop) (R : E → E → Prop)
    (h : inverse F D R) : surface F D R := by
  obtain ⟨x,hD,hR⟩ := h
  intro y hF
  exact ⟨x,hD,hR y hF⟩

theorem surface_not_inverse :
    surface (fun _ : Bool=>True) (fun _ : Bool=>True) (fun y x=>y=x) ∧
    ¬ inverse (fun _ : Bool=>True) (fun _ : Bool=>True) (fun y x=>y=x) := by
  constructor
  · intro y _
    exact ⟨y,trivial,rfl⟩
  · rintro ⟨x,_,h⟩
    have h₁ := h true trivial
    have h₂ := h false trivial
    have : true = false := h₁.trans h₂.symm
    contradiction

theorem empty_restriction_no_existence :
    ((∅ : Set Bool) ⊆ ∅) ∧ ¬ ((∅ : Set Bool) ∩ ∅).Nonempty := by simp

theorem most_rules_are_not_type_consequences :
    ∃ Most : (Bool → Prop) → (Bool → Prop) → Prop,
      Most (fun _=>False) (fun _=>False) ∧ ¬ ∃ x : Bool, False ∧ False := by
  exact ⟨fun _ _=>True,trivial,by simp⟩

end Chapter03Conditions

#print axioms Chapter03Conditions.overlap_domain
#print axioms Chapter03Conditions.overlap_valid
#print axioms Chapter03Conditions.overlap_bounds
#print axioms Chapter03Conditions.overlap_zero_iff
#print axioms Chapter03Conditions.overlap_one_iff
#print axioms Chapter03Conditions.inverse_implies_surface
#print axioms Chapter03Conditions.surface_not_inverse
#print axioms Chapter03Conditions.empty_restriction_no_existence
#print axioms Chapter03Conditions.most_rules_are_not_type_consequences
