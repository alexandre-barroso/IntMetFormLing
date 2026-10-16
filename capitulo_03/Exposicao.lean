import Mathlib

namespace Chapter03Exposition

theorem coffee_tea {E : Type*} (woman coffee tea : E → Prop)
    (hall : ∀ x, woman x → coffee x ∨ tea x)
    (hsome : ∃ x, woman x ∧ ¬ coffee x) :
    ∃ x, woman x ∧ tea x := by
  obtain ⟨x,hW,hC⟩ := hsome
  exact ⟨x,hW,(hall x hW).resolve_left hC⟩

theorem noninjective_no_left_inverse {E F : Type*} (f : E → F)
    (hf : ¬ Function.Injective f) : ¬ ∃ g : F → E, Function.LeftInverse g f := by
  rintro ⟨g,hg⟩
  exact hf hg.injective

theorem common_witness {A B : Type*} (R : A → B → Prop)
    (h : ∃ b, ∀ a, R a b) : ∀ a, ∃ b, R a b := by
  obtain ⟨b,hb⟩ := h
  exact fun a => ⟨b,hb a⟩

def diagonal (farmer donkey : Fin 3) : Prop := farmer = donkey

def common (_farmer : Fin 3) (_donkey : Fin 1) : Prop := True

theorem figure_F03_left : (∀ y, ∃ x, diagonal y x) ∧ ¬ (∃ x, ∀ y, diagonal y x) := by
  unfold diagonal
  decide +kernel

theorem figure_F03_right : (∀ y, ∃ x, common y x) ∧ (∃ x, ∀ y, common y x) := by
  unfold common
  decide +kernel

theorem widening_restriction_invalid :
    ¬ (∀ (M H P : Bool → Prop), (∀ x, M x → H x) →
      (∀ x, M x → P x) → (∀ x, H x → P x)) := by
  intro h
  have hbad := h (fun x => x = false) (fun _ => True) (fun x => x = false)
    (by simp) (by simp) true trivial
  cases hbad

end Chapter03Exposition

#print axioms Chapter03Exposition.coffee_tea
#print axioms Chapter03Exposition.noninjective_no_left_inverse
#print axioms Chapter03Exposition.common_witness
#print axioms Chapter03Exposition.figure_F03_left
#print axioms Chapter03Exposition.figure_F03_right
#print axioms Chapter03Exposition.widening_restriction_invalid
