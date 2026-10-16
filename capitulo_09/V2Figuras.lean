import Mathlib

namespace Chapter09V2Figures

theorem disjoint_regions : (292+103:ℕ)=395 ∧ (292+491:ℕ)=783 ∧
    (292+103+491:ℕ)=886 := by norm_num

theorem printed_percentage_rounding :
    |(100*(292/395:ℚ))-739/10|<1/20 ∧
    |(100*(292/783:ℚ))-373/10|<1/20 := by norm_num

theorem exterior_definition {α : Type*} (S P Q : Set α) (x : α) :
    x∈S\(P∪Q) ↔ x∈S ∧ x∉P ∧ x∉Q := by
  simp only [Set.mem_sdiff,Set.mem_union,not_or]

theorem exterior_not_determined_by_margins (t : ℕ) :
    (292+103:ℕ)=395 ∧ (292+491:ℕ)=783 ∧
    292+103+491+t=886+t := by omega

theorem accuracy_depends_on_exterior (s t : ℝ) (hs : 0 ≤ s) (ht : s < t) :
    (292+s)/(886+s) < (292+t)/(886+t) := by
  apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

end Chapter09V2Figures
