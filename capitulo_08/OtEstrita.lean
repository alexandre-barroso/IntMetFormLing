import Mathlib

namespace Chapter08StrictOT

def prefers {n : ℕ} (p q : Fin n → ℕ) : Prop :=
    ∃ k, (∀ j, j<k → p j=q j) ∧ p k<q k

theorem first_different_constraint {n : ℕ} (p q : Fin n → ℕ) (k : Fin n)
    (heq : ∀ j, j<k → p j=q j) (hbetter : p k<q k) : prefers p q :=
  ⟨k,heq,hbetter⟩

theorem irreflexive {n : ℕ} (p : Fin n → ℕ) : ¬prefers p p := by
  rintro ⟨k,_,h⟩
  exact (lt_irrefl (p k)) h

theorem asymmetric {n : ℕ} (p q : Fin n → ℕ) (h : prefers p q) :
    ¬prefers q p := by
  rcases h with ⟨k,hk,hlt⟩
  rintro ⟨l,hl,hlLt⟩
  rcases lt_trichotomy k l with hkl|hkl|hkl
  · have e := hl k hkl; omega
  · subst l; omega
  · have e := hk l hkl; omega

theorem transitive {n : ℕ} (p q r : Fin n → ℕ)
    (hpq : prefers p q) (hqr : prefers q r) : prefers p r := by
  rcases hpq with ⟨k,hk,hlt⟩
  rcases hqr with ⟨l,hl,hlLt⟩
  rcases lt_trichotomy k l with hkl|hkl|hkl
  · refine ⟨k, ?_, ?_⟩
    · intro j hj
      exact (hk j hj).trans (hl j (lt_trans hj hkl))
    · rw [←hl k hkl]; exact hlt
  · subst l
    refine ⟨k, ?_, lt_trans hlt hlLt⟩
    intro j hj
    exact (hk j hj).trans (hl j hj)
  · refine ⟨l, ?_, ?_⟩
    · intro j hj
      exact (hk j (lt_trans hj hkl)).trans (hl j hj)
    · rw [hk l hkl]; exact hlLt

theorem equal_profiles_tie {n : ℕ} (p q : Fin n → ℕ) (h : p=q) :
    ¬prefers p q ∧ ¬prefers q p := by
  subst q
  exact ⟨irreflexive p,irreflexive p⟩

theorem unequal_profiles_comparable {n : ℕ} (p q : Fin n → ℕ) (h : p≠q) :
    prefers p q ∨ prefers q p := by
  classical
  have hex : ∃ k, p k≠q k := by
    by_contra hn
    apply h
    funext k
    push Not at hn
    exact hn k
  let different := Finset.univ.filter (fun k => p k≠q k)
  have hd : different.Nonempty := by
    rcases hex with ⟨k,hk⟩
    exact ⟨k, by simp [different,hk]⟩
  let k := different.min' hd
  have hk : k∈different := Finset.min'_mem different hd
  have hneq : p k≠q k := by simpa [different] using hk
  have heq : ∀ j, j<k → p j=q j := by
    intro j hj
    by_contra hn
    have hjmem : j∈different := by simp [different,hn]
    have hmin : k≤j := Finset.min'_le different j hjmem
    exact (not_le_of_gt hj) hmin
  rcases lt_or_gt_of_ne hneq with hlt|hgt
  · exact Or.inl ⟨k,heq,hlt⟩
  · exact Or.inr ⟨k,fun j hj => (heq j hj).symm,hgt⟩

end Chapter08StrictOT

#print axioms Chapter08StrictOT.transitive
#print axioms Chapter08StrictOT.unequal_profiles_comparable
#print axioms Chapter08StrictOT.equal_profiles_tie
