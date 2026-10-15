import capitulo_08.Dinamica
import capitulo_08.Verificar

namespace Chapter08UnitCost

variable {α : Type} [DecidableEq α]

inductive UnitStep : List α → List α → ℕ → ℕ → Prop
  | delete (pre post : List α) (a : α) : UnitStep (pre++a::post) (pre++post) 1 1
  | insert (pre post : List α) (a : α) : UnitStep (pre++post) (pre++a::post) 1 1
  | substitute (pre post : List α) (a b : α) :
      UnitStep (pre++a::post) (pre++b::post) (if a=b then 0 else 1) 0

inductive UnitPath : List α → List α → ℕ → ℕ → Prop
  | refl (x : List α) : UnitPath x x 0 0
  | step {x y z : List α} {c k d e : ℕ} :
      UnitStep x y c d → UnitPath y z k e → UnitPath x z (c+k) (d+e)

theorem step_lift {x y : List α} {c d : ℕ} (h : UnitStep x y c d) :
    ∃ r, Chapter08Dynamic.Step x y r ∧ r+d=2*c := by
  cases h with
  | delete pre post a => exact ⟨1,Chapter08Dynamic.Step.delete pre post a,by omega⟩
  | insert pre post a => exact ⟨1,Chapter08Dynamic.Step.insert pre post a,by omega⟩
  | substitute pre post a b =>
      refine ⟨if a=b then 0 else 2,Chapter08Dynamic.Step.substitute pre post a b,?_⟩
      split <;> omega

theorem path_lift {x y : List α} {k d : ℕ} (h : UnitPath x y k d) :
    ∃ r, Chapter08Dynamic.Path x y r ∧ r+d=2*k := by
  induction h with
  | refl x => exact ⟨0,Chapter08Dynamic.Path.refl x,by omega⟩
  | @step x y z c k d e hs hp ih =>
      obtain ⟨r,hr,heq⟩ := step_lift hs
      obtain ⟨s,hs,heq'⟩ := ih
      exact ⟨r+s,Chapter08Dynamic.Path.step hr hs,by omega⟩

def mismatch (a b : α) : ℕ := if a=b then 0 else 1

def hamming : List α → List α → ℕ
  | [], _ => 0
  | _, [] => 0
  | a::x, b::y => mismatch a b + hamming x y

theorem mismatch_triangle (a b c : α) : mismatch a c ≤ mismatch a b + mismatch b c := by
  by_cases hab : a=b
  · subst b
    simp [mismatch]
  · by_cases hbc : b=c
    · subst c
      simp [mismatch]
    · simp [mismatch,hab,hbc]
      split <;> omega

theorem hamming_refl (x : List α) : hamming x x=0 := by
  induction x with
  | nil => rfl
  | cons a x ih => simp [hamming,mismatch,ih]

theorem hamming_substitution_bound (pre post z : List α) (a b : α) :
    hamming (pre++a::post) z ≤ mismatch a b + hamming (pre++b::post) z := by
  induction pre generalizing z with
  | nil =>
      cases z with
      | nil => simp [hamming]
      | cons c z =>
          simp only [List.nil_append,hamming]
          have h := mismatch_triangle a b c
          omega
  | cons c pre ih =>
      cases z with
      | nil => simp [hamming]
      | cons e z =>
          simp only [List.cons_append,hamming]
          have h := ih z
          omega

theorem zero_gap_hamming_bound {x y : List α} {k d : ℕ} (h : UnitPath x y k d) :
    d=0 → hamming x y≤k := by
  induction h with
  | refl x => intro hd;simpa [hamming_refl]
  | @step x u y c k d e hs hp ih =>
      intro hd
      have he : e=0 := by omega
      have htail := ih he
      cases hs with
      | delete pre post a => omega
      | insert pre post a => omega
      | substitute pre post a b =>
          have hb := hamming_substitution_bound pre post y a b
          unfold mismatch at hb
          omega

open Chapter08.c08_a05

theorem table_boundaries (i : ℕ) (hi : i<10) : d i 0=i ∧ d 0 i=i := by
  have h := List.all_eq_true.mp boundaries i (by simpa using hi)
  simpa using h

theorem table_recurrence (i j : ℕ) (hi : i<9) (hj : j<9) :
    d (i+1) (j+1)=min (d i (j+1)+1)
      (min (d (i+1) j+1) (d i j+(if source[i]=target[j] then 0 else 2))) := by
  interval_cases i <;> interval_cases j <;> decide +kernel +revert

theorem table_matches_prefix (i j : ℕ) (hi : i≤9) (hj : j≤9) :
    Chapter08Dynamic.prefixDistance source target i j=d i j := by
  induction n:i+j using Nat.strong_induction_on generalizing i j with
  | h n ih =>
      cases i with
      | zero =>
          rw [Chapter08Dynamic.prefix_empty_source source target j (by simpa [target] using hj)]
          exact (table_boundaries j (by omega)).2.symm
      | succ i =>
          cases j with
          | zero =>
              rw [Chapter08Dynamic.prefix_empty_target source target (i+1) (by simpa [source] using hi)]
              exact (table_boundaries (i+1) (by omega)).1.symm
          | succ j =>
              rw [Chapter08Dynamic.prefix_recurrence source target i j (by simpa [source] using (show i<9 by omega)) (by simpa [target] using (show j<9 by omega))]
              rw [ih (i+(j+1)) (by omega) i (j+1) (by omega) (by omega) rfl]
              rw [ih ((i+1)+j) (by omega) (i+1) j (by omega) (by omega) rfl]
              rw [ih (i+j) (by omega) i j (by omega) (by omega) rfl]
              exact (table_recurrence i j (by omega) (by omega)).symm

theorem doubled_distance_eight : Chapter08Dynamic.distance "intention".toList "execution".toList=8 := by
  have h := table_matches_prefix 9 9 (by omega) (by omega)
  have hfinal := sourceResult.1
  have hs : source.take 9=source := by decide +kernel
  have ht : target.take 9=target := by decide +kernel
  change Chapter08Dynamic.distance (source.take 9) (target.take 9)=d 9 9 at h
  rw [hs,ht,hfinal] at h
  exact h

theorem hamming_five : hamming "intention".toList "execution".toList=5 := by decide +kernel

theorem unit_lower_bound {k d : ℕ} (h : UnitPath "intention".toList "execution".toList k d) : 5≤k := by
  by_cases hd : d=0
  · have hh := zero_gap_hamming_bound h hd
    rw [hamming_five] at hh
    exact hh
  · obtain ⟨r,hr,heq⟩ := path_lift h
    have hmin := (Chapter08Dynamic.minimum_edit_cost "intention".toList "execution".toList).2 hr
    rw [doubled_distance_eight] at hmin
    omega

theorem published_unit_path : UnitPath "intention".toList "execution".toList 5 2 := by
  have h1 : UnitStep "intention".toList "ntention".toList 1 1 := by
    simpa using UnitStep.delete [] "ntention".toList 'i'
  have h2 : UnitStep "ntention".toList "etention".toList 1 0 := by
    simpa using UnitStep.substitute [] "tention".toList 'n' 'e'
  have h3 : UnitStep "etention".toList "exention".toList 1 0 := by
    simpa using UnitStep.substitute "e".toList "ention".toList 't' 'x'
  have h4 : UnitStep "exention".toList "exenution".toList 1 1 := by
    simpa using UnitStep.insert "exen".toList "tion".toList 'u'
  have h5 : UnitStep "exenution".toList "execution".toList 1 0 := by
    simpa using UnitStep.substitute "exe".toList "ution".toList 'n' 'c'
  exact UnitPath.step h1 (UnitPath.step h2 (UnitPath.step h3 (UnitPath.step h4 (UnitPath.step h5 (UnitPath.refl _)))))

theorem unit_minimum_five : IsLeast {k : ℕ | ∃d,UnitPath "intention".toList "execution".toList k d} 5 := by
  exact ⟨⟨2,published_unit_path⟩,fun k ⟨d,h⟩=>unit_lower_bound h⟩

#print axioms path_lift
#print axioms zero_gap_hamming_bound
#print axioms doubled_distance_eight
#print axioms unit_minimum_five

end Chapter08UnitCost
