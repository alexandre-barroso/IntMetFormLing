import Mathlib

namespace Chapter08Dynamic

variable {α : Type} [DecidableEq α]

inductive Step : List α → List α → ℕ → Prop
  | delete (pre post : List α) (a : α) : Step (pre ++ a :: post) (pre ++ post) 1
  | insert (pre post : List α) (a : α) : Step (pre ++ post) (pre ++ a :: post) 1
  | substitute (pre post : List α) (a b : α) : Step (pre ++ a :: post) (pre ++ b :: post) (if a=b then 0 else 2)

inductive Path : List α → List α → ℕ → Prop
  | refl (x : List α) : Path x x 0
  | step {x y z : List α} {c k : ℕ} : Step x y c → Path y z k → Path x z (c+k)

inductive Alignment : List α → List α → ℕ → Prop
  | nil : Alignment [] [] 0
  | delete {x y : List α} {k : ℕ} (a : α) : Alignment x y k → Alignment (a::x) y (k+1)
  | insert {x y : List α} {k : ℕ} (a : α) : Alignment x y k → Alignment x (a::y) (k+1)
  | keep {x y : List α} {k : ℕ} (a : α) : Alignment x y k → Alignment (a::x) (a::y) k

theorem alignment_refl (x : List α) : Alignment x x 0 := by
  induction x with
  | nil => exact Alignment.nil
  | cons a x ih => exact Alignment.keep a ih

theorem step_cons {x y : List α} {k : ℕ} (a : α) (h : Step x y k) :
    Step (a::x) (a::y) k := by
  cases h with
  | delete pre post b => exact Step.delete (a::pre) post b
  | insert pre post b => exact Step.insert (a::pre) post b
  | substitute pre post b c => exact Step.substitute (a::pre) post b c

theorem path_cons {x y : List α} {k : ℕ} (a : α) (h : Path x y k) :
    Path (a::x) (a::y) k := by
  induction h with
  | refl x => exact Path.refl (a::x)
  | step hstep hpath ih => exact Path.step (step_cons a hstep) ih

theorem alignment_to_path {x y : List α} {k : ℕ} (h : Alignment x y k) :
    Path x y k := by
  induction h with
  | nil => exact Path.refl []
  | @delete x y k a h ih =>
      simpa [Nat.add_comm] using Path.step (Step.delete [] x a) ih
  | @insert x y k a h ih =>
      simpa [Nat.add_comm] using Path.step (Step.insert [] x a) (path_cons a ih)
  | keep a h ih => exact path_cons a ih

theorem alignment_remove_source {x y : List α} {k : ℕ} (h : Alignment x y k) :
    ∀ (pre post : List α) (a : α), x=pre++a::post →
      ∃ l, Alignment (pre++post) y l ∧ l≤k+1 := by
  induction h with
  | nil =>
      intro pre post a he
      cases pre <;> simp at he
  | @delete x y k b h ih =>
      intro pre post a he
      cases pre with
      | nil =>
          simp only [List.nil_append,List.cons.injEq] at he
          rcases he with ⟨rfl,rfl⟩
          exact ⟨k,h,by omega⟩
      | cons d pre =>
          simp only [List.cons_append,List.cons.injEq] at he
          rcases he with ⟨rfl,he⟩
          obtain ⟨l,hl,hbound⟩ := ih pre post a he
          exact ⟨l+1,Alignment.delete b hl,by omega⟩
  | @insert x y k b h ih =>
      intro pre post a he
      obtain ⟨l,hl,hbound⟩ := ih pre post a he
      exact ⟨l+1,Alignment.insert b hl,by omega⟩
  | @keep x y k b h ih =>
      intro pre post a he
      cases pre with
      | nil =>
          simp only [List.nil_append,List.cons.injEq] at he
          rcases he with ⟨rfl,rfl⟩
          exact ⟨k+1,Alignment.insert b h,by omega⟩
      | cons d pre =>
          simp only [List.cons_append,List.cons.injEq] at he
          rcases he with ⟨rfl,he⟩
          obtain ⟨l,hl,hbound⟩ := ih pre post a he
          exact ⟨l,Alignment.keep b hl,by omega⟩

theorem alignment_add_source {x y : List α} {k : ℕ} (h : Alignment x y k) :
    ∀ (pre post : List α) (a : α), x=pre++post →
      ∃ l, Alignment (pre++a::post) y l ∧ l≤k+1 := by
  induction h with
  | nil =>
      intro pre post a he
      have hz := List.append_eq_nil_iff.mp he.symm
      rcases hz with ⟨rfl,rfl⟩
      exact ⟨1,Alignment.delete a Alignment.nil,by omega⟩
  | @delete x y k b h ih =>
      intro pre post a he
      cases pre with
      | nil =>
          simp only [List.nil_append] at he ⊢
          subst post
          exact ⟨k+2,Alignment.delete a (Alignment.delete b h),by omega⟩
      | cons d pre =>
          simp only [List.cons_append,List.cons.injEq] at he
          rcases he with ⟨rfl,he⟩
          obtain ⟨l,hl,hbound⟩ := ih pre post a he
          exact ⟨l+1,Alignment.delete b hl,by omega⟩
  | @insert x y k b h ih =>
      intro pre post a he
      obtain ⟨l,hl,hbound⟩ := ih pre post a he
      exact ⟨l+1,Alignment.insert b hl,by omega⟩
  | @keep x y k b h ih =>
      intro pre post a he
      cases pre with
      | nil =>
          simp only [List.nil_append] at he ⊢
          subst post
          exact ⟨k+1,Alignment.delete a (Alignment.keep b h),by omega⟩
      | cons d pre =>
          simp only [List.cons_append,List.cons.injEq] at he
          rcases he with ⟨rfl,he⟩
          obtain ⟨l,hl,hbound⟩ := ih pre post a he
          exact ⟨l,Alignment.keep b hl,by omega⟩

theorem path_to_alignment {x y : List α} {k : ℕ} (h : Path x y k) :
    ∃ l, Alignment x y l ∧ l≤k := by
  induction h with
  | refl x => exact ⟨0,alignment_refl x,le_refl _⟩
  | @step x u y c k step path ih =>
      obtain ⟨l,halign,hle⟩ := ih
      cases step with
      | delete pre post a =>
          obtain ⟨m,hm,hml⟩ := alignment_add_source halign pre post a rfl
          exact ⟨m,hm,by omega⟩
      | insert pre post a =>
          obtain ⟨m,hm,hml⟩ := alignment_remove_source halign pre post a rfl
          exact ⟨m,hm,by omega⟩
      | substitute pre post a b =>
          by_cases hab : a=b
          · subst b
            exact ⟨l,halign,by simpa using hle⟩
          · obtain ⟨m,hm,hml⟩ := alignment_remove_source halign pre post b rfl
            obtain ⟨r,hr,hrm⟩ := alignment_add_source hm pre post a rfl
            exact ⟨r,hr,by simp only [if_neg hab];omega⟩


def distance : List α → List α → ℕ
  | [], y => y.length
  | _a::x, [] => x.length+1
  | a::x, b::y => min (distance x (b::y)+1)
      (min (distance (a::x) y+1) (distance x y + if a=b then 0 else 2))
termination_by x y => x.length+y.length

theorem alignment_nil_left (y : List α) : Alignment [] y y.length := by
  induction y with
  | nil => exact Alignment.nil
  | cons a y ih => simpa using Alignment.insert a ih

theorem alignment_nil_right (x : List α) : Alignment x [] x.length := by
  induction x with
  | nil => exact Alignment.nil
  | cons a x ih => simpa using Alignment.delete a ih

theorem alignment_min {x y : List α} {a b : ℕ}
    (ha : Alignment x y a) (hb : Alignment x y b) : Alignment x y (min a b) := by
  by_cases h : a≤b
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right (le_of_lt (Nat.lt_of_not_ge h))] using hb

theorem distance_alignment (x y : List α) : Alignment x y (distance x y) := by
  induction x, y using distance.induct with
  | case1 y => simpa only [distance] using alignment_nil_left y
  | case2 a x => simpa only [distance,List.length_cons] using alignment_nil_right (a::x)
  | case3 a x b y ih1 ih2 ih3 =>
      have h1 := Alignment.delete a ih1
      have h2 := Alignment.insert b ih2
      have h3 : Alignment (a::x) (b::y) (distance x y + if a=b then 0 else 2) := by
        by_cases h : a=b
        · subst b
          simpa using Alignment.keep a ih3
        · simpa [h,Nat.add_assoc] using Alignment.delete a (Alignment.insert b ih3)
      simpa only [distance] using alignment_min h1 (alignment_min h2 h3)

theorem distance_delete_le (a : α) (x y : List α) :
    distance (a::x) y ≤ distance x y+1 := by
  cases y with
  | nil => cases x <;> simp [distance]
  | cons b y =>
      simp only [distance]
      exact min_le_left _ _

theorem distance_insert_le (b : α) (x y : List α) :
    distance x (b::y) ≤ distance x y+1 := by
  cases x with
  | nil => simp [distance]
  | cons a x =>
      simp only [distance]
      exact le_trans (min_le_right _ _) (min_le_left _ _)

theorem distance_keep_le (a : α) (x y : List α) :
    distance (a::x) (a::y) ≤ distance x y := by
  simp only [distance,ite_true,Nat.add_zero]
  exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem distance_le_alignment {x y : List α} {k : ℕ} (h : Alignment x y k) :
    distance x y≤k := by
  induction h with
  | nil => simp [distance]
  | @delete x y k a h ih => exact (distance_delete_le a x y).trans (Nat.add_le_add_right ih 1)
  | @insert x y k a h ih => exact (distance_insert_le a x y).trans (Nat.add_le_add_right ih 1)
  | @keep x y k a h ih => exact (distance_keep_le a x y).trans ih

theorem minimum_alignment_cost (x y : List α) :
    IsLeast {k : ℕ | Alignment x y k} (distance x y) := by
  exact ⟨distance_alignment x y,fun _ h=>distance_le_alignment h⟩

theorem minimum_edit_cost (x y : List α) :
    IsLeast {k : ℕ | Path x y k} (distance x y) := by
  refine ⟨alignment_to_path (distance_alignment x y),?_⟩
  intro k h
  obtain ⟨l,halign,hle⟩ := path_to_alignment h
  exact (distance_le_alignment halign).trans hle

theorem recurrence_is_edit_minimum (a b : α) (x y : List α) :
    IsLeast {k : ℕ | Path (a::x) (b::y) k}
      (min (distance x (b::y)+1)
        (min (distance (a::x) y+1) (distance x y + if a=b then 0 else 2))) := by
  simpa only [distance] using minimum_edit_cost (a::x) (b::y)

theorem step_reverse {x y : List α} {k : ℕ} (h : Step x y k) :
    Step x.reverse y.reverse k := by
  cases h with
  | delete pre post a =>
      simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using Step.delete post.reverse pre.reverse a
  | insert pre post a =>
      simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using Step.insert post.reverse pre.reverse a
  | substitute pre post a b =>
      simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using Step.substitute post.reverse pre.reverse a b

theorem path_reverse {x y : List α} {k : ℕ} (h : Path x y k) :
    Path x.reverse y.reverse k := by
  induction h with
  | refl x => exact Path.refl x.reverse
  | step hstep hpath ih => exact Path.step (step_reverse hstep) ih

theorem distance_reverse (x y : List α) : distance x.reverse y.reverse=distance x y := by
  apply Nat.le_antisymm
  · exact (minimum_edit_cost x.reverse y.reverse).2 (path_reverse (minimum_edit_cost x y).1)
  · have h : Path x y (distance x.reverse y.reverse) := by
      simpa using path_reverse (minimum_edit_cost x.reverse y.reverse).1
    exact (minimum_edit_cost x y).2 h

theorem distance_snoc (a b : α) (x y : List α) :
    distance (x++[a]) (y++[b]) =
      min (distance x (y++[b])+1)
        (min (distance (x++[a]) y+1) (distance x y + if a=b then 0 else 2)) := by
  have h1 := distance_reverse x (y++[b])
  have h2 := distance_reverse (x++[a]) y
  have h3 := distance_reverse x y
  have h4 := distance_reverse (x++[a]) (y++[b])
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append] at h1 h2 h4
  rw [←h4,distance,h1,h2,h3]

def prefixDistance (x y : List α) (i j : ℕ) : ℕ := distance (x.take i) (y.take j)

theorem prefix_recurrence (x y : List α) (i j : ℕ) (hi : i<x.length) (hj : j<y.length) :
    prefixDistance x y (i+1) (j+1) =
      min (prefixDistance x y i (j+1)+1)
        (min (prefixDistance x y (i+1) j+1)
          (prefixDistance x y i j + if x[i]=y[j] then 0 else 2)) := by
  unfold prefixDistance
  rw [List.take_succ_eq_append_getElem hi,List.take_succ_eq_append_getElem hj]
  exact distance_snoc x[i] y[j] (x.take i) (y.take j)

theorem prefix_is_edit_minimum (x y : List α) (i j : ℕ) :
    IsLeast {k : ℕ | Path (x.take i) (y.take j) k} (prefixDistance x y i j) := by
  exact minimum_edit_cost (x.take i) (y.take j)

theorem empty_source_minimum (y : List α) : IsLeast {k : ℕ | Path [] y k} y.length := by
  simpa only [distance] using minimum_edit_cost ([] : List α) y

theorem empty_target_minimum (x : List α) : IsLeast {k : ℕ | Path x [] k} x.length := by
  cases x with
  | nil => simpa only [distance,List.length_nil] using minimum_edit_cost ([] : List α) []
  | cons a x => simpa only [distance,List.length_cons] using minimum_edit_cost (a::x) []

theorem prefix_empty_target (x y : List α) (i : ℕ) (hi : i≤x.length) :
    prefixDistance x y i 0=i := by
  unfold prefixDistance
  simp only [List.take_zero]
  have h := (empty_target_minimum (x.take i)).unique (minimum_edit_cost (x.take i) [])
  simpa only [List.length_take,Nat.min_eq_left hi] using h.symm

theorem prefix_empty_source (x y : List α) (j : ℕ) (hj : j≤y.length) :
    prefixDistance x y 0 j=j := by
  simp only [prefixDistance,List.take_zero,distance,List.length_take,Nat.min_eq_left hj]

#print axioms alignment_add_source
#print axioms alignment_remove_source
#print axioms path_to_alignment
#print axioms minimum_edit_cost
#print axioms recurrence_is_edit_minimum
#print axioms prefix_recurrence
#print axioms prefix_is_edit_minimum
#print axioms empty_source_minimum
#print axioms prefix_empty_target
#print axioms prefix_empty_source
#print axioms empty_target_minimum

end Chapter08Dynamic
