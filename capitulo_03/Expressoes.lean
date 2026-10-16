import Mathlib

set_option maxHeartbeats 4000000

namespace Chapter03Expressions

def acc : Fin 8 → String := !["us","es","es","is","a","a","i","a"]
def gen : Fin 8 → String := !["u","zero","s","s","u","u","us","os"]
def fiber (f : Fin 8 → String) (s : String) : Finset (Fin 8) := Finset.univ.filter (fun i => f i = s)
def relation : Finset (String × String) := Finset.univ.image (fun i => (acc i,gen i))

theorem fibers :
    fiber acc "us" = {0} ∧ fiber acc "es" = {1,2} ∧ fiber acc "is" = {3} ∧
    fiber acc "a" = {4,5,7} ∧ fiber acc "i" = {6} := by decide +kernel

theorem partition_disjoint (a b : String) (h : a ≠ b) : Disjoint (fiber acc a) (fiber acc b) := by
  apply Finset.disjoint_left.mpr
  intro x ha hb
  exact h ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)

theorem partition_cover : fiber acc "us" ∪ fiber acc "es" ∪ fiber acc "is" ∪ fiber acc "a" ∪ fiber acc "i" = Finset.univ := by decide +kernel

theorem relation_from_columns : relation = {("us","u"),("es","zero"),("es","s"),("is","s"),("a","u"),("i","us"),("a","os")} ∧ relation.card = 7 := by decide +kernel

theorem set_membership : (5:ℕ) ∈ ({5,6,8}:Finset ℕ) ∧ (1:ℕ) ∉ ({5,6,8}:Finset ℕ) ∧ (({5,6,8}:Finset ℕ) ∩ {1,5,6}).card=2 ∧ (({5,6,8}:Finset ℕ) ∪ {1,5,6}).card=4 := by decide +kernel

def All {E : Type*} (A B : Set E) : Prop := ∀ x, x ∈ A → x ∈ B
def Some {E : Type*} (A B : Set E) : Prop := ∃ x, x ∈ A ∧ x ∈ B
def No {E : Type*} (A B : Set E) : Prop := ¬ ∃ x, x ∈ A ∧ x ∈ B

theorem all_sets {E : Type*} (A B : Set E) : All A B ↔ A ⊆ B := Iff.rfl

theorem some_sets {E : Type*} (A B : Set E) : Some A B ↔ (A ∩ B).Nonempty := Iff.rfl

theorem no_sets {E : Type*} (A B : Set E) : No A B ↔ A ∩ B = ∅ := by
  simp [No,Set.eq_empty_iff_forall_notMem]

def Q {E : Type*} (P : E → Prop) : (E → Prop) → Prop := fun F => ∃ x, P x ∧ F x
def V {E : Type*} (O : E → E → Prop) (Q₁ Q₂ : (E → Prop) → Prop) : Prop := Q₂ (fun x => Q₁ (fun y => O x y))

theorem verb_object_beta {E : Type*} (T : E → Prop) (O : E → E → Prop) :
    V O (Q T) = (fun Q₂ => Q₂ (fun x => ∃ y, T y ∧ O x y)) := rfl

theorem verb_subject_beta {E : Type*} (W T : E → Prop) (O : E → E → Prop) :
    V O (Q T) (Q W) = (∃ x, W x ∧ ∃ y, T y ∧ O x y) := rfl

theorem de_morgan_all {E : Type*} (xs : List E) (P : E → Bool) :
    (!(xs.all P)) = xs.any (fun x => !(P x)) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.not_and]

theorem de_morgan_any {E : Type*} (xs : List E) (P : E → Bool) :
    (!(xs.any P)) = xs.all (fun x => !(P x)) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Bool.not_or]

theorem modal_not_veridical : ¬ (∀ (M : Prop → Prop) (P : Prop), M P → P) := by
  intro h
  exact h (fun _ => True) False trivial

structure ParadigmCell where
  nounClass : Fin 8
  grammaticalCase : String
  number : String
  ending : String
  deriving DecidableEq

def genitiveSeven : ParadigmCell := ⟨6,"genitivo","singular",gen 6⟩
def accusativeOne : ParadigmCell := ⟨0,"acusativo","plural",acc 0⟩

theorem feature_record : genitiveSeven=⟨6,"genitivo","singular","us"⟩ ∧
    genitiveSeven.ending=accusativeOne.ending ∧ genitiveSeven≠accusativeOne := by decide +kernel

#print axioms feature_record

theorem published_sets_from_columns :
    (fiber acc "a").image (fun i=>i.val+1) = ({5,6,8}:Finset ℕ) ∧
    (fiber gen "u").image (fun i=>i.val+1) = ({1,5,6}:Finset ℕ) := by decide +kernel

#print axioms published_sets_from_columns

theorem morphological_product :
    (Finset.univ.image acc).card=5 ∧ (Finset.univ.image gen).card=5 ∧
    ((Finset.univ.image acc) ×ˢ (Finset.univ.image gen)).card=25 ∧
    relation ⊆ (Finset.univ.image acc) ×ˢ (Finset.univ.image gen) := by decide +kernel

#print axioms morphological_product

end Chapter03Expressions

#print axioms Chapter03Expressions.fibers
#print axioms Chapter03Expressions.partition_disjoint
#print axioms Chapter03Expressions.partition_cover
#print axioms Chapter03Expressions.relation_from_columns
#print axioms Chapter03Expressions.set_membership
#print axioms Chapter03Expressions.all_sets
#print axioms Chapter03Expressions.some_sets
#print axioms Chapter03Expressions.no_sets
#print axioms Chapter03Expressions.verb_object_beta
#print axioms Chapter03Expressions.verb_subject_beta
#print axioms Chapter03Expressions.de_morgan_all
#print axioms Chapter03Expressions.de_morgan_any
#print axioms Chapter03Expressions.modal_not_veridical
