import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter03

namespace c03_r01
theorem arithmetic_001 : ((3+3-2) : ℚ) = (4) := by norm_num
def A : Finset ℕ := {5,6,8}
def B : Finset ℕ := {1,5,6}
theorem publishedSets : A ∩ B = {5,6} ∧ A ∪ B = {1,5,6,8} ∧ A \ B = {8} ∧ A.card=3 ∧ B.card=3 := by decide +kernel

end c03_r01

namespace c03_r02
theorem differenceEmpty {α : Type*} (S L : Set α) (h : S ⊆ L) : S \ L = ∅ := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hx.2 (h hx.1)
theorem noOverlap {α : Type*} (L U : Set α) : L ∩ (U \ L) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact hx.2.2 hx.1
theorem coverUniverse {α : Type*} (L U : Set α) (h : L ⊆ U) : L ∪ (U \ L)=U := by
  ext x
  simp only [Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro (hx | hx)
    · exact h hx
    · exact hx.1
  · intro hx
    by_cases hl : x ∈ L
    · exact Or.inl hl
    · exact Or.inr ⟨hx,hl⟩

end c03_r02

namespace c03_r03
theorem arithmetic_001 : ((5*5) : ℚ) = (25) := by norm_num
def R : List (String × String) := [("-us", "-u"), ("-es", "zero"), ("-es", "-s"), ("-is", "-s"), ("-a", "-u"), ("-i", "-us"), ("-a", "-os")]
theorem sevenPairs : R.length=7 ∧ R.dedup.length=7 := by decide +kernel
theorem notFunctional : ¬ (∀ x y z : String, (x,y) ∈ R → (x,z) ∈ R → y=z) := by
  intro h
  have he := h "-a" "-u" "-os" (by decide +kernel) (by decide +kernel)
  exact (by decide : ("-u" : String) ≠ "-os") he
def genitivePlural (_d : Fin 8) : String := "-on"
theorem notInjective : ¬ Function.Injective genitivePlural := by
  intro h
  have he : (0 : Fin 8) = 1 := h rfl
  norm_num at he

end c03_r03

namespace c03_r04
theorem disjunctionElimination (p q : Prop) (h : p ∨ q) (hn : ¬p) : q := h.resolve_left hn
theorem modusPonens (p q : Prop) (h : p → q) (hp : p) : q := h hp
theorem truthTable : ([(true,true),(true,false),(false,true),(false,false)] : List (Bool × Bool)).map (fun x => (x.1,x.2,!x.1,x.1 && x.2,x.1 || x.2,!x.1 || x.2)) = [(true,true,false,true,true,true),(true,false,false,false,true,false),(false,true,true,false,true,true),(false,false,true,false,false,true)] := by decide +kernel

end c03_r04

namespace c03_r05
theorem commonWitnessEntailsVariable {α : Type*} (F D : α → Prop) (R : α → α → Prop)
  (h : ∃ x, D x ∧ ∀ y, F y → R y x) : ∀ y, F y → ∃ x, D x ∧ R y x := by
  obtain ⟨x,hd,hr⟩ := h
  intro y hy
  exact ⟨x,hd,hr y hy⟩

end c03_r05

namespace c03_r06
theorem arithmetic_001 : ((4+2) : ℚ) = (6) := by norm_num
theorem arithmetic_002 : ((4+3+2) : ℚ) = (7+2) := by norm_num
theorem arithmetic_003 : ((7+2) : ℚ) = (9) := by norm_num
theorem publishedChains : ("work" ++ "ed" : String) = "worked" ∧ ("worked" : String).length=6 ∧ ("care" ++ "ful" ++ "ly" : String) = "carefully" ∧ ("carefully" : String).length=9 := by decide +kernel
theorem concatenationAssociative (a b c : String) : (a++b)++c=a++(b++c) := String.append_assoc
theorem emptyIdentity (u : String) : u++""=u ∧ ""++u=u := by simp

end c03_r06

namespace c03_d01
theorem inclusionChain {α : Type*} (S L N : Set α) (hSL : S ⊆ L) (hLN : L ⊆ N) : S ⊆ N := fun _ hx => hLN (hSL hx)
theorem notUniversal {α : Type*} (P : α → Prop) : (¬ ∀ x, P x) ↔ ∃ x, ¬P x := by
  classical
  exact not_forall
theorem notExistential {α : Type*} (P : α → Prop) : (¬ ∃ x, P x) ↔ ∀ x, ¬P x := not_exists

end c03_d01

namespace c03_d02
theorem arithmetic_001 : ((1+2+1+3+1) : ℚ) = (8) := by norm_num
theorem sameOutputEquivalence {α β : Type*} (f : α → β) : Equivalence (fun d e => f d=f e) := by
  constructor
  · intro d
    rfl
  · intro d e h
    exact h.symm
  · intro d e g hde heg
    exact hde.trans heg
def acc : List String := ["-us","-es","-es","-is","-a","-a","-i","-a"]
theorem fiveForms : acc.length=8 ∧ acc.dedup.length=5 ∧ acc.count "-a"=3 ∧ acc.count "-es"=2 := by decide +kernel
theorem partition : (([{1},{2,3},{4},{5,6,8},{7}] : List (Finset ℕ)).foldl (· ∪ ·) ∅) = {1,2,3,4,5,6,7,8} := by decide +kernel

end c03_d02

namespace c03_p01
theorem lexicalBeta {α : Type*} (W : α → Prop) : ((fun P : α → Prop => fun x => P x) W)=(fun x => W x) := rfl
theorem subjectBeta {α : Type*} (W : α → Prop) : ((fun F : α → Prop => fun G : α → Prop => ∃ x, F x ∧ G x) W)=(fun G => ∃ x, W x ∧ G x) := rfl
theorem objectBeta {α : Type*} (T : α → Prop) (O : α → α → Prop) (x : α) :
  ((fun F : α → Prop => ∃ y, T y ∧ F y) (fun y => O x y)) = (∃ y, T y ∧ O x y) := rfl
theorem renamedArgument {α : Type*} (F : α → Prop) : (fun x => F x)=(fun z => F z) := rfl
theorem objectIntermediate {α : Type*} (T : α → Prop) (O : α → α → Prop) (x : α) :
  ((fun F : α → Prop => ∃ y, T y ∧ F y) (fun z => O x z)) =
  (∃ y, T y ∧ (fun z => O x z) y) := rfl
theorem subjectIntermediate {α : Type*} (W T : α → Prop) (O : α → α → Prop) :
  ((fun G : α → Prop => ∃ x, W x ∧ G x) (fun z => ∃ y, T y ∧ O z y)) =
  (∃ x, W x ∧ (fun z => ∃ y, T y ∧ O z y) x) := rfl
theorem publishedComposition {α : Type*} (W T : α → Prop) (O : α → α → Prop) :
  (((fun Q1 : (α → Prop) → Prop => fun Q2 : (α → Prop) → Prop => Q2 (fun x => Q1 (fun y => O x y)))
    (fun F => ∃ y, T y ∧ F y)) (fun G => ∃ x, W x ∧ G x)) = (∃ x, W x ∧ ∃ y, T y ∧ O x y) := rfl

end c03_p01

namespace c03_p02
theorem restrictedUniversal {α : Type*} (S W C : α → Prop) (h : ∀ x, S x ∧ W x → C x) (x : α) (hs : S x) (hw : W x) : C x := h x ⟨hs,hw⟩
theorem allWithWitness {α : Type*} (A B : Set α) (h : A ⊆ B) (hn : A.Nonempty) : (A ∩ B).Nonempty := by
  obtain ⟨x,hx⟩ := hn
  exact ⟨x,hx,h hx⟩
theorem emptyUniversal {α : Type*} (B : Set α) : (∅ : Set α) ⊆ B := Set.empty_subset B
theorem mostMonotonicity {α : Type*} (Most : (α → Prop) → (α → Prop) → Prop)
  (rule : ∀ F G H, Most F G → (∀ x, G x → H x) → Most F H)
  (F G H : α → Prop) (h : Most F G) (inc : ∀ x, G x → H x) : Most F H := rule F G H h inc
theorem mostExistence {α : Type*} (Most : (α → Prop) → (α → Prop) → Prop)
  (rule : ∀ F G, Most F G → ∃ x, F x ∧ G x) (F G : α → Prop) (h : Most F G) : ∃ x, F x ∧ G x := rule F G h
theorem manageInference {α : Type*} (S C : α → Prop) (Manage : α → Prop → Prop)
  (veridical : ∀ x P, Manage x P → P) (h : ∃ x, S x ∧ Manage x (C x)) : ∃ x, S x ∧ C x := by
  obtain ⟨x,hs,hm⟩ := h
  exact ⟨x,hs,veridical x (C x) hm⟩

end c03_p02

namespace c03_p03
theorem arithmetic_001 : ((69-59) : ℚ) = (10) := by norm_num
theorem arithmetic_002 : ((8651/100-85) : ℚ) = (151/100) := by norm_num
theorem arithmetic_003 : ((96-72) : ℚ) = (24) := by norm_num
theorem arithmetic_004 : ((534+303) : ℚ) = (837) := by norm_num
end c03_p03

namespace c03_n01
theorem arithmetic_001 : ((4/4) : ℚ) = (1) := by norm_num
theorem arithmetic_002 : ((3/4) : ℚ) = (75/100) := by norm_num
theorem arithmetic_003 : ((2/4) : ℚ) = (1/2) := by norm_num
theorem arithmetic_004 : ((1/2) : ℚ) = (5/10) := by norm_num
theorem arithmetic_005 : ((158/200) : ℚ) = (79/100) := by norm_num
theorem arithmetic_006 : ((72/200) : ℚ) = (36/100) := by norm_num
def A : Finset String := {"s","or","pr","endere"}
def B : Finset String := {"s","or","pr","endere","bbe"}
def C : Finset String := {"s","or","pr","end","iamo"}
def D : Finset String := {"s","or","pre","se"}
theorem publishedSegments : A ⊆ B ∧ A.card=4 ∧ B.card=5 ∧ C.card=5 ∧ D.card=4 ∧ (A∩B).card=4 ∧ (A∩C).card=3 ∧ (A∩D).card=2 := by decide +kernel
theorem interBounds {α : Type*} [DecidableEq α] (X Y : Finset α) : (X∩Y).card ≤ min X.card Y.card :=
  le_min (Finset.card_le_card Finset.inter_subset_left) (Finset.card_le_card Finset.inter_subset_right)
theorem coefficientBounds (n a b : ℚ) (hn : 0 ≤ n) (ha : 0 < a) (hb : 0 < b) (hna : n ≤ a) (hnb : n ≤ b) : 0 ≤ n/min a b ∧ n/min a b ≤ 1 := by
  have hm : 0 < min a b := lt_min ha hb
  constructor
  · exact div_nonneg hn (le_of_lt hm)
  · apply (div_le_iff₀ hm).2
    simpa using le_min hna hnb
theorem subsetOne {α : Type*} [DecidableEq α] (X Y : Finset α) (hXY : X ⊆ Y) (hx : X.Nonempty) :
  ((X∩Y).card : ℚ)/(min X.card Y.card : ℕ)=1 := by
  rw [Finset.inter_eq_left.mpr hXY, min_eq_left (Finset.card_le_card hXY)]
  have hc : (0 : ℚ) < X.card := by exact_mod_cast (Finset.card_pos.mpr hx)
  exact div_self (ne_of_gt hc)

end c03_n01

namespace c03_n02
theorem arithmetic_001 : ((8740/100) : ℚ) > (4756/100) := by norm_num
theorem arithmetic_002 : ((6476/100) : ℚ) > (3872/100) := by norm_num
theorem arithmetic_003 : ((6516/100) : ℚ) > (2431/100) := by norm_num
theorem arithmetic_004 : ((3491/100) : ℚ) < (4976/100) := by norm_num
theorem removeConjunct {α : Type*} (M S D : α → Prop) (h : ∀ x, M x → S x ∧ D x) : ∀ x, M x → D x := fun x hx => (h x hx).2
theorem restrictMen {α : Type*} (M B S D : α → Prop) (lexical : ∀ x, B x → M x) (h : ∀ x, M x → S x ∧ D x) : ∀ x, B x → S x ∧ D x := fun x hx => h x (lexical x hx)

end c03_n02
end Chapter03
#print axioms Chapter03.c03_r01.arithmetic_001
#print axioms Chapter03.c03_r01.publishedSets
#print axioms Chapter03.c03_r02.differenceEmpty
#print axioms Chapter03.c03_r02.noOverlap
#print axioms Chapter03.c03_r02.coverUniverse
#print axioms Chapter03.c03_r03.arithmetic_001
#print axioms Chapter03.c03_r03.sevenPairs
#print axioms Chapter03.c03_r03.notFunctional
#print axioms Chapter03.c03_r03.notInjective
#print axioms Chapter03.c03_r04.disjunctionElimination
#print axioms Chapter03.c03_r04.modusPonens
#print axioms Chapter03.c03_r04.truthTable
#print axioms Chapter03.c03_r05.commonWitnessEntailsVariable
#print axioms Chapter03.c03_r06.arithmetic_001
#print axioms Chapter03.c03_r06.arithmetic_002
#print axioms Chapter03.c03_r06.arithmetic_003
#print axioms Chapter03.c03_r06.publishedChains
#print axioms Chapter03.c03_r06.concatenationAssociative
#print axioms Chapter03.c03_r06.emptyIdentity
#print axioms Chapter03.c03_d01.inclusionChain
#print axioms Chapter03.c03_d01.notUniversal
#print axioms Chapter03.c03_d01.notExistential
#print axioms Chapter03.c03_d02.arithmetic_001
#print axioms Chapter03.c03_d02.sameOutputEquivalence
#print axioms Chapter03.c03_d02.fiveForms
#print axioms Chapter03.c03_d02.partition
#print axioms Chapter03.c03_p01.lexicalBeta
#print axioms Chapter03.c03_p01.subjectBeta
#print axioms Chapter03.c03_p01.objectBeta
#print axioms Chapter03.c03_p01.renamedArgument
#print axioms Chapter03.c03_p01.objectIntermediate
#print axioms Chapter03.c03_p01.subjectIntermediate
#print axioms Chapter03.c03_p01.publishedComposition
#print axioms Chapter03.c03_p02.restrictedUniversal
#print axioms Chapter03.c03_p02.allWithWitness
#print axioms Chapter03.c03_p02.emptyUniversal
#print axioms Chapter03.c03_p02.mostMonotonicity
#print axioms Chapter03.c03_p02.mostExistence
#print axioms Chapter03.c03_p02.manageInference
#print axioms Chapter03.c03_p03.arithmetic_001
#print axioms Chapter03.c03_p03.arithmetic_002
#print axioms Chapter03.c03_p03.arithmetic_003
#print axioms Chapter03.c03_p03.arithmetic_004
#print axioms Chapter03.c03_n01.arithmetic_001
#print axioms Chapter03.c03_n01.arithmetic_002
#print axioms Chapter03.c03_n01.arithmetic_003
#print axioms Chapter03.c03_n01.arithmetic_004
#print axioms Chapter03.c03_n01.arithmetic_005
#print axioms Chapter03.c03_n01.arithmetic_006
#print axioms Chapter03.c03_n01.publishedSegments
#print axioms Chapter03.c03_n01.interBounds
#print axioms Chapter03.c03_n01.coefficientBounds
#print axioms Chapter03.c03_n01.subsetOne
#print axioms Chapter03.c03_n02.arithmetic_001
#print axioms Chapter03.c03_n02.arithmetic_002
#print axioms Chapter03.c03_n02.arithmetic_003
#print axioms Chapter03.c03_n02.arithmetic_004
#print axioms Chapter03.c03_n02.removeConjunct
#print axioms Chapter03.c03_n02.restrictMen
