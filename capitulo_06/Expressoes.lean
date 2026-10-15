import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open scoped BigOperators

namespace Chapter06Expressions

def acc : Fin 8 → Fin 5 := ![0,1,1,2,3,3,4,3]
def gen : Fin 8 → Fin 5 := ![0,1,2,2,0,0,3,4]
def joint (i j : Fin 5) : ℚ := (Finset.univ.filter (fun k => acc k=i ∧ gen k=j)).card/8

theorem joint_from_classes : joint=!![1/8,0,0,0,0;0,1/8,1/8,0,0;0,0,1/8,0,0;2/8,0,0,0,1/8;0,0,0,1/8,0] := by decide +kernel

def px (i : Fin 5) : ℚ := ∑ j,joint i j
def py (j : Fin 5) : ℚ := ∑ i,joint i j

theorem marginal_from_classes : px=![1/8,2/8,1/8,3/8,1/8] ∧ py=![3/8,1/8,2/8,1/8,1/8] := by decide +kernel

theorem marginal_count_plot :
 (fun j:Fin 5=>((j.val+1:ℕ),8*py j))= ![(1,3),(2,1),(3,2),(4,1),(5,1)] := by decide +kernel

theorem observed_es_count_plot :
 (fun j:Fin 5=>((j.val+1:ℕ),8*joint 1 j))= ![(1,0),(2,1),(3,1),(4,0),(5,0)] := by decide +kernel

theorem conditional_from_classes : joint 1 1/px 1=1/2 ∧ joint 1 1/py 1=1 ∧ joint 3 0/px 3=2/3 ∧ joint 3 4/px 3=1/3 := by decide +kernel

theorem joint_not_independent : joint 1 1 ≠ px 1*py 1 := by decide +kernel

noncomputable def entropy {n : ℕ} (p : Fin n → ℝ) : ℝ := -∑ i,p i*Real.logb 2 (p i)
noncomputable def conditionalEntropy {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ) : ℝ := -∑ i,∑ j,p i j*Real.logb 2 (p i j/(∑ k,p i k))
noncomputable def mutualInformation {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i,∑ j,p i j*Real.logb 2 (p i j/((∑ k,p i k)*(∑ k,p k j)))

theorem log_zero_weight (x y : ℝ) : (0:ℝ)*Real.logb 2 (0/(x*y))=0 := by simp

theorem mutual_term (p x y : ℝ) (hx : x≠0) (hy : y≠0) :
    p*Real.logb 2 (p/x)-p*Real.logb 2 y=p*Real.logb 2 (p/(x*y)) := by
  by_cases hp : p=0
  · simp [hp]
  · rw [Real.logb_div hp hx,Real.logb_div hp (mul_ne_zero hx hy),Real.logb_mul hx hy]
    ring

theorem marginal_entropy_expansion {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ) :
    entropy (fun j => ∑ i,p i j) = -∑ i,∑ j,p i j*Real.logb 2 (∑ k,p k j) := by
  unfold entropy
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem information_entropy_identity {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ)
    (hx : ∀ i,(∑ j,p i j)≠0) (hy : ∀ j,(∑ i,p i j)≠0) :
    mutualInformation p=entropy (fun j=>∑ i,p i j)-conditionalEntropy p := by
  rw [marginal_entropy_expansion]
  unfold conditionalEntropy mutualInformation
  simp_rw [←mutual_term _ _ _ (hx _) (hy _),Finset.sum_sub_distrib]
  ring

noncomputable def binomialSum (n : ℕ) (p : ℝ) (f : ℕ → ℝ) : ℝ := ∑ k∈Finset.range (n+1),(n.choose k:ℝ)*f k*p^k*(1-p)^(n-k)

theorem binomial_sum_succ (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    binomialSum (n+1) p f=p*binomialSum n p (fun k=>f (k+1))+(1-p)*binomialSum n p f := by
  have h := Finset.sum_choose_succ_mul (fun k l => f k*p^k*(1-p)^l) n
  simp only [binomialSum]
  conv_rhs => rw [add_comm]
  convert! h using 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp_rw [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hnk : n+1-k=n-k+1 := by have := Finset.mem_range.mp hk;omega
      rw [hnk,pow_succ]
      ring
    · apply Finset.sum_congr rfl
      intro k hk
      rw [pow_succ]
      ring

theorem binomial_sum_linear (n : ℕ) (p a b : ℝ) (f g : ℕ → ℝ) :
    binomialSum n p (fun k=>a*f k+b*g k)=a*binomialSum n p f+b*binomialSum n p g := by
  unfold binomialSum
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem binomial_total (n : ℕ) (p : ℝ) : binomialSum n p (fun _=>1)=1 := by
  induction n with
  | zero => simp [binomialSum]
  | succ n ih => rw [binomial_sum_succ,ih];ring

theorem binomial_mean (n : ℕ) (p : ℝ) : binomialSum n p (fun k=>(k:ℝ))=n*p := by
  induction n with
  | zero => simp [binomialSum]
  | succ n ih =>
    rw [binomial_sum_succ]
    have h : (fun k : ℕ => ((k+1:ℕ):ℝ))=(fun k : ℕ =>1*(k:ℝ)+1*1) := by funext k;push_cast;ring
    rw [h,binomial_sum_linear,ih,binomial_total]
    push_cast
    ring

theorem binomial_second_moment (n : ℕ) (p : ℝ) :
    binomialSum n p (fun k=>(k:ℝ)^2)=(n*p)^2+n*p*(1-p) := by
  induction n with
  | zero => simp [binomialSum]
  | succ n ih =>
    rw [binomial_sum_succ]
    have h : (fun k : ℕ => ((k+1:ℕ):ℝ)^2)=(fun k : ℕ =>1*(k:ℝ)^2+1*(2*(k:ℝ)+1*1)) := by funext k;push_cast;ring
    rw [h,binomial_sum_linear,binomial_sum_linear,ih,binomial_mean,binomial_total]
    push_cast
    ring

theorem binomial_variance (n : ℕ) (p : ℝ) :
    binomialSum n p (fun k=>((k:ℝ)-n*p)^2)=n*p*(1-p) := by
  have h : (fun k : ℕ => ((k:ℝ)-n*p)^2)=(fun k : ℕ =>1*(k:ℝ)^2+1*((-2*n*p)*(k:ℝ)+(n*p)^2*1)) := by funext k;ring
  rw [h,binomial_sum_linear,binomial_sum_linear,binomial_second_moment,binomial_mean,binomial_total]
  ring


noncomputable def binomialProbability (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k:ℝ)*p^k*(1-p)^(n-k)

theorem binomial_probability_nonnegative (n k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomialProbability n p k := by
  unfold binomialProbability
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _)) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem binomial_probability_total (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n+1),binomialProbability n p k)=1 := by
  simpa [binomialSum,binomialProbability] using binomial_total n p

theorem binomial_probability_at_most_one (n k : ℕ) (p : ℝ) (hk : k ≤ n) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialProbability n p k ≤ 1 := by
  rw [←binomial_probability_total n p]
  exact Finset.single_le_sum (fun j _=>binomial_probability_nonnegative n j p hp hp1) (Finset.mem_range.mpr (by omega))

theorem binomial_probability_mean (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n+1),(k:ℝ)*binomialProbability n p k)=n*p := by
  convert binomial_mean n p using 1
  unfold binomialSum binomialProbability
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem binomial_probability_variance (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n+1),binomialProbability n p k*((k:ℝ)-n*p)^2)=n*p*(1-p) := by
  convert binomial_variance n p using 1
  unfold binomialSum binomialProbability
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem negative_binomial_counterexample : binomialProbability 1 2 0 = -1 := by
  norm_num [binomialProbability]

theorem entry_le_row {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ)
    (hp : ∀ i j,0 ≤ p i j) (i : Fin m) (j : Fin n) : p i j ≤ ∑ k,p i k := by
  exact Finset.single_le_sum (fun k _=>hp i k) (Finset.mem_univ j)

theorem entry_le_column {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ)
    (hp : ∀ i j,0 ≤ p i j) (i : Fin m) (j : Fin n) : p i j ≤ ∑ k,p k j := by
  exact Finset.single_le_sum (fun k _=>hp k j) (Finset.mem_univ i)

theorem information_term_valid {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ)
    (hp : ∀ i j,0 ≤ p i j) (i : Fin m) (j : Fin n) :
    p i j*Real.logb 2 (p i j/(∑ k,p i k))-p i j*Real.logb 2 (∑ k,p k j)=
    p i j*Real.logb 2 (p i j/((∑ k,p i k)*(∑ k,p k j))) := by
  by_cases h : p i j=0
  · simp [h]
  · have hpos : 0 < p i j := lt_of_le_of_ne (hp i j) (Ne.symm h)
    exact mutual_term _ _ _ (ne_of_gt (lt_of_lt_of_le hpos (entry_le_row p hp i j)))
      (ne_of_gt (lt_of_lt_of_le hpos (entry_le_column p hp i j)))

theorem information_entropy_identity_valid {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ)
    (hp : ∀ i j,0 ≤ p i j) :
    mutualInformation p=entropy (fun j=>∑ i,p i j)-conditionalEntropy p := by
  rw [marginal_entropy_expansion]
  unfold conditionalEntropy mutualInformation
  simp_rw [←information_term_valid p hp,Finset.sum_sub_distrib]
  ring

theorem conditional_probability_valid {m n : ℕ} (p : Matrix (Fin m) (Fin n) ℝ)
    (hp : ∀ i j,0 ≤ p i j) (i : Fin m) (hi : 0 < ∑ k,p i k) :
    (∀ j,0 ≤ p i j/(∑ k,p i k)) ∧ (∑ j,p i j/(∑ k,p i k))=1 := by
  constructor
  · intro j
    exact div_nonneg (hp i j) hi.le
  · rw [←Finset.sum_div,div_self (ne_of_gt hi)]

#print axioms binomial_probability_nonnegative
#print axioms binomial_probability_total
#print axioms binomial_probability_at_most_one
#print axioms binomial_probability_mean
#print axioms binomial_probability_variance
#print axioms negative_binomial_counterexample
#print axioms information_entropy_identity_valid
#print axioms conditional_probability_valid


theorem greek_joint_valid : (∀ i j,0 ≤ joint i j) ∧ (∑ i,∑ j,joint i j)=1 := by decide +kernel

theorem greek_conditionals_valid : ∀ i,0 < px i ∧ (∑ j,joint i j/px i)=1 := by decide +kernel

theorem greek_entropy_from_classes :
    entropy (fun j=>(py j:ℝ))=11/4-(3/8)*Real.logb 2 3 := by
  have h2 : Real.logb 2 2=1 := Real.logb_self_eq_one (by norm_num)
  have h8 : Real.logb 2 8=3 := by rw [show (8:ℝ)=2^3 by norm_num,Real.logb_pow,h2];norm_num
  have h4 : Real.logb 2 4=2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.logb_pow,h2];norm_num
  rw [show py=![3/8,1/8,2/8,1/8,1/8] from marginal_from_classes.2]
  norm_num [entropy,Fin.sum_univ_succ,Real.logb_div,h8,h4]
  ring

theorem greek_conditional_entropy_from_classes :
    conditionalEntropy (fun i j=>(joint i j:ℝ))=(3/8)*Real.logb 2 3 := by
  have h2 : Real.logb 2 2=1 := Real.logb_self_eq_one (by norm_num)
  rw [joint_from_classes]
  norm_num [conditionalEntropy,Fin.sum_univ_succ,Real.logb_div,h2]
  ring

theorem greek_mutual_information_from_classes :
    mutualInformation (fun i j=>(joint i j:ℝ))=11/4-(3/4)*Real.logb 2 3 := by
  have hp : ∀ i j,0 ≤ (joint i j:ℝ) := by intro i j;exact_mod_cast greek_joint_valid.1 i j
  rw [information_entropy_identity_valid _ hp]
  have he : (fun j=>∑ i,(joint i j:ℝ))=(fun j=>(py j:ℝ)) := by
    funext j
    simp [py]
  rw [he,greek_entropy_from_classes,greek_conditional_entropy_from_classes]
  ring

#print axioms greek_joint_valid
#print axioms greek_conditionals_valid
#print axioms greek_entropy_from_classes
#print axioms greek_conditional_entropy_from_classes
#print axioms greek_mutual_information_from_classes


noncomputable def guardedPMI (jointMass rowMass columnMass : ℝ) : Option ℝ :=
  if 0 < jointMass ∧ 0 < rowMass ∧ 0 < columnMass then
    some (Real.logb 2 (jointMass/(rowMass*columnMass))) else none

theorem pmi_positive_domain (jointMass rowMass columnMass : ℝ)
    (hj : 0 < jointMass) (hr : 0 < rowMass) (hc : 0 < columnMass) :
    guardedPMI jointMass rowMass columnMass=some (Real.logb 2 (jointMass/(rowMass*columnMass))) ∧
    0 < jointMass/(rowMass*columnMass) := by
  exact ⟨by simp [guardedPMI,hj,hr,hc],div_pos hj (mul_pos hr hc)⟩

theorem pmi_zero_rejected (a b : ℝ) :
    guardedPMI 0 a b=none ∧ guardedPMI a 0 b=none ∧ guardedPMI a b 0=none := by
  simp [guardedPMI]

#print axioms pmi_positive_domain
#print axioms pmi_zero_rejected


def constantCellJoint (i : Fin 1) (j : Fin 5) : ℚ :=
  (Finset.univ.filter (fun k : Fin 8=>gen k=j)).card/8

theorem constant_cell_joint_from_classes : constantCellJoint 0=py := by decide +kernel

theorem constant_cell_mass : (∑ j,constantCellJoint 0 j)=1 := by decide +kernel

theorem constant_cell_no_information :
    conditionalEntropy (fun i j=>(constantCellJoint i j:ℝ))=entropy (fun j=>(py j:ℝ)) := by
  unfold conditionalEntropy entropy
  simp only [Fin.sum_univ_one]
  have hm : (∑ j,(constantCellJoint 0 j:ℝ))=1 := by exact_mod_cast constant_cell_mass
  rw [hm]
  simp only [div_one,constant_cell_joint_from_classes]

#print axioms constant_cell_joint_from_classes
#print axioms constant_cell_mass
#print axioms constant_cell_no_information

theorem constant_cell_conditional_entropy_zero :
    conditionalEntropy (fun j i=>(constantCellJoint i j:ℝ))=0 := by
  have h : ∀ i j,constantCellJoint i j=(![3/8,1/8,2/8,1/8,1/8]:Fin 5→ℚ) j := by decide +kernel
  simp_rw [h]
  norm_num [conditionalEntropy,Fin.sum_univ_succ]

theorem constant_cell_mutual_information_zero :
    mutualInformation (fun i j=>(constantCellJoint i j:ℝ))=0 ∧
    mutualInformation (fun j i=>(constantCellJoint i j:ℝ))=0 := by
  have h : ∀ i j,constantCellJoint i j=(![3/8,1/8,2/8,1/8,1/8]:Fin 5→ℚ) j := by decide +kernel
  simp_rw [h]
  norm_num [mutualInformation,Fin.sum_univ_succ]

#print axioms constant_cell_conditional_entropy_zero
#print axioms constant_cell_mutual_information_zero

end Chapter06Expressions

#print axioms Chapter06Expressions.joint_from_classes
#print axioms Chapter06Expressions.marginal_from_classes
#print axioms Chapter06Expressions.conditional_from_classes
#print axioms Chapter06Expressions.joint_not_independent
#print axioms Chapter06Expressions.log_zero_weight
#print axioms Chapter06Expressions.mutual_term
#print axioms Chapter06Expressions.marginal_entropy_expansion
#print axioms Chapter06Expressions.information_entropy_identity
#print axioms Chapter06Expressions.binomial_sum_succ
#print axioms Chapter06Expressions.binomial_sum_linear
#print axioms Chapter06Expressions.binomial_total
#print axioms Chapter06Expressions.binomial_mean
#print axioms Chapter06Expressions.binomial_second_moment
#print axioms Chapter06Expressions.binomial_variance
