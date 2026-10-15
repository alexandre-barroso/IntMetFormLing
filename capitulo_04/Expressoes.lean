import Mathlib

set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

open scoped BigOperators

namespace Chapter04Expressions

def edges : Finset (Fin 5 × Fin 5) := {(1,0),(1,2),(1,4),(4,3)}
def A : Matrix (Fin 5) (Fin 5) ℚ := fun i j => if (i,j) ∈ edges then 1 else 0

theorem adjacency : A = !![0,0,0,0,0;1,0,1,0,1;0,0,0,0,0;0,0,0,0,0;0,0,0,1,0] := by decide +kernel

theorem degree_vectors : (fun i => ∑ j,A i j) = ![0,3,0,0,1] ∧ (fun j => ∑ i,A i j) = ![1,0,1,1,1] := by
  constructor <;> ext i <;> fin_cases i <;> norm_num [adjacency,Fin.sum_univ_succ]

theorem adjacency_entries : A 1 4=1 ∧ A 4 1=0 ∧ A 1 3=0 ∧ (∑ i,∑ j,A i j)=4 := by
  decide +kernel

theorem two_steps : A*A = !![0,0,0,0,0;0,0,0,1,0;0,0,0,0,0;0,0,0,0,0;0,0,0,0,0] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [adjacency,Matrix.mul_apply,Fin.sum_univ_succ]

theorem no_three_steps : (A*A)*A=0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [two_steps,adjacency,Matrix.mul_apply,Fin.sum_univ_succ]

def linked (i j : Fin 5) : Bool := decide ((i,j) ∈ edges ∨ (j,i) ∈ edges)
def walk : ℕ → Fin 5 → Fin 5 → Bool
  | 0,i,j => i==j
  | n+1,i,j => (List.finRange 5).any (fun k => linked i k && walk n k j)

theorem graph_distance : walk 2 0 4=true ∧ walk 0 0 4=false ∧ walk 1 0 4=false := by decide +kernel

def positionA (i : Fin 5) : ℤ := i.val+1
def positionB : Fin 5 → ℤ := ![1,2,5,3,4]
def dependencyLength (p : Fin 5 → ℤ) : ℤ := ∑ e∈edges,|p e.1-p e.2|

theorem order_lengths : dependencyLength positionA=6 ∧ dependencyLength positionB=7 := by decide +kernel

theorem permutationB : Function.Injective positionB ∧ Finset.univ.image positionB={1,2,3,4,5} := by decide +kernel

def T : Matrix (Fin 2) (Fin 8) ℚ := !![1,1,1,1,1,1,0,0;0,0,0,0,1,1,1,1]
def R : Matrix (Fin 8) (Fin 4) ℚ := !![1,0,0,0;1,0,0,0;1,0,0,0;1,0,0,0;1,1,0,1;1,1,1,1;0,0,0,1;0,0,0,1]

theorem polysemy : T*R = !![6,2,1,2;2,2,1,4] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [T,R,Matrix.mul_apply,Fin.sum_univ_succ]

def cherry : Fin 3 → ℝ := ![442,8,2]
def digital : Fin 3 → ℝ := ![5,1683,1670]
def information : Fin 3 → ℝ := ![5,3982,3325]
noncomputable def length {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i,(v i)^2)
noncomputable def cosine {n : ℕ} (v w : Fin n → ℝ) : ℝ := (∑ i,v i*w i)/(length v*length w)

theorem dot_products : (∑ i,cherry i*information i)=40716 ∧ (∑ i,digital i*information i)=12254481 := by norm_num [cherry,digital,information,Fin.sum_univ_succ]

theorem squared_lengths : length cherry=Real.sqrt 195432 ∧ length digital=Real.sqrt 5621414 ∧ length information=Real.sqrt 26911974 := by norm_num [length,cherry,digital,information,Fin.sum_univ_succ]

theorem cosine_square (d a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    (d/(Real.sqrt a*Real.sqrt b))^2=d^2/(a*b) := by
  rw [div_pow,mul_pow,Real.sq_sqrt ha,Real.sq_sqrt hb]

theorem cosine_cherry_bounds : 175/10000 < cosine cherry information ∧ cosine cherry information < 185/10000 := by
  have he : cosine cherry information = 40716/(Real.sqrt 195432*Real.sqrt 26911974) := by
    unfold cosine; rw [dot_products.1,squared_lengths.1,squared_lengths.2.2]
  rw [he]
  have hs := cosine_square 40716 195432 26911974 (by norm_num) (by norm_num)
  have hp : 0 ≤ (40716:ℝ)/(Real.sqrt 195432*Real.sqrt 26911974) := by positivity
  have hlow : (175/10000:ℝ)^2 < 40716^2/(195432*26911974) := by norm_num
  have hhigh : (40716:ℝ)^2/(195432*26911974) < (185/10000)^2 := by norm_num
  constructor <;> nlinarith

theorem cosine_digital_bounds : 9955/10000 < cosine digital information ∧ cosine digital information < 9965/10000 := by
  have he : cosine digital information = 12254481/(Real.sqrt 5621414*Real.sqrt 26911974) := by
    unfold cosine; rw [dot_products.2,squared_lengths.2.1,squared_lengths.2.2]
  rw [he]
  have hs := cosine_square 12254481 5621414 26911974 (by norm_num) (by norm_num)
  have hp : 0 ≤ (12254481:ℝ)/(Real.sqrt 5621414*Real.sqrt 26911974) := by positivity
  have hlow : (9955/10000:ℝ)^2 < 12254481^2/(5621414*26911974) := by norm_num
  have hhigh : (12254481:ℝ)^2/(5621414*26911974) < (9965/10000)^2 := by norm_num
  constructor <;> nlinarith

theorem length_positive {n : ℕ} (v : Fin n → ℝ) (h : v ≠ 0) : 0 < length v := by
  apply Real.sqrt_pos.mpr
  apply Finset.sum_pos'
  · intro i hi; exact sq_nonneg _
  · have hi : ∃ i,v i≠0 := by simpa [funext_iff] using h
    obtain ⟨i,hi⟩ := hi
    exact ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩

theorem unit_normalization {n : ℕ} (v : Fin n → ℝ) (h : v ≠ 0) :
    length (fun i => v i/length v)=1 := by
  have hs : (length v)^2=∑ i,(v i)^2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  have hp := ne_of_gt (length_positive v h)
  change Real.sqrt (∑ i,(v i/length v)^2)=1
  simp_rw [div_pow]
  rw [←Finset.sum_div,←hs,div_self (pow_ne_zero 2 hp),Real.sqrt_one]

def M : Matrix (Fin 12) (Fin 9) ℚ := !![
  1,0,0,1,0,0,0,0,0;
  1,0,1,0,0,0,0,0,0;
  1,1,0,0,0,0,0,0,0;
  0,1,1,0,1,0,0,0,0;
  0,1,1,2,0,0,0,0,0;
  0,1,0,0,1,0,0,0,0;
  0,1,0,0,1,0,0,0,0;
  0,0,1,1,0,0,0,0,0;
  0,1,0,0,0,0,0,0,1;
  0,0,0,0,0,1,1,1,0;
  0,0,0,0,0,0,1,1,1;
  0,0,0,0,0,0,0,1,1]

def Urow : Matrix (Fin 1) (Fin 2) ℚ := !![22/100,-11/100]
def sigma : Matrix (Fin 2) (Fin 2) ℚ := !![334/100,0;0,254/100]
def Vrows : Matrix (Fin 2) (Fin 2) ℚ := !![20/100,-6/100;61/100,17/100]

theorem reconstruction_entries : Urow*sigma*Vrows.transpose=!![163724/1000000,40073/100000] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Urow,sigma,Vrows,Matrix.mul_apply,Fin.sum_univ_succ]

def frobeniusSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i,∑ j,(A i j)^2

theorem reconstruction_error (A B : Matrix (Fin 12) (Fin 9) ℝ) :
    frobeniusSquared (A-B)=∑ i,∑ j,(A i j-B i j)^2 := rfl

noncomputable def alignmentObjective {n d : ℕ} (W₁ W₂ : Matrix (Fin n) (Fin d) ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ := Real.sqrt (frobeniusSquared (W₁*Q-W₂))
def isAlignmentMinimizer {n d : ℕ} (W₁ W₂ : Matrix (Fin n) (Fin d) ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Q.transpose*Q=1 ∧ ∀ P : Matrix (Fin d) (Fin d) ℝ,P.transpose*P=1 → alignmentObjective W₁ W₂ Q≤alignmentObjective W₁ W₂ P

def marine : Fin 6 → ℚ := ![40,821/10,853/10,448/10,32/10,33/10]
def teacher : Fin 6 → ℚ := ![52/10,7,93/10,47/10,484/10,536/10]
def unfoldColumn (j : Fin 2) (k : Fin 3) : Fin 6 := ⟨2*k.val+j.val,by omega⟩

theorem tensor_indices : unfoldColumn 1 1=3 ∧ unfoldColumn 1 2=5 ∧ marine (unfoldColumn 1 1)=448/10 ∧ teacher (unfoldColumn 1 2)=536/10 := by decide +kernel

theorem tensor_bijection : Function.Bijective (fun p : Fin 2×Fin 3 => unfoldColumn p.1 p.2) := by decide +kernel

def leftInverse : Matrix (Fin 9) (Fin 12) ℚ := !![1/2,1/4,1/4,0,-1/4,0,0,0,0,0,0,0;
-1/2,-1/4,3/4,0,1/4,0,0,0,0,0,0,0;
-1/2,3/4,-1/4,0,1/4,0,0,0,0,0,0,0;
1/2,-1/4,-1/4,0,1/4,0,0,0,0,0,0,0;
1,-1/2,-1/2,1,-1/2,0,0,0,0,0,0,0;
1/2,1/4,-3/4,0,-1/4,0,0,0,1,1,-1,0;
0,0,0,0,0,0,0,0,0,0,1,-1;
-1/2,-1/4,3/4,0,1/4,0,0,0,-1,0,0,1;
1/2,1/4,-3/4,0,-1/4,0,0,0,1,0,0,0]

theorem full_rank_certificate : leftInverse*M=1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [leftInverse,M,Matrix.mul_apply,Fin.sum_univ_succ]

theorem original_rank : M.rank=9 := by
  apply Nat.le_antisymm
  · simpa using Matrix.rank_le_card_width M
  · calc
      9 = Matrix.rank (1 : Matrix (Fin 9) (Fin 9) ℚ) := by simp
      _ = Matrix.rank (leftInverse*M) := by rw [full_rank_certificate]
      _ ≤ M.rank := Matrix.rank_mul_le_right _ _

def countries : Fin 4 → Fin 2 → ℚ :=
  ![![-677709/1000000,1874645/1000000],![-885794/1000000,1253283/1000000],![-1305110/1000000,-84347/1000000],![-1716295/1000000,-1397095/1000000]]
def capitals : Fin 4 → Fin 2 → ℚ :=
  ![![1119508/1000000,1726213/1000000],![1546941/1000000,902989/1000000],![1135124/1000000,-402403/1000000],![852681/1000000,-1576851/1000000]]
def differences (i:Fin 4) : Fin 2 → ℚ := capitals i-countries i

theorem projected_differences : differences=
  ![![1797217/1000000,-148432/1000000],![2432735/1000000,-350294/1000000],![2440234/1000000,-318056/1000000],![2568976/1000000,-179756/1000000]] := by
 ext i j
 fin_cases i <;> fin_cases j <;> norm_num [differences,capitals,countries]

theorem projected_arrow_endpoint (i:Fin 4) : countries i+differences i=capitals i := by
 unfold differences
 abel

theorem projected_common_direction : ∀ i,0<differences i 0 ∧ differences i 1<0 := by
 intro i
 fin_cases i <;> norm_num [projected_differences]

theorem projected_slopes_not_identical : differences 0 1/differences 0 0≠differences 1 1/differences 1 0 := by
 norm_num [projected_differences]

#print axioms projected_differences
#print axioms projected_arrow_endpoint
#print axioms projected_common_direction
#print axioms projected_slopes_not_identical

theorem two_step_entry_formula (i j:Fin 5) : (A^2) i j=∑ k,A i k*A k j := by simp [pow_two,Matrix.mul_apply]

theorem two_step_terms : (fun k:Fin 5=>A 1 k*A k 3)=![0,0,0,0,1] := by decide +kernel

def bagWords : Fin 5→String := !["John","threw","out","the","trash"]

theorem bag_counts :
 (fun i=>["John","threw","out","the","trash"].count (bagWords i))=![1,1,1,1,1] ∧
 (fun i=>["John","threw","the","trash","out"].count (bagWords i))=![1,1,1,1,1] := by decide +kernel

end Chapter04Expressions

#print axioms Chapter04Expressions.adjacency
#print axioms Chapter04Expressions.degree_vectors
#print axioms Chapter04Expressions.adjacency_entries
#print axioms Chapter04Expressions.two_steps
#print axioms Chapter04Expressions.no_three_steps
#print axioms Chapter04Expressions.graph_distance
#print axioms Chapter04Expressions.order_lengths
#print axioms Chapter04Expressions.permutationB
#print axioms Chapter04Expressions.polysemy
#print axioms Chapter04Expressions.dot_products
#print axioms Chapter04Expressions.squared_lengths
#print axioms Chapter04Expressions.cosine_square
#print axioms Chapter04Expressions.cosine_cherry_bounds
#print axioms Chapter04Expressions.cosine_digital_bounds
#print axioms Chapter04Expressions.length_positive
#print axioms Chapter04Expressions.unit_normalization
#print axioms Chapter04Expressions.reconstruction_entries
#print axioms Chapter04Expressions.reconstruction_error
#print axioms Chapter04Expressions.tensor_indices
#print axioms Chapter04Expressions.tensor_bijection
#print axioms Chapter04Expressions.full_rank_certificate
#print axioms Chapter04Expressions.original_rank
