import Mathlib

open scoped BigOperators

namespace Chapter06Review

theorem posterior_from_product (posterior evidence likelihood prior:ℝ) (he:0<evidence)
    (h:posterior*evidence=likelihood*prior) : posterior=likelihood*prior/evidence := by
 exact (eq_div_iff (ne_of_gt he)).2 h

theorem posterior_normalization_chain (q1 q2:ℝ) (h:q1/2+q2/3≠0) :
 (q1/2)/(q1/2+q2/3)+(q2/3)/(q1/2+q2/3)=(q1/2+q2/3)/(q1/2+q2/3) ∧
 (q1/2+q2/3)/(q1/2+q2/3)=1 := by
 constructor
 · rw [add_div]
 · exact div_self h

def rsaMembership : Matrix (Fin 3) (Fin 4) ℚ := !![1,1,0,0;1,0,1,0;0,1,0,1]
def rsaExtension (j:Fin 4):ℚ := ∑ i,rsaMembership i j
def rsaWeight (i:Fin 3) (j:Fin 4):ℚ := rsaMembership i j/rsaExtension j
def rsaSpeaker (i:Fin 3) (j:Fin 4):ℚ := rsaWeight i j/(∑ k,rsaWeight i k)

theorem rsa_extension_weights : rsaExtension=![2,2,1,1] ∧
 rsaWeight=!![1/2,1/2,0,0;1/2,0,1,0;0,1/2,0,1] := by decide +kernel

theorem rsa_speaker_blue : (fun i=>rsaSpeaker i 0)=![1/2,1/3,0] := by decide +kernel

theorem rsa_speaker_circle_chain :
 ((1/2:ℚ)/(1/2+1))=(1/2)/(3/2) ∧ (1/2:ℚ)/(3/2)=(1/2)*(2/3) ∧
 (1/2:ℚ)*(2/3)=1/3 ∧ (1:ℚ)/(3/2)=2/3 := by norm_num

theorem binomial_factorial {n k:ℕ} (h:k≤n) : n.choose k=n.factorial/(k.factorial*(n-k).factorial) := Nat.choose_eq_factorial_div_factorial h

theorem bernoulli_mean (p:ℝ) : 1*p+0*(1-p)=p := by ring

theorem bernoulli_variance_chain (p:ℝ) :
 p*(1-p)^2+(1-p)*(0-p)^2=p*(1-2*p+p^2)+(1-p)*p^2 ∧
 p*(1-2*p+p^2)+(1-p)*p^2=p-2*p^2+p^3+p^2-p^3 ∧
 p-2*p^2+p^3+p^2-p^3=p-p^2 ∧ p-p^2=p*(1-p) := by and_intros <;> ring

theorem binomial_source_zero :
 Nat.choose 100 0=1 ∧ (1/1000:ℚ)^0=1 ∧
 (Nat.choose 100 0:ℚ)*(1/1000)^0*(1-1/1000)^100=(999/1000)^100 := by norm_num

theorem log_two : Real.logb 2 2=1 := Real.logb_self_eq_one (by norm_num)
theorem log_four : Real.logb 2 4=2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.logb_pow,log_two];norm_num
theorem log_eight : Real.logb 2 8=3 := by rw [show (8:ℝ)=2^3 by norm_num,Real.logb_pow,log_two];norm_num

theorem log2_greek_reductions :
 Real.logb 2 (3/8)=Real.logb 2 3-3 ∧
 Real.logb 2 (2/8)=Real.logb 2 (1/4) ∧ Real.logb 2 (1/4)=-2 ∧
 Real.logb 2 (1/8)=-3 ∧ Real.logb 2 (2/3)=1-Real.logb 2 3 ∧
 Real.logb 2 (1/3)=-Real.logb 2 3 := by
 norm_num [Real.logb_div,log_two,log_four,log_eight]

theorem group_entropy_chain :
 -(2/3:ℝ)*Real.logb 2 (2/3)-(1/3)*Real.logb 2 (1/3)=
 -(2/3)*(1-Real.logb 2 3)-(1/3)*(-Real.logb 2 3) ∧
 -(2/3:ℝ)*(1-Real.logb 2 3)-(1/3)*(-Real.logb 2 3)=
 -2/3+(2/3)*Real.logb 2 3+(1/3)*Real.logb 2 3 ∧
 (-2/3:ℝ)+(2/3)*Real.logb 2 3+(1/3)*Real.logb 2 3=Real.logb 2 3-2/3 := by
 constructor
 · rw [log2_greek_reductions.2.2.2.2.1,log2_greek_reductions.2.2.2.2.2]
 · constructor <;> ring

theorem surprise_product_chain :
 -Real.logb 2 ((2/8)*(1/2))=-Real.logb 2 (2/8)-Real.logb 2 (1/2) ∧
 -Real.logb 2 (2/8)-Real.logb 2 (1/2)=-Real.logb 2 (1/4)-Real.logb 2 (1/2) ∧
 -Real.logb 2 (1/4)-Real.logb 2 (1/2)=2+1 ∧ (2:ℝ)+1=3 := by
 norm_num [Real.logb_div,log_two,log_four,log_eight]

theorem surprise_graph_points :
 (1/8:ℚ)=125/1000 ∧ (1/2:ℚ)=5/10 ∧
 -Real.logb 2 (125/1000)=3 ∧ -Real.logb 2 (5/10)=1 ∧ -Real.logb 2 1=0 := by
 norm_num [show (125/1000:ℝ)=1/8 by norm_num,show (5/10:ℝ)=1/2 by norm_num,Real.logb_div,log_two,log_eight]

theorem lognormal_source_model (t:ℝ) :
 1/((59/100)*t*Real.sqrt (2*Real.pi))*Real.exp (-((Real.log t-(-268/100))^2)/(2*(59/100)^2))=
 Real.exp (-((Real.log t+268/100)^2)/(2*(59/100)^2))/(t*(59/100)*Real.sqrt (2*Real.pi)) ∧
 Real.log t-(-268/100)=Real.log t+268/100 := by
 have he : Real.exp (-((Real.log t-(-268/100))^2)/(2*(59/100)^2))=
     Real.exp (-((Real.log t+268/100)^2)/(2*(59/100)^2)) := by congr 1;ring
 constructor
 · rw [he]
   ring
 · ring

theorem lognormal_source_domain : (0:ℚ)<59/100 ∧ (0:ℚ)<2/1000 ∧ (2:ℚ)/1000<3/100 ∧ (3:ℚ)/100<14/100 ∧ (14:ℚ)/100<8/10 := by norm_num

def kappaTable : Matrix (Fin 2) (Fin 2) ℚ := !![20,20;10,50]

theorem kappa_margins : (fun i=>∑ j,kappaTable i j)=![40,60] ∧
 (fun j=>∑ i,kappaTable i j)=![30,70] ∧ (∑ i,∑ j,kappaTable i j)=100 := by decide +kernel

theorem unequal_conditional_masses : (2/3:ℚ)≠1/2 ∧ (1/3:ℚ)≠1/2 := by norm_num

theorem surprisal_change_base (p:ℝ) : -Real.logb 2 p= -Real.log p/Real.log 2 := by rw [Real.logb];ring

theorem surprise_eighth_chain : (2:ℝ)^(-3:ℤ)=1/8 ∧ Real.logb 2 (1/8)=-3 ∧ -Real.logb 2 (1/8)= -(-3) ∧ (-(-3):ℝ)=3 := by
 norm_num [Real.logb_div,log_eight]

theorem bernoulli_sum_means (n:ℕ) (p:ℝ) : (∑ i:Fin n,p)=(n:ℝ)*p := by simp

theorem posterior_joint_weight_chain (joint evidence prior:ℝ) (he:0<evidence) (hp:0<prior) :
 (joint/evidence)*evidence=joint ∧ joint=(joint/prior)*prior ∧
 (joint/evidence)*evidence=(joint/prior)*prior ∧
 joint/evidence=(joint/prior)*prior/evidence := by
 and_intros <;> field_simp [ne_of_gt he,ne_of_gt hp]

theorem binomial_one_factorial_chain :
 (Nat.choose 100 1:ℚ)=(Nat.factorial 100:ℚ)/((Nat.factorial 1:ℚ)*(Nat.factorial 99:ℚ)) ∧
 (Nat.factorial 100:ℚ)/((Nat.factorial 1:ℚ)*(Nat.factorial 99:ℚ))=
    (100*(Nat.factorial 99:ℚ))/(Nat.factorial 99:ℚ) ∧
 (100*(Nat.factorial 99:ℚ))/(Nat.factorial 99:ℚ)=100 := by norm_num

theorem surprise_product_full_chain (a b:ℝ) (ha:0<a) (hb:0<b) :
 -Real.logb 2 (a*b)= -(Real.logb 2 a+Real.logb 2 b) ∧
 -(Real.logb 2 a+Real.logb 2 b)= -Real.logb 2 a-Real.logb 2 b := by
 rw [Real.logb_mul (ne_of_gt ha) (ne_of_gt hb)]
 constructor <;> ring

theorem pmi_frequency_full_chain (fxy fx fy n:ℝ) (hz:0<fxy) (hx:0<fx) (hy:0<fy) (hn:0<n) :
 0<(fxy/n)/((fx/n)*(fy/n)) ∧ 0<(fxy/n)*(n^2/(fx*fy)) ∧
 0<fxy*n/(fx*fy) ∧
 Real.logb 2 ((fxy/n)/((fx/n)*(fy/n)))=Real.logb 2 ((fxy/n)*(n^2/(fx*fy))) ∧
 Real.logb 2 ((fxy/n)*(n^2/(fx*fy)))=Real.logb 2 (fxy*n/(fx*fy)) := by
 refine ⟨div_pos (div_pos hz hn) (mul_pos (div_pos hx hn) (div_pos hy hn)),
   mul_pos (div_pos hz hn) (div_pos (sq_pos_of_pos hn) (mul_pos hx hy)),
   div_pos (mul_pos hz hn) (mul_pos hx hy),?_,?_⟩
 · congr 1
   field_simp [ne_of_gt hx,ne_of_gt hy,ne_of_gt hn]
   <;> ring
 · congr 1
   field_simp [ne_of_gt hx,ne_of_gt hy,ne_of_gt hn]
   <;> ring

noncomputable def jointInformationTerm (p q w:ℝ) : ℝ :=
 if p*q=0 then 0 else p*q*Real.logb 2 ((p*q)/(p*w))

noncomputable def conditionalInformationTerm (p q w:ℝ) : ℝ :=
 if p*q=0 then 0 else p*q*Real.logb 2 (q/w)

theorem weighted_information_term (p q w:ℝ) :
 jointInformationTerm p q w=conditionalInformationTerm p q w := by
 by_cases hz:p*q=0
 · simp [jointInformationTerm,conditionalInformationTerm,hz]
 · have hp:p≠0 := by intro h;apply hz;rw [h];ring
   simp only [jointInformationTerm,conditionalInformationTerm,if_neg hz]
   rw [mul_div_mul_left q w hp]

theorem weighted_information_sum {m n:ℕ} (p:Fin m→ℝ)
    (q:Matrix (Fin m) (Fin n) ℝ) (w:Fin n→ℝ) :
 (∑ i,∑ j,jointInformationTerm (p i) (q i j) (w j))=
 ∑ i,∑ j,conditionalInformationTerm (p i) (q i j) (w j) := by
 simp_rw [weighted_information_term]

def bernoulliPatternWeight (p:ℝ) (xs:List Bool) : ℝ :=
 (xs.map (fun b=>if b then p else 1-p)).prod

theorem bernoulli_pattern_product (p:ℝ) (xs:List Bool) :
 bernoulliPatternWeight p xs=p^(xs.count true)*(1-p)^(xs.count false) := by
 induction xs with
 | nil => simp [bernoulliPatternWeight]
 | cons b xs ih =>
   cases b <;> simp [bernoulliPatternWeight,List.count_cons,pow_succ] at * <;> rw [ih] <;> ring

theorem binary_count_sum (xs:List Bool) : xs.count true+xs.count false=xs.length := by
 induction xs with
 | nil => simp
 | cons b xs ih =>
   cases b
   · rw [List.count_cons_of_ne (by decide),List.count_cons_self,List.length_cons]
     omega
   · rw [List.count_cons_self,List.count_cons_of_ne (by decide),List.length_cons]
     omega

theorem bernoulli_pattern_n_minus_k (p:ℝ) (xs:List Bool) :
 bernoulliPatternWeight p xs=p^(xs.count true)*(1-p)^(xs.length-xs.count true) := by
 have hf:xs.count false=xs.length-xs.count true := by have h:=binary_count_sum xs;omega
 simpa [hf] using bernoulli_pattern_product p xs

end Chapter06Review
