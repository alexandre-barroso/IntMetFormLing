import Mathlib
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
open scoped BigOperators
namespace Chapter08Figures

lemma logEnclosure (x a b:ℝ) (n:ℕ) (hx:|x|<1)
 (ha:a<2*((∑ i ∈ Finset.range n,x^(2*i+1)/(2*i+1))-|x|^(2*n+1)/(1-x^2)))
 (hb:2*((∑ i ∈ Finset.range n,x^(2*i+1)/(2*i+1))+|x|^(2*n+1)/(1-x^2))<b) :
 a<Real.log ((1+x)/(1-x)) ∧ Real.log ((1+x)/(1-x))<b := by
 have h:=abs_le.mp (Real.sum_range_sub_log_div_le hx n)
 constructor <;> linarith [h.1,h.2]

theorem log2 : ((34657359027997/50000000000000):ℝ)<Real.log (2:ℝ) ∧ Real.log (2:ℝ)<((13862943611199/20000000000000):ℝ) := by
 have h:=logEnclosure ((1/3):ℝ) ((34657359027997/50000000000000):ℝ) ((13862943611199/20000000000000):ℝ) 15 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms log2

theorem log07 : ((-17833747196937/50000000000000):ℝ)<Real.log ((7/10):ℝ) ∧ Real.log ((7/10):ℝ)<((-35667494393873/100000000000000):ℝ) := by
 have h:=logEnclosure ((-3/17):ℝ) ((-17833747196937/50000000000000):ℝ) ((-35667494393873/100000000000000):ℝ) 10 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms log07

theorem log03 : ((-60198640216297/50000000000000):ℝ)<Real.log ((3/10):ℝ) ∧ Real.log ((3/10):ℝ)<((-120397280432593/100000000000000):ℝ) := by
 have h:=logEnclosure ((-7/13):ℝ) ((-60198640216297/50000000000000):ℝ) ((-120397280432593/100000000000000):ℝ) 28 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms log03

theorem expNegative0833 : ((54342887340451/125000000000000):ℝ)<Real.exp ((-833/1000):ℝ) ∧ Real.exp ((-833/1000):ℝ)<((434743098723609/1000000000000000):ℝ) := by
 have h := Real.exp_bound (x:=((-833/1000):ℝ)) (by norm_num) (n:=24) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
#print axioms expNegative0833

theorem expNegative07 : ((496585303791409/1000000000000000):ℝ)<Real.exp ((-7/10):ℝ) ∧ Real.exp ((-7/10):ℝ)<((49658530379141/100000000000000):ℝ) := by
 have h := Real.exp_bound (x:=((-7/10):ℝ)) (by norm_num) (n:=24) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
#print axioms expNegative07

theorem logStepLower : ((8063720977709/20000000000000):ℝ)<Real.log ((1496585303791409/1000000000000000):ℝ) ∧ Real.log ((1496585303791409/1000000000000000):ℝ)<((20159302444273/50000000000000):ℝ) := by
 have h:=logEnclosure ((496585303791409/2496585303791409):ℝ) ((8063720977709/20000000000000):ℝ) ((20159302444273/50000000000000):ℝ) 11 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms logStepLower

theorem logStepUpper : ((8063720977709/20000000000000):ℝ)<Real.log ((149658530379141/100000000000000):ℝ) ∧ Real.log ((149658530379141/100000000000000):ℝ)<((20159302444273/50000000000000):ℝ) := by
 have h:=logEnclosure ((49658530379141/249658530379141):ℝ) ((8063720977709/20000000000000):ℝ) ((20159302444273/50000000000000):ℝ) 11 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms logStepUpper


theorem loss_points : |(-Real.log (7/10:ℝ))-356674944/1000000000|<1/2000000000 ∧
    |(-Real.log (3/10:ℝ))-1203972804/1000000000|<1/2000000000 := by
 have h:=log07
 have g:=log03
 constructor <;> rw [abs_lt] <;> constructor <;> linarith

theorem loss_start_point : |Real.log 2-693147181/1000000000|<1/2000000000 := by
 have h:=log2
 rw [abs_lt]
 constructor <;> linarith

theorem sigmoid_point : |1/(1+Real.exp (-833/1000:ℝ))-6969888901/10000000000|<1/20000000000 := by
 have h:=expNegative0833
 have hn : 0<1+Real.exp (-833/1000:ℝ) := by positivity
 rw [abs_lt]
 constructor
 · have : (6969888901/10000000000-1/20000000000:ℝ)<1/(1+Real.exp (-833/1000:ℝ)) := by
     apply (lt_div_iff₀ hn).2
     linarith [h.2]
   linarith
 · have : 1/(1+Real.exp (-833/1000:ℝ))<(6969888901/10000000000+1/20000000000:ℝ) := by
     apply (div_lt_iff₀ hn).2
     linarith [h.1]
   linarith


theorem gradient_loss_point : |Real.log (1+Real.exp (7/10:ℝ))-7/10-403186049/1000000000|<1/2000000000 := by
 have h:=expNegative07
 have hl:=Real.strictMonoOn_log (by norm_num : (0:ℝ)<1+(496585303791409/1000000000000000))
    (by positivity : (0:ℝ)<1+Real.exp (-7/10:ℝ)) (by linarith : 1+(496585303791409/1000000000000000)<1+Real.exp (-7/10:ℝ))
 have hu:=Real.strictMonoOn_log (by positivity : (0:ℝ)<1+Real.exp (-7/10:ℝ))
    (by norm_num : (0:ℝ)<1+(49658530379141/100000000000000)) (by linarith : 1+Real.exp (-7/10:ℝ)<1+(49658530379141/100000000000000))
 have lower:=logStepLower
 have upper:=logStepUpper
 have hid : Real.log (1+Real.exp (7/10:ℝ))-7/10=Real.log (1+Real.exp (-7/10:ℝ)) := by
   have he : 1+Real.exp (7/10:ℝ)=(1+Real.exp (-7/10:ℝ))*Real.exp (7/10:ℝ) := by
     rw [add_mul,one_mul,←Real.exp_add]
     norm_num
     ring
   rw [he,Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
   ring
 rw [hid,abs_lt]
 constructor <;> linarith

#print axioms loss_points
#print axioms loss_start_point
#print axioms sigmoid_point
#print axioms gradient_loss_point
theorem relu_negative (z:ℝ) (hz:z≤0) : max 0 z=0 := max_eq_left hz

theorem relu_positive (z:ℝ) (hz:0≤z) : max 0 z=z := max_eq_right hz

theorem relu_graph_points : max (0:ℝ) (-12/10)=0 ∧ max (0:ℝ) 0=0 ∧ max (0:ℝ) 2=2 := by norm_num

theorem upper_constraint_arrow (w:ℝ) : (w+1+2/5)-(w-2/5)>1 := by linarith

theorem lower_constraint_arrow (w:ℝ) : (w+2/5)-(w-1-2/5)>1 := by linarith

#print axioms relu_negative
#print axioms relu_positive
#print axioms relu_graph_points
#print axioms upper_constraint_arrow
#print axioms lower_constraint_arrow

end Chapter08Figures
