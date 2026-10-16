import Mathlib
namespace Chapter08Review
theorem c08_e0112_integral (z:ℝ) : 0 < Real.exp (-z) := Real.exp_pos _
theorem c08_e0135_integral (a w:ℝ) : Real.exp (a+w)=Real.exp a*Real.exp w := Real.exp_add _ _
theorem c08_e0222_integral (p:ℝ) : p^(1:ℕ)*(1-p)^(0:ℕ)=p ∧ p^(0:ℕ)*(1-p)^(1:ℕ)=1-p := by simp
theorem c08_e0250_integral : (1:ℝ)/(1+Real.exp 0)=1/2 := by norm_num
theorem c08_e0253_integral (w x a:ℝ) : HasDerivAt (fun u:ℝ=>u*x+a) x w := by simpa using ((hasDerivAt_id w).mul_const x).add_const a
theorem c08_e0281_integral (w:ℝ) : (0<w → |w|=w) ∧ (w<0 → |w|= -w) := by constructor; exact fun h=>abs_of_pos h; exact fun h=>abs_of_neg h
theorem c08_e0324_integral (a b:ℝ) : (a-b≥1 ↔ b≤a-1) ∧ (b-a≥1 ↔ b≥a+1) := by constructor <;> constructor <;> intro h <;> linarith
theorem c08_e0326_integral (a b:ℝ) (h1:a-b≥1) (h2:b-a≥1) : (a-b)+(b-a)≥1+1 := by linarith
theorem c08_e0382_integral (p:ℝ) (hp:0<p) (h1:p<1) : p-1<0 ∧ p-0>0 := by constructor <;> linarith
theorem c08_e0496_integral : Real.sqrt 64=8 := by norm_num
theorem log_ratio_sign (p q:ℝ) (hp:0<p) (hq:0<q) : Real.log p-Real.log q<0 ↔ p<q := by rw [sub_neg,Real.log_lt_log_iff hp hq]
theorem odds_equivalence_steps (r p:ℝ) (hr:0<r) (hp:p≠1) :
 (r=p/(1-p) ↔ r*(1-p)=p) ∧ (r*(1-p)=p ↔ r-r*p=p) ∧
 (r-r*p=p ↔ r=p*(1+r)) ∧ (r=p*(1+r) ↔ p=r/(1+r)) := by
 have hd:1-p≠0:=sub_ne_zero.mpr (Ne.symm hp)
 have hd2:1+r≠0:=by positivity
 constructor
 · exact eq_div_iff hd
 constructor
 · constructor <;> intro h <;> nlinarith
 constructor
 · constructor <;> intro h <;> nlinarith
 · rw [eq_div_iff hd2]
   constructor <;> intro h <;> nlinarith
theorem sigmoid_logarithms (z:ℝ) :
 Real.log (Real.exp z/(1+Real.exp z))=z-Real.log (1+Real.exp z) ∧
 Real.log (1-Real.exp z/(1+Real.exp z))= -Real.log (1+Real.exp z) := by
 have he:Real.exp z≠0:=ne_of_gt (Real.exp_pos z)
 have hd:1+Real.exp z≠0:=by positivity
 constructor
 · rw [Real.log_div he hd,Real.log_exp]
 · have hc:1-Real.exp z/(1+Real.exp z)=1/(1+Real.exp z):=by field_simp; ring
   rw [hc,Real.log_div one_ne_zero hd,Real.log_one]
   ring
theorem harmonic_intermediate (p r:ℝ) (hp:0<p) (hr:0<r) :
 1/((1/p+1/r)/2)=2/(1/p+1/r) ∧ 2/(1/p+1/r)=2*p*r/(p+r) := by
 have h:p+r≠0:=ne_of_gt (add_pos hp hr)
 constructor <;> field_simp <;> ring
theorem sigmoid_text_roundings (p:ℝ) (h:|p-6969888901/10000000000|<1/20000000000) :
 |p-697/1000|<1/2000 ∧ |p-7/10|<1/200 ∧ |(697/1000:ℝ)-7/10|<1/200 := by
 rcases abs_lt.mp h with ⟨hl,hu⟩
 refine ⟨?_,?_,?_⟩
 · rw [abs_lt]; constructor <;> linarith
 · rw [abs_lt]; constructor <;> linarith
 · norm_num
theorem first_decimal_quotient (x s:ℝ) (hx:36441/20000<x ∧ x<36443/20000)
 (hs:664697/20000<s ∧ s<664699/20000) : |x/s-(18221/332349)|<1/20000 ∧ |((18221/332349):ℝ)-(548/10000)|<1/20000 := by
 have hs0:0<s:=by linarith [hs.1]
 constructor
 · rw [abs_lt]
   constructor
   · have hb:(18221/332349)-1/20000<x/s:=by
       apply (lt_div_iff₀ hs0).2
       linarith [hx.1,hs.2]
     linarith
   · have hb:x/s<(18221/332349)+1/20000:=by
       apply (div_lt_iff₀ hs0).2
       linarith [hx.2,hs.1]
     linarith
 · norm_num
theorem fifth_decimal_quotient (x s:ℝ) (hx:490649/20000<x ∧ x<490651/20000)
 (hs:664697/20000<s ∧ s<664699/20000) : |x/s-(245325/332349)|<1/20000 ∧ |((245325/332349):ℝ)-(7382/10000)|<1/20000 := by
 have hs0:0<s:=by linarith [hs.1]
 constructor
 · rw [abs_lt]
   constructor
   · have hb:(245325/332349)-1/20000<x/s:=by
       apply (lt_div_iff₀ hs0).2
       linarith [hx.1,hs.2]
     linarith
   · have hb:x/s<(245325/332349)+1/20000:=by
       apply (div_lt_iff₀ hs0).2
       linarith [hx.2,hs.1]
     linarith
 · norm_num
theorem sgns_arbitrary_coordinate {n:ℕ} (u v:Fin n→ℝ) (j:Fin n) (y:ℝ) :
 HasDerivAt
 (fun t:ℝ=>Real.log (1+Real.exp (∑ i,(u i+if i=j then t else 0)*v i))-y*(∑ i,(u i+if i=j then t else 0)*v i))
 ((Real.exp (∑ i,u i*v i)/(1+Real.exp (∑ i,u i*v i))-y)*v j) 0 := by
 have hc (t:ℝ) : (∑ i,(u i+if i=j then t else 0)*v i)=(∑ i,u i*v i)+t*v j := by
   simp [add_mul,Finset.sum_add_distrib,ite_mul]
 simp_rw [hc]
 have hl (z:ℝ) : HasDerivAt (fun t:ℝ=>Real.log (1+Real.exp t)-y*t) (Real.exp z/(1+Real.exp z)-y) z := by
   have hn:1+Real.exp z≠0:=by positivity
   exact ((((Real.hasDerivAt_exp z).const_add 1).log hn).sub ((hasDerivAt_id z).const_mul y)).congr_deriv (by ring)
 simpa only [Function.comp_def,id_eq,one_mul,zero_mul,add_zero] using
   (hl ((∑ i,u i*v i)+0*v j)).comp 0 (((hasDerivAt_id 0).mul_const (v j)).const_add (∑ i,u i*v i))
theorem labeled_tableau_winners :
 let rows1:List (String×(ℚ×ℚ)) := [("ban.tan",(-2,0)),("ba.tan",(-1,-1))]
 let rows2:List (String×(ℚ×ℚ)) := [("ban",(-1,0)),("ba",(0,-1))]
 let scores1 := rows1.map (fun row=>(row.1,2*row.2.1+row.2.2))
 let scores2 := rows2.map (fun row=>(row.1,row.2.1+2*row.2.2))
 scores1=[("ban.tan",-4),("ba.tan",-3)] ∧ scores2=[("ban",-1),("ba",-2)] ∧
 ((scores1.filter (fun row=>scores1.all (fun other=>decide (other.2≤row.2)))).map Prod.fst)=["ba.tan"] ∧
 ((scores2.filter (fun row=>scores2.all (fun other=>decide (other.2≤row.2)))).map Prod.fst)=["ban"] := by decide +kernel
def reviewTransitions (q:ℕ) (c:Char) : List (ℕ×Char) :=
 if q=0 ∨ q=1 then if c='d' then [(1,'d'),(2,'t')] else if c='t' ∨ c='a' then [(0,c)] else [] else []
def reviewTraces : ℕ → List Char → List (List ℕ × List Char)
 | q,[] => [([q],[])]
 | q,c::cs => (reviewTransitions q c).flatMap (fun qo => (reviewTraces qo.1 cs).map (fun su => (q::su.1,qo.2::su.2)))
def acceptedReviewTraces (s:String) := (reviewTraces 0 s.toList).filter (fun p => p.1.getLast! = 0 ∨ p.1.getLast! = 2)
theorem published_transduction_traces : acceptedReviewTraces "tad" = [([0,0,0,2],"tat".toList)] ∧
 acceptedReviewTraces "tada" = [([0,0,0,1,0],"tada".toList)] := by decide +kernel
theorem edit_table_minimum_steps :
 min (min (1+1:ℕ) (1+1)) (0+2) = min (min 2 2) 2 ∧
 min (min (2:ℕ) 2) 2 = 2 ∧ min (min (4+1:ℕ) (4+1)) (3+0)=3 := by norm_num
def bigramProduct (q:String→String→ℝ) : String → List String → ℝ
 | _,[] => 1
 | previous,next::rest => q previous next * bigramProduct q next rest
theorem bigram_boundary_expansion (q:String→String→ℝ) :
 bigramProduct q "<s>" ["i","want","english","food","</s>"] =
 q "<s>" "i" * q "i" "want" * q "want" "english" * q "english" "food" * q "food" "</s>" := by
 simp [bigramProduct]
 ring
theorem relu_hidden_coordinate {d h:ℕ} (x:Fin d→ℝ) (W:Matrix (Fin d) (Fin h) ℝ) (b:Fin h→ℝ) (j:Fin h) :
 max 0 ((Matrix.vecMul x W+b) j)=max 0 ((∑ r,x r*W r j)+b j) := rfl
end Chapter08Review
