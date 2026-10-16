import Mathlib
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
open Polynomial
namespace Chapter04SpectralRoots

noncomputable def p : Polynomial ℝ := X^9-31*X^8+374*X^7-2286*X^6+7697*X^5-14557*X^4+15014*X^3-7755*X^2+1732*X-124
noncomputable def published : Fin 9 → ℝ := ![334/100,254/100,235/100,164/100,150/100,131/100,85/100,56/100,36/100]
noncomputable def lower (i:Fin 9) : ℝ := (published i-1/200)^2
noncomputable def upper (i:Fin 9) : ℝ := (published i+1/200)^2

theorem polynomial_degree : p.natDegree=9 := by unfold p; compute_degree!

theorem polynomial_ne_zero : p≠0 := by
 intro h
 have hd:=polynomial_degree
 rw [h] at hd
 norm_num at hd

theorem intervals_ordered : ∀ i,0<lower i ∧ lower i<upper i ∧ 0<published i-1/200 := by
 intro i
 fin_cases i <;> norm_num [lower,upper,published]

theorem sign_changes : ∀ i,p.eval (lower i)*p.eval (upper i)<0 := by
 intro i
 fin_cases i <;> norm_num [p,lower,upper,published]

theorem interval_root (i:Fin 9) : ∃ x∈Set.Ioo (lower i) (upper i),p.eval x=0 := by
 have hb:=(intervals_ordered i).2.1
 have hs:=sign_changes i
 have hleft : p.eval (lower i)≠0 := by intro h;rw [h,zero_mul] at hs;exact (lt_irrefl 0) hs
 have hright : p.eval (upper i)≠0 := by intro h;rw [h,mul_zero] at hs;exact (lt_irrefl 0) hs
 have hc:ContinuousOn (fun x:ℝ=>p.eval x) (Set.Icc (lower i) (upper i)) := p.continuous.continuousOn
 have he : ∃ x∈Set.Icc (lower i) (upper i),p.eval x=0 := by
   by_cases h:p.eval (lower i)<0
   · have hu:0<p.eval (upper i) := by nlinarith
     exact intermediate_value_Icc hb.le hc ⟨h.le,hu.le⟩
   · have hl:0<p.eval (lower i) := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hleft)
     have hu:p.eval (upper i)<0 := by nlinarith
     exact intermediate_value_Icc' hb.le hc ⟨hu.le,hl.le⟩
 obtain ⟨x,hx,hzero⟩:=he
 refine ⟨x,⟨lt_of_le_of_ne hx.1 ?_,lt_of_le_of_ne hx.2 ?_⟩,hzero⟩
 · intro heq
   exact hleft (heq ▸ hzero)
 · intro heq
   exact hright (heq ▸ hzero)

noncomputable def root (i:Fin 9) : ℝ := Classical.choose (interval_root i)

theorem root_spec (i:Fin 9) : root i∈Set.Ioo (lower i) (upper i) ∧ p.eval (root i)=0 := Classical.choose_spec (interval_root i)

theorem separate_intervals (i j:Fin 9) (h:i≠j) : upper i<lower j ∨ upper j<lower i := by
 fin_cases i <;> fin_cases j <;> norm_num [lower,upper,published] at *

theorem root_injective : Function.Injective root := by
 intro i j heq
 by_contra h
 have hi:=(root_spec i).1
 have hj:=(root_spec j).1
 rcases separate_intervals i j h with hs | hs <;> rw [heq] at hi <;> linarith [hi.1,hi.2,hj.1,hj.2]

noncomputable def allRoots : Finset ℝ := Finset.univ.image root

theorem root_cardinality : allRoots.card=9 := by
 classical
 rw [allRoots,Finset.card_image_of_injective _ root_injective]
 simp

theorem all_roots : p.roots=allRoots.val := by
 classical
 apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
 · intro x hx
   obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
   exact (root_spec i).2
 · rw [polynomial_degree,root_cardinality]
 · exact polynomial_ne_zero

theorem rounded_sqrt_root (i:Fin 9) : |Real.sqrt (root i)-published i|<1/200 := by
 have hr:=(root_spec i).1
 have hb:=intervals_ordered i
 have hp:0<root i := lt_trans hb.1 hr.1
 have hs:=Real.sq_sqrt hp.le
 have hn:=Real.sqrt_nonneg (root i)
 unfold lower upper at hr
 rw [abs_lt]
 constructor <;> nlinarith [hr.1,hr.2,hb.2.2]

theorem all_positive_spectral_roots (s:ℝ) (hs : 0 ≤ s) (he:p.eval (s^2)=0) : ∃ i,|s-published i|<1/200 := by
 classical
 have hm : s^2∈p.roots := (p.mem_roots polynomial_ne_zero).mpr he
 rw [all_roots] at hm
 change s^2 ∈ allRoots at hm
 unfold allRoots at hm
 obtain ⟨i,hi,hri⟩:=Finset.mem_image.mp hm
 refine ⟨i,?_⟩
 have h:=rounded_sqrt_root i
 rw [hri,Real.sqrt_sq hs] at h
 exact h

#print axioms polynomial_degree
#print axioms polynomial_ne_zero
#print axioms intervals_ordered
#print axioms sign_changes
#print axioms interval_root
#print axioms root_spec
#print axioms separate_intervals
#print axioms root_injective
#print axioms root_cardinality
#print axioms all_roots
#print axioms rounded_sqrt_root
#print axioms all_positive_spectral_roots
def IsSingularValue (M:Matrix (Fin 12) (Fin 9) ℝ) (s:ℝ) : Prop :=
  0 ≤ s ∧ (Matrix.scalar (Fin 9) (s^2)-M.transpose*M).det=0

theorem singular_value_certificate (M:Matrix (Fin 12) (Fin 9) ℝ)
    (hchar:(M.transpose*M).charpoly=p) (s:ℝ) (hs:IsSingularValue M s) :
    ∃ i,|s-published i|<1/200 := by
  apply all_positive_spectral_roots s hs.1
  rw [←hchar,Matrix.eval_charpoly]
  exact hs.2

#print axioms singular_value_certificate

end Chapter04SpectralRoots
