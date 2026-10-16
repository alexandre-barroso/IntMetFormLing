import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter06

namespace c06_r01
theorem arithmetic_001 : ((1/8+2/8+1/8+3/8+1/8) : ℚ) = (1) := by norm_num
theorem greekCounts : (["us","es","es","is","a","a","i","a"]:List String).count "es"=2 ∧ (["us","es","es","is","a","a","i","a"]:List String).count "a"=3 := by decide +kernel
end c06_r01

namespace c06_r02
theorem arithmetic_001 : (((1/8)/(2/8)) : ℚ) = (1/2) := by norm_num
theorem arithmetic_002 : (((1/8)/(1/8)) : ℚ) = (1) := by norm_num
theorem arithmetic_003 : (((2/8)/(3/8)) : ℚ) = (2/3) := by norm_num
theorem arithmetic_004 : (((1/8)/(3/8)) : ℚ) = (1/3) := by norm_num
theorem arithmetic_005 : ((2/3+1/3) : ℚ) = (1) := by norm_num
end c06_r02

namespace c06_r03
theorem bayesRatio (a b c:ℝ) (hb:b≠0) (hc:c≠0) : (a/b)*b/c=a/c := by field_simp
theorem normalizeFinite {ι:Type*} (s:Finset ι) (w:ι→ℝ) (h:(∑ i∈s,w i)≠0) : (∑ i∈s,w i/(∑ j∈s,w j))=1 := by rw [←Finset.sum_div]; exact div_self h
theorem posteriorFromProduct (posterior evidence likelihood prior:ℝ)
 (he:evidence≠0) (h:posterior*evidence=likelihood*prior) :
 posterior=likelihood*prior/evidence := (eq_div_iff he).mpr h
end c06_r03

namespace c06_r04
theorem arithmetic_001 : (((2/8)*(1/2)) : ℚ) = (1/8) := by norm_num
theorem arithmetic_002 : (((2/8)*(1/8)) : ℚ) = (1/32) := by norm_num
theorem arithmetic_003 : ((1/8) : ℚ) ≠ (1/32) := by norm_num
theorem productRule (a b:ℝ) (hb:b≠0) : b*(a/b)=a := by field_simp
end c06_r04

namespace c06_r05
theorem arithmetic_001 : (((1/10)/100) : ℚ) = (1/1000) := by norm_num
theorem arithmetic_002 : ((1-1/1000) : ℚ) = (999/1000) := by norm_num
theorem arithmetic_003 : ((100*(1/1000)) : ℚ) = (1/10) := by norm_num
theorem arithmetic_004 : ((945/10000) : ℚ) < (1-(999/1000)^100) := by norm_num
theorem arithmetic_005 : ((1-(999/1000)^100) : ℚ) < (955/10000) := by norm_num
theorem arithmetic_006 : ((22/10000) : ℚ) < (1-(999/1000)^100) := by norm_num
theorem binomialNormalization (n:ℕ) (p:ℝ) : (∑ k ∈ Finset.range (n+1), p^k*(1-p)^(n-k)*(n.choose k:ℝ))=1 := by
 have h:=add_pow p (1-p) n
 have hp:p+(1-p)=1 := by ring
 rw [hp,one_pow] at h
 exact h.symm
theorem zeroCount (p:ℝ) : (Nat.choose 100 0:ℝ)*p^0*(1-p)^(100-0)=(1-p)^100 := by norm_num
theorem chooseOne : Nat.choose 100 1=100 := by norm_num
theorem factorialCancellation :
 (Nat.factorial 100:ℚ)/((Nat.factorial 1:ℚ)*(Nat.factorial 99:ℚ))=100 := by norm_num
theorem oneCount : (Nat.choose 100 1:ℚ)*(1/1000)^1*(1-1/1000)^(100-1)=
 (1/10)*(999/1000)^99 := by norm_num
end c06_r05

namespace c06_r06
theorem arithmetic_001 : ((100*(1/1000)) : ℚ) = (1/10) := by norm_num
theorem arithmetic_002 : (((1/10)*(1-1/1000)) : ℚ) = (999/10000) := by norm_num
theorem bernoulliMean (p:ℝ) : 1*p+0*(1-p)=p := by ring
theorem bernoulliVariance (p:ℝ) : p*(1-p)^2+(1-p)*(0-p)^2=p-p^2 ∧ p-p^2=p*(1-p) := by constructor <;> ring
theorem sumMeans (n:ℕ) (p:ℝ) : (∑ i:Fin n,p)=(n:ℝ)*p := by simp
theorem sumVariances (n:ℕ) (p:ℝ) : (∑ i:Fin n,p*(1-p))=(n:ℝ)*p*(1-p) := by simp [mul_assoc]
open MeasureTheory in
theorem independentVariance {Ω ι:Type*} [MeasurableSpace Ω] (μ:Measure Ω) (s:Finset ι) (X:ι→Ω→ℝ)
 (hm:∀ i∈s,MemLp (X i) 2 μ) (hi:Set.Pairwise (s:Set ι) fun i j=>ProbabilityTheory.IndepFun (X i) (X j) μ) :
 ProbabilityTheory.variance (∑ i∈s,X i) μ=∑ i∈s,ProbabilityTheory.variance (X i) μ := ProbabilityTheory.IndepFun.variance_sum hm hi
end c06_r06

namespace c06_r07
theorem logTwo : Real.logb 2 2=1 := Real.logb_self_eq_one (by norm_num)
theorem logFour : Real.logb 2 4=2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.logb_pow,logTwo]; norm_num
theorem logEight : Real.logb 2 8=3 := by rw [show (8:ℝ)=2^3 by norm_num,Real.logb_pow,logTwo]; norm_num
theorem basicSurprise : -Real.logb 2 1=0 ∧ -Real.logb 2 (1/2)=1 ∧ -Real.logb 2 (1/4)=2 ∧ -Real.logb 2 (1/8)=3 := by
 simp only [Real.logb_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0),Real.logb_div (by norm_num : (1:ℝ)≠0) (by norm_num : (4:ℝ)≠0),Real.logb_div (by norm_num : (1:ℝ)≠0) (by norm_num : (8:ℝ)≠0),Real.logb_one,logTwo,logFour,logEight]
 norm_num
theorem powBounds (x:ℝ) (hx:0<x) (n l u:ℕ) (hn:0<n)
 (hlo:(2:ℝ)^l<x^n) (hhi:x^n<(2:ℝ)^u): (l:ℝ)/n<Real.logb 2 x ∧ Real.logb 2 x<(u:ℝ)/n := by
 have hl:=Real.logb_lt_logb (b:=2) (by norm_num) (by positivity) hlo
 have hu:=Real.logb_lt_logb (b:=2) (by norm_num) (by positivity) hhi
 rw [Real.logb_pow,Real.logb_pow,logTwo,mul_one] at hl hu
 constructor
 · apply (div_lt_iff₀ (show (0:ℝ)<n by exact_mod_cast hn)).2; nlinarith
 · apply (lt_div_iff₀ (show (0:ℝ)<n by exact_mod_cast hn)).2; nlinarith
theorem threeBounds : (3169/2000:ℝ)<Real.logb 2 3 ∧ Real.logb 2 3<3170/2000 := by
 exact powBounds 3 (by norm_num) 2000 3169 3170 (by norm_num) (by exact_mod_cast (show (2:ℕ)^3169<3^2000 by decide +kernel)) (by exact_mod_cast (show (3:ℕ)^2000<2^3170 by decide +kernel))
end c06_r07

namespace c06_r08
theorem arithmetic_001 : (((2/8)*(1/2)) : ℚ) = (1/8) := by norm_num
theorem arithmetic_002 : ((2+1) : ℚ) = (3) := by norm_num
theorem surpriseProduct (a b:ℝ) (ha:0<a) (hb:0<b) : -Real.logb 2 (a*b)= -Real.logb 2 a-Real.logb 2 b := by rw [Real.logb_mul (ne_of_gt ha) (ne_of_gt hb)]; ring
theorem contextualMeanSign {ι:Type*} (S:Finset ι) (w f:ι→ℝ) :
 (∑ i∈S,w i*(-f i))= -(∑ i∈S,w i*f i) := by simp [mul_neg,Finset.sum_neg_distrib]
theorem tokenMean {n:ℕ} (f:Fin n→ℝ) :
 (∑ i,-f i)/(n:ℝ)=(-1/(n:ℝ))*(∑ i,f i) := by rw [Finset.sum_neg_distrib]; ring
end c06_r08

namespace c06_r09
theorem arithmetic_001 : ((8*(1/8)*3) : ℚ) = (3) := by norm_num
theorem arithmetic_002 : ((1*0) : ℚ) = (0) := by norm_num
theorem classEntropy : 8*(1/8:ℝ)*(-Real.logb 2 (1/8))=3 := by rw [c06_r07.basicSurprise.2.2.2]; norm_num
theorem constantEntropy : (1:ℝ)*(-Real.logb 2 1)=0 := by simp
end c06_r09

namespace c06_r10
theorem arithmetic_001 : (((1/2)/(1/2+1)) : ℚ) = (1/3) := by norm_num
theorem arithmetic_002 : ((1/(1/2+1)) : ℚ) = (2/3) := by norm_num
theorem arithmetic_003 : (((1/2)/(1/2+1/2)) : ℚ) = (1/2) := by norm_num
theorem arithmetic_004 : ((1/3+2/3) : ℚ) = (1) := by norm_num
theorem arithmetic_005 : ((1/2+1/2) : ℚ) = (1) := by norm_num
end c06_r10

namespace c06_d01
theorem arithmetic_001 : (((1/2)/(1/2+1)) : ℚ) = (1/3) := by norm_num
theorem arithmetic_002 : ((1/(1/2+1)) : ℚ) = (2/3) := by norm_num
theorem arithmetic_003 : (((1/2)/(1/2+1/2)) : ℚ) = (1/2) := by norm_num
theorem arithmetic_004 : ((1/3+2/3) : ℚ) = (1) := by norm_num
theorem arithmetic_005 : ((1/2+1/2) : ℚ) = (1) := by norm_num
theorem posteriorSum (q1 q2:ℝ) (h:q1/2+q2/3≠0) : (q1/2)/(q1/2+q2/3)+(q2/3)/(q1/2+q2/3)=1 := by rw [←add_div]; exact div_self h
end c06_d01

namespace c06_d02
theorem arithmetic_001 : ((20+20) : ℚ) = (40) := by norm_num
theorem arithmetic_002 : ((10+50) : ℚ) = (60) := by norm_num
theorem arithmetic_003 : ((20+10) : ℚ) = (30) := by norm_num
theorem arithmetic_004 : ((20+50) : ℚ) = (70) := by norm_num
theorem arithmetic_005 : (((20+50)/100) : ℚ) = (7/10) := by norm_num
theorem arithmetic_006 : (((30/100)*(40/100)) : ℚ) = (12/100) := by norm_num
theorem arithmetic_007 : (((70/100)*(60/100)) : ℚ) = (42/100) := by norm_num
theorem arithmetic_008 : ((12/100+42/100) : ℚ) = (54/100) := by norm_num
theorem arithmetic_009 : (((70/100-54/100)/(1-54/100)) : ℚ) = (8/23) := by norm_num
theorem arithmetic_010 : ((16/46) : ℚ) = (8/23) := by norm_num
theorem arithmetic_011 : ((3475/10000) : ℚ) < (8/23) := by norm_num
theorem arithmetic_012 : ((8/23) : ℚ) < (3485/10000) := by norm_num
end c06_d02

namespace c06_d03
theorem arithmetic_001 : ((30*15000000) : ℚ) = (450000000) := by norm_num
theorem arithmetic_002 : ((1105*241) : ℚ) = (266305) := by norm_num
theorem arithmetic_003 : ((6*15000000) : ℚ) = (90000000) := by norm_num
theorem arithmetic_004 : ((30/6) : ℚ) = (5) := by norm_num
theorem ratio (a b c N:ℝ) (hN:N≠0) : (a/N)/((b/N)*(c/N))=a*N/(b*c) := by field_simp <;> ring
theorem forwardRound : (1065/100:ℝ)<Real.logb 2 (450000000/266305) ∧ Real.logb 2 (450000000/266305)<1075/100 := by
 convert c06_r07.powBounds (450000000/266305) (by norm_num) 20 213 215 (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
theorem reverseRound : (835/100:ℝ)<Real.logb 2 (90000000/266305) ∧ Real.logb 2 (90000000/266305)<845/100 := by
 convert c06_r07.powBounds (90000000/266305) (by norm_num) 20 167 169 (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
end c06_d03

namespace c06_d04
theorem entropyAsExpectedSurprisal {ι:Type*} (s:Finset ι) (p:ι→ℝ) : -(∑ i∈s,p i*Real.logb 2 (p i))=∑ i∈s,p i*(-Real.logb 2 (p i)) := by simp [←Finset.sum_neg_distrib]
end c06_d04

namespace c06_p01
theorem arithmetic_001 : ((3/8+2/8+3*(1/8)) : ℚ) = (1) := by norm_num
theorem arithmetic_002 : ((9/8+1/2+9/8) : ℚ) = (11/4) := by norm_num
theorem arithmetic_003 : (((9+4+9)/8) : ℚ) = (11/4) := by norm_num
theorem classCounts : (["u","zero","s","s","u","u","us","os"]:List String).count "u"=3 ∧ (["u","zero","s","s","u","u","us","os"]:List String).count "s"=2 := by decide +kernel
theorem greekEntropy : -(3/8:ℝ)*Real.logb 2 (3/8)-(2/8:ℝ)*Real.logb 2 (2/8)-3*((1/8:ℝ)*Real.logb 2 (1/8))=11/4-(3/8)*Real.logb 2 3 := by
 rw [Real.logb_div (by norm_num : (3:ℝ)≠0) (by norm_num : (8:ℝ)≠0),Real.logb_div (by norm_num : (2:ℝ)≠0) (by norm_num : (8:ℝ)≠0),Real.logb_div (by norm_num : (1:ℝ)≠0) (by norm_num : (8:ℝ)≠0)]
 rw [Real.logb_one,c06_r07.logTwo,c06_r07.logEight]; ring
theorem initialRound : (21555/10000:ℝ)<11/4-(3/8)*Real.logb 2 3 ∧ 11/4-(3/8)*Real.logb 2 3<21565/10000 := by rcases c06_r07.threeBounds with ⟨h1,h2⟩; constructor <;> linarith
theorem entropySubstituted (L:ℝ) :
 -(3/8)*(L-3)-(1/4)*(-2)-3*((1/8)*(-3))=11/4-(3/8)*L := by ring
end c06_p01

namespace c06_p02
theorem arithmetic_001 : (((1/8)/(2/8)) : ℚ) = (1/2) := by norm_num
theorem arithmetic_002 : (((3/8)*(2/3)) : ℚ) = (1/4) := by norm_num
theorem arithmetic_003 : ((2/3+1/3) : ℚ) = (1) := by norm_num
theorem arithmetic_004 : ((6/24) : ℚ) = (1/4) := by norm_num
theorem arithmetic_005 : ((3/8+3/8) : ℚ) = (3/4) := by norm_num
theorem groupEntropy : -(2/3:ℝ)*Real.logb 2 (2/3)-(1/3:ℝ)*Real.logb 2 (1/3)=Real.logb 2 3-2/3 := by
 rw [Real.logb_div (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0),Real.logb_div (by norm_num : (1:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
 rw [Real.logb_one,c06_r07.logTwo]; ring
theorem conditional (l:ℝ) : (2/8:ℝ)*1+(3/8)*(l-2/3)=(3/8)*l := by ring
theorem information (l:ℝ) : (11/4-(3/8)*l)-(3/8)*l=11/4-(3/4)*l := by ring
theorem conditionalRound : (5935/10000:ℝ)<3/8*Real.logb 2 3 ∧ 3/8*Real.logb 2 3<5945/10000 := by rcases c06_r07.threeBounds with ⟨h1,h2⟩; constructor <;> linarith
theorem groupRound : (9175/10000:ℝ)<Real.logb 2 3-2/3 ∧ Real.logb 2 3-2/3<9185/10000 := by rcases c06_r07.threeBounds with ⟨h1,h2⟩; constructor <;> linarith
theorem cancelWeight (x y:ℝ) (hx:x≠0) : x*(y/x)=y := by field_simp
theorem logMutual (xy x y:ℝ) (hxy:0<xy) (hx:0<x) (hy:0<y) : Real.logb 2 (xy/x)-Real.logb 2 y=Real.logb 2 (xy/(x*y)) := by
 rw [Real.logb_div (ne_of_gt hxy) (mul_ne_zero (ne_of_gt hx) (ne_of_gt hy)),Real.logb_mul (ne_of_gt hx) (ne_of_gt hy),Real.logb_div (ne_of_gt hxy) (ne_of_gt hx)]; ring
theorem mutualSymmetry {α β:Type*} (s:Finset α) (t:Finset β) (p:α→β→ℝ) (x:α→ℝ) (y:β→ℝ) :
 (∑ i∈s,∑ j∈t,p i j*Real.logb 2 (p i j/(x i*y j)))=(∑ j∈t,∑ i∈s,p i j*Real.logb 2 (p i j/(y j*x i))) := by rw [Finset.sum_comm]; simp [mul_comm]
theorem groupEntropySubstitution (L:ℝ) :
 -(2/3)*(1-L)-(1/3)*(-L)=L-2/3 := by ring
theorem allFiveGroups (L:ℝ) :
 (1/8)*0+(2/8)*1+(1/8)*0+(3/8)*(L-2/3)+(1/8)*0=(3/8)*L := by ring
theorem informationSubtraction (L:ℝ) :
 (11/4-(3/8)*L)-(3/8)*L=11/4-(3/4)*L := by ring
end c06_p02

namespace c06_p04
theorem arithmetic_001 : ((0-0) : ℚ) = (0) := by norm_num
theorem constantCell : (["on","on","on","on","on","on","on","on"]:List String).count "on"=8 := by decide +kernel
theorem noReduction (h:ℝ) : h-h=0 := sub_self h
theorem noUncertainty : -(1:ℝ)*Real.logb 2 1=0 := by simp
end c06_p04

namespace c06_p03
theorem arithmetic_001 : (((59/100)^2) : ℚ) = (3481/10000) := by norm_num
theorem arithmetic_002 : ((2*(3481/10000)) : ℚ) = (6962/10000) := by norm_num
theorem arithmetic_003 : ((90-10) : ℚ) = (80) := by norm_num
open MeasureTheory
open scoped Interval
noncomputable def f (m s t:ℝ):ℝ := 1/(t*s*Real.sqrt (2*Real.pi))*Real.exp (-((Real.log t-m)^2)/(2*s^2))
noncomputable def z (m s t:ℝ):ℝ := (Real.log t-m)/s
noncomputable def g (z:ℝ):ℝ := 1/Real.sqrt (2*Real.pi)*Real.exp (-z^2/2)
theorem derivative (m s t:ℝ) (ht:0<t) : HasDerivAt (z m s) (1/(s*t)) t := by
 have h:=((Real.hasDerivAt_log (ne_of_gt ht)).sub_const m).div_const s
 change HasDerivAt (fun x:ℝ => (Real.log x-m)/s) (1/(s*t)) t
 have he : 1/(s*t)=t⁻¹/s := by simp [div_eq_mul_inv,mul_comm]
 rw [he]; exact h
theorem substitution (m s t:ℝ) : g (z m s t)*(1/(s*t))=f m s t := by
 unfold g z f
 have h : -((Real.log t-m)/s)^2/2 = -((Real.log t-m)^2)/(2*s^2) := by ring
 rw [h]
 ring
theorem interval (m s a b:ℝ) (ha:0<a) (hab:a≤b) (hs:0<s) :
 (∫ t in a..b, f m s t)=∫ y in z m s a..z m s b, g y := by
 have hpos : ∀ x ∈ Set.uIcc a b, 0<x := by
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact lt_of_lt_of_le ha hx.1
 have h:=intervalIntegral.integral_comp_mul_deriv (f:=z m s) (f':=fun x=>1/(s*x)) (g:=g)
  (fun x hx=>derivative m s x (hpos x hx))
  (continuousOn_const.div (continuousOn_const.mul continuousOn_id) (fun x hx=>mul_ne_zero (ne_of_gt hs) (ne_of_gt (hpos x hx))))
  (by unfold g; fun_prop)
 simpa only [Function.comp_apply,substitution] using h
theorem gaussianArea : (∫ y:ℝ, g y)=1 := by
 have h:=ProbabilityTheory.integral_gaussianPDFReal_eq_one (0:ℝ) (v:=1) (by norm_num)
 simpa [ProbabilityTheory.gaussianPDFReal,g,one_div] using h
theorem lognormalArea (m s:ℝ) (hs:0<s) : (∫ t in Set.Ioi 0,f m s t)=1 := by
 have hz : Set.InjOn (z m s) (Set.Ioi 0) := by
  intro x hx y hy he
  have hlog : Real.log x=Real.log y := by
   unfold z at he
   have hh:Real.log x-m=Real.log y-m := (div_left_inj' (ne_of_gt hs)).mp he
   linarith
  exact Real.log_injOn_pos hx hy hlog
 have image : z m s '' Set.Ioi 0=Set.univ := by
  ext y
  simp only [Set.mem_univ,iff_true]
  refine ⟨Real.exp (s*y+m),Real.exp_pos _,?_⟩
  unfold z
  rw [Real.log_exp]
  field_simp
  ring
 have h:=MeasureTheory.integral_image_eq_integral_abs_deriv_smul
  (f:=z m s) (f':=fun t=>1/(s*t)) measurableSet_Ioi
  (fun t ht=>(derivative m s t ht).hasDerivWithinAt) hz g
 rw [image,MeasureTheory.setIntegral_univ,gaussianArea] at h
 rw [h]
 apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
 intro t ht
 change f m s t=|1/(s*t)| * g (z m s t)
 have htp:0<t:=ht
 rw [abs_of_pos (by positivity : 0<1/(s*t)),mul_comm]
 exact (substitution m s t).symm

theorem derivativeFactors (s t:ℝ) : (1/s)*(1/t-0)=1/(s*t) := by ring
theorem normalizedExponent (v m s:ℝ) :
 -(v-m)^2/(2*s^2)= -(1/2)*((v-m)/s)^2 := by ring
theorem densityFactorSeparation (t s c e:ℝ) :
 (1/(t*s*c))*e=(1/c)*e*(1/(s*t)) := by ring
end c06_p03

namespace c06_n01
theorem ratioCancellation (p q w:ℝ) (hp:p≠0) : (p*q)/(p*w)=q/w := mul_div_mul_left q w hp
theorem objectiveDifference (c i j beta:ℝ) : (c-beta*i)-(c-beta*j)= -beta*(i-j) := by ring
theorem accuracyReducesObjective (c i j beta:ℝ) (hb:0<beta) (hij:i<j) : c-beta*j<c-beta*i := by nlinarith
theorem marginalTotal {α β:Type*} (s:Finset α) (t:Finset β) (p:α→ℝ) (q:α→β→ℝ) (hp:∑ i∈s,p i=1) (hq:∀ i∈s,∑ j∈t,q i j=1) :
 (∑ j∈t,∑ i∈s,p i*q i j)=1 := by
 rw [Finset.sum_comm]
 simp_rw [←Finset.mul_sum]
 calc
  (∑ i∈s,p i*(∑ j∈t,q i j)) = ∑ i∈s,p i := by
   apply Finset.sum_congr rfl
   intro i hi
   rw [hq i hi,mul_one]
  _=1 := hp
end c06_n01
end Chapter06
#print axioms Chapter06.c06_r01.arithmetic_001
#print axioms Chapter06.c06_r01.greekCounts
#print axioms Chapter06.c06_r02.arithmetic_001
#print axioms Chapter06.c06_r02.arithmetic_002
#print axioms Chapter06.c06_r02.arithmetic_003
#print axioms Chapter06.c06_r02.arithmetic_004
#print axioms Chapter06.c06_r02.arithmetic_005
#print axioms Chapter06.c06_r03.bayesRatio
#print axioms Chapter06.c06_r03.normalizeFinite
#print axioms Chapter06.c06_r03.posteriorFromProduct
#print axioms Chapter06.c06_r04.arithmetic_001
#print axioms Chapter06.c06_r04.arithmetic_002
#print axioms Chapter06.c06_r04.arithmetic_003
#print axioms Chapter06.c06_r04.productRule
#print axioms Chapter06.c06_r05.arithmetic_001
#print axioms Chapter06.c06_r05.arithmetic_002
#print axioms Chapter06.c06_r05.arithmetic_003
#print axioms Chapter06.c06_r05.arithmetic_004
#print axioms Chapter06.c06_r05.arithmetic_005
#print axioms Chapter06.c06_r05.arithmetic_006
#print axioms Chapter06.c06_r05.binomialNormalization
#print axioms Chapter06.c06_r05.zeroCount
#print axioms Chapter06.c06_r05.chooseOne
#print axioms Chapter06.c06_r05.factorialCancellation
#print axioms Chapter06.c06_r05.oneCount
#print axioms Chapter06.c06_r06.arithmetic_001
#print axioms Chapter06.c06_r06.arithmetic_002
#print axioms Chapter06.c06_r06.bernoulliMean
#print axioms Chapter06.c06_r06.bernoulliVariance
#print axioms Chapter06.c06_r06.sumMeans
#print axioms Chapter06.c06_r06.sumVariances
#print axioms Chapter06.c06_r06.independentVariance
#print axioms Chapter06.c06_r07.logTwo
#print axioms Chapter06.c06_r07.logFour
#print axioms Chapter06.c06_r07.logEight
#print axioms Chapter06.c06_r07.basicSurprise
#print axioms Chapter06.c06_r07.powBounds
#print axioms Chapter06.c06_r07.threeBounds
#print axioms Chapter06.c06_r08.arithmetic_001
#print axioms Chapter06.c06_r08.arithmetic_002
#print axioms Chapter06.c06_r08.surpriseProduct
#print axioms Chapter06.c06_r08.contextualMeanSign
#print axioms Chapter06.c06_r08.tokenMean
#print axioms Chapter06.c06_r09.arithmetic_001
#print axioms Chapter06.c06_r09.arithmetic_002
#print axioms Chapter06.c06_r09.classEntropy
#print axioms Chapter06.c06_r09.constantEntropy
#print axioms Chapter06.c06_r10.arithmetic_001
#print axioms Chapter06.c06_r10.arithmetic_002
#print axioms Chapter06.c06_r10.arithmetic_003
#print axioms Chapter06.c06_r10.arithmetic_004
#print axioms Chapter06.c06_r10.arithmetic_005
#print axioms Chapter06.c06_d01.arithmetic_001
#print axioms Chapter06.c06_d01.arithmetic_002
#print axioms Chapter06.c06_d01.arithmetic_003
#print axioms Chapter06.c06_d01.arithmetic_004
#print axioms Chapter06.c06_d01.arithmetic_005
#print axioms Chapter06.c06_d01.posteriorSum
#print axioms Chapter06.c06_d02.arithmetic_001
#print axioms Chapter06.c06_d02.arithmetic_002
#print axioms Chapter06.c06_d02.arithmetic_003
#print axioms Chapter06.c06_d02.arithmetic_004
#print axioms Chapter06.c06_d02.arithmetic_005
#print axioms Chapter06.c06_d02.arithmetic_006
#print axioms Chapter06.c06_d02.arithmetic_007
#print axioms Chapter06.c06_d02.arithmetic_008
#print axioms Chapter06.c06_d02.arithmetic_009
#print axioms Chapter06.c06_d02.arithmetic_010
#print axioms Chapter06.c06_d02.arithmetic_011
#print axioms Chapter06.c06_d02.arithmetic_012
#print axioms Chapter06.c06_d03.arithmetic_001
#print axioms Chapter06.c06_d03.arithmetic_002
#print axioms Chapter06.c06_d03.arithmetic_003
#print axioms Chapter06.c06_d03.arithmetic_004
#print axioms Chapter06.c06_d03.ratio
#print axioms Chapter06.c06_d03.forwardRound
#print axioms Chapter06.c06_d03.reverseRound
#print axioms Chapter06.c06_d04.entropyAsExpectedSurprisal
#print axioms Chapter06.c06_p01.arithmetic_001
#print axioms Chapter06.c06_p01.arithmetic_002
#print axioms Chapter06.c06_p01.arithmetic_003
#print axioms Chapter06.c06_p01.classCounts
#print axioms Chapter06.c06_p01.greekEntropy
#print axioms Chapter06.c06_p01.initialRound
#print axioms Chapter06.c06_p01.entropySubstituted
#print axioms Chapter06.c06_p02.arithmetic_001
#print axioms Chapter06.c06_p02.arithmetic_002
#print axioms Chapter06.c06_p02.arithmetic_003
#print axioms Chapter06.c06_p02.arithmetic_004
#print axioms Chapter06.c06_p02.arithmetic_005
#print axioms Chapter06.c06_p02.groupEntropy
#print axioms Chapter06.c06_p02.conditional
#print axioms Chapter06.c06_p02.information
#print axioms Chapter06.c06_p02.conditionalRound
#print axioms Chapter06.c06_p02.groupRound
#print axioms Chapter06.c06_p02.cancelWeight
#print axioms Chapter06.c06_p02.logMutual
#print axioms Chapter06.c06_p02.mutualSymmetry
#print axioms Chapter06.c06_p02.groupEntropySubstitution
#print axioms Chapter06.c06_p02.allFiveGroups
#print axioms Chapter06.c06_p02.informationSubtraction
#print axioms Chapter06.c06_p04.arithmetic_001
#print axioms Chapter06.c06_p04.constantCell
#print axioms Chapter06.c06_p04.noReduction
#print axioms Chapter06.c06_p04.noUncertainty
#print axioms Chapter06.c06_p03.arithmetic_001
#print axioms Chapter06.c06_p03.arithmetic_002
#print axioms Chapter06.c06_p03.arithmetic_003
#print axioms Chapter06.c06_p03.derivative
#print axioms Chapter06.c06_p03.substitution
#print axioms Chapter06.c06_p03.interval
#print axioms Chapter06.c06_p03.gaussianArea
#print axioms Chapter06.c06_p03.lognormalArea
#print axioms Chapter06.c06_p03.derivativeFactors
#print axioms Chapter06.c06_p03.normalizedExponent
#print axioms Chapter06.c06_p03.densityFactorSeparation
#print axioms Chapter06.c06_n01.ratioCancellation
#print axioms Chapter06.c06_n01.objectiveDifference
#print axioms Chapter06.c06_n01.accuracyReducesObjective
#print axioms Chapter06.c06_n01.marginalTotal
