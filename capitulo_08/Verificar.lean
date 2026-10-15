import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter08

namespace c08_a01
def transitions (q:ℕ) (c:Char) : List (ℕ×Char) :=
  if q=0 then if c='d' then [(1,'d'),(2,'t')] else if c='t' || c='a' then [(0,c)] else []
  else if q=1 then if c='d' then [(1,'d'),(2,'t')] else if c='t' || c='a' then [(0,c)] else []
  else []
def run : ℕ → List Char → List (ℕ×List Char)
  | q, [] => [(q,[])]
  | q, c::cs => (transitions q c).flatMap (fun qo => (run qo.1 cs).map (fun su => (su.1,qo.2::su.2)))
def outputs (s:String) : List (List Char) := ((run 0 s.toList).filter (fun x => x.1=0 || x.1=2)).map Prod.snd
theorem sourceTad : outputs "tad" = ["tat".toList] := by decide +kernel
theorem sourceTada : outputs "tada" = ["tada".toList] := by decide +kernel

end c08_a01

namespace c08_a02
def transitions (q:ℕ) (c:Char) : List (ℕ×Char) :=
  if q=0 then if c='d' then [(1,'d'),(2,'t')] else if c='t' || c='a' then [(0,c)] else []
  else if q=1 then if c='d' then [(1,'d'),(2,'t')] else if c='t' || c='a' then [(0,c)] else []
  else []
def run : ℕ → List Char → List (ℕ×List Char)
  | q, [] => [(q,[])]
  | q, c::cs => (transitions q c).flatMap (fun qo => (run qo.1 cs).map (fun su => (su.1,qo.2::su.2)))
def outputs (s:String) : List (List Char) := ((run 0 s.toList).filter (fun x => x.1=0 || x.1=2)).map Prod.snd
theorem sourceTad : outputs "tad" = ["tat".toList] := by decide +kernel
theorem sourceTada : outputs "tada" = ["tada".toList] := by decide +kernel
def step (_q:ℕ) (c:Char) : ℕ := if c='D' then 1 else 0
theorem finalState (xs:List Char) (c:Char) : (xs++[c]).foldl step 0 = if c='D' then 1 else 0 := by simp [List.foldl_append,step]
theorem emptyAccepted : ([]:List Char).foldl step 0 = 0 := by rfl

end c08_a02

namespace c08_a04
theorem surface : "Cylindr"++"ical"++"ly"="Cylindrically" := by decide +kernel
theorem canonicalBase : "Cylind"++"e"++"r"="Cylinder" := by decide +kernel
theorem canonicalSegmentation : "Cylinder"++"-"++"ical"++"-"++"ly"="Cylinder-ical-ly" := by decide +kernel
theorem differentBases : "Cylindr"≠"Cylinder" := by decide +kernel
end c08_a04

namespace c08_a03
theorem arithmetic_001 : ((1+2+2+1+2) : ℚ) = (8) := by norm_num
theorem arithmetic_002 : ((1+1+3*2) : ℚ) = (8) := by norm_num
theorem arithmetic_003 : ((1+1+3) : ℚ) = (5) := by norm_num
theorem deletion : "intention".toList.tail = "ntention".toList := by decide +kernel
theorem substitution1 : 'e'::"ntention".toList.tail="etention".toList := by decide +kernel
theorem substitution2 : "e".toList++"x".toList++("etention".toList.drop 2)="exention".toList := by decide +kernel
theorem insertion : ("exention".toList.take 4)++['u']++("exention".toList.drop 4)="exenution".toList := by decide +kernel
theorem substitution3 : ("exenution".toList.take 3)++['c']++("exenution".toList.drop 4)="execution".toList := by decide +kernel
end c08_a03

namespace c08_a05
theorem arithmetic_001 : (((9+1)*(9+1)) : ℚ) = (100) := by norm_num
theorem arithmetic_002 : ((4+1) : ℚ) = (5) := by norm_num
theorem arithmetic_003 : ((3+0) : ℚ) = (3) := by norm_num
def rows : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 2, 3, 4, 5, 6, 7, 6, 7, 8], [2, 3, 4, 5, 6, 7, 8, 7, 8, 7], [3, 4, 5, 6, 7, 8, 7, 8, 9, 8], [4, 3, 4, 5, 6, 7, 8, 9, 10, 9], [5, 4, 5, 6, 7, 8, 9, 10, 11, 10], [6, 5, 6, 7, 8, 9, 8, 9, 10, 11], [7, 6, 7, 8, 9, 10, 9, 8, 9, 10], [8, 7, 8, 9, 10, 11, 10, 9, 8, 9], [9, 8, 9, 10, 11, 12, 11, 10, 9, 8]]
def d (i j:ℕ):ℕ := (rows[i]!).getD j 0
def source : List Char := "intention".toList
def target : List Char := "execution".toList
theorem boundaries : (List.range 10).all (fun i=>d i 0==i && d 0 i==i)=true := by decide +kernel
theorem everyCell : (List.range 9).all (fun i=>(List.range 9).all (fun j=>d (i+1) (j+1)==min (d i (j+1)+1) (min (d (i+1) j+1) (d i j+(if (source[i]!) == (target[j]!) then 0 else 2)))))=true := by decide +kernel
theorem sourceResult : d 9 9=8 ∧ d 1 1=2 ∧ d 4 1=3 := by decide +kernel
end c08_a05

namespace c08_r01
theorem arithmetic_001 : ((927-608) : ℚ) = (319) := by norm_num
theorem arithmetic_002 : ((608+319) : ℚ) = (927) := by norm_num
theorem arithmetic_003 : ((608/927+319/927) : ℚ) = (1) := by norm_num
theorem arithmetic_004 : ((608/927) : ℚ) ≥ (1311/2000) := by norm_num
theorem arithmetic_005 : ((608/927) : ℚ) < (1313/2000) := by norm_num
theorem derivative (p:ℝ) (hp:0<p) (hp1:p<1) : HasDerivAt (fun x:ℝ=>608*Real.log x+319*Real.log (1-x)) ((608-927*p)/(p*(1-p))) p := by
 have hn:p≠0:=ne_of_gt hp
 have hm:1-p≠0:=ne_of_gt (by linarith)
 have h:=((Real.hasDerivAt_log hn).const_mul 608).add ((((hasDerivAt_id p).const_sub 1).log hm).const_mul 319)
 exact h.congr_deriv (by dsimp; field_simp; ring)
theorem critical (p:ℝ) : 608-927*p=0 ↔ p=608/927 := by constructor <;> intro h <;> linarith
theorem signBefore (p:ℝ) (hp:0<p) (h:p<608/927) : 0<(608-927*p)/(p*(1-p)) := by apply div_pos <;> nlinarith
theorem signAfter (p:ℝ) (h:608/927<p) (hp:p<1) : (608-927*p)/(p*(1-p))<0 := by apply div_neg_of_neg_of_pos <;> nlinarith
end c08_r01

namespace c08_r02
theorem arithmetic_001 : ((25/100*33/100) : ℚ) = (825/10000) := by norm_num
theorem arithmetic_002 : ((825/10000*11/10000) : ℚ) = (9075/100000000) := by norm_num
theorem arithmetic_003 : ((9075/100000000*1/2) : ℚ) = (45375/1000000000) := by norm_num
theorem arithmetic_004 : ((45375/1000000000*68/100) : ℚ) = (30855/1000000000) := by norm_num
end c08_r02

namespace c08_r03
theorem arithmetic_001 : ((608+1) : ℚ) = (609) := by norm_num
theorem arithmetic_002 : ((927+1446) : ℚ) = (2373) := by norm_num
theorem arithmetic_003 : ((0+1) : ℚ) = (1) := by norm_num
theorem arithmetic_004 : ((609/2373) : ℚ) ≥ (513/2000) := by norm_num
theorem arithmetic_005 : ((609/2373) : ℚ) < (515/2000) := by norm_num
theorem arithmetic_006 : ((609/2373) : ℚ) < (608/927) := by norm_num
theorem normalized {α:Type*} (s:Finset α) (c:α→ℝ) (h:∑ j∈s,(c j+1)≠0) : ∑ j∈s,((c j+1)/(∑ k∈s,(c k+1)))=1 := by rw [←Finset.sum_div,div_self h]
theorem denominator {α:Type*} (s:Finset α) (c:α→ℝ) : ∑ j∈s,(c j+1)=(∑ j∈s,c j)+s.card := by simp [Finset.sum_add_distrib]
end c08_r03

namespace c08_r04
theorem arithmetic_001 : ((25/10*3) : ℚ) = (75/10) := by norm_num
theorem arithmetic_002 : ((-5*2) : ℚ) = (-10) := by norm_num
theorem arithmetic_003 : ((-12/10*1) : ℚ) = (-12/10) := by norm_num
theorem arithmetic_004 : ((1/2*3) : ℚ) = (3/2) := by norm_num
theorem arithmetic_005 : ((2*0) : ℚ) = (0) := by norm_num
theorem arithmetic_006 : ((7/10*419/100) : ℚ) = (2933/1000) := by norm_num
theorem arithmetic_007 : ((75/10-10-12/10+3/2+2933/1000+1/10) : ℚ) = (833/1000) := by norm_num
theorem sigmoidBounds (z:ℝ) : 0<1/(1+Real.exp (-z)) ∧ 1/(1+Real.exp (-z))<1 := by
 have h:0<Real.exp (-z):=Real.exp_pos _
 constructor
 · positivity
 · apply (div_lt_one (by positivity)).2; linarith
theorem sigmoidRewrite (z:ℝ) : 1/(1+Real.exp (-z))=Real.exp z/(1+Real.exp z) := by
 rw [Real.exp_neg]
 have h:Real.exp z≠0:=ne_of_gt (Real.exp_pos z)
 have h1:1+Real.exp z≠0:=ne_of_gt (by positivity)
 field_simp
 <;> ring
theorem oddsSolve (r p:ℝ) (hr:0<r) (hp:p≠1) : r=p/(1-p) ↔ p=r/(1+r) := by
 have hp':1-p≠0:=sub_ne_zero.mpr (Ne.symm hp)
 have hr':1+r≠0:=ne_of_gt (by linarith)
 constructor <;> intro h
 · apply (eq_div_iff hr').2; have h':= (eq_div_iff hp').1 h; nlinarith
 · apply (eq_div_iff hp').2; have h':= (eq_div_iff hr').1 h; nlinarith

theorem roundedProbabilityExpbase : (217371549/500000000:ℝ)<Real.exp (-833/1000:ℝ) ∧ Real.exp (-833/1000:ℝ)<(434743099/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(-833/1000:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem roundedProbabilityExp : (217371549/500000000:ℝ)<Real.exp (-833/1000:ℝ) ∧ Real.exp (-833/1000:ℝ)<(434743099/1000000000:ℝ) := roundedProbabilityExpbase
theorem roundedProbability : (1393/2000:ℝ)<1/(1+Real.exp (-833/1000:ℝ)) ∧ 1/(1+Real.exp (-833/1000:ℝ))<(279/400:ℝ) := by
 have h := roundedProbabilityExp
 have hn : 0<1+Real.exp (-833/1000:ℝ) := by positivity
 constructor
 · apply (lt_div_iff₀ hn).2
   linarith [h.2]
 · apply (div_lt_iff₀ hn).2
   linarith [h.1]
theorem lengthLowerExpbase : (1687292207/1000000000:ℝ)<Real.exp (837/1600:ℝ) ∧ Real.exp (837/1600:ℝ)<(105455763/62500000:ℝ) := by
 have h := Real.exp_bound (x:=(837/1600:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem lengthLowerExp : (656935007/10000000:ℝ)<Real.exp (837/200:ℝ) ∧ Real.exp (837/200:ℝ)<(3284675051/50000000:ℝ) := by
 have h := lengthLowerExpbase
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=8) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=8) (by norm_num)
 have he : Real.exp (837/200:ℝ) = (Real.exp (837/1600:ℝ))^8 := by
  convert Real.exp_nat_mul (837/1600:ℝ) 8 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (656935007/10000000:ℝ) < (1687292207/1000000000:ℝ)^8 := by norm_num
        _ < _ := hL
 · calc (Real.exp (837/1600:ℝ))^8 < (105455763/62500000:ℝ)^8 := hU
        _ < (3284675051/50000000:ℝ) := by norm_num
theorem lengthUpperExpbase : (1689402641/1000000000:ℝ)<Real.exp (839/1600:ℝ) ∧ Real.exp (839/1600:ℝ)<(844701321/500000000:ℝ) := by
 have h := Real.exp_bound (x:=(839/1600:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem lengthUpperExp : (1327074627/20000000:ℝ)<Real.exp (839/200:ℝ) ∧ Real.exp (839/200:ℝ)<(414710823/6250000:ℝ) := by
 have h := lengthUpperExpbase
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=8) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=8) (by norm_num)
 have he : Real.exp (839/200:ℝ) = (Real.exp (839/1600:ℝ))^8 := by
  convert Real.exp_nat_mul (839/1600:ℝ) 8 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (1327074627/20000000:ℝ) < (1689402641/1000000000:ℝ)^8 := by norm_num
        _ < _ := hL
 · calc (Real.exp (839/1600:ℝ))^8 < (844701321/500000000:ℝ)^8 := hU
        _ < (414710823/6250000:ℝ) := by norm_num
theorem roundedLogLength : (837/200:ℝ)<Real.log 66 ∧ Real.log 66<839/200 := by
 constructor
 · apply (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<66)).2
   linarith [lengthLowerExp.2]
 · apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<66)).2
   linarith [lengthUpperExp.1]

end c08_r04

namespace c08_r05
theorem arithmetic_001 : ((833/1000) : ℚ) > (0) := by norm_num
theorem arithmetic_002 : ((697/1000) : ℚ) > (1/2) := by norm_num
theorem positiveDecision (z:ℝ) (hz:0<z) : (1/2:ℝ)<1/(1+Real.exp (-z)) := by
 have he : Real.exp (-z)<1 := by simpa using (Real.exp_lt_exp.mpr (show -z<0 by linarith))
 have hd:0<1+Real.exp (-z):=by positivity
 apply (lt_div_iff₀ hd).2
 linarith
end c08_r05

namespace c08_r06
theorem arithmetic_001 : ((8+10+1) : ℚ) = (19) := by norm_num
theorem arithmetic_002 : ((5+60+50) : ℚ) = (115) := by norm_num
theorem arithmetic_003 : ((3+30+200) : ℚ) = (233) := by norm_num
theorem arithmetic_004 : ((19+115+233) : ℚ) = (367) := by norm_num
theorem arithmetic_005 : ((8+60+200) : ℚ) = (268) := by norm_num
theorem arithmetic_006 : ((10+1) : ℚ) = (11) := by norm_num
theorem arithmetic_007 : ((5+3) : ℚ) = (8) := by norm_num
theorem arithmetic_008 : ((60+50+30+200) : ℚ) = (340) := by norm_num
theorem arithmetic_009 : ((8/(8+11)) : ℚ) = (8/19) := by norm_num
theorem arithmetic_010 : ((8/(8+8)) : ℚ) = (1/2) := by norm_num
theorem arithmetic_011 : ((2*(8/19)*(1/2)/(8/19+1/2)) : ℚ) = (16/35) := by norm_num
theorem arithmetic_012 : ((16/(16+11+8)) : ℚ) = (16/35) := by norm_num
theorem arithmetic_013 : (((8+340)/367) : ℚ) = (348/367) := by norm_num
theorem arithmetic_014 : ((268/367) : ℚ) ≥ (1459/2000) := by norm_num
theorem arithmetic_015 : ((268/367) : ℚ) < (1461/2000) := by norm_num

namespace Harmonic
 theorem harmonicTwo (p r : ℝ) (hp : 0<p) (hr : 0<r) :
  1 / ((1/p+1/r)/2) = 2*p*r/(p+r) := by
  have h : p+r≠0 := ne_of_gt (add_pos hp hr)
  field_simp
  <;> ring
 theorem counts (t f g : ℝ) (ht : 0<t) (hf : 0≤f) (hg : 0≤g) :
  2*(t/(t+f))*(t/(t+g))/(t/(t+f)+t/(t+g)) = 2*t/(2*t+f+g) := by
  have ha : t+f ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ht hf)
  have hb : t+g ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ht hg)
  have hc : 2*t+f+g ≠ 0 := by positivity
  field_simp
  <;> ring
end Harmonic
end c08_r06

namespace c08_r07
theorem arithmetic_001 : ((5+50) : ℚ) = (55) := by norm_num
theorem arithmetic_002 : ((10+30) : ℚ) = (40) := by norm_num
theorem arithmetic_003 : ((3+30) : ℚ) = (33) := by norm_num
theorem arithmetic_004 : ((1+50) : ℚ) = (51) := by norm_num
theorem arithmetic_005 : ((120/(120+55+40)) : ℚ) = (24/43) := by norm_num
theorem arithmetic_006 : ((400/(400+33+51)) : ℚ) = (100/121) := by norm_num
theorem arithmetic_007 : ((367-268) : ℚ) = (99) := by norm_num
theorem arithmetic_008 : ((2*268/(2*268+99+99)) : ℚ) = (268/367) := by norm_num
theorem arithmetic_009 : ((536/734) : ℚ) = (268/367) := by norm_num
theorem arithmetic_010 : ((1000000-100) : ℚ) = (999900) := by norm_num
theorem arithmetic_011 : ((999900/1000000) : ℚ) = (9999/10000) := by norm_num
theorem arithmetic_012 : ((9999/10000*100) : ℚ) = (9999/100) := by norm_num
theorem arithmetic_013 : ((0/100) : ℚ) = (0) := by norm_num
theorem arithmetic_014 : (((16/35+24/43+100/121)/3) : ℚ) ≥ (1227/2000) := by norm_num
theorem arithmetic_015 : (((16/35+24/43+100/121)/3) : ℚ) < (1229/2000) := by norm_num
theorem zeroDenominator : ¬∃ x:ℝ, (0:ℝ)*x=1 := by simp
end c08_r07

namespace c08_r08
theorem arithmetic_001 : ((60/100) : ℚ) = (3/5) := by norm_num
theorem arithmetic_002 : ((20/100) : ℚ) = (1/5) := by norm_num
theorem arithmetic_003 : ((3/5+1/5+1/5) : ℚ) = (1) := by norm_num
theorem arithmetic_004 : ((500+419+500) : ℚ) = (1419) := by norm_num
theorem arithmetic_005 : ((500/1419+419/1419+500/1419) : ℚ) = (1) := by norm_num
theorem arithmetic_006 : ((500/1419) : ℚ) ≠ (3/5) := by norm_num
theorem arithmetic_007 : ((419/1419) : ℚ) ≠ (1/5) := by norm_num
end c08_r08

namespace c08_r09
theorem arithmetic_001 : ((1/100) : ℚ) < (16/100) := by norm_num
theorem arithmetic_002 : ((16/100) : ℚ) < (149/100) := by norm_num
theorem arithmetic_003 : ((149/100) : ℚ) < (2) := by norm_num
theorem binaryBrier (p y:ℝ) : (p-y)^2+((1-p)-(1-y))^2=2*(p-y)^2 := by ring
theorem binaryBound (p y:ℝ) (hp:0≤p) (hp1:p≤1) (hy:y=0∨y=1) : 0≤2*(p-y)^2 ∧ 2*(p-y)^2≤2 := by rcases hy with rfl|rfl <;> constructor <;> nlinarith [sq_nonneg p,sq_nonneg (p-1)]
end c08_r09

namespace c08_d01
theorem oddsRatio (a w:ℝ) : Real.exp (a+w)/Real.exp a=Real.exp w := by rw [Real.exp_add]; exact mul_div_cancel_left₀ _ (ne_of_gt (Real.exp_pos a))
theorem probabilityDifference (a w:ℝ) : Real.exp (a+w)/(1+Real.exp (a+w))-Real.exp a/(1+Real.exp a)=Real.exp a*(Real.exp w-1)/((1+Real.exp (a+w))*(1+Real.exp a)) := by
 rw [Real.exp_add]
 have h1:1+Real.exp a*Real.exp w≠0:=by positivity
 have h2:1+Real.exp a≠0:=by positivity
 field_simp
 <;> ring
end c08_d01

namespace c08_d02
theorem arithmetic_001 : ((2*(1637/10000)*(1846/10000)) : ℚ) = (6043804/100000000) := by norm_num
theorem arithmetic_002 : ((1637/10000+1846/10000) : ℚ) = (3483/10000) := by norm_num
theorem arithmetic_003 : (((6043804/100000000)/(3483/10000)) : ℚ) ≥ (3469/20000) := by norm_num
theorem arithmetic_004 : (((6043804/100000000)/(3483/10000)) : ℚ) < (3471/20000) := by norm_num
end c08_d02

namespace c08_d03
theorem binary (p y:ℝ) : (p-y)^2+((1-p)-(1-y))^2=2*(p-y)^2 := by ring
theorem pooled (nc ne bc be:ℝ) : (nc*bc+ne*be)/(nc+ne)=(nc/(nc+ne))*bc+(ne/(nc+ne))*be := by ring
end c08_d03

namespace c08_d04
theorem arithmetic_001 : ((800+100+100) : ℚ) = (1000) := by norm_num
theorem arithmetic_002 : ((800/1000) : ℚ) = (4/5) := by norm_num
theorem arithmetic_003 : ((100/1000) : ℚ) = (1/10) := by norm_num
theorem arithmetic_004 : ((67*800) : ℚ) = (53600) := by norm_num
theorem arithmetic_005 : ((67*100) : ℚ) = (6700) := by norm_num
theorem arithmetic_006 : ((53600+6700+6700) : ℚ) = (67000) := by norm_num
theorem arithmetic_007 : ((67*1000) : ℚ) = (67000) := by norm_num
end c08_d04

namespace c08_p01
theorem arithmetic_001 : ((1-7/10) : ℚ) = (3/10) := by norm_num
theorem sigmoidBounds (z:ℝ) : 0<1/(1+Real.exp (-z)) ∧ 1/(1+Real.exp (-z))<1 := by
 have h:0<Real.exp (-z):=Real.exp_pos _
 constructor
 · positivity
 · apply (div_lt_one (by positivity)).2; linarith
theorem sigmoidRewrite (z:ℝ) : 1/(1+Real.exp (-z))=Real.exp z/(1+Real.exp z) := by
 rw [Real.exp_neg]
 have h:Real.exp z≠0:=ne_of_gt (Real.exp_pos z)
 have h1:1+Real.exp z≠0:=ne_of_gt (by positivity)
 field_simp
 <;> ring
theorem oddsSolve (r p:ℝ) (hr:0<r) (hp:p≠1) : r=p/(1-p) ↔ p=r/(1+r) := by
 have hp':1-p≠0:=sub_ne_zero.mpr (Ne.symm hp)
 have hr':1+r≠0:=ne_of_gt (by linarith)
 constructor <;> intro h
 · apply (eq_div_iff hr').2; have h':= (eq_div_iff hp').1 h; nlinarith
 · apply (eq_div_iff hp').2; have h':= (eq_div_iff hr').1 h; nlinarith
theorem complement (z:ℝ) : 1-Real.exp z/(1+Real.exp z)=1/(1+Real.exp z) := by field_simp; ring
theorem lossRewrite (z y:ℝ) : -(y*Real.log (Real.exp z/(1+Real.exp z))+(1-y)*Real.log (1/(1+Real.exp z)))=Real.log (1+Real.exp z)-y*z := by
 have he:Real.exp z≠0:=ne_of_gt (Real.exp_pos z)
 have hd:1+Real.exp z≠0:=by positivity
 rw [Real.log_div he hd,Real.log_exp,Real.log_div one_ne_zero hd,Real.log_one]
 ring
theorem positiveLoss (p:ℝ) : -(1*Real.log p+(1-1)*Real.log (1-p))= -Real.log p := by ring
theorem negativeLoss (p:ℝ) : -(0*Real.log p+(1-0)*Real.log (1-p))= -Real.log (1-p) := by ring
theorem lossAtZero : Real.log (1+Real.exp 0)-1*0=Real.log 2 := by norm_num
theorem curvePositive (p:ℝ) (hp:p≠0) : HasDerivAt (fun x:ℝ => -Real.log x) (-p⁻¹) p := (Real.hasDerivAt_log hp).neg
theorem curveNegative (p:ℝ) (hp:1-p≠0) : HasDerivAt (fun x:ℝ => -Real.log (1-x)) (1/(1-p)) p := by
 exact ((((hasDerivAt_id p).const_sub 1).log hp).neg).congr_deriv (by simp only [id_eq]; ring)
theorem positiveLossBoundsLowerExpbase : (700122471/1000000000:ℝ)<Real.exp (-713/2000:ℝ) ∧ Real.exp (-713/2000:ℝ)<(87515309/125000000:ℝ) := by
 have h := Real.exp_bound (x:=(-713/2000:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem positiveLossBoundsLowerExp : (700122471/1000000000:ℝ)<Real.exp (-713/2000:ℝ) ∧ Real.exp (-713/2000:ℝ)<(87515309/125000000:ℝ) := positiveLossBoundsLowerExpbase
theorem positiveLossBoundsUpperExpbase : (349711349/500000000:ℝ)<Real.exp (-143/400:ℝ) ∧ Real.exp (-143/400:ℝ)<(699422699/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(-143/400:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem positiveLossBoundsUpperExp : (349711349/500000000:ℝ)<Real.exp (-143/400:ℝ) ∧ Real.exp (-143/400:ℝ)<(699422699/1000000000:ℝ) := positiveLossBoundsUpperExpbase
theorem positiveLossBounds : (713/2000:ℝ)< -Real.log (7/10:ℝ) ∧ -Real.log (7/10:ℝ)<(143/400:ℝ) := by
 have hL := (Real.log_lt_iff_lt_exp (by norm_num : 0<(7/10:ℝ))).2 (show (7/10:ℝ)<Real.exp (-713/2000:ℝ) by linarith [positiveLossBoundsLowerExp.1])
 have hU := (Real.lt_log_iff_exp_lt (by norm_num : 0<(7/10:ℝ))).2 (show Real.exp (-143/400:ℝ)<(7/10:ℝ) by linarith [positiveLossBoundsUpperExp.2])
 constructor <;> linarith
theorem negativeLossBoundsLowerExpbase : (109570411/200000000:ℝ)<Real.exp (-2407/4000:ℝ) ∧ Real.exp (-2407/4000:ℝ)<(68481507/125000000:ℝ) := by
 have h := Real.exp_bound (x:=(-2407/4000:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem negativeLossBoundsLowerExp : (30014187/100000000:ℝ)<Real.exp (-2407/2000:ℝ) ∧ Real.exp (-2407/2000:ℝ)<(7503547/25000000:ℝ) := by
 have h := negativeLossBoundsLowerExpbase
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=2) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=2) (by norm_num)
 have he : Real.exp (-2407/2000:ℝ) = (Real.exp (-2407/4000:ℝ))^2 := by
  convert Real.exp_nat_mul (-2407/4000:ℝ) 2 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (30014187/100000000:ℝ) < (109570411/200000000:ℝ)^2 := by norm_num
        _ < _ := hL
 · calc (Real.exp (-2407/4000:ℝ))^2 < (68481507/125000000:ℝ)^2 := hU
        _ < (7503547/25000000:ℝ) := by norm_num
theorem negativeLossBoundsUpperExpbase : (273789099/500000000:ℝ)<Real.exp (-2409/4000:ℝ) ∧ Real.exp (-2409/4000:ℝ)<(547578199/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(-2409/4000:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem negativeLossBoundsUpperExp : (7496047/25000000:ℝ)<Real.exp (-2409/2000:ℝ) ∧ Real.exp (-2409/2000:ℝ)<(29984189/100000000:ℝ) := by
 have h := negativeLossBoundsUpperExpbase
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=2) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=2) (by norm_num)
 have he : Real.exp (-2409/2000:ℝ) = (Real.exp (-2409/4000:ℝ))^2 := by
  convert Real.exp_nat_mul (-2409/4000:ℝ) 2 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (7496047/25000000:ℝ) < (273789099/500000000:ℝ)^2 := by norm_num
        _ < _ := hL
 · calc (Real.exp (-2409/4000:ℝ))^2 < (547578199/1000000000:ℝ)^2 := hU
        _ < (29984189/100000000:ℝ) := by norm_num
theorem negativeLossBounds : (2407/2000:ℝ)< -Real.log (3/10:ℝ) ∧ -Real.log (3/10:ℝ)<(2409/2000:ℝ) := by
 have hL := (Real.log_lt_iff_lt_exp (by norm_num : 0<(3/10:ℝ))).2 (show (3/10:ℝ)<Real.exp (-2407/2000:ℝ) by linarith [negativeLossBoundsLowerExp.1])
 have hU := (Real.lt_log_iff_exp_lt (by norm_num : 0<(3/10:ℝ))).2 (show Real.exp (-2409/2000:ℝ)<(3/10:ℝ) by linarith [negativeLossBoundsUpperExp.2])
 constructor <;> linarith

end c08_p01

namespace c08_p02
theorem arithmetic_001 : ((1/(1+1)) : ℚ) = (1/2) := by norm_num
theorem arithmetic_002 : ((1/2-1) : ℚ) = (-1/2) := by norm_num
theorem arithmetic_003 : (((-1/2)*3) : ℚ) = (-3/2) := by norm_num
theorem arithmetic_004 : (((-1/2)*2) : ℚ) = (-1) := by norm_num
theorem arithmetic_005 : ((0-(1/10)*(-3/2)) : ℚ) = (3/20) := by norm_num
theorem arithmetic_006 : ((0-(1/10)*(-1)) : ℚ) = (1/10) := by norm_num
theorem arithmetic_007 : ((0-(1/10)*(-1/2)) : ℚ) = (1/20) := by norm_num
theorem arithmetic_008 : (((3/20)*3+(1/10)*2+1/20) : ℚ) = (7/10) := by norm_num
theorem lossDerivative (z y:ℝ) : HasDerivAt (fun t:ℝ=>Real.log (1+Real.exp t)-y*t) (Real.exp z/(1+Real.exp z)-y) z := by
 have hn:1+Real.exp z≠0:=by positivity
 exact ((((Real.hasDerivAt_exp z).const_add 1).log hn).sub ((hasDerivAt_id z).const_mul y)).congr_deriv (by ring)
theorem logisticDerivative (z:ℝ) : HasDerivAt (fun t:ℝ=>Real.exp t/(1+Real.exp t)) (Real.exp z/(1+Real.exp z)^2) z := by
 have hn:1+Real.exp z≠0:=by positivity
 have h:=(Real.hasDerivAt_exp z).div ((Real.hasDerivAt_exp z).const_add 1) hn
 exact h.congr_deriv (by ring)
theorem curvature (z:ℝ) : 0<Real.exp z/(1+Real.exp z)^2 := by positivity
theorem chainCoordinate (a w x y:ℝ) : HasDerivAt (fun t:ℝ=>Real.log (1+Real.exp (a+t*x))-y*(a+t*x)) ((Real.exp (a+w*x)/(1+Real.exp (a+w*x))-y)*x) w := by
 simpa only [Function.comp_def, id_eq, one_mul] using (lossDerivative (a+w*x) y).comp w (((hasDerivAt_id w).mul_const x).const_add a)
theorem quotientExpansion (e:ℝ) : e*(1+e)-e*e=e := by ring

theorem updatedProbabilityExpbase : (496585303/1000000000:ℝ)<Real.exp (-7/10:ℝ) ∧ Real.exp (-7/10:ℝ)<(62073163/125000000:ℝ) := by
 have h := Real.exp_bound (x:=(-7/10:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem updatedProbabilityExp : (496585303/1000000000:ℝ)<Real.exp (-7/10:ℝ) ∧ Real.exp (-7/10:ℝ)<(62073163/125000000:ℝ) := updatedProbabilityExpbase
theorem updatedProbability : (267/400:ℝ)<1/(1+Real.exp (-7/10:ℝ)) ∧ 1/(1+Real.exp (-7/10:ℝ))<(1337/2000:ℝ) := by
 have h := updatedProbabilityExp
 have hn : 0<1+Real.exp (-7/10:ℝ) := by positivity
 constructor
 · apply (lt_div_iff₀ hn).2
   linarith [h.2]
 · apply (div_lt_iff₀ hn).2
   linarith [h.1]
theorem updatedScoreExpbase : (2013752707/1000000000:ℝ)<Real.exp (7/10:ℝ) ∧ Real.exp (7/10:ℝ)<(503438177/250000000:ℝ) := by
 have h := Real.exp_bound (x:=(7/10:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem updatedScoreExp : (2013752707/1000000000:ℝ)<Real.exp (7/10:ℝ) ∧ Real.exp (7/10:ℝ)<(503438177/250000000:ℝ) := updatedScoreExpbase
theorem lossLowerExpbase : (867710469/500000000:ℝ)<Real.exp (441/800:ℝ) ∧ Real.exp (441/800:ℝ)<(1735420939/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(441/800:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem lossLowerExp : (301168583/100000000:ℝ)<Real.exp (441/400:ℝ) ∧ Real.exp (441/400:ℝ)<(37646073/12500000:ℝ) := by
 have h := lossLowerExpbase
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=2) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=2) (by norm_num)
 have he : Real.exp (441/400:ℝ) = (Real.exp (441/800:ℝ))^2 := by
  convert Real.exp_nat_mul (441/800:ℝ) 2 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (301168583/100000000:ℝ) < (867710469/500000000:ℝ)^2 := by norm_num
        _ < _ := hL
 · calc (Real.exp (441/800:ℝ))^2 < (1735420939/1000000000:ℝ)^2 := hU
        _ < (37646073/12500000:ℝ) := by norm_num
theorem lossUpperExpbase : (868144433/500000000:ℝ)<Real.exp (2207/4000:ℝ) ∧ Real.exp (2207/4000:ℝ)<(1736288867/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(2207/4000:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem lossUpperExp : (150734951/50000000:ℝ)<Real.exp (2207/2000:ℝ) ∧ Real.exp (2207/2000:ℝ)<(301469903/100000000:ℝ) := by
 have h := lossUpperExpbase
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=2) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=2) (by norm_num)
 have he : Real.exp (2207/2000:ℝ) = (Real.exp (2207/4000:ℝ))^2 := by
  convert Real.exp_nat_mul (2207/4000:ℝ) 2 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (150734951/50000000:ℝ) < (868144433/500000000:ℝ)^2 := by norm_num
        _ < _ := hL
 · calc (Real.exp (2207/4000:ℝ))^2 < (1736288867/1000000000:ℝ)^2 := hU
        _ < (301469903/100000000:ℝ) := by norm_num
theorem logTwoLowerExpbase : (1993715533/1000000000:ℝ)<Real.exp (69/100:ℝ) ∧ Real.exp (69/100:ℝ)<(996857767/500000000:ℝ) := by
 have h := Real.exp_bound (x:=(69/100:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem logTwoLowerExp : (1993715533/1000000000:ℝ)<Real.exp (69/100:ℝ) ∧ Real.exp (69/100:ℝ)<(996857767/500000000:ℝ) := logTwoLowerExpbase
theorem updatedLossBounds : (805/2000:ℝ)<Real.log (1+Real.exp (7/10))-7/10 ∧ Real.log (1+Real.exp (7/10))-7/10<807/2000 := by
 have hn : 0<1+Real.exp (7/10:ℝ) := by positivity
 have hL := (Real.lt_log_iff_exp_lt hn).2 (show Real.exp (441/400:ℝ)<1+Real.exp (7/10:ℝ) by linarith [lossLowerExp.2,updatedScoreExp.1])
 have hU := (Real.log_lt_iff_lt_exp hn).2 (show 1+Real.exp (7/10:ℝ)<Real.exp (2207/2000:ℝ) by linarith [lossUpperExp.1,updatedScoreExp.2])
 constructor <;> linarith
theorem stepDecreases : Real.log (1+Real.exp (7/10:ℝ))-7/10<Real.log 2 := by
 have h := (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<2)).2 (show Real.exp (69/100:ℝ)<2 by linarith [logTwoLowerExp.2])
 linarith [updatedLossBounds.2]

end c08_p02

namespace c08_p03
theorem arithmetic_001 : ((100*292/395) : ℚ) ≥ (1477/20) := by norm_num
theorem arithmetic_002 : ((100*292/395) : ℚ) < (1479/20) := by norm_num
theorem arithmetic_003 : ((100*292/783) : ℚ) ≥ (745/20) := by norm_num
theorem arithmetic_004 : ((100*292/783) : ℚ) < (747/20) := by norm_num
theorem penaltySquared (w:ℝ) : HasDerivAt (fun x:ℝ=>x^2) (2*w) w := by simpa using hasDerivAt_pow 2 w
theorem penaltyPositive (w:ℝ) (hw:0<w) : HasDerivAt (fun x:ℝ=>|x|) 1 w := hasDerivAt_abs_pos hw
theorem penaltyNegative (w:ℝ) (hw:w<0) : HasDerivAt (fun x:ℝ=>|x|) (-1) w := hasDerivAt_abs_neg hw
end c08_p03

namespace c08_p04
theorem cancelTotal (o e n:ℝ) (hn:n≠0) : (o/n)/(e/n)=o/e := by field_simp
theorem logRatio (o e n:ℝ) (ho:0<o) (he:0<e) (hn:0<n) : Real.log (o/n)-Real.log (e/n)=Real.log (o/e) := by rw [←Real.log_div (ne_of_gt (div_pos ho hn)) (ne_of_gt (div_pos he hn)),cancelTotal o e n (ne_of_gt hn)]
theorem comparison (dataTerm free restricted:ℝ) : (dataTerm+free)-(dataTerm+restricted)=free-restricted := by ring
end c08_p04

namespace c08_p05
theorem arithmetic_001 : ((55/1000+90/1000+67/10000+1/10+74/100+1/100) : ℚ) = (10017/10000) := by norm_num
theorem normalization {α:Type*} (s:Finset α) (z:α→ℝ) (hs:s.Nonempty) : ∑ j∈s, (Real.exp (z j)/(∑ k∈s,Real.exp (z k)))=1 := by
 have h:0<∑ k∈s,Real.exp (z k):=Finset.sum_pos (fun i hi=>Real.exp_pos _) hs
 rw [←Finset.sum_div,div_self (ne_of_gt h)]
theorem shift {α:Type*} (s:Finset α) (z:α→ℝ) (c:ℝ) (j:α) : Real.exp (z j+c)/(∑ k∈s,Real.exp (z k+c))=Real.exp (z j)/(∑ k∈s,Real.exp (z k)) := by
 simp_rw [Real.exp_add]
 rw [←Finset.sum_mul]
 exact mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos c))

theorem expScore0base : (4555297/2500000:ℝ)<Real.exp (3/5:ℝ) ∧ Real.exp (3/5:ℝ)<(1822118801/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(3/5:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem expScore0 : (4555297/2500000:ℝ)<Real.exp (3/5:ℝ) ∧ Real.exp (3/5:ℝ)<(1822118801/1000000000:ℝ) := expScore0base
theorem expScore1base : (1733253017/1000000000:ℝ)<Real.exp (11/20:ℝ) ∧ Real.exp (11/20:ℝ)<(866626509/500000000:ℝ) := by
 have h := Real.exp_bound (x:=(11/20:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem expScore1 : (150208301/50000000:ℝ)<Real.exp (11/10:ℝ) ∧ Real.exp (11/10:ℝ)<(300416603/100000000:ℝ) := by
 have h := expScore1base
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=2) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=2) (by norm_num)
 have he : Real.exp (11/10:ℝ) = (Real.exp (11/20:ℝ))^2 := by
  convert Real.exp_nat_mul (11/20:ℝ) 2 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (150208301/50000000:ℝ) < (1733253017/1000000000:ℝ)^2 := by norm_num
        _ < _ := hL
 · calc (Real.exp (11/20:ℝ))^2 < (866626509/500000000:ℝ)^2 := hU
        _ < (300416603/100000000:ℝ) := by norm_num
theorem expScore2base : (59045819/125000000:ℝ)<Real.exp (-3/4:ℝ) ∧ Real.exp (-3/4:ℝ)<(472366553/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(-3/4:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem expScore2 : (4462603/20000000:ℝ)<Real.exp (-3/2:ℝ) ∧ Real.exp (-3/2:ℝ)<(22313017/100000000:ℝ) := by
 have h := expScore2base
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=2) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=2) (by norm_num)
 have he : Real.exp (-3/2:ℝ) = (Real.exp (-3/4:ℝ))^2 := by
  convert Real.exp_nat_mul (-3/4:ℝ) 2 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (4462603/20000000:ℝ) < (59045819/125000000:ℝ)^2 := by norm_num
        _ < _ := hL
 · calc (Real.exp (-3/4:ℝ))^2 < (472366553/1000000000:ℝ)^2 := hU
        _ < (22313017/100000000:ℝ) := by norm_num
theorem expScore3base : (4555297/2500000:ℝ)<Real.exp (3/5:ℝ) ∧ Real.exp (3/5:ℝ)<(1822118801/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(3/5:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem expScore3 : (83002923/25000000:ℝ)<Real.exp (6/5:ℝ) ∧ Real.exp (6/5:ℝ)<(332011693/100000000:ℝ) := by
 have h := expScore3base
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=2) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=2) (by norm_num)
 have he : Real.exp (6/5:ℝ) = (Real.exp (3/5:ℝ))^2 := by
  convert Real.exp_nat_mul (3/5:ℝ) 2 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (83002923/25000000:ℝ) < (4555297/2500000:ℝ)^2 := by norm_num
        _ < _ := hL
 · calc (Real.exp (3/5:ℝ))^2 < (1822118801/1000000000:ℝ)^2 := hU
        _ < (332011693/100000000:ℝ) := by norm_num
theorem expScore4base : (34774077/15625000:ℝ)<Real.exp (4/5:ℝ) ∧ Real.exp (4/5:ℝ)<(2225540929/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(4/5:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem expScore4 : (2453253017/100000000:ℝ)<Real.exp (16/5:ℝ) ∧ Real.exp (16/5:ℝ)<(1226626511/50000000:ℝ) := by
 have h := expScore4base
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=4) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=4) (by norm_num)
 have he : Real.exp (16/5:ℝ) = (Real.exp (4/5:ℝ))^4 := by
  convert Real.exp_nat_mul (4/5:ℝ) 4 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (2453253017/100000000:ℝ) < (34774077/15625000:ℝ)^4 := by norm_num
        _ < _ := hL
 · calc (Real.exp (4/5:ℝ))^4 < (2225540929/1000000000:ℝ)^4 := hU
        _ < (1226626511/50000000:ℝ) := by norm_num
theorem expScore5base : (57694981/100000000:ℝ)<Real.exp (-11/20:ℝ) ∧ Real.exp (-11/20:ℝ)<(576949811/1000000000:ℝ) := by
 have h := Real.exp_bound (x:=(-11/20:ℝ)) (by norm_num) (n:=12) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
theorem expScore5 : (8321777/25000000:ℝ)<Real.exp (-11/10:ℝ) ∧ Real.exp (-11/10:ℝ)<(33287109/100000000:ℝ) := by
 have h := expScore5base
 have hL := pow_lt_pow_left₀ h.1 (by norm_num) (n:=2) (by norm_num)
 have hU := pow_lt_pow_left₀ h.2 (le_of_lt (Real.exp_pos _)) (n:=2) (by norm_num)
 have he : Real.exp (-11/10:ℝ) = (Real.exp (-11/20:ℝ))^2 := by
  convert Real.exp_nat_mul (-11/20:ℝ) 2 using 1 <;> norm_num
 rw [he]
 constructor
 · calc (8321777/25000000:ℝ) < (57694981/100000000:ℝ)^2 := by norm_num
        _ < _ := hL
 · calc (Real.exp (-11/20:ℝ))^2 < (576949811/1000000000:ℝ)^2 := hU
        _ < (33287109/100000000:ℝ) := by norm_num
theorem probability0 : (109/2000:ℝ)<Real.exp (3/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ Real.exp (3/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ))<(111/2000:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 have hs : 0<(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) := by positivity
 constructor
 · apply (lt_div_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
 · apply (div_lt_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
theorem probability1 : (179/2000:ℝ)<Real.exp (11/10:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ Real.exp (11/10:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ))<(181/2000:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 have hs : 0<(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) := by positivity
 constructor
 · apply (lt_div_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
 · apply (div_lt_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
theorem probability2 : (133/20000:ℝ)<Real.exp (-3/2:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ Real.exp (-3/2:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ))<(27/4000:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 have hs : 0<(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) := by positivity
 constructor
 · apply (lt_div_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
 · apply (div_lt_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
theorem probability3 : (19/200:ℝ)<Real.exp (6/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ Real.exp (6/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ))<(21/200:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 have hs : 0<(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) := by positivity
 constructor
 · apply (lt_div_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
 · apply (div_lt_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
theorem probability4 : (147/200:ℝ)<Real.exp (16/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ Real.exp (16/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ))<(149/200:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 have hs : 0<(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) := by positivity
 constructor
 · apply (lt_div_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
 · apply (div_lt_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
theorem probability5 : (19/2000:ℝ)<Real.exp (-11/10:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ Real.exp (-11/10:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ))<(21/2000:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 have hs : 0<(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) := by positivity
 constructor
 · apply (lt_div_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
 · apply (div_lt_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]

theorem operationalExp0 : (36441/20000:ℝ) < Real.exp (3/5:ℝ) ∧ Real.exp (3/5:ℝ) < (36443/20000:ℝ) := by
 have h:=expScore0
 constructor <;> linarith [h.1,h.2]
theorem operationalExp1 : (60083/20000:ℝ) < Real.exp (11/10:ℝ) ∧ Real.exp (11/10:ℝ) < (12017/4000:ℝ) := by
 have h:=expScore1
 constructor <;> linarith [h.1,h.2]
theorem operationalExp2 : (4461/20000:ℝ) < Real.exp (-3/2:ℝ) ∧ Real.exp (-3/2:ℝ) < (4463/20000:ℝ) := by
 have h:=expScore2
 constructor <;> linarith [h.1,h.2]
theorem operationalExp3 : (66401/20000:ℝ) < Real.exp (6/5:ℝ) ∧ Real.exp (6/5:ℝ) < (66403/20000:ℝ) := by
 have h:=expScore3
 constructor <;> linarith [h.1,h.2]
theorem operationalExp4 : (490649/20000:ℝ) < Real.exp (16/5:ℝ) ∧ Real.exp (16/5:ℝ) < (490651/20000:ℝ) := by
 have h:=expScore4
 constructor <;> linarith [h.1,h.2]
theorem operationalExp5 : (6657/20000:ℝ) < Real.exp (-11/10:ℝ) ∧ Real.exp (-11/10:ℝ) < (6659/20000:ℝ) := by
 have h:=expScore5
 constructor <;> linarith [h.1,h.2]
theorem operationalDenominator : (664697/20000:ℝ) < (Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ (Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) < (664699/20000:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
theorem operationalProbability0 : (219/4000:ℝ) < Real.exp (3/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ Real.exp (3/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) < (1097/20000:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 have hs : 0<(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) := by positivity
 constructor
 · apply (lt_div_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
 · apply (div_lt_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
theorem operationalProbability4 : (14763/20000:ℝ) < Real.exp (16/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) ∧ Real.exp (16/5:ℝ)/(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) < (2953/4000:ℝ) := by
 have h0:=expScore0
 have h1:=expScore1
 have h2:=expScore2
 have h3:=expScore3
 have h4:=expScore4
 have h5:=expScore5
 have hs : 0<(Real.exp (3/5:ℝ)+Real.exp (11/10:ℝ)+Real.exp (-3/2:ℝ)+Real.exp (6/5:ℝ)+Real.exp (16/5:ℝ)+Real.exp (-11/10:ℝ)) := by positivity
 constructor
 · apply (lt_div_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
 · apply (div_lt_iff₀ hs).2
   linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]

end c08_p05

namespace c08_p06
theorem lossDerivative (z y:ℝ) : HasDerivAt (fun t:ℝ=>Real.log (1+Real.exp t)-y*t) (Real.exp z/(1+Real.exp z)-y) z := by
 have hn:1+Real.exp z≠0:=by positivity
 exact ((((Real.hasDerivAt_exp z).const_add 1).log hn).sub ((hasDerivAt_id z).const_mul y)).congr_deriv (by ring)
theorem logisticDerivative (z:ℝ) : HasDerivAt (fun t:ℝ=>Real.exp t/(1+Real.exp t)) (Real.exp z/(1+Real.exp z)^2) z := by
 have hn:1+Real.exp z≠0:=by positivity
 have h:=(Real.hasDerivAt_exp z).div ((Real.hasDerivAt_exp z).const_add 1) hn
 exact h.congr_deriv (by ring)
theorem curvature (z:ℝ) : 0<Real.exp z/(1+Real.exp z)^2 := by positivity
theorem chainCoordinate (a w x y:ℝ) : HasDerivAt (fun t:ℝ=>Real.log (1+Real.exp (a+t*x))-y*(a+t*x)) ((Real.exp (a+w*x)/(1+Real.exp (a+w*x))-y)*x) w := by
 simpa only [Function.comp_def, id_eq, one_mul] using (lossDerivative (a+w*x) y).comp w (((hasDerivAt_id w).mul_const x).const_add a)
theorem quotientExpansion (e:ℝ) : e*(1+e)-e*e=e := by ring
theorem sigmoidOpposite (z:ℝ) : 1/(1+Real.exp z)=1-Real.exp z/(1+Real.exp z) := by field_simp; ring
theorem dotStep {d:ℕ} (u v:Fin d→ℝ) (a p y:ℝ) : ∑ j, (u j-a*(p-y)*v j)*v j=(∑ j,u j*v j)-a*(p-y)*(∑ j,(v j)^2) := by
 calc
  (∑ j, (u j-a*(p-y)*v j)*v j) = ∑ j, (u j*v j-a*(p-y)*(v j)^2) := by
   apply Finset.sum_congr rfl
   intro i hi
   ring
  _ = _ := by rw [Finset.sum_sub_distrib,←Finset.mul_sum]
theorem positivePair (a p s:ℝ) (ha:0<a) (hp:p<1) (hs:0<s) : 0< -a*(p-1)*s := by nlinarith [mul_pos ha (sub_pos.mpr hp),mul_pos (mul_pos ha (sub_pos.mpr hp)) hs]
theorem negativePair (a p s:ℝ) (ha:0<a) (hp:0<p) (hs:0<s) : -a*p*s<0 := by nlinarith [mul_pos ha hp,mul_pos (mul_pos ha hp) hs]
end c08_p06

namespace c08_n01
theorem table : (([(0,0),(0,1),(1,0),(1,1)] : List (ℚ×ℚ)).map (fun (x,y) => (max 0 (x+y),max 0 (x+y-1),max 0 (max 0 (x+y)-2*max 0 (x+y-1))))) = [(0,0,0),(1,0,1),(1,0,1),(2,1,0)] := by decide +kernel
theorem reluNegative (z:ℝ) (hz:z≤0) : max 0 z=0 := max_eq_left hz
theorem reluPositive (z:ℝ) (hz:0≤z) : max 0 z=z := max_eq_right hz
theorem reluContinuous : Continuous (fun z:ℝ => max 0 z) := continuous_const.max continuous_id
theorem leftSlope (x y:ℝ) (hx:x≤0) (hy:y≤0) : (max 0 y-max 0 x)/(y-x)=0 := by rw [max_eq_left hx,max_eq_left hy]; simp
theorem rightSlope (x y:ℝ) (hx:0≤x) (hy:0≤y) (hne:y≠x) : (max 0 y-max 0 x)/(y-x)=1 := by rw [max_eq_right hx,max_eq_right hy]; exact div_self (sub_ne_zero.mpr hne)
theorem noAffineXor (a b c:ℝ) (h0:a≤0) (h1:0<a+c) (h2:0<a+b) (h3:a+b+c≤0) : False := by linarith
 theorem xorAffineInput (x₁ x₂ : ℝ) :
  Matrix.mulVec (!![(1:ℝ),1;1,1]) ![x₁,x₂] + ![0,-1] = ![x₁+x₂,x₁+x₂-1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

end c08_n01

namespace c08_n02
theorem arithmetic_001 : ((512/8) : ℚ) = (64) := by norm_num
theorem arithmetic_002 : ((8*64) : ℚ) = (512) := by norm_num
theorem arithmetic_003 : ((8^2) : ℚ) = (64) := by norm_num
theorem normalization {α:Type*} (s:Finset α) (z:α→ℝ) (hs:s.Nonempty) : ∑ j∈s, (Real.exp (z j)/(∑ k∈s,Real.exp (z k)))=1 := by
 have h:0<∑ k∈s,Real.exp (z k):=Finset.sum_pos (fun i hi=>Real.exp_pos _) hs
 rw [←Finset.sum_div,div_self (ne_of_gt h)]
theorem shift {α:Type*} (s:Finset α) (z:α→ℝ) (c:ℝ) (j:α) : Real.exp (z j+c)/(∑ k∈s,Real.exp (z k+c))=Real.exp (z j)/(∑ k∈s,Real.exp (z k)) := by
 simp_rw [Real.exp_add]
 rw [←Finset.sum_mul]
 exact mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos c))
theorem root : Real.sqrt 64=8 := by norm_num
theorem queryKeyProduct {n d:ℕ} (Q K:Matrix (Fin n) (Fin d) ℝ) (i j:Fin n) : (Q*K.transpose) i j=∑ k, Q i k*K j k := by rfl
theorem weightedValues {n r:ℕ} (A:Matrix (Fin n) (Fin n) ℝ) (V:Matrix (Fin n) (Fin r) ℝ) (i:Fin n) (j:Fin r) : (A*V) i j=∑ k, A i k*V k j := by rfl
open scoped BigOperators
 theorem projectedComparisons {n d k : ℕ}
     (X : Matrix (Fin n) (Fin d) ℝ)
     (WQ WK : Matrix (Fin d) (Fin k) ℝ) (i j : Fin n) :
  ((X*WQ)*(X*WK).transpose) i j =
    ∑ r : Fin k, (∑ s : Fin d, X i s * WQ s r) *
      (∑ t : Fin d, X j t * WK t r) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
 theorem ffnExpanded {d m k : ℕ} (x : Fin d → ℝ)
     (W₁ : Matrix (Fin d) (Fin m) ℝ)
     (W₂ : Matrix (Fin m) (Fin k) ℝ)
     (b₁ : Fin m → ℝ) (b₂ : Fin k → ℝ) (j : Fin k) :
  (Matrix.vecMul (fun r => max 0 ((Matrix.vecMul x W₁) r + b₁ r)) W₂ + b₂) j =
  (∑ r : Fin m, max 0 ((∑ s : Fin d, x s * W₁ s r) + b₁ r) * W₂ r j) + b₂ j := by
  rfl

end c08_n02

namespace c08_n03
theorem arithmetic_001 : ((872/10-542/10) : ℚ) = (33) := by norm_num
theorem arithmetic_002 : ((920/10-480/10) : ℚ) = (44) := by norm_num
theorem sigmoidBounds (z:ℝ) : 0<1/(1+Real.exp (-z)) ∧ 1/(1+Real.exp (-z))<1 := by
 have h:0<Real.exp (-z):=Real.exp_pos _
 constructor
 · positivity
 · apply (div_lt_one (by positivity)).2; linarith
theorem sigmoidRewrite (z:ℝ) : 1/(1+Real.exp (-z))=Real.exp z/(1+Real.exp z) := by
 rw [Real.exp_neg]
 have h:Real.exp z≠0:=ne_of_gt (Real.exp_pos z)
 have h1:1+Real.exp z≠0:=ne_of_gt (by positivity)
 field_simp
 <;> ring
theorem oddsSolve (r p:ℝ) (hr:0<r) (hp:p≠1) : r=p/(1-p) ↔ p=r/(1+r) := by
 have hp':1-p≠0:=sub_ne_zero.mpr (Ne.symm hp)
 have hr':1+r≠0:=ne_of_gt (by linarith)
 constructor <;> intro h
 · apply (eq_div_iff hr').2; have h':= (eq_div_iff hp').1 h; nlinarith
 · apply (eq_div_iff hp').2; have h':= (eq_div_iff hr').1 h; nlinarith
theorem keep (c new:ℝ) : 1*c+0*new=c := by ring
theorem replace (c new:ℝ) : 0*c+1*new=new := by ring
end c08_n03

namespace c08_n04
theorem arithmetic_001 : ((67*1000) : ℚ) = (67000) := by norm_num
theorem arithmetic_002 : ((800+100+100) : ℚ) = (1000) := by norm_num
theorem efficiencyTwo (v0 vA vB vAB:ℝ) : (1/2)*((vA-v0)+(vAB-vB))+(1/2)*((vB-v0)+(vAB-vA))=vAB-v0 := by ring
end c08_n04

namespace c08_n05
theorem arithmetic_001 : ((2*(-2)+1*0) : ℚ) = (-4) := by norm_num
theorem arithmetic_002 : ((2*(-1)+1*(-1)) : ℚ) = (-3) := by norm_num
theorem arithmetic_003 : ((1*(-1)+2*0) : ℚ) = (-1) := by norm_num
theorem arithmetic_004 : ((1*0+2*(-1)) : ℚ) = (-2) := by norm_num
theorem arithmetic_005 : ((2*(-2)) : ℚ) = (-4) := by norm_num
theorem arithmetic_006 : ((1*0) : ℚ) = (0) := by norm_num
theorem arithmetic_007 : ((2*(-1)) : ℚ) = (-2) := by norm_num
theorem arithmetic_008 : ((1*(-1)) : ℚ) = (-1) := by norm_num
theorem arithmetic_009 : ((-2-1) : ℚ) = (-3) := by norm_num
theorem arithmetic_010 : ((0-2) : ℚ) = (-2) := by norm_num
theorem arithmetic_011 : ((1+1) : ℚ) = (2) := by norm_num
theorem arithmetic_012 : ((8+4) : ℚ) = (12) := by norm_num
theorem arithmetic_013 : ((12-11) : ℚ) = (1) := by norm_num
theorem arithmetic_014 : ((-3) : ℚ) > (-4) := by norm_num
theorem arithmetic_015 : ((-1) : ℚ) > (-2) := by norm_num
theorem arithmetic_016 : ((0) : ℚ) < (2) := by norm_num
theorem arithmetic_017 : ((8) : ℚ) < (11) := by norm_num
theorem arithmetic_018 : ((4) : ℚ) < (11) := by norm_num
theorem arithmetic_019 : ((12) : ℚ) > (11) := by norm_num
theorem tableaux : (([(-2,0),(-1,-1)]:List (ℚ×ℚ)).map (fun (a,b) => 2*a+b))=[-4,-3] ∧ (([(-1,0),(0,-1)]:List (ℚ×ℚ)).map (fun (a,b) => a+2*b))=[-1,-2] := by decide +kernel
 theorem harmonyDifference (w1 w2:ℝ) : (-w1-w2)-(-2*w1)=w1-w2 ∧ (-w1)-(-w2)=w2-w1 := by constructor <;> ring
 theorem conditions (w1 w2:ℝ) : (-w1-w2 > -2*w1 ↔ w1>w2) ∧ (-w1 > -w2 ↔ w2>w1) := by constructor <;> constructor <;> intro h <;> linarith
 theorem strictImpossible (w1 w2:ℝ) : ¬ (w1>w2 ∧ w2>w1) := by intro h; linarith [h.1,h.2]
 theorem marginConditions (w1 w2:ℝ) : (w1-w2≥1 ↔ w2≤w1-1) ∧ (w2-w1≥1 ↔ w2≥w1+1) := by constructor <;> constructor <;> intro h <;> linarith
 theorem marginImpossible (w1 w2:ℝ) : ¬ (w1-w2≥1 ∧ w2-w1≥1) := by intro h; linarith [h.1,h.2]
 theorem canceledMargins (w1 w2:ℝ) : (w1-w2)+(w2-w1)=0 := by ring
 theorem separation (w:ℝ) : (w+1)-(w-1)=2 := by ring
 theorem plotUpper (w:ℝ) : -(w:ℝ)+(w+1)=1 := by ring
 theorem plotLower (w:ℝ) : (w:ℝ)-(w-1)=1 := by ring
 theorem upwardRegion (w y:ℝ) : w+1≤y → -w+y≥1 := by intro h; linarith
 theorem downwardRegion (w y:ℝ) : y≤w-1 → w-y≥1 := by intro h; linarith
end c08_n05

namespace c08_n06
theorem arithmetic_001 : ((1+1+1+1) : ℚ) = (4) := by norm_num
theorem arithmetic_002 : ((1/4+1/4+1/4+1/4) : ℚ) = (1) := by norm_num
theorem arithmetic_003 : ((55) : ℚ) > (24) := by norm_num
theorem arithmetic_004 : ((64) : ℚ) > (59) := by norm_num
theorem publishedWindow : ([-2,-1,1,2]:List ℤ).length=4 ∧ ([-2,-1,1,2]:List ℤ).Nodup ∧ (0:ℤ)∉([-2,-1,1,2]:List ℤ) := by decide +kernel
 theorem contextMean (a b c d:ℝ) : (a+b+c+d)/4=a/4+b/4+c/4+d/4 := by ring
 theorem reorderedMean (a b c d:ℝ) : (a+b+c+d)/4=(d+c+b+a)/4 := by ring
end c08_n06

namespace c08_n07
theorem arithmetic_001 : ((884/10-855/10) : ℚ) = (29/10) := by norm_num
theorem logRatio (p q:ℝ) (hp:0<p) (hq:0<q) : Real.log p-Real.log q=Real.log (p/q) := (Real.log_div (ne_of_gt hp) (ne_of_gt hq)).symm
theorem preference (p q:ℝ) (hp:0<p) (hq:0<q) : 0<Real.log p-Real.log q ↔ q<p := by
 rw [sub_pos,Real.log_lt_log_iff hq hp]
theorem noPreference (p q:ℝ) (hp:0<p) (hq:0<q) : Real.log p-Real.log q=0 ↔ p=q := by
 rw [sub_eq_zero]
 constructor
 · intro h; exact Real.log_injOn_pos hp hq h
 · rintro rfl; rfl
end c08_n07

namespace c08_n08
theorem arithmetic_001 : ((825/10-598/10) : ℚ) = (227/10) := by norm_num
def squared {m k:ℕ} (B:Fin k→Fin m→ℝ) (x y:Fin m→ℝ) : ℝ := ∑ r,(∑ c,B r c*(x c-y c))^2
theorem nonnegative {m k:ℕ} (B:Fin k→Fin m→ℝ) (x y:Fin m→ℝ) : 0 ≤ squared B x y := Finset.sum_nonneg (fun r hr=>sq_nonneg _)
theorem symmetric {m k:ℕ} (B:Fin k→Fin m→ℝ) (x y:Fin m→ℝ) : squared B x y=squared B y x := by
 unfold squared
 apply Finset.sum_congr rfl
 intro r hr
 have h:(∑ c,B r c*(x c-y c))= -(∑ c,B r c*(y c-x c)) := by
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring
 rw [h]
 ring
theorem zeroDiagonal {m k:ℕ} (B:Fin k→Fin m→ℝ) (x:Fin m→ℝ) : squared B x x=0 := by simp [squared]
theorem dotAsSquares {k:ℕ} (u:Fin k→ℝ) : (∑ r,u r*u r)=∑ r,(u r)^2 := by apply Finset.sum_congr rfl; intro r hr; ring
end c08_n08

namespace c08_n09
theorem arithmetic_001 : ((4400/100-2034/100) : ℚ) = (2366/100) := by norm_num
theorem arithmetic_002 : ((6378/100-6172/100) : ℚ) = (206/100) := by norm_num
theorem normalized {n:ℕ} (g c:Fin n→ℝ) (w:ℝ) (hg:(∑ a : Fin n, g a)=1) (hc:(∑ a : Fin n, c a)=1) : (∑ a : Fin n, (w * g a + (1 - w) * c a))=1 := by
 rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hg,hc]
 ring
theorem nonnegative (w g c:ℝ) (hw:0 ≤ w) (hw1:w ≤ 1) (hg:0 ≤ g) (hc:0 ≤ c) : 0 ≤ w*g+(1-w)*c := add_nonneg (mul_nonneg hw hg) (mul_nonneg (sub_nonneg.mpr hw1) hc)
theorem sourceCurves :
 ([2034,4034,5027,5510,6019,6172]:List ℚ).Pairwise (· < ·) ∧
 ([4400,5300,5654,5958,6238,6378]:List ℚ).Pairwise (· < ·) ∧
 ([5099,5726,6108,6314,6488,6667]:List ℚ).Pairwise (· < ·) := by decide +kernel
theorem ordering : ∀ (i:Fin 6),
 (![2034,4034,5027,5510,6019,6172] i:ℚ) < ![4400,5300,5654,5958,6238,6378] i ∧
 (![4400,5300,5654,5958,6238,6378] i:ℚ) < ![5099,5726,6108,6314,6488,6667] i := by decide +kernel
open scoped BigOperators
def popolucaInput : Fin 8 → Char := !['k','k','i',':','m','b','a',':']
theorem copyPositions (a : Fin 8 → ℝ) :
 (∑ j : Fin 8, if popolucaInput j='k' then a j else 0) = a 0+a 1 := by
 simp [popolucaInput,Fin.sum_univ_succ]
theorem copyMixture (a : Fin 8 → ℝ) (w g:ℝ) :
 w*g+(1-w)*(∑ j : Fin 8, if popolucaInput j='k' then a j else 0) = w*g+(1-w)*(a 0+a 1) := by
 rw [copyPositions]

end c08_n09
end Chapter08
#print axioms Chapter08.c08_a01.sourceTad
#print axioms Chapter08.c08_a01.sourceTada
#print axioms Chapter08.c08_a02.sourceTad
#print axioms Chapter08.c08_a02.sourceTada
#print axioms Chapter08.c08_a02.finalState
#print axioms Chapter08.c08_a02.emptyAccepted
#print axioms Chapter08.c08_a04.surface
#print axioms Chapter08.c08_a04.canonicalBase
#print axioms Chapter08.c08_a04.canonicalSegmentation
#print axioms Chapter08.c08_a04.differentBases
#print axioms Chapter08.c08_a03.arithmetic_001
#print axioms Chapter08.c08_a03.arithmetic_002
#print axioms Chapter08.c08_a03.arithmetic_003
#print axioms Chapter08.c08_a03.deletion
#print axioms Chapter08.c08_a03.substitution1
#print axioms Chapter08.c08_a03.substitution2
#print axioms Chapter08.c08_a03.insertion
#print axioms Chapter08.c08_a03.substitution3
#print axioms Chapter08.c08_a05.arithmetic_001
#print axioms Chapter08.c08_a05.arithmetic_002
#print axioms Chapter08.c08_a05.arithmetic_003
#print axioms Chapter08.c08_a05.boundaries
#print axioms Chapter08.c08_a05.everyCell
#print axioms Chapter08.c08_a05.sourceResult
#print axioms Chapter08.c08_r01.arithmetic_001
#print axioms Chapter08.c08_r01.arithmetic_002
#print axioms Chapter08.c08_r01.arithmetic_003
#print axioms Chapter08.c08_r01.arithmetic_004
#print axioms Chapter08.c08_r01.arithmetic_005
#print axioms Chapter08.c08_r01.derivative
#print axioms Chapter08.c08_r01.critical
#print axioms Chapter08.c08_r01.signBefore
#print axioms Chapter08.c08_r01.signAfter
#print axioms Chapter08.c08_r02.arithmetic_001
#print axioms Chapter08.c08_r02.arithmetic_002
#print axioms Chapter08.c08_r02.arithmetic_003
#print axioms Chapter08.c08_r02.arithmetic_004
#print axioms Chapter08.c08_r03.arithmetic_001
#print axioms Chapter08.c08_r03.arithmetic_002
#print axioms Chapter08.c08_r03.arithmetic_003
#print axioms Chapter08.c08_r03.arithmetic_004
#print axioms Chapter08.c08_r03.arithmetic_005
#print axioms Chapter08.c08_r03.arithmetic_006
#print axioms Chapter08.c08_r03.normalized
#print axioms Chapter08.c08_r03.denominator
#print axioms Chapter08.c08_r04.arithmetic_001
#print axioms Chapter08.c08_r04.arithmetic_002
#print axioms Chapter08.c08_r04.arithmetic_003
#print axioms Chapter08.c08_r04.arithmetic_004
#print axioms Chapter08.c08_r04.arithmetic_005
#print axioms Chapter08.c08_r04.arithmetic_006
#print axioms Chapter08.c08_r04.arithmetic_007
#print axioms Chapter08.c08_r04.sigmoidBounds
#print axioms Chapter08.c08_r04.sigmoidRewrite
#print axioms Chapter08.c08_r04.oddsSolve
#print axioms Chapter08.c08_r04.roundedProbabilityExpbase
#print axioms Chapter08.c08_r04.roundedProbabilityExp
#print axioms Chapter08.c08_r04.roundedProbability
#print axioms Chapter08.c08_r04.lengthLowerExpbase
#print axioms Chapter08.c08_r04.lengthLowerExp
#print axioms Chapter08.c08_r04.lengthUpperExpbase
#print axioms Chapter08.c08_r04.lengthUpperExp
#print axioms Chapter08.c08_r04.roundedLogLength
#print axioms Chapter08.c08_r05.arithmetic_001
#print axioms Chapter08.c08_r05.arithmetic_002
#print axioms Chapter08.c08_r05.positiveDecision
#print axioms Chapter08.c08_r06.arithmetic_001
#print axioms Chapter08.c08_r06.arithmetic_002
#print axioms Chapter08.c08_r06.arithmetic_003
#print axioms Chapter08.c08_r06.arithmetic_004
#print axioms Chapter08.c08_r06.arithmetic_005
#print axioms Chapter08.c08_r06.arithmetic_006
#print axioms Chapter08.c08_r06.arithmetic_007
#print axioms Chapter08.c08_r06.arithmetic_008
#print axioms Chapter08.c08_r06.arithmetic_009
#print axioms Chapter08.c08_r06.arithmetic_010
#print axioms Chapter08.c08_r06.arithmetic_011
#print axioms Chapter08.c08_r06.arithmetic_012
#print axioms Chapter08.c08_r06.arithmetic_013
#print axioms Chapter08.c08_r06.arithmetic_014
#print axioms Chapter08.c08_r06.arithmetic_015
#print axioms Chapter08.c08_r06.Harmonic.harmonicTwo
#print axioms Chapter08.c08_r06.Harmonic.counts
#print axioms Chapter08.c08_r07.arithmetic_001
#print axioms Chapter08.c08_r07.arithmetic_002
#print axioms Chapter08.c08_r07.arithmetic_003
#print axioms Chapter08.c08_r07.arithmetic_004
#print axioms Chapter08.c08_r07.arithmetic_005
#print axioms Chapter08.c08_r07.arithmetic_006
#print axioms Chapter08.c08_r07.arithmetic_007
#print axioms Chapter08.c08_r07.arithmetic_008
#print axioms Chapter08.c08_r07.arithmetic_009
#print axioms Chapter08.c08_r07.arithmetic_010
#print axioms Chapter08.c08_r07.arithmetic_011
#print axioms Chapter08.c08_r07.arithmetic_012
#print axioms Chapter08.c08_r07.arithmetic_013
#print axioms Chapter08.c08_r07.arithmetic_014
#print axioms Chapter08.c08_r07.arithmetic_015
#print axioms Chapter08.c08_r07.zeroDenominator
#print axioms Chapter08.c08_r08.arithmetic_001
#print axioms Chapter08.c08_r08.arithmetic_002
#print axioms Chapter08.c08_r08.arithmetic_003
#print axioms Chapter08.c08_r08.arithmetic_004
#print axioms Chapter08.c08_r08.arithmetic_005
#print axioms Chapter08.c08_r08.arithmetic_006
#print axioms Chapter08.c08_r08.arithmetic_007
#print axioms Chapter08.c08_r09.arithmetic_001
#print axioms Chapter08.c08_r09.arithmetic_002
#print axioms Chapter08.c08_r09.arithmetic_003
#print axioms Chapter08.c08_r09.binaryBrier
#print axioms Chapter08.c08_r09.binaryBound
#print axioms Chapter08.c08_d01.oddsRatio
#print axioms Chapter08.c08_d01.probabilityDifference
#print axioms Chapter08.c08_d02.arithmetic_001
#print axioms Chapter08.c08_d02.arithmetic_002
#print axioms Chapter08.c08_d02.arithmetic_003
#print axioms Chapter08.c08_d02.arithmetic_004
#print axioms Chapter08.c08_d03.binary
#print axioms Chapter08.c08_d03.pooled
#print axioms Chapter08.c08_d04.arithmetic_001
#print axioms Chapter08.c08_d04.arithmetic_002
#print axioms Chapter08.c08_d04.arithmetic_003
#print axioms Chapter08.c08_d04.arithmetic_004
#print axioms Chapter08.c08_d04.arithmetic_005
#print axioms Chapter08.c08_d04.arithmetic_006
#print axioms Chapter08.c08_d04.arithmetic_007
#print axioms Chapter08.c08_p01.arithmetic_001
#print axioms Chapter08.c08_p01.sigmoidBounds
#print axioms Chapter08.c08_p01.sigmoidRewrite
#print axioms Chapter08.c08_p01.oddsSolve
#print axioms Chapter08.c08_p01.complement
#print axioms Chapter08.c08_p01.lossRewrite
#print axioms Chapter08.c08_p01.positiveLoss
#print axioms Chapter08.c08_p01.negativeLoss
#print axioms Chapter08.c08_p01.lossAtZero
#print axioms Chapter08.c08_p01.curvePositive
#print axioms Chapter08.c08_p01.curveNegative
#print axioms Chapter08.c08_p01.positiveLossBoundsLowerExpbase
#print axioms Chapter08.c08_p01.positiveLossBoundsLowerExp
#print axioms Chapter08.c08_p01.positiveLossBoundsUpperExpbase
#print axioms Chapter08.c08_p01.positiveLossBoundsUpperExp
#print axioms Chapter08.c08_p01.positiveLossBounds
#print axioms Chapter08.c08_p01.negativeLossBoundsLowerExpbase
#print axioms Chapter08.c08_p01.negativeLossBoundsLowerExp
#print axioms Chapter08.c08_p01.negativeLossBoundsUpperExpbase
#print axioms Chapter08.c08_p01.negativeLossBoundsUpperExp
#print axioms Chapter08.c08_p01.negativeLossBounds
#print axioms Chapter08.c08_p02.arithmetic_001
#print axioms Chapter08.c08_p02.arithmetic_002
#print axioms Chapter08.c08_p02.arithmetic_003
#print axioms Chapter08.c08_p02.arithmetic_004
#print axioms Chapter08.c08_p02.arithmetic_005
#print axioms Chapter08.c08_p02.arithmetic_006
#print axioms Chapter08.c08_p02.arithmetic_007
#print axioms Chapter08.c08_p02.arithmetic_008
#print axioms Chapter08.c08_p02.lossDerivative
#print axioms Chapter08.c08_p02.logisticDerivative
#print axioms Chapter08.c08_p02.curvature
#print axioms Chapter08.c08_p02.chainCoordinate
#print axioms Chapter08.c08_p02.quotientExpansion
#print axioms Chapter08.c08_p02.updatedProbabilityExpbase
#print axioms Chapter08.c08_p02.updatedProbabilityExp
#print axioms Chapter08.c08_p02.updatedProbability
#print axioms Chapter08.c08_p02.updatedScoreExpbase
#print axioms Chapter08.c08_p02.updatedScoreExp
#print axioms Chapter08.c08_p02.lossLowerExpbase
#print axioms Chapter08.c08_p02.lossLowerExp
#print axioms Chapter08.c08_p02.lossUpperExpbase
#print axioms Chapter08.c08_p02.lossUpperExp
#print axioms Chapter08.c08_p02.logTwoLowerExpbase
#print axioms Chapter08.c08_p02.logTwoLowerExp
#print axioms Chapter08.c08_p02.updatedLossBounds
#print axioms Chapter08.c08_p02.stepDecreases
#print axioms Chapter08.c08_p03.arithmetic_001
#print axioms Chapter08.c08_p03.arithmetic_002
#print axioms Chapter08.c08_p03.arithmetic_003
#print axioms Chapter08.c08_p03.arithmetic_004
#print axioms Chapter08.c08_p03.penaltySquared
#print axioms Chapter08.c08_p03.penaltyPositive
#print axioms Chapter08.c08_p03.penaltyNegative
#print axioms Chapter08.c08_p04.cancelTotal
#print axioms Chapter08.c08_p04.logRatio
#print axioms Chapter08.c08_p04.comparison
#print axioms Chapter08.c08_p05.arithmetic_001
#print axioms Chapter08.c08_p05.normalization
#print axioms Chapter08.c08_p05.shift
#print axioms Chapter08.c08_p05.expScore0base
#print axioms Chapter08.c08_p05.expScore0
#print axioms Chapter08.c08_p05.expScore1base
#print axioms Chapter08.c08_p05.expScore1
#print axioms Chapter08.c08_p05.expScore2base
#print axioms Chapter08.c08_p05.expScore2
#print axioms Chapter08.c08_p05.expScore3base
#print axioms Chapter08.c08_p05.expScore3
#print axioms Chapter08.c08_p05.expScore4base
#print axioms Chapter08.c08_p05.expScore4
#print axioms Chapter08.c08_p05.expScore5base
#print axioms Chapter08.c08_p05.expScore5
#print axioms Chapter08.c08_p05.probability0
#print axioms Chapter08.c08_p05.probability1
#print axioms Chapter08.c08_p05.probability2
#print axioms Chapter08.c08_p05.probability3
#print axioms Chapter08.c08_p05.probability4
#print axioms Chapter08.c08_p05.probability5
#print axioms Chapter08.c08_p05.operationalExp0
#print axioms Chapter08.c08_p05.operationalExp1
#print axioms Chapter08.c08_p05.operationalExp2
#print axioms Chapter08.c08_p05.operationalExp3
#print axioms Chapter08.c08_p05.operationalExp4
#print axioms Chapter08.c08_p05.operationalExp5
#print axioms Chapter08.c08_p05.operationalDenominator
#print axioms Chapter08.c08_p05.operationalProbability0
#print axioms Chapter08.c08_p05.operationalProbability4
#print axioms Chapter08.c08_p06.lossDerivative
#print axioms Chapter08.c08_p06.logisticDerivative
#print axioms Chapter08.c08_p06.curvature
#print axioms Chapter08.c08_p06.chainCoordinate
#print axioms Chapter08.c08_p06.quotientExpansion
#print axioms Chapter08.c08_p06.sigmoidOpposite
#print axioms Chapter08.c08_p06.dotStep
#print axioms Chapter08.c08_p06.positivePair
#print axioms Chapter08.c08_p06.negativePair
#print axioms Chapter08.c08_n01.table
#print axioms Chapter08.c08_n01.reluNegative
#print axioms Chapter08.c08_n01.reluPositive
#print axioms Chapter08.c08_n01.reluContinuous
#print axioms Chapter08.c08_n01.leftSlope
#print axioms Chapter08.c08_n01.rightSlope
#print axioms Chapter08.c08_n01.noAffineXor
#print axioms Chapter08.c08_n01.xorAffineInput
#print axioms Chapter08.c08_n02.arithmetic_001
#print axioms Chapter08.c08_n02.arithmetic_002
#print axioms Chapter08.c08_n02.arithmetic_003
#print axioms Chapter08.c08_n02.normalization
#print axioms Chapter08.c08_n02.shift
#print axioms Chapter08.c08_n02.root
#print axioms Chapter08.c08_n02.queryKeyProduct
#print axioms Chapter08.c08_n02.weightedValues
#print axioms Chapter08.c08_n02.projectedComparisons
#print axioms Chapter08.c08_n02.ffnExpanded
#print axioms Chapter08.c08_n03.arithmetic_001
#print axioms Chapter08.c08_n03.arithmetic_002
#print axioms Chapter08.c08_n03.sigmoidBounds
#print axioms Chapter08.c08_n03.sigmoidRewrite
#print axioms Chapter08.c08_n03.oddsSolve
#print axioms Chapter08.c08_n03.keep
#print axioms Chapter08.c08_n03.replace
#print axioms Chapter08.c08_n04.arithmetic_001
#print axioms Chapter08.c08_n04.arithmetic_002
#print axioms Chapter08.c08_n04.efficiencyTwo
#print axioms Chapter08.c08_n05.arithmetic_001
#print axioms Chapter08.c08_n05.arithmetic_002
#print axioms Chapter08.c08_n05.arithmetic_003
#print axioms Chapter08.c08_n05.arithmetic_004
#print axioms Chapter08.c08_n05.arithmetic_005
#print axioms Chapter08.c08_n05.arithmetic_006
#print axioms Chapter08.c08_n05.arithmetic_007
#print axioms Chapter08.c08_n05.arithmetic_008
#print axioms Chapter08.c08_n05.arithmetic_009
#print axioms Chapter08.c08_n05.arithmetic_010
#print axioms Chapter08.c08_n05.arithmetic_011
#print axioms Chapter08.c08_n05.arithmetic_012
#print axioms Chapter08.c08_n05.arithmetic_013
#print axioms Chapter08.c08_n05.arithmetic_014
#print axioms Chapter08.c08_n05.arithmetic_015
#print axioms Chapter08.c08_n05.arithmetic_016
#print axioms Chapter08.c08_n05.arithmetic_017
#print axioms Chapter08.c08_n05.arithmetic_018
#print axioms Chapter08.c08_n05.arithmetic_019
#print axioms Chapter08.c08_n05.tableaux
#print axioms Chapter08.c08_n05.harmonyDifference
#print axioms Chapter08.c08_n05.conditions
#print axioms Chapter08.c08_n05.strictImpossible
#print axioms Chapter08.c08_n05.marginConditions
#print axioms Chapter08.c08_n05.marginImpossible
#print axioms Chapter08.c08_n05.canceledMargins
#print axioms Chapter08.c08_n05.separation
#print axioms Chapter08.c08_n05.plotUpper
#print axioms Chapter08.c08_n05.plotLower
#print axioms Chapter08.c08_n05.upwardRegion
#print axioms Chapter08.c08_n05.downwardRegion
#print axioms Chapter08.c08_n06.arithmetic_001
#print axioms Chapter08.c08_n06.arithmetic_002
#print axioms Chapter08.c08_n06.arithmetic_003
#print axioms Chapter08.c08_n06.arithmetic_004
#print axioms Chapter08.c08_n06.publishedWindow
#print axioms Chapter08.c08_n06.contextMean
#print axioms Chapter08.c08_n06.reorderedMean
#print axioms Chapter08.c08_n07.arithmetic_001
#print axioms Chapter08.c08_n07.logRatio
#print axioms Chapter08.c08_n07.preference
#print axioms Chapter08.c08_n07.noPreference
#print axioms Chapter08.c08_n08.arithmetic_001
#print axioms Chapter08.c08_n08.nonnegative
#print axioms Chapter08.c08_n08.symmetric
#print axioms Chapter08.c08_n08.zeroDiagonal
#print axioms Chapter08.c08_n08.dotAsSquares
#print axioms Chapter08.c08_n09.arithmetic_001
#print axioms Chapter08.c08_n09.arithmetic_002
#print axioms Chapter08.c08_n09.normalized
#print axioms Chapter08.c08_n09.nonnegative
#print axioms Chapter08.c08_n09.sourceCurves
#print axioms Chapter08.c08_n09.ordering
#print axioms Chapter08.c08_n09.copyPositions
#print axioms Chapter08.c08_n09.copyMixture
