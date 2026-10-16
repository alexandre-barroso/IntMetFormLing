import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter05

namespace c05_r01
theorem arithmetic_001 : ((3-1) : ℚ) = (2) := by norm_num
theorem sourceCounts : ([2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2]:List ℕ).length=20 ∧ ([2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2]:List ℕ).count 1=4 ∧ ([2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2]:List ℕ).count 2=14 ∧ ([2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2]:List ℕ).count 3=2 := by decide +kernel
end c05_r01

namespace c05_r02
theorem arithmetic_001 : ((4*1+14*2+2*3) : ℚ) = (38) := by norm_num
theorem arithmetic_002 : ((38/20) : ℚ) = (19/10) := by norm_num
theorem arithmetic_003 : ((112/25) : ℚ) = (112/25) := by norm_num
theorem arithmetic_004 : ((23-1) : ℚ) = (22) := by norm_num
theorem arithmetic_005 : ((22/2) : ℚ) = (11) := by norm_num
theorem arithmetic_006 : ((18/2) : ℚ) = (9) := by norm_num
theorem arithmetic_007 : (((5+6)/2) : ℚ) = (11/2) := by norm_num
theorem arithmetic_008 : (((23+1)/2) : ℚ) = (12) := by norm_num
theorem arithmetic_009 : ((18/2+1) : ℚ) = (10) := by norm_num
theorem ordinalCenters : ([1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,5,6]:List ℕ)[11]?=some 1 ∧ ([1,1,2,4,5,5,5,5,5,6,7,7,8,9,10,10,10,10]:List ℕ)[8]?=some 5 ∧ ([1,1,2,4,5,5,5,5,5,6,7,7,8,9,10,10,10,10]:List ℕ)[9]?=some 6 := by decide +kernel
end c05_r02

namespace c05_r03
theorem arithmetic_001 : ((1-19/10) : ℚ) = (-9/10) := by norm_num
theorem arithmetic_002 : ((2-19/10) : ℚ) = (1/10) := by norm_num
theorem arithmetic_003 : ((3-19/10) : ℚ) = (11/10) := by norm_num
theorem arithmetic_004 : ((4*(-9/10)+14*(1/10)+2*(11/10)) : ℚ) = (0) := by norm_num
theorem arithmetic_005 : (((-9/10)^2) : ℚ) = (81/100) := by norm_num
theorem arithmetic_006 : (((1/10)^2) : ℚ) = (1/100) := by norm_num
theorem arithmetic_007 : (((11/10)^2) : ℚ) = (121/100) := by norm_num
theorem arithmetic_008 : ((4*(81/100)) : ℚ) = (324/100) := by norm_num
theorem arithmetic_009 : ((14*(1/100)) : ℚ) = (14/100) := by norm_num
theorem arithmetic_010 : ((2*(121/100)) : ℚ) = (242/100) := by norm_num
theorem arithmetic_011 : ((324/100+14/100+242/100) : ℚ) = (58/10) := by norm_num
theorem arithmetic_012 : (((58/10)/(20-1)) : ℚ) = (29/95) := by norm_num
theorem arithmetic_013 : ((30525/100000) : ℚ) < (29/95) := by norm_num
theorem arithmetic_014 : ((29/95) : ℚ) < (30535/100000) := by norm_num
theorem standardDeviation : (Real.sqrt (29/95:ℝ))^2=29/95 := Real.sq_sqrt (by norm_num)
theorem centeredSum {n:ℕ} (x:Fin n→ℝ) (m:ℝ) (h:(∑ i,x i)=(n:ℝ)*m) : (∑ i,(x i-m))=0 := by simp [Finset.sum_sub_distrib,h]
theorem morphologyDifference {n:ℕ} (a b:Fin n→ℝ) (j:Fin n) : (b-a) j=b j-a j := rfl
theorem normDifferenceNonnegative {n:ℕ} (a b:Fin n→ℝ) : 0≤Real.sqrt (∑ j,(b j-a j)^2) := Real.sqrt_nonneg _
end c05_r03

namespace c05_r04
theorem arithmetic_001 : ((90/100-10/100) : ℚ) = (80/100) := by norm_num
theorem arithmetic_002 : ((1/2) : ℚ) = (50/100) := by norm_num
theorem arithmetic_003 : ((1/4) : ℚ) = (25/100) := by norm_num
theorem arithmetic_004 : ((3/4) : ℚ) = (75/100) := by norm_num
theorem arithmetic_005 : ((3/100) : ℚ) < (14/100) := by norm_num
theorem arithmetic_006 : ((8/100) : ℚ) < (45/100) := by norm_num
theorem arithmetic_007 : ((2668/10000) : ℚ) < (9252/10000) := by norm_num
end c05_r04

namespace c05_r05
theorem arithmetic_001 : ((|(6/10-4/10)|) : ℚ) = (2/10) := by norm_num
theorem arithmetic_002 : ((|(2/10-3/10)|) : ℚ) = (1/10) := by norm_num
theorem arithmetic_003 : (((2/10+1/10+1/10)/2) : ℚ) = (1/5) := by norm_num
theorem arithmetic_004 : ((4/10+3/10+3/10) : ℚ) = (1) := by norm_num
theorem arithmetic_005 : ((6/10+2/10+2/10) : ℚ) = (1) := by norm_num
theorem arithmetic_006 : ((998/1000) : ℚ) > (676/1000) := by norm_num
end c05_r05

namespace c05_r06
theorem arithmetic_001 : ((4/20+14/20+2/20) : ℚ) = (1) := by norm_num
theorem arithmetic_002 : (((4/20)*1+(14/20)*2+(2/20)*3) : ℚ) = (19/10) := by norm_num
end c05_r06

namespace c05_r07
theorem arithmetic_001 : ((38333/10000-19/10) : ℚ) = (19333/10000) := by norm_num
theorem arithmetic_002 : ((19333/10000/(21562/10000)) : ℚ) = (19333/21562) := by norm_num
theorem arithmetic_003 : ((89655/100000) : ℚ) < (19333/21562) := by norm_num
theorem arithmetic_004 : ((19333/21562) : ℚ) < (89665/100000) := by norm_num
end c05_r07

namespace c05_r08
theorem meanLoss (x y a:ℝ) : (x-a)^2+(y-a)^2=(x-(x+y)/2)^2+(y-(x+y)/2)^2+2*(a-(x+y)/2)^2 := by ring
theorem meanMinimum (x y a:ℝ) : (x-(x+y)/2)^2+(y-(x+y)/2)^2≤(x-a)^2+(y-a)^2 := by rw [meanLoss]; nlinarith [sq_nonneg (a-(x+y)/2)]
theorem expandSquare (c d:ℝ) : (c+d)^2=c^2+2*c*d+d^2 := by ring
theorem symmetricLoss (d h:ℝ) : (d-h)^2+(-d-h)^2=2*d^2+2*h^2 := by ring
theorem midRecover (x y:ℝ) : (x+y)/2+(x-y)/2=x ∧ (x+y)/2-(x-y)/2=y := by constructor <;> ring
theorem shiftedUpper (m d h:ℝ) : (m+d)-(m+h)=d-h := by ring
theorem shiftedLower (m d h:ℝ) : (m-d)-(m+h)= -d-h := by ring
theorem recoverCandidate (a m h:ℝ) (hh:h=a-m) : a=m+h := by linarith
end c05_r08

namespace c05_p01
theorem arithmetic_001 : ((180+3) : ℚ) = (183) := by norm_num
theorem arithmetic_002 : ((20+153) : ℚ) = (173) := by norm_num
theorem arithmetic_003 : ((180+20) : ℚ) = (200) := by norm_num
theorem arithmetic_004 : ((3+153) : ℚ) = (156) := by norm_num
theorem arithmetic_005 : ((183+173) : ℚ) = (356) := by norm_num
theorem arithmetic_006 : ((200+156) : ℚ) = (356) := by norm_num
theorem arithmetic_007 : ((183*200) : ℚ) = (36600) := by norm_num
theorem arithmetic_008 : ((183*156) : ℚ) = (28548) := by norm_num
theorem arithmetic_009 : ((173*200) : ℚ) = (34600) := by norm_num
theorem arithmetic_010 : ((173*156) : ℚ) = (26988) := by norm_num
theorem arithmetic_011 : (((36600+28548)/356) : ℚ) = (183) := by norm_num
theorem arithmetic_012 : (((36600+34600)/356) : ℚ) = (200) := by norm_num
theorem arithmetic_013 : ((102805/1000) : ℚ) < (36600/356) := by norm_num
theorem arithmetic_014 : ((36600/356) : ℚ) < (102815/1000) := by norm_num
theorem arithmetic_015 : ((80185/1000) : ℚ) < (28548/356) := by norm_num
theorem arithmetic_016 : ((28548/356) : ℚ) < (80195/1000) := by norm_num
theorem rowTotal (r c d:ℝ) (h:c+d≠0) : r*c/(c+d)+r*d/(c+d)=r := by field_simp <;> ring
end c05_p01

namespace c05_p02
theorem arithmetic_001 : ((29+13) : ℚ) = (42) := by norm_num
theorem arithmetic_002 : ((123+31612) : ℚ) = (31735) := by norm_num
theorem arithmetic_003 : ((29+123) : ℚ) = (152) := by norm_num
theorem arithmetic_004 : ((13+31612) : ℚ) = (31625) := by norm_num
theorem arithmetic_005 : ((42+31735) : ℚ) = (31777) := by norm_num
theorem arithmetic_006 : ((42*152) : ℚ) = (6384) := by norm_num
theorem arithmetic_007 : ((42*31625) : ℚ) = (1328250) := by norm_num
theorem arithmetic_008 : ((31735*152) : ℚ) = (4823720) := by norm_num
theorem arithmetic_009 : ((31735*31625) : ℚ) = (1003619375) := by norm_num
theorem arithmetic_010 : ((29*31777/6384) : ℚ) = (921533/6384) := by norm_num
theorem arithmetic_011 : ((42*(152+31625)/31777) : ℚ) = (42) := by norm_num
theorem arithmetic_012 : ((152*(42+31735)/31777) : ℚ) = (152) := by norm_num
theorem arithmetic_013 : ((123*31777) : ℚ) = (3908571) := by norm_num
theorem arithmetic_014 : ((31612*31777) : ℚ) = (1004534524) := by norm_num
theorem arithmetic_015 : ((1441951/10000-151830/10000-258760/10000+288122/10000) : ℚ) = (1319483/10000) := by norm_num
theorem arithmetic_016 : ((2*(1319483/10000)) : ℚ) = (2638966/10000) := by norm_num
theorem arithmetic_017 : ((6384/31777) : ℚ) < (1) := by norm_num
theorem arithmetic_018 : ((144) : ℚ) < (921533/6384) := by norm_num
theorem arithmetic_019 : ((921533/6384) : ℚ) < (145) := by norm_num
theorem zeroTermLimit (E:ℝ) : Filter.Tendsto (fun x:ℝ=>x*Real.log x-x*Real.log E) (nhds 0) (nhds 0) := by
 have h : Continuous (fun x:ℝ=>x*Real.log x-x*Real.log E) := Real.continuous_mul_log.fun_sub (continuous_id.fun_mul continuous_const)
 simpa using h.tendsto (0:ℝ)
theorem positiveTermIdentity (x E:ℝ) (hx:0<x) (hE:0<E) : x*Real.log (x/E)=x*Real.log x-x*Real.log E := by rw [Real.log_div (ne_of_gt hx) (ne_of_gt hE)]; ring
theorem fourContributions (a b c d:ℝ) : 2*(a+b+c+d)=2*a+2*b+2*c+2*d := by ring
lemma logEnclosure (x a b:ℝ) (n:ℕ) (hx:|x|<1)
 (ha:a<2*((∑ i ∈ Finset.range n,x^(2*i+1)/(2*i+1))-|x|^(2*n+1)/(1-x^2)))
 (hb:2*((∑ i ∈ Finset.range n,x^(2*i+1)/(2*i+1))+|x|^(2*n+1)/(1-x^2))<b) :
 a<Real.log ((1+x)/(1-x)) ∧ Real.log ((1+x)/(1-x))<b := by
 have h:=abs_le.mp (Real.sum_range_sub_log_div_le hx n)
 constructor <;> linarith [h.1,h.2]
theorem logBound0 : (69314718053/100000000000:ℝ)<Real.log (2/1:ℝ) ∧ Real.log (2/1:ℝ)<(34657359029/50000000000:ℝ) := by
 have h:=logEnclosure (1/3:ℝ) (69314718053/100000000000:ℝ) (34657359029/50000000000:ℝ) 12 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
theorem logBound1 : (2404269271/20000000000:ℝ)<Real.log (921533/817152:ℝ) ∧ Real.log (921533/817152:ℝ)<(300533659/2500000000:ℝ) := by
 have h:=logEnclosure (104381/1738685:ℝ) (2404269271/20000000000:ℝ) (300533659/2500000000:ℝ) 5 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
theorem logBound2 : (21836891089/100000000000:ℝ)<Real.log (826202/664125:ℝ) ∧ Real.log (826202/664125:ℝ)<(10918445547/50000000000:ℝ) := by
 have h:=logEnclosure (162077/1490327:ℝ) (21836891089/100000000000:ℝ) (10918445547/50000000000:ℝ) 6 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
theorem logBound3 : (-1051867903/5000000000:ℝ)<Real.log (3908571/4823720:ℝ) ∧ Real.log (3908571/4823720:ℝ)<(-4207471611/20000000000:ℝ) := by
 have h:=logEnclosure (-915149/8732291:ℝ) (-1051867903/5000000000:ℝ) (-4207471611/20000000000:ℝ) 6 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
theorem logBound4 : (91143317/100000000000:ℝ)<Real.log (1004534524/1003619375:ℝ) ∧ Real.log (1004534524/1003619375:ℝ)<(45571661/50000000000:ℝ) := by
 have h:=logEnclosure (915149/2008153899:ℝ) (91143317/100000000000:ℝ) (45571661/50000000000:ℝ) 2 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
theorem logFirst : Real.log (921533/6384:ℝ)=7*Real.log 2+Real.log (921533/817152:ℝ) := by
 calc
  Real.log (921533/6384:ℝ)=Real.log ((2:ℝ)^7*(921533/817152)) := by congr 1 <;> norm_num
  _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num),Real.log_pow]; norm_num
theorem logSecond : Real.log (413101/1328250:ℝ)=Real.log (826202/664125:ℝ)-2*Real.log 2 := by
 calc
  Real.log (413101/1328250:ℝ)=Real.log ((826202/664125:ℝ)/(2:ℝ)^2) := by congr 1 <;> norm_num
  _ = _ := by rw [Real.log_div (by norm_num) (by norm_num),Real.log_pow]; norm_num
theorem termBounds :
 (14419505/100000:ℝ)<29*Real.log (921533/6384:ℝ) ∧ 29*Real.log (921533/6384:ℝ)<14419515/100000 ∧
 (-1518305/100000:ℝ)<13*Real.log (413101/1328250:ℝ) ∧ 13*Real.log (413101/1328250:ℝ)< -1518295/100000 ∧
 (-2587605/100000:ℝ)<123*Real.log (3908571/4823720:ℝ) ∧ 123*Real.log (3908571/4823720:ℝ)< -2587595/100000 ∧
 (2881215/100000:ℝ)<31612*Real.log (1004534524/1003619375:ℝ) ∧ 31612*Real.log (1004534524/1003619375:ℝ)<2881225/100000 := by
 have h0:=logBound0;have h1:=logBound1;have h2:=logBound2;have h3:=logBound3;have h4:=logBound4
 rw [logFirst,logSecond]
 constructor; nlinarith [h0.1,h1.1]
 constructor; nlinarith [h0.2,h1.2]
 constructor; nlinarith [h0.2,h2.1]
 constructor; nlinarith [h0.1,h2.2]
 constructor; nlinarith [h3.1]
 constructor; nlinarith [h3.2]
 constructor; nlinarith [h4.1]
 nlinarith [h4.2]
theorem publishedRounding :
 (263895/1000:ℝ)<2*(29*Real.log (921533/6384:ℝ)+13*Real.log (413101/1328250:ℝ)+123*Real.log (3908571/4823720:ℝ)+31612*Real.log (1004534524/1003619375:ℝ)) ∧
 2*(29*Real.log (921533/6384:ℝ)+13*Real.log (413101/1328250:ℝ)+123*Real.log (3908571/4823720:ℝ)+31612*Real.log (1004534524/1003619375:ℝ))<263905/1000 := by
 rcases termBounds with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
 constructor <;> linarith

end c05_p02

namespace c05_p03
theorem expectedScale (k r c N:ℝ) (hk:k≠0) (hN:N≠0) : (k*r)*(k*c)/(k*N)=k*(r*c/N) := by field_simp <;> ring
theorem ratioScale (k o e:ℝ) (hk:k≠0) : (k*o)/(k*e)=o/e := by exact mul_div_mul_left o e hk
theorem statisticScale (k o e:ℝ) (hk:k≠0) : 2*(k*o)*Real.log ((k*o)/(k*e))=k*(2*o*Real.log (o/e)) := by rw [ratioScale k o e hk]; ring
end c05_p03

namespace c05_d01
theorem arithmetic_001 : ((4+14+2) : ℚ) = (20) := by norm_num
theorem arithmetic_002 : ((4/20+14/20+2/20) : ℚ) = (1) := by norm_num
theorem arithmetic_003 : ((4+14) : ℚ) = (18) := by norm_num
theorem arithmetic_004 : ((18/20) : ℚ) = (9/10) := by norm_num
end c05_d01

namespace c05_d02
theorem arithmetic_001 : ((112-20) : ℚ) = (92) := by norm_num
theorem arithmetic_002 : ((25-1) : ℚ) = (24) := by norm_num
theorem arithmetic_003 : ((92/24) : ℚ) = (23/6) := by norm_num
theorem arithmetic_004 : ((57-14) : ℚ) = (43) := by norm_num
theorem arithmetic_005 : ((20-1) : ℚ) = (19) := by norm_num
theorem arithmetic_006 : ((23/6) : ℚ) > (19/10) := by norm_num
theorem arithmetic_007 : ((2255/1000) : ℚ) < (43/19) := by norm_num
theorem arithmetic_008 : ((43/19) : ℚ) < (2265/1000) := by norm_num
end c05_d02

namespace c05_d03
theorem arithmetic_001 : ((1-3/10) : ℚ) = (7/10) := by norm_num
theorem arithmetic_002 : (((1/5)/(7/10)) : ℚ) = (2/7) := by norm_num
theorem arithmetic_003 : ((28565/100000) : ℚ) < (2/7) := by norm_num
theorem arithmetic_004 : ((2/7) : ℚ) < (28575/100000) := by norm_num
end c05_d03

namespace c05_d04
theorem arithmetic_001 : (((5+6)/2) : ℚ) = (11/2) := by norm_num
theorem arithmetic_002 : ((5) : ℚ) < (11/2) := by norm_num
theorem arithmetic_003 : ((11/2) : ℚ) < (6) := by norm_num
end c05_d04
end Chapter05
#print axioms Chapter05.c05_r01.arithmetic_001
#print axioms Chapter05.c05_r01.sourceCounts
#print axioms Chapter05.c05_r02.arithmetic_001
#print axioms Chapter05.c05_r02.arithmetic_002
#print axioms Chapter05.c05_r02.arithmetic_003
#print axioms Chapter05.c05_r02.arithmetic_004
#print axioms Chapter05.c05_r02.arithmetic_005
#print axioms Chapter05.c05_r02.arithmetic_006
#print axioms Chapter05.c05_r02.arithmetic_007
#print axioms Chapter05.c05_r02.arithmetic_008
#print axioms Chapter05.c05_r02.arithmetic_009
#print axioms Chapter05.c05_r02.ordinalCenters
#print axioms Chapter05.c05_r03.arithmetic_001
#print axioms Chapter05.c05_r03.arithmetic_002
#print axioms Chapter05.c05_r03.arithmetic_003
#print axioms Chapter05.c05_r03.arithmetic_004
#print axioms Chapter05.c05_r03.arithmetic_005
#print axioms Chapter05.c05_r03.arithmetic_006
#print axioms Chapter05.c05_r03.arithmetic_007
#print axioms Chapter05.c05_r03.arithmetic_008
#print axioms Chapter05.c05_r03.arithmetic_009
#print axioms Chapter05.c05_r03.arithmetic_010
#print axioms Chapter05.c05_r03.arithmetic_011
#print axioms Chapter05.c05_r03.arithmetic_012
#print axioms Chapter05.c05_r03.arithmetic_013
#print axioms Chapter05.c05_r03.arithmetic_014
#print axioms Chapter05.c05_r03.standardDeviation
#print axioms Chapter05.c05_r03.centeredSum
#print axioms Chapter05.c05_r03.morphologyDifference
#print axioms Chapter05.c05_r03.normDifferenceNonnegative
#print axioms Chapter05.c05_r04.arithmetic_001
#print axioms Chapter05.c05_r04.arithmetic_002
#print axioms Chapter05.c05_r04.arithmetic_003
#print axioms Chapter05.c05_r04.arithmetic_004
#print axioms Chapter05.c05_r04.arithmetic_005
#print axioms Chapter05.c05_r04.arithmetic_006
#print axioms Chapter05.c05_r04.arithmetic_007
#print axioms Chapter05.c05_r05.arithmetic_001
#print axioms Chapter05.c05_r05.arithmetic_002
#print axioms Chapter05.c05_r05.arithmetic_003
#print axioms Chapter05.c05_r05.arithmetic_004
#print axioms Chapter05.c05_r05.arithmetic_005
#print axioms Chapter05.c05_r05.arithmetic_006
#print axioms Chapter05.c05_r06.arithmetic_001
#print axioms Chapter05.c05_r06.arithmetic_002
#print axioms Chapter05.c05_r07.arithmetic_001
#print axioms Chapter05.c05_r07.arithmetic_002
#print axioms Chapter05.c05_r07.arithmetic_003
#print axioms Chapter05.c05_r07.arithmetic_004
#print axioms Chapter05.c05_r08.meanLoss
#print axioms Chapter05.c05_r08.meanMinimum
#print axioms Chapter05.c05_r08.expandSquare
#print axioms Chapter05.c05_r08.symmetricLoss
#print axioms Chapter05.c05_r08.midRecover
#print axioms Chapter05.c05_r08.shiftedUpper
#print axioms Chapter05.c05_r08.shiftedLower
#print axioms Chapter05.c05_r08.recoverCandidate
#print axioms Chapter05.c05_p01.arithmetic_001
#print axioms Chapter05.c05_p01.arithmetic_002
#print axioms Chapter05.c05_p01.arithmetic_003
#print axioms Chapter05.c05_p01.arithmetic_004
#print axioms Chapter05.c05_p01.arithmetic_005
#print axioms Chapter05.c05_p01.arithmetic_006
#print axioms Chapter05.c05_p01.arithmetic_007
#print axioms Chapter05.c05_p01.arithmetic_008
#print axioms Chapter05.c05_p01.arithmetic_009
#print axioms Chapter05.c05_p01.arithmetic_010
#print axioms Chapter05.c05_p01.arithmetic_011
#print axioms Chapter05.c05_p01.arithmetic_012
#print axioms Chapter05.c05_p01.arithmetic_013
#print axioms Chapter05.c05_p01.arithmetic_014
#print axioms Chapter05.c05_p01.arithmetic_015
#print axioms Chapter05.c05_p01.arithmetic_016
#print axioms Chapter05.c05_p01.rowTotal
#print axioms Chapter05.c05_p02.arithmetic_001
#print axioms Chapter05.c05_p02.arithmetic_002
#print axioms Chapter05.c05_p02.arithmetic_003
#print axioms Chapter05.c05_p02.arithmetic_004
#print axioms Chapter05.c05_p02.arithmetic_005
#print axioms Chapter05.c05_p02.arithmetic_006
#print axioms Chapter05.c05_p02.arithmetic_007
#print axioms Chapter05.c05_p02.arithmetic_008
#print axioms Chapter05.c05_p02.arithmetic_009
#print axioms Chapter05.c05_p02.arithmetic_010
#print axioms Chapter05.c05_p02.arithmetic_011
#print axioms Chapter05.c05_p02.arithmetic_012
#print axioms Chapter05.c05_p02.arithmetic_013
#print axioms Chapter05.c05_p02.arithmetic_014
#print axioms Chapter05.c05_p02.arithmetic_015
#print axioms Chapter05.c05_p02.arithmetic_016
#print axioms Chapter05.c05_p02.arithmetic_017
#print axioms Chapter05.c05_p02.arithmetic_018
#print axioms Chapter05.c05_p02.arithmetic_019
#print axioms Chapter05.c05_p02.zeroTermLimit
#print axioms Chapter05.c05_p02.positiveTermIdentity
#print axioms Chapter05.c05_p02.fourContributions
#print axioms Chapter05.c05_p02.logBound0
#print axioms Chapter05.c05_p02.logBound1
#print axioms Chapter05.c05_p02.logBound2
#print axioms Chapter05.c05_p02.logBound3
#print axioms Chapter05.c05_p02.logBound4
#print axioms Chapter05.c05_p02.logFirst
#print axioms Chapter05.c05_p02.logSecond
#print axioms Chapter05.c05_p02.termBounds
#print axioms Chapter05.c05_p02.publishedRounding
#print axioms Chapter05.c05_p03.expectedScale
#print axioms Chapter05.c05_p03.ratioScale
#print axioms Chapter05.c05_p03.statisticScale
#print axioms Chapter05.c05_d01.arithmetic_001
#print axioms Chapter05.c05_d01.arithmetic_002
#print axioms Chapter05.c05_d01.arithmetic_003
#print axioms Chapter05.c05_d01.arithmetic_004
#print axioms Chapter05.c05_d02.arithmetic_001
#print axioms Chapter05.c05_d02.arithmetic_002
#print axioms Chapter05.c05_d02.arithmetic_003
#print axioms Chapter05.c05_d02.arithmetic_004
#print axioms Chapter05.c05_d02.arithmetic_005
#print axioms Chapter05.c05_d02.arithmetic_006
#print axioms Chapter05.c05_d02.arithmetic_007
#print axioms Chapter05.c05_d02.arithmetic_008
#print axioms Chapter05.c05_d03.arithmetic_001
#print axioms Chapter05.c05_d03.arithmetic_002
#print axioms Chapter05.c05_d03.arithmetic_003
#print axioms Chapter05.c05_d03.arithmetic_004
#print axioms Chapter05.c05_d04.arithmetic_001
#print axioms Chapter05.c05_d04.arithmetic_002
#print axioms Chapter05.c05_d04.arithmetic_003
