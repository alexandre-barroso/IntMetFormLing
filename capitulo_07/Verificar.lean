import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter07

namespace c07_r01
theorem arithmetic_001 : ((7/10-5/10) : ℚ) = (2/10) := by norm_num
theorem arithmetic_002 : ((2/10) : ℚ) = (1/5) := by norm_num
theorem sourceTotals : ([1, 1, 1, 0, 1, 0, 1, 1, 0, 1]:List ℚ).sum=7 ∧ ([1, 0, 1, 1, 0, 1, 0, 1, 0, 0]:List ℚ).sum=5 := by norm_num
end c07_r01

namespace c07_r02
theorem arithmetic_001 : ((1-1) : ℚ) = (0) := by norm_num
theorem arithmetic_002 : ((1-0) : ℚ) = (1) := by norm_num
theorem arithmetic_003 : ((0-1) : ℚ) = (-1) := by norm_num
theorem swap (a b : ℝ) : b-a=-(a-b) := by ring
end c07_r02

namespace c07_r03
theorem fraction_bounds (K N:ℝ) (hN:0<N) (hK:0≤K) (h:K≤N) : 0≤K/N ∧ K/N≤1 := ⟨div_nonneg hK (le_of_lt hN), (div_le_one hN).2 h⟩
end c07_r03

namespace c07_r04
theorem arithmetic_001 : ((1000*(25/10)/100) : ℚ) = (25) := by norm_num
theorem arithmetic_002 : ((1000*(1/40)) : ℚ) = (25) := by norm_num
theorem arithmetic_003 : ((1000-25-25) : ℚ) = (950) := by norm_num
theorem arithmetic_004 : ((950/1000) : ℚ) = (19/20) := by norm_num
theorem arithmetic_005 : ((25+1) : ℚ) = (26) := by norm_num
theorem arithmetic_006 : ((1000-25) : ℚ) = (975) := by norm_num
theorem arithmetic_007 : ((1000-25+1) : ℚ) = (976) := by norm_num
theorem arithmetic_008 : ((975-26+1) : ℚ) = (950) := by norm_num

theorem retainedPositions : (Finset.Icc 26 975).card=950 := by norm_num
end c07_r04

namespace c07_r05
theorem arithmetic_001 : ((6/10-6/10) : ℚ) = (0) := by norm_num
theorem arithmetic_002 : ((6/10-7/10) : ℚ) = (-1/10) := by norm_num
theorem arithmetic_003 : ((2*(2/10)) : ℚ) = (4/10) := by norm_num
theorem arithmetic_004 : ((47/10000) : ℚ) < (1/100) := by norm_num
theorem centeredThreshold (d star:ℝ) : star-d≥d ↔ star≥2*d := by constructor <;> intro h <;> linarith
def resample1 : List (ℚ×ℚ) := [(1,0),(1,1),(1,0),(0,1),(0,1),(1,0),(0,1),(1,1),(0,0),(1,1)]
theorem resample1Totals : (resample1.map Prod.fst).sum=6 ∧ (resample1.map Prod.snd).sum=6 := by norm_num [resample1]
def resample2 : List (ℚ×ℚ) := [(1,0),(1,1),(0,0),(0,1),(0,1),(1,1),(0,1),(1,0),(1,1),(1,1)]
theorem resample2Totals : (resample2.map Prod.fst).sum=6 ∧ (resample2.map Prod.snd).sum=7 := by norm_num [resample2]
end c07_r05

namespace c07_r06
theorem arithmetic_001 : (((0+0+0+1+1+1)/6) : ℚ) = (1/2) := by norm_num
theorem arithmetic_002 : (((233+204+242+130+112+142)/6) : ℚ) = (1063/6) := by norm_num
theorem arithmetic_003 : ((233+204+242) : ℚ) = (679) := by norm_num
theorem arithmetic_004 : ((130+112+142) : ℚ) = (384) := by norm_num
theorem arithmetic_005 : ((3*(-1/2)^2+3*(1/2)^2) : ℚ) = (3/2) := by norm_num
theorem arithmetic_006 : ((679-3*(1063/6)) : ℚ) = (295/2) := by norm_num
theorem arithmetic_007 : ((384-3*(1063/6)) : ℚ) = (-295/2) := by norm_num
theorem arithmetic_008 : (((-1/2)*(295/2)+(1/2)*(-295/2)) : ℚ) = (-295/2) := by norm_num
theorem sumProducts : (([0,0,0,1,1,1]:List ℚ).zipWith (fun x y => (x-1/2)*(y-1063/6)) [233,204,242,130,112,142]).sum = -295/2 := by norm_num
end c07_r06

namespace c07_r07
theorem arithmetic_001 : (((-295/2)/(3/2)) : ℚ) = (-295/3) := by norm_num
theorem arithmetic_002 : ((1063/6-(-295/3)*(1/2)) : ℚ) = (679/3) := by norm_num
theorem arithmetic_003 : (((679-295)/3) : ℚ) = (128) := by norm_num
theorem arithmetic_004 : ((233-679/3) : ℚ) = (20/3) := by norm_num
theorem arithmetic_005 : ((204-679/3) : ℚ) = (-67/3) := by norm_num
theorem arithmetic_006 : ((242-679/3) : ℚ) = (47/3) := by norm_num
theorem arithmetic_007 : ((130-128) : ℚ) = (2) := by norm_num
theorem arithmetic_008 : ((112-128) : ℚ) = (-16) := by norm_num
theorem arithmetic_009 : ((142-128) : ℚ) = (14) := by norm_num
theorem arithmetic_010 : (((20-67+47)/3) : ℚ) = (0) := by norm_num
theorem arithmetic_011 : ((2-16+14) : ℚ) = (0) := by norm_num
theorem arithmetic_012 : ((400+4489+2209) : ℚ) = (7098) := by norm_num
theorem arithmetic_013 : ((7098/9) : ℚ) = (2366/3) := by norm_num
theorem arithmetic_014 : ((4+256+196) : ℚ) = (456) := by norm_num
theorem arithmetic_015 : ((2366/3+456) : ℚ) = (3734/3) := by norm_num
end c07_r07

namespace c07_r08
theorem arithmetic_001 : ((233^2+204^2+242^2+130^2+112^2+142^2) : ℚ) = (204077) := by norm_num
theorem arithmetic_002 : ((1063^2) : ℚ) = (1129969) := by norm_num
theorem arithmetic_003 : ((204077*6) : ℚ) = (1224462) := by norm_num
theorem arithmetic_004 : ((204077-6*(1063/6)^2) : ℚ) = (94493/6) := by norm_num
theorem arithmetic_005 : ((1-(3734/3)/(94493/6)) : ℚ) = (87025/94493) := by norm_num
theorem arithmetic_006 : ((295^2) : ℚ) = (87025) := by norm_num
theorem arithmetic_007 : (((3/2)*(94493/6)) : ℚ) = (94493/4) := by norm_num
theorem arithmetic_008 : ((233^2) : ℚ) = (54289) := by norm_num
theorem arithmetic_009 : ((204^2) : ℚ) = (41616) := by norm_num
theorem arithmetic_010 : ((242^2) : ℚ) = (58564) := by norm_num
theorem arithmetic_011 : ((130^2) : ℚ) = (16900) := by norm_num
theorem arithmetic_012 : ((112^2) : ℚ) = (12544) := by norm_num
theorem arithmetic_013 : ((142^2) : ℚ) = (20164) := by norm_num
theorem arithmetic_014 : ((54289+41616+58564+16900+12544+20164) : ℚ) = (204077) := by norm_num
theorem arithmetic_015 : ((6*(1063/6)) : ℚ) = (1063) := by norm_num
theorem arithmetic_016 : ((87025/94493) : ℚ) ≥ (9205/10000) := by norm_num
theorem arithmetic_017 : ((87025/94493) : ℚ) < (9215/10000) := by norm_num
theorem correlationSquare : ((-295:ℝ)/Real.sqrt 94493)^2 = 87025/94493 := by rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤94493)]; norm_num
theorem squareExpansion {n : ℕ} (f : Fin n → ℝ) (m : ℝ) :
 (∑ i, (f i-m)^2) = (∑ i, (f i)^2) - 2*m*(∑ i, f i) + (n:ℝ)*m^2 := by
 simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
  ←Finset.sum_mul, ←Finset.mul_sum, Finset.sum_const,
  Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
 ring
theorem centeredSquares {n : ℕ} (f : Fin n → ℝ) (m : ℝ)
 (hm : (∑ i, f i) = (n:ℝ)*m) :
 (∑ i, (f i-m)^2) = (∑ i, (f i)^2) - (n:ℝ)*m^2 := by
 rw [squareExpansion,hm]
 ring

end c07_r08

namespace c07_r09
theorem arithmetic_001 : ((401454/100-61557/100) : ℚ) = (339897/100) := by norm_num
theorem arithmetic_002 : ((61557/100) : ℚ) < (401454/100) := by norm_num
end c07_r09

namespace c07_d01
theorem arithmetic_001 : ((3+4+2+1) : ℚ) = (10) := by norm_num
theorem arithmetic_002 : (((4-2)/10) : ℚ) = (1/5) := by norm_num
theorem pairedDiffs : ([1, 1, 1, 0, 1, 0, 1, 1, 0, 1]:List ℚ).zipWith (· - ·) [1, 0, 1, 1, 0, 1, 0, 1, 0, 0]=[0,1,0,-1,1,-1,1,0,0,1] := by norm_num
theorem pairedMean (sA sB n:ℝ) : (sA-sB)/n=sA/n-sB/n := sub_div _ _ _
end c07_d01

namespace c07_d02
theorem arithmetic_001 : (((30*1+70*0)/100) : ℚ) = (3/10) := by norm_num
theorem arithmetic_002 : ((1-3/10) : ℚ) = (7/10) := by norm_num
theorem arithmetic_003 : ((0-3/10) : ℚ) = (-3/10) := by norm_num
theorem arithmetic_004 : ((30*(7/10)^2+70*(-3/10)^2) : ℚ) = (21) := by norm_num
theorem arithmetic_005 : ((21/99) : ℚ) = (7/33) := by norm_num
theorem arithmetic_006 : (((7/33)/100) : ℚ) = (7/3300) := by norm_num
theorem seSquare : (Real.sqrt (7/3300))^2=(7/3300:ℝ) := Real.sq_sqrt (by norm_num)
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MeanOps
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
theorem independentMeanVariance {n : ℕ} (hn : 0<n)
    (X : Fin n → Ω → ℝ) (v : ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hi : ∀ i j, i≠j → IndepFun (X i) (X j) μ)
    (hv : ∀ i, variance (X i) μ = v) :
    variance (fun ω => (1/(n:ℝ)) * ∑ i : Fin n, X i ω) μ = v/(n:ℝ) := by
 have hs : variance (fun ω => ∑ i : Fin n, X i ω) μ = ∑ i : Fin n, variance (X i) μ := by
  have hf : (fun ω => ∑ i : Fin n, X i ω) = ∑ i : Fin n, X i := by
   funext ω
   simp
  rw [hf]
  exact ProbabilityTheory.IndepFun.variance_sum (s:=Finset.univ)
    (fun i _ => hX i) (fun i _ j _ hij => hi i j hij)
 rw [variance_const_mul, hs]
 simp_rw [hv]
 simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
 have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
 field_simp
end MeanOps
end c07_d02

namespace c07_d03
theorem arithmetic_001 : (((14+23+35+48+52+67)/6) : ℚ) = (239/6) := by norm_num
theorem arithmetic_002 : (((252+244+240+233+212+204)/6) : ℚ) = (1385/6) := by norm_num
theorem arithmetic_003 : (((-10519/6)/(11561/6)) : ℚ) = (-10519/11561) := by norm_num
theorem arithmetic_004 : ((1385/6-(-10519/11561)*(239/6)) : ℚ) = (3087671/11561) := by norm_num
theorem arithmetic_005 : ((3087671/11561-(10519/11561)*(239/6)) : ℚ) = (1385/6) := by norm_num
theorem arithmetic_006 : ((14^2) : ℚ) = (196) := by norm_num
theorem arithmetic_007 : ((23^2) : ℚ) = (529) := by norm_num
theorem arithmetic_008 : ((35^2) : ℚ) = (1225) := by norm_num
theorem arithmetic_009 : ((48^2) : ℚ) = (2304) := by norm_num
theorem arithmetic_010 : ((52^2) : ℚ) = (2704) := by norm_num
theorem arithmetic_011 : ((67^2) : ℚ) = (4489) := by norm_num
theorem arithmetic_012 : ((196+529+1225+2304+2704+4489) : ℚ) = (11447) := by norm_num
theorem arithmetic_013 : ((14*252) : ℚ) = (3528) := by norm_num
theorem arithmetic_014 : ((23*244) : ℚ) = (5612) := by norm_num
theorem arithmetic_015 : ((35*240) : ℚ) = (8400) := by norm_num
theorem arithmetic_016 : ((48*233) : ℚ) = (11184) := by norm_num
theorem arithmetic_017 : ((52*212) : ℚ) = (11024) := by norm_num
theorem arithmetic_018 : ((67*204) : ℚ) = (13668) := by norm_num
theorem arithmetic_019 : ((3528+5612+8400+11184+11024+13668) : ℚ) = (53416) := by norm_num
theorem arithmetic_020 : ((239^2) : ℚ) = (57121) := by norm_num
theorem arithmetic_021 : ((11447*6) : ℚ) = (68682) := by norm_num
theorem arithmetic_022 : ((68682-57121) : ℚ) = (11561) := by norm_num
theorem arithmetic_023 : ((11447-57121/6) : ℚ) = (11561/6) := by norm_num
theorem arithmetic_024 : ((239*1385) : ℚ) = (331015) := by norm_num
theorem arithmetic_025 : ((53416*6) : ℚ) = (320496) := by norm_num
theorem arithmetic_026 : ((320496-331015) : ℚ) = (-10519) := by norm_num
theorem arithmetic_027 : ((53416-331015/6) : ℚ) = (-10519/6) := by norm_num
theorem arithmetic_028 : (((-10519/6)*(6/11561)) : ℚ) = (-10519/11561) := by norm_num
theorem arithmetic_029 : ((1385*11561) : ℚ) = (16011985) := by norm_num
theorem arithmetic_030 : ((10519*239) : ℚ) = (2514041) := by norm_num
theorem arithmetic_031 : ((6*11561) : ℚ) = (69366) := by norm_num
theorem arithmetic_032 : ((16011985+2514041) : ℚ) = (18526026) := by norm_num
theorem arithmetic_033 : ((18526026/69366) : ℚ) = (3087671/11561) := by norm_num
theorem arithmetic_034 : ((3087671/11561) : ℚ) ≥ (26707645/100000) := by norm_num
theorem arithmetic_035 : ((3087671/11561) : ℚ) < (26707655/100000) := by norm_num
theorem arithmetic_036 : ((-10519/11561) : ℚ) ≥ (-90995/100000) := by norm_num
theorem arithmetic_037 : ((-10519/11561) : ℚ) < (-90985/100000) := by norm_num
theorem ageProducts : (([14,23,35,48,52,67]:List ℚ).map (fun x => (x-239/6)^2)).sum=11561/6 ∧ (([14,23,35,48,52,67]:List ℚ).zipWith (fun x y => (x-239/6)*(y-1385/6)) [252,244,240,233,212,204]).sum = -10519/6 := by norm_num
theorem recenter (a b u:ℝ) : a+b*(u+239/6)=(a+b*(239/6))+b*u := by ring
theorem squareExpansion {n : ℕ} (f : Fin n → ℝ) (m : ℝ) :
 (∑ i, (f i-m)^2) = (∑ i, (f i)^2) - 2*m*(∑ i, f i) + (n:ℝ)*m^2 := by
 simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
  ←Finset.sum_mul, ←Finset.mul_sum, Finset.sum_const,
  Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
 ring
theorem centeredSquares {n : ℕ} (f : Fin n → ℝ) (m : ℝ)
 (hm : (∑ i, f i) = (n:ℝ)*m) :
 (∑ i, (f i-m)^2) = (∑ i, (f i)^2) - (n:ℝ)*m^2 := by
 rw [squareExpansion,hm]
 ring
theorem productExpansion {n : ℕ} (f g : Fin n → ℝ) (a b : ℝ) :
 (∑ i, (f i-a)*(g i-b)) = (∑ i, f i*g i) - b*(∑ i, f i) - a*(∑ i, g i) + (n:ℝ)*a*b := by
 simp only [sub_mul, mul_sub, Finset.sum_sub_distrib,
  ←Finset.sum_mul, ←Finset.mul_sum, Finset.sum_const,
  Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
 ring
theorem centeredProducts {n : ℕ} (f g : Fin n → ℝ) (a b : ℝ)
 (ha : (∑ i, f i) = (n:ℝ)*a) (hb : (∑ i, g i) = (n:ℝ)*b) :
 (∑ i, (f i-a)*(g i-b)) = (∑ i, f i*g i) - (n:ℝ)*a*b := by
 rw [productExpansion,ha,hb]
 ring

end c07_d03

namespace c07_d04
theorem arithmetic_001 : ((392/1000) : ℚ) > (0) := by norm_num
theorem arithmetic_002 : ((140/1000) : ℚ) > (0) := by norm_num
theorem arithmetic_003 : ((-666/1000) : ℚ) < (0) := by norm_num
theorem arithmetic_004 : ((-592/1000) : ℚ) < (0) := by norm_num
theorem arithmetic_005 : ((-757/1000) : ℚ) < (0) := by norm_num
end c07_d04

namespace c07_p01
theorem arithmetic_001 : ((2*1063) : ℚ) = (2126) := by norm_num
theorem arithmetic_002 : ((2*384) : ℚ) = (768) := by norm_num
theorem lossExpansion (a b:ℝ) : (233-a)^2+(204-a)^2+(242-a)^2+(130-a-b)^2+(112-a-b)^2+(142-a-b)^2=6*a^2+6*a*b+3*b^2-2126*a-768*b+204077 := by ring
end c07_p01

namespace c07_p02
theorem arithmetic_001 : ((3734/3+461041/3+49152) : ℚ) = (204077) := by norm_num
theorem arithmetic_002 : ((-1358-768) : ℚ) = (-2126) := by norm_num
theorem arithmetic_003 : ((1063-384) : ℚ) = (679) := by norm_num
theorem arithmetic_004 : ((384-679) : ℚ) = (-295) := by norm_num
theorem arithmetic_005 : (((20-67+47)/3+2-16+14) : ℚ) = (0) := by norm_num
theorem completed (a b:ℝ) : (233-a)^2+(204-a)^2+(242-a)^2+(130-a-b)^2+(112-a-b)^2+(142-a-b)^2=3734/3+3*(a-679/3)^2+3*(a+b-128)^2 := by ring
theorem minimum (a b:ℝ) : (3734/3:ℝ)≤(233-a)^2+(204-a)^2+(242-a)^2+(130-a-b)^2+(112-a-b)^2+(142-a-b)^2 := by rw [completed]; nlinarith [sq_nonneg (a-679/3),sq_nonneg (a+b-128)]
theorem normalSolution (a b:ℝ) : (6*a+3*b=1063 ∧ 3*a+3*b=384) ↔ (a=679/3 ∧ b= -295/3) := by constructor; rintro ⟨h1,h2⟩; constructor <;> linarith; rintro ⟨rfl,rfl⟩; norm_num
theorem partialA (a b:ℝ) : HasDerivAt (fun x:ℝ => 6*x^2+6*x*b+3*b^2-2126*x-768*b+204077) (12*a+6*b-2126) a := by
 exact (((((((hasDerivAt_pow 2 a).const_mul 6).add (((hasDerivAt_id a).const_mul 6).mul_const b)).add_const (3*b^2)).sub ((hasDerivAt_id a).const_mul 2126)).sub_const (768*b)).add_const 204077).congr_deriv (by dsimp; ring)
theorem partialB (a b:ℝ) : HasDerivAt (fun x:ℝ => 6*a^2+6*a*x+3*x^2-2126*a-768*x+204077) (6*a+6*b-768) b := by
 exact (((((((hasDerivAt_id b).const_mul (6*a)).const_add (6*a^2)).add ((hasDerivAt_pow 2 b).const_mul 3)).sub_const (2126*a)).sub ((hasDerivAt_id b).const_mul 768)).add_const 204077).congr_deriv (by dsimp; ring)

end c07_p02

namespace c07_p03
theorem interaction (a b c d p:ℝ) : a+b*p+c*0+d*p*0=a+b*p ∧ a+b*p+c*1+d*p*1=(a+c)+(b+d)*p ∧ (b+d)-b=d := by constructor; ring; constructor <;> ring
end c07_p03

namespace c07_p04
theorem arithmetic_001 : ((202588/1000-19695/1000) : ℚ) = (182893/1000) := by norm_num
theorem sharedExpansion (u v e w f:ℝ) : (u+v+e)*(u+w+f)=u*u+u*w+u*f+v*u+v*w+v*f+e*u+e*w+e*f := by ring
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem sharedParticipant (u v e w f : Ω → ℝ)
 (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (he : MemLp e 2 μ)
 (hw : MemLp w 2 μ) (hf : MemLp f 2 μ)
 (huw : IndepFun u w μ) (huf : IndepFun u f μ)
 (hvu : IndepFun v u μ) (hvw : IndepFun v w μ) (hvf : IndepFun v f μ)
 (heu : IndepFun e u μ) (hew : IndepFun e w μ) (hef : IndepFun e f μ) :
 covariance (u+v+e) (u+w+f) μ = variance u μ := by
 rw [covariance_add_left (hu.add hv) he ((hu.add hw).add hf),
     covariance_add_left hu hv ((hu.add hw).add hf),
     covariance_add_right hu (hu.add hw) hf,
     covariance_add_right hu hu hw,
     covariance_add_right hv (hu.add hw) hf,
     covariance_add_right hv hu hw,
     covariance_add_right he (hu.add hw) hf,
     covariance_add_right he hu hw,
     huw.covariance_eq_zero hu hw, huf.covariance_eq_zero hu hf,
     hvu.covariance_eq_zero hv hu, hvw.covariance_eq_zero hv hw,
     hvf.covariance_eq_zero hv hf, heu.covariance_eq_zero he hu,
     hew.covariance_eq_zero he hw, hef.covariance_eq_zero he hf,
     covariance_self hu.aemeasurable]
 ring
theorem centeredCrossMoment (u v : Ω → ℝ)
 (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (h : IndepFun u v μ)
 (mu : (∫ ω, u ω ∂μ) = 0) (mv : (∫ ω, v ω ∂μ) = 0) :
 (∫ ω, u ω * v ω ∂μ) = 0 := by
 change (∫ ω, (u*v) ω ∂μ) = 0
 rw [h.integral_mul_eq_mul_integral hu.aestronglyMeasurable hv.aestronglyMeasurable, mu, mv]
 norm_num
theorem centeredVariance (u : Ω → ℝ) (hu : MemLp u 2 μ)
 (mu : (∫ ω, u ω ∂μ) = 0) : variance u μ = ∫ ω, (u ω)^2 ∂μ := by
 rw [variance_eq_integral hu.aemeasurable]
 simp only [mu, sub_zero]

end c07_p04

namespace c07_p05
theorem redundant (p q:Bool) (h:q=true→p=true) : (p&&q)=q := by cases p <;> cases q <;> simp_all
theorem samePrediction (a b c h q:ℝ) : a+(b+h)*q+(c-h)*q=a+(b+c)*q := by ring
end c07_p05

namespace c07_n01
theorem arithmetic_001 : ((10^6) : ℚ) = (1000000) := by norm_num
theorem arithmetic_002 : ((869/942*100) : ℚ) = (86900/942) := by norm_num
theorem arithmetic_003 : ((86900/942) : ℚ) > (92245/1000) := by norm_num
theorem arithmetic_004 : ((86900/942) : ℚ) < (92255/1000) := by norm_num
theorem arithmetic_005 : ((869) : ℚ) ≤ (942) := by norm_num
theorem arithmetic_006 : ((48/100) : ℚ) < (1/2) := by norm_num
theorem centered (d s:ℝ) : s-d>d ↔ s>2*d := by constructor <;> intro h <;> linarith
theorem tailBound (s b:ℝ) (hs:0 ≤ s) (hb:0<b) (hle:s ≤ b) : 0 ≤ s/b ∧ s/b ≤ 1 := ⟨div_nonneg hs hb.le,(div_le_one hb).2 hle⟩
end c07_n01
end Chapter07
#print axioms Chapter07.c07_r01.arithmetic_001
#print axioms Chapter07.c07_r01.arithmetic_002
#print axioms Chapter07.c07_r01.sourceTotals
#print axioms Chapter07.c07_r02.arithmetic_001
#print axioms Chapter07.c07_r02.arithmetic_002
#print axioms Chapter07.c07_r02.arithmetic_003
#print axioms Chapter07.c07_r02.swap
#print axioms Chapter07.c07_r03.fraction_bounds
#print axioms Chapter07.c07_r04.arithmetic_001
#print axioms Chapter07.c07_r04.arithmetic_002
#print axioms Chapter07.c07_r04.arithmetic_003
#print axioms Chapter07.c07_r04.arithmetic_004
#print axioms Chapter07.c07_r04.arithmetic_005
#print axioms Chapter07.c07_r04.arithmetic_006
#print axioms Chapter07.c07_r04.arithmetic_007
#print axioms Chapter07.c07_r04.arithmetic_008
#print axioms Chapter07.c07_r04.retainedPositions
#print axioms Chapter07.c07_r05.arithmetic_001
#print axioms Chapter07.c07_r05.arithmetic_002
#print axioms Chapter07.c07_r05.arithmetic_003
#print axioms Chapter07.c07_r05.arithmetic_004
#print axioms Chapter07.c07_r05.centeredThreshold
#print axioms Chapter07.c07_r05.resample1Totals
#print axioms Chapter07.c07_r05.resample2Totals
#print axioms Chapter07.c07_r06.arithmetic_001
#print axioms Chapter07.c07_r06.arithmetic_002
#print axioms Chapter07.c07_r06.arithmetic_003
#print axioms Chapter07.c07_r06.arithmetic_004
#print axioms Chapter07.c07_r06.arithmetic_005
#print axioms Chapter07.c07_r06.arithmetic_006
#print axioms Chapter07.c07_r06.arithmetic_007
#print axioms Chapter07.c07_r06.arithmetic_008
#print axioms Chapter07.c07_r06.sumProducts
#print axioms Chapter07.c07_r07.arithmetic_001
#print axioms Chapter07.c07_r07.arithmetic_002
#print axioms Chapter07.c07_r07.arithmetic_003
#print axioms Chapter07.c07_r07.arithmetic_004
#print axioms Chapter07.c07_r07.arithmetic_005
#print axioms Chapter07.c07_r07.arithmetic_006
#print axioms Chapter07.c07_r07.arithmetic_007
#print axioms Chapter07.c07_r07.arithmetic_008
#print axioms Chapter07.c07_r07.arithmetic_009
#print axioms Chapter07.c07_r07.arithmetic_010
#print axioms Chapter07.c07_r07.arithmetic_011
#print axioms Chapter07.c07_r07.arithmetic_012
#print axioms Chapter07.c07_r07.arithmetic_013
#print axioms Chapter07.c07_r07.arithmetic_014
#print axioms Chapter07.c07_r07.arithmetic_015
#print axioms Chapter07.c07_r08.arithmetic_001
#print axioms Chapter07.c07_r08.arithmetic_002
#print axioms Chapter07.c07_r08.arithmetic_003
#print axioms Chapter07.c07_r08.arithmetic_004
#print axioms Chapter07.c07_r08.arithmetic_005
#print axioms Chapter07.c07_r08.arithmetic_006
#print axioms Chapter07.c07_r08.arithmetic_007
#print axioms Chapter07.c07_r08.arithmetic_008
#print axioms Chapter07.c07_r08.arithmetic_009
#print axioms Chapter07.c07_r08.arithmetic_010
#print axioms Chapter07.c07_r08.arithmetic_011
#print axioms Chapter07.c07_r08.arithmetic_012
#print axioms Chapter07.c07_r08.arithmetic_013
#print axioms Chapter07.c07_r08.arithmetic_014
#print axioms Chapter07.c07_r08.arithmetic_015
#print axioms Chapter07.c07_r08.arithmetic_016
#print axioms Chapter07.c07_r08.arithmetic_017
#print axioms Chapter07.c07_r08.correlationSquare
#print axioms Chapter07.c07_r08.squareExpansion
#print axioms Chapter07.c07_r08.centeredSquares
#print axioms Chapter07.c07_r09.arithmetic_001
#print axioms Chapter07.c07_r09.arithmetic_002
#print axioms Chapter07.c07_d01.arithmetic_001
#print axioms Chapter07.c07_d01.arithmetic_002
#print axioms Chapter07.c07_d01.pairedDiffs
#print axioms Chapter07.c07_d01.pairedMean
#print axioms Chapter07.c07_d02.arithmetic_001
#print axioms Chapter07.c07_d02.arithmetic_002
#print axioms Chapter07.c07_d02.arithmetic_003
#print axioms Chapter07.c07_d02.arithmetic_004
#print axioms Chapter07.c07_d02.arithmetic_005
#print axioms Chapter07.c07_d02.arithmetic_006
#print axioms Chapter07.c07_d02.seSquare
#print axioms Chapter07.c07_d02.MeanOps.independentMeanVariance
#print axioms Chapter07.c07_d03.arithmetic_001
#print axioms Chapter07.c07_d03.arithmetic_002
#print axioms Chapter07.c07_d03.arithmetic_003
#print axioms Chapter07.c07_d03.arithmetic_004
#print axioms Chapter07.c07_d03.arithmetic_005
#print axioms Chapter07.c07_d03.arithmetic_006
#print axioms Chapter07.c07_d03.arithmetic_007
#print axioms Chapter07.c07_d03.arithmetic_008
#print axioms Chapter07.c07_d03.arithmetic_009
#print axioms Chapter07.c07_d03.arithmetic_010
#print axioms Chapter07.c07_d03.arithmetic_011
#print axioms Chapter07.c07_d03.arithmetic_012
#print axioms Chapter07.c07_d03.arithmetic_013
#print axioms Chapter07.c07_d03.arithmetic_014
#print axioms Chapter07.c07_d03.arithmetic_015
#print axioms Chapter07.c07_d03.arithmetic_016
#print axioms Chapter07.c07_d03.arithmetic_017
#print axioms Chapter07.c07_d03.arithmetic_018
#print axioms Chapter07.c07_d03.arithmetic_019
#print axioms Chapter07.c07_d03.arithmetic_020
#print axioms Chapter07.c07_d03.arithmetic_021
#print axioms Chapter07.c07_d03.arithmetic_022
#print axioms Chapter07.c07_d03.arithmetic_023
#print axioms Chapter07.c07_d03.arithmetic_024
#print axioms Chapter07.c07_d03.arithmetic_025
#print axioms Chapter07.c07_d03.arithmetic_026
#print axioms Chapter07.c07_d03.arithmetic_027
#print axioms Chapter07.c07_d03.arithmetic_028
#print axioms Chapter07.c07_d03.arithmetic_029
#print axioms Chapter07.c07_d03.arithmetic_030
#print axioms Chapter07.c07_d03.arithmetic_031
#print axioms Chapter07.c07_d03.arithmetic_032
#print axioms Chapter07.c07_d03.arithmetic_033
#print axioms Chapter07.c07_d03.arithmetic_034
#print axioms Chapter07.c07_d03.arithmetic_035
#print axioms Chapter07.c07_d03.arithmetic_036
#print axioms Chapter07.c07_d03.arithmetic_037
#print axioms Chapter07.c07_d03.ageProducts
#print axioms Chapter07.c07_d03.recenter
#print axioms Chapter07.c07_d03.squareExpansion
#print axioms Chapter07.c07_d03.centeredSquares
#print axioms Chapter07.c07_d03.productExpansion
#print axioms Chapter07.c07_d03.centeredProducts
#print axioms Chapter07.c07_d04.arithmetic_001
#print axioms Chapter07.c07_d04.arithmetic_002
#print axioms Chapter07.c07_d04.arithmetic_003
#print axioms Chapter07.c07_d04.arithmetic_004
#print axioms Chapter07.c07_d04.arithmetic_005
#print axioms Chapter07.c07_p01.arithmetic_001
#print axioms Chapter07.c07_p01.arithmetic_002
#print axioms Chapter07.c07_p01.lossExpansion
#print axioms Chapter07.c07_p02.arithmetic_001
#print axioms Chapter07.c07_p02.arithmetic_002
#print axioms Chapter07.c07_p02.arithmetic_003
#print axioms Chapter07.c07_p02.arithmetic_004
#print axioms Chapter07.c07_p02.arithmetic_005
#print axioms Chapter07.c07_p02.completed
#print axioms Chapter07.c07_p02.minimum
#print axioms Chapter07.c07_p02.normalSolution
#print axioms Chapter07.c07_p02.partialA
#print axioms Chapter07.c07_p02.partialB
#print axioms Chapter07.c07_p03.interaction
#print axioms Chapter07.c07_p04.arithmetic_001
#print axioms Chapter07.c07_p04.sharedExpansion
#print axioms Chapter07.c07_p04.sharedParticipant
#print axioms Chapter07.c07_p04.centeredCrossMoment
#print axioms Chapter07.c07_p04.centeredVariance
#print axioms Chapter07.c07_p05.redundant
#print axioms Chapter07.c07_p05.samePrediction
#print axioms Chapter07.c07_n01.arithmetic_001
#print axioms Chapter07.c07_n01.arithmetic_002
#print axioms Chapter07.c07_n01.arithmetic_003
#print axioms Chapter07.c07_n01.arithmetic_004
#print axioms Chapter07.c07_n01.arithmetic_005
#print axioms Chapter07.c07_n01.arithmetic_006
#print axioms Chapter07.c07_n01.centered
#print axioms Chapter07.c07_n01.tailBound
