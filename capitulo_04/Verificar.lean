import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter04

namespace c04_n04
theorem arithmetic_001 : ((437/1000) : ℚ) = (0.437) := by norm_num
theorem arithmetic_002 : ((155/1000000) : ℚ) = (0.000155) := by norm_num
theorem arithmetic_003 : ((267/100) : ℚ) = (2.67) := by norm_num
theorem arithmetic_004 : ((4*(4-1)/2) : ℚ) = (6) := by norm_num
theorem arithmetic_005 : ((2/6) : ℚ) = (1/3) := by norm_num
theorem arithmetic_006 : ((0.437) : ℚ) > (0.000155) := by norm_num
theorem arithmetic_007 : ((2.67) : ℚ) < (3) := by norm_num

theorem possiblePairs (k:ℕ) : k.choose 2=k*(k-1)/2 := Nat.choose_two_right k

theorem clusteringFraction (L k:ℝ) (hk:1<k) : L/(k*(k-1)/2)=2*L/(k*(k-1)) := by
  have h0:k≠0 := ne_of_gt (by linarith)
  have h1:k-1≠0 := ne_of_gt (by linarith)
  field_simp
  <;> ring

theorem clusteringBounds (L k:ℝ) (hk:2≤k) (hL:0≤L) (hmax:L≤k*(k-1)/2) :
    0≤L/(k*(k-1)/2) ∧ L/(k*(k-1)/2)≤1 := by
  have hp:0<k := by linarith
  have hm:0<k-1 := by linarith
  have hd:0<k*(k-1)/2 := by positivity
  exact ⟨div_nonneg hL hd.le, (div_le_one hd).mpr hmax⟩

theorem averageCoefficients {n:ℕ} (C:Fin n→ℝ) :
    (∑ i,C i)/(n:ℝ)=∑ i,C i/(n:ℝ) := by rw [Finset.sum_div]

def publishedEdges : List (ℕ×ℕ) :=
 [(1,2),(1,3),(2,3),(1,4),(1,5),(4,5),(2,6),(2,7),(6,7),(4,6),(6,8),(4,8)]
def johnNeighbors : List ℕ := [2,3,4,5]
theorem johnDegree :
 ((publishedEdges.filter (fun e=>e.1==1 || e.2==1)).map
   (fun e=>if e.1==1 then e.2 else e.1))=johnNeighbors := by decide +kernel
theorem edgesAmongNeighbors :
 publishedEdges.filter (fun e=>johnNeighbors.contains e.1 && johnNeighbors.contains e.2)=
 [(2,3),(4,5)] := by decide +kernel
theorem johnCoefficient : johnNeighbors.length=4 ∧
 (publishedEdges.filter (fun e=>johnNeighbors.contains e.1 && johnNeighbors.contains e.2)).length=2 ∧
 (2:ℚ)/(4*(4-1)/2)=1/3 := by decide +kernel
end c04_n04

namespace c04_n05

theorem reversedContrast (D1 D2:ℝ) : D2-D1= -(D1-D2) := by ring

theorem positiveContrast (D1 D2:ℝ) : 0<D1-D2 ↔ D2<D1 := sub_pos

theorem zeroContrast (D1 D2:ℝ) : D1-D2=0 ↔ D1=D2 := sub_eq_zero

theorem groupCoordinate {n:ℕ} (v:Fin n→ℝ) :
    (∑ i,v i)/(n:ℝ)=∑ i,v i/(n:ℝ) := by rw [Finset.sum_div]

theorem aggregateReversal {n:ℕ} (a b:Fin n→ℝ) :
    (∑ i,(b i-a i))= -(∑ i,(a i-b i)) := by
  simp only [Finset.sum_sub_distrib]; ring

theorem coordinateSquare (v g:ℝ) : (v-g)^2=v^2-2*v*g+g^2 := by ring

theorem nonnegativeSumSquares {n:ℕ} (v g:Fin n→ℝ) :
    0≤∑ i,(v i-g i)^2 := Finset.sum_nonneg (fun i _=>sq_nonneg (v i-g i))

theorem normContrast {E:Type*} [SeminormedAddCommGroup E] (v g1 g2:E) :
    ‖v-g2‖-‖v-g1‖= -(‖v-g1‖-‖v-g2‖) := by ring

theorem normalizedSquaredLength {n:ℕ} (u:Fin n→ℝ) (s:ℝ)
 (hs:s≠0) (h:(∑ i,(u i)^2)=s^2) : (∑ i,(u i/s)^2)=1 := by
 simp_rw [div_pow]
 rw [←Finset.sum_div,h]
 exact div_self (pow_ne_zero 2 hs)
theorem normalizedLength {n:ℕ} (u:Fin n→ℝ) (s:ℝ)
 (hs:s≠0) (h:(∑ i,(u i)^2)=s^2) : Real.sqrt (∑ i,(u i/s)^2)=1 := by
 rw [normalizedSquaredLength u s hs h,Real.sqrt_one]
theorem positiveRescaling {n:ℕ} (u:Fin n→ℝ) (s:ℝ) (hs:0<s) :
 (0<1/s) ∧ (∀ i,u i/s=(1/s)*u i) := by
 constructor
 · positivity
 · intro i; ring
end c04_n05

namespace c04_r01
theorem arithmetic_001 : ((5-1) : ℚ) = (4) := by norm_num
theorem treeEdges : ([(2,1),(2,3),(2,5),(5,4)]:List (ℕ×ℕ)).length=4 ∧ ([(2,1),(2,3),(2,5),(5,4)]:List (ℕ×ℕ)).map Prod.snd=[1,3,5,4] := by decide +kernel
end c04_r01

namespace c04_r02
theorem arithmetic_001 : ((|(2-1)|) : ℚ) = (1) := by norm_num
theorem arithmetic_002 : ((|(2-3)|) : ℚ) = (1) := by norm_num
theorem arithmetic_003 : ((|(2-5)|) : ℚ) = (3) := by norm_num
theorem arithmetic_004 : ((|(5-4)|) : ℚ) = (1) := by norm_num
theorem arithmetic_005 : ((1+1+3+1) : ℚ) = (6) := by norm_num
theorem arithmetic_006 : ((|(1-5)|) : ℚ) = (4) := by norm_num
theorem arithmetic_007 : ((|(2-4)|) : ℚ) = (2) := by norm_num
theorem arithmetic_008 : ((|(4-3)|) : ℚ) = (1) := by norm_num
theorem arithmetic_009 : ((1+3+2+1) : ℚ) = (7) := by norm_num
end c04_r02

namespace c04_r03
theorem arithmetic_001 : ((1+0+1+0+1) : ℚ) = (3) := by norm_num
theorem arithmetic_002 : ((5-1) : ℚ) = (4) := by norm_num
theorem adjacencyRows : (([0,0,0,0,0]:List ℚ).sum=0) ∧ (([1,0,1,0,1]:List ℚ).sum=3) ∧ (([0,0,0,1,0]:List ℚ).sum=1) := by decide +kernel
end c04_r03

namespace c04_r04
theorem arithmetic_001 : ((1*0+0*0+1*0+0*0+1*1) : ℚ) = (1) := by norm_num
theorem arithmetic_002 : ((1*1+1*1) : ℚ) = (2) := by norm_num
theorem twoStep : (1*0+0*0+1*0+0*0+1*1:ℚ)=1 := by norm_num
theorem entryFormula {n:ℕ} (A:Matrix (Fin n) (Fin n) ℝ) (i j:Fin n) : (A*A) i j=∑ k, A i k*A k j := rfl
theorem publishedPolysemy : ([(6,2,1,2),(2,2,1,4)]:List (ℕ×ℕ×ℕ×ℕ)).length=2 := by decide +kernel
theorem translationComposition {n m k:ℕ} (T:Matrix (Fin n) (Fin m) ℝ) (R:Matrix (Fin m) (Fin k) ℝ) (i:Fin n) (j:Fin k) : (T*R) i j=∑ w,T i w*R w j := rfl
end c04_r04

namespace c04_p01
theorem arithmetic_001 : ((1+1+3+1) : ℚ) = (6) := by norm_num
theorem arithmetic_002 : ((1+3+2+1) : ℚ) = (7) := by norm_num
theorem sums : ([1,1,3,1]:List ℕ).sum=6 ∧ ([1,3,2,1]:List ℕ).sum=7 := by decide +kernel
end c04_p01

namespace c04_r05
theorem vectorSizes : ([442,8,2]:List ℕ).length=3 ∧ ([5,1683,1670]:List ℕ).length=3 ∧ ([5,3982,3325]:List ℕ).length=3 := by decide +kernel
end c04_r05

namespace c04_r06
theorem arithmetic_001 : ((442*5) : ℚ) = (2210) := by norm_num
theorem arithmetic_002 : ((8*3982) : ℚ) = (31856) := by norm_num
theorem arithmetic_003 : ((2*3325) : ℚ) = (6650) := by norm_num
theorem arithmetic_004 : ((2210+31856+6650) : ℚ) = (40716) := by norm_num
theorem arithmetic_005 : ((1*(-4)+(41/10)*0+1*(-4)) : ℚ) = (-8) := by norm_num
theorem arithmetic_006 : ((1*0+(41/10)*(-2)+1*0) : ℚ) = (-41/5) := by norm_num
theorem arithmetic_007 : ((-8) : ℚ) > (-41/5) := by norm_num
end c04_r06

namespace c04_r07
theorem arithmetic_001 : ((442^2) : ℚ) = (195364) := by norm_num
theorem arithmetic_002 : ((8^2) : ℚ) = (64) := by norm_num
theorem arithmetic_003 : ((2^2) : ℚ) = (4) := by norm_num
theorem arithmetic_004 : ((195364+64+4) : ℚ) = (195432) := by norm_num
theorem arithmetic_005 : ((3982^2) : ℚ) = (15856324) := by norm_num
theorem arithmetic_006 : ((3325^2) : ℚ) = (11055625) := by norm_num
theorem arithmetic_007 : ((25+15856324+11055625) : ℚ) = (26911974) := by norm_num
theorem arithmetic_008 : ((1683*3982) : ℚ) = (6701706) := by norm_num
theorem arithmetic_009 : ((1670*3325) : ℚ) = (5552750) := by norm_num
theorem arithmetic_010 : ((25+6701706+5552750) : ℚ) = (12254481) := by norm_num
theorem arithmetic_011 : ((1683^2) : ℚ) = (2832489) := by norm_num
theorem arithmetic_012 : ((1670^2) : ℚ) = (2788900) := by norm_num
theorem arithmetic_013 : ((25+2832489+2788900) : ℚ) = (5621414) := by norm_num
theorem arithmetic_014 : (((175/10000)^2) : ℚ) < (40716^2/(195432*26911974)) := by norm_num
theorem arithmetic_015 : ((40716^2/(195432*26911974)) : ℚ) < ((185/10000)^2) := by norm_num
theorem arithmetic_016 : (((9955/10000)^2) : ℚ) < (12254481^2/(5621414*26911974)) := by norm_num
theorem arithmetic_017 : ((12254481^2/(5621414*26911974)) : ℚ) < ((9965/10000)^2) := by norm_num
theorem normCherry : (Real.sqrt 195432)^2=(195432:ℝ) := Real.sq_sqrt (by norm_num)
theorem normDigital : (Real.sqrt 5621414)^2=(5621414:ℝ) := Real.sq_sqrt (by norm_num)
theorem normInformation : (Real.sqrt 26911974)^2=(26911974:ℝ) := Real.sq_sqrt (by norm_num)
theorem positiveDenominators : 0<Real.sqrt (195432:ℝ)*Real.sqrt 26911974 ∧ 0<Real.sqrt (5621414:ℝ)*Real.sqrt 26911974 := by constructor <;> positivity
theorem squaredBoundsImplyBounds (x a b:ℝ) (hx:0≤x) (ha:0≤a) (hb:0≤b) (h1:a^2<x^2) (h2:x^2<b^2) : a<x ∧ x<b := by constructor <;> nlinarith
end c04_r07

namespace c04_r08
theorem arithmetic_001 : ((-4+0-4) : ℚ) = (-8) := by norm_num
theorem arithmetic_002 : ((0-82/10+0) : ℚ) = (-41/5) := by norm_num
theorem weightedRows : ((!![-4,0,-4;0,-2,0]:Matrix (Fin 2) (Fin 3) ℚ)* (!![1;41/10;1]:Matrix (Fin 3) (Fin 1) ℚ))=(!![-8;-41/5]:Matrix (Fin 2) (Fin 1) ℚ) := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]
theorem fullAddCoordinate {n:ℕ} (A B:Matrix (Fin n) (Fin n) ℝ) (u v:Fin n→ℝ) (i:Fin n) :
 (A.mulVec u+B.mulVec v) i=(∑ j,A i j*u j)+(∑ j,B i j*v j) := rfl
theorem weightedAddCoordinate (u v:Fin 350→ℝ) (i:Fin 350) : ((16/100:ℝ)•u+(33/100:ℝ)•v) i=(16/100)*u i+(33/100)*v i := rfl
end c04_r08

namespace c04_r09
theorem sameTokens : (["John","threw","out","the","trash"]:List String).map (fun w => (["John","threw","out","the","trash"]:List String).count w) = (["John","threw","out","the","trash"]:List String).map (fun w => (["John","threw","the","trash","out"]:List String).count w) := by decide +kernel
end c04_r09

namespace c04_p02
theorem usualBasisSum : (![1,0,0,0,0,0,0,0,0]:Fin 9→ℚ)+![0,0,0,1,0,0,0,0,0]=![1,0,0,1,0,0,0,0,0] := by ext i; fin_cases i <;> norm_num
 theorem transposeEntry {m n:ℕ} (M:Matrix (Fin m) (Fin n) ℚ) (i:Fin n) (j:Fin m) : M.transpose i j=M j i := rfl
end c04_p02

namespace c04_p03
theorem arithmetic_001 : (((22/100)*(334/100)) : ℚ) = (7348/10000) := by norm_num
theorem arithmetic_002 : (((-11/100)*(254/100)) : ℚ) = (-2794/10000) := by norm_num
theorem arithmetic_003 : (((7348/10000)*(20/100)) : ℚ) = (14696/100000) := by norm_num
theorem arithmetic_004 : (((-2794/10000)*(-6/100)) : ℚ) = (16764/1000000) := by norm_num
theorem arithmetic_005 : ((14696/100000+16764/1000000) : ℚ) = (163724/1000000) := by norm_num
theorem arithmetic_006 : (((7348/10000)*(61/100)) : ℚ) = (448228/1000000) := by norm_num
theorem arithmetic_007 : (((-2794/10000)*(17/100)) : ℚ) = (-47498/1000000) := by norm_num
theorem arithmetic_008 : ((448228/1000000-47498/1000000) : ℚ) = (40073/100000) := by norm_num
theorem arithmetic_009 : (((22/100)*(334/100)+(-11/100)*0) : ℚ) = (7348/10000) := by norm_num
theorem arithmetic_010 : (((22/100)*0+(-11/100)*(254/100)) : ℚ) = (-2794/10000) := by norm_num
theorem arithmetic_011 : ((155/1000) : ℚ) < (163724/1000000) := by norm_num
theorem arithmetic_012 : ((163724/1000000) : ℚ) < (165/1000) := by norm_num
theorem arithmetic_013 : ((395/1000) : ℚ) < (40073/100000) := by norm_num
theorem arithmetic_014 : ((40073/100000) : ℚ) < (405/1000) := by norm_num
theorem independentDocumentColumns (a b c d e f g h i:ℝ) (h1:a+d=0) (h2:a+c=0) (h3:a+b=0) (h4:b+c+e=0) (h5:b+c+2*d=0) (h6:b+e=0) (h7:c+d=0) (h8:b+i=0) (h9:f+g+h=0) (h10:g+h+i=0) (h11:h+i=0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 ∧ f=0 ∧ g=0 ∧ h=0 ∧ i=0  := by
 have ha : a=0 := by linarith only [h1,h2,h7]
 have hb : b=0 := by linarith only [h3,ha]
 have hc : c=0 := by linarith only [h2,ha]
 have hd : d=0 := by linarith only [h1,ha]
 have he : e=0 := by linarith only [h6,hb]
 have hi : i=0 := by linarith only [h8,hb]
 have hh : h=0 := by linarith only [h11,hi]
 have hg : g=0 := by linarith only [h10,hh,hi]
 have hf : f=0 := by linarith only [h9,hg,hh]
 exact ⟨ha,hb,hc,hd,he,hf,hg,hh,hi⟩
theorem publishedDiagonalProduct :
 ((!![22/100,-11/100]:Matrix (Fin 1) (Fin 2) ℚ)*
 (!![334/100,0;0,254/100]:Matrix (Fin 2) (Fin 2) ℚ))=
 (!![7348/10000,-2794/10000]:Matrix (Fin 1) (Fin 2) ℚ) := by
 ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_succ]
end c04_p03

namespace c04_p04
theorem orthogonalProduct {d m n:ℕ} (U:Matrix (Fin m) (Fin d) ℝ) (V:Matrix (Fin n) (Fin d) ℝ) (Q:Matrix (Fin d) (Fin d) ℝ) (hQ:Q*Q.transpose=1) : (U*Q)*(V*Q).transpose=U*V.transpose := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]; rw [←Matrix.mul_assoc Q Q.transpose V.transpose,hQ,Matrix.one_mul]
theorem alignmentEntry {n d:ℕ} (W1 W2:Matrix (Fin n) (Fin d) ℝ)
 (Q:Matrix (Fin d) (Fin d) ℝ) (i:Fin n) (j:Fin d) :
 (W1*Q-W2) i j=(∑ k,W1 i k*Q k j)-W2 i j := rfl
theorem alignmentErrorNonnegative {n d:ℕ} (E:Matrix (Fin n) (Fin d) ℝ) :
 0≤∑ i,∑ j,(E i j)^2 := by positivity
theorem alignmentRoot {n d:ℕ} (E:Matrix (Fin n) (Fin d) ℝ) :
 (Real.sqrt (∑ i,∑ j,(E i j)^2))^2=∑ i,∑ j,(E i j)^2 :=
 Real.sq_sqrt (alignmentErrorNonnegative E)
end c04_p04

namespace c04_d01
theorem arithmetic_001 : ((3-1) : ℚ) = (2) := by norm_num
theorem arithmetic_002 : ((2-3) : ℚ) = (-1) := by norm_num
theorem arithmetic_003 : (((3-1)+(2-3)) : ℚ) = (1) := by norm_num
theorem arithmetic_004 : ((7-6) : ℚ) = (1) := by norm_num
end c04_d01

namespace c04_d02
theorem arithmetic_001 : ((12-1) : ℚ) = (11) := by norm_num
theorem arithmetic_002 : ((191/10) : ℚ) < (273/10) := by norm_num
end c04_d02

namespace c04_d03
theorem windows : ([[1,0,1],[0,0,2],[0,1,0],[1,1,0]]:List (List ℕ)).map List.length=[3,3,3,3] := by decide +kernel
end c04_d03

namespace c04_d04
theorem arithmetic_001 : ((3*2*3) : ℚ) = (18) := by norm_num
theorem arithmetic_002 : ((3*6) : ℚ) = (18) := by norm_num
theorem publishedEntries : ([400,821,853,448,32,33]:List ℕ)[3]?=some 448 ∧ ([52,70,93,47,484,536]:List ℕ)[5]?=some 536 := by decide +kernel
end c04_d04

namespace c04_n03
theorem arithmetic_001 : ((|(2-1)|+|(2-3)|+|(2-6)|+|(6-4)|+|(6-5)|+|(6-7)|+|(7-8)|+|(8-10)|+|(10-9)|) : ℚ) = (14) := by norm_num
theorem arithmetic_002 : ((|(2-1)|+|(2-10)|+|(2-5)|+|(5-3)|+|(5-4)|+|(5-6)|+|(6-7)|+|(7-9)|+|(9-8)|) : ℚ) = (20) := by norm_num
theorem arithmetic_003 : ((1+1+4+2+1+1+1+2+1) : ℚ) = (14) := by norm_num
theorem arithmetic_004 : ((1+8+3+2+1+1+1+2+1) : ℚ) = (20) := by norm_num
theorem arithmetic_005 : ((8-1) : ℚ) = (7) := by norm_num
theorem arithmetic_006 : ((3-4) : ℚ) = (-1) := by norm_num
theorem arithmetic_007 : ((7-1) : ℚ) = (6) := by norm_num
theorem arithmetic_008 : ((20-14) : ℚ) = (6) := by norm_num
theorem arithmetic_009 : ((10-1) : ℚ) = (9) := by norm_num
theorem arithmetic_010 : ((191/10) : ℚ) < (273/10) := by norm_num
end c04_n03

namespace c04_n01
theorem arithmetic_001 : ((903/1000*100) : ℚ) = (903/10) := by norm_num
theorem arithmetic_002 : ((73/100*100) : ℚ) = (73) := by norm_num
theorem arithmetic_003 : ((72/1000*100) : ℚ) = (72/10) := by norm_num
theorem arithmetic_004 : ((50/1000*100) : ℚ) = (5) := by norm_num
theorem arithmetic_005 : ((744/1000*100) : ℚ) = (744/10) := by norm_num
theorem arithmetic_006 : ((75/100*100) : ℚ) = (75) := by norm_num
theorem arithmetic_007 : ((0*100) : ℚ) = (0) := by norm_num
end c04_n01

namespace c04_n02
theorem arithmetic_001 : ((114/100-(-131/100)) : ℚ) = (245/100) := by norm_num
theorem arithmetic_002 : ((114/100+131/100) : ℚ) = (245/100) := by norm_num
theorem arithmetic_003 : ((-40/100-(-8/100)) : ℚ) = (-32/100) := by norm_num
theorem arithmetic_004 : ((-40/100+8/100) : ℚ) = (-32/100) := by norm_num
theorem arithmetic_005 : ((|(-1305110/1000000-(-131/100))|) : ℚ) < (1/200) := by norm_num
theorem arithmetic_006 : ((|(-84347/1000000-(-8/100))|) : ℚ) < (1/200) := by norm_num
theorem arithmetic_007 : ((|(1135124/1000000-114/100)|) : ℚ) < (1/200) := by norm_num
theorem arithmetic_008 : ((|(-402403/1000000-(-40/100))|) : ℚ) < (1/200) := by norm_num
theorem analogyCoordinate (k m w:ℝ) : k+(w-m)=k-m+w := by ring
 theorem vectorAnalogy {n:ℕ} (k m w:Fin n→ℝ) : (fun i => k i+(w i-m i))=(fun i => k i-m i+w i) := by funext i; ring
 theorem projectedDifference : ((114/100:ℚ)-(-131/100),(-40/100:ℚ)-(-8/100))=(245/100,-32/100) := by norm_num
end c04_n02
end Chapter04
#print axioms Chapter04.c04_n04.arithmetic_001
#print axioms Chapter04.c04_n04.arithmetic_002
#print axioms Chapter04.c04_n04.arithmetic_003
#print axioms Chapter04.c04_n04.arithmetic_004
#print axioms Chapter04.c04_n04.arithmetic_005
#print axioms Chapter04.c04_n04.arithmetic_006
#print axioms Chapter04.c04_n04.arithmetic_007
#print axioms Chapter04.c04_n04.possiblePairs
#print axioms Chapter04.c04_n04.clusteringFraction
#print axioms Chapter04.c04_n04.clusteringBounds
#print axioms Chapter04.c04_n04.averageCoefficients
#print axioms Chapter04.c04_n04.johnDegree
#print axioms Chapter04.c04_n04.edgesAmongNeighbors
#print axioms Chapter04.c04_n04.johnCoefficient
#print axioms Chapter04.c04_n05.reversedContrast
#print axioms Chapter04.c04_n05.positiveContrast
#print axioms Chapter04.c04_n05.zeroContrast
#print axioms Chapter04.c04_n05.groupCoordinate
#print axioms Chapter04.c04_n05.aggregateReversal
#print axioms Chapter04.c04_n05.coordinateSquare
#print axioms Chapter04.c04_n05.nonnegativeSumSquares
#print axioms Chapter04.c04_n05.normContrast
#print axioms Chapter04.c04_n05.normalizedSquaredLength
#print axioms Chapter04.c04_n05.normalizedLength
#print axioms Chapter04.c04_n05.positiveRescaling
#print axioms Chapter04.c04_r01.arithmetic_001
#print axioms Chapter04.c04_r01.treeEdges
#print axioms Chapter04.c04_r02.arithmetic_001
#print axioms Chapter04.c04_r02.arithmetic_002
#print axioms Chapter04.c04_r02.arithmetic_003
#print axioms Chapter04.c04_r02.arithmetic_004
#print axioms Chapter04.c04_r02.arithmetic_005
#print axioms Chapter04.c04_r02.arithmetic_006
#print axioms Chapter04.c04_r02.arithmetic_007
#print axioms Chapter04.c04_r02.arithmetic_008
#print axioms Chapter04.c04_r02.arithmetic_009
#print axioms Chapter04.c04_r03.arithmetic_001
#print axioms Chapter04.c04_r03.arithmetic_002
#print axioms Chapter04.c04_r03.adjacencyRows
#print axioms Chapter04.c04_r04.arithmetic_001
#print axioms Chapter04.c04_r04.arithmetic_002
#print axioms Chapter04.c04_r04.twoStep
#print axioms Chapter04.c04_r04.entryFormula
#print axioms Chapter04.c04_r04.publishedPolysemy
#print axioms Chapter04.c04_r04.translationComposition
#print axioms Chapter04.c04_p01.arithmetic_001
#print axioms Chapter04.c04_p01.arithmetic_002
#print axioms Chapter04.c04_p01.sums
#print axioms Chapter04.c04_r05.vectorSizes
#print axioms Chapter04.c04_r06.arithmetic_001
#print axioms Chapter04.c04_r06.arithmetic_002
#print axioms Chapter04.c04_r06.arithmetic_003
#print axioms Chapter04.c04_r06.arithmetic_004
#print axioms Chapter04.c04_r06.arithmetic_005
#print axioms Chapter04.c04_r06.arithmetic_006
#print axioms Chapter04.c04_r06.arithmetic_007
#print axioms Chapter04.c04_r07.arithmetic_001
#print axioms Chapter04.c04_r07.arithmetic_002
#print axioms Chapter04.c04_r07.arithmetic_003
#print axioms Chapter04.c04_r07.arithmetic_004
#print axioms Chapter04.c04_r07.arithmetic_005
#print axioms Chapter04.c04_r07.arithmetic_006
#print axioms Chapter04.c04_r07.arithmetic_007
#print axioms Chapter04.c04_r07.arithmetic_008
#print axioms Chapter04.c04_r07.arithmetic_009
#print axioms Chapter04.c04_r07.arithmetic_010
#print axioms Chapter04.c04_r07.arithmetic_011
#print axioms Chapter04.c04_r07.arithmetic_012
#print axioms Chapter04.c04_r07.arithmetic_013
#print axioms Chapter04.c04_r07.arithmetic_014
#print axioms Chapter04.c04_r07.arithmetic_015
#print axioms Chapter04.c04_r07.arithmetic_016
#print axioms Chapter04.c04_r07.arithmetic_017
#print axioms Chapter04.c04_r07.normCherry
#print axioms Chapter04.c04_r07.normDigital
#print axioms Chapter04.c04_r07.normInformation
#print axioms Chapter04.c04_r07.positiveDenominators
#print axioms Chapter04.c04_r07.squaredBoundsImplyBounds
#print axioms Chapter04.c04_r08.arithmetic_001
#print axioms Chapter04.c04_r08.arithmetic_002
#print axioms Chapter04.c04_r08.weightedRows
#print axioms Chapter04.c04_r08.fullAddCoordinate
#print axioms Chapter04.c04_r08.weightedAddCoordinate
#print axioms Chapter04.c04_r09.sameTokens
#print axioms Chapter04.c04_p02.usualBasisSum
#print axioms Chapter04.c04_p02.transposeEntry
#print axioms Chapter04.c04_p03.arithmetic_001
#print axioms Chapter04.c04_p03.arithmetic_002
#print axioms Chapter04.c04_p03.arithmetic_003
#print axioms Chapter04.c04_p03.arithmetic_004
#print axioms Chapter04.c04_p03.arithmetic_005
#print axioms Chapter04.c04_p03.arithmetic_006
#print axioms Chapter04.c04_p03.arithmetic_007
#print axioms Chapter04.c04_p03.arithmetic_008
#print axioms Chapter04.c04_p03.arithmetic_009
#print axioms Chapter04.c04_p03.arithmetic_010
#print axioms Chapter04.c04_p03.arithmetic_011
#print axioms Chapter04.c04_p03.arithmetic_012
#print axioms Chapter04.c04_p03.arithmetic_013
#print axioms Chapter04.c04_p03.arithmetic_014
#print axioms Chapter04.c04_p03.independentDocumentColumns
#print axioms Chapter04.c04_p03.publishedDiagonalProduct
#print axioms Chapter04.c04_p04.orthogonalProduct
#print axioms Chapter04.c04_p04.alignmentEntry
#print axioms Chapter04.c04_p04.alignmentErrorNonnegative
#print axioms Chapter04.c04_p04.alignmentRoot
#print axioms Chapter04.c04_d01.arithmetic_001
#print axioms Chapter04.c04_d01.arithmetic_002
#print axioms Chapter04.c04_d01.arithmetic_003
#print axioms Chapter04.c04_d01.arithmetic_004
#print axioms Chapter04.c04_d02.arithmetic_001
#print axioms Chapter04.c04_d02.arithmetic_002
#print axioms Chapter04.c04_d03.windows
#print axioms Chapter04.c04_d04.arithmetic_001
#print axioms Chapter04.c04_d04.arithmetic_002
#print axioms Chapter04.c04_d04.publishedEntries
#print axioms Chapter04.c04_n03.arithmetic_001
#print axioms Chapter04.c04_n03.arithmetic_002
#print axioms Chapter04.c04_n03.arithmetic_003
#print axioms Chapter04.c04_n03.arithmetic_004
#print axioms Chapter04.c04_n03.arithmetic_005
#print axioms Chapter04.c04_n03.arithmetic_006
#print axioms Chapter04.c04_n03.arithmetic_007
#print axioms Chapter04.c04_n03.arithmetic_008
#print axioms Chapter04.c04_n03.arithmetic_009
#print axioms Chapter04.c04_n03.arithmetic_010
#print axioms Chapter04.c04_n01.arithmetic_001
#print axioms Chapter04.c04_n01.arithmetic_002
#print axioms Chapter04.c04_n01.arithmetic_003
#print axioms Chapter04.c04_n01.arithmetic_004
#print axioms Chapter04.c04_n01.arithmetic_005
#print axioms Chapter04.c04_n01.arithmetic_006
#print axioms Chapter04.c04_n01.arithmetic_007
#print axioms Chapter04.c04_n02.arithmetic_001
#print axioms Chapter04.c04_n02.arithmetic_002
#print axioms Chapter04.c04_n02.arithmetic_003
#print axioms Chapter04.c04_n02.arithmetic_004
#print axioms Chapter04.c04_n02.arithmetic_005
#print axioms Chapter04.c04_n02.arithmetic_006
#print axioms Chapter04.c04_n02.arithmetic_007
#print axioms Chapter04.c04_n02.arithmetic_008
#print axioms Chapter04.c04_n02.analogyCoordinate
#print axioms Chapter04.c04_n02.vectorAnalogy
#print axioms Chapter04.c04_n02.projectedDifference
