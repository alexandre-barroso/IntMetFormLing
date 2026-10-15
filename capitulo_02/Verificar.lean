import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter02

namespace c02_r01
theorem splitDuration (m x y : ℝ) : m*(x+y)=m*x+m*y := by ring
end c02_r01

namespace c02_r02
theorem arithmetic_001 : ((100*(8/100)) : ℚ) = (8) := by norm_num
theorem arithmetic_002 : ((100*(24/100)) : ℚ) = (24) := by norm_num
theorem arithmetic_003 : ((24/8) : ℚ) = (3) := by norm_num
theorem arithmetic_004 : (((8/100)*3) : ℚ) = (24/100) := by norm_num
theorem recoverCount (m L : ℝ) (hm : m ≠ 0) : (m*L)/m=L := by field_simp
end c02_r02

namespace c02_r03
theorem arithmetic_001 : ((5) : ℚ) ≤ (5) := by norm_num
theorem arithmetic_002 : ((6) : ℚ) > (5) := by norm_num
theorem filterPartition (c : ℕ) : c ≤ 5 ∨ c > 5 := le_or_gt c 5
theorem firstAccepted : ∀ c : ℕ, c > 5 ↔ 6 ≤ c := by omega
theorem reverseOrder (u v : ℝ) (h : u < v) : -u > -v := neg_lt_neg h

end c02_r03

namespace c02_r04
theorem durationZero (m : ℝ) : m*0=0 := mul_zero m
theorem positiveDuration (m L : ℝ) (hm : 0 < m) (hL : 0 < L) : 0 < m*L := mul_pos hm hL

end c02_r04

namespace c02_r05
theorem durationDifference (m L h : ℝ) : m*(L+h)-m*L=m*h := by ring
theorem durationSlope (m L h : ℝ) (hh : h ≠ 0) : (m*(L+h)-m*L)/h=m := by field_simp <;> ring

end c02_r05

namespace c02_r06
theorem arithmetic_001 : ((10^5) : ℚ) = (100000) := by norm_num
theorem arithmetic_002 : ((8*10^5) : ℚ) = (800000) := by norm_num
theorem arithmetic_003 : ((3*10^5) : ℚ) = (300000) := by norm_num
theorem arithmetic_004 : ((5*10^4) : ℚ) = (50000) := by norm_num
theorem negativeExponent (r α : ℝ) (hr : 0 < r) : r^(-α)=1/r^α := by simpa [one_div] using Real.rpow_neg (le_of_lt hr) α
theorem fractionalExponent (r : ℝ) (hr : 0 < r) : (r^((63:ℝ)/100))^(100:ℝ)=r^(63:ℝ) := by
  rw [←Real.rpow_mul (le_of_lt hr)]
  congr 1
  norm_num
theorem heapsTime (D T m beta : ℝ) (hT : 0 < T) (hm : 0 < m) :
  D*(T/m)^beta=(D/m^beta)*T^beta := by
  rw [Real.div_rpow (le_of_lt hT) (le_of_lt hm)]
  ring

end c02_r06

namespace c02_r07
theorem arithmetic_001 : ((2^9) : ℚ) = (512) := by norm_num
theorem arithmetic_002 : ((2^10) : ℚ) = (1024) := by norm_num
theorem arithmetic_003 : ((119275347/128700) : ℚ) > (512) := by norm_num
theorem arithmetic_004 : ((119275347/128700) : ℚ) < (1024) := by norm_num
theorem logProduct (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : Real.log (x*y)=Real.log x+Real.log y := Real.log_mul (ne_of_gt hx) (ne_of_gt hy)
theorem logQuotient (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : Real.log (x/y)=Real.log x-Real.log y := Real.log_div (ne_of_gt hx) (ne_of_gt hy)
theorem logExp (x : ℝ) : Real.log (Real.exp x)=x := Real.log_exp x
theorem expLog (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x)=x := Real.exp_log hx
theorem logPower (x q : ℝ) (hx : 0 < x) : Real.log (x^q)=q*Real.log x := Real.log_rpow hx q
theorem eRounded : (27175:ℝ)/10000 < Real.exp 1 ∧ Real.exp 1 < (27185:ℝ)/10000 := by
  constructor <;> linarith [Real.exp_one_gt_d9, Real.exp_one_lt_d9]

end c02_r07

namespace c02_r08
theorem arithmetic_001 : (((63/100)/20) : ℚ) = (63/2000) := by norm_num
theorem arithmetic_002 : ((63/2000) : ℚ) = (315/10000) := by norm_num
theorem arithmetic_003 : (((141/100)/20) : ℚ) = (141/2000) := by norm_num
theorem arithmetic_004 : ((141/2000) : ℚ) = (705/10000) := by norm_num
theorem rankLengthRearrangement (A C α lam l r : ℝ) (hlam : lam ≠ 0)
    (h : A-lam*l=C-α*r) : l=(α/lam)*r+(A-C)/lam := by
  field_simp
  nlinarith

end c02_r08

namespace c02_d01
theorem arithmetic_001 : ((1000*(24/100)) : ℚ) = (240) := by norm_num
theorem unitConversion (L : ℝ) : 1000*((24/100)*L)=240*L := by ring
end c02_d01

namespace c02_d02
theorem speedInverse (n y : ℝ) (hn : n ≠ 0) (hy : y ≠ 0) : n/(n*y)=1/y := by field_simp
end c02_d02

namespace c02_d03
theorem arithmetic_001 : ((5) : ℚ) ≤ (5) := by norm_num
theorem arithmetic_002 : ((6) : ℚ) > (5) := by norm_num
theorem filterPartition (c : ℕ) : c ≤ 5 ∨ c > 5 := le_or_gt c 5
theorem firstAccepted : ∀ c : ℕ, c > 5 ↔ 6 ≤ c := by omega
theorem reverseOrder (u v : ℝ) (h : u < v) : -u > -v := neg_lt_neg h

end c02_d03

namespace c02_d04
theorem arithmetic_001 : ((-63/100) : ℚ) > (-141/100) := by norm_num
theorem logFrequency (C r α : ℝ) (hC : 0 < C) (hr : 0 < r) :
  Real.log (C*r^(-α))=Real.log C-α*Real.log r := by
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hr _)), Real.log_rpow hr]
  ring

end c02_d04

namespace c02_p01
theorem arithmetic_001 : ((364/1000) : ℚ) > (0) := by norm_num
theorem arithmetic_002 : ((-227/1000) : ℚ) < (0) := by norm_num
theorem arithmetic_003 : ((-67/10000) : ℚ) < (0) := by norm_num
theorem malPositive (a b c n : ℝ) (ha : 0 < a) (hn : 0 < n) : 0 < a*n^b*Real.exp (-c*n) := mul_pos (mul_pos ha (Real.rpow_pos_of_pos hn b)) (Real.exp_pos _)
theorem malExponential (a b c n : ℝ) (hn : 0 < n) : a*n^b*Real.exp (-c*n)=a*Real.exp (b*Real.log n-c*n) := by
  rw [Real.rpow_def_of_pos hn, mul_assoc, ←Real.exp_add]
  congr 2
  ring

end c02_p01

namespace c02_p02
theorem arithmetic_001 : (((-227/1000)/(-67/10000)) : ℚ) = (2270/67) := by norm_num
theorem arithmetic_002 : ((2270/67) : ℚ) > (33875/1000) := by norm_num
theorem arithmetic_003 : ((2270/67) : ℚ) < (33885/1000) := by norm_num
theorem linearRate (m L : ℝ) : HasDerivAt (fun u : ℝ => m*u) m L := by
  simpa using (hasDerivAt_id L).const_mul m
theorem malDerivative (a b c n : ℝ) (hn : 0 < n) :
  HasDerivAt (fun x : ℝ => a*Real.exp (b*Real.log x-c*x))
    (a*Real.exp (b*Real.log n-c*n)*(b/n-c)) n := by
  have h := ((((Real.hasDerivAt_log (ne_of_gt hn)).const_mul b).sub ((hasDerivAt_id n).const_mul c)).exp).const_mul a
  convert! h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
theorem reciprocalDifference (u h : ℝ) (hu : u ≠ 0) (hh : h ≠ 0) (huh : u+h ≠ 0) :
  (1/(u+h)-1/u)/h = -1/(u*(u+h)) := by
  field_simp
  ring
theorem reciprocalDerivative (u : ℝ) (hu : u ≠ 0) :
  HasDerivAt (fun x : ℝ => 1/x) (-1/u^2) u := by
  convert! (hasDerivAt_id u).inv hu using 1
  funext x
  simp only [Pi.inv_apply, id_eq, one_div]
theorem stationaryEquation (b c n : ℝ) (hn : n ≠ 0) (hc : c ≠ 0) : b/n-c=0 ↔ n=b/c := by
  constructor <;> intro h <;> field_simp at * <;> nlinarith
theorem speedDerivative (y : ℝ → ℝ) (d n : ℝ) (hy : y n ≠ 0) (h : HasDerivAt y d n) :
  HasDerivAt (fun x => 1/y x) (-d/(y n)^2) n := by
  convert! h.inv hy using 1
  funext x
  simp only [Pi.inv_apply, one_div]

end c02_p02

namespace c02_p03
theorem equalParts (m L N : ℝ) (hN : N ≠ 0) : N*m*(L/N)=m*L := by field_simp <;> ring
theorem constantIntegral (m L : ℝ) : (∫ _ in (0:ℝ)..L, m)=m*L := by simp [mul_comm]
theorem primitiveDifference (m L : ℝ) : m*L-m*0=m*L := by ring

end c02_p03

namespace c02_p04
theorem surprisalDerivative (p : ℝ) (hp : 0 < p) :
  HasDerivAt (fun x : ℝ => -(Real.log x/Real.log 2)) (-1/(p*Real.log 2)) p := by
  have h := ((Real.hasDerivAt_log (ne_of_gt hp)).div_const (Real.log 2)).neg
  convert! h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
theorem readingDerivative (A b p : ℝ) (hp : 0 < p) :
  HasDerivAt (fun x : ℝ => A-b*Real.log x/Real.log 2) (-b/(p*Real.log 2)) p := by
  have h := (hasDerivAt_const p A).sub (((Real.hasDerivAt_log (ne_of_gt hp)).const_mul b).div_const (Real.log 2))
  convert! h using 1 <;> simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

end c02_p04

namespace c02_p05
theorem arithmetic_001 : ((14/100-3/100) : ℚ) = (11/100) := by norm_num
theorem partitionEnd (a b N : ℝ) (hN : N ≠ 0) : a+N*((b-a)/N)=b := by field_simp <;> ring
theorem partitionStart (a b N : ℝ) : a+0*((b-a)/N)=a := by ring
theorem intervalIntegrableOfContinuous (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : IntervalIntegrable f MeasureTheory.volume a b := hf.intervalIntegrable a b

end c02_p05

namespace c02_n01

open MeasureTheory
open scoped BigOperators

theorem widths (T m:ℝ) (hm:m≠0) : m*(T/m)=T := by field_simp

theorem scaledProduct (c w f:ℝ) : (c*w)*f=c*(w*f) := by ring

theorem squareScaling (c w:ℝ) : (c*w)^2=c^2*w^2 := by ring

theorem weightedSum {ι:Type*} (s:Finset ι) (v:ι→ℝ) (c:ℝ) :
    (∑ i∈s,c*v i)=c*(∑ i∈s,v i) := by simp only [Finset.mul_sum]

theorem integralScaling (c T:ℝ) (w f:ℝ→ℝ) :
    (∫ t in (0:ℝ)..T, (c*w t)*f t)=c*(∫ t in (0:ℝ)..T,w t*f t) := by
  simp only [mul_assoc, intervalIntegral.integral_const_mul]

theorem integralSquareScaling (c T:ℝ) (w:ℝ→ℝ) :
    (∫ t in (0:ℝ)..T, (c*w t)^2)=c^2*(∫ t in (0:ℝ)..T,(w t)^2) := by
  simp only [mul_pow, intervalIntegral.integral_const_mul]

theorem squareIntegralNonnegative (T:ℝ) (hT:0≤T) (w:ℝ→ℝ) :
    0≤∫ t in (0:ℝ)..T,(w t)^2 :=
  intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg (w t))

theorem continuousProductIntegrable (T:ℝ) (w f:ℝ→ℝ)
    (hw:Continuous w) (hf:Continuous f) : IntervalIntegrable (fun t=>w t*f t) volume 0 T :=
  (hw.mul hf).intervalIntegrable 0 T

end c02_n01
end Chapter02
#print axioms Chapter02.c02_r01.splitDuration
#print axioms Chapter02.c02_r02.arithmetic_001
#print axioms Chapter02.c02_r02.arithmetic_002
#print axioms Chapter02.c02_r02.arithmetic_003
#print axioms Chapter02.c02_r02.arithmetic_004
#print axioms Chapter02.c02_r02.recoverCount
#print axioms Chapter02.c02_r03.arithmetic_001
#print axioms Chapter02.c02_r03.arithmetic_002
#print axioms Chapter02.c02_r03.filterPartition
#print axioms Chapter02.c02_r03.firstAccepted
#print axioms Chapter02.c02_r03.reverseOrder
#print axioms Chapter02.c02_r04.durationZero
#print axioms Chapter02.c02_r04.positiveDuration
#print axioms Chapter02.c02_r05.durationDifference
#print axioms Chapter02.c02_r05.durationSlope
#print axioms Chapter02.c02_r06.arithmetic_001
#print axioms Chapter02.c02_r06.arithmetic_002
#print axioms Chapter02.c02_r06.arithmetic_003
#print axioms Chapter02.c02_r06.arithmetic_004
#print axioms Chapter02.c02_r06.negativeExponent
#print axioms Chapter02.c02_r06.fractionalExponent
#print axioms Chapter02.c02_r06.heapsTime
#print axioms Chapter02.c02_r07.arithmetic_001
#print axioms Chapter02.c02_r07.arithmetic_002
#print axioms Chapter02.c02_r07.arithmetic_003
#print axioms Chapter02.c02_r07.arithmetic_004
#print axioms Chapter02.c02_r07.logProduct
#print axioms Chapter02.c02_r07.logQuotient
#print axioms Chapter02.c02_r07.logExp
#print axioms Chapter02.c02_r07.expLog
#print axioms Chapter02.c02_r07.logPower
#print axioms Chapter02.c02_r07.eRounded
#print axioms Chapter02.c02_r08.arithmetic_001
#print axioms Chapter02.c02_r08.arithmetic_002
#print axioms Chapter02.c02_r08.arithmetic_003
#print axioms Chapter02.c02_r08.arithmetic_004
#print axioms Chapter02.c02_r08.rankLengthRearrangement
#print axioms Chapter02.c02_d01.arithmetic_001
#print axioms Chapter02.c02_d01.unitConversion
#print axioms Chapter02.c02_d02.speedInverse
#print axioms Chapter02.c02_d03.arithmetic_001
#print axioms Chapter02.c02_d03.arithmetic_002
#print axioms Chapter02.c02_d03.filterPartition
#print axioms Chapter02.c02_d03.firstAccepted
#print axioms Chapter02.c02_d03.reverseOrder
#print axioms Chapter02.c02_d04.arithmetic_001
#print axioms Chapter02.c02_d04.logFrequency
#print axioms Chapter02.c02_p01.arithmetic_001
#print axioms Chapter02.c02_p01.arithmetic_002
#print axioms Chapter02.c02_p01.arithmetic_003
#print axioms Chapter02.c02_p01.malPositive
#print axioms Chapter02.c02_p01.malExponential
#print axioms Chapter02.c02_p02.arithmetic_001
#print axioms Chapter02.c02_p02.arithmetic_002
#print axioms Chapter02.c02_p02.arithmetic_003
#print axioms Chapter02.c02_p02.linearRate
#print axioms Chapter02.c02_p02.malDerivative
#print axioms Chapter02.c02_p02.reciprocalDifference
#print axioms Chapter02.c02_p02.reciprocalDerivative
#print axioms Chapter02.c02_p02.stationaryEquation
#print axioms Chapter02.c02_p02.speedDerivative
#print axioms Chapter02.c02_p03.equalParts
#print axioms Chapter02.c02_p03.constantIntegral
#print axioms Chapter02.c02_p03.primitiveDifference
#print axioms Chapter02.c02_p04.surprisalDerivative
#print axioms Chapter02.c02_p04.readingDerivative
#print axioms Chapter02.c02_p05.arithmetic_001
#print axioms Chapter02.c02_p05.partitionEnd
#print axioms Chapter02.c02_p05.partitionStart
#print axioms Chapter02.c02_p05.intervalIntegrableOfContinuous
#print axioms Chapter02.c02_n01.widths
#print axioms Chapter02.c02_n01.scaledProduct
#print axioms Chapter02.c02_n01.squareScaling
#print axioms Chapter02.c02_n01.weightedSum
#print axioms Chapter02.c02_n01.integralScaling
#print axioms Chapter02.c02_n01.integralSquareScaling
#print axioms Chapter02.c02_n01.squareIntegralNonnegative
#print axioms Chapter02.c02_n01.continuousProductIntegrable
