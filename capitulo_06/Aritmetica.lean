import Mathlib
namespace Chapter06SourceArithmetic
theorem c06_e0014 : (((((((1+2)+1)+3)+1)/8) : ℚ) = (8/8)) ∧ (((8/8) : ℚ) = 1) := by norm_num
#print axioms c06_e0014
theorem c06_e0033 : ((((2/8)*(1/8)) : ℚ) = (1/32)) := by norm_num
#print axioms c06_e0033
theorem c06_e0057 : ((((1/2)/((1/2)+(1/2))) : ℚ) = (1/2)) := by norm_num
#print axioms c06_e0057
theorem c06_e0061 : ((((1/2)/((1/2)+1)) : ℚ) = (1/3)) := by norm_num
#print axioms c06_e0061
theorem c06_e0087 : (((Nat.factorial 0 : ℚ) : ℚ) = 1) := by norm_num
#print axioms c06_e0087
theorem c06_e0096 : (((Nat.factorial 100 : ℚ) : ℚ) = (100*(Nat.factorial 99 : ℚ))) := by norm_num
#print axioms c06_e0096
theorem c06_e0097 : (((Nat.factorial 1 : ℚ) : ℚ) = 1) := by norm_num
#print axioms c06_e0097
theorem c06_e0119 : ((((30/100)*(40/100)) : ℚ) = (3/25)) := by norm_num
#print axioms c06_e0119
theorem c06_e0120 : ((((70/100)*(60/100)) : ℚ) = (21/50)) := by norm_num
#print axioms c06_e0120
theorem c06_e0136 : (((1/(2^1)) : ℚ) = (1/2)) := by norm_num
#print axioms c06_e0136
theorem c06_e0143 : ((((2/8)*(1/2)) : ℚ) = (1/8)) := by norm_num
#print axioms c06_e0143
theorem c06_e0181 : (((30/6) : ℚ) = 5) := by norm_num
#print axioms c06_e0181
theorem c06_e0207 : ((((1/2)+1) : ℚ) = (3/2)) := by norm_num
#print axioms c06_e0207
theorem c06_e0231 : (((((9+4)+9)/8) : ℚ) = (22/8)) ∧ (((22/8) : ℚ) = (11/4)) := by norm_num
#print axioms c06_e0231
theorem c06_e0257 : ((((2/3)+(1/3)) : ℚ) = 1) := by norm_num
#print axioms c06_e0257
theorem c06_e0334 : (((2*((59/100)^2)) : ℚ) = (2*(3481/10000))) ∧ (((2*(3481/10000)) : ℚ) = (3481/5000)) := by norm_num
#print axioms c06_e0334
end Chapter06SourceArithmetic
