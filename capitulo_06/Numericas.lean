import Mathlib
namespace Chapter06NumericalExpressions

theorem c06_e0014_1 : ((((((1+2)+1)+3)+1)*(1/(8^1))):ℚ) = ((8*(1/(8^1)))) := by norm_num
#print axioms c06_e0014_1
theorem c06_e0014_2 : ((8*(1/(8^1))):ℚ) = (1) := by norm_num
#print axioms c06_e0014_2
theorem c06_e0021_1 : (((1*(1/(8^1)))*(1/((2*(1/(8^1)))^1))):ℚ) = (((1*(1/(8^1)))*(8*(1/(2^1))))) := by norm_num
#print axioms c06_e0021_1
theorem c06_e0021_2 : (((1*(1/(8^1)))*(8*(1/(2^1)))):ℚ) = ((1*(1/(2^1)))) := by norm_num
#print axioms c06_e0021_2
theorem c06_e0024_1 : (((1*(1/(8^1)))*(1/((1*(1/(8^1)))^1))):ℚ) = (1) := by norm_num
#print axioms c06_e0024_1
theorem c06_e0025_1 : (((2*(1/(8^1)))*(1/((3*(1/(8^1)))^1))):ℚ) = ((2*(1/(3^1)))) := by norm_num
#print axioms c06_e0025_1
theorem c06_e0025_2 : (((1*(1/(8^1)))*(1/((3*(1/(8^1)))^1))):ℚ) = ((1*(1/(3^1)))) := by norm_num
#print axioms c06_e0025_2
theorem c06_e0028_1 : (((2*(1/(8^1)))*(1*(1/(2^1)))):ℚ) = ((2*(1/(16^1)))) := by norm_num
#print axioms c06_e0028_1
theorem c06_e0033_1 : (((2*(1/(8^1)))*(1*(1/(8^1)))):ℚ) = ((1*(1/(32^1)))) := by norm_num
#print axioms c06_e0033_1
theorem c06_e0057_1 : (((1*(1/(2^1)))*(1/(((1*(1/(2^1)))+(1*(1/(2^1))))^1))):ℚ) = ((1*(1/(2^1)))) := by norm_num
#print axioms c06_e0057_1
theorem c06_e0061_1 : (((1*(1/(2^1)))*(1/(((1*(1/(2^1)))+1)^1))):ℚ) = ((1*(1/(3^1)))) := by norm_num
#print axioms c06_e0061_1
theorem c06_e0091_1 : (((1/10)*(1/(100^1))):ℚ) = ((1/1000)) := by norm_num
#print axioms c06_e0091_1
theorem c06_e0095_1 : (((1*1)*((1+(-1*(1/1000)))^100)):ℚ) = (((999/1000)^100)) := by norm_num
#print axioms c06_e0095_1
theorem c06_e0113_1 : ((100*(1/1000)):ℚ) = ((1/10)) := by norm_num
#print axioms c06_e0113_1
theorem c06_e0114_1 : (((100*(1/1000))*(999/1000)):ℚ) = ((999/10000)) := by norm_num
#print axioms c06_e0114_1
theorem c06_e0115_1 : (((20+50)*(1/(100^1))):ℚ) = ((70*(1/(100^1)))) := by norm_num
#print axioms c06_e0115_1
theorem c06_e0115_2 : ((70*(1/(100^1))):ℚ) = ((7/10)) := by norm_num
#print axioms c06_e0115_2
theorem c06_e0119_1 : (((30*(1/(100^1)))*(40*(1/(100^1)))):ℚ) = ((3/25)) := by norm_num
#print axioms c06_e0119_1
theorem c06_e0120_1 : (((70*(1/(100^1)))*(60*(1/(100^1)))):ℚ) = ((21/50)) := by norm_num
#print axioms c06_e0120_1
theorem c06_e0121_1 : (((3/25)+(21/50)):ℚ) = ((27/50)) := by norm_num
#print axioms c06_e0121_1
theorem c06_e0124_1 : ((((7/10)+(-1*(27/50)))*(1/((1+(-1*(27/50)))^1))):ℚ) = (((4/25)*(1/((23/50)^1)))) := by norm_num
#print axioms c06_e0124_1
theorem c06_e0124_2 : ((16*(1/(46^1))):ℚ) = ((8*(1/(23^1)))) := by norm_num
#print axioms c06_e0124_2
theorem c06_e0136_1 : ((1/(2^1)):ℚ) = ((1*(1/(2^1)))) := by norm_num
#print axioms c06_e0136_1
theorem c06_e0137_1 : ((-1*(-1*1)):ℚ) = (1) := by norm_num
#print axioms c06_e0137_1
theorem c06_e0143_1 : (((2*(1/(8^1)))*(1*(1/(2^1)))):ℚ) = ((1*(1/(8^1)))) := by norm_num
#print axioms c06_e0143_1
theorem c06_e0165_1 : ((8*((1*(1/(8^1)))*3)):ℚ) = ((8*(3*(1/(8^1))))) := by norm_num
#print axioms c06_e0165_1
theorem c06_e0165_2 : ((8*(3*(1/(8^1)))):ℚ) = (3) := by norm_num
#print axioms c06_e0165_2
theorem c06_e0181_1 : ((30*(1/(6^1))):ℚ) = (5) := by norm_num
#print axioms c06_e0181_1
theorem c06_e0207_1 : (((1*(1/(2^1)))+1):ℚ) = ((3*(1/(2^1)))) := by norm_num
#print axioms c06_e0207_1
theorem c06_e0208_1 : (((1*(1/(2^1)))*(1/((3*(1/(2^1)))^1))):ℚ) = (((1*(1/(2^1)))*(2*(1/(3^1))))) := by norm_num
#print axioms c06_e0208_1
theorem c06_e0208_2 : (((1*(1/(2^1)))*(2*(1/(3^1)))):ℚ) = ((1*(1/(3^1)))) := by norm_num
#print axioms c06_e0208_2
theorem c06_e0208_3 : ((1*(1/((3*(1/(2^1)))^1))):ℚ) = ((2*(1/(3^1)))) := by norm_num
#print axioms c06_e0208_3
theorem c06_e0231_1 : ((((9+4)+9)*(1/(8^1))):ℚ) = ((22*(1/(8^1)))) := by norm_num
#print axioms c06_e0231_1
theorem c06_e0231_2 : ((22*(1/(8^1))):ℚ) = ((11*(1/(4^1)))) := by norm_num
#print axioms c06_e0231_2
theorem c06_e0245_1 : (((1*(1/(8^1)))*(1/((2*(1/(8^1)))^1))):ℚ) = ((1*(1/(2^1)))) := by norm_num
#print axioms c06_e0245_1
theorem c06_e0257_1 : (((2*(1/(3^1)))+(1*(1/(3^1)))):ℚ) = (1) := by norm_num
#print axioms c06_e0257_1
theorem c06_e0290_1 : ((0+(-1*0)):ℚ) = (0) := by norm_num
#print axioms c06_e0290_1
theorem c06_e0332_1 : ((2*((59/100)^2)):ℚ) = ((2*(3481/10000))) := by norm_num
#print axioms c06_e0332_1
theorem c06_e0332_2 : ((2*(3481/10000)):ℚ) = ((3481/5000)) := by norm_num
#print axioms c06_e0332_2
end Chapter06NumericalExpressions
