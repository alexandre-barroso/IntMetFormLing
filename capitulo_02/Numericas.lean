import Mathlib
namespace Chapter02NumericalExpressions

theorem c02_e0031_1 : (((2/25)*3):ℚ) = ((6/25)) := by norm_num
#print axioms c02_e0031_1
theorem c02_e0095_1 : ((10^5):ℚ) = (((((10*10)*10)*10)*10)) := by norm_num
#print axioms c02_e0095_1
theorem c02_e0095_2 : (((((10*10)*10)*10)*10):ℚ) = (100000) := by norm_num
#print axioms c02_e0095_2
theorem c02_e0096_1 : ((8*(10^5)):ℚ) = (800000) := by norm_num
#print axioms c02_e0096_1
theorem c02_e0097_1 : ((3*(10^5)):ℚ) = (300000) := by norm_num
#print axioms c02_e0097_1
theorem c02_e0098_1 : ((5*(10^4)):ℚ) = (50000) := by norm_num
#print axioms c02_e0098_1
theorem c02_e0134_1 : ((2^9):ℚ) = (512) := by norm_num
#print axioms c02_e0134_1
theorem c02_e0135_1 : ((2^10):ℚ) = (1024) := by norm_num
#print axioms c02_e0135_1
theorem c02_e0197_1 : (((63/100)*(1/(20^1))):ℚ) = ((63/2000)) := by norm_num
#print axioms c02_e0197_1
theorem c02_e0198_1 : (((141/100)*(1/(20^1))):ℚ) = ((141/2000)) := by norm_num
#print axioms c02_e0198_1
theorem c02_e0270_1 : (((-1*(227/1000))*(1/((-1*(67/10000))^1))):ℚ) = (((227/1000)*(1/((67/10000)^1)))) := by norm_num
#print axioms c02_e0270_1
theorem c02_e0270_2 : (((227/1000)*(1/((67/10000)^1))):ℚ) = ((2270*(1/(67^1)))) := by norm_num
#print axioms c02_e0270_2
theorem c02_e0270_3 : |((2270*(1/(67^1))):ℚ)-((847/25))|≤(1/200) := by norm_num
#print axioms c02_e0270_3
end Chapter02NumericalExpressions
