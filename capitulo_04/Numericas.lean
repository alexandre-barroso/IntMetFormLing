import Mathlib
namespace Chapter04NumericalExpressions

theorem c04_e0008_1 : (|1|:ℚ) = (1) := by norm_num
#print axioms c04_e0008_1
theorem c04_e0008_2 : (|(-1*1)|:ℚ) = (1) := by norm_num
#print axioms c04_e0008_2
theorem c04_e0008_3 : (|(-1*3)|:ℚ) = (3) := by norm_num
#print axioms c04_e0008_3
theorem c04_e0010_1 : ((((1+1)+3)+1):ℚ) = (6) := by norm_num
#print axioms c04_e0010_1
theorem c04_e0013_1 : (|(1+(-1*5))|:ℚ) = (4) := by norm_num
#print axioms c04_e0013_1
theorem c04_e0014_1 : ((((|(2+(-1*1))|+|(2+(-1*5))|)+|(2+(-1*4))|)+|(4+(-1*3))|):ℚ) = ((((1+3)+2)+1)) := by norm_num
#print axioms c04_e0014_1
theorem c04_e0014_2 : ((((1+3)+2)+1):ℚ) = (7) := by norm_num
#print axioms c04_e0014_2
theorem c04_e0015_1 : (((3+(-1*1))+(2+(-1*3))):ℚ) = ((2+(-1*1))) := by norm_num
#print axioms c04_e0015_1
theorem c04_e0015_2 : ((2+(-1*1)):ℚ) = (1) := by norm_num
#print axioms c04_e0015_2
theorem c04_e0028_1 : (((((1+0)+1)+0)+1):ℚ) = (3) := by norm_num
#print axioms c04_e0028_1
theorem c04_e0049_1 : (((1*1)+(1*1)):ℚ) = (2) := by norm_num
#print axioms c04_e0049_1
theorem c04_e0062_1 : (((((((((1+1)+4)+2)+1)+1)+1)+2)+1):ℚ) = (14) := by norm_num
#print axioms c04_e0062_1
theorem c04_e0075_1 : (((4*(4+(-1*1)))*(1/(2^1))):ℚ) = (((4*3)*(1/(2^1)))) := by norm_num
#print axioms c04_e0075_1
theorem c04_e0075_2 : (((4*3)*(1/(2^1))):ℚ) = (6) := by norm_num
#print axioms c04_e0075_2
theorem c04_e0098_1 : ((((1*(-1*4))+((41/10)*0))+(1*(-1*4))):ℚ) = ((((-1*4)+0)+(-1*4))) := by norm_num
#print axioms c04_e0098_1
theorem c04_e0098_2 : ((((-1*4)+0)+(-1*4)):ℚ) = ((-1*8)) := by norm_num
#print axioms c04_e0098_2
theorem c04_e0099_1 : ((((1*0)+((41/10)*(-1*2)))+(1*0)):ℚ) = (((0+(-1*(41/5)))+0)) := by norm_num
#print axioms c04_e0099_1
theorem c04_e0099_2 : (((0+(-1*(41/5)))+0):ℚ) = ((-1*(41/5))) := by norm_num
#print axioms c04_e0099_2
theorem c04_e0100_1 : ((-1*8):ℚ) > ((-1*(41/5))) := by norm_num
#print axioms c04_e0100_1
theorem c04_e0107_1 : (((25+6701706)+5552750):ℚ) = (12254481) := by norm_num
#print axioms c04_e0107_1
theorem c04_e0112_1 : (((903/1000)*100):ℚ) = ((903/10)) := by norm_num
#print axioms c04_e0112_1
theorem c04_e0113_1 : (((1/20)*100):ℚ) = (5) := by norm_num
#print axioms c04_e0113_1
theorem c04_e0273_1 : (((1837/12500)+(4191/250000)):ℚ) = ((40931/250000)) := by norm_num
#print axioms c04_e0273_1
theorem c04_e0277_1 : (((112057/250000)+(-1*(23749/500000))):ℚ) = ((40073/100000)) := by norm_num
#print axioms c04_e0277_1
end Chapter04NumericalExpressions
