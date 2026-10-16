import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter01

namespace c01_p01
theorem arithmetic_001 : ((660*195) : ℚ) = (128700) := by norm_num
theorem arithmetic_002 : ((660*(195/4112943)) : ℚ) = (128700/4112943) := by norm_num
theorem arithmetic_003 : ((29/(128700/4112943)) : ℚ) = (29*4112943/128700) := by norm_num
theorem arithmetic_004 : ((29*4112943) : ℚ) = (119275347) := by norm_num
theorem arithmetic_005 : ((128700/4112943) : ℚ) > (3/100) := by norm_num
theorem arithmetic_006 : ((128700/4112943) : ℚ) < (4/100) := by norm_num
theorem arithmetic_007 : ((119275347/128700) : ℚ) > (926) := by norm_num
theorem arithmetic_008 : ((119275347/128700) : ℚ) < (927) := by norm_num
end c01_p01

namespace c01_b01
theorem arithmetic_001 : ((19+4) : ℚ) = (23) := by norm_num
theorem arithmetic_002 : ((23) : ℚ) ≠ (19) := by norm_num
end c01_b01

namespace c01_b02
theorem arithmetic_001 : ((19+4) : ℚ) = (23) := by norm_num
theorem arithmetic_002 : ((23-19) : ℚ) = (4) := by norm_num
theorem arithmetic_003 : ((24/100/(8/100)) : ℚ) = (3) := by norm_num
end c01_b02

namespace c01_b03
theorem arithmetic_001 : ((65) : ℚ) = (60+5) := by norm_num
theorem arithmetic_002 : ((23) : ℚ) = (20+3) := by norm_num
theorem arithmetic_003 : ((23+27) : ℚ) = ((20+3)+(20+7)) := by norm_num
theorem arithmetic_004 : (((20+3)+(20+7)) : ℚ) = (40+10) := by norm_num
theorem arithmetic_005 : ((40+10) : ℚ) = (50) := by norm_num
end c01_b03

namespace c01_b04
theorem arithmetic_001 : ((14/16) : ℚ) = (7/8) := by norm_num
theorem arithmetic_002 : ((7/8) : ℚ) = (875/1000) := by norm_num
theorem arithmetic_003 : ((7/8*100) : ℚ) = (875/10) := by norm_num
end c01_b04

namespace c01_b05
theorem arithmetic_001 : ((8/100-24/100) : ℚ) = (-16/100) := by norm_num
theorem arithmetic_002 : ((|(-16/100)|) : ℚ) = (16/100) := by norm_num
theorem arithmetic_003 : ((8/100) : ℚ) < (24/100) := by norm_num
end c01_b05

namespace c01_r01
theorem arithmetic_001 : ((16-2) : ℚ) = (14) := by norm_num
theorem arithmetic_002 : ((16+2) : ℚ) = (18) := by norm_num
theorem publishedTokens : (["they", "picnicked", "by", "the", "pool", "then", "lay", "back", "on", "the", "grass", "and", "looked", "at", "the", "stars"] : List String).length=16 ∧ (["they", "picnicked", "by", "the", "pool", "then", "lay", "back", "on", "the", "grass", "and", "looked", "at", "the", "stars"] : List String).dedup.length=14 ∧ (["they", "picnicked", "by", "the", "pool", "then", "lay", "back", "on", "the", "grass", "and", "looked", "at", "the", "stars"] : List String).count "the"=3 := by decide +kernel
end c01_r01

namespace c01_r02
theorem arithmetic_001 : ((8/100*1000) : ℚ) = (8000/100) := by norm_num
theorem arithmetic_002 : ((8000/100) : ℚ) = (80) := by norm_num
theorem arithmetic_003 : ((24/100*1000) : ℚ) = (240) := by norm_num
theorem arithmetic_004 : ((240/1000) : ℚ) = (24/100) := by norm_num
end c01_r02

namespace c01_r03
theorem arithmetic_001 : ((8/100-24/100) : ℚ) = ((8-24)/100) := by norm_num
theorem arithmetic_002 : (((8-24)/100) : ℚ) = (-16/100) := by norm_num
theorem arithmetic_003 : ((|(-16/100)|) : ℚ) = (16/100) := by norm_num
theorem arithmetic_004 : ((16/100*1000) : ℚ) = (160) := by norm_num
theorem arithmetic_005 : ((24/100-8/100) : ℚ) = (16/100) := by norm_num
theorem arithmetic_006 : ((24/100/(8/100)) : ℚ) = (3) := by norm_num
end c01_r03

namespace c01_r04
theorem arithmetic_001 : ((23+27+5+10) : ℚ) = (50+5+10) := by norm_num
theorem arithmetic_002 : ((50+5+10) : ℚ) = (65) := by norm_num
theorem arithmetic_003 : ((19+4) : ℚ) = (23) := by norm_num
end c01_r04

namespace c01_r05
theorem arithmetic_001 : ((14/100-3/100) : ℚ) = (11/100) := by norm_num
theorem arithmetic_002 : ((11/100*1000) : ℚ) = (110) := by norm_num
theorem arithmetic_003 : ((3/100) : ℚ) < (14/100) := by norm_num
end c01_r05

namespace c01_r06
theorem arithmetic_001 : ((19/65+4/65) : ℚ) = ((19+4)/65) := by norm_num
theorem arithmetic_002 : (((19+4)/65) : ℚ) = (23/65) := by norm_num
theorem arithmetic_003 : ((23/65+27/65+5/65+10/65) : ℚ) = ((23+27+5+10)/65) := by norm_num
theorem arithmetic_004 : (((23+27+5+10)/65) : ℚ) = (65/65) := by norm_num
theorem arithmetic_005 : ((65/65) : ℚ) = (1) := by norm_num
theorem arithmetic_006 : ((1*100) : ℚ) = (100) := by norm_num
theorem arithmetic_007 : ((10/65) : ℚ) = ((10/5)/(65/5)) := by norm_num
theorem arithmetic_008 : (((10/5)/(65/5)) : ℚ) = (2/13) := by norm_num
end c01_r06

namespace c01_r07
theorem arithmetic_001 : ((14/168799*120000) : ℚ) = (1680000/168799) := by norm_num
theorem arithmetic_002 : ((14*120000) : ℚ) = (1680000) := by norm_num
theorem arithmetic_003 : ((242/4623107*120000) : ℚ) = (29040000/4623107) := by norm_num
theorem arithmetic_004 : ((242*120000) : ℚ) = (29040000) := by norm_num
theorem arithmetic_005 : ((1680000/168799) : ℚ) > (9945/1000) := by norm_num
theorem arithmetic_006 : ((1680000/168799) : ℚ) < (9955/1000) := by norm_num
theorem arithmetic_007 : ((29040000/4623107) : ℚ) > (6275/1000) := by norm_num
theorem arithmetic_008 : ((29040000/4623107) : ℚ) < (6285/1000) := by norm_num
theorem arithmetic_009 : ((14) : ℚ) < (242) := by norm_num
theorem arithmetic_010 : ((995/100) : ℚ) > (628/100) := by norm_num
end c01_r07

namespace c01_r08
theorem arithmetic_001 : ((706/10-584/10) : ℚ) = (122/10) := by norm_num
theorem arithmetic_002 : (((706/10-584/10)/(584/10)) : ℚ) = ((122/10)/(584/10)) := by norm_num
theorem arithmetic_003 : (((122/10)/(584/10)) : ℚ) = (122/584) := by norm_num
theorem arithmetic_004 : ((122/584) : ℚ) = (61/292) := by norm_num
theorem arithmetic_005 : ((61/292) : ℚ) > (2085/10000) := by norm_num
theorem arithmetic_006 : ((61/292) : ℚ) < (2095/10000) := by norm_num
end c01_r08

namespace c01_r09
theorem distributeMean {ι : Type*} (s : Finset ι) (t : ι → ℝ) (n : ℝ) : (∑ i ∈ s, t i)/n = ∑ i ∈ s, (1/n)*t i := by
  simp only [div_eq_mul_inv, one_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring
theorem equalWeights (n : ℝ) (hn : n ≠ 0) : n*(1/n)=1 := by field_simp

end c01_r09

namespace c01_r10
theorem arithmetic_001 : ((25-23) : ℚ) = (2) := by norm_num
theorem arithmetic_002 : ((23-25) : ℚ) = (-2) := by norm_num
theorem arithmetic_003 : ((23) : ℚ) < (25) := by norm_num
end c01_r10

namespace c01_r11
theorem zeroProduct (q : ℝ) : 0*q=0 := zero_mul q
end c01_r11

namespace c01_d01
theorem arithmetic_001 : ((2-1) : ℚ) = (1) := by norm_num
end c01_d01

namespace c01_d02
theorem arithmetic_001 : ((65/666*100) : ℚ) = (6500/666) := by norm_num
theorem arithmetic_002 : ((6500/666) : ℚ) > (9755/1000) := by norm_num
theorem arithmetic_003 : ((6500/666) : ℚ) < (9765/1000) := by norm_num
end c01_d02

namespace c01_d03
theorem arithmetic_001 : ((78/356-49/356) : ℚ) = ((78-49)/356) := by norm_num
theorem arithmetic_002 : (((78-49)/356) : ℚ) = (29/356) := by norm_num
theorem arithmetic_003 : ((31/20772) : ℚ) > (145/100000) := by norm_num
theorem arithmetic_004 : ((31/20772) : ℚ) < (155/100000) := by norm_num
theorem arithmetic_005 : ((382/1702) : ℚ) > (22435/100000) := by norm_num
theorem arithmetic_006 : ((382/1702) : ℚ) < (22445/100000) := by norm_num
theorem arithmetic_007 : ((78/356) : ℚ) > (21905/100000) := by norm_num
theorem arithmetic_008 : ((78/356) : ℚ) < (21915/100000) := by norm_num
theorem arithmetic_009 : ((49/356) : ℚ) > (13755/100000) := by norm_num
theorem arithmetic_010 : ((49/356) : ℚ) < (13765/100000) := by norm_num
theorem arithmetic_011 : ((78/356) : ℚ) > (49/356) := by norm_num
end c01_d03

namespace c01_d04
theorem arithmetic_001 : ((180/1012985*120000) : ℚ) = (21600000/1012985) := by norm_num
theorem arithmetic_002 : ((180*120000) : ℚ) = (21600000) := by norm_num
theorem arithmetic_003 : ((236/1009304*120000) : ℚ) = (28320000/1009304) := by norm_num
theorem arithmetic_004 : ((236*120000) : ℚ) = (28320000) := by norm_num
theorem arithmetic_005 : ((21600000/1012985) : ℚ) > (21315/1000) := by norm_num
theorem arithmetic_006 : ((21600000/1012985) : ℚ) < (21325/1000) := by norm_num
theorem arithmetic_007 : ((28320000/1009304) : ℚ) > (28055/1000) := by norm_num
theorem arithmetic_008 : ((28320000/1009304) : ℚ) < (28065/1000) := by norm_num
end c01_d04
end Chapter01
#print axioms Chapter01.c01_p01.arithmetic_001
#print axioms Chapter01.c01_p01.arithmetic_002
#print axioms Chapter01.c01_p01.arithmetic_003
#print axioms Chapter01.c01_p01.arithmetic_004
#print axioms Chapter01.c01_p01.arithmetic_005
#print axioms Chapter01.c01_p01.arithmetic_006
#print axioms Chapter01.c01_p01.arithmetic_007
#print axioms Chapter01.c01_p01.arithmetic_008
#print axioms Chapter01.c01_b01.arithmetic_001
#print axioms Chapter01.c01_b01.arithmetic_002
#print axioms Chapter01.c01_b02.arithmetic_001
#print axioms Chapter01.c01_b02.arithmetic_002
#print axioms Chapter01.c01_b02.arithmetic_003
#print axioms Chapter01.c01_b03.arithmetic_001
#print axioms Chapter01.c01_b03.arithmetic_002
#print axioms Chapter01.c01_b03.arithmetic_003
#print axioms Chapter01.c01_b03.arithmetic_004
#print axioms Chapter01.c01_b03.arithmetic_005
#print axioms Chapter01.c01_b04.arithmetic_001
#print axioms Chapter01.c01_b04.arithmetic_002
#print axioms Chapter01.c01_b04.arithmetic_003
#print axioms Chapter01.c01_b05.arithmetic_001
#print axioms Chapter01.c01_b05.arithmetic_002
#print axioms Chapter01.c01_b05.arithmetic_003
#print axioms Chapter01.c01_r01.arithmetic_001
#print axioms Chapter01.c01_r01.arithmetic_002
#print axioms Chapter01.c01_r01.publishedTokens
#print axioms Chapter01.c01_r02.arithmetic_001
#print axioms Chapter01.c01_r02.arithmetic_002
#print axioms Chapter01.c01_r02.arithmetic_003
#print axioms Chapter01.c01_r02.arithmetic_004
#print axioms Chapter01.c01_r03.arithmetic_001
#print axioms Chapter01.c01_r03.arithmetic_002
#print axioms Chapter01.c01_r03.arithmetic_003
#print axioms Chapter01.c01_r03.arithmetic_004
#print axioms Chapter01.c01_r03.arithmetic_005
#print axioms Chapter01.c01_r03.arithmetic_006
#print axioms Chapter01.c01_r04.arithmetic_001
#print axioms Chapter01.c01_r04.arithmetic_002
#print axioms Chapter01.c01_r04.arithmetic_003
#print axioms Chapter01.c01_r05.arithmetic_001
#print axioms Chapter01.c01_r05.arithmetic_002
#print axioms Chapter01.c01_r05.arithmetic_003
#print axioms Chapter01.c01_r06.arithmetic_001
#print axioms Chapter01.c01_r06.arithmetic_002
#print axioms Chapter01.c01_r06.arithmetic_003
#print axioms Chapter01.c01_r06.arithmetic_004
#print axioms Chapter01.c01_r06.arithmetic_005
#print axioms Chapter01.c01_r06.arithmetic_006
#print axioms Chapter01.c01_r06.arithmetic_007
#print axioms Chapter01.c01_r06.arithmetic_008
#print axioms Chapter01.c01_r07.arithmetic_001
#print axioms Chapter01.c01_r07.arithmetic_002
#print axioms Chapter01.c01_r07.arithmetic_003
#print axioms Chapter01.c01_r07.arithmetic_004
#print axioms Chapter01.c01_r07.arithmetic_005
#print axioms Chapter01.c01_r07.arithmetic_006
#print axioms Chapter01.c01_r07.arithmetic_007
#print axioms Chapter01.c01_r07.arithmetic_008
#print axioms Chapter01.c01_r07.arithmetic_009
#print axioms Chapter01.c01_r07.arithmetic_010
#print axioms Chapter01.c01_r08.arithmetic_001
#print axioms Chapter01.c01_r08.arithmetic_002
#print axioms Chapter01.c01_r08.arithmetic_003
#print axioms Chapter01.c01_r08.arithmetic_004
#print axioms Chapter01.c01_r08.arithmetic_005
#print axioms Chapter01.c01_r08.arithmetic_006
#print axioms Chapter01.c01_r09.distributeMean
#print axioms Chapter01.c01_r09.equalWeights
#print axioms Chapter01.c01_r10.arithmetic_001
#print axioms Chapter01.c01_r10.arithmetic_002
#print axioms Chapter01.c01_r10.arithmetic_003
#print axioms Chapter01.c01_r11.zeroProduct
#print axioms Chapter01.c01_d01.arithmetic_001
#print axioms Chapter01.c01_d02.arithmetic_001
#print axioms Chapter01.c01_d02.arithmetic_002
#print axioms Chapter01.c01_d02.arithmetic_003
#print axioms Chapter01.c01_d03.arithmetic_001
#print axioms Chapter01.c01_d03.arithmetic_002
#print axioms Chapter01.c01_d03.arithmetic_003
#print axioms Chapter01.c01_d03.arithmetic_004
#print axioms Chapter01.c01_d03.arithmetic_005
#print axioms Chapter01.c01_d03.arithmetic_006
#print axioms Chapter01.c01_d03.arithmetic_007
#print axioms Chapter01.c01_d03.arithmetic_008
#print axioms Chapter01.c01_d03.arithmetic_009
#print axioms Chapter01.c01_d03.arithmetic_010
#print axioms Chapter01.c01_d03.arithmetic_011
#print axioms Chapter01.c01_d04.arithmetic_001
#print axioms Chapter01.c01_d04.arithmetic_002
#print axioms Chapter01.c01_d04.arithmetic_003
#print axioms Chapter01.c01_d04.arithmetic_004
#print axioms Chapter01.c01_d04.arithmetic_005
#print axioms Chapter01.c01_d04.arithmetic_006
#print axioms Chapter01.c01_d04.arithmetic_007
#print axioms Chapter01.c01_d04.arithmetic_008
