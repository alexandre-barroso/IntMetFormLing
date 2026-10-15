import Mathlib
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Chapter09

namespace c09_r01
theorem arithmetic_001 : ((86239-55632) : ℚ) = (30607) := by norm_num
theorem arithmetic_002 : ((55632) : ℚ) < (86239) := by norm_num
theorem arithmetic_003 : ((783) : ℚ) ≤ (55632) := by norm_num
end c09_r01

namespace c09_r02
theorem arithmetic_001 : ((3961-39) : ℚ) = (3922) := by norm_num
theorem arithmetic_002 : ((39) : ℚ) ≤ (3961) := by norm_num

def publishedTokens : List String := ["mò","zhī","néng","yù","yě"]
theorem publishedObjectVerbPositions : publishedTokens.idxOf "zhī" + 1 = 2 ∧ publishedTokens.idxOf "yù" + 1 = 4 := by decide +kernel
theorem publishedOV : publishedTokens.idxOf "zhī" < publishedTokens.idxOf "yù" := by decide +kernel
end c09_r02

namespace c09_r03
theorem arithmetic_001 : ((395-292) : ℚ) = (103) := by norm_num
theorem arithmetic_002 : ((601) : ℚ) ≤ (5509) := by norm_num
theorem arithmetic_003 : ((292) : ℚ) ≤ (395) := by norm_num
theorem arithmetic_004 : ((89) : ℚ) ≤ (209) := by norm_num
theorem arithmetic_005 : ((292) : ℚ) ≤ (601) := by norm_num
end c09_r03

namespace c09_r04
theorem arithmetic_001 : ((100*292/395) : ℚ) = (29200/395) := by norm_num
theorem arithmetic_002 : ((100*292/783) : ℚ) = (29200/783) := by norm_num
theorem arithmetic_003 : ((100*601/5509) : ℚ) ≥ (217/20) := by norm_num
theorem arithmetic_004 : ((100*601/5509) : ℚ) < (219/20) := by norm_num
theorem arithmetic_005 : ((100*292/395) : ℚ) ≥ (1477/20) := by norm_num
theorem arithmetic_006 : ((100*292/395) : ℚ) < (1479/20) := by norm_num
theorem arithmetic_007 : ((100*89/209) : ℚ) ≥ (851/20) := by norm_num
theorem arithmetic_008 : ((100*89/209) : ℚ) < (853/20) := by norm_num
theorem arithmetic_009 : ((100*601/783) : ℚ) ≥ (1535/20) := by norm_num
theorem arithmetic_010 : ((100*601/783) : ℚ) < (1537/20) := by norm_num
theorem arithmetic_011 : ((100*292/783) : ℚ) ≥ (745/20) := by norm_num
theorem arithmetic_012 : ((100*292/783) : ℚ) < (747/20) := by norm_num
theorem arithmetic_013 : ((100*89/783) : ℚ) ≥ (227/20) := by norm_num
theorem arithmetic_014 : ((100*89/783) : ℚ) < (229/20) := by norm_num
end c09_r04

namespace c09_r05
theorem arithmetic_001 : ((2*292) : ℚ) = (584) := by norm_num
theorem arithmetic_002 : ((601-584) : ℚ) = (17) := by norm_num
theorem arithmetic_003 : ((292/601) : ℚ) < (1/2) := by norm_num
end c09_r05

namespace c09_r06
theorem arithmetic_001 : ((3961-39) : ℚ) = (3922) := by norm_num
theorem arithmetic_002 : (((3961-39)/3961) : ℚ) = (1-39/3961) := by norm_num
theorem arithmetic_003 : ((100*3922/3961) : ℚ) ≥ (1979/20) := by norm_num
theorem arithmetic_004 : ((100*3922/3961) : ℚ) < (1981/20) := by norm_num
end c09_r06

namespace c09_r07
theorem arithmetic_001 : ((395-292) : ℚ) = (103) := by norm_num
theorem arithmetic_002 : ((783-292) : ℚ) = (491) := by norm_num
theorem arithmetic_003 : ((292+103) : ℚ) = (395) := by norm_num
theorem arithmetic_004 : ((292+491) : ℚ) = (783) := by norm_num
end c09_r07

namespace c09_r08
theorem arithmetic_001 : ((100+109) : ℚ) = (209) := by norm_num
theorem arithmetic_002 : ((85+4) : ℚ) = (89) := by norm_num
theorem arithmetic_003 : ((100+4) : ℚ) = (104) := by norm_num
theorem arithmetic_004 : ((104-89) : ℚ) = (15) := by norm_num
end c09_r08

namespace c09_d01
theorem arithmetic_001 : ((234+23) : ℚ) = (257) := by norm_num
theorem arithmetic_002 : ((2+1+20) : ℚ) = (23) := by norm_num
theorem arithmetic_003 : ((17+3) : ℚ) = (20) := by norm_num
theorem arithmetic_004 : ((234+2+1+17+3) : ℚ) = (257) := by norm_num
theorem arithmetic_005 : ((100*122/257) : ℚ) = (12200/257) := by norm_num
theorem arithmetic_006 : ((100*96/257) : ℚ) = (9600/257) := by norm_num
theorem arithmetic_007 : ((100*122/257) : ℚ) ≥ (949/20) := by norm_num
theorem arithmetic_008 : ((100*122/257) : ℚ) < (951/20) := by norm_num
theorem arithmetic_009 : ((100*96/257) : ℚ) ≥ (747/20) := by norm_num
theorem arithmetic_010 : ((100*96/257) : ℚ) < (749/20) := by norm_num
end c09_d01

namespace c09_d02
theorem arithmetic_001 : ((85+15) : ℚ) = (100) := by norm_num
theorem arithmetic_002 : ((100-15) : ℚ) = (85) := by norm_num
end c09_d02

namespace c09_d03
theorem arithmetic_001 : ((70+20+10) : ℚ) = (100) := by norm_num
theorem arithmetic_002 : ((923/1000-717/1000) : ℚ) = (206/1000) := by norm_num
theorem arithmetic_003 : ((206/1000*100) : ℚ) = (206/10) := by norm_num
theorem arithmetic_004 : ((997/1000+986/1000+918/1000+951/1000+966/1000+936/1000+813/1000+906/1000+985/1000) : ℚ) = (8458/1000) := by norm_num
theorem arithmetic_005 : (((8458/1000)/9) : ℚ) = (4229/4500) := by norm_num
theorem arithmetic_006 : ((4229/4500) : ℚ) ≥ (18795/20000) := by norm_num
theorem arithmetic_007 : ((4229/4500) : ℚ) < (18797/20000) := by norm_num
theorem arithmetic_008 : ((175807) : ℚ) > (310) := by norm_num
end c09_d03

namespace c09_d04
theorem arithmetic_001 : ((100+4) : ℚ) = (104) := by norm_num
theorem arithmetic_002 : ((292/395) : ℚ) > (292/783) := by norm_num
end c09_d04

namespace c09_p01
theorem arithmetic_001 : ((100-15) : ℚ) = (85) := by norm_num
theorem arithmetic_002 : ((85+4) : ℚ) = (89) := by norm_num
theorem arithmetic_003 : ((100+4) : ℚ) = (104) := by norm_num
theorem arithmetic_004 : ((100+109) : ℚ) = (209) := by norm_num
theorem arithmetic_005 : ((104/209-89/209) : ℚ) = ((104-89)/209) := by norm_num
theorem arithmetic_006 : (((104-89)/209) : ℚ) = (15/209) := by norm_num
theorem arithmetic_007 : ((100/100) : ℚ) = (1) := by norm_num
theorem arithmetic_008 : ((100-85) : ℚ) = (15) := by norm_num
theorem arithmetic_009 : ((100-100) : ℚ) = (0) := by norm_num
theorem arithmetic_010 : ((109-4) : ℚ) = (105) := by norm_num
theorem arithmetic_011 : ((85+15) : ℚ) = (100) := by norm_num
theorem arithmetic_012 : ((100+0) : ℚ) = (100) := by norm_num
theorem arithmetic_013 : ((4+105) : ℚ) = (109) := by norm_num
theorem arithmetic_014 : ((15+105) : ℚ) = (120) := by norm_num
theorem arithmetic_015 : ((89+120) : ℚ) = (209) := by norm_num
theorem arithmetic_016 : ((104+105) : ℚ) = (209) := by norm_num
theorem arithmetic_017 : ((120-105) : ℚ) = (15) := by norm_num
theorem arithmetic_018 : ((4/109) : ℚ) < (100/100) := by norm_num
end c09_p01

namespace c09_p02
theorem inter_of_subset {α : Type*} (A B : Set α) (h : B ⊆ A) : A ∩ B = B := by
  ext x
  constructor
  · intro hx; exact hx.2
  · intro hx; exact ⟨h hx, hx⟩
theorem indicators (a b : Bool) (h : b = true → a = true) : (a && b) = b := by
  cases a <;> cases b <;> simp_all
end c09_p02
end Chapter09
#print axioms Chapter09.c09_r01.arithmetic_001
#print axioms Chapter09.c09_r01.arithmetic_002
#print axioms Chapter09.c09_r01.arithmetic_003
#print axioms Chapter09.c09_r02.arithmetic_001
#print axioms Chapter09.c09_r02.arithmetic_002
#print axioms Chapter09.c09_r02.publishedObjectVerbPositions
#print axioms Chapter09.c09_r02.publishedOV
#print axioms Chapter09.c09_r03.arithmetic_001
#print axioms Chapter09.c09_r03.arithmetic_002
#print axioms Chapter09.c09_r03.arithmetic_003
#print axioms Chapter09.c09_r03.arithmetic_004
#print axioms Chapter09.c09_r03.arithmetic_005
#print axioms Chapter09.c09_r04.arithmetic_001
#print axioms Chapter09.c09_r04.arithmetic_002
#print axioms Chapter09.c09_r04.arithmetic_003
#print axioms Chapter09.c09_r04.arithmetic_004
#print axioms Chapter09.c09_r04.arithmetic_005
#print axioms Chapter09.c09_r04.arithmetic_006
#print axioms Chapter09.c09_r04.arithmetic_007
#print axioms Chapter09.c09_r04.arithmetic_008
#print axioms Chapter09.c09_r04.arithmetic_009
#print axioms Chapter09.c09_r04.arithmetic_010
#print axioms Chapter09.c09_r04.arithmetic_011
#print axioms Chapter09.c09_r04.arithmetic_012
#print axioms Chapter09.c09_r04.arithmetic_013
#print axioms Chapter09.c09_r04.arithmetic_014
#print axioms Chapter09.c09_r05.arithmetic_001
#print axioms Chapter09.c09_r05.arithmetic_002
#print axioms Chapter09.c09_r05.arithmetic_003
#print axioms Chapter09.c09_r06.arithmetic_001
#print axioms Chapter09.c09_r06.arithmetic_002
#print axioms Chapter09.c09_r06.arithmetic_003
#print axioms Chapter09.c09_r06.arithmetic_004
#print axioms Chapter09.c09_r07.arithmetic_001
#print axioms Chapter09.c09_r07.arithmetic_002
#print axioms Chapter09.c09_r07.arithmetic_003
#print axioms Chapter09.c09_r07.arithmetic_004
#print axioms Chapter09.c09_r08.arithmetic_001
#print axioms Chapter09.c09_r08.arithmetic_002
#print axioms Chapter09.c09_r08.arithmetic_003
#print axioms Chapter09.c09_r08.arithmetic_004
#print axioms Chapter09.c09_d01.arithmetic_001
#print axioms Chapter09.c09_d01.arithmetic_002
#print axioms Chapter09.c09_d01.arithmetic_003
#print axioms Chapter09.c09_d01.arithmetic_004
#print axioms Chapter09.c09_d01.arithmetic_005
#print axioms Chapter09.c09_d01.arithmetic_006
#print axioms Chapter09.c09_d01.arithmetic_007
#print axioms Chapter09.c09_d01.arithmetic_008
#print axioms Chapter09.c09_d01.arithmetic_009
#print axioms Chapter09.c09_d01.arithmetic_010
#print axioms Chapter09.c09_d02.arithmetic_001
#print axioms Chapter09.c09_d02.arithmetic_002
#print axioms Chapter09.c09_d03.arithmetic_001
#print axioms Chapter09.c09_d03.arithmetic_002
#print axioms Chapter09.c09_d03.arithmetic_003
#print axioms Chapter09.c09_d03.arithmetic_004
#print axioms Chapter09.c09_d03.arithmetic_005
#print axioms Chapter09.c09_d03.arithmetic_006
#print axioms Chapter09.c09_d03.arithmetic_007
#print axioms Chapter09.c09_d03.arithmetic_008
#print axioms Chapter09.c09_d04.arithmetic_001
#print axioms Chapter09.c09_d04.arithmetic_002
#print axioms Chapter09.c09_p01.arithmetic_001
#print axioms Chapter09.c09_p01.arithmetic_002
#print axioms Chapter09.c09_p01.arithmetic_003
#print axioms Chapter09.c09_p01.arithmetic_004
#print axioms Chapter09.c09_p01.arithmetic_005
#print axioms Chapter09.c09_p01.arithmetic_006
#print axioms Chapter09.c09_p01.arithmetic_007
#print axioms Chapter09.c09_p01.arithmetic_008
#print axioms Chapter09.c09_p01.arithmetic_009
#print axioms Chapter09.c09_p01.arithmetic_010
#print axioms Chapter09.c09_p01.arithmetic_011
#print axioms Chapter09.c09_p01.arithmetic_012
#print axioms Chapter09.c09_p01.arithmetic_013
#print axioms Chapter09.c09_p01.arithmetic_014
#print axioms Chapter09.c09_p01.arithmetic_015
#print axioms Chapter09.c09_p01.arithmetic_016
#print axioms Chapter09.c09_p01.arithmetic_017
#print axioms Chapter09.c09_p01.arithmetic_018
#print axioms Chapter09.c09_p02.inter_of_subset
#print axioms Chapter09.c09_p02.indicators
