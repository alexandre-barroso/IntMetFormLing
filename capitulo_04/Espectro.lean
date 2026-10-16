import Mathlib
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384
open Polynomial
namespace Chapter04Spectrum
noncomputable def minor0 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x - 3,-2;-2,x - 3]
theorem minor0_det (x:ℝ) : (minor0 x).det=x^2 - 6*x + 5 := by
 norm_num [minor0,Matrix.det_fin_two] <;> ring
#print axioms minor0_det
noncomputable def minor1 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-2,-2;-1,x - 3]
theorem minor1_det (x:ℝ) : (minor1 x).det=4 - 2*x := by
 norm_num [minor1,Matrix.det_fin_two] <;> ring
#print axioms minor1_det
noncomputable def minor2 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-2,x - 3;-1,-2]
theorem minor2_det (x:ℝ) : (minor2 x).det=x + 1 := by
 norm_num [minor2,Matrix.det_fin_two] <;> ring
#print axioms minor2_det
noncomputable def minor3 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![x - 2,-2,-1;-2,x - 3,-2;-1,-2,x - 3]
theorem minor3_det (x:ℝ) : (minor3 x).det=x^3 - 8*x^2 + 12*x - 3 := by
 have sub0 : (minor3 x).submatrix (0:Fin 3).succAbove (0:Fin 3).succAbove=minor0 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor3 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor1 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor3 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor2 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor3 x) (0:Fin 3) (0:Fin 3)=x - 2 := by rfl
 have entry1 : (minor3 x) (0:Fin 3) (Fin.succ (0:Fin 2))=-2 := by rfl
 have entry2 : (minor3 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-1 := by rfl
 rw [Matrix.det_succ_row (minor3 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor0_det, minor1_det, minor2_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor3_det
noncomputable def minor4 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,-1;-1,-2]
theorem minor4_det (x:ℝ) : (minor4 x).det=1 := by
 norm_num [minor4,Matrix.det_fin_two] <;> ring
#print axioms minor4_det
noncomputable def minor5 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,-2;-1,x - 3]
theorem minor5_det (x:ℝ) : (minor5 x).det=1 - x := by
 norm_num [minor5,Matrix.det_fin_two] <;> ring
#print axioms minor5_det
noncomputable def minor6 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,-2,-1;-1,x - 3,-2;0,-2,x - 3]
theorem minor6_det (x:ℝ) : (minor6 x).det=-x^2 + 4*x - 1 := by
 have sub1 : (minor6 x).submatrix (2:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor4 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor6 x).submatrix (2:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor5 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor6 x) (2:Fin 3) (0:Fin 3)=0 := by rfl
 have entry1 : (minor6 x) (2:Fin 3) (Fin.succ (0:Fin 2))=-2 := by rfl
 have entry2 : (minor6 x) (2:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=x - 3 := by rfl
 rw [Matrix.det_succ_row (minor6 x) 2]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, minor4_det, minor5_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor6_det
noncomputable def minor7 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,x - 2;-1,-2]
theorem minor7_det (x:ℝ) : (minor7 x).det=x := by
 norm_num [minor7,Matrix.det_fin_two] <;> ring
#print axioms minor7_det
noncomputable def minor8 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,x - 2,-1;-1,-2,-2;0,-1,x - 3]
theorem minor8_det (x:ℝ) : (minor8 x).det=x^2 - 3*x + 1 := by
 have sub1 : (minor8 x).submatrix (2:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor4 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor8 x).submatrix (2:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor7 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor8 x) (2:Fin 3) (0:Fin 3)=0 := by rfl
 have entry1 : (minor8 x) (2:Fin 3) (Fin.succ (0:Fin 2))=-1 := by rfl
 have entry2 : (minor8 x) (2:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=x - 3 := by rfl
 rw [Matrix.det_succ_row (minor8 x) 2]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, minor4_det, minor7_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor8_det
noncomputable def minor9 (x:ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![x - 1,-1,-1,0;-1,x - 2,-2,-1;-1,-2,x - 3,-2;0,-1,-2,x - 3]
theorem minor9_det (x:ℝ) : (minor9 x).det=x^4 - 9*x^3 + 18*x^2 - 8*x + 1 := by
 have sub0 : (minor9 x).submatrix (0:Fin 4).succAbove (0:Fin 4).succAbove=minor3 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor9 x).submatrix (0:Fin 4).succAbove (Fin.succ (0:Fin 3)).succAbove=minor6 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor9 x).submatrix (0:Fin 4).succAbove (Fin.succ (Fin.succ (0:Fin 2))).succAbove=minor8 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor9 x) (0:Fin 4) (0:Fin 4)=x - 1 := by rfl
 have entry1 : (minor9 x) (0:Fin 4) (Fin.succ (0:Fin 3))=-1 := by rfl
 have entry2 : (minor9 x) (0:Fin 4) (Fin.succ (Fin.succ (0:Fin 2)))=-1 := by rfl
 have entry3 : (minor9 x) (0:Fin 4) (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))=0 := by rfl
 rw [Matrix.det_succ_row (minor9 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor3_det, minor6_det, minor8_det]
 rw [entry0, entry1, entry2, entry3]
 norm_num <;> ring
#print axioms minor9_det
noncomputable def minor10 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,-2;0,x - 3]
theorem minor10_det (x:ℝ) : (minor10 x).det=0 := by
 norm_num [minor10,Matrix.det_fin_two] <;> ring
#print axioms minor10_det
noncomputable def minor11 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,-1;0,-1]
theorem minor11_det (x:ℝ) : (minor11 x).det=0 := by
 norm_num [minor11,Matrix.det_fin_two] <;> ring
#print axioms minor11_det
noncomputable def minor12 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,x - 1,-1;0,-1,-2;0,-1,x - 3]
theorem minor12_det (x:ℝ) : (minor12 x).det=0 := by
 have sub1 : (minor12 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor10 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor12 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor11 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor12 x) (0:Fin 3) (0:Fin 3)=0 := by rfl
 have entry1 : (minor12 x) (0:Fin 3) (Fin.succ (0:Fin 2))=x - 1 := by rfl
 have entry2 : (minor12 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-1 := by rfl
 rw [Matrix.det_succ_row (minor12 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, minor10_det, minor11_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor12_det
noncomputable def minor13 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,x - 2;0,-2]
theorem minor13_det (x:ℝ) : (minor13 x).det=0 := by
 norm_num [minor13,Matrix.det_fin_two] <;> ring
#print axioms minor13_det
noncomputable def minor14 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,x - 1,-1;0,-1,x - 2;0,-1,-2]
theorem minor14_det (x:ℝ) : (minor14 x).det=0 := by
 have sub1 : (minor14 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor13 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor14 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor11 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor14 x) (0:Fin 3) (0:Fin 3)=0 := by rfl
 have entry1 : (minor14 x) (0:Fin 3) (Fin.succ (0:Fin 2))=x - 1 := by rfl
 have entry2 : (minor14 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-1 := by rfl
 rw [Matrix.det_succ_row (minor14 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, minor13_det, minor11_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor14_det
noncomputable def minor15 (x:ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![0,x - 1,-1,-1;0,-1,x - 2,-2;0,-1,-2,x - 3;0,0,-1,-2]
theorem minor15_det (x:ℝ) : (minor15 x).det=0 := by
 have sub2 : (minor15 x).submatrix (3:Fin 4).succAbove (Fin.succ (Fin.succ (0:Fin 2))).succAbove=minor12 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub3 : (minor15 x).submatrix (3:Fin 4).succAbove (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))).succAbove=minor14 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor15 x) (3:Fin 4) (0:Fin 4)=0 := by rfl
 have entry1 : (minor15 x) (3:Fin 4) (Fin.succ (0:Fin 3))=0 := by rfl
 have entry2 : (minor15 x) (3:Fin 4) (Fin.succ (Fin.succ (0:Fin 2)))=-1 := by rfl
 have entry3 : (minor15 x) (3:Fin 4) (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))=-2 := by rfl
 rw [Matrix.det_succ_row (minor15 x) 3]
 simp only [Fin.sum_univ_succ]
 rw [sub2, sub3, minor12_det, minor14_det]
 rw [entry0, entry1, entry2, entry3]
 norm_num <;> ring
#print axioms minor15_det
noncomputable def minor16 (x:ℝ) : Matrix (Fin 5) (Fin 5) ℝ := !![-3,0,0,0,-1;0,x - 1,-1,-1,0;0,-1,x - 2,-2,-1;0,-1,-2,x - 3,-2;0,0,-1,-2,x - 3]
theorem minor16_det (x:ℝ) : (minor16 x).det=-3*x^4 + 27*x^3 - 54*x^2 + 24*x - 3 := by
 have sub0 : (minor16 x).submatrix (0:Fin 5).succAbove (0:Fin 5).succAbove=minor9 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub4 : (minor16 x).submatrix (0:Fin 5).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))).succAbove=minor15 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor16 x) (0:Fin 5) (0:Fin 5)=-3 := by rfl
 have entry1 : (minor16 x) (0:Fin 5) (Fin.succ (0:Fin 4))=0 := by rfl
 have entry2 : (minor16 x) (0:Fin 5) (Fin.succ (Fin.succ (0:Fin 3)))=0 := by rfl
 have entry3 : (minor16 x) (0:Fin 5) (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))=0 := by rfl
 have entry4 : (minor16 x) (0:Fin 5) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor16 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub4, minor9_det, minor15_det]
 rw [entry0, entry1, entry2, entry3, entry4]
 norm_num <;> ring
#print axioms minor16_det
noncomputable def minor17 (x:ℝ) : Matrix (Fin 5) (Fin 5) ℝ := !![-2,0,0,0,-1;0,x - 1,-1,-1,0;0,-1,x - 2,-2,-1;0,-1,-2,x - 3,-2;0,0,-1,-2,x - 3]
theorem minor17_det (x:ℝ) : (minor17 x).det=-2*x^4 + 18*x^3 - 36*x^2 + 16*x - 2 := by
 have sub0 : (minor17 x).submatrix (0:Fin 5).succAbove (0:Fin 5).succAbove=minor9 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub4 : (minor17 x).submatrix (0:Fin 5).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))).succAbove=minor15 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor17 x) (0:Fin 5) (0:Fin 5)=-2 := by rfl
 have entry1 : (minor17 x) (0:Fin 5) (Fin.succ (0:Fin 4))=0 := by rfl
 have entry2 : (minor17 x) (0:Fin 5) (Fin.succ (Fin.succ (0:Fin 3)))=0 := by rfl
 have entry3 : (minor17 x) (0:Fin 5) (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))=0 := by rfl
 have entry4 : (minor17 x) (0:Fin 5) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor17 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub4, minor9_det, minor15_det]
 rw [entry0, entry1, entry2, entry3, entry4]
 norm_num <;> ring
#print axioms minor17_det
noncomputable def minor18 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![-2,-3,0,0,0,-1;-3,-1,0,0,0,0;0,0,x - 1,-1,-1,0;0,0,-1,x - 2,-2,-1;0,0,-1,-2,x - 3,-2;0,0,0,-1,-2,x - 3]
theorem minor18_det (x:ℝ) : (minor18 x).det=-7*x^4 + 63*x^3 - 126*x^2 + 56*x - 7 := by
 have sub0 : (minor18 x).submatrix (1:Fin 6).succAbove (0:Fin 6).succAbove=minor16 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor18 x).submatrix (1:Fin 6).succAbove (Fin.succ (0:Fin 5)).succAbove=minor17 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor18 x) (1:Fin 6) (0:Fin 6)=-3 := by rfl
 have entry1 : (minor18 x) (1:Fin 6) (Fin.succ (0:Fin 5))=-1 := by rfl
 have entry2 : (minor18 x) (1:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor18 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor18 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=0 := by rfl
 have entry5 : (minor18 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor18 x) 1]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor16_det, minor17_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor18_det
noncomputable def minor19 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![-2,-3,0,0,0,-1;x - 4,-1,0,0,0,0;0,0,x - 1,-1,-1,0;0,0,-1,x - 2,-2,-1;0,0,-1,-2,x - 3,-2;0,0,0,-1,-2,x - 3]
theorem minor19_det (x:ℝ) : (minor19 x).det=3*x^5 - 37*x^4 + 144*x^3 - 204*x^2 + 83*x - 10 := by
 have sub0 : (minor19 x).submatrix (1:Fin 6).succAbove (0:Fin 6).succAbove=minor16 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor19 x).submatrix (1:Fin 6).succAbove (Fin.succ (0:Fin 5)).succAbove=minor17 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor19 x) (1:Fin 6) (0:Fin 6)=x - 4 := by rfl
 have entry1 : (minor19 x) (1:Fin 6) (Fin.succ (0:Fin 5))=-1 := by rfl
 have entry2 : (minor19 x) (1:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor19 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor19 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=0 := by rfl
 have entry5 : (minor19 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor19 x) 1]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor16_det, minor17_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor19_det
noncomputable def minor20 (x:ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![-2,-2,-3,0,0,0,-1;x - 4,-3,-1,0,0,0,0;-3,x - 6,0,0,0,0,0;0,0,0,x - 1,-1,-1,0;0,0,0,-1,x - 2,-2,-1;0,0,0,-1,-2,x - 3,-2;0,0,0,0,-1,-2,x - 3]
theorem minor20_det (x:ℝ) : (minor20 x).det=-3*x^6 + 55*x^5 - 345*x^4 + 879*x^3 - 929*x^2 + 340*x - 39 := by
 have sub0 : (minor20 x).submatrix (2:Fin 7).succAbove (0:Fin 7).succAbove=minor18 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor20 x).submatrix (2:Fin 7).succAbove (Fin.succ (0:Fin 6)).succAbove=minor19 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor20 x) (2:Fin 7) (0:Fin 7)=-3 := by rfl
 have entry1 : (minor20 x) (2:Fin 7) (Fin.succ (0:Fin 6))=x - 6 := by rfl
 have entry2 : (minor20 x) (2:Fin 7) (Fin.succ (Fin.succ (0:Fin 5)))=0 := by rfl
 have entry3 : (minor20 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))=0 := by rfl
 have entry4 : (minor20 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))=0 := by rfl
 have entry5 : (minor20 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))=0 := by rfl
 have entry6 : (minor20 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor20 x) 2]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor18_det, minor19_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6]
 norm_num <;> ring
#print axioms minor20_det
noncomputable def minor21 (x:ℝ) : Matrix (Fin 5) (Fin 5) ℝ := !![-1,0,0,0,-1;0,x - 1,-1,-1,0;0,-1,x - 2,-2,-1;0,-1,-2,x - 3,-2;0,0,-1,-2,x - 3]
theorem minor21_det (x:ℝ) : (minor21 x).det=-x^4 + 9*x^3 - 18*x^2 + 8*x - 1 := by
 have sub0 : (minor21 x).submatrix (0:Fin 5).succAbove (0:Fin 5).succAbove=minor9 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub4 : (minor21 x).submatrix (0:Fin 5).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))).succAbove=minor15 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor21 x) (0:Fin 5) (0:Fin 5)=-1 := by rfl
 have entry1 : (minor21 x) (0:Fin 5) (Fin.succ (0:Fin 4))=0 := by rfl
 have entry2 : (minor21 x) (0:Fin 5) (Fin.succ (Fin.succ (0:Fin 3)))=0 := by rfl
 have entry3 : (minor21 x) (0:Fin 5) (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))=0 := by rfl
 have entry4 : (minor21 x) (0:Fin 5) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor21 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub4, minor9_det, minor15_det]
 rw [entry0, entry1, entry2, entry3, entry4]
 norm_num <;> ring
#print axioms minor21_det
noncomputable def minor22 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![-1,-3,0,0,0,-1;-1,-1,0,0,0,0;0,0,x - 1,-1,-1,0;0,0,-1,x - 2,-2,-1;0,0,-1,-2,x - 3,-2;0,0,0,-1,-2,x - 3]
theorem minor22_det (x:ℝ) : (minor22 x).det=-2*x^4 + 18*x^3 - 36*x^2 + 16*x - 2 := by
 have sub0 : (minor22 x).submatrix (1:Fin 6).succAbove (0:Fin 6).succAbove=minor16 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor22 x).submatrix (1:Fin 6).succAbove (Fin.succ (0:Fin 5)).succAbove=minor21 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor22 x) (1:Fin 6) (0:Fin 6)=-1 := by rfl
 have entry1 : (minor22 x) (1:Fin 6) (Fin.succ (0:Fin 5))=-1 := by rfl
 have entry2 : (minor22 x) (1:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor22 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor22 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=0 := by rfl
 have entry5 : (minor22 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor22 x) 1]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor16_det, minor21_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor22_det
noncomputable def minor23 (x:ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![-1,-2,-3,0,0,0,-1;-1,-3,-1,0,0,0,0;-1,x - 6,0,0,0,0,0;0,0,0,x - 1,-1,-1,0;0,0,0,-1,x - 2,-2,-1;0,0,0,-1,-2,x - 3,-2;0,0,0,0,-1,-2,x - 3]
theorem minor23_det (x:ℝ) : (minor23 x).det=2*x^5 - 23*x^4 + 81*x^3 - 106*x^2 + 42*x - 5 := by
 have sub0 : (minor23 x).submatrix (2:Fin 7).succAbove (0:Fin 7).succAbove=minor18 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor23 x).submatrix (2:Fin 7).succAbove (Fin.succ (0:Fin 6)).succAbove=minor22 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor23 x) (2:Fin 7) (0:Fin 7)=-1 := by rfl
 have entry1 : (minor23 x) (2:Fin 7) (Fin.succ (0:Fin 6))=x - 6 := by rfl
 have entry2 : (minor23 x) (2:Fin 7) (Fin.succ (Fin.succ (0:Fin 5)))=0 := by rfl
 have entry3 : (minor23 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))=0 := by rfl
 have entry4 : (minor23 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))=0 := by rfl
 have entry5 : (minor23 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))=0 := by rfl
 have entry6 : (minor23 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor23 x) 2]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor18_det, minor22_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6]
 norm_num <;> ring
#print axioms minor23_det
noncomputable def minor24 (x:ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![-1,-2,-3,0,0,0,-1;-1,x - 4,-1,0,0,0,0;-1,-3,0,0,0,0,0;0,0,0,x - 1,-1,-1,0;0,0,0,-1,x - 2,-2,-1;0,0,0,-1,-2,x - 3,-2;0,0,0,0,-1,-2,x - 3]
theorem minor24_det (x:ℝ) : (minor24 x).det=-3*x^5 + 31*x^4 - 90*x^3 + 96*x^2 - 35*x + 4 := by
 have sub0 : (minor24 x).submatrix (2:Fin 7).succAbove (0:Fin 7).succAbove=minor19 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor24 x).submatrix (2:Fin 7).succAbove (Fin.succ (0:Fin 6)).succAbove=minor22 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor24 x) (2:Fin 7) (0:Fin 7)=-1 := by rfl
 have entry1 : (minor24 x) (2:Fin 7) (Fin.succ (0:Fin 6))=-3 := by rfl
 have entry2 : (minor24 x) (2:Fin 7) (Fin.succ (Fin.succ (0:Fin 5)))=0 := by rfl
 have entry3 : (minor24 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))=0 := by rfl
 have entry4 : (minor24 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))=0 := by rfl
 have entry5 : (minor24 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))=0 := by rfl
 have entry6 : (minor24 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor24 x) 2]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor19_det, minor22_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6]
 norm_num <;> ring
#print axioms minor24_det
noncomputable def minor25 (x:ℝ) : Matrix (Fin 8) (Fin 8) ℝ := !![x - 3,-1,-1,0,0,0,0,0;-1,-2,-2,-3,0,0,0,-1;-1,x - 4,-3,-1,0,0,0,0;-1,-3,x - 6,0,0,0,0,0;0,0,0,0,x - 1,-1,-1,0;0,0,0,0,-1,x - 2,-2,-1;0,0,0,0,-1,-2,x - 3,-2;0,0,0,0,0,-1,-2,x - 3]
theorem minor25_det (x:ℝ) : (minor25 x).det=-3*x^7 + 64*x^6 - 505*x^5 + 1860*x^4 - 3395*x^3 + 2925*x^2 - 982*x + 108 := by
 have sub0 : (minor25 x).submatrix (0:Fin 8).succAbove (0:Fin 8).succAbove=minor20 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor25 x).submatrix (0:Fin 8).succAbove (Fin.succ (0:Fin 7)).succAbove=minor23 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor25 x).submatrix (0:Fin 8).succAbove (Fin.succ (Fin.succ (0:Fin 6))).succAbove=minor24 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor25 x) (0:Fin 8) (0:Fin 8)=x - 3 := by rfl
 have entry1 : (minor25 x) (0:Fin 8) (Fin.succ (0:Fin 7))=-1 := by rfl
 have entry2 : (minor25 x) (0:Fin 8) (Fin.succ (Fin.succ (0:Fin 6)))=-1 := by rfl
 have entry3 : (minor25 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (0:Fin 5))))=0 := by rfl
 have entry4 : (minor25 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 4)))))=0 := by rfl
 have entry5 : (minor25 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))))=0 := by rfl
 have entry6 : (minor25 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))))=0 := by rfl
 have entry7 : (minor25 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor25 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor20_det, minor23_det, minor24_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7]
 norm_num <;> ring
#print axioms minor25_det
noncomputable def minor26 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,x - 3;-1,-2]
theorem minor26_det (x:ℝ) : (minor26 x).det=x - 3 := by
 norm_num [minor26,Matrix.det_fin_two] <;> ring
#print axioms minor26_det
noncomputable def minor27 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,-2;-1,-1]
theorem minor27_det (x:ℝ) : (minor27 x).det=-2 := by
 norm_num [minor27,Matrix.det_fin_two] <;> ring
#print axioms minor27_det
noncomputable def minor28 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,x - 2,-2;0,-2,x - 3;-1,-1,-2]
theorem minor28_det (x:ℝ) : (minor28 x).det=-x^2 + 5*x - 2 := by
 have sub1 : (minor28 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor26 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor28 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor27 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor28 x) (0:Fin 3) (0:Fin 3)=0 := by rfl
 have entry1 : (minor28 x) (0:Fin 3) (Fin.succ (0:Fin 2))=x - 2 := by rfl
 have entry2 : (minor28 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-2 := by rfl
 rw [Matrix.det_succ_row (minor28 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, minor26_det, minor27_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor28_det
noncomputable def minor29 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0,-1;-1,0]
theorem minor29_det (x:ℝ) : (minor29 x).det=-1 := by
 norm_num [minor29,Matrix.det_fin_two] <;> ring
#print axioms minor29_det
noncomputable def minor30 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,-2;0,-1,x - 3;-1,0,-2]
theorem minor30_det (x:ℝ) : (minor30 x).det=x - 1 := by
 have sub1 : (minor30 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor26 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor30 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor29 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor30 x) (0:Fin 3) (0:Fin 3)=0 := by rfl
 have entry1 : (minor30 x) (0:Fin 3) (Fin.succ (0:Fin 2))=-1 := by rfl
 have entry2 : (minor30 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-2 := by rfl
 rw [Matrix.det_succ_row (minor30 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, minor26_det, minor29_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor30_det
noncomputable def minor31 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,x - 2;0,-1,-2;-1,0,-1]
theorem minor31_det (x:ℝ) : (minor31 x).det=-x := by
 have sub1 : (minor31 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor27 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor31 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor29 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor31 x) (0:Fin 3) (0:Fin 3)=0 := by rfl
 have entry1 : (minor31 x) (0:Fin 3) (Fin.succ (0:Fin 2))=-1 := by rfl
 have entry2 : (minor31 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=x - 2 := by rfl
 rw [Matrix.det_succ_row (minor31 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, minor27_det, minor29_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor31_det
noncomputable def minor32 (x:ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![0,x - 1,-1,-1;0,-1,x - 2,-2;0,-1,-2,x - 3;-1,0,-1,-2]
theorem minor32_det (x:ℝ) : (minor32 x).det=x^3 - 6*x^2 + 5*x - 1 := by
 have sub1 : (minor32 x).submatrix (0:Fin 4).succAbove (Fin.succ (0:Fin 3)).succAbove=minor28 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor32 x).submatrix (0:Fin 4).succAbove (Fin.succ (Fin.succ (0:Fin 2))).succAbove=minor30 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub3 : (minor32 x).submatrix (0:Fin 4).succAbove (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))).succAbove=minor31 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor32 x) (0:Fin 4) (0:Fin 4)=0 := by rfl
 have entry1 : (minor32 x) (0:Fin 4) (Fin.succ (0:Fin 3))=x - 1 := by rfl
 have entry2 : (minor32 x) (0:Fin 4) (Fin.succ (Fin.succ (0:Fin 2)))=-1 := by rfl
 have entry3 : (minor32 x) (0:Fin 4) (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor32 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, sub3, minor28_det, minor30_det, minor31_det]
 rw [entry0, entry1, entry2, entry3]
 norm_num <;> ring
#print axioms minor32_det
noncomputable def minor33 (x:ℝ) : Matrix (Fin 5) (Fin 5) ℝ := !![x - 6,0,0,0,-1;0,x - 1,-1,-1,0;0,-1,x - 2,-2,-1;0,-1,-2,x - 3,-2;-1,0,-1,-2,x - 3]
theorem minor33_det (x:ℝ) : (minor33 x).det=x^5 - 15*x^4 + 71*x^3 - 110*x^2 + 44*x - 5 := by
 have sub0 : (minor33 x).submatrix (0:Fin 5).succAbove (0:Fin 5).succAbove=minor9 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub4 : (minor33 x).submatrix (0:Fin 5).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))).succAbove=minor32 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor33 x) (0:Fin 5) (0:Fin 5)=x - 6 := by rfl
 have entry1 : (minor33 x) (0:Fin 5) (Fin.succ (0:Fin 4))=0 := by rfl
 have entry2 : (minor33 x) (0:Fin 5) (Fin.succ (Fin.succ (0:Fin 3)))=0 := by rfl
 have entry3 : (minor33 x) (0:Fin 5) (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))=0 := by rfl
 have entry4 : (minor33 x) (0:Fin 5) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor33 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub4, minor9_det, minor32_det]
 rw [entry0, entry1, entry2, entry3, entry4]
 norm_num <;> ring
#print axioms minor33_det
noncomputable def minor34 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![x - 6,-3,0,0,0,-1;-2,-1,0,0,0,0;0,0,x - 1,-1,-1,0;0,0,-1,x - 2,-2,-1;0,0,-1,-2,x - 3,-2;-1,0,0,-1,-2,x - 3]
theorem minor34_det (x:ℝ) : (minor34 x).det=-x^5 + 9*x^4 - 17*x^3 + 2*x^2 + 4*x - 1 := by
 have sub0 : (minor34 x).submatrix (1:Fin 6).succAbove (0:Fin 6).succAbove=minor16 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor34 x).submatrix (1:Fin 6).succAbove (Fin.succ (0:Fin 5)).succAbove=minor33 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor34 x) (1:Fin 6) (0:Fin 6)=-2 := by rfl
 have entry1 : (minor34 x) (1:Fin 6) (Fin.succ (0:Fin 5))=-1 := by rfl
 have entry2 : (minor34 x) (1:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor34 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor34 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=0 := by rfl
 have entry5 : (minor34 x) (1:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor34 x) 1]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor16_det, minor33_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor34_det
noncomputable def minor35 (x:ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![x - 6,-2,-3,0,0,0,-1;-2,-3,-1,0,0,0,0;-2,x - 6,0,0,0,0,0;0,0,0,x - 1,-1,-1,0;0,0,0,-1,x - 2,-2,-1;0,0,0,-1,-2,x - 3,-2;-1,0,0,0,-1,-2,x - 3]
theorem minor35_det (x:ℝ) : (minor35 x).det=x^6 - 15*x^5 + 85*x^4 - 230*x^3 + 260*x^2 - 87*x + 8 := by
 have sub0 : (minor35 x).submatrix (2:Fin 7).succAbove (0:Fin 7).succAbove=minor18 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor35 x).submatrix (2:Fin 7).succAbove (Fin.succ (0:Fin 6)).succAbove=minor34 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor35 x) (2:Fin 7) (0:Fin 7)=-2 := by rfl
 have entry1 : (minor35 x) (2:Fin 7) (Fin.succ (0:Fin 6))=x - 6 := by rfl
 have entry2 : (minor35 x) (2:Fin 7) (Fin.succ (Fin.succ (0:Fin 5)))=0 := by rfl
 have entry3 : (minor35 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))=0 := by rfl
 have entry4 : (minor35 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))=0 := by rfl
 have entry5 : (minor35 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))=0 := by rfl
 have entry6 : (minor35 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor35 x) 2]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor18_det, minor34_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6]
 norm_num <;> ring
#print axioms minor35_det
noncomputable def minor36 (x:ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![-1,x - 6,-3,0,0,0,-1;-1,-2,-1,0,0,0,0;-1,-2,0,0,0,0,0;0,0,0,x - 1,-1,-1,0;0,0,0,-1,x - 2,-2,-1;0,0,0,-1,-2,x - 3,-2;0,-1,0,0,-1,-2,x - 3]
theorem minor36_det (x:ℝ) : (minor36 x).det=x^5 - 13*x^4 + 53*x^3 - 74*x^2 + 28*x - 3 := by
 have sub0 : (minor36 x).submatrix (2:Fin 7).succAbove (0:Fin 7).succAbove=minor34 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor36 x).submatrix (2:Fin 7).succAbove (Fin.succ (0:Fin 6)).succAbove=minor22 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor36 x) (2:Fin 7) (0:Fin 7)=-1 := by rfl
 have entry1 : (minor36 x) (2:Fin 7) (Fin.succ (0:Fin 6))=-2 := by rfl
 have entry2 : (minor36 x) (2:Fin 7) (Fin.succ (Fin.succ (0:Fin 5)))=0 := by rfl
 have entry3 : (minor36 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))=0 := by rfl
 have entry4 : (minor36 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))=0 := by rfl
 have entry5 : (minor36 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))=0 := by rfl
 have entry6 : (minor36 x) (2:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor36 x) 2]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor34_det, minor22_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6]
 norm_num <;> ring
#print axioms minor36_det
noncomputable def minor37 (x:ℝ) : Matrix (Fin 8) (Fin 8) ℝ := !![x - 3,-1,-1,0,0,0,0,0;-1,x - 6,-2,-3,0,0,0,-1;-1,-2,-3,-1,0,0,0,0;-1,-2,x - 6,0,0,0,0,0;0,0,0,0,x - 1,-1,-1,0;0,0,0,0,-1,x - 2,-2,-1;0,0,0,0,-1,-2,x - 3,-2;0,-1,0,0,0,-1,-2,x - 3]
theorem minor37_det (x:ℝ) : (minor37 x).det=x^7 - 18*x^6 + 131*x^5 - 495*x^4 + 978*x^3 - 899*x^2 + 283*x - 26 := by
 have sub0 : (minor37 x).submatrix (0:Fin 8).succAbove (0:Fin 8).succAbove=minor35 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor37 x).submatrix (0:Fin 8).succAbove (Fin.succ (0:Fin 7)).succAbove=minor23 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor37 x).submatrix (0:Fin 8).succAbove (Fin.succ (Fin.succ (0:Fin 6))).succAbove=minor36 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor37 x) (0:Fin 8) (0:Fin 8)=x - 3 := by rfl
 have entry1 : (minor37 x) (0:Fin 8) (Fin.succ (0:Fin 7))=-1 := by rfl
 have entry2 : (minor37 x) (0:Fin 8) (Fin.succ (Fin.succ (0:Fin 6)))=-1 := by rfl
 have entry3 : (minor37 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (0:Fin 5))))=0 := by rfl
 have entry4 : (minor37 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 4)))))=0 := by rfl
 have entry5 : (minor37 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))))=0 := by rfl
 have entry6 : (minor37 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))))=0 := by rfl
 have entry7 : (minor37 x) (0:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor37 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor35_det, minor23_det, minor36_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7]
 norm_num <;> ring
#print axioms minor37_det
noncomputable def minor38 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-2,-1;x - 6,0]
theorem minor38_det (x:ℝ) : (minor38 x).det=x - 6 := by
 norm_num [minor38,Matrix.det_fin_two] <;> ring
#print axioms minor38_det
noncomputable def minor39 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-2,-1;-3,0]
theorem minor39_det (x:ℝ) : (minor39 x).det=-3 := by
 norm_num [minor39,Matrix.det_fin_two] <;> ring
#print axioms minor39_det
noncomputable def minor40 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-2,-2,-1;x - 4,-3,0;-3,x - 6,0]
theorem minor40_det (x:ℝ) : (minor40 x).det=-x^2 + 10*x - 15 := by
 have sub0 : (minor40 x).submatrix (1:Fin 3).succAbove (0:Fin 3).succAbove=minor38 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor40 x).submatrix (1:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor39 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor40 x) (1:Fin 3) (0:Fin 3)=x - 4 := by rfl
 have entry1 : (minor40 x) (1:Fin 3) (Fin.succ (0:Fin 2))=-3 := by rfl
 have entry2 : (minor40 x) (1:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=0 := by rfl
 rw [Matrix.det_succ_row (minor40 x) 1]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor38_det, minor39_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor40_det
noncomputable def minor41 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,-1;-1,0]
theorem minor41_det (x:ℝ) : (minor41 x).det=-1 := by
 norm_num [minor41,Matrix.det_fin_two] <;> ring
#print axioms minor41_det
noncomputable def minor42 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,-2,-1;-1,-3,0;-1,x - 6,0]
theorem minor42_det (x:ℝ) : (minor42 x).det=x - 3 := by
 have sub0 : (minor42 x).submatrix (1:Fin 3).succAbove (0:Fin 3).succAbove=minor38 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor42 x).submatrix (1:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor41 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor42 x) (1:Fin 3) (0:Fin 3)=-1 := by rfl
 have entry1 : (minor42 x) (1:Fin 3) (Fin.succ (0:Fin 2))=-3 := by rfl
 have entry2 : (minor42 x) (1:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=0 := by rfl
 rw [Matrix.det_succ_row (minor42 x) 1]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor38_det, minor41_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor42_det
noncomputable def minor43 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,-2,-1;-1,x - 4,0;-1,-3,0]
theorem minor43_det (x:ℝ) : (minor43 x).det=1 - x := by
 have sub0 : (minor43 x).submatrix (1:Fin 3).succAbove (0:Fin 3).succAbove=minor39 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor43 x).submatrix (1:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor41 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor43 x) (1:Fin 3) (0:Fin 3)=-1 := by rfl
 have entry1 : (minor43 x) (1:Fin 3) (Fin.succ (0:Fin 2))=x - 4 := by rfl
 have entry2 : (minor43 x) (1:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=0 := by rfl
 rw [Matrix.det_succ_row (minor43 x) 1]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor39_det, minor41_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor43_det
noncomputable def minor44 (x:ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![x - 3,-1,-1,0;-1,-2,-2,-1;-1,x - 4,-3,0;-1,-3,x - 6,0]
theorem minor44_det (x:ℝ) : (minor44 x).det=-x^3 + 13*x^2 - 43*x + 41 := by
 have sub0 : (minor44 x).submatrix (0:Fin 4).succAbove (0:Fin 4).succAbove=minor40 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor44 x).submatrix (0:Fin 4).succAbove (Fin.succ (0:Fin 3)).succAbove=minor42 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor44 x).submatrix (0:Fin 4).succAbove (Fin.succ (Fin.succ (0:Fin 2))).succAbove=minor43 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor44 x) (0:Fin 4) (0:Fin 4)=x - 3 := by rfl
 have entry1 : (minor44 x) (0:Fin 4) (Fin.succ (0:Fin 3))=-1 := by rfl
 have entry2 : (minor44 x) (0:Fin 4) (Fin.succ (Fin.succ (0:Fin 2)))=-1 := by rfl
 have entry3 : (minor44 x) (0:Fin 4) (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))=0 := by rfl
 rw [Matrix.det_succ_row (minor44 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor40_det, minor42_det, minor43_det]
 rw [entry0, entry1, entry2, entry3]
 norm_num <;> ring
#print axioms minor44_det
noncomputable def minor45 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x - 4,-3;-3,x - 6]
theorem minor45_det (x:ℝ) : (minor45 x).det=x^2 - 10*x + 15 := by
 norm_num [minor45,Matrix.det_fin_two] <;> ring
#print axioms minor45_det
noncomputable def minor46 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-2,-3;-2,x - 6]
theorem minor46_det (x:ℝ) : (minor46 x).det=6 - 2*x := by
 norm_num [minor46,Matrix.det_fin_two] <;> ring
#print axioms minor46_det
noncomputable def minor47 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-2,x - 4;-2,-3]
theorem minor47_det (x:ℝ) : (minor47 x).det=2*x - 2 := by
 norm_num [minor47,Matrix.det_fin_two] <;> ring
#print axioms minor47_det
noncomputable def minor48 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![x - 6,-2,-2;-2,x - 4,-3;-2,-3,x - 6]
theorem minor48_det (x:ℝ) : (minor48 x).det=x^3 - 16*x^2 + 67*x - 74 := by
 have sub0 : (minor48 x).submatrix (0:Fin 3).succAbove (0:Fin 3).succAbove=minor45 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor48 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor46 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor48 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor47 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor48 x) (0:Fin 3) (0:Fin 3)=x - 6 := by rfl
 have entry1 : (minor48 x) (0:Fin 3) (Fin.succ (0:Fin 2))=-2 := by rfl
 have entry2 : (minor48 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-2 := by rfl
 rw [Matrix.det_succ_row (minor48 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor45_det, minor46_det, minor47_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor48_det
noncomputable def minor49 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,-3;-1,x - 6]
theorem minor49_det (x:ℝ) : (minor49 x).det=3 - x := by
 norm_num [minor49,Matrix.det_fin_two] <;> ring
#print axioms minor49_det
noncomputable def minor50 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,x - 4;-1,-3]
theorem minor50_det (x:ℝ) : (minor50 x).det=x - 1 := by
 norm_num [minor50,Matrix.det_fin_two] <;> ring
#print axioms minor50_det
noncomputable def minor51 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,-2,-2;-1,x - 4,-3;-1,-3,x - 6]
theorem minor51_det (x:ℝ) : (minor51 x).det=-x^2 + 6*x - 7 := by
 have sub0 : (minor51 x).submatrix (0:Fin 3).succAbove (0:Fin 3).succAbove=minor45 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor51 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor49 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor51 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor50 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor51 x) (0:Fin 3) (0:Fin 3)=-1 := by rfl
 have entry1 : (minor51 x) (0:Fin 3) (Fin.succ (0:Fin 2))=-2 := by rfl
 have entry2 : (minor51 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-2 := by rfl
 rw [Matrix.det_succ_row (minor51 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor45_det, minor49_det, minor50_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor51_det
noncomputable def minor52 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,-2;-1,-2]
theorem minor52_det (x:ℝ) : (minor52 x).det=0 := by
 norm_num [minor52,Matrix.det_fin_two] <;> ring
#print axioms minor52_det
noncomputable def minor53 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,x - 6,-2;-1,-2,-3;-1,-2,x - 6]
theorem minor53_det (x:ℝ) : (minor53 x).det=x^2 - 7*x + 12 := by
 have sub0 : (minor53 x).submatrix (0:Fin 3).succAbove (0:Fin 3).succAbove=minor46 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor53 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor49 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor53 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor52 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor53 x) (0:Fin 3) (0:Fin 3)=-1 := by rfl
 have entry1 : (minor53 x) (0:Fin 3) (Fin.succ (0:Fin 2))=x - 6 := by rfl
 have entry2 : (minor53 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-2 := by rfl
 rw [Matrix.det_succ_row (minor53 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor46_det, minor49_det, minor52_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor53_det
noncomputable def minor54 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,x - 6,-2;-1,-2,x - 4;-1,-2,-3]
theorem minor54_det (x:ℝ) : (minor54 x).det=-x^2 + 5*x - 4 := by
 have sub0 : (minor54 x).submatrix (0:Fin 3).succAbove (0:Fin 3).succAbove=minor47 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor54 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor50 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor54 x).submatrix (0:Fin 3).succAbove (Fin.succ (Fin.succ (0:Fin 1))).succAbove=minor52 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor54 x) (0:Fin 3) (0:Fin 3)=-1 := by rfl
 have entry1 : (minor54 x) (0:Fin 3) (Fin.succ (0:Fin 2))=x - 6 := by rfl
 have entry2 : (minor54 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=-2 := by rfl
 rw [Matrix.det_succ_row (minor54 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor47_det, minor50_det, minor52_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor54_det
noncomputable def minor55 (x:ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![x - 3,-1,-1,-1;-1,x - 6,-2,-2;-1,-2,x - 4,-3;-1,-2,-3,x - 6]
theorem minor55_det (x:ℝ) : (minor55 x).det=x^4 - 19*x^3 + 112*x^2 - 257*x + 199 := by
 have sub0 : (minor55 x).submatrix (0:Fin 4).succAbove (0:Fin 4).succAbove=minor48 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor55 x).submatrix (0:Fin 4).succAbove (Fin.succ (0:Fin 3)).succAbove=minor51 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor55 x).submatrix (0:Fin 4).succAbove (Fin.succ (Fin.succ (0:Fin 2))).succAbove=minor53 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub3 : (minor55 x).submatrix (0:Fin 4).succAbove (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))).succAbove=minor54 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor55 x) (0:Fin 4) (0:Fin 4)=x - 3 := by rfl
 have entry1 : (minor55 x) (0:Fin 4) (Fin.succ (0:Fin 3))=-1 := by rfl
 have entry2 : (minor55 x) (0:Fin 4) (Fin.succ (Fin.succ (0:Fin 2)))=-1 := by rfl
 have entry3 : (minor55 x) (0:Fin 4) (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor55 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, sub3, minor48_det, minor51_det, minor53_det, minor54_det]
 rw [entry0, entry1, entry2, entry3]
 norm_num <;> ring
#print axioms minor55_det
noncomputable def minor56 (x:ℝ) : Matrix (Fin 5) (Fin 5) ℝ := !![x - 3,-1,-1,-1,0;-1,x - 6,-2,-2,-1;-1,-2,x - 4,-3,0;-1,-2,-3,x - 6,0;0,-1,0,0,x - 3]
theorem minor56_det (x:ℝ) : (minor56 x).det=x^5 - 22*x^4 + 168*x^3 - 580*x^2 + 927*x - 556 := by
 have sub1 : (minor56 x).submatrix (4:Fin 5).succAbove (Fin.succ (0:Fin 4)).succAbove=minor44 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub4 : (minor56 x).submatrix (4:Fin 5).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))).succAbove=minor55 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor56 x) (4:Fin 5) (0:Fin 5)=0 := by rfl
 have entry1 : (minor56 x) (4:Fin 5) (Fin.succ (0:Fin 4))=-1 := by rfl
 have entry2 : (minor56 x) (4:Fin 5) (Fin.succ (Fin.succ (0:Fin 3)))=0 := by rfl
 have entry3 : (minor56 x) (4:Fin 5) (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))=0 := by rfl
 have entry4 : (minor56 x) (4:Fin 5) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))=x - 3 := by rfl
 rw [Matrix.det_succ_row (minor56 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub4, minor44_det, minor55_det]
 rw [entry0, entry1, entry2, entry3, entry4]
 norm_num <;> ring
#print axioms minor56_det
noncomputable def minor57 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-3,0;x - 6,0]
theorem minor57_det (x:ℝ) : (minor57 x).det=0 := by
 norm_num [minor57,Matrix.det_fin_two] <;> ring
#print axioms minor57_det
noncomputable def minor58 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x - 4,0;-3,0]
theorem minor58_det (x:ℝ) : (minor58 x).det=0 := by
 norm_num [minor58,Matrix.det_fin_two] <;> ring
#print axioms minor58_det
noncomputable def minor59 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-2,-2,0;x - 4,-3,0;-3,x - 6,0]
theorem minor59_det (x:ℝ) : (minor59 x).det=0 := by
 have sub0 : (minor59 x).submatrix (0:Fin 3).succAbove (0:Fin 3).succAbove=minor57 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor59 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor58 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor59 x) (0:Fin 3) (0:Fin 3)=-2 := by rfl
 have entry1 : (minor59 x) (0:Fin 3) (Fin.succ (0:Fin 2))=-2 := by rfl
 have entry2 : (minor59 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=0 := by rfl
 rw [Matrix.det_succ_row (minor59 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor57_det, minor58_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor59_det
noncomputable def minor60 (x:ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-1,0;-1,0]
theorem minor60_det (x:ℝ) : (minor60 x).det=0 := by
 norm_num [minor60,Matrix.det_fin_two] <;> ring
#print axioms minor60_det
noncomputable def minor61 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,-2,0;-1,-3,0;-1,x - 6,0]
theorem minor61_det (x:ℝ) : (minor61 x).det=0 := by
 have sub0 : (minor61 x).submatrix (0:Fin 3).succAbove (0:Fin 3).succAbove=minor57 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor61 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor60 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor61 x) (0:Fin 3) (0:Fin 3)=-1 := by rfl
 have entry1 : (minor61 x) (0:Fin 3) (Fin.succ (0:Fin 2))=-2 := by rfl
 have entry2 : (minor61 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=0 := by rfl
 rw [Matrix.det_succ_row (minor61 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor57_det, minor60_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor61_det
noncomputable def minor62 (x:ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-1,-2,0;-1,x - 4,0;-1,-3,0]
theorem minor62_det (x:ℝ) : (minor62 x).det=0 := by
 have sub0 : (minor62 x).submatrix (0:Fin 3).succAbove (0:Fin 3).succAbove=minor58 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor62 x).submatrix (0:Fin 3).succAbove (Fin.succ (0:Fin 2)).succAbove=minor60 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor62 x) (0:Fin 3) (0:Fin 3)=-1 := by rfl
 have entry1 : (minor62 x) (0:Fin 3) (Fin.succ (0:Fin 2))=-2 := by rfl
 have entry2 : (minor62 x) (0:Fin 3) (Fin.succ (Fin.succ (0:Fin 1)))=0 := by rfl
 rw [Matrix.det_succ_row (minor62 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, minor58_det, minor60_det]
 rw [entry0, entry1, entry2]
 norm_num <;> ring
#print axioms minor62_det
noncomputable def minor63 (x:ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![x - 3,-1,-1,0;-1,-2,-2,0;-1,x - 4,-3,0;-1,-3,x - 6,0]
theorem minor63_det (x:ℝ) : (minor63 x).det=0 := by
 have sub0 : (minor63 x).submatrix (0:Fin 4).succAbove (0:Fin 4).succAbove=minor59 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub1 : (minor63 x).submatrix (0:Fin 4).succAbove (Fin.succ (0:Fin 3)).succAbove=minor61 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor63 x).submatrix (0:Fin 4).succAbove (Fin.succ (Fin.succ (0:Fin 2))).succAbove=minor62 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor63 x) (0:Fin 4) (0:Fin 4)=x - 3 := by rfl
 have entry1 : (minor63 x) (0:Fin 4) (Fin.succ (0:Fin 3))=-1 := by rfl
 have entry2 : (minor63 x) (0:Fin 4) (Fin.succ (Fin.succ (0:Fin 2)))=-1 := by rfl
 have entry3 : (minor63 x) (0:Fin 4) (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))=0 := by rfl
 rw [Matrix.det_succ_row (minor63 x) 0]
 simp only [Fin.sum_univ_succ]
 rw [sub0, sub1, sub2, minor59_det, minor61_det, minor62_det]
 rw [entry0, entry1, entry2, entry3]
 norm_num <;> ring
#print axioms minor63_det
noncomputable def minor64 (x:ℝ) : Matrix (Fin 5) (Fin 5) ℝ := !![x - 3,-1,-1,-1,0;-1,x - 6,-2,-2,0;-1,-2,x - 4,-3,0;-1,-2,-3,x - 6,0;0,-1,0,0,-2]
theorem minor64_det (x:ℝ) : (minor64 x).det=-2*x^4 + 38*x^3 - 224*x^2 + 514*x - 398 := by
 have sub1 : (minor64 x).submatrix (4:Fin 5).succAbove (Fin.succ (0:Fin 4)).succAbove=minor63 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub4 : (minor64 x).submatrix (4:Fin 5).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))).succAbove=minor55 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor64 x) (4:Fin 5) (0:Fin 5)=0 := by rfl
 have entry1 : (minor64 x) (4:Fin 5) (Fin.succ (0:Fin 4))=-1 := by rfl
 have entry2 : (minor64 x) (4:Fin 5) (Fin.succ (Fin.succ (0:Fin 3)))=0 := by rfl
 have entry3 : (minor64 x) (4:Fin 5) (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))=0 := by rfl
 have entry4 : (minor64 x) (4:Fin 5) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))=-2 := by rfl
 rw [Matrix.det_succ_row (minor64 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub4, minor63_det, minor55_det]
 rw [entry0, entry1, entry2, entry3, entry4]
 norm_num <;> ring
#print axioms minor64_det
noncomputable def minor65 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![x - 3,-1,-1,-1,0,0;-1,x - 6,-2,-2,0,-1;-1,-2,x - 4,-3,0,0;-1,-2,-3,x - 6,0,0;0,0,0,0,x - 3,-2;0,-1,0,0,-2,x - 3]
theorem minor65_det (x:ℝ) : (minor65 x).det=x^6 - 25*x^5 + 230*x^4 - 1008*x^3 + 2219*x^2 - 2309*x + 872 := by
 have sub4 : (minor65 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))).succAbove=minor56 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor65 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))).succAbove=minor64 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor65 x) (4:Fin 6) (0:Fin 6)=0 := by rfl
 have entry1 : (minor65 x) (4:Fin 6) (Fin.succ (0:Fin 5))=0 := by rfl
 have entry2 : (minor65 x) (4:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor65 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor65 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=x - 3 := by rfl
 have entry5 : (minor65 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=-2 := by rfl
 rw [Matrix.det_succ_row (minor65 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, minor56_det, minor64_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor65_det
noncomputable def minor66 (x:ℝ) : Matrix (Fin 5) (Fin 5) ℝ := !![x - 3,-1,-1,-1,0;-1,x - 6,-2,-2,0;-1,-2,x - 4,-3,0;-1,-2,-3,x - 6,0;0,-1,0,0,-1]
theorem minor66_det (x:ℝ) : (minor66 x).det=-x^4 + 19*x^3 - 112*x^2 + 257*x - 199 := by
 have sub1 : (minor66 x).submatrix (4:Fin 5).succAbove (Fin.succ (0:Fin 4)).succAbove=minor63 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub4 : (minor66 x).submatrix (4:Fin 5).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))).succAbove=minor55 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor66 x) (4:Fin 5) (0:Fin 5)=0 := by rfl
 have entry1 : (minor66 x) (4:Fin 5) (Fin.succ (0:Fin 4))=-1 := by rfl
 have entry2 : (minor66 x) (4:Fin 5) (Fin.succ (Fin.succ (0:Fin 3)))=0 := by rfl
 have entry3 : (minor66 x) (4:Fin 5) (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))=0 := by rfl
 have entry4 : (minor66 x) (4:Fin 5) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor66 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub4, minor63_det, minor55_det]
 rw [entry0, entry1, entry2, entry3, entry4]
 norm_num <;> ring
#print axioms minor66_det
noncomputable def minor67 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![x - 3,-1,-1,-1,0,0;-1,x - 6,-2,-2,0,-1;-1,-2,x - 4,-3,0,0;-1,-2,-3,x - 6,0,0;0,0,0,0,-2,-2;0,-1,0,0,-1,x - 3]
theorem minor67_det (x:ℝ) : (minor67 x).det=-2*x^5 + 42*x^4 - 298*x^3 + 936*x^2 - 1340*x + 714 := by
 have sub4 : (minor67 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))).succAbove=minor56 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor67 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))).succAbove=minor66 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor67 x) (4:Fin 6) (0:Fin 6)=0 := by rfl
 have entry1 : (minor67 x) (4:Fin 6) (Fin.succ (0:Fin 5))=0 := by rfl
 have entry2 : (minor67 x) (4:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor67 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor67 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=-2 := by rfl
 have entry5 : (minor67 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=-2 := by rfl
 rw [Matrix.det_succ_row (minor67 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, minor56_det, minor66_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor67_det
noncomputable def minor68 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![x - 3,-1,-1,-1,0,0;-1,x - 6,-2,-2,0,0;-1,-2,x - 4,-3,0,0;-1,-2,-3,x - 6,0,0;0,0,0,0,-2,x - 3;0,-1,0,0,-1,-2]
theorem minor68_det (x:ℝ) : (minor68 x).det=x^5 - 18*x^4 + 93*x^3 - 145*x^2 - 58*x + 199 := by
 have sub4 : (minor68 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))).succAbove=minor64 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor68 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))).succAbove=minor66 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor68 x) (4:Fin 6) (0:Fin 6)=0 := by rfl
 have entry1 : (minor68 x) (4:Fin 6) (Fin.succ (0:Fin 5))=0 := by rfl
 have entry2 : (minor68 x) (4:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor68 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor68 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=-2 := by rfl
 have entry5 : (minor68 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=x - 3 := by rfl
 rw [Matrix.det_succ_row (minor68 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, minor64_det, minor66_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor68_det
noncomputable def minor69 (x:ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![x - 3,-1,-1,-1,0,0,0;-1,x - 6,-2,-2,0,0,-1;-1,-2,x - 4,-3,0,0,0;-1,-2,-3,x - 6,0,0,0;0,0,0,0,x - 2,-2,-1;0,0,0,0,-2,x - 3,-2;0,-1,0,0,-1,-2,x - 3]
theorem minor69_det (x:ℝ) : (minor69 x).det=x^7 - 27*x^6 + 275*x^5 - 1366*x^4 + 3546*x^3 - 4730*x^2 + 2868*x - 515 := by
 have sub4 : (minor69 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))).succAbove=minor65 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor69 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))).succAbove=minor67 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub6 : (minor69 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))).succAbove=minor68 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor69 x) (4:Fin 7) (0:Fin 7)=0 := by rfl
 have entry1 : (minor69 x) (4:Fin 7) (Fin.succ (0:Fin 6))=0 := by rfl
 have entry2 : (minor69 x) (4:Fin 7) (Fin.succ (Fin.succ (0:Fin 5)))=0 := by rfl
 have entry3 : (minor69 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))=0 := by rfl
 have entry4 : (minor69 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))=x - 2 := by rfl
 have entry5 : (minor69 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))=-2 := by rfl
 have entry6 : (minor69 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor69 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, sub6, minor65_det, minor67_det, minor68_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6]
 norm_num <;> ring
#print axioms minor69_det
noncomputable def minor70 (x:ℝ) : Matrix (Fin 5) (Fin 5) ℝ := !![x - 3,-1,-1,-1,0;-1,x - 6,-2,-2,0;-1,-2,x - 4,-3,0;-1,-2,-3,x - 6,0;0,-1,0,0,0]
theorem minor70_det (x:ℝ) : (minor70 x).det=0 := by
 have sub1 : (minor70 x).submatrix (4:Fin 5).succAbove (Fin.succ (0:Fin 4)).succAbove=minor63 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor70 x) (4:Fin 5) (0:Fin 5)=0 := by rfl
 have entry1 : (minor70 x) (4:Fin 5) (Fin.succ (0:Fin 4))=-1 := by rfl
 have entry2 : (minor70 x) (4:Fin 5) (Fin.succ (Fin.succ (0:Fin 3)))=0 := by rfl
 have entry3 : (minor70 x) (4:Fin 5) (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))=0 := by rfl
 have entry4 : (minor70 x) (4:Fin 5) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))=0 := by rfl
 rw [Matrix.det_succ_row (minor70 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub1, minor63_det]
 rw [entry0, entry1, entry2, entry3, entry4]
 norm_num <;> ring
#print axioms minor70_det
noncomputable def minor71 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![x - 3,-1,-1,-1,0,0;-1,x - 6,-2,-2,0,-1;-1,-2,x - 4,-3,0,0;-1,-2,-3,x - 6,0,0;0,0,0,0,-1,-2;0,-1,0,0,0,x - 3]
theorem minor71_det (x:ℝ) : (minor71 x).det=-x^5 + 22*x^4 - 168*x^3 + 580*x^2 - 927*x + 556 := by
 have sub4 : (minor71 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))).succAbove=minor56 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor71 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))).succAbove=minor70 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor71 x) (4:Fin 6) (0:Fin 6)=0 := by rfl
 have entry1 : (minor71 x) (4:Fin 6) (Fin.succ (0:Fin 5))=0 := by rfl
 have entry2 : (minor71 x) (4:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor71 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor71 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=-1 := by rfl
 have entry5 : (minor71 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=-2 := by rfl
 rw [Matrix.det_succ_row (minor71 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, minor56_det, minor70_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor71_det
noncomputable def minor72 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![x - 3,-1,-1,-1,0,0;-1,x - 6,-2,-2,0,0;-1,-2,x - 4,-3,0,0;-1,-2,-3,x - 6,0,0;0,0,0,0,-1,x - 3;0,-1,0,0,0,-2]
theorem minor72_det (x:ℝ) : (minor72 x).det=2*x^4 - 38*x^3 + 224*x^2 - 514*x + 398 := by
 have sub4 : (minor72 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))).succAbove=minor64 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor72 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))).succAbove=minor70 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor72 x) (4:Fin 6) (0:Fin 6)=0 := by rfl
 have entry1 : (minor72 x) (4:Fin 6) (Fin.succ (0:Fin 5))=0 := by rfl
 have entry2 : (minor72 x) (4:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor72 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor72 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=-1 := by rfl
 have entry5 : (minor72 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=x - 3 := by rfl
 rw [Matrix.det_succ_row (minor72 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, minor64_det, minor70_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor72_det
noncomputable def minor73 (x:ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![x - 3,-1,-1,-1,0,0,0;-1,x - 6,-2,-2,0,0,-1;-1,-2,x - 4,-3,0,0,0;-1,-2,-3,x - 6,0,0,0;0,0,0,0,-1,-2,-1;0,0,0,0,-1,x - 3,-2;0,-1,0,0,0,-2,x - 3]
theorem minor73_det (x:ℝ) : (minor73 x).det=-x^6 + 23*x^5 - 188*x^4 + 710*x^3 - 1283*x^2 + 969*x - 158 := by
 have sub4 : (minor73 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))).succAbove=minor65 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor73 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))).succAbove=minor71 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub6 : (minor73 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))).succAbove=minor72 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor73 x) (4:Fin 7) (0:Fin 7)=0 := by rfl
 have entry1 : (minor73 x) (4:Fin 7) (Fin.succ (0:Fin 6))=0 := by rfl
 have entry2 : (minor73 x) (4:Fin 7) (Fin.succ (Fin.succ (0:Fin 5)))=0 := by rfl
 have entry3 : (minor73 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))=0 := by rfl
 have entry4 : (minor73 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))=-1 := by rfl
 have entry5 : (minor73 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))=-2 := by rfl
 have entry6 : (minor73 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor73 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, sub6, minor65_det, minor71_det, minor72_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6]
 norm_num <;> ring
#print axioms minor73_det
noncomputable def minor74 (x:ℝ) : Matrix (Fin 6) (Fin 6) ℝ := !![x - 3,-1,-1,-1,0,0;-1,x - 6,-2,-2,0,0;-1,-2,x - 4,-3,0,0;-1,-2,-3,x - 6,0,0;0,0,0,0,-1,-2;0,-1,0,0,0,-1]
theorem minor74_det (x:ℝ) : (minor74 x).det=x^4 - 19*x^3 + 112*x^2 - 257*x + 199 := by
 have sub4 : (minor74 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))).succAbove=minor66 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor74 x).submatrix (4:Fin 6).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))).succAbove=minor70 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor74 x) (4:Fin 6) (0:Fin 6)=0 := by rfl
 have entry1 : (minor74 x) (4:Fin 6) (Fin.succ (0:Fin 5))=0 := by rfl
 have entry2 : (minor74 x) (4:Fin 6) (Fin.succ (Fin.succ (0:Fin 4)))=0 := by rfl
 have entry3 : (minor74 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))=0 := by rfl
 have entry4 : (minor74 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))=-1 := by rfl
 have entry5 : (minor74 x) (4:Fin 6) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))=-2 := by rfl
 rw [Matrix.det_succ_row (minor74 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, minor66_det, minor70_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5]
 norm_num <;> ring
#print axioms minor74_det
noncomputable def minor75 (x:ℝ) : Matrix (Fin 7) (Fin 7) ℝ := !![x - 3,-1,-1,-1,0,0,0;-1,x - 6,-2,-2,0,0,-1;-1,-2,x - 4,-3,0,0,0;-1,-2,-3,x - 6,0,0,0;0,0,0,0,-1,x - 2,-1;0,0,0,0,-1,-2,-2;0,-1,0,0,0,-1,x - 3]
theorem minor75_det (x:ℝ) : (minor75 x).det=x^6 - 22*x^5 + 169*x^4 - 599*x^3 + 1039*x^2 - 813*x + 199 := by
 have sub4 : (minor75 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))).succAbove=minor67 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor75 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))).succAbove=minor71 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub6 : (minor75 x).submatrix (4:Fin 7).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))).succAbove=minor74 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor75 x) (4:Fin 7) (0:Fin 7)=0 := by rfl
 have entry1 : (minor75 x) (4:Fin 7) (Fin.succ (0:Fin 6))=0 := by rfl
 have entry2 : (minor75 x) (4:Fin 7) (Fin.succ (Fin.succ (0:Fin 5)))=0 := by rfl
 have entry3 : (minor75 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))=0 := by rfl
 have entry4 : (minor75 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))=-1 := by rfl
 have entry5 : (minor75 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))=x - 2 := by rfl
 have entry6 : (minor75 x) (4:Fin 7) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))=-1 := by rfl
 rw [Matrix.det_succ_row (minor75 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, sub6, minor67_det, minor71_det, minor74_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6]
 norm_num <;> ring
#print axioms minor75_det
noncomputable def minor76 (x:ℝ) : Matrix (Fin 8) (Fin 8) ℝ := !![x - 3,-1,-1,-1,0,0,0,0;-1,x - 6,-2,-2,0,0,0,-1;-1,-2,x - 4,-3,0,0,0,0;-1,-2,-3,x - 6,0,0,0,0;0,0,0,0,x - 1,-1,-1,0;0,0,0,0,-1,x - 2,-2,-1;0,0,0,0,-1,-2,x - 3,-2;0,-1,0,0,0,-1,-2,x - 3]
theorem minor76_det (x:ℝ) : (minor76 x).det=x^8 - 28*x^7 + 300*x^6 - 1596*x^5 + 4555*x^4 - 6967*x^3 + 5276*x^2 - 1601*x + 158 := by
 have sub4 : (minor76 x).submatrix (4:Fin 8).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))).succAbove=minor69 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub5 : (minor76 x).submatrix (4:Fin 8).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))).succAbove=minor73 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub6 : (minor76 x).submatrix (4:Fin 8).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))).succAbove=minor75 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor76 x) (4:Fin 8) (0:Fin 8)=0 := by rfl
 have entry1 : (minor76 x) (4:Fin 8) (Fin.succ (0:Fin 7))=0 := by rfl
 have entry2 : (minor76 x) (4:Fin 8) (Fin.succ (Fin.succ (0:Fin 6)))=0 := by rfl
 have entry3 : (minor76 x) (4:Fin 8) (Fin.succ (Fin.succ (Fin.succ (0:Fin 5))))=0 := by rfl
 have entry4 : (minor76 x) (4:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 4)))))=x - 1 := by rfl
 have entry5 : (minor76 x) (4:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3))))))=-1 := by rfl
 have entry6 : (minor76 x) (4:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2)))))))=-1 := by rfl
 have entry7 : (minor76 x) (4:Fin 8) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1))))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor76 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub4, sub5, sub6, minor69_det, minor73_det, minor75_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7]
 norm_num <;> ring
#print axioms minor76_det
noncomputable def minor77 (x:ℝ) : Matrix (Fin 9) (Fin 9) ℝ := !![x - 3,-1,-1,-1,0,0,0,0,0;-1,x - 6,-2,-2,-3,0,0,0,-1;-1,-2,x - 4,-3,-1,0,0,0,0;-1,-2,-3,x - 6,0,0,0,0,0;0,-3,-1,0,x - 3,0,0,0,0;0,0,0,0,0,x - 1,-1,-1,0;0,0,0,0,0,-1,x - 2,-2,-1;0,0,0,0,0,-1,-2,x - 3,-2;0,-1,0,0,0,0,-1,-2,x - 3]
theorem minor77_det (x:ℝ) : (minor77 x).det=x^9 - 31*x^8 + 374*x^7 - 2286*x^6 + 7697*x^5 - 14557*x^4 + 15014*x^3 - 7755*x^2 + 1732*x - 124 := by
 have sub1 : (minor77 x).submatrix (4:Fin 9).succAbove (Fin.succ (0:Fin 8)).succAbove=minor25 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub2 : (minor77 x).submatrix (4:Fin 9).succAbove (Fin.succ (Fin.succ (0:Fin 7))).succAbove=minor37 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have sub4 : (minor77 x).submatrix (4:Fin 9).succAbove (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 5))))).succAbove=minor76 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> rfl
 have entry0 : (minor77 x) (4:Fin 9) (0:Fin 9)=0 := by rfl
 have entry1 : (minor77 x) (4:Fin 9) (Fin.succ (0:Fin 8))=-3 := by rfl
 have entry2 : (minor77 x) (4:Fin 9) (Fin.succ (Fin.succ (0:Fin 7)))=-1 := by rfl
 have entry3 : (minor77 x) (4:Fin 9) (Fin.succ (Fin.succ (Fin.succ (0:Fin 6))))=0 := by rfl
 have entry4 : (minor77 x) (4:Fin 9) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 5)))))=x - 3 := by rfl
 have entry5 : (minor77 x) (4:Fin 9) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 4))))))=0 := by rfl
 have entry6 : (minor77 x) (4:Fin 9) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 3)))))))=0 := by rfl
 have entry7 : (minor77 x) (4:Fin 9) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 2))))))))=0 := by rfl
 have entry8 : (minor77 x) (4:Fin 9) (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0:Fin 1)))))))))=0 := by rfl
 rw [Matrix.det_succ_row (minor77 x) 4]
 simp only [Fin.sum_univ_succ]
 rw [sub1, sub2, sub4, minor25_det, minor37_det, minor76_det]
 rw [entry0, entry1, entry2, entry3, entry4, entry5, entry6, entry7, entry8]
 norm_num <;> ring
#print axioms minor77_det
noncomputable def sourceMatrix : Matrix (Fin 12) (Fin 9) ℝ := !![1,0,0,1,0,0,0,0,0;1,0,1,0,0,0,0,0,0;1,1,0,0,0,0,0,0,0;0,1,1,0,1,0,0,0,0;0,1,1,2,0,0,0,0,0;0,1,0,0,1,0,0,0,0;0,1,0,0,1,0,0,0,0;0,0,1,1,0,0,0,0,0;0,1,0,0,0,0,0,0,1;0,0,0,0,0,1,1,1,0;0,0,0,0,0,0,1,1,1;0,0,0,0,0,0,0,1,1]
noncomputable def gram : Matrix (Fin 9) (Fin 9) ℝ := !![3,1,1,1,0,0,0,0,0;1,6,2,2,3,0,0,0,1;1,2,4,3,1,0,0,0,0;1,2,3,6,0,0,0,0,0;0,3,1,0,3,0,0,0,0;0,0,0,0,0,1,1,1,0;0,0,0,0,0,1,2,2,1;0,0,0,0,0,1,2,3,2;0,1,0,0,0,0,1,2,3]
theorem gram_from_source : sourceMatrix.transpose*sourceMatrix=gram := by
 ext i j
 fin_cases i <;> fin_cases j <;> norm_num [sourceMatrix,gram,Matrix.mul_apply,Fin.sum_univ_succ]

theorem determinant_polynomial (x:ℝ) : (Matrix.scalar (Fin 9) x-gram).det=x^9 - 31*x^8 + 374*x^7 - 2286*x^6 + 7697*x^5 - 14557*x^4 + 15014*x^3 - 7755*x^2 + 1732*x - 124 := by
 have hmat : Matrix.scalar (Fin 9) x-gram=minor77 x := by
   ext i j
   fin_cases i <;> fin_cases j <;> norm_num [gram,minor77,Matrix.scalar_apply,Matrix.diagonal_apply]
 rw [hmat,minor77_det]

noncomputable def characteristic : Polynomial ℝ := X^9-31*X^8+374*X^7-2286*X^6+7697*X^5-14557*X^4+15014*X^3-7755*X^2+1732*X-124

theorem characteristic_from_gram : gram.charpoly=characteristic := by
 apply Polynomial.funext
 intro x
 rw [Matrix.eval_charpoly]
 rw [determinant_polynomial]
 simp [characteristic]
 <;> ring

#print axioms gram_from_source
#print axioms determinant_polynomial
#print axioms characteristic_from_gram
end Chapter04Spectrum
