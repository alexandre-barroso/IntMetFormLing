import Mathlib
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
open scoped BigOperators
namespace Chapter06Figures

lemma logEnclosure (x a b:ℝ) (n:ℕ) (hx:|x|<1)
 (ha:a<2*((∑ i ∈ Finset.range n,x^(2*i+1)/(2*i+1))-|x|^(2*n+1)/(1-x^2)))
 (hb:2*((∑ i ∈ Finset.range n,x^(2*i+1)/(2*i+1))+|x|^(2*n+1)/(1-x^2))<b) :
 a<Real.log ((1+x)/(1-x)) ∧ Real.log ((1+x)/(1-x))<b := by
 have h:=abs_le.mp (Real.sum_range_sub_log_div_le hx n)
 constructor <;> linarith [h.1,h.2]

theorem log2 : ((34657359027997/50000000000000):ℝ)<Real.log (2:ℝ) ∧ Real.log (2:ℝ)<((13862943611199/20000000000000):ℝ) := by
 have h:=logEnclosure ((1/3):ℝ) ((34657359027997/50000000000000):ℝ) ((13862943611199/20000000000000):ℝ) 15 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms log2


noncomputable def density (t:ℝ) : ℝ :=
 Real.exp (-((Real.log t+268/100)^2)/(2*(59/100)^2))/(t*(59/100)*Real.sqrt (2*Real.pi))

theorem sqrt_two_pi : (250662827463100/100000000000000:ℝ)<Real.sqrt (2*Real.pi) ∧
    Real.sqrt (2*Real.pi)<(250662827463101/100000000000000:ℝ) := by
 have h:=Real.sq_sqrt (by positivity : (0:ℝ)≤2*Real.pi)
 have hp:=Real.pi_gt_d20
 have hq:=Real.pi_lt_d20
 have hn:=Real.sqrt_nonneg (2*Real.pi)
 constructor <;> nlinarith

theorem logScaled0 : ((65232518603969/100000000000000):ℝ)<Real.log ((48/25):ℝ) ∧ Real.log ((48/25):ℝ)<((6523251860397/10000000000000):ℝ) := by
 have h:=logEnclosure ((23/73):ℝ) ((65232518603969/100000000000000):ℝ) ((6523251860397/10000000000000):ℝ) 16 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms logScaled0

theorem log_t0 : ((-1753278948661/500000000000):ℝ)<Real.log ((3/100):ℝ) ∧ Real.log ((3/100):ℝ)<((-3506557897317/1000000000000):ℝ) := by
 have h:=logScaled0
 have h2:=log2
 have hid : Real.log ((3/100):ℝ)=Real.log ((48/25):ℝ)-6*Real.log 2 := by
   have hh:=Real.log_div (by norm_num : ((48/25):ℝ)≠0) (by norm_num : (2:ℝ)^6≠0)
   rw [Real.log_pow] at hh
   norm_num at hh ⊢
   exact hh
 rw [hid]
 constructor <;> linarith

theorem expLo0 : ((46851801750617/125000000000000):ℝ)<Real.exp ((-1962648543/2000000000):ℝ) ∧ Real.exp ((-1962648543/2000000000):ℝ)<((374814414004937/1000000000000000):ℝ) := by
 have h := Real.exp_bound (x:=((-1962648543/2000000000):ℝ)) (by norm_num) (n:=24) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
#print axioms expLo0

theorem expHi0 : ((374814414192343/1000000000000000):ℝ)<Real.exp ((-981324271/1000000000):ℝ) ∧ Real.exp ((-981324271/1000000000):ℝ)<((46851801774043/125000000000000):ℝ) := by
 have h := Real.exp_bound (x:=((-981324271/1000000000):ℝ)) (by norm_num) (n:=24) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
#print axioms expHi0

theorem density_endpoint0 : |density ((3/100))-(527999/62500)|<1/2000000 := by
 have h:=log_t0
 have hs1 : ((-826557897317/1000000000000):ℝ)^2≤(Real.log ((3/100):ℝ)+268/100)^2 := by nlinarith [sq_nonneg (Real.log ((3/100):ℝ)+268/100-(-826557897317/1000000000000))]
 have hs2 : (Real.log ((3/100):ℝ)+268/100)^2≤((-413278948661/500000000000):ℝ)^2 := by
   have hh:=mul_self_le_mul_self (by linarith : (0:ℝ)≤-(Real.log ((3/100):ℝ)+268/100)) (by linarith : -(Real.log ((3/100):ℝ)+268/100)≤-(-413278948661/500000000000))
   nlinarith
 have helo : ((-1962648543/2000000000):ℝ)<(-((Real.log ((3/100):ℝ)+268/100)^2)/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
 have hehi : (-((Real.log ((3/100):ℝ)+268/100)^2)/(2*(59/100)^2))<((-981324271/1000000000):ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
 have hlo:=lt_trans (expLo0).1 (Real.exp_lt_exp.mpr helo)
 have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) (expHi0).2
 have hs:=sqrt_two_pi
 have hp : 0<((3/100):ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
 unfold density
 rw [abs_lt]
 constructor
 · have hh : ((527999/62500)-1/2000000:ℝ)<Real.exp (-((Real.log ((3/100):ℝ)+268/100)^2)/(2*(59/100)^2))/(((3/100):ℝ)*(59/100)*Real.sqrt (2*Real.pi)) := by
     apply (lt_div_iff₀ hp).2
     nlinarith
   linarith
 · have hh : Real.exp (-((Real.log ((3/100):ℝ)+268/100)^2)/(2*(59/100)^2))/(((3/100):ℝ)*(59/100)*Real.sqrt (2*Real.pi))<((527999/62500)+1/2000000:ℝ) := by
     apply (div_lt_iff₀ hp).2
     nlinarith
   linarith
#print axioms density_endpoint0

theorem logScaled1 : ((113328685307/1000000000000):ℝ)<Real.log ((28/25):ℝ) ∧ Real.log ((28/25):ℝ)<((11332868530701/100000000000000):ℝ) := by
 have h:=logEnclosure ((3/53):ℝ) ((113328685307/1000000000000):ℝ) ((11332868530701/100000000000000):ℝ) 6 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms logScaled1

theorem log_t1 : ((-15728902851/8000000000):ℝ)<Real.log ((7/50):ℝ) ∧ Real.log ((7/50):ℝ)<((-196611285637/100000000000):ℝ) := by
 have h:=logScaled1
 have h2:=log2
 have hid : Real.log ((7/50):ℝ)=Real.log ((28/25):ℝ)-3*Real.log 2 := by
   have hh:=Real.log_div (by norm_num : ((28/25):ℝ)≠0) (by norm_num : (2:ℝ)^3≠0)
   rw [Real.log_pow] at hh
   norm_num at hh ⊢
   exact hh
 rw [hid]
 constructor <;> linarith

theorem expLo1 : ((96186953747827/200000000000000):ℝ)<Real.exp ((-366011817/500000000):ℝ) ∧ Real.exp ((-366011817/500000000):ℝ)<((7514605761549/15625000000000):ℝ) := by
 have h := Real.exp_bound (x:=((-366011817/500000000):ℝ)) (by norm_num) (n:=24) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
#print axioms expLo1

theorem expHi1 : ((480934768979603/1000000000000000):ℝ)<Real.exp ((-1464047267/2000000000):ℝ) ∧ Real.exp ((-1464047267/2000000000):ℝ)<((120233692244901/250000000000000):ℝ) := by
 have h := Real.exp_bound (x:=((-1464047267/2000000000):ℝ)) (by norm_num) (n:=24) (by norm_num)
 norm_num [Finset.sum_range_succ,Nat.factorial] at h
 rcases abs_le.mp h with ⟨hl,hu⟩
 constructor <;> linarith
#print axioms expHi1

theorem density_endpoint1 : |density ((7/50))-(2322823/1000000)|<1/2000000 := by
 have h:=log_t1
 have hs1 : ((5711097149/8000000000):ℝ)^2≤(Real.log ((7/50):ℝ)+268/100)^2 := by
   have hh:=mul_self_le_mul_self (by norm_num : (0:ℝ)≤(5711097149/8000000000)) (by linarith : (5711097149/8000000000)≤Real.log ((7/50):ℝ)+268/100)
   nlinarith
 have hs2 : (Real.log ((7/50):ℝ)+268/100)^2≤((71388714363/100000000000):ℝ)^2 := by
   have hh:=mul_self_le_mul_self (by linarith : (0:ℝ)≤Real.log ((7/50):ℝ)+268/100) (by linarith : Real.log ((7/50):ℝ)+268/100≤(71388714363/100000000000))
   nlinarith
 have helo : ((-366011817/500000000):ℝ)<(-((Real.log ((7/50):ℝ)+268/100)^2)/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
 have hehi : (-((Real.log ((7/50):ℝ)+268/100)^2)/(2*(59/100)^2))<((-1464047267/2000000000):ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
 have hlo:=lt_trans (expLo1).1 (Real.exp_lt_exp.mpr helo)
 have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) (expHi1).2
 have hs:=sqrt_two_pi
 have hp : 0<((7/50):ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
 unfold density
 rw [abs_lt]
 constructor
 · have hh : ((2322823/1000000)-1/2000000:ℝ)<Real.exp (-((Real.log ((7/50):ℝ)+268/100)^2)/(2*(59/100)^2))/(((7/50):ℝ)*(59/100)*Real.sqrt (2*Real.pi)) := by
     apply (lt_div_iff₀ hp).2
     nlinarith
   linarith
 · have hh : Real.exp (-((Real.log ((7/50):ℝ)+268/100)^2)/(2*(59/100)^2))/(((7/50):ℝ)*(59/100)*Real.sqrt (2*Real.pi))<((2322823/1000000)+1/2000000:ℝ) := by
     apply (div_lt_iff₀ hp).2
     nlinarith
   linarith
#print axioms density_endpoint1

end Chapter06Figures
