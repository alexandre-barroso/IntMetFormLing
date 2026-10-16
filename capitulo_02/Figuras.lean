import Mathlib
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192
open scoped BigOperators
namespace Chapter02Figures

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

theorem logA : ((37569294977449/100000000000000):ℝ)<Real.log ((182/125):ℝ) ∧ Real.log ((182/125):ℝ)<((751385899549/2000000000000):ℝ) := by
 have h:=logEnclosure ((57/307):ℝ) ((37569294977449/100000000000000):ℝ) ((751385899549/2000000000000):ℝ) 10 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms logA

theorem logRank : ((228426353139/4000000000000):ℝ)<Real.log ((1135/1072):ℝ) ∧ Real.log ((1135/1072):ℝ)<((1427664707119/25000000000000):ℝ) := by
 have h:=logEnclosure ((63/2207):ℝ) ((228426353139/4000000000000):ℝ) ((1427664707119/25000000000000):ℝ) 5 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms logRank

theorem logVelocityLower : ((79164332840927/50000000000000):ℝ)<Real.log ((9741877271/2000000000):ℝ) ∧ Real.log ((9741877271/2000000000):ℝ)<((31665733136371/20000000000000):ℝ) := by
 have h:=logEnclosure ((7741877271/11741877271):ℝ) ((79164332840927/50000000000000):ℝ) ((31665733136371/20000000000000):ℝ) 42 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms logVelocityLower

theorem logVelocityUpper : ((9895541606399/6250000000000):ℝ)<Real.log ((9741877273/2000000000):ℝ) ∧ Real.log ((9741877273/2000000000):ℝ)<((31665733140477/20000000000000):ℝ) := by
 have h:=logEnclosure ((7741877273/11741877273):ℝ) ((9895541606399/6250000000000):ℝ) ((31665733140477/20000000000000):ℝ) 41 (by norm_num)
  (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
 norm_num at h ⊢
 exact h
#print axioms logVelocityUpper


noncomputable def velocity (n:ℝ) : ℝ := 1/((364/1000:ℝ)*n^(-227/1000:ℝ)*Real.exp ((67/10000:ℝ)*n))

theorem maximum_position : (227/1000:ℚ)/(67/10000)=2270/67 ∧ |(2270/67:ℚ)-33880597/1000000|<1/2000000 := by norm_num

theorem log_velocity : Real.log (velocity (2270/67))=
    (627/200:ℝ)*Real.log 2-Real.log (182/125)+(227/1000:ℝ)*Real.log (1135/1072)-227/1000 := by
 have hn : (2270/67:ℝ)>0 := by norm_num
 have hpow : (0:ℝ)<(2270/67:ℝ)^(-227/1000:ℝ) := Real.rpow_pos_of_pos hn _
 unfold velocity
 rw [Real.log_div (by norm_num) (by positivity),Real.log_one,
   Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
   Real.log_mul (by norm_num) (ne_of_gt hpow),Real.log_rpow hn,Real.log_exp]
 have ha : Real.log (364/1000:ℝ)=Real.log (182/125:ℝ)-2*Real.log 2 := by
   have h:=Real.log_div (by norm_num : (182/125:ℝ)≠0) (by norm_num : (2:ℝ)^2≠0)
   rw [Real.log_pow] at h
   norm_num at h ⊢
   exact h
 have hr : Real.log (2270/67:ℝ)=Real.log (1135/1072:ℝ)+5*Real.log 2 := by
   have h:=Real.log_mul (by norm_num : (1135/1072:ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
   rw [Real.log_pow] at h
   norm_num at h ⊢
   exact h
 rw [ha,hr]
 ring

theorem maximum_velocity_point : |velocity (2270/67)-4870938636/1000000000|<1/2000000000 := by
 have hlog:=log_velocity
 have ha:=logA
 have hb:=logRank
 have hc:=log2
 have hl:=logVelocityLower
 have hu:=logVelocityUpper
 have hv : 0<velocity (2270/67) := by unfold velocity; positivity
 have hlo : Real.log (9741877271/2000000000:ℝ)<Real.log (velocity (2270/67)) := by linarith
 have hup : Real.log (velocity (2270/67))<Real.log (9741877273/2000000000:ℝ) := by linarith
 have lo : (9741877271/2000000000:ℝ)<velocity (2270/67) := (Real.log_lt_log_iff (by norm_num) hv).mp hlo
 have up : velocity (2270/67)<(9741877273/2000000000:ℝ) := (Real.log_lt_log_iff hv (by norm_num)).mp hup
 rw [abs_lt]
 constructor <;> linarith

#print axioms maximum_position
#print axioms log_velocity
#print axioms maximum_velocity_point

theorem velocity_derivative (n:ℝ) (hn:0<n) :
    HasDerivAt velocity (velocity n*((227/1000:ℝ)/n-67/10000)) n := by
  have hp := (Real.hasDerivAt_rpow_const (p:=(-227/1000:ℝ)) (Or.inl (ne_of_gt hn))).const_mul (364/1000:ℝ)
  have he := ((hasDerivAt_id n).const_mul (67/10000:ℝ)).exp
  have hy := hp.mul he
  have hpos : (0:ℝ)<(364/1000:ℝ)*n^(-227/1000:ℝ)*Real.exp ((67/10000:ℝ)*n) := by positivity
  convert! hy.inv (ne_of_gt hpos) using 1
  · ext x
    simp [velocity,one_div]
  · rw [Real.rpow_sub hn,Real.rpow_one]
    unfold velocity
    simp only [id_eq,Pi.mul_apply]
    field_simp
    ring

theorem velocity_derivative_positive (n:ℝ) (hn:0<n) (hb:n<2270/67) :
    0<deriv velocity n := by
  rw [(velocity_derivative n hn).deriv]
  apply mul_pos
  · unfold velocity
    positivity
  · apply sub_pos.mpr
    apply (lt_div_iff₀ hn).mpr
    linarith

theorem velocity_derivative_negative (n:ℝ) (hb:2270/67<n) :
    deriv velocity n<0 := by
  have hn:0<n := by linarith
  rw [(velocity_derivative n hn).deriv]
  apply mul_neg_of_pos_of_neg
  · unfold velocity
    positivity
  · apply sub_neg.mpr
    apply (div_lt_iff₀ hn).mpr
    linarith

theorem velocity_increasing : StrictMonoOn velocity (Set.Ioc (0:ℝ) (2270/67)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc _ _)
  · intro x hx
    exact (velocity_derivative x hx.1).continuousAt.continuousWithinAt
  · intro x hx
    simp only [interior_Ioc] at hx
    exact velocity_derivative_positive x hx.1 hx.2

theorem velocity_decreasing : StrictAntiOn velocity (Set.Ici (2270/67:ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (velocity_derivative x (by have h : (2270/67:ℝ)≤x := hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    simp only [interior_Ici] at hx
    exact velocity_derivative_negative x hx

theorem velocity_global_maximum (n:ℝ) (hn:0<n) : velocity n≤velocity (2270/67) := by
  rcases lt_trichotomy n (2270/67:ℝ) with hl | he | hr
  · exact (velocity_increasing ⟨hn,hl.le⟩ ⟨by norm_num,le_rfl⟩ hl).le
  · simp [he]
  · exact (velocity_decreasing (by simp) (by simpa using hr.le) hr).le

#print axioms velocity_global_maximum
#print axioms velocity_derivative
#print axioms velocity_derivative_positive
#print axioms velocity_derivative_negative
#print axioms velocity_increasing
#print axioms velocity_decreasing
end Chapter02Figures
