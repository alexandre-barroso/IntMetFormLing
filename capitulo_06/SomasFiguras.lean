import capitulo_06.Area
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
open scoped BigOperators
namespace Chapter06RightSums
theorem logScaled1 : (67658648473/1000000000000 : ℝ)<Real.log (107/100 : ℝ) ∧ Real.log (107/100 : ℝ)<(33829324237/500000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (7/207 : ℝ) (67658648473/1000000000000 : ℝ) (33829324237/500000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint1 : (-169903863/50000000 : ℝ)<Real.log (107/3200 : ℝ) ∧ Real.log (107/3200 : ℝ)<(-13592309/4000000 : ℝ) := by
  have h:=logScaled1
  have h2:=Chapter06Figures.log2
  have hid : Real.log (107/3200 : ℝ)=Real.log (107/100 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (107/100 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo1 : (47680771/100000000 : ℝ)<Real.exp (-74064199/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-74064199/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi1 : Real.exp (-18516049/25000000 : ℝ)<(47680773/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-18516049/25000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density1 : (4821/500 : ℝ)<Chapter06Figures.density (107/3200 : ℝ) ∧ Chapter06Figures.density (107/3200 : ℝ)<(96421/10000 : ℝ) := by
  have h:=logPoint1
  have hs1 : (-2872309/4000000 : ℝ)^2≤(Real.log (107/3200 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-2872309/4000000 : ℝ)) (by linarith : 0≤-(Real.log (107/3200 : ℝ)+268/100))).mpr (by linarith : -(-2872309/4000000 : ℝ)≤-(Real.log (107/3200 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (107/3200 : ℝ)+268/100)^2≤(-35903863/50000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (107/3200 : ℝ)+268/100)) (by norm_num : 0≤-(-35903863/50000000 : ℝ))).mpr (by linarith : -(Real.log (107/3200 : ℝ)+268/100)≤-(-35903863/50000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-74064199/100000000 : ℝ)<(-(Real.log (107/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (107/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-18516049/25000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo1 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi1
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(107/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled2 : (165514438477/1000000000000 : ℝ)<Real.log (59/50 : ℝ) ∧ Real.log (59/50 : ℝ)<(82757219239/500000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (9/109 : ℝ) (165514438477/1000000000000 : ℝ) (82757219239/500000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint2 : (-330022147/100000000 : ℝ)<Real.log (59/1600 : ℝ) ∧ Real.log (59/1600 : ℝ)<(-165011073/50000000 : ℝ) := by
  have h:=logScaled2
  have h2:=Chapter06Figures.log2
  have hid : Real.log (59/1600 : ℝ)=Real.log (59/50 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (59/50 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo2 : (2301957/4000000 : ℝ)<Real.exp (-1726671/3125000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-1726671/3125000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi2 : Real.exp (-5525347/10000000 : ℝ)<(57548927/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-5525347/10000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density2 : (52763/5000 : ℝ)<Chapter06Figures.density (59/1600 : ℝ) ∧ Chapter06Figures.density (59/1600 : ℝ)<(105527/10000 : ℝ) := by
  have h:=logPoint2
  have hs1 : (-31011073/50000000 : ℝ)^2≤(Real.log (59/1600 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-31011073/50000000 : ℝ)) (by linarith : 0≤-(Real.log (59/1600 : ℝ)+268/100))).mpr (by linarith : -(-31011073/50000000 : ℝ)≤-(Real.log (59/1600 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (59/1600 : ℝ)+268/100)^2≤(-62022147/100000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (59/1600 : ℝ)+268/100)) (by norm_num : 0≤-(-62022147/100000000 : ℝ))).mpr (by linarith : -(Real.log (59/1600 : ℝ)+268/100)≤-(-62022147/100000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-1726671/3125000 : ℝ)<(-(Real.log (59/1600 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (59/1600 : ℝ)+268/100)^2/(2*(59/100)^2))<(-5525347/10000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo2 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi2
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(59/1600 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled3 : (254642218373/1000000000000 : ℝ)<Real.log (129/100 : ℝ) ∧ Real.log (129/100 : ℝ)<(127321109187/500000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (29/229 : ℝ) (254642218373/1000000000000 : ℝ) (127321109187/500000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint3 : (-321109369/100000000 : ℝ)<Real.log (129/3200 : ℝ) ∧ Real.log (129/3200 : ℝ)<(-40138671/12500000 : ℝ) := by
  have h:=logScaled3
  have h2:=Chapter06Figures.log2
  have hid : Real.log (129/3200 : ℝ)=Real.log (129/100 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (129/100 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo3 : (16672037/25000000 : ℝ)<Real.exp (-40514293/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-40514293/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi3 : Real.exp (-40514291/100000000 : ℝ)<(66688151/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-40514291/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density3 : (111857/10000 : ℝ)<Chapter06Figures.density (129/3200 : ℝ) ∧ Chapter06Figures.density (129/3200 : ℝ)<(55929/5000 : ℝ) := by
  have h:=logPoint3
  have hs1 : (-6638671/12500000 : ℝ)^2≤(Real.log (129/3200 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-6638671/12500000 : ℝ)) (by linarith : 0≤-(Real.log (129/3200 : ℝ)+268/100))).mpr (by linarith : -(-6638671/12500000 : ℝ)≤-(Real.log (129/3200 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (129/3200 : ℝ)+268/100)^2≤(-53109369/100000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (129/3200 : ℝ)+268/100)) (by norm_num : 0≤-(-53109369/100000000 : ℝ))).mpr (by linarith : -(Real.log (129/3200 : ℝ)+268/100)≤-(-53109369/100000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-40514293/100000000 : ℝ)<(-(Real.log (129/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (129/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-40514291/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo3 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi3
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(129/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled4 : (336472236621/1000000000000 : ℝ)<Real.log (7/5 : ℝ) ∧ Real.log (7/5 : ℝ)<(168236118311/500000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (1/6 : ℝ) (336472236621/1000000000000 : ℝ) (168236118311/500000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint4 : (-312926367/100000000 : ℝ)<Real.log (7/160 : ℝ) ∧ Real.log (7/160 : ℝ)<(-156463183/50000000 : ℝ) := by
  have h:=logScaled4
  have h2:=Chapter06Figures.log2
  have hid : Real.log (7/160 : ℝ)=Real.log (7/5 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (7/5 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo4 : (37416411/50000000 : ℝ)<Real.exp (-45299/156250 : ℝ) := by
  have h:=Real.exp_bound (x:=(-45299/156250 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi4 : Real.exp (-14495679/50000000 : ℝ)<(9354103/12500000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-14495679/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density4 : (115657/10000 : ℝ)<Chapter06Figures.density (7/160 : ℝ) ∧ Chapter06Figures.density (7/160 : ℝ)<(57829/5000 : ℝ) := by
  have h:=logPoint4
  have hs1 : (-22463183/50000000 : ℝ)^2≤(Real.log (7/160 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-22463183/50000000 : ℝ)) (by linarith : 0≤-(Real.log (7/160 : ℝ)+268/100))).mpr (by linarith : -(-22463183/50000000 : ℝ)≤-(Real.log (7/160 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (7/160 : ℝ)+268/100)^2≤(-44926367/100000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (7/160 : ℝ)+268/100)) (by norm_num : 0≤-(-44926367/100000000 : ℝ))).mpr (by linarith : -(Real.log (7/160 : ℝ)+268/100)≤-(-44926367/100000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-45299/156250 : ℝ)<(-(Real.log (7/160 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (7/160 : ℝ)+268/100)^2/(2*(59/100)^2))<(-14495679/50000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo4 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi4
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(7/160 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled5 : (206054825413/500000000000 : ℝ)<Real.log (151/100 : ℝ) ∧ Real.log (151/100 : ℝ)<(412109650827/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (51/251 : ℝ) (206054825413/500000000000 : ℝ) (412109650827/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint5 : (-152681313/50000000 : ℝ)<Real.log (151/3200 : ℝ) ∧ Real.log (151/3200 : ℝ)<(-2442901/800000 : ℝ) := by
  have h:=logScaled5
  have h2:=Chapter06Figures.log2
  have hid : Real.log (151/3200 : ℝ)=Real.log (151/100 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (151/100 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo5 : (81831151/100000000 : ℝ)<Real.exp (-20051219/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-20051219/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi5 : Real.exp (-20051217/100000000 : ℝ)<(40915577/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-20051217/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density5 : (117259/10000 : ℝ)<Chapter06Figures.density (151/3200 : ℝ) ∧ Chapter06Figures.density (151/3200 : ℝ)<(5863/500 : ℝ) := by
  have h:=logPoint5
  have hs1 : (-298901/800000 : ℝ)^2≤(Real.log (151/3200 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-298901/800000 : ℝ)) (by linarith : 0≤-(Real.log (151/3200 : ℝ)+268/100))).mpr (by linarith : -(-298901/800000 : ℝ)≤-(Real.log (151/3200 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (151/3200 : ℝ)+268/100)^2≤(-18681313/50000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (151/3200 : ℝ)+268/100)) (by norm_num : 0≤-(-18681313/50000000 : ℝ))).mpr (by linarith : -(Real.log (151/3200 : ℝ)+268/100)≤-(-18681313/50000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-20051219/100000000 : ℝ)<(-(Real.log (151/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (151/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-20051217/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo5 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi5
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(151/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled6 : (120606537311/250000000000 : ℝ)<Real.log (81/50 : ℝ) ∧ Real.log (81/50 : ℝ)<(96485229849/200000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (31/131 : ℝ) (120606537311/250000000000 : ℝ) (96485229849/200000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint6 : (-9322843/3125000 : ℝ)<Real.log (81/1600 : ℝ) ∧ Real.log (81/1600 : ℝ)<(-11933239/4000000 : ℝ) := by
  have h:=logScaled6
  have h2:=Chapter06Figures.log2
  have hid : Real.log (81/1600 : ℝ)=Real.log (81/50 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (81/50 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo6 : (5476357/6250000 : ℝ)<Real.exp (-1651767/12500000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-1651767/12500000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi6 : Real.exp (-6607067/50000000 : ℝ)<(17524343/20000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-6607067/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density6 : (14629/1250 : ℝ)<Chapter06Figures.density (81/1600 : ℝ) ∧ Chapter06Figures.density (81/1600 : ℝ)<(117033/10000 : ℝ) := by
  have h:=logPoint6
  have hs1 : (-1213239/4000000 : ℝ)^2≤(Real.log (81/1600 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-1213239/4000000 : ℝ)) (by linarith : 0≤-(Real.log (81/1600 : ℝ)+268/100))).mpr (by linarith : -(-1213239/4000000 : ℝ)≤-(Real.log (81/1600 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (81/1600 : ℝ)+268/100)^2≤(-947843/3125000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (81/1600 : ℝ)+268/100)) (by norm_num : 0≤-(-947843/3125000 : ℝ))).mpr (by linarith : -(Real.log (81/1600 : ℝ)+268/100)≤-(-947843/3125000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-1651767/12500000 : ℝ)<(-(Real.log (81/1600 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (81/1600 : ℝ)+268/100)^2/(2*(59/100)^2))<(-6607067/50000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo6 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi6
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(81/1600 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled7 : (548121408509/1000000000000 : ℝ)<Real.log (173/100 : ℝ) ∧ Real.log (173/100 : ℝ)<(54812140851/100000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (73/273 : ℝ) (548121408509/1000000000000 : ℝ) (54812140851/100000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint7 : (-5835229/2000000 : ℝ)<Real.log (173/3200 : ℝ) ∧ Real.log (173/3200 : ℝ)<(-291761449/100000000 : ℝ) := by
  have h:=logScaled7
  have h2:=Chapter06Figures.log2
  have hid : Real.log (173/3200 : ℝ)=Real.log (173/100 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (173/100 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo7 : (92210301/100000000 : ℝ)<Real.exp (-8109833/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-8109833/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi7 : Real.exp (-8109831/100000000 : ℝ)<(720393/781250 : ℝ) := by
  have h:=Real.exp_bound (x:=(-8109831/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density7 : (115329/10000 : ℝ)<Chapter06Figures.density (173/3200 : ℝ) ∧ Chapter06Figures.density (173/3200 : ℝ)<(11533/1000 : ℝ) := by
  have h:=logPoint7
  have hs1 : (-23761449/100000000 : ℝ)^2≤(Real.log (173/3200 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-23761449/100000000 : ℝ)) (by linarith : 0≤-(Real.log (173/3200 : ℝ)+268/100))).mpr (by linarith : -(-23761449/100000000 : ℝ)≤-(Real.log (173/3200 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (173/3200 : ℝ)+268/100)^2≤(-475229/2000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (173/3200 : ℝ)+268/100)) (by norm_num : 0≤-(-475229/2000000 : ℝ))).mpr (by linarith : -(Real.log (173/3200 : ℝ)+268/100)≤-(-475229/2000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-8109833/100000000 : ℝ)<(-(Real.log (173/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (173/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-8109831/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo7 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi7
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(173/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled8 : (30488278581/50000000000 : ℝ)<Real.log (46/25 : ℝ) ∧ Real.log (46/25 : ℝ)<(609765571621/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (21/71 : ℝ) (30488278581/50000000000 : ℝ) (609765571621/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint8 : (-142798517/50000000 : ℝ)<Real.log (23/400 : ℝ) ∧ Real.log (23/400 : ℝ)<(-285597033/100000000 : ℝ) := by
  have h:=logScaled8
  have h2:=Chapter06Figures.log2
  have hid : Real.log (23/400 : ℝ)=Real.log (46/25 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (46/25 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo8 : (95649667/100000000 : ℝ)<Real.exp (-4447797/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-4447797/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi8 : Real.exp (-1111949/25000000 : ℝ)<(95649669/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-1111949/25000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density8 : (112479/10000 : ℝ)<Chapter06Figures.density (23/400 : ℝ) ∧ Chapter06Figures.density (23/400 : ℝ)<(1406/125 : ℝ) := by
  have h:=logPoint8
  have hs1 : (-17597033/100000000 : ℝ)^2≤(Real.log (23/400 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-17597033/100000000 : ℝ)) (by linarith : 0≤-(Real.log (23/400 : ℝ)+268/100))).mpr (by linarith : -(-17597033/100000000 : ℝ)≤-(Real.log (23/400 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (23/400 : ℝ)+268/100)^2≤(-8798517/50000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (23/400 : ℝ)+268/100)) (by norm_num : 0≤-(-8798517/50000000 : ℝ))).mpr (by linarith : -(Real.log (23/400 : ℝ)+268/100)≤-(-8798517/50000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-4447797/100000000 : ℝ)<(-(Real.log (23/400 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (23/400 : ℝ)+268/100)^2/(2*(59/100)^2))<(-1111949/25000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo8 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi8
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(23/400 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled9 : (26713174903/40000000000 : ℝ)<Real.log (39/20 : ℝ) ∧ Real.log (39/20 : ℝ)<(20869667893/31250000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (19/59 : ℝ) (26713174903/40000000000 : ℝ) (20869667893/31250000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint9 : (-139895327/50000000 : ℝ)<Real.log (39/640 : ℝ) ∧ Real.log (39/640 : ℝ)<(-279790653/100000000 : ℝ) := by
  have h:=logScaled9
  have h2:=Chapter06Figures.log2
  have hid : Real.log (39/640 : ℝ)=Real.log (39/20 : ℝ)-5*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (39/20 : ℝ)≠0) (by norm_num : (2:ℝ)^5≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo9 : (9802297/10000000 : ℝ)<Real.exp (-998417/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-998417/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi9 : Real.exp (-62401/3125000 : ℝ)<(98022973/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-62401/3125000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density9 : (6798/625 : ℝ)<Chapter06Figures.density (39/640 : ℝ) ∧ Chapter06Figures.density (39/640 : ℝ)<(108769/10000 : ℝ) := by
  have h:=logPoint9
  have hs1 : (-11790653/100000000 : ℝ)^2≤(Real.log (39/640 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-11790653/100000000 : ℝ)) (by linarith : 0≤-(Real.log (39/640 : ℝ)+268/100))).mpr (by linarith : -(-11790653/100000000 : ℝ)≤-(Real.log (39/640 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (39/640 : ℝ)+268/100)^2≤(-5895327/50000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (39/640 : ℝ)+268/100)) (by norm_num : 0≤-(-5895327/50000000 : ℝ))).mpr (by linarith : -(Real.log (39/640 : ℝ)+268/100)≤-(-5895327/50000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-998417/50000000 : ℝ)<(-(Real.log (39/640 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (39/640 : ℝ)+268/100)^2/(2*(59/100)^2))<(-62401/3125000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo9 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi9
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(39/640 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled10 : (29558802241/1000000000000 : ℝ)<Real.log (103/100 : ℝ) ∧ Real.log (103/100 : ℝ)<(14779401121/500000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (3/203 : ℝ) (29558802241/1000000000000 : ℝ) (14779401121/500000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint10 : (-17143937/6250000 : ℝ)<Real.log (103/1600 : ℝ) ∧ Real.log (103/1600 : ℝ)<(-274302991/100000000 : ℝ) := by
  have h:=logScaled10
  have h2:=Chapter06Figures.log2
  have hid : Real.log (103/1600 : ℝ)=Real.log (103/100 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (103/100 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo10 : (24857747/25000000 : ℝ)<Real.exp (-570637/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-570637/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi10 : Real.exp (-142659/25000000 : ℝ)<(9943099/10000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-142659/25000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density10 : (52219/5000 : ℝ)<Chapter06Figures.density (103/1600 : ℝ) ∧ Chapter06Figures.density (103/1600 : ℝ)<(104439/10000 : ℝ) := by
  have h:=logPoint10
  have hs1 : (-6302991/100000000 : ℝ)^2≤(Real.log (103/1600 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-6302991/100000000 : ℝ)) (by linarith : 0≤-(Real.log (103/1600 : ℝ)+268/100))).mpr (by linarith : -(-6302991/100000000 : ℝ)≤-(Real.log (103/1600 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (103/1600 : ℝ)+268/100)^2≤(-393937/6250000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (103/1600 : ℝ)+268/100)) (by norm_num : 0≤-(-393937/6250000 : ℝ))).mpr (by linarith : -(Real.log (103/1600 : ℝ)+268/100)≤-(-393937/6250000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-570637/100000000 : ℝ)<(-(Real.log (103/1600 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (103/1600 : ℝ)+268/100)^2/(2*(59/100)^2))<(-142659/25000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo10 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi10
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(103/1600 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled11 : (5098749187/62500000000 : ℝ)<Real.log (217/200 : ℝ) ∧ Real.log (217/200 : ℝ)<(81579986993/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (17/417 : ℝ) (5098749187/62500000000 : ℝ) (81579986993/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint11 : (-134550437/50000000 : ℝ)<Real.log (217/3200 : ℝ) ∧ Real.log (217/3200 : ℝ)<(-269100873/100000000 : ℝ) := by
  have h:=logScaled11
  have h2:=Chapter06Figures.log2
  have hid : Real.log (217/3200 : ℝ)=Real.log (217/200 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (217/200 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo11 : (99982593/100000000 : ℝ)<Real.exp (-68/390625 : ℝ) := by
  have h:=Real.exp_bound (x:=(-68/390625 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi11 : Real.exp (-17407/100000000 : ℝ)<(19996519/20000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-17407/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density11 : (49847/5000 : ℝ)<Chapter06Figures.density (217/3200 : ℝ) ∧ Chapter06Figures.density (217/3200 : ℝ)<(19939/2000 : ℝ) := by
  have h:=logPoint11
  have hs1 : (-1100873/100000000 : ℝ)^2≤(Real.log (217/3200 : ℝ)+268/100)^2 := by
    have h:=(sq_le_sq₀ (by norm_num : 0≤-(-1100873/100000000 : ℝ)) (by linarith : 0≤-(Real.log (217/3200 : ℝ)+268/100))).mpr (by linarith : -(-1100873/100000000 : ℝ)≤-(Real.log (217/3200 : ℝ)+268/100))
    simpa only [neg_sq] using h
  have hs2 : (Real.log (217/3200 : ℝ)+268/100)^2≤(-550437/50000000 : ℝ)^2 := by
    have h:=(sq_le_sq₀ (by linarith : 0≤-(Real.log (217/3200 : ℝ)+268/100)) (by norm_num : 0≤-(-550437/50000000 : ℝ))).mpr (by linarith : -(Real.log (217/3200 : ℝ)+268/100)≤-(-550437/50000000 : ℝ))
    simpa only [neg_sq] using h
  have helo : (-68/390625 : ℝ)<(-(Real.log (217/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (217/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-17407/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo11 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi11
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(217/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled12 : (65514131203/500000000000 : ℝ)<Real.log (57/50 : ℝ) ∧ Real.log (57/50 : ℝ)<(131028262407/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (7/107 : ℝ) (65514131203/500000000000 : ℝ) (131028262407/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint12 : (-132078023/50000000 : ℝ)<Real.log (57/800 : ℝ) ∧ Real.log (57/800 : ℝ)<(-52831209/20000000 : ℝ) := by
  have h:=logScaled12
  have h2:=Chapter06Figures.log2
  have hid : Real.log (57/800 : ℝ)=Real.log (57/50 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (57/50 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo12 : (99787987/100000000 : ℝ)<Real.exp (-106119/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-106119/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi12 : Real.exp (-212237/100000000 : ℝ)<(99787989/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-212237/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density12 : (947/100 : ℝ)<Chapter06Figures.density (57/800 : ℝ) ∧ Chapter06Figures.density (57/800 : ℝ)<(94701/10000 : ℝ) := by
  have h:=logPoint12
  have hs1 : (1921977/50000000 : ℝ)^2≤(Real.log (57/800 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (57/800 : ℝ)+268/100)^2≤(768791/20000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-106119/50000000 : ℝ)<(-(Real.log (57/800 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (57/800 : ℝ)+268/100)^2/(2*(59/100)^2))<(-212237/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo12 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi12
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(57/800 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled13 : (178146185383/1000000000000 : ℝ)<Real.log (239/200 : ℝ) ∧ Real.log (239/200 : ℝ)<(22268273173/125000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (39/439 : ℝ) (178146185383/1000000000000 : ℝ) (22268273173/125000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint13 : (-129722127/50000000 : ℝ)<Real.log (239/3200 : ℝ) ∧ Real.log (239/3200 : ℝ)<(-259444253/100000000 : ℝ) := by
  have h:=logScaled13
  have h2:=Chapter06Figures.log2
  have hid : Real.log (239/3200 : ℝ)=Real.log (239/200 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (239/200 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo13 : (49477037/50000000 : ℝ)<Real.exp (-525717/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-525717/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi13 : Real.exp (-1051433/100000000 : ℝ)<(24738519/25000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-1051433/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density13 : (44793/5000 : ℝ)<Chapter06Figures.density (239/3200 : ℝ) ∧ Chapter06Figures.density (239/3200 : ℝ)<(89587/10000 : ℝ) := by
  have h:=logPoint13
  have hs1 : (4277873/50000000 : ℝ)^2≤(Real.log (239/3200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (239/3200 : ℝ)+268/100)^2≤(8555747/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-525717/50000000 : ℝ)<(-(Real.log (239/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (239/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-1051433/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo13 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi13
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(239/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled14 : (111571775657/500000000000 : ℝ)<Real.log (5/4 : ℝ) ∧ Real.log (5/4 : ℝ)<(44628710263/200000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (1/9 : ℝ) (111571775657/500000000000 : ℝ) (44628710263/200000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint14 : (-127472259/50000000 : ℝ)<Real.log (5/64 : ℝ) ∧ Real.log (5/64 : ℝ)<(-254944517/100000000 : ℝ) := by
  have h:=logScaled14
  have h2:=Chapter06Figures.log2
  have hid : Real.log (5/64 : ℝ)=Real.log (5/4 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (5/4 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo14 : (97581497/100000000 : ℝ)<Real.exp (-2448229/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-2448229/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi14 : Real.exp (-2448227/100000000 : ℝ)<(97581499/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-2448227/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density14 : (10557/1250 : ℝ)<Chapter06Figures.density (5/64 : ℝ) ∧ Chapter06Figures.density (5/64 : ℝ)<(84457/10000 : ℝ) := by
  have h:=logPoint14
  have hs1 : (6527741/50000000 : ℝ)^2≤(Real.log (5/64 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (5/64 : ℝ)+268/100)^2≤(13055483/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-2448229/100000000 : ℝ)<(-(Real.log (5/64 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (5/64 : ℝ)+268/100)^2/(2*(59/100)^2))<(-2448227/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo14 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi14
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(5/64 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled15 : (133101520387/500000000000 : ℝ)<Real.log (261/200 : ℝ) ∧ Real.log (261/200 : ℝ)<(10648121631/40000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (61/461 : ℝ) (133101520387/500000000000 : ℝ) (10648121631/40000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint15 : (-250638569/100000000 : ℝ)<Real.log (261/3200 : ℝ) ∧ Real.log (261/3200 : ℝ)<(-31329821/12500000 : ℝ) := by
  have h:=logScaled15
  have h2:=Chapter06Figures.log2
  have hid : Real.log (261/3200 : ℝ)=Real.log (261/200 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (261/200 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo15 : (9576289/10000000 : ℝ)<Real.exp (-2164747/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-2164747/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi15 : Real.exp (-1082373/25000000 : ℝ)<(95762893/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-1082373/25000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density15 : (79389/10000 : ℝ)<Chapter06Figures.density (261/3200 : ℝ) ∧ Chapter06Figures.density (261/3200 : ℝ)<(7939/1000 : ℝ) := by
  have h:=logPoint15
  have hs1 : (17361431/100000000 : ℝ)^2≤(Real.log (261/3200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (261/3200 : ℝ)+268/100)^2≤(2170179/12500000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-2164747/50000000 : ℝ)<(-(Real.log (261/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (261/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-1082373/25000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo15 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi15
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(261/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled16 : (307484699747/1000000000000 : ℝ)<Real.log (34/25 : ℝ) ∧ Real.log (34/25 : ℝ)<(76871174937/250000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (9/59 : ℝ) (307484699747/1000000000000 : ℝ) (76871174937/250000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint16 : (-246510403/100000000 : ℝ)<Real.log (17/200 : ℝ) ∧ Real.log (17/200 : ℝ)<(-123255201/50000000 : ℝ) := by
  have h:=logScaled16
  have h2:=Chapter06Figures.log2
  have hid : Real.log (17/200 : ℝ)=Real.log (34/25 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (34/25 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo16 : (93582019/100000000 : ℝ)<Real.exp (-829149/12500000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-829149/12500000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi16 : Real.exp (-6633191/100000000 : ℝ)<(93582021/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-6633191/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density16 : (18611/2500 : ℝ)<Chapter06Figures.density (17/200 : ℝ) ∧ Chapter06Figures.density (17/200 : ℝ)<(14889/2000 : ℝ) := by
  have h:=logPoint16
  have hs1 : (21489597/100000000 : ℝ)^2≤(Real.log (17/200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (17/200 : ℝ)+268/100)^2≤(10744799/50000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-829149/12500000 : ℝ)<(-(Real.log (17/200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (17/200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-6633191/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo16 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi16
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(17/200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled17 : (69425906219/200000000000 : ℝ)<Real.log (283/200 : ℝ) ∧ Real.log (283/200 : ℝ)<(43391191387/125000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (83/483 : ℝ) (69425906219/200000000000 : ℝ) (43391191387/125000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint17 : (-189489/78125 : ℝ)<Real.log (283/3200 : ℝ) ∧ Real.log (283/3200 : ℝ)<(-242545919/100000000 : ℝ) := by
  have h:=logScaled17
  have h2:=Chapter06Figures.log2
  have hid : Real.log (283/3200 : ℝ)=Real.log (283/200 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (283/200 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo17 : (18222707/20000000 : ℝ)<Real.exp (-9306381/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-9306381/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi17 : Real.exp (-465319/5000000 : ℝ)<(91113537/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-465319/5000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density17 : (69663/10000 : ℝ)<Chapter06Figures.density (283/3200 : ℝ) ∧ Chapter06Figures.density (283/3200 : ℝ)<(4354/625 : ℝ) := by
  have h:=logPoint17
  have hs1 : (19886/78125 : ℝ)^2≤(Real.log (283/3200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (283/3200 : ℝ)+268/100)^2≤(25454081/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-9306381/100000000 : ℝ)<(-(Real.log (283/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (283/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-465319/5000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo17 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi17
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(283/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled18 : (38526240079/100000000000 : ℝ)<Real.log (147/100 : ℝ) ∧ Real.log (147/100 : ℝ)<(385262400791/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (47/247 : ℝ) (38526240079/100000000000 : ℝ) (385262400791/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint18 : (-238732633/100000000 : ℝ)<Real.log (147/1600 : ℝ) ∧ Real.log (147/1600 : ℝ)<(-29841579/12500000 : ℝ) := by
  have h:=logScaled18
  have h2:=Chapter06Figures.log2
  have hid : Real.log (147/1600 : ℝ)=Real.log (147/100 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (147/100 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo18 : (44211577/50000000 : ℝ)<Real.exp (-768977/6250000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-768977/6250000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi18 : Real.exp (-1230363/10000000 : ℝ)<(88423157/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-1230363/10000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density18 : (16269/2500 : ℝ)<Chapter06Figures.density (147/1600 : ℝ) ∧ Chapter06Figures.density (147/1600 : ℝ)<(65077/10000 : ℝ) := by
  have h:=logPoint18
  have hs1 : (29267367/100000000 : ℝ)^2≤(Real.log (147/1600 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (147/1600 : ℝ)+268/100)^2≤(3658421/12500000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-768977/6250000 : ℝ)<(-(Real.log (147/1600 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (147/1600 : ℝ)+268/100)^2/(2*(59/100)^2))<(-1230363/10000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo18 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi18
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(147/1600 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled19 : (421994410059/1000000000000 : ℝ)<Real.log (61/40 : ℝ) ∧ Real.log (61/40 : ℝ)<(21099720503/50000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (21/101 : ℝ) (421994410059/1000000000000 : ℝ) (21099720503/50000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint19 : (-29382429/12500000 : ℝ)<Real.log (61/640 : ℝ) ∧ Real.log (61/640 : ℝ)<(-235059431/100000000 : ℝ) := by
  have h:=logScaled19
  have h2:=Chapter06Figures.log2
  have hid : Real.log (61/640 : ℝ)=Real.log (61/40 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (61/40 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo19 : (85568097/100000000 : ℝ)<Real.exp (-15585767/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-15585767/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi19 : Real.exp (-3117153/20000000 : ℝ)<(85568099/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-3117153/20000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density19 : (3794/625 : ℝ)<Chapter06Figures.density (61/640 : ℝ) ∧ Chapter06Figures.density (61/640 : ℝ)<(12141/2000 : ℝ) := by
  have h:=logPoint19
  have hs1 : (4117571/12500000 : ℝ)^2≤(Real.log (61/640 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (61/640 : ℝ)+268/100)^2≤(32940569/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-15585767/100000000 : ℝ)<(-(Real.log (61/640 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (61/640 : ℝ)+268/100)^2/(2*(59/100)^2))<(-3117153/20000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo19 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi19
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(61/640 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled20 : (228712423519/500000000000 : ℝ)<Real.log (79/50 : ℝ) ∧ Real.log (79/50 : ℝ)<(457424847039/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (29/129 : ℝ) (228712423519/500000000000 : ℝ) (457424847039/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint20 : (-57879097/25000000 : ℝ)<Real.log (79/800 : ℝ) ∧ Real.log (79/800 : ℝ)<(-231516387/100000000 : ℝ) := by
  have h:=logScaled20
  have h2:=Chapter06Figures.log2
  have hid : Real.log (79/800 : ℝ)=Real.log (79/50 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (79/50 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo20 : (8259769/10000000 : ℝ)<Real.exp (-9559423/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-9559423/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi20 : Real.exp (-4779711/25000000 : ℝ)<(82597693/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-4779711/25000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density20 : (56557/10000 : ℝ)<Chapter06Figures.density (79/800 : ℝ) ∧ Chapter06Figures.density (79/800 : ℝ)<(28279/5000 : ℝ) := by
  have h:=logPoint20
  have hs1 : (9120903/25000000 : ℝ)^2≤(Real.log (79/800 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (79/800 : ℝ)+268/100)^2≤(36483613/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-9559423/50000000 : ℝ)<(-(Real.log (79/800 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (79/800 : ℝ)+268/100)^2/(2*(59/100)^2))<(-4779711/25000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo20 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi20
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(79/800 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled21 : (491642804349/1000000000000 : ℝ)<Real.log (327/200 : ℝ) ∧ Real.log (327/200 : ℝ)<(9832856087/20000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (127/527 : ℝ) (491642804349/1000000000000 : ℝ) (9832856087/20000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint21 : (-1781989/781250 : ℝ)<Real.log (327/3200 : ℝ) ∧ Real.log (327/3200 : ℝ)<(-228094591/100000000 : ℝ) := by
  have h:=logScaled21
  have h2:=Chapter06Figures.log2
  have hid : Real.log (327/3200 : ℝ)=Real.log (327/200 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (327/200 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo21 : (39777031/50000000 : ℝ)<Real.exp (-22873337/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-22873337/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi21 : Real.exp (-4574667/20000000 : ℝ)<(4972129/6250000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-4574667/20000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density21 : (658/125 : ℝ)<Chapter06Figures.density (327/3200 : ℝ) ∧ Chapter06Figures.density (327/3200 : ℝ)<(52641/10000 : ℝ) := by
  have h:=logPoint21
  have hs1 : (311761/781250 : ℝ)^2≤(Real.log (327/3200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (327/3200 : ℝ)+268/100)^2≤(39905409/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-22873337/100000000 : ℝ)<(-(Real.log (327/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (327/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-4574667/20000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo21 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi21
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(327/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled22 : (262364264467/500000000000 : ℝ)<Real.log (169/100 : ℝ) ∧ Real.log (169/100 : ℝ)<(104945705787/200000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (69/269 : ℝ) (262364264467/500000000000 : ℝ) (104945705787/200000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint22 : (-11239301/5000000 : ℝ)<Real.log (169/1600 : ℝ) ∧ Real.log (169/1600 : ℝ)<(-224786019/100000000 : ℝ) := by
  have h:=logScaled22
  have h2:=Chapter06Figures.log2
  have hid : Real.log (169/1600 : ℝ)=Real.log (169/100 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (169/100 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo22 : (76472847/100000000 : ℝ)<Real.exp (-6705861/25000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-6705861/25000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi22 : Real.exp (-13411721/50000000 : ℝ)<(1529457/2000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-13411721/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density22 : (9791/2000 : ℝ)<Chapter06Figures.density (169/1600 : ℝ) ∧ Chapter06Figures.density (169/1600 : ℝ)<(12239/2500 : ℝ) := by
  have h:=logPoint22
  have hs1 : (2160699/5000000 : ℝ)^2≤(Real.log (169/1600 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (169/1600 : ℝ)+268/100)^2≤(43213981/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-6705861/25000000 : ℝ)<(-(Real.log (169/1600 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (169/1600 : ℝ)+268/100)^2/(2*(59/100)^2))<(-13411721/50000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo22 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi22
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(169/1600 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled23 : (278377277827/500000000000 : ℝ)<Real.log (349/200 : ℝ) ∧ Real.log (349/200 : ℝ)<(111350911131/200000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (149/549 : ℝ) (278377277827/500000000000 : ℝ) (111350911131/200000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint23 : (-221583417/100000000 : ℝ)<Real.log (349/3200 : ℝ) ∧ Real.log (349/3200 : ℝ)<(-27697927/12500000 : ℝ) := by
  have h:=logScaled23
  have h2:=Chapter06Figures.log2
  have hid : Real.log (349/3200 : ℝ)=Real.log (349/200 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (349/200 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo23 : (73383903/100000000 : ℝ)<Real.exp (-30946557/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-30946557/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi23 : Real.exp (-6189311/20000000 : ℝ)<(36691953/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-6189311/20000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density23 : (45497/10000 : ℝ)<Chapter06Figures.density (349/3200 : ℝ) ∧ Chapter06Figures.density (349/3200 : ℝ)<(22749/5000 : ℝ) := by
  have h:=logPoint23
  have hs1 : (46416583/100000000 : ℝ)^2≤(Real.log (349/3200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (349/3200 : ℝ)+268/100)^2≤(5802073/12500000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-30946557/100000000 : ℝ)<(-(Real.log (349/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (349/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-6189311/20000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo23 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi23
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(349/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled24 : (293893332451/500000000000 : ℝ)<Real.log (9/5 : ℝ) ∧ Real.log (9/5 : ℝ)<(587786664903/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (2/7 : ℝ) (293893332451/500000000000 : ℝ) (587786664903/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint24 : (-109240103/50000000 : ℝ)<Real.log (9/80 : ℝ) ∧ Real.log (9/80 : ℝ)<(-43696041/20000000 : ℝ) := by
  have h:=logScaled24
  have h2:=Chapter06Figures.log2
  have hid : Real.log (9/80 : ℝ)=Real.log (9/5 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (9/5 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo24 : (70311991/100000000 : ℝ)<Real.exp (-35222783/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-35222783/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi24 : Real.exp (-1761139/5000000 : ℝ)<(35155997/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-1761139/5000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density24 : (2113/500 : ℝ)<Chapter06Figures.density (9/80 : ℝ) ∧ Chapter06Figures.density (9/80 : ℝ)<(42261/10000 : ℝ) := by
  have h:=logPoint24
  have hs1 : (24759897/50000000 : ℝ)^2≤(Real.log (9/80 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (9/80 : ℝ)+268/100)^2≤(9903959/20000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-35222783/100000000 : ℝ)<(-(Real.log (9/80 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (9/80 : ℝ)+268/100)^2/(2*(59/100)^2))<(-1761139/5000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo24 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi24
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(9/80 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled25 : (617884696059/1000000000000 : ℝ)<Real.log (371/200 : ℝ) ∧ Real.log (371/200 : ℝ)<(30894234803/50000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (171/571 : ℝ) (617884696059/1000000000000 : ℝ) (30894234803/50000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint25 : (-215470403/100000000 : ℝ)<Real.log (371/3200 : ℝ) ∧ Real.log (371/3200 : ℝ)<(-107735201/50000000 : ℝ) := by
  have h:=logScaled25
  have h2:=Chapter06Figures.log2
  have hid : Real.log (371/3200 : ℝ)=Real.log (371/200 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (371/200 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo25 : (2102419/3125000 : ℝ)<Real.exp (-39634569/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-39634569/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi25 : Real.exp (-39634567/100000000 : ℝ)<(6727741/10000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-39634567/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density25 : (39237/10000 : ℝ)<Chapter06Figures.density (371/3200 : ℝ) ∧ Chapter06Figures.density (371/3200 : ℝ)<(19619/5000 : ℝ) := by
  have h:=logPoint25
  have hs1 : (52529597/100000000 : ℝ)^2≤(Real.log (371/3200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (371/3200 : ℝ)+268/100)^2≤(26264799/50000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-39634569/100000000 : ℝ)<(-(Real.log (371/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (371/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-39634567/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo25 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi25
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(371/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled26 : (323551621029/500000000000 : ℝ)<Real.log (191/100 : ℝ) ∧ Real.log (191/100 : ℝ)<(647103242059/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (91/291 : ℝ) (323551621029/500000000000 : ℝ) (647103242059/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint26 : (-212548549/100000000 : ℝ)<Real.log (191/1600 : ℝ) ∧ Real.log (191/1600 : ℝ)<(-53137137/25000000 : ℝ) := by
  have h:=logScaled26
  have h2:=Chapter06Figures.log2
  have hid : Real.log (191/1600 : ℝ)=Real.log (191/100 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (191/100 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo26 : (32148287/50000000 : ℝ)<Real.exp (-44166383/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-44166383/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi26 : Real.exp (-2208319/5000000 : ℝ)<(64296577/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-2208319/5000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density26 : (36419/10000 : ℝ)<Chapter06Figures.density (191/1600 : ℝ) ∧ Chapter06Figures.density (191/1600 : ℝ)<(1821/500 : ℝ) := by
  have h:=logPoint26
  have hs1 : (55451451/100000000 : ℝ)^2≤(Real.log (191/1600 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (191/1600 : ℝ)+268/100)^2≤(13862863/25000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-44166383/100000000 : ℝ)<(-(Real.log (191/1600 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (191/1600 : ℝ)+268/100)^2/(2*(59/100)^2))<(-2208319/5000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo26 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi26
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(191/1600 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled27 : (675492245321/1000000000000 : ℝ)<Real.log (393/200 : ℝ) ∧ Real.log (393/200 : ℝ)<(337746122661/500000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (193/593 : ℝ) (675492245321/1000000000000 : ℝ) (337746122661/500000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint27 : (-13106853/6250000 : ℝ)<Real.log (393/3200 : ℝ) ∧ Real.log (393/3200 : ℝ)<(-209709647/100000000 : ℝ) := by
  have h:=logScaled27
  have h2:=Chapter06Figures.log2
  have hid : Real.log (393/3200 : ℝ)=Real.log (393/200 : ℝ)-4*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (393/200 : ℝ)≠0) (by norm_num : (2:ℝ)^4≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo27 : (383641/625000 : ℝ)<Real.exp (-48804443/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-48804443/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi27 : Real.exp (-1220111/2500000 : ℝ)<(30691281/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-1220111/2500000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density27 : (6759/2000 : ℝ)<Chapter06Figures.density (393/3200 : ℝ) ∧ Chapter06Figures.density (393/3200 : ℝ)<(8449/2500 : ℝ) := by
  have h:=logPoint27
  have hs1 : (3643147/6250000 : ℝ)^2≤(Real.log (393/3200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (393/3200 : ℝ)+268/100)^2≤(58290353/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-48804443/100000000 : ℝ)<(-(Real.log (393/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (393/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-1220111/2500000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo27 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi27
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(393/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled28 : (9950330853/1000000000000 : ℝ)<Real.log (101/100 : ℝ) ∧ Real.log (101/100 : ℝ)<(4975165427/500000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (1/201 : ℝ) (9950330853/1000000000000 : ℝ) (4975165427/500000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint28 : (-103474561/50000000 : ℝ)<Real.log (101/800 : ℝ) ∧ Real.log (101/800 : ℝ)<(-206949121/100000000 : ℝ) := by
  have h:=logScaled28
  have h2:=Chapter06Figures.log2
  have hid : Real.log (101/800 : ℝ)=Real.log (101/100 : ℝ)-3*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (101/100 : ℝ)≠0) (by norm_num : (2:ℝ)^3≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo28 : (29272783/50000000 : ℝ)<Real.exp (-26768241/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-26768241/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi28 : Real.exp (-53536479/100000000 : ℝ)<(58545569/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-53536479/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density28 : (7839/2500 : ℝ)<Chapter06Figures.density (101/800 : ℝ) ∧ Chapter06Figures.density (101/800 : ℝ)<(31357/10000 : ℝ) := by
  have h:=logPoint28
  have hs1 : (30525439/50000000 : ℝ)^2≤(Real.log (101/800 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (101/800 : ℝ)+268/100)^2≤(61050879/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-26768241/50000000 : ℝ)<(-(Real.log (101/800 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (101/800 : ℝ)+268/100)^2/(2*(59/100)^2))<(-53536479/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo28 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi28
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(101/800 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled29 : (18406986561/500000000000 : ℝ)<Real.log (83/80 : ℝ) ∧ Real.log (83/80 : ℝ)<(36813973123/1000000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (3/163 : ℝ) (18406986561/500000000000 : ℝ) (36813973123/1000000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint29 : (-204262757/100000000 : ℝ)<Real.log (83/640 : ℝ) ∧ Real.log (83/640 : ℝ)<(-51065689/25000000 : ℝ) := by
  have h:=logScaled29
  have h2:=Chapter06Figures.log2
  have hid : Real.log (83/640 : ℝ)=Real.log (83/80 : ℝ)-3*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (83/80 : ℝ)≠0) (by norm_num : (2:ℝ)^3≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo29 : (27896669/50000000 : ℝ)<Real.exp (-5835157/10000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-5835157/10000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi29 : Real.exp (-58351567/100000000 : ℝ)<(55793341/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-58351567/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density29 : (29089/10000 : ℝ)<Chapter06Figures.density (83/640 : ℝ) ∧ Chapter06Figures.density (83/640 : ℝ)<(2909/1000 : ℝ) := by
  have h:=logPoint29
  have hs1 : (63737243/100000000 : ℝ)^2≤(Real.log (83/640 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (83/640 : ℝ)+268/100)^2≤(15934311/25000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-5835157/10000000 : ℝ)<(-(Real.log (83/640 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (83/640 : ℝ)+268/100)^2/(2*(59/100)^2))<(-58351567/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo29 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi29
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(83/640 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled30 : (62974799161/1000000000000 : ℝ)<Real.log (213/200 : ℝ) ∧ Real.log (213/200 : ℝ)<(31487399581/500000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (13/413 : ℝ) (62974799161/1000000000000 : ℝ) (31487399581/500000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint30 : (-8065867/4000000 : ℝ)<Real.log (213/1600 : ℝ) ∧ Real.log (213/1600 : ℝ)<(-100823337/50000000 : ℝ) := by
  have h:=logScaled30
  have h2:=Chapter06Figures.log2
  have hid : Real.log (213/1600 : ℝ)=Real.log (213/200 : ℝ)-3*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (213/200 : ℝ)≠0) (by norm_num : (2:ℝ)^3≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo30 : (13282887/25000000 : ℝ)<Real.exp (-6323993/10000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-6323993/10000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi30 : Real.exp (-63239927/100000000 : ℝ)<(53131551/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-63239927/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density30 : (13493/5000 : ℝ)<Chapter06Figures.density (213/1600 : ℝ) ∧ Chapter06Figures.density (213/1600 : ℝ)<(26987/10000 : ℝ) := by
  have h:=logPoint30
  have hs1 : (2654133/4000000 : ℝ)^2≤(Real.log (213/1600 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (213/1600 : ℝ)+268/100)^2≤(33176663/50000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-6323993/10000000 : ℝ)<(-(Real.log (213/1600 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (213/1600 : ℝ)+268/100)^2/(2*(59/100)^2))<(-63239927/100000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo30 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi30
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(213/1600 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled31 : (88468647987/1000000000000 : ℝ)<Real.log (437/400 : ℝ) ∧ Real.log (437/400 : ℝ)<(22117161997/250000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (37/837 : ℝ) (88468647987/1000000000000 : ℝ) (22117161997/250000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint31 : (-19909729/10000000 : ℝ)<Real.log (437/3200 : ℝ) ∧ Real.log (437/3200 : ℝ)<(-199097289/100000000 : ℝ) := by
  have h:=logScaled31
  have h2:=Chapter06Figures.log2
  have hid : Real.log (437/3200 : ℝ)=Real.log (437/400 : ℝ)-3*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (437/400 : ℝ)≠0) (by norm_num : (2:ℝ)^3≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo31 : (50564111/100000000 : ℝ)<Real.exp (-68192813/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-68192813/100000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi31 : Real.exp (-6819281/10000000 : ℝ)<(50564113/100000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-6819281/10000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density31 : (6259/2500 : ℝ)<Chapter06Figures.density (437/3200 : ℝ) ∧ Chapter06Figures.density (437/3200 : ℝ)<(25037/10000 : ℝ) := by
  have h:=logPoint31
  have hs1 : (6890271/10000000 : ℝ)^2≤(Real.log (437/3200 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (437/3200 : ℝ)+268/100)^2≤(68902711/100000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-68192813/100000000 : ℝ)<(-(Real.log (437/3200 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (437/3200 : ℝ)+268/100)^2/(2*(59/100)^2))<(-6819281/10000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo31 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi31
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(437/3200 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem logScaled32 : (113328685307/1000000000000 : ℝ)<Real.log (28/25 : ℝ) ∧ Real.log (28/25 : ℝ)<(28332171327/250000000000 : ℝ) := by
  have h:=Chapter06Figures.logEnclosure (3/53 : ℝ) (113328685307/1000000000000 : ℝ) (28332171327/250000000000 : ℝ) 16 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])
  norm_num at h ⊢
  exact h
theorem logPoint32 : (-98305643/50000000 : ℝ)<Real.log (7/50 : ℝ) ∧ Real.log (7/50 : ℝ)<(-39322257/20000000 : ℝ) := by
  have h:=logScaled32
  have h2:=Chapter06Figures.log2
  have hid : Real.log (7/50 : ℝ)=Real.log (28/25 : ℝ)-3*Real.log 2 := by
    have hh:=Real.log_div (by norm_num : (28/25 : ℝ)≠0) (by norm_num : (2:ℝ)^3≠0)
    rw [Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  rw [hid]
  constructor <;> linarith

theorem exp_lo32 : (12023369/25000000 : ℝ)<Real.exp (-14640473/20000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-14640473/20000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem exp_hi32 : Real.exp (-36601181/50000000 : ℝ)<(24046739/50000000 : ℝ) := by
  have h:=Real.exp_bound (x:=(-36601181/50000000 : ℝ)) (by norm_num) (n:=14) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rcases abs_le.mp h with ⟨hl,hu⟩
  linarith

theorem density32 : (5807/2500 : ℝ)<Chapter06Figures.density (7/50 : ℝ) ∧ Chapter06Figures.density (7/50 : ℝ)<(23229/10000 : ℝ) := by
  have h:=logPoint32
  have hs1 : (35694357/50000000 : ℝ)^2≤(Real.log (7/50 : ℝ)+268/100)^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hs2 : (Real.log (7/50 : ℝ)+268/100)^2≤(14277743/20000000 : ℝ)^2 := (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have helo : (-14640473/20000000 : ℝ)<(-(Real.log (7/50 : ℝ)+268/100)^2/(2*(59/100)^2)) := by apply (lt_div_iff₀ (by norm_num)).mpr; nlinarith
  have hehi : (-(Real.log (7/50 : ℝ)+268/100)^2/(2*(59/100)^2))<(-36601181/50000000 : ℝ) := by apply (div_lt_iff₀ (by norm_num)).mpr; nlinarith
  have hlo:=lt_trans exp_lo32 (Real.exp_lt_exp.mpr helo)
  have hhi:=lt_trans (Real.exp_lt_exp.mpr hehi) exp_hi32
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<(7/50 : ℝ)*(59/100)*Real.sqrt (2*Real.pi) := by positivity
  unfold Chapter06Figures.density
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]

theorem right_sum_4 : |Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) 4-(6941/10000 : ℝ)|<1/20000 := by
  have h8:=density8
  have h16:=density16
  have h24:=density24
  have h32:=density32
  norm_num [Chapter02Riemann.rightSum,Chapter02Riemann.grid,Finset.sum_range_succ]
  rw [abs_lt]
  constructor <;> linarith
#print axioms right_sum_4

theorem right_sum_8 : |Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) 8-(1893/2500 : ℝ)|<1/20000 := by
  have h4:=density4
  have h8:=density8
  have h12:=density12
  have h16:=density16
  have h20:=density20
  have h24:=density24
  have h28:=density28
  have h32:=density32
  norm_num [Chapter02Riemann.rightSum,Chapter02Riemann.grid,Finset.sum_range_succ]
  rw [abs_lt]
  constructor <;> linarith
#print axioms right_sum_8

theorem right_sum_32 : |Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) 32-(7953/10000 : ℝ)|<1/20000 := by
  have h1:=density1
  have h2:=density2
  have h3:=density3
  have h4:=density4
  have h5:=density5
  have h6:=density6
  have h7:=density7
  have h8:=density8
  have h9:=density9
  have h10:=density10
  have h11:=density11
  have h12:=density12
  have h13:=density13
  have h14:=density14
  have h15:=density15
  have h16:=density16
  have h17:=density17
  have h18:=density18
  have h19:=density19
  have h20:=density20
  have h21:=density21
  have h22:=density22
  have h23:=density23
  have h24:=density24
  have h25:=density25
  have h26:=density26
  have h27:=density27
  have h28:=density28
  have h29:=density29
  have h30:=density30
  have h31:=density31
  have h32:=density32
  norm_num [Chapter02Riemann.rightSum,Chapter02Riemann.grid,Finset.sum_range_succ]
  rw [abs_lt]
  constructor <;> linarith
#print axioms right_sum_32

theorem displayed_errors_decrease :
    Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) 4 < Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) 8 ∧
    Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) 8 < Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) 32 ∧
    Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) 32 < (∫ t in (3/100 : ℝ)..(14/100 : ℝ),Chapter06Figures.density t) := by
  rcases abs_lt.mp right_sum_4 with ⟨h4a,h4b⟩
  rcases abs_lt.mp right_sum_8 with ⟨h8a,h8b⟩
  rcases abs_lt.mp right_sum_32 with ⟨h32a,h32b⟩
  rcases abs_lt.mp Chapter06Area.source_area_rounding with ⟨hia,hib⟩
  constructor
  · linarith
  constructor <;> linarith
#print axioms displayed_errors_decrease
end Chapter06RightSums