import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Chapter02Riemann

noncomputable def grid (a b : ℝ) (N k : ℕ) : ℝ := a+(k:ℝ)*((b-a)/N)
noncomputable def rightSum (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  ∑ k∈Finset.range N,f (grid a b N (k+1))*((b-a)/N)

theorem grid_start (a b : ℝ) (N : ℕ) : grid a b N 0=a := by simp [grid]

theorem grid_finish (a b : ℝ) (N : ℕ) (hN : 0<N) : grid a b N N=b := by
  have h : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold grid
  field_simp
  ring

theorem grid_step (a b : ℝ) (N k : ℕ) : grid a b N (k+1)-grid a b N k=(b-a)/N := by
  unfold grid
  push_cast
  ring

theorem grid_monotone (a b : ℝ) (hab : a≤b) (N : ℕ) : Monotone (grid a b N) := by
  intro i j hij
  unfold grid
  simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N))) a

theorem grid_inside (a b : ℝ) (hab : a≤b) (N k : ℕ) (hN : 0<N) (hk : k≤N) : grid a b N k∈Set.Icc a b := by
  constructor
  · simpa [grid_start] using grid_monotone a b hab N (Nat.zero_le k)
  · simpa [grid_finish a b N hN] using grid_monotone a b hab N hk

theorem partition_error (f : ℝ → ℝ) (nodes : ℕ → ℝ) (N : ℕ) (eta : ℝ)
    (ordered : Monotone nodes)
    (integrable : ∀ k<N,IntervalIntegrable f volume (nodes k) (nodes (k+1)))
    (oscillation : ∀ k<N,∀ t∈Set.Icc (nodes k) (nodes (k+1)),|f (nodes (k+1))-f t|≤eta) :
    |(∑ k∈Finset.range N,f (nodes (k+1))*(nodes (k+1)-nodes k))-
      ∫ t in nodes 0..nodes N,f t| ≤ eta*(nodes N-nodes 0) := by
  have hcell : ∀ k<N,
      |f (nodes (k+1))*(nodes (k+1)-nodes k)-∫ t in nodes k..nodes (k+1),f t| ≤ eta*(nodes (k+1)-nodes k) := by
    intro k hk
    have hn : nodes k≤nodes (k+1) := ordered (by omega)
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=nodes k) (b:=nodes (k+1)) (f:=fun t=>f (nodes (k+1))-f t) (C:=eta) (by
        intro t ht
        rw [Set.uIoc_of_le hn] at ht
        simpa only [Real.norm_eq_abs] using oscillation k hk t ⟨ht.1.le,ht.2⟩)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (integrable k hk),intervalIntegral.integral_const] at hb
    simpa only [Real.norm_eq_abs,smul_eq_mul,abs_of_nonneg (sub_nonneg.mpr hn),mul_comm] using hb
  rw [←intervalIntegral.sum_integral_adjacent_intervals integrable,←Finset.sum_sub_distrib]
  calc
    |∑ k∈Finset.range N,(f (nodes (k+1))*(nodes (k+1)-nodes k)-∫ t in nodes k..nodes (k+1),f t)|
      ≤ ∑ k∈Finset.range N,|f (nodes (k+1))*(nodes (k+1)-nodes k)-∫ t in nodes k..nodes (k+1),f t| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k∈Finset.range N,eta*(nodes (k+1)-nodes k) := Finset.sum_le_sum (fun k hk=>hcell k (Finset.mem_range.mp hk))
    _ = eta*(nodes N-nodes 0) := by rw [←Finset.mul_sum,Finset.sum_range_sub]

theorem right_sum_error (f : ℝ → ℝ) (a b eta : ℝ) (hab : a≤b) (N : ℕ) (hN : 0<N)
    (hf : ContinuousOn f (Set.Icc a b))
    (oscillation : ∀ k<N,∀ t∈Set.Icc (grid a b N k) (grid a b N (k+1)),|f (grid a b N (k+1))-f t|≤eta) :
    |rightSum f a b N-∫ t in a..b,f t|≤eta*(b-a) := by
  have hg := grid_monotone a b hab N
  have hint : ∀ k<N,IntervalIntegrable f volume (grid a b N k) (grid a b N (k+1)) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable_of_Icc (hg (by omega))
    apply hf.mono
    intro t ht
    exact ⟨le_trans (grid_inside a b hab N k hN (by omega)).1 ht.1,
      le_trans ht.2 (grid_inside a b hab N (k+1) hN (by omega)).2⟩
  have h := partition_error f (grid a b N) N eta hg hint oscillation
  simpa only [grid_start,grid_finish a b N hN,grid_step,rightSum] using h

theorem right_sum_limit (f : ℝ → ℝ) (a b : ℝ) (hab : a<b) (hf : ContinuousOn f (Set.Icc a b)) :
    Tendsto (fun N : ℕ=>rightSum f a b (N+1)) atTop (𝓝 (∫ t in a..b,f t)) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  have hlength : 0<b-a := sub_pos.mpr hab
  have heta : 0<epsilon/(2*(b-a)) := by positivity
  obtain ⟨delta,hdelta,hu⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (epsilon/(2*(b-a))) heta
  obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/delta)
  refine ⟨N,?_⟩
  intro n hn
  have hnp : 0<(n+1:ℕ) := by omega
  have hnreal : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr hnp
  have hndelta : (b-a)/((n+1:ℕ):ℝ)<delta := by
    apply (div_lt_iff₀ hnreal).mpr
    have hcast : (N:ℝ)≤(n+1:ℕ) := Nat.cast_le.mpr (by omega)
    have hh : b-a < (N:ℝ)*delta := (div_lt_iff₀ hdelta).mp hN
    nlinarith
  have hosc : ∀ k<n+1,∀ t∈Set.Icc (grid a b (n+1) k) (grid a b (n+1) (k+1)),
      |f (grid a b (n+1) (k+1))-f t|≤epsilon/(2*(b-a)) := by
    intro k hk t ht
    have hright := grid_inside a b hab.le (n+1) (k+1) hnp (by omega)
    have hleft := grid_inside a b hab.le (n+1) k hnp (by omega)
    have htglobal : t∈Set.Icc a b := ⟨hleft.1.trans ht.1,ht.2.trans hright.2⟩
    have hdist : dist (grid a b (n+1) (k+1)) t<delta := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.2)]
      have hstep := grid_step a b (n+1) k
      linarith [ht.1]
    simpa only [Real.dist_eq] using (hu _ hright t htglobal hdist).le
  have herr := right_sum_error f a b (epsilon/(2*(b-a))) hab.le (n+1) hnp hf hosc
  have heq : (epsilon/(2*(b-a)))*(b-a)=epsilon/2 := by field_simp <;> ring
  rw [heq] at herr
  rw [Real.dist_eq]
  linarith

theorem weighted_right_sum_limit (w f : ℝ → ℝ) (a b : ℝ) (hab : a<b)
    (hw : ContinuousOn w (Set.Icc a b)) (hf : ContinuousOn f (Set.Icc a b)) :
    Tendsto (fun N : ℕ=>rightSum (fun t=>w t*f t) a b (N+1)) atTop (𝓝 (∫ t in a..b,w t*f t)) :=
  right_sum_limit _ a b hab (hw.mul hf)

noncomputable def taggedSum (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) (tags : ℕ → ℝ) : ℝ :=
  ∑ k∈Finset.range N,f (tags k)*((b-a)/N)

theorem tagged_partition_error (f : ℝ → ℝ) (nodes tags : ℕ → ℝ) (N : ℕ) (eta : ℝ)
    (ordered : Monotone nodes)
    (integrable : ∀ k<N,IntervalIntegrable f volume (nodes k) (nodes (k+1)))
    (oscillation : ∀ k<N,∀ t∈Set.Icc (nodes k) (nodes (k+1)),|f (tags k)-f t|≤eta) :
    |(∑ k∈Finset.range N,f (tags k)*(nodes (k+1)-nodes k))-
      ∫ t in nodes 0..nodes N,f t| ≤ eta*(nodes N-nodes 0) := by
  have hcell : ∀ k<N,
      |f (tags k)*(nodes (k+1)-nodes k)-∫ t in nodes k..nodes (k+1),f t| ≤ eta*(nodes (k+1)-nodes k) := by
    intro k hk
    have hn : nodes k≤nodes (k+1) := ordered (by omega)
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=nodes k) (b:=nodes (k+1)) (f:=fun t=>f (tags k)-f t) (C:=eta) (by
        intro t ht
        rw [Set.uIoc_of_le hn] at ht
        simpa only [Real.norm_eq_abs] using oscillation k hk t ⟨ht.1.le,ht.2⟩)
    rw [intervalIntegral.integral_sub intervalIntegrable_const (integrable k hk),intervalIntegral.integral_const] at hb
    simpa only [Real.norm_eq_abs,smul_eq_mul,abs_of_nonneg (sub_nonneg.mpr hn),mul_comm] using hb
  rw [←intervalIntegral.sum_integral_adjacent_intervals integrable,←Finset.sum_sub_distrib]
  calc
    |∑ k∈Finset.range N,(f (tags k)*(nodes (k+1)-nodes k)-∫ t in nodes k..nodes (k+1),f t)|
      ≤ ∑ k∈Finset.range N,|f (tags k)*(nodes (k+1)-nodes k)-∫ t in nodes k..nodes (k+1),f t| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k∈Finset.range N,eta*(nodes (k+1)-nodes k) := Finset.sum_le_sum (fun k hk=>hcell k (Finset.mem_range.mp hk))
    _ = eta*(nodes N-nodes 0) := by rw [←Finset.mul_sum,Finset.sum_range_sub]


theorem tagged_sum_limit (f : ℝ → ℝ) (a b : ℝ) (hab : a<b)
    (hf : ContinuousOn f (Set.Icc a b)) (tags : ℕ → ℕ → ℝ)
    (htags : ∀ N : ℕ,0<N → ∀ k<N,tags N k∈Set.Icc (grid a b N k) (grid a b N (k+1))) :
    Tendsto (fun N : ℕ=>taggedSum f a b (N+1) (tags (N+1))) atTop (𝓝 (∫ t in a..b,f t)) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  have hlength : 0<b-a := sub_pos.mpr hab
  have heta : 0<epsilon/(2*(b-a)) := by positivity
  obtain ⟨delta,hdelta,hu⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (epsilon/(2*(b-a))) heta
  obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/delta)
  refine ⟨N,?_⟩
  intro n hn
  have hnp : 0<(n+1:ℕ) := by omega
  have hnreal : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr hnp
  have hndelta : (b-a)/((n+1:ℕ):ℝ)<delta := by
    apply (div_lt_iff₀ hnreal).mpr
    have hcast : (N:ℝ)≤(n+1:ℕ) := Nat.cast_le.mpr (by omega)
    have hh : b-a < (N:ℝ)*delta := (div_lt_iff₀ hdelta).mp hN
    nlinarith
  have hg := grid_monotone a b hab.le (n+1)
  have hcell : ∀ k<n+1,Set.Icc (grid a b (n+1) k) (grid a b (n+1) (k+1))⊆Set.Icc a b := by
    intro k hk t ht
    exact ⟨le_trans (grid_inside a b hab.le (n+1) k hnp (by omega)).1 ht.1,
      le_trans ht.2 (grid_inside a b hab.le (n+1) (k+1) hnp (by omega)).2⟩
  have hint : ∀ k<n+1,IntervalIntegrable f volume (grid a b (n+1) k) (grid a b (n+1) (k+1)) := by
    intro k hk
    exact ContinuousOn.intervalIntegrable_of_Icc (hg (by omega)) (hf.mono (hcell k hk))
  have hosc : ∀ k<n+1,∀ t∈Set.Icc (grid a b (n+1) k) (grid a b (n+1) (k+1)),
      |f (tags (n+1) k)-f t|≤epsilon/(2*(b-a)) := by
    intro k hk t ht
    have htag := htags (n+1) hnp k hk
    have hdist : dist (tags (n+1) k) t<delta := by
      rw [Real.dist_eq]
      have hstep := grid_step a b (n+1) k
      apply lt_of_le_of_lt (abs_le.mpr ?_) hndelta
      constructor <;> linarith [htag.1,htag.2,ht.1,ht.2]
    simpa only [Real.dist_eq] using (hu _ (hcell k hk htag) t (hcell k hk ht) hdist).le
  have herr := tagged_partition_error f (grid a b (n+1)) (tags (n+1)) (n+1)
    (epsilon/(2*(b-a))) hg hint hosc
  simp only [grid_start,grid_finish a b (n+1) hnp,grid_step] at herr
  have heq : (epsilon/(2*(b-a)))*(b-a)=epsilon/2 := by field_simp <;> ring
  rw [heq] at herr
  rw [Real.dist_eq]
  unfold taggedSum
  linarith

theorem weighted_tagged_sum_limit (w f : ℝ → ℝ) (a b : ℝ) (hab : a<b)
    (hw : ContinuousOn w (Set.Icc a b)) (hf : ContinuousOn f (Set.Icc a b))
    (tags : ℕ → ℕ → ℝ)
    (htags : ∀ N : ℕ,0<N → ∀ k<N,tags N k∈Set.Icc (grid a b N k) (grid a b N (k+1))) :
    Tendsto (fun N : ℕ=>taggedSum (fun t=>w t*f t) a b (N+1) (tags (N+1)))
      atTop (𝓝 (∫ t in a..b,w t*f t)) :=
  tagged_sum_limit _ a b hab (hw.mul hf) tags htags

#print axioms tagged_partition_error
#print axioms tagged_sum_limit
#print axioms weighted_tagged_sum_limit

end Chapter02Riemann

#print axioms Chapter02Riemann.grid_start
#print axioms Chapter02Riemann.grid_finish
#print axioms Chapter02Riemann.grid_step
#print axioms Chapter02Riemann.grid_monotone
#print axioms Chapter02Riemann.grid_inside
#print axioms Chapter02Riemann.partition_error
#print axioms Chapter02Riemann.right_sum_error
#print axioms Chapter02Riemann.right_sum_limit
#print axioms Chapter02Riemann.weighted_right_sum_limit
