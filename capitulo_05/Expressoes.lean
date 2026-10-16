import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open scoped BigOperators

namespace Chapter05Expressions

def x : Fin 20 → ℚ := ![2,2,2,2,3,1,2,2,2,2,1,2,1,3,2,1,2,2,2,2]
def mean {n : ℕ} (x : Fin n → ℚ) : ℚ := (∑ i,x i)/n
def variance {n : ℕ} (x : Fin n → ℚ) : ℚ := (∑ i,(x i-mean x)^2)/(n-1)

theorem mean_from_observations : (∑ i,x i)=38 ∧ mean x=19/10 := by decide +kernel

theorem variance_from_observations : (∑ i,(x i-mean x))=0 ∧ (∑ i,(x i-mean x)^2)=29/5 ∧ variance x=29/95 := by decide +kernel

def sizes : Fin 3 → ℚ := ![4/10,3/10,3/10]
def observations : Fin 3 → ℚ := ![6/10,2/10,2/10]
def dispersion {n : ℕ} (o s : Fin n → ℚ) : ℚ := (∑ i,|o i-s i|)/2

theorem dispersion_from_distributions : dispersion observations sizes=1/5 ∧ (∑ i,sizes i)=1 ∧ (∑ i,observations i)=1 := by decide +kernel

theorem normalized_dispersion : (∀ i,sizes 1 ≤ sizes i) ∧ dispersion observations sizes/(1-sizes 1)=2/7 := by decide +kernel

def weightedMean {n : ℕ} (w x : Fin n → ℚ) : ℚ := ∑ i,w i*x i

theorem weighted_empirical_mean : weightedMean ![4/20,14/20,2/20] ![1,2,3]=mean x := by decide +kernel

noncomputable def standardize (x m s : ℝ) : ℝ := (x-m)/s

theorem standardization_origin_unit (m s : ℝ) (hs : s≠0) : standardize m m s=0 ∧ standardize (m+s) m s=1 := by simp [standardize,hs]

def O₁ : Matrix (Fin 2) (Fin 2) ℚ := !![180,3;20,153]
def O₂ : Matrix (Fin 2) (Fin 2) ℚ := !![29,13;123,31612]
def row {r c : ℕ} (O : Matrix (Fin r) (Fin c) ℚ) (i : Fin r) : ℚ := ∑ j,O i j
def col {r c : ℕ} (O : Matrix (Fin r) (Fin c) ℚ) (j : Fin c) : ℚ := ∑ i,O i j
def total {r c : ℕ} (O : Matrix (Fin r) (Fin c) ℚ) : ℚ := ∑ i,row O i
def expected {r c : ℕ} (O : Matrix (Fin r) (Fin c) ℚ) : Matrix (Fin r) (Fin c) ℚ := fun i j => row O i*col O j/total O

theorem margins_one : row O₁=![183,173] ∧ col O₁=![200,156] ∧ total O₁=356 := by decide +kernel

theorem margins_two : row O₂=![42,31735] ∧ col O₂=![152,31625] ∧ total O₂=31777 := by decide +kernel

theorem expected_one : expected O₁=!![36600/356,28548/356;34600/356,26988/356] := by decide +kernel

theorem expected_two : expected O₂=!![6384/31777,1328250/31777;4823720/31777,1003619375/31777] := by decide +kernel

theorem expected_row_general {r c : ℕ} (O : Matrix (Fin r) (Fin c) ℚ) (ht : total O≠0) (i : Fin r) :
    (∑ j,expected O i j)=row O i := by
  unfold expected
  rw [←Finset.sum_div,←Finset.mul_sum]
  have he : (∑ j,col O j)=total O := by unfold col total row;rw [Finset.sum_comm]
  rw [he,mul_div_cancel_right₀ _ ht]

noncomputable def contribution (O : Matrix (Fin 2) (Fin 2) ℚ) (i j : Fin 2) : ℝ := (O i j:ℝ)*Real.log ((O i j:ℝ)/(expected O i j:ℝ))
noncomputable def gStatistic (O : Matrix (Fin 2) (Fin 2) ℚ) : ℝ := 2*∑ i,∑ j,contribution O i j

theorem contributions_from_table :
    contribution O₂ 0 0=29*Real.log (921533/6384) ∧
    contribution O₂ 0 1=13*Real.log (413101/1328250) ∧
    contribution O₂ 1 0=123*Real.log (3908571/4823720) ∧
    contribution O₂ 1 1=31612*Real.log (1004534524/1003619375) := by
  simp only [contribution,expected_two]
  norm_num [O₂]

theorem g_from_table : gStatistic O₂=2*(29*Real.log (921533/6384)+13*Real.log (413101/1328250)+123*Real.log (3908571/4823720)+31612*Real.log (1004534524/1003619375)) := by
  unfold gStatistic
  simp only [Fin.sum_univ_two]
  rw [contributions_from_table.1,contributions_from_table.2.1,contributions_from_table.2.2.1,contributions_from_table.2.2.2]
  ring


theorem mean_requires_positive_size {n : ℕ} (hn : 0 < n) : (n:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)

theorem sample_variance_nonnegative {n : ℕ} (x : Fin n → ℚ) (hn : 2 ≤ n) : 0 ≤ variance x := by
  unfold variance
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _=>sq_nonneg _)
  · have h : (2:ℚ) ≤ n := by exact_mod_cast hn
    linarith

theorem sample_variance_denominator {n : ℕ} (hn : 2 ≤ n) : 0 < (n:ℚ)-1 := by
  have h : (2:ℚ) ≤ n := by exact_mod_cast hn
  linarith

theorem sample_variance_constant {n : ℕ} (c : ℚ) (hn : 2 ≤ n) : variance (fun _ : Fin n => c)=0 := by
  have hnq : (n:ℚ)≠0 := mean_requires_positive_size (by omega)
  simp [variance,mean,Finset.sum_const,mul_div_cancel_left₀,hnq]

theorem standardization_sign (x m s : ℝ) (hs : 0 < s) :
    (0 < standardize x m s ↔ m < x) ∧ (standardize x m s < 0 ↔ x < m) := by
  unfold standardize
  exact ⟨by rw [div_pos_iff_of_pos_right hs,sub_pos],by rw [div_lt_iff₀ hs,zero_mul,sub_neg]⟩

def guardedStandardize (x m s : ℚ) : Option ℚ := if 0 < s then some ((x-m)/s) else none

theorem standardization_zero_scale (x m : ℚ) : guardedStandardize x m 0=none := by simp [guardedStandardize]

theorem expected_nonnegative {r c : ℕ} (O : Matrix (Fin r) (Fin c) ℚ)
    (hO : ∀ i j,0 ≤ O i j) (i : Fin r) (j : Fin c) : 0 ≤ expected O i j := by
  apply div_nonneg
  · exact mul_nonneg (Finset.sum_nonneg (fun k _=>hO i k)) (Finset.sum_nonneg (fun k _=>hO k j))
  · exact Finset.sum_nonneg (fun k _=>Finset.sum_nonneg (fun l _=>hO k l))

theorem expected_column_general {r c : ℕ} (O : Matrix (Fin r) (Fin c) ℚ)
    (ht : total O≠0) (j : Fin c) : (∑ i,expected O i j)=col O j := by
  unfold expected
  rw [←Finset.sum_div,←Finset.sum_mul]
  change total O*col O j/total O=col O j
  field_simp

theorem expected_total_general {r c : ℕ} (O : Matrix (Fin r) (Fin c) ℚ)
    (ht : total O≠0) : total (expected O)=total O := by
  unfold total row
  apply Finset.sum_congr rfl
  intro i hi
  exact expected_row_general O ht i

#print axioms mean_requires_positive_size
#print axioms sample_variance_nonnegative
#print axioms sample_variance_denominator
#print axioms sample_variance_constant
#print axioms standardization_sign
#print axioms standardization_zero_scale
#print axioms expected_nonnegative
#print axioms expected_column_general
#print axioms expected_total_general

end Chapter05Expressions

#print axioms Chapter05Expressions.mean_from_observations
#print axioms Chapter05Expressions.variance_from_observations
#print axioms Chapter05Expressions.dispersion_from_distributions
#print axioms Chapter05Expressions.normalized_dispersion
#print axioms Chapter05Expressions.weighted_empirical_mean
#print axioms Chapter05Expressions.standardization_origin_unit
#print axioms Chapter05Expressions.margins_one
#print axioms Chapter05Expressions.margins_two
#print axioms Chapter05Expressions.expected_one
#print axioms Chapter05Expressions.expected_two
#print axioms Chapter05Expressions.expected_row_general
#print axioms Chapter05Expressions.contributions_from_table
#print axioms Chapter05Expressions.g_from_table
