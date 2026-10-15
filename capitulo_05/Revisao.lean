import Mathlib

open scoped BigOperators

namespace Chapter05Review

theorem trimmed_mean_rounding : |(23:ℚ)/6-383/100|<1/200 := by norm_num

theorem square_expansion_chain (c d:ℝ) :
 (c+d)^2=(c+d)*(c+d) ∧
 (c+d)*(c+d)=c*c+c*d+d*c+d*d ∧
 c*c+c*d+d*c+d*d=c^2+c*d+c*d+d^2 ∧
 c^2+c*d+c*d+d^2=c^2+2*c*d+d^2 := by and_intros <;> ring

theorem midpoint_recovery_chain (x y:ℝ) :
 (x+y)/2+(x-y)/2=(x+y+x-y)/2 ∧ (x+y+x-y)/2=2*x/2 ∧ 2*x/2=x ∧
 (x+y)/2-(x-y)/2=(x+y-(x-y))/2 ∧ (x+y-(x-y))/2=(x+y-x+y)/2 ∧
 (x+y-x+y)/2=2*y/2 ∧ 2*y/2=y := by and_intros <;> ring

theorem recover_candidate (a m h:ℝ) (hh:h=a-m) : a=m+h := by rw [hh];ring

theorem shifted_deviation_chains (m d h:ℝ) :
 (m+d)-(m+h)=d-h ∧ (m-d)-(m+h)=-d-h := by constructor <;> ring

theorem symmetric_loss_chain (d h:ℝ) :
 (d-h)^2+(-d-h)^2=(d^2-2*d*h+h^2)+(d^2+2*d*h+h^2) ∧
 (d^2-2*d*h+h^2)+(d^2+2*d*h+h^2)=2*d^2+2*h^2 := by constructor <;> ring

theorem loss_penalty_nonnegative (h:ℝ) : 0≤2*h^2 := mul_nonneg (by norm_num) (sq_nonneg h)

theorem mean_minimum (x y a:ℝ) :
 (x-(x+y)/2)^2+(y-(x+y)/2)^2≤(x-a)^2+(y-a)^2 := by
 nlinarith [sq_nonneg (a-(x+y)/2)]

theorem statistic_scale_finite {n:ℕ} (o e:Fin n→ℝ) (k:ℝ) (hk:k≠0) :
 2*(∑ i,(k*o i)*Real.log ((k*o i)/(k*e i)))=
 k*(2*(∑ i,o i*Real.log (o i/e i))) := by
 have h:∀i,(k*o i)*Real.log ((k*o i)/(k*e i))=k*(o i*Real.log (o i/e i)) := by
  intro i
  rw [mul_div_mul_left (o i) (e i) hk]
  ring
 simp_rw [h]
 rw [← Finset.mul_sum]
 ring

theorem total_scale {n:ℕ} (o:Fin n→ℝ) (k:ℝ) : (∑ i,k*o i)=k*(∑ i,o i) := by rw [Finset.mul_sum]

theorem variance_rounding : |(29:ℚ)/95-3053/10000|<1/20000 := by norm_num

theorem normalized_entry_le_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (j : Fin n) : p j ≤ 1 := by
  rw [← hs]
  exact Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ j)

theorem normalized_minimum_bounds {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (j : Fin n) (m : ℝ)
    (hm : m = p j) : 0 ≤ m ∧ m ≤ 1 := by
  rw [hm]
  exact ⟨hp j, normalized_entry_le_one p hp hs j⟩

end Chapter05Review
