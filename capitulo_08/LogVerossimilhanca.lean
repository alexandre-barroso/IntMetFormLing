import Mathlib

namespace Chapter08LogLikelihood

noncomputable def firstContribution (o e n:ℝ) : ℝ := if o=0 then 0 else o*(Real.log (o/n)-Real.log (e/n))
noncomputable def middleContribution (o e n:ℝ) : ℝ := if o=0 then 0 else o*Real.log ((o/n)/(e/n))
noncomputable def finalContribution (o e:ℝ) : ℝ := if o=0 then 0 else o*Real.log (o/e)

theorem contribution_chain (o e n:ℝ) (ho:0≤o) (he:0<e) (hn:0<n) :
 firstContribution o e n=middleContribution o e n ∧ middleContribution o e n=finalContribution o e := by
 by_cases hz:o=0
 · simp [firstContribution,middleContribution,finalContribution,hz]
 have hp:0<o:=lt_of_le_of_ne ho (Ne.symm hz)
 have ha:o/n≠0:=ne_of_gt (div_pos hp hn)
 have hb:e/n≠0:=ne_of_gt (div_pos he hn)
 have hratio:(o/n)/(e/n)=o/e:=by field_simp
 constructor
 · simp only [firstContribution,middleContribution,hz,if_false]
   rw [Real.log_div ha hb]
 · simp only [middleContribution,finalContribution,hz,if_false]
   rw [hratio]

theorem finite_sum_chain {k:ℕ} (o e:Fin k→ℝ) (n:ℝ) (ho:∀ i,0≤o i) (he:∀ i,0<e i) (hn:0<n) :
 (∑ i,firstContribution (o i) (e i) n)=(∑ i,middleContribution (o i) (e i) n) ∧
 (∑ i,middleContribution (o i) (e i) n)=(∑ i,finalContribution (o i) (e i)) := by
 constructor
 · apply Finset.sum_congr rfl
   intro i hi
   exact (contribution_chain (o i) (e i) n (ho i) (he i) hn).1
 · apply Finset.sum_congr rfl
   intro i hi
   exact (contribution_chain (o i) (e i) n (ho i) (he i) hn).2


theorem matrix_sum_chain {m k:ℕ} (o e:Fin m→Fin k→ℝ) (n:ℝ)
 (ho:∀ i j,0≤o i j) (he:∀ i j,0<e i j) (hn:0<n) :
 (∑ i,∑ j,firstContribution (o i j) (e i j) n)=(∑ i,∑ j,middleContribution (o i j) (e i j) n) ∧
 (∑ i,∑ j,middleContribution (o i j) (e i j) n)=(∑ i,∑ j,finalContribution (o i j) (e i j)) := by
 constructor
 · apply Finset.sum_congr rfl
   intro i hi
   apply Finset.sum_congr rfl
   intro j hj
   exact (contribution_chain (o i j) (e i j) n (ho i j) (he i j) hn).1
 · apply Finset.sum_congr rfl
   intro i hi
   apply Finset.sum_congr rfl
   intro j hj
   exact (contribution_chain (o i j) (e i j) n (ho i j) (he i j) hn).2

theorem zero_contribution_limit (e:ℝ) (he:0<e) :
 Filter.Tendsto (fun x:ℝ=>x*Real.log (x/e)) (nhds 0) (nhds 0) := by
 have hfun:(fun x:ℝ=>x*Real.log (x/e))=(fun x:ℝ=>x*Real.log x-x*Real.log e):=by
  funext x
  by_cases hx:x=0
  · simp [hx]
  · rw [Real.log_div hx (ne_of_gt he)]
    ring
 rw [hfun]
 have hc:Continuous (fun x:ℝ=>x*Real.log x-x*Real.log e):=Real.continuous_mul_log.sub (continuous_id.mul_const _)
 simpa using hc.tendsto (0:ℝ)

end Chapter08LogLikelihood
