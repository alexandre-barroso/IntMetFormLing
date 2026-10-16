import Mathlib

open scoped BigOperators

namespace Chapter01Conditions

noncomputable def safeRate (c : ℝ) (N : ℕ) : Option ℝ :=
  if N = 0 then none else some (c / (N : ℝ) * 120000)

noncomputable def safeMean {N : ℕ} (t : Fin N → ℝ) : Option ℝ :=
  if N = 0 then none else some ((∑ i, t i) / (N : ℝ))

theorem rate_zero (c : ℝ) : safeRate c 0 = none := by simp [safeRate]

theorem rate_defined (c : ℝ) (N : ℕ) (hN : 0 < N) :
    safeRate c N = some (c * 120000 / (N : ℝ)) := by
  simp [safeRate, Nat.ne_of_gt hN]
  ring

theorem mean_zero (t : Fin 0 → ℝ) : safeMean t = none := by simp [safeMean]

theorem mean_defined {N : ℕ} (t : Fin N → ℝ) (hN : 0 < N) :
    safeMean t = some (∑ i : Fin N, (1 / (N : ℝ)) * t i) := by
  simp only [safeMean, if_neg (Nat.ne_of_gt hN), ← Finset.mul_sum]
  congr 1
  ring

theorem rate_domain (c : ℝ) (N : ℕ) : safeRate c N = none ↔ N = 0 := by
  by_cases hN : N = 0 <;> simp [safeRate, hN]

theorem mean_domain {N : ℕ} (t : Fin N → ℝ) : safeMean t = none ↔ N = 0 := by
  by_cases hN : N = 0 <;> simp [safeMean, hN]

theorem relative_change_denominator (x y : ℝ) (hy : y ≠ 0) :
    ((x-y)/y)*y=x-y := div_mul_cancel₀ (x-y) hy

theorem ratio_determined (x y : ℝ) (hy : y ≠ 0) :
    ∃! q : ℝ, y*q=x := by
  refine ⟨x/y, ?_, ?_⟩
  · field_simp
  · intro q hq
    apply (eq_div_iff hy).mpr
    nlinarith

end Chapter01Conditions

#print axioms Chapter01Conditions.rate_zero
#print axioms Chapter01Conditions.rate_defined
#print axioms Chapter01Conditions.mean_zero
#print axioms Chapter01Conditions.mean_defined
#print axioms Chapter01Conditions.rate_domain
#print axioms Chapter01Conditions.mean_domain
#print axioms Chapter01Conditions.relative_change_denominator
#print axioms Chapter01Conditions.ratio_determined
