import Mathlib
namespace Chapter09Review
theorem indicator_numeric_cases (p q:ℝ) (hq:q=0 ∨ q=1) (h:q=1 → p=1) : p*q=q := by rcases hq with hq|hq; simp [hq]; simp [hq,h hq]
end Chapter09Review
