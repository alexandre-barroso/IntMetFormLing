import Mathlib

open scoped BigOperators

namespace Capitulo04Base

def e {n : ℕ} (i : Fin n) (j : Fin n) : ℝ := if j = i then 1 else 0

theorem c04_p02_coordinate {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    (∑ i : Fin n, x i * e i j) = x j := by
  classical
  simp [e]

theorem c04_p02_independent {n : ℕ} (x : Fin n → ℝ)
    (h : ∀ j : Fin n, (∑ i : Fin n, x i * e i j) = 0) :
    ∀ j, x j = 0 := by
  intro j
  simpa [c04_p02_coordinate] using h j

theorem c04_p02_orthogonal {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∑ k : Fin n, e i k * e j k) = 0 := by
  classical
  simp [e, Ne.symm hij]

theorem c04_p02_unit_norm {n : ℕ} (i : Fin n) :
    Real.sqrt (∑ k : Fin n, (e i k)^2) = 1 := by
  classical
  simp [e]

end Capitulo04Base

#print axioms Capitulo04Base.c04_p02_coordinate
#print axioms Capitulo04Base.c04_p02_independent
#print axioms Capitulo04Base.c04_p02_orthogonal
#print axioms Capitulo04Base.c04_p02_unit_norm
