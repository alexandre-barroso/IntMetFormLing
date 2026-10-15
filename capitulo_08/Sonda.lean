import Mathlib

namespace Chapter08Probe

theorem transformed_dot_as_squares {m k:ℕ} (B:Matrix (Fin k) (Fin m) ℝ) (x y:Fin m→ℝ) :
 dotProduct (B.mulVec (x-y)) (B.mulVec (x-y)) = ∑ r,(∑ c,B r c*(x c-y c))^2 := by
 simp [dotProduct,Matrix.mulVec,pow_two]

end Chapter08Probe
