import Mathlib
namespace Chapter06Density
noncomputable def intervalMass (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ t in a..b, f t

theorem zero_width (a : ℝ) : a-a=0 := sub_self a

theorem point_mass_zero (f : ℝ → ℝ) (a : ℝ) : intervalMass f a a=0 := by
  simp [intervalMass]

theorem set_integral_singleton_zero (f : ℝ → ℝ) (a : ℝ) :
    (∫ t in ({a} : Set ℝ), f t)=0 := by
  simp [MeasureTheory.integral_singleton]

#print axioms point_mass_zero
#print axioms set_integral_singleton_zero
end Chapter06Density
