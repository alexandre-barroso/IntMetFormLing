import Mathlib

open scoped BigOperators

namespace Chapter01Expressions

def corpusTotal : ℚ := 4112943
def beerProportion : ℚ := 195 / corpusTotal
def expectedPairs : ℚ := 660 * beerProportion
def associationRatio : ℚ := 29 / expectedPairs

theorem association_bindings :
    corpusTotal = 4112943 ∧ beerProportion = 195/4112943 ∧
    expectedPairs = 128700/4112943 ∧ associationRatio = 119275347/128700 := by
  norm_num [corpusTotal, beerProportion, expectedPairs, associationRatio]

theorem association_bounds :
    3/100 < expectedPairs ∧ expectedPairs < 4/100 ∧
    926 < associationRatio ∧ associationRatio < 927 := by
  norm_num [expectedPairs, beerProportion, corpusTotal, associationRatio]

def orthographic : List String := ["I'm"]
def grammatical : List String := ["I", "am"]

theorem segmentation_bindings :
    orthographic.length = 1 ∧ grammatical.length = 2 ∧
    grammatical.length - orthographic.length = 1 := by
  decide +kernel

def second : ℚ := 1
def millisecond : ℚ := 1/1000

theorem units_and_percent :
    (8/100 : ℚ)*second = 80*millisecond ∧
    (24/100 : ℚ)*second = 240*millisecond ∧
    (14/100-3/100 : ℚ)*second = 110*millisecond ∧
    (16/100 : ℚ)*second = 160*millisecond ∧
    (14/16 : ℚ) = (875/10)/100 := by
  norm_num [second, millisecond]

def concordance : Fin 4 → ℚ := ![23, 27, 5, 10]

theorem concordance_sum :
    (∑ i : Fin 4, concordance i) = 23+27+5+10 ∧
    (∑ i : Fin 4, concordance i) = 65 ∧
    (∑ i : Fin 4, concordance i / 65) = 1 := by
  norm_num [concordance, Fin.sum_univ_succ]

theorem four_term_sum (x : Fin 4 → ℝ) :
    (∑ i : Fin 4, x i) = x 0+x 1+x 2+x 3 := by
  simp [Fin.sum_univ_succ]
  ring

theorem interval_membership (t : ℝ) :
    t ∈ Set.Icc (3/100 : ℝ) (14/100) ↔ 3/100 ≤ t ∧ t ≤ 14/100 := Iff.rfl

def normalizedRate (c N : ℚ) : ℚ := c / N * 120000

theorem rate_numerator (c N : ℚ) : normalizedRate c N = c * 120000 / N := by
  unfold normalizedRate
  ring

theorem rate_bindings :
    normalizedRate 14 168799 = 1680000/168799 ∧
    normalizedRate 242 4623107 = 29040000/4623107 ∧
    normalizedRate 180 1012985 = 21600000/1012985 ∧
    normalizedRate 236 1009304 = 28320000/1009304 := by
  norm_num [normalizedRate]

theorem reversed_relative_difference :
    ((584/10-706/10)/(706/10) : ℚ) = -61/353 ∧
    ((584/10-706/10)/(706/10) : ℚ) ≠ -61/292 := by norm_num

def totalDuration {n : ℕ} (t : Fin n → ℝ) : ℝ := ∑ i, t i
noncomputable def meanDuration {n : ℕ} (t : Fin n → ℝ) : ℝ := totalDuration t / n

theorem arbitrary_mean {n : ℕ} (t : Fin n → ℝ) :
    meanDuration t = (∑ i : Fin n, t i) / n ∧
    meanDuration t = ∑ i : Fin n, (1/(n:ℝ))*t i := by
  constructor
  · rfl
  · simp only [meanDuration, totalDuration, ← Finset.mul_sum, one_div]
    ring

theorem arbitrary_weights (n : ℕ) (hn : 0 < n) :
    (∑ _i : Fin n, (1/(n:ℝ))) = 1 := by
  have h : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp [h]

def ratio (numerator denominator : ℚ) : Option ℚ :=
  if denominator = 0 then none else some (numerator / denominator)

theorem zero_denominator_undefined (x : ℚ) : ratio x 0 = none := by simp [ratio]

theorem positive_denominator_defined (x y : ℚ) (hy : 0 < y) :
    ratio x y = some (x/y) := by simp [ratio, ne_of_gt hy]

theorem zero_equation_not_unique : ¬ ∃! q : ℚ, 0*q = 0 := by
  rintro ⟨q, _, hq⟩
  have h0 := hq 0 (by norm_num)
  have h1 := hq 1 (by norm_num)
  linarith

end Chapter01Expressions

#print axioms Chapter01Expressions.association_bindings
#print axioms Chapter01Expressions.association_bounds
#print axioms Chapter01Expressions.segmentation_bindings
#print axioms Chapter01Expressions.units_and_percent
#print axioms Chapter01Expressions.concordance_sum
#print axioms Chapter01Expressions.four_term_sum
#print axioms Chapter01Expressions.interval_membership
#print axioms Chapter01Expressions.rate_numerator
#print axioms Chapter01Expressions.rate_bindings
#print axioms Chapter01Expressions.reversed_relative_difference
#print axioms Chapter01Expressions.arbitrary_mean
#print axioms Chapter01Expressions.arbitrary_weights
#print axioms Chapter01Expressions.zero_denominator_undefined
#print axioms Chapter01Expressions.positive_denominator_defined
#print axioms Chapter01Expressions.zero_equation_not_unique
