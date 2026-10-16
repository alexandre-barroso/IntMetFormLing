import Mathlib

namespace Chapter07V2Figures

def original : List (ℚ × ℚ) := [(1,1),(1,0),(1,1),(0,1),(1,0),(0,1),(1,0),(1,1),(0,0),(1,0)]
def firstSample : List (ℚ × ℚ) := [(1,0),(1,1),(1,0),(0,1),(0,1),(1,0),(0,1),(1,1),(0,0),(1,1)]
def secondSample : List (ℚ × ℚ) := [(1,0),(1,1),(0,0),(0,1),(0,1),(1,1),(0,1),(1,0),(1,1),(1,1)]
def differences (xs : List (ℚ × ℚ)) : ℚ := (xs.map (fun p => p.1-p.2)).sum / xs.length

theorem three_sample_values :
    differences original=1/5 ∧ differences firstSample=0 ∧ differences secondSample= -1/10 := by
  norm_num [differences, original, firstSample, secondSample]

theorem paired_bootstrap_admissible :
    firstSample.length=original.length ∧ secondSample.length=original.length ∧
    (∀ p∈firstSample, p∈original) ∧ (∀ p∈secondSample, p∈original) := by
  decide +kernel

theorem paired_resample_counts :
    (firstSample.map Prod.fst).sum=6 ∧ (firstSample.map Prod.snd).sum=6 ∧
    (secondSample.map Prod.fst).sum=6 ∧ (secondSample.map Prod.snd).sum=7 := by
  norm_num [firstSample,secondSample]

theorem source_pair_nonidentification :
    original[1]?=original[4]? ∧ (1:ℕ)≠4 := by decide +kernel

end Chapter07V2Figures
