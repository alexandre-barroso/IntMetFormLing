import Mathlib

open scoped BigOperators

namespace Chapter01Exposition

theorem expected_count {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, p i = q) : (∑ i, p i) = n * q := by
  simp [hp]

theorem expected_count_finite_model {Ω : Type*} [Fintype Ω]
    {n : ℕ} (w : Ω → ℝ) (X : Fin n → Ω → Bool) (q : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hprob : ∑ ω, w ω = 1)
    (hq : ∀ i, ∑ ω, w ω * (if X i ω then (1:ℝ) else 0) = q) :
    (∑ ω, w ω * ∑ i, (if X i ω then (1:ℝ) else 0)) = n*q := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hq]
  simp

theorem ttr_repeated_type (V N : ℝ) (hV : 0 ≤ V) (hN : 0 < N) :
    V / (N + 1) ≤ V / N := by
  apply (div_le_div_iff₀ (by linarith : 0 < N+1) hN).mpr
  nlinarith

theorem ttr_repeated_type_strict (V N : ℝ) (hV : 0 < V) (hN : 0 < N) :
    V / (N + 1) < V / N := by
  apply (div_lt_div_iff₀ (by linarith : 0 < N+1) hN).mpr
  nlinarith

theorem ttr_new_type (V N : ℝ) (hN : 0 < N) (hVN : V ≤ N) :
    V / N ≤ (V + 1) / (N + 1) := by
  apply (div_le_div_iff₀ hN (by linarith : 0 < N+1)).mpr
  nlinarith

theorem ttr_bounds (V N : ℝ) (hV : 0 ≤ V) (hN : 0 < N) (hVN : V ≤ N) :
    0 ≤ V / N ∧ V / N ≤ 1 := by
  exact ⟨div_nonneg hV hN.le, (div_le_one hN).mpr hVN⟩

theorem normalization_scaling (c N k b : ℝ) (hN : N ≠ 0) (hk : k ≠ 0) :
    (k*c)/(k*N)*b = c/N*b := by
  field_simp

theorem normalization_order (c₁ c₂ N₁ N₂ b : ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hb : 0 < b) :
    c₁/N₁*b < c₂/N₂*b ↔ c₁*N₂ < c₂*N₁ := by
  rw [mul_lt_mul_iff_left₀ hb, div_lt_div_iff₀ hN₁ hN₂]

def tokens : List String := ["They", "picnicked", "by", "the", "pool", "then", "lay", "back", "on", "the", "grass", "and", "looked", "at", "the", "stars"]

def repetitions : List ℕ := (List.range tokens.length).filter (fun i => tokens[i]? = some "the")

theorem figure_F01 : tokens.length = 16 ∧ tokens.dedup.length = 14 ∧
    repetitions.map (· + 1) = [4,10,15] ∧ tokens.count "the" = 3 := by
  decide +kernel

theorem token_count_append (xs : List String) (w : String) :
    (xs ++ [w]).length = xs.length + 1 := by simp

theorem type_count_append (xs : List String) (w : String) :
    (xs ++ [w]).toFinset.card = xs.toFinset.card + (if w ∈ xs then 0 else 1) := by
  by_cases h : w ∈ xs
  · simp [List.toFinset_append, Finset.union_singleton, h]
  · simp [List.toFinset_append, Finset.union_singleton, h]

theorem repeated_type_inventory (xs : List String) (w : String) (hw : w ∈ xs) :
    (xs ++ [w]).length = xs.length + 1 ∧ (xs ++ [w]).toFinset.card = xs.toFinset.card := by
  constructor
  · exact token_count_append xs w
  · simpa [hw] using type_count_append xs w

theorem new_type_inventory (xs : List String) (w : String) (hw : w ∉ xs) :
    (xs ++ [w]).length = xs.length + 1 ∧ (xs ++ [w]).toFinset.card = xs.toFinset.card + 1 := by
  constructor
  · exact token_count_append xs w
  · simpa [hw] using type_count_append xs w

theorem figure_F01_punctuation : (tokens ++ [",", "."]).length = 18 := by decide +kernel

end Chapter01Exposition

#print axioms Chapter01Exposition.expected_count
#print axioms Chapter01Exposition.ttr_repeated_type
#print axioms Chapter01Exposition.ttr_repeated_type_strict
#print axioms Chapter01Exposition.ttr_new_type
#print axioms Chapter01Exposition.ttr_bounds
#print axioms Chapter01Exposition.normalization_scaling
#print axioms Chapter01Exposition.normalization_order
#print axioms Chapter01Exposition.figure_F01

#print axioms Chapter01Exposition.expected_count_finite_model

#print axioms Chapter01Exposition.type_count_append
#print axioms Chapter01Exposition.repeated_type_inventory
#print axioms Chapter01Exposition.new_type_inventory
#print axioms Chapter01Exposition.figure_F01_punctuation
