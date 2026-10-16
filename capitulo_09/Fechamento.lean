import Mathlib

open scoped BigOperators
namespace Chapter09Closure

noncomputable def safeF1 (tp fp fn : ℝ) : Option ℝ :=
  if 0 < 2*tp+fp+fn then some (2*tp/(2*tp+fp+fn)) else none

theorem f1_range (tp fp fn : ℝ) (ht : 0 ≤ tp) (hf : 0 ≤ fp) (hn : 0 ≤ fn)
    (hd : 0 < 2*tp+fp+fn) : 0 ≤ 2*tp/(2*tp+fp+fn) ∧ 2*tp/(2*tp+fp+fn) ≤ 1 := by
  constructor
  · exact div_nonneg (by linarith) hd.le
  · apply (div_le_one hd).mpr
    linarith

theorem safe_f1_valid (tp fp fn score : ℝ) (ht : 0 ≤ tp) (hf : 0 ≤ fp) (hn : 0 ≤ fn)
    (h : safeF1 tp fp fn = some score) :
    0 < 2*tp+fp+fn ∧ score = 2*tp/(2*tp+fp+fn) ∧ 0 ≤ score ∧ score ≤ 1 := by
  unfold safeF1 at h
  split_ifs at h with hd
  · have he := Option.some.inj h
    subst score
    exact ⟨hd, rfl, f1_range tp fp fn ht hf hn hd⟩

theorem zero_true_positives (fp fn : ℝ) (h : 0 < fp+fn) : safeF1 0 fp fn = some 0 := by
  simp [safeF1, h]

theorem empty_counts_undefined : safeF1 0 0 0 = none := by norm_num [safeF1]

theorem macro_f1_range {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ (∑ i, f i) / n ∧ (∑ i, f i) / n ≤ 1 := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => (hf i).1)) hnr.le
  · apply (div_le_one hnr).mpr
    calc (∑ i, f i) ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hf i).2)
      _ = n := by simp

end Chapter09Closure

#print axioms Chapter09Closure.f1_range
#print axioms Chapter09Closure.safe_f1_valid
#print axioms Chapter09Closure.zero_true_positives
#print axioms Chapter09Closure.empty_counts_undefined
#print axioms Chapter09Closure.macro_f1_range
