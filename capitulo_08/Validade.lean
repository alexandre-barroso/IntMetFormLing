import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open scoped BigOperators

namespace Chapter08Validity

noncomputable def partition {n : ℕ} (z : Fin n → ℝ) : ℝ := ∑ j, Real.exp (z j)
noncomputable def probability {n : ℕ} (z : Fin n → ℝ) (j : Fin n) : ℝ := Real.exp (z j) / partition z

theorem partition_positive {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) : 0 < partition z := by
  apply Finset.sum_pos'
  · intro j hj
    exact (Real.exp_pos _).le
  · exact ⟨⟨0,hn⟩, Finset.mem_univ _, Real.exp_pos _⟩

theorem softmax_valid {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    (∑ j, probability z j) = 1 ∧ ∀ j, 0 < probability z j ∧ probability z j ≤ 1 := by
  have hZ := partition_positive hn z
  constructor
  · simp only [probability, ← Finset.sum_div]
    exact div_self (ne_of_gt hZ)
  · intro j
    constructor
    · exact div_pos (Real.exp_pos _) hZ
    · apply (div_le_one hZ).2
      exact Finset.single_le_sum (fun k hk => (Real.exp_pos _).le) (Finset.mem_univ j)

theorem empty_partition : partition (fun i : Fin 0 => Fin.elim0 i) = 0 := by simp [partition]

theorem dimension_scale {d : ℕ} (hd : 0 < d) : 0 < Real.sqrt (d : ℝ) ∧ Real.sqrt (d : ℝ) ≠ 0 := by
  have h : 0 < (d : ℝ) := by exact_mod_cast hd
  exact ⟨Real.sqrt_pos.mpr h, ne_of_gt (Real.sqrt_pos.mpr h)⟩

noncomputable def scaledScores {n d : ℕ} (Q K : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => (Q * K.transpose) i j / Real.sqrt d
noncomputable def attention {n d v : ℕ} (Q K : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin n) (Fin v) ℝ) : Matrix (Fin n) (Fin v) ℝ := (show Matrix (Fin n) (Fin n) ℝ from fun i j => probability (scaledScores Q K i) j) * V

theorem attention_valid {n d v : ℕ} (hn : 0 < n) (hd : 0 < d)
    (Q K : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin n) (Fin v) ℝ) :
    0 < Real.sqrt (d : ℝ) ∧
    (∀ i, (∑ j, probability (scaledScores Q K i) j) = 1) ∧
    (∀ i j, 0 < probability (scaledScores Q K i) j ∧ probability (scaledScores Q K i) j ≤ 1) ∧
    (∀ i r, attention Q K V i r = ∑ j,
      (Real.exp ((∑ s, Q i s * K j s) / Real.sqrt d) /
       (∑ m, Real.exp ((∑ s, Q i s * K m s) / Real.sqrt d))) * V j r) := by
  refine ⟨(dimension_scale hd).1, ?_, ?_, ?_⟩
  · intro i
    exact (softmax_valid hn _).1
  · intro i j
    exact (softmax_valid hn _).2 j
  · intro i r
    rfl

theorem attention_convex_coordinate {n d v : ℕ} (hn : 0 < n)
    (Q K : Matrix (Fin n) (Fin d) ℝ) (V : Matrix (Fin n) (Fin v) ℝ)
    (i : Fin n) (r : Fin v) (lo hi : ℝ) (hV : ∀ j, lo ≤ V j r ∧ V j r ≤ hi) :
    lo ≤ attention Q K V i r ∧ attention Q K V i r ≤ hi := by
  have hs := (softmax_valid hn (scaledScores Q K i)).1
  have hp := (softmax_valid hn (scaledScores Q K i)).2
  change lo ≤ ∑ j, probability (scaledScores Q K i) j * V j r ∧
    (∑ j, probability (scaledScores Q K i) j * V j r) ≤ hi
  constructor
  · calc lo = (∑ j, probability (scaledScores Q K i) j) * lo := by rw [hs]; ring
         _ = ∑ j, probability (scaledScores Q K i) j * lo := Finset.sum_mul _ _ _
         _ ≤ _ := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hV j).1 (hp j).1.le)
  · calc (∑ j, probability (scaledScores Q K i) j * V j r) ≤ ∑ j, probability (scaledScores Q K i) j * hi :=
          Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hV j).2 (hp j).1.le)
         _ = (∑ j, probability (scaledScores Q K i) j) * hi := (Finset.sum_mul _ _ _).symm
         _ = hi := by rw [hs]; ring

noncomputable def projectedAttention {n d k v : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (WQ WK : Matrix (Fin d) (Fin k) ℝ) (WV : Matrix (Fin d) (Fin v) ℝ) : Matrix (Fin n) (Fin v) ℝ :=
    attention (X * WQ) (X * WK) (X * WV)

theorem projected_attention_entry {n d k v : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (WQ WK : Matrix (Fin d) (Fin k) ℝ) (WV : Matrix (Fin d) (Fin v) ℝ)
    (i : Fin n) (r : Fin v) :
    projectedAttention X WQ WK WV i r = ∑ j,
      probability (scaledScores (X * WQ) (X * WK) i) j * (∑ s, X j s * WV s r) := rfl

noncomputable def layer {d h : ℕ} (x : Fin d → ℝ) (W₁ : Matrix (Fin d) (Fin h) ℝ)
    (W₂ : Matrix (Fin h) (Fin d) ℝ) (b₁ : Fin h → ℝ) (b₂ : Fin d → ℝ) : Fin d → ℝ :=
    Matrix.vecMul (fun j => max 0 ((Matrix.vecMul x W₁ + b₁) j)) W₂ + b₂

theorem layer_composed_entry {d h : ℕ} (x : Fin d → ℝ) (W₁ : Matrix (Fin d) (Fin h) ℝ)
    (W₂ : Matrix (Fin h) (Fin d) ℝ) (b₁ : Fin h → ℝ) (b₂ : Fin d → ℝ) (k : Fin d) :
    layer x W₁ W₂ b₁ b₂ k = (∑ j, max 0 ((∑ r, x r * W₁ r j) + b₁ j) * W₂ j k) + b₂ k := rfl

noncomputable def laplace {v : ℕ} (counts : Fin v → ℕ) (j : Fin v) : ℝ :=
    (counts j + 1 : ℝ) / ((∑ k, (counts k : ℝ)) + v)

theorem laplace_valid {v : ℕ} (hv : 0 < v) (counts : Fin v → ℕ) :
    (∑ j, laplace counts j) = 1 ∧ ∀ j, 0 < laplace counts j ∧ laplace counts j ≤ 1 := by
  have hn : 0 < (∑ k, (counts k : ℝ)) + v := by positivity
  have hs : (∑ k : Fin v, ((counts k : ℝ) + 1)) = (∑ k, (counts k : ℝ)) + v := by simp [Finset.sum_add_distrib]
  constructor
  · simp only [laplace, ← Finset.sum_div, hs]
    exact div_self (ne_of_gt hn)
  · intro j
    constructor
    · exact div_pos (by positivity) hn
    · apply (div_le_one hn).2
      rw [← hs]
      exact Finset.single_le_sum (f := fun k : Fin v => (counts k : ℝ) + 1) (fun k hk => by positivity) (Finset.mem_univ j)

noncomputable def logLikelihood (p : ℝ) : ℝ := 608 * Real.log p + 319 * Real.log (1-p)
noncomputable def likelihood (p : ℝ) : ℝ := p^608 * (1-p)^319

theorem log_likelihood (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Real.log (likelihood p) = logLikelihood p := by
  rw [likelihood, Real.log_mul (pow_ne_zero _ hp.ne') (pow_ne_zero _ (sub_pos.mpr hp1).ne'), Real.log_pow, Real.log_pow]
  norm_num [logLikelihood]

theorem strict_log_maximum (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hne : p ≠ 608/927) :
    logLikelihood p < logLikelihood (608/927) := by
  have hA : 0 < p / (608/927 : ℝ) := by positivity
  have hB : 0 < (1-p) / (319/927 : ℝ) := by positivity
  have hneA : p / (608/927 : ℝ) ≠ 1 := by
    intro h
    apply hne
    linarith [(div_eq_one_iff_eq (by norm_num : (608/927 : ℝ) ≠ 0)).mp h]
  have ha := Real.log_lt_sub_one_of_pos hA hneA
  have hb := Real.log_le_sub_one_of_pos hB
  rw [Real.log_div hp.ne' (by norm_num)] at ha
  rw [Real.log_div (sub_pos.mpr hp1).ne' (by norm_num)] at hb
  norm_num [logLikelihood] at *
  linarith

theorem unique_likelihood_maximum (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    likelihood p ≤ likelihood (608/927) ∧
    (likelihood p = likelihood (608/927) ↔ p = 608/927) := by
  have hq : 0 < likelihood (608/927) := by unfold likelihood; positivity
  by_cases hp0 : p = 0
  · subst p
    norm_num [likelihood] at *
  by_cases hpOne : p = 1
  · subst p
    norm_num [likelihood] at *
  by_cases heq : p = 608/927
  · subst p
    exact ⟨le_rfl, by simp⟩
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hp1' : p < 1 := lt_of_le_of_ne hp1 hpOne
  have hpos : 0 < likelihood p := mul_pos (pow_pos hp' _) (pow_pos (sub_pos.mpr hp1') _)
  have hl := strict_log_maximum p hp' hp1' heq
  rw [← log_likelihood p hp' hp1', ← log_likelihood (608/927) (by norm_num) (by norm_num)] at hl
  have hlt : likelihood p < likelihood (608/927) := (Real.log_lt_log_iff hpos hq).mp hl
  exact ⟨hlt.le, by constructor; intro h; exact False.elim (hlt.ne h); intro h; exact False.elim (heq h)⟩

noncomputable def brier {n k : ℕ} (hn : 0 < n) (p : Matrix (Fin n) (Fin k) ℝ)
    (truth : Fin n → Fin k) : ℝ :=
    (∑ i, ∑ j, (p i j - (if j = truth i then 1 else 0))^2) / n

theorem brier_nonnegative {n k : ℕ} (hn : 0 < n) (p : Matrix (Fin n) (Fin k) ℝ)
    (truth : Fin n → Fin k) : 0 ≤ brier hn p truth := by
  unfold brier
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg _))
  · positivity

theorem brier_probability_domain {n k : ℕ} (p : Matrix (Fin n) (Fin k) ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (hs : ∀ i, ∑ j, p i j = 1) : ∀ i j, p i j ≤ 1 := by
  intro i j
  rw [← hs i]
  exact Finset.single_le_sum (fun r hr => hp i r) (Finset.mem_univ j)

#print axioms brier_nonnegative
#print axioms brier_probability_domain

#print axioms softmax_valid
#print axioms attention_valid
#print axioms attention_convex_coordinate
#print axioms projected_attention_entry
#print axioms layer_composed_entry
#print axioms laplace_valid
#print axioms unique_likelihood_maximum

end Chapter08Validity
