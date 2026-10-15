import capitulo_06.Expressoes

namespace Chapter07Bootstrap

open Chapter06Expressions
open scoped BigOperators

def binaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (binaryWords n).map (false::·) ++ (binaryWords n).map (true::·)

def ones : List Bool → ℕ
  | [] => 0
  | false::w => ones w
  | true::w => ones w+1

noncomputable def sequenceWeight (p : ℝ) : List Bool → ℝ
  | [] => 1
  | false::w => (1-p)*sequenceWeight p w
  | true::w => p*sequenceWeight p w

noncomputable def sequenceSum (n : ℕ) (p : ℝ) (f : ℕ → ℝ) : ℝ :=
  ((binaryWords n).map (fun w=>sequenceWeight p w*f (ones w))).sum

theorem binary_words_complete (n : ℕ) (w : List Bool) : w∈binaryWords n ↔ w.length=n := by
  induction n generalizing w with
  | zero => simp [binaryWords]
  | succ n ih =>
      cases w with
      | nil => simp [binaryWords]
      | cons bit w =>
          cases bit <;> simp [binaryWords,ih]

theorem binary_words_unique (n : ℕ) : (binaryWords n).Nodup := by
  induction n with
  | zero => simp [binaryWords]
  | succ n ih =>
      unfold binaryWords
      apply List.Nodup.append
      · exact ih.map (fun x y h=>List.cons.inj h |>.2)
      · exact ih.map (fun x y h=>List.cons.inj h |>.2)
      · apply List.disjoint_left.mpr
        intro w hw hw'
        obtain ⟨x,hx,hxe⟩ := List.mem_map.mp hw
        obtain ⟨y,hy,hye⟩ := List.mem_map.mp hw'
        have h := hxe.trans hye.symm
        cases List.cons.inj h |>.1

theorem weighted_sum_scale (l : List (List Bool)) (a : ℝ) (f : List Bool → ℝ) :
    (l.map (fun w=>a*f w)).sum=a*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons w l ih => simp [ih,mul_add]

theorem sequence_sum_succ (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    sequenceSum (n+1) p f=(1-p)*sequenceSum n p f+p*sequenceSum n p (fun k=>f (k+1)) := by
  simp only [sequenceSum,binaryWords,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  simp only [sequenceWeight,ones]
  simp_rw [mul_assoc]
  rw [weighted_sum_scale,weighted_sum_scale]

theorem sequence_sum_eq_binomial (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    sequenceSum n p f=binomialSum n p f := by
  induction n generalizing f with
  | zero => simp [sequenceSum,binaryWords,sequenceWeight,ones,binomialSum]
  | succ n ih =>
      rw [sequence_sum_succ,binomial_sum_succ,ih f,ih (fun k=>f (k+1))]
      ring

noncomputable def countMass (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  sequenceSum n p (fun j=>if j=k then 1 else 0)

theorem count_mass_succ (n k : ℕ) (p : ℝ) :
    countMass (n+1) p (k+1)=(1-p)*countMass n p (k+1)+p*countMass n p k := by
  simp only [countMass,sequence_sum_succ,Nat.add_right_cancel_iff]

theorem count_mass_zero_succ (n : ℕ) (p : ℝ) :
    countMass (n+1) p 0=(1-p)*countMass n p 0 := by
  simp only [countMass,sequence_sum_succ,Nat.add_one_ne_zero,ite_false]
  simp [sequenceSum]

theorem count_mass_formula (n k : ℕ) (p : ℝ) (hk : k≤n) :
    countMass n p k=binomialProbability n p k := by
  rw [countMass,sequence_sum_eq_binomial]
  unfold binomialSum binomialProbability
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [hjk]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem sequence_mean (b : ℕ) (p : ℝ) (hb : 0<b) :
    sequenceSum b p (fun k=>(k:ℝ)/(b:ℝ))=p := by
  rw [sequence_sum_eq_binomial]
  have hbn : (b:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hb
  have he : (fun k : ℕ=>(k:ℝ)/(b:ℝ))=(fun k : ℕ=>(1/(b:ℝ))*(k:ℝ)+0*1) := by
    funext k
    ring
  rw [he,binomial_sum_linear,binomial_mean,binomial_total]
  field_simp <;> ring

noncomputable def averageMean (b : ℕ) (p : ℝ) : ℝ :=
  binomialSum b p (fun k=>(k:ℝ)/(b:ℝ))

noncomputable def averageVariance (b : ℕ) (p : ℝ) : ℝ :=
  binomialSum b p (fun k=>((k:ℝ)/(b:ℝ)-p)^2)

theorem count_distribution_valid (b : ℕ) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    (∀k,0≤binomialProbability b p k) ∧
      (∑k∈Finset.range (b+1),binomialProbability b p k)=1 := by
  exact ⟨fun k=>binomial_probability_nonnegative b k p hp hp1,binomial_probability_total b p⟩

theorem average_mean (b : ℕ) (p : ℝ) (hb : 0<b) : averageMean b p=p := by
  have hbn : (b:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hb
  have he : (fun k : ℕ=>(k:ℝ)/(b:ℝ))=(fun k : ℕ=>(1/(b:ℝ))*(k:ℝ)+0*1) := by
    funext k
    ring
  unfold averageMean
  rw [he,binomial_sum_linear,binomial_mean,binomial_total]
  field_simp <;> ring

theorem average_variance (b : ℕ) (p : ℝ) (hb : 0<b) :
    averageVariance b p=p*(1-p)/(b:ℝ) := by
  have hbn : (b:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hb
  have he : (fun k : ℕ=>((k:ℝ)/(b:ℝ)-p)^2)=
      (fun k : ℕ=>(1/(b:ℝ)^2)*((k:ℝ)-(b:ℝ)*p)^2+0*1) := by
    funext k
    field_simp <;> ring
  unfold averageVariance
  rw [he,binomial_sum_linear,binomial_variance,binomial_total]
  field_simp <;> ring

theorem sequence_average_variance (b : ℕ) (p : ℝ) (hb : 0<b) :
    sequenceSum b p (fun k=>((k:ℝ)/(b:ℝ)-p)^2)=p*(1-p)/(b:ℝ) := by
  rw [sequence_sum_eq_binomial]
  exact average_variance b p hb

theorem average_variance_nonnegative (b : ℕ) (p : ℝ) (hb : 0<b)
    (hp : 0≤p) (hp1 : p≤1) : 0≤averageVariance b p := by
  rw [average_variance b p hb]
  exact div_nonneg (mul_nonneg hp (sub_nonneg.mpr hp1)) (Nat.cast_nonneg b)

theorem variance_decrease_exact (b₁ b₂ : ℕ) (p : ℝ) (h₁ : 0<b₁) (h₂ : 0<b₂) :
    averageVariance b₁ p-averageVariance b₂ p=
      p*(1-p)*((b₂:ℝ)-(b₁:ℝ))/((b₁:ℝ)*(b₂:ℝ)) := by
  rw [average_variance b₁ p h₁,average_variance b₂ p h₂]
  have hn₁ : (b₁:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt h₁
  have hn₂ : (b₂:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt h₂
  field_simp <;> ring

theorem variance_antitone (b₁ b₂ : ℕ) (p : ℝ) (h₁ : 0<b₁) (h₁₂ : b₁≤b₂)
    (hp : 0≤p) (hp1 : p≤1) : averageVariance b₂ p≤averageVariance b₁ p := by
  have h₂ : 0<b₂ := lt_of_lt_of_le h₁ h₁₂
  rw [average_variance b₁ p h₁,average_variance b₂ p h₂]
  have hr₁ : (0:ℝ)<b₁ := by exact_mod_cast h₁
  have hr₂ : (0:ℝ)<b₂ := by exact_mod_cast h₂
  have hr₁₂ : (b₁:ℝ)≤b₂ := by exact_mod_cast h₁₂
  have hnum : 0≤p*(1-p) := mul_nonneg hp (sub_nonneg.mpr hp1)
  apply (div_le_div_iff₀ hr₂ hr₁).2
  nlinarith

theorem variance_strict_decrease (b₁ b₂ : ℕ) (p : ℝ) (h₁ : 0<b₁) (h₁₂ : b₁<b₂)
    (hp : 0<p) (hp1 : p<1) : averageVariance b₂ p<averageVariance b₁ p := by
  have h₂ : 0<b₂ := lt_trans h₁ h₁₂
  rw [average_variance b₁ p h₁,average_variance b₂ p h₂]
  have hr₁ : (0:ℝ)<b₁ := by exact_mod_cast h₁
  have hr₂ : (0:ℝ)<b₂ := by exact_mod_cast h₂
  have hr₁₂ : (b₁:ℝ)<b₂ := by exact_mod_cast h₁₂
  have hnum : 0<p*(1-p) := mul_pos hp (sub_pos.mpr hp1)
  apply (div_lt_div_iff₀ hr₂ hr₁).2
  nlinarith

theorem endpoint_variance_zero (b : ℕ) (hb : 0<b) :
    averageVariance b 0=0 ∧ averageVariance b 1=0 := by
  rw [average_variance b 0 hb,average_variance b 1 hb]
  norm_num

theorem dependent_repetitions_counterexample :
    (1/2:ℝ)*(0-1/2)^2+(1/2)*(1-1/2)^2=1/4 ∧
      (1/4:ℝ)≠((1/2)*(1-1/2))/2 := by norm_num

#print axioms binary_words_complete
#print axioms binary_words_unique
#print axioms sequence_sum_succ
#print axioms sequence_sum_eq_binomial
#print axioms count_mass_formula
#print axioms sequence_mean
#print axioms sequence_average_variance
#print axioms count_distribution_valid
#print axioms average_mean
#print axioms average_variance
#print axioms variance_antitone
#print axioms variance_strict_decrease
#print axioms endpoint_variance_zero
#print axioms dependent_repetitions_counterexample

end Chapter07Bootstrap
