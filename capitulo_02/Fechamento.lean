import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Chapter02Closure

theorem addition_preserves_strict_order (u v k : ℝ) (h : u < v) :
    u + k < v + k := by linarith

theorem addition_preserves_weak_order (u v k : ℝ) (h : u ≤ v) :
    u + k ≤ v + k := by linarith

theorem positive_scaling_preserves_strict_order (u v k : ℝ) (h : u < v) (hk : 0 < k) :
    k * u < k * v := mul_lt_mul_of_pos_left h hk

theorem positive_scaling_preserves_weak_order (u v k : ℝ) (h : u ≤ v) (hk : 0 < k) :
    k * u ≤ k * v := mul_le_mul_of_nonneg_left h hk.le

theorem negative_scaling_reverses_strict_order (u v k : ℝ) (h : u < v) (hk : k < 0) :
    k * v < k * u := mul_lt_mul_of_neg_left h hk

theorem negative_scaling_reverses_weak_order (u v k : ℝ) (h : u ≤ v) (hk : k < 0) :
    k * v ≤ k * u := mul_le_mul_of_nonpos_left h hk.le

theorem decreasing_exponential (A lam x y : ℝ) (hA : 0 < A) (hl : 0 < lam)
    (hxy : x < y) : A * Real.exp (-lam * y) < A * Real.exp (-lam * x) := by
  apply mul_lt_mul_of_pos_left _ hA
  apply Real.exp_lt_exp.mpr
  nlinarith

theorem growing_exponential_factor (c x y : ℝ) (hc : c < 0) (hxy : x < y) :
    Real.exp (-c * x) < Real.exp (-c * y) := by
  apply Real.exp_lt_exp.mpr
  nlinarith

theorem negative_parameter_argument (c n : ℝ) (hc : c < 0) (hn : 0 < n) :
    0 < -c * n := mul_pos (neg_pos.mpr hc) hn

theorem derivative_constant (c x : ℝ) : HasDerivAt (fun _ : ℝ => c) 0 x :=
  hasDerivAt_const x c

theorem derivative_sum (f g : ℝ → ℝ) (df dg x : ℝ)
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun u => f u + g u) (df + dg) x := hf.add hg

theorem derivative_constant_factor (f : ℝ → ℝ) (df c x : ℝ)
    (hf : HasDerivAt f df x) : HasDerivAt (fun u => c * f u) (c * df) x :=
  hf.const_mul c

theorem derivative_composition (f g : ℝ → ℝ) (df dg x : ℝ)
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg (f x)) :
    HasDerivAt (fun u => g (f u)) (dg * df) x := hg.comp x hf

theorem probability_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) :
    0 ≤ μ.real s ∧ μ.real s ≤ 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

theorem probability_disjoint_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s t : Set Ω)
    (ht : MeasurableSet t) (hd : Disjoint s t) :
    μ.real (s ∪ t) = μ.real s + μ.real t ∧ 0 ≤ μ.real s + μ.real t ∧
      μ.real s + μ.real t ≤ 1 := by
  have he : μ.real (s ∪ t) = μ.real s + μ.real t := measureReal_union hd ht
  exact ⟨he, he ▸ measureReal_nonneg, he ▸ measureReal_le_one⟩

theorem probability_finite_disjoint_union {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : ι → Set Ω)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    μ.real (⋃ i, s i) = ∑ i, μ.real (s i) ∧
      0 ≤ ∑ i, μ.real (s i) ∧ (∑ i, μ.real (s i)) ≤ 1 := by
  have he : μ.real (⋃ i, s i) = ∑ i, μ.real (s i) := measureReal_iUnion_fintype hd hs
  exact ⟨he, he ▸ measureReal_nonneg, he ▸ measureReal_le_one⟩

theorem density_event_bounds (f : ℝ → ℝ) (hf : Integrable f)
    (hn : ∀ x, 0 ≤ f x) (htotal : (∫ x, f x) = 1) (s : Set ℝ) :
    0 ≤ (∫ x in s, f x) ∧ (∫ x in s, f x) ≤ 1 := by
  constructor
  · exact integral_nonneg hn
  · rw [← htotal]
    exact setIntegral_le_integral hf (Filter.Eventually.of_forall hn)

theorem density_disjoint_events (f : ℝ → ℝ) (hf : Integrable f)
    (hn : ∀ x, 0 ≤ f x) (htotal : (∫ x, f x) = 1)
    (s t : Set ℝ) (ht : MeasurableSet t) (hd : Disjoint s t) :
    (∫ x in s ∪ t, f x) = (∫ x in s, f x) + (∫ x in t, f x) ∧
      0 ≤ (∫ x in s, f x) + (∫ x in t, f x) ∧
      (∫ x in s, f x) + (∫ x in t, f x) ≤ 1 := by
  have he : (∫ x in s ∪ t, f x) = (∫ x in s, f x) + (∫ x in t, f x) :=
    setIntegral_union hd ht hf.integrableOn hf.integrableOn
  obtain ⟨hl, hu⟩ := density_event_bounds f hf hn htotal (s ∪ t)
  exact ⟨he, he ▸ hl, he ▸ hu⟩

theorem density_finite_disjoint_events {ι : Type*} [Fintype ι]
    (f : ℝ → ℝ) (hf : Integrable f) (hn : ∀ x, 0 ≤ f x)
    (htotal : (∫ x, f x) = 1) (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∫ x in ⋃ i, s i, f x) = ∑ i, ∫ x in s i, f x ∧
      0 ≤ (∑ i, ∫ x in s i, f x) ∧ (∑ i, ∫ x in s i, f x) ≤ 1 := by
  have he : (∫ x in ⋃ i, s i, f x) = ∑ i, ∫ x in s i, f x :=
    integral_iUnion_fintype hs hd (fun _ => hf.integrableOn)
  obtain ⟨hl, hu⟩ := density_event_bounds f hf hn htotal (⋃ i, s i)
  exact ⟨he, he ▸ hl, he ▸ hu⟩

end Chapter02Closure

#print axioms Chapter02Closure.addition_preserves_strict_order
#print axioms Chapter02Closure.addition_preserves_weak_order
#print axioms Chapter02Closure.positive_scaling_preserves_strict_order
#print axioms Chapter02Closure.positive_scaling_preserves_weak_order
#print axioms Chapter02Closure.negative_scaling_reverses_strict_order
#print axioms Chapter02Closure.negative_scaling_reverses_weak_order
#print axioms Chapter02Closure.decreasing_exponential
#print axioms Chapter02Closure.growing_exponential_factor
#print axioms Chapter02Closure.negative_parameter_argument
#print axioms Chapter02Closure.derivative_constant
#print axioms Chapter02Closure.derivative_sum
#print axioms Chapter02Closure.derivative_constant_factor
#print axioms Chapter02Closure.derivative_composition
#print axioms Chapter02Closure.probability_bounds
#print axioms Chapter02Closure.probability_disjoint_union
#print axioms Chapter02Closure.probability_finite_disjoint_union
#print axioms Chapter02Closure.density_event_bounds
#print axioms Chapter02Closure.density_disjoint_events
#print axioms Chapter02Closure.density_finite_disjoint_events
