import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open scoped BigOperators

namespace Chapter02Expressions

def keep (c : ℕ) : ℕ := if c ≤ 5 then 0 else 1

theorem keep_cases (c : ℕ) :
    (keep c = 0 ↔ c ≤ 5) ∧ (keep c = 1 ↔ c > 5) := by
  by_cases h : c ≤ 5 <;> simp [keep, h] <;> omega

theorem affine_difference (m L₁ L₂ : ℝ) :
    m*L₂-m*L₁ = m*(L₂-L₁) := by ring

theorem finite_rate (m L₁ L₂ : ℝ) (h : L₂ ≠ L₁) :
    (m*L₂-m*L₁)/(L₂-L₁) = m := by
  rw [affine_difference]
  exact mul_div_cancel_right₀ m (sub_ne_zero.mpr h)

theorem linear_increment_steps (m L h : ℝ) (hh : h ≠ 0) :
    (m*(L+h)-m*L)/h = (m*L+m*h-m*L)/h ∧
    (m*L+m*h-m*L)/h = (m*h)/h ∧ (m*h)/h = m := by
  constructor
  · ring
  constructor
  · ring
  · exact mul_div_cancel_right₀ m hh

theorem power_product (u v : ℝ) : (2:ℝ)^(u+v) = (2:ℝ)^u * (2:ℝ)^v :=
  Real.rpow_add (by norm_num) u v

theorem logarithm_base_conversion (x : ℝ) : Real.logb 2 x = Real.log x / Real.log 2 := rfl

theorem logarithm_inverse (x : ℝ) (hx : 0 < x) :
    (2:ℝ)^(Real.logb 2 x) = x := Real.rpow_logb (by norm_num) (by norm_num) hx

theorem logarithm_product (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb 2 (x*y) = Real.logb 2 x + Real.logb 2 y :=
  Real.logb_mul (ne_of_gt hx) (ne_of_gt hy)

theorem logarithm_quotient (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb 2 (x/y) = Real.logb 2 x - Real.logb 2 y :=
  Real.logb_div (ne_of_gt hx) (ne_of_gt hy)

theorem logarithm_power (x v : ℝ) (hx : 0 < x) :
    Real.logb 2 (x^v) = v*Real.logb 2 x := Real.logb_rpow_eq_mul_logb_of_pos hx

theorem association_logarithm_bounds :
    (197/20 : ℝ) < Real.logb 2 (119275347/128700) ∧
    Real.logb 2 (119275347/128700) < (199/20 : ℝ) := by
  have hl : (2:ℝ)^197 < (119275347/128700:ℝ)^20 := by norm_num
  have hu : (119275347/128700:ℝ)^20 < (2:ℝ)^199 := by norm_num
  have hl' := Real.logb_lt_logb (b:=2) (by norm_num) (by positivity) hl
  have hu' := Real.logb_lt_logb (b:=2) (by norm_num) (by positivity) hu
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hl' hu'
  constructor <;> linarith

theorem association_logarithm_order :
    9 < Real.logb 2 (119275347/128700) ∧ Real.logb 2 (119275347/128700) < 10 := by
  rcases association_logarithm_bounds with ⟨hl,hu⟩
  constructor <;> linarith

noncomputable def mal (a b c n : ℝ) : ℝ := a*n^b*Real.exp (-c*n)

theorem mal_logarithm (a b c n : ℝ) (ha : 0 < a) (hn : 0 < n) :
    Real.log (mal a b c n) = Real.log a + b*Real.log n-c*n := by
  unfold mal
  rw [Real.log_mul (ne_of_gt (mul_pos ha (Real.rpow_pos_of_pos hn b))) (Real.exp_ne_zero _)]
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.rpow_pos_of_pos hn b)), Real.log_rpow hn, Real.log_exp]
  ring

theorem mal_derivative_original (a b c n : ℝ) (hn : 0 < n) :
    HasDerivAt (fun x : ℝ => mal a b c x) (mal a b c n*(b/n-c)) n := by
  have hp := (Real.hasDerivAt_rpow_const (p:=b) (Or.inl (ne_of_gt hn))).const_mul a
  have he := (((hasDerivAt_id n).const_mul c).neg).exp
  convert! hp.mul he using 1
  · ext x
    simp [mal, neg_mul]
  · rw [Real.rpow_sub hn, Real.rpow_one]
    unfold mal
    simp only [neg_mul, Pi.neg_apply, id_eq]
    ring

theorem mal_logarithmic_rate (a b c n : ℝ) (ha : 0 < a) (hn : 0 < n) :
    (mal a b c n*(b/n-c))/mal a b c n = b/n-c := by
  have h : mal a b c n ≠ 0 := ne_of_gt (mul_pos (mul_pos ha (Real.rpow_pos_of_pos hn b)) (Real.exp_pos _))
  exact mul_div_cancel_left₀ _ h

theorem derivative_sign_before (b c n : ℝ) (hc : c < 0) (hn : 0 < n) (h : n < b/c) :
    b/n-c < 0 := by
  have hbc : b < n*c := (lt_div_iff_of_neg hc).mp h
  apply sub_neg.mpr
  apply (div_lt_iff₀ hn).mpr
  nlinarith

theorem derivative_sign_after (b c n : ℝ) (hc : c < 0) (hn : 0 < n) (h : b/c < n) :
    0 < b/n-c := by
  have hbc : n*c < b := (div_lt_iff_of_neg hc).mp h
  apply sub_pos.mpr
  apply (lt_div_iff₀ hn).mpr
  nlinarith

theorem inverse_rate_sign (d y : ℝ) (hy : y ≠ 0) :
    (0 < -d/y^2 ↔ d < 0) ∧ (-d/y^2 < 0 ↔ 0 < d) := by
  have hs : 0 < y^2 := sq_pos_of_ne_zero hy
  constructor
  · rw [div_pos_iff_of_pos_right hs]
    constructor <;> intro h <;> linarith
  · rw [div_lt_iff₀ hs]
    constructor <;> intro h <;> linarith

theorem reciprocal_steps (u h : ℝ) (hu : u ≠ 0) (hh : h ≠ 0) (huh : u+h ≠ 0) :
    (1/(u+h)-1/u)/h = (u-(u+h))/(u*(u+h)*h) ∧
    (u-(u+h))/(u*(u+h)*h) = -h/(u*(u+h)*h) ∧
    -h/(u*(u+h)*h) = -1/(u*(u+h)) := by
  constructor
  · field_simp <;> ring
  constructor
  · ring
  · field_simp

theorem equal_partition_sum (N : ℕ) (hN : 0 < N) (m L : ℝ) :
    (∑ _j : Fin N, m*(L/N)) = (N:ℝ)*m*(L/N) ∧
    (∑ _j : Fin N, m*(L/N)) = m*L := by
  have h : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  constructor
  · simp
    ring
  · simp
    field_simp

theorem decreasing_reading_time (b p : ℝ) (hb : 0 < b) (hp : 0 < p) :
    -b/(p*Real.log 2) < 0 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hb) (mul_pos hp hl)

theorem zipf_logarithm (C r alpha : ℝ) (hC : 0<C) (hr : 0<r) :
    Real.log (C*r^(-alpha))=Real.log C-alpha*Real.log r := by
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hr _)),Real.log_rpow hr]
  ring

theorem frequency_duration_logarithm (A lambda ell : ℝ) (hA : 0<A) :
    Real.log (A*Real.exp (-lambda*ell))=Real.log A-lambda*ell := by
  rw [Real.log_mul (ne_of_gt hA) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
  ring

theorem frequency_duration_composition (A C r alpha lambda ell : ℝ)
    (hA : 0<A) (hC : 0<C) (hr : 0<r) (hlambda : lambda≠0)
    (h : A*Real.exp (-lambda*ell)=C*r^(-alpha)) :
    ell=(alpha/lambda)*Real.log r+(Real.log A-Real.log C)/lambda := by
  have hh := congrArg Real.log h
  rw [frequency_duration_logarithm A lambda ell hA,zipf_logarithm C r alpha hC hr] at hh
  field_simp
  nlinarith

#print axioms zipf_logarithm
#print axioms frequency_duration_logarithm
#print axioms frequency_duration_composition

end Chapter02Expressions

#print axioms Chapter02Expressions.keep_cases
#print axioms Chapter02Expressions.affine_difference
#print axioms Chapter02Expressions.finite_rate
#print axioms Chapter02Expressions.linear_increment_steps
#print axioms Chapter02Expressions.power_product
#print axioms Chapter02Expressions.logarithm_base_conversion
#print axioms Chapter02Expressions.logarithm_inverse
#print axioms Chapter02Expressions.logarithm_product
#print axioms Chapter02Expressions.logarithm_quotient
#print axioms Chapter02Expressions.logarithm_power
#print axioms Chapter02Expressions.association_logarithm_bounds
#print axioms Chapter02Expressions.association_logarithm_order
#print axioms Chapter02Expressions.mal_logarithm
#print axioms Chapter02Expressions.mal_derivative_original
#print axioms Chapter02Expressions.mal_logarithmic_rate
#print axioms Chapter02Expressions.derivative_sign_before
#print axioms Chapter02Expressions.derivative_sign_after
#print axioms Chapter02Expressions.inverse_rate_sign
#print axioms Chapter02Expressions.reciprocal_steps
#print axioms Chapter02Expressions.equal_partition_sum
#print axioms Chapter02Expressions.decreasing_reading_time
