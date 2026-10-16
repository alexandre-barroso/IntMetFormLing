import Mathlib
import capitulo_06.Figuras
import capitulo_06.Verificar
import capitulo_02.SomasRiemann
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open MeasureTheory Filter
open scoped BigOperators Topology Interval
namespace Chapter06Area
noncomputable def polynomial (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 12, (-1/2 : ℝ)^k / k.factorial * x^(2*k)
noncomputable def integrated (a b : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 12, (-1/2 : ℝ)^k / k.factorial * ((b^(2*k+1)-a^(2*k+1))/(2*k+1))
lemma polynomial_continuous : Continuous polynomial := by
  unfold polynomial
  fun_prop
lemma polynomial_integral (a b : ℝ) : (∫ x in a..b, polynomial x)=integrated a b := by
  unfold polynomial integrated
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul,integral_pow]
    push_cast
    rfl
  · intro k hk
    exact (by fun_prop : Continuous (fun x : ℝ => (-1/2 : ℝ)^k / k.factorial * x^(2*k))).intervalIntegrable a b
lemma polynomial_error (x : ℝ) (hx : |x|≤141/100) :
    |Real.exp (-x^2/2)-polynomial x|≤13/((12:ℕ).factorial*12) := by
  have hs : x^2≤(141/100 : ℝ)^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) (by norm_num)).mpr hx
  have he : |-x^2/2|≤1 := by rw [abs_of_nonpos (by nlinarith [sq_nonneg x] : -x^2/2≤0)]; nlinarith [sq_nonneg x]
  have h:=Real.exp_bound he (by norm_num : 0<12)
  have hp : |-x^2/2|^12≤1 := pow_le_one₀ (abs_nonneg _) he
  have hid : (∑ k ∈ Finset.range 12, (-x^2/2)^k / k.factorial)=polynomial x := by
    unfold polynomial
    apply Finset.sum_congr rfl
    intro k hk
    rw [show -x^2/2=(-1/2 : ℝ)*x^2 by ring,mul_pow,←pow_mul]
    ring
  rw [hid] at h
  calc
    _≤|-x^2/2|^12*((13 : ℝ)/((12:ℕ).factorial*12)) := by simpa using h
    _≤1*((13 : ℝ)/((12:ℕ).factorial*12)) := mul_le_mul_of_nonneg_right hp (by positivity)
    _=_ := by ring
lemma gaussian_integral_bounds (a b : ℝ) (hab:a≤b)
    (ha:-(141/100 : ℝ)≤a) (hb:b≤141/100) :
    integrated a b-(b-a)*(13/((12:ℕ).factorial*12))≤(∫ x in a..b,Real.exp (-x^2/2)) ∧
    (∫ x in a..b,Real.exp (-x^2/2))≤ integrated a b+(b-a)*(13/((12:ℕ).factorial*12)) := by
  have hh:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b)
    (f:=fun x : ℝ => Real.exp (-x^2/2)-polynomial x) (C:=13/((12:ℕ).factorial*12)) (by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      rw [Real.norm_eq_abs]
      exact polynomial_error x (abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩))
  rw [intervalIntegral.integral_sub (by exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x^2/2))).intervalIntegrable a b) (polynomial_continuous.intervalIntegrable a b),polynomial_integral,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  rcases abs_le.mp hh with ⟨hl,hu⟩
  constructor <;> linarith
noncomputable def za : ℝ := (Real.log (3/100)+268/100)/(59/100)
noncomputable def zb : ℝ := (Real.log (14/100)+268/100)/(59/100)
lemma transformed_limits :
    (-1400945589/1000000000 : ℝ)<za ∧ za< -1400945588/1000000000 ∧
    (1209978209/1000000000 : ℝ)<zb ∧ zb<1209978210/1000000000 := by
  have hl:=Chapter06Figures.log_t0
  have hu:=Chapter06Figures.log_t1
  unfold za zb
  constructor
  · apply (lt_div_iff₀ (by norm_num)).mpr;linarith
  constructor
  · apply (div_lt_iff₀ (by norm_num)).mpr;linarith
  constructor
  · apply (lt_div_iff₀ (by norm_num)).mpr;linarith
  · apply (div_lt_iff₀ (by norm_num)).mpr;norm_num at hu;linarith
lemma inner_integral_lower :
    (20209469/10000000 : ℝ)<∫ x in (-1400945588/1000000000 : ℝ)..(1209978209/1000000000 : ℝ), Real.exp (-x^2/2) := by
  have h:=(gaussian_integral_bounds (-1400945588/1000000000) (1209978209/1000000000) (by norm_num) (by norm_num) (by norm_num)).1
  have hn : (20209469/10000000 : ℝ)< integrated (-1400945588/1000000000) (1209978209/1000000000)-((1209978209/1000000000 : ℝ)-(-1400945588/1000000000))*(13/((12:ℕ).factorial*12)) := by
    norm_num [integrated,Finset.sum_range_succ,Nat.factorial]
  exact lt_of_lt_of_le hn h
lemma outer_integral_upper :
    (∫ x in (-1400945589/1000000000 : ℝ)..(1209978210/1000000000 : ℝ), Real.exp (-x^2/2))<(20209471/10000000 : ℝ) := by
  have h:=(gaussian_integral_bounds (-1400945589/1000000000) (1209978210/1000000000) (by norm_num) (by norm_num) (by norm_num)).2
  have hn : integrated (-1400945589/1000000000) (1209978210/1000000000)+((1209978210/1000000000 : ℝ)-(-1400945589/1000000000))*(13/((12:ℕ).factorial*12))<(20209471/10000000 : ℝ) := by
    norm_num [integrated,Finset.sum_range_succ,Nat.factorial]
  exact lt_of_le_of_lt h hn
lemma standardized_area_bounds :
    (8062405/10000000 : ℝ)<(∫ x in za..zb,Chapter06.c06_p03.g x) ∧
    (∫ x in za..zb,Chapter06.c06_p03.g x)<(8062415/10000000 : ℝ) := by
  have hz:=transformed_limits
  have hc : Continuous (fun x : ℝ=>Real.exp (-x^2/2)) := by fun_prop
  have hi:= intervalIntegral.integral_mono_interval (μ:=volume) (f:=fun x : ℝ=>Real.exp (-x^2/2))
    (c:=za) (a:=(-1400945588/1000000000 : ℝ)) (b:=(1209978209/1000000000 : ℝ)) (d:=zb)
    (le_of_lt hz.2.1) (by norm_num) (le_of_lt hz.2.2.1)
    (Filter.Eventually.of_forall (fun x=>le_of_lt (Real.exp_pos _))) (hc.intervalIntegrable za zb)
  have ho:= intervalIntegral.integral_mono_interval (μ:=volume) (f:=fun x : ℝ=>Real.exp (-x^2/2))
    (c:=(-1400945589/1000000000 : ℝ)) (a:=za) (b:=zb) (d:=(1209978210/1000000000 : ℝ))
    (le_of_lt hz.1) (by linarith [hz.2.1,hz.2.2.1]) (le_of_lt hz.2.2.2)
    (Filter.Eventually.of_forall (fun x=>le_of_lt (Real.exp_pos _))) (hc.intervalIntegrable _ _)
  have hl:=lt_of_lt_of_le inner_integral_lower hi
  have hu:=lt_of_le_of_lt ho outer_integral_upper
  have hs:=Chapter06Figures.sqrt_two_pi
  have hp : 0<Real.sqrt (2*Real.pi) := by positivity
  simp only [Chapter06.c06_p03.g,intervalIntegral.integral_const_mul,one_div]
  constructor
  · rw [←div_eq_inv_mul]
    apply (lt_div_iff₀ hp).mpr
    nlinarith [hs.2]
  · rw [←div_eq_inv_mul]
    apply (div_lt_iff₀ hp).mpr
    nlinarith [hs.1]
theorem source_area_rounding :
    |(∫ t in (3/100 : ℝ)..(14/100 : ℝ),Chapter06Figures.density t)-806241/1000000|<1/2000000 := by
  have he : Chapter06Figures.density=Chapter06.c06_p03.f (-268/100) (59/100) := by
    ext t
    unfold Chapter06Figures.density Chapter06.c06_p03.f
    simp only [sub_neg_eq_add,neg_div]
    ring
  rw [he,Chapter06.c06_p03.interval _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
  have h:=standardized_area_bounds
  have hza : Chapter06.c06_p03.z (-268/100) (59/100) (3/100)=za := by unfold Chapter06.c06_p03.z za; ring
  have hzb : Chapter06.c06_p03.z (-268/100) (59/100) (14/100)=zb := by unfold Chapter06.c06_p03.z zb; ring
  rw [hza,hzb]
  rw [abs_lt]
  constructor <;> linarith [h.1,h.2]
theorem source_density_continuous : ContinuousOn Chapter06Figures.density (Set.Icc (3/100) (14/100)) := by
  unfold Chapter06Figures.density
  apply ContinuousOn.div
  · apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div_const
    apply ContinuousOn.neg
    apply ContinuousOn.pow
    apply ContinuousOn.add_const
    exact continuousOn_id.log (fun x hx=>ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1))
  · fun_prop
  · intro x hx
    have hp : 0<x := lt_of_lt_of_le (by norm_num) hx.1
    positivity
theorem source_right_sums_converge :
    Tendsto (fun N : ℕ=>Chapter02Riemann.rightSum Chapter06Figures.density (3/100) (14/100) (N+1)) atTop
      (nhds (∫ t in (3/100 : ℝ)..(14/100 : ℝ),Chapter06Figures.density t)) :=
  Chapter02Riemann.right_sum_limit _ _ _ (by norm_num) source_density_continuous
end Chapter06Area
#print axioms Chapter06Area.source_area_rounding
#print axioms Chapter06Area.source_right_sums_converge
