import Mathlib

set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Chapter07Validity

noncomputable def squaredLoss {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) := ∑ i, (y i - (a + b*x i))^2
noncomputable def Sxx {n : ℕ} (x : Fin n → ℝ) (mx : ℝ) := ∑ i, (x i-mx)^2
noncomputable def Sxy {n : ℕ} (x y : Fin n → ℝ) (mx my : ℝ) := ∑ i, (x i-mx)*(y i-my)
noncomputable def Syy {n : ℕ} (y : Fin n → ℝ) (my : ℝ) := ∑ i, (y i-my)^2

theorem shifted_square_sum {n : ℕ} (u : Fin n → ℝ) (c : ℝ) :
    (∑ i, (u i+c)^2) = (∑ i, (u i)^2) + 2*c*(∑ i,u i) + (n : ℝ)*c^2 := by
  calc (∑ i, (u i+c)^2) = ∑ i, ((u i)^2+2*c*u i+c^2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
       _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem centered_loss {n : ℕ} (x y : Fin n → ℝ) (mx my a b : ℝ)
    (hx : ∑ i,x i = (n : ℝ)*mx) (hy : ∑ i,y i = (n : ℝ)*my) :
    squaredLoss x y a b = Syy y my - 2*b*Sxy x y mx my + b^2*Sxx x mx + (n : ℝ)*(my-a-b*mx)^2 := by
  let u := fun i => (y i-my)-b*(x i-mx)
  have hu : ∑ i, u i = 0 := by
    dsimp [u]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hx,hy]
    ring
  have hsq : (∑ i,(u i)^2) = Syy y my-2*b*Sxy x y mx my+b^2*Sxx x mx := by
    unfold Syy Sxy Sxx
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [u]
    ring
  have heq : squaredLoss x y a b = ∑ i,(u i+(my-a-b*mx))^2 := by
    unfold squaredLoss
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [u]
    congr 1
    ring
  rw [heq,shifted_square_sum,hu,hsq]
  ring

theorem complete_square (xx xy yy mx my a b n : ℝ) (hxx : xx ≠ 0) :
    yy-2*b*xy+b^2*xx+n*(my-a-b*mx)^2 =
    yy-xy^2/xx+xx*(b-xy/xx)^2+n*(my-a-b*mx)^2 := by
  field_simp
  <;> ring

theorem regression_minimum {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (mx my a b : ℝ)
    (hx : ∑ i,x i = (n : ℝ)*mx) (hy : ∑ i,y i = (n : ℝ)*my) (hxx : 0 < Sxx x mx) :
    squaredLoss x y (my-(Sxy x y mx my/Sxx x mx)*mx) (Sxy x y mx my/Sxx x mx) ≤ squaredLoss x y a b := by
  rw [centered_loss x y mx my a b hx hy,complete_square _ _ _ _ _ _ _ _ hxx.ne']
  rw [centered_loss x y mx my _ _ hx hy,complete_square _ _ _ _ _ _ _ _ hxx.ne']
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : my - (my - Sxy x y mx my / Sxx x mx * mx) - Sxy x y mx my / Sxx x mx * mx = 0 := by ring
  rw [sub_self,he]
  nlinarith [mul_nonneg hxx.le (sq_nonneg (b-Sxy x y mx my/Sxx x mx)),mul_nonneg hnR.le (sq_nonneg (my-a-b*mx))]

theorem source_unique_minimum (a b : ℝ) :
    (233-a)^2+(204-a)^2+(242-a)^2+(130-a-b)^2+(112-a-b)^2+(142-a-b)^2 = 3734/3 ↔
    a = 679/3 ∧ b = -295/3 := by
  have he : (233-a)^2+(204-a)^2+(242-a)^2+(130-a-b)^2+(112-a-b)^2+(142-a-b)^2 =
    3734/3 + 3*(a-679/3)^2 + 3*(a+b-128)^2 := by ring
  rw [he]
  constructor
  · intro h
    have ha : a-679/3=0 := (sq_eq_zero_iff).mp (by nlinarith [sq_nonneg (a-679/3),sq_nonneg (a+b-128)])
    have hb : a+b-128=0 := (sq_eq_zero_iff).mp (by nlinarith [sq_nonneg (a-679/3),sq_nonneg (a+b-128)])
    constructor <;> linarith
  · rintro ⟨rfl,rfl⟩
    norm_num

noncomputable def pairedMean {n : ℕ} (a b : Fin n → ℝ) : Option ℝ :=
    if n=0 then none else some ((∑ i,(a i-b i))/(n : ℝ))

theorem paired_domain {n : ℕ} (a b : Fin n → ℝ) : (pairedMean a b = none ↔ n=0) := by simp [pairedMean]

theorem paired_valid {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ) :
    pairedMean a b = some ((∑ i,a i)/(n : ℝ)-(∑ i,b i)/(n : ℝ)) := by
  simp [pairedMean,Nat.ne_of_gt hn,Finset.sum_sub_distrib,sub_div]

#print axioms shifted_square_sum
#print axioms centered_loss
#print axioms complete_square
#print axioms regression_minimum
#print axioms source_unique_minimum
#print axioms paired_domain
#print axioms paired_valid

end Chapter07Validity
