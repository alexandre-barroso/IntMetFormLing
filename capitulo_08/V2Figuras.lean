import Mathlib

namespace Chapter08V2Figures

open scoped BigOperators

def loss (a b : ℝ) : ℝ :=
    (233-a)^2+(204-a)^2+(242-a)^2+
    (130-a-b)^2+(112-a-b)^2+(142-a-b)^2

def excess (u v : ℝ) : ℝ := 3*u^2+3*(u+v)^2

theorem optimum_sum : (679/3:ℝ)+(-295/3)=128 := by norm_num

theorem centered_second_predictor (a b : ℝ) :
    a+b-128=(a-679/3)+(b-(-295/3)) := by ring

theorem loss_centering (u v : ℝ) :
    loss (u+679/3) (v-295/3) - 3734/3 = excess u v := by
  unfold loss excess
  ring

theorem excess_nonnegative (u v : ℝ) : 0 ≤ excess u v := by
  unfold excess
  positivity

theorem unique_zero (u v : ℝ) : excess u v=0 ↔ u=0 ∧ v=0 := by
  unfold excess
  constructor
  · intro h
    have hu : u^2=0 := by nlinarith [sq_nonneg u, sq_nonneg (u+v)]
    have hz : u=0 := by nlinarith [sq_nonneg u]
    constructor
    · exact hz
    · rw [hz] at h; nlinarith [sq_nonneg v]
  · rintro ⟨rfl,rfl⟩; norm_num

theorem gradient_u (u v : ℝ) :
    HasDerivAt (fun t => excess t v) (12*u+6*v) u := by
  unfold excess
  exact (((hasDerivAt_pow 2 u).const_mul 3).add
    ((((hasDerivAt_id u).add_const v).pow 2).const_mul 3)).congr_deriv (by dsimp; ring)

theorem gradient_v (u v : ℝ) :
    HasDerivAt (fun t => excess u t) (6*u+6*v) v := by
  unfold excess
  exact ((hasDerivAt_const v (3*u^2)).add
    ((((hasDerivAt_id v).const_add u).pow 2).const_mul 3)).congr_deriv (by dsimp; ring)

theorem exact_step (u v η : ℝ) :
    excess (u-η*(12*u+6*v)) (v-η*(6*u+6*v))-excess u v =
    -η*((12*u+6*v)^2+(6*u+6*v)^2)+
      η^2*excess (12*u+6*v) (6*u+6*v) := by
  unfold excess
  ring

theorem local_descent (u v η : ℝ)
    (hη : 0 < η)
    (hstep : η*excess (12*u+6*v) (6*u+6*v) <
      (12*u+6*v)^2+(6*u+6*v)^2) :
    excess (u-η*(12*u+6*v)) (v-η*(6*u+6*v)) < excess u v := by
  have h := mul_lt_mul_of_pos_left hstep hη
  have he := exact_step u v η
  nlinarith

theorem figure_point : excess (-8) 14=300 ∧
    (12*(-8)+6*14:ℝ)= -12 ∧ (6*(-8)+6*14:ℝ)=36 ∧
    ((-12)^2+36^2:ℝ)=1440 ∧ excess (-12) 36=2160 := by
  norm_num [excess]

theorem plotted_step_decreases :
    excess (-8-(8/Real.sqrt 1440)*(-12))
      (14-(8/Real.sqrt 1440)*36) < excess (-8) 14 := by
  have hs : 0 < Real.sqrt (1440:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt (1440:ℝ))^2=1440 := Real.sq_sqrt (by norm_num)
  have hbound : (12:ℝ) < Real.sqrt 1440 := by nlinarith
  have he : (8/Real.sqrt (1440:ℝ))*2160 < 1440 := by
    calc
      (8/Real.sqrt (1440:ℝ))*2160 = (8*2160)/Real.sqrt 1440 := by ring
      _ < 1440 := (div_lt_iff₀ hs).2 (by nlinarith)
  have hη : 0 < (8/Real.sqrt (1440:ℝ)) := div_pos (by norm_num) hs
  have hc : (8/Real.sqrt (1440:ℝ))*excess (12*(-8)+6*14) (6*(-8)+6*14) <
      (12*(-8)+6*14)^2+(6*(-8)+6*14)^2 := by
    norm_num [excess]
    exact he
  have h := local_descent (-8) 14 (8/Real.sqrt 1440) hη hc
  norm_num at h ⊢
  exact h

theorem zero_context_no_update {d : ℕ} (u : Fin d → ℝ) (α p y : ℝ) :
    (fun i => u i-α*(p-y)*(0:Fin d → ℝ) i)=u ∧
    (∑ i, (u i-α*(p-y)*(0:Fin d → ℝ) i)*(0:Fin d → ℝ) i)=
      ∑ i, u i*(0:Fin d → ℝ) i := by simp


def editRoute : List (ℕ × ℕ) :=
  [(0,0),(1,0),(2,1),(3,2),(4,3),(5,4),(5,5),(6,6),(7,7),(8,8),(9,9)]

def editRouteCost : ℕ :=
  ((editRoute.zip editRoute.tail).map (fun (p,q) =>
    if q.1=p.1+1 ∧ q.2=p.2+1 then
      if ("intention".toList[q.1-1]!)=("execution".toList[q.2-1]!) then 0 else 2
    else 1)).sum

theorem plotted_edit_path_cost : editRouteCost=8 := by decide +kernel

theorem plotted_edit_path_adjacency :
    (editRoute.zip editRoute.tail).all (fun (p,q) =>
      (q.1=p.1+1 ∧ q.2=p.2) ∨ (q.1=p.1 ∧ q.2=p.2+1) ∨
      (q.1=p.1+1 ∧ q.2=p.2+1))=true := by decide +kernel

theorem plotted_edit_path_bounds :
    editRoute.all (fun q => q.1≤9 ∧ q.2≤9)=true ∧
    editRoute.head?=some (0,0) ∧ editRoute.getLast?=some (9,9) := by decide +kernel

end Chapter08V2Figures

#print axioms Chapter08V2Figures.loss_centering
#print axioms Chapter08V2Figures.local_descent
#print axioms Chapter08V2Figures.plotted_step_decreases
