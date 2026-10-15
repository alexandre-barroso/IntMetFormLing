import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open scoped BigOperators

namespace Chapter08Expressions

def confusion : Matrix (Fin 3) (Fin 3) ℚ := !![8,10,1;5,60,50;3,30,200]
def tp (i : Fin 3) : ℚ := confusion i i
def fp (i : Fin 3) : ℚ := (∑ j,confusion i j)-tp i
def fn (i : Fin 3) : ℚ := (∑ j,confusion j i)-tp i
def precision (i : Fin 3) : ℚ := tp i/(tp i+fp i)
def recallRate (i : Fin 3) : ℚ := tp i/(tp i+fn i)
def f1 (i : Fin 3) : ℚ := 2*tp i/(2*tp i+fp i+fn i)

theorem confusion_totals : (∑ i,∑ j,confusion i j)=367 ∧ (∑ i,tp i)=268 := by decide +kernel

theorem confusion_components : tp=![8,60,200] ∧ fp=![11,55,33] ∧ fn=![8,40,51] := by decide +kernel

theorem urgent_metrics : precision 0=8/19 ∧ recallRate 0=1/2 ∧ f1 0=16/35 := by decide +kernel

theorem f1_classes : f1=![16/35,24/43,100/121] := by decide +kernel

theorem micro_f1 : (2*(∑ i,tp i))/(2*(∑ i,tp i)+(∑ i,fp i)+(∑ i,fn i))=268/367 := by decide +kernel

theorem macro_f1 : (∑ i,f1 i)/3=(16/35+24/43+100/121)/3 := by decide +kernel

def safeDivide (a b : ℚ) : Option ℚ := if b=0 then none else some (a/b)

theorem undefined_precision : safeDivide 0 0=none ∧ safeDivide 0 100=some 0 := by decide +kernel

def W : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,1]
def bias : Fin 2 → ℝ := ![0,-1]
noncomputable def relu (z : ℝ) : ℝ := max 0 z
noncomputable def hidden (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i=>relu ((W.mulVec x+bias) i)
noncomputable def output (x : Fin 2 → ℝ) : ℝ := relu ((hidden x) 0-2*(hidden x) 1)

theorem neural_matrix (x₁ x₂ : ℝ) : W.mulVec ![x₁,x₂]+bias=![x₁+x₂,x₁+x₂-1] := by
  ext i;fin_cases i <;> simp [W,bias,Matrix.mulVec,dotProduct,Fin.sum_univ_two,sub_eq_add_neg]

theorem neural_hidden (x₁ x₂ : ℝ) : hidden ![x₁,x₂]=![relu (x₁+x₂),relu (x₁+x₂-1)] := by
  unfold hidden
  rw [neural_matrix]
  ext i;fin_cases i <;> rfl

theorem neural_all_inputs : output ![0,0]=0 ∧ output ![0,1]=1 ∧ output ![1,0]=1 ∧ output ![1,1]=0 := by
  norm_num [output,neural_hidden,relu]

noncomputable def softmax {n : ℕ} (s : Fin n → ℝ) (j : Fin n) : ℝ := Real.exp (s j)/(∑ k,Real.exp (s k))
noncomputable def scores {n dk : ℕ} (Q K : Matrix (Fin n) (Fin dk) ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j=>(Q*K.transpose) i j/Real.sqrt dk
noncomputable def attention {n dk dv : ℕ} (Q K : Matrix (Fin n) (Fin dk) ℝ) (V : Matrix (Fin n) (Fin dv) ℝ) : Matrix (Fin n) (Fin dv) ℝ := (show Matrix (Fin n) (Fin n) ℝ from fun i=>softmax (scores Q K i))*V

theorem projection_entry {n d dk : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (WQ : Matrix (Fin d) (Fin dk) ℝ) (i : Fin n) (j : Fin dk) :
    (X*WQ) i j=∑ r,X i r*WQ r j := rfl

theorem score_entry {n dk : ℕ} (Q K : Matrix (Fin n) (Fin dk) ℝ) (i j : Fin n) :
    scores Q K i j=(∑ r,Q i r*K j r)/Real.sqrt dk := rfl

theorem attention_entry {n dk dv : ℕ} (Q K : Matrix (Fin n) (Fin dk) ℝ) (V : Matrix (Fin n) (Fin dv) ℝ) (i : Fin n) (r : Fin dv) :
    attention Q K V i r=∑ j,(Real.exp (scores Q K i j)/(∑ m,Real.exp (scores Q K i m)))*V j r := rfl

theorem attention_weights {n dk : ℕ} (hn : 0<n) (Q K : Matrix (Fin n) (Fin dk) ℝ) (i : Fin n) :
    (∑ j,softmax (scores Q K i) j)=1 := by
  have h : (∑ k,Real.exp (scores Q K i k))>0 := by
    apply Finset.sum_pos'
    · intro k hk;exact (Real.exp_pos _).le
    · exact ⟨⟨0,hn⟩,Finset.mem_univ _,Real.exp_pos _⟩
  unfold softmax
  rw [←Finset.sum_div,div_self (ne_of_gt h)]

noncomputable def feedForward {d h : ℕ} (x : Fin d → ℝ) (W₁ : Matrix (Fin d) (Fin h) ℝ) (W₂ : Matrix (Fin h) (Fin d) ℝ) (b₁ : Fin h → ℝ) (b₂ : Fin d → ℝ) : Fin d → ℝ :=
  Matrix.vecMul (fun j=>relu ((Matrix.vecMul x W₁+b₁) j)) W₂+b₂

theorem feed_forward_entry {d h : ℕ} (x : Fin d → ℝ) (W₁ : Matrix (Fin d) (Fin h) ℝ) (W₂ : Matrix (Fin h) (Fin d) ℝ) (b₁ : Fin h → ℝ) (b₂ : Fin d → ℝ) (k : Fin d) :
    feedForward x W₁ W₂ b₁ b₂ k=(∑ j,relu ((∑ r,x r*W₁ r j)+b₁ j)*W₂ j k)+b₂ k := rfl

noncomputable def cbow {d : ℕ} (v : ℤ → Fin d → ℝ) (t : ℤ) : Fin d → ℝ := fun i=>(v (t-2) i+v (t-1) i+v (t+1) i+v (t+2) i)/4

theorem cbow_coordinate {d : ℕ} (v : ℤ → Fin d → ℝ) (t : ℤ) (i : Fin d) :
    cbow v t i=(1/4)*(v (t-2) i+v (t-1) i+v (t+1) i+v (t+2) i) := by unfold cbow;ring

noncomputable def brier {n k : ℕ} (p o : Matrix (Fin n) (Fin k) ℝ) : ℝ := (∑ i,∑ j,(p i j-o i j)^2)/n

theorem brier_binary (p y : ℝ) : (p-y)^2+((1-p)-(1-y))^2=2*(p-y)^2 := by ring

theorem grouped_mean (NC NE SC SE : ℝ) (hC : NC≠0) (hE : NE≠0) :
    (NC*(SC/NC)+NE*(SE/NE))/(NC+NE)=(SC+SE)/(NC+NE) := by field_simp

theorem likelihood_log (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    Real.log (p^608*(1-p)^319)=608*Real.log p+319*Real.log (1-p) := by
  rw [Real.log_mul (pow_ne_zero _ (ne_of_gt hp)) (pow_ne_zero _ (ne_of_gt (sub_pos.mpr hp1))),Real.log_pow,Real.log_pow]
  norm_num

theorem ot_first_preference (w1 w2 : ℝ) : -w1-w2 > -2*w1 ↔ w1>w2 := by constructor <;> intro h <;> linarith

theorem ot_second_preference (w1 w2 : ℝ) : -w1 > -w2 ↔ w2>w1 := by constructor <;> intro h <;> linarith

theorem ot_incompatible_preferences (w1 w2 : ℝ) : ¬(-w1-w2 > -2*w1 ∧ -w1 > -w2) := by rintro ⟨h1,h2⟩; linarith

theorem ot_margin_regions (w1 w2 : ℝ) :
    (w1-w2≥1 ↔ w2≤w1-1) ∧ (w2-w1≥1 ↔ w2≥w1+1) := by
  constructor <;> constructor <;> intro h <;> linarith

theorem ot_incompatible_margins (w1 w2 : ℝ) : ¬(w1-w2≥1 ∧ w2-w1≥1) := by
  rintro ⟨h1,h2⟩
  have impossible : (0:ℝ)≥2 := by linarith
  norm_num at impossible

#print axioms ot_first_preference
#print axioms ot_second_preference
#print axioms ot_incompatible_preferences
#print axioms ot_margin_regions
#print axioms ot_incompatible_margins

end Chapter08Expressions

#print axioms Chapter08Expressions.confusion_totals
#print axioms Chapter08Expressions.confusion_components
#print axioms Chapter08Expressions.urgent_metrics
#print axioms Chapter08Expressions.f1_classes
#print axioms Chapter08Expressions.micro_f1
#print axioms Chapter08Expressions.macro_f1
#print axioms Chapter08Expressions.undefined_precision
#print axioms Chapter08Expressions.neural_matrix
#print axioms Chapter08Expressions.neural_hidden
#print axioms Chapter08Expressions.neural_all_inputs
#print axioms Chapter08Expressions.projection_entry
#print axioms Chapter08Expressions.score_entry
#print axioms Chapter08Expressions.attention_entry
#print axioms Chapter08Expressions.attention_weights
#print axioms Chapter08Expressions.feed_forward_entry
#print axioms Chapter08Expressions.cbow_coordinate
#print axioms Chapter08Expressions.brier_binary
#print axioms Chapter08Expressions.grouped_mean
#print axioms Chapter08Expressions.likelihood_log
