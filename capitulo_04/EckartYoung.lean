import Mathlib

open scoped BigOperators

namespace Chapter04EckartYoung

noncomputable def frobeniusSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (A.transpose*A).trace

theorem frobenius_nonnegative {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0≤frobeniusSquared A := by
  unfold frobeniusSquared
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (A j i)

theorem projection_complement {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : P.transpose=P) (hi : P*P=P) :
    (1-P).transpose=1-P ∧ (1-P)*(1-P)=1-P := by
  constructor
  · simp only [Matrix.transpose_sub,Matrix.transpose_one,hs]
  · simp only [sub_mul,mul_sub,Matrix.one_mul,Matrix.mul_one,hi]
    abel

theorem projection_diagonal_nonnegative {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : P.transpose=P) (hi : P*P=P) (i : Fin n) : 0≤P i i := by
  have he : P i i=∑j,P j i*P j i := by
    nth_rw 1 [←hi]
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg (fun Q : Matrix (Fin n) (Fin n) ℝ => Q j i) hs
    simpa only [Matrix.transpose_apply] using congrArg (fun z : ℝ => z*P j i) h
  rw [he]
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg _

theorem projection_diagonal_bounds {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : P.transpose=P) (hi : P*P=P) (i : Fin n) : 0≤P i i ∧ P i i≤1 := by
  have hc := projection_complement P hs hi
  have h := projection_diagonal_nonnegative (1-P) hc.1 hc.2 i
  simp only [Matrix.sub_apply,Matrix.one_apply_eq] at h
  exact ⟨projection_diagonal_nonnegative P hs hi i,by linarith⟩

theorem orthogonal_conjugate {n : ℕ} (V P : Matrix (Fin n) (Fin n) ℝ)
    (hv : V.transpose*V=1) (_hvv : V*V.transpose=1)
    (hp : P.transpose=P) (hpp : P*P=P) :
    (V*P*V.transpose).transpose=V*P*V.transpose ∧
    (V*P*V.transpose)*(V*P*V.transpose)=V*P*V.transpose ∧
    (V*P*V.transpose).trace=P.trace := by
  refine ⟨?_,?_,?_⟩
  · simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hp,Matrix.mul_assoc]
  · calc
      (V*P*V.transpose)*(V*P*V.transpose)=V*P*(V.transpose*V)*P*V.transpose := by simp only [Matrix.mul_assoc]
      _=V*P*V.transpose := by rw [hv,Matrix.mul_one];simp only [Matrix.mul_assoc,hpp]
  · rw [Matrix.trace_mul_cycle, hv, Matrix.one_mul]

theorem row_projection_exists {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) :
    ∃P : Matrix (Fin n) (Fin n) ℝ,
      P.transpose=P ∧ P*P=P ∧ B*P=B ∧ P.trace=(B.rank:ℝ) := by
  classical
  let G := B.transpose*B
  have hg : G.IsHermitian := by
    simpa only [G,Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.isHermitian_conjTranspose_mul_self B
  let V : Matrix (Fin n) (Fin n) ℝ := hg.eigenvectorUnitary
  let e := hg.eigenvalues
  let d : Fin n→ℝ := fun i => if e i=0 then 0 else 1
  let D := Matrix.diagonal d
  let P := V*D*V.transpose
  have hv : V.transpose*V=1 := by
    simpa only [V,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_star_mul_self hg.eigenvectorUnitary
  have hvv : V*V.transpose=1 := by
    simpa only [V,Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self hg.eigenvectorUnitary
  have hspectral : G=V*Matrix.diagonal e*V.transpose := by
    simpa only [V,e,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,RCLike.ofReal_real_eq_id,Function.comp_def,Function.id_def] using hg.spectral_theorem
  have hd : D*D=D := by
    simp only [D,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp only [d]
    split_ifs <;> norm_num
  have hp := orthogonal_conjugate V D hv hvv (Matrix.diagonal_transpose _) hd
  have he : Matrix.diagonal e*D=Matrix.diagonal e := by
    simp only [D,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    dsimp only [d]
    split_ifs with h <;> simp [h]
  have hGP : G*P=G := by
    change G*(V*D*V.transpose)=G
    rw [hspectral]
    calc
      V*Matrix.diagonal e*V.transpose*(V*D*V.transpose)=V*Matrix.diagonal e*(V.transpose*V)*D*V.transpose := by simp only [Matrix.mul_assoc]
      _=V*Matrix.diagonal e*V.transpose := by rw [hv,Matrix.mul_one];rw [Matrix.mul_assoc V (Matrix.diagonal e) D,he]
  have hB : B*P=B := by
    have hz : (B*(1-P)).transpose*(B*(1-P))=0 := by
      rw [Matrix.transpose_mul]
      calc
        (1-P).transpose*B.transpose*(B*(1-P))=(1-P).transpose*(G*(1-P)) := by simp only [G,Matrix.mul_assoc]
        _=0 := by rw [mul_sub,Matrix.mul_one,hGP,sub_self,Matrix.mul_zero]
    have hzero : B*(1-P)=0 := by
      apply Matrix.conjTranspose_mul_self_eq_zero.mp
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hz
    have hz : B-B*P=0 := by simpa only [Matrix.mul_sub,Matrix.mul_one] using hzero
    exact (sub_eq_zero.mp hz).symm
  refine ⟨P,hp.1,hp.2.1,hB,?_⟩
  calc
    P.trace=D.trace := hp.2.2
    _=(Fintype.card {i : Fin n // e i≠0}:ℝ) := by
      simp only [D,Matrix.trace_diagonal,d,Fintype.card_subtype]
      simpa only [ite_not] using (Finset.sum_boole (R:=ℝ) (fun i : Fin n=>e i≠0) Finset.univ)
    _=(G.rank:ℝ) := by rw [hg.rank_eq_card_non_zero_eigs]
    _=(B.rank:ℝ) := by change ((B.transpose*B).rank:ℝ)=(B.rank:ℝ);rw [Matrix.rank_transpose_mul_self]

theorem frobenius_projection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : P.transpose=P) (hi : P*P=P) :
    frobeniusSquared (A*P)=(A.transpose*A*P).trace := by
  unfold frobeniusSquared
  rw [Matrix.transpose_mul,hs]
  calc
    (P*A.transpose*(A*P)).trace=(P*(A.transpose*A)*P).trace := by simp only [Matrix.mul_assoc]
    _=(P*P*(A.transpose*A)).trace := Matrix.trace_mul_cycle _ _ _
    _=(A.transpose*A*P).trace := by rw [hi,Matrix.trace_mul_comm]

theorem frobenius_projection_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : P.transpose=P) (hi : P*P=P) :
    frobeniusSquared (A*P)≤frobeniusSquared A := by
  have hc := projection_complement P hs hi
  have h := frobenius_nonnegative (A*(1-P))
  rw [frobenius_projection A (1-P) hc.1 hc.2,mul_sub,Matrix.mul_one,Matrix.trace_sub] at h
  rw [frobenius_projection A P hs hi]
  unfold frobeniusSquared
  linarith

theorem error_projection_lower_bound {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : P.transpose=P) (hi : P*P=P) (hB : B*P=B) :
    (A.transpose*A*(1-P)).trace≤frobeniusSquared (A-B) := by
  have hc := projection_complement P hs hi
  have hz : B*(1-P)=0 := by rw [Matrix.mul_sub,Matrix.mul_one,hB,sub_self]
  have h := frobenius_projection_le (A-B) (1-P) hc.1 hc.2
  rw [Matrix.sub_mul,hz,sub_zero,frobenius_projection A (1-P) hc.1 hc.2] at h
  exact h

noncomputable def indicator {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ := if i∈S then 1 else 0

theorem indicator_sum {n : ℕ} (S : Finset (Fin n)) : ∑ i,indicator S i=(S.card:ℝ) := by
  simp [indicator]

theorem ordered_weight_bound {n : ℕ} (S : Finset (Fin n)) (e w : Fin n→ℝ) (t : ℝ)
    (ht : 0≤t) (hinside : ∀i∈S,t≤e i) (houtside : ∀i∉S,e i≤t)
    (hw : ∀i,0≤w i ∧ w i≤1) (hmass : (∑i,w i)≤(S.card:ℝ)) :
    (∑i,e i*(1-indicator S i))≤∑i,e i*(1-w i) := by
  have hterms : 0≤∑i,(e i-t)*(indicator S i-w i) := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i∈S
    · simp only [indicator,if_pos hi]
      exact mul_nonneg (sub_nonneg.mpr (hinside i hi)) (sub_nonneg.mpr (hw i).2)
    · simp only [indicator,if_neg hi,zero_sub]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (houtside i hi)) (neg_nonpos.mpr (hw i).1)
  have hmass' : 0≤t*((S.card:ℝ)-∑i,w i) := mul_nonneg ht (sub_nonneg.mpr hmass)
  have hid : (∑i,e i*indicator S i)-(∑i,e i*w i)=
      (∑i,(e i-t)*(indicator S i-w i))+t*((S.card:ℝ)-∑i,w i) := by
    rw [←indicator_sum S]
    simp only [mul_sub,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    ring
  have hweight : (∑i,e i*w i)≤∑i,e i*indicator S i := by linarith
  simpa only [mul_sub,mul_one,Finset.sum_sub_distrib] using sub_le_sub_left hweight (∑i,e i)

theorem trace_conjugate_times {n : ℕ} (V L P : Matrix (Fin n) (Fin n) ℝ) :
    (V*L*V.transpose*P).trace=(L*(V.transpose*P*V)).trace := by
  calc
    (V*L*V.transpose*P).trace=(V*(L*V.transpose*P)).trace := by simp only [Matrix.mul_assoc]
    _=((L*V.transpose*P)*V).trace := Matrix.trace_mul_comm _ _
    _=(L*(V.transpose*P*V)).trace := by simp only [Matrix.mul_assoc]

theorem gram_projection_trace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (V P : Matrix (Fin n) (Fin n) ℝ) (e : Fin n→ℝ)
    (hv : V.transpose*V=1) (hgram : A.transpose*A=V*Matrix.diagonal e*V.transpose) :
    (A.transpose*A*(1-P)).trace=∑i,e i*(1-(V.transpose*P*V) i i) := by
  rw [Matrix.mul_sub,Matrix.mul_one,Matrix.trace_sub,hgram]
  have ht : (V*Matrix.diagonal e*V.transpose).trace=∑i,e i := by
    rw [Matrix.trace_mul_cycle,hv,Matrix.one_mul,Matrix.trace_diagonal]
  rw [ht,trace_conjugate_times]
  simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul,mul_sub,mul_one,Finset.sum_sub_distrib]

theorem truncation_projection {n : ℕ} (V : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (hv : V.transpose*V=1) (hvv : V*V.transpose=1) :
    let P := V*Matrix.diagonal (indicator S)*V.transpose
    P.transpose=P ∧ P*P=P ∧ P.rank≤S.card ∧
      V.transpose*P*V=Matrix.diagonal (indicator S) := by
  dsimp only
  let D := Matrix.diagonal (indicator S)
  have hd : D*D=D := by
    simp only [D,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i∈S <;> simp [indicator,hi]
  have hp := orthogonal_conjugate V D hv hvv (Matrix.diagonal_transpose _) hd
  refine ⟨hp.1,hp.2.1,?_,?_⟩
  · have hdRank : D.rank=S.card := by
      change (Matrix.diagonal (indicator S)).rank=S.card
      rw [Matrix.rank_diagonal,Fintype.card_subtype]
      simp [indicator]
    exact (Matrix.rank_mul_le_left (V*D) V.transpose).trans ((Matrix.rank_mul_le_right V D).trans_eq hdRank)
  · change V.transpose*(V*D*V.transpose)*V=D
    calc
      V.transpose*(V*D*V.transpose)*V=(V.transpose*V)*D*(V.transpose*V) := by simp only [Matrix.mul_assoc]
      _=D := by rw [hv,Matrix.one_mul,Matrix.mul_one]

theorem truncation_error {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (e : Fin n→ℝ) (S : Finset (Fin n))
    (hv : V.transpose*V=1) (hvv : V*V.transpose=1)
    (hgram : A.transpose*A=V*Matrix.diagonal e*V.transpose) :
    frobeniusSquared (A-A*(V*Matrix.diagonal (indicator S)*V.transpose))=
      ∑i,e i*(1-indicator S i) := by
  let P := V*Matrix.diagonal (indicator S)*V.transpose
  have hp := truncation_projection V S hv hvv
  change frobeniusSquared (A-A*P)=_
  have he : A-A*P=A*(1-P) := by rw [Matrix.mul_sub,Matrix.mul_one]
  rw [he,frobenius_projection A (1-P)
    (projection_complement P hp.1 hp.2.1).1 (projection_complement P hp.1 hp.2.1).2]
  rw [gram_projection_trace A V P e hv hgram,hp.2.2.2]
  simp only [Matrix.diagonal_apply_eq]

theorem eckart_young_global {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (e : Fin n→ℝ) (S : Finset (Fin n)) (t : ℝ)
    (hv : V.transpose*V=1) (hvv : V*V.transpose=1)
    (hgram : A.transpose*A=V*Matrix.diagonal e*V.transpose)
    (ht : 0≤t) (hinside : ∀i∈S,t≤e i) (houtside : ∀i∉S,e i≤t) :
    (A*(V*Matrix.diagonal (indicator S)*V.transpose)).rank≤S.card ∧
    ∀B : Matrix (Fin m) (Fin n) ℝ,B.rank≤S.card →
      frobeniusSquared (A-A*(V*Matrix.diagonal (indicator S)*V.transpose))≤frobeniusSquared (A-B) := by
  constructor
  · exact (Matrix.rank_mul_le_right A _).trans (truncation_projection V S hv hvv).2.2.1
  intro B hb
  obtain ⟨P,hs,hi,hBP,htrace⟩ := row_projection_exists B
  let Q := V.transpose*P*V
  have hQ : Q.transpose=Q ∧ Q*Q=Q ∧ Q.trace=P.trace := by
    simpa only [Matrix.transpose_transpose] using orthogonal_conjugate V.transpose P hvv hv hs hi
  have hmass : (∑i,Q i i)≤(S.card:ℝ) := by
    change Q.trace≤(S.card:ℝ)
    rw [hQ.2.2,htrace]
    exact_mod_cast hb
  have hw : ∀i,0≤Q i i ∧ Q i i≤1 := projection_diagonal_bounds Q hQ.1 hQ.2.1
  calc
    frobeniusSquared (A-A*(V*Matrix.diagonal (indicator S)*V.transpose))=
      ∑i,e i*(1-indicator S i) := truncation_error A V e S hv hvv hgram
    _≤∑i,e i*(1-Q i i) := ordered_weight_bound S e (fun i=>Q i i) t ht hinside houtside hw hmass
    _=(A.transpose*A*(1-P)).trace := (gram_projection_trace A V P e hv hgram).symm
    _≤frobeniusSquared (A-B) := error_projection_lower_bound A B P hs hi hBP

theorem gram_from_exact_svd {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (s : Fin n→ℝ) (hu : U.transpose*U=1) :
    (U*Matrix.diagonal s*V.transpose).transpose*(U*Matrix.diagonal s*V.transpose)=
      V*Matrix.diagonal (fun i=>s i^2)*V.transpose := by
  simp only [Matrix.transpose_mul,Matrix.diagonal_transpose,Matrix.transpose_transpose]
  calc
    V*(Matrix.diagonal s*U.transpose)*(U*Matrix.diagonal s*V.transpose)=
      V*Matrix.diagonal s*(U.transpose*U)*Matrix.diagonal s*V.transpose := by simp only [Matrix.mul_assoc]
    _=V*Matrix.diagonal (fun i=>s i^2)*V.transpose := by
      rw [hu,Matrix.mul_one,Matrix.mul_assoc V (Matrix.diagonal s) (Matrix.diagonal s),Matrix.diagonal_mul_diagonal]
      simp only [pow_two]

theorem svd_truncation_identity {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (s : Fin n→ℝ) (S : Finset (Fin n))
    (hv : V.transpose*V=1) :
    (U*Matrix.diagonal s*V.transpose)*(V*Matrix.diagonal (indicator S)*V.transpose)=
      U*Matrix.diagonal (fun i=>s i*indicator S i)*V.transpose := by
  calc
    (U*Matrix.diagonal s*V.transpose)*(V*Matrix.diagonal (indicator S)*V.transpose)=
      U*Matrix.diagonal s*(V.transpose*V)*Matrix.diagonal (indicator S)*V.transpose := by
        simp only [Matrix.mul_assoc]
    _=U*Matrix.diagonal (fun i=>s i*indicator S i)*V.transpose := by
      rw [hv,Matrix.mul_one,Matrix.mul_assoc U (Matrix.diagonal s) (Matrix.diagonal (indicator S)),Matrix.diagonal_mul_diagonal]

theorem eckart_young_svd {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (s : Fin n→ℝ) (S : Finset (Fin n)) (t : ℝ)
    (hu : U.transpose*U=1) (hv : V.transpose*V=1) (hvv : V*V.transpose=1)
    (ht : 0≤t) (hinside : ∀ i ∈ S, t ≤ s i ^ 2) (houtside : ∀ i ∉ S, s i ^ 2 ≤ t) :
    (U*Matrix.diagonal (fun i=>s i*indicator S i)*V.transpose).rank≤S.card ∧
    ∀B : Matrix (Fin m) (Fin n) ℝ,B.rank≤S.card →
      frobeniusSquared (U*Matrix.diagonal s*V.transpose-
        U*Matrix.diagonal (fun i=>s i*indicator S i)*V.transpose)≤
      frobeniusSquared (U*Matrix.diagonal s*V.transpose-B) := by
  simpa only [svd_truncation_identity U V s S hv] using
    eckart_young_global (U*Matrix.diagonal s*V.transpose) V (fun i=>s i^2) S t hv hvv
      (gram_from_exact_svd U V s hu) ht hinside houtside

noncomputable def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (frobeniusSquared A)

theorem eckart_young_svd_norm {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) (s : Fin n→ℝ) (S : Finset (Fin n)) (t : ℝ)
    (hu : U.transpose*U=1) (hv : V.transpose*V=1) (hvv : V*V.transpose=1)
    (ht : 0 ≤ t) (hinside : ∀ i ∈ S, t ≤ s i ^ 2) (houtside : ∀ i ∉ S, s i ^ 2 ≤ t) :
    (U*Matrix.diagonal (fun i=>s i*indicator S i)*V.transpose).rank≤S.card ∧
    ∀B : Matrix (Fin m) (Fin n) ℝ,B.rank≤S.card →
      frobeniusNorm (U*Matrix.diagonal s*V.transpose-
        U*Matrix.diagonal (fun i=>s i*indicator S i)*V.transpose)≤
      frobeniusNorm (U*Matrix.diagonal s*V.transpose-B) := by
  have h := eckart_young_svd U V s S t hu hv hvv ht hinside houtside
  refine ⟨h.1,?_⟩
  intro B hb
  exact Real.sqrt_le_sqrt (h.2 B hb)

#print axioms eckart_young_svd_norm
#print axioms eckart_young_global
#print axioms eckart_young_svd

end Chapter04EckartYoung
