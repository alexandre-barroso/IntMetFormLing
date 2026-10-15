import capitulo_07.Verificar

namespace Chapter07AffineMoments

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

theorem covariance_constant_shifts (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (a b : ℝ) :
    covariance (fun ω => a + X ω) (fun ω => b + Y ω) μ = covariance X Y μ := by
  rw [covariance_const_add_left (hX.integrable (by norm_num)) a,
    covariance_const_add_right (hY.integrable (by norm_num)) b]

theorem sharedParticipantAffine (u v e w f : Ω → ℝ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (he : MemLp e 2 μ)
    (hw : MemLp w 2 μ) (hf : MemLp f 2 μ)
    (huw : IndepFun u w μ) (huf : IndepFun u f μ)
    (hvu : IndepFun v u μ) (hvw : IndepFun v w μ) (hvf : IndepFun v f μ)
    (heu : IndepFun e u μ) (hew : IndepFun e w μ) (hef : IndepFun e f μ)
    (a b : ℝ) :
    covariance (fun ω => a + (u ω + v ω + e ω))
      (fun ω => b + (u ω + w ω + f ω)) μ = variance u μ := by
  change covariance (fun ω => a + (u + v + e) ω)
    (fun ω => b + (u + w + f) ω) μ = variance u μ
  rw [covariance_constant_shifts (u + v + e) (u + w + f)
    ((hu.add hv).add he) ((hu.add hw).add hf) a b]
  exact Chapter07.c07_p04.sharedParticipant u v e w f
    hu hv he hw hf huw huf hvu hvw hvf heu hew hef

theorem sharedParticipantAffine_left_associated (u v e w f : Ω → ℝ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (he : MemLp e 2 μ)
    (hw : MemLp w 2 μ) (hf : MemLp f 2 μ)
    (huw : IndepFun u w μ) (huf : IndepFun u f μ)
    (hvu : IndepFun v u μ) (hvw : IndepFun v w μ) (hvf : IndepFun v f μ)
    (heu : IndepFun e u μ) (hew : IndepFun e w μ) (hef : IndepFun e f μ)
    (a b : ℝ) :
    covariance (fun ω => a + u ω + v ω + e ω)
      (fun ω => b + u ω + w ω + f ω) μ = variance u μ := by
  simpa only [add_assoc] using sharedParticipantAffine u v e w f
    hu hv he hw hf huw huf hvu hvw hvf heu hew hef a b

end Chapter07AffineMoments

#print axioms Chapter07AffineMoments.covariance_constant_shifts
#print axioms Chapter07AffineMoments.sharedParticipantAffine
#print axioms Chapter07AffineMoments.sharedParticipantAffine_left_associated
