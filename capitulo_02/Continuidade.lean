import Mathlib

set_option maxHeartbeats 400000
set_option maxRecDepth 8192

open MeasureTheory Filter
open scoped Topology

namespace Capitulo02Continuidade

theorem c02_p05_riemann_continuous
    (μ : Measure (Fin 1 → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : BoxIntegral.Box (Fin 1)) (f : (Fin 1 → ℝ) → ℝ)
    (hf : ContinuousOn f (BoxIntegral.Box.Icc I)) :
    BoxIntegral.HasIntegral.{0,0,0} I BoxIntegral.IntegrationParams.Riemann f
      μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) :=
  MeasureTheory.ContinuousOn.hasBoxIntegral μ hf BoxIntegral.IntegrationParams.Riemann

theorem c02_p05_riemann_limit
    (μ : Measure (Fin 1 → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : BoxIntegral.Box (Fin 1)) (f : (Fin 1 → ℝ) → ℝ)
    (hf : ContinuousOn f (BoxIntegral.Box.Icc I)) :
    Tendsto (BoxIntegral.integralSum f
      μ.toBoxAdditive.toSMul)
      (BoxIntegral.IntegrationParams.Riemann.toFilteriUnion I ⊤)
      (𝓝 (∫ x in I, f x ∂μ)) :=
  (c02_p05_riemann_continuous μ I f hf).tendsto

theorem c02_n01_weighted_riemann_limit
    (μ : Measure (Fin 1 → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : BoxIntegral.Box (Fin 1)) (w f : (Fin 1 → ℝ) → ℝ)
    (hw : ContinuousOn w (BoxIntegral.Box.Icc I))
    (hf : ContinuousOn f (BoxIntegral.Box.Icc I)) :
    Tendsto (BoxIntegral.integralSum (fun x => w x * f x)
      μ.toBoxAdditive.toSMul)
      (BoxIntegral.IntegrationParams.Riemann.toFilteriUnion I ⊤)
      (𝓝 (∫ x in I, w x * f x ∂μ)) :=
  c02_p05_riemann_limit μ I (fun x => w x * f x) (hw.mul hf)

end Capitulo02Continuidade

#print axioms Capitulo02Continuidade.c02_p05_riemann_continuous
#print axioms Capitulo02Continuidade.c02_p05_riemann_limit
#print axioms Capitulo02Continuidade.c02_n01_weighted_riemann_limit
