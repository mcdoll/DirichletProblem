/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import DirichletProblem.Mathlib.Analysis.Fourier.FourierTransform

@[expose] public noncomputable section

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace

namespace SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem norm_fourierInv_apply_le_toLp_one (f : 𝓢(V, F)) (x : V) :
    ‖𝓕⁻ f x‖ ≤ ‖f.toLp 1‖ := calc
  _ = ‖∫ (v : V), 𝐞 (inner ℝ v x) • f v‖ := by rw [fourierInv_coe, Real.fourierInv_eq]
  _ ≤ ∫ (v : V), ‖𝐞 (inner ℝ v x) • f v‖ := norm_integral_le_integral_norm _
  _ = _ := by simp [norm_toLp_one]

theorem norm_fourierInv_toBoundedContinuousFunction_le_toLp_one (f : 𝓢(V, F)) :
    ‖(𝓕⁻ f).toBoundedContinuousFunction‖ ≤ ‖f.toLp 1‖ := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  simpa using norm_fourierInv_apply_le_toLp_one f

theorem norm_fourierInv_Lp_top_leq_toLp_one (f : 𝓢(V, F)) :
    ‖(𝓕⁻ f).toLp ⊤‖ ≤ ‖f.toLp 1‖ :=
  norm_toLp_top_le.trans (seminorm_le_bound ℝ 0 0 _ (by positivity)
    (by simpa using norm_fourierInv_apply_le_toLp_one f))

theorem toLp_one_fourierTransform_eq (f : 𝓢(V, F)) :
    Lp.fourierTransform (f.toLp 1) = (𝓕 f).toBoundedContinuousFunction := by
  ext x
  simpa [fourier_coe] using fourier_congr_ae (coeFn_toLp f 1 volume) x

theorem toLp_one_fourierTransformInv_eq (f : 𝓢(V, F)) :
    Lp.fourierTransformInv (f.toLp 1) = (𝓕⁻ f).toBoundedContinuousFunction := by
  ext x
  simpa [fourierInv_coe] using fourierInv_congr_ae (coeFn_toLp f 1 volume) x

end SchwartzMap
