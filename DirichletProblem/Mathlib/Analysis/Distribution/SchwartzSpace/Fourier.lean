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
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

section Fubini

variable [CompleteSpace E] [CompleteSpace F]

/-- Plancherel's theorem for Schwartz functions.

Version where the inner product is replaced by a general sesquilinear form `M`. -/
theorem integral_sesq_fourierInv_fourierInv (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕⁻ f ξ) (𝓕⁻ g ξ) = ∫ x, M (f x) (g x) := by
  simpa using (integral_sesq_fourier_eq (𝓕⁻ f) g M).symm

end Fubini

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


section L2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Plancherel's theorem for Schwartz functions. -/
@[simp] theorem integral_inner_fourierInv_fourierInv (f g : 𝓢(V, H)) :
    ∫ ξ, ⟪𝓕⁻ f ξ, 𝓕⁻ g ξ⟫ = ∫ x, ⟪f x, g x⟫ :=
  integral_sesq_fourierInv_fourierInv f g (innerSL ℂ)

theorem integral_norm_sq_fourierInv (f : 𝓢(V, H)) :
    ∫ ξ, ‖𝓕⁻ f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    integral_inner_fourierInv_fourierInv f f

theorem inner_fourierInv_toL2_eq (f g : 𝓢(V, H)) :
    ⟪(𝓕⁻ f).toLp 2, (𝓕⁻ g).toLp 2⟫ = ⟪f.toLp 2, g.toLp 2⟫ := by simp

@[simp] theorem norm_fourierInv_toL2_eq (f : 𝓢(V, H)) :
    ‖(𝓕⁻ f).toLp 2‖ = ‖f.toLp 2‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourierInv_toL2_eq]

end L2


end SchwartzMap
