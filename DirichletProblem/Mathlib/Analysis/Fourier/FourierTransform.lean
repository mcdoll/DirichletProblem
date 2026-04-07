/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Moritz Doll
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public noncomputable section

variable {V W E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W] [BorelSpace W]
  [FiniteDimensional ℝ W]

variable [FiniteDimensional ℝ V]

open scoped BoundedContinuousFunction FourierTransform

open MeasureTheory

section CompContinuousCLM

namespace BoundedContinuousFunction

variable {𝕜 α β γ : Type*} [TopologicalSpace α] [SeminormedAddCommGroup β] [TopologicalSpace γ]
  [NormedField 𝕜] [NormedSpace 𝕜 β]

variable (𝕜) in
def compContinuousCLM (g : C(γ, α)) : (α →ᵇ β) →L[𝕜] γ →ᵇ β :=
  LinearMap.mkContinuous
    { toFun f := f.compContinuous g,
      map_add' := by intros; ext; simp,
      map_smul' := by intros; ext; simp }
    1 (by simpa using norm_compContinuous_le · g)

@[simp]
theorem compContinuousCLM_apply (f : α →ᵇ β) (g : C(γ, α)) :
  compContinuousCLM 𝕜 g f = f.compContinuous g := rfl

end BoundedContinuousFunction

end CompContinuousCLM

namespace Real

/-- The Fourier transform from `L1` functions to bounded continuous functions. -/
def Lp.fourierTransformInv (f : Lp (α := V) E 1) : V →ᵇ E :=
  (Lp.fourierTransform f).compContinuous (-ContinuousMap.id V)

theorem fourierInv_congr_ae {f₁ f₂ : V → E} (hf : f₁ =ᵐ[volume] f₂) (x : V) :
    𝓕⁻ f₁ x = 𝓕⁻ f₂ x := by
  apply integral_congr_ae
  filter_upwards [hf] with _ hf'
  rw [hf']

@[simp]
theorem Lp.fourierTransformInv_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransformInv f x = 𝓕⁻ (f : V → E) x := by
  simp [Lp.fourierTransformInv, fourierInv_eq_fourier_neg]

@[norm_cast]
theorem Lp.coe_fourierTransformInv (f : Lp (α := V) E 1) :
    (Lp.fourierTransformInv f : V → E) = 𝓕⁻ (f : V → E) := by
  ext x
  simp

@[simp]
theorem Lp.fourierTransformInv_toLp {f : V → E} (hf : MemLp f 1) :
    (Lp.fourierTransformInv hf.toLp : V → E) = 𝓕⁻ f := by
  simp only [Lp.coe_fourierTransformInv]
  ext x
  exact (Real.fourierInv_congr_ae hf.coeFn_toLp) x

variable (V E) in
/-- The Fourier transform from `L1` functions to bounded continuous functions as a continuous linear
map. -/
def Lp.fourierTransformInvCLM : Lp (α := V) E 1 →L[ℂ] V →ᵇ E :=
  BoundedContinuousFunction.compContinuousCLM ℂ (-ContinuousMap.id V) ∘L Lp.fourierTransformCLM V E

@[simp]
theorem Lp.fourierTransformInvCLM_apply (f : Lp (α := V) E 1) :
    Lp.fourierTransformInvCLM V E f = Lp.fourierTransformInv f := by
  simp [Lp.fourierTransformInvCLM, Lp.fourierTransformInv]

end Real
