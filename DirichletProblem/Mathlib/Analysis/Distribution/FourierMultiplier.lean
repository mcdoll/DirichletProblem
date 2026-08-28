/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier

/-! # Fourier multiplier on Schwartz functions and tempered distributions -/


@[expose] public noncomputable section

variable {ι 𝕜 E F : Type*}

namespace SchwartzMap

/-! ## Schwartz functions -/

open scoped SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

theorem fourierMultiplierCLM_add_apply {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (g₁ + g₂) f =
      fourierMultiplierCLM F g₁ f + fourierMultiplierCLM F g₂ f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_add hg₁ hg₂]

variable (F) in
theorem fourierMultiplierCLM_add {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext1 f
  exact fourierMultiplierCLM_add_apply hg₁ hg₂ f

end SchwartzMap

namespace TemperedDistribution

/-! ## Tempered distributions -/

open scoped SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

theorem fourierMultiplierCLM_add_apply {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F (g₁ + g₂) f =
      fourierMultiplierCLM F g₁ f + fourierMultiplierCLM F g₂ f := by
  ext u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

variable (F) in
theorem fourierMultiplierCLM_add {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F (g₁ + g₂) = fourierMultiplierCLM F g₁ + fourierMultiplierCLM F g₂ := by
  ext f : 1
  exact fourierMultiplierCLM_add_apply hg₁ hg₂ f

end TemperedDistribution
