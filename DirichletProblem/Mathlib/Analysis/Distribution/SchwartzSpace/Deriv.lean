/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Missing integration by parts lemmas

-/

public noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E]
  [InnerProductSpace 𝕜 F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped InnerProductSpace SchwartzMap

open MeasureTheory

open scoped LineDeriv Laplacian

variable {μ : Measure E} [μ.IsAddHaarMeasure]

local instance InnerProductSpace.instRCLikeToReal : InnerProductSpace ℝ F :=
  InnerProductSpace.rclikeToReal 𝕜 F

variable (𝕜 F) in
private def innerRealₗ : F →ₗ[ℝ] F →ₗ[ℝ] 𝕜 :=
  LinearMap.mk₂ ℝ (inner 𝕜) ?_ ?_ ?_ ?_
where finally
  · simp [inner_add_left]
  · intro c x y
    convert inner_smul_left x y (c : 𝕜)
    · rfl
    · rw [RCLike.conj_ofReal]
      rfl
  · simp [inner_add_right]
  · intro c x y
    convert inner_smul_right x y (c : 𝕜)
    · rfl
    · rfl

@[simp]
private theorem innerRealₗ_apply (x y : F) : innerRealₗ 𝕜 F x y = inner 𝕜 x y := rfl

variable (𝕜 F) in
private def innerRealL : F →L[ℝ] F →L[ℝ] 𝕜 :=
  LinearMap.mkContinuous₂ (innerRealₗ 𝕜 F) 1 (by simpa using norm_inner_le_norm)

namespace SchwartzMap

/-- Integration by parts of Schwartz functions for directional derivatives.

Version for the inner product. -/
theorem integral_inner_lineDerivOp_right_eq_neg_left (f : 𝓢(E, F)) (g : 𝓢(E, F)) (v : E) :
    ∫ (x : E), ⟪f x, ∂_{v} g x⟫_𝕜 ∂μ = -∫ (x : E), ⟪∂_{v} f x, g x⟫_𝕜 ∂μ := by
  apply integral_bilinear_lineDerivOp_right_eq_neg_left f g (innerRealL 𝕜 F) v

/-- Integration by parts of Schwartz functions for the Laplacian.

Version for the inner product. -/
theorem integral_inner_laplacian_right_eq_left (f : 𝓢(E, F)) (g : 𝓢(E, F)) :
    ∫ (x : E), ⟪f x, Δ g x⟫_𝕜 ∂μ = ∫ (x : E), ⟪Δ f x, g x⟫_𝕜 ∂μ := by
  apply integral_bilinear_laplacian_right_eq_left f g (innerRealL 𝕜 F)

end SchwartzMap
