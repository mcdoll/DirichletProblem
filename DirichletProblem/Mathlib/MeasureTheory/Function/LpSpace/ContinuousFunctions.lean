/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Embedding of continuous functions into `L∞` -/

@[expose] public noncomputable section

open BoundedContinuousFunction MeasureTheory Filter
open scoped ENNReal

variable {𝕜 α E : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [TopologicalSpace α] [BorelSpace α] [NormedAddCommGroup E] [SecondCountableTopologyEither α E]

variable [RCLike 𝕜] [NormedSpace 𝕜 E]

namespace BoundedContinuousFunction

variable (𝕜 μ) in
/-- The map from bounded continuous functions to `Lp` with `p = ⊤` as a continuous linear map. -/
def toLp_top : (α →ᵇ E) →L[𝕜] Lp E ⊤ μ :=
  LinearMap.mkContinuous
    { toFun f := f.memLp_top.toLp
      map_add' f g := by
        grind [coe_add, MeasureTheory.MemLp.toLp_add]
      map_smul' c f:= by
        simp only [coe_smul, RingHom.id_apply] -- `coe_smul` is bad, should be `↑(c • f) = c • ↑f`
        apply MeasureTheory.MemLp.toLp_const_smul } 1 <| by
    intro f
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp, eLpNorm_exponent_top, one_mul]
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
      ENNReal.ofReal_toReal (by apply (memLp_top f).eLpNorm_ne_top)]
    grind [eLpNormEssSup_le_of_ae_bound, Eventually.of_forall, norm_coe_le_norm]

@[simp]
theorem toLp_top_apply (f : α →ᵇ E) : toLp_top 𝕜 μ f = f.memLp_top.toLp := rfl

end BoundedContinuousFunction
