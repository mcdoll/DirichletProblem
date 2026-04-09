module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

variable {ι 𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

open SchwartzMap
open scoped Topology

variable {f : 𝓢(E, F)} {g : 𝓢(E, 𝕜)} {c : 𝕜}

theorem foo {g : 𝓢(E, 𝕜)} (hg : g 0 = 1) :
    Filter.Tendsto (fun (r : ℝ) ↦ smulLeftCLM F (g <| r⁻¹ • · ) f) Filter.atTop (𝓝 f) := by
  rw [(_root_.schwartz_withSeminorms 𝕜 E F).tendsto_nhds_atTop]
  intro ⟨k, n⟩ ε hε
  /-use 1
  intro r hr
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply seminorm_le_bound _ _ _ _ (half_pos hε).le
  intro x-/
  sorry
