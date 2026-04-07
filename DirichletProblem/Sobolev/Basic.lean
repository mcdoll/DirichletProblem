/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DirichletProblem.Mathlib.Analysis.Distribution.Sobolev
public import DirichletProblem.Mathlib.Analysis.Fourier.ZeroAtInfty
public import DirichletProblem.Mathlib.Analysis.Distribution.TemperedDistribution

@[expose] public noncomputable section

namespace TemperedDistribution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℂ F] [CompleteSpace F]

open scoped SchwartzMap ZeroAtInfty FourierTransform

/-- *Sobolev embedding theorem*: a Sobolev function of order `s` with `s > d / 2` can be represented
by a `C₀(E, F)` function. -/
theorem MemSobolev.zeroAtInfty {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) :
    ∃ (v : C₀(E, F)), f  = v.toBCF.toTemperedDistribution := by
  obtain ⟨g, hg⟩ := hf.fourier_memL1 hs
  use Real.Lp.fourierTransformInvZeroAtInftyCLM E F g
  simp [← MeasureTheory.Lp.fourierInv_toTemperedDistributionCLM_eq, ← hg]

end TemperedDistribution
