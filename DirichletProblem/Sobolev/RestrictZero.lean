/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DirichletProblem.Sobolev.Restrict

/-! # Sobolev spaces on domains via restriction with zero boundary values

In this file we define the space `H^s_0(Ω)` and prove basic facts. -/

@[expose] public noncomputable section

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace 𝕜 F] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [InnerProductSpace ℂ F]

open FourierTransform TemperedDistribution ENNReal MeasureTheory TopologicalSpace
open scoped SchwartzMap CompactConvergenceCLM

variable {Ω : Opens E} {s : ℝ}

variable (F Ω s) in
/-- The space `H^s_0` -/
abbrev SobolevRestrictZero := (TestFunction.toSobolevRestrict F Ω s).range.closure
