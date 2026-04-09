module

public import DirichletProblem.Sobolev.Basic
public import Mathlib.Analysis.Distribution.Support

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F]

open TopologicalSpace Distribution

section normed

variable [NormedSpace ℂ F]

variable {s : ℝ}

variable (F s) in
def SobolevSupportedIn (K : Closeds E) : ClosedSubmodule ℂ (Sobolev E F s 2) where
  carrier := { f | dsupport f.toDistr ⊆ K }
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, Sobolev.toDistr_add]
    sorry
  zero_mem' := by
    simp
    sorry
  smul_mem' c {f} hf := by
    simp
    sorry
  isClosed' := by
    refine IsSeqClosed.isClosed ?_
    intro a f ha haf
    simp only [Set.mem_setOf_eq] at ha ⊢
    intro x hx
    sorry

@[simp]
theorem Sobolev.mem_SobolevSupportedIn_iff {K : Closeds E} (u : Sobolev E F s 2) :
    u ∈ SobolevSupportedIn F s K ↔ dsupport u.toDistr ⊆ K := by rfl

end normed

section inner

variable [InnerProductSpace ℂ F]

variable {s : ℝ} {K : Closeds E}

namespace Sobolev

--variable (E F s) in
def projectionSupportedIn (K : Closeds E) : Sobolev E F s 2 →L[ℂ] Sobolev E F s 2 :=
  (SobolevSupportedIn F s K).toSubmodule.starProjection

theorem projectionSupportedIn_eq_self_iff {K : Closeds E} (u : Sobolev E F s 2) :
    u.projectionSupportedIn K = u ↔ dsupport u.toDistr ⊆ K :=
  Submodule.starProjection_eq_self_iff

theorem dsupport_projectionSupportedIn_subset {K : Closeds E} (u : Sobolev E F s 2) :
    dsupport (u.projectionSupportedIn K).toDistr ⊆ K := by
  rw [← Sobolev.mem_SobolevSupportedIn_iff]
  apply Submodule.starProjection_apply_mem

end Sobolev

end inner
