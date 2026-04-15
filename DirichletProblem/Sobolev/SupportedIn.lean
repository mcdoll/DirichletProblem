module

public import DirichletProblem.Sobolev.Basic
public import DirichletProblem.Mathlib.Analysis.Distribution.Support

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F]

open TopologicalSpace Distribution

section normed

variable [NormedSpace ℂ F]

variable {s : ℝ}

open FourierTransform

variable (F s) in
def SobolevSupportedIn (K : Closeds E) : ClosedSubmodule ℂ (Sobolev E F s 2) where
  carrier := { f | dsupport f.toDistr ⊆ K }
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, Sobolev.toDistr_add]
    grw [TemperedDistribution.dsupport_add]
    grind
  zero_mem' := by simp
  smul_mem' c {f} hf := by
    simp only [Set.mem_setOf_eq, Sobolev.toDistr_smul]
    grw [TemperedDistribution.dsupport_smul]
    exact hf
  isClosed' := by
    refine IsSeqClosed.isClosed ?_
    intro a f ha haf
    simp only [Set.mem_setOf_eq] at ha ⊢
    intro x hx
    rw [mem_dsupport_iff_forall_exists_ne] at hx
    by_contra h
    obtain ⟨u, hu₁, hu₂⟩ := hx K.compl h K.compl.isOpen
    apply hu₂
    have ha' : ∀ n, (a n).toDistr u = 0 := by
      intro n
      specialize ha n
      apply TemperedDistribution.bar'
      grw [hu₁]
      rwa [← Set.compl_subset_compl] at ha
    apply tendsto_nhds_unique _ (tendsto_atTop_of_eventually_const (i₀ := 0) (fun x _ ↦ ha' x))
    simp only [Sobolev.toDistr_apply]
    exact ((ContinuousLinearMap.cont _).comp (by fun_prop) |>.tendsto f).comp haf

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
