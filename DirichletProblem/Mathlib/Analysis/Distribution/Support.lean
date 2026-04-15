module

public import Mathlib.Analysis.Distribution.Support

@[expose] public noncomputable section

variable {ι α β 𝕜 E F F₁ F₂ R V : Type*}

namespace Distribution

variable [FunLike F α β] [TopologicalSpace α] [Zero β]

variable {f g : F → V} {s s₁ s₂ : Set α} [Zero V]

variable (F V s) in
@[simp, grind .]
theorem isVanishingOn_zero : IsVanishingOn (0 : F → V) s := by
  simp [IsVanishingOn]

@[simp]
theorem zero_dsupport : dsupport (0 : F → V) = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, notMem_dsupport_iff]
  intro x
  use Set.univ
  simp

end Distribution

variable
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]

/-! ## Tempered distributions -/

namespace TemperedDistribution

open SchwartzMap Distribution TemperedDistribution

variable {f g : 𝓢'(E, F)} {s s₁ s₂ : Set E}

@[grind .]
theorem IsVanishingOn.add (hf : IsVanishingOn f s₁) (hg : IsVanishingOn g s₂) :
    IsVanishingOn (f + g) (s₁ ∩ s₂) := by
  intro u hu
  simp [hf u (hu.trans Set.inter_subset_left), hg u (hu.trans Set.inter_subset_right)]

@[grind .]
theorem IsVanishingOn.smul (c : ℂ) (hf : IsVanishingOn f s₁) :
    IsVanishingOn (c • f) s₁ := by
  intro u hu
  simp [hf u hu]

@[grind =>]
theorem dsupport_add : dsupport (f + g) ⊆ dsupport f ∪ dsupport g := by
  rw [← Set.compl_subset_compl]
  intro u hu
  simp only [Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, notMem_dsupport_iff] at hu ⊢
  obtain ⟨⟨s₁, hs₁, hs₁', hs₁''⟩, ⟨s₂, hs₂, hs₂', hs₂''⟩⟩ := hu
  use s₁ ∩ s₂
  grind [IsOpen.inter]

@[grind =>]
theorem dsupport_smul (c : ℂ) : dsupport (c • f) ⊆ dsupport f := by
  rw [← Set.compl_subset_compl]
  intro u hu
  simp only [Set.mem_compl_iff, notMem_dsupport_iff] at hu ⊢
  peel hu with s hs
  grind

theorem bar' {u : 𝓢'(E, F)} : IsVanishingOn u (dsupport u)ᶜ := by
  -- your proof is in another castle (PR)
  sorry

theorem isVanishingOn_dsupport_subset_compl {Ω : Set E} {u : 𝓢'(E, F)} (hu : dsupport u ⊆ Ωᶜ) :
    IsVanishingOn u Ω := by
  apply bar'.mono
  rwa [Set.subset_compl_comm]

end TemperedDistribution
