module

public import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Filter Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variable {l l' : Filter α}

theorem isBigO_cocompact_iff [TopologicalSpace α] : f =O[cocompact α] g'' ↔
    ∃ c > 0, ∃ s, IsCompact s ∧ ∀ y ∈ sᶜ, ‖f y‖ ≤ c * ‖g'' y‖ := by
  rw [isBigO_iff']
  congrm (∃ c > 0, ?_)
  simp_rw [eventually_iff_exists_mem, Filter.mem_cocompact]
  constructor
  · intro ⟨s, ⟨t, ht, hs⟩, h⟩
    exact ⟨t, ht, fun y hy ↦ h y (hs hy)⟩
  · intro ⟨s, hs, h⟩
    exact ⟨sᶜ, ⟨s, hs, by rfl⟩, h⟩
