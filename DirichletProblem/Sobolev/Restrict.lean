module

public import Mathlib.Analysis.Distribution.Distribution
public import DirichletProblem.Mathlib.Analysis.Distribution.Sobolev
public import DirichletProblem.Sobolev.SupportedIn
public import Mathlib.Analysis.Distribution.Support

/-! # Sobolev spaces on domains via restriction

In this file we define the space `H^s(Ω)` and prove basic facts. -/



@[expose] public noncomputable section

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

open FourierTransform TemperedDistribution ENNReal MeasureTheory TopologicalSpace
open scoped SchwartzMap CompactConvergenceCLM

-- We do this because we don't want to run through the complexification machinery for every
-- definition
open scoped Distributions in
scoped[MDDistributions] notation "𝓓'^{" n "}(" Ω ", " F ")" => TestFunction Ω ℂ n →L_c[ℂ] F

open scoped Distributions in
scoped[MDDistributions] notation "𝓓'(" Ω ", " F ")" => TestFunction Ω ℂ ⊤ →L_c[ℂ] F

open scoped MDDistributions

namespace ContDiffMapSupportedIn

private
theorem exists_norm_pow_le (K : Compacts E) (n : ℕ) : ∃ (C : ℝ), 0 ≤ C ∧ ∀ x ∈ K, ‖x‖ ^ n ≤ C := by
  obtain ⟨r, hr⟩ := Bornology.IsBounded.subset_ball K.isCompact.isBounded 0
  use (max 1 r) ^ n, by positivity
  intro x hx
  gcongr
  specialize hr hx
  rw [mem_ball_iff_norm, sub_zero] at hr
  grw [hr]
  exact Std.right_le_max

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F] [NormedSpace ℝ E]

variable (𝕜 F) in
def toSchwartzMapLM (K : Compacts E) : ContDiffMapSupportedIn E F ⊤ K →ₗ[𝕜] 𝓢(E, F) where
  toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

@[simp]
theorem coe_toSchwartzMapLM {K : Compacts E}
    (f : ContDiffMapSupportedIn E F ⊤ K) :
    (f.toSchwartzMapLM 𝕜 F K : E → F) = f := rfl

@[simp]
theorem toSchwartzMapLM_apply_apply {K : Compacts E}
    (f : ContDiffMapSupportedIn E F ⊤ K) (x : E) :
    f.toSchwartzMapLM 𝕜 F K x = f x := rfl

variable (𝕜) in
def toSchwartzMapCLM (K : Compacts E) : ContDiffMapSupportedIn E F ⊤ K →L[𝕜] 𝓢(E, F) where
  toLinearMap := toSchwartzMapLM 𝕜 F K
  cont := show Continuous (toSchwartzMapLM 𝕜 F K) by
    apply WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms 𝕜 ..)
      (schwartz_withSeminorms 𝕜 E F) _
    rintro ⟨n, k⟩
    obtain ⟨C, hC_pos, hC⟩ := exists_norm_pow_le K n
    use {k}, ⟨C, hC_pos⟩, fun f ↦ ?_
    simp only [SchwartzMap.schwartzSeminormFamily_apply, Seminorm.comp_apply,
      Finset.sup_singleton, Seminorm.smul_apply, NNReal.smul_def, NNReal.coe_mk, smul_eq_mul]
    apply SchwartzMap.seminorm_le_bound 𝕜 n k _ (by positivity)
    intro x
    by_cases! hx : x ∈ K
    · gcongr
      · exact hC x hx
      · apply norm_iteratedFDeriv_apply_le_seminorm 𝕜 (by simp)
    · -- LHS is zero
      have : iteratedFDeriv ℝ k f x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact hx <| f.tsupport_subset <| tsupport_iteratedFDeriv_subset k h
      simp only [coe_toSchwartzMapLM, this, norm_zero, mul_zero, ge_iff_le]
      positivity

end ContDiffMapSupportedIn

namespace TestFunction

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable (𝕜) in
def toSchwartzMapCLM (Ω : Opens E) : TestFunction Ω F ⊤ →L[𝕜] 𝓢(E, F) :=
  TestFunction.limitCLM 𝕜 (fun f ↦ f.hasCompactSupport.toSchwartzMap f.contDiff)
    (fun K _ ↦ ContDiffMapSupportedIn.toSchwartzMapCLM 𝕜 K) (by intros; rfl)

@[simp]
theorem toSchwartzMapCLM_apply {Ω : Opens E} (f : TestFunction Ω F ⊤) (x : E) :
  f.toSchwartzMapCLM 𝕜 Ω x = f x := rfl

@[simp]
theorem coe_toSchwartzMapCLM {Ω : Opens E} (f : TestFunction Ω F ⊤) :
  (f.toSchwartzMapCLM 𝕜 Ω : E → F) = f := rfl

theorem tsupport_toSchwartzMapCLM_subset {Ω : Opens E} (f : TestFunction Ω F ⊤) :
    tsupport (f.toSchwartzMapCLM 𝕜 Ω) ⊆ Ω :=
  f.tsupport_subset

end TestFunction

variable [InnerProductSpace ℝ E]

namespace TemperedDistribution

variable [NormedSpace ℂ F]

/-- The restriction map from `𝓢'` to `𝓓'`.

Due to the choice of topologies, this map is not continuous. -/
def restrict (Ω : Opens E) : 𝓢'(E, F) →ₗ[ℂ] 𝓓'(Ω, F) where
  toFun u := {
    toFun f := u <| f.toSchwartzMapCLM ℂ Ω
    map_add' := by simp
    map_smul' := by simp
    cont := by fun_prop }
  map_add' u v := rfl
  map_smul' c u := rfl

variable {Ω : Opens E}

@[simp]
theorem restrict_apply (u : 𝓢'(E, F)) (f : TestFunction Ω ℂ ⊤) :
    u.restrict Ω f = u (f.toSchwartzMapCLM ℂ Ω) := rfl

open Distribution

theorem bar' {u : 𝓢'(E, F)} : IsVanishingOn u (dsupport u)ᶜ := by
  -- your proof is in another castle (PR)
  sorry

theorem foo {u : 𝓢'(E, F)} (hu : dsupport u ⊆ Ωᶜ) : u.restrict Ω = 0 := by
  ext f
  simp only [u.restrict_apply, UniformConvergenceCLM.coe_zero, Pi.zero_apply]
  have : IsVanishingOn u Ω := by
    apply bar'.mono
    rwa [Set.subset_compl_comm]
  exact this _ (TestFunction.tsupport_toSchwartzMapCLM_subset _)

theorem eq_of_restrict {f g : 𝓢'(E, F)} {u : 𝓢(E, ℂ)} (h₁ : f.restrict Ω = g.restrict Ω)
    (h₂ : tsupport u ⊆ Ω) : f u = g u := by
  -- Need that smooth compactly supported functions are dense in `𝓢`.

  sorry

end TemperedDistribution

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable [CompleteSpace F]

variable (F) in
/-- The Sobolev space `H^s(Ω)` of all distributions that are restrictions of `H^s(ℝ^n)`
distributions.

We use `H^s(ℝ^n)` in its unbundled form, because we do not care about the topology and
to avoid coercions between `H^s` and `𝓢'`. -/
structure SobolevRestrict [NormedSpace ℂ F] (Ω : Opens E) (s : ℝ) where
  toFun : 𝓓'(Ω, F)
  exists_memSobolev : ∃ u : 𝓢'(E, F), toFun = u.restrict Ω ∧ MemSobolev s 2 u

namespace Sobolev

variable [NormedSpace ℂ F]
variable {Ω : Opens E} {s : ℝ}

def restrict (f : Sobolev E F s 2) (Ω : Opens E) : SobolevRestrict F Ω s where
  toFun := f.toDistr.restrict Ω
  exists_memSobolev := by
    use f.toDistr
    simp [f.memSobolev_toDistr]

@[simp]
theorem toFun_restrict (f : Sobolev E F s 2) (Ω : Opens E) :
    (f.restrict Ω).toFun = f.toDistr.restrict Ω := rfl

end Sobolev

namespace SobolevRestrict

section NormedSpace

variable [NormedSpace ℂ F]
variable {Ω : Opens E} {s : ℝ}

@[ext]
theorem ext {f g : SobolevRestrict F Ω s} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; congr

open Classical in
def chooseSobolev (f : SobolevRestrict F Ω s) : Sobolev E F s 2 :=
  f.exists_memSobolev.choose_spec.2.toSobolev

theorem restrict_toDistr_chooseSobolev {f : SobolevRestrict F Ω s} :
    f.chooseSobolev.toDistr.restrict Ω = f.toFun :=
  f.exists_memSobolev.choose_spec.1.symm

theorem restrict_chooseSobolev {f : SobolevRestrict F Ω s} :
    f.chooseSobolev.restrict Ω = f := by
  ext1
  apply restrict_toDistr_chooseSobolev

theorem bla' {f g : Sobolev E F s 2} (h : f.restrict Ω = g.restrict Ω) :
    f - g ∈ SobolevSupportedIn F s Ω.compl := by
  simp only [Sobolev.mem_SobolevSupportedIn_iff, Sobolev.toDistr_sub, Opens.coe_compl]
  rw [Set.subset_compl_comm]
  intro x hx
  simp only [Set.mem_compl_iff, Distribution.notMem_dsupport_iff]
  use Ω
  simp only [Ω.isOpen, hx, and_self, and_true]
  intro u hu
  simp_rw [SobolevRestrict.ext_iff, Sobolev.toFun_restrict] at h
  simp [eq_of_restrict h hu]

instance : Zero (SobolevRestrict F Ω s) where
  zero := {
    toFun := 0
    exists_memSobolev := by
      use 0
      simp }

instance : Add (SobolevRestrict F Ω s) where
  add f g :=
    { toFun := f.toFun + g.toFun,
      exists_memSobolev := by
        obtain ⟨uf, hf₁, hf₂⟩ := f.exists_memSobolev
        obtain ⟨ug, hg₁, hg₂⟩ := g.exists_memSobolev
        use uf + ug
        simp [hf₂.add hg₂, hf₁, hg₁] }

instance : Sub (SobolevRestrict F Ω s) where
  sub f g :=
    { toFun := f.toFun - g.toFun,
      exists_memSobolev := by
        obtain ⟨uf, hf₁, hf₂⟩ := f.exists_memSobolev
        obtain ⟨ug, hg₁, hg₂⟩ := g.exists_memSobolev
        use uf - ug
        simp [hf₂.sub hg₂, hf₁, hg₁] }

instance : Neg (SobolevRestrict F Ω s) where
  neg f :=
    { toFun := -f.toFun,
      exists_memSobolev := by
        obtain ⟨uf, hf₁, hf₂⟩ := f.exists_memSobolev
        use -uf
        simp [hf₂.neg, hf₁] }

instance : SMul ℂ (SobolevRestrict F Ω s) where
  smul c f :=
    { toFun := c • f.toFun,
      exists_memSobolev := by
        obtain ⟨uf, hf₁, hf₂⟩ := f.exists_memSobolev
        use c • uf
        simp [hf₂.smul c, hf₁] }

instance : AddCommMonoid (SobolevRestrict F Ω s) := sorry

instance : Module ℂ (SobolevRestrict F Ω s) := sorry

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℂ F]
variable {Ω : Opens E} {s : ℝ}

def toSobolev (f : SobolevRestrict F Ω s) : Sobolev E F s 2 :=
    f.chooseSobolev - Sobolev.projectionSupportedIn Ω.compl f.chooseSobolev

theorem toSobolev_spec (f : SobolevRestrict F Ω s) :
    f.toSobolev.toDistr.restrict Ω = f.toFun := by
  rw [← restrict_toDistr_chooseSobolev, toSobolev]
  simp only [Sobolev.toDistr_sub, map_sub, sub_eq_self]
  apply foo
  apply Sobolev.dsupport_projectionSupportedIn_subset

theorem restrict_toSobolev (f : SobolevRestrict F Ω s) :
    f.toSobolev.restrict Ω = f := by
  ext1
  simp [toSobolev_spec]

theorem toSobolev_mem (f : SobolevRestrict F Ω s) :
    f.toSobolev ∈ (SobolevSupportedIn F s Ω.compl)ᗮ := by
  apply Submodule.sub_starProjection_mem_orthogonal

theorem toSobolev_injective : Function.Injective (toSobolev (F := F) (Ω := Ω) (s := s)) := by
  intro f g h
  ext1
  simp_rw [← toSobolev_spec, h]

theorem toSobolev_range :
    Set.range (toSobolev (F := F) (Ω := Ω) (s := s)) = (SobolevSupportedIn F s Ω.compl)ᗮ := by
  ext f
  constructor
  · intro hf
    obtain ⟨f', hf'⟩ := hf
    rw [← hf']
    apply toSobolev_mem
  · intro hf
    simp only [Set.mem_range]
    use f.restrict Ω
    have mem : (f.restrict Ω).toSobolev - f ∈ SobolevSupportedIn F s Ω.compl := by
      apply bla'
      rw [restrict_toSobolev]
    have mem_ortho : (f.restrict Ω).toSobolev - f ∈ (SobolevSupportedIn F s Ω.compl)ᗮ := by
      simp only [SetLike.mem_coe, ← ClosedSubmodule.mem_toSubmodule_iff] at hf
      rw [← ClosedSubmodule.mem_toSubmodule_iff]
      apply sub_mem _ hf
      rw [ClosedSubmodule.mem_toSubmodule_iff]
      apply toSobolev_mem
    have : (f.restrict Ω).toSobolev - f ∈ (⊥ : ClosedSubmodule ℂ _) := by
      rw [← (SobolevSupportedIn F s Ω.compl).inf_orthogonal_eq_bot]
      simp [mem, mem_ortho]
    simpa [ClosedSubmodule.mem_bot, sub_eq_zero]


def toSobolevₗ : SobolevRestrict F Ω s →ₗ[ℂ] Sobolev E F s 2 where
  toFun := toSobolev
  map_add' f g := by
    ext u
    simp
    sorry
  map_smul' := sorry

end InnerProductSpace

end SobolevRestrict
