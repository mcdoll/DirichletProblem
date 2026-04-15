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

theorem restrict_eq_zero {u : 𝓢'(E, F)} (hu : dsupport u ⊆ Ωᶜ) : u.restrict Ω = 0 := by
  ext f
  exact isVanishingOn_dsupport_subset_compl hu _ (TestFunction.tsupport_toSchwartzMapCLM_subset _)

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

namespace SobolevRestrict

section NormedSpace

variable [NormedSpace ℂ F]
variable {Ω : Opens E} {s : ℝ}

@[ext]
theorem ext {f g : SobolevRestrict F Ω s} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; congr

variable (F Ω s) in
theorem injective_toFun :
    Function.Injective (SobolevRestrict.toFun (F := F) (Ω := Ω) (s := s)) := by
  apply ext

instance : Zero (SobolevRestrict F Ω s) where
  zero := {
    toFun := 0
    exists_memSobolev := by
      use 0
      simp }

@[simp]
theorem toFun_zero : (0 : SobolevRestrict F Ω s).toFun = 0 := rfl

instance : Add (SobolevRestrict F Ω s) where
  add f g :=
    { toFun := f.toFun + g.toFun,
      exists_memSobolev := by
        obtain ⟨uf, hf₁, hf₂⟩ := f.exists_memSobolev
        obtain ⟨ug, hg₁, hg₂⟩ := g.exists_memSobolev
        use uf + ug
        simp [hf₂.add hg₂, hf₁, hg₁] }

@[simp]
theorem toFun_add (f g : SobolevRestrict F Ω s) : (f + g).toFun = f.toFun + g.toFun := rfl

instance : Sub (SobolevRestrict F Ω s) where
  sub f g :=
    { toFun := f.toFun - g.toFun,
      exists_memSobolev := by
        obtain ⟨uf, hf₁, hf₂⟩ := f.exists_memSobolev
        obtain ⟨ug, hg₁, hg₂⟩ := g.exists_memSobolev
        use uf - ug
        simp [hf₂.sub hg₂, hf₁, hg₁] }

@[simp]
theorem toFun_sub (f g : SobolevRestrict F Ω s) : (f - g).toFun = f.toFun - g.toFun := rfl

instance : Neg (SobolevRestrict F Ω s) where
  neg f :=
    { toFun := -f.toFun,
      exists_memSobolev := by
        obtain ⟨uf, hf₁, hf₂⟩ := f.exists_memSobolev
        use -uf
        simp [hf₂.neg, hf₁] }

@[simp]
theorem toFun_neg (f : SobolevRestrict F Ω s) : (-f).toFun = -f.toFun := rfl

variable {R : Type*}
  [SMul R ℂ] [SMul R 𝓢'(E, F)] [SMul R (Lp F 2 (μ := (volume : Measure E)))]
  [SMul R 𝓓'(Ω, F)]
  [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ (Lp F 2 (μ := (volume : Measure E)))]
  [IsScalarTower R ℂ 𝓓'(Ω, F)]

instance : SMul R (SobolevRestrict F Ω s) where
  smul c f :=
    { toFun := c • f.toFun,
      exists_memSobolev := by
        obtain ⟨uf, hf₁, hf₂⟩ := f.exists_memSobolev
        use c • uf
        simp [hf₂.smul c, hf₁] }

@[simp]
theorem toFun_smul (c : R) (f : SobolevRestrict F Ω s) : (c • f).toFun = c • f.toFun := rfl

instance instAddCommGroup : AddCommGroup (SobolevRestrict F Ω s) :=
  (injective_toFun F Ω s).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (F Ω s) in
/-- Coercion as an additive homomorphism. -/
def coeHom : SobolevRestrict F Ω s →+ 𝓓'(Ω, F) where
  toFun f := f.toFun
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeHom_injective : Function.Injective (coeHom F Ω s) := by
  apply ext

instance instModule : Module ℂ (SobolevRestrict F Ω s) :=
  coeHom_injective.module ℂ (coeHom F Ω s) fun _ _ => rfl

end NormedSpace

end SobolevRestrict

namespace Sobolev

variable [NormedSpace ℂ F]
variable {Ω : Opens E} {s : ℝ}

def restrict (Ω : Opens E) : Sobolev E F s 2 →ₗ[ℂ] SobolevRestrict F Ω s where
  toFun f :=
    { toFun := f.toDistr.restrict Ω,
      exists_memSobolev := by
        use f.toDistr
        simp [f.memSobolev_toDistr] }
  map_add' := by intros; ext1; simp
  map_smul' := by intros; ext1; simp

@[simp]
theorem toFun_restrict (f : Sobolev E F s 2) (Ω : Opens E) :
    (f.restrict Ω).toFun = f.toDistr.restrict Ω := rfl

theorem restrict_eq_zero_of_dsupport {f : Sobolev E F s 2}
    (hf : Distribution.dsupport f.toDistr ⊆ Ωᶜ) : f.restrict Ω = 0 := by
  ext1
  simpa using restrict_eq_zero hf

end Sobolev

namespace SobolevRestrict

section NormedSpace

variable [NormedSpace ℂ F]
variable {Ω : Opens E} {s : ℝ}

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
  apply restrict_eq_zero
  apply Sobolev.dsupport_projectionSupportedIn_subset

theorem restrict_toSobolev (f : SobolevRestrict F Ω s) :
    f.toSobolev.restrict Ω = f := by
  ext1
  simp [toSobolev_spec]

theorem toSobolev_mem (f : SobolevRestrict F Ω s) :
    f.toSobolev ∈ (SobolevSupportedIn F s Ω.compl)ᗮ := by
  apply Submodule.sub_starProjection_mem_orthogonal

theorem toSobolev_restrict {f : Sobolev E F s 2} (hf : f ∈ (SobolevSupportedIn F s Ω.compl)ᗮ) :
    (f.restrict Ω).toSobolev = f := by
  have mem : (f.restrict Ω).toSobolev - f ∈ SobolevSupportedIn F s Ω.compl := by
    apply bla'
    rw [restrict_toSobolev]
  have mem_ortho : (f.restrict Ω).toSobolev - f ∈ (SobolevSupportedIn F s Ω.compl)ᗮ := by
    simp only [← ClosedSubmodule.mem_toSubmodule_iff] at hf
    rw [← ClosedSubmodule.mem_toSubmodule_iff]
    apply sub_mem _ hf
    rw [ClosedSubmodule.mem_toSubmodule_iff]
    apply toSobolev_mem
  have : (f.restrict Ω).toSobolev - f ∈ (⊥ : ClosedSubmodule ℂ _) := by
    rw [← (SobolevSupportedIn F s Ω.compl).inf_orthogonal_eq_bot]
    simp [mem, mem_ortho]
  simpa [ClosedSubmodule.mem_bot, sub_eq_zero]

theorem toSobolev_injective : Function.Injective (toSobolev (F := F) (Ω := Ω) (s := s)) := by
  intro f g h
  ext1
  simp_rw [← toSobolev_spec, h]

-- unclear if needed
theorem dsupport_toSobolev (f : SobolevRestrict F Ω s) :
    Distribution.dsupport f.toSobolev.toDistr ⊆ Ω := by
  sorry

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
    apply toSobolev_restrict hf

variable (F Ω s) in
def _root_.Sobolev.supportedIn_toSobolevRestrict :
    (SobolevSupportedIn F s Ω.compl)ᗮ.toSubmodule ≃ₗ[ℂ] SobolevRestrict F Ω s where
  toFun f := f.1.restrict Ω
  map_add' f g := by
    ext1
    simp
    -- some lemma is missing here:
    rfl
  map_smul' c f := by
    ext1
    simp
    -- some lemma is missing here:
    rfl
  invFun f := ⟨f.toSobolev, f.toSobolev_mem⟩
  left_inv f := by
    obtain ⟨f, hf⟩ := f
    simp [toSobolev_restrict hf]
  right_inv f := by
    simpa using restrict_toSobolev f

theorem toSobolev_add (f g : SobolevRestrict F Ω s) :
    (f + g).toSobolev = f.toSobolev + g.toSobolev := by
  have := map_add (Sobolev.supportedIn_toSobolevRestrict F Ω s).symm f g
  rw [Subtype.ext_iff] at this
  exact this

theorem toSobolev_smul (c : ℂ) (f : SobolevRestrict F Ω s) :
    (c • f).toSobolev = c • f.toSobolev := by
  have := map_smul (Sobolev.supportedIn_toSobolevRestrict F Ω s).symm c f
  rw [Subtype.ext_iff] at this
  exact this

@[simp]
theorem _root_.Sobolev.supportedIn_toSobolevRestrict_apply
    (f : (SobolevSupportedIn F s Ω.compl)ᗮ.toSubmodule) :
    Sobolev.supportedIn_toSobolevRestrict F Ω s f = f.1.restrict Ω := rfl

@[simp]
theorem _root_.Sobolev.supportedIn_toSobolevRestrict_symm_apply
    (f : SobolevRestrict F Ω s) :
    (Sobolev.supportedIn_toSobolevRestrict F Ω s).symm f = ⟨f.toSobolev, f.toSobolev_mem⟩ := rfl

variable (F Ω s) in
def toSobolevₗ : SobolevRestrict F Ω s →ₗ[ℂ] Sobolev E F s 2 :=
  Submodule.subtype _ ∘ₗ (Sobolev.supportedIn_toSobolevRestrict F Ω s).symm.toLinearMap

@[simp]
theorem toSobolevₗ_apply (f : SobolevRestrict F Ω s) : f.toSobolevₗ F Ω s = f.toSobolev := rfl

variable (F Ω s) in
theorem injective_toSobolevₗ : Function.Injective (toSobolevₗ F Ω s) := by
  simpa [toSobolevₗ] using
    EmbeddingLike.injective (Sobolev.supportedIn_toSobolevRestrict F Ω s).symm

instance instNormedAddCommGroup :
    NormedAddCommGroup (SobolevRestrict F Ω s) :=
  NormedAddCommGroup.induced (SobolevRestrict F Ω s) ((SobolevSupportedIn F s Ω.compl)ᗮ.toSubmodule)
    (Sobolev.supportedIn_toSobolevRestrict F Ω s).symm.toLinearMap
    (Sobolev.supportedIn_toSobolevRestrict F Ω s).symm.injective

theorem foo (y : SobolevRestrict F Ω s) :
    ‖(Sobolev.supportedIn_toSobolevRestrict F Ω s).symm y‖ = ‖y‖ := rfl

theorem norm_toSobolev (y : SobolevRestrict F Ω s) :
    ‖y.toSobolev‖ = ‖y‖ := rfl

instance instNormedSpace :
    NormedSpace ℂ (SobolevRestrict F Ω s) where
  norm_smul_le c f := by
    simp_rw [← norm_toSobolev, ← norm_smul, toSobolev_smul]
    rfl

instance instInnerProductSpace (s : ℝ) :
    InnerProductSpace ℂ (SobolevRestrict F Ω s) where
  inner f g := inner ℂ f.toSobolev g.toSobolev
  norm_sq_eq_re_inner f := by simp; norm_cast
  conj_inner_symm f g := by simp
  add_left f g h := by rw [toSobolev_add, inner_add_left]
  smul_left f g c := by rw [toSobolev_smul, inner_smul_left]

variable (F Ω s) in
def _root_.Sobolev.toSobolevRestrict :
  (SobolevSupportedIn F s Ω.compl)ᗮ.toSubmodule ≃ₗᵢ[ℂ] SobolevRestrict F Ω s where
  __ := Sobolev.supportedIn_toSobolevRestrict F Ω s
  norm_map' x := calc
    _ = ‖(Sobolev.supportedIn_toSobolevRestrict F Ω s).symm <|
        (Sobolev.supportedIn_toSobolevRestrict F Ω s) x‖ := by
      rw [foo]
    _ = ‖x‖ := by
      congr
      exact (Sobolev.supportedIn_toSobolevRestrict F Ω s).symm_apply_apply x

@[simp]
theorem _root_.Sobolev.toSobolevRestrict_apply
    (f : (SobolevSupportedIn F s Ω.compl)ᗮ) :
    Sobolev.toSobolevRestrict F Ω s f = f.1.restrict Ω := rfl

@[simp]
theorem _root_.Sobolev.toSobolevRestrict_symm_apply
    (f : SobolevRestrict F Ω s) :
    (Sobolev.toSobolevRestrict F Ω s).symm f = ⟨f.toSobolev, f.toSobolev_mem⟩ := rfl

variable (F Ω s) in
def _root_.Sobolev.restrictCLM : Sobolev E F s 2 →L[ℂ] SobolevRestrict F Ω s :=
  (Sobolev.toSobolevRestrict F Ω s).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (SobolevSupportedIn F s Ω.compl)ᗮ.orthogonalProjection

set_option backward.isDefEq.respectTransparency false in
-- defeq abuse in coercions between closed submodules and orthogonality
theorem root_.Sobolev.restrictCLM_apply_of_mem {f : Sobolev E F s 2}
    (hf : f ∈ SobolevSupportedIn F s Ω.compl) : f.restrictCLM F Ω s = 0 := by
  have := Submodule.orthogonalProjection_eq_zero_iff
    (K := (SobolevSupportedIn F s Ω.compl)ᗮ.toSubmodule) (v := f)
  simp only [ClosedSubmodule.toSubmodule_orthogonal_eq, Submodule.orthogonal_orthogonal] at this
  simp [Sobolev.restrictCLM, this.mpr hf]

set_option backward.isDefEq.respectTransparency false in
-- defeq abuse in coercions between closed submodules and orthogonality
theorem root_.Sobolev.restrictCLM_apply_of_mem_orthogonal {f : Sobolev E F s 2}
    (hf : f ∈ (SobolevSupportedIn F s Ω.compl)ᗮ) : f.restrictCLM F Ω s = f.restrict Ω := by
  have := Submodule.orthogonalProjection_mem_subspace_eq_self ⟨f, hf⟩
  simp only [ClosedSubmodule.toSubmodule_orthogonal_eq] at this
  simp [Sobolev.restrictCLM, this]
  rfl

@[simp]
theorem root_.Sobolev.restrictCLM_apply (f : Sobolev E F s 2) :
    f.restrictCLM F Ω s = f.restrict Ω := by
  obtain ⟨f₁, hf₁, f₂, hf₂, h⟩ :=
    Submodule.exists_add_mem_mem_orthogonal f (K := (SobolevSupportedIn F s Ω.compl)ᗮ.toSubmodule)
  simp only [ClosedSubmodule.toSubmodule_orthogonal_eq] at hf₁ hf₂
  simp only [Submodule.orthogonal_orthogonal] at hf₂
  simpa [h, Sobolev.restrictCLM_apply_of_mem_orthogonal hf₁, Sobolev.restrictCLM_apply_of_mem hf₂]
    using Sobolev.restrict_eq_zero_of_dsupport hf₂

end InnerProductSpace

end SobolevRestrict
