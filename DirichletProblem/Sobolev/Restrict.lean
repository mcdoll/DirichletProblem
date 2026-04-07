module

public import Mathlib.Analysis.Distribution.Distribution
public import DirichletProblem.Mathlib.Analysis.Distribution.Sobolev

/-! # Sobolev spaces on domains via restriction

In this file we define the space `H^s(Ω)` and prove basic facts. -/



@[expose] public noncomputable section

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

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

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

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

theorem foo (K : Compacts E) (n : ℕ) : ∃ (C : ℝ), 0 ≤ C ∧ ∀ x ∈ K, ‖x‖ ^ n ≤ C := by
  sorry

variable (𝕜) in
def toSchwartzMapCLM (K : Compacts E) : ContDiffMapSupportedIn E F ⊤ K →L[𝕜] 𝓢(E, F) where
  toLinearMap := toSchwartzMapLM 𝕜 F K
  cont := show Continuous (toSchwartzMapLM 𝕜 F K) by
    apply WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms 𝕜 ..)
      (schwartz_withSeminorms 𝕜 E F) _
    rintro ⟨n, k⟩
    obtain ⟨C, hC_pos, hC⟩ := foo K n
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

variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

variable (𝕜) in
def toSchwartzMapCLM (Ω : Opens E) : TestFunction Ω F ⊤ →L[𝕜] 𝓢(E, F) where
  toFun f := f.hasCompactSupport.toSchwartzMap f.contDiff
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp
  cont := by

    sorry

end TestFunction

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

end TemperedDistribution

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

end NormedSpace

end SobolevRestrict
