module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
--public import Mathlib.Analysis.Normed.Lp.ProdLp

@[expose] public noncomputable section

variable {ι 𝕜 D E E' F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] --[NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] --[NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

namespace SchwartzMap
open scoped Topology

variable {f : 𝓢(E, F)} {g : 𝓢(E, 𝕜)} {c : 𝕜}

variable (𝕜) in
/-- Composition with a continuous linear equiv on the right is a continuous linear map on
Schwartz space. -/
def compCLEOfContinuousLinearEquiv (g : D ≃L[ℝ] E) :
    𝓢(E, F) ≃L[𝕜] 𝓢(D, F) :=
  ContinuousLinearEquiv.equivOfInverse (compCLMOfContinuousLinearEquiv 𝕜 g)
    (compCLMOfContinuousLinearEquiv 𝕜 g.symm) ?_ ?_
where finally
  all_goals { intro; ext; simp }

@[simp]
lemma compCLEOfContinuousLinearEquiv_apply (g : D ≃L[ℝ] E) (f : 𝓢(E, F)) :
    compCLEOfContinuousLinearEquiv 𝕜 g f = f ∘ g := rfl

@[simp]
lemma compCLEOfContinuousLinearEquiv_symm_apply (g : D ≃L[ℝ] E) (f : 𝓢(D, F)) :
    (compCLEOfContinuousLinearEquiv 𝕜 g).symm f = f ∘ g.symm := rfl

open ENNReal

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (𝕜 p) in
def precompProdLp : 𝓢(E × E', F) ≃L[𝕜] 𝓢(WithLp p (E × E'), F) :=
  compCLEOfContinuousLinearEquiv 𝕜 (WithLp.prodContinuousLinearEquiv p ℝ E E')
  --sorry

@[simp]
theorem precompProdLp_apply (f : 𝓢(E × E', F)) (x : WithLp p (E × E')) :
  f.precompProdLp 𝕜 p x = f (x.ofLp) := rfl

@[simp]
theorem precompProdLp_symm_apply (f : 𝓢(WithLp p (E × E'), F)) (x : E × E') :
  (precompProdLp 𝕜 p).symm f x = f (WithLp.toLp p x) := rfl

variable (𝕜 E' F) in
def restrictSnd (a : E) : 𝓢(E × E', F) →L[𝕜] 𝓢(E', F) :=
  compCLMOfAntilipschitz (g := fun x ↦ (a, x)) (K := 1) 𝕜 ?_ ?_
where finally
  · apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖a‖)
    · have : fderiv ℝ (fun (x : E') ↦ (a, x)) =
          fun _ ↦ (0 : E' →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E') := by
        ext x : 1
        rw [DifferentiableAt.fderiv_prodMk (by fun_prop) (by fun_prop)]
        simp
      rw [this]
      fun_prop
    · fun_prop
    · intro x
      simp only [Prod.norm_mk, pow_one, sup_le_iff]
      constructor
      · ring_nf
        move_add [‖a‖]
        rw [le_add_iff_nonneg_left]
        positivity
      · ring_nf
        rw [le_add_iff_nonneg_left]
        positivity
  · intro x y
    simp [edist_dist, dist_eq_norm]

variable (𝕜 E F) in
def restrictFst (a : E') : 𝓢(E × E', F) →L[𝕜] 𝓢(E, F) :=
  compCLMOfAntilipschitz (g := fun x ↦ (x, a)) (K := 1) 𝕜 ?_ ?_
where finally
  · apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖a‖)
    · have : fderiv ℝ (fun (x : E) ↦ (x, a)) =
          fun _ ↦ (ContinuousLinearMap.id ℝ E).prod 0 := by
        ext x : 1
        rw [DifferentiableAt.fderiv_prodMk (by fun_prop) (by fun_prop)]
        simp
      rw [this]
      fun_prop
    · fun_prop
    · intro x
      simp only [Prod.norm_mk, pow_one, sup_le_iff]
      constructor
      · ring_nf
        rw [le_add_iff_nonneg_left]
        positivity
      · ring_nf
        move_add [‖a‖]
        rw [le_add_iff_nonneg_left]
        positivity
  · intro x y
    simp [edist_dist, dist_eq_norm]

end SchwartzMap
