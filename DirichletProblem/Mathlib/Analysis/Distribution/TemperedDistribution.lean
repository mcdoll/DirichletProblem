module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import DirichletProblem.Mathlib.Analysis.Asymptotics.Lemmas
public import DirichletProblem.Mathlib.Analysis.Fourier.FourierTransform
public import DirichletProblem.Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import DirichletProblem.Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

@[expose] public noncomputable section

open SchwartzMap ContinuousLinearMap MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {ι 𝕜 E F F₁ F₂ : Type*}

namespace MeasureTheory.LocallyIntegrable

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

open Asymptotics Filter

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [hμ : μ.HasTemperateGrowth]

theorem integrable_schwartzMap_smul {f : E → F} {k : ℕ} (hf : LocallyIntegrable f μ)
    (hf' : f =O[cocompact E] (‖·‖ ^ k)) (g : 𝓢(E, ℂ)) :
    Integrable (fun x ↦ g x • f x) μ := by
  obtain ⟨c, _hc, s, hs₁, hs₂⟩ := isBigO_cocompact_iff.mp hf'
  simp only [Set.mem_compl_iff, norm_pow, norm_norm] at hs₂
  have h₁ : IntegrableOn (fun x ↦ g x • f x) sᶜ μ := by
    have h_int := ((g.integrable_pow_mul μ k).integrableOn (s := sᶜ)).smul c
    have := hf.aestronglyMeasurable
    apply h_int.mono' (by fun_prop)
    rw [MeasureTheory.ae_restrict_iff₀]
    · filter_upwards with x hx
      simp only [norm_smul, Pi.smul_apply, smul_eq_mul]
      grw [hs₂ x hx]
      apply le_of_eq
      ring
    exact AEStronglyMeasurable.nullMeasurableSet_le (by fun_prop) (by fun_prop)
  have h₂ : IntegrableOn (fun x ↦ g x • f x) s μ :=
    (hf.integrableOn_isCompact hs₁).continuousOn_smul (by fun_prop) hs₁
  rw [← MeasureTheory.integrableOn_univ, ← Set.union_compl_self s]
  exact h₂.union h₁

--set_option backward.isDefEq.respectTransparency false in
--set_option backward.privateInPublic true in
def toTemperedDistribution {f : E → F} {k : ℕ} (hf : LocallyIntegrable f μ)
    (hf' : f =O[Filter.cocompact E] (‖·‖ ^ k)) : 𝓢'(E, F) :=
  toPointwiseConvergenceCLM _ _ _ _ <|
    SchwartzMap.mkCLMtoNormedSpace (fun g ↦ ∫ x, g x • f x ∂μ) ?_ ?_ ?_
where finally
  · intro g₁ g₂
    simp only [SchwartzMap.add_apply, add_smul]
    apply integral_add (hf.integrable_schwartzMap_smul hf' g₁)
      (hf.integrable_schwartzMap_smul hf' g₂)
  · intro c g
    simp only [SchwartzMap.smul_apply, smul_assoc, RingHom.id_apply]
    apply integral_smul
  · obtain ⟨c, _hc, s, hs₁, hs₂⟩ := isBigO_cocompact_iff.mp hf'
    simp only [Set.mem_compl_iff, norm_pow, norm_norm] at hs₂
    set C₁ := ∫ (a : E) in s, ‖f a‖ ∂μ
    have hC₁ : 0 ≤ C₁ := by positivity
    set C₂ := c * 2 ^ μ.integrablePower * ∫ (x : E), ((1 + ‖x‖) ^ μ.integrablePower)⁻¹ ∂μ
    use {(0,0), (k + μ.integrablePower, 0)}, 2 * (C₁ + C₂), by positivity
    intro g
    set k₁ := g.seminorm ℂ 0 0
    set k₂ := g.seminorm ℂ (k + μ.integrablePower) 0
    have hs : ‖∫ x in s, g x • f x ∂μ‖ ≤ C₁ * k₁ := calc
      _ ≤ ∫ x in s, ‖g x • f x‖ ∂μ := by
        grw [MeasureTheory.norm_integral_le_integral_norm]
      _ ≤ ∫ x in s, k₁ * ‖f x‖ ∂μ := by
        simp_rw [norm_smul]
        have hf : IntegrableOn (‖f ·‖) s μ :=
          MeasureTheory.Integrable.norm (hf.integrableOn_isCompact hs₁)
        apply MeasureTheory.setIntegral_mono_on (hf.continuousOn_mul (by fun_prop) hs₁)
          (hf.const_mul _) hs₁.measurableSet
        intro x _hx
        grw [norm_le_seminorm ℂ g]
      _ ≤ _ := by
        rw [integral_const_mul, mul_comm]
    have hsc : ‖∫ (x : E) in sᶜ, g x • f x ∂μ‖ ≤ C₂ * (k₁ + k₂) := calc
      _ ≤ ∫ x in sᶜ, ‖g x • f x‖ ∂μ := by
        grw [MeasureTheory.norm_integral_le_integral_norm]
      _ ≤ ∫ x in sᶜ, c * (‖x‖ ^ k * ‖g x‖) ∂μ := by
        apply setIntegral_mono_on (hf.integrable_schwartzMap_smul hf' g).integrableOn.norm
          ((integrable_pow_mul μ g k).integrableOn.const_mul _) hs₁.measurableSet.compl
        intro x hx
        simp_rw [norm_smul]
        grw [hs₂ x hx]
        apply le_of_eq
        ring
      _ ≤ c * ∫ x, ‖x‖ ^ k * ‖g x‖ ∂μ := by
        simp_rw [integral_const_mul]
        gcongr
        · filter_upwards with
          positivity
        · exact integrable_pow_mul μ g k
        · exact restrict_le_self
      _ ≤ _ := by
        have := integral_pow_mul_iteratedFDeriv_le ℂ μ g k 0
        simp only [norm_iteratedFDeriv_zero, Real.rpow_neg_natCast, zpow_neg, zpow_natCast] at this
        grw [this]
        apply le_of_eq
        ring
    calc
      _ = ‖∫ (x : E), g x • f x ∂μ‖ := rfl
      _ ≤ ‖∫ x in s, g x • f x ∂μ‖ + ‖∫ x in sᶜ, g x • f x ∂μ‖ := by
        rw [← MeasureTheory.integral_add_compl₀ hs₁.nullMeasurableSet
          (hf.integrable_schwartzMap_smul hf' g)]
        apply norm_add_le
      _ ≤ C₁ * k₁ + C₂ * (k₁ + k₂) := by
        grw [hs, hsc]
      _ = (C₁ + C₂) * k₁ + C₂ * k₂ := by ring
      _ ≤ (C₁ + C₂) * k₁ + (C₁ + C₂) * k₂ := by
        gcongr
        grw [← hC₁]
        simp
      _ = (C₁ + C₂) * (k₁ + k₂) := by ring
      _ ≤ (C₁ + C₂) * (2 * max k₁ k₂) := by
        gcongr
        grind
      _ = 2 * (C₁ + C₂) * (max k₁ k₂) := by ring
      _ = _ := by
        simp [k₁, k₂]

@[simp]
theorem toTemperedDistribution_apply {f : E → F} {k : ℕ} (hf : LocallyIntegrable f μ)
    (hf' : f =O[Filter.cocompact E] (‖·‖ ^ k)) (g : 𝓢(E, ℂ)) :
    hf.toTemperedDistribution hf' g = ∫ x, g x • f x ∂μ := rfl

end MeasureTheory.LocallyIntegrable

namespace BoundedContinuousFunction

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] [IsLocallyFiniteMeasure μ]

variable {μ : Measure E} in
@[fun_prop]
theorem integrable_schwartzMap_smul [hμ : μ.HasTemperateGrowth] [IsLocallyFiniteMeasure μ]
    (f : E →ᵇ F) (g : 𝓢(E, ℂ)) :
    Integrable (fun x ↦ g x • f x) μ := by
  apply (map_continuous f).locallyIntegrable.integrable_schwartzMap_smul (k := 0)
  rw [isBigO_cocompact_iff]
  use ‖f‖ + 1
  refine ⟨by positivity, ?_⟩
  use ∅, by simp
  intro x _
  grw [BoundedContinuousFunction.norm_coe_le_norm f x]
  simp

set_option backward.privateInPublic true in
def toTemperedDistribution (f : E →ᵇ F) : 𝓢'(E, F) :=
  LocallyIntegrable.toTemperedDistribution (μ := μ) (f := f) (k := 0) ?_ ?_
where finally
  · exact (map_continuous f).locallyIntegrable
  · rw [isBigO_cocompact_iff]
    use ‖f‖ + 1
    refine ⟨by positivity, ?_⟩
    use ∅, by simp
    intro x _
    grw [BoundedContinuousFunction.norm_coe_le_norm f x]
    simp

set_option backward.privateInPublic true in
@[simp]
theorem toTemperedDistribution_apply (f : E →ᵇ F) (g : 𝓢(E, ℂ)) :
    f.toTemperedDistribution μ g = ∫ x, g x • f x ∂μ := rfl

set_option backward.privateInPublic true in
@[simp]
theorem _root_.SchwartzMap.toBCF_toTemperedDistribution (f : 𝓢(E, F)) :
    f.toBoundedContinuousFunction.toTemperedDistribution μ = f.toTemperedDistributionCLM E F μ := by
  ext u
  simp

variable [CompleteSpace F]

set_option backward.privateInPublic true in
variable (E F) in
def toTemperedDistributionCLM : (E →ᵇ F) →L[ℂ] 𝓢'(E, F) where
  toFun f := f.toTemperedDistribution μ
  map_add' f₁ f₂ := by
    ext u
    simpa using integral_add (by fun_prop) (by fun_prop)
  map_smul' c f := by
    ext u
    simp [← integral_smul, ← smul_assoc, mul_comm]
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro g
    simp only [toTemperedDistribution_apply]
    convert ((lsmul ℂ ℂ).lpPairing μ 1 ⊤ (g.toLp 1 μ) ∘L
      (BoundedContinuousFunction.toLp_top (E := F) ℂ μ)).cont with f
    simp only [coe_comp, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp, coe_coe,
      Function.comp_apply, toLp_top_apply, lpPairing_eq_integral, lsmul_apply]
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp 1 μ, f.memLp_top.coeFn_toLp] with x hg hf
    simp [hg, hf]

end BoundedContinuousFunction

namespace MeasureTheory.Lp

open scoped FourierTransform

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℝ E] [NormedSpace ℂ F]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [hμ : (volume (α := E)).HasTemperateGrowth] [CompleteSpace F]

set_option backward.privateInPublic true in
theorem fourier_toTemperedDistributionCLM_eq (f : Lp (α := E) F 1) :
    𝓕 (f : 𝓢'(E, F)) = (Real.Lp.fourierTransform f).toTemperedDistribution := by
  set p := fun f : Lp (α := E) F 1 ↦
    𝓕 (f : 𝓢'(E, F)) = (Real.Lp.fourierTransform f).toTemperedDistribution
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 1) ENNReal.one_ne_top) f
  · apply isClosed_eq
    · have := (Lp.toTemperedDistributionCLM F (volume : Measure E) 1).cont
      fun_prop
    · exact ((BoundedContinuousFunction.toTemperedDistributionCLM E F) ∘L
        (Real.Lp.fourierTransformCLM E F)).cont
  · intro f
    unfold p
    simp [SchwartzMap.toLp_one_fourierTransform_eq,
      TemperedDistribution.fourier_toTemperedDistributionCLM_eq f]

set_option backward.privateInPublic true in
theorem fourierInv_toTemperedDistributionCLM_eq (f : Lp (α := E) F 1) :
    𝓕⁻ (f : 𝓢'(E, F)) = (Real.Lp.fourierTransformInv f).toTemperedDistribution := by
  set p := fun f : Lp (α := E) F 1 ↦
    𝓕⁻ (f : 𝓢'(E, F)) = (Real.Lp.fourierTransformInv f).toTemperedDistribution
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 1) ENNReal.one_ne_top) f
  · apply isClosed_eq
    · have := (Lp.toTemperedDistributionCLM F (volume : Measure E) 1).cont
      fun_prop
    · exact ((BoundedContinuousFunction.toTemperedDistributionCLM E F) ∘L
        (Real.Lp.fourierTransformInvCLM E F)).cont
  · intro f
    unfold p
    simp [SchwartzMap.toLp_one_fourierTransformInv_eq,
      TemperedDistribution.fourierInv_toTemperedDistributionCLM_eq f]

end MeasureTheory.Lp
