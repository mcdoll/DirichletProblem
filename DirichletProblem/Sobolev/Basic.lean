/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DirichletProblem.Mathlib.Analysis.Distribution.Sobolev
public import DirichletProblem.Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import DirichletProblem.Mathlib.Analysis.Fourier.ZeroAtInfty
public import DirichletProblem.Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.LpSpace

/-! # Sobolev spaces -/

@[expose] public noncomputable section

variable {E F : Type*}

namespace TemperedDistribution

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℂ F] [CompleteSpace F]

open scoped SchwartzMap ZeroAtInfty FourierTransform

/-- *Sobolev embedding theorem*: a Sobolev function of order `s` with `s > d / 2` can be represented
by a `C₀(E, F)` function. -/
theorem MemSobolev.zeroAtInfty {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) :
    ∃ (v : C₀(E, F)), f = v.toBCF.toTemperedDistribution := by
  obtain ⟨g, hg⟩ := hf.fourier_memL1 hs
  use Real.Lp.fourierTransformInvZeroAtInftyCLM E F g
  simp [← MeasureTheory.Lp.fourierInv_toTemperedDistributionCLM_eq, ← hg]

end TemperedDistribution

section BCF

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]

open scoped ENNReal
open BoundedContinuousFunction MeasureTheory

def foo {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) : E →ᵇ ℂ :=
  ofNormedAddCommGroup (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2) • g x) ?_ C ?_
where finally
  · have : Function.HasTemperateGrowth (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2) • g x) := by fun_prop
    exact this.1.continuous
  · intro x
    specialize hg₂ x
    simp only [Complex.real_smul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_eq_self.mpr (by positivity), neg_div, Real.rpow_neg (by positivity)]
    field_simp
    rwa [mul_comm]

theorem coe_foo {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) :
    (foo s C hg₁ hg₂ : E → ℂ) = (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2) • g x) := rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

def foo' {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) :
    Lp F p (volume : Measure E) →L[ℂ] Lp F p (volume : Measure E) :=
    (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ⊤ p p ((foo s C  hg₁ hg₂).memLp_top.toLp)

theorem foo'_apply {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) (f : Lp F p (volume : Measure E)) :
    foo' s C hg₁ hg₂ f = (foo s C hg₁ hg₂).memLp_top.toLp _ (μ := volume) • f := by
  rfl

end BCF

section Lp

open BoundedContinuousFunction MeasureTheory Lp

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable {s : ℝ}

-- define the function as an `Lp` function (complex-valued)

theorem _root_.MeasureTheory.Lp.memLp_rpow_add_sq_norm (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
  constructor
  · have : (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
      fun_prop
    exact this.1.continuous.aestronglyMeasurable
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    suffices h : ∫⁻ a : E, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
      norm_cast
      simp_rw [ofReal_norm] at h
      simp_rw [← enorm_pow]
      convert h using 4
      rw [← Real.rpow_mul_natCast (by positivity)]
      simp
    apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
    congr
    ring

theorem _root_.MeasureTheory.Lp.memLp_ofReal_rpow_add_sq_norm (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) 2 := by
  apply (memLp_rpow_add_sq_norm hs).ofReal

variable (E F s) in
private
def blubb : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 1 (volume : Measure E) :=
  if hs : Module.finrank ℝ E < 2 * s then
    (ContinuousLinearMap.lsmul ℂ ℂ).holderL (volume : Measure E) 2 2 1
      (memLp_ofReal_rpow_add_sq_norm hs).toLp
  else 0

private
theorem blubb_apply (hs : Module.finrank ℝ E < 2 * s) (f : Lp F 2 (volume : Measure E)) :
    blubb E F s f = (memLp_ofReal_rpow_add_sq_norm hs).toLp • f := by
  simp only [blubb, hs, ↓reduceDIte]
  rfl

end Lp

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

section normed

variable [NormedSpace ℂ F]

variable (E F) in
/-- The Sobolev space of order `s : ℝ`.

It is defined as the set of all tempered distributions `f` such that
`𝓕⁻ (1 + ‖x‖ ^ 2) ^ (s / 2) 𝓕 f` can be represented by a `Lp` function `f'`. Both `f` and `f'` are
stored as data to avoid using `Classical.choose`. -/
structure Sobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] where
  /-- The underlying tempered distribution -/
  toDistr : 𝓢'(E, F)
  /-- The underlying `Lp` function -/
  sobFn : Lp F p (volume : Measure E)
  /-- The Sobolev function is given by applying the Bessel potential operator to the distribution -/
  bessel_toDistr_eq_sobFn : besselPotential E F s toDistr = sobFn

namespace Sobolev

variable {s s' : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

theorem ext' {f g : Sobolev E F s p}
    (h₁ : f.toDistr = g.toDistr) (h₂ : f.sobFn = g.sobFn) : f = g := by
  cases f; cases g; congr

theorem memSobolev_toDistr (f : Sobolev E F s p) : MemSobolev s p f.toDistr :=
  ⟨f.sobFn, f.bessel_toDistr_eq_sobFn⟩

@[simp]
theorem besselPotential_neg_sobFn_eq {f : Sobolev E F s p} :
    besselPotential E F (-s) f.sobFn = f.toDistr := by
  simp [← f.bessel_toDistr_eq_sobFn]

@[ext]
theorem ext {f g : Sobolev E F s p} (h₁ : f.toDistr = g.toDistr) : f = g := by
  apply ext' h₁
  apply_fun MeasureTheory.Lp.toTemperedDistribution; swap
  · apply LinearMap.ker_eq_bot.mp MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
  calc
    f.sobFn = besselPotential E F s f.toDistr := f.bessel_toDistr_eq_sobFn.symm
    _ = besselPotential E F s g.toDistr := by congr
    _ = g.sobFn := g.bessel_toDistr_eq_sobFn

/-- Transfer a Sobolev function in `H^{s,p}` to `H^{s', p}` given that `s = s'`. -/
def copy (hs : s = s') (f : Sobolev E F s p) : Sobolev E F s' p where
  toDistr := f.toDistr
  sobFn := f.sobFn
  bessel_toDistr_eq_sobFn := by
    rw [← hs]
    exact f.bessel_toDistr_eq_sobFn

@[simp]
theorem toDistr_copy (f : Sobolev E F s p) (hs : s = s') :
  (f.copy hs).toDistr = f.toDistr := rfl

@[simp]
theorem sobFn_copy (f : Sobolev E F s p) (hs : s = s') :
  (f.copy hs).sobFn = f.sobFn := rfl

variable (E F s p) in
theorem injective_sobFn :
    Function.Injective (sobFn (s := s) (p := p) (E := E) (F := F)) := by
  intro f g hfg
  refine ext' ?_ hfg
  calc
    f.toDistr = besselPotential E F (-s) (Sobolev.sobFn f) := by simp
    _ = besselPotential E F (-s) (Sobolev.sobFn g) := by congr
    _ = g.toDistr := by simp

instance instZero : Zero (Sobolev E F s p) where
  zero := {
    toDistr := 0
    sobFn := 0
    bessel_toDistr_eq_sobFn := by simp [← Lp.toTemperedDistributionCLM_apply] }

@[simp]
theorem toDistr_zero : (0 : Sobolev E F s p).toDistr = 0 := rfl

@[simp]
theorem sobFn_zero : (0 : Sobolev E F s p).sobFn = 0 := rfl

instance instAdd : Add (Sobolev E F s p) where
  add f g := {
    toDistr := f.toDistr + g.toDistr
    sobFn := f.sobFn + g.sobFn
    bessel_toDistr_eq_sobFn := by simp [← Lp.toTemperedDistributionCLM_apply, map_add,
      f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_add (f g : Sobolev E F s p) : (f + g).toDistr = f.toDistr + g.toDistr := rfl

@[simp]
theorem sobFn_add (f g : Sobolev E F s p) : (f + g).sobFn = f.sobFn + g.sobFn := rfl

instance instSub : Sub (Sobolev E F s p) where
  sub f g := {
    toDistr := f.toDistr - g.toDistr
    sobFn := f.sobFn - g.sobFn
    bessel_toDistr_eq_sobFn := by simp [← Lp.toTemperedDistributionCLM_apply, map_sub,
      f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_sub (f g : Sobolev E F s p) : (f - g).toDistr = f.toDistr - g.toDistr := rfl

@[simp]
theorem sobFn_sub (f g : Sobolev E F s p) : (f - g).sobFn = f.sobFn - g.sobFn := rfl

instance instNeg : Neg (Sobolev E F s p) where
  neg f := {
    toDistr := -f.toDistr
    sobFn := -f.sobFn
    bessel_toDistr_eq_sobFn := by
      simp [← Lp.toTemperedDistributionCLM_apply, map_neg, f.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_neg (f : Sobolev E F s p) : (-f).toDistr = -f.toDistr := rfl

@[simp]
theorem sobFn_neg (f : Sobolev E F s p) : (-f).sobFn = -f.sobFn := rfl

variable {R : Type*} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
  [SMul R ℂ] [SMul R 𝓢'(E, F)] [SMul R (Lp F p (μ := (volume : Measure E)))]
  [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ (Lp F p (μ := (volume : Measure E)))]

instance instSMul : SMul R (Sobolev E F s p) where
  smul c f := {
    toDistr := c • f.toDistr
    sobFn := c • f.sobFn
    bessel_toDistr_eq_sobFn := by
      simp [← Lp.toTemperedDistributionCLM_apply, f.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_smul (c : R) (f : Sobolev E F s p) : (c • f).toDistr = c • f.toDistr := rfl

@[simp]
theorem sobFn_smul (c : R) (f : Sobolev E F s p) : (c • f).sobFn = c • f.sobFn := rfl

instance instAddCommGroup : AddCommGroup (Sobolev E F s p) :=
  (injective_sobFn E F s p).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F s p) in
/-- Coercion as an additive homomorphism. -/
def coeHom : Sobolev E F s p →+ 𝓢'(E, F) where
  toFun f := f.toDistr
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeHom_injective : Function.Injective (coeHom E F s p) := by
  apply ext

instance instModule : Module ℂ (Sobolev E F s p) :=
  coeHom_injective.module ℂ (coeHom E F s p) fun _ _ => rfl

variable (E F s p) in
/-- The map `f ↦ 𝓕⁻ (1 + ‖x‖ ^ 2) ^ (s / 2) 𝓕 f` as a linear map from `H ^ {s,p}` to `Lp`.

This definition is mainly used to define the norm and inner product on `H ^ {s,p}` and `H ^ s`,
respectively. -/
def toLpₗ : Sobolev E F s p →ₗ[ℂ] Lp F p (volume : Measure E) where
  toFun := sobFn
  map_add' f g := by rfl
  map_smul' c f := by rfl

variable (s) in
def ofLp (f : Lp F p (volume : Measure E)) : Sobolev E F s p where
  toDistr := besselPotential E F (-s) f
  sobFn := f
  bessel_toDistr_eq_sobFn := by simp

@[simp]
theorem sobFn_ofLp (f : Lp F p (volume : Measure E)) :
    (ofLp s f).sobFn = f := rfl

@[simp]
theorem toDistr_ofLp (f : Lp F p (volume : Measure E)) :
    (ofLp s f).toDistr = besselPotential E F (-s) f := rfl

@[simp]
theorem ofLp_sobFn (f : Sobolev E F s p) :
    ofLp s f.sobFn = f :=
  injective_sobFn E F s p rfl

@[simp]
theorem toLpₗ_apply (f : Sobolev E F s p) :
    toLpₗ E F s p f = sobFn f := rfl

instance instNormedAddCommGroup :
    NormedAddCommGroup (Sobolev E F s p) :=
  NormedAddCommGroup.induced (Sobolev E F s p) (Lp F p (volume : Measure E)) (toLpₗ E F s p)
    (injective_sobFn E F s p)

@[simp]
theorem norm_sobFn_eq (f : Sobolev E F s p) : ‖f.sobFn‖ = ‖f‖ :=
  rfl

instance instNormedSpace :
    NormedSpace ℂ (Sobolev E F s p) where
  norm_smul_le c f := by
    simp_rw [← norm_sobFn_eq, ← norm_smul]
    rfl

variable (E F s p) in
def toLpₗᵢ :
    Sobolev E F s p ≃ₗᵢ[ℂ] Lp F p (volume : Measure E) where
  __ := toLpₗ E F s p
  invFun := ofLp s
  left_inv f := by simp
  right_inv f := by simp
  norm_map' _ := rfl

@[simp]
theorem toLpₗᵢ_apply (f : Sobolev E F s p) :
    toLpₗᵢ E F s p f = sobFn f := rfl

instance instCompleteSpace : CompleteSpace (Sobolev E F s p) :=
  (toLpₗᵢ E F s p).toIsometryEquiv.completeSpace

open ContinuousLinearMap

variable (F) in
/-- A Schwartz function defines a continuous linear map from `Lp` to `F` via integration. -/
def _root_.SchwartzMap.toLpFunctional (f : 𝓢(E, ℂ)) : Lp F p (volume : Measure E) →L[ℂ] F :=
  haveI := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  haveI : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
  (lsmul ℂ ℂ).lpPairing (volume : Measure E) (1 - p⁻¹)⁻¹ p (f.toLp _)

@[simp]
theorem _root_.SchwartzMap.toLpFunctional_apply (f : 𝓢(E, ℂ)) (g : Lp F p) :
    f.toLpFunctional F g = ∫ x, f x • g x := by
  rw [SchwartzMap.toLpFunctional, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (1 - p⁻¹)⁻¹] with x hf
  simp [hf]

theorem toDistr_apply (f : Sobolev E F s p) (u : 𝓢(E, ℂ)) :
    f.toDistr u = (𝓕 <| 𝓕⁻ u |>.smulLeftCLM ℂ fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).toLpFunctional F
      f.sobFn := by
  rw [SchwartzMap.toLpFunctional_apply, ← besselPotential_neg_sobFn_eq]
  rw [besselPotential]
  simp only [fourierMultiplierCLM_apply_apply, Lp.toTemperedDistribution_apply]
  congr
  ext x
  congr 3
  apply SchwartzMap.smulLeftCLM_ofReal
  exact Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-s / 2)

variable (E F s p) in
/-- The map from Sobolev functions `H^{s,p}` to `𝓢'` as a continuous linear map. -/
def toTemperedDistributionCLM : Sobolev E F s p →L[ℂ] 𝓢'(E, F) where
  toFun f := f.toDistr
  map_add' := toDistr_add
  map_smul' := toDistr_smul
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro g
    simp_rw [toDistr_apply]
    fun_prop


end Sobolev

namespace SchwartzMap

variable {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

variable (E F s p) in
/-- The embedding of Schwartz functions into the Sobolev space. -/
def toSobolev : 𝓢(E, F) →L[ℂ] Sobolev E F s p :=
  (Sobolev.toLpₗᵢ E F s p).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
  toLpCLM ℂ F p (volume : Measure E) ∘L
  SchwartzMap.fourierMultiplierCLM F (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)))

theorem toSobolev_apply (f : 𝓢(E, F)) :
  f.toSobolev E F s p = Sobolev.ofLp s ((f.fourierMultiplierCLM F
    (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2)))).toLp p)  := rfl

@[simp]
theorem toDistr_toSobolev (f : 𝓢(E, F)) :
    (f.toSobolev E F s p).toDistr = f := by
  rw [toSobolev_apply, Sobolev.toDistr_ofLp, Lp.toTemperedDistribution_toLp_eq,
    ← fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop), ← besselPotential]
  simp

theorem norm_toSobolev (f : 𝓢(E, F)) : ‖f.toSobolev E F s p‖ = ‖f.fourierMultiplierCLM F
    (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) |>.toLp p‖ := by
  simp [toSobolev_apply, ← Sobolev.norm_sobFn_eq]

variable (E F s) in
theorem denseRange_toSobolev (hp : p ≠ ⊤) : DenseRange (toSobolev E F s p) := by
  simp only [toSobolev, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]
  apply (Sobolev.toLpₗᵢ E F s p).symm.surjective.denseRange.comp _ (by fun_prop)
  apply (denseRange_toLpCLM hp).comp _ (by fun_prop)
  apply Function.Surjective.denseRange
  intro f
  use f.fourierMultiplierCLM F (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ))
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  convert DFunLike.ext_iff.mp (fourierMultiplierCLM_const (1 : ℂ)) f
  · rw [Pi.mul_apply]
    norm_cast
    rw [← Real.rpow_add (by positivity)]
    ring_nf
    simp
  · simp

-- dense range

end SchwartzMap

namespace TemperedDistribution

variable {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

def MemSobolev.toSobolev {f : 𝓢'(E, F)} (hf : MemSobolev s p f) : Sobolev E F s p where
  toDistr := f
  sobFn := hf.choose
  bessel_toDistr_eq_sobFn := hf.choose_spec

@[simp]
theorem MemSobolev.toSobolev_toDistr {f : 𝓢'(E, F)} (hf : MemSobolev s p f) :
    hf.toSobolev.toDistr = f := rfl

theorem MemSobolev.toSobolev_injective {f g : 𝓢'(E, F)} (hf : MemSobolev s p f)
    (hg : MemSobolev s p g) (h : hf.toSobolev = hg.toSobolev) : f = g := by
  rw [← hf.toSobolev_toDistr, ← hg.toSobolev_toDistr, h]

end TemperedDistribution

end normed

section inner

variable [InnerProductSpace ℂ F]

namespace SchwartzMap

variable {s : ℝ}

/-- The Sobolev norm is given by `‖(1 + |x| ^ 2) ^ (s / 2) • 𝓕 f ξ‖`. -/
theorem norm_toSobolev_eq_smulLeftCLM_fourier (f : 𝓢(E, F)) : ‖f.toSobolev E F s 2‖ =
    ‖(𝓕 f).smulLeftCLM F (fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) |>.toLp 2‖ := by
  rw [norm_toSobolev, fourierMultiplierCLM_apply, norm_fourierInv_toL2_eq]

end SchwartzMap

namespace Sobolev

variable {s : ℝ}

theorem norm_fourier_sobFn_eq (f : Sobolev E F s 2) : ‖𝓕 f.sobFn‖ = ‖f‖ :=
  LinearIsometryEquiv.norm_map' _ _

instance instInnerProductSpace (s : ℝ) :
    InnerProductSpace ℂ (Sobolev E F s 2) where
  inner f g := inner ℂ f.sobFn g.sobFn
  norm_sq_eq_re_inner f := norm_sq_eq_re_inner f.sobFn
  conj_inner_symm f g := by simp
  add_left f g h := by simp [inner_add_left]
  smul_left f g c := by simp [inner_smul_left]

theorem smulLeftCLM_fourier_toDistr_eq {s : ℝ} (f : Sobolev E F s 2) :
    smulLeftCLM F (fun x ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f.toDistr) = 𝓕 f.sobFn := by
  have : (besselPotential E F s) f.toDistr = Lp.toTemperedDistribution f.sobFn :=
    f.bessel_toDistr_eq_sobFn
  apply_fun 𝓕 at this
  rw [fourier_besselPotential_eq_smulLeftCLM_fourierInv_apply] at this
  rw [this, Lp.fourier_toTemperedDistribution_eq]

section BCF

open BoundedContinuousFunction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem toTemperedDistribution_foo' {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) (f : Lp F p (volume : Measure E)) :
    Lp.toTemperedDistribution (foo' s C hg₁ hg₂ f) =
      smulLeftCLM F (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2) • g x) f := by
  rw [foo'_apply]
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
  · rfl
  rw [coe_foo]
  fun_prop

theorem fourierInv_toTemperedDistribution_foo'_fourier {g : E → ℂ} (s C : ℝ)
    (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) (f : Lp F 2 (volume : Measure E)) :
    𝓕⁻ (Lp.toTemperedDistribution <| foo' s C hg₁ hg₂ <| 𝓕 f) =
      besselPotential E F (-s) (fourierMultiplierCLM F g f) := by
  rw [toTemperedDistribution_foo', ← Lp.fourier_toTemperedDistribution_eq]
  rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ (by fun_prop)]
  rw [fourierMultiplierCLM_apply]
  congr
  ext x
  simp [mul_comm]

end BCF

section SobolevEmbedding

open scoped ZeroAtInfty
open MeasureTheory.Lp

variable (E F) in
/-- The *Sobolev embedding theorem* -/
@[no_expose]
def toZeroAtInfty (s : ℝ) : Sobolev E F s 2 →L[ℂ] C₀(E, F) :=
  Real.Lp.fourierTransformInvZeroAtInftyCLM E F ∘L
  (blubb E F s) ∘L
  ((toLpₗᵢ E F s 2).trans (Lp.fourierTransformₗᵢ E F)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem fourierTransformₗᵢ_apply (f : Lp F 2 (volume : Measure E)) :
    Lp.fourierTransformₗᵢ E F f = 𝓕 f := rfl

@[simp]
theorem fourierTransformₗᵢ_symm_apply (f : Lp F 2 (volume : Measure E)) :
    (Lp.fourierTransformₗᵢ E F).symm f = 𝓕⁻ f := rfl

theorem toZeroAtInfty_apply (hs : Module.finrank ℝ E < 2 * s) (f : Sobolev E F s 2) :
    toZeroAtInfty E F s f = Real.Lp.fourierTransformInvZeroAtInftyCLM E F
      ((memLp_ofReal_rpow_add_sq_norm hs).toLp • 𝓕 f.sobFn) := by
  simp [toZeroAtInfty, blubb_apply hs]

theorem toZeroAtInfty_apply_toTemperedDistribution (hs : Module.finrank ℝ E < 2 * s)
    (f : Sobolev E F s 2) :
    (toZeroAtInfty E F s f).toBCF.toTemperedDistribution = f.toDistr := calc
  _ = 𝓕⁻ (Lp.toTemperedDistribution ((memLp_ofReal_rpow_add_sq_norm hs).toLp • 𝓕 f.sobFn)) := by
    simp [toZeroAtInfty_apply hs, Lp.fourierInv_toTemperedDistributionCLM_eq]
  _ = 𝓕⁻ (smulLeftCLM F (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) <|
      𝓕 (f.sobFn : 𝓢'(E, F))) := by
    rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq (F := F) (by fun_prop),
      Lp.fourier_toTemperedDistribution_eq]
  _ = _ := by
    rw [← besselPotential_neg_sobFn_eq, besselPotential, fourierMultiplierCLM_apply]

end SobolevEmbedding

section Trace

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']

variable (f : 𝓢(E × E', F)) (a : E')

variable (E F s) in
/-- The trace operator `H ^ s (E × E') →L[ℂ] H ^ s E`

For `s > -d / 2` this is an extension of the trace on Schwartz functions. -/
@[no_expose]
def restrictFst (a : E') :
    Sobolev (WithLp 2 (E × E')) F s 2 →L[ℂ] Sobolev E F (s - (Module.finrank ℝ E') / 2) 2 :=
  f.extendOfNorm e
where
  f := SchwartzMap.toSobolev E F (s - (Module.finrank ℝ E') / 2) 2 ∘L
    SchwartzMap.restrictFst ℂ E F a ∘L
    (SchwartzMap.precompProdLp ℂ 2).symm.toContinuousLinearMap
      |>.toLinearMap
  e := (SchwartzMap.toSobolev (WithLp 2 (E × E')) F s 2).toLinearMap

private theorem denseRange_e : DenseRange (restrictFst.e E F s (E' := E')) :=
  SchwartzMap.denseRange_toSobolev _ F s (by simp)

open Module in
private theorem norm_restrictFst_f_le (a : E') (hs : finrank ℝ E' < 2 * s)
    (f : 𝓢(WithLp 2 (E × E'), F)) :
    ‖(restrictFst.f E F s a) f‖ ≤ (∫ x : E, (1 + ‖x‖ ^ 2) ^ (-s)) * ‖(restrictFst.e E F s) f‖ := by
  let s' := s - (finrank ℝ E') / 2
  apply le_of_sq_le_sq _ (by positivity)
  calc
    _ = ∫ (x : E),
        ‖((SchwartzMap.smulLeftCLM F fun x ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s' / 2)))
                (𝓕 ((SchwartzMap.restrictFst ℂ E F a) ((SchwartzMap.precompProdLp ℂ 2).symm f))))
              x‖ ^ 2 := by
      simp only [restrictFst.f, ContinuousLinearMap.coe_comp,
        ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
        SchwartzMap.norm_toSobolev_eq_smulLeftCLM_fourier, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, ofNat_ne_top, SchwartzMap.norm_toLp', toReal_ofNat, Real.rpow_ofNat]
      -- the next three lines should be their own tactic
      simp only [← Real.rpow_ofNat]
      rw [← Real.rpow_mul (by positivity)]
      simp only [Real.rpow_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
        Real.rpow_one, s']
    _ = ∫ (x : E),
        ‖(1 + ‖x‖ ^ 2) ^ (s' / 2) •
                (𝓕 ((SchwartzMap.restrictFst ℂ E F a) ((SchwartzMap.precompProdLp ℂ 2).symm f)))
              x‖ ^ 2 := by
      congr
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      simp
    _ ≤ (∫ x : E, (1 + ‖x‖ ^ 2) ^ (-s)) ^ 2 * ∫ ξ, ‖(1 + ‖ξ‖ ^ 2) ^ (s / 2) • 𝓕 f ξ‖ ^ 2 := by
      sorry
    _ = _ := by
      simp only [restrictFst.e, ContinuousLinearMap.coe_coe,
        SchwartzMap.norm_toSobolev_eq_smulLeftCLM_fourier, mul_pow, mul_eq_mul_left_iff, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
      left
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ofNat_ne_top,
        SchwartzMap.norm_toLp', toReal_ofNat]
      -- the next three lines should be their own tactic
      simp only [← Real.rpow_ofNat]
      rw [← Real.rpow_mul (by positivity)]
      simp only [Real.rpow_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, inv_mul_cancel₀,
        Real.rpow_one]
      congr
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      simp

theorem restrictFst_toSobolev_eq (f : 𝓢(WithLp 2 (E × E'), F)) (hs : Module.finrank ℝ E' < 2 * s) :
    (f.toSobolev _ _ s 2).restrictFst E F s a =
    ((SchwartzMap.precompProdLp ℂ 2).symm f |>.restrictFst ℂ E F a).toSobolev E F
      (s - (Module.finrank ℝ E')/2) 2 := by
  apply LinearMap.extendOfNorm_eq denseRange_e
  exact ⟨∫ x : E, (1 + ‖x‖ ^ 2) ^ (-s), norm_restrictFst_f_le a hs⟩

theorem norm_restrictFst_le (a : E') (hs : Module.finrank ℝ E' < 2 * s) :
    ‖Sobolev.restrictFst E F s a‖ ≤ ∫ x : E, (1 + ‖x‖ ^ 2) ^ (-s) :=
  LinearMap.opNorm_extendOfNorm_le denseRange_e (by positivity) (norm_restrictFst_f_le a hs)

end Trace

@[no_expose]
def fourierMultiplierCLM (s s' C : ℝ) (g : E → ℂ)
    (hg₁ : g.HasTemperateGrowth) (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) :
    Sobolev E F s 2 →L[ℂ] Sobolev E F s' 2 :=
  ((toLpₗᵢ E F s' 2).trans (Lp.fourierTransformₗᵢ E F)
    |>.symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
  foo' (s - s') C hg₁ hg₂ ∘L
  ((toLpₗᵢ E F s 2).trans (Lp.fourierTransformₗᵢ E F)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
private
theorem fourierMultiplierCLM_sobFn {s : ℝ} (s' C : ℝ) {g : E → ℂ} (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) (f : Sobolev E F s 2) :
    (f.fourierMultiplierCLM s s' C g hg₁ hg₂).sobFn = 𝓕⁻ (foo' (s - s') C hg₁ hg₂ (𝓕 f.sobFn)) :=
  rfl

@[simp]
theorem fourierMultiplierCLM_toDistr {s : ℝ} (s' C : ℝ) {g : E → ℂ} (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) (f : Sobolev E F s 2) :
    (f.fourierMultiplierCLM s s' C g hg₁ hg₂).toDistr = f.toDistr.fourierMultiplierCLM F g := by
  rw [← besselPotential_neg_sobFn_eq, fourierMultiplierCLM_sobFn,
    ← Lp.fourierInv_toTemperedDistribution_eq,
    fourierInv_toTemperedDistribution_foo'_fourier,
    besselPotential_besselPotential_apply, ← besselPotential_neg_sobFn_eq,
    besselPotential_fourierMultiplierCLM_comm _ hg₁]
  ring_nf

variable (E F) in
@[no_expose]
def mono (s s' : ℝ) :
    Sobolev E F s 2 →L[ℂ] Sobolev E F s' 2 :=
  if h : s' ≤ s then
    fourierMultiplierCLM s s' 1 (fun _ ↦ 1) (by fun_prop) (fun _ ↦ ?_)
  else
    0
where finally
  simp only [one_mem, CStarRing.norm_of_mem_unitary, one_mul]
  exact Real.one_le_rpow (by simp) (by grind)

variable {s' : ℝ}

theorem mono_apply (h : s' ≤ s) (f : Sobolev E F s 2) : (f.mono E F s s').toDistr = f.toDistr := by
  simp [mono, h]

theorem mono_apply_eq_zero_of_lt (h : s < s') (f : Sobolev E F s 2) :
    (f.mono E F s s').toDistr = 0 := by
  have h : ¬ s' ≤ s := by grind
  simp [mono, h]

open LineDeriv Laplacian Real

variable (F) in
def lineDerivOp (s : ℝ) (m : E) : Sobolev E F s 2 →L[ℂ] Sobolev E F (s - 1) 2 :=
  (2 * π * Complex.I) • (fourierMultiplierCLM s (s - 1) ‖m‖ (fun x ↦ Complex.ofReal <| inner ℝ x m)
    ?_ ?_)
where finally
  · fun_prop
  · intro x
    simp only [Complex.norm_real, norm_eq_abs, _root_.sub_sub_cancel, one_div]
    grw [abs_real_inner_le_norm]
    rw [mul_comm]
    gcongr
    apply le_of_sq_le_sq _ (by positivity)
    calc
      _ ≤ 1 + ‖x‖ ^ 2 := by simp
      _ = ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; simp
      _ = _ := by simp

instance instLineDeriv (s : ℝ) : LineDeriv E (Sobolev E F s 2) (Sobolev E F (s - 1) 2) where
  lineDerivOp m f := f.lineDerivOp F s m

@[simp]
theorem lineDerivOp_apply (m : E) (f : Sobolev E F s 2) : f.lineDerivOp F s m = ∂_{m} f := rfl

@[simp]
theorem lineDerivOp_toDistr (m : E) {s : ℝ} (f : Sobolev E F s 2) :
    (∂_{m} f).toDistr = ∂_{m} f.toDistr := by
  rw [← lineDerivOp_apply, lineDerivOp, smul_apply,
    toDistr_smul, fourierMultiplierCLM_toDistr,
    lineDeriv_eq_fourierMultiplierCLM]

variable (E F) in
def laplacian (s : ℝ) : Sobolev E F s 2 →L[ℂ] Sobolev E F (s - 2) 2 :=
  -(2 * π) ^ 2 • (fourierMultiplierCLM s (s - 2) 1 (fun x ↦ Complex.ofReal <| ‖x‖ ^ 2) ?_ ?_)
where finally
  · fun_prop
  · simp

instance instLaplacian (s : ℝ) : Laplacian (Sobolev E F s 2) (Sobolev E F (s - 2) 2) where
  laplacian f := f.laplacian E F s

@[simp]
theorem laplacian_apply (f : Sobolev E F s 2) : f.laplacian E F s = Δ f := rfl

set_option backward.isDefEq.respectTransparency false in -- because of real-complex nonsense
@[simp]
theorem laplacian_toDistr {s : ℝ} (f : Sobolev E F s 2) : (Δ f).toDistr = Δ f.toDistr := by
  rw [← laplacian_apply, laplacian, smul_apply,
    toDistr_smul, fourierMultiplierCLM_toDistr,
    laplacian_eq_fourierMultiplierCLM]

variable (E) in
private def deltaAux (s : ℝ) (hs : 2 * s < -Module.finrank ℝ E) : Sobolev E ℂ s 2 where
  toDistr := TemperedDistribution.delta (0 : E)
  sobFn := 𝓕⁻ (MeasureTheory.Lp.memLp_ofReal_rpow_add_sq_norm (s := -s) (by grind)).toLp
  bessel_toDistr_eq_sobFn := by
    simp only [neg_neg]
    rw [besselPotential, fourierMultiplierCLM_apply]
    rw [fourier_delta_zero]
    rw [← Lp.fourierInv_toTemperedDistribution_eq]
    congr 1
    rw [(volume : Measure E).smulLeftCLM_toTemperedDistribution (by fun_prop)]
    ext u
    simp only [Function.HasTemperateGrowth.toTemperedDistribution_apply, smul_eq_mul,
      Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    have : MemLp (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (s / 2))) 2 := by
      rw [← neg_neg s]
      apply MeasureTheory.Lp.memLp_ofReal_rpow_add_sq_norm (E := E) (s := -s) (by grind)
    filter_upwards [this.coeFn_toLp] with x h
    simp [h]

variable (E s) in
@[no_expose]
def delta : Sobolev E ℂ s 2 :=
  if hs : 2 * s < -Module.finrank ℝ E then deltaAux E s hs else 0

theorem delta_toDistr (hs : 2 * s < -Module.finrank ℝ E) :
    (delta E s).toDistr = TemperedDistribution.delta (0 : E) := by
  simp [delta, hs]
  rfl

end Sobolev

end inner
