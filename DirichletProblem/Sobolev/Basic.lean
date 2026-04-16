/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DirichletProblem.Mathlib.Analysis.Distribution.Sobolev
public import DirichletProblem.Mathlib.Analysis.Fourier.ZeroAtInfty
public import DirichletProblem.Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public noncomputable section

namespace TemperedDistribution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
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

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
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
  toDistr : 𝓢'(E, F)
  sobFn : Lp F p (volume : Measure E)
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
def copy (hs : s = s') (f : Sobolev E F s p) :
    Sobolev E F s' p where
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
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (_ + _)
      simp [map_add, f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_add (f g : Sobolev E F s p) : (f + g).toDistr = f.toDistr + g.toDistr := rfl

@[simp]
theorem sobFn_add (f g : Sobolev E F s p) : (f + g).sobFn = f.sobFn + g.sobFn := rfl

instance instSub : Sub (Sobolev E F s p) where
  sub f g := {
    toDistr := f.toDistr - g.toDistr
    sobFn := f.sobFn - g.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (_ - _)
      simp [map_sub, f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_sub (f g : Sobolev E F s p) : (f - g).toDistr = f.toDistr - g.toDistr := rfl

@[simp]
theorem sobFn_sub (f g : Sobolev E F s p) : (f - g).sobFn = f.sobFn - g.sobFn := rfl

instance instNeg : Neg (Sobolev E F s p) where
  neg f := {
    toDistr := -f.toDistr
    sobFn := -f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (- _)
      simp [map_neg, f.bessel_toDistr_eq_sobFn] }

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
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [f.bessel_toDistr_eq_sobFn] }

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

instance instCompleteSpace : CompleteSpace (Sobolev E F s p) :=
  (toLpₗᵢ E F s p).toIsometryEquiv.completeSpace

open ContinuousLinearMap

variable (F) in
def _root_.SchwartzMap.toLpFunctional (f : 𝓢(E, ℂ)) : Lp F p (volume : Measure E) →L[ℂ] F :=
  haveI := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  haveI : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
  (lsmul ℂ ℂ).lpPairing (volume : Measure E) (1 - p⁻¹)⁻¹ p (f.toLp _)

@[simp]
theorem _root_.SchwartzMap.toLpFunctional_apply (f : 𝓢(E, ℂ)) (g : Lp F p) :
    f.toLpFunctional F g = ∫ x, f x • g x := by
  rw [SchwartzMap.toLpFunctional]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
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
/-- The map from bounded continuous functions to `Lp` with `p = ⊤` as a continuous linear map. -/
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

section SobolevEmbedding

open scoped ZeroAtInfty

theorem _root_.memLp_rpow_add_sq_norm (hs : Module.finrank ℝ E < 2 * s) :
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

theorem _root_.memLp_ofReal_rpow_add_sq_norm (hs : Module.finrank ℝ E < 2 * s) :
    MemLp (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) 2 := by
  apply (memLp_rpow_add_sq_norm hs).ofReal

variable (E F) in
/-- The *Sobolev embedding theorem* -/
def toZeroAtInftyAux (hs : Module.finrank ℝ E < 2 * s) : Sobolev E F s 2 →L[ℂ] C₀(E, F) :=
  Real.Lp.fourierTransformInvZeroAtInftyCLM E F ∘L
  ((ContinuousLinearMap.lsmul ℂ ℂ).holderL (volume : Measure E) 2 2 1
    (memLp_ofReal_rpow_add_sq_norm hs).toLp) ∘L
  ((toLpₗᵢ E F s 2).trans (Lp.fourierTransformₗᵢ E F)).toContinuousLinearEquiv.toContinuousLinearMap

theorem toZeroAtInftyAux_apply (hs : Module.finrank ℝ E < 2 * s) (f : Sobolev E F s 2) :
    toZeroAtInftyAux E F hs f = Real.Lp.fourierTransformInvZeroAtInftyCLM E F
      ((memLp_ofReal_rpow_add_sq_norm hs).toLp • 𝓕 f.sobFn) := rfl

theorem toZeroAtInftyAux_apply_toTemperedDistribution (hs : Module.finrank ℝ E < 2 * s)
    (f : Sobolev E F s 2) :
    (toZeroAtInftyAux E F hs f).toBCF.toTemperedDistribution = f.toDistr := by
  have : 𝓕 f.toDistr = MeasureTheory.Lp.toTemperedDistribution
      ((memLp_ofReal_rpow_add_sq_norm hs).toLp • 𝓕 f.sobFn) := by
    rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq (by fun_prop),
      ← smulLeftCLM_fourier_toDistr_eq, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert (smulLeftCLM_const 1 (𝓕 f.toDistr)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  simp [toZeroAtInftyAux_apply, ← MeasureTheory.Lp.fourierInv_toTemperedDistributionCLM_eq, ← this]

end SobolevEmbedding

open BoundedContinuousFunction

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

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def foo' {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) :
    Lp F p (volume : Measure E) →L[ℂ] Lp F p (volume : Measure E) :=
    (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ⊤ p p ((foo s C  hg₁ hg₂).memLp_top.toLp)

theorem foo'_apply {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) (f : Lp F p (volume : Measure E)) :
    foo' s C hg₁ hg₂ f = (foo s C hg₁ hg₂).memLp_top.toLp _ (μ := volume) • f := by
  rfl

theorem toTemperedDistribution_foo' {g : E → ℂ} (s C : ℝ) (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (s / 2)) (f : Lp F p (volume : Measure E)) :
    Lp.toTemperedDistribution (foo' s C hg₁ hg₂ f) =
      smulLeftCLM F (fun x ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2) • g x) f := by
  rw [foo'_apply]
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
  · rfl
  --apply MeasureTheory.Lp.toTemperedDistribution_smul_eq
  rw [coe_foo]
  fun_prop

/-- The Fourier multiplier with a bounded function maps `H ^ s` to `H ^ s'`. -/
def fourierMultiplier {s : ℝ} (s' C : ℝ) {g : E → ℂ} (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) (f : Sobolev E F s 2) :
    Sobolev E F s' 2 where
  toDistr := fourierMultiplierCLM F g f.toDistr
  sobFn := 𝓕⁻ (foo' (s - s') C hg₁ hg₂ (𝓕 f.sobFn))
  bessel_toDistr_eq_sobFn := calc
    _ = 𝓕⁻ ((smulLeftCLM F (fun x ↦ (1 + ‖x‖ ^ 2) ^ (s' / 2) • g x)) (𝓕 f.toDistr)) := by
      rw [besselPotential, fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop)
        (by fun_prop), fourierMultiplierCLM_apply]
      congr
      ext x
      simp [mul_comm]
    _ = 𝓕⁻ (Lp.toTemperedDistribution <| (foo' (s - s') C  hg₁ hg₂) (𝓕 f.sobFn)) := by
      congr 1
      rw [toTemperedDistribution_foo', ← Lp.fourier_toTemperedDistribution_eq,
        ← bessel_toDistr_eq_sobFn, besselPotential, fourierMultiplierCLM_apply,
        fourier_fourierInv_eq, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
      congr
      ext x
      simp only [Complex.real_smul, neg_sub, Pi.mul_apply, ← mul_assoc, mul_eq_mul_right_iff]
      left
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      congr
      ring
    _ = _ := by
      rw [Lp.fourierInv_toTemperedDistribution_eq]

@[simp]
theorem fourierMultiplier_toDistr {s : ℝ} (s' C : ℝ) {g : E → ℂ} (f : Sobolev E F s 2)
    (hg₁ : g.HasTemperateGrowth) (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) :
    (fourierMultiplier s' C hg₁ hg₂ f).toDistr = fourierMultiplierCLM F g f.toDistr := rfl

@[simp]
theorem fourierMultiplier_sobFn {s : ℝ} (s' C : ℝ) {g : E → ℂ} (f : Sobolev E F s 2)
    (hg₁ : g.HasTemperateGrowth) (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) :
    (fourierMultiplier s' C hg₁ hg₂ f).sobFn = 𝓕⁻ (foo' (s - s') C hg₁ hg₂ (𝓕 f.sobFn)) := rfl

/-- The Fourier multiplier with a bounded function maps `H ^ s` to `H ^ s`. -/
def fourierMultiplierCLM (s s' C : ℝ) (g : E → ℂ)
    (hg₁ : g.HasTemperateGrowth) (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2)) :
    Sobolev E F s 2 →L[ℂ] Sobolev E F s' 2 :=
  LinearMap.mkContinuous
    { toFun := fourierMultiplier s' C hg₁ hg₂
      map_add' f₁ f₂ := by
        ext1
        exact (TemperedDistribution.fourierMultiplierCLM F g).map_add f₁.toDistr f₂.toDistr
      map_smul' c f := by
        ext1
        exact (TemperedDistribution.fourierMultiplierCLM F g).map_smul c f.toDistr }
    ‖(foo' (s - s') C hg₁ hg₂ (E := E) (F := F) (p := 2))‖ <| by
    intro f
    simp only [LinearMap.coe_mk, AddHom.coe_mk, ← norm_fourier_sobFn_eq, fourierMultiplier_sobFn,
      fourier_fourierInv_eq]
    exact (foo' (s - s') C hg₁ hg₂).le_opNorm (𝓕 f.sobFn)

@[simp]
theorem fourierMultiplierCLM_apply (s s' C : ℝ) (g : E → ℂ)
    (hg₁ : g.HasTemperateGrowth) (hg₂ : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((s - s') / 2))
    (f : Sobolev E F s 2) :
    f.fourierMultiplierCLM s s' C g hg₁ hg₂ = f.fourierMultiplier s' C hg₁ hg₂ := rfl

open Laplacian Real

set_option backward.isDefEq.respectTransparency false in -- because of real-complex nonsense
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
  rw [← laplacian_apply, laplacian, ContinuousLinearMap.smul_apply,
    fourierMultiplierCLM_apply, toDistr_smul, fourierMultiplier_toDistr,
    laplacian_eq_fourierMultiplierCLM]

end Sobolev

end inner
