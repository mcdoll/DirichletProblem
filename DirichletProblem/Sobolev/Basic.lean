/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DirichletProblem.Mathlib.Analysis.Distribution.Sobolev
public import DirichletProblem.Mathlib.Analysis.Fourier.ZeroAtInfty
public import DirichletProblem.Mathlib.Analysis.Distribution.TemperedDistribution

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
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [-Lp.toTemperedDistributionCLM_apply] }

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

instance instInnerProductSpace (s : ℝ) :
    InnerProductSpace ℂ (Sobolev E F s 2) where
  inner f g := inner ℂ f.sobFn g.sobFn
  norm_sq_eq_re_inner f := by simp; norm_cast
  conj_inner_symm f g := by simp
  add_left f g h := by simp [inner_add_left]
  smul_left f g c := by simp [inner_smul_left]

open Laplacian

instance instLaplacian (s : ℝ) : Laplacian (Sobolev E F s 2) (Sobolev E F (s - 2) 2) where
  laplacian f := f.memSobolev_toDistr.laplacian.toSobolev

@[simp]
theorem laplacian_toDistr {s : ℝ} (f : Sobolev E F s 2) : (Δ f).toDistr = Δ f.toDistr := rfl

def laplacianₗ {s : ℝ} : Sobolev E F s 2 →ₗ[ℂ] Sobolev E F (s - 2) 2 where
  toFun := Δ
  map_add' f g := by
    ext1
    simpa using (LineDeriv.laplacianCLM ℂ E 𝓢'(E, F)).map_add f.toDistr g.toDistr
  map_smul' c f := by
    ext1
    simpa only [laplacian_toDistr, laplacianCLM_apply] using
      (LineDeriv.laplacianCLM ℂ E 𝓢'(E, F)).map_smul c f.toDistr

end Sobolev

end inner
