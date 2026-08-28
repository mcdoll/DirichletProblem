/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DirichletProblem.Sobolev.Basic
public import DirichletProblem.Mathlib.Analysis.InnerProductSpace.LinearPMap
public import DirichletProblem.Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import DirichletProblem.Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! # Spectral theory of the Laplacian

We prove that the Laplacian is a self-adjoint operator on `L2`.

-/

@[expose] public noncomputable section

variable {𝕜 𝕜' E F : Type*}

section iteratedFDeriv

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E]

theorem norm_iteratedFDeriv_eq_norm_iter_deriv (f : 𝕜' → E) (n : ℕ) (x : 𝕜')
    (hf : ContDiffAt 𝕜' n f x) :
    ‖iteratedFDeriv 𝕜 n f x‖ = ‖deriv^[n] f x‖ := by
  rw [← iteratedDeriv_eq_iterate, ← hf.restrictScalars_iteratedFDeriv]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
  exact norm_iteratedFDeriv_eq_norm_iteratedDeriv

end iteratedFDeriv


variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F]

open scoped InnerProductSpace LinearPMap

open MeasureTheory

variable {s : ℝ}

variable (f : Sobolev E F s 2)

variable (E F) in
/-- The Laplacian as a unbounded operator. -/
def ConcreteLinearPMap.laplacian :
    ConcreteLinearPMap ℂ (Sobolev E F 2 2) (Lp (α := E) F 2) (Lp (α := E) F 2) where
  toFun := (Sobolev.toLpₗ E F (2 - 2) 2) ∘ₗ (Sobolev.laplacian E F 2).toLinearMap
  emb := (Sobolev.toLpₗ E F 0 2) ∘ₗ (Sobolev.mono E F 2 0).toLinearMap
  inj := by
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe]
    rw [Function.Injective.of_comp_iff]
    · exact Sobolev.mono_injective (by simp)
    · exact (Sobolev.toLpₗᵢ E F 0 2).injective

open scoped SchwartzMap Laplacian FourierTransform

@[fun_prop]
theorem ConcreteLinearPMap.continuous_laplacian_toFun :
    Continuous (ConcreteLinearPMap.laplacian E F).toFun := by
  simp only [ConcreteLinearPMap.laplacian, LinearMap.coe_comp, ContinuousLinearMap.coe_coe]
  fun_prop

@[fun_prop]
theorem ConcreteLinearPMap.continuous_laplacian_emb :
    Continuous (ConcreteLinearPMap.laplacian E F).emb := by
  simp only [ConcreteLinearPMap.laplacian, LinearMap.coe_comp, ContinuousLinearMap.coe_coe]
  fun_prop

@[simp]
theorem ConcreteLinearPMap.laplacian_toFun_toSobolev (f : 𝓢(E, F)) :
    (ConcreteLinearPMap.laplacian E F).toFun (f.toSobolev E F 2 2) = (Δ f).toLp 2 := by
  simp only [ConcreteLinearPMap.laplacian, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
    Function.comp_apply, Sobolev.laplacian_apply, ← Sobolev.laplacian_toSobolev,
    Sobolev.toLpₗ_apply]
  rw [SchwartzMap.toSobolev_eq_toLp_of_eq_zero _ (by simp)]

@[simp]
theorem ConcreteLinearPMap.laplacian_emb_toSobolev (f : 𝓢(E, F)) :
    (ConcreteLinearPMap.laplacian E F).emb (f.toSobolev E F 2 2) = f.toLp 2 := by
  simp only [laplacian, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
    Sobolev.toLpₗ_apply]
  rw [f.toSobolev_mono _ _ (by simp), f.toSobolev_eq_toLp_of_eq_zero rfl]

@[simp]
theorem ConcreteLinearPMap.toTemperedDistribution_laplacian_toFun (f : Sobolev E F 2 2) :
    Lp.toTemperedDistribution ((ConcreteLinearPMap.laplacian E F).toFun f) = Δ f.toDistr := by
  simp only [laplacian, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
    Sobolev.laplacian_apply, Sobolev.toLpₗ_apply]
  rw [Sobolev.sobFn_eq_toDistr_of_eq_zero (by simp)]
  simp

@[simp]
theorem ConcreteLinearPMap.toTemperedDistribution_laplacian_emb (f : Sobolev E F 2 2) :
    Lp.toTemperedDistribution ((ConcreteLinearPMap.laplacian E F).emb f) = f.toDistr := by
  simp only [laplacian, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
    Sobolev.toLpₗ_apply]
  rw [Sobolev.sobFn_eq_toDistr_of_eq_zero (by simp)]
  apply Sobolev.mono_apply (by simp)

variable (E F) in
/-- The Laplacian as a unbounded operator. -/
def LinearPMap.laplacian : Lp (α := E) F 2 →ₗ.[ℂ] Lp (α := E) F 2 :=
  (ConcreteLinearPMap.laplacian E F).toLinearPMap

/-- The Laplacian on `ℝ^n` is self-adjoint. -/
theorem LinearPMap.isSymmetric_laplacian : IsSymmetric (LinearPMap.laplacian E F) := by
  apply isSymmetric_toLinearPMap
  intro x y
  induction x, y using (SchwartzMap.denseRange_toSobolev E F 2 (p := 2) (by simp)).induction_on₂
    with
  | hp =>
    exact isClosed_eq (by fun_prop) (by fun_prop)
  | h f g =>
    simp only [ConcreteLinearPMap.laplacian_toFun_toSobolev,
      ConcreteLinearPMap.laplacian_emb_toSobolev, SchwartzMap.inner_toL2_toL2_eq]
    -- actually missing
    apply (SchwartzMap.integral_inner_laplacian_right_eq_left f g).symm

theorem LinearPMap.dense_domain_laplacian :
    Dense ((laplacian E F).domain : Set (Lp (α := E) F 2)) := by
  apply (ConcreteLinearPMap.dense_domain_toLinearPMap_iff _).mpr
  apply (Sobolev.toLpₗᵢ E F 0 2).surjective.denseRange.comp _ (by fun_prop)
  exact Sobolev.denseRange_mono (by simp)

theorem Complex.iteratedDeriv_cpow_const (z : ℂ) (hz : z ∈ slitPlane) (k : ℕ) (r : ℂ) :
    deriv^[k] (fun x : ℂ ↦ x ^ r) z = Polynomial.eval r (descPochhammer ℂ k) * z ^ (r - ↑k) := by
  suffices Set.EqOn (deriv^[k] (fun x : ℂ ↦ x ^ r))
      (fun z ↦ Polynomial.eval r (descPochhammer ℂ k) * z ^ (r - ↑k)) slitPlane from this hz
  induction k with
  | zero =>
    intro z hz
    simp
  | succ k IH =>
    intro z hz
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have : deriv (deriv^[k] fun x ↦ x ^ r) z =
        deriv (fun z ↦ Polynomial.eval r (descPochhammer ℂ k) * z ^ (r - k)) z := by
      refine Filter.EventuallyEq.deriv_eq ?_
      rw [Filter.eventuallyEq_iff_exists_mem]
      use slitPlane
      rw [← Complex.isOpen_slitPlane.mem_nhds_iff] at hz
      simp [IH, hz]
    simp [this, Complex.deriv_cpow_const hz, descPochhammer_succ_right]
    grind only

theorem Complex.iteratedDeriv_inv (z : ℂ) (hz : z ∈ slitPlane) (k : ℕ) :
    deriv^[k] (fun x : ℂ ↦ x⁻¹) z =
      Polynomial.eval (-1) (descPochhammer ℂ k) * z ^ ( - 1 - (k : ℂ)) := by
  simp_rw [← cpow_neg_one, Complex.iteratedDeriv_cpow_const z hz]

open scoped ContDiff

@[fun_prop]
theorem hasTemperateGrowth_const_smul_I_inv (c : ℝ) (hc : c ≠ 0) :
    Function.HasTemperateGrowth fun x : ℝ ↦ (c • Complex.I + x)⁻¹ := by
  set t := { z : ℂ | |c| / 2 < |z.im| }
  have ht_unique : UniqueDiffOn ℝ t := (isOpen_lt (by fun_prop) (by fun_prop)).uniqueDiffOn
  have ht_subset : t ⊆ Complex.slitPlane := by
    intro x hx
    rw [Complex.mem_slitPlane_iff]
    right
    simp [t] at hx
    grind
  have ht : ContDiffOn ℝ ∞ Inv.inv t := by
    suffices t ⊆ {0}ᶜ from (contDiffOn_inv ℝ).mono this
    grw [ht_subset]
    simp
  apply Function.HasTemperateGrowth.comp' (t := t) (f := fun x : ℝ ↦ c • Complex.I + x) _ _ _ _
    (by fun_prop)
  · intro z
    simp only [Complex.real_smul, Set.mem_range, forall_exists_index]
    intro x hx
    rw [← hx]
    simp [t, hc]
  · apply (isOpen_lt (by fun_prop) (by fun_prop)).uniqueDiffOn
  · exact ht
  · intro n
    set C := ∑ k ∈ Finset.range (n + 1), (‖Polynomial.eval (-1) (descPochhammer ℂ k)‖ *
      (|c| / 2) ^ (-1 - (k : ℤ)))
    use 0, C, by positivity [C]
    intro m hmn x hx
    have hx' : x ≠ 0 := Complex.slitPlane_ne_zero (ht_subset hx)
    calc
      _ ≤ ‖Polynomial.eval (-1) (descPochhammer ℂ m)‖ * ‖x ^ (-(1 : ℂ) - m)‖ := by
        rw [iteratedFDerivWithin_eq_iteratedFDeriv ht_unique (by fun_prop) hx,
          norm_iteratedFDeriv_eq_norm_iter_deriv _ _ _ (by fun_prop)]
        rw [Complex.iteratedDeriv_inv _ (ht_subset hx)]
        simp
      _ ≤ ‖Polynomial.eval (-1) (descPochhammer ℂ m)‖ * (|c| / 2)  ^ (-(1 : ℤ) - m) := by
        gcongr
        suffices (|c| / 2) ^ (m + 1) ≤ ‖x‖ ^ (m + 1) by
          rw [Complex.cpow_sub (-1) m hx', zpow_sub₀ (by positivity)]
          simp_rw [div_pow, pow_add] at this
          simp [Complex.cpow_neg_one, div_pow]
          field_simp at this ⊢
          simpa
        gcongr
        simp only [Set.mem_ofPred_eq, t] at hx
        grw [hx]
        exact Complex.abs_im_le_norm x
      _ ≤ _ := by
        simp only [Int.reduceNeg, C, pow_zero, mul_one]
        have hmn' : m ∈ Finset.range (n + 1) := by simpa using hmn
        apply Finset.single_le_sum (fun _ _ ↦ by positivity) hmn'

def foobar (c C : ℝ) (f : E → ℝ) (hC : 0 < C) (hc : c ≠ 0) (hf : f.HasTemperateGrowth)
    (hf' : ∀ x, (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ C * (1 + ‖f x‖))
    (u : Lp (α := E) F 2) : Sobolev E F s 2 :=
  Sobolev.fourierMultiplierCLM 0 s (2 * C * max 1 (|c|⁻¹)) (fun x ↦ (c • Complex.I + f x)⁻¹) ?_ ?_
    (Sobolev.ofLp 0 u)
where finally
  · suffices Function.HasTemperateGrowth fun x : ℝ ↦ (c • Complex.I + x)⁻¹ from this.comp hf
    fun_prop
  · intro x
    simp only [Complex.real_smul, norm_inv, zero_sub]
    have h_pos : 0 < ‖c * Complex.I + (f x)‖ := by
      rw [norm_pos_iff]
      refine Complex.slitPlane_ne_zero ?_
      -- might be useful somewhere else:
      refine Complex.mem_slitPlane_iff.mpr ?_
      simp [hc]
    suffices (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ (2 * C * max 1 (|c|⁻¹)) * ‖c * Complex.I + (f x)‖ by
      rw [neg_div 2 s]
      rw [Real.rpow_neg (by positivity) (s / 2)]
      field_simp
      grind
    calc
      _ ≤ C * (1 + ‖f x‖) := hf' x
      _ ≤ C * (max 1 (|c|⁻¹) * (‖c • Complex.I‖ + ‖f x‖)) := by
        rw [mul_add (max _ _)]
        gcongr
        · rw [sup_mul₀ (by positivity)]
          apply le_sup_of_le_right
          simp [hc]
        · rw [sup_mul₀ (by positivity)]
          refine le_sup_of_le_left ?_
          simp
      _ ≤ C * (max 1 (|c|⁻¹) * (2 * ‖c • Complex.I + f x‖)) := by
        gcongr
        simp only [Complex.real_smul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one]
        rw [two_mul]
        gcongr
        · grw [← Complex.abs_im_le_norm ]
          simp
        · grw [← Complex.abs_re_le_norm ]
          simp
      _ = (2 * C * max 1 (|c|⁻¹)) * ‖c • Complex.I + f x‖ := by ring

@[simp]
theorem foobar_toDistr (c C : ℝ) (f : E → ℝ) (hC : 0 < C) (hc : c ≠ 0) (hf : f.HasTemperateGrowth)
    (hf' : ∀ x, (1 + ‖x‖ ^ 2) ^ (s / 2) ≤ C * (1 + ‖f x‖))
    (u : Lp (α := E) F 2) : (foobar c C f hC hc hf hf' u).toDistr =
    (Lp.toTemperedDistribution u).fourierMultiplierCLM F (fun x ↦ (c • Complex.I + f x)⁻¹) := by
  simp [foobar]

open Real

def foobarLaplacian (c : ℝ) (hc : c ≠ 0) (u : Lp (α := E) F 2) : Sobolev E F 2 2 :=
  foobar c (max 1 ((2 * π) ^ 2)⁻¹) (fun x ↦ -(2 * π) ^ 2 * ‖x‖ ^ 2) ?_ hc ?_ ?_ u
where finally
  · positivity
  · fun_prop
  · intro x
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self, rpow_one]
    rw [mul_add]
    gcongr
    · simp
    · have : 1 ≤ max 1 ((2 * π) ^ 2)⁻¹ * (2 * π) ^ 2 := by
        -- this is a bit silly, because the max is always `1`, but proof is simpler currently
        -- need some grind improvements
        rw [sup_mul₀ (by positivity)]
        refine le_sup_of_le_right ?_
        simp
      simp only [neg_mul, norm_neg, norm_mul, norm_pow, norm_ofNat, norm_eq_abs, ge_iff_le]
      rw [abs_of_pos (by positivity)]
      grw [← mul_assoc, ← this]
      simp

@[simp]
theorem foobarLaplacian_toDistr (c : ℝ) (hc : c ≠ 0) (u : Lp (α := E) F 2) :
    (foobarLaplacian c hc u).toDistr = (Lp.toTemperedDistribution u).fourierMultiplierCLM F
      (fun x ↦ (c • Complex.I - (2 * π) ^ 2 * ‖x‖ ^ 2)⁻¹) := by
  simp [foobarLaplacian, ← sub_eq_add_neg]

theorem foobarLaplacian_prop (c : ℝ) (hc : c ≠ 0) (u : Lp (α := E) F 2) :
    ((c • Complex.I) • (ConcreteLinearPMap.laplacian E F).emb (foobarLaplacian c hc u) +
      (ConcreteLinearPMap.laplacian E F).toFun (foobarLaplacian c hc u)) = u := by
  apply Lp.toTemperedDistribution_injective
  -- this should be a `calc` block
  simp_rw [← Lp.toTemperedDistributionCLM_apply]
  simp only [_root_.map_add, _root_.map_smul]
  simp only [Lp.toTemperedDistributionCLM_apply,
    ConcreteLinearPMap.toTemperedDistribution_laplacian_emb, foobarLaplacian_toDistr,
    ConcreteLinearPMap.toTemperedDistribution_laplacian_toFun]
  rw [← _root_.smul_apply]
  have : Function.HasTemperateGrowth fun x : E ↦ ((c • Complex.I) - (2 * π) ^ 2 * ‖x‖ ^ 2)⁻¹ := by
    have h₁ : Function.HasTemperateGrowth fun x : ℝ ↦ (c • Complex.I + x)⁻¹ := by fun_prop
    have h₂ : Function.HasTemperateGrowth fun x : E ↦ -(2 * π) ^ 2 * ‖x‖ ^ 2 := by fun_prop
    convert h₁.comp h₂
    simp [← sub_eq_add_neg]
  rw [← TemperedDistribution.fourierMultiplierCLM_smul this]
  rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply this (by fun_prop)]
  rw [← _root_.smul_apply]
  rw [← Complex.coe_smul (-(2 * π) ^ 2)]
  rw [← TemperedDistribution.fourierMultiplierCLM_smul (by fun_prop)]
  rw [← TemperedDistribution.fourierMultiplierCLM_add_apply (by fun_prop) (by fun_prop)]
  convert DFunLike.ext_iff.mp (TemperedDistribution.fourierMultiplierCLM_const 1) _ with x
  · simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_ofNat, neg_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
      Pi.mul_apply]
    have : (c * Complex.I - 2 ^ 2 * π ^ 2 * ‖x‖ ^ 2) ≠ 0 := by
      rw [ne_eq, Complex.ext_iff, not_and_or, Complex.sub_im]
      norm_cast
      simp [hc]
    field_simp
    ring
  · simp
  · infer_instance


/-- The Laplacian on `ℝ^n` is self-adjoint. -/
theorem LinearPMap.isSelfAdjoint_laplacian : IsSelfAdjoint (LinearPMap.laplacian E F) := by
  apply (isSelfAdjoint_tfae LinearPMap.isSymmetric_laplacian LinearPMap.dense_domain_laplacian
    |>.out 1 3).mpr
  -- first step: reduction to a `Lp` or distribution statement
  constructor
  · rw [Submodule.eq_top_iff']
    intro u
    simp only [vadd_domain, vadd_toFun, LinearMap.mem_range, LinearMap.add_apply,
      LinearMap.coe_comp, LinearMap.coe_smul, LinearMap.id_coe, Submodule.coe_subtype,
      Function.comp_apply, Pi.smul_apply, id_eq, toFun_eq_coe]
    suffices ∃ f : Sobolev E F 2 2, Complex.I • ((ConcreteLinearPMap.laplacian E F).emb f) +
        ((ConcreteLinearPMap.laplacian E F).toFun f) = u by
      obtain ⟨f, hf⟩ := this
      use ⟨(ConcreteLinearPMap.laplacian E F).emb f, by simp [laplacian]⟩
      convert hf
      apply ConcreteLinearPMap.toLinearPMap_apply
    use foobarLaplacian 1 (by simp) u
    simpa using foobarLaplacian_prop 1 (by simp) u
  · rw [Submodule.eq_top_iff']
    intro u
    simp only [vadd_domain, vadd_toFun, LinearMap.mem_range, LinearMap.add_apply,
      LinearMap.coe_comp, LinearMap.coe_smul, LinearMap.id_coe, Submodule.coe_subtype,
      Function.comp_apply, Pi.smul_apply, id_eq, toFun_eq_coe]
    suffices ∃ f : Sobolev E F 2 2, (-Complex.I) • ((ConcreteLinearPMap.laplacian E F).emb f) +
        ((ConcreteLinearPMap.laplacian E F).toFun f) = u by
      obtain ⟨f, hf⟩ := this
      use ⟨(ConcreteLinearPMap.laplacian E F).emb f, by simp [laplacian]⟩
      convert hf
      apply ConcreteLinearPMap.toLinearPMap_apply
    use foobarLaplacian (-1) (by simp) u
    simpa using foobarLaplacian_prop (-1) (by simp) u
