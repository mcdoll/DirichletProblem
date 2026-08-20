/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Algebra.Order.AddTorsor

/-! # Extension of linear maps -/

@[expose] public noncomputable section


open NormedField Set Seminorm TopologicalSpace Filter List Bornology

open NNReal Pointwise Topology Uniformity

variable {𝕜 𝕜₁ 𝕜₂ 𝕜₁' 𝕜₂' E E₁ E₂ Eₗ F F₁ F₂ ι ι' : Type*}

section WithSeminormsEmbedding

variable [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E₁] [Module 𝕜₁ E₁] [AddCommGroup E₂] [Module 𝕜₂ E₂]

namespace Seminorm

/-- A seminorm `p` is bounded by another seminorm `q` if there exists `C : ℝ≥0` such that
`p ≤ C • q`. -/
def IsBoundedBy (p q : Seminorm 𝕜₁ E₁) : Prop :=
  ∃ (C : ℝ≥0), p ≤ C • q

/-- Two seminorms `p, q` are equivalent if `p` is bounded by `q` and `q` is bounded by `p`. -/
def IsEquivalent (p q : Seminorm 𝕜₁ E₁) : Prop :=
  ∃ (C : ℝ≥0), p ≤ C • q ∧ q ≤ C • p

variable {p p' q q' : Seminorm 𝕜₁ E₁}

theorem isBoundedBy_iff (p q : Seminorm 𝕜₁ E₁) :
    p.IsBoundedBy q ↔ ∃ (C : ℝ≥0), p ≤ C • q := by rfl

/-- A seminorm `p` is bounded by another seminorm `q` if and only if there exists `C : ℝ` such that
for all `x`, `p x ≤ C * q x`. -/
@[grind =]
theorem isBoundedBy_iff_forall (p q : Seminorm 𝕜₁ E₁) :
    p.IsBoundedBy q ↔ ∃ C, ∀ x, p x ≤ C * q x := by
  rw [isBoundedBy_iff]
  constructor
  · intro ⟨C, h⟩
    use C
    intro x
    rw [Seminorm.le_def] at h
    grw [h x]
    norm_cast
  · intro ⟨C, h⟩
    use C.toNNReal
    rw [Seminorm.le_def]
    intro x
    grw [h x]
    suffices C • q x ≤ (C.toNNReal : ℝ) • q x by simpa using! this
    gcongr
    simp

variable {R : Type*} [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]
  [Preorder R] [Zero R] [IsOrderedModule R ℝ]

instance : IsOrderedSMul R (Seminorm 𝕜₁ E₁) where
  smul_le_smul_left p q hpq c := by
    rw [le_def] at hpq ⊢
    intro x
    simp only [smul_apply]
    have hp : (c • (1 : ℝ≥0)) • p x = c • p x := by simp
    have hq : (c • (1 : ℝ≥0)) • q x = c • q x := by simp
    grw [← hp, smul_le_smul_of_nonneg_left (hpq x) (by positivity), hq]
  smul_le_smul_right a b hab p := by
    rw [le_def]
    intro x
    simp only [smul_apply]
    grw [smul_le_smul_of_nonneg_right hab (by positivity)]

@[grind .]
theorem isBoundedBy_self (p : Seminorm 𝕜₁ E₁) : p.IsBoundedBy p := by
  use 1
  simp

@[grind →]
theorem IsBoundedBy.trans (h : p.IsBoundedBy q) (h' : q.IsBoundedBy q') :
    p.IsBoundedBy q' := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  use C * C'
  grw [h, h']
  simp [← smul_assoc]

@[grind .]
theorem IsBoundedBy.smul_left (h : p.IsBoundedBy q) (a : R) : (a • p).IsBoundedBy q := by
  obtain ⟨C, h⟩ := h
  use a • C
  grw [h, smul_assoc]

@[grind ←]
theorem IsBoundedBy.smul_right (h : p.IsBoundedBy q) {a : ℝ≥0} (ha : a ≠ 0) :
    p.IsBoundedBy (a • q) := by
  obtain ⟨C, h⟩ := h
  use a⁻¹ • C
  calc
    _ ≤ C • q := h
    _ = _ := by
      rw [← smul_assoc]
      congr
      simp [field]

attribute [gcongr] IsOrderedSMul.smul_le_smul

@[grind .]
theorem IsBoundedBy.add (h : p.IsBoundedBy q) (h' : p'.IsBoundedBy q') :
    (p + p').IsBoundedBy (q + q') := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  use max C C'
  calc
    _ ≤ C • q + C' • q' := by grw [h, h']
    _ ≤ max C C' • q + max C C' • q' := by
      gcongr
      all_goals simp
    _ = _ := by simp

instance : IsStrictOrderedModule ℕ ℝ where

--instance : IsOrderedModule ℕ ℝ where

@[grind .]
theorem IsBoundedBy.add_left (h : p.IsBoundedBy q) (h' : p'.IsBoundedBy q) :
    (p + p').IsBoundedBy q := by
  have h₁ : (p + p').IsBoundedBy (q + q) := h.add h'
  have h₂ : (2 • q).IsBoundedBy q := by grind
  grind [two_nsmul]

@[symm]
theorem IsEquivalent.symm (h : p.IsEquivalent q) : q.IsEquivalent p := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, h.symm⟩

@[grind =]
theorem isEquivalent_comm (p q : Seminorm 𝕜₁ E₁) : p.IsEquivalent q ↔ q.IsEquivalent p :=
  ⟨(·.symm), (·.symm)⟩

@[grind =]
theorem isEquivalent_iff_isBoundedBy (p q : Seminorm 𝕜₁ E₁) :
    p.IsEquivalent q ↔ p.IsBoundedBy q ∧ q.IsBoundedBy p := by
  constructor
  · intro ⟨C, h₁, h₂⟩
    exact ⟨⟨C, h₁⟩, ⟨C, h₂⟩⟩
  · intro ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩
    use max C₁ C₂
    constructor
    · grw [h₁]
      gcongr
      simp
    · grw [h₂]
      gcongr
      simp

theorem isEquivalent_self (p : Seminorm 𝕜₁ E₁) : p.IsEquivalent p := by grind

end Seminorm

def SeminormFamily.IsBoundedBy (p : SeminormFamily 𝕜₁ E₁ ι) (q : SeminormFamily 𝕜₁ E₁ ι') : Prop :=
  ∀ i, ∃ (s : Finset ι'), (p i).IsBoundedBy (s.sup q)

def SeminormFamily.IsEquivalent (p : SeminormFamily 𝕜₁ E₁ ι) (q : SeminormFamily 𝕜₁ E₁ ι') : Prop :=
  p.IsBoundedBy q ∧ q.IsBoundedBy p

def IsWithSeminormsMap (f : E₁ →ₛₗ[σ₁₂] E₂) (p : SeminormFamily 𝕜₁ E₁ ι)
    (q : SeminormFamily 𝕜₂ E₂ ι') : Prop :=
  Seminorm.IsBounded (q.comp f) p LinearMap.id

variable [TopologicalSpace E₁] [TopologicalSpace E₂]

variable (𝕜₁ E₁) in
def continuousSeminorms : SeminormFamily 𝕜₁ E₁ {p : Seminorm 𝕜₁ E₁ // Continuous p} := (·.1)

def IsCodomainEmbedding [PolynormableSpace 𝕜₂ E₂] (f : E₁ →ₛₗ[σ₁₂] E₂)
    (p : SeminormFamily 𝕜₁ E₁ ι) : Prop :=
  ((continuousSeminorms 𝕜₂ E₂).comp f).IsBoundedBy p

structure IsDomainEmbedding [PolynormableSpace 𝕜₁ E₁] (f : E₁ →ₛₗ[σ₁₂] E₂)
    (q : SeminormFamily 𝕜₂ E₂ ι') : Prop where
  dense : DenseRange f
  foobar : (continuousSeminorms 𝕜₁ E₁).IsBoundedBy (q.comp f)

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
structure WithSeminormsEmbedding (f : E₁ →ₛₗ[σ₁₂] E₂) (p : SeminormFamily 𝕜₁ E₁ ι)
    (q : SeminormFamily 𝕜₂ E₂ ι') : Prop where
  dense : DenseRange f
  isWithSeminorms : (q.comp f).IsBoundedBy p
  foobar : p.IsBoundedBy (q.comp f)

variable {f : E₁ →ₛₗ[σ₁₂] E₂} {p : SeminormFamily 𝕜₁ E₁ ι} {q : SeminormFamily 𝕜₂ E₂ ι'}

omit [TopologicalSpace E₁] [TopologicalSpace E₂] in
theorem isWithSeminormsMap_def : IsWithSeminormsMap f p q ↔
      ∀ i, ∃ (s : Finset ι') (C : ℝ≥0), ∀ x, p i x ≤ C • (s.sup q) (f x) := by
  unfold IsWithSeminormsMap Seminorm.IsBounded
  simp_rw [Seminorm.le_def]
  congrm (∀ i, ∃ s C, ∀ x, ?_)
  simp [← SeminormFamily.finset_sup_comp q s f]

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
structure WithSeminormsEmbedding' (f : E₁ →ₛₗ[σ₁₂] E₂) (p : SeminormFamily 𝕜₂ E₂ ι) : Prop where
  dense : DenseRange f
  withSeminorms_comp : WithSeminorms (p.comp f)


theorem t2space_iff [IsTopologicalAddGroup E₁] {p : SeminormFamily 𝕜₁ E₁ ι} (hp : WithSeminorms p) :
    T2Space E₁ ↔ ∀ x, (∀ i, p i x = 0) → x = 0 := by
  have : T2Space E₁ ↔ ∀ (x : E₁), x ≠ 0 → ∃ U ∈ 𝓝 0, x ∉ U := by
    constructor
    · intro h x
      have ht1 : T1Space E₁ := inferInstance
      contrapose!
      simp_rw [t1Space_iff_specializes_imp_eq, specializes_iff_pure, Filter.pure_le_iff] at ht1
      apply ht1
    · intro h
      exact IsTopologicalAddGroup.t2Space_of_zero_sep h
  rw [this]
  congrm (∀ x, ?_)
  suffices (∀ x_1 ∈ 𝓝 0, x ∈ x_1) ↔ ∀ (i : ι), (p i) x = 0 by grind
  constructor
  · intro h i
    apply le_antisymm _ (by positivity)
    rw [← forall_gt_iff_le]
    intro ε hε
    simpa using h ((p i).ball 0 ε) (ball_mem_nhds (WithSeminorms.continuous_seminorm hp i) hε)
  · intro h U hU
    rw [hp.mem_nhds_iff] at hU
    obtain ⟨s, r, hr, hs⟩ := hU
    apply hs
    suffices s.sup p x = 0 by simp [this, hr]
    exact le_antisymm (finset_sup_apply_le (by simp) (by grind)) (by positivity)

end WithSeminormsEmbedding

section foo

variable [NontriviallyNormedField 𝕜₁] [NormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E₁] [Module 𝕜₁ E₁] [AddCommGroup E₂] [Module 𝕜₂ E₂]

variable [TopologicalSpace E₁] [TopologicalSpace E₂]

variable {f : E₁ →ₛₗ[σ₁₂] E₂} {p : SeminormFamily 𝕜₁ E₁ ι} {q : SeminormFamily 𝕜₂ E₂ ι'}

theorem continuous_iff_isBounded (hp : WithSeminorms p) (hq : WithSeminorms q) :
    Continuous f ↔ Seminorm.IsBounded p q f := by
  constructor
  · intro h i
    have := hq.topologicalAddGroup
    have := hp.topologicalAddGroup
    rw [hq.continuous_iff_continuous_comp] at h
    obtain ⟨s, C, _, h⟩ := ((q i).comp f).bound_of_continuous hp (h i)
    exact ⟨s, C, h⟩
  · exact WithSeminorms.continuous_of_isBounded hp hq f

theorem WithSeminorms.continuous_iff_isBoundedBy (hp : WithSeminorms p) (hq : WithSeminorms q) :
    Continuous f ↔ (q.comp f).IsBoundedBy p := by
  constructor
  · intro h i
    have := hq.topologicalAddGroup
    have := hp.topologicalAddGroup
    rw [hq.continuous_iff_continuous_comp] at h
    obtain ⟨s, C, _, h⟩ := ((q i).comp f).bound_of_continuous hp (h i)
    exact ⟨s, C, h⟩
  · exact WithSeminorms.continuous_of_isBounded hp hq f

theorem WithSeminorms.isBoundedBy {p : SeminormFamily 𝕜₁ E₁ ι} {q : SeminormFamily 𝕜₁ E₁ ι'}
    (hp : WithSeminorms p) (hq : WithSeminorms q) : p.IsBoundedBy q := by
  have : Continuous LinearMap.id := (ContinuousLinearMap.id 𝕜₁ E₁).continuous
  rw [hq.continuous_iff_isBoundedBy hp] at this
  exact this

end foo

namespace LinearMap

section compInv

variable [NormedField 𝕜] [NormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup Eₗ]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable {p : SeminormFamily 𝕜 Eₗ ι} {q : SeminormFamily 𝕜₂ F ι'}
variable (f : E →ₛₗ[σ₁₂] F) (g : E →ₗ[𝕜] Eₗ)

variable (i : ι) (i' : ι')

theorem ker_le_ker_of_isBoundedBy_comp_comp (hq : ∀ x, x ≠ 0 → ∃ i, q i x ≠ 0)
    (h : (q.comp f).IsBoundedBy (p.comp g)) :
    g.ker ≤ f.ker := by
  intro x (hx : g x = 0)
  suffices ∀ (i : ι'), (q i) (f x) = 0 by
    specialize hq (f x)
    simp; grind
  intro i
  obtain ⟨s, C, hC⟩ := h i
  rw [Seminorm.le_def] at hC
  apply le_antisymm _ (by positivity)
  convert! hC x
  simp [← SeminormFamily.finset_sup_comp, hx]

variable [TopologicalSpace Eₗ] [TopologicalSpace F]

open scoped Classical in
/-- Composition of a semilinear map `f` with the left inverse of a linear map `g` as a continuous
linear map provided that the norm estimate `‖f x‖ ≤ C * ‖g x‖` holds for all `x : E`. -/
def compLeftInverse' [T2Space F] (hp : WithSeminorms p) (hq : WithSeminorms q) :
    g.range →SL[σ₁₂] F :=
  if h : (q.comp f).IsBoundedBy (p.comp g) then
  ⟨((g.ker.liftQ f ?_).comp g.quotKerEquivRange.symm.toLinearMap), ?_⟩
  else 0
where finally
  · exact ker_le_ker_of_isBoundedBy_comp_comp f g hq.separating_of_T1 h
  · refine WithSeminorms.continuous_of_isBounded (p := p.comp g.range.subtype) ?_ hq _ ?_
    · apply LinearMap.withSeminorms_induced hp
    · intro i
      obtain ⟨s, C, hC⟩ := h i
      use s, C
      intro ⟨y, x, hxy⟩
      simpa [← SeminormFamily.finset_sup_comp, ← hxy] using! hC x

theorem compLeftInverse_apply_of_bdd' [T2Space F] (hp : WithSeminorms p) (hq : WithSeminorms q)
    (h : (q.comp f).IsBoundedBy (p.comp g))
    (x : E) (y : Eₗ) (hx : g x = y) :
    f.compLeftInverse' g hp hq ⟨y, ⟨x, hx⟩⟩ = f x := by
  simp [compLeftInverse', h, ← hx]

end compInv

section Extend

variable [NormedField 𝕜] [NormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup Eₗ]
  [UniformSpace F] [IsUniformAddGroup F]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]

variable [UniformSpace Eₗ] [IsUniformAddGroup Eₗ] [ContinuousConstSMul 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜₂ F] [CompleteSpace F]

variable (S : Submodule 𝕜 Eₗ)

instance (S : Submodule 𝕜 Eₗ) : IsUniformAddGroup S :=
  inferInstanceAs (IsUniformAddGroup S.toAddSubgroup)

variable {p : SeminormFamily 𝕜 Eₗ ι} {q : SeminormFamily 𝕜₂ F ι'}
variable (f : E →ₛₗ[σ₁₂] F) (e : E →ₗ[𝕜] Eₗ)

/-- Extension of a linear map `f : E →ₛₗ[σ₁₂] F` to a continuous linear map `Eₗ →SL[σ₁₂] F`,
where `E` is a normed space and `F` a complete normed space, using a dense map `e : E →ₗ[𝕜] Eₗ`
together with a bound `‖f x‖ ≤ C * ‖e x‖` for all `x : E`. -/
def extendOfNorm' [T2Space F] (hp : WithSeminorms p) (hq : WithSeminorms q) :
    Eₗ →SL[σ₁₂] F := (f.compLeftInverse' e hp hq).extend e.range.subtypeL

end Extend

end LinearMap
