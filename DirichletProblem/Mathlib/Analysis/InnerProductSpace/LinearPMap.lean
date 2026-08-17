/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Symmetric and self-adjoint operators -/

@[expose] public noncomputable section

open RCLike LinearPMap WithLp

open scoped ComplexConjugate

variable {𝕜 E E' F : Type*} [RCLike 𝕜]

section LinearMap

variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

end LinearMap


variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearPMap

/-- A linear map is symmetric if it is its own formal adjoint. -/
def IsSymmetric (T : E →ₗ.[𝕜] E) : Prop :=
  T.IsFormalAdjoint T

/-- A linear map is essentially self-adjoint if its closure is self-adjoint. -/
def IsEssentiallySelfAdjoint (T : E →ₗ.[𝕜] E) : Prop :=
  IsSelfAdjoint (T.closure)

variable {T S : E →ₗ.[𝕜] E}

/- todo: move this-/
theorem IsClosed.closure_eq (hT : T.IsClosed) : T.closure = T := by
  apply eq_of_eq_graph
  rw [← hT.isClosable.graph_closure_eq_closure_graph, hT.submodule_topologicalClosure_eq]

theorem mem_range_iff' {f : E →ₗ.[𝕜] E} {y : E} : y ∈ f.toFun.range ↔ ∃ x : E, (x, y) ∈ f.graph := by
  exact LinearPMap.mem_range_iff

theorem IsClosed.vadd {f : E →ₗ.[𝕜] E} (hf : f.IsClosed) (g : E →ₗ[𝕜] E) : (g +ᵥ f).IsClosed := by
  rw [IsClosed] at hf ⊢

  sorry

theorem IsClosable.closure_adjoint (hT : T.IsClosable) (hT' : Dense (T.domain : Set E)) :
    T.closure† = T† := by
  apply eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint sorry, adjoint_graph_eq_graph_adjoint hT',
    ← hT.graph_closure_eq_closure_graph]

  sorry


theorem IsSymmetric.of_le (hT : T.IsSymmetric) (h : S ≤ T) : S.IsSymmetric := by
  intro x y
  obtain ⟨x', hx, hx'⟩ := exists_of_le h x
  obtain ⟨y', hy, hy'⟩ := exists_of_le h y
  rw [hx, hx', hy, hy']
  apply hT x' y'

theorem IsSymmetric.le_adjoint (hT : T.IsSymmetric) (hT' : Dense (T.domain : Set E)) : T ≤ T† := by
  constructor
  · intro x hx
    apply mem_adjoint_domain_of_exists
    use T ⟨x, hx⟩
    intro y
    apply hT
  · intro x y hxy
    symm
    apply adjoint_apply_eq hT' y
    intro x'
    rw [← hxy]
    apply hT

theorem IsSymmetric.isSelfAdjoint_of_le_domain (hT : T.IsSymmetric) (hT' : Dense (T.domain : Set E))
    (hT'' : T†.domain ≤ T.domain) : IsSelfAdjoint T := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine (eq_of_le_of_domain_eq (hT.le_adjoint hT') ?_).symm
  apply le_antisymm (hT.le_adjoint hT').1 hT''

theorem _root_.IsSelfAdjoint.isEssentiallySelfAdjoint (hT : IsSelfAdjoint T) :
    T.IsEssentiallySelfAdjoint := by
  unfold IsEssentiallySelfAdjoint
  convert hT
  rw [hT.isClosed.closure_eq]

theorem IsSelfAdjoint.adjoint_eq (hT : IsSelfAdjoint T) : T† = T := hT

theorem IsSelfAdjoint.isSelfAdjoint_adjoint (hT : IsSelfAdjoint T) : IsSelfAdjoint T† := by
  rwa [IsSelfAdjoint.adjoint_eq hT]

theorem IsSelfAdjoint.isSymmetric (hT : IsSelfAdjoint T) : T.IsSymmetric := by
  unfold IsSymmetric
  convert adjoint_isFormalAdjoint hT.dense_domain
  exact hT.symm

theorem IsEssentiallySelfAdjoint.isSymmetric (hT : T.IsEssentiallySelfAdjoint) : T.IsSymmetric :=
  (IsSelfAdjoint.isSymmetric hT).of_le (le_closure T)

theorem IsEssentiallySelfAdjoint.isClosable (hT : T.IsEssentiallySelfAdjoint) : T.IsClosable :=
  hT.isClosed.isClosable.leIsClosable (le_closure T)

theorem IsEssentiallySelfAdjoint.existsUnique_isSelfAdjoint (hT : T.IsEssentiallySelfAdjoint) :
    ∃! S : E →ₗ.[𝕜] E, IsSelfAdjoint S ∧ T ≤ S := by
  apply existsUnique_of_exists_of_unique
  · exact ⟨T.closure, hT, le_closure T⟩
  · intro S₁ S₂ ⟨hS₁, hTS₁⟩ ⟨hS₂, hTS₂⟩
    -- S₁ = S₁† ≤ T† ≤ T†† ≤ S₂†† = S₂
    sorry

open Complex

omit [CompleteSpace E'] in
theorem bar {T : E' →ₗ.[ℂ] E'} (hT : T.IsSymmetric) (c : ℝ) (x : T.domain) :
    ‖(c • I) • x + T x‖ ^ 2 = ‖c‖ ^2 * ‖x‖ ^ 2 + ‖T x‖ ^ 2 := by
  simp_rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  simp_rw [inner_add_add_self]
  simp_rw [inner_smul_left, inner_smul_right]
  simp_rw [← mul_assoc, RCLike.conj_mul]
  simp [hT x x]
  norm_cast
  simp

theorem bar' {T : E' →ₗ.[ℂ] E'} (hT : T.IsSymmetric) (h₁ : T.IsClosed) {c : ℝ} (hc : c ≠ 0) :
    _root_.IsClosed (((c • I) • LinearMap.id (R := ℂ) (M := E') +ᵥ T).toFun.range : Set E') := by
      apply IsSeqClosed.isClosed
      intro x x₀ hx h_lim
      simp only [vadd_domain, SetLike.mem_coe, LinearMap.mem_range, toFun_eq_coe, coe_vadd,
        LinearMap.coe_comp, LinearMap.coe_smul,
        LinearMap.id_coe, Submodule.coe_subtype, Pi.add_apply, Function.comp_apply,
        Pi.smul_apply, id_eq, Subtype.exists] at h_lim hx
      choose a ha_mem hax using hx
      have : ∃ a₀, Filter.Tendsto a Filter.atTop (nhds a₀) := by
        apply cauchySeq_tendsto_of_complete
        obtain ⟨b, hb, h, hb'⟩ := cauchySeq_iff_le_tendsto_0.mp h_lim.cauchySeq
        refine cauchySeq_iff_le_tendsto_0.mpr ?_
        have hb_lim : Filter.Tendsto (‖c‖⁻¹ • b) Filter.atTop (nhds 0) := by
          simpa using! hb'.const_smul ‖c‖⁻¹
        use ‖c‖⁻¹ • b, ?_, ?_, hb_lim
        · intro n
          specialize hb n
          simp only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul]
          positivity
        simp only [Pi.smul_apply, smul_eq_mul]
        intro n m N hn hm
        grw [← h n m N hn hm]
        simp_rw [dist_eq_norm]
        rw [le_inv_mul_iff₀ (by positivity)]
        apply le_of_sq_le_sq _ (by positivity)
        calc
          _ ≤ ‖c‖ ^ 2 * ‖a n - a m‖ ^ 2 + ‖T (⟨a n, ha_mem n⟩ - ⟨a m, ha_mem m⟩)‖ ^ 2 := by
            rw [mul_pow]
            refine le_add_of_nonneg_right ?_
            positivity
          _ = ‖((c • Complex.I) • (a n - a m)) + T (⟨a n, ha_mem n⟩ - ⟨a m, ha_mem m⟩)‖ ^ 2 := by
            simpa using (bar hT c (⟨a n, ha_mem n⟩ - ⟨a m, ha_mem m⟩)).symm
          _ = _ := by
            congr
            simp_rw [← hax, LinearPMap.map_sub]
            module
      obtain ⟨a₀, ha_lim⟩ := this
      have ha₀' : (a₀, x₀) ∈ ((c • Complex.I) • LinearMap.id (R := ℂ) (M := E') +ᵥ T).graph := by
        apply IsClosed.isSeqClosed (h₁.vadd _) (x := fun n ↦ (a n, x n)) (p := (a₀, x₀))
        · intro n
          simp only [SetLike.mem_coe, mem_graph_iff, vadd_domain, coe_vadd,
            LinearMap.coe_comp, LinearMap.coe_smul,
            LinearMap.id_coe, Submodule.coe_subtype, Pi.add_apply,
            Function.comp_apply, Pi.smul_apply, id_eq, Subtype.exists, exists_and_left,
            exists_eq_left]
          use ha_mem n, hax n
        · exact ha_lim.prodMk_nhds h_lim
      simp only [SetLike.mem_coe, mem_range_iff']
      use a₀

variable (T) in
/-- The kernel of a `E →ₗ.[𝕜] F` -/
def ker : Submodule 𝕜 E := T.toFun.ker.map T.domain.subtype

omit [CompleteSpace E]
theorem ker_eq_bot : T.ker = ⊥ ↔ ∀ x, T x = 0 → x = 0 := by
  unfold ker
  simp [← LinearMap.le_ker_iff_map, LinearMap.ker_eq_bot']

omit [CompleteSpace E]
theorem sub_mem_ker_iff {x y : T.domain} : ↑(x - y) ∈ T.ker ↔ T x = T y := by
  unfold ker
  simp_rw [Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
  norm_cast
  simp [LinearPMap.map_sub, sub_eq_zero]

omit [CompleteSpace E'] in
theorem IsSymmetric.ker_const_smul_im_eq_bot {T : E' →ₗ.[ℂ] E'} (hT : IsSymmetric T)
    {c : ℝ} (hc : c ≠ 0) :
    (((c • I) • LinearMap.id (R := ℂ) (M := E')) +ᵥ T).ker = ⊥ := by
  rw [LinearPMap.ker_eq_bot]
  intro ⟨x, hx⟩ hx'
  simp only [vadd_domain, coe_vadd, LinearMap.coe_comp, LinearMap.coe_smul,
    LinearMap.id_coe, Submodule.coe_subtype, Pi.add_apply, Function.comp_apply, Pi.smul_apply,
    id_eq] at hx'
  simp only [vadd_domain, Submodule.mk_eq_zero]
  have : (c • I) * inner ℂ x x = (c • I) * (- inner ℂ x x) := by
    have : T ⟨x, hx⟩ = -((c • I) • x) := by
      rw [← add_eq_zero_iff_eq_neg', hx']
    calc
      _ = inner ℂ (T ⟨x, hx⟩) x := by
        simp [this, inner_smul_left]
      _ = inner ℂ x (T ⟨x, hx⟩) := by
        exact hT ⟨x, hx⟩ ⟨x, hx⟩
      _ = _ := by
        simp [this, inner_smul_right]
  have : inner ℂ x x = 0 := by
    rw [← neg_eq_self]
    exact (mul_left_cancel₀ (by simp [hc]) this).symm
  grind [inner_self_eq_zero]

omit [CompleteSpace E'] in
@[simp]
theorem vadd_toFun {T : E' →ₗ.[ℂ] E'} {S : E' →ₗ[ℂ] E'} :
    (S +ᵥ T).toFun = S ∘ₗ T.domain.subtype + T.toFun := by
  ext x
  simp

theorem adjoint_id_vadd {T : E' →ₗ.[ℂ] E'} (hT : Dense (T.domain : Set E')) (c : ℂ) :
    (c • LinearMap.id (R := ℂ) (M := E') +ᵥ T)† =
    starRingEnd ℂ c • LinearMap.id (R := ℂ) (M := E') +ᵥ T† := by
  ext x hf hg
  · simp_rw [mem_adjoint_domain_iff, vadd_toFun, LinearMap.comp_add]
    simp_rw [LinearMap.coe_add]
    simp only [vadd_domain, LinearMap.coe_comp, coe_innerₛₗ_apply, LinearMap.coe_smul,
      LinearMap.id_coe, Submodule.coe_subtype, mem_adjoint_domain_iff]
    constructor
    · intro h
      have h' : Continuous (-(inner ℂ x ·) ∘ (c • id) ∘ (Subtype.val : T.domain → E')) := by
        fun_prop
      convert h'.add h
      simp
    · intro h
      fun_prop
  · simp only [vadd_domain, coe_vadd, LinearMap.coe_comp, LinearMap.coe_smul, LinearMap.id_coe,
    Submodule.coe_subtype, Pi.add_apply, Function.comp_apply, Pi.smul_apply, id_eq]
    apply adjoint_apply_eq
    · simp [hT]
    · intro ⟨y, hy⟩
      simpa [inner_add_left, inner_smul_left, inner_add_right, inner_smul_right] using
        adjoint_isFormalAdjoint hT ⟨x, hg⟩ ⟨y, hy⟩

theorem adjoint_vadd {T : E' →ₗ.[ℂ] E'} (S : E' →L[ℂ] E') :
    (S.toLinearMap +ᵥ T)† = S.adjoint.toLinearMap +ᵥ T† := by
  sorry

omit [CompleteSpace E'] in
theorem mem_range_orthogonal_iff {T : E' →ₗ.[ℂ] E'} {x : E'} :
    x ∈ T.toFun.rangeᗮ ↔ ∀ (y : T.domain), inner ℂ (T y) x = 0 := calc
  _ ↔ ∀ (u y : E') (hy : y ∈ T.domain), T ⟨y, hy⟩ = u → inner ℂ u x = 0 := by
    simp [Submodule.mem_orthogonal]
  _ ↔ ∀ (y : T.domain), inner ℂ (T y) x = 0 := by grind

theorem mem_adjoint_domain_of_mem_range_orthogonal {T : E' →ₗ.[ℂ] E'}
    {x : E'} (hx : x ∈ T.toFun.rangeᗮ) : x ∈ T†.domain := by
  apply mem_adjoint_domain_of_exists
  use 0
  grind [inner_zero_left, inner_eq_zero_symm, mem_range_orthogonal_iff]

theorem mem_range_orthogonal_iff' {T : E' →ₗ.[ℂ] E'}
    (hT' : Dense (T.domain : Set E')) {x : E'} (hx : x ∈ T†.domain) :
    x ∈ T.toFun.rangeᗮ ↔ T† ⟨x, hx⟩ = 0 := calc
  _ ↔ ∀ (u y : E') (hy : y ∈ T.domain), T ⟨y, hy⟩ = u → inner ℂ u x = 0 := by
    simp [Submodule.mem_orthogonal]
  _ ↔ ∀ (y : T.domain), inner ℂ (T y) x = 0 := by grind
  _ ↔ ∀ (y : T.domain), inner ℂ (y : E') (T† ⟨x, hx⟩) = 0 := by
    congrm (∀ y, ?_ = 0)
    exact (adjoint_isFormalAdjoint hT').symm y ⟨x, hx⟩
  _ ↔ ∀ (y : E') (hy : y ∈ T.domain), inner ℂ y (T† ⟨x, hx⟩) = 0 := by simp
  _ ↔ _ := by
    constructor
    · intro h
      apply hT'.eq_zero_of_inner_right ℂ h
    · intro h
      simp [h]

theorem ker_adjoint_eq_bot_iff {T : E' →ₗ.[ℂ] E'} (hT' : Dense (T.domain : Set E')) :
    (T†).ker = ⊥ ↔ Dense (T.toFun.range : Set E') := by
  rw [ker_eq_bot]
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  rw [Submodule.eq_bot_iff]
  simp only [Subtype.forall, Submodule.mk_eq_zero]
  congrm (∀ x, ?_)
  grind [mem_adjoint_domain_of_mem_range_orthogonal, mem_range_orthogonal_iff']

theorem foo'' {T : E' →ₗ.[ℂ] E'} (hT' : Dense (T.domain : Set E')) (c : ℝ) :
    (((c * I) • LinearMap.id (R := ℂ) (M := E')) +ᵥ T†).ker = ⊥ ↔
    Dense (LinearMap.range ((-(c * I) • LinearMap.id (R := ℂ) (M := E')) +ᵥ T).toFun : Set E') := by
  rw [← ker_adjoint_eq_bot_iff (by simp [hT'])]
  congrm (LinearPMap.ker ?_ = ⊥)
  rw [adjoint_id_vadd hT']
  simp

theorem foo {T : E' →ₗ.[ℂ] E'} (hT' : Dense (T.domain : Set E')) :
    ((I • LinearMap.id (R := ℂ) (M := E')) +ᵥ T†).ker = ⊥ ↔
    Dense (LinearMap.range ((-I • LinearMap.id (R := ℂ) (M := E')) +ᵥ T).toFun : Set E') := by
  have := foo'' hT' 1
  simp only [Complex.ofReal_one, one_mul] at this
  rw [this]
  congrm (Dense ?_)
  simp

theorem foo' {T : E' →ₗ.[ℂ] E'} (hT' : Dense (T.domain : Set E')) :
    (-(I • LinearMap.id (R := ℂ) (M := E')) +ᵥ T†).ker = ⊥ ↔
    Dense (LinearMap.range ((I • LinearMap.id (R := ℂ) (M := E')) +ᵥ T).toFun : Set E') := by
  convert! foo'' hT' (-1) using 4
  · simp
  · simp

theorem isSelfAdjoint_tfae {T : E' →ₗ.[ℂ] E'} (hT : T.IsSymmetric)
    (hT' : Dense (T.domain : Set E')) : List.TFAE [
    IsSelfAdjoint T,
    T.IsClosed ∧ ((I • LinearMap.id (R := ℂ) (M := E')) +ᵥ T†).ker = ⊥ ∧
      (-(I • LinearMap.id (R := ℂ) (M := E')) +ᵥ T†).ker = ⊥,
    LinearMap.range ((I • LinearMap.id (R := ℂ) (M := E')) +ᵥ T).toFun = ⊤ ∧
      LinearMap.range ((-I • LinearMap.id (R := ℂ) (M := E')) +ᵥ T).toFun = ⊤] := by
  tfae_have 1 → 2 := by
    intro hT
    have : T†.IsSymmetric := by
      rw [IsSelfAdjoint.adjoint_eq hT]
      apply IsSelfAdjoint.isSymmetric hT
    refine ⟨hT.isClosed, ?_, ?_⟩
    · simpa using IsSymmetric.ker_const_smul_im_eq_bot this (c := 1) (by simp)
    · simpa using IsSymmetric.ker_const_smul_im_eq_bot this (c := -1) (by simp)
  tfae_have 2 → 3 := by
    intro ⟨h₁, h₂, h₃⟩
    constructor
    · --apply?
      rwa [foo' hT', Submodule.dense_iff_topologicalClosure_eq_top,
        IsClosed.submodule_topologicalClosure_eq] at h₃
      convert! bar' hT h₁ (c := 1) (by simp) using 4
      simp
    · rwa [foo hT', Submodule.dense_iff_topologicalClosure_eq_top,
        IsClosed.submodule_topologicalClosure_eq] at h₂
      convert! bar' hT h₁ (c := -1) (by simp) using 4
      simp
  tfae_have 3 → 1 := by
    intro ⟨h₁, h₂⟩
    apply hT.isSelfAdjoint_of_le_domain hT'
    intro x hx
    -- there exists `y ∈ T.domain`, such that `(T - i) y = (T† - i) x`
    rw [LinearMap.range_eq_top] at h₂
    obtain ⟨⟨y, hy⟩, hy'⟩ := h₂ (-Complex.I • x + T† ⟨x, hx⟩)
    simp only [neg_smul, vadd_domain] at hy
    -- We claim that `x = y`
    convert hy
    have hy₁ : y ∈ T†.domain := (hT.le_adjoint hT').1 hy
    -- The crucial step is that `T† - i` is injective
    have h_ker : (-Complex.I • LinearMap.id (R := ℂ) (M := E') +ᵥ T†).ker = ⊥ := by
      rw [neg_smul, foo' hT', h₁]
      simp
    have hy' : (-Complex.I • LinearMap.id (R := ℂ) (M := E') +ᵥ T†) ⟨y, by simp [hy₁]⟩ =
        (-Complex.I • LinearMap.id (R := ℂ) (M := E') +ᵥ T†) ⟨x, hx⟩ := by
      have := (hT.le_adjoint hT').2 (x := ⟨y, hy⟩) (y := ⟨y, hy₁⟩) rfl
      simpa [this] using hy'
    rw [← LinearPMap.sub_mem_ker_iff, h_ker] at hy'
    simp only [vadd_domain, AddSubgroupClass.coe_sub, Submodule.mem_bot, sub_eq_zero] at hy'
    exact hy'.symm
  tfae_finish


end LinearPMap
