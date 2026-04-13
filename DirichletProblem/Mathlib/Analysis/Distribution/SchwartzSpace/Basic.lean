module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

variable {ι 𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

open SchwartzMap
open scoped Topology

variable {f : 𝓢(E, F)} {g : 𝓢(E, 𝕜)} {c : 𝕜}

theorem foo {g : 𝓢(E, 𝕜)} (hg : g 0 = 1) :
    Filter.Tendsto (fun (r : ℝ) ↦ smulLeftCLM F (g <| r⁻¹ • · ) f) Filter.atTop (𝓝 f) := by
  rw [(_root_.schwartz_withSeminorms ℝ E F).tendsto_nhds_atTop]
  intro ⟨k, n⟩ ε hε
  /-use 1
  intro r hr
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply seminorm_le_bound _ _ _ _ (half_pos hε).le
  intro x-/
  sorry

-- Helper: pointwise evaluation of smulLeftCLM
private lemma smulLeftCLM_comp_apply (g : 𝓢(E, 𝕜)) (r : ℝ) (f : 𝓢(E, F)) (x : E) :
    smulLeftCLM F (fun x => g (r⁻¹ • x)) f x = g (r⁻¹ • x) • f x := by
  apply smulLeftCLM_apply_apply (by fun_prop)

-- Helper: pointwise evaluation of the difference
private lemma diff_apply (g : 𝓢(E, 𝕜)) (r : ℝ) (f : 𝓢(E, F)) (x : E) :
    ((smulLeftCLM F (fun x => g (r⁻¹ • x))) f - f) x = (g (r⁻¹ • x) - 1) • f x := by
  simp [sub_apply, smulLeftCLM_comp_apply, sub_smul]

private lemma norm_iteratedFDeriv_comp_smul (g : 𝓢(E, 𝕜)) (r : ℝ) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x => g (r⁻¹ • x)) x‖ =
      |r⁻¹| ^ i * ‖iteratedFDeriv ℝ i g (r⁻¹ • x)‖ := by
  rw [iteratedFDeriv_comp_const_smul _ (g.smooth _)]
  simp [norm_smul]

private lemma schwartz_mvt_bound (g : 𝓢(E, 𝕜)) (y : E) :
    ‖g y - g 0‖ ≤ (SchwartzMap.seminorm 𝕜 0 1 g) * ‖y‖ := by
  suffices h : ‖g y - g 0‖ ≤ (SchwartzMap.seminorm 𝕜 0 1 g) * ‖y - 0‖ from by
    simpa using h
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (by fun_prop) _ convex_univ
    (Set.mem_univ _) (Set.mem_univ _)
  intro x _
  rw [← norm_iteratedFDeriv_one]
  apply norm_iteratedFDeriv_le_seminorm

/-
Helper: for i ≥ 1, iteratedFDeriv of (g ∘ scale - 1) equals iteratedFDeriv of (g ∘ scale)
-/
private lemma iteratedFDeriv_sub_const (g : 𝓢(E, 𝕜)) (r : ℝ) (i : ℕ) (hi : 1 ≤ i) (x : E) :
    iteratedFDeriv ℝ i (fun x => g (r⁻¹ • x) - 1) x =
    iteratedFDeriv ℝ i (fun x => g (r⁻¹ • x)) x := by
  rw [fun_iteratedFDeriv_sub (by apply (g.smooth i).comp (contDiff_id.const_smul _)) (by fun_prop)]
  simp [iteratedFDeriv_const_of_ne (by apply Nat.ne_zero_iff_zero_lt.mpr hi)]

/-
The main seminorm bound
-/
private lemma seminorm_smulLeft_sub_le (g : 𝓢(E, 𝕜)) (hg : g 0 = 1)
    (f : 𝓢(E, F)) (k n : ℕ) (r : ℝ) (hr : 1 ≤ |r|) :
    (SchwartzMap.seminorm 𝕜 k n) ((smulLeftCLM F (fun x => g (r⁻¹ • x))) f - f) ≤
      |r⁻¹| * ((SchwartzMap.seminorm 𝕜 0 1 g) * (SchwartzMap.seminorm 𝕜 (k + 1) n f) +
        ∑ i ∈ Finset.range n,
          ↑(n.choose (i + 1)) *
            (SchwartzMap.seminorm 𝕜 0 (i + 1) g) *
            (SchwartzMap.seminorm 𝕜 k (n - (i + 1)) f)) := by
  -- For each x, need to show: ‖x‖^k * ‖iteratedFDeriv ℝ n (⇑((smulLeftCLM F (fun x => g (r⁻¹ • x))) f - f)) x‖ ≤ RHS
  have h_bound : ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑((smulLeftCLM F (fun x => g (r⁻¹ • x))) f - f)) x‖ ≤
    |r⁻¹| * ((SchwartzMap.seminorm 𝕜 0 1 g) * ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n f x‖ +
    ∑ i ∈ Finset.range n, (Nat.choose n (i + 1) : ℝ) * (SchwartzMap.seminorm 𝕜 0 (i + 1) g) * ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - (i + 1)) f x‖) := by
      intro x
      have h_apply_norm_iteratedFDeriv_smul_le : ‖iteratedFDeriv ℝ n (fun y => (g (r⁻¹ • y) - 1) • f y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => g (r⁻¹ • y) - 1) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
          have h_norm_iteratedFDeriv_smul_le : ContDiff ℝ n (fun y => (g (r⁻¹ • y) - 1)) ∧ ContDiff ℝ n f := by
            refine' ⟨ _, _ ⟩;
            · have h_cont_diff : ContDiff ℝ n g := by
                exact g.smooth n;
              exact ContDiff.sub ( h_cont_diff.comp ( contDiff_const.smul contDiff_id ) ) contDiff_const;
            · exact f.smooth n;
          convert norm_iteratedFDeriv_smul_le h_norm_iteratedFDeriv_smul_le.1 h_norm_iteratedFDeriv_smul_le.2 x _;
          exact le_rfl;
      -- Apply the bounds for each term in the sum.
      have h_apply_bounds : ∀ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i (fun y => g (r⁻¹ • y) - 1) x‖ ≤ if i = 0 then (SchwartzMap.seminorm 𝕜 0 1 g) * |r⁻¹| * ‖x‖ else |r⁻¹| * (SchwartzMap.seminorm 𝕜 0 i g) := by
        intro i hi; split_ifs <;> simp_all +decide [ norm_smul, mul_assoc ] ;
        · have := schwartz_mvt_bound g ( r⁻¹ • x ) ; simp_all +decide [ norm_smul, mul_assoc, mul_comm, mul_left_comm ] ;
          aesop;
        · rw [ iteratedFDeriv_sub_const ];
          · rw [norm_iteratedFDeriv_comp_smul g r i x]
            --refine' le_trans ( norm_iteratedFDeriv_comp_smul_le g r i x ) _;
            rw [ abs_inv ];
            exact le_trans ( mul_le_mul_of_nonneg_left ( norm_iteratedFDeriv_le_seminorm _ g i _ ) ( by positivity ) ) ( mul_le_mul_of_nonneg_right ( pow_le_of_le_one ( by positivity ) ( inv_le_one_of_one_le₀ hr ) ( by positivity ) ) ( by positivity ) );
          · exact Nat.pos_of_ne_zero ‹_›;
      convert mul_le_mul_of_nonneg_left ( h_apply_norm_iteratedFDeriv_smul_le.trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_apply_bounds i hi ) ( Nat.cast_nonneg _ ) ) ( norm_nonneg _ ) ) ) ( by positivity : 0 ≤ ‖x‖ ^ k ) using 1;
      · congr
        --congr! 2;
        congr! 2;
        (exact diff_apply g r f _);
      · simp +decide [ Finset.sum_range_succ', pow_succ, mul_assoc, mul_comm, mul_left_comm];
        simp +decide only [mul_add, Finset.mul_sum _ _ _, mul_left_comm] ; ring;
  -- Apply the bound to each term in the sum.
  have h_sum_bound : ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑((smulLeftCLM F (fun x => g (r⁻¹ • x))) f - f)) x‖ ≤
    |r⁻¹| * ((SchwartzMap.seminorm 𝕜 0 1 g) * (SchwartzMap.seminorm 𝕜 (k + 1) n f) +
    ∑ i ∈ Finset.range n, (Nat.choose n (i + 1) : ℝ) * (SchwartzMap.seminorm 𝕜 0 (i + 1) g) * (SchwartzMap.seminorm 𝕜 k (n - (i + 1)) f)) := by
      intro x
      specialize h_bound x
      have h_term_bound : ∀ i ∈ Finset.range n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - (i + 1)) f x‖ ≤ (SchwartzMap.seminorm 𝕜 k (n - (i + 1)) f) := by
        grind +suggestions;
      refine' le_trans h_bound ( mul_le_mul_of_nonneg_left ( add_le_add _ _ ) ( by positivity ) );
      · rw [ mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( SchwartzMap.le_seminorm .. ) ( by positivity );
      · exact Finset.sum_le_sum fun i hi => by simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left ( h_term_bound i hi ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) ;
  convert SchwartzMap.seminorm_le_bound 𝕜 k n _ _ h_sum_bound using 1;
  exact mul_nonneg ( abs_nonneg _ ) ( add_nonneg ( mul_nonneg ( by positivity ) ( by positivity ) ) ( Finset.sum_nonneg fun _ _ => mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) ( by positivity ) ) )


theorem foo' {g : 𝓢(E, 𝕜)} (hg : g 0 = 1) :
    Filter.Tendsto (fun (r : ℝ) ↦ smulLeftCLM F (g <| r⁻¹ • · ) f) Filter.atTop (𝓝 f) := by
  rw [(_root_.schwartz_withSeminorms 𝕜 E F).tendsto_nhds_atTop]
  intro ⟨k, n⟩ ε hε
  -- The constant C depends on f, g, k, n
  set C := (SchwartzMap.seminorm 𝕜 0 1 g) * (SchwartzMap.seminorm 𝕜 (k + 1) n f) +
    ∑ i ∈ Finset.range n,
      (n.choose (i + 1)) *
        (SchwartzMap.seminorm 𝕜 0 (i + 1) g) *
        (SchwartzMap.seminorm 𝕜 k (n - (i + 1)) f)
  use max 1 (C / ε + 1)
  intro r hr
  have hr1 : 1 ≤ r := le_of_max_le_left hr
  have hr_pos : 0 < r := by positivity
  have hr' : C / ε < r := calc
    _ < C / ε + 1 := by simp
    _ ≤ r := le_of_max_le_right hr
  have hr_abs : 1 ≤ |r| := by rwa [abs_of_pos hr_pos]
  calc (schwartzSeminormFamily 𝕜 E F (k, n)) ((smulLeftCLM F fun x_1 => g (r⁻¹ • x_1)) f - f)
      _ ≤ |r⁻¹| * C := seminorm_smulLeft_sub_le g hg f k n r hr_abs
      _ < ε := by
        simp [abs_of_pos hr_pos]
        field_simp at hr' ⊢
        exact hr'
