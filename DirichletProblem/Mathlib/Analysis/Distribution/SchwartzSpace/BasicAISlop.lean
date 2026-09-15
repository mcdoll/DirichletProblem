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

private lemma norm_iteratedFDeriv_comp_smul (g : 𝓢(E, 𝕜)) (r : ℝ) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x => g (r⁻¹ • x)) x‖ =
      |r⁻¹| ^ i * ‖iteratedFDeriv ℝ i g (r⁻¹ • x)‖ := by sorry

private lemma schwartz_mvt_bound (g : 𝓢(E, 𝕜)) (y : E) :
    ‖g y - g 0‖ ≤ (SchwartzMap.seminorm 𝕜 0 1 g) * ‖y‖ := by
  have h_mvt : ∀ z : E, ‖fderiv ℝ g z‖ ≤ SchwartzMap.seminorm 𝕜 0 1 g := by
    intro z
    have h_diff : ‖iteratedFDeriv ℝ 1 g z‖ ≤ (SchwartzMap.seminorm 𝕜 0 1 g) := by
      exact norm_iteratedFDeriv_le_seminorm 𝕜 g 1 z;
    convert h_diff using 1;
    exact Eq.symm (norm_iteratedFDeriv_one ⇑g);
  --grw [← h_mvt]
  --apply?
  have := @Convex.norm_image_sub_le_of_norm_fderiv_le;
  specialize this ( show ∀ x ∈ Set.univ, DifferentiableAt ℝ g x from fun x _ => g.differentiableAt ) ( show ∀ x ∈ Set.univ, ‖fderiv ℝ g x‖ ≤ SchwartzMap.seminorm 𝕜 0 1 g from fun x _ => h_mvt x ) ( convex_univ ) ( Set.mem_univ 0 ) ( Set.mem_univ y ) ; simp_all +decide [ norm_sub_rev ] ;

/-
Helper: for i ≥ 1, iteratedFDeriv of (g ∘ scale - 1) equals iteratedFDeriv of (g ∘ scale)
-/
private lemma iteratedFDeriv_sub_const (g : 𝓢(E, 𝕜)) (r : ℝ) (i : ℕ) (hi : 1 ≤ i) (x : E) :
    iteratedFDeriv ℝ i (fun x => g (r⁻¹ • x) - 1) x =
    iteratedFDeriv ℝ i (fun x => g (r⁻¹ • x)) x := by
  induction i generalizing x with
  | zero =>
    ext x
    simp at hi
  | succ n hn =>
    sorry
  · ext; simp [iteratedFDeriv_succ_const];
    rw [ fderiv_sub_const ];
  · simp +decide only [iteratedFDeriv_succ_eq_comp_left];
    rw [ show iteratedFDeriv ℝ i ( fun x => g ( r⁻¹ • x ) - 1 ) = iteratedFDeriv ℝ i ( fun x => g ( r⁻¹ • x ) ) from funext ih ]

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
            (SchwartzMap.seminorm 𝕜 k (n - (i + 1)) f)) := by sorry

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
