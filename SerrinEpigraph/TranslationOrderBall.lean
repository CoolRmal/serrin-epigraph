module

public import SerrinEpigraph.TranslatedPhaseConnected

/-!
# Global Sliding Rigidity from a Uniform Boundary Coarse Cone

This module formalizes sections DS8, DS9, DS10, DS11, and DS12 of
`docs/rigidity-proof/distance-and-sliding.md`:

Under `HasUniformBoundaryCoarseCone g e` (`‖e‖ = 1`), every positive-projection direction
`z : Space (m + 1)` with `0 < inner ℝ e z` belongs to `translationOrderSet (zeroExtension g u)`.
Consequently `u` and `g` satisfy `IsAffineOneDimensional g u`.

## Proof outline

1. **Parameter-space tangent ball (DS8)**:
   Suppose `0 < inner ℝ e b` and `b ∉ K := translationOrderSet (zeroExtension g u)`.
   By `eventually_ray_mem_interior_translationOrderSet` (`EventualTranslationOrder`), `T • e ∈ interior K`
   for sufficiently large `T > 0`. Applying `exists_positive_contact_tangent_ball`
   (`TranslationOrderSet`) yields `c, a₀ : Space (m + 1)` and `r > 0` with `a₀ ∈ frontier K`,
   `ball c r ⊆ K`, `dist a₀ c = r`, and `0 < inner ℝ e a₀`.
2. **Critical translation contact and zero-phase pin (DS9)**:
   `exists_critical_translation_contact` (`CriticalTranslationContact`) extracts a threshold
   `b_thr ∈ (0, 1)`, disallowed approaches `a_j → a₀` with `U (p_j + a_j) < U (p_j)` and
   `U (p_j + a_j) ≤ b_thr`, and a physical translation limit `V` of `U (p_j + ·)` satisfying
   `K ⊆ translationOrderSet V`, `V a₀ = V 0`, and `V 0 ≤ b_thr < 1`.
   Since `0 ≤ U (p_j + a_j) < U (p_j)`, `physical_translation_limit_mem_closure_positive`
   (`PhysicalTranslationClearing`) places `0 ∈ closure {x | 0 < V x}`.
   By `critical_contact_strict_and_zero` (`TranslatedPhaseConnected`), `{x | 0 < V x}` is
   preconnected, `∀ y, 0 < V y → V y < V (y + a₀)`, and `V 0 = V a₀ = 0`.
3. **Opposite phase balls and Hopf slope exclusion (DS10–DS11)**:
   `opposite_phase_balls_of_translation_orders` (`TranslationOrderSet`) produces a unit vector `ν`
   with `ball (r • ν) r ⊆ {x | 0 < V (x + a₀)}` and `ball (-(r • ν)) r ⊆ {x | V x = 0}`.
   Setting `V_tilde x := V (x + a₀)` (physical translation limit around `p_j + a₀`), every
   `x ∈ ball (r • ν) r` satisfies `V x < V_tilde x` (either `V x = 0 < V_tilde x` or `0 < V x`
   and `V x < V (x + a₀)`), which contradicts `false_of_opposite_phase_balls_and_positive_diff`
   (`ExteriorBallSlope`).
4. **Affine one-dimensionality (DS12)**:
   `isAffineOneDimensional_of_translation_order` (`DirectionalRigidity`) concludes
   `IsAffineOneDimensional g u`.
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology NNReal

namespace SerrinEpigraph

/-- Under a uniform boundary coarse cone along a unit direction `e`, every vector with strictly
positive projection onto `e` belongs to `translationOrderSet (zeroExtension g u)`. -/
theorem RigidityHypotheses.translation_order_of_uniformBoundaryCoarseCone
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e)
    {b : Space (m + 1)} (hb_in : 0 < inner ℝ e b) :
    b ∈ translationOrderSet (zeroExtension g u) := by
  let U := zeroExtension g u
  let K : Set (Space (m + 1)) := translationOrderSet U
  by_contra hb_not
  -- DS8: Extract an interior parameter ball `ball c r ⊆ K` tangent at `a₀ ∈ frontier K`
  have hfar := hr.eventually_ray_mem_interior_translationOrderSet h he hcone
  obtain ⟨c, a₀, r, hr_pos, ha₀_front, hball_K, htangent, ha₀_in⟩ :=
    exists_positive_contact_tangent_ball he hfar hb_not hb_in
  -- DS9.1: Extract a critical physical translation limit `V` below the stable well
  obtain ⟨b_thr, hb_thr, hcrit⟩ := hr.exists_critical_translation_contact h
  obtain ⟨a_seq, p_seq, V, _, _, hfail_bnd, hV, hV_val, hV_lim, hK_sub, heq_contact, hV0_le⟩ :=
    hcrit a₀ ha₀_front
  -- Positive centers `0 < U (p_seq j)` yield `0 ∈ closure {x | 0 < V x}`
  have hp_pos (j : ℕ) : 0 < U (p_seq j) :=
    (h.zeroExtension_nonneg (p_seq j + a_seq j)).trans_lt (hfail_bnd j).1
  have hcl0 : (0 : Space (m + 1)) ∈ closure {x | 0 < V x} :=
    hr.physical_translation_limit_mem_closure_positive h (fun x ↦ (hV_val x).1) hp_pos hV_lim
  -- `a₀ ∈ K ⊆ translationOrderSet V` and `V 0 ≤ b_thr < 1`
  have ha₀_K : a₀ ∈ K :=
    (isClosed_translationOrderSet h.zeroExtension_continuous).frontier_subset ha₀_front
  have ha₀_V : a₀ ∈ translationOrderSet V := hK_sub ha₀_K
  have hV0_lt1 : V 0 < 1 := hV0_le.trans_lt hb_thr.2
  -- DS9.2–DS9.3: Strict interior translation order on `{0 < V}` and `V 0 = V a₀ = 0`
  obtain ⟨hstrict_pos, hV0, hVa₀⟩ := hr.critical_contact_strict_and_zero h he hcone hV hV_val
    hV_lim hcl0 ha₀_V ha₀_in heq_contact hV0_lt1
  -- DS10: Opposite positive and zero phase balls at `0` for `V_tilde = V (· + a₀)` and `V`
  obtain ⟨ν, hν, hpos_ball, hzero_ball⟩ := opposite_phase_balls_of_translation_orders
    (fun x ↦ (hV_val x).1) hK_sub hcl0 hr_pos hVa₀ hball_K htangent
  let V_tilde : Space (m + 1) → ℝ := fun x ↦ V (x + a₀)
  let q_seq : ℕ → Space (m + 1) := fun j ↦ p_seq j + a₀
  have hVt_lim : ∀ Kc : Set (Space (m + 1)), IsCompact Kc →
      TendstoUniformlyOn (fun j x ↦ U (q_seq j + x)) V_tilde atTop Kc := by
    intro Kc hKc
    have hKa : IsCompact ((fun x ↦ x + a₀) '' Kc) :=
      hKc.image (by fun_prop)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hV_lim _ hKa) ε hε] with j hj x hx
    have hd := hj (x + a₀) ⟨x, hx, rfl⟩
    have heq_add : p_seq j + (x + a₀) = q_seq j + x := by dsimp only [q_seq]; abel
    rwa [heq_add] at hd
  have hVt0 : V_tilde 0 = 0 := by
    dsimp only [V_tilde]
    rw [zero_add]
    exact hVa₀
  have hstrict_ball (x : Space (m + 1)) (hx : x ∈ ball (r • ν) r) : V x < V_tilde x := by
    have hVt_pos : 0 < V_tilde x := hpos_ball hx
    by_cases hVx : 0 < V x
    · exact hstrict_pos x hVx
    · have hVx0 : V x = 0 := le_antisymm (not_lt.mp hVx) (hV_val x).1
      rwa [hVx0]
  -- DS11: Annular Hopf slope comparison rules out opposite phase balls with strict difference
  exact hr.false_of_opposite_phase_balls_and_positive_diff h hν hr_pos hV_lim hVt_lim hV0 hVt0
    hcl0 ha₀_V hzero_ball hpos_ball hstrict_ball

/-- **Global sliding rigidity from a uniform boundary coarse cone (DS1–DS12)**:
Any solution `(g, u)` satisfying `HasUniformBoundaryCoarseCone g e` along a unit direction `e`
satisfies `IsAffineOneDimensional g u`. -/
theorem RigidityHypotheses.isAffineOneDimensional_of_uniformBoundaryCoarseCone
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e) :
    IsAffineOneDimensional g u := by
  have he_ne : e ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at he
    exact zero_ne_one he
  apply h.isAffineOneDimensional_of_translation_order he_ne
  intro x z hz
  exact hr.translation_order_of_uniformBoundaryCoarseCone h he hcone hz x

end SerrinEpigraph
