module

public import SerrinEpigraph.BallLowerBound
public import SerrinEpigraph.StableWellTranslation

/-!
# Eventual translation orders from a uniform boundary coarse cone

From uniform coarse positive and negative cones at all boundary points of the
epigraph (DS1.1--DS1.2), large positive-projection translations carry the entire
positive phase uniformly deep into the stable well (DS2). Combining this uniform
depth with the unbounded-domain maximum principle near the stable equilibrium yields
comparison for all sufficiently far translations in every strict positive cone,
interior points of the translation order set along the normal ray, and eventual
translation order in every positive-projection direction (DS3, DS8).
-/

public section

noncomputable section

open Set Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Uniform coarse positive and negative phase cones at every boundary point of the epigraph. -/
@[expose] def HasUniformBoundaryCoarseCone {m : ℕ} (g : Space m → ℝ)
    (e : Space (m + 1)) : Prop :=
  ∀ η ∈ Ioo (0 : ℝ) 1, ∃ R_cone : ℝ, 0 < R_cone ∧
    ∀ p ∈ frontier (epigraph g), ∀ w : Space (m + 1), R_cone ≤ ‖w‖ →
      (η * ‖w‖ ≤ inner ℝ e w → p + w ∈ epigraph g) ∧
      (inner ℝ e w ≤ -η * ‖w‖ → p + w ∉ epigraph g)

/-- Starting at any positive-phase point and moving backwards along a unit vector in a strict
positive cone eventually exits the positive phase; the first exit lies on the frontier. -/
theorem exists_frontier_exit_along_cone_ray {m : ℕ} {g : Space m → ℝ}
    (hg : Continuous g) {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hcone : HasUniformBoundaryCoarseCone g e) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    {ξ : Space (m + 1)} (hξ : ‖ξ‖ = 1) (hinner : α ≤ inner ℝ e ξ)
    {x : Space (m + 1)} (hx : x ∈ epigraph g) :
    ∃ s_star : ℝ, 0 ≤ s_star ∧ x - s_star • ξ ∈ frontier (epigraph g) ∧
      x = (x - s_star • ξ) + s_star • ξ := by
  have hη : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  obtain ⟨R_cone, hR_pos, hR_cone⟩ := hcone (α / 2) hη
  let p₀ : Space (m + 1) := point 0 (g 0)
  have hp₀ : p₀ ∈ frontier (epigraph g) := point_mem_frontier_epigraph hg 0
  let S : Set ℝ := {s : ℝ | 0 ≤ s ∧ x - s • ξ ∉ epigraph g}
  have hS_closed : IsClosed S := by
    have hcont : Continuous (fun s : ℝ ↦ x - s • ξ) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    exact isClosed_Ici.inter ((isOpen_epigraph hg).isClosed_compl.preimage hcont)
  have hS_bdd : BddBelow S := ⟨0, fun _ hs ↦ hs.1⟩
  have hS_nonempty : S.Nonempty := by
    let v : Space (m + 1) := x - p₀
    let s₁ : ℝ := R_cone + (4 / α) * (‖v‖ + 1)
    have hα_pos : 0 < α := hα.1
    have hdiv_gt_one : 1 < 4 / α := (one_lt_div hα_pos).mpr (by linarith [hα.2])
    have hs₁_gt : R_cone + ‖v‖ < s₁ := by
      dsimp only [s₁]
      nlinarith [norm_nonneg v]
    have hs₁_pos : 0 < s₁ := by linarith [norm_nonneg v]
    let w : Space (m + 1) := v - s₁ • ξ
    have hw_norm_ge : R_cone ≤ ‖w‖ := by
      have htri : ‖s₁ • ξ‖ ≤ ‖w‖ + ‖v‖ := by
        have heq : s₁ • ξ = v - w := by dsimp only [w]; abel
        rw [heq, norm_sub_rev]
        exact norm_sub_le w v
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs₁_pos, hξ, mul_one] at htri
      linarith
    have hw_norm_le : ‖w‖ ≤ ‖v‖ + s₁ := by
      calc
        ‖w‖ ≤ ‖v‖ + ‖s₁ • ξ‖ := norm_sub_le v (s₁ • ξ)
        _ = ‖v‖ + s₁ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs₁_pos, hξ, mul_one]
    have hw_inner : inner ℝ e w ≤ -(α / 2) * ‖w‖ := by
      have hv_inner : inner ℝ e v ≤ ‖v‖ := by
        simpa only [he, one_mul] using real_inner_le_norm e v
      have hs_inner : α * s₁ ≤ s₁ * inner ℝ e ξ := by nlinarith
      have hprod : (α / 2) * s₁ = (α / 2) * R_cone + 2 * (‖v‖ + 1) := by
        dsimp only [s₁]
        field_simp
        ring
      have hlin : ‖v‖ - α * s₁ ≤ -(α / 2) * (‖v‖ + s₁) := by
        nlinarith [norm_nonneg v, hα.1, hα.2]
      have hneg_mono : -(α / 2) * (‖v‖ + s₁) ≤ -(α / 2) * ‖w‖ := by
        nlinarith [hα.1]
      calc
        inner ℝ e w = inner ℝ e v - s₁ * inner ℝ e ξ := by
          dsimp only [w]
          rw [inner_sub_right, real_inner_smul_right]
        _ ≤ ‖v‖ - α * s₁ := by linarith
        _ ≤ -(α / 2) * (‖v‖ + s₁) := hlin
        _ ≤ -(α / 2) * ‖w‖ := hneg_mono
    have hnotMem := (hR_cone p₀ hp₀ w hw_norm_ge).2 hw_inner
    have hp₀w : p₀ + w = x - s₁ • ξ := by dsimp only [w, v]; abel
    rw [hp₀w] at hnotMem
    exact ⟨s₁, hs₁_pos.le, hnotMem⟩
  let s_star : ℝ := sInf S
  have hs_mem : s_star ∈ S := hS_closed.csInf_mem hS_nonempty hS_bdd
  have hs_pos : 0 < s_star := by
    apply lt_of_le_of_ne hs_mem.1
    intro hzero
    apply hs_mem.2
    simpa only [← hzero, zero_smul, sub_zero] using hx
  have hcl : x - s_star • ξ ∈ closure (epigraph g) := by
    have hmap : MapsTo (fun t : ℝ ↦ x - t • ξ) (Ioo 0 s_star) (epigraph g) := by
      intro t ht
      by_contra hnot
      have htS : t ∈ S := ⟨ht.1.le, hnot⟩
      exact not_le_of_gt ht.2 (csInf_le hS_bdd htS)
    have hcont : Continuous (fun t : ℝ ↦ x - t • ξ) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    apply hmap.closure hcont
    rw [closure_Ioo hs_pos.ne]
    exact ⟨hs_pos.le, le_rfl⟩
  have hfront : x - s_star • ξ ∈ frontier (epigraph g) := by
    rw [frontier, (isOpen_epigraph hg).interior_eq]
    exact ⟨hcl, hs_mem.2⟩
  exact ⟨s_star, hs_mem.1, hfront, (sub_add_cancel x (s_star • ξ)).symm⟩

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Every sufficiently large translation inside a strict cone around `e` carries the entire
positive phase to points with a proportional interior ball and value uniformly close to one. -/
theorem RigidityHypotheses.uniform_stable_well_of_coarse_cone
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e)
    {α b : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ z : Space (m + 1), L₀ ≤ ‖z‖ → α * ‖z‖ ≤ inner ℝ e z →
      ∀ x ∈ epigraph g,
        closedBall (x + z) ((α / 8) * ‖z‖) ⊆ epigraph g ∧ b < u (x + z) := by
  have hη : α / 4 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  obtain ⟨R_cone, hR_pos, hR_cone⟩ := hcone (α / 4) hη
  let a : ℝ := (b + 1) / 2
  have ha_mem : a ∈ Ioo (0 : ℝ) 1 := by
    dsimp only [a]
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hfa : 0 < f a := hr.reaction_pos a ha_mem
  let q : ℝ := f a / a
  have hq : 0 < q := div_pos hfa ha_mem.1
  have hsq_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  let N : ℝ := (Module.finrank ℝ (Space (m + 1)) : ℝ) + 2
  have hN_pos : 0 < N := by dsimp only [N]; positivity
  let L₀ : ℝ := max (2 * R_cone) ((8 / α) * (N / Real.sqrt q + 1))
  have hL₀_pos : 0 < L₀ := lt_max_of_lt_left (by positivity)
  refine ⟨L₀, hL₀_pos, fun z hzL hze x hx ↦ ?_⟩
  let L : ℝ := ‖z‖
  have hL_pos : 0 < L := hL₀_pos.trans_le hzL
  let ξ : Space (m + 1) := L⁻¹ • z
  have hξ : ‖ξ‖ = 1 := by
    simp only [ξ, L, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hL_pos.ne']
  have hξ_inner : α ≤ inner ℝ e ξ := by
    rw [show ξ = L⁻¹ • z from rfl, real_inner_smul_right]
    exact (le_inv_mul_iff₀ hL_pos).mpr (by simpa only [mul_comm] using hze)
  obtain ⟨s_star, hs_nonneg, hp_front, hx_eq⟩ :=
    exists_frontier_exit_along_cone_ray h.graph_contDiff.continuous he hcone hα hξ hξ_inner hx
  let p : Space (m + 1) := x - s_star • ξ
  have hLξ : L • ξ = z := by
    simp only [ξ, smul_smul, mul_inv_cancel₀ hL_pos.ne', one_smul]
  have hxz_eq : x + z = p + (s_star + L) • ξ := by
    calc
      x + z = (p + s_star • ξ) + L • ξ := by rw [← hx_eq, hLξ]
      _ = p + (s_star + L) • ξ := by rw [add_smul, add_assoc]
  have hball : closedBall (x + z) ((α / 8) * L) ⊆ epigraph g := by
    intro y hy
    let v : Space (m + 1) := y - (x + z)
    have hv : ‖v‖ ≤ (α / 8) * L := by
      simpa only [v, mem_closedBall, dist_eq_norm] using hy
    let M : ℝ := s_star + L
    have hL_le_M : L ≤ M := by dsimp only [M]; linarith
    have hM_pos : 0 < M := hL_pos.trans_le hL_le_M
    have h2R_le_M : 2 * R_cone ≤ M := (le_max_left _ _).trans (hzL.trans hL_le_M)
    have hv_le_αM : ‖v‖ ≤ (α / 8) * M :=
      hv.trans (mul_le_mul_of_nonneg_left hL_le_M (by linarith [hα.1]))
    have hv_le_M : ‖v‖ ≤ (1 / 8) * M := by nlinarith [hα.2, hM_pos]
    let w : Space (m + 1) := M • ξ + v
    have hw_norm_ge : R_cone ≤ ‖w‖ := by
      have htri : ‖M • ξ‖ ≤ ‖w‖ + ‖v‖ := by
        have heq : M • ξ = w - v := by dsimp only [w]; abel
        rw [heq]
        exact norm_sub_le w v
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hM_pos, hξ, mul_one] at htri
      linarith
    have hw_norm_le : ‖w‖ ≤ M + ‖v‖ := by
      calc
        ‖w‖ ≤ ‖M • ξ‖ + ‖v‖ := norm_add_le (M • ξ) v
        _ = M + ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hM_pos, hξ, mul_one]
    have hw_inner : (α / 4) * ‖w‖ ≤ inner ℝ e w := by
      have hv_inner : -‖v‖ ≤ inner ℝ e v := by
        have hneg : inner ℝ e (-v) ≤ ‖v‖ := by
          simpa only [he, one_mul, norm_neg] using real_inner_le_norm e (-v)
        rw [inner_neg_right] at hneg
        linarith
      have hM_inner : M * α ≤ M * inner ℝ e ξ :=
        mul_le_mul_of_nonneg_left hξ_inner hM_pos.le
      have hrew : inner ℝ e w = M * inner ℝ e ξ + inner ℝ e v := by
        dsimp only [w]
        rw [inner_add_right, real_inner_smul_right]
      rw [hrew]
      nlinarith [hα.1, hM_pos]
    have hmem := (hR_cone p hp_front w hw_norm_ge).1 hw_inner
    have hpw : p + w = y := by
      dsimp only [w, v, M]
      rw [← add_assoc, ← hxz_eq]
      abel
    rwa [hpw] at hmem
  refine ⟨hball, ?_⟩
  let R : ℝ := (α / 8) * L
  have hR_ge : N / Real.sqrt q + 1 ≤ R := by
    have hL_ge : (8 / α) * (N / Real.sqrt q + 1) ≤ L := (le_max_right _ _).trans hzL
    have hmul := mul_le_mul_of_nonneg_left hL_ge (by linarith [hα.1] : 0 ≤ α / 8)
    have hcancel : (α / 8) * ((8 / α) * (N / Real.sqrt q + 1)) = N / Real.sqrt q + 1 := by
      have hα_ne : α ≠ 0 := hα.1.ne'
      field_simp
    rwa [hcancel] at hmul
  have hdiv_pos : 0 < N / Real.sqrt q := div_pos hN_pos hsq_pos
  have hR_pos : 0 < R := by linarith
  have hN_lt : N < R * Real.sqrt q :=
    (div_lt_iff₀ hsq_pos).mp (by linarith)
  have hsq_lt : N ^ 2 < R ^ 2 * q := by
    have h1 : N ^ 2 < R ^ 2 * (Real.sqrt q) ^ 2 := by nlinarith
    rwa [Real.sq_sqrt hq.le] at h1
  have hgap : N ^ 2 / R ^ 2 < f a / a :=
    (div_lt_iff₀ (sq_pos_of_pos hR_pos)).mpr (by simpa only [q, mul_comm] using hsq_lt)
  have hau : a ≤ u (x + z) := h.solution_ge_at_ball_center hR_pos ha_mem.1 hball hgap
  have hb_lt_a : b < a := by dsimp only [a]; linarith [hb.2]
  exact hb_lt_a.trans_le hau

/-- Every sufficiently far strict positive cone around `e` is contained in the full-space
translation order set of the zero-extended solution. -/
theorem RigidityHypotheses.eventual_cone_subset_translationOrderSet
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ L₀ : ℝ, 0 < L₀ ∧
      {z : Space (m + 1) | L₀ ≤ ‖z‖ ∧ α * ‖z‖ ≤ inner ℝ e z} ⊆
        translationOrderSet (zeroExtension g u) := by
  obtain ⟨b, c, hb, hc, hdiff⟩ := hr.exists_stable_reaction_difference h
  obtain ⟨L₀, hL₀, hwell_unif⟩ := hr.uniform_stable_well_of_coarse_cone h he hcone hα hb
  refine ⟨L₀, hL₀, fun z hz ↦ ?_⟩
  apply hr.translation_order_of_failures_in_stable_well h hb.1 hc hdiff z
  intro x hfail
  have hx_pos : 0 < zeroExtension g u x :=
    (h.zeroExtension_nonneg (x + z)).trans_lt hfail
  have hx_mem : x ∈ epigraph g := (h.zeroExtension_pos_iff x).mp hx_pos
  obtain ⟨hball, hub⟩ := hwell_unif z hz.1 hz.2 x hx_mem
  have hxz_mem : x + z ∈ epigraph g :=
    hball (mem_closedBall_self (mul_nonneg (by linarith [hα.1]) (norm_nonneg z)))
  rwa [zeroExtension_of_mem hxz_mem]

/-- Sufficiently far points along the positive normal ray lie in the interior of the
translation order set. -/
theorem RigidityHypotheses.eventually_ray_mem_interior_translationOrderSet
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e) :
    ∀ᶠ T : ℝ in atTop, T • e ∈ interior (translationOrderSet (zeroExtension g u)) := by
  obtain ⟨L₀, hL₀, hsub⟩ :=
    hr.eventual_cone_subset_translationOrderSet h he hcone (α := 1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop (2 * L₀)] with T hT
  have hT_pos : 0 < T := by linarith
  have hball_cone : ball (T • e) (T / 4) ⊆
      {z : Space (m + 1) | L₀ ≤ ‖z‖ ∧ (1 / 2) * ‖z‖ ≤ inner ℝ e z} := by
    intro z hz
    let v : Space (m + 1) := z - T • e
    have hv : ‖v‖ < T / 4 := by simpa only [v, mem_ball, dist_eq_norm] using hz
    have hTe_norm : ‖T • e‖ = T := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT_pos, he, mul_one]
    have hz_norm_ge : L₀ ≤ ‖z‖ := by
      have htri : ‖T • e‖ ≤ ‖z‖ + ‖v‖ := by
        have heq : T • e = z - v := by dsimp only [v]; abel
        rw [heq]
        exact norm_sub_le z v
      linarith
    have hz_norm_le : ‖z‖ ≤ T + ‖v‖ := by
      have heq : z = T • e + v := by dsimp only [v]; abel
      rw [heq]
      exact (norm_add_le (T • e) v).trans_eq (by rw [hTe_norm])
    have hz_inner : (1 / 2) * ‖z‖ ≤ inner ℝ e z := by
      have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
      have hv_inner : -‖v‖ ≤ inner ℝ e v := by
        have hneg : inner ℝ e (-v) ≤ ‖v‖ := by
          simpa only [he, one_mul, norm_neg] using real_inner_le_norm e (-v)
        rw [inner_neg_right] at hneg
        linarith
      have hrew : inner ℝ e z = T + inner ℝ e v := by
        have heq : z = T • e + v := by dsimp only [v]; abel
        rw [heq, inner_add_right, real_inner_smul_right, hee, mul_one]
      linarith
    exact ⟨hz_norm_ge, hz_inner⟩
  exact interior_maximal (hball_cone.trans hsub) isOpen_ball
    (mem_ball_self (by linarith))

/-- Every vector with strictly positive projection onto `e` eventually enters the
translation order set upon positive scaling. -/
theorem RigidityHypotheses.eventually_smul_mem_translationOrderSet
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hcone : HasUniformBoundaryCoarseCone g e)
    {z : Space (m + 1)} (hz : 0 < inner ℝ e z) :
    ∀ᶠ t : ℝ in atTop, t • z ∈ translationOrderSet (zeroExtension g u) := by
  have hz_le : inner ℝ e z ≤ ‖z‖ := by
    simpa only [he, one_mul] using real_inner_le_norm e z
  have hz_norm : 0 < ‖z‖ := hz.trans_le hz_le
  let α : ℝ := inner ℝ e z / (2 * ‖z‖)
  have hα : α ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hz (by positivity), (div_lt_one (by positivity)).mpr (by linarith)⟩
  obtain ⟨L₀, hL₀, hsub⟩ := hr.eventual_cone_subset_translationOrderSet h he hcone hα
  filter_upwards [eventually_ge_atTop (L₀ / ‖z‖)] with t ht
  have ht_pos : 0 < t := (div_pos hL₀ hz_norm).trans_le ht
  have htz_norm : ‖t • z‖ = t * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
  apply hsub
  refine ⟨?_, ?_⟩
  · rw [htz_norm]
    exact (div_le_iff₀ hz_norm).mp ht
  · rw [htz_norm, real_inner_smul_right]
    have hprod : α * (t * ‖z‖) = t * inner ℝ e z / 2 := by
      dsimp only [α]
      have hne : ‖z‖ ≠ 0 := hz_norm.ne'
      field_simp
    rw [hprod]
    nlinarith

end SerrinEpigraph
