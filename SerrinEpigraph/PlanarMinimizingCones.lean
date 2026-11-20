module

public import SerrinEpigraph.PlanarConeChord

/-!
# Minimizing cones in the plane are half-planes (`SimonsHyp 2`)

Let `T ⊆ ℝ²` be a minimizing cone whose boundary points other than the vertex are `C¹` boundary
points. Then `T` is a.e. a half-plane (`Planar.simonsHyp_two_planar`).

1. **Local structure** (`Planar.local_halfplane`). At a nonzero boundary point `x` the `C¹`
   defining function `F` vanishes on the ray through `x` (the boundary is a cone), so `DF(x) x = 0`
   and `DF(x) ν > 0` for a unit normal `ν ⊥ x`; the mean value theorem along the normal lines
   through the ray shows that near `x` the cone is a.e. the half-plane `{⟪ν, ·⟫ > 0}`. In pointwise
   form (`Planar.LocalHalfplanes`): near `x`, points with `⟪ν, ·⟫ > 0` are measure-theoretic
   interior points and points with `⟪ν, ·⟫ < 0` are exterior points.
2. **No acute sectors** (`Planar.no_boundary_on_side`). Let `a` be a unit boundary point with
   normal `n`. The slopes `σ` of the boundary directions `n + σ a` are bounded above; if there were
   any, the largest one `σ*` would give a direction `c = n + σ* a` such that the open sector
   between `a` and `c` (of angle `< π`) is free of boundary points, hence full. The local
   structure at `a` and `c` then shows that the cone coincides, on a slightly wider sector, with
   the sector itself. In the frame of the bisector this is exactly the configuration excluded by
   the chord argument `Planar.chord_false` (`Planar.chord_false_frame`).
3. **Conclusion** (`Planar.ae_eq_halfplane`). Applying 2. to `T` and to `Tᶜ`, both open
   half-planes bounded by `ℝ a` are free of boundary points, so the cone is a.e. the half-plane
   on the side of the normal.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal

namespace SerrinEpigraph

namespace Planar

/-! ### 1. Planar linear algebra -/

theorem inner_two (u v : Space 2) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The rotation by a right angle. -/
def rot (v : Space 2) : Space 2 := pt (-v 1) (v 0)

theorem inner_rot_self (v : Space 2) : inner ℝ (rot v) v = 0 := by
  rw [inner_two, rot, pt_zero, pt_one]
  ring

theorem norm_rot (v : Space 2) : ‖rot v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two, rot,
    pt_zero, pt_one]
  simp only [Real.norm_eq_abs, sq_abs, neg_sq]
  ring_nf

/-- Every vector is the combination of an orthonormal pair of the plane. -/
theorem decomp {e ν : Space 2} (he : ‖e‖ = 1) (hν : ‖ν‖ = 1) (h : inner ℝ e ν = 0)
    (z : Space 2) : z = inner ℝ e z • e + inner ℝ ν z • ν := by
  have hon : Orthonormal ℝ ![e, ν] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [he, hν, h, real_inner_comm e ν]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ![e, ν]) := by
    rw [hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)]
  have h2 := (OrthonormalBasis.mk hon hsp).sum_repr' z
  simp only [OrthonormalBasis.coe_mk, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h2
  exact h2.symm

theorem unit_rot {x : Space 2} (hx : x ≠ 0) : ‖‖x‖⁻¹ • rot x‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, norm_rot, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-! ### 2. Local half-plane structure at regular points -/

/-- A `C¹` defining function vanishes at the boundary points in its ball. -/
theorem eq_zero_of_mem_boundary_C1 {E : Set (Space 2)} {F : Space 2 → ℝ} {x : Space 2} {r : ℝ}
    (hF : ContDiffOn ℝ 1 F (ball x r))
    (hae : ∀ᵐ y ∂volume, y ∈ ball x r → (y ∈ E ↔ 0 < F y)) {z : Space 2} (hz : z ∈ ball x r)
    (hzB : z ∈ measureTheoreticBoundary E) : F z = 0 := by
  have hcont : ContinuousAt F z := (hF.continuousOn).continuousAt (isOpen_ball.mem_nhds hz)
  by_contra hne
  have hb : ∀ᶠ y in 𝓝 z, y ∈ ball x r := isOpen_ball.mem_nhds hz
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨s, hs, hsub⟩ := Metric.eventually_nhds_iff_ball.mp
      (hb.and (hcont.eventually (gt_mem_nhds hneg)))
    apply (hzB s hs).1
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy hyE
    have h := hsub y hyE.2
    have := (hy h.1).mp hyE.1
    linarith [h.2]
  · obtain ⟨s, hs, hsub⟩ := Metric.eventually_nhds_iff_ball.mp
      (hb.and (hcont.eventually (lt_mem_nhds hpos)))
    apply (hzB s hs).2
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy hyE
    have h := hsub y hyE.1
    exact hyE.2 ((hy h.1).mpr h.2)

/-- **Local half-plane structure.** Near a nonzero `C¹` boundary point `x` of a cone in the plane,
the cone is a.e. a half-plane bounded by the line `ℝ x`. -/
theorem local_halfplane {T : Set (Space 2)} (hT : IsMinimizingCone T) {x : Space 2}
    (hxB : x ∈ measureTheoreticBoundary T) (hx0 : x ≠ 0) (hreg : IsC1BoundaryPoint T x) :
    ∃ ν : Space 2, ‖ν‖ = 1 ∧ inner ℝ ν x = 0 ∧ ∃ ρ > 0,
      ∀ᵐ y ∂volume, y ∈ ball x ρ → (y ∈ T ↔ 0 < inner ℝ ν y) := by
  obtain ⟨F, r, hr, hF, hFx, hdF, hae⟩ := hreg
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hdiff : ∀ z ∈ ball x r, DifferentiableAt ℝ F z := fun z hz ↦
    (hF.differentiableOn one_ne_zero z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  -- `F` vanishes along the ray through `x`
  have hray : fderiv ℝ F x x = 0 := by
    have h1 : HasDerivAt (fun s : ℝ ↦ s • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hd := (hdiff x (mem_ball_self hr)).hasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ) h1
      (by simp)
    have hcs : Continuous (fun s : ℝ ↦ s • x) := continuous_id.smul continuous_const
    have hev : (fun s : ℝ ↦ F (s • x)) =ᶠ[𝓝 1] fun _ ↦ 0 := by
      have h2 : ∀ᶠ s in 𝓝 (1 : ℝ), s • x ∈ ball x r :=
        (hcs.tendsto' 1 x (one_smul ℝ x)).eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
      filter_upwards [h2, lt_mem_nhds (zero_lt_one' ℝ)] with s hs hs0
      exact eq_zero_of_mem_boundary_C1 hF hae hs
        ((hT.smul_mem_measureTheoreticBoundary_iff hs0 x).mpr hxB)
    exact (by simpa [Function.comp_def] using hd :
      HasDerivAt (fun s : ℝ ↦ F (s • x)) (fderiv ℝ F x x) 1).unique
      ((hasDerivAt_const (1 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)
  -- the normal direction
  set e : Space 2 := ‖x‖⁻¹ • x with he_def
  set τ : Space 2 := ‖x‖⁻¹ • rot x with hτ_def
  have he1 : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
  have hτ1 : ‖τ‖ = 1 := unit_rot hx0
  have heτ : inner ℝ e τ = 0 := by
    rw [he_def, hτ_def, real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      inner_rot_self, mul_zero, mul_zero]
  have hdτ : fderiv ℝ F x τ ≠ 0 := by
    intro h0
    apply hdF
    ext1 w
    rw [decomp he1 hτ1 heτ w, map_add, map_smul, map_smul, he_def, map_smul, hray, h0]
    simp
  set κ := fderiv ℝ F x τ with hκ
  set ν : Space 2 := (κ / |κ|) • τ with hν_def
  have hκabs : 0 < |κ| := abs_pos.mpr hdτ
  have hν1 : ‖ν‖ = 1 := by
    rw [hν_def, norm_smul, hτ1, mul_one, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs,
      div_self hκabs.ne']
  have hνx : inner ℝ ν x = 0 := by
    have : x = ‖x‖ • e := by rw [he_def, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
    rw [this, hν_def, real_inner_smul_left, real_inner_smul_right, real_inner_comm, heτ]
    ring
  have heν : inner ℝ e ν = 0 := by
    rw [hν_def, real_inner_smul_right, heτ, mul_zero]
  have hdν : 0 < fderiv ℝ F x ν := by
    rw [hν_def, map_smul, smul_eq_mul, ← hκ]
    have : κ / |κ| * κ = |κ| := by
      rw [div_mul_eq_mul_div, ← sq, ← sq_abs, sq, mul_div_assoc, div_self hκabs.ne', mul_one]
    rw [this]
    exact hκabs
  -- positivity of the derivative along `ν` near `x`
  have hcd : ContinuousAt (fun z ↦ fderiv ℝ F z ν) x :=
    ((hF.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).continuousAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))).clm_apply continuousAt_const
  have hbx : ∀ᶠ z in 𝓝 x, z ∈ ball x r := isOpen_ball.mem_nhds (mem_ball_self hr)
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.eventually_nhds_iff_ball.mp
    (hbx.and (hcd.eventually (lt_mem_nhds hdν)))
  set δ := min (δ₁ / 2) (‖x‖ / 2) with hδ_def
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨ν, hν1, hνx, δ, hδ, ?_⟩
  filter_upwards [hae] with y hy hyb
  rw [mem_ball, dist_eq_norm] at hyb
  have hyr : y ∈ ball x r := (hδ₁sub y (by
    rw [mem_ball, dist_eq_norm]
    linarith [min_le_left (δ₁ / 2) (‖x‖ / 2)])).1
  rw [hy hyr]
  -- the foot point on the ray
  set t := inner ℝ ν y with ht
  set y₀ := y - t • ν with hy₀
  have hy₀e : y₀ = inner ℝ e y • e := by
    rw [hy₀, sub_eq_iff_eq_add]
    exact decomp he1 hν1 heν y
  have hfoot : ‖y₀ - x‖ ≤ ‖y - x‖ := by
    have h1 : y₀ - x = (y - x) - inner ℝ ν (y - x) • ν := by
      rw [hy₀, inner_sub_right, hνx, sub_zero]
      abel
    rw [h1]
    have h2 : ‖(y - x) - inner ℝ ν (y - x) • ν‖ ^ 2 = ‖y - x‖ ^ 2 - inner ℝ ν (y - x) ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, hν1, mul_one, real_inner_smul_right, real_inner_comm,
        Real.norm_eq_abs, sq_abs]
      ring
    have h3 : ‖(y - x) - inner ℝ ν (y - x) • ν‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
      rw [h2]
      nlinarith [sq_nonneg (inner ℝ ν (y - x))]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
  have hey : 0 < inner ℝ e y := by
    have h1 : inner ℝ e x = ‖x‖ := by
      rw [he_def, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    have h2 : |inner ℝ e (y - x)| ≤ ‖y - x‖ := by
      have := abs_real_inner_le_norm e (y - x)
      rwa [he1, one_mul] at this
    rw [inner_sub_right, h1] at h2
    have h3 : ‖y - x‖ < ‖x‖ / 2 := lt_of_lt_of_le hyb (min_le_right _ _)
    linarith [(abs_le.mp h2).1]
  have hy₀B : y₀ ∈ measureTheoreticBoundary T := by
    rw [hy₀e, he_def, smul_smul]
    exact (hT.smul_mem_measureTheoreticBoundary_iff (by positivity) x).mpr hxB
  have hy₀r : y₀ ∈ ball x r := by
    refine (hδ₁sub y₀ ?_).1
    rw [mem_ball, dist_eq_norm]
    linarith [min_le_left (δ₁ / 2) (‖x‖ / 2)]
  have hFy₀ : F y₀ = 0 := eq_zero_of_mem_boundary_C1 hF hae hy₀r hy₀B
  -- monotonicity of `F` along the normal line through `y₀`
  have hseg : ∀ s : ℝ, |s| ≤ |t| → y₀ + s • ν ∈ ball x δ₁ := by
    intro s hs
    rw [mem_ball, dist_eq_norm]
    have h1 : |t| ≤ ‖y - x‖ := by
      have h := abs_real_inner_le_norm ν (y - x)
      rwa [hν1, one_mul, inner_sub_right, hνx, sub_zero, ← ht] at h
    calc ‖y₀ + s • ν - x‖ = ‖(y₀ - x) + s • ν‖ := by congr 1; abel
      _ ≤ ‖y₀ - x‖ + ‖s • ν‖ := norm_add_le _ _
      _ ≤ ‖y - x‖ + |t| := by
          rw [norm_smul, hν1, mul_one, Real.norm_eq_abs]
          exact add_le_add hfoot hs
      _ < δ₁ := by linarith [min_le_left (δ₁ / 2) (‖x‖ / 2)]
  have hφ : ∀ s : ℝ, |s| ≤ |t| →
      HasDerivAt (fun s ↦ F (y₀ + s • ν)) (fderiv ℝ F (y₀ + s • ν) ν) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ ↦ y₀ + s • ν) ν s := by
      simpa using ((hasDerivAt_id s).smul_const ν).const_add y₀
    have hz := (hδ₁sub _ (hseg s hs)).1
    exact (hdiff _ hz).hasFDerivAt.comp_hasDerivAt s h1
  have hyt : y = y₀ + t • ν := by rw [hy₀]; abel
  rw [hyt]
  rcases lt_trichotomy t 0 with htn | ht0 | htp
  · -- `t < 0`
    have hin : ∀ s, t ≤ s → s ≤ 0 → |s| ≤ |t| := fun s h1 h2 ↦ by
      rw [abs_of_nonpos h2, abs_of_neg htn]
      linarith
    obtain ⟨c, hc, hcd'⟩ := exists_hasDerivAt_eq_slope (fun s ↦ F (y₀ + s • ν))
      (fun s ↦ fderiv ℝ F (y₀ + s • ν) ν) htn
      (fun s hs ↦ (hφ s (hin s hs.1 hs.2)).continuousAt.continuousWithinAt)
      (fun s hs ↦ hφ s (hin s hs.1.le hs.2.le))
    have hpos := (hδ₁sub _ (hseg c (hin c hc.1.le hc.2.le))).2
    rw [hcd', zero_smul, add_zero, hFy₀, zero_sub, zero_sub, neg_div_neg_eq] at hpos
    have : F (y₀ + t • ν) < 0 := by
      rcases div_pos_iff.mp hpos with h | h
      · linarith [h.2]
      · exact h.1
    constructor <;> intro h <;> linarith
  · rw [ht0, zero_smul, add_zero, hFy₀]
  · have hin : ∀ s, 0 ≤ s → s ≤ t → |s| ≤ |t| := fun s h1 h2 ↦ by
      rw [abs_of_nonneg h1, abs_of_pos htp]
      exact h2
    obtain ⟨c, hc, hcd'⟩ := exists_hasDerivAt_eq_slope (fun s ↦ F (y₀ + s • ν))
      (fun s ↦ fderiv ℝ F (y₀ + s • ν) ν) htp
      (fun s hs ↦ (hφ s (hin s hs.1 hs.2)).continuousAt.continuousWithinAt)
      (fun s hs ↦ hφ s (hin s hs.1.le hs.2.le))
    have hpos := (hδ₁sub _ (hseg c (hin c hc.1.le hc.2.le))).2
    rw [hcd', zero_smul, add_zero, hFy₀, sub_zero, sub_zero] at hpos
    have : 0 < F (y₀ + t • ν) := by
      rcases div_pos_iff.mp hpos with h | h
      · exact h.1
      · linarith [h.2]
    constructor <;> intro h <;> linarith

/-! ### 3. Pointwise local structure -/

theorem abs_inner_sub_le {ν : Space 2} (hν : ‖ν‖ = 1) (y z : Space 2) :
    |inner ℝ ν y - inner ℝ ν z| ≤ ‖y - z‖ := by
  rw [← inner_sub_right]
  calc |inner ℝ ν (y - z)| ≤ ‖ν‖ * ‖y - z‖ := abs_real_inner_le_norm _ _
    _ = ‖y - z‖ := by rw [hν, one_mul]

theorem notMem_boundary_of_mem_interior {T : Set (Space 2)} {x : Space 2}
    (hx : x ∈ measureTheoreticInterior T) : x ∉ measureTheoreticBoundary T := by
  obtain ⟨r, hr, h⟩ := hx
  exact fun hB ↦ (hB r hr).2 h

theorem subset_interior_of_preconnected {T V : Set (Space 2)} (hV : IsPreconnected V)
    (hVb : ∀ z ∈ V, z ∉ measureTheoreticBoundary T) {q : Space 2} (hqV : q ∈ V)
    (hq : q ∈ measureTheoreticInterior T) : V ⊆ measureTheoreticInterior T := by
  rcases subset_measureTheoreticInterior_or_exterior hV hVb with h | h
  · exact h
  · exact absurd (h hqV) (disjoint_left.mp (disjoint_measureTheoreticInterior_exterior T) hq)

theorem subset_exterior_of_preconnected {T V : Set (Space 2)} (hV : IsPreconnected V)
    (hVb : ∀ z ∈ V, z ∉ measureTheoreticBoundary T) {q : Space 2} (hqV : q ∈ V)
    (hq : q ∈ measureTheoreticExterior T) : V ⊆ measureTheoreticExterior T := by
  rcases subset_measureTheoreticInterior_or_exterior hV hVb with h | h
  · exact absurd hq (disjoint_left.mp (disjoint_measureTheoreticInterior_exterior T) (h hqV))
  · exact h

theorem convex_inner_pos (v : Space 2) : Convex ℝ {z : Space 2 | 0 < inner ℝ v z} := by
  intro x hx y hy α β hα hβ hαβ
  simp only [mem_ofPred_eq] at hx hy ⊢
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rcases hα.lt_or_eq with hα' | hα'
  · nlinarith [mul_pos hα' hx, mul_nonneg hβ hy.le]
  · rw [← hα', zero_add] at hαβ
    rw [← hα', hαβ]
    linarith

/-- An a.e. half-plane structure on a ball, in pointwise form: points on the positive side are
measure-theoretic interior points, points on the negative side are exterior points. -/
theorem halfplane_pointwise {T : Set (Space 2)} {x ν : Space 2} (hν : ‖ν‖ = 1) {ρ : ℝ}
    (h : ∀ᵐ y ∂volume, y ∈ ball x ρ → (y ∈ T ↔ 0 < inner ℝ ν y)) :
    ∀ q ∈ ball x ρ, (0 < inner ℝ ν q → q ∈ measureTheoreticInterior T) ∧
      (inner ℝ ν q < 0 → q ∈ measureTheoreticExterior T) := by
  intro q hq
  have hd : 0 < ρ - dist q x := sub_pos.mpr (mem_ball.mp hq)
  have hsub : ∀ z, dist z q < ρ - dist q x → z ∈ ball x ρ := by
    intro z hz
    rw [mem_ball]
    calc dist z x ≤ dist z q + dist q x := dist_triangle _ _ _
      _ < ρ - dist q x + dist q x := by linarith
      _ = ρ := by ring
  constructor
  · intro hpos
    refine ⟨min (ρ - dist q x) (inner ℝ ν q), lt_min hd hpos, ?_⟩
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with z hz hzm
    obtain ⟨hzb, hzT⟩ := hzm
    have hz1 := mem_ball.mp hzb
    apply hzT
    refine (hz (hsub z (lt_of_lt_of_le hz1 (min_le_left _ _)))).mpr ?_
    have h1 := abs_inner_sub_le hν z q
    rw [abs_le] at h1
    have h2 : ‖z - q‖ < inner ℝ ν q := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le hz1 (min_le_right _ _)
    linarith [h1.1]
  · intro hneg
    refine ⟨min (ρ - dist q x) (-inner ℝ ν q), lt_min hd (by linarith), ?_⟩
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with z hz hzm
    obtain ⟨hzT, hzb⟩ := hzm
    have hz1 := mem_ball.mp hzb
    have hpos := (hz (hsub z (lt_of_lt_of_le hz1 (min_le_left _ _)))).mp hzT
    have h1 := abs_inner_sub_le hν z q
    rw [abs_le] at h1
    have h2 : ‖z - q‖ < -inner ℝ ν q := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le hz1 (min_le_right _ _)
    linarith [h1.2]

/-- Every nonzero boundary point of `T` has a local (pointwise) half-plane structure. -/
def LocalHalfplanes (T : Set (Space 2)) : Prop :=
  ∀ x ∈ measureTheoreticBoundary T, x ≠ 0 → ∃ ν : Space 2, ‖ν‖ = 1 ∧ inner ℝ ν x = 0 ∧
    ∃ ρ > 0, ∀ q ∈ ball x ρ, (0 < inner ℝ ν q → q ∈ measureTheoreticInterior T) ∧
      (inner ℝ ν q < 0 → q ∈ measureTheoreticExterior T)

theorem localHalfplanes_of_C1 {T : Set (Space 2)} (hT : IsMinimizingCone T)
    (hreg : ∀ x ∈ measureTheoreticBoundary T, x ≠ 0 → IsC1BoundaryPoint T x) :
    LocalHalfplanes T := by
  intro x hxB hx0
  obtain ⟨ν, hν1, hνx, ρ, hρ, hae⟩ := local_halfplane hT hxB hx0 (hreg x hxB hx0)
  exact ⟨ν, hν1, hνx, ρ, hρ, halfplane_pointwise hν1 hae⟩

theorem LocalHalfplanes.compl {T : Set (Space 2)} (h : LocalHalfplanes T) :
    LocalHalfplanes Tᶜ := by
  intro x hxB hx0
  rw [measureTheoreticBoundary_compl] at hxB
  obtain ⟨ν, hν1, hνx, ρ, hρ, hloc⟩ := h x hxB hx0
  refine ⟨-ν, by rw [norm_neg, hν1], by rw [inner_neg_left, hνx, neg_zero], ρ, hρ,
    fun q hq ↦ ?_⟩
  rw [measureTheoreticInterior_compl, measureTheoreticExterior_compl, inner_neg_left]
  exact ⟨fun hq' ↦ (hloc q hq).2 (by linarith), fun hq' ↦ (hloc q hq).1 (by linarith)⟩

/-! ### 4. The chord argument in an arbitrary orthogonal frame -/

/-- `Planar.chord_false` in the frame of two orthogonal vectors `w, u`: a minimizing cone cannot
coincide, on the sector `{q |⟪w, ·⟫| < ⟪u, ·⟫}` with `0 < q < 1`, with the narrower sector
`{|⟪w, ·⟫| < ⟪u, ·⟫}`. -/
theorem chord_false_frame {E : Set (Space 2)} (hE : IsMinimizingCone E) {u w : Space 2}
    (hu : u ≠ 0) (hw : w ≠ 0) (huw : inner ℝ u w = 0) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (h : ∀ᵐ y ∂volume, q * |inner ℝ w y| < inner ℝ u y →
      (y ∈ E ↔ |inner ℝ w y| < inner ℝ u y)) : False := by
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set f : Space 2 := ‖w‖⁻¹ • w with hf
  set e : Space 2 := ‖u‖⁻¹ • u with he
  have hf1 : ‖f‖ = 1 := by rw [hf, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0.ne']
  have he1 : ‖e‖ = 1 := by rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu0.ne']
  have hfe : inner ℝ f e = 0 := by
    rw [hf, he, real_inner_smul_left, real_inner_smul_right, real_inner_comm, huw, mul_zero,
      mul_zero]
  have hon : Orthonormal ℝ ![f, e] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hf1, he1, hfe, real_inner_comm f e]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ![f, e]) := by
    rw [hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)]
  set B := OrthonormalBasis.mk hon hsp with hB
  have hB0 : B 0 = f := by simp [hB]
  have hB1 : B 1 = e := by simp [hB]
  set Q : Space 2 ≃ₗᵢ[ℝ] Space 2 := B.repr.symm with hQ
  have hQi : ∀ (x : Space 2) (i : Fin 2), inner ℝ (B i) (Q x) = x i := by
    intro x i
    rw [← B.repr_apply_apply, hQ, LinearIsometryEquiv.apply_symm_apply]
  have hwQ : ∀ x : Space 2, inner ℝ w (Q x) = ‖w‖ * x 0 := by
    intro x
    rw [← hQi x 0, hB0, hf, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hw0.ne', one_mul]
  have huQ : ∀ x : Space 2, inner ℝ u (Q x) = ‖u‖ * x 1 := by
    intro x
    rw [← hQi x 1, hB1, he, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hu0.ne', one_mul]
  have hκ : 0 < ‖w‖ / ‖u‖ := div_pos hw0 hu0
  have hiff : ∀ (c : ℝ) (x : Space 2),
      c * |‖w‖ * x 0| < ‖u‖ * x 1 ↔ c * (‖w‖ / ‖u‖) * |x 0| < x 1 := by
    intro c x
    rw [abs_mul, abs_of_pos hw0, mul_div_assoc', div_mul_eq_mul_div, div_lt_iff₀ hu0]
    constructor <;> intro h' <;> linarith
  refine chord_false (hE.preimage_linearIsometryEquiv Q) (mul_pos hq0 hκ)
    (mul_lt_of_lt_one_left hκ hq1) ?_
  filter_upwards [Q.measurePreserving.quasiMeasurePreserving.ae h] with x hx hxW
  rw [hwQ, huQ] at hx
  have h1 := hiff 1 x
  rw [one_mul, one_mul] at h1
  exact (hx ((hiff q x).mpr hxW)).trans h1

/-! ### 5. No boundary points on the side of the normal -/

theorem sector_iff {s N M : ℝ} (hs : 0 < s) :
    |s * N - M| < s * N + M ↔ (0 < N ∧ 0 < M) := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    by_contra h
    have h' : N ≤ 0 := not_lt.mp h
    nlinarith
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith [mul_pos hs h1], by linarith⟩

/-- The wide sector near the edge `ℝ₊ a`, in the coordinates `N = ⟪n, ·⟫`, `M = ⟪m, ·⟫`. -/
theorem margin_a {s ρ η σ N M : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hη2 : η * (1 + ρ * |σ|) ≤ ρ * s) (hW : (1 - η) * |s * N - M| < s * N + M) (hN : N < 0) :
    0 < M + σ * N ∧ -N < ρ * (M + σ * N) := by
  have h0 : 0 ≤ (1 - η) * |s * N - M| := mul_nonneg (by linarith) (abs_nonneg _)
  have hsN : s * N < 0 := mul_neg_of_pos_of_neg hs hN
  have hab : |s * N - M| = M - s * N := by
    rw [abs_of_neg (by linarith)]
    ring
  rw [hab] at hW
  have hP : 0 < s * -N := by linarith
  have h1 : (2 - η) * (s * -N) < η * M := by linarith
  have h2 : s * -N ≤ (2 - η) * (s * -N) := by nlinarith
  have h3 : η * ((1 + ρ * |σ|) * -N) ≤ ρ * s * -N := by
    have := mul_le_mul_of_nonneg_right hη2 (by linarith : (0 : ℝ) ≤ -N)
    linarith
  have h4 : η * ((1 + ρ * |σ|) * -N) < η * (ρ * M) := by
    linarith [mul_lt_mul_of_pos_left h1 hρ, mul_le_mul_of_nonneg_left h2 hρ.le]
  have h5 : (1 + ρ * |σ|) * -N < ρ * M := lt_of_mul_lt_mul_left h4 hη.le
  have h6 : ρ * σ * -N ≤ ρ * |σ| * -N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self σ) hρ.le) (by linarith)
  have h7 : -N < ρ * (M + σ * N) := by linarith
  refine ⟨?_, h7⟩
  by_contra h
  have h' : M + σ * N ≤ 0 := not_lt.mp h
  nlinarith

/-- The wide sector near the edge `ℝ₊ c`, in the coordinates `N = ⟪n, ·⟫`, `M = ⟪m, ·⟫`. -/
theorem margin_c {s ρ η N M : ℝ} (hs : 0 < s) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hη3 : η * s ≤ ρ) (hW : (1 - η) * |s * N - M| < s * N + M) (hM : M < 0) :
    0 < N ∧ -M < ρ * N := by
  have h0 : 0 ≤ (1 - η) * |s * N - M| := mul_nonneg (by linarith) (abs_nonneg _)
  have hsN : 0 < s * N := by linarith
  have hN : 0 < N := pos_of_mul_pos_right hsN hs.le
  have hab : |s * N - M| = s * N - M := abs_of_pos (by linarith)
  rw [hab] at hW
  have h1 : (2 - η) * -M < η * (s * N) := by linarith
  have h2 : -M ≤ (2 - η) * -M := by nlinarith
  have h3 : η * s * N ≤ ρ * N := mul_le_mul_of_nonneg_right hη3 hN.le
  exact ⟨hN, by linarith⟩

/-- **No acute sectors.** Let `a` be a unit vector and `n ⊥ a` a unit normal such that the cone
is the half-plane `{⟪n, ·⟫ > 0}` near `a`. Then there are no boundary points on the side of `n`:
otherwise the boundary direction `n + σ* a` with the largest slope `σ*` bounds, together with `a`,
a sector of angle `< π` in which the cone is full and along whose edges it is a half-plane, which
is excluded by the chord argument. -/
theorem no_boundary_on_side {T : Set (Space 2)} (hT : IsMinimizingCone T)
    (hH : LocalHalfplanes T) {a n : Space 2} (ha : ‖a‖ = 1) (hn : ‖n‖ = 1)
    (han : inner ℝ a n = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hloc : ∀ q ∈ ball a ρ, (0 < inner ℝ n q → q ∈ measureTheoreticInterior T) ∧
      (inner ℝ n q < 0 → q ∈ measureTheoreticExterior T))
    {y : Space 2} (hy : 0 < inner ℝ n y) : y ∉ measureTheoreticBoundary T := by
  intro hyB
  have haa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have hna : inner ℝ n a = 0 := by rw [real_inner_comm]; exact han
  have hcB : ∀ t : ℝ, 0 < t → ∀ z : Space 2,
      t • z ∈ measureTheoreticBoundary T ↔ z ∈ measureTheoreticBoundary T :=
    fun t ht z ↦ hT.smul_mem_measureTheoreticBoundary_iff ht z
  have hcE : ∀ t : ℝ, 0 < t → ∀ z : Space 2,
      t • z ∈ measureTheoreticExterior T ↔ z ∈ measureTheoreticExterior T :=
    fun t ht z ↦ mem_measureTheoreticExterior_smul_iff_of_ae_cone hT.dilation ht z
  have hray : ∀ z : Space 2, 0 < inner ℝ n z →
      (inner ℝ n z)⁻¹ • z = n + (inner ℝ a z / inner ℝ n z) • a := by
    intro z hz
    calc (inner ℝ n z)⁻¹ • z
        = (inner ℝ n z)⁻¹ • (inner ℝ a z • a + inner ℝ n z • n) := by
          rw [← decomp ha hn han z]
      _ = n + (inner ℝ a z / inner ℝ n z) • a := by
          rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hz.ne', one_smul, add_comm,
            div_eq_inv_mul]
  -- the slopes of the boundary directions on the side of `n`
  set S : Set ℝ := {σ : ℝ | n + σ • a ∈ measureTheoreticBoundary T} with hS
  have hSmem : ∀ z : Space 2, 0 < inner ℝ n z →
      (z ∈ measureTheoreticBoundary T ↔ inner ℝ a z / inner ℝ n z ∈ S) := by
    intro z hz
    have h1 := hcB _ (inv_pos.mpr hz) z
    rw [hray z hz] at h1
    exact h1.symm
  have hS0 : inner ℝ a y / inner ℝ n y ∈ S := (hSmem y hy).mp hyB
  have hSbdd : BddAbove S := by
    refine ⟨ρ⁻¹, fun σ hσ ↦ ?_⟩
    by_contra hlt'
    have hlt : ρ⁻¹ < σ := not_le.mp hlt'
    have hσpos : 0 < σ := lt_trans (inv_pos.mpr hρ) hlt
    have hmem := (hcB _ (inv_pos.mpr hσpos) (n + σ • a)).mpr hσ
    have heq : σ⁻¹ • (n + σ • a) = a + σ⁻¹ • n := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hσpos.ne', one_smul, add_comm]
    rw [heq] at hmem
    have hball : a + σ⁻¹ • n ∈ ball a ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hn, mul_one, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hσpos)]
      exact (inv_lt_comm₀ hσpos hρ).mpr hlt
    have hinn : 0 < inner ℝ n (a + σ⁻¹ • n) := by
      rw [inner_add_right, hna, real_inner_smul_right, hnn, mul_one, zero_add]
      exact inv_pos.mpr hσpos
    exact notMem_boundary_of_mem_interior ((hloc _ hball).1 hinn) hmem
  have hSclosed : IsClosed S := by
    have hcont : Continuous (fun σ : ℝ ↦ n + σ • a) := by fun_prop
    exact IsClosed.preimage hcont (isClosed_measureTheoreticBoundary T)
  set σs := sSup S with hσs
  have hσsS : σs ∈ S := hSclosed.csSup_mem ⟨_, hS0⟩ hSbdd
  have hgt : ∀ σ, σs < σ → σ ∉ S := fun σ hσ hσS ↦ (not_le.mpr hσ) (le_csSup hSbdd hσS)
  -- the extreme boundary direction `c`
  set c : Space 2 := n + σs • a with hc
  have hcB' : c ∈ measureTheoreticBoundary T := hσsS
  have hnc : inner ℝ n c = 1 := by
    rw [hc, inner_add_right, hnn, real_inner_smul_right, hna, mul_zero, add_zero]
  have hac : inner ℝ a c = σs := by
    rw [hc, inner_add_right, han, real_inner_smul_right, haa, mul_one, zero_add]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, inner_zero_right] at hnc
    exact zero_ne_one hnc
  obtain ⟨ν, hν1, hνc, ρc, hρc, hlocc⟩ := hH c hcB' hc0
  -- the open sector between `a` and `c`
  set m : Space 2 := a - σs • n with hm
  have hmz : ∀ z : Space 2, inner ℝ m z = inner ℝ a z - σs * inner ℝ n z := by
    intro z
    rw [hm, inner_sub_left, real_inner_smul_left]
  have ham : inner ℝ a m = 1 := by
    rw [hm, inner_sub_right, haa, real_inner_smul_right, han, mul_zero, sub_zero]
  have hma : inner ℝ m a = 1 := by rw [real_inner_comm]; exact ham
  have hnm : inner ℝ n m = -σs := by
    rw [hm, inner_sub_right, hna, real_inner_smul_right, hnn, mul_one, zero_sub]
  have hmn : inner ℝ m n = -σs := by rw [real_inner_comm]; exact hnm
  have hmm : inner ℝ m m = 1 + σs ^ 2 := by rw [hmz, ham, hnm]; ring
  have hmc : inner ℝ m c = 0 := by rw [hmz, hac, hnc]; ring
  set V : Set (Space 2) := {z | 0 < inner ℝ n z} ∩ {z | 0 < inner ℝ m z} with hV
  have hVconv : Convex ℝ V := (convex_inner_pos n).inter (convex_inner_pos m)
  have hVb : ∀ z ∈ V, z ∉ measureTheoreticBoundary T := by
    intro z hz hzB
    have hz1 : 0 < inner ℝ n z := hz.1
    have hz2 : 0 < inner ℝ m z := hz.2
    refine hgt _ ?_ ((hSmem z hz1).mp hzB)
    rw [lt_div_iff₀ hz1]
    rw [hmz] at hz2
    linarith
  -- the sector is full: it contains interior points near `a`
  set ε := min (ρ / 2) (1 / (|σs| + 1)) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by positivity)
  have hερ : ε < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεσ : σs * ε < 1 := by
    have h1 : ε ≤ 1 / (|σs| + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : σs * ε ≤ |σs| * ε := mul_le_mul_of_nonneg_right (le_abs_self σs) hεpos.le
    linarith
  have hq1n : inner ℝ n (a + ε • n) = ε := by
    rw [inner_add_right, hna, real_inner_smul_right, hnn, mul_one, zero_add]
  have hq1m : inner ℝ m (a + ε • n) = 1 - σs * ε := by
    rw [inner_add_right, hma, real_inner_smul_right, hmn]
    ring
  have hq1 : a + ε • n ∈ measureTheoreticInterior T := by
    refine (hloc _ ?_).1 (by rw [hq1n]; exact hεpos)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hn, mul_one, Real.norm_eq_abs,
      abs_of_pos hεpos]
    exact hερ
  have hq1V : a + ε • n ∈ V :=
    ⟨show 0 < inner ℝ n (a + ε • n) by rw [hq1n]; exact hεpos,
      show 0 < inner ℝ m (a + ε • n) by rw [hq1m]; linarith⟩
  have hVint : V ⊆ measureTheoreticInterior T :=
    subset_interior_of_preconnected hVconv.isPreconnected hVb hq1V hq1
  -- the normal at `c` is a positive multiple of `m`
  have hνn : inner ℝ n ν = -(σs * inner ℝ a ν) := by
    have h0 : inner ℝ ν c = 0 := hνc
    rw [hc, inner_add_right, real_inner_smul_right, real_inner_comm n ν,
      real_inner_comm a ν] at h0
    linarith
  have hνm : ν = inner ℝ a ν • m := by
    conv_lhs => rw [decomp ha hn han ν]
    rw [hνn, hm]
    module
  have hνne : inner ℝ a ν ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hνm
    rw [hνm, norm_zero] at hν1
    exact zero_ne_one hν1
  have hνpos : 0 < inner ℝ a ν := by
    by_contra hle
    have hneg : inner ℝ a ν < 0 := lt_of_le_of_ne (not_lt.mp hle) hνne
    have hq2n : inner ℝ n (c + (ρc / 2) • a) = 1 := by
      rw [inner_add_right, hnc, real_inner_smul_right, hna, mul_zero, add_zero]
    have hq2m : inner ℝ m (c + (ρc / 2) • a) = ρc / 2 := by
      rw [inner_add_right, hmc, real_inner_smul_right, hma, mul_one, zero_add]
    have hq2V : c + (ρc / 2) • a ∈ V :=
      ⟨show 0 < inner ℝ n (c + (ρc / 2) • a) by rw [hq2n]; exact one_pos,
        show 0 < inner ℝ m (c + (ρc / 2) • a) by rw [hq2m]; positivity⟩
    have hq2b : c + (ρc / 2) • a ∈ ball c ρc := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, ha, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have hq2ν : inner ℝ ν (c + (ρc / 2) • a) < 0 := by
      rw [hνm, real_inner_smul_left, hq2m]
      exact mul_neg_of_neg_of_pos hneg (by positivity)
    exact disjoint_left.mp (disjoint_measureTheoreticInterior_exterior T) (hVint hq2V)
      ((hlocc _ hq2b).2 hq2ν)
  have hlocm : ∀ q ∈ ball c ρc, inner ℝ m q < 0 → q ∈ measureTheoreticExterior T := by
    intro q hq hmq
    refine (hlocc q hq).2 ?_
    rw [hνm, real_inner_smul_left]
    exact mul_neg_of_pos_of_neg hνpos hmq
  -- the frame of the bisector
  set s := √(1 + σs ^ 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = 1 + σs ^ 2 := Real.sq_sqrt (by positivity)
  set u : Space 2 := s • n + m with hu
  set w : Space 2 := s • n - m with hw
  have huz : ∀ z : Space 2, inner ℝ u z = s * inner ℝ n z + inner ℝ m z := by
    intro z
    rw [hu, inner_add_left, real_inner_smul_left]
  have hwz : ∀ z : Space 2, inner ℝ w z = s * inner ℝ n z - inner ℝ m z := by
    intro z
    rw [hw, inner_sub_left, real_inner_smul_left]
  have huw : inner ℝ u w = 0 := by
    rw [huz, real_inner_comm w n, real_inner_comm w m, hwz, hwz, hnn, hmn, hnm, hmm]
    linear_combination hs2
  have huc : inner ℝ u c = s := by rw [huz, hnc, hmc]; ring
  have hwc : inner ℝ w c = s := by rw [hwz, hnc, hmc]; ring
  have hu0 : u ≠ 0 := fun h0 ↦ by
    rw [h0, inner_zero_left] at huc
    exact hspos.ne huc
  have hw0 : w ≠ 0 := fun h0 ↦ by
    rw [h0, inner_zero_left] at hwc
    exact hspos.ne hwc
  -- the width of the margins
  set η := min (1 / 2) (min (ρ * s / (1 + ρ * |σs|)) (ρc / s)) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η * (1 + ρ * |σs|) ≤ ρ * s := by
    have h : η ≤ ρ * s / (1 + ρ * |σs|) := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ (by positivity)] at h
  have hη3 : η * s ≤ ρc := by
    have h : η ≤ ρc / s := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hspos] at h
  -- outside the sector but inside the wide sector, the cone is empty
  have hext : ∀ z : Space 2, (1 - η) * |inner ℝ w z| < inner ℝ u z →
      ¬ (0 < inner ℝ n z ∧ 0 < inner ℝ m z) → inner ℝ n z ≠ 0 → inner ℝ m z ≠ 0 →
      z ∈ measureTheoreticExterior T := by
    intro z hW hnot hN0 hM0
    rw [huz, hwz] at hW
    have hA : inner ℝ a z = inner ℝ m z + σs * inner ℝ n z := by rw [hmz]; ring
    rcases lt_or_gt_of_ne hN0 with hNneg | hNpos
    · -- near the edge `ℝ₊ a`
      obtain ⟨htpos, hlt⟩ := margin_a hspos hρ hηpos hη1 hη2 hW hNneg
      rw [← hA] at htpos hlt
      have hz' : (inner ℝ a z)⁻¹ • z = a + (inner ℝ n z / inner ℝ a z) • n := by
        calc (inner ℝ a z)⁻¹ • z
            = (inner ℝ a z)⁻¹ • (inner ℝ a z • a + inner ℝ n z • n) := by
              rw [← decomp ha hn han z]
          _ = a + (inner ℝ n z / inner ℝ a z) • n := by
              rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul,
                div_eq_inv_mul]
      have hmemb : (inner ℝ a z)⁻¹ • z ∈ ball a ρ := by
        rw [hz', mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hn, mul_one,
          Real.norm_eq_abs, abs_div, abs_of_neg hNneg, abs_of_pos htpos, div_lt_iff₀ htpos]
        exact hlt
      have hinn : inner ℝ n ((inner ℝ a z)⁻¹ • z) < 0 := by
        rw [real_inner_smul_right]
        exact mul_neg_of_pos_of_neg (inv_pos.mpr htpos) hNneg
      have h' := (hcE _ htpos _).mpr ((hloc _ hmemb).2 hinn)
      rwa [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul] at h'
    · -- near the edge `ℝ₊ c`
      have hMneg : inner ℝ m z < 0 :=
        lt_of_le_of_ne (not_lt.mp fun h ↦ hnot ⟨hNpos, h⟩) hM0
      obtain ⟨-, hlt⟩ := margin_c hspos hηpos hη1 hη3 hW hMneg
      have hmemb : (inner ℝ n z)⁻¹ • z ∈ ball c ρc := by
        rw [hray z hNpos, mem_ball, dist_eq_norm, hc]
        have h1 : n + (inner ℝ a z / inner ℝ n z) • a - (n + σs • a) =
            (inner ℝ m z / inner ℝ n z) • a := by
          rw [hmz, sub_div, mul_div_assoc, div_self hNpos.ne', mul_one, sub_smul]
          abel
        rw [h1, norm_smul, ha, mul_one, Real.norm_eq_abs, abs_div, abs_of_neg hMneg,
          abs_of_pos hNpos, div_lt_iff₀ hNpos]
        exact hlt
      have hinn : inner ℝ m ((inner ℝ n z)⁻¹ • z) < 0 := by
        rw [real_inner_smul_right]
        exact mul_neg_of_pos_of_neg (inv_pos.mpr hNpos) hMneg
      have h' := (hcE _ hNpos _).mpr (hlocm _ hmemb hinn)
      rwa [smul_smul, mul_inv_cancel₀ hNpos.ne', one_smul] at h'
  -- the chord argument
  have hn0 : n ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hm0 : m ≠ 0 := fun h0 ↦ by
    rw [h0, inner_zero_right] at ham
    exact zero_ne_one ham
  have hNae : ∀ᵐ z ∂volume, inner ℝ n z ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp (volume_orthogonal_hyperplane_eq_zero hn0)
  have hMae : ∀ᵐ z ∂volume, inner ℝ m z ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp (volume_orthogonal_hyperplane_eq_zero hm0)
  refine chord_false_frame hT hu0 hw0 huw (q := 1 - η) (by linarith) (by linarith) ?_
  filter_upwards [hT.minimizer.ae_mem_iff_measureTheoreticInterior,
    hT.minimizer.ae_mem_compl_iff_measureTheoreticExterior, hNae, hMae]
    with z hzi hze hzN hzM hzW
  have hiff : |inner ℝ w z| < inner ℝ u z ↔ (0 < inner ℝ n z ∧ 0 < inner ℝ m z) := by
    rw [huz, hwz]
    exact sector_iff hspos
  rw [hiff]
  by_cases hS' : 0 < inner ℝ n z ∧ 0 < inner ℝ m z
  · exact iff_of_true ((hzi (mem_univ z)).mpr (hVint hS')) hS'
  · exact iff_of_false (fun hzT ↦ (hze (mem_univ z)).mpr (hext z hzW hS' hzN hzM) hzT) hS'

/-! ### 6. Planar minimizing cones are half-planes -/

/-- A minimizing cone has a boundary point other than the vertex. -/
theorem exists_ne_zero_mem_boundary {m : ℕ} (hm : 0 < m) {T : Set (Space (m + 1))}
    (hT : IsMinimizingCone T) : ∃ y ∈ measureTheoreticBoundary T, y ≠ 0 := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  have hP : ∀ n : ℕ, variationalPerimeter b T (ball 0 ((n : ℝ) + 1)) ≠ ⊤ := fun n ↦
    hT.minimizer.perimeter_ball_ne_top 0 _ (by positivity) (subset_univ _)
  by_contra hcon
  have hcon' : ∀ y ∈ measureTheoreticBoundary T, y = 0 := fun y hy ↦
    not_not.mp fun h ↦ hcon ⟨y, hy, h⟩
  set μ := perimeterRadonMeasure b hT.measurableSet hP
  have hμ : ∀ U, IsOpen U → U ⊆ univ → μ U = variationalPerimeter b T U := fun U hU _ ↦
    perimeterRadonMeasure_apply_open b hT.measurableSet hP hU
  have h1 := hT.minimizer.measure_sdiff_boundary_eq_zero μ hμ
  have h2 := hT.minimizer.measure_singleton_eq_zero hm μ hμ (mem_univ (0 : Space (m + 1)))
  have hsub : ball (0 : Space (m + 1)) 1 ⊆ (univ \ measureTheoreticBoundary T) ∪ {0} := by
    intro x _
    by_cases hx : x ∈ measureTheoreticBoundary T
    · exact Or.inr (hcon' x hx)
    · exact Or.inl ⟨mem_univ _, hx⟩
  have h3 : μ (ball 0 1) = 0 := measure_mono_null hsub (measure_union_null h1 h2)
  have hge := hT.minimizer.variationalPerimeter_ball_toReal_ge
    hT.zero_mem_measureTheoreticBoundary one_pos (subset_univ _)
  rw [← hμ _ isOpen_ball (subset_univ _), h3, ENNReal.toReal_zero, one_pow, mul_one] at hge
  exact absurd hge (not_le.mpr (minimizerPerimeterLowerConst_pos m))

/-- A planar minimizing cone with local half-plane structure at its nonzero boundary points is
a.e. a half-plane. -/
theorem ae_eq_halfplane {T : Set (Space 2)} (hT : IsMinimizingCone T) (hH : LocalHalfplanes T) :
    ∃ e : Space 2, ‖e‖ = 1 ∧ T =ᵐ[volume] positiveHalfspace e := by
  obtain ⟨y₀, hy₀B, hy₀0⟩ : ∃ y ∈ measureTheoreticBoundary T, y ≠ 0 :=
    exists_ne_zero_mem_boundary (m := 1) one_pos hT
  have hy₀pos : 0 < ‖y₀‖ := norm_pos_iff.mpr hy₀0
  set a : Space 2 := ‖y₀‖⁻¹ • y₀ with ha_def
  have ha1 : ‖a‖ = 1 := by
    rw [ha_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy₀pos.ne']
  have haB : a ∈ measureTheoreticBoundary T :=
    (hT.smul_mem_measureTheoreticBoundary_iff (inv_pos.mpr hy₀pos) y₀).mpr hy₀B
  have ha0 : a ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at ha1
    exact zero_ne_one ha1
  obtain ⟨n, hn1, hna, ρ, hρ, hloc⟩ := hH a haB ha0
  have han : inner ℝ a n = 0 := by rw [real_inner_comm]; exact hna
  have hpos : ∀ z, 0 < inner ℝ n z → z ∉ measureTheoreticBoundary T :=
    fun z hz ↦ no_boundary_on_side hT hH ha1 hn1 han hρ hloc hz
  have hneg : ∀ z, inner ℝ n z < 0 → z ∉ measureTheoreticBoundary T := by
    intro z hz hzB
    have hlocc : ∀ q ∈ ball a ρ, (0 < inner ℝ (-n) q → q ∈ measureTheoreticInterior Tᶜ) ∧
        (inner ℝ (-n) q < 0 → q ∈ measureTheoreticExterior Tᶜ) := by
      intro q hq
      rw [measureTheoreticInterior_compl, measureTheoreticExterior_compl, inner_neg_left]
      exact ⟨fun h ↦ (hloc q hq).2 (by linarith), fun h ↦ (hloc q hq).1 (by linarith)⟩
    have := no_boundary_on_side hT.compl hH.compl ha1 (by rw [norm_neg]; exact hn1)
      (by rw [inner_neg_right, han, neg_zero]) hρ hlocc (y := z)
      (by rw [inner_neg_left]; linarith)
    exact this (by rwa [measureTheoreticBoundary_compl])
  -- interior and exterior points near `a`
  have hqn : ∀ t : ℝ, inner ℝ n (a + t • n) = t := by
    intro t
    rw [inner_add_right, hna, real_inner_smul_right, real_inner_self_eq_norm_sq, hn1]
    ring
  have hqb : ∀ t : ℝ, |t| < ρ → a + t • n ∈ ball a ρ := by
    intro t ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hn1, mul_one, Real.norm_eq_abs]
    exact ht
  have hqpos : a + (ρ / 2) • n ∈ measureTheoreticInterior T :=
    (hloc _ (hqb _ (by rw [abs_of_pos (by positivity)]; linarith))).1 (by rw [hqn]; positivity)
  have hqneg : a + (-(ρ / 2)) • n ∈ measureTheoreticExterior T :=
    (hloc _ (hqb _ (by rw [abs_neg, abs_of_pos (by positivity)]; linarith))).2
      (by rw [hqn]; linarith)
  have hint : {z : Space 2 | 0 < inner ℝ n z} ⊆ measureTheoreticInterior T :=
    subset_interior_of_preconnected (convex_inner_pos n).isPreconnected hpos
      (show 0 < inner ℝ n (a + (ρ / 2) • n) by rw [hqn]; positivity) hqpos
  have hext : {z : Space 2 | 0 < inner ℝ (-n) z} ⊆ measureTheoreticExterior T := by
    refine subset_exterior_of_preconnected (convex_inner_pos (-n)).isPreconnected
      (fun z hz ↦ hneg z ?_) (show 0 < inner ℝ (-n) (a + (-(ρ / 2)) • n) by
        rw [inner_neg_left, hqn]; linarith) hqneg
    have h' : 0 < inner ℝ (-n) z := hz
    rw [inner_neg_left] at h'
    linarith
  refine ⟨n, hn1, ?_⟩
  have hn0 : n ≠ 0 := fun h0 ↦ by
    rw [h0, norm_zero] at hn1
    exact zero_ne_one hn1
  have hnull : ∀ᵐ z ∂volume, inner ℝ n z ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp (volume_orthogonal_hyperplane_eq_zero hn0)
  filter_upwards [hT.minimizer.ae_mem_iff_measureTheoreticInterior, hnull] with x hx hx0
  have hxi := hx (mem_univ x)
  apply propext
  rw [hxi]
  show x ∈ measureTheoreticInterior T ↔ 0 < inner ℝ n x
  rcases lt_or_gt_of_ne hx0 with hlt | hgt
  · refine iff_of_false (fun hxint ↦ ?_) (not_lt.mpr hlt.le)
    exact disjoint_left.mp (disjoint_measureTheoreticInterior_exterior T) hxint
      (hext (show 0 < inner ℝ (-n) x by rw [inner_neg_left]; linarith))
  · exact iff_of_true (hint hgt) hgt

/-- **`SimonsHyp 2`.** A minimizing cone in the plane whose nonzero boundary points are `C¹`
boundary points is a.e. a half-plane. -/
theorem simonsHyp_two_planar : SimonsHyp 2 := fun _ hT hreg ↦
  ae_eq_halfplane hT (localHalfplanes_of_C1 hT hreg)

end Planar

end SerrinEpigraph
