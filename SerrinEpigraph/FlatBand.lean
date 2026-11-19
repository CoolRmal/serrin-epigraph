module

public import SerrinEpigraph.TiltExcessDecay

/-!
# The band of a flat configuration and recentring (`GR13`, preparation)

* `IsLocalPerimeterMinimizer.band_width_aux_of_le`, `band_width_le_of_le`: the density form of
  `GR10.1` over a base ball `B_ρ` with `ρ + r₀ ≤ 1`.
* `SlabTrappedRepresentation.mem_interior_of_band`, `mem_exterior_of_band`: above the band the
  points are measure-theoretic interior points, below it exterior points.
* `flatBand m e = ((bandOscConst m √e + 2e)/c)^(1/(m+1))`, `IsFlatConfig.band`: the boundary of a
  flat configuration over `B_{3/4}` lies in the band `|t - a| ≤ flatBand m e`, `|a| ≤ flatBand m e`.
* `IsFlatConfig.recenter`: around a boundary point `p` of the half cylinder, the configuration
  rescaled by `1/8` is again flat, with excess at most `8^m e`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

namespace IsLocalPerimeterMinimizer

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **Band width, density form, over `B_ρ`** (`GR10`, with `ρ + r₀ ≤ 1`). -/
theorem band_width_aux_of_le (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU1 : ball (0 : Space m) 1 ⊆ U)
    (hcyl : cylinderSet U H' ⊆ Ω) (a : ℝ) {x : Space (m + 1)}
    (hx : x ∈ measureTheoreticBoundary E) {ρ r₀ : ℝ} (hxh : horizontal x ∈ ball (0 : Space m) ρ)
    (hρ : ρ + r₀ ≤ 1) (hxn : |x (Fin.last m)| < H') (hr₀ : 0 < r₀)
    (hr₀H : r₀ ≤ (H' - H) / 2) :
    minimizerVolumeDensityConst m * (min |x (Fin.last m) - a| r₀) ^ (m + 1) ≤
      volume.real (halfspaceDiscrepancy E H' a) := by
  set D := halfspaceDiscrepancy E H' a with hD_def
  have hDfin : volume D ≠ ⊤ :=
    (measure_ne_top_of_subset (halfspaceDiscrepancy_subset E H' a)
      (volume_cylinderSet_ball_lt_top 0 1 H').ne)
  set h := |x (Fin.last m) - a| with hh_def
  set r := min h r₀ with hr_def
  have hc0 := minimizerVolumeDensityConst_pos m
  rcases eq_or_lt_of_le (abs_nonneg (x (Fin.last m) - a)) with h0 | hpos
  · have hr0 : r = 0 := by rw [hr_def, hh_def, ← h0, min_eq_left hr₀.le]
    rw [hr0, zero_pow (by omega), mul_zero]
    exact measureReal_nonneg
  have hr : 0 < r := lt_min hpos hr₀
  have hrh : r ≤ h := min_le_left _ _
  have hrr₀ : r ≤ r₀ := min_le_right _ _
  have hxh' : dist (horizontal x) 0 < ρ := hxh
  have hxU : horizontal x ∈ U := hU1 (by rw [mem_ball]; linarith)
  have hxH := hS.abs_last_le_of_mem_measureTheoreticBoundary hx hxU hxn
  have hclosed : closedBall x r ⊆ cylinderSet (ball (0 : Space m) 1) H' := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : ‖horizontal z - horizontal x‖ ≤ r := by
      rw [← horizontal_sub_eq]
      exact (norm_horizontal_le_norm_of_space _).trans hz
    have h2 : |z (Fin.last m) - x (Fin.last m)| ≤ r := by
      have := (abs_apply_last_le_norm (z - x)).trans hz
      simpa using this
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      calc
        dist (horizontal z) 0 ≤ dist (horizontal z) (horizontal x) + dist (horizontal x) 0 :=
          dist_triangle _ _ _
        _ < 1 := by rw [dist_eq_norm]; linarith
    · have h3 := abs_le.mp h2
      have h4 := abs_le.mp hxH
      exact ⟨by linarith, by linarith⟩
  have hsub : closedBall x r ⊆ Ω :=
    hclosed.trans ((cylinderSet_mono hU1 le_rfl).trans hcyl)
  have hballD : ∀ z ∈ ball x r, z ∈ cylinderSet (ball (0 : Space m) 1) H' :=
    fun z hz ↦ hclosed (ball_subset_closedBall hz)
  have hlastz : ∀ z ∈ ball x r, |z (Fin.last m) - x (Fin.last m)| < r := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have := (abs_apply_last_le_norm (z - x)).trans_lt hz
    simpa using this
  rcases lt_or_gt_of_ne (show x (Fin.last m) - a ≠ 0 from fun h0 ↦ by
    rw [h0, abs_zero] at hpos; exact lt_irrefl _ hpos) with hneg | hposa
  · have habs : h = a - x (Fin.last m) := by rw [hh_def, abs_of_neg hneg]; ring
    have hsubD : E ∩ ball x r ⊆ D := by
      intro z hz
      refine ⟨hballD z hz.2, fun hiff ↦ ?_⟩
      have h1 := hlastz z hz.2
      have h2 : z (Fin.last m) < a := by
        have := (abs_lt.mp h1).2
        linarith
      exact absurd (hiff.mp hz.1) (not_lt.mpr h2.le)
    calc
      minimizerVolumeDensityConst m * r ^ (m + 1) ≤ volume.real (E ∩ ball x r) :=
        hmin.volume_inter_ball_ge hx hr hsub
      _ ≤ volume.real D := measureReal_mono hsubD hDfin
  · have habs : h = x (Fin.last m) - a := by rw [hh_def, abs_of_pos hposa]
    have hsubD : ball x r \ E ⊆ D := by
      intro z hz
      refine ⟨hballD z hz.1, fun hiff ↦ ?_⟩
      have h1 := hlastz z hz.1
      have h2 : a < z (Fin.last m) := by
        have := (abs_lt.mp h1).1
        linarith
      exact hz.2 (hiff.mpr h2)
    calc
      minimizerVolumeDensityConst m * r ^ (m + 1) ≤ volume.real (ball x r \ E) :=
        hmin.volume_sdiff_ball_ge hx hr hsub
      _ ≤ volume.real D := measureReal_mono hsubD hDfin

/-- **Band width over `B_ρ`** (`GR10.1`, with `ρ + r₀ ≤ 1`). -/
theorem band_width_le_of_le (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU1 : ball (0 : Space m) 1 ⊆ U)
    (hcyl : cylinderSet U H' ⊆ Ω) (a : ℝ) {ρ r₀ : ℝ} (hρ : ρ + r₀ ≤ 1) (hr₀ : 0 < r₀)
    (hr₀H : r₀ ≤ (H' - H) / 2)
    (hsmall : volume.real (halfspaceDiscrepancy E H' a) <
      minimizerVolumeDensityConst m * r₀ ^ (m + 1))
    {x : Space (m + 1)} (hx : x ∈ measureTheoreticBoundary E)
    (hxh : horizontal x ∈ ball (0 : Space m) ρ) (hxn : |x (Fin.last m)| < H') :
    |x (Fin.last m) - a| ≤
      (volume.real (halfspaceDiscrepancy E H' a) / minimizerVolumeDensityConst m) ^
        ((1 : ℝ) / (m + 1)) := by
  have haux := hmin.band_width_aux_of_le hS hU1 hcyl a hx hxh hρ hxn hr₀ hr₀H
  have hc0 := minimizerVolumeDensityConst_pos m
  set V := volume.real (halfspaceDiscrepancy E H' a) with hV_def
  set h := |x (Fin.last m) - a| with hh_def
  have hlt : h < r₀ := by
    by_contra hge
    push Not at hge
    rw [min_eq_right hge] at haux
    linarith
  rw [min_eq_left hlt.le] at haux
  have hh0 : 0 ≤ h := abs_nonneg _
  have hpow : h ^ (m + 1) ≤ V / minimizerVolumeDensityConst m := by
    rw [le_div_iff₀ hc0]
    linarith
  have hexp : ((1 : ℝ) / (m + 1)) = ((m + 1 : ℕ) : ℝ)⁻¹ := by
    rw [one_div, Nat.cast_add, Nat.cast_one]
  calc
    h = (h ^ (m + 1)) ^ ((1 : ℝ) / (m + 1)) := by
      rw [hexp, Real.pow_rpow_inv_natCast hh0 (by omega)]
    _ ≤ (V / minimizerVolumeDensityConst m) ^ ((1 : ℝ) / (m + 1)) :=
      Real.rpow_le_rpow (pow_nonneg hh0 _) hpow (by positivity)

end IsLocalPerimeterMinimizer

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **Above the band the points are interior.** -/
theorem mem_interior_of_band (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {B : Set (Space m)} (hBc : Convex ℝ B) (hBU : B ⊆ U) {a δ : ℝ} (ha : |a| ≤ H) (hδ : 0 ≤ δ)
    (hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ B → |x (Fin.last m)| < H' →
      |x (Fin.last m) - a| ≤ δ)
    {x : Space (m + 1)} (hxB : horizontal x ∈ B) (hx1 : a + δ < x (Fin.last m))
    (hx2 : x (Fin.last m) < H') : x ∈ measureTheoreticInterior E := by
  have hH := hS.pos
  have hHH' := hS.lt
  have haH := abs_le.mp ha
  set Vp := {z : Space (m + 1) | horizontal z ∈ B ∧ z (Fin.last m) ∈ Ioo (a + δ) H'} with hVp
  have hxV : x ∈ Vp := ⟨hxB, hx1, hx2⟩
  have hVpb : ∀ z ∈ Vp, z ∉ measureTheoreticBoundary E := by
    intro z hz hzb
    have h1 := hband z hzb hz.1 (abs_lt.mpr ⟨by linarith [hz.2.1], hz.2.2⟩)
    have h2 := (abs_le.mp h1).2
    linarith [hz.2.1]
  rcases subset_measureTheoreticInterior_or_exterior
    (convex_cylinder_Ioo hBc (a + δ) H').isPreconnected hVpb with hI | hX
  · exact hI hxV
  · exfalso
    set t₀ := (max H (a + δ) + H') / 2
    have hmax : max H (a + δ) < H' := max_lt hHH' (by linarith)
    have ht₁ : max H (a + δ) < t₀ := by simp only [t₀]; linarith
    have ht₂ : t₀ < H' := by simp only [t₀]; linarith
    set p := point (horizontal x) t₀
    have hpV : p ∈ Vp := by
      refine ⟨by simpa [p, horizontal_point] using hxB, ?_, ?_⟩
      · simp only [p, last_point]; exact lt_of_le_of_lt (le_max_right _ _) ht₁
      · simp only [p, last_point]; exact ht₂
    have hpI : p ∈ measureTheoreticInterior E := by
      refine hS.mem_measureTheoreticInterior_of_top ?_ ?_ ?_
      · simpa [p, horizontal_point] using hBU hxB
      · simp only [p, last_point]; exact lt_of_le_of_lt (le_max_left _ _) ht₁
      · simp only [p, last_point]; exact ht₂
    exact Set.disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) hpI (hX hpV)

/-- **Below the band the points are exterior.** -/
theorem mem_exterior_of_band (hS : SlabTrappedRepresentation b E U H H' μ ν)
    {B : Set (Space m)} (hBc : Convex ℝ B) (hBU : B ⊆ U) {a δ : ℝ} (ha : |a| ≤ H) (hδ : 0 ≤ δ)
    (hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ B → |x (Fin.last m)| < H' →
      |x (Fin.last m) - a| ≤ δ)
    {x : Space (m + 1)} (hxB : horizontal x ∈ B) (hx1 : -H' < x (Fin.last m))
    (hx2 : x (Fin.last m) < a - δ) : x ∈ measureTheoreticExterior E := by
  have hH := hS.pos
  have hHH' := hS.lt
  have haH := abs_le.mp ha
  set Vm := {z : Space (m + 1) | horizontal z ∈ B ∧ z (Fin.last m) ∈ Ioo (-H') (a - δ)}
    with hVm
  have hxV : x ∈ Vm := ⟨hxB, hx1, hx2⟩
  have hVmb : ∀ z ∈ Vm, z ∉ measureTheoreticBoundary E := by
    intro z hz hzb
    have h1 := hband z hzb hz.1 (abs_lt.mpr ⟨hz.2.1, by linarith [hz.2.2]⟩)
    have h2 := (abs_le.mp h1).1
    linarith [hz.2.2]
  rcases subset_measureTheoreticInterior_or_exterior
    (convex_cylinder_Ioo hBc (-H') (a - δ)).isPreconnected hVmb with hI | hX
  · exfalso
    set t₀ := (min (-H) (a - δ) + -H') / 2
    have hlt : -H' < min (-H) (a - δ) := lt_min (by linarith) (by linarith)
    have ht₁ : t₀ < min (-H) (a - δ) := by simp only [t₀]; linarith
    have ht₂ : -H' < t₀ := by simp only [t₀]; linarith
    set p := point (horizontal x) t₀
    have hpV : p ∈ Vm := by
      refine ⟨by simpa [p, horizontal_point] using hxB, ?_, ?_⟩
      · simp only [p, last_point]; exact ht₂
      · simp only [p, last_point]; exact lt_of_lt_of_le ht₁ (min_le_right _ _)
    have hpX : p ∈ measureTheoreticExterior E := by
      refine hS.mem_measureTheoreticExterior_of_bot ?_ ?_ ?_
      · simpa [p, horizontal_point] using hBU hxB
      · simp only [p, last_point]; exact ht₂
      · simp only [p, last_point]; exact lt_of_lt_of_le ht₁ (min_le_left _ _)
    exact Set.disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) (hI hpV) hpX
  · exact hX hxV

end SlabTrappedRepresentation

/-- The band width of a flat configuration with excess `e`. -/
def flatBand (m : ℕ) (e : ℝ) : ℝ :=
  ((bandOscConst m * Real.sqrt e + 2 * 1 * e) / minimizerVolumeDensityConst m) ^
    ((1 : ℝ) / (m + 1))

theorem flatBand_nonneg (m : ℕ) {e : ℝ} (he : 0 ≤ e) : 0 ≤ flatBand m e := by
  unfold flatBand
  have := minimizerVolumeDensityConst_pos m
  have := bandOscConst_nonneg m
  positivity

theorem flatBand_mono (m : ℕ) {e e' : ℝ} (he : 0 ≤ e) (hee' : e ≤ e') :
    flatBand m e ≤ flatBand m e' := by
  unfold flatBand
  have hc := minimizerVolumeDensityConst_pos m
  have hb := bandOscConst_nonneg m
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  apply div_le_div_of_nonneg_right _ hc.le
  have := Real.sqrt_le_sqrt hee'
  nlinarith

theorem tendsto_flatBand (m : ℕ) : Tendsto (flatBand m) (𝓝 0) (𝓝 0) := by
  have h1 : Tendsto (fun e : ℝ ↦ (bandOscConst m * Real.sqrt e + 2 * 1 * e) /
      minimizerVolumeDensityConst m) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun e : ℝ ↦ (bandOscConst m * Real.sqrt e + 2 * 1 * e) /
        minimizerVolumeDensityConst m) := by fun_prop
    simpa using hc.tendsto 0
  have h2 : Tendsto (fun x : ℝ ↦ x ^ ((1 : ℝ) / (m + 1))) (𝓝 0) (𝓝 0) := by
    have hq : (0 : ℝ) < 1 / (m + 1) := by positivity
    have := (Real.continuousAt_rpow_const 0 ((1 : ℝ) / (m + 1)) (Or.inr hq.le)).tendsto
    rwa [Real.zero_rpow hq.ne'] at this
  exact h2.comp h1

namespace IsFlatConfig

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}

/-- **The band of a flat configuration over `B_{3/4}`.** -/
theorem band (hF : IsFlatConfig b E Ω μ ν)
    (he1 : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ 1)
    (hsmall : bandOscConst m * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) +
      2 * 1 * (projectedExcessMeasure μ ν).real (ball 0 2) <
        minimizerVolumeDensityConst m * (1 / 8) ^ (m + 1)) :
    ∃ a : ℝ, |a| ≤ flatBand m ((projectedExcessMeasure μ ν).real (ball 0 2)) ∧
      ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (3 / 4) →
        |x (Fin.last m)| < 1 →
          |x (Fin.last m) - a| ≤ flatBand m ((projectedExcessMeasure μ ν).real (ball 0 2)) := by
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  have hc0 := minimizerVolumeDensityConst_pos m
  have hpow : minimizerVolumeDensityConst m * (1 / 8 : ℝ) ^ (m + 1) ≤
      minimizerVolumeDensityConst m * (1 / 4 : ℝ) ^ (m + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) _) hc0.le
  have hgr10 := hF.min.gr10_band_width hF.slab subset_rfl hF.cyl he1 (r₀ := 1 / 4)
    (by norm_num) le_rfl (by norm_num) (hsmall.trans_le hpow)
  set a := ⨍ z in ball (0 : Space m) 1, columnSignedHeight E (1 / 2) z with ha_def
  have hV := hgr10.1
  have hU1 : ball (0 : Space m) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (3 / 4) →
      |x (Fin.last m)| < 1 → |x (Fin.last m) - a| ≤ flatBand m e := by
    intro x hx hxh hxn
    have hb := hF.min.band_width_le_of_le hF.slab hU1 hF.cyl a (ρ := 3 / 4) (r₀ := 1 / 8)
      (by norm_num) (by norm_num) (by norm_num) (hV.trans_lt hsmall) hx hxh hxn
    refine hb.trans ?_
    unfold flatBand
    exact Real.rpow_le_rpow (div_nonneg measureReal_nonneg hc0.le)
      (div_le_div_of_nonneg_right hV hc0.le) (by positivity)
  refine ⟨a, ?_, hband⟩
  have h := hband 0 hF.zero_mem (by rw [horizontal_zero]; exact mem_ball_self (by norm_num))
    (by simp)
  simpa using h

/-- **Recentring.** Around a boundary point `p` of the half cylinder, the configuration rescaled
by `1/8` is again flat, with excess at most `8^m e`. -/
theorem recenter (hF : IsFlatConfig b E Ω μ ν) {a δ : ℝ} (haδ : |a| ≤ δ) (hδ : δ < 1 / 32)
    (hband : ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (3 / 4) →
      |x (Fin.last m)| < 1 → |x (Fin.last m) - a| ≤ δ)
    {p : Space (m + 1)} (hp : p ∈ measureTheoreticBoundary E)
    (hpπ : horizontal p ∈ ball (0 : Space m) (1 / 2)) (hpn : |p (Fin.last m)| < 1 / 2) :
    IsFlatConfig b (similarity (LinearIsometryEquiv.refl ℝ (Space (m + 1))) p (1 / 8) ⁻¹' E)
        (similarity (LinearIsometryEquiv.refl ℝ (Space (m + 1))) p (1 / 8) ⁻¹' Ω)
        ((similarityMeasure μ (LinearIsometryEquiv.refl ℝ (Space (m + 1))) p (1 / 8)).restrict
          (cylinderSet (ball (0 : Space m) 2) 1))
        (fun x ↦ (LinearIsometryEquiv.refl ℝ (Space (m + 1))).symm
          (ν (similarity (LinearIsometryEquiv.refl ℝ (Space (m + 1))) p (1 / 8) x))) ∧
      (projectedExcessMeasure ((similarityMeasure μ (LinearIsometryEquiv.refl ℝ (Space (m + 1)))
          p (1 / 8)).restrict (cylinderSet (ball (0 : Space m) 2) 1))
          (fun x ↦ (LinearIsometryEquiv.refl ℝ (Space (m + 1))).symm
            (ν (similarity (LinearIsometryEquiv.refl ℝ (Space (m + 1))) p (1 / 8) x)))).real
          (ball 0 2) ≤ 8 ^ m * (projectedExcessMeasure μ ν).real (ball 0 2) := by
  set Q := LinearIsometryEquiv.refl ℝ (Space (m + 1)) with hQ_def
  set S := similarity Q p (1 / 8) with hS_def
  set T := affineIsometryHomeomorph Q p with hT_def
  set W := cylinderSet (ball (0 : Space m) 2) (1 : ℝ) with hW_def
  have hd : 1 ≤ m + 1 := by omega
  have hS := hF.slab
  have := hS.isFiniteMeasure
  have hδ0 : 0 ≤ δ := (abs_nonneg a).trans haδ
  have hpa : |p (Fin.last m) - a| ≤ δ :=
    hband p hp (ball_subset_ball (by norm_num) hpπ) (by linarith)
  have hSx : ∀ x, S x = p + (1 / 8 : ℝ) • x := fun x ↦ by
    simp [hS_def, similarity, hQ_def]
  have hπS : ∀ x, horizontal (S x) = horizontal p + (1 / 8 : ℝ) • horizontal x := fun x ↦ by
    rw [hSx]
    exact (map_add horizontalContinuousLinearMap p _).trans
      (by rw [map_smul]; rfl)
  have hnS : ∀ x, S x (Fin.last m) = p (Fin.last m) + (1 / 8) * x (Fin.last m) := fun x ↦ by
    rw [hSx]
    simp
  have hpπ' : ‖horizontal p‖ < 1 / 2 := mem_ball_zero_iff.mp hpπ
  have hpn' := abs_lt.mp hpn
  -- the image of the new cylinder
  have hSW : ∀ x ∈ W, horizontal (S x) ∈ ball (0 : Space m) (3 / 4) ∧
      |S x (Fin.last m) - p (Fin.last m)| < 1 / 8 := by
    intro x hx
    have hxπ : ‖horizontal x‖ < 2 := mem_ball_zero_iff.mp hx.1
    have hxn : |x (Fin.last m)| < 1 := abs_lt.mpr ⟨hx.2.1, hx.2.2⟩
    constructor
    · rw [hπS, mem_ball_zero_iff]
      calc ‖horizontal p + (1 / 8 : ℝ) • horizontal x‖
          ≤ ‖horizontal p‖ + ‖(1 / 8 : ℝ) • horizontal x‖ := norm_add_le _ _
        _ = ‖horizontal p‖ + 1 / 8 * ‖horizontal x‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        _ < 3 / 4 := by linarith
    · rw [hnS, add_sub_cancel_left, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
      linarith
  have hWsub : W ⊆ S ⁻¹' W := by
    intro x hx
    obtain ⟨h1, h2⟩ := hSW x hx
    have h2' := abs_lt.mp h2
    exact ⟨ball_subset_ball (by norm_num) h1, by linarith, by linarith⟩
  have hWo : IsOpen W := isOpen_cylinderSet isOpen_ball 1
  have hrep'' := (hS.rep.preimage_similarity hd Q p (by norm_num : (0 : ℝ) < 1 / 8)).restrict
    hWo hWsub
  -- trapping of the recentred configuration
  have hphase := hS.ae_mem_iff_of_band (convex_ball (0 : Space m) (3 / 4))
    (ball_subset_ball (by norm_num)) (a := a) (δ := δ) (by linarith) hδ0 hband
  have hGS := ae_comp_similarity Q p (by norm_num : (1 / 8 : ℝ) ≠ 0) hphase
  have hbot' : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) 2 →
      x (Fin.last m) ∈ Ioo (-1) (-(1 / 2)) → x ∉ S ⁻¹' E := by
    filter_upwards [hGS] with x hx hxπ hxn
    have hxW : x ∈ W := ⟨hxπ, hxn.1, by linarith [hxn.2]⟩
    obtain ⟨h1, h2⟩ := hSW x hxW
    have hlast := hnS x
    have hpa' := abs_le.mp hpa
    have hy1 : |S x (Fin.last m)| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hxn.1, hxn.2]
    have hgap : δ < |S x (Fin.last m) - a| := by
      rw [abs_of_neg (by linarith [hxn.2])]
      linarith [hxn.2]
    intro hxE
    have := (hx h1 hy1 hgap).mp hxE
    linarith [hxn.2]
  have htop' : ∀ᵐ x ∂volume, horizontal x ∈ ball (0 : Space m) 2 →
      x (Fin.last m) ∈ Ioo (1 / 2) 1 → x ∈ S ⁻¹' E := by
    filter_upwards [hGS] with x hx hxπ hxn
    have hxW : x ∈ W := ⟨hxπ, by linarith [hxn.1], hxn.2⟩
    obtain ⟨h1, h2⟩ := hSW x hxW
    have hlast := hnS x
    have hpa' := abs_le.mp hpa
    have hy1 : |S x (Fin.last m)| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hxn.1, hxn.2]
    have hgap : δ < |S x (Fin.last m) - a| := by
      rw [abs_of_pos (by linarith [hxn.1])]
      linarith [hxn.1]
    exact (hx h1 hy1 hgap).mpr (by linarith [hxn.1])
  have hzero : (0 : Space (m + 1)) ∈ measureTheoreticBoundary (S ⁻¹' E) := by
    rw [measureTheoreticBoundary_preimage_similarity E Q p (by norm_num : (0 : ℝ) < 1 / 8),
      mem_preimage]
    have h0 : similarity Q p (1 / 8) 0 = p := by simp [similarity]
    rw [h0]
    exact hp
  refine ⟨⟨hF.min.preimage_similarity hd Q p (by norm_num),
    ⟨hS.measurableSet.preimage (continuous_similarity Q p _).measurable, isOpen_ball,
      by norm_num, by norm_num, hrep'', hbot', htop'⟩,
    hWsub.trans (preimage_mono hF.cyl), hzero⟩, ?_⟩
  -- the excess
  have := hrep''.isFiniteMeasure
  have hπB : MeasurableSet (horizontal ⁻¹' ball (0 : Space m) 2 : Set (Space (m + 1))) :=
    measurableSet_ball.preimage continuous_horizontal.measurable
  have hWπ : horizontal ⁻¹' ball (0 : Space m) 2 ∩ W = W :=
    inter_eq_right.mpr fun x hx ↦ hx.1
  set ν' : Space (m + 1) → Space (m + 1) := fun x ↦ Q.symm (ν (S x)) with hν'_def
  have hν'n : ∀ y, ν' ((1 / 8 : ℝ)⁻¹ • T.symm y) (Fin.last m) = ν y (Fin.last m) := by
    intro y
    have hSy : S ((1 / 8 : ℝ)⁻¹ • T.symm y) = y :=
      similarity_inv_apply Q p (by norm_num : (1 / 8 : ℝ) ≠ 0) y
    show (LinearIsometryEquiv.refl ℝ (Space (m + 1))).symm (ν (S ((1 / 8 : ℝ)⁻¹ • T.symm y)))
      (Fin.last m) = ν y (Fin.last m)
    rw [hSy]
    rfl
  have hexc : (projectedExcessMeasure ((similarityMeasure μ Q p (1 / 8)).restrict W) ν').real
      (ball 0 2) = ((1 / 8 : ℝ) ^ m)⁻¹ * ∫ y, W.indicator (fun x ↦ 1 - ν' x (Fin.last m))
        ((1 / 8 : ℝ)⁻¹ • T.symm y) ∂μ := by
    rw [projectedExcessMeasure_real_eq_setIntegral hrep''.integrable hrep''.norm_eq_one
      measurableSet_ball, Measure.restrict_restrict hπB, hWπ,
      ← integral_indicator hWo.measurableSet,
      integral_similarityMeasure μ Q p (by norm_num : (0 : ℝ) < 1 / 8), Nat.add_sub_cancel]
  rw [hexc, projectedExcessMeasure_real_eq_setIntegral hS.rep.integrable hS.rep.norm_eq_one
    measurableSet_ball]
  have hg_int : Integrable (fun y ↦ 1 - ν y (Fin.last m)) μ := by
    have h : Integrable (fun x ↦ 1 - inner ℝ (ν x) (verticalDirection m)) μ :=
      (integrable_const 1).sub (hS.rep.integrable.inner_const _)
    simpa only [inner_verticalDirection_right] using h
  have hg_nonneg := ae_one_sub_last_nonneg hS.rep.norm_eq_one
  have hcmp : ∫ y, W.indicator (fun x ↦ 1 - ν' x (Fin.last m)) ((1 / 8 : ℝ)⁻¹ • T.symm y) ∂μ ≤
      ∫ y in horizontal ⁻¹' ball (0 : Space m) 2, (1 - ν y (Fin.last m)) ∂μ := by
    rw [← integral_indicator hπB]
    refine integral_mono_of_nonneg ?_ (hg_int.indicator hπB) ?_
    · filter_upwards [hg_nonneg] with y hy
      by_cases hx : (1 / 8 : ℝ)⁻¹ • T.symm y ∈ W
      · rw [indicator_of_mem hx, hν'n]
        exact hy.1
      · rw [indicator_of_notMem hx]
        exact le_rfl
    · filter_upwards [hg_nonneg] with y hy
      by_cases hx : (1 / 8 : ℝ)⁻¹ • T.symm y ∈ W
      · have hSy : S ((1 / 8 : ℝ)⁻¹ • T.symm y) = y :=
          similarity_inv_apply Q p (by norm_num : (1 / 8 : ℝ) ≠ 0) y
        have hyB : y ∈ horizontal ⁻¹' ball (0 : Space m) 2 := by
          have := (hSW _ hx).1
          rw [hSy] at this
          exact ball_subset_ball (by norm_num) this
        rw [indicator_of_mem hx, indicator_of_mem hyB, hν'n]
      · rw [indicator_of_notMem hx]
        by_cases hyB : y ∈ horizontal ⁻¹' ball (0 : Space m) 2
        · rw [indicator_of_mem hyB]
          exact hy.1
        · rw [indicator_of_notMem hyB]
  have h8 : ((1 / 8 : ℝ) ^ m)⁻¹ = 8 ^ m := by
    rw [one_div, inv_pow, inv_inv]
  rw [h8]
  exact mul_le_mul_of_nonneg_left hcmp (by positivity)

end IsFlatConfig

end SerrinEpigraph
