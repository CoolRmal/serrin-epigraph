module

public import SerrinEpigraph.ExcessGradientBound

/-!
# Excess controls the band width (`GR10`)

Normalized setting of `GR9`: the cylinder base contains `B_2` and `e = ε(B_2) ≤ 1`. Let
`a = g_{B_1}` be the average of the signed height over the unit ball.

* `SlabTrappedRepresentation.integral_abs_sub_average_unitBall_le`:
  `∫_{B_1} |g - a| ≤ C √e` (BV Poincaré and `GR9.1`).
* `SlabTrappedRepresentation.volume_real_halfspaceDiscrepancy_le`: inside the cylinder over `B_1`, the
  phase differs from the half-space `{t > a}` on a set of measure at most `∫_{B_1}|g - a| + 2H' e`
  (single-layer columns contribute `|g - a|`, multi-layer columns have measure at most `e`).
* `IsLocalPerimeterMinimizer.band_width_aux` / `band_width_le` (`GR10.1`): by the two-phase
  volume density bounds, every measure-theoretic boundary point `x` of a minimizer over `B_{1/2}`
  satisfies `c (min |x_n - a| r₀)^(m+1) ≤ C √e`, hence `|x_n - a| ≤ (C √e / c)^(1/(m+1))` once the
  right-hand side is below the threshold `c r₀^(m+1)`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported NNReal

namespace SerrinEpigraph

/-- The dimensional constant of `∫_{B_1} |g - a| ≤ C √e`. -/
def bandOscConst (m : ℕ) : ℝ :=
  2 ^ (m + 1) * Real.sqrt (2 * (2 ^ m * volume.real (ball (0 : Space m) 1) + 1))

theorem bandOscConst_nonneg (m : ℕ) : 0 ≤ bandOscConst m := by
  unfold bandOscConst
  positivity

/-- The symmetric difference of the phase and the half-space `{t > a}` inside the cylinder over
`B_1`. -/
def halfspaceDiscrepancy {m : ℕ} (E : Set (Space (m + 1))) (H' a : ℝ) : Set (Space (m + 1)) :=
  {x ∈ cylinderSet (ball (0 : Space m) 1) H' | ¬(x ∈ E ↔ a < x (Fin.last m))}

theorem measurableSet_halfspaceDiscrepancy {m : ℕ} {E : Set (Space (m + 1))}
    (hE : MeasurableSet E) (H' a : ℝ) : MeasurableSet (halfspaceDiscrepancy E H' a) := by
  have hlast : Measurable fun x : Space (m + 1) ↦ x (Fin.last m) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous.measurable
  have hA : MeasurableSet {x : Space (m + 1) | a < x (Fin.last m)} :=
    measurableSet_lt measurable_const hlast
  have heq : halfspaceDiscrepancy E H' a = cylinderSet (ball (0 : Space m) 1) H' ∩
      ((E \ {x | a < x (Fin.last m)}) ∪ ({x | a < x (Fin.last m)} \ E)) := by
    ext x
    simp only [halfspaceDiscrepancy, mem_ofPred_eq, mem_inter_iff, mem_union, Set.mem_sdiff]
    tauto
  rw [heq]
  exact (measurableSet_cylinderSet measurableSet_ball H').inter
    ((hE.diff hA).union (hA.diff hE))

theorem integral_indicator_const_one {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {s : Set X} (hs : MeasurableSet s) : ∫ x, s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ = μ.real s :=
  integral_indicator_one hs

theorem halfspaceDiscrepancy_subset {m : ℕ} (E : Set (Space (m + 1))) (H' a : ℝ) :
    halfspaceDiscrepancy E H' a ⊆ cylinderSet (ball (0 : Space m) 1) H' :=
  fun _ hx ↦ hx.1

theorem volume_cylinderSet_ball_lt_top {m : ℕ} (y₀ : Space m) (r H' : ℝ) :
    volume (cylinderSet (ball y₀ r) H') < ⊤ := by
  have hmp := measurePreserving_horizontal_last m
  have hsub : cylinderSet (ball y₀ r) H' ⊆
      (fun x : Space (m + 1) ↦ (horizontal x, x (Fin.last m))) ⁻¹' (ball y₀ r ×ˢ Ioo (-H') H') :=
    fun x hx ↦ hx
  refine (measure_mono hsub).trans_lt ?_
  rw [hmp.measure_preimage (measurableSet_ball.prod measurableSet_Ioo).nullMeasurableSet,
    Measure.prod_prod, Real.volume_Ioo]
  exact ENNReal.mul_lt_top measure_ball_lt_top ENNReal.ofReal_lt_top

theorem horizontal_sub_eq {m : ℕ} (z x : Space (m + 1)) :
    horizontal (z - x) = horizontal z - horizontal x :=
  map_sub horizontalContinuousLinearMap z x

namespace SlabTrappedRepresentation

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **`L¹` oscillation on the unit ball** (`GR10`): `∫_{B_1} |g - g_{B_1}| ≤ C √e`. -/
theorem integral_abs_sub_average_unitBall_le
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    (he1 : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ 1) :
    ∫ y in ball (0 : Space m) 1,
        |columnSignedHeight E H y - ⨍ z in ball (0 : Space m) 1, columnSignedHeight E H z| ≤
      bandOscConst m * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) := by
  have hP := integral_abs_columnSignedHeight_sub_average_le hS.measurableSet hS.isOpen hS.pos
    hS.lt hS.rep hS.bot hS.top (y₀ := 0) (r := 1) (R := 2) one_pos one_lt_two hU2
  have hM := integral_norm_horizontal_normal_le hS.measurableSet hS.isOpen hS.pos hS.lt hS.rep
    hS.bot hS.top measurableSet_ball hU2
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  set V₁ := volume.real (ball (0 : Space m) 1) with hV₁_def
  have he0 : 0 ≤ e := measureReal_nonneg
  have hV₂ : volume.real (ball (0 : Space m) 2) = 2 ^ m * V₁ := by
    have h := volume_real_ball_mul (0 : Space m) 0 (r := 1) (c := 2) one_pos two_pos
    rwa [mul_one] at h
  have hsq : Real.sqrt (2 * e * (volume.real (ball (0 : Space m) 2) + e)) ≤
      Real.sqrt e * Real.sqrt (2 * (2 ^ m * V₁ + 1)) := by
    rw [← Real.sqrt_mul he0]
    apply Real.sqrt_le_sqrt
    rw [hV₂]
    have hV : 0 ≤ 2 ^ m * V₁ := by positivity
    nlinarith
  calc
    _ ≤ 2 ^ (m + 1) * 1 * ∫ x in horizontal ⁻¹' ball (0 : Space m) 2, ‖horizontal (ν x)‖ ∂μ := hP
    _ ≤ 2 ^ (m + 1) * 1 * (Real.sqrt e * Real.sqrt (2 * (2 ^ m * V₁ + 1))) :=
      mul_le_mul_of_nonneg_left (hM.trans hsq) (by positivity)
    _ = bandOscConst m * Real.sqrt e := by
      rw [bandOscConst]
      ring

/-- **The phase is close to a half-space** (`GR10`): inside the cylinder over `B_1`,
`|E Δ {t > a}| ≤ ∫_{B_1} |g - a| + 2 H' ε(B_1)` for every level `|a| ≤ H`. -/
theorem volume_real_halfspaceDiscrepancy_le
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU1 : ball (0 : Space m) 1 ⊆ U)
    (a : ℝ) :
    volume.real (halfspaceDiscrepancy E H' a) ≤
      (∫ y in ball (0 : Space m) 1, |columnSignedHeight E H y - a|) +
        2 * H' * (projectedExcessMeasure μ ν).real (ball 0 1) := by
  set g := columnSignedHeight E H with hg_def
  set ε := projectedExcessMeasure μ ν with hε_def
  have := hS.isFiniteMeasure
  have := hS.isFiniteMeasure_excess
  set D := halfspaceDiscrepancy E H' a with hD_def
  set B₁ : Set (Space m) := ball 0 1 with hB₁_def
  set M := multiLayerColumns E U H H' with hM_def
  have hDm : MeasurableSet D := measurableSet_halfspaceDiscrepancy hS.measurableSet H' a
  have hDfin : volume D < ⊤ :=
    (measure_mono (halfspaceDiscrepancy_subset E H' a)).trans_lt
      (volume_cylinderSet_ball_lt_top 0 1 H')
  have hMm : MeasurableSet M :=
    measurableSet_multiLayerColumns hS.measurableSet hS.isOpen.measurableSet H H'
  have hH'0 : 0 < H' := hS.pos.trans hS.lt
  have hint : Integrable (D.indicator fun _ ↦ (1 : ℝ)) volume :=
    (integrableOn_const hDfin.ne).integrable_indicator hDm
  rw [← integral_indicator_const_one hDm, integral_space_eq_integral_horizontal_vertical hint]
  set ψ : Space m → ℝ := fun y ↦ B₁.indicator (fun y ↦ |g y - a|) y +
    2 * H' * (M ∩ B₁).indicator (fun _ ↦ (1 : ℝ)) y with hψ_def
  have habsint : IntegrableOn (fun y ↦ |g y - a|) B₁ :=
    ((integrableOn_columnSignedHeight_ball hS.measurableSet hS.pos.le 0 1).sub
      (integrableOn_const measure_ball_ne_top)).abs
  have hMBint : Integrable ((M ∩ B₁).indicator fun _ ↦ (1 : ℝ)) volume :=
    (integrableOn_const (measure_ne_top_of_subset inter_subset_right
      measure_ball_ne_top)).integrable_indicator (hMm.inter measurableSet_ball)
  have hψint : Integrable ψ volume :=
    (habsint.integrable_indicator measurableSet_ball).add (hMBint.const_mul _)
  have hφnonneg : 0 ≤ᵐ[volume] fun y : Space m ↦ ∫ t, D.indicator (fun _ ↦ (1 : ℝ)) (point y t) :=
    Eventually.of_forall fun y ↦ integral_nonneg fun t ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hIoo : ∀ y, ∫ t, D.indicator (fun _ ↦ (1 : ℝ)) (point y t) ≤ 2 * H' := by
    intro y
    calc
      ∫ t, D.indicator (fun _ ↦ (1 : ℝ)) (point y t) ≤
          ∫ t, (Ioo (-H') H').indicator (fun _ ↦ (1 : ℝ)) t := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t ↦
          indicator_nonneg (fun _ _ ↦ zero_le_one) _)
          ((integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator
            measurableSet_Ioo) (Eventually.of_forall fun t ↦ ?_)
        show D.indicator (fun _ ↦ (1 : ℝ)) (point y t) ≤
          (Ioo (-H') H').indicator (fun _ ↦ (1 : ℝ)) t
        by_cases hpt : point y t ∈ D
        · have ht : t ∈ Ioo (-H') H' := by
            have := (halfspaceDiscrepancy_subset E H' a hpt).2
            rwa [last_point] at this
          rw [indicator_of_mem hpt, indicator_of_mem ht]
        · rw [indicator_of_notMem hpt]
          exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
      _ = 2 * H' := by
        rw [integral_indicator_const_one measurableSet_Ioo, Real.volume_real_Ioo_of_le (by linarith)]
        ring
  have hbound : ∀ y, ∫ t, D.indicator (fun _ ↦ (1 : ℝ)) (point y t) ≤ ψ y := by
    intro y
    by_cases hyB : y ∈ B₁
    · by_cases hyM : y ∈ M
      · have h1 := hIoo y
        have h2 : 0 ≤ |g y - a| := abs_nonneg _
        simp only [hψ_def, indicator_of_mem hyB, indicator_of_mem (show y ∈ M ∩ B₁ from ⟨hyM, hyB⟩),
          mul_one]
        linarith
      · -- single layer column
        have hyU : y ∈ U := hU1 hyB
        have hsl : ∀ᵐ t ∂volume.restrict (Ioo (-H') H'),
            E.indicator (fun _ ↦ (1 : ℝ)) (point y t) =
              (Ioi (g y)).indicator (fun _ ↦ (1 : ℝ)) t := by
          by_contra hn
          exact hyM ⟨hyU, hn⟩
        have hsl' := (ae_restrict_iff' measurableSet_Ioo).mp hsl
        set lo := min (g y) a with hlo
        set hi := max (g y) a with hhi
        have hle : ∫ t, D.indicator (fun _ ↦ (1 : ℝ)) (point y t) ≤
            ∫ t, (Ioc lo hi).indicator (fun _ ↦ (1 : ℝ)) t := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t ↦
            indicator_nonneg (fun _ _ ↦ zero_le_one) _)
            ((integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
              measurableSet_Ioc) ?_
          filter_upwards [hsl'] with t ht
          by_cases hpt : point y t ∈ D
          · have htI : t ∈ Ioo (-H') H' := by
              have := (halfspaceDiscrepancy_subset E H' a hpt).2
              rwa [last_point] at this
            have hiff : point y t ∈ E ↔ g y < t := by
              have h1 := ht htI
              by_cases hE : point y t ∈ E <;> by_cases hlt : g y < t
              · exact ⟨fun _ ↦ hlt, fun _ ↦ hE⟩
              · rw [indicator_of_mem hE, indicator_of_notMem (show t ∉ Ioi (g y) from hlt)] at h1
                exact absurd h1 one_ne_zero
              · rw [indicator_of_notMem hE, indicator_of_mem (show t ∈ Ioi (g y) from hlt)] at h1
                exact absurd h1.symm one_ne_zero
              · exact ⟨fun h ↦ absurd h hE, fun h ↦ absurd h hlt⟩
            have hnot : ¬(g y < t ↔ a < t) := by
              have := hpt.2
              rwa [hiff, last_point] at this
            have htIoc : t ∈ Ioc lo hi := by
              by_cases h1 : g y < t
              · have h2 : t ≤ a := not_lt.mp fun h ↦ hnot ⟨fun _ ↦ h, fun _ ↦ h1⟩
                exact ⟨(min_le_left _ _).trans_lt h1, h2.trans (le_max_right _ _)⟩
              · have h2 : a < t := by
                  by_contra h3
                  exact hnot ⟨fun h ↦ absurd h h1, fun h ↦ absurd h h3⟩
                exact ⟨(min_le_right _ _).trans_lt h2, (not_lt.mp h1).trans (le_max_left _ _)⟩
            rw [indicator_of_mem hpt, indicator_of_mem htIoc]
          · rw [indicator_of_notMem hpt]
            exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
        have hIoc : ∫ t, (Ioc lo hi).indicator (fun _ ↦ (1 : ℝ)) t = |g y - a| := by
          rw [integral_indicator_const_one measurableSet_Ioc, Real.volume_real_Ioc_of_le
            (min_le_max)]
          rcases le_total (g y) a with h | h
          · rw [min_eq_left h, max_eq_right h, abs_sub_comm, abs_of_nonneg (by linarith)]
          · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
        have hyMB : y ∉ M ∩ B₁ := fun h ↦ hyM h.1
        simp only [hψ_def, indicator_of_mem hyB, indicator_of_notMem hyMB, mul_zero, add_zero]
        linarith
    · have h0 : ∫ t, D.indicator (fun _ ↦ (1 : ℝ)) (point y t) = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
        have hpt : point y t ∉ D := fun h ↦ hyB (by
          have := (halfspaceDiscrepancy_subset E H' a h).1
          rwa [horizontal_point] at this)
        simp [indicator_of_notMem hpt]
      rw [h0]
      have h1 : 0 ≤ (M ∩ B₁).indicator (fun _ ↦ (1 : ℝ)) y :=
        indicator_nonneg (fun _ _ ↦ zero_le_one) _
      simp only [hψ_def, indicator_of_notMem hyB]
      positivity
  calc
    ∫ y, ∫ t, D.indicator (fun _ ↦ (1 : ℝ)) (point y t) ≤ ∫ y, ψ y :=
      integral_mono_of_nonneg hφnonneg hψint (Eventually.of_forall hbound)
    _ = (∫ y in B₁, |g y - a|) + 2 * H' * volume.real (M ∩ B₁) := by
      rw [hψ_def, integral_add (habsint.integrable_indicator measurableSet_ball)
        (hMBint.const_mul _), integral_indicator measurableSet_ball, integral_const_mul,
        integral_indicator_const_one (hMm.inter measurableSet_ball)]
    _ ≤ (∫ y in B₁, |g y - a|) + 2 * H' * ε.real B₁ := by
      have hvM := volume_multiLayerColumns_inter_le b hS.measurableSet hS.isOpen hS.pos hS.lt μ
        hS.rep.measure_compl hS.rep.measure_open hS.rep.integrable hS.rep.norm_eq_one
        hS.rep.dist hS.bot hS.top measurableSet_ball hU1
      have h1 : volume.real (M ∩ B₁) ≤ ε.real (M ∩ B₁) :=
        ENNReal.toReal_mono (measure_ne_top _ _) hvM
      have h2 : ε.real (M ∩ B₁) ≤ ε.real B₁ := measureReal_mono inter_subset_right
      have h3 : 0 ≤ 2 * H' := by linarith
      nlinarith

/-- Measure-theoretic boundary points over the cylinder base lie in the trapping slab. -/
theorem abs_last_le_of_mem_measureTheoreticBoundary
    (hS : SlabTrappedRepresentation b E U H H' μ ν) {x : Space (m + 1)}
    (hx : x ∈ measureTheoreticBoundary E) (hxU : horizontal x ∈ U)
    (hxn : |x (Fin.last m)| < H') : |x (Fin.last m)| ≤ H := by
  have hlast : Continuous fun z : Space (m + 1) ↦ z (Fin.last m) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous
  by_contra hgt
  push Not at hgt
  rcases le_or_gt 0 (x (Fin.last m)) with hpos | hneg
  · rw [abs_of_nonneg hpos] at hgt hxn
    set O := {z : Space (m + 1) | horizontal z ∈ U ∧ z (Fin.last m) ∈ Ioo H H'}
    have hO : IsOpen O :=
      (hS.isOpen.preimage continuous_horizontal).inter (isOpen_Ioo.preimage hlast)
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO x ⟨hxU, hgt, hxn⟩
    apply (hx r hr).2
    refine measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp hS.top)
    intro h
    exact hz.2 (h (hrO hz.1).1 (hrO hz.1).2)
  · rw [abs_of_neg hneg] at hgt hxn
    set O := {z : Space (m + 1) | horizontal z ∈ U ∧ z (Fin.last m) ∈ Ioo (-H') (-H)}
    have hO : IsOpen O :=
      (hS.isOpen.preimage continuous_horizontal).inter (isOpen_Ioo.preimage hlast)
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO x ⟨hxU, by linarith, by linarith⟩
    apply (hx r hr).1
    refine measure_mono_null (fun z hz ↦ ?_) (ae_iff.mp hS.bot)
    intro h
    exact h (hrO hz.2).1 (hrO hz.2).2 hz.1

end SlabTrappedRepresentation

/-! ### The band width (`GR10.1`) -/

namespace IsLocalPerimeterMinimizer

variable {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
  {E Ω : Set (Space (m + 1))} {U : Set (Space m)} {H H' : ℝ} {μ : Measure (Space (m + 1))}
  {ν : Space (m + 1) → Space (m + 1)}

/-- **Band width, density form** (`GR10`): a measure-theoretic boundary point `x` of a minimizer
over `B_{1/2}` at height distance `h = |x_n - a|` from the level `a` forces
`c (min h r₀)^(m+1) ≤ |E Δ {t > a}|` (inside the cylinder over `B_1`), by the two-phase volume
density bounds on the ball `B_{min h r₀}(x)`, which lies on one side of `{t = a}`. -/
theorem band_width_aux (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU1 : ball (0 : Space m) 1 ⊆ U)
    (hcyl : cylinderSet U H' ⊆ Ω) (a : ℝ) {x : Space (m + 1)}
    (hx : x ∈ measureTheoreticBoundary E) (hxh : horizontal x ∈ ball (0 : Space m) (1 / 2))
    (hxn : |x (Fin.last m)| < H') {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 4)
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
  have hxU : horizontal x ∈ U := hU1 (ball_subset_ball (by norm_num) hxh)
  have hxH := hS.abs_last_le_of_mem_measureTheoreticBoundary hx hxU hxn
  have hxh' : dist (horizontal x) 0 < 1 / 2 := hxh
  -- the closed ball lies in the cylinder over `B_1`
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
  · -- below the level: the wrong phase is `E`
    have habs : h = a - x (Fin.last m) := by rw [hh_def, abs_of_neg hneg]; ring
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
  · -- above the level: the wrong phase is the complement
    have habs : h = x (Fin.last m) - a := by rw [hh_def, abs_of_pos hposa]
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

/-- **Band width** (`GR10.1`): if `|E Δ {t > a}|` (inside the cylinder over `B_1`) is below the
threshold `c r₀^(m+1)`, every measure-theoretic boundary point over `B_{1/2}` satisfies
`|x_n - a| ≤ (|E Δ {t > a}| / c)^(1/(m+1))`. -/
theorem band_width_le (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU1 : ball (0 : Space m) 1 ⊆ U)
    (hcyl : cylinderSet U H' ⊆ Ω) (a : ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 4)
    (hr₀H : r₀ ≤ (H' - H) / 2)
    (hsmall : volume.real (halfspaceDiscrepancy E H' a) <
      minimizerVolumeDensityConst m * r₀ ^ (m + 1))
    {x : Space (m + 1)} (hx : x ∈ measureTheoreticBoundary E)
    (hxh : horizontal x ∈ ball (0 : Space m) (1 / 2)) (hxn : |x (Fin.last m)| < H') :
    |x (Fin.last m) - a| ≤
      (volume.real (halfspaceDiscrepancy E H' a) / minimizerVolumeDensityConst m) ^
        ((1 : ℝ) / (m + 1)) := by
  have haux := hmin.band_width_aux hS hU1 hcyl a hx hxh hxn hr₀ hr₀1 hr₀H
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

/-- **`GR10` in the normalized setting.** With `a = g_{B_1}` and `e = ε(B_2) ≤ 1`, the phase
differs from `{t > a}` inside the cylinder over `B_1` on a set of measure at most
`S(e) = C √e + 2H' e`; if `S(e) < c r₀^(m+1)`, every measure-theoretic boundary point over
`B_{1/2}` lies in the band `|x_n - a| ≤ (S(e)/c)^(1/(m+1))`. -/
theorem gr10_band_width (hmin : IsLocalPerimeterMinimizer b E Ω)
    (hS : SlabTrappedRepresentation b E U H H' μ ν) (hU2 : ball (0 : Space m) 2 ⊆ U)
    (hcyl : cylinderSet U H' ⊆ Ω)
    (he1 : (projectedExcessMeasure μ ν).real (ball 0 2) ≤ 1) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hr₀1 : r₀ ≤ 1 / 4) (hr₀H : r₀ ≤ (H' - H) / 2)
    (hsmall : bandOscConst m * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) +
      2 * H' * (projectedExcessMeasure μ ν).real (ball 0 2) <
        minimizerVolumeDensityConst m * r₀ ^ (m + 1)) :
    volume.real (halfspaceDiscrepancy E H'
        (⨍ z in ball (0 : Space m) 1, columnSignedHeight E H z)) ≤
      bandOscConst m * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) +
        2 * H' * (projectedExcessMeasure μ ν).real (ball 0 2) ∧
    ∀ x ∈ measureTheoreticBoundary E, horizontal x ∈ ball (0 : Space m) (1 / 2) →
      |x (Fin.last m)| < H' →
      |x (Fin.last m) - ⨍ z in ball (0 : Space m) 1, columnSignedHeight E H z| ≤
        ((bandOscConst m * Real.sqrt ((projectedExcessMeasure μ ν).real (ball 0 2)) +
          2 * H' * (projectedExcessMeasure μ ν).real (ball 0 2)) /
            minimizerVolumeDensityConst m) ^ ((1 : ℝ) / (m + 1)) := by
  set e := (projectedExcessMeasure μ ν).real (ball (0 : Space m) 2) with he_def
  set a := ⨍ z in ball (0 : Space m) 1, columnSignedHeight E H z with ha_def
  have := hS.isFiniteMeasure_excess
  have hU1 : ball (0 : Space m) 1 ⊆ U := (ball_subset_ball (by norm_num)).trans hU2
  have hH'0 : 0 < H' := hS.pos.trans hS.lt
  have hosc := hS.integral_abs_sub_average_unitBall_le hU2 he1
  have hdisc := hS.volume_real_halfspaceDiscrepancy_le hU1 a
  have hε1 : (projectedExcessMeasure μ ν).real (ball (0 : Space m) 1) ≤ e :=
    measureReal_mono (ball_subset_ball (by norm_num)) (measure_ne_top _ _)
  have hV : volume.real (halfspaceDiscrepancy E H' a) ≤ bandOscConst m * Real.sqrt e + 2 * H' * e := by
    have h2 : 2 * H' * (projectedExcessMeasure μ ν).real (ball (0 : Space m) 1) ≤ 2 * H' * e :=
      mul_le_mul_of_nonneg_left hε1 (by linarith)
    linarith
  refine ⟨hV, fun x hx hxh hxn ↦ ?_⟩
  have hc0 := minimizerVolumeDensityConst_pos m
  have hb := hmin.band_width_le hS hU1 hcyl a hr₀ hr₀1 hr₀H (hV.trans_lt hsmall) hx hxh hxn
  refine hb.trans (Real.rpow_le_rpow (div_nonneg measureReal_nonneg hc0.le)
    (div_le_div_of_nonneg_right hV hc0.le) (by positivity))

end IsLocalPerimeterMinimizer

end SerrinEpigraph
