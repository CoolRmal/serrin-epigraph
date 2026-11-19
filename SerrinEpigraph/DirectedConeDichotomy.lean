module

public import SerrinEpigraph.DirectedConeJacobi
public import SerrinEpigraph.DirectionalInvariance
public import SerrinEpigraph.DimensionReduction

/-!
# The cone dichotomy for directed minimizing cones

**Main theorem** (`IsDirectedMinimizingCone.halfspace_or_verticalInvariant_of_hyps`). Given
ε-regularity, upper semicontinuity of singular sets, Simons' theorem in dimensions `2, …, 7` and
the smoothness of `C¹` boundary points (`C1RegularSmoothHyp`), a directed minimizing cone
`E ⊆ Space (m + 1)` is a.e. a half-space or a.e. invariant under vertical translations.

This is §5A of `docs/rigidity-proof/one-sided.md`. In dimension at most seven the cone is a
half-space by the classification of minimizing cones. Otherwise, by steps A–C
(`IsDirectedMinimizingCone.sqNorm_mul_inner_vertical_eq_zero`), `|A|² ⟪ν, eₙ⟫ = 0` at every regular
boundary point, while `⟪ν, eₙ⟫ ≥ 0` by vertical monotonicity.

* **Step D** (`IsDirectedMinimizingCone.ae_eq_positiveHalfspace_of_inner_pos`). If
  `⟪ν(x₀), eₙ⟫ > 0` at some regular point, the boundary is flat near `x₀` and lies in the
  hyperplane `P = ν(x₀)^⊥` (the position vector is tangent). The set of points of `P` near which
  `E` is a.e. the half-space `H = {⟪ν(x₀), ·⟫ > 0}` is relatively open and closed in `P \ Sing E`
  (at a limit point the normal is still `ν(x₀)`, so the vertical component is positive and the
  boundary is flat there), and `P \ Sing E` is connected because the singular set has vanishing
  `μH[m - 1]` measure. Finally the vertical lines over the complement of a null cylinder cross `P`
  at regular points, and vertical monotonicity sweeps the local information to `E =ᵐ H`.
* **Step E** (`IsDirectedMinimizingCone.verticalInvariant_of_inner_eq_zero`). If `⟪ν, eₙ⟫ = 0` at
  every regular point, the perimeter measure is concentrated on the regular part where its polar
  vector is the chart normal, so `∫_E ∂ₙ φ = 0` for all test functions and `E` is vertically
  invariant (`ae_mem_iff_add_smul_mem_of_integral_fderiv_eq_zero`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff ENNReal NNReal

namespace SerrinEpigraph

/-! ### 1. Null vertical cylinders -/

/-- In `Space k`, sets of vanishing `k`-dimensional Hausdorff measure are Lebesgue null. -/
theorem volume_eq_zero_of_hausdorffMeasure_eq_zero {k : ℕ} {A : Set (Space k)}
    (hA : μH[(k : ℝ)] A = 0) : volume A = 0 := by
  set B : Set (Fin k → ℝ) := WithLp.ofLp '' A with hB
  have hB0 : μH[(k : ℝ)] B = 0 := by
    have h1 := (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin k ↦ ℝ)).hausdorffMeasure_image_le
      (Nat.cast_nonneg k) A
    rw [hA, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  have hBv : volume B = 0 := by
    have h3 : (μH[(Fintype.card (Fin k) : ℝ)] : Measure (Fin k → ℝ)) = volume :=
      hausdorffMeasure_pi_real
    rw [Fintype.card_fin] at h3
    rw [← h3]
    exact hB0
  have hT : volume (WithLp.ofLp ⁻¹' toMeasurable volume B : Set (Space k)) = 0 := by
    rw [(PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
      (measurableSet_toMeasurable volume B).nullMeasurableSet, measure_toMeasurable, hBv]
  exact measure_mono_null (fun x hx ↦ subset_toMeasurable volume B ⟨x, hx, rfl⟩) hT

private theorem horizontal_sub_aux' {k : ℕ} (x y : Space (k + 1)) :
    horizontal (x - y) = horizontal x - horizontal y := by
  ext i
  simp [horizontal]

private theorem norm_horizontal_le_aux' {k : ℕ} (x : Space (k + 1)) : ‖horizontal x‖ ≤ ‖x‖ := by
  have h : ‖x‖ ^ 2 = ‖horizontal x‖ ^ 2 + x (Fin.last k) ^ 2 := by
    conv_lhs => rw [← point_horizontal_last x]
    rw [← real_inner_self_eq_norm_sq, inner_point_point, real_inner_self_eq_norm_sq]
    ring
  have h2 : ‖horizontal x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg (x (Fin.last k))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

private theorem lipschitzWith_horizontal_aux (k : ℕ) :
    LipschitzWith 1 (horizontal : Space (k + 1) → Space k) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, ← horizontal_sub_aux', NNReal.coe_one, one_mul]
  exact norm_horizontal_le_aux' _

private theorem horizontal_add_smul_vertical_aux {k : ℕ} (x : Space (k + 1)) (τ : ℝ) :
    horizontal (x + τ • verticalDirection k) = horizontal x := by
  ext i
  simp [horizontal, verticalDirection]

/-- The union of the vertical lines through a `μH[m]`-null subset of `Space (m + 1)` is Lebesgue
null. -/
theorem volume_setOf_add_smul_vertical_mem_eq_zero {m : ℕ} {S : Set (Space (m + 1))}
    (hS : μH[(m : ℝ)] S = 0) :
    volume {z : Space (m + 1) | ∃ τ : ℝ, z + τ • verticalDirection m ∈ S} = 0 := by
  have hh : μH[(m : ℝ)] (horizontal '' S) = 0 := by
    have h1 := (lipschitzWith_horizontal_aux m).hausdorffMeasure_image_le (Nat.cast_nonneg m) S
    rw [hS, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  refine measure_mono_null (fun z hz ↦ ?_)
    (volume_preimage_horizontal_eq_zero (volume_eq_zero_of_hausdorffMeasure_eq_zero hh))
  obtain ⟨τ, hτ⟩ := hz
  exact ⟨z + τ • verticalDirection m, hτ, horizontal_add_smul_vertical_aux z τ⟩

/-! ### 2. The vertical sweep -/

/-- **Vertical sweep.** Let `E` be vertically monotone, let `P = {⟪ν, ·⟫ = 0}` be a hyperplane
which is not vertical, `⟪ν, eₙ⟫ > 0`, and let `S` be a set whose vertical cylinder is null. If
near every point of `P \ S` the set `E` is a.e. the half-space `{⟪ν, ·⟫ > 0}`, then `E` is a.e.
this half-space. -/
theorem ae_eq_positiveHalfspace_of_forall_hyperplane {m : ℕ} {E : Set (Space (m + 1))}
    (hmono : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • verticalDirection m ∈ E)
    {ν : Space (m + 1)} (ha : 0 < inner ℝ ν (verticalDirection m)) {S : Set (Space (m + 1))}
    (hS : volume {z : Space (m + 1) | ∃ τ : ℝ, z + τ • verticalDirection m ∈ S} = 0)
    (hgood : ∀ p, inner ℝ ν p = 0 → p ∉ S →
      ∃ r > 0, ∀ᵐ z ∂volume, z ∈ ball p r → (z ∈ E ↔ z ∈ positiveHalfspace ν)) :
    E =ᵐ[volume] positiveHalfspace ν := by
  classical
  set e := verticalDirection m with he
  have he1 : ‖e‖ = 1 := by simp [he, verticalDirection]
  set a := inner ℝ ν e with hadef
  set P : Set (Space (m + 1)) := {p | inner ℝ ν p = 0} \ S with hP
  have hgood' : ∀ p ∈ P, ∃ r > 0,
      ∀ᵐ z ∂volume, z ∈ ball p r → (z ∈ E ↔ z ∈ positiveHalfspace ν) :=
    fun p hp ↦ hgood p hp.1 hp.2
  choose! rad hrad hgoodr using hgood'
  obtain ⟨T, hTP, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable P
    (fun p ↦ ball p (rad p)) (fun p _ ↦ isOpen_ball)
  have hcover : P ⊆ ⋃ p ∈ T, ball p (rad p) := by
    rw [hTU]
    intro p hp
    exact mem_biUnion hp (mem_ball_self (hrad p hp))
  -- countably many almost-everywhere statements
  have hA : ∀ᵐ z ∂volume, ∀ p ∈ T, ∀ q : ℚ,
      (z - (q : ℝ) • e ∈ ball p (rad p) →
        (z - (q : ℝ) • e ∈ E ↔ z - (q : ℝ) • e ∈ positiveHalfspace ν)) ∧
      (z + (q : ℝ) • e ∈ ball p (rad p) →
        (z + (q : ℝ) • e ∈ E ↔ z + (q : ℝ) • e ∈ positiveHalfspace ν)) := by
    rw [ae_ball_iff hTc]
    intro p hpT
    rw [ae_all_iff]
    intro q
    have h0 := hgoodr p (hTP hpT)
    exact ((measurePreserving_sub_right volume ((q : ℝ) • e)).quasiMeasurePreserving.ae h0).and
      ((measurePreserving_add_right volume ((q : ℝ) • e)).quasiMeasurePreserving.ae h0)
  have hD : ∀ᵐ z ∂volume, ∀ q : ℚ, 0 ≤ (q : ℝ) →
      (z ∈ E → z + (q : ℝ) • e ∈ E) ∧ (z - (q : ℝ) • e ∈ E → z ∈ E) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 ≤ (q : ℝ)
    · have h1 := hmono q hq
      have h2 : ∀ᵐ z ∂volume, z - (q : ℝ) • e ∈ E → z - (q : ℝ) • e + (q : ℝ) • e ∈ E :=
        (measurePreserving_sub_right volume ((q : ℝ) • e)).quasiMeasurePreserving.ae h1
      filter_upwards [h1, h2] with z hz1 hz2 _
      exact ⟨hz1, fun h ↦ by simpa using hz2 h⟩
    · exact Eventually.of_forall fun z hq' ↦ absurd hq' hq
  have hN : ∀ᵐ z ∂volume, z ∉ {z : Space (m + 1) | ∃ τ : ℝ, z + τ • e ∈ S} :=
    measure_eq_zero_iff_ae_notMem.mp hS
  filter_upwards [hA, hD, hN] with z hzA hzD hzN
  have hzN' : ∀ τ : ℝ, z + τ • e ∉ S := fun τ hτ ↦ hzN ⟨τ, hτ⟩
  -- the point of `P` on the vertical line through `z`
  set s := inner ℝ ν z / a with hs
  set p := z - s • e with hp
  have hνp : inner ℝ ν p = 0 := by
    rw [hp, inner_sub_right, real_inner_smul_right, hs, ← hadef, div_mul_cancel₀ _ ha.ne',
      sub_self]
  have hpS : p ∉ S := by
    have := hzN' (-s)
    rwa [neg_smul, ← sub_eq_add_neg] at this
  obtain ⟨p₀, hp₀T, hpp₀⟩ := mem_iUnion₂.mp (hcover ⟨hνp, hpS⟩)
  set δ := rad p₀ - dist p p₀ with hδ
  have hδ0 : 0 < δ := by
    rw [mem_ball] at hpp₀
    linarith
  have hnear : ∀ τ : ℝ, |τ + s| < δ → z + τ • e ∈ ball p₀ (rad p₀) := by
    intro τ hτ
    rw [mem_ball]
    have hdist : dist (z + τ • e) p = |τ + s| := by
      rw [hp, dist_eq_norm]
      have : z + τ • e - (z - s • e) = (τ + s) • e := by
        rw [add_smul]
        abel
      rw [this, norm_smul, he1, mul_one, Real.norm_eq_abs]
    calc dist (z + τ • e) p₀ ≤ dist (z + τ • e) p + dist p p₀ := dist_triangle _ _ _
      _ < δ + dist p p₀ := by rw [hdist]; linarith
      _ = rad p₀ := by rw [hδ]; ring
  have hinner : ∀ τ : ℝ, inner ℝ ν (z + τ • e) = a * (τ + s) := by
    intro τ
    rw [inner_add_right, real_inner_smul_right, ← hadef, hs]
    field_simp
    ring
  rcases lt_trichotomy (inner ℝ ν z) 0 with hneg | hzero | hpos
  · -- below the hyperplane
    have hs0 : s < 0 := div_neg_of_neg_of_pos hneg ha
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (-s - δ) < -s from
      max_lt (by linarith) (by linarith))
    have hq0 : 0 ≤ (q : ℝ) := (le_max_left _ _).trans hq1.le
    have hqδ : |(q : ℝ) + s| < δ := by
      rw [abs_lt]
      constructor <;> linarith [le_max_right 0 (-s - δ)]
    have hnotH : z + (q : ℝ) • e ∉ positiveHalfspace ν := by
      show ¬ (0 < inner ℝ ν (z + (q : ℝ) • e))
      rw [hinner]
      nlinarith
    have hnotE : z + (q : ℝ) • e ∉ E := fun h ↦
      hnotH (((hzA p₀ hp₀T q).2 (hnear q hqδ)).mp h)
    have hzE : z ∉ E := fun h ↦ hnotE ((hzD q hq0).1 h)
    have hzH : z ∉ positiveHalfspace ν := by
      show ¬ (0 < inner ℝ ν z)
      linarith
    exact propext (iff_of_false hzE hzH)
  · -- on the hyperplane
    have hs0 : s = 0 := by rw [hs, hzero, zero_div]
    have hball : z - ((0 : ℚ) : ℝ) • e ∈ ball p₀ (rad p₀) := by
      have := hnear 0 (by rw [zero_add, hs0, abs_zero]; exact hδ0)
      simpa using this
    have h1 := (hzA p₀ hp₀T 0).1 hball
    simp only [Rat.cast_zero, zero_smul, sub_zero] at h1
    exact propext h1
  · -- above the hyperplane
    have hs0 : 0 < s := div_pos hpos ha
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (s - δ) < s from
      max_lt hs0 (by linarith))
    have hq0 : 0 ≤ (q : ℝ) := (le_max_left _ _).trans hq1.le
    have hqδ : |-(q : ℝ) + s| < δ := by
      rw [abs_lt]
      constructor <;> linarith [le_max_right 0 (s - δ)]
    have hball : z - (q : ℝ) • e ∈ ball p₀ (rad p₀) := by
      have := hnear (-(q : ℝ)) hqδ
      rwa [neg_smul, ← sub_eq_add_neg] at this
    have hH : z - (q : ℝ) • e ∈ positiveHalfspace ν := by
      show 0 < inner ℝ ν (z - (q : ℝ) • e)
      have := hinner (-(q : ℝ))
      rw [neg_smul, ← sub_eq_add_neg] at this
      rw [this]
      nlinarith
    have hE' : z - (q : ℝ) • e ∈ E := ((hzA p₀ hp₀T q).1 hball).mpr hH
    have hzE : z ∈ E := (hzD q hq0).2 hE'
    have hzH : z ∈ positiveHalfspace ν := hpos
    exact propext (iff_of_true hzE hzH)

/-! ### 3. Step D: a regular point with positive vertical normal component -/

/-- **Step D.** If the vertical normal component is positive at some regular boundary point, the
directed minimizing cone is a.e. a half-space. -/
theorem IsDirectedMinimizingCone.ae_eq_positiveHalfspace_of_inner_pos {m : ℕ} (hm : 2 ≤ m)
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E) (hsmooth : C1RegularSmoothHyp)
    (hSnull : μH[((m + 1 : ℕ) : ℝ) - 2] (singularSet E) = 0)
    (hSnull' : μH[(m : ℝ)] (singularSet E) = 0)
    (hC : ∀ (U : Set (Space (m + 1))) (F : Space (m + 1) → ℝ), IsSmoothBoundaryChart E U F →
      ∀ z ∈ U, F z = 0 →
        sqNormSecondFundamentalForm F z * inner ℝ (chartNormal F z) (verticalDirection m) = 0)
    {U₀ : Set (Space (m + 1))} {F₀ : Space (m + 1) → ℝ} (h₀ : IsSmoothBoundaryChart E U₀ F₀)
    {x₀ : Space (m + 1)} (hx₀ : x₀ ∈ U₀) (hFx₀ : F₀ x₀ = 0)
    (hw₀ : 0 < inner ℝ (chartNormal F₀ x₀) (verticalDirection m)) :
    ∃ e : Space (m + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e := by
  set e := verticalDirection m with he
  have hmin := hE.minimizer
  have hcone : ∀ x ∈ measureTheoreticBoundary E, ∀ a : ℝ, 0 < a →
      a • x ∈ measureTheoreticBoundary E :=
    fun x hx a ha ↦ (hE.isMinimizingCone.smul_mem_measureTheoreticBoundary_iff ha x).mpr hx
  -- near a regular point with positive vertical normal component, `E` is a half-space
  have hloc : ∀ (U : Set (Space (m + 1))) (F : Space (m + 1) → ℝ),
      IsSmoothBoundaryChart E U F → ∀ y ∈ U, F y = 0 → 0 < inner ℝ (chartNormal F y) e →
      ∃ r > 0, ∀ᵐ z ∂volume, z ∈ ball y r →
        (z ∈ E ↔ z ∈ positiveHalfspace (chartNormal F y)) := by
    intro U F h y hy hFy hw
    have hwcont : ContinuousOn (fun z ↦ inner ℝ (chartNormal F z) e) U :=
      h.contDiffOn_chartNormal.continuousOn.inner continuousOn_const
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.eventually_nhds_iff_ball.mp
      (((hwcont.continuousAt (h.isOpen.mem_nhds hy)).eventually (lt_mem_nhds hw)).and
        (h.isOpen.mem_nhds hy))
    have hρU : ball y ρ ⊆ U := fun z hz ↦ (hρsub z hz).2
    have h' := h.mono isOpen_ball hρU
    have hA : ∀ z ∈ ball y ρ, F z = 0 → sqNormSecondFundamentalForm F z = 0 := by
      intro z hz hFz
      rcases mul_eq_zero.mp (hC U F h z (hρU hz) hFz) with h2 | h2
      · exact h2
      · exact absurd h2 (hρsub z hz).1.ne'
    obtain ⟨r, hr, hae⟩ := h'.exists_ae_eq_halfspace_of_sqNorm_eq_zero hA (mem_ball_self hρ) hFy
    refine ⟨r, hr, ?_⟩
    have hyν : inner ℝ (chartNormal F y) y = 0 := h.inner_chartNormal_self_eq_zero hcone hy hFy
    filter_upwards [hae] with z hz hzB
    rw [hz hzB, inner_sub_right, hyν, sub_zero]
    exact Iff.rfl
  set ν₀ := chartNormal F₀ x₀ with hν₀
  have hν₀n : ‖ν₀‖ = 1 := norm_chartNormal (h₀.gradient_ne_zero x₀ hx₀)
  have hν₀0 : ν₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hν₀n
    exact zero_ne_one hν₀n
  set H := positiveHalfspace ν₀ with hH
  set S := singularSet E with hS
  set good : Set (Space (m + 1)) :=
    {y | ∃ r > 0, ∀ᵐ z ∂volume, z ∈ ball y r → (z ∈ E ↔ z ∈ H)} with hgood
  have hgood_open : IsOpen good := by
    rw [Metric.isOpen_iff]
    rintro y ⟨r, hr, hae⟩
    refine ⟨r / 2, by positivity, fun y' hy' ↦ ⟨r / 2, by positivity, ?_⟩⟩
    filter_upwards [hae] with z hz hzB
    apply hz
    rw [mem_ball] at hy' hzB ⊢
    calc dist z y ≤ dist z y' + dist y' y := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hzB hy'
      _ = r := by ring
  -- good points of the hyperplane are boundary points
  have hgoodB : ∀ y ∈ good, inner ℝ ν₀ y = 0 → y ∈ measureTheoreticBoundary E := by
    rintro y ⟨r, hr, hae⟩ hy
    exact (isSmoothBoundaryChart_inner isOpen_ball hν₀0 hae).mem_measureTheoreticBoundary
      (mem_ball_self hr) hy
  have hx₀good : x₀ ∈ good := hloc U₀ F₀ h₀ x₀ hx₀ hFx₀ hw₀
  have hx₀P : inner ℝ ν₀ x₀ = 0 := h₀.inner_chartNormal_self_eq_zero hcone hx₀ hFx₀
  have hx₀S : x₀ ∉ S := fun h ↦ h.2 (h₀.isC1BoundaryPoint hx₀ hFx₀)
  set Pset : Set (Space (m + 1)) := {x | inner ℝ ν₀ x = 0} \ S with hPset
  have hPconn : IsPreconnected Pset :=
    (isPathConnected_hyperplane_diff_space (by omega) hν₀0 hSnull).isConnected.isPreconnected
  -- closedness: a point of `Pset` in the closure of the good points of `Pset` is good
  have hclosed : ∀ y ∈ Pset, y ∈ closure (good ∩ Pset) → y ∈ good := by
    intro y hyP hycl
    have hyB : y ∈ measureTheoreticBoundary E :=
      closure_minimal (fun z hz ↦ hgoodB z hz.1 hz.2.1) (isClosed_measureTheoreticBoundary E) hycl
    obtain ⟨U, F, hyU, h⟩ := hsmooth.exists_chart hmin hyB hyP.2
    have hFy : F y = 0 := h.eq_zero_of_mem_measureTheoreticBoundary hyU hyB
    have hνy : chartNormal F y = ν₀ := by
      by_contra hne
      have hcont : ContinuousAt (chartNormal F) y :=
        h.contDiffOn_chartNormal.continuousOn.continuousAt (h.isOpen.mem_nhds hyU)
      have hnhds : {z | chartNormal F z ∈ ({ν₀}ᶜ : Set (Space (m + 1)))} ∩ U ∈ 𝓝 y :=
        inter_mem (hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hne))
          (h.isOpen.mem_nhds hyU)
      obtain ⟨z, ⟨hzne, hzU⟩, hzgood, hzP⟩ := mem_closure_iff_nhds.mp hycl _ hnhds
      obtain ⟨r, hr, hae⟩ := hzgood
      have hlin := isSmoothBoundaryChart_inner isOpen_ball hν₀0 hae
      have hzB : z ∈ measureTheoreticBoundary E := hgoodB z ⟨r, hr, hae⟩ hzP.1
      have h1 := hlin.chartNormal_eq_of_mem_boundary h (mem_ball_self hr) hzU hzB
      rw [chartNormal_inner_left_const hν₀n] at h1
      exact hzne h1
    obtain ⟨r, hr, hae⟩ := hloc U F h y hyU hFy (by rw [hνy]; exact hw₀)
    rw [hνy] at hae
    exact ⟨r, hr, hae⟩
  have hall : Pset ⊆ good := by
    rcases isPreconnected_iff_subset_of_disjoint.mp hPconn good (closure (good ∩ Pset))ᶜ
      hgood_open isClosed_closure.isOpen_compl
      (fun y hy ↦ by
        by_cases hy' : y ∈ closure (good ∩ Pset)
        · exact Or.inl (hclosed y hy hy')
        · exact Or.inr hy')
      (eq_empty_of_forall_notMem fun y hy ↦ hy.2.2 (subset_closure ⟨hy.2.1, hy.1⟩))
      with h1 | h1
    · exact h1
    · have hx₀cl : x₀ ∈ closure (good ∩ Pset) := subset_closure ⟨hx₀good, hx₀P, hx₀S⟩
      exact absurd hx₀cl (h1 ⟨hx₀P, hx₀S⟩)
  refine ⟨ν₀, hν₀n, ae_eq_positiveHalfspace_of_forall_hyperplane hE.vertical hw₀
    (volume_setOf_add_smul_vertical_mem_eq_zero hSnull') fun p hp hpS ↦ hall ⟨hp, hpS⟩⟩

/-! ### 4. Step E: vanishing vertical normal component -/

/-- **Step E.** If the vertical normal component vanishes at every regular boundary point, the
directed minimizing cone is a.e. invariant under vertical translations. -/
theorem IsDirectedMinimizingCone.verticalInvariant_of_inner_eq_zero {m : ℕ}
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E) (hsmooth : C1RegularSmoothHyp)
    (hSnull : μH[(m : ℝ)] (singularSet E) = 0)
    (hw : ∀ (U : Set (Space (m + 1))) (F : Space (m + 1) → ℝ), IsSmoothBoundaryChart E U F →
      ∀ z ∈ U, F z = 0 → inner ℝ (chartNormal F z) (verticalDirection m) = 0) :
    ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E := by
  classical
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ with hb
  set e := verticalDirection m with he
  have hmin := hE.minimizer
  have hmeas := hE.measurableSet
  obtain ⟨μ, hμloc, -, hμ⟩ := exists_global_perimeter_measure b hmeas
    (fun n ↦ hmin.perimeter_ball_ne_top 0 _ (by positivity) (subset_univ _))
  have := hμloc
  have hμ' : ∀ V, IsOpen V → V ⊆ univ → μ V = variationalPerimeter b E V := fun V hV _ ↦ hμ V hV
  have hμB : μ (univ \ measureTheoreticBoundary E) = 0 := hmin.measure_sdiff_boundary_eq_zero μ hμ'
  have hμS : μ (singularSet E) = 0 := by
    have h1 := hmin.measure_le_hausdorffMeasure_inter_boundary μ hμ' (subset_univ (singularSet E))
    rw [measure_mono_null inter_subset_left hSnull, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  intro t
  refine ae_mem_iff_add_smul_mem_of_integral_fderiv_eq_zero hmeas e (fun φ hφ hφc ↦ ?_) t
  obtain ⟨ρ₁, hρ₁⟩ := (show IsCompact (tsupport φ) from hφc).isBounded.subset_ball
    (0 : Space (m + 1))
  set ρ := max ρ₁ 1 with hρdef
  have hρ : 0 < ρ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hρsub : tsupport φ ⊆ ball (0 : Space (m + 1)) ρ :=
    hρ₁.trans (ball_subset_ball (le_max_left _ _))
  set Ω : Set (Space (m + 1)) := ball 0 ρ with hΩ
  obtain ⟨ν, hp⟩ := exists_isPerimeterPolarOn_of_perimeter_measure b hmeas isOpen_ball
    (hmin.perimeter_ball_ne_top 0 ρ hρ (subset_univ _)) μ hμ
  -- countably many charts cover the regular part of `Ω`
  set I := Ω ∩ (measureTheoreticBoundary E \ singularSet E) with hI
  have hchart : ∀ x ∈ I, ∃ U F, x ∈ U ∧ IsSmoothBoundaryChart E U F := fun x hx ↦
    hsmooth.exists_chart hmin hx.2.1 hx.2.2
  choose! Uc Fc hxU hch using hchart
  obtain ⟨T, hTI, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable I (fun x ↦ Uc x ∩ Ω)
    (fun x hx ↦ (hch x hx).isOpen.inter isOpen_ball)
  have hcover : I ⊆ ⋃ x ∈ T, Uc x ∩ Ω := by
    rw [hTU]
    intro x hx
    exact mem_biUnion hx ⟨hxU x hx, hx.1⟩
  have hae_chart : ∀ᵐ y ∂μ, ∀ x ∈ T, y ∈ Uc x ∩ Ω →
      ν y = chartNormal (Fc x) y ∧ Fc x y = 0 := by
    rw [ae_ball_iff hTc]
    intro x hxT
    have hO : IsOpen (Uc x ∩ Ω) := (hch x (hTI hxT)).isOpen.inter isOpen_ball
    have h' := (hch x (hTI hxT)).mono hO inter_subset_left
    exact (ae_restrict_iff' hO.measurableSet).mp
      ((h'.ae_restrict_eq_chartNormal hp inter_subset_right).and
        (h'.ae_restrict_eq_zero hp inter_subset_right))
  have hB : ∀ᵐ y ∂μ, y ∈ measureTheoreticBoundary E := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμB] with y hy
    by_contra h
    exact hy ⟨mem_univ y, h⟩
  have hνe : ∀ᵐ y ∂μ.restrict Ω, inner ℝ (ν y) e = 0 := by
    rw [ae_restrict_iff' isOpen_ball.measurableSet]
    filter_upwards [hae_chart, hB, measure_eq_zero_iff_ae_notMem.mp hμS] with y hy hyB hyS hyΩ
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.mp (hcover ⟨hyΩ, hyB, hyS⟩)
    obtain ⟨hν, hF⟩ := hy x hxT hyx
    rw [hν]
    exact hw (Uc x) (Fc x) (hch x (hTI hxT)) y hyx.1 hF
  -- the distributional vertical derivative of `1_E` vanishes
  have hX : ContDiff ℝ 1 (fun x ↦ φ x • e) := (hφ.of_le (by simp)).smul contDiff_const
  have hXc : HasCompactSupport (fun x ↦ φ x • e) := hasCompactSupport_smul_left' hφc fun _ ↦ e
  have hXΩ : tsupport (fun x ↦ φ x • e) ⊆ Ω := (tsupport_smul_subset_left' _ _).trans hρsub
  have hpair := hp.pairing hX hXc hXΩ
  have hR : ∫ x, inner ℝ (φ x • e) (ν x) ∂μ.restrict Ω = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hνe] with y hy
    rw [real_inner_smul_left, real_inner_comm, hy, mul_zero]
    rfl
  have hL : ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fieldDivergence b (fun x ↦ φ x • e) x =
      ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x * fderiv ℝ φ x e := by
    congr 1
    funext x
    rw [fieldDivergence_smul_const_eq_fderiv b ((hφ.differentiable (by simp)) x)]
  rw [hR, hL] at hpair
  linarith

/-! ### 5. The dichotomy -/

/-- **The cone dichotomy (§5A).** Given ε-regularity, upper semicontinuity of singular sets,
Simons' theorem in dimensions `2, …, 7` and the smoothness of `C¹` boundary points, a directed
minimizing cone is a.e. a half-space or a.e. invariant under vertical translations. -/
theorem IsDirectedMinimizingCone.halfspace_or_verticalInvariant_of_hyps
    (hreg : EpsilonRegularityHyp) (husc : SingularSetUSCHyp)
    (hs : ∀ k, 2 ≤ k → k ≤ 7 → SimonsHyp k) (hsmooth : C1RegularSmoothHyp) {m : ℕ}
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E) :
    (∃ e : Space (m + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e) ∨
      (∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) := by
  by_cases hlow : m + 1 ≤ 7
  · exact Or.inl (hE.isMinimizingCone.ae_eq_positiveHalfspace_of_le_seven_of_regularity hreg hs
      hlow)
  have hm : 7 ≤ m := by omega
  have hclass := coneClassification_of_simonsHyp hreg hs
  have hSnull : ∀ s : ℝ, ((m + 1 : ℕ) : ℝ) - 8 < s → μH[s] (singularSet E) = 0 := by
    intro s hs'
    have h1 := hE.minimizer.hausdorffMeasure_singularSet_inter_eq_zero hreg husc hclass hs'
    rwa [inter_univ] at h1
  have hC := fun (U : Set (Space (m + 1))) (F : Space (m + 1) → ℝ)
      (h : IsSmoothBoundaryChart E U F) (z : Space (m + 1)) (hz : z ∈ U) (hFz : F z = 0) ↦
    hE.sqNorm_mul_inner_vertical_eq_zero (by omega) hsmooth hSnull h hz hFz
  have hSm : μH[(m : ℝ)] (singularSet E) = 0 := hSnull _ (by push_cast; linarith)
  by_cases hpos : ∃ (U : Set (Space (m + 1))) (F : Space (m + 1) → ℝ),
      IsSmoothBoundaryChart E U F ∧ ∃ z ∈ U, F z = 0 ∧
        0 < inner ℝ (chartNormal F z) (verticalDirection m)
  · obtain ⟨U, F, h, z, hz, hFz, hw⟩ := hpos
    exact Or.inl (hE.ae_eq_positiveHalfspace_of_inner_pos (by omega) hsmooth
      (hSnull _ (by push_cast; linarith)) hSm hC h hz hFz hw)
  · refine Or.inr (hE.verticalInvariant_of_inner_eq_zero hsmooth hSm fun U F h z hz hFz ↦ ?_)
    refine le_antisymm (not_lt.mp fun hlt ↦ hpos ⟨U, F, h, z, hz, hFz, hlt⟩) ?_
    exact h.inner_chartNormal_nonneg_of_monotone hE.vertical hz hFz

end SerrinEpigraph
