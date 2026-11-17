module

public import SerrinEpigraph.LocalPerimeterMinimizer
public import SerrinEpigraph.BVBallGluing
public import SerrinEpigraph.BVIsoperimetric
public import SerrinEpigraph.MollifiedGradientMass
public import SerrinEpigraph.MeasurablePhaseMollification
public import SerrinEpigraph.SegmentGradientEstimate
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Density estimates, canonical open representatives, and coarse Hausdorff bounds (BV6–BV7)

For local perimeter minimizers (`IsLocalPerimeterMinimizer b E Ω`) in `Space (m + 1)` (`m : ℕ`),
this module establishes:
- **Measure-theoretic representatives**: `measureTheoreticInterior`, `measureTheoreticExterior`,
  and `measureTheoreticBoundary`, together with openness/closedness, disjoint partition, complement
  symmetry, null-set invariance, and affine rescaling laws.
- **Universal upper perimeter bound (BV6.2 upper)**: `P(E, B_r(x₀)) ≤ C_upper(m) r^m` at every
  interior ball `closedBall x₀ r ⊆ Ω`.
- **Two-phase volume density lower bounds (BV6.1)**: at `x₀ ∈ measureTheoreticBoundary E` with
  `closedBall x₀ r ⊆ Ω`, both `|E ∩ B_r(x₀)|` and `|B_r(x₀) \ E|` are bounded below by
  `c_vol(m) r^(m + 1)`.
- **Perimeter lower bound (BV6.2 lower)**: via the unit-ball `L¹` Poincaré inequality on smooth
  mollifications, `P(E, B_r(x₀)) ≥ c_per(m) r^m` at `x₀ ∈ measureTheoreticBoundary E`.
- **Canonical open representatives, support identity, and coarse Hausdorff `m`-measure bound
  (BV7, BV7.1, BV7.2)**: `|∂*E ∩ Ω| = 0`, `E =ᵐ measureTheoreticInterior E` on `Ω`,
  `frontier (measureTheoreticInterior E) ∩ Ω = measureTheoreticBoundary E ∩ Ω`,
  `supp μ ∩ Ω = measureTheoreticBoundary E ∩ Ω`, and `μH[m] (S ∩ ∂*E) ≤ C_H(m) * μ S` for `S ⊆ Ω`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology CompactlySupported ENNReal Pointwise MeasureTheory

namespace SerrinEpigraph

/-! ### 1. Measure-theoretic interior, exterior, and boundary -/

/-- Points around which some open ball has null complement with respect to `E`. -/
def measureTheoreticInterior {d : ℕ} (E : Set (Space d)) : Set (Space d) :=
  {x | ∃ r > 0, volume (ball x r \ E) = 0}

/-- Points around which some open ball has null intersection with `E`. -/
def measureTheoreticExterior {d : ℕ} (E : Set (Space d)) : Set (Space d) :=
  {x | ∃ r > 0, volume (E ∩ ball x r) = 0}

/-- Points where every centered open ball meets both `E` and `Eᶜ` in sets of positive measure. -/
def measureTheoreticBoundary {d : ℕ} (E : Set (Space d)) : Set (Space d) :=
  {x | ∀ r > 0, volume (E ∩ ball x r) ≠ 0 ∧ volume (ball x r \ E) ≠ 0}

theorem measureTheoreticExterior_eq_interior_compl {d : ℕ} (E : Set (Space d)) :
    measureTheoreticExterior E = measureTheoreticInterior Eᶜ := by
  ext x
  simp only [measureTheoreticExterior, measureTheoreticInterior, mem_ofPred_eq]
  refine exists_congr fun r ↦ and_congr_right fun _ ↦ ?_
  have hset : E ∩ ball x r = ball x r \ Eᶜ := by
    ext y
    simp [and_comm]
  rw [hset]

theorem measureTheoreticInterior_compl {d : ℕ} (E : Set (Space d)) :
    measureTheoreticInterior Eᶜ = measureTheoreticExterior E :=
  (measureTheoreticExterior_eq_interior_compl E).symm

theorem measureTheoreticExterior_compl {d : ℕ} (E : Set (Space d)) :
    measureTheoreticExterior Eᶜ = measureTheoreticInterior E := by
  rw [measureTheoreticExterior_eq_interior_compl, compl_compl]

theorem isOpen_measureTheoreticInterior {d : ℕ} (E : Set (Space d)) :
    IsOpen (measureTheoreticInterior E) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨r, hr, hvol⟩
  refine ⟨r, hr, fun y hy ↦ ⟨r - dist y x, sub_pos.mpr hy, ?_⟩⟩
  refine measure_mono_null ?_ hvol
  refine sdiff_subset_sdiff ?_ Subset.rfl
  exact ball_subset_ball' (by linarith [mem_ball.mp hy])

theorem isOpen_measureTheoreticExterior {d : ℕ} (E : Set (Space d)) :
    IsOpen (measureTheoreticExterior E) := by
  rw [measureTheoreticExterior_eq_interior_compl]
  exact isOpen_measureTheoreticInterior Eᶜ

theorem disjoint_measureTheoreticInterior_exterior {d : ℕ} (E : Set (Space d)) :
    Disjoint (measureTheoreticInterior E) (measureTheoreticExterior E) := by
  rw [disjoint_left]
  rintro x ⟨r₁, hr₁, h₁⟩ ⟨r₂, hr₂, h₂⟩
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hsub₁ : ball x r \ E ⊆ ball x r₁ \ E :=
    sdiff_subset_sdiff (ball_subset_ball (min_le_left _ _)) Subset.rfl
  have hsub₂ : E ∩ ball x r ⊆ E ∩ ball x r₂ :=
    inter_subset_inter_right E (ball_subset_ball (min_le_right _ _))
  have hcov : ball x r ⊆ (E ∩ ball x r) ∪ (ball x r \ E) := by
    intro y hy
    by_cases hyE : y ∈ E
    · exact Or.inl ⟨hyE, hy⟩
    · exact Or.inr ⟨hy, hyE⟩
  have hzero : volume (ball x r) = 0 := by
    refine nonpos_iff_eq_zero.mp ?_
    calc
      volume (ball x r) ≤ volume ((E ∩ ball x r) ∪ (ball x r \ E)) := measure_mono hcov
      _ ≤ volume (E ∩ ball x r) + volume (ball x r \ E) := measure_union_le _ _
      _ = 0 := by rw [measure_mono_null hsub₂ h₂, measure_mono_null hsub₁ h₁, add_zero]
  exact (measure_ball_pos volume x hr).ne' hzero

theorem compl_measureTheoreticInterior_union_exterior {d : ℕ} (E : Set (Space d)) :
    (measureTheoreticInterior E ∪ measureTheoreticExterior E)ᶜ = measureTheoreticBoundary E := by
  ext x
  simp only [mem_compl_iff, mem_union, measureTheoreticInterior, measureTheoreticExterior,
    measureTheoreticBoundary, mem_ofPred_eq, not_or, not_exists, not_and]
  constructor
  · rintro ⟨h₁, h₂⟩ r hr
    exact ⟨h₂ r hr, h₁ r hr⟩
  · intro h
    exact ⟨fun r hr ↦ (h r hr).2, fun r hr ↦ (h r hr).1⟩

theorem isClosed_measureTheoreticBoundary {d : ℕ} (E : Set (Space d)) :
    IsClosed (measureTheoreticBoundary E) := by
  rw [← compl_measureTheoreticInterior_union_exterior]
  exact ((isOpen_measureTheoreticInterior E).union (isOpen_measureTheoreticExterior E)).isClosed_compl

@[simp]
theorem measureTheoreticBoundary_compl {d : ℕ} (E : Set (Space d)) :
    measureTheoreticBoundary Eᶜ = measureTheoreticBoundary E := by
  rw [← compl_measureTheoreticInterior_union_exterior,
    ← compl_measureTheoreticInterior_union_exterior,
    measureTheoreticInterior_compl, measureTheoreticExterior_compl, union_comm]

theorem frontier_measureTheoreticInterior_subset {d : ℕ} (E : Set (Space d)) :
    frontier (measureTheoreticInterior E) ⊆ measureTheoreticBoundary E := by
  intro x hx
  rw [frontier, (isOpen_measureTheoreticInterior E).interior_eq] at hx
  rw [← compl_measureTheoreticInterior_union_exterior, mem_compl_iff, mem_union]
  rintro (hx₁ | hx₂)
  · exact hx.2 hx₁
  · obtain ⟨y, hy₁, hy₂⟩ :=
      mem_closure_iff.mp hx.1 (measureTheoreticExterior E) (isOpen_measureTheoreticExterior E) hx₂
    exact disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) hy₂ hy₁

theorem measureTheoreticInterior_inter_open_congr_ae {d : ℕ} {E E' Ω : Set (Space d)}
    (hΩ : IsOpen Ω) (hae : ∀ᵐ x ∂volume, x ∈ Ω → (x ∈ E ↔ x ∈ E')) :
    measureTheoreticInterior E ∩ Ω = measureTheoreticInterior E' ∩ Ω := by
  let N := {y : Space d | ¬(y ∈ Ω → (y ∈ E ↔ y ∈ E'))}
  have hN : volume N = 0 := ae_iff.mp hae
  have haux {A B : Set (Space d)}
      (hAB : ∀ y, y ∉ N → y ∈ Ω → (y ∈ A ↔ y ∈ B)) :
      measureTheoreticInterior A ∩ Ω ⊆ measureTheoreticInterior B ∩ Ω := by
    rintro x ⟨⟨r₁, hr₁, hvol₁⟩, hxΩ⟩
    obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
    let r := min r₁ r₀
    have hr : 0 < r := lt_min hr₁ hr₀
    refine ⟨⟨r, hr, ?_⟩, hxΩ⟩
    have hsub : ball x r \ B ⊆ (ball x r₁ \ A) ∪ N := by
      intro y ⟨hyb, hyB⟩
      by_cases hyN : y ∈ N
      · exact Or.inr hyN
      · refine Or.inl ⟨ball_subset_ball (min_le_left _ _) hyb, fun hyA ↦ hyB ?_⟩
        exact (hAB y hyN (hball₀ (ball_subset_ball (min_le_right _ _) hyb))).mp hyA
    refine nonpos_iff_eq_zero.mp ?_
    calc
      volume (ball x r \ B) ≤ volume ((ball x r₁ \ A) ∪ N) := measure_mono hsub
      _ ≤ volume (ball x r₁ \ A) + volume N := measure_union_le _ _
      _ = 0 := by rw [hvol₁, hN, add_zero]
  apply Subset.antisymm
  · exact haux fun y hyN hyΩ ↦ not_not.mp hyN hyΩ
  · exact haux fun y hyN hyΩ ↦ (not_not.mp hyN hyΩ).symm

theorem measureTheoreticExterior_inter_open_congr_ae {d : ℕ} {E E' Ω : Set (Space d)}
    (hΩ : IsOpen Ω) (hae : ∀ᵐ x ∂volume, x ∈ Ω → (x ∈ E ↔ x ∈ E')) :
    measureTheoreticExterior E ∩ Ω = measureTheoreticExterior E' ∩ Ω := by
  rw [measureTheoreticExterior_eq_interior_compl, measureTheoreticExterior_eq_interior_compl]
  refine measureTheoreticInterior_inter_open_congr_ae hΩ ?_
  filter_upwards [hae] with x hx hxΩ
  exact not_congr (hx hxΩ)

theorem measureTheoreticBoundary_inter_open_congr_ae {d : ℕ} {E E' Ω : Set (Space d)}
    (hΩ : IsOpen Ω) (hae : ∀ᵐ x ∂volume, x ∈ Ω → (x ∈ E ↔ x ∈ E')) :
    measureTheoreticBoundary E ∩ Ω = measureTheoreticBoundary E' ∩ Ω := by
  have hi := measureTheoreticInterior_inter_open_congr_ae hΩ hae
  have he := measureTheoreticExterior_inter_open_congr_ae hΩ hae
  ext x
  simp only [← compl_measureTheoreticInterior_union_exterior, mem_inter_iff, mem_compl_iff,
    mem_union]
  constructor <;> rintro ⟨hn, hxΩ⟩ <;> refine ⟨fun h ↦ hn ?_, hxΩ⟩
  · rcases h with h₁ | h₂
    · exact Or.inl ((Set.ext_iff.mp hi x).mpr ⟨h₁, hxΩ⟩).1
    · exact Or.inr ((Set.ext_iff.mp he x).mpr ⟨h₂, hxΩ⟩).1
  · rcases h with h₁ | h₂
    · exact Or.inl ((Set.ext_iff.mp hi x).mp ⟨h₁, hxΩ⟩).1
    · exact Or.inr ((Set.ext_iff.mp he x).mp ⟨h₂, hxΩ⟩).1

theorem measureTheoreticInterior_congr_ae {d : ℕ} {E E' : Set (Space d)}
    (hae : E =ᵐ[volume] E') :
    measureTheoreticInterior E = measureTheoreticInterior E' := by
  have h := measureTheoreticInterior_inter_open_congr_ae (E := E) (E' := E') isOpen_univ
    (by filter_upwards [hae] with x hx _; exact iff_of_eq hx)
  simpa using h

theorem measureTheoreticExterior_congr_ae {d : ℕ} {E E' : Set (Space d)}
    (hae : E =ᵐ[volume] E') :
    measureTheoreticExterior E = measureTheoreticExterior E' := by
  have h := measureTheoreticExterior_inter_open_congr_ae (E := E) (E' := E') isOpen_univ
    (by filter_upwards [hae] with x hx _; exact iff_of_eq hx)
  simpa using h

theorem measureTheoreticBoundary_congr_ae {d : ℕ} {E E' : Set (Space d)}
    (hae : E =ᵐ[volume] E') :
    measureTheoreticBoundary E = measureTheoreticBoundary E' := by
  have h := measureTheoreticBoundary_inter_open_congr_ae (E := E) (E' := E') isOpen_univ
    (by filter_upwards [hae] with x hx _; exact iff_of_eq hx)
  simpa using h

private theorem measure_image_add_smul_eq_zero_iff {d : ℕ} (x₀ : Space d) {r : ℝ} (hr : 0 < r)
    (A : Set (Space d)) :
    volume ((fun z : Space d ↦ x₀ + r • z) '' A) = 0 ↔ volume A = 0 := by
  have hpre : (fun z : Space d ↦ x₀ + r • z) '' A = (fun z ↦ -x₀ + z) ⁻¹' (r • A) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (neg_add_cancel_left x₀ (r • y)).symm⟩
    · rintro ⟨y, hy, hyz⟩
      refine ⟨y, hy, ?_⟩
      change r • y = -x₀ + z at hyz
      change x₀ + r • y = z
      rw [hyz, add_neg_cancel_left]
  rw [hpre, measure_preimage_add, Measure.addHaar_smul_of_nonneg volume hr.le]
  have hc : ENNReal.ofReal (r ^ Module.finrank ℝ (Space d)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  exact mul_eq_zero.trans (or_iff_right hc)

theorem measureTheoreticInterior_preimage_add_smul {d : ℕ} (E : Set (Space d))
    (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    measureTheoreticInterior ((fun z ↦ x₀ + r • z) ⁻¹' E) =
      (fun z ↦ x₀ + r • z) ⁻¹' measureTheoreticInterior E := by
  let T : Space d → Space d := fun z ↦ x₀ + r • z
  let S : Space d → Space d := fun x ↦ r⁻¹ • (x - x₀)
  have hTS (x : Space d) : T (S x) = x := by simp [T, S, smul_smul, mul_inv_cancel₀ hr.ne']
  have himg_ball (y : Space d) (ρ : ℝ) :
      T '' (ball y ρ \ T ⁻¹' E) = ball (T y) (r * ρ) \ E := by
    ext x
    constructor
    · rintro ⟨z, ⟨hzb, hzE⟩, rfl⟩
      refine ⟨?_, hzE⟩
      rw [mem_ball, dist_eq_norm] at hzb ⊢
      have hdiff : T z - T y = r • (z - y) := by
        dsimp [T]
        rw [add_sub_add_left_eq_sub, ← smul_sub]
      rw [hdiff, norm_smul, Real.norm_of_nonneg hr.le]
      exact mul_lt_mul_of_pos_left hzb hr
    · rintro ⟨hxb, hxE⟩
      refine ⟨S x, ⟨?_, ?_⟩, hTS x⟩
      · rw [mem_ball, dist_eq_norm] at hxb ⊢
        have hdiff : S x - y = r⁻¹ • (x - T y) := by
          dsimp [S, T]
          have hy : y = r⁻¹ • (r • y) := by simp [smul_smul, inv_mul_cancel₀ hr.ne']
          nth_rw 1 [hy]
          rw [← smul_sub, sub_sub]
        rw [hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact (inv_mul_lt_iff₀ hr).mpr hxb
      · simpa [hTS x] using hxE
  ext y
  simp only [measureTheoreticInterior, mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨ρ, hρ, hvol⟩
    refine ⟨r * ρ, mul_pos hr hρ, ?_⟩
    rw [← himg_ball, measure_image_add_smul_eq_zero_iff x₀ hr]
    exact hvol
  · rintro ⟨ρ', hρ', hvol'⟩
    refine ⟨r⁻¹ * ρ', mul_pos (inv_pos.mpr hr) hρ', ?_⟩
    rw [← measure_image_add_smul_eq_zero_iff x₀ hr, himg_ball, mul_inv_cancel_left₀ hr.ne']
    exact hvol'

theorem measureTheoreticExterior_preimage_add_smul {d : ℕ} (E : Set (Space d))
    (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    measureTheoreticExterior ((fun z ↦ x₀ + r • z) ⁻¹' E) =
      (fun z ↦ x₀ + r • z) ⁻¹' measureTheoreticExterior E := by
  rw [measureTheoreticExterior_eq_interior_compl, measureTheoreticExterior_eq_interior_compl]
  exact measureTheoreticInterior_preimage_add_smul Eᶜ x₀ hr

theorem measureTheoreticBoundary_preimage_add_smul {d : ℕ} (E : Set (Space d))
    (x₀ : Space d) {r : ℝ} (hr : 0 < r) :
    measureTheoreticBoundary ((fun z ↦ x₀ + r • z) ⁻¹' E) =
      (fun z ↦ x₀ + r • z) ⁻¹' measureTheoreticBoundary E := by
  rw [← compl_measureTheoreticInterior_union_exterior,
    ← compl_measureTheoreticInterior_union_exterior,
    preimage_compl, preimage_union,
    measureTheoreticInterior_preimage_add_smul E x₀ hr,
    measureTheoreticExterior_preimage_add_smul E x₀ hr]

theorem mem_measureTheoreticBoundary_preimage_add_smul {d : ℕ} (E : Set (Space d))
    (x₀ y : Space d) {r : ℝ} (hr : 0 < r) :
    y ∈ measureTheoreticBoundary ((fun z ↦ x₀ + r • z) ⁻¹' E) ↔
      x₀ + r • y ∈ measureTheoreticBoundary E := by
  rw [measureTheoreticBoundary_preimage_add_smul E x₀ hr]
  rfl

/-! ### 2. Universal upper perimeter bound on balls (BV6.2 upper) -/

/-- Explicit positive dimensional upper bound constant for perimeter on balls of a local perimeter
minimizer in `Space (m + 1)`. -/
def minimizerPerimeterUpperConst (m : ℕ) : ℝ :=
  ballGluingConstant * ((m : ℝ) + 1) * volume.real (ball (0 : Space (m + 1)) 1)

theorem minimizerPerimeterUpperConst_pos (m : ℕ) : 0 < minimizerPerimeterUpperConst m := by
  have hω : 0 < volume.real (ball (0 : Space (m + 1)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  unfold minimizerPerimeterUpperConst
  exact mul_pos (mul_pos ballGluingConstant_pos (by positivity)) hω

private theorem exists_mem_Ioo_of_ae {P : ℝ → Prop} {a b : ℝ} (hab : a < b)
    (hae : ∀ᵐ r : ℝ ∂volume, P r) : ∃ r ∈ Ioo a b, P r := by
  by_contra hnone
  have hsub : Ioo a b ⊆ {r | ¬ P r} := fun r hr hp ↦ hnone ⟨r, hr, hp⟩
  have hzero : volume (Ioo a b) = 0 := measure_mono_null hsub (ae_iff.mp hae)
  rw [Real.volume_Ioo] at hzero
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hzero

private theorem deriv_volume_inter_ball_le {m : ℕ} (E : Set (Space (m + 1)))
    (hE : MeasurableSet E) (x₀ : Space (m + 1)) {ρ d' : ℝ} (hρ : 0 < ρ)
    (hderiv : HasDerivAt (fun s ↦ volume.real (E ∩ ball x₀ s)) d' ρ) :
    d' ≤ ((m : ℝ) + 1) * volume.real (ball (0 : Space (m + 1)) 1) * ρ ^ m := by
  let ω := volume.real (ball (0 : Space (m + 1)) 1)
  let V : ℝ → ℝ := fun s ↦ volume.real (E ∩ ball x₀ s)
  let W : ℝ → ℝ := fun s ↦ ω * s ^ (m + 1)
  have hW_ball {s : ℝ} (hs : 0 < s) : volume.real (ball x₀ s) = W s := by
    change (volume (ball x₀ s)).toReal = _
    rw [volume.addHaar_ball_of_pos x₀ hs, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hs.le _)]
    simp only [Space, finrank_euclideanSpace_fin]
    change s ^ (m + 1) * ω = ω * s ^ (m + 1)
    ring
  have hdW : HasDerivAt W (ω * (((m + 1 : ℕ) : ℝ) * ρ ^ m)) ρ := by
    simpa [W, Nat.add_sub_cancel] using (hasDerivAt_pow (m + 1) ρ).const_mul ω
  have hdiff := hdW.sub hderiv
  have hnonneg : 0 ≤ ω * (((m + 1 : ℕ) : ℝ) * ρ ^ m) - d' := by
    refine ge_of_tendsto hdiff.tendsto_slope_zero_right ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [smul_eq_mul]
    refine mul_nonneg (inv_nonneg.mpr ht.le) ?_
    have hρt : 0 < ρ + t := by linarith
    have hle : ρ ≤ ρ + t := by linarith
    have hV_diff : V (ρ + t) - V ρ =
        volume.real ((E ∩ ball x₀ (ρ + t)) \ (E ∩ ball x₀ ρ)) := by
      symm
      exact measureReal_sdiff (inter_subset_inter_right E (ball_subset_ball hle))
        (hE.inter measurableSet_ball)
        (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono inter_subset_right))
    have hW_diff : W (ρ + t) - W ρ = volume.real (ball x₀ (ρ + t) \ ball x₀ ρ) := by
      rw [← hW_ball hρt, ← hW_ball hρ]
      symm
      exact measureReal_sdiff (ball_subset_ball hle) measurableSet_ball measure_ball_ne_top
    have hmono : V (ρ + t) - V ρ ≤ W (ρ + t) - W ρ := by
      rw [hV_diff, hW_diff]
      exact measureReal_mono (fun x hx ↦ ⟨hx.1.2, fun hb ↦ hx.2 ⟨hx.1.1, hb⟩⟩)
        (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset))
    change 0 ≤ (W (ρ + t) - V (ρ + t)) - (W ρ - V ρ)
    linarith
  have heq : ω * (((m + 1 : ℕ) : ℝ) * ρ ^ m) = ((m : ℝ) + 1) * ω * ρ ^ m := by
    push_cast
    ring
  linarith

/-- Universal upper perimeter bound on any interior ball of a local perimeter minimizer
(centered at an arbitrary point `x₀`, boundary or not). -/
theorem IsLocalPerimeterMinimizer.variationalPerimeter_ball_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω) :
    variationalPerimeter b E (ball x₀ r) ≤
      ENNReal.ofReal (minimizerPerimeterUpperConst m * r ^ m) := by
  obtain ⟨δ, μ₀, -, hδ, hcb, hfin₀, -, hμ₀, -, -, -⟩ :=
    hmin.exists_ball_radon_measure hr hsub
  let Ω₀ := ball x₀ (r + δ)
  let : IsFiniteMeasure μ₀ := hfin₀
  have hmin₀ : IsLocalPerimeterMinimizer b E Ω₀ :=
    hmin.mono isOpen_ball (ball_subset_closedBall.trans hcb)
  let V : ℝ → ℝ := fun s ↦ volume.real (E ∩ ball x₀ s)
  have hV_mono : Monotone V := monotone_volume_real_inter_ball E x₀
  let b_seq : ℕ → ℝ := fun k ↦ r + (δ / 2) * (1 / ((k : ℝ) + 1))
  have hb_gt (k : ℕ) : r < b_seq k := by
    dsimp [b_seq]
    exact lt_add_of_pos_right r (by positivity)
  have hb_lt (k : ℕ) : b_seq k < r + δ := by
    dsimp [b_seq]
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  have hex (k : ℕ) : ∃ ρ ∈ Ioo r (b_seq k), HasDerivAt V (deriv V ρ) ρ := by
    refine exists_mem_Ioo_of_ae (hb_gt k) ?_
    filter_upwards [hV_mono.ae_hasDerivAt] with ρ hρ
    exact hρ.deriv ▸ hρ
  choose ρ hρ hderiv using hex
  have hbound (k : ℕ) :
      variationalPerimeter b E (ball x₀ r) ≤
        ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ k ^ m) := by
    have hρ_pos : 0 < ρ k := hr.trans (hρ k).1
    have hρ_lt : ρ k < r + δ := (hρ k).2.trans (hb_lt k)
    have hcb_ρ : closedBall x₀ (ρ k) ⊆ Ω₀ := closedBall_subset_ball hρ_lt
    have hcomp : variationalPerimeter b E Ω₀ ≤ variationalPerimeter b (E \ ball x₀ (ρ k)) Ω₀ := by
      refine hmin₀.minimizes Ω₀ (E \ ball x₀ (ρ k)) (closedBall x₀ (ρ k)) isOpen_ball
        Subset.rfl (hmin.measurableSet.diff measurableSet_ball)
        (isCompact_closedBall x₀ (ρ k)) hcb_ρ ?_
      exact Eventually.of_forall fun x hx ↦ by
        have hxb : x ∉ ball x₀ (ρ k) := fun hb ↦ hx (ball_subset_closedBall hb)
        simp [hxb]
    have hμ_le := perimeter_closedBall_le_of_sdiff_ball_comparison (by omega) b
      hmin.measurableSet isOpen_ball μ₀ hμ₀ hρ_pos hcb_ρ (measure_ne_top μ₀ _) hcomp (hderiv k)
    have hd_le := deriv_volume_inter_ball_le E hmin.measurableSet x₀ hρ_pos (hderiv k)
    have hconst_le : ballGluingConstant * deriv V (ρ k) ≤
        minimizerPerimeterUpperConst m * ρ k ^ m := by
      calc
        ballGluingConstant * deriv V (ρ k) ≤
            ballGluingConstant *
              (((m : ℝ) + 1) * volume.real (ball (0 : Space (m + 1)) 1) * ρ k ^ m) :=
          mul_le_mul_of_nonneg_left hd_le ballGluingConstant_pos.le
        _ = minimizerPerimeterUpperConst m * ρ k ^ m := by
          unfold minimizerPerimeterUpperConst
          ring
    calc
      variationalPerimeter b E (ball x₀ r) = μ₀ (ball x₀ r) :=
        (hμ₀ (ball x₀ r) isOpen_ball (ball_subset_ball (by linarith))).symm
      _ ≤ μ₀ (closedBall x₀ (ρ k)) :=
        measure_mono ((ball_subset_ball (hρ k).1.le).trans ball_subset_closedBall)
      _ ≤ ENNReal.ofReal (ballGluingConstant * deriv V (ρ k)) := hμ_le
      _ ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ k ^ m) :=
        ENNReal.ofReal_le_ofReal hconst_le
  have hb_lim : Tendsto b_seq atTop (𝓝 r) := by
    have h0 := (tendsto_const_nhds (x := δ / 2)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [b_seq, mul_zero, add_zero] using (tendsto_const_nhds (x := r)).add h0
  have hρ_lim : Tendsto ρ atTop (𝓝 r) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb_lim
      (fun k ↦ (hρ k).1.le) (fun k ↦ (hρ k).2.le)
  have hrhs_lim : Tendsto
      (fun k ↦ ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ k ^ m)) atTop
      (𝓝 (ENNReal.ofReal (minimizerPerimeterUpperConst m * r ^ m))) :=
    ENNReal.tendsto_ofReal ((tendsto_const_nhds.mul (hρ_lim.pow m)))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hrhs_lim hbound

theorem IsLocalPerimeterMinimizer.variationalPerimeter_ball_toReal_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω) :
    (variationalPerimeter b E (ball x₀ r)).toReal ≤ minimizerPerimeterUpperConst m * r ^ m := by
  have hle := hmin.variationalPerimeter_ball_le hr hsub
  have hnonneg : 0 ≤ minimizerPerimeterUpperConst m * r ^ m :=
    mul_nonneg (minimizerPerimeterUpperConst_pos m).le (pow_nonneg hr.le _)
  exact (ENNReal.toReal_le_of_le_ofReal hnonneg hle)

/-- Closed-ball upper perimeter bound for any measure agreeing with `variationalPerimeter b E`
on open subsets of `Ω`. -/
theorem IsLocalPerimeterMinimizer.measure_closedBall_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U)
    {x₀ : Space (m + 1)} {r : ℝ} (hr : 0 < r) (hsub : closedBall x₀ r ⊆ Ω) :
    μ (closedBall x₀ r) ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m * r ^ m) := by
  obtain ⟨δ, hδ, hcb⟩ := exists_pos_closedBall_add_subset_open hmin.isOpen_domain hsub
  let ρ : ℕ → ℝ := fun k ↦ r + δ * (1 / ((k : ℝ) + 1))
  have hbound (k : ℕ) :
      μ (closedBall x₀ r) ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ k ^ m) := by
    have hpos : 0 < δ * (1 / ((k : ℝ) + 1)) := by positivity
    have hle_δ : δ * (1 / ((k : ℝ) + 1)) ≤ δ := by
      have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      nlinarith
    have hρ_pos : 0 < ρ k := by dsimp [ρ]; linarith
    have hcb_k : closedBall x₀ (ρ k) ⊆ Ω :=
      (closedBall_subset_closedBall (by dsimp [ρ]; linarith)).trans hcb
    calc
      μ (closedBall x₀ r) ≤ μ (ball x₀ (ρ k)) :=
        measure_mono (closedBall_subset_ball (by dsimp [ρ]; linarith))
      _ = variationalPerimeter b E (ball x₀ (ρ k)) :=
        hμ (ball x₀ (ρ k)) isOpen_ball (ball_subset_closedBall.trans hcb_k)
      _ ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ k ^ m) :=
        hmin.variationalPerimeter_ball_le hρ_pos hcb_k
  have hρ_lim : Tendsto ρ atTop (𝓝 r) := by
    have h0 := (tendsto_const_nhds (x := δ)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [ρ, mul_zero, add_zero] using (tendsto_const_nhds (x := r)).add h0
  have hrhs_lim : Tendsto
      (fun k ↦ ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ k ^ m)) atTop
      (𝓝 (ENNReal.ofReal (minimizerPerimeterUpperConst m * r ^ m))) :=
    ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (hρ_lim.pow m))
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hrhs_lim hbound

/-! ### 3. Two-phase volume density lower bounds (BV6.1) -/

/-- Positive-volume integer-power Euclidean isoperimetric inequality valid for all `m : ℕ`
(including `m = 0`, i.e. ambient dimension `1`, without any `0 < m` assumption). -/
theorem finite_perimeter_isoperimetric_pow_of_pos {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {E : Set (Space (m + 1))} (hE : MeasurableSet E) (hEV : volume E ≠ ⊤)
    (hEpos : 0 < volume.real E)
    {B : ℝ} (hB : 0 ≤ B) (hP : variationalPerimeter b E univ ≤ ENNReal.ofReal B) :
    volume.real (ball (0 : Space (m + 1)) 1) * volume.real E ^ m ≤
      2 ^ (m + 2) * B ^ (m + 1) := by
  let V := volume.real E
  let ω := volume.real (ball (0 : Space (m + 1)) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne'
    measure_ball_ne_top
  have hVpos : 0 < V := hEpos
  have hV0 : 0 ≤ V := hVpos.le
  let r := (2 * V / ω) ^ (((m + 1 : ℕ) : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos (mul_pos (by norm_num) hVpos) hω) _
  have hrpow : r ^ (m + 1) = 2 * V / ω :=
    Real.rpow_inv_natCast_pow (div_nonneg (mul_nonneg (by norm_num) hV0) hω.le)
      (Nat.succ_ne_zero m)
  have hball : volume.real (ball (0 : Space (m + 1)) r) = 2 * V := by
    change (volume (ball (0 : Space (m + 1)) r)).toReal = _
    rw [volume.addHaar_ball_of_pos _ hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
    simp only [Space, finrank_euclideanSpace_fin]
    change r ^ (m + 1) * ω = 2 * V
    rw [hrpow, div_mul_cancel₀ _ hω.ne']
  have hinter := phase_volume_perimeter_interpolation b hE hEV hB hP (r := r)
  rw [hball] at hinter
  change V * (2 * V - V) ≤ r * B * (2 * V) at hinter
  have hlinear : V ≤ 2 * r * B := by nlinarith
  have hpower := pow_le_pow_left₀ hV0 hlinear (m + 1)
  have hscaled := mul_le_mul_of_nonneg_left hpower hω.le
  rw [mul_pow, mul_pow, hrpow] at hscaled
  have halgebra : ω * ((2 : ℝ) ^ (m + 1) * (2 * V / ω) * B ^ (m + 1)) =
      V * (2 ^ (m + 2) * B ^ (m + 1)) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    field_simp
    ring
  rw [halgebra, pow_succ] at hscaled
  have hfinal : V * (ω * V ^ m) ≤ V * (2 ^ (m + 2) * B ^ (m + 1)) := by
    convert hscaled using 1
    ring
  exact (mul_le_mul_iff_right₀ hVpos).mp hfinal

/-- Explicit positive dimensional volume density lower bound constant in `Space (m + 1)`. -/
def minimizerVolumeDensityConst (m : ℕ) : ℝ :=
  volume.real (ball (0 : Space (m + 1)) 1) /
    (2 ^ (m + 2) * (2 * ballGluingConstant * ((m : ℝ) + 1)) ^ (m + 1))

theorem minimizerVolumeDensityConst_pos (m : ℕ) : 0 < minimizerVolumeDensityConst m := by
  have hω : 0 < volume.real (ball (0 : Space (m + 1)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  unfold minimizerVolumeDensityConst
  have hden : 0 < (2 : ℝ) ^ (m + 2) * (2 * ballGluingConstant * ((m : ℝ) + 1)) ^ (m + 1) := by
    have hbase : 0 < 2 * ballGluingConstant * ((m : ℝ) + 1) :=
      mul_pos (mul_pos (by norm_num) ballGluingConstant_pos) (by positivity)
    positivity
  exact div_pos hω hden

/-- Lower volume density bound for `E ∩ ball x₀ r` at any measure-theoretic boundary center
(BV6.1, interior phase). -/
theorem IsLocalPerimeterMinimizer.volume_inter_ball_ge {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall x₀ r ⊆ Ω) :
    minimizerVolumeDensityConst m * r ^ (m + 1) ≤ volume.real (E ∩ ball x₀ r) := by
  obtain ⟨δ, μ₀, -, hδ, hcb, hfin₀, -, hμ₀, -, -, -⟩ :=
    hmin.exists_ball_radon_measure hr hsub
  let Ω₀ := ball x₀ (r + δ)
  let : IsFiniteMeasure μ₀ := hfin₀
  have hmin₀ : IsLocalPerimeterMinimizer b E Ω₀ :=
    hmin.mono isOpen_ball (ball_subset_closedBall.trans hcb)
  let V : ℝ → ℝ := fun s ↦ volume.real (E ∩ ball x₀ s)
  have hV_mono : Monotone V := monotone_volume_real_inter_ball E x₀
  have hV_pos {s : ℝ} (hs : 0 < s) : 0 < V s :=
    ENNReal.toReal_pos (hx₀ s hs).1
      (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono inter_subset_right))
  let p : ℝ := (((m + 1 : ℕ) : ℝ))⁻¹
  have hp_pos : 0 < p := by dsimp [p]; positivity
  let g : ℝ → ℝ := fun s ↦ (V s) ^ p
  have hg_mono : Monotone g := fun s₁ s₂ hs₁₂ ↦
    Real.rpow_le_rpow measureReal_nonneg (hV_mono hs₁₂) hp_pos.le
  have hg_pow (s : ℝ) : (g s) ^ (m + 1) = V s :=
    Real.rpow_inv_natCast_pow measureReal_nonneg (Nat.succ_ne_zero m)
  have hg0 : g 0 = 0 := by
    have hV0 : V 0 = 0 := by simp [V]
    dsimp [g]
    rw [hV0]
    exact Real.zero_rpow hp_pos.ne'
  let c₀ : ℝ := (minimizerVolumeDensityConst m) ^ p
  have hc₀_pos : 0 < c₀ := Real.rpow_pos_of_pos (minimizerVolumeDensityConst_pos m) p
  have hc₀_pow : c₀ ^ (m + 1) = minimizerVolumeDensityConst m :=
    Real.rpow_inv_natCast_pow (minimizerVolumeDensityConst_pos m).le (Nat.succ_ne_zero m)
  obtain ⟨hg_int, hint_le⟩ := monotone_setIntegral_deriv_Ioo_le hg_mono hr.le
  have hae_c₀ : (fun _ : ℝ ↦ c₀) ≤ᵐ[volume.restrict (Ioo 0 r)] deriv g := by
    change ∀ᵐ ρ : ℝ ∂volume.restrict (Ioo 0 r), c₀ ≤ deriv g ρ
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hV_mono.ae_hasDerivAt] with ρ hdV hρ
    have hρ_pos : 0 < ρ := hρ.1
    have hρ_lt : ρ < r + δ := hρ.2.trans (by linarith)
    have hdV' : HasDerivAt V (deriv V ρ) ρ := hdV.deriv ▸ hdV
    have hcb_ρ : closedBall x₀ ρ ⊆ Ω₀ := closedBall_subset_ball hρ_lt
    have hcomp : variationalPerimeter b E Ω₀ ≤ variationalPerimeter b (E \ ball x₀ ρ) Ω₀ := by
      refine hmin₀.minimizes Ω₀ (E \ ball x₀ ρ) (closedBall x₀ ρ) isOpen_ball
        Subset.rfl (hmin.measurableSet.diff measurableSet_ball)
        (isCompact_closedBall x₀ ρ) hcb_ρ ?_
      exact Eventually.of_forall fun x hx ↦ by
        have hxb : x ∉ ball x₀ ρ := fun hb ↦ hx (ball_subset_closedBall hb)
        simp [hxb]
    have hperim := variationalPerimeter_inter_ball_univ_le_two_mul_of_sdiff_ball_comparison
      (by omega) b hmin.measurableSet isOpen_ball μ₀ hμ₀ hρ_pos hcb_ρ
      (measure_ne_top μ₀ _) hcomp hdV'
    have hdV_nonneg : 0 ≤ deriv V ρ := monotone_hasDerivAt_nonneg hV_mono hdV'
    have hB_nonneg : 0 ≤ 2 * ballGluingConstant * deriv V ρ :=
      mul_nonneg (mul_nonneg (by norm_num) ballGluingConstant_pos.le) hdV_nonneg
    have hiso := finite_perimeter_isoperimetric_pow_of_pos b
      (hmin.measurableSet.inter measurableSet_ball)
      (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono inter_subset_right))
      (hV_pos hρ_pos) hB_nonneg hperim
    change volume.real (ball (0 : Space (m + 1)) 1) * (V ρ) ^ m ≤
      2 ^ (m + 2) * (2 * ballGluingConstant * deriv V ρ) ^ (m + 1) at hiso
    have hdiff_g : DifferentiableAt ℝ g ρ :=
      hdV'.differentiableAt.rpow_const (Or.inl (hV_pos hρ_pos).ne')
    have hdg : HasDerivAt g (deriv g ρ) ρ := hdiff_g.hasDerivAt
    have hdg_pow := hdg.pow (m + 1)
    have hfun_eq : g ^ (m + 1) = V := funext hg_pow
    rw [hfun_eq, Nat.add_sub_cancel] at hdg_pow
    have hderiv_rel : deriv V ρ = ((m + 1 : ℕ) : ℝ) * (g ρ) ^ m * deriv g ρ :=
      hdV'.unique hdg_pow
    have hrhs_eq :
        (2 : ℝ) ^ (m + 2) * (2 * ballGluingConstant * deriv V ρ) ^ (m + 1) =
          ((2 : ℝ) ^ (m + 2) * (2 * ballGluingConstant * ((m : ℝ) + 1)) ^ (m + 1) *
            (deriv g ρ) ^ (m + 1)) * (V ρ) ^ m := by
      have hgm_pow : ((g ρ) ^ m) ^ (m + 1) = (V ρ) ^ m := by
        rw [← pow_mul, mul_comm m (m + 1), pow_mul, hg_pow ρ]
      have hbase_eq : 2 * ballGluingConstant * (((m + 1 : ℕ) : ℝ) * (g ρ) ^ m * deriv g ρ) =
          ((2 * ballGluingConstant * ((m : ℝ) + 1)) * deriv g ρ) * (g ρ) ^ m := by
        push_cast
        ring
      rw [hderiv_rel, hbase_eq, mul_pow, mul_pow, hgm_pow]
      ring
    rw [hrhs_eq] at hiso
    have hVm_pos : 0 < (V ρ) ^ m := pow_pos (hV_pos hρ_pos) m
    have hc_pow_le' : volume.real (ball (0 : Space (m + 1)) 1) ≤
        (2 : ℝ) ^ (m + 2) * (2 * ballGluingConstant * ((m : ℝ) + 1)) ^ (m + 1) *
          (deriv g ρ) ^ (m + 1) :=
      (mul_le_mul_iff_left₀ hVm_pos).mp hiso
    have hden_pos : 0 < (2 : ℝ) ^ (m + 2) *
        (2 * ballGluingConstant * ((m : ℝ) + 1)) ^ (m + 1) := by
      have hbase : 0 < 2 * ballGluingConstant * ((m : ℝ) + 1) :=
        mul_pos (mul_pos (by norm_num) ballGluingConstant_pos) (by positivity)
      positivity
    have hc₀_pow_le : c₀ ^ (m + 1) ≤ (deriv g ρ) ^ (m + 1) := by
      rw [hc₀_pow, minimizerVolumeDensityConst, div_le_iff₀ hden_pos]
      simpa [mul_comm] using hc_pow_le'
    have hdg_nonneg : 0 ≤ deriv g ρ := monotone_deriv_nonneg hg_mono ρ
    exact (pow_le_pow_iff_left₀ hc₀_pos.le hdg_nonneg (Nat.succ_ne_zero m)).mp hc₀_pow_le
  have hIoo_fin : volume (Ioo 0 r) ≠ ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hc₀_int : IntegrableOn (fun _ : ℝ ↦ c₀) (Ioo 0 r) volume :=
    integrableOn_const hIoo_fin
  have hint_c₀ : c₀ * r ≤ g r := by
    have h1 := integral_mono_ae hc₀_int hg_int hae_c₀
    rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal hr.le, mul_comm r c₀] at h1
    linarith [hint_le, hg0]
  have hpow_final := pow_le_pow_left₀ (mul_nonneg hc₀_pos.le hr.le) hint_c₀ (m + 1)
  rwa [mul_pow, hc₀_pow, hg_pow r] at hpow_final

/-- Lower volume density bound for the complement phase `ball x₀ r \ E` at any measure-theoretic
boundary center (BV6.1, exterior phase). -/
theorem IsLocalPerimeterMinimizer.volume_sdiff_ball_ge {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall x₀ r ⊆ Ω) :
    minimizerVolumeDensityConst m * r ^ (m + 1) ≤ volume.real (ball x₀ r \ E) := by
  have hx₀' : x₀ ∈ measureTheoreticBoundary Eᶜ := by
    rwa [measureTheoreticBoundary_compl]
  have hset : ball x₀ r \ E = Eᶜ ∩ ball x₀ r := by
    ext y
    simp [and_comm]
  rw [hset]
  exact hmin.compl.volume_inter_ball_ge hx₀' hr hsub

/-! ### 4. Unit-ball `L¹` Poincaré inequality and perimeter lower bound (BV6.2 lower) -/

/-- Double-integral `L¹` Poincaré inequality on the unit open ball `ball 0 1` in `Space (m + 1)`
for `C¹` functions. -/
theorem integral_unitBall_norm_sub_le_gradient {m : ℕ} {v : Space (m + 1) → ℝ}
    (hv : ContDiff ℝ 1 v) :
    (∫ x in ball (0 : Space (m + 1)) 1, ∫ y in ball (0 : Space (m + 1)) 1, ‖v x - v y‖) ≤
      2 ^ (m + 2) * volume.real (ball (0 : Space (m + 1)) 1) *
        ∫ z in ball (0 : Space (m + 1)) 1, ‖gradient v z‖ := by
  let B₁ : Set (Space (m + 1)) := ball 0 1
  let μB : Measure (Space (m + 1)) := volume.restrict B₁
  let I_half : Set ℝ := Icc (0 : ℝ) (1 / 2)
  let μT : Measure ℝ := volume.restrict I_half
  let : IsFiniteMeasure μB := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact measure_ball_lt_top⟩
  let : IsFiniteMeasure μT := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hG_cont : Continuous (fun z ↦ ‖gradient v z‖) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (hv.continuous_fderiv one_ne_zero).norm
  have hGi_B : IntegrableOn (fun z ↦ ‖gradient v z‖) B₁ volume :=
    (hG_cont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      ball_subset_closedBall
  let g : Space (m + 1) → ℝ := B₁.indicator (fun z ↦ ‖gradient v z‖)
  have hgi : Integrable g volume := hGi_B.integrable_indicator measurableSet_ball
  let H : Space (m + 1) × Space (m + 1) → ℝ → ℝ :=
    fun p t ↦ ‖gradient v ((1 - t) • p.1 + t • p.2)‖
  have hH_cont : Continuous (Function.uncurry H) :=
    hG_cont.comp (((continuous_const.sub continuous_snd).smul
      (continuous_fst.comp continuous_fst)).add
      (continuous_snd.smul (continuous_snd.comp continuous_fst)))
  have hHi : Integrable (Function.uncurry H) ((μB.prod μB).prod μT) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    refine (hH_cont.continuousOn.integrableOn_compact
      (((isCompact_closedBall (0 : Space (m + 1)) 1).prod
        (isCompact_closedBall (0 : Space (m + 1)) 1)).prod
          (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 2)))).mono_set ?_
    exact Set.prod_mono (Set.prod_mono ball_subset_closedBall ball_subset_closedBall) Subset.rfl
  let Φ : Space (m + 1) × Space (m + 1) → ℝ := fun p ↦ ∫ t in I_half, H p t
  have hΦ_cont : Continuous Φ :=
    continuous_parametric_integral_of_continuous (μ := volume) hH_cont isCompact_Icc
  have hΦ_int : Integrable Φ (μB.prod μB) := by
    rw [Measure.prod_restrict]
    exact (hΦ_cont.continuousOn.integrableOn_compact
      ((isCompact_closedBall 0 1).prod (isCompact_closedBall 0 1))).mono_set
      (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
  let Φ_swap : Space (m + 1) × Space (m + 1) → ℝ := fun p ↦ Φ (p.2, p.1)
  have hΦ_swap_cont : Continuous Φ_swap := hΦ_cont.comp continuous_swap
  have hΦ_swap_int : Integrable Φ_swap (μB.prod μB) := by
    rw [Measure.prod_restrict]
    exact (hΦ_swap_cont.continuousOn.integrableOn_compact
      ((isCompact_closedBall 0 1).prod (isCompact_closedBall 0 1))).mono_set
      (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
  have hdiff_cont : Continuous (fun p : Space (m + 1) × Space (m + 1) ↦ ‖v p.1 - v p.2‖) :=
    ((hv.continuous.comp continuous_fst).sub (hv.continuous.comp continuous_snd)).norm
  have hdiff_int : Integrable (fun p : Space (m + 1) × Space (m + 1) ↦ ‖v p.1 - v p.2‖)
      (μB.prod μB) := by
    rw [Measure.prod_restrict]
    exact (hdiff_cont.continuousOn.integrableOn_compact
      ((isCompact_closedBall 0 1).prod (isCompact_closedBall 0 1))).mono_set
      (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
  have hpoint (p : Space (m + 1) × Space (m + 1)) (hp : p ∈ B₁ ×ˢ B₁) :
      ‖v p.1 - v p.2‖ ≤ 2 * (Φ p + Φ_swap p) := by
    have hx : ‖p.1‖ < 1 := by simpa [B₁] using hp.1
    have hy : ‖p.2‖ < 1 := by simpa [B₁] using hp.2
    have hdist : ‖p.2 - p.1‖ ≤ 2 := by
      have htri := norm_sub_le p.2 p.1
      linarith
    have hseg := norm_sub_le_integral_segment_gradient hv p.1 (p.2 - p.1)
    have hadd : p.1 + (p.2 - p.1) = p.2 := add_sub_cancel p.1 p.2
    rw [hadd, norm_sub_rev] at hseg
    have hgamma (t : ℝ) : p.1 + t • (p.2 - p.1) = (1 - t) • p.1 + t • p.2 := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    simp_rw [hgamma] at hseg
    have hc_seg : Continuous (fun t : ℝ ↦ H p t) :=
      hG_cont.comp (((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const))
    have hnonneg_int : 0 ≤ ∫ t in (0 : ℝ)..1, H p t :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ norm_nonneg _
    have hsplit : (∫ t in (0 : ℝ)..1, H p t) = Φ p + Φ_swap p := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hc_seg.intervalIntegrable 0 (1 / 2))
        (hc_seg.intervalIntegrable (1 / 2) 1)]
      congr 1
      · rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
      · have hsub_var := intervalIntegral.integral_comp_sub_left
          (fun s : ℝ ↦ ‖gradient v (s • p.1 + (1 - s) • p.2)‖) (1 : ℝ) (a := (1 / 2 : ℝ)) (b := 1)
        simp only [sub_self] at hsub_var
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring] at hsub_var
        have hlhs_eq : (∫ t in (1 / 2 : ℝ)..1, H p t) =
            ∫ t in (1 / 2 : ℝ)..1, ‖gradient v ((1 - t) • p.1 + (1 - (1 - t)) • p.2)‖ := by
          congr 1 with t
          simp [H]
        rw [hlhs_eq, hsub_var, intervalIntegral.integral_of_le (by norm_num),
          ← integral_Icc_eq_integral_Ioc]
        refine setIntegral_congr_fun measurableSet_Icc fun s _ ↦ ?_
        dsimp [Φ_swap, Φ, H]
        have hcomm : s • p.1 + (1 - s) • p.2 = (1 - s) • p.2 + s • p.1 := add_comm _ _
        rw [hcomm]
    calc
      ‖v p.1 - v p.2‖ ≤ ‖p.2 - p.1‖ * ∫ t in (0 : ℝ)..1, H p t := hseg
      _ ≤ 2 * ∫ t in (0 : ℝ)..1, H p t := mul_le_mul_of_nonneg_right hdist hnonneg_int
      _ = 2 * (Φ p + Φ_swap p) := by rw [hsplit]
  have hprod_le : (∫ p, ‖v p.1 - v p.2‖ ∂(μB.prod μB)) ≤
      2 * ((∫ p, Φ p ∂(μB.prod μB)) + ∫ p, Φ_swap p ∂(μB.prod μB)) := by
    have hae : (fun p ↦ ‖v p.1 - v p.2‖) ≤ᵐ[μB.prod μB] fun p ↦ 2 * (Φ p + Φ_swap p) := by
      change ∀ᵐ p ∂(μB.prod μB), ‖v p.1 - v p.2‖ ≤ 2 * (Φ p + Φ_swap p)
      rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_ball.prod measurableSet_ball)]
      exact Eventually.of_forall hpoint
    have h1 := integral_mono_ae hdiff_int ((hΦ_int.add hΦ_swap_int).const_mul 2) hae
    change (∫ p, ‖v p.1 - v p.2‖ ∂(μB.prod μB)) ≤
      ∫ p, 2 * (Φ p + Φ_swap p) ∂(μB.prod μB) at h1
    rwa [integral_const_mul, integral_add hΦ_int hΦ_swap_int] at h1
  have hswap_eq : (∫ p, Φ_swap p ∂(μB.prod μB)) = ∫ p, Φ p ∂(μB.prod μB) := by
    rw [integral_prod _ hΦ_swap_int, integral_integral_swap hΦ_swap_int]
    change (∫ y, ∫ x, Φ (y, x) ∂μB ∂μB) = _
    rw [← integral_prod _ hΦ_int]
  have hslice (t : ℝ) (ht : t ∈ I_half) :
      (∫ p, H p t ∂(μB.prod μB)) ≤
        2 ^ (m + 1) * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖ := by
    have ht0 : 0 ≤ t := ht.1
    have ht_half : t ≤ 1 / 2 := ht.2
    let s : ℝ := 1 - t
    have hs_half : 1 / 2 ≤ s := by dsimp [s]; linarith
    have hs_pos : 0 < s := by linarith
    have hHt_int : Integrable (fun p : Space (m + 1) × Space (m + 1) ↦ H p t) (μB.prod μB) := by
      rw [Measure.prod_restrict]
      have hc : Continuous (fun p : Space (m + 1) × Space (m + 1) ↦ H p t) :=
        hG_cont.comp ((continuous_fst.const_smul (1 - t)).add (continuous_snd.const_smul t))
      exact (hc.continuousOn.integrableOn_compact
        ((isCompact_closedBall 0 1).prod (isCompact_closedBall 0 1))).mono_set
        (Set.prod_mono ball_subset_closedBall ball_subset_closedBall)
    have hinner (y : Space (m + 1)) (hy : y ∈ B₁) :
        (∫ x in B₁, H (x, y) t) ≤ 2 ^ (m + 1) * ∫ z in B₁, ‖gradient v z‖ := by
      have hconv (x : Space (m + 1)) (hx : x ∈ B₁) : H (x, y) t = g (t • y + s • x) := by
        have hmem : (1 - t) • x + t • y ∈ B₁ :=
          (convex_ball (0 : Space (m + 1)) 1) hx hy hs_pos.le ht0 (by ring)
        have hmem' : t • y + s • x ∈ B₁ := by
          dsimp [s]
          rwa [add_comm (t • y) ((1 - t) • x)]
        dsimp [H, g, s]
        rw [add_comm ((1 - t) • x) (t • y), indicator_of_mem hmem']
      have heq_set : (∫ x in B₁, H (x, y) t) = ∫ x in B₁, g (t • y + s • x) :=
        setIntegral_congr_fun measurableSet_ball hconv
      have hgi_shift : Integrable (fun u ↦ g (t • y + u)) volume :=
        (measurePreserving_add_left volume (t • y)).integrable_comp_of_integrable hgi
      have hgi_comp : Integrable (fun x ↦ g (t • y + s • x)) volume :=
        hgi_shift.comp_smul hs_pos.ne'
      have hle_univ : (∫ x in B₁, g (t • y + s • x)) ≤ ∫ x, g (t • y + s • x) :=
        setIntegral_le_integral hgi_comp (Eventually.of_forall fun x ↦ by
          dsimp [g]
          by_cases h : t • y + s • x ∈ B₁ <;> simp [h])
      have hdil := Measure.integral_comp_smul (μ := volume)
        (f := fun u : Space (m + 1) ↦ g (t • y + u)) s
      simp only [Space, finrank_euclideanSpace_fin, abs_inv, abs_pow,
        abs_of_pos hs_pos, smul_eq_mul] at hdil
      have htrans : (∫ u : Space (m + 1), g (t • y + u)) = ∫ z in B₁, ‖gradient v z‖ := by
        rw [integral_add_left_eq_self g (t • y), integral_indicator measurableSet_ball]
      have hscale_le : (s ^ (m + 1))⁻¹ ≤ (2 : ℝ) ^ (m + 1) := by
        have hpow_le : ((1 : ℝ) / 2) ^ (m + 1) ≤ s ^ (m + 1) :=
          pow_le_pow_left₀ (by positivity) hs_half (m + 1)
        have hinv := inv_anti₀ (by positivity) hpow_le
        have h2 : (((1 : ℝ) / 2) ^ (m + 1))⁻¹ = (2 : ℝ) ^ (m + 1) := by
          rw [one_div, inv_pow, inv_inv]
        rwa [h2] at hinv
      have hgrad_nonneg : 0 ≤ ∫ z in B₁, ‖gradient v z‖ :=
        integral_nonneg fun _ ↦ norm_nonneg _
      rw [heq_set]
      refine hle_univ.trans ?_
      rw [hdil, htrans]
      exact mul_le_mul_of_nonneg_right hscale_le hgrad_nonneg
    rw [integral_prod _ hHt_int, integral_integral_swap hHt_int]
    have hmono := setIntegral_mono_on hHt_int.integral_prod_right
      (integrableOn_const (μ := volume) (s := B₁) (C := 2 ^ (m + 1) * ∫ z in B₁, ‖gradient v z‖)
        measure_ball_ne_top)
      measurableSet_ball hinner
    simpa only [setIntegral_const, smul_eq_mul, mul_comm (volume.real B₁), mul_assoc] using hmono
  have hΦ_bound : (∫ p, Φ p ∂(μB.prod μB)) ≤
      (1 / 2 : ℝ) * (2 ^ (m + 1) * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖) := by
    change (∫ p, (∫ t, H p t ∂μT) ∂(μB.prod μB)) ≤ _
    rw [integral_integral_swap hHi]
    have hmono := setIntegral_mono_on hHi.integral_prod_right
      (integrableOn_const (μ := volume) (s := I_half)
        (C := 2 ^ (m + 1) * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      measurableSet_Icc hslice
    simpa only [μT, I_half, setIntegral_const, Real.volume_real_Icc, sub_zero,
      max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul,
      Function.uncurry_apply_pair] using hmono
  rw [← integral_prod _ hdiff_int]
  calc
    (∫ p, ‖v p.1 - v p.2‖ ∂(μB.prod μB)) ≤ 4 * ∫ p, Φ p ∂(μB.prod μB) := by
      linarith [hprod_le, hswap_eq]
    _ ≤ 4 * ((1 / 2 : ℝ) * (2 ^ (m + 1) * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖)) :=
      mul_le_mul_of_nonneg_left hΦ_bound (by norm_num)
    _ = 2 ^ (m + 2) * volume.real B₁ * ∫ z in B₁, ‖gradient v z‖ := by
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring

/-- Explicit positive dimensional lower bound constant for perimeter on boundary-centered balls
in `Space (m + 1)`. -/
def minimizerPerimeterLowerConst (m : ℕ) : ℝ :=
  (minimizerVolumeDensityConst m) ^ 2 /
    (2 ^ (2 * m + 1) * volume.real (ball (0 : Space (m + 1)) 1))

theorem minimizerPerimeterLowerConst_pos (m : ℕ) : 0 < minimizerPerimeterLowerConst m := by
  have hω : 0 < volume.real (ball (0 : Space (m + 1)) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  have hc : 0 < minimizerVolumeDensityConst m := minimizerVolumeDensityConst_pos m
  unfold minimizerPerimeterLowerConst
  positivity

theorem IsLocalPerimeterMinimizer.variationalPerimeter_ball_toReal_ge {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall x₀ r ⊆ Ω) :
    minimizerPerimeterLowerConst m * r ^ m ≤
      (variationalPerimeter b E (ball x₀ r)).toReal := by
  let s : ℝ := r / 2
  have hs : 0 < s := half_pos hr
  let T : Space (m + 1) → Space (m + 1) := fun u ↦ x₀ + s • u
  let E' : Set (Space (m + 1)) := T ⁻¹' E
  let Ω' : Set (Space (m + 1)) := T ⁻¹' Ω
  have hmin' : IsLocalPerimeterMinimizer b E' Ω' :=
    hmin.preimage_add_smul (by omega) x₀ hs
  have h0_bdry : (0 : Space (m + 1)) ∈ measureTheoreticBoundary E' := by
    rw [mem_measureTheoreticBoundary_preimage_add_smul E x₀ 0 hs]
    simpa using hx₀
  have hcb2 : closedBall (0 : Space (m + 1)) 2 ⊆ Ω' := by
    intro u hu
    change x₀ + s • u ∈ Ω
    apply hsub
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    have hu' : ‖u‖ ≤ 2 := by simpa using hu
    dsimp [s]
    nlinarith [hr, hu']
  have hcb1 : closedBall (0 : Space (m + 1)) 1 ⊆ Ω' :=
    (closedBall_subset_closedBall (by norm_num)).trans hcb2
  let B₁ : Set (Space (m + 1)) := ball (0 : Space (m + 1)) 1
  have hvol1 : minimizerVolumeDensityConst m ≤ volume.real (E' ∩ B₁) := by
    simpa using hmin'.volume_inter_ball_ge h0_bdry zero_lt_one hcb1
  have hvol2 : minimizerVolumeDensityConst m ≤ volume.real (B₁ \ E') := by
    simpa using hmin'.volume_sdiff_ball_ge h0_bdry zero_lt_one hcb1
  have hP_scale : variationalPerimeter b E' (ball 0 2) =
      ENNReal.ofReal ((s ^ m)⁻¹) * variationalPerimeter b E (ball x₀ r) := by
    have hh := variationalPerimeter_preimage_add_smul_ball (d := m + 1) (by omega) b E x₀ 0 hs
      (ρ := 2)
    have hsr : s * 2 = r := by dsimp [s]; ring
    simpa [E', T, hsr] using hh
  have hPr_fin : variationalPerimeter b E (ball x₀ r) ≠ ⊤ :=
    hmin.perimeter_ball_ne_top x₀ r hr hsub
  have hP'_fin : variationalPerimeter b E' (ball 0 2) ≠ ⊤ := by
    rw [hP_scale]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPr_fin
  let P' : ℝ := (variationalPerimeter b E' (ball 0 2)).toReal
  have hP'_eq : variationalPerimeter b E' (ball 0 2) = ENNReal.ofReal P' :=
    (ENNReal.ofReal_toReal hP'_fin).symm
  let χ : Space (m + 1) → ℝ := E'.indicator (fun _ ↦ (1 : ℝ))
  let v : ℕ → Space (m + 1) → ℝ := fun n ↦ mollify χ n
  let μB : Measure (Space (m + 1)) := volume.restrict B₁
  let : IsFiniteMeasure μB := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact measure_ball_lt_top⟩
  have hχ_int : Integrable χ μB :=
    (integrable_const (1 : ℝ)).indicator hmin'.measurableSet
  have hχc_int : Integrable (E'ᶜ.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ))) μB :=
    (integrable_const (1 : ℝ)).indicator hmin'.measurableSet.compl
  have hχ_diff_id (x y : Space (m + 1)) :
      ‖χ x - χ y‖ =
        χ x * E'ᶜ.indicator (fun _ ↦ (1 : ℝ)) y +
          E'ᶜ.indicator (fun _ ↦ (1 : ℝ)) x * χ y := by
    by_cases hx : x ∈ E' <;> by_cases hy : y ∈ E' <;> simp [χ, hx, hy]
  have hχ_double :
      (∫ x in B₁, ∫ y in B₁, ‖χ x - χ y‖) =
        2 * volume.real (E' ∩ B₁) * volume.real (B₁ \ E') := by
    have hy_c : (∫ y in B₁, E'ᶜ.indicator (fun _ : Space (m + 1) ↦ (1 : ℝ)) y) =
        volume.real (B₁ \ E') := by
      rw [integral_indicator hmin'.measurableSet.compl]
      simp only [setIntegral_const, smul_eq_mul, mul_one, Measure.restrict_restrict
        hmin'.measurableSet.compl, Measure.real]
      have hset : E'ᶜ ∩ B₁ = B₁ \ E' := by ext z; simp [and_comm]
      rw [hset]
    have hy_e : (∫ y in B₁, χ y) = volume.real (E' ∩ B₁) := by
      dsimp [χ]
      rw [integral_indicator hmin'.measurableSet]
      simp [Measure.restrict_restrict hmin'.measurableSet, Measure.real]
    simp_rw [hχ_diff_id]
    have h1 (x : Space (m + 1)) :
        (∫ y in B₁, χ x * E'ᶜ.indicator (fun _ ↦ (1 : ℝ)) y +
            E'ᶜ.indicator (fun _ ↦ (1 : ℝ)) x * χ y) =
          χ x * volume.real (B₁ \ E') +
            E'ᶜ.indicator (fun _ ↦ (1 : ℝ)) x * volume.real (E' ∩ B₁) := by
      rw [integral_add (hχc_int.const_mul (χ x)) (hχ_int.const_mul _),
        integral_const_mul, integral_const_mul, hy_c, hy_e]
    simp_rw [h1]
    rw [integral_add (hχ_int.mul_const _) (hχc_int.mul_const _),
      integral_mul_const, integral_mul_const, hy_e, hy_c]
    ring
  let err : ℕ → ℝ := fun n ↦ ∫ x in closedBall (0 : Space (m + 1)) 1, ‖v n x - χ x‖
  have herr_lim : Tendsto err atTop (𝓝 0) :=
    mollify_phaseIndicator_integral_tendsto hmin'.measurableSet (isCompact_closedBall 0 1)
  have hgrad_ev := eventually_integral_gradient_mollified_phase_le b hmin'.measurableSet
    (r := 1) (R := 2) (by norm_num) ENNReal.toReal_nonneg (le_of_eq hP'_eq)
  have hstep : ∀ᶠ n in atTop,
      2 * volume.real (E' ∩ B₁) * volume.real (B₁ \ E') - 2 * volume.real B₁ * err n ≤
        2 ^ (m + 2) * volume.real B₁ * P' := by
    filter_upwards [hgrad_ev] with n hn_grad
    have hvn : ContDiff ℝ 1 (v n) :=
      (mollify_contDiff_of_locallyIntegrable
        (locallyIntegrable_phaseIndicator hmin'.measurableSet) n).of_le (by simp)
    have hpoinc := integral_unitBall_norm_sub_le_gradient hvn
    have hvn_int : Integrable (v n) μB :=
      (hvn.continuous.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
        ball_subset_closedBall
    have herr_B_int : Integrable (fun x ↦ ‖v n x - χ x‖) μB := (hvn_int.sub hχ_int).norm
    have herr_B_le : (∫ x in B₁, ‖v n x - χ x‖) ≤ err n := by
      have hi_cb : IntegrableOn (fun x ↦ ‖v n x - χ x‖) (closedBall 0 1) volume := by
        let : IsFiniteMeasure (volume.restrict (closedBall (0 : Space (m + 1)) 1)) := ⟨by
          rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
          exact (isCompact_closedBall 0 1).measure_lt_top⟩
        have hχ_cb : IntegrableOn χ (closedBall 0 1) volume :=
          (integrable_const (1 : ℝ)).indicator hmin'.measurableSet
        exact ((hvn.continuous.continuousOn.integrableOn_compact
          (isCompact_closedBall 0 1)).sub hχ_cb).norm
      exact setIntegral_mono_set hi_cb (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (Eventually.of_forall ball_subset_closedBall)
    have htri_double :
        (∫ x in B₁, ∫ y in B₁, ‖χ x - χ y‖) ≤
          (∫ x in B₁, ∫ y in B₁, ‖v n x - v n y‖) +
            2 * volume.real B₁ * ∫ x in B₁, ‖v n x - χ x‖ := by
      have hinner_le (x : Space (m + 1)) :
          (∫ y in B₁, ‖χ x - χ y‖) ≤
            (∫ y in B₁, ‖v n x - v n y‖) +
              volume.real B₁ * ‖v n x - χ x‖ + ∫ y in B₁, ‖v n y - χ y‖ := by
        have hy1 : Integrable (fun y ↦ ‖χ x - χ y‖) μB :=
          ((integrable_const (χ x)).sub hχ_int).norm
        have hy2 : Integrable (fun y ↦ ‖v n x - v n y‖) μB :=
          ((integrable_const (v n x)).sub hvn_int).norm
        have hy3 : Integrable (fun _ : Space (m + 1) ↦ ‖v n x - χ x‖) μB :=
          integrable_const _
        have hpt (y : Space (m + 1)) :
            ‖χ x - χ y‖ ≤ ‖v n x - v n y‖ + ‖v n x - χ x‖ + ‖v n y - χ y‖ := by
          have h1 := norm_add_le (χ x - v n x) (v n x - χ y)
          have h2 := norm_add_le (v n x - v n y) (v n y - χ y)
          rw [sub_add_sub_cancel] at h1 h2
          rw [norm_sub_rev (χ x) (v n x)] at h1
          linarith
        have hy23 : Integrable (fun y ↦ ‖v n x - v n y‖ + ‖v n x - χ x‖) μB := hy2.add hy3
        have hm := integral_mono hy1 (hy23.add herr_B_int) hpt
        change (∫ y, ‖χ x - χ y‖ ∂μB) ≤
          ∫ y, ((‖v n x - v n y‖ + ‖v n x - χ x‖) + ‖v n y - χ y‖) ∂μB at hm
        rw [integral_add hy23 herr_B_int, integral_add hy2 hy3,
          setIntegral_const, smul_eq_mul] at hm
        exact hm
      have hf1 : Integrable (fun x ↦ ∫ y in B₁, ‖χ x - χ y‖) μB := by
        have hp_int : Integrable (fun p : Space (m + 1) × Space (m + 1) ↦ ‖χ p.1 - χ p.2‖)
            (μB.prod μB) := ((hχ_int.comp_fst μB).sub (hχ_int.comp_snd μB)).norm
        exact hp_int.integral_prod_left
      have hf2 : Integrable (fun x ↦ ∫ y in B₁, ‖v n x - v n y‖) μB := by
        have hp_int : Integrable (fun p : Space (m + 1) × Space (m + 1) ↦ ‖v n p.1 - v n p.2‖)
            (μB.prod μB) := ((hvn_int.comp_fst μB).sub (hvn_int.comp_snd μB)).norm
        exact hp_int.integral_prod_left
      have hf3 : Integrable (fun x ↦ volume.real B₁ * ‖v n x - χ x‖) μB :=
        herr_B_int.const_mul _
      have hf4 : Integrable (fun _ : Space (m + 1) ↦ ∫ y in B₁, ‖v n y - χ y‖) μB :=
        integrable_const _
      have hf23 : Integrable
          (fun x ↦ (∫ y in B₁, ‖v n x - v n y‖) + volume.real B₁ * ‖v n x - χ x‖) μB :=
        hf2.add hf3
      have hm := integral_mono hf1 (hf23.add hf4) hinner_le
      change (∫ x, (∫ y in B₁, ‖χ x - χ y‖) ∂μB) ≤
        ∫ x, (((∫ y in B₁, ‖v n x - v n y‖) + volume.real B₁ * ‖v n x - χ x‖) +
          ∫ y in B₁, ‖v n y - χ y‖) ∂μB at hm
      rw [integral_add hf23 hf4, integral_add hf2 hf3,
        integral_const_mul, setIntegral_const, smul_eq_mul] at hm
      linarith
    have hω_nonneg : 0 ≤ volume.real B₁ := measureReal_nonneg
    have hrhs_le : 2 ^ (m + 2) * volume.real B₁ * (∫ z in B₁, ‖gradient (v n) z‖) ≤
        2 ^ (m + 2) * volume.real B₁ * P' :=
      mul_le_mul_of_nonneg_left hn_grad (mul_nonneg (by positivity) hω_nonneg)
    have herr_mul_le : 2 * volume.real B₁ * (∫ x in B₁, ‖v n x - χ x‖) ≤
        2 * volume.real B₁ * err n :=
      mul_le_mul_of_nonneg_left herr_B_le (mul_nonneg (by norm_num) hω_nonneg)
    linarith [hχ_double, htri_double, hpoinc, hrhs_le, herr_mul_le]
  have hlhs_lim : Tendsto
      (fun n ↦ 2 * volume.real (E' ∩ B₁) * volume.real (B₁ \ E') - 2 * volume.real B₁ * err n)
      atTop (𝓝 (2 * volume.real (E' ∩ B₁) * volume.real (B₁ \ E'))) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub ((tendsto_const_nhds (x := 2 * volume.real B₁)).mul herr_lim))
  have hlim_ineq : 2 * volume.real (E' ∩ B₁) * volume.real (B₁ \ E') ≤
      2 ^ (m + 2) * volume.real B₁ * P' :=
    le_of_tendsto hlhs_lim hstep
  have hc_pos : 0 < minimizerVolumeDensityConst m := minimizerVolumeDensityConst_pos m
  have hprod_ge : 2 * (minimizerVolumeDensityConst m) ^ 2 ≤
      2 * volume.real (E' ∩ B₁) * volume.real (B₁ \ E') := by
    have hsq : (minimizerVolumeDensityConst m) ^ 2 ≤
        volume.real (E' ∩ B₁) * volume.real (B₁ \ E') := by
      rw [sq]
      exact mul_le_mul hvol1 hvol2 hc_pos.le measureReal_nonneg
    linarith
  have hP'_toReal : P' = ((s ^ m)⁻¹) * (variationalPerimeter b E (ball x₀ r)).toReal := by
    dsimp [P']
    rw [hP_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hs.le m))]
  have hsm_inv : (s ^ m)⁻¹ = (2 : ℝ) ^ m / r ^ m := by
    dsimp [s]
    rw [div_pow, inv_div]
  have hω_pos : 0 < volume.real B₁ :=
    ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  have hrm_pos : 0 < r ^ m := pow_pos hr m
  have hcomb : 2 * (minimizerVolumeDensityConst m) ^ 2 ≤
      2 * (2 ^ (2 * m + 1) * volume.real B₁) *
        ((variationalPerimeter b E (ball x₀ r)).toReal / r ^ m) := by
    have hpow2 : (2 : ℝ) ^ (m + 2) * (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (2 * m + 1) := by
      rw [← pow_add, show m + 2 + m = (2 * m + 1) + 1 by omega, pow_succ]
      ring
    calc
      2 * (minimizerVolumeDensityConst m) ^ 2 ≤ 2 ^ (m + 2) * volume.real B₁ * P' :=
        hprod_ge.trans hlim_ineq
      _ = 2 ^ (m + 2) * volume.real B₁ *
          (((2 : ℝ) ^ m / r ^ m) * (variationalPerimeter b E (ball x₀ r)).toReal) := by
        rw [hP'_toReal, hsm_inv]
      _ = ((2 : ℝ) ^ (m + 2) * (2 : ℝ) ^ m) * volume.real B₁ *
          ((variationalPerimeter b E (ball x₀ r)).toReal / r ^ m) := by
        ring
      _ = 2 * (2 ^ (2 * m + 1) * volume.real B₁) *
          ((variationalPerimeter b E (ball x₀ r)).toReal / r ^ m) := by
        rw [hpow2]
        ring
  have hdiv_ineq : (minimizerVolumeDensityConst m) ^ 2 ≤
      (2 ^ (2 * m + 1) * volume.real B₁) *
        ((variationalPerimeter b E (ball x₀ r)).toReal / r ^ m) := by
    linarith
  have hden_pos : 0 < (2 : ℝ) ^ (2 * m + 1) * volume.real B₁ := by positivity
  rw [minimizerPerimeterLowerConst, div_mul_eq_mul_div, div_le_iff₀ hden_pos]
  have hmul := mul_le_mul_of_nonneg_right hdiv_ineq hrm_pos.le
  have hrhs_simp : (2 ^ (2 * m + 1) * volume.real B₁) *
      ((variationalPerimeter b E (ball x₀ r)).toReal / r ^ m) * r ^ m =
      (variationalPerimeter b E (ball x₀ r)).toReal * (2 ^ (2 * m + 1) * volume.real B₁) := by
    rw [mul_assoc, div_mul_cancel₀ _ hrm_pos.ne', mul_comm]
  rwa [hrhs_simp] at hmul

/-- Lower perimeter bound on any interior ball centered on `measureTheoreticBoundary E`
(BV6.2, `ℝ≥0∞` form). -/
theorem IsLocalPerimeterMinimizer.variationalPerimeter_ball_ge {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)}
    (hx₀ : x₀ ∈ measureTheoreticBoundary E) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall x₀ r ⊆ Ω) :
    ENNReal.ofReal (minimizerPerimeterLowerConst m * r ^ m) ≤
      variationalPerimeter b E (ball x₀ r) := by
  have hfin := hmin.perimeter_ball_ne_top x₀ r hr hsub
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal (hmin.variationalPerimeter_ball_toReal_ge hx₀ hr hsub)

/-! ### 5. Canonical open representatives, support identity, and coarse `μH[m]` bound (BV7) -/

/-- The measure-theoretic boundary of a local perimeter minimizer has Lebesgue measure zero
inside `Ω` (BV7). -/
theorem IsLocalPerimeterMinimizer.measure_measureTheoreticBoundary_inter_eq_zero {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) :
    volume (measureTheoreticBoundary E ∩ Ω) = 0 := by
  rw [← compl_mem_ae_iff]
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
    hmin.measurableSet] with x hdens ⟨hx_bdry, hxΩ⟩
  obtain ⟨r₀, hr₀, hcb₀⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hmin.isOpen_domain.mem_nhds hxΩ)
  let ω := volume.real (ball (0 : Space (m + 1)) 1)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne'
    measure_ball_ne_top
  let θ : ℝ := minimizerVolumeDensityConst m / ω
  have hθ : 0 < θ := div_pos (minimizerVolumeDensityConst_pos m) hω
  let q : ℝ → ℝ≥0∞ := fun r ↦ volume (E ∩ closedBall x r) / volume (closedBall x r)
  have hq_bounds {r : ℝ} (hr : r ∈ Ioo 0 r₀) :
      ENNReal.ofReal θ ≤ q r ∧ q r ≤ ENNReal.ofReal (1 - θ) := by
    have hr_pos : 0 < r := hr.1
    have hcb : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hr.2.le).trans hcb₀
    have hv1 := hmin.volume_inter_ball_ge hx_bdry hr_pos hcb
    have hv2 := hmin.volume_sdiff_ball_ge hx_bdry hr_pos hcb
    have hsphere : volume (sphere x r) = 0 := volume.addHaar_sphere x r
    have hinter_eq : volume (E ∩ closedBall x r) = volume (E ∩ ball x r) := by
      apply le_antisymm _ (measure_mono (inter_subset_inter_right E ball_subset_closedBall))
      have hcov : E ∩ closedBall x r ⊆ (E ∩ ball x r) ∪ sphere x r := by
        intro y ⟨hyE, hycb⟩
        rcases (mem_closedBall.mp hycb).lt_or_eq with hlt | heq
        · exact Or.inl ⟨hyE, hlt⟩
        · exact Or.inr heq
      calc
        volume (E ∩ closedBall x r) ≤ volume ((E ∩ ball x r) ∪ sphere x r) := measure_mono hcov
        _ ≤ volume (E ∩ ball x r) + volume (sphere x r) := measure_union_le _ _
        _ = volume (E ∩ ball x r) := by rw [hsphere, add_zero]
    have hcb_eq : volume (closedBall x r) = volume (ball x r) :=
      volume.addHaar_closedBall_eq_addHaar_ball x r
    have hball_vol : volume.real (ball x r) = ω * r ^ (m + 1) := by
      change (volume (ball x r)).toReal = _
      rw [volume.addHaar_ball_of_pos x hr_pos, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hr_pos.le _)]
      simp only [Space, finrank_euclideanSpace_fin]
      change r ^ (m + 1) * ω = ω * r ^ (m + 1)
      ring
    have hsum : volume.real (E ∩ ball x r) + volume.real (ball x r \ E) =
        volume.real (ball x r) := by
      have hm := measure_inter_add_sdiff (ball x r) hmin.measurableSet (μ := volume)
      have h1 : volume (ball x r ∩ E) ≠ ⊤ :=
        ne_top_of_le_ne_top measure_ball_ne_top (measure_mono inter_subset_left)
      have h2 : volume (ball x r \ E) ≠ ⊤ :=
        ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)
      rw [inter_comm] at hm h1
      simpa only [Measure.real, ENNReal.toReal_add h1 h2] using congrArg ENNReal.toReal hm
    have hcb_pos : volume (closedBall x r) ≠ 0 := by
      rw [hcb_eq]
      exact (measure_ball_pos volume x hr_pos).ne'
    have hcb_fin : volume (closedBall x r) ≠ ⊤ :=
      (isCompact_closedBall x r).measure_ne_top
    have hnum_fin : volume (E ∩ closedBall x r) ≠ ⊤ :=
      ne_top_of_le_ne_top hcb_fin (measure_mono inter_subset_right)
    have hqr_fin : q r ≠ ⊤ := ENNReal.div_ne_top hnum_fin hcb_pos
    have hqr_real : (q r).toReal = volume.real (E ∩ ball x r) / (ω * r ^ (m + 1)) := by
      dsimp [q]
      rw [ENNReal.toReal_div, hinter_eq, hcb_eq, ← measureReal_def, ← measureReal_def, hball_vol]
    have hden_pos : 0 < ω * r ^ (m + 1) := mul_pos hω (pow_pos hr_pos (m + 1))
    have hlow : θ ≤ (q r).toReal := by
      rw [hqr_real, le_div_iff₀ hden_pos]
      calc
        θ * (ω * r ^ (m + 1)) = (θ * ω) * r ^ (m + 1) := by ring
        _ = minimizerVolumeDensityConst m * r ^ (m + 1) := by
          dsimp [θ]
          rw [div_mul_cancel₀ _ hω.ne']
        _ ≤ volume.real (E ∩ ball x r) := hv1
    have hhigh : (q r).toReal ≤ 1 - θ := by
      rw [hqr_real, div_le_iff₀ hden_pos]
      have hθω : (1 - θ) * (ω * r ^ (m + 1)) =
          ω * r ^ (m + 1) - minimizerVolumeDensityConst m * r ^ (m + 1) := by
        have hh : θ * ω = minimizerVolumeDensityConst m := div_mul_cancel₀ _ hω.ne'
        calc
          (1 - θ) * (ω * r ^ (m + 1)) = ω * r ^ (m + 1) - (θ * ω) * r ^ (m + 1) := by ring
          _ = ω * r ^ (m + 1) - minimizerVolumeDensityConst m * r ^ (m + 1) := by rw [hh]
      linarith [hsum, hball_vol, hv2, hθω]
    rw [← ENNReal.ofReal_toReal hqr_fin]
    exact ⟨ENNReal.ofReal_le_ofReal hlow, ENNReal.ofReal_le_ofReal hhigh⟩
  by_cases hxE : x ∈ E
  · have hlim : Tendsto q (𝓝[>] 0) (𝓝 1) := by simpa [q, hxE] using hdens
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), q r ≤ ENNReal.ofReal (1 - θ) := by
      filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
      exact (hq_bounds hr).2
    have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - θ) := le_of_tendsto hlim hev
    have hlt : ENNReal.ofReal (1 - θ) < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
    exact not_lt_of_ge hle hlt
  · have hlim : Tendsto q (𝓝[>] 0) (𝓝 0) := by simpa [q, hxE] using hdens
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal θ ≤ q r := by
      filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
      exact (hq_bounds hr).1
    have hge : ENNReal.ofReal θ ≤ 0 := ge_of_tendsto hlim hev
    exact not_lt_of_ge hge (ENNReal.ofReal_pos.mpr hθ)

/-- Inside `Ω`, a local perimeter minimizer agrees almost everywhere with its open canonical
representative `measureTheoreticInterior E` (BV7). -/
theorem IsLocalPerimeterMinimizer.ae_mem_iff_measureTheoreticInterior {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) :
    ∀ᵐ x ∂volume, x ∈ Ω → (x ∈ E ↔ x ∈ measureTheoreticInterior E) := by
  have hnull := hmin.measure_measureTheoreticBoundary_inter_eq_zero
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
    hmin.measurableSet, compl_mem_ae_iff.mpr hnull] with x hdens hx_not_bdry hxΩ
  have hx_union : x ∈ measureTheoreticInterior E ∪ measureTheoreticExterior E := by
    by_contra hnot
    have hmem : x ∈ measureTheoreticBoundary E := by
      rw [← compl_measureTheoreticInterior_union_exterior]
      exact hnot
    exact hx_not_bdry ⟨hmem, hxΩ⟩
  let q : ℝ → ℝ≥0∞ := fun r ↦ volume (E ∩ closedBall x r) / volume (closedBall x r)
  rcases hx_union with hx_int | hx_ext
  · refine ⟨fun _ ↦ hx_int, fun _ ↦ ?_⟩
    obtain ⟨r₀, hr₀, hvol₀⟩ := hx_int
    have hev : q =ᶠ[𝓝[>] 0] fun _ ↦ (1 : ℝ≥0∞) := by
      filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
      have hcb_pos : volume (closedBall x r) ≠ 0 := by
        rw [volume.addHaar_closedBall_eq_addHaar_ball x r]
        exact (measure_ball_pos volume x hr.1).ne'
      have hcb_fin : volume (closedBall x r) ≠ ⊤ :=
        (isCompact_closedBall x r).measure_ne_top
      have hsdiff0 : volume (closedBall x r \ E) = 0 :=
        measure_mono_null (sdiff_subset_sdiff (closedBall_subset_ball hr.2) Subset.rfl) hvol₀
      have heq : volume (E ∩ closedBall x r) = volume (closedBall x r) := by
        have hm := measure_inter_add_sdiff (closedBall x r) hmin.measurableSet (μ := volume)
        rw [inter_comm, hsdiff0, add_zero] at hm
        exact hm
      dsimp [q]
      rw [heq]
      exact ENNReal.div_self hcb_pos hcb_fin
    by_contra hxE
    have hlim0 : Tendsto q (𝓝[>] 0) (𝓝 0) := by simpa [q, hxE] using hdens
    have hlim1 : Tendsto q (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds.congr' hev.symm
    exact zero_ne_one (tendsto_nhds_unique hlim0 hlim1)
  · have hx_not_int : x ∉ measureTheoreticInterior E :=
      disjoint_right.mp (disjoint_measureTheoreticInterior_exterior E) hx_ext
    refine ⟨fun hxE ↦ ?_, fun hx_int ↦ (hx_not_int hx_int).elim⟩
    obtain ⟨r₀, hr₀, hvol₀⟩ := hx_ext
    have hev : q =ᶠ[𝓝[>] 0] fun _ ↦ (0 : ℝ≥0∞) := by
      filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
      have hinter0 : volume (E ∩ closedBall x r) = 0 :=
        measure_mono_null (inter_subset_inter_right E (closedBall_subset_ball hr.2)) hvol₀
      dsimp [q]
      rw [hinter0, ENNReal.zero_div]
    have hlim1 : Tendsto q (𝓝[>] 0) (𝓝 1) := by simpa [q, hxE] using hdens
    have hlim0 : Tendsto q (𝓝[>] 0) (𝓝 0) := tendsto_const_nhds.congr' hev.symm
    exact False.elim (zero_ne_one (tendsto_nhds_unique hlim0 hlim1))

/-- Inside `Ω`, the complement `Eᶜ` agrees almost everywhere with `measureTheoreticExterior E`. -/
theorem IsLocalPerimeterMinimizer.ae_mem_compl_iff_measureTheoreticExterior {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) :
    ∀ᵐ x ∂volume, x ∈ Ω → (x ∈ Eᶜ ↔ x ∈ measureTheoreticExterior E) := by
  rw [measureTheoreticExterior_eq_interior_compl]
  exact hmin.compl.ae_mem_iff_measureTheoreticInterior

/-- Inside `Ω`, the topological frontier of `measureTheoreticInterior E` coincides with
`measureTheoreticBoundary E` (BV7). -/
theorem IsLocalPerimeterMinimizer.frontier_measureTheoreticInterior_inter_eq {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) :
    frontier (measureTheoreticInterior E) ∩ Ω = measureTheoreticBoundary E ∩ Ω := by
  apply Subset.antisymm
  · exact inter_subset_inter_left Ω (frontier_measureTheoreticInterior_subset E)
  · rintro x ⟨hx_bdry, hxΩ⟩
    refine ⟨?_, hxΩ⟩
    rw [frontier, (isOpen_measureTheoreticInterior E).interior_eq]
    refine ⟨Metric.mem_closure_iff.mpr fun r hr ↦ ?_, ?_⟩
    · obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hmin.isOpen_domain x hxΩ
      let ρ := min r r₀
      have hρ : 0 < ρ := lt_min hr hr₀
      have hρ_Ω : ball x ρ ⊆ Ω := (ball_subset_ball (min_le_right _ _)).trans hball₀
      let N := {y : Space (m + 1) | ¬(y ∈ Ω → (y ∈ E ↔ y ∈ measureTheoreticInterior E))}
      have hN : volume N = 0 := ae_iff.mp hmin.ae_mem_iff_measureTheoreticInterior
      have hne : (measureTheoreticInterior E ∩ ball x ρ).Nonempty := by
        by_contra hempty
        rw [not_nonempty_iff_eq_empty] at hempty
        have hsub : E ∩ ball x ρ ⊆ (measureTheoreticInterior E ∩ ball x ρ) ∪ N := by
          intro y ⟨hyE, hyb⟩
          by_cases hyN : y ∈ N
          · exact Or.inr hyN
          · exact Or.inl ⟨(not_not.mp hyN (hρ_Ω hyb)).mp hyE, hyb⟩
        have hzero : volume (E ∩ ball x ρ) = 0 := by
          refine nonpos_iff_eq_zero.mp ?_
          calc
            volume (E ∩ ball x ρ) ≤ volume ((measureTheoreticInterior E ∩ ball x ρ) ∪ N) :=
              measure_mono hsub
            _ = volume N := by rw [hempty, empty_union]
            _ = 0 := hN
        exact (hx_bdry ρ hρ).1 hzero
      obtain ⟨y, hy_int, hy_ρ⟩ := hne
      refine ⟨y, hy_int, ?_⟩
      rw [dist_comm]
      exact mem_ball.mp (ball_subset_ball (min_le_left _ _) hy_ρ)
    · intro hx_int
      rw [← compl_measureTheoreticInterior_union_exterior] at hx_bdry
      exact hx_bdry (Or.inl hx_int)

/-- Inside `Ω`, the topological frontier of `measureTheoreticExterior E` also coincides with
`measureTheoreticBoundary E` (BV7). -/
theorem IsLocalPerimeterMinimizer.frontier_measureTheoreticExterior_inter_eq {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) :
    frontier (measureTheoreticExterior E) ∩ Ω = measureTheoreticBoundary E ∩ Ω := by
  rw [measureTheoreticExterior_eq_interior_compl, ← measureTheoreticBoundary_compl E]
  exact hmin.compl.frontier_measureTheoreticInterior_inter_eq

/-- An interior ball carries positive variational perimeter if and only if it intersects
`measureTheoreticBoundary E` (BV7.1 preparation). -/
theorem IsLocalPerimeterMinimizer.variationalPerimeter_ball_pos_iff {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {x₀ : Space (m + 1)} {r : ℝ}
    (hsub : closedBall x₀ r ⊆ Ω) :
    0 < variationalPerimeter b E (ball x₀ r) ↔
      (ball x₀ r ∩ measureTheoreticBoundary E).Nonempty := by
  constructor
  · intro hpos
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    let U₁ := measureTheoreticInterior E
    let U₀ := measureTheoreticExterior E
    have hcov : ball x₀ r ⊆ U₁ ∪ U₀ := by
      intro x hx
      by_contra hnot
      have hx_bdry : x ∈ measureTheoreticBoundary E := by
        rw [← compl_measureTheoreticInterior_union_exterior]
        exact hnot
      have hmem : x ∈ ball x₀ r ∩ measureTheoreticBoundary E := ⟨hx, hx_bdry⟩
      rw [hempty] at hmem
      exact hmem
    have hprec : IsPreconnected (ball x₀ r) := (convex_ball x₀ r).isPreconnected
    have hball_Ω : ball x₀ r ⊆ Ω := ball_subset_closedBall.trans hsub
    have hzero : variationalPerimeter b E (ball x₀ r) = 0 := by
      by_cases h1 : (ball x₀ r ∩ U₁).Nonempty
      · have h0_empty : ball x₀ r ∩ U₀ = ∅ := by
          rw [← not_nonempty_iff_eq_empty]
          intro h0
          obtain ⟨z, -, hz₁, hz₀⟩ := hprec U₁ U₀ (isOpen_measureTheoreticInterior E)
            (isOpen_measureTheoreticExterior E) hcov h1 h0
          exact disjoint_left.mp (disjoint_measureTheoreticInterior_exterior E) hz₁ hz₀
        have hsub₁ : ball x₀ r ⊆ U₁ := by
          intro x hx
          rcases hcov hx with hx₁ | hx₀
          · exact hx₁
          · exfalso
            have hm : x ∈ ball x₀ r ∩ U₀ := ⟨hx, hx₀⟩
            rw [h0_empty] at hm
            exact hm
        have heq : variationalPerimeter b E (ball x₀ r) =
            variationalPerimeter b univ (ball x₀ r) := by
          apply variationalPerimeter_congr_ae_on b
          filter_upwards [hmin.ae_mem_iff_measureTheoreticInterior] with x hx hxb
          simp [(hx (hball_Ω hxb)).mpr (hsub₁ hxb)]
        rw [heq, variationalPerimeter_univ]
      · rw [not_nonempty_iff_eq_empty] at h1
        have hsub₀ : ball x₀ r ⊆ U₀ := by
          intro x hx
          rcases hcov hx with hx₁ | hx₀
          · exfalso
            have hm : x ∈ ball x₀ r ∩ U₁ := ⟨hx, hx₁⟩
            rw [h1] at hm
            exact hm
          · exact hx₀
        have heq : variationalPerimeter b E (ball x₀ r) =
            variationalPerimeter b ∅ (ball x₀ r) := by
          apply variationalPerimeter_congr_ae_on b
          filter_upwards [hmin.ae_mem_iff_measureTheoreticInterior] with x hx hxb
          have hnot₁ : x ∉ measureTheoreticInterior E :=
            disjoint_right.mp (disjoint_measureTheoreticInterior_exterior E) (hsub₀ hxb)
          simp [hx (hball_Ω hxb), hnot₁]
        rw [heq, variationalPerimeter_empty]
    exact hpos.ne' hzero
  · rintro ⟨y, hy_ball, hy_bdry⟩
    let ρ := (r - dist y x₀) / 2
    have hρ : 0 < ρ := by
      dsimp [ρ]
      linarith [mem_ball.mp hy_ball]
    have hcb_y : closedBall y ρ ⊆ ball x₀ r := by
      intro z hz
      rw [mem_ball]
      calc
        dist z x₀ ≤ dist z y + dist y x₀ := dist_triangle z y x₀
        _ ≤ ρ + dist y x₀ := add_le_add (mem_closedBall.mp hz) le_rfl
        _ < r := by dsimp [ρ]; linarith [mem_ball.mp hy_ball]
    have hpos_low : 0 < ENNReal.ofReal (minimizerPerimeterLowerConst m * ρ ^ m) :=
      ENNReal.ofReal_pos.mpr (mul_pos (minimizerPerimeterLowerConst_pos m) (pow_pos hρ m))
    calc
      0 < ENNReal.ofReal (minimizerPerimeterLowerConst m * ρ ^ m) := hpos_low
      _ ≤ variationalPerimeter b E (ball y ρ) :=
        hmin.variationalPerimeter_ball_ge hy_bdry hρ (hcb_y.trans (ball_subset_closedBall.trans hsub))
      _ ≤ variationalPerimeter b E (ball x₀ r) :=
        variationalPerimeter_mono b E (ball_subset_closedBall.trans hcb_y)

/-- Support identity inside `Ω` for any measure agreeing with `variationalPerimeter b E` on open
subsets of `Ω` (BV7.1). -/
theorem IsLocalPerimeterMinimizer.support_measure_inter_eq {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U) :
    Measure.support μ ∩ Ω = measureTheoreticBoundary E ∩ Ω := by
  ext x
  simp only [mem_inter_iff]
  refine ⟨fun ⟨hx_supp, hxΩ⟩ ↦ ⟨?_, hxΩ⟩, fun ⟨hx_bdry, hxΩ⟩ ↦ ⟨?_, hxΩ⟩⟩
  · by_contra hx_not_bdry
    have hopen : IsOpen (Ω ∩ (measureTheoreticBoundary E)ᶜ) :=
      hmin.isOpen_domain.inter (isClosed_measureTheoreticBoundary E).isOpen_compl
    obtain ⟨r, hr, hcb⟩ :=
      Metric.nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds ⟨hxΩ, hx_not_bdry⟩)
    have hcb_Ω : closedBall x r ⊆ Ω := fun y hy ↦ (hcb hy).1
    have hempty : ¬(ball x r ∩ measureTheoreticBoundary E).Nonempty := by
      rintro ⟨y, hyb, hy_bdry⟩
      exact (hcb (ball_subset_closedBall hyb)).2 hy_bdry
    have hP0 : variationalPerimeter b E (ball x r) = 0 := by
      by_contra hne
      exact hempty ((hmin.variationalPerimeter_ball_pos_iff hcb_Ω).mp (pos_iff_ne_zero.mpr hne))
    have hμ0 : μ (ball x r) = 0 := by
      rw [hμ (ball x r) isOpen_ball (ball_subset_closedBall.trans hcb_Ω), hP0]
    have hpos : 0 < μ (ball x r) :=
      (Measure.mem_support_iff_forall x).mp hx_supp (ball x r)
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    exact hpos.ne' hμ0
  · rw [Measure.mem_support_iff_forall]
    intro U hU
    have hUΩ : U ∩ Ω ∈ 𝓝 x := Filter.inter_mem hU (hmin.isOpen_domain.mem_nhds hxΩ)
    obtain ⟨r, hr, hcb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hUΩ
    have hcb_Ω : closedBall x r ⊆ Ω := fun y hy ↦ (hcb hy).2
    have hball_U : ball x r ⊆ U := fun y hy ↦ (hcb (ball_subset_closedBall hy)).1
    have hpos : 0 < variationalPerimeter b E (ball x r) :=
      (hmin.variationalPerimeter_ball_pos_iff hcb_Ω).mpr ⟨x, mem_ball_self hr, hx_bdry⟩
    calc
      0 < variationalPerimeter b E (ball x r) := hpos
      _ = μ (ball x r) := (hμ (ball x r) isOpen_ball (ball_subset_closedBall.trans hcb_Ω)).symm
      _ ≤ μ U := measure_mono hball_U

/-- Explicit positive dimensional constant controlling the Hausdorff `m`-measure of
`measureTheoreticBoundary E` by variational perimeter in `Space (m + 1)`. -/
def minimizerHausdorffConst (m : ℕ) : ℝ :=
  (10 : ℝ) ^ m / minimizerPerimeterLowerConst m

theorem minimizerHausdorffConst_pos (m : ℕ) : 0 < minimizerHausdorffConst m :=
  div_pos (by positivity) (minimizerPerimeterLowerConst_pos m)

/-- Coarse Hausdorff `m`-measure bound for `K ∩ measureTheoreticBoundary E` in terms of
variational perimeter on any open neighborhood `V` of `K` with `V ⊆ Ω` (BV7.2, open form). -/
theorem IsLocalPerimeterMinimizer.hausdorffMeasure_inter_boundary_le_open {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {K V : Set (Space (m + 1))}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) (hVΩ : V ⊆ Ω) :
    μH[(m : ℝ)] (K ∩ measureTheoreticBoundary E) ≤
      ENNReal.ofReal (minimizerHausdorffConst m) * variationalPerimeter b E V := by
  have hC_pos : 0 < minimizerHausdorffConst m := minimizerHausdorffConst_pos m
  by_cases hPV : variationalPerimeter b E V = ⊤
  · rw [hPV, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hC_pos).ne']
    exact le_top
  obtain ⟨σ, hmass, -, -, hdist⟩ :=
    exists_perimeter_vector_measure_concentrated b hmin.measurableSet hV.measurableSet hPV
  let ν := σ.variation
  let : IsFiniteMeasure ν := ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr hPV⟩
  have hν_open (U : Set (Space (m + 1))) (hU : IsOpen U) (hUV : U ⊆ V) :
      ν U = variationalPerimeter b E U :=
    variation_eq_variationalPerimeter_of_representation b σ hdist hU hUV
  let S := K ∩ measureTheoreticBoundary E
  have hS_comp : IsCompact S := hK.inter_right (isClosed_measureTheoreticBoundary E)
  have hSV : S ⊆ V := inter_subset_left.trans hKV
  obtain ⟨δ₀, hδ₀, hthick⟩ := hS_comp.exists_thickening_subset_open hV hSV
  have hcb_V {x : Space (m + 1)} (hx : x ∈ S) {ρ : ℝ} (hρ : ρ ≤ δ₀ / 2) :
      closedBall x ρ ⊆ V := by
    have hlt : ρ < δ₀ := by linarith
    exact (closedBall_subset_ball hlt).trans ((ball_subset_thickening hx δ₀).trans hthick)
  let ρ : ℕ → ℝ := fun n ↦ (δ₀ / 2) * (1 / ((n : ℝ) + 1))
  have hρ_pos (n : ℕ) : 0 < ρ n := by dsimp [ρ]; positivity
  have hρ_le (n : ℕ) : ρ n ≤ δ₀ / 2 := by
    dsimp [ρ]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith
  have hvitali (n : ℕ) :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball S id (fun _ ↦ ρ n) (ρ n)
      (fun _ _ ↦ le_rfl) 5 (by norm_num)
  choose u hu_sub hu_disj hu_cov using hvitali
  let : ∀ n, Countable (u n) := fun n ↦
    ((hu_disj n).subtype _ _).countable_of_isOpen_disjoint
      (fun _ ↦ isOpen_ball) (fun _ ↦ nonempty_ball.mpr (hρ_pos n))
  let R_seq : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (10 * ρ n)
  have hR_lim : Tendsto R_seq atTop (𝓝 0) := by
    have hρ_lim : Tendsto (fun n ↦ 10 * ρ n) atTop (𝓝 0) := by
      have h0 := (tendsto_const_nhds (x := 10 * (δ₀ / 2))).mul
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [ρ, mul_assoc, mul_zero] using h0
    simpa only [R_seq, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hρ_lim
  let cover : ∀ n : ℕ, u n → Set (Space (m + 1)) := fun n y ↦ ball (y : Space (m + 1)) (5 * ρ n)
  have hediam (n : ℕ) (y : u n) : ediam (cover n y) ≤ R_seq n := by
    refine ediam_le_of_forall_dist_le fun z₁ hz₁ z₂ hz₂ ↦ ?_
    calc
      dist z₁ z₂ ≤ dist z₁ (y : Space (m + 1)) + dist (y : Space (m + 1)) z₂ :=
        dist_triangle z₁ y z₂
      _ ≤ 5 * ρ n + 5 * ρ n := by
        rw [dist_comm (y : Space (m + 1)) z₂]
        exact add_le_add (mem_ball.mp hz₁).le (mem_ball.mp hz₂).le
      _ = 10 * ρ n := by ring
  have hS_cov (n : ℕ) : S ⊆ ⋃ y : u n, cover n y := by
    intro x hx
    obtain ⟨y, hyu, hball_sub⟩ := hu_cov n x hx
    exact mem_iUnion.mpr ⟨⟨y, hyu⟩, hball_sub (mem_ball_self (hρ_pos n))⟩
  have hH_le := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (m : ℝ) S R_seq hR_lim
    cover (Eventually.of_forall hediam) (Eventually.of_forall hS_cov)
  refine hH_le.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n ↦ ?_))
  have hterm (y : u n) :
      ediam (cover n y) ^ (m : ℝ) ≤
        ENNReal.ofReal (minimizerHausdorffConst m) * ν (ball (y : Space (m + 1)) (ρ n)) := by
    have hyS : (y : Space (m + 1)) ∈ S := hu_sub n y.2
    have hcb_y : closedBall (y : Space (m + 1)) (ρ n) ⊆ V := hcb_V hyS (hρ_le n)
    have hball_y_V : ball (y : Space (m + 1)) (ρ n) ⊆ V := ball_subset_closedBall.trans hcb_y
    have hlow := hmin.variationalPerimeter_ball_ge hyS.2 (hρ_pos n) (hcb_y.trans hVΩ)
    have hed_pow : ediam (cover n y) ^ (m : ℝ) ≤ ENNReal.ofReal ((10 : ℝ) ^ m * ρ n ^ m) := by
      calc
        ediam (cover n y) ^ (m : ℝ) ≤ (R_seq n) ^ (m : ℝ) :=
          ENNReal.rpow_le_rpow (hediam n y) (Nat.cast_nonneg m)
        _ = ENNReal.ofReal ((10 * ρ n) ^ m) := by
          dsimp [R_seq]
          rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (by positivity)]
        _ = ENNReal.ofReal ((10 : ℝ) ^ m * ρ n ^ m) := by rw [mul_pow]
    have hconst_id : (10 : ℝ) ^ m * ρ n ^ m =
        minimizerHausdorffConst m * (minimizerPerimeterLowerConst m * ρ n ^ m) := by
      have hpos_low : minimizerPerimeterLowerConst m ≠ 0 := (minimizerPerimeterLowerConst_pos m).ne'
      unfold minimizerHausdorffConst
      field_simp
    calc
      ediam (cover n y) ^ (m : ℝ) ≤ ENNReal.ofReal ((10 : ℝ) ^ m * ρ n ^ m) := hed_pow
      _ = ENNReal.ofReal (minimizerHausdorffConst m) *
          ENNReal.ofReal (minimizerPerimeterLowerConst m * ρ n ^ m) := by
        rw [hconst_id, ENNReal.ofReal_mul hC_pos.le]
      _ ≤ ENNReal.ofReal (minimizerHausdorffConst m) *
          variationalPerimeter b E (ball (y : Space (m + 1)) (ρ n)) :=
        mul_le_mul_of_nonneg_left hlow zero_le
      _ = ENNReal.ofReal (minimizerHausdorffConst m) * ν (ball (y : Space (m + 1)) (ρ n)) := by
        rw [hν_open _ isOpen_ball hball_y_V]
  calc
    (∑' y : u n, ediam (cover n y) ^ (m : ℝ)) ≤
        ∑' y : u n, ENNReal.ofReal (minimizerHausdorffConst m) *
          ν (ball (y : Space (m + 1)) (ρ n)) :=
      ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (minimizerHausdorffConst m) *
        ∑' y : u n, ν (ball (y : Space (m + 1)) (ρ n)) := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (minimizerHausdorffConst m) *
        ν (⋃ y : u n, ball (y : Space (m + 1)) (ρ n)) := by
      congr 1
      have hdisj_sub : Pairwise
          (Function.onFun Disjoint fun y : u n ↦ ball (y : Space (m + 1)) (ρ n)) :=
        fun y₁ y₂ hne ↦ hu_disj n y₁.2 y₂.2 (Subtype.coe_ne_coe.mpr hne)
      exact (measure_iUnion hdisj_sub (fun _ ↦ measurableSet_ball)).symm
    _ ≤ ENNReal.ofReal (minimizerHausdorffConst m) * ν V := by
      refine mul_le_mul_of_nonneg_left (measure_mono ?_) zero_le
      exact iUnion_subset fun y ↦ ball_subset_closedBall.trans (hcb_V (hu_sub n y.2) (hρ_le n))
    _ = ENNReal.ofReal (minimizerHausdorffConst m) * variationalPerimeter b E V := by
      rw [hν_open V hV Subset.rfl]

/-- Coarse Hausdorff `m`-measure bound on any open set `V ⊆ Ω` (exhausting `V` by compact sets). -/
theorem IsLocalPerimeterMinimizer.hausdorffMeasure_open_inter_boundary_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {V : Set (Space (m + 1))}
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) :
    μH[(m : ℝ)] (V ∩ measureTheoreticBoundary E) ≤
      ENNReal.ofReal (minimizerHausdorffConst m) * variationalPerimeter b E V := by
  let K : ℕ → Set (Space (m + 1)) := fun n ↦
    closedBall 0 ((n : ℝ) + 1) \ thickening (1 / ((n : ℝ) + 1)) Vᶜ
  have hK_comp (n : ℕ) : IsCompact (K n) :=
    (isCompact_closedBall 0 ((n : ℝ) + 1)).diff isOpen_thickening
  have hK_sub (n : ℕ) : K n ⊆ V := by
    intro x ⟨_, hx_not⟩
    by_contra hxV
    exact hx_not (self_subset_thickening (by positivity) Vᶜ hxV)
  have hK_mono : Monotone K := by
    intro j k hjk x ⟨hxb, hx_not⟩
    refine ⟨closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hjk 1) hxb,
      fun hxt ↦ hx_not ?_⟩
    refine thickening_mono ?_ Vᶜ hxt
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hK_union : (⋃ n : ℕ, K n ∩ measureTheoreticBoundary E) =
      V ∩ measureTheoreticBoundary E := by
    apply Subset.antisymm
    · exact iUnion_subset fun n ↦ inter_subset_inter_left _ (hK_sub n)
    · rintro x ⟨hxV, hxB⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV x hxV
      obtain ⟨n₁, hn₁⟩ := exists_nat_gt ‖x‖
      obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt hr
      let n := max n₁ n₂
      refine mem_iUnion.mpr ⟨n, ⟨?_, ?_⟩, hxB⟩
      · rw [mem_closedBall, dist_zero_right]
        have hle : (n₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left n₁ n₂
        linarith
      · intro hxt
        rw [mem_thickening_iff] at hxt
        obtain ⟨y, hyVc, hdist⟩ := hxt
        have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((n₂ : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity)
            (by exact_mod_cast Nat.add_le_add_right (le_max_right n₁ n₂) 1)
        have hy_ball : y ∈ ball x r := by
          rw [mem_ball, dist_comm]
          linarith
        exact hyVc (hball hy_ball)
  have hmono_inter : Monotone (fun n ↦ K n ∩ measureTheoreticBoundary E) :=
    fun j k hjk ↦ inter_subset_inter_left _ (hK_mono hjk)
  rw [← hK_union, hmono_inter.measure_iUnion]
  exact iSup_le fun n ↦ hmin.hausdorffMeasure_inter_boundary_le_open (hK_comp n) hV (hK_sub n) hVΩ

/-- Coarse Hausdorff `m`-measure bound on any subset `S ⊆ Ω` in terms of any locally finite
measure `μ` agreeing with `variationalPerimeter b E` on open subsets of `Ω` (BV7.2). -/
theorem IsLocalPerimeterMinimizer.hausdorffMeasure_subset_inter_boundary_le_measure {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U)
    {S : Set (Space (m + 1))} (hSΩ : S ⊆ Ω) :
    μH[(m : ℝ)] (S ∩ measureTheoreticBoundary E) ≤
      ENNReal.ofReal (minimizerHausdorffConst m) * μ S := by
  let C := ENNReal.ofReal (minimizerHausdorffConst m)
  have hC_ne_zero : C ≠ 0 := (ENNReal.ofReal_pos.mpr (minimizerHausdorffConst_pos m)).ne'
  rw [Set.measure_eq_iInf_isOpen S μ,
    ENNReal.mul_iInf_of_ne hC_ne_zero ENNReal.ofReal_ne_top]
  refine le_iInf fun U ↦ ?_
  by_cases hSU : S ⊆ U
  · rw [iInf_pos hSU]
    by_cases hU : IsOpen U
    · rw [iInf_pos hU]
      let V := U ∩ Ω
      have hV : IsOpen V := hU.inter hmin.isOpen_domain
      have hSV : S ⊆ V := subset_inter hSU hSΩ
      calc
        μH[(m : ℝ)] (S ∩ measureTheoreticBoundary E) ≤
            μH[(m : ℝ)] (V ∩ measureTheoreticBoundary E) :=
          measure_mono (inter_subset_inter_left _ hSV)
        _ ≤ C * variationalPerimeter b E V :=
          hmin.hausdorffMeasure_open_inter_boundary_le hV inter_subset_right
        _ = C * μ V := by rw [hμ V hV inter_subset_right]
        _ ≤ C * μ U := mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) zero_le
    · rw [iInf_neg hU, ENNReal.mul_top hC_ne_zero]
      exact le_top
  · simp [hSU, ENNReal.mul_top hC_ne_zero]

/-- Coarse Hausdorff `m`-measure bound on any compact subset `K ⊆ Ω` (BV7.2, compact form). -/
theorem IsLocalPerimeterMinimizer.hausdorffMeasure_inter_boundary_le_measure {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U)
    {K : Set (Space (m + 1))} (_hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    μH[(m : ℝ)] (K ∩ measureTheoreticBoundary E) ≤
      ENNReal.ofReal (minimizerHausdorffConst m) * μ K :=
  hmin.hausdorffMeasure_subset_inter_boundary_le_measure μ hμ hKΩ

/-- Null-set transfer from the perimeter measure `μ` to Hausdorff `m`-measure on
`measureTheoreticBoundary E` inside `Ω` (BV7.2 corollary). -/
theorem IsLocalPerimeterMinimizer.hausdorffMeasure_inter_boundary_eq_zero_of_measure_eq_zero {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U)
    {S : Set (Space (m + 1))} (hSΩ : S ⊆ Ω) (hμS : μ S = 0) :
    μH[(m : ℝ)] (S ∩ measureTheoreticBoundary E) = 0 := by
  have hle := hmin.hausdorffMeasure_subset_inter_boundary_le_measure μ hμ hSΩ
  rw [hμS, mul_zero] at hle
  exact nonpos_iff_eq_zero.mp hle

/-- Local finiteness of the Hausdorff `m`-measure of `measureTheoreticBoundary E` on compact
subsets of `Ω` (BV7.2). -/
theorem IsLocalPerimeterMinimizer.hausdorffMeasure_inter_boundary_lt_top {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) {K : Set (Space (m + 1))}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    μH[(m : ℝ)] (K ∩ measureTheoreticBoundary E) < ⊤ := by
  have hball : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ Ω :=
    fun x hx ↦ Metric.nhds_basis_closedBall.mem_iff.mp (hmin.isOpen_domain.mem_nhds (hKΩ hx))
  choose! r hr hcb using hball
  obtain ⟨F, hcov⟩ := hK.elim_finite_subcover
    (fun x : K ↦ ball (x : Space (m + 1)) (r x / 2))
    (fun _ ↦ isOpen_ball)
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hr x hx))⟩)
  have hsub : K ∩ measureTheoreticBoundary E ⊆
      ⋃ x ∈ F, (closedBall (x : Space (m + 1)) (r x / 2) ∩ measureTheoreticBoundary E) := by
    intro y ⟨hyK, hyB⟩
    obtain ⟨x, hy_sub⟩ := mem_iUnion.mp (hcov hyK)
    obtain ⟨hxF, hy_ball⟩ := mem_iUnion.mp hy_sub
    exact mem_iUnion₂.mpr ⟨x, hxF, ⟨ball_subset_closedBall hy_ball, hyB⟩⟩
  refine (measure_mono hsub).trans_lt ?_
  refine (measure_biUnion_finset_le F _).trans_lt ?_
  rw [ENNReal.sum_lt_top]
  intro x _
  have hxK : (x : Space (m + 1)) ∈ K := x.2
  have hcb_sub : closedBall (x : Space (m + 1)) (r x / 2) ⊆ ball (x : Space (m + 1)) (r x) :=
    closedBall_subset_ball (half_lt_self (hr x hxK))
  have hball_Ω : ball (x : Space (m + 1)) (r x) ⊆ Ω := ball_subset_closedBall.trans (hcb x hxK)
  have hle := hmin.hausdorffMeasure_inter_boundary_le_open
    (isCompact_closedBall (x : Space (m + 1)) (r x / 2)) isOpen_ball hcb_sub hball_Ω
  refine hle.trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr (hmin.perimeter_ball_ne_top x (r x) (hr x hxK) (hcb x hxK)))

/-- Any perimeter measure `μ` on `Ω` vanishes outside `measureTheoreticBoundary E` inside `Ω`. -/
theorem IsLocalPerimeterMinimizer.measure_sdiff_boundary_eq_zero {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U) :
    μ (Ω \ measureTheoreticBoundary E) = 0 := by
  have hsupp := hmin.support_measure_inter_eq μ hμ
  have hsub : Ω \ measureTheoreticBoundary E ⊆ μ.supportᶜ := by
    intro x ⟨hxΩ, hxB⟩ hx_supp
    have hm : x ∈ Measure.support μ ∩ Ω := ⟨hx_supp, hxΩ⟩
    rw [hsupp] at hm
    exact hxB hm.1
  exact measure_mono_null hsub Measure.measure_compl_support

/-- Inside `Ω`, any perimeter measure `μ` is concentrated on `measureTheoreticBoundary E`. -/
theorem IsLocalPerimeterMinimizer.measure_eq_measure_inter_boundary {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U)
    {S : Set (Space (m + 1))} (hSΩ : S ⊆ Ω) :
    μ S = μ (S ∩ measureTheoreticBoundary E) := by
  apply le_antisymm _ (measure_mono inter_subset_left)
  have hcov : S ⊆ (S ∩ measureTheoreticBoundary E) ∪ (Ω \ measureTheoreticBoundary E) := by
    intro x hxS
    by_cases hxB : x ∈ measureTheoreticBoundary E
    · exact Or.inl ⟨hxS, hxB⟩
    · exact Or.inr ⟨hSΩ hxS, hxB⟩
  calc
    μ S ≤ μ ((S ∩ measureTheoreticBoundary E) ∪ (Ω \ measureTheoreticBoundary E)) :=
      measure_mono hcov
    _ ≤ μ (S ∩ measureTheoreticBoundary E) + μ (Ω \ measureTheoreticBoundary E) :=
      measure_union_le _ _
    _ = μ (S ∩ measureTheoreticBoundary E) := by
      rw [hmin.measure_sdiff_boundary_eq_zero μ hμ, add_zero]

/-- Reverse coarse Hausdorff `m`-measure bound: for any subset `S ⊆ Ω`, the perimeter measure
`μ S` is controlled by a dimensional constant times `μH[m] (S ∩ measureTheoreticBoundary E)`
(BV7.2 reverse bound). -/
theorem IsLocalPerimeterMinimizer.measure_le_hausdorffMeasure_inter_boundary {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer b E Ω) (μ : Measure (Space (m + 1)))
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U)
    {S : Set (Space (m + 1))} (hSΩ : S ⊆ Ω) :
    μ S ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m) *
      μH[(m : ℝ)] (S ∩ measureTheoreticBoundary E) := by
  let C := ENNReal.ofReal (minimizerPerimeterUpperConst m)
  have hC_pos : 0 < minimizerPerimeterUpperConst m := minimizerPerimeterUpperConst_pos m
  have hC_ne_zero : C ≠ 0 := (ENNReal.ofReal_pos.mpr hC_pos).ne'
  have hcompact_aux {A K : Set (Space (m + 1))}
      (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hAK : A ⊆ K) :
      μ A ≤ C * μH[(m : ℝ)] A := by
    obtain ⟨δ₀, hδ₀, hthick⟩ := hK.exists_thickening_subset_open hmin.isOpen_domain hKΩ
    have hcb_Ω {x : Space (m + 1)} (hx : x ∈ A) {ρ : ℝ} (hρ : ρ ≤ δ₀ / 2) :
        closedBall x ρ ⊆ Ω := by
      have hlt : ρ < δ₀ := by linarith
      exact (closedBall_subset_ball hlt).trans ((ball_subset_thickening (hAK hx) δ₀).trans hthick)
    let r₀ : ℝ≥0∞ := ENNReal.ofReal (δ₀ / 2)
    have hr₀_pos : 0 < r₀ := ENNReal.ofReal_pos.mpr (half_pos hδ₀)
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    rw [ENNReal.mul_iSup]
    refine le_iSup_of_le r₀ ?_
    rw [ENNReal.mul_iSup]
    refine le_iSup_of_le hr₀_pos ?_
    rw [ENNReal.mul_iInf_of_ne hC_ne_zero ENNReal.ofReal_ne_top]
    refine le_iInf fun t ↦ ?_
    by_cases hcov : A ⊆ ⋃ n, t n
    · rw [iInf_pos hcov, ENNReal.mul_iInf_of_ne hC_ne_zero ENNReal.ofReal_ne_top]
      refine le_iInf fun htd ↦ ?_
      have hA_cov : A ⊆ ⋃ n, (t n ∩ A) := by
        intro x hxA
        obtain ⟨n, hxt⟩ := mem_iUnion.mp (hcov hxA)
        exact mem_iUnion.mpr ⟨n, hxt, hxA⟩
      rw [← ENNReal.tsum_mul_left]
      refine (measure_mono hA_cov).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun n ↦ ?_))
      rcases (t n ∩ A).eq_empty_or_nonempty with hempty | ⟨x, hxt, hxA⟩
      · simp [hempty]
      · have htne : (t n).Nonempty := ⟨x, hxt⟩
        rw [iSup_pos htne]
        have hed_le : ediam (t n) ≤ r₀ := htd n
        have hed_fin : ediam (t n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hed_le
        rcases eq_or_ne (ediam (t n)) 0 with hed0 | hed_ne0
        · have hsub_sing : t n ∩ A ⊆ {x} := by
            intro y ⟨hyt, _⟩
            have hed_yx : edist y x = 0 :=
              nonpos_iff_eq_zero.mp ((edist_le_ediam_of_mem hyt hxt).trans_eq hed0)
            exact mem_singleton_iff.mpr (edist_eq_zero.mp hed_yx)
          rcases Nat.eq_zero_or_pos m with rfl | hm_pos
          · rw [hed0]
            simp only [Nat.cast_zero, ENNReal.rpow_zero, mul_one]
            have hcb_x := hmin.measure_closedBall_le μ hμ (half_pos hδ₀) (hcb_Ω hxA le_rfl)
            simp only [pow_zero, mul_one] at hcb_x
            exact (measure_mono (hsub_sing.trans
              (singleton_subset_iff.mpr (mem_closedBall_self (half_pos hδ₀).le)))).trans hcb_x
          · have hμ_sing : μ {x} = 0 := by
              refine nonpos_iff_eq_zero.mp ?_
              let ρ_seq : ℕ → ℝ := fun k ↦ (δ₀ / 2) * (1 / ((k : ℝ) + 1))
              have hbound_k (k : ℕ) :
                  μ {x} ≤ ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ_seq k ^ m) := by
                have hpos_k : 0 < ρ_seq k := by dsimp [ρ_seq]; positivity
                have hle_k : ρ_seq k ≤ δ₀ / 2 := by
                  dsimp [ρ_seq]
                  have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
                  nlinarith
                exact (measure_mono (singleton_subset_iff.mpr (mem_closedBall_self hpos_k.le))).trans
                  (hmin.measure_closedBall_le μ hμ hpos_k (hcb_Ω hxA hle_k))
              have hρ_lim : Tendsto ρ_seq atTop (𝓝 0) := by
                have h0 := (tendsto_const_nhds (x := δ₀ / 2)).mul
                  tendsto_one_div_add_atTop_nhds_zero_nat
                simpa only [ρ_seq, mul_zero] using h0
              have hrhs_lim : Tendsto
                  (fun k ↦ ENNReal.ofReal (minimizerPerimeterUpperConst m * ρ_seq k ^ m))
                  atTop (𝓝 0) := by
                have hpow_lim : Tendsto (fun k ↦ minimizerPerimeterUpperConst m * ρ_seq k ^ m)
                    atTop (𝓝 0) := by
                  simpa only [zero_pow hm_pos.ne', mul_zero] using
                    tendsto_const_nhds.mul (hρ_lim.pow m)
                simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hpow_lim
              exact le_of_tendsto_of_tendsto' tendsto_const_nhds hrhs_lim hbound_k
            rw [measure_mono_null hsub_sing hμ_sing]
            exact zero_le
        · let d := (ediam (t n)).toReal
          have hd_pos : 0 < d := ENNReal.toReal_pos hed_ne0 hed_fin
          have hd_le : d ≤ δ₀ / 2 := by
            dsimp [d]
            exact ENNReal.toReal_le_of_le_ofReal (half_pos hδ₀).le hed_le
          have hsub_cb : t n ∩ A ⊆ closedBall x d := by
            intro y ⟨hyt, _⟩
            rw [mem_closedBall, dist_edist]
            exact ENNReal.toReal_mono hed_fin (edist_le_ediam_of_mem hyt hxt)
          have hcb_bound := hmin.measure_closedBall_le μ hμ hd_pos (hcb_Ω hxA hd_le)
          have hpow_eq : ENNReal.ofReal (minimizerPerimeterUpperConst m * d ^ m) =
              C * ediam (t n) ^ (m : ℝ) := by
            rw [ENNReal.ofReal_mul hC_pos.le, ENNReal.ofReal_pow hd_pos.le]
            dsimp [C, d]
            rw [ENNReal.ofReal_toReal hed_fin, ENNReal.rpow_natCast]
          rw [← hpow_eq]
          exact (measure_mono hsub_cb).trans hcb_bound
    · simp [hcov, ENNReal.mul_top hC_ne_zero]
  rw [hmin.measure_eq_measure_inter_boundary μ hμ hSΩ]
  let A := S ∩ measureTheoreticBoundary E
  have hAΩ : A ⊆ Ω := inter_subset_left.trans hSΩ
  let K : ℕ → Set (Space (m + 1)) := fun j ↦
    closedBall 0 ((j : ℝ) + 1) \ thickening (1 / ((j : ℝ) + 1)) Ωᶜ
  have hK_comp (j : ℕ) : IsCompact (K j) :=
    (isCompact_closedBall 0 ((j : ℝ) + 1)).diff isOpen_thickening
  have hK_sub (j : ℕ) : K j ⊆ Ω := by
    intro x ⟨_, hx_not⟩
    by_contra hxΩ
    exact hx_not (self_subset_thickening (by positivity) Ωᶜ hxΩ)
  have hK_mono : Monotone K := by
    intro j k hjk x ⟨hxb, hx_not⟩
    refine ⟨closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hjk 1) hxb,
      fun hxt ↦ hx_not ?_⟩
    refine thickening_mono ?_ Ωᶜ hxt
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hA_union : (⋃ j : ℕ, A ∩ K j) = A := by
    apply Subset.antisymm (iUnion_subset fun _ ↦ inter_subset_left)
    intro x hxA
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hmin.isOpen_domain x (hAΩ hxA)
    obtain ⟨n₁, hn₁⟩ := exists_nat_gt ‖x‖
    obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt hr
    let j := max n₁ n₂
    refine mem_iUnion.mpr ⟨j, hxA, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have hle : (n₁ : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_max_left n₁ n₂
      linarith
    · intro hxt
      rw [mem_thickening_iff] at hxt
      obtain ⟨y, hyΩc, hdist⟩ := hxt
      have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((n₂ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.add_le_add_right (le_max_right n₁ n₂) 1)
      have hy_ball : y ∈ ball x r := by
        rw [mem_ball, dist_comm]
        linarith
      exact hyΩc (hball hy_ball)
  have hmono_A : Monotone (fun j ↦ A ∩ K j) :=
    fun j k hjk ↦ inter_subset_inter_right A (hK_mono hjk)
  change μ A ≤ C * μH[(m : ℝ)] A
  nth_rw 1 [← hA_union]
  rw [hmono_A.measure_iUnion]
  refine iSup_le fun j ↦ ?_
  exact (hcompact_aux (hK_comp j) (hK_sub j) inter_subset_right).trans
    (mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) zero_le)

/-- Mutual null-set equivalence inside `Ω` between a locally finite perimeter measure `μ` and
Hausdorff `m`-measure restricted to `measureTheoreticBoundary E` (BV7.2). -/
theorem IsLocalPerimeterMinimizer.measure_eq_zero_iff_hausdorffMeasure_inter_boundary_eq_zero
    {m : ℕ} {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E Ω : Set (Space (m + 1))} (hmin : IsLocalPerimeterMinimizer b E Ω)
    (μ : Measure (Space (m + 1))) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ U, IsOpen U → U ⊆ Ω → μ U = variationalPerimeter b E U)
    {S : Set (Space (m + 1))} (hSΩ : S ⊆ Ω) :
    μ S = 0 ↔ μH[(m : ℝ)] (S ∩ measureTheoreticBoundary E) = 0 := by
  refine ⟨hmin.hausdorffMeasure_inter_boundary_eq_zero_of_measure_eq_zero μ hμ hSΩ, fun hH ↦ ?_⟩
  have hle := hmin.measure_le_hausdorffMeasure_inter_boundary μ hμ hSΩ
  rw [hH, mul_zero] at hle
  exact nonpos_iff_eq_zero.mp hle

end SerrinEpigraph
