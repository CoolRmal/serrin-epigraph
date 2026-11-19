module

public import SerrinEpigraph.ColumnHeightPoincare
public import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The good set of small excess density (`GR9`, first part)

Let `ε = projectedExcessMeasure μ ν = π_# ((1 - ν_n) μ)` be the horizontal excess measure of
`BV13–BV14`. For a horizontal set `A`, a maximal radius `s₀` and a density threshold `κ`
(`κ = λ²` in `GR9`), the *good set* `excessGoodSet ε A s₀ κ` consists of the points of `A` at which
every closed ball of radius `s < s₀` carries excess at most `κ` times its volume; it is the
sublevel set `{M ε ≤ κ}` of the local Hardy–Littlewood maximal function of `ε`.

* `measurableSet_excessGoodSet`: the good set is Borel (reduction to rational radii and upper
  semicontinuity of `y ↦ ε (closedBall y q)`).
* `volume_ball_diff_excessGoodSet_le` (weak type estimate, Vitali covering with factor `4`):
  `|B_R \ G| ≤ 4^m κ⁻¹ ε(B_{R+s₀})`.
* `measure_le_of_subset_excessGoodSet` (Besicovitch differentiation): `ε(S) ≤ κ |S|` for every
  `S ⊆ G`; in particular `ε ⌊ G ≤ κ · Lebesgue ⌊ G`.
* `ae_mem_iff_columnSignedHeight_lt_of_excessGoodSet` (`BV14.2`, single layer): if `κ < 1`, then
  `E` coincides a.e. over `G` with the epigraph of the signed height.
* `measure_preimage_diff_excessGoodSet_le` (`GR9.2`): `μ(π⁻¹(A \ G)) ≤ |A \ G| + ε(A)`.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ENNReal CompactlySupported

namespace SerrinEpigraph

/-! ### 1. The good set and its measurability -/

/-- The good set of `GR9`: points of `A` at which all closed balls of radius `s < s₀` carry excess
measure at most `κ` times their volume. -/
def excessGoodSet {m : ℕ} (ε : Measure (Space m)) (A : Set (Space m)) (s₀ κ : ℝ) :
    Set (Space m) :=
  {y ∈ A | ∀ s, 0 < s → s < s₀ →
    ε (closedBall y s) ≤ ENNReal.ofReal κ * volume (closedBall y s)}

theorem excessGoodSet_subset {m : ℕ} (ε : Measure (Space m)) (A : Set (Space m)) (s₀ κ : ℝ) :
    excessGoodSet ε A s₀ κ ⊆ A :=
  fun _ hy ↦ hy.1

theorem closedBall_eq_iInter_closedBall {d : ℕ} (y : Space d) (q : ℝ) :
    closedBall y q = ⋂ n : ℕ, closedBall y (q + 1 / ((n : ℝ) + 1)) := by
  ext z
  simp only [mem_closedBall, mem_iInter]
  constructor
  · intro h n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨n, hnlt⟩ := exists_nat_one_div_lt (sub_pos.mpr hn)
    have := h n
    linarith

/-- The excess of closed balls depends upper semicontinuously on the center. -/
theorem measurable_measure_closedBall {d : ℕ} (ε : Measure (Space d)) [IsFiniteMeasure ε]
    (q : ℝ) : Measurable fun y : Space d ↦ ε (closedBall y q) := by
  apply UpperSemicontinuous.measurable
  intro y c hc
  have hanti : Antitone fun n : ℕ ↦ closedBall y (q + 1 / ((n : ℝ) + 1)) := by
    intro n k hnk
    apply closedBall_subset_closedBall
    have : (n : ℝ) ≤ k := Nat.cast_le.mpr hnk
    have h1 : 0 < (n : ℝ) + 1 := by positivity
    gcongr
  have hlim : Tendsto (fun n : ℕ ↦ ε (closedBall y (q + 1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (ε (closedBall y q))) := by
    rw [closedBall_eq_iInter_closedBall y q]
    exact tendsto_measure_iInter_atTop
      (fun n ↦ isClosed_closedBall.measurableSet.nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  filter_upwards [ball_mem_nhds y hδ] with y' hy'
  refine lt_of_le_of_lt (measure_mono ?_) hn
  apply closedBall_subset_closedBall'
  rw [mem_ball] at hy'
  linarith

/-- The good set is the countable intersection of its rational-radius conditions. -/
theorem excessGoodSet_eq_iInter_rat {m : ℕ} (ε : Measure (Space m)) (A : Set (Space m))
    (s₀ κ : ℝ) :
    excessGoodSet ε A s₀ κ = A ∩ ⋂ q : ℚ, {y | 0 < (q : ℝ) → (q : ℝ) < s₀ →
      ε (closedBall y q) ≤ ENNReal.ofReal κ * volume (closedBall y q)} := by
  ext y
  simp only [excessGoodSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hyA, hy⟩
    exact ⟨hyA, fun q hq hqs ↦ hy q hq hqs⟩
  · rintro ⟨hyA, hy⟩
    refine ⟨hyA, fun s hs hss ↦ ?_⟩
    -- approximate `s` from above by rational radii below `s₀`
    have hq : ∀ n : ℕ, ∃ q : ℚ, s < q ∧ (q : ℝ) < min s₀ (s + 1 / ((n : ℝ) + 1)) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact exists_rat_btwn (lt_min hss (by linarith))
    choose q hq using hq
    have hqlim : Tendsto (fun n ↦ (q n : ℝ)) atTop (𝓝 s) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun n ↦ (hq n).1.le) (fun n ↦ ((hq n).2.trans_le (min_le_right _ _)).le)
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add s
    have hbound : ∀ n, ε (closedBall y s) ≤ ENNReal.ofReal κ *
        (ENNReal.ofReal ((q n : ℝ) ^ m) * volume (ball (0 : Space m) 1)) := by
      intro n
      have hqpos : (0 : ℝ) < q n := hs.trans (hq n).1
      have hqs₀ : (q n : ℝ) < s₀ := (hq n).2.trans_le (min_le_left _ _)
      calc
        ε (closedBall y s) ≤ ε (closedBall y (q n)) :=
          measure_mono (closedBall_subset_closedBall (hq n).1.le)
        _ ≤ ENNReal.ofReal κ * volume (closedBall y (q n)) := hy (q n) hqpos hqs₀
        _ = _ := by
          rw [Measure.addHaar_closedBall volume y hqpos.le, finrank_euclideanSpace_fin]
    have hlim : Tendsto (fun n ↦ ENNReal.ofReal κ *
        (ENNReal.ofReal ((q n : ℝ) ^ m) * volume (ball (0 : Space m) 1))) atTop
        (𝓝 (ENNReal.ofReal κ * (ENNReal.ofReal (s ^ m) * volume (ball (0 : Space m) 1)))) := by
      refine ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const ?_ ?_) ?_
      · exact ENNReal.tendsto_ofReal (hqlim.pow m)
      · exact Or.inr measure_ball_ne_top
      · exact Or.inr ENNReal.ofReal_ne_top
    have hle := ge_of_tendsto' hlim hbound
    rwa [Measure.addHaar_closedBall volume y hs.le, finrank_euclideanSpace_fin]

/-- The good set is Borel measurable. -/
theorem measurableSet_excessGoodSet {m : ℕ} (ε : Measure (Space m)) [IsFiniteMeasure ε]
    {A : Set (Space m)} (hA : MeasurableSet A) (s₀ κ : ℝ) :
    MeasurableSet (excessGoodSet ε A s₀ κ) := by
  rw [excessGoodSet_eq_iInter_rat]
  refine hA.inter (MeasurableSet.iInter fun q ↦ ?_)
  by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) < s₀
  · have hset : {y : Space m | 0 < (q : ℝ) → (q : ℝ) < s₀ →
        ε (closedBall y q) ≤ ENNReal.ofReal κ * volume (closedBall y q)} =
        {y | ε (closedBall y q) ≤ ENNReal.ofReal κ *
          (ENNReal.ofReal ((q : ℝ) ^ m) * volume (ball (0 : Space m) 1))} := by
      ext y
      simp only [mem_ofPred_eq, hq.1, hq.2, forall_const]
      rw [Measure.addHaar_closedBall volume y hq.1.le, finrank_euclideanSpace_fin]
    rw [hset]
    exact measurableSet_le (measurable_measure_closedBall ε q) measurable_const
  · have hset : {y : Space m | 0 < (q : ℝ) → (q : ℝ) < s₀ →
        ε (closedBall y q) ≤ ENNReal.ofReal κ * volume (closedBall y q)} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hq
    rw [hset]
    exact MeasurableSet.univ

/-! ### 2. The weak type estimate for the bad set -/

/-- **Weak type estimate** (`GR9`): the bad set in `B_R(y₀)`, where some ball of radius below `s₀`
carries excess above `κ` times its volume, has measure at most `4^m κ⁻¹ ε(B_{R+s₀}(y₀))`. -/
theorem volume_ball_diff_excessGoodSet_le {m : ℕ} (ε : Measure (Space m)) [IsFiniteMeasure ε]
    (y₀ : Space m) {R s₀ κ : ℝ} (hκ : 0 < κ) :
    volume (ball y₀ R \ excessGoodSet ε (ball y₀ R) s₀ κ) ≤
      ENNReal.ofReal (4 ^ m / κ) * ε (ball y₀ (R + s₀)) := by
  set D := ball y₀ R \ excessGoodSet ε (ball y₀ R) s₀ κ with hD_def
  have hbad : ∀ y ∈ D, ∃ s, 0 < s ∧ s < s₀ ∧
      ENNReal.ofReal κ * volume (closedBall y s) < ε (closedBall y s) := by
    intro y hy
    have hyR : y ∈ ball y₀ R := hy.1
    have hng : ¬ ∀ s, 0 < s → s < s₀ →
        ε (closedBall y s) ≤ ENNReal.ofReal κ * volume (closedBall y s) :=
      fun h ↦ hy.2 ⟨hyR, h⟩
    push Not at hng
    exact hng
  choose! rad hrad using hbad
  obtain ⟨u, huD, hudisj, hucov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall D id rad s₀
      (fun a ha ↦ (hrad a ha).2.1.le) 4 (by norm_num)
  have hucount : u.Countable := by
    refine hudisj.countable_of_nonempty_interior fun b hb ↦ ?_
    have hpos := (hrad b (huD hb)).1
    exact ⟨b, mem_interior.mpr ⟨ball b (rad b), ball_subset_closedBall, isOpen_ball,
      mem_ball_self hpos⟩⟩
  have hcover : D ⊆ ⋃ b ∈ u, closedBall b (4 * rad b) := by
    intro a ha
    obtain ⟨b, hbu, hab⟩ := hucov a ha
    exact mem_biUnion hbu (hab (mem_closedBall_self (hrad a ha).1.le))
  have hvol_scale : ∀ b, 0 ≤ rad b →
      volume (closedBall b (4 * rad b)) = ENNReal.ofReal (4 ^ m) * volume (closedBall b (rad b)) := by
    intro b hb
    rw [Measure.addHaar_closedBall volume b (by positivity),
      Measure.addHaar_closedBall volume b hb, finrank_euclideanSpace_fin, mul_pow,
      ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hvol_le : ∀ b ∈ u, volume (closedBall b (rad b)) ≤
      ENNReal.ofReal κ⁻¹ * ε (closedBall b (rad b)) := by
    intro b hb
    have hlt := (hrad b (huD hb)).2.2
    have hκ' : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.mpr hκ).ne'
    have h1 : volume (closedBall b (rad b)) ≤ ε (closedBall b (rad b)) / ENNReal.ofReal κ := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hκ') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact hlt.le
    rwa [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hκ] at h1
  have hsub : (⋃ b ∈ u, closedBall b (rad b)) ⊆ ball y₀ (R + s₀) := by
    intro z hz
    obtain ⟨b, hbu, hzb⟩ := mem_iUnion₂.mp hz
    have hbR : dist b y₀ < R := (huD hbu).1
    have hrb := (hrad b (huD hbu)).2.1
    rw [mem_closedBall] at hzb
    rw [mem_ball]
    calc
      dist z y₀ ≤ dist z b + dist b y₀ := dist_triangle _ _ _
      _ < R + s₀ := by linarith
  calc
    volume D ≤ volume (⋃ b ∈ u, closedBall b (4 * rad b)) := measure_mono hcover
    _ ≤ ∑' b : u, volume (closedBall (b : Space m) (4 * rad b)) :=
      measure_biUnion_le volume hucount _
    _ = ∑' b : u, ENNReal.ofReal (4 ^ m) * volume (closedBall (b : Space m) (rad b)) := by
      congr 1
      funext b
      exact hvol_scale b (hrad b (huD b.2)).1.le
    _ ≤ ∑' b : u, ENNReal.ofReal (4 ^ m) *
          (ENNReal.ofReal κ⁻¹ * ε (closedBall (b : Space m) (rad b))) :=
      ENNReal.tsum_le_tsum fun b ↦ by gcongr; exact hvol_le b b.2
    _ = ENNReal.ofReal (4 ^ m / κ) * ∑' b : u, ε (closedBall (b : Space m) (rad b)) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv]
    _ = ENNReal.ofReal (4 ^ m / κ) * ε (⋃ b ∈ u, closedBall b (rad b)) := by
      have hudisj' : u.PairwiseDisjoint fun a ↦ closedBall a (rad a) := hudisj
      rw [measure_biUnion hucount hudisj' fun b _ ↦ isClosed_closedBall.measurableSet]
    _ ≤ ENNReal.ofReal (4 ^ m / κ) * ε (ball y₀ (R + s₀)) := by
      gcongr

/-! ### 3. The density bound on the good set -/

/-- **Density bound on the good set** (Besicovitch differentiation): every subset `S` of the good
set satisfies `ε(S) ≤ κ |S|`. -/
theorem measure_le_of_subset_excessGoodSet {m : ℕ} (ε : Measure (Space m)) [IsFiniteMeasure ε]
    {A : Set (Space m)} {s₀ κ : ℝ} (hs₀ : 0 < s₀) {S : Set (Space m)}
    (hS : S ⊆ excessGoodSet ε A s₀ κ) : ε S ≤ ENNReal.ofReal κ * volume S := by
  set μ₀ : Measure (Space m) := volume + ε with hμ₀_def
  have hρ : ε ≪ μ₀ := by
    intro s hs
    rw [hμ₀_def, Measure.add_apply] at hs
    exact (add_eq_zero.mp hs).2
  set v := Besicovitch.vitaliFamily μ₀
  set ν₀ : Measure (Space m) := (Real.toNNReal κ) • volume with hν₀_def
  have hν₀ : ∀ s, ν₀ s = ENNReal.ofReal κ * volume s := fun s ↦ by
    rw [hν₀_def, Measure.coe_nnreal_smul_apply]
    rfl
  have hfreq : ∀ x ∈ S, ∃ᶠ a in v.filterAt x, ε a ≤ ν₀ a := by
    intro x hx
    have hgood := (hS hx).2
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ε (closedBall x r) ≤ ν₀ (closedBall x r) := by
      filter_upwards [Ioo_mem_nhdsGT hs₀] with r hr
      rw [hν₀]
      exact hgood r hr.1 hr.2
    exact (Besicovitch.tendsto_filterAt μ₀ x).frequently hev.frequently
  have h := v.measure_le_of_frequently_le ν₀ hρ S hfreq
  rwa [hν₀] at h

/-- The excess measure restricted to the good set is dominated by `κ` times Lebesgue measure. -/
theorem restrict_le_smul_volume_of_excessGoodSet {m : ℕ} (ε : Measure (Space m))
    [IsFiniteMeasure ε] (A : Set (Space m)) {s₀ : ℝ} (κ : ℝ) (hs₀ : 0 < s₀) :
    ε.restrict (excessGoodSet ε A s₀ κ) ≤
      ENNReal.ofReal κ • volume.restrict (excessGoodSet ε A s₀ κ) := by
  rw [Measure.le_iff]
  intro T hT
  rw [Measure.restrict_apply hT, Measure.smul_apply, Measure.restrict_apply hT, smul_eq_mul]
  exact measure_le_of_subset_excessGoodSet ε hs₀ inter_subset_right

/-! ### 4. Single layer over the good set and the bad columns (`BV14.2`, `GR9.2`) -/

/-- **Single layer over the good set** (`BV14.2`, `GR9`): if `κ < 1`, then `E` coincides a.e.
over the good set (inside the cylinder) with the epigraph of the signed height. -/
theorem ae_mem_iff_columnSignedHeight_lt_of_excessGoodSet {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}
    (hrep : IsPerimeterRepresentation b E (cylinderSet U H') μ ν)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {A : Set (Space m)} (hA : MeasurableSet A) (hAU : A ⊆ U) {s₀ κ : ℝ} (hs₀ : 0 < s₀)
    (hκ : κ < 1) :
    ∀ᵐ x ∂volume, x ∈ cylinderSet U H' →
      horizontal x ∈ excessGoodSet (projectedExcessMeasure μ ν) A s₀ κ →
      (x ∈ E ↔ columnSignedHeight E H (horizontal x) < x (Fin.last m)) := by
  have := hrep.isFiniteMeasure
  have := isFiniteMeasure_projectedExcessMeasure μ hrep.integrable
  exact ae_mem_iff_columnSignedHeight_lt_of_excess_le b hE hU hH hHH' μ hrep.measure_compl
    hrep.measure_open hrep.integrable hrep.norm_eq_one hrep.dist hbot htop
    (measurableSet_excessGoodSet _ hA s₀ κ) ((excessGoodSet_subset _ _ _ _).trans hAU) hκ
    (restrict_le_smul_volume_of_excessGoodSet _ A κ hs₀)

/-- **Perimeter over the bad columns** (`GR9.2`): `μ(π⁻¹(A \ G)) ≤ |A \ G| + ε(A)`. -/
theorem measure_preimage_diff_excessGoodSet_le {m : ℕ}
    {b : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1))}
    {E : Set (Space (m + 1))} (hE : MeasurableSet E)
    {U : Set (Space m)} (hU : IsOpen U) {H H' : ℝ} (hH : 0 < H) (hHH' : H < H')
    {μ : Measure (Space (m + 1))} {ν : Space (m + 1) → Space (m + 1)}
    (hrep : IsPerimeterRepresentation b E (cylinderSet U H') μ ν)
    (hbot : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo (-H') (-H) → x ∉ E)
    (htop : ∀ᵐ x ∂volume, horizontal x ∈ U → x (Fin.last m) ∈ Ioo H H' → x ∈ E)
    {A : Set (Space m)} (hA : MeasurableSet A) (hAU : A ⊆ U) (s₀ κ : ℝ) :
    μ (horizontal ⁻¹' (A \ excessGoodSet (projectedExcessMeasure μ ν) A s₀ κ)) ≤
      volume (A \ excessGoodSet (projectedExcessMeasure μ ν) A s₀ κ) +
        projectedExcessMeasure μ ν A := by
  have := hrep.isFiniteMeasure
  have := isFiniteMeasure_projectedExcessMeasure μ hrep.integrable
  set G := excessGoodSet (projectedExcessMeasure μ ν) A s₀ κ
  have hGm : MeasurableSet G := measurableSet_excessGoodSet _ hA s₀ κ
  have hDm : MeasurableSet (A \ G) := hA.diff hGm
  have hproj : μ (horizontal ⁻¹' (A \ G)) = projectedPerimeterMeasure μ (A \ G) := by
    unfold projectedPerimeterMeasure
    rw [Measure.map_apply continuous_horizontal.measurable hDm]
  rw [hproj, projectedPerimeterMeasure_apply_eq b hE hU hH hHH' μ hrep.measure_compl
    hrep.measure_open hrep.integrable hrep.norm_eq_one hrep.dist hbot htop hDm
    (sdiff_subset.trans hAU)]
  exact add_le_add le_rfl (measure_mono sdiff_subset)

end SerrinEpigraph
