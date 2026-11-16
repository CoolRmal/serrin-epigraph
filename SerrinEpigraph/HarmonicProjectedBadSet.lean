module

public import SerrinEpigraph.Basic
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import SerrinEpigraph.DiffuseTiltEstimate

/-!
# Projected bad-ball estimates

The covering is selected in the base space. Disjoint base balls have disjoint
ambient lifts, independently of the heights of their centers. This is the
geometric step needed to estimate the projection of the bad set in harmonic
approximation.
-/

public section
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SerrinEpigraph

/-- Disjoint balls in a contractive projection imply disjoint ambient balls
with the same centers and radii. -/
theorem pairwiseDisjoint_balls_of_projection {n d : ℕ} {ι : Type*}
    {π : Space n → Space d} (hπ : LipschitzWith 1 π)
    {c : ι → Space n} {r : ι → ℝ} {t : Set ι}
    (hd : t.PairwiseDisjoint (fun i ↦ ball (π (c i)) (r i))) :
    t.PairwiseDisjoint (fun i ↦ ball (c i) (r i)) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  apply Set.disjoint_left.mp (hd hi hj hij)
  · exact lt_of_le_of_lt (by simpa using hπ.dist_le_mul z (c i)) hzi
  · exact lt_of_le_of_lt (by simpa using hπ.dist_le_mul z (c j)) hzj

/-- A projected five-ball covering estimate for an arbitrary ambient measure.
Only the cost of each enlarged base ball and disjointness of the original
ambient balls are used; the projection need not preserve volume. -/
theorem measure_projected_centers_le_of_ball_cost {n d : ℕ} {ι : Type*}
    {π : Space n → Space d} (hπ : LipschitzWith 1 π)
    (μ : Measure (Space n)) (ν : Measure (Space d))
    {c : ι → Space n} {r : ι → ℝ} {t : Set ι}
    {R : ℝ} (hrpos : ∀ i ∈ t, 0 < r i) (hrbound : ∀ i ∈ t, r i ≤ R)
    {A : Set (Space n)} (hA : ∀ i ∈ t, ball (c i) (r i) ⊆ A)
    {C : ℝ≥0∞}
    (hcost : ∀ i ∈ t, ν (ball (π (c i)) (5 * r i)) ≤ C * μ (ball (c i) (r i))) :
    ν ((π ∘ c) '' t) ≤ C * μ A := by
  obtain ⟨s, hst, hdis, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball t (π ∘ c) r R
      hrbound 5 (by norm_num)
  have hs : s.Countable := hdis.countable_of_isOpen (fun i _ ↦ isOpen_ball)
    (fun i hi ↦ ⟨π (c i), mem_ball_self (hrpos i (hst hi))⟩)
  have : Countable s := hs.to_subtype
  have hsub : (π ∘ c) '' t ⊆ ⋃ i : s, ball (π (c i)) (5 * r i) := by
    rintro z ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hball⟩ := hcover i hi
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hball (mem_ball_self (hrpos i hi))⟩
  have hsum : (∑' i : s, μ (ball (c i) (r i))) ≤ μ A := by
    rw [← measure_biUnion hs (pairwiseDisjoint_balls_of_projection hπ hdis)
      (fun i _ ↦ measurableSet_ball)]
    apply measure_mono
    exact iUnion₂_subset fun i hi ↦ hA i (hst hi)
  calc
    ν ((π ∘ c) '' t) ≤ ν (⋃ i : s, ball (π (c i)) (5 * r i)) :=
      measure_mono hsub
    _ ≤ ∑' i : s, ν (ball (π (c i)) (5 * r i)) := measure_iUnion_le _
    _ ≤ ∑' i : s, C * μ (ball (c i) (r i)) :=
      ENNReal.tsum_le_tsum (fun i ↦ hcost i (hst i.property))
    _ = C * ∑' i : s, μ (ball (c i) (r i)) := ENNReal.tsum_mul_left
    _ ≤ C * μ A := by gcongr

/-- A density threshold with the dimension of the base controls the measure
of all projected centers by the ambient measure divided by that threshold. -/
theorem measure_projected_centers_le_of_density {n d : ℕ} {ι : Type*}
    {π : Space n → Space d} (hπ : LipschitzWith 1 π)
    (μ : Measure (Space n)) {c : ι → Space n} {r : ι → ℝ} {t : Set ι}
    {R : ℝ} (hrpos : ∀ i ∈ t, 0 < r i) (hrbound : ∀ i ∈ t, r i ≤ R)
    {A : Set (Space n)} (hA : ∀ i ∈ t, ball (c i) (r i) ⊆ A)
    {η : ℝ} (hη : 0 < η)
    (hdensity : ∀ i ∈ t, ENNReal.ofReal (η * r i ^ d) ≤ μ (ball (c i) (r i))) :
    volume ((π ∘ c) '' t) ≤
      (ENNReal.ofReal ((5 : ℝ) ^ d) * volume (ball (0 : Space d) 1) /
        ENNReal.ofReal η) * μ A := by
  apply measure_projected_centers_le_of_ball_cost hπ μ volume hrpos hrbound hA
  intro i hi
  let a := ENNReal.ofReal ((5 : ℝ) ^ d) * volume (ball (0 : Space d) 1)
  have hzero : ENNReal.ofReal η ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hη)
  calc
    volume (ball (π (c i)) (5 * r i)) = a * ENNReal.ofReal (r i ^ d) := by
      rw [Measure.addHaar_ball_of_pos volume _ (mul_pos (by norm_num) (hrpos i hi))]
      simp only [finrank_euclideanSpace_fin, mul_pow,
        ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) _)]
      dsimp only [a]
      ac_rfl
    _ = (a / ENNReal.ofReal η) * ENNReal.ofReal (η * r i ^ d) := by
      rw [ENNReal.ofReal_mul hη.le, ← mul_assoc,
        ENNReal.div_mul_cancel hzero ENNReal.ofReal_ne_top]
    _ ≤ (a / ENNReal.ofReal η) * μ (ball (c i) (r i)) := by gcongr; exact hdensity i hi

/-- The projected weak maximal estimate, stated directly for the set where
some admissible ball violates the density threshold. The set need not be measurable. -/
theorem measure_projected_bad_set_le {n d : ℕ}
    {π : Space n → Space d} (hπ : LipschitzWith 1 π)
    (μ : Measure (Space n)) (A : Set (Space n)) (R : ℝ)
    {η : ℝ} (hη : 0 < η) :
    volume (π '' {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
      ENNReal.ofReal (η * r ^ d) ≤ μ (ball x r)}) ≤
      (ENNReal.ofReal ((5 : ℝ) ^ d) * volume (ball (0 : Space d) 1) /
        ENNReal.ofReal η) * μ A := by
  let S := {x : Space n | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
    ENNReal.ofReal (η * r ^ d) ≤ μ (ball x r)}
  choose r hrpos hrbound hrA hrdensity using fun x : S ↦ x.property
  have hh := measure_projected_centers_le_of_density hπ μ
    (c := fun x : S ↦ x.val) (r := r) (t := univ)
    (fun x _ ↦ hrpos x) (fun x _ ↦ hrbound x) (fun x _ ↦ hrA x) hη
    (fun x _ ↦ hrdensity x)
  simpa only [image_univ, Set.range_comp, Subtype.range_coe_subtype, Set.ofPred_mem_eq, S] using hh

/-- The projected maximal estimate for an actual nonnegative integrable density,
with the threshold written using the ordinary Lebesgue integral. -/
theorem measure_projected_bad_set_integral_le {n d : ℕ}
    {π : Space n → Space d} (hπ : LipschitzWith 1 π)
    {q : Space n → ℝ} {A : Set (Space n)} (hA : MeasurableSet A)
    (hq : IntegrableOn q A) (hqn : ∀ x, 0 ≤ q x) (R : ℝ)
    {η : ℝ} (hη : 0 < η) :
    volume (π '' {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
      η * r ^ d ≤ ∫ y in ball x r, q y}) ≤
      (ENNReal.ofReal ((5 : ℝ) ^ d) * volume (ball (0 : Space d) 1) /
        ENNReal.ofReal η) * ENNReal.ofReal (∫ x in A, q x) := by
  let μ := volume.withDensity (fun x ↦ ENNReal.ofReal (q x))
  have hμ {B : Set (Space n)} (hB : MeasurableSet B) (hBA : B ⊆ A) :
      μ B = ENNReal.ofReal (∫ x in B, q x) := by
    rw [show μ B = ∫⁻ x in B, ENNReal.ofReal (q x) from withDensity_apply _ hB]
    exact (ofReal_integral_eq_lintegral_ofReal (hq.mono_set hBA)
      (Filter.Eventually.of_forall hqn)).symm
  have hh := measure_projected_bad_set_le hπ μ A R hη
  rw [hμ hA (Subset.refl _)] at hh
  apply le_trans (measure_mono (image_mono ?_)) hh
  rintro x ⟨r, hr, hrR, hrA, hd⟩
  refine ⟨r, hr, hrR, hrA, ?_⟩
  rw [hμ measurableSet_ball hrA]
  exact ENNReal.ofReal_le_ofReal hd

/-- The HA bad-set projection bound for the genuine diffuse tangential energy.
The density is the actual Euclidean gradient density of the Lipschitz function. -/
theorem measure_projected_tilt_bad_set_le {n d : ℕ}
    {π : Space n → Space d} (hπ : LipschitzWith 1 π)
    {v : Space n → ℝ} (hv : LocallyLipschitz v)
    {e : Space n} (he : ‖e‖ = 1) {T : ℝ} (hT : 0 < T)
    {A : Set (Space n)} (hA : IsCompact A) (R : ℝ) {η : ℝ} (hη : 0 < η) :
    volume (π '' {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
      η * r ^ d ≤ ∫ y in ball x r, diffuseTiltDensity T v e y}) ≤
      (ENNReal.ofReal ((5 : ℝ) ^ d) * volume (ball (0 : Space d) 1) /
        ENNReal.ofReal η) * ENNReal.ofReal (∫ x in A, diffuseTiltDensity T v e x) :=
  measure_projected_bad_set_integral_le hπ hA.measurableSet
    (integrableOn_diffuseTiltDensity hv hA T he)
    (diffuseTiltDensity_nonneg hT v he) R hη

/-- The same five-ball selection bounds the ambient mass of the bad set.
The ambient mass may have surface-order growth of any integer dimension. -/
theorem measure_bad_set_le_of_surface_growth {n : ℕ}
    (μ ν : Measure (Space n)) (A : Set (Space n)) (R : ℝ) (k : ℕ)
    {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hgrowth : ∀ x : Space n, ∀ r : ℝ, 0 < r →
      ν (ball x r) ≤ ENNReal.ofReal (L * r ^ k)) :
    ν {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
      ENNReal.ofReal (η * r ^ k) ≤ μ (ball x r)} ≤
      (ENNReal.ofReal (L * (5 : ℝ) ^ k) / ENNReal.ofReal η) * μ A := by
  let S := {x : Space n | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
    ENNReal.ofReal (η * r ^ k) ≤ μ (ball x r)}
  choose r hrpos hrbound hrA hrdensity using fun x : S ↦ x.property
  have hcost (x : S) :
      ν (ball x.val (5 * r x)) ≤
        (ENNReal.ofReal (L * (5 : ℝ) ^ k) / ENNReal.ofReal η) * μ (ball x.val (r x)) := by
    have hzero : ENNReal.ofReal η ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hη)
    calc
      _ ≤ ENNReal.ofReal (L * (5 * r x) ^ k) :=
        hgrowth x.val _ (mul_pos (by norm_num) (hrpos x))
      _ = ENNReal.ofReal (L * (5 : ℝ) ^ k) * ENNReal.ofReal (r x ^ k) := by
        rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hL (by positivity))]
      _ = (ENNReal.ofReal (L * (5 : ℝ) ^ k) / ENNReal.ofReal η) *
          ENNReal.ofReal (η * r x ^ k) := by
        rw [ENNReal.ofReal_mul hη.le, ← mul_assoc,
          ENNReal.div_mul_cancel hzero ENNReal.ofReal_ne_top]
      _ ≤ _ := by gcongr; exact hrdensity x
  have hh := measure_projected_centers_le_of_ball_cost
    (π := id) LipschitzWith.id μ ν
    (c := fun x : S ↦ x.val) (r := r) (t := univ)
    (fun x _ ↦ hrpos x) (fun x _ ↦ hrbound x) (fun x _ ↦ hrA x)
    (fun x _ ↦ hcost x)
  simpa only [Function.id_comp, image_univ, Subtype.range_coe_subtype,
    Set.ofPred_mem_eq, S] using hh

/-- Two genuine nonnegative densities give the HA weighted bad-set estimate:
the mass density has surface growth, while the tilt density selects the bad balls. -/
theorem lintegral_weighted_bad_set_le {n : ℕ}
    {q w : Space n → ℝ} {A : Set (Space n)} (hA : MeasurableSet A)
    (hq : IntegrableOn q A) (hqn : ∀ x, 0 ≤ q x)
    (hw : LocallyIntegrable w volume) (hwn : ∀ x, 0 ≤ w x)
    (R : ℝ) (k : ℕ) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hgrowth : ∀ x : Space n, ∀ r : ℝ, 0 < r →
      (∫ y in ball x r, w y) ≤ L * r ^ k) :
    (∫⁻ x in {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ A ∧
      η * r ^ k ≤ ∫ y in ball x r, q y}, ENNReal.ofReal (w x)) ≤
      (ENNReal.ofReal (L * (5 : ℝ) ^ k) / ENNReal.ofReal η) *
        ENNReal.ofReal (∫ x in A, q x) := by
  let μ := volume.withDensity (fun x ↦ ENNReal.ofReal (q x))
  let ν := volume.withDensity (fun x ↦ ENNReal.ofReal (w x))
  have hμ {B : Set (Space n)} (hB : MeasurableSet B) (hBA : B ⊆ A) :
      μ B = ENNReal.ofReal (∫ x in B, q x) := by
    rw [show μ B = ∫⁻ x in B, ENNReal.ofReal (q x) from withDensity_apply _ hB]
    exact (ofReal_integral_eq_lintegral_ofReal (hq.mono_set hBA)
      (Filter.Eventually.of_forall hqn)).symm
  have hν (x : Space n) (r : ℝ) :
      ν (ball x r) = ENNReal.ofReal (∫ y in ball x r, w y) := by
    rw [show ν (ball x r) = ∫⁻ y in ball x r, ENNReal.ofReal (w y) from
      withDensity_apply _ measurableSet_ball]
    exact (ofReal_integral_eq_lintegral_ofReal
      ((hw.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall)
      (Filter.Eventually.of_forall hwn)).symm
  have hh := measure_bad_set_le_of_surface_growth μ ν A R k hL hη
    (fun x r hr ↦ by rw [hν]; exact ENNReal.ofReal_le_ofReal (hgrowth x r hr))
  rw [hμ hA (Subset.refl _)] at hh
  rw [← withDensity_apply' (fun x ↦ ENNReal.ofReal (w x))]
  apply le_trans (measure_mono ?_) hh
  rintro x ⟨r, hr, hrR, hrA, hd⟩
  refine ⟨r, hr, hrR, hrA, ?_⟩
  rw [hμ measurableSet_ball hrA]
  exact ENNReal.ofReal_le_ofReal hd

end SerrinEpigraph
