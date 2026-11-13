module

public import SerrinEpigraph.WeightedGraphArea

/-!
# Compatible smooth weights and graph scales
-/

public section

open Set
open scoped Topology Manifold ContDiff

namespace SerrinEpigraph

/-- Euclidean graph area density is at least one. -/
theorem one_le_graphAreaDensity {d : ℕ} (b : Space d → ℝ) (y : Space d) :
    1 ≤ graphAreaDensity b y := by
  have hs := graphAreaDensity_sq b y
  have hp := graphAreaDensity_pos b y
  nlinarith [sq_nonneg (‖gradient b y‖)]

/-- A compact base inside a compact neighborhood admits finite smooth weights whose active
scales dominate graph area density by at most the prescribed error. -/
theorem exists_compatible_graphPartition {d : ℕ} {b : Space d → ℝ}
    (hb : ContDiff ℝ 1 b) {A B : Set (Space d)} (hA : IsCompact A) (hB : IsCompact B)
    (hBA : B ⊆ interior A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset (Space d)) (L : s → ℝ) (w : s → Space d → ℝ),
      (∀ i, 1 ≤ L i) ∧ (∀ i, ContDiff ℝ ∞ (w i)) ∧
      (∀ i, HasCompactSupport (w i)) ∧ (∀ i, tsupport (w i) ⊆ A) ∧
      (∀ i y, 0 ≤ w i y) ∧ (∀ y, ∑ i, w i y ≤ 1) ∧
      (∀ y ∈ B, ∑ i, w i y = 1) ∧
      (∀ i y, 0 < w i y → graphAreaDensity b y ≤ L i ∧ L i ≤ graphAreaDensity b y + ε) := by
  classical
  let L : Space d → ℝ := fun y ↦ graphAreaDensity b y + ε / 2
  let U : Space d → Set (Space d) := fun y ↦ interior A ∩
    {z | graphAreaDensity b z < L y ∧ L y < graphAreaDensity b z + ε}
  have hc := continuous_graphAreaDensity hb
  have hU (y : Space d) : IsOpen (U y) := isOpen_interior.inter
    ((isOpen_lt hc continuous_const).inter (isOpen_lt continuous_const (hc.add continuous_const)))
  have hself (y : Space d) (hy : y ∈ B) : y ∈ U y := by
    refine ⟨hBA hy, ?_, ?_⟩ <;> dsimp [L] <;> linarith
  have hcover : B ⊆ ⋃ y ∈ B, U y := fun y hy ↦
    mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hself y hy⟩⟩
  obtain ⟨s, _, hsfin, hscover⟩ := hB.elim_finite_subcover_image (fun y _ ↦ hU y) hcover
  let t := hsfin.toFinset
  have htcover : B ⊆ ⋃ i : t, U i := by
    simpa only [t, iUnion_subtype, hsfin.mem_toFinset] using hscover
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, Space d))
    hB.isClosed (fun i : t ↦ U i) (fun i ↦ hU i) htcover
  have hsupp (i : t) : tsupport (p i) ⊆ A :=
    (hp i).trans (fun _ hz ↦ interior_subset hz.1)
  refine ⟨t, fun i ↦ L i, fun i ↦ p i, ?_, ?_, ?_, hsupp, p.nonneg, ?_, ?_, ?_⟩
  · intro i
    have hi := one_le_graphAreaDensity b (i : Space d)
    dsimp [L]
    linarith
  · intro i
    exact (p i).contMDiff.contDiff
  · intro i
    exact hA.of_isClosed_subset (isClosed_tsupport _) (hsupp i)
  · intro y
    simpa only [finsum_eq_sum_of_fintype] using p.sum_le_one y
  · intro y hy
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hy
  · intro i y hy
    have hm : y ∈ tsupport (p i) := subset_closure (show y ∈ Function.support (p i) from ne_of_gt hy)
    exact ⟨((hp i) hm).2.1.le, ((hp i) hm).2.2.le⟩

/-- Dominating the graph area density supplies the squared slope condition for recovery. -/
theorem graphScale_controls_slope {d : ℕ} {b : Space d → ℝ} {y : Space d} {L : ℝ}
    (hL : graphAreaDensity b y ≤ L) : 1 + ‖gradient b y‖ ^ 2 ≤ L ^ 2 := by
  have hs := graphAreaDensity_sq b y
  have hp := graphAreaDensity_pos b y
  nlinarith

/-- Scales lying in the same narrow interval above area density have equally close inverses. -/
theorem graphScales_inverse_close {d : ℕ} {b : Space d → ℝ} {y : Space d} {L M ε : ℝ}
    (hL : graphAreaDensity b y ≤ L) (hM : graphAreaDensity b y ≤ M)
    (hL' : L ≤ graphAreaDensity b y + ε) (hM' : M ≤ graphAreaDensity b y + ε) :
    |L⁻¹ - M⁻¹| ≤ ε := by
  have ha := one_le_graphAreaDensity b y
  have hLp : 0 < L := lt_of_lt_of_le (graphAreaDensity_pos b y) hL
  have hMp : 0 < M := lt_of_lt_of_le (graphAreaDensity_pos b y) hM
  have hprod : 1 ≤ L * M := by nlinarith
  have he : L⁻¹ - M⁻¹ = (M - L) / (L * M) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hLp hMp)]
  apply (div_le_self (abs_nonneg _) hprod).trans
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end SerrinEpigraph
