module

public import SerrinEpigraph.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Hausdorff content: tools for Federer's dimension reduction

This module provides the measure-theoretic input of Federer's dimension reduction
(`docs/rigidity-proof/gmt-regularity.md`, GR15 and GR17) and of the link-dimension bound in
`docs/rigidity-proof/one-sided.md` §5A. Everything is stated for general (e)metric or normed
spaces and applies to `Space d` for every `d`.

We use Mathlib's unnormalized Hausdorff measure `μH[s]`, built from covers with cost
`diam ^ s`. With the same normalization:
* `hausdorffContent s` is the Hausdorff content `ℋ^s_∞`, the outer measure
  `A ↦ inf {∑ₙ diam (tₙ) ^ s : A ⊆ ⋃ₙ tₙ}` with no restriction on the size of the covering sets;
* `hausdorffApprox s δ` is the size-`δ` approximation `ℋ^s_δ`, so that
  `μH[s] = ⨆ δ > 0, ℋ^s_δ` (`hausdorffMeasure_eq_iSup_hausdorffApprox`).

## Main results

* (a) `hausdorffContent_le_hausdorffMeasure` and
  `hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero`: `ℋ^s_∞ ≤ μH[s]`, and for `s ≥ 0`
  both have the same null sets. Monotonicity and countable subadditivity are those of an outer
  measure (`hausdorffContent_mono`, `hausdorffContent_iUnion_le`).
* (b) `limsup_hausdorffContent_le`: if `K` is compact and `K j` eventually lies in every open
  thickening of `K`, then `limsup_j ℋ^s_∞ (K j) ≤ ℋ^s_∞ K`. It rests on the outer regularity
  `exists_isOpen_superset_hausdorffContent_lt`.
* (c) `hausdorffMeasure_setOf_upperContentDensity_lt_one_eq_zero` (Federer 2.10.19(2)): for
  `s ≥ 0` and an arbitrary set `A`, `μH[s]`-almost every `x ∈ A` satisfies
  `limsup_{r → 0+} ℋ^s_∞ (A ∩ B̄_r(x)) / r ^ s ≥ 1`. Consequences:
  `exists_mem_one_le_upperContentDensity` (such points exist outside any `μH[s]`-null set as
  soon as `μH[s] A ≠ 0`), `exists_seq_lt_hausdorffContent_inter_closedBall` and
  `exists_seq_lt_hausdorffContent_blowup_inter_closedBall` (radii `r k → 0+` along which the
  blow-ups `(A - x) / r k` keep content `> c` in the closed unit ball, for any `c` below the
  density, in particular any `c < 1` at the points above).
* (d) `hausdorffContent_image_le_of_lipschitzOnWith`, `hausdorffContent_vadd`,
  `hausdorffContent_smul₀`, `hausdorffContent_vadd_smul`, `hausdorffContent_affine_image`,
  `hausdorffContent_inter_closedBall_div`: Lipschitz images, translation and scaling.
* (e) For `A ⊆ sphere 0 1` and the truncated cone `{t • θ : 1 ≤ t ≤ 2, θ ∈ A}`:
  `hausdorffContent_le_hausdorffContent_cone` (`ℋ^s_∞ A ≤ ℋ^{s+1}_∞` of the cone),
  `hausdorffMeasure_cone_ne_zero`, and `dimH_cone_eq` (the cone has dimension `dimH A + 1`);
  the upper bound comes from `dimH_Icc_prod_le` (`dimH ([a, b] × A) ≤ dimH A + 1`).
* (f) `hausdorffMeasure_segment_pos`, `hausdorffMeasure_one_ne_zero_of_segment_subset`,
  `one_le_dimH_of_segment_subset`.

The density constant in (c) is `1` in this normalization; in the radius normalization
`(2r) ^ s` it is the classical `2 ^ (-s)`. The proof of (c) does not assume `μH[s] A < ∞`: on a
totally bounded set `F` with small content density, `ℋ^s_δ F ≤ ε ℋ^s_δ F` with `ε < 1` and
`ℋ^s_δ F < ∞`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology Pointwise

namespace SerrinEpigraph

/-! ### Definitions and comparison with the Hausdorff measure -/

section Content

variable {X : Type*} [EMetricSpace X]

/-- The Hausdorff content `ℋ^s_∞` (no restriction on the size of the covering sets). -/
def hausdorffContent (s : ℝ) : OuterMeasure X :=
  OuterMeasure.boundedBy fun t => ediam t ^ s

/-- The size-`δ` Hausdorff approximating outer measure `ℋ^s_δ`. -/
def hausdorffApprox (s : ℝ) (δ : ℝ≥0∞) : OuterMeasure X :=
  OuterMeasure.mkMetric'.pre (fun t => ediam t ^ s) δ

theorem hausdorffContent_apply (s : ℝ) (A : Set X) :
    hausdorffContent s A =
      ⨅ (t : ℕ → Set X) (_ : A ⊆ ⋃ n, t n), ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ s :=
  OuterMeasure.boundedBy_apply A

theorem hausdorffContent_le_ediam_rpow (s : ℝ) (A : Set X) :
    hausdorffContent s A ≤ ediam A ^ s :=
  OuterMeasure.boundedBy_le A

theorem hausdorffContent_mono (s : ℝ) {A B : Set X} (h : A ⊆ B) :
    hausdorffContent s A ≤ hausdorffContent s B :=
  measure_mono h

theorem hausdorffContent_iUnion_le (s : ℝ) (A : ℕ → Set X) :
    hausdorffContent s (⋃ n, A n) ≤ ∑' n, hausdorffContent s (A n) :=
  measure_iUnion_le A

theorem hausdorffContent_le_hausdorffApprox (s : ℝ) (δ : ℝ≥0∞) :
    (hausdorffContent s : OuterMeasure X) ≤ hausdorffApprox s δ :=
  OuterMeasure.mkMetric'.le_pre.2 fun t _ => OuterMeasure.boundedBy_le t

theorem hausdorffApprox_le_ediam_rpow (s : ℝ) {δ : ℝ≥0∞} {A : Set X} (hA : ediam A ≤ δ) :
    hausdorffApprox s δ A ≤ ediam A ^ s :=
  OuterMeasure.mkMetric'.pre_le hA

theorem hausdorffApprox_anti (s : ℝ) {δ δ' : ℝ≥0∞} (h : δ ≤ δ') (A : Set X) :
    hausdorffApprox s δ' A ≤ hausdorffApprox s δ A :=
  OuterMeasure.mkMetric'.mono_pre _ h A

section Measure

variable [MeasurableSpace X] [BorelSpace X]

theorem hausdorffMeasure_eq_iSup_hausdorffApprox (s : ℝ) (A : Set X) :
    μH[s] A = ⨆ (δ : ℝ≥0∞) (_ : 0 < δ), hausdorffApprox s δ A := by
  rw [Measure.hausdorffMeasure, ← OuterMeasure.coe_mkMetric]
  simp only [OuterMeasure.mkMetric, OuterMeasure.mkMetric', OuterMeasure.iSup_apply,
    hausdorffApprox]

theorem hausdorffApprox_le_hausdorffMeasure (s : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) (A : Set X) :
    hausdorffApprox s δ A ≤ μH[s] A := by
  rw [hausdorffMeasure_eq_iSup_hausdorffApprox]
  exact le_iSup₂_of_le δ hδ le_rfl

theorem hausdorffContent_le_hausdorffMeasure (s : ℝ) (A : Set X) :
    hausdorffContent s A ≤ μH[s] A :=
  (hausdorffContent_le_hausdorffApprox s 1 A).trans
    (hausdorffApprox_le_hausdorffMeasure s one_pos A)

end Measure

end Content

/-! ### Small content forces small covering sets; null sets -/

section NullSets

variable {X : Type*} [EMetricSpace X]

/-- A cover whose cost is below `c` exists as soon as the content is below `c`. -/
theorem exists_cover_of_hausdorffContent_lt {s : ℝ} {A : Set X} {c : ℝ≥0∞}
    (h : hausdorffContent s A < c) :
    ∃ t : ℕ → Set X, A ⊆ ⋃ n, t n ∧ ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ s < c := by
  rw [hausdorffContent_apply] at h
  simpa only [iInf_lt_iff, exists_prop] using h

/-- If the content of `A` is below `δ ^ s`, then almost optimal covers consist of sets of
diameter at most `δ`; hence the size-`δ` approximation does not exceed the content. -/
theorem hausdorffApprox_le_hausdorffContent_of_lt {s : ℝ} (hs : 0 < s) {δ : ℝ≥0∞} {A : Set X}
    (h : hausdorffContent s A < δ ^ s) :
    hausdorffApprox s δ A ≤ hausdorffContent s A := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨t, hAt, hsum⟩ := exists_cover_of_hausdorffContent_lt (lt_min hc h)
  have hpiece : ∀ n, hausdorffApprox s δ (t n) ≤ ⨆ _ : (t n).Nonempty, ediam (t n) ^ s := by
    intro n
    rcases (t n).eq_empty_or_nonempty with hn | hn
    · simp [hn]
    · have hle : ediam (t n) ^ s < δ ^ s := by
        calc ediam (t n) ^ s ≤ ⨆ _ : (t n).Nonempty, ediam (t n) ^ s := le_iSup_of_le hn le_rfl
          _ ≤ ∑' k, ⨆ _ : (t k).Nonempty, ediam (t k) ^ s :=
            ENNReal.le_tsum (f := fun k => ⨆ _ : (t k).Nonempty, ediam (t k) ^ s) n
          _ < min c (δ ^ s) := hsum
          _ ≤ δ ^ s := min_le_right _ _
      have hdiam : ediam (t n) ≤ δ := ((ENNReal.rpow_lt_rpow_iff hs).1 hle).le
      exact (hausdorffApprox_le_ediam_rpow s hdiam).trans (le_iSup_of_le hn le_rfl)
  calc hausdorffApprox s δ A ≤ hausdorffApprox s δ (⋃ n, t n) := measure_mono hAt
    _ ≤ ∑' n, hausdorffApprox s δ (t n) := measure_iUnion_le _
    _ ≤ ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ s := ENNReal.tsum_le_tsum hpiece
    _ ≤ c := hsum.le.trans (min_le_left _ _)

theorem hausdorffApprox_eq_hausdorffContent_of_lt {s : ℝ} (hs : 0 < s) {δ : ℝ≥0∞} {A : Set X}
    (h : hausdorffContent s A < δ ^ s) :
    hausdorffApprox s δ A = hausdorffContent s A :=
  le_antisymm (hausdorffApprox_le_hausdorffContent_of_lt hs h)
    (hausdorffContent_le_hausdorffApprox s δ A)

/-- In dimension zero, every nonempty set has content one. -/
theorem hausdorffContent_zero_of_nonempty {A : Set X} (hA : A.Nonempty) :
    hausdorffContent 0 A = 1 := by
  refine le_antisymm ((hausdorffContent_le_ediam_rpow 0 A).trans_eq (ENNReal.rpow_zero)) ?_
  rw [hausdorffContent_apply]
  refine le_iInf₂ fun t ht => ?_
  obtain ⟨x, hx⟩ := hA
  obtain ⟨n, hn⟩ := mem_iUnion.1 (ht hx)
  calc (1 : ℝ≥0∞) = ⨆ _ : (t n).Nonempty, ediam (t n) ^ (0 : ℝ) := by
        rw [iSup_pos ⟨x, hn⟩, ENNReal.rpow_zero]
    _ ≤ ∑' k, ⨆ _ : (t k).Nonempty, ediam (t k) ^ (0 : ℝ) :=
        ENNReal.le_tsum (f := fun k => ⨆ _ : (t k).Nonempty, ediam (t k) ^ (0 : ℝ)) n

theorem hausdorffContent_zero_eq_zero_iff {A : Set X} : hausdorffContent 0 A = 0 ↔ A = ∅ := by
  constructor
  · intro h
    by_contra hne
    rw [hausdorffContent_zero_of_nonempty (nonempty_iff_ne_empty.2 hne)] at h
    exact one_ne_zero h
  · rintro rfl
    exact measure_empty

section Measure

variable [MeasurableSpace X] [BorelSpace X]

/-- **Null sets for the Hausdorff measure and the Hausdorff content coincide.** -/
theorem hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero {s : ℝ} (hs : 0 ≤ s) {A : Set X} :
    μH[s] A = 0 ↔ hausdorffContent s A = 0 := by
  refine ⟨fun h => le_antisymm ((hausdorffContent_le_hausdorffMeasure s A).trans h.le) bot_le,
    fun h => ?_⟩
  rcases hs.eq_or_lt with rfl | hs
  · rw [hausdorffContent_zero_eq_zero_iff.1 h, measure_empty]
  rw [hausdorffMeasure_eq_iSup_hausdorffApprox]
  refine le_antisymm (iSup₂_le fun δ hδ => ?_) bot_le
  have hpos : hausdorffContent s A < δ ^ s := by
    rw [h]
    exact ENNReal.rpow_pos_of_nonneg hδ hs.le
  exact (hausdorffApprox_le_hausdorffContent_of_lt hs hpos).trans h.le

theorem hausdorffMeasure_ne_zero_iff_hausdorffContent_ne_zero {s : ℝ} (hs : 0 ≤ s) {A : Set X} :
    μH[s] A ≠ 0 ↔ hausdorffContent s A ≠ 0 :=
  (hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero hs).not

end Measure

end NullSets

/-! ### (b) Outer regularity and upper semicontinuity -/

section UpperSemicontinuity

variable {X : Type*} [EMetricSpace X]

/-- The content of a set is bounded by the cost of the set as a one-element cover. -/
theorem hausdorffContent_le_iSup_nonempty (s : ℝ) (t : Set X) :
    hausdorffContent s t ≤ ⨆ _ : t.Nonempty, ediam t ^ s := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  · rw [iSup_pos ht]
    exact hausdorffContent_le_ediam_rpow s t

/-- A small open thickening increases the cost `diam ^ s` of a set by at most `η`. -/
theorem exists_thickening_cost_le {s : ℝ} (hs : 0 ≤ s) (t : Set X) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (⨆ _ : (thickening δ t).Nonempty, ediam (thickening δ t) ^ s) ≤
        (⨆ _ : t.Nonempty, ediam t ^ s) + η := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · exact ⟨1, one_pos, by simp⟩
  simp only [iSup_pos ht]
  by_cases htop : ediam t ^ s = ⊤
  · exact ⟨1, one_pos, by simp [htop]⟩
  have hlt : ediam t ^ s < ediam t ^ s + η := ENNReal.lt_add_right htop hη
  have hcont : Tendsto (fun δ : ℝ≥0 => (ediam t + 2 * (δ : ℝ≥0∞)) ^ s) (𝓝 0)
      (𝓝 ((ediam t + 2 * ((0 : ℝ≥0) : ℝ≥0∞)) ^ s)) := by
    have : Continuous fun δ : ℝ≥0 => (ediam t + 2 * (δ : ℝ≥0∞)) ^ s :=
      ENNReal.continuous_rpow_const.comp
        (continuous_const.add
          ((ENNReal.continuous_const_mul (by simp)).comp ENNReal.continuous_coe))
    exact this.tendsto 0
  simp only [ENNReal.coe_zero, mul_zero, add_zero] at hcont
  have hev : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, (ediam t + 2 * (δ : ℝ≥0∞)) ^ s < ediam t ^ s + η :=
    (hcont.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨δ, hδpos, ?_⟩
  have hiS : ∀ _ : (thickening (δ : ℝ) t).Nonempty,
      ediam (thickening (δ : ℝ) t) ^ s ≤ ediam t ^ s + η := fun _ =>
    (ENNReal.rpow_le_rpow (ediam_thickening_le δ) hs).trans hδ.le
  exact iSup_le hiS

/-- **Outer approximation by open sets.** If the content of `A` is below `c`, then so is the
content of some open neighbourhood of `A`. -/
theorem exists_isOpen_superset_hausdorffContent_lt {s : ℝ} (hs : 0 ≤ s) {A : Set X} {c : ℝ≥0∞}
    (h : hausdorffContent s A < c) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ hausdorffContent s U < c := by
  obtain ⟨t, hAt, hsum⟩ := exists_cover_of_hausdorffContent_lt h
  set S := ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ s with hS
  have hgap : c - S ≠ 0 := (tsub_pos_of_lt hsum).ne'
  obtain ⟨η, hηpos, hηsum⟩ := ENNReal.exists_pos_sum_of_countable hgap ℕ
  have hδ : ∀ n, ∃ δ : ℝ, 0 < δ ∧
      (⨆ _ : (thickening δ (t n)).Nonempty, ediam (thickening δ (t n)) ^ s) ≤
        (⨆ _ : (t n).Nonempty, ediam (t n) ^ s) + η n := fun n =>
    exists_thickening_cost_le hs (t n) (by simpa using (hηpos n).ne')
  choose δ hδpos hδle using hδ
  refine ⟨⋃ n, thickening (δ n) (t n), isOpen_iUnion fun n => isOpen_thickening,
    hAt.trans (iUnion_mono fun n => self_subset_thickening (hδpos n) _), ?_⟩
  calc hausdorffContent s (⋃ n, thickening (δ n) (t n))
      ≤ ∑' n, hausdorffContent s (thickening (δ n) (t n)) := measure_iUnion_le _
    _ ≤ ∑' n, ((⨆ _ : (t n).Nonempty, ediam (t n) ^ s) + η n) :=
        ENNReal.tsum_le_tsum fun n =>
          (hausdorffContent_le_iSup_nonempty s _).trans (hδle n)
    _ = S + ∑' n, (η n : ℝ≥0∞) := ENNReal.tsum_add
    _ < S + (c - S) := ENNReal.add_lt_add_left (hsum.trans_le le_top).ne hηsum
    _ = c := add_tsub_cancel_of_le hsum.le

/-- For a compact set, some open thickening has content arbitrarily close to that of the set. -/
theorem exists_hausdorffContent_thickening_lt_of_isCompact {s : ℝ} (hs : 0 ≤ s) {K : Set X}
    (hK : IsCompact K) {c : ℝ≥0∞} (h : hausdorffContent s K < c) :
    ∃ ε : ℝ, 0 < ε ∧ hausdorffContent s (thickening ε K) < c := by
  obtain ⟨U, hU, hKU, hUc⟩ := exists_isOpen_superset_hausdorffContent_lt hs h
  obtain ⟨ε, hε, hεU⟩ := hK.exists_thickening_subset_open hU hKU
  exact ⟨ε, hε, (measure_mono hεU).trans_lt hUc⟩

/-- The contents of the thickenings of a compact set converge to its content. -/
theorem tendsto_hausdorffContent_thickening_of_isCompact {s : ℝ} (hs : 0 ≤ s) {K : Set X}
    (hK : IsCompact K) :
    Tendsto (fun ε : ℝ => hausdorffContent s (thickening ε K)) (𝓝[>] 0)
      (𝓝 (hausdorffContent s K)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ha.trans_le (measure_mono (self_subset_thickening hε K))
  · obtain ⟨ε₀, hε₀, hlt⟩ := exists_hausdorffContent_thickening_lt_of_isCompact hs hK hc
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    exact (measure_mono (thickening_mono hε.2.le K)).trans_lt hlt

/-- **Upper semicontinuity of the Hausdorff content under Hausdorff convergence from inside.**
If `K` is compact and, for every `ε > 0`, eventually `K j` lies in the open `ε`-thickening of
`K`, then `limsup_j ℋ^s_∞ (K j) ≤ ℋ^s_∞ K`. The sets `K j` need not be compact. -/
theorem limsup_hausdorffContent_le {ι : Type*} {l : Filter ι} {s : ℝ} (hs : 0 ≤ s) {K : Set X}
    (hK : IsCompact K) {Kj : ι → Set X} (hKj : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in l, Kj j ⊆ thickening ε K) :
    limsup (fun j => hausdorffContent s (Kj j)) l ≤ hausdorffContent s K := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨ε, hε, hlt⟩ := exists_hausdorffContent_thickening_lt_of_isCompact hs hK hc
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hKj ε hε] with j hj
  exact ((measure_mono hj).trans_lt hlt).le

end UpperSemicontinuity

/-! ### (d) Lipschitz images -/

section Lipschitz

variable {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

theorem ediam_image_le_of_lipschitzOnWith {K : ℝ≥0} {f : X → Y} {A t : Set X}
    (hf : LipschitzOnWith K f A) (ht : t ⊆ A) : ediam (f '' t) ≤ K * ediam t := by
  rw [ediam_image_le_iff]
  intro x hx y hy
  exact (hf (ht hx) (ht hy)).trans (mul_le_mul_right (edist_le_ediam_of_mem hx hy) _)

/-- A `K`-Lipschitz map increases the Hausdorff content at most by the factor `K ^ s`. -/
theorem hausdorffContent_image_le_of_lipschitzOnWith {K : ℝ≥0} {f : X → Y} {A : Set X}
    (hf : LipschitzOnWith K f A) {s : ℝ} (hs : 0 ≤ s) :
    hausdorffContent s (f '' A) ≤ (K : ℝ≥0∞) ^ s * hausdorffContent s A := by
  have hKs : (K : ℝ≥0∞) ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs ENNReal.coe_ne_top
  have key : OuterMeasure.restrict A (OuterMeasure.comap f (hausdorffContent s)) ≤
      OuterMeasure.boundedBy ((K : ℝ≥0∞) ^ s • fun t : Set X => ediam t ^ s) := by
    refine OuterMeasure.le_boundedBy.2 fun t => ?_
    rw [OuterMeasure.restrict_apply, OuterMeasure.comap_apply, Pi.smul_apply, smul_eq_mul]
    calc hausdorffContent s (f '' (t ∩ A)) ≤ ediam (f '' (t ∩ A)) ^ s :=
          hausdorffContent_le_ediam_rpow s _
      _ ≤ ((K : ℝ≥0∞) * ediam t) ^ s :=
          ENNReal.rpow_le_rpow ((ediam_image_le_of_lipschitzOnWith hf inter_subset_right).trans
            (mul_le_mul_right (ediam_mono inter_subset_left) _)) hs
      _ = (K : ℝ≥0∞) ^ s * ediam t ^ s := ENNReal.mul_rpow_of_nonneg _ _ hs
  have hsmul : OuterMeasure.boundedBy ((K : ℝ≥0∞) ^ s • fun t : Set X => ediam t ^ s) =
      (K : ℝ≥0∞) ^ s • (hausdorffContent s : OuterMeasure X) :=
    (OuterMeasure.smul_boundedBy hKs).symm
  have := key A
  rwa [hsmul, OuterMeasure.restrict_apply, OuterMeasure.comap_apply, inter_self, smul_apply,
    smul_eq_mul] at this

theorem hausdorffContent_image_le_of_lipschitzWith {K : ℝ≥0} {f : X → Y}
    (hf : LipschitzWith K f) {s : ℝ} (hs : 0 ≤ s) (A : Set X) :
    hausdorffContent s (f '' A) ≤ (K : ℝ≥0∞) ^ s * hausdorffContent s A :=
  hausdorffContent_image_le_of_lipschitzOnWith hf.lipschitzOnWith hs

/-- Isometric equivalences preserve the Hausdorff content. -/
theorem hausdorffContent_image_isometryEquiv (e : X ≃ᵢ Y) {s : ℝ} (hs : 0 ≤ s) (A : Set X) :
    hausdorffContent s (e '' A) = hausdorffContent s A := by
  refine le_antisymm ?_ ?_
  · simpa using hausdorffContent_image_le_of_lipschitzWith e.isometry.lipschitzWith hs A
  · have h := hausdorffContent_image_le_of_lipschitzWith e.symm.isometry.lipschitzWith hs (e '' A)
    have hA : e.symm '' (e '' A) = A := by
      rw [image_image]
      simp
    rwa [hA, ENNReal.coe_one, ENNReal.one_rpow, one_mul] at h

end Lipschitz

/-! ### (d) Translations, dilations and blow-ups -/

section Scaling

variable {E : Type*} [NormedAddCommGroup E]

/-- **Translation invariance** of the Hausdorff content. -/
theorem hausdorffContent_vadd {s : ℝ} (hs : 0 ≤ s) (x : E) (A : Set E) :
    hausdorffContent s (x +ᵥ A) = hausdorffContent s A := by
  rw [← image_vadd]
  exact hausdorffContent_image_isometryEquiv (IsometryEquiv.constVAdd (X := E) x) hs A

/-- **Scaling law** of the Hausdorff content: `ℋ^s_∞ (r • A) = ‖r‖ ^ s * ℋ^s_∞ A`. -/
theorem hausdorffContent_smul₀ {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E]
    [NormSMulClass 𝕜 E] {s : ℝ} (hs : 0 ≤ s) {r : 𝕜} (hr : r ≠ 0) (A : Set E) :
    hausdorffContent s (r • A) = (‖r‖₊ : ℝ≥0∞) ^ s * hausdorffContent s A := by
  have hle : ∀ (c : 𝕜) (B : Set E),
      hausdorffContent s (c • B) ≤ (‖c‖₊ : ℝ≥0∞) ^ s * hausdorffContent s B := fun c B => by
    rw [← image_smul]
    exact hausdorffContent_image_le_of_lipschitzWith (lipschitzWith_smul c) hs B
  refine le_antisymm (hle r A) ?_
  have h := hle r⁻¹ (r • A)
  rw [inv_smul_smul₀ hr] at h
  have hone : (‖r‖₊ : ℝ≥0∞) ^ s * (‖r⁻¹‖₊ : ℝ≥0∞) ^ s = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hs, ← ENNReal.coe_mul, nnnorm_inv,
      mul_inv_cancel₀ (nnnorm_ne_zero_iff.2 hr), ENNReal.coe_one, ENNReal.one_rpow]
  calc (‖r‖₊ : ℝ≥0∞) ^ s * hausdorffContent s A
      ≤ (‖r‖₊ : ℝ≥0∞) ^ s * ((‖r⁻¹‖₊ : ℝ≥0∞) ^ s * hausdorffContent s (r • A)) :=
        mul_le_mul_right h _
    _ = hausdorffContent s (r • A) := by rw [← mul_assoc, hone, one_mul]

variable [NormedSpace ℝ E]

/-- Affine images `y ↦ x + r • y` with `r > 0` multiply the content by `r ^ s`. -/
theorem hausdorffContent_affine_image {s : ℝ} (hs : 0 ≤ s) (x : E) {r : ℝ} (hr : 0 < r)
    (A : Set E) :
    hausdorffContent s ((fun y => x + r • y) '' A) =
      ENNReal.ofReal r ^ s * hausdorffContent s A := by
  have himage : (fun y => x + r • y) '' A = x +ᵥ (r • A) := by
    rw [← image_smul, ← image_vadd, image_image]
    rfl
  rw [himage, hausdorffContent_vadd hs, hausdorffContent_smul₀ hs hr.ne', ← enorm_eq_nnnorm,
    Real.enorm_eq_ofReal hr.le]

/-- Pointwise form of the scaling law: `ℋ^s_∞ (x +ᵥ r • A) = r ^ s * ℋ^s_∞ A` for `r > 0`. -/
theorem hausdorffContent_vadd_smul {s : ℝ} (hs : 0 ≤ s) (x : E) {r : ℝ} (hr : 0 < r)
    (A : Set E) :
    hausdorffContent s (x +ᵥ r • A) = ENNReal.ofReal r ^ s * hausdorffContent s A := by
  rw [hausdorffContent_vadd hs, hausdorffContent_smul₀ hs hr.ne', ← enorm_eq_nnnorm,
    Real.enorm_eq_ofReal hr.le]

/-- Blow-ups `y ↦ r⁻¹ • (y - x)` with `r > 0` divide the content by `r ^ s`. -/
theorem hausdorffContent_blowup_image {s : ℝ} (hs : 0 ≤ s) (x : E) {r : ℝ} (hr : 0 < r)
    (A : Set E) :
    hausdorffContent s ((fun y => r⁻¹ • (y - x)) '' A) =
      hausdorffContent s A / ENNReal.ofReal r ^ s := by
  have hfun : (fun y => r⁻¹ • (y - x)) = fun y => (-(r⁻¹ • x)) + r⁻¹ • y := by
    funext y
    rw [smul_sub]
    abel
  rw [hfun, hausdorffContent_affine_image hs _ (inv_pos.2 hr), ENNReal.ofReal_inv_of_pos hr,
    ENNReal.inv_rpow, ENNReal.div_eq_inv_mul]

/-- The blow-up of `A ∩ closedBall x r` is the blow-up of `A` intersected with the unit ball. -/
theorem blowup_image_inter_closedBall (x : E) {r : ℝ} (hr : 0 < r) (A : Set E) :
    (fun y => r⁻¹ • (y - x)) '' (A ∩ closedBall x r) =
      ((fun y => r⁻¹ • (y - x)) '' A) ∩ closedBall 0 1 := by
  ext z
  simp only [mem_image, mem_inter_iff, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨y, ⟨hyA, hyr⟩, rfl⟩
    refine ⟨⟨y, hyA, rfl⟩, ?_⟩
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← dist_eq_norm]
    exact inv_mul_le_one_of_le₀ hyr hr.le
  · rintro ⟨⟨y, hyA, rfl⟩, hz⟩
    refine ⟨y, ⟨hyA, ?_⟩, rfl⟩
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← dist_eq_norm] at hz
    rwa [inv_mul_le_one₀ hr] at hz

/-- The density ratio `ℋ^s_∞ (A ∩ B_r(x)) / r ^ s` is the content of the blown-up set in the unit
ball. -/
theorem hausdorffContent_inter_closedBall_div {s : ℝ} (hs : 0 ≤ s) (x : E) {r : ℝ} (hr : 0 < r)
    (A : Set E) :
    hausdorffContent s (A ∩ closedBall x r) / ENNReal.ofReal r ^ s =
      hausdorffContent s (((fun y => r⁻¹ • (y - x)) '' A) ∩ closedBall 0 1) := by
  rw [← blowup_image_inter_closedBall x hr A, hausdorffContent_blowup_image hs x hr]

end Scaling

/-! ### (c) Federer's content density theorem -/

section Density

variable {X : Type*} [MetricSpace X]

/-- The size-`δ` approximating measure of a totally bounded set is finite. -/
theorem hausdorffApprox_lt_top_of_totallyBounded {s : ℝ} (hs : 0 ≤ s) {F : Set X}
    (hF : TotallyBounded F) {δ : ℝ} (hδ : 0 < δ) :
    hausdorffApprox s (ENNReal.ofReal δ) F < ⊤ := by
  obtain ⟨t, htfin, hFt⟩ := Metric.totallyBounded_iff.1 hF (δ / 2) (half_pos hδ)
  have hdiam : ∀ y : X, ediam (ball y (δ / 2)) ≤ ENNReal.ofReal δ := by
    intro y
    refine ediam_le_of_forall_dist_le fun a ha b hb => ?_
    calc dist a b ≤ dist a y + dist y b := dist_triangle _ _ _
      _ ≤ δ / 2 + δ / 2 := by
          rw [dist_comm y b]
          exact add_le_add (mem_ball.1 ha).le (mem_ball.1 hb).le
      _ = δ := add_halves δ
  have hcover : F ⊆ ⋃ y ∈ htfin.toFinset, ball y (δ / 2) := by
    simpa only [Set.Finite.mem_toFinset] using hFt
  calc hausdorffApprox s (ENNReal.ofReal δ) F
      ≤ hausdorffApprox s (ENNReal.ofReal δ) (⋃ y ∈ htfin.toFinset, ball y (δ / 2)) :=
        measure_mono hcover
    _ ≤ ∑ y ∈ htfin.toFinset, hausdorffApprox s (ENNReal.ofReal δ) (ball y (δ / 2)) :=
        measure_biUnion_finset_le _ _
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.2 fun y _ => ?_
        calc hausdorffApprox s (ENNReal.ofReal δ) (ball y (δ / 2))
            ≤ ediam (ball y (δ / 2)) ^ s := hausdorffApprox_le_ediam_rpow s (hdiam y)
          _ ≤ ENNReal.ofReal δ ^ s := ENNReal.rpow_le_rpow (hdiam y) hs
          _ < ⊤ := ENNReal.rpow_lt_top_of_nonneg hs ENNReal.ofReal_ne_top

/-- One piece of a cover of size `δ < r₀`: if `F` has small content in all balls of radius
`< r₀` centred on `F`, then the `δ`-approximating measure of `t ∩ F` is at most
`ε * diam t ^ s`. -/
theorem hausdorffApprox_inter_le_of_hausdorffContent_le {s : ℝ} (hs : 0 < s) {ε : ℝ≥0∞}
    (hε : ε < 1) {F : Set X} {r₀ δ : ℝ} (hδ : 0 < δ) (hδr : δ < r₀)
    (h : ∀ x ∈ F, ∀ r ∈ Ioo 0 r₀,
      hausdorffContent s (F ∩ closedBall x r) ≤ ε * ENNReal.ofReal r ^ s)
    {t : Set X} (ht : ediam t ≤ ENNReal.ofReal δ) :
    hausdorffApprox s (ENNReal.ofReal δ) (t ∩ F) ≤ ε * ediam t ^ s := by
  rcases (t ∩ F).eq_empty_or_nonempty with he | ⟨x, hxt, hxF⟩
  · rw [he, measure_empty]
    exact zero_le
  have hfin : ediam t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ht
  set ρ := (ediam t).toReal with hρ
  have hρeq : ENNReal.ofReal ρ = ediam t := ENNReal.ofReal_toReal hfin
  have hsub : t ∩ F ⊆ F ∩ closedBall x ρ := by
    rintro y ⟨hyt, hyF⟩
    refine ⟨hyF, ?_⟩
    rw [mem_closedBall, dist_edist]
    exact ENNReal.toReal_mono hfin (edist_le_ediam_of_mem hyt hxt)
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : 0 ≤ ρ) with hρ0 | hρpos
  · have h0 : ediam t = 0 := by
      have h0' : ENNReal.ofReal ρ = 0 := ENNReal.ofReal_eq_zero.2 hρ0.symm.le
      rw [← hρeq, h0']
    have h0' : ediam (t ∩ F) = 0 :=
      le_antisymm ((ediam_mono inter_subset_left).trans h0.le) (zero_le)
    calc hausdorffApprox s (ENNReal.ofReal δ) (t ∩ F) ≤ ediam (t ∩ F) ^ s :=
          hausdorffApprox_le_ediam_rpow s (h0'.le.trans (zero_le))
      _ = 0 := by rw [h0', ENNReal.zero_rpow_of_pos hs]
      _ ≤ ε * ediam t ^ s := zero_le
  have hρr : ρ < r₀ := (ENNReal.toReal_le_of_le_ofReal hδ.le ht).trans_lt hδr
  have hc : hausdorffContent s (t ∩ F) ≤ ε * ediam t ^ s :=
    calc hausdorffContent s (t ∩ F) ≤ hausdorffContent s (F ∩ closedBall x ρ) := measure_mono hsub
      _ ≤ ε * ENNReal.ofReal ρ ^ s := h x hxF ρ ⟨hρpos, hρr⟩
      _ = ε * ediam t ^ s := by rw [hρeq]
  have hpos : ediam t ^ s ≠ 0 := by
    rw [← hρeq]
    exact (ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.2 hρpos) hs.le).ne'
  have hne : ediam t ^ s ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs.le hfin
  have hlt : ε * ediam t ^ s < ENNReal.ofReal δ ^ s :=
    calc ε * ediam t ^ s < 1 * ediam t ^ s := ENNReal.mul_lt_mul_left hpos hne hε
      _ = ediam t ^ s := one_mul _
      _ ≤ ENNReal.ofReal δ ^ s := ENNReal.rpow_le_rpow ht hs.le
  exact (hausdorffApprox_le_hausdorffContent_of_lt hs (hc.trans_lt hlt)).trans hc

/-- The upper density of `A` at `x` measured with the Hausdorff content:
`limsup_{r → 0+} ℋ^s_∞ (A ∩ B̄_r(x)) / r ^ s`. -/
def upperContentDensity (s : ℝ) (A : Set X) (x : X) : ℝ≥0∞ :=
  limsup (fun r : ℝ => hausdorffContent s (A ∩ closedBall x r) / ENNReal.ofReal r ^ s) (𝓝[>] 0)

/-- If `c` is below the upper content density of `A` at `x` (e.g. `c < 1 ≤` the density), then
there is a sequence of radii `r k → 0+` with `c * r k ^ s < ℋ^s_∞ (A ∩ B̄_{r k}(x))`. -/
theorem exists_seq_lt_hausdorffContent_inter_closedBall {s : ℝ} {A : Set X} {x : X}
    {c : ℝ≥0∞} (hc : c < upperContentDensity s A x) :
    ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ Tendsto r atTop (𝓝[>] 0) ∧
      ∀ k, c * ENNReal.ofReal (r k) ^ s < hausdorffContent s (A ∩ closedBall x (r k)) := by
  have hfreq : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      c < hausdorffContent s (A ∩ closedBall x r) / ENNReal.ofReal r ^ s :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hc
  have hfreq' : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      0 < r ∧ c < hausdorffContent s (A ∩ closedBall x r) / ENNReal.ofReal r ^ s :=
    (hfreq.and_eventually self_mem_nhdsWithin).mono fun r hr => ⟨hr.2, hr.1⟩
  obtain ⟨r, hr_tendsto, hr⟩ := frequently_iff_seq_forall.1 hfreq'
  refine ⟨r, fun k => (hr k).1, hr_tendsto, fun k => ?_⟩
  have hpos : ENNReal.ofReal (r k) ≠ 0 := (ENNReal.ofReal_pos.2 (hr k).1).ne'
  have hne0 : ENNReal.ofReal (r k) ^ s ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hpos) ENNReal.ofReal_ne_top).ne'
  have hnetop : ENNReal.ofReal (r k) ^ s ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hpos ENNReal.ofReal_ne_top
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl hne0) (Or.inl hnetop)).1 (hr k).2

/-- In dimension `0` the upper content density at points of `A` equals one. -/
theorem upperContentDensity_zero_of_mem {A : Set X} {x : X} (hx : x ∈ A) :
    upperContentDensity 0 A x = 1 := by
  unfold upperContentDensity
  rw [limsup_congr (v := fun _ => (1 : ℝ≥0∞)) ?_, limsup_const]
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hne : (A ∩ closedBall x r).Nonempty := ⟨x, hx, mem_closedBall_self (le_of_lt hr)⟩
  rw [hausdorffContent_zero_of_nonempty hne, ENNReal.rpow_zero, div_one]

variable [MeasurableSpace X] [BorelSpace X]

/-- **Federer's density lemma, key step.** Let `s > 0`, `ε < 1`, and let `F` be totally
bounded. If `ℋ^s_∞ (F ∩ B_r(x)) ≤ ε r ^ s` for all `x ∈ F` and all `0 < r < r₀`, then
`μH[s] F = 0`. No finiteness of `μH[s] F` is assumed. -/
theorem hausdorffMeasure_eq_zero_of_hausdorffContent_inter_closedBall_le {s : ℝ} (hs : 0 < s)
    {ε : ℝ≥0∞} (hε : ε < 1) {F : Set X} (hF : TotallyBounded F) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ x ∈ F, ∀ r ∈ Ioo 0 r₀,
      hausdorffContent s (F ∩ closedBall x r) ≤ ε * ENNReal.ofReal r ^ s) :
    μH[s] F = 0 := by
  have hstep : ∀ δ : ℝ, 0 < δ → δ < r₀ → hausdorffApprox s (ENNReal.ofReal δ) F = 0 := by
    intro δ hδ hδr
    set P : OuterMeasure X := hausdorffApprox s (ENNReal.ofReal δ) with hP
    have hle : ε⁻¹ • OuterMeasure.restrict F P ≤ P := by
      refine OuterMeasure.mkMetric'.le_pre.2 fun t ht => ?_
      rw [smul_apply, OuterMeasure.restrict_apply, smul_eq_mul]
      calc ε⁻¹ * P (t ∩ F) ≤ ε⁻¹ * (ε * ediam t ^ s) :=
            mul_le_mul_right (hausdorffApprox_inter_le_of_hausdorffContent_le hs hε hδ hδr h ht) _
        _ = (ε⁻¹ * ε) * ediam t ^ s := (mul_assoc _ _ _).symm
        _ ≤ 1 * ediam t ^ s := mul_le_mul_left (ENNReal.inv_mul_le_one ε) _
        _ = ediam t ^ s := one_mul _
    have hF' : ε⁻¹ * P F ≤ P F := by
      have := hle F
      rwa [smul_apply, OuterMeasure.restrict_apply, inter_self, smul_eq_mul] at this
    have hfin : P F ≠ ⊤ := (hausdorffApprox_lt_top_of_totallyBounded hs.le hF hδ).ne
    by_contra hne
    have hlt : 1 * P F < ε⁻¹ * P F :=
      ENNReal.mul_lt_mul_left hne hfin (ENNReal.one_lt_inv.2 hε)
    rw [one_mul] at hlt
    exact hlt.not_ge hF'
  rw [hausdorffMeasure_eq_iSup_hausdorffApprox]
  refine le_antisymm (iSup₂_le fun δ hδ => ?_) bot_le
  obtain ⟨r, -, hr0, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 hr0
  set δ' := min r (r₀ / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hrpos (half_pos hr₀)
  have hδ'r : δ' < r₀ := (min_le_right _ _).trans_lt (half_lt_self hr₀)
  have hδ'δ : ENNReal.ofReal δ' ≤ δ :=
    (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans hrδ.le
  calc hausdorffApprox s δ F ≤ hausdorffApprox s (ENNReal.ofReal δ') F :=
        hausdorffApprox_anti s hδ'δ F
    _ = 0 := hstep δ' hδ'pos hδ'r
    _ ≤ ⊥ := le_rfl

/-- **Federer's content density theorem** (Federer 2.10.19(2), with our normalization).
For `s ≥ 0`, the points of an arbitrary set `A` at which the upper content density of `A` is
less than one form a `μH[s]`-null set. -/
theorem hausdorffMeasure_setOf_upperContentDensity_lt_one_eq_zero [SigmaCompactSpace X] {s : ℝ}
    (hs : 0 ≤ s) (A : Set X) :
    μH[s] {x | x ∈ A ∧ upperContentDensity s A x < 1} = 0 := by
  rcases hs.eq_or_lt with rfl | hs
  · have hempty : {x | x ∈ A ∧ upperContentDensity 0 A x < 1} = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have h1 := hx.2
      rw [upperContentDensity_zero_of_mem hx.1] at h1
      exact lt_irrefl _ h1
    rw [hempty, measure_empty]
  set q' : ℚ → ℝ≥0∞ := fun q => (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) with hq'
  set G : ℚ → ℕ → ℕ → Set X := fun q n m =>
    {x | x ∈ A ∧ x ∈ compactCovering X m ∧ q' q < 1 ∧
      ∀ r ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        hausdorffContent s (A ∩ closedBall x r) ≤ q' q * ENNReal.ofReal r ^ s} with hG
  have hBG : {x | x ∈ A ∧ upperContentDensity s A x < 1} ⊆ ⋃ q, ⋃ n, ⋃ m, G q n m := by
    rintro x ⟨hxA, hx⟩
    obtain ⟨q, -, hdq, hq1⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hx
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        hausdorffContent s (A ∩ closedBall x r) / ENNReal.ofReal r ^ s < q' q :=
      eventually_lt_of_limsup_lt hdq (by isBoundedDefault)
    obtain ⟨r₁, hr₁, hr₁sub⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr₁
    have hxm : x ∈ ⋃ m, compactCovering X m := by
      rw [iUnion_compactCovering]
      exact mem_univ x
    obtain ⟨m, hm⟩ := mem_iUnion.1 hxm
    refine mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨m, hxA, hm, hq1, fun r hr => ?_⟩⟩⟩
    have hrlt := hr₁sub ⟨hr.1, hr.2.trans hn⟩
    have hpos : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr.1).ne'
    have hne0 : ENNReal.ofReal r ^ s ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hpos) ENNReal.ofReal_ne_top).ne'
    have hnetop : ENNReal.ofReal r ^ s ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero hpos ENNReal.ofReal_ne_top
    exact ((ENNReal.div_lt_iff (Or.inl hne0) (Or.inl hnetop)).1 hrlt).le
  have hGnull : ∀ q n m, μH[s] (G q n m) = 0 := by
    intro q n m
    rcases (G q n m).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · rw [he, measure_empty]
    have hq1 : q' q < 1 := hx₀.2.2.1
    have htb : TotallyBounded (G q n m) :=
      (isCompact_compactCovering X m).totallyBounded.subset fun x hx => hx.2.1
    refine hausdorffMeasure_eq_zero_of_hausdorffContent_inter_closedBall_le hs hq1 htb
      (r₀ := 1 / ((n : ℝ) + 1)) (by positivity) fun x hx r hr => ?_
    exact (measure_mono (inter_subset_inter_left _ fun y hy => hy.1)).trans (hx.2.2.2 r hr)
  exact measure_mono_null hBG (measure_iUnion_null fun q => measure_iUnion_null fun n =>
    measure_iUnion_null fun m => hGnull q n m)

/-- **Content density points exist outside any null set.** If `μH[s] A ≠ 0` and
`μH[s] N = 0`, there is `x ∈ A \ N` at which the upper content density of `A` is at least one. -/
theorem exists_mem_one_le_upperContentDensity [SigmaCompactSpace X] {s : ℝ} (hs : 0 ≤ s)
    {A N : Set X} (hA : μH[s] A ≠ 0) (hN : μH[s] N = 0) :
    ∃ x ∈ A, x ∉ N ∧ 1 ≤ upperContentDensity s A x := by
  by_contra hcon
  push Not at hcon
  apply hA
  have hsub : A ⊆ {x | x ∈ A ∧ upperContentDensity s A x < 1} ∪ N := by
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, hcon x hx hxN⟩
  exact measure_mono_null hsub
    (measure_union_null (hausdorffMeasure_setOf_upperContentDensity_lt_one_eq_zero hs A) hN)

/-- **Content density lemma** (GR15): if `μH[s] A ≠ 0` then some point of `A` has upper
content density at least one. -/
theorem exists_mem_one_le_upperContentDensity_of_ne_zero [SigmaCompactSpace X] {s : ℝ}
    (hs : 0 ≤ s) {A : Set X} (hA : μH[s] A ≠ 0) :
    ∃ x ∈ A, 1 ≤ upperContentDensity s A x := by
  obtain ⟨x, hxA, -, hx⟩ := exists_mem_one_le_upperContentDensity hs hA (N := ∅) measure_empty
  exact ⟨x, hxA, hx⟩

end Density

/-! ### (c) Blow-ups at content density points -/

section BlowUp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Blow-ups at a content density point keep uniformly positive content in the unit ball.**
If `c` is below the upper content density of `A` at `x` (e.g. `c < 1 ≤` the density), there
are radii `r k → 0+` such that the blow-ups `(A - x) / r k` have content `> c` in
`closedBall 0 1`. -/
theorem exists_seq_lt_hausdorffContent_blowup_inter_closedBall {s : ℝ} (hs : 0 ≤ s) {A : Set E}
    {x : E} {c : ℝ≥0∞} (hc : c < upperContentDensity s A x) :
    ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ Tendsto r atTop (𝓝[>] 0) ∧
      ∀ k, c < hausdorffContent s (((fun y => (r k)⁻¹ • (y - x)) '' A) ∩ closedBall 0 1) := by
  obtain ⟨r, hrpos, hrlim, hr⟩ := exists_seq_lt_hausdorffContent_inter_closedBall hc
  refine ⟨r, hrpos, hrlim, fun k => ?_⟩
  rw [← hausdorffContent_inter_closedBall_div hs x (hrpos k)]
  have hpos : ENNReal.ofReal (r k) ≠ 0 := (ENNReal.ofReal_pos.2 (hrpos k)).ne'
  have hne0 : ENNReal.ofReal (r k) ^ s ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hpos) ENNReal.ofReal_ne_top).ne'
  have hnetop : ENNReal.ofReal (r k) ^ s ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hpos ENNReal.ofReal_ne_top
  exact (ENNReal.lt_div_iff_mul_lt (Or.inl hne0) (Or.inl hnetop)).2 (hr k)

end BlowUp

/-! ### (f) Segments -/

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nondegenerate segment has positive one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_segment_pos [MeasurableSpace E] [BorelSpace E] {x y : E} (h : x ≠ y) :
    0 < μH[1] (segment ℝ x y) := by
  rw [hausdorffMeasure_segment]
  exact edist_pos.2 h

/-- A set containing a nondegenerate segment has nonzero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_one_ne_zero_of_segment_subset [MeasurableSpace E] [BorelSpace E]
    {x y : E} (h : x ≠ y) {S : Set E} (hS : segment ℝ x y ⊆ S) : μH[1] S ≠ 0 :=
  ((hausdorffMeasure_segment_pos h).trans_le (measure_mono hS)).ne'

/-- A set containing a nondegenerate segment has Hausdorff dimension at least one. -/
theorem one_le_dimH_of_segment_subset {x y : E} (h : x ≠ y) {S : Set E}
    (hS : segment ℝ x y ⊆ S) : 1 ≤ dimH S := by
  borelize E
  have hS1 : μH[((1 : ℝ≥0) : ℝ)] S ≠ 0 := by
    rw [NNReal.coe_one]
    exact hausdorffMeasure_one_ne_zero_of_segment_subset h hS
  simpa using le_dimH_of_hausdorffMeasure_ne_zero hS1

end Segment

/-! ### Products with an interval raise the dimension by at most one -/

section Product

variable {Y : Type*} [EMetricSpace Y]

/-- `[a, b]` is covered by `⌊(b - a) / ρ⌋ + 1` closed intervals of length `ρ`. -/
theorem Icc_subset_biUnion_Icc_range {a b ρ : ℝ} (hρ : 0 < ρ) :
    Icc a b ⊆ ⋃ k ∈ Finset.range (⌊(b - a) / ρ⌋₊ + 1),
      Icc (a + (k : ℝ) * ρ) (a + ((k : ℝ) + 1) * ρ) := by
  intro x hx
  have hxa : 0 ≤ (x - a) / ρ := div_nonneg (sub_nonneg.2 hx.1) hρ.le
  have hk : ⌊(x - a) / ρ⌋₊ < ⌊(b - a) / ρ⌋₊ + 1 :=
    Nat.lt_succ_of_le (Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith [hx.2]) hρ.le))
  refine mem_iUnion₂.2 ⟨⌊(x - a) / ρ⌋₊, Finset.mem_range.2 hk, ?_, ?_⟩
  · have h1 := Nat.floor_le hxa
    rw [le_div_iff₀ hρ] at h1
    linarith
  · have h2 := Nat.lt_floor_add_one ((x - a) / ρ)
    rw [div_lt_iff₀ hρ] at h2
    linarith

/-- Diameter of a product with an interval of length `ρ`. -/
theorem ediam_Icc_prod_le {c ρ : ℝ} {B : Set Y} (hB : ediam B ≤ ENNReal.ofReal ρ) :
    ediam (Icc c (c + ρ) ×ˢ B) ≤ ENNReal.ofReal ρ := by
  refine ediam_le fun p hp q hq => ?_
  rw [Prod.edist_eq]
  refine max_le ?_ ((edist_le_ediam_of_mem hp.2 hq.2).trans hB)
  calc edist p.1 q.1 ≤ ediam (Icc c (c + ρ)) := edist_le_ediam_of_mem hp.1 hq.1
    _ = ENNReal.ofReal ρ := by rw [Real.ediam_Icc, add_sub_cancel_left]

/-- **Content of a product with an interval.** If `diam B ≤ ρ`, then
`ℋ^{s+1}_∞ ([a, b] × B) ≤ (b - a) ρ ^ s + ρ ^ (s + 1)`. -/
theorem hausdorffContent_Icc_prod_le {s : ℝ} (hs : 0 ≤ s) {a b ρ : ℝ} (hab : a ≤ b)
    (hρ : 0 < ρ) {B : Set Y} (hB : ediam B ≤ ENNReal.ofReal ρ) :
    hausdorffContent (s + 1) (Icc a b ×ˢ B) ≤ ENNReal.ofReal ((b - a) * ρ ^ s + ρ ^ (s + 1)) := by
  set N : ℕ := ⌊(b - a) / ρ⌋₊ + 1 with hN
  have hcov : Icc a b ×ˢ B ⊆
      ⋃ k ∈ Finset.range N, Icc (a + (k : ℝ) * ρ) (a + ((k : ℝ) + 1) * ρ) ×ˢ B := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 (Icc_subset_biUnion_Icc_range hρ hx)
    exact mem_iUnion₂.2 ⟨k, hk, hxk, hy⟩
  have hdiam : ∀ k : ℕ,
      ediam (Icc (a + (k : ℝ) * ρ) (a + ((k : ℝ) + 1) * ρ) ×ˢ B) ≤ ENNReal.ofReal ρ := by
    intro k
    have hk : a + ((k : ℝ) + 1) * ρ = (a + (k : ℝ) * ρ) + ρ := by ring
    rw [hk]
    exact ediam_Icc_prod_le hB
  have hs1 : 0 ≤ s + 1 := by linarith
  have hNle : (N : ℝ) ≤ (b - a) / ρ + 1 := by
    rw [hN, Nat.cast_add, Nat.cast_one]
    exact add_le_add_left (Nat.floor_le (div_nonneg (sub_nonneg.2 hab) hρ.le)) 1
  have hreal : (N : ℝ) * ρ ^ (s + 1) ≤ (b - a) * ρ ^ s + ρ ^ (s + 1) := by
    have hρs : ρ ^ (s + 1) = ρ ^ s * ρ := Real.rpow_add_one hρ.ne' s
    have hpos : 0 ≤ ρ ^ (s + 1) := Real.rpow_nonneg hρ.le _
    calc (N : ℝ) * ρ ^ (s + 1) ≤ ((b - a) / ρ + 1) * ρ ^ (s + 1) :=
          mul_le_mul_of_nonneg_right hNle hpos
      _ = (b - a) * ρ ^ s + ρ ^ (s + 1) := by
          rw [add_mul, one_mul, hρs]
          field_simp
  calc hausdorffContent (s + 1) (Icc a b ×ˢ B)
      ≤ ∑ k ∈ Finset.range N,
          hausdorffContent (s + 1) (Icc (a + (k : ℝ) * ρ) (a + ((k : ℝ) + 1) * ρ) ×ˢ B) :=
        (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal ρ ^ (s + 1) :=
        Finset.sum_le_sum fun k _ => (hausdorffContent_le_ediam_rpow _ _).trans
          (ENNReal.rpow_le_rpow (hdiam k) hs1)
    _ = ENNReal.ofReal ((N : ℝ) * ρ ^ (s + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_rpow_of_pos hρ]
    _ ≤ ENNReal.ofReal ((b - a) * ρ ^ s + ρ ^ (s + 1)) := ENNReal.ofReal_le_ofReal hreal

/-- A product of an interval with a set of zero diameter has zero `(s + 1)`-content. -/
theorem hausdorffContent_Icc_prod_eq_zero_of_ediam_eq_zero {s : ℝ} (hs : 0 < s) {a b : ℝ}
    (hab : a ≤ b) {B : Set Y} (hB : ediam B = 0) :
    hausdorffContent (s + 1) (Icc a b ×ˢ B) = 0 := by
  have hcont : Continuous fun ρ : ℝ => ENNReal.ofReal ((b - a) * ρ ^ s + ρ ^ (s + 1)) :=
    ENNReal.continuous_ofReal.comp ((continuous_const.mul (Real.continuous_rpow_const hs.le)).add
      (Real.continuous_rpow_const (by linarith)))
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal ((b - a) * ρ ^ s + ρ ^ (s + 1))) (𝓝[>] 0)
      (𝓝 0) := by
    have h0 := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [Real.zero_rpow hs.ne', Real.zero_rpow (by linarith), mul_zero, add_zero,
      ENNReal.ofReal_zero] at h0
  refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  exact hausdorffContent_Icc_prod_le hs.le hab hρ (by rw [hB]; exact zero_le)

/-- For `diam B ≤ 1`: `ℋ^{s+1}_∞ ([a, b] × B) ≤ (b - a + 1) (diam B) ^ s`. -/
theorem hausdorffContent_Icc_prod_le_ediam_rpow {s : ℝ} (hs : 0 < s) {a b : ℝ} (hab : a ≤ b)
    {B : Set Y} (hB : ediam B ≤ 1) :
    hausdorffContent (s + 1) (Icc a b ×ˢ B) ≤ ENNReal.ofReal (b - a + 1) * ediam B ^ s := by
  rcases eq_or_ne (ediam B) 0 with h0 | h0
  · rw [hausdorffContent_Icc_prod_eq_zero_of_ediam_eq_zero hs hab h0]
    exact zero_le
  have hfin : ediam B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hB
  set ρ := (ediam B).toReal with hρ
  have hρeq : ENNReal.ofReal ρ = ediam B := ENNReal.ofReal_toReal hfin
  have hρpos : 0 < ρ := ENNReal.toReal_pos h0 hfin
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hB
  have hreal : (b - a) * ρ ^ s + ρ ^ (s + 1) ≤ (b - a + 1) * ρ ^ s := by
    have hρs : ρ ^ (s + 1) = ρ ^ s * ρ := Real.rpow_add_one hρpos.ne' s
    have hpow : 0 ≤ ρ ^ s := Real.rpow_nonneg hρpos.le s
    rw [hρs]
    nlinarith
  calc hausdorffContent (s + 1) (Icc a b ×ˢ B)
      ≤ ENNReal.ofReal ((b - a) * ρ ^ s + ρ ^ (s + 1)) :=
        hausdorffContent_Icc_prod_le hs.le hab hρpos hρeq.ge
    _ ≤ ENNReal.ofReal ((b - a + 1) * ρ ^ s) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (b - a + 1) * ediam B ^ s := by
        rw [ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_rpow_of_pos hρpos, hρeq]

/-- If `A` has zero `s`-content (`s > 0`), then `[a, b] × A` has zero `(s + 1)`-content. -/
theorem hausdorffContent_Icc_prod_eq_zero {s : ℝ} (hs : 0 < s) (a b : ℝ) {A : Set Y}
    (hA : hausdorffContent s A = 0) :
    hausdorffContent (s + 1) (Icc a b ×ˢ A) = 0 := by
  rcases lt_or_ge b a with hba | hab
  · rw [Icc_eq_empty_of_lt hba, empty_prod, measure_empty]
  set M : ℝ≥0∞ := ENNReal.ofReal (b - a + 1) with hM
  have hbound : ∀ η : ℝ≥0∞, 0 < η → η < 1 → hausdorffContent (s + 1) (Icc a b ×ˢ A) ≤ M * η := by
    intro η hη0 hη1
    obtain ⟨t, hAt, hsum⟩ := exists_cover_of_hausdorffContent_lt (hA.trans_lt hη0)
    have hpiece : ∀ n, hausdorffContent (s + 1) (Icc a b ×ˢ t n) ≤
        M * ⨆ _ : (t n).Nonempty, ediam (t n) ^ s := by
      intro n
      rcases (t n).eq_empty_or_nonempty with he | hne
      · rw [he, prod_empty, measure_empty]
        exact zero_le
      rw [iSup_pos hne]
      have hcost : ediam (t n) ^ s < 1 :=
        calc ediam (t n) ^ s = ⨆ _ : (t n).Nonempty, ediam (t n) ^ s := by rw [iSup_pos hne]
          _ ≤ ∑' k, ⨆ _ : (t k).Nonempty, ediam (t k) ^ s :=
            ENNReal.le_tsum (f := fun k => ⨆ _ : (t k).Nonempty, ediam (t k) ^ s) n
          _ < η := hsum
          _ < 1 := hη1
      have hdiam : ediam (t n) ≤ 1 := by
        by_contra hgt
        exact (ENNReal.one_le_rpow (not_le.1 hgt).le hs).not_gt hcost
      exact hausdorffContent_Icc_prod_le_ediam_rpow hs hab hdiam
    calc hausdorffContent (s + 1) (Icc a b ×ˢ A)
        ≤ hausdorffContent (s + 1) (⋃ n, Icc a b ×ˢ t n) := by
          refine measure_mono ?_
          rintro ⟨x, y⟩ ⟨hx, hy⟩
          obtain ⟨n, hn⟩ := mem_iUnion.1 (hAt hy)
          exact mem_iUnion.2 ⟨n, hx, hn⟩
      _ ≤ ∑' n, hausdorffContent (s + 1) (Icc a b ×ˢ t n) := measure_iUnion_le _
      _ ≤ ∑' n, M * ⨆ _ : (t n).Nonempty, ediam (t n) ^ s := ENNReal.tsum_le_tsum hpiece
      _ = M * ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ s := ENNReal.tsum_mul_left
      _ ≤ M * η := mul_le_mul_right hsum.le _
  have hlim : Tendsto (fun η : ℝ≥0∞ => M * η) (𝓝[>] 0) (𝓝 (M * 0)) :=
    ENNReal.Tendsto.const_mul (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ≥0∞)] with η hη hη'
  exact hbound η hη hη'.2

/-- **Product with an interval raises the Hausdorff dimension by at most one.** -/
theorem dimH_Icc_prod_le (a b : ℝ) (A : Set Y) : dimH (Icc a b ×ˢ A) ≤ dimH A + 1 := by
  borelize Y (ℝ × Y)
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rcases eq_or_ne c ⊤ with rfl | hctop
  · exact le_top
  have hc1 : dimH A < c - 1 := (ENNReal.cancel_of_ne ENNReal.one_ne_top).lt_tsub_iff_right.2 hc
  obtain ⟨d, hAd, hdc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc1
  have hdpos : 0 < (d : ℝ) := by
    have : (0 : ℝ≥0∞) < d := lt_of_le_of_lt (zero_le) hAd
    exact_mod_cast this
  have hA0 : μH[(d : ℝ)] A = 0 := hausdorffMeasure_of_dimH_lt hAd
  rw [hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero d.coe_nonneg] at hA0
  have hP0 : μH[((d + 1 : ℝ≥0) : ℝ)] (Icc a b ×ˢ A) = 0 := by
    rw [NNReal.coe_add, NNReal.coe_one,
      hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero (by positivity)]
    exact hausdorffContent_Icc_prod_eq_zero hdpos a b hA0
  calc dimH (Icc a b ×ˢ A) ≤ ((d + 1 : ℝ≥0) : ℝ≥0∞) :=
        dimH_le_of_hausdorffMeasure_ne_top (by rw [hP0]; exact ENNReal.zero_ne_top)
    _ = (d : ℝ≥0∞) + 1 := by rw [ENNReal.coe_add, ENNReal.coe_one]
    _ ≤ c - 1 + 1 := add_le_add_left hdc.le 1
    _ ≤ c := by rw [tsub_add_cancel_of_le (le_trans (by simp) hc.le)]

end Product

/-! ### (e) Truncated cones over subsets of the unit sphere -/

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Every slice `t ∩ sphere 0 τ` costs at most the cost of `t`, and nothing unless `τ` is a norm
of a point of `t` (the norms of `t` are enlarged to a measurable set). -/
theorem hausdorffContent_inter_sphere_le_indicator (s : ℝ) (t : Set E) (τ : ℝ) :
    hausdorffContent s (t ∩ sphere 0 τ) ≤
      (toMeasurable volume (norm '' t)).indicator (fun _ => ⨆ _ : t.Nonempty, ediam t ^ s) τ := by
  by_cases hτ : τ ∈ toMeasurable volume (norm '' t)
  · rw [indicator_of_mem hτ]
    exact (measure_mono inter_subset_left).trans (hausdorffContent_le_iSup_nonempty s t)
  · rw [indicator_of_notMem hτ]
    have hempty : t ∩ sphere 0 τ = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => hτ ?_
      refine subset_toMeasurable volume _ ⟨y, hy.1, ?_⟩
      exact mem_sphere_zero_iff_norm.1 hy.2
    rw [hempty, measure_empty]

/-- Radial contraction by `τ⁻¹ ≤ 1` does not increase the content. -/
theorem hausdorffContent_inv_smul_image_le {s : ℝ} (hs : 0 ≤ s) {τ : ℝ} (hτ : 1 ≤ τ)
    (B : Set E) :
    hausdorffContent s ((fun y => τ⁻¹ • y) '' B) ≤ hausdorffContent s B := by
  have hle := hausdorffContent_image_le_of_lipschitzWith (lipschitzWith_smul τ⁻¹) hs B
  have hnorm : (‖τ⁻¹‖₊ : ℝ≥0∞) ≤ 1 := by
    rw [ENNReal.coe_le_one_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, norm_inv,
      Real.norm_of_nonneg (zero_le_one.trans hτ)]
    exact inv_le_one_of_one_le₀ hτ
  calc hausdorffContent s ((fun y => τ⁻¹ • y) '' B)
      ≤ (‖τ⁻¹‖₊ : ℝ≥0∞) ^ s * hausdorffContent s B := hle
    _ ≤ 1 * hausdorffContent s B := mul_le_mul_left (ENNReal.rpow_le_one hnorm hs) _
    _ = hausdorffContent s B := one_mul _

/-- The slice-wise covering estimate behind the cone lower bound. -/
theorem hausdorffContent_le_tsum_indicator {s : ℝ} (hs : 0 ≤ s) {A : Set E}
    (hA : A ⊆ sphere 0 1) {t : ℕ → Set E}
    (ht : (fun p : ℝ × E => p.1 • p.2) '' (Icc (1 : ℝ) 2 ×ˢ A) ⊆ ⋃ n, t n) {τ : ℝ}
    (hτ : τ ∈ Icc (1 : ℝ) 2) :
    hausdorffContent s A ≤ ∑' n,
      (toMeasurable volume (norm '' t n)).indicator
        (fun _ => ⨆ _ : (t n).Nonempty, ediam (t n) ^ s) τ := by
  have hτ0 : τ ≠ 0 := (zero_lt_one.trans_le hτ.1).ne'
  have hcover : A ⊆ ⋃ n, (fun y => τ⁻¹ • y) '' (t n ∩ sphere 0 τ) := by
    intro θ hθ
    have hmem : τ • θ ∈ (fun p : ℝ × E => p.1 • p.2) '' (Icc (1 : ℝ) 2 ×ˢ A) :=
      ⟨(τ, θ), ⟨hτ, hθ⟩, rfl⟩
    obtain ⟨n, hn⟩ := mem_iUnion.1 (ht hmem)
    have hnorm : ‖τ • θ‖ = τ := by
      rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hτ.1),
        mem_sphere_zero_iff_norm.1 (hA hθ), mul_one]
    refine mem_iUnion.2 ⟨n, τ • θ, ⟨hn, mem_sphere_zero_iff_norm.2 hnorm⟩, ?_⟩
    exact inv_smul_smul₀ hτ0 θ
  calc hausdorffContent s A
      ≤ hausdorffContent s (⋃ n, (fun y => τ⁻¹ • y) '' (t n ∩ sphere 0 τ)) := measure_mono hcover
    _ ≤ ∑' n, hausdorffContent s ((fun y => τ⁻¹ • y) '' (t n ∩ sphere 0 τ)) :=
        measure_iUnion_le _
    _ ≤ ∑' n, hausdorffContent s (t n ∩ sphere 0 τ) :=
        ENNReal.tsum_le_tsum fun n => hausdorffContent_inv_smul_image_le hs hτ.1 _
    _ ≤ _ := ENNReal.tsum_le_tsum fun n => hausdorffContent_inter_sphere_le_indicator s (t n) τ

/-- **Cone lower bound.** For `A` on the unit sphere and `s ≥ 0`,
`ℋ^s_∞ A ≤ ℋ^{s+1}_∞ {t • θ : 1 ≤ t ≤ 2, θ ∈ A}`. The proof slices the truncated cone by the
spheres of radius `τ ∈ [1, 2]`, projects each slice radially to `A`, and integrates in `τ`; a
covering set `t` meets only spheres with radii in a set of length at most `diam t`. -/
theorem hausdorffContent_le_hausdorffContent_cone {s : ℝ} (hs : 0 ≤ s) {A : Set E}
    (hA : A ⊆ sphere 0 1) :
    hausdorffContent s A ≤
      hausdorffContent (s + 1) ((fun p : ℝ × E => p.1 • p.2) '' (Icc (1 : ℝ) 2 ×ˢ A)) := by
  rw [hausdorffContent_apply (s + 1)]
  refine le_iInf₂ fun t ht => ?_
  set I : ℕ → Set ℝ := fun n => toMeasurable volume (norm '' t n) with hI
  set c : ℕ → ℝ≥0∞ := fun n => ⨆ _ : (t n).Nonempty, ediam (t n) ^ s with hc
  have hvol : volume (Icc (1 : ℝ) 2) = 1 := by
    rw [Real.volume_Icc]
    norm_num
  have hmeas : ∀ n, AEMeasurable (fun τ => (I n).indicator (fun _ => c n) τ)
      (volume.restrict (Icc (1 : ℝ) 2)) := fun n =>
    (measurable_const.indicator (measurableSet_toMeasurable _ _)).aemeasurable
  have hpiece : ∀ n, c n * volume (I n) ≤ ⨆ _ : (t n).Nonempty, ediam (t n) ^ (s + 1) := by
    intro n
    rcases (t n).eq_empty_or_nonempty with he | hne
    · have hc0 : c n = 0 := by simp [hc, he]
      rw [hc0, zero_mul]
      exact zero_le
    · rw [iSup_pos hne, ENNReal.rpow_add_of_nonneg _ _ hs zero_le_one, ENNReal.rpow_one]
      have hcn : c n = ediam (t n) ^ s := by simp [hc, iSup_pos hne]
      rw [hcn]
      refine mul_le_mul_right ?_ _
      calc volume (I n) = volume (norm '' t n) := measure_toMeasurable _
        _ ≤ ediam (norm '' t n) := Real.volume_le_diam _
        _ ≤ (1 : ℝ≥0) * ediam (t n) := lipschitzWith_one_norm.ediam_image_le _
        _ = ediam (t n) := by rw [ENNReal.coe_one, one_mul]
  calc hausdorffContent s A = ∫⁻ _ in Icc (1 : ℝ) 2, hausdorffContent s A := by
        rw [setLIntegral_const, hvol, mul_one]
    _ ≤ ∫⁻ τ in Icc (1 : ℝ) 2, ∑' n, (I n).indicator (fun _ => c n) τ :=
        setLIntegral_mono' measurableSet_Icc fun τ hτ =>
          hausdorffContent_le_tsum_indicator hs hA ht hτ
    _ = ∑' n, ∫⁻ τ in Icc (1 : ℝ) 2, (I n).indicator (fun _ => c n) τ := lintegral_tsum hmeas
    _ = ∑' n, c n * volume.restrict (Icc (1 : ℝ) 2) (I n) := by
        congr 1
        funext n
        exact lintegral_indicator_const (measurableSet_toMeasurable _ _) _
    _ ≤ ∑' n, c n * volume (I n) :=
        ENNReal.tsum_le_tsum fun n => mul_le_mul_right (Measure.restrict_apply_le _ _) _
    _ ≤ ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (s + 1) := ENNReal.tsum_le_tsum hpiece

/-- **Cone lower bound for Hausdorff measures.** If `A` lies on the unit sphere and
`μH[s] A ≠ 0`, then the truncated cone `{t • θ : 1 ≤ t ≤ 2, θ ∈ A}` has nonzero
`μH[s + 1]`-measure. -/
theorem hausdorffMeasure_cone_ne_zero [MeasurableSpace E] [BorelSpace E] {s : ℝ} (hs : 0 ≤ s)
    {A : Set E} (hA : A ⊆ sphere 0 1) (hAs : μH[s] A ≠ 0) :
    μH[s + 1] ((fun p : ℝ × E => p.1 • p.2) '' (Icc (1 : ℝ) 2 ×ˢ A)) ≠ 0 := by
  rw [hausdorffMeasure_ne_zero_iff_hausdorffContent_ne_zero (by linarith)]
  rw [hausdorffMeasure_ne_zero_iff_hausdorffContent_ne_zero hs] at hAs
  exact fun h => hAs (le_antisymm ((hausdorffContent_le_hausdorffContent_cone hs hA).trans h.le)
    bot_le)

/-- **Dimension of a truncated cone.** For a nonempty `A` on the unit sphere,
`dimH A + 1 ≤ dimH {t • θ : 1 ≤ t ≤ 2, θ ∈ A}`. -/
theorem dimH_add_one_le_dimH_cone {A : Set E} (hA : A ⊆ sphere 0 1) (hne : A.Nonempty) :
    dimH A + 1 ≤ dimH ((fun p : ℝ × E => p.1 • p.2) '' (Icc (1 : ℝ) 2 ×ˢ A)) := by
  borelize E
  set C := (fun p : ℝ × E => p.1 • p.2) '' (Icc (1 : ℝ) 2 ×ˢ A) with hC
  have key : ∀ d : ℝ≥0, μH[(d : ℝ)] A ≠ 0 → (d : ℝ≥0∞) + 1 ≤ dimH C := by
    intro d hd
    have h1 : μH[((d + 1 : ℝ≥0) : ℝ)] C ≠ 0 := by
      rw [NNReal.coe_add, NNReal.coe_one]
      exact hausdorffMeasure_cone_ne_zero d.coe_nonneg hA hd
    have h2 := le_dimH_of_hausdorffMeasure_ne_zero h1
    rwa [ENNReal.coe_add, ENNReal.coe_one] at h2
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  by_cases hr1 : r ≤ 1
  · have h0 : μH[((0 : ℝ≥0) : ℝ)] A ≠ 0 := by
      rw [NNReal.coe_zero]
      exact (zero_lt_one.trans_le (Measure.one_le_hausdorffMeasure_zero_of_nonempty hne)).ne'
    calc (r : ℝ≥0∞) ≤ 1 := by exact_mod_cast hr1
      _ = ((0 : ℝ≥0) : ℝ≥0∞) + 1 := by simp
      _ ≤ dimH C := key 0 h0
  · push Not at hr1
    have hd : ((r - 1 : ℝ≥0) : ℝ≥0∞) < dimH A := by
      rw [ENNReal.coe_sub, ENNReal.coe_one]
      exact ENNReal.sub_lt_of_lt_add (by exact_mod_cast hr1.le) hr
    have hμ : μH[((r - 1 : ℝ≥0) : ℝ)] A ≠ 0 := by
      rw [hausdorffMeasure_of_lt_dimH hd]
      exact ENNReal.top_ne_zero
    calc (r : ℝ≥0∞) = ((r - 1 : ℝ≥0) : ℝ≥0∞) + 1 := by
          rw [← ENNReal.coe_one, ← ENNReal.coe_add, tsub_add_cancel_of_le hr1.le]
      _ ≤ dimH C := key (r - 1) hμ

/-- The radial map `(t, θ) ↦ t • θ` is `3`-Lipschitz on `[1, 2] × A` for `A` in the unit ball. -/
theorem lipschitzOnWith_smul_Icc_prod {A : Set E} (hA : A ⊆ closedBall 0 1) :
    LipschitzOnWith 3 (fun p : ℝ × E => p.1 • p.2) (Icc (1 : ℝ) 2 ×ˢ A) := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have hθ : ‖p.2‖ ≤ 1 := mem_closedBall_zero_iff.1 (hA hp.2)
  have ht' : |q.1| ≤ 2 := by
    rw [abs_of_nonneg (by linarith [hq.1.1])]
    exact hq.1.2
  have h1 : |p.1 - q.1| ≤ dist p q := by
    rw [← Real.dist_eq, Prod.dist_eq]
    exact le_max_left _ _
  have h2 : ‖p.2 - q.2‖ ≤ dist p q := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_right _ _
  have hd : 0 ≤ dist p q := dist_nonneg
  calc dist (p.1 • p.2) (q.1 • q.2) = ‖(p.1 - q.1) • p.2 + q.1 • (p.2 - q.2)‖ := by
        rw [dist_eq_norm, sub_smul, smul_sub]
        congr 1
        abel
    _ ≤ ‖(p.1 - q.1) • p.2‖ + ‖q.1 • (p.2 - q.2)‖ := norm_add_le _ _
    _ = |p.1 - q.1| * ‖p.2‖ + |q.1| * ‖p.2 - q.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ dist p q * 1 + 2 * dist p q := by
        gcongr
    _ = ((3 : ℝ≥0) : ℝ) * dist p q := by
        push_cast
        ring

/-- **Upper bound for truncated cones**: `dimH {t • θ : 1 ≤ t ≤ 2, θ ∈ A} ≤ dimH A + 1` for `A`
in the closed unit ball. -/
theorem dimH_cone_le {A : Set E} (hA : A ⊆ closedBall 0 1) :
    dimH ((fun p : ℝ × E => p.1 • p.2) '' (Icc (1 : ℝ) 2 ×ˢ A)) ≤ dimH A + 1 :=
  (lipschitzOnWith_smul_Icc_prod hA).dimH_image_le.trans (dimH_Icc_prod_le 1 2 A)

/-- **Dimension of a truncated cone over a subset of the sphere**:
`dimH {t • θ : 1 ≤ t ≤ 2, θ ∈ A} = dimH A + 1` for nonempty `A ⊆ sphere 0 1`. -/
theorem dimH_cone_eq {A : Set E} (hA : A ⊆ sphere 0 1) (hne : A.Nonempty) :
    dimH ((fun p : ℝ × E => p.1 • p.2) '' (Icc (1 : ℝ) 2 ×ˢ A)) = dimH A + 1 :=
  le_antisymm (dimH_cone_le (hA.trans sphere_subset_closedBall))
    (dimH_add_one_le_dimH_cone hA hne)

end Cone

end SerrinEpigraph
