module

public import SerrinEpigraph.PhysicalTranslationGradient
public import SerrinEpigraph.PhysicalTranslationClearing
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# The actual positive phase of a physical translation limit

Clearing passes to the limit. Together with the sharp Lipschitz bound this
gives holes in the zero phase near every point of the positive-phase closure.
Lebesgue density then excludes a positive-volume limiting free boundary.
-/

public section

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- Physical translation limits inherit the small-amplitude clearing theorem
with constants independent of the sequence of centers. -/
theorem RigidityHypotheses.exists_physical_limit_clearing_constants
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ a R₀ : ℝ, 0 < a ∧ 0 < R₀ ∧
      ∀ (p : ℕ → Space (m + 1)) (V : Space (m + 1) → ℝ),
      (∀ K : Set (Space (m + 1)), IsCompact K →
        TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K) →
      ∀ c R, 0 < R → R ≤ R₀ → (∀ x ∈ ball c R, V x ≤ a * R) →
        EqOn V 0 (ball c (R / 2)) := by
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_phase_clearing_constants h
  refine ⟨a / 2, R₀, half_pos ha, hR₀, fun p V hlim c R hR hRR hsmall x hx ↦ ?_⟩
  have hevent : ∀ᶠ j in atTop, zeroExtension g u (p j + x) = 0 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (hlim (closedBall c R) (isCompact_closedBall _ _)) (a * R / 2) (by positivity)] with j hj
    have hsmallj : ∀ y ∈ ball (p j + c) R, zeroExtension g u y ≤ a * R := by
      intro y hy
      have hyd : dist (y - p j) c = dist y (p j + c) := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      have hyc : y - p j ∈ ball c R := by simpa only [mem_ball, hyd] using hy
      have hh := hj (y - p j) (ball_subset_closedBall hyc)
      have he : p j + (y - p j) = y := by abel
      rw [he, Real.dist_eq] at hh
      have hlow := (abs_lt.mp hh).1
      linarith [hsmall _ hyc]
    exact hclear (p j + c) R hR hRR hsmallj (by simpa only [mem_ball, dist_add_left] using hx)
  have ht := (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hevent.mono (fun _ hj ↦ hj.symm)))

/-- The inherited clearing estimate gives linear growth in every small ball
centered in the actual closure of the positive phase. -/
theorem exists_positive_value_of_clearing {d : ℕ} {V : Space d → ℝ} {a R₀ : ℝ}
    (hclear : ∀ c R, 0 < R → R ≤ R₀ → (∀ x ∈ ball c R, V x ≤ a * R) →
      EqOn V 0 (ball c (R / 2)))
    {c : Space d} (hc : c ∈ closure {x | 0 < V x}) {R : ℝ} (hR : 0 < R) (hRR : R ≤ R₀) :
    ∃ y ∈ ball c R, a * R < V y := by
  by_contra hn
  push Not at hn
  have hz := hclear c R hR hRR hn
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc (R / 2) (half_pos hR)
  have hyball : y ∈ ball c (R / 2) := by
    simpa only [mem_ball, dist_comm] using hdist
  have he := hz hyball
  change V y = 0 at he
  exact hy.ne' he

/-- A set cannot have density points with uniformly sized nearby holes.
Using moving-center differentiation avoids any boundary-area formula. -/
theorem ae_notMem_of_closedBall_holes {d : ℕ} {S T : Set (Space d)} {c R₀ : ℝ}
    (hc : 0 < c) (hR₀ : 0 < R₀)
    (hholes : ∀ x ∈ T, ∀ R : ℝ, 0 < R → R ≤ R₀ →
      ∃ y, dist x y ≤ R ∧ Disjoint S (closedBall y (c * R))) :
    ∀ᵐ x ∂volume.restrict S, x ∉ T := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
    (volume : Measure (Space d)) S (1 / c)] with x hx
  intro hxT
  let R : ℕ → ℝ := fun j ↦ R₀ * (1 / (j + 1 : ℝ))
  have hRpos (j : ℕ) : 0 < R j := by dsimp only [R]; positivity
  have hRle (j : ℕ) : R j ≤ R₀ := by
    apply mul_le_of_le_one_right hR₀.le
    exact (div_le_one (by positivity)).mpr (by have hn := Nat.cast_nonneg (α := ℝ) j; linarith)
  choose y hy hdisj using fun j ↦ hholes x hxT (R j) (hRpos j) (hRle j)
  have hRt : Tendsto R atTop (𝓝 0) := by
    simpa only [mul_zero] using
      tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδt : Tendsto (fun j ↦ c * R j) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [mul_zero] using tendsto_const_nhds.mul hRt,
      Eventually.of_forall (fun j ↦ mul_pos hc (hRpos j))⟩
  have hmem : ∀ᶠ j in atTop, x ∈ closedBall (y j) (1 / c * (c * R j)) := by
    filter_upwards with j
    change dist x (y j) ≤ 1 / c * (c * R j)
    simpa only [one_div, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hy j
  have ht := hx y (fun j ↦ c * R j) hδt hmem
  have hz : ∀ j, volume (S ∩ closedBall (y j) (c * R j)) /
      volume (closedBall (y j) (c * R j)) = 0 := by
    intro j
    simp only [Set.disjoint_iff_inter_eq_empty.mp (hdisj j), measure_empty, ENNReal.zero_div]
  simp only [hz] at ht
  have he : (0 : ENNReal) = 1 := tendsto_nhds_unique tendsto_const_nhds ht
  exact zero_ne_one he

/-- Linear growth and a Lipschitz bound force almost every zero point to lie
outside the closure of the positive phase. In particular the free boundary
has zero ambient volume. -/
theorem ae_zero_outside_closure_positive_of_clearing
    {d : ℕ} {V : Space d → ℝ} {L : NNReal} (hV : LipschitzWith L V)
    {a R₀ : ℝ} (ha : 0 < a) (hR₀ : 0 < R₀)
    (hclear : ∀ c R, 0 < R → R ≤ R₀ → (∀ x ∈ ball c R, V x ≤ a * R) →
      EqOn V 0 (ball c (R / 2))) :
    ∀ᵐ x, V x = 0 → x ∉ closure {y | 0 < V y} := by
  let c := a / (2 * ((L : ℝ) + 1))
  have hc : 0 < c := div_pos ha (by positivity)
  have hLc : (L : ℝ) * c < a := by
    have he : c * (2 * ((L : ℝ) + 1)) = a := div_mul_cancel₀ a (by positivity)
    nlinarith [L.coe_nonneg]
  have hholes : ∀ x ∈ closure {y | 0 < V y}, ∀ R : ℝ, 0 < R → R ≤ R₀ →
      ∃ y, dist x y ≤ R ∧ Disjoint {z | V z = 0} (closedBall y (c * R)) := by
    intro x hx R hR hRR
    obtain ⟨y, hy, hval⟩ := exists_positive_value_of_clearing hclear hx hR hRR
    refine ⟨y, by simpa only [dist_comm] using (show dist y x < R from hy).le, ?_⟩
    apply disjoint_left.mpr
    intro z hz hzb
    have hd := hV.dist_le_mul z y
    rw [Real.dist_eq] at hd
    have hlower := (abs_le.mp hd).1
    have hdist := mul_le_mul_of_nonneg_left hzb L.coe_nonneg
    have hstrict := mul_lt_mul_of_pos_right hLc hR
    change V z = 0 at hz
    nlinarith
  have hnot := ae_notMem_of_closedBall_holes hc hR₀ hholes
  exact (ae_restrict_iff' (isClosed_eq hV.continuous continuous_const).measurableSet).mp hnot

/-- A physical translation limit has no positive-volume limiting free boundary. -/
theorem RigidityHypotheses.physical_translation_limit_ae_zero_outside_phase_closure
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K) :
    ∀ᵐ x, V x = 0 → x ∉ closure {y | 0 < V y} := by
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_physical_limit_clearing_constants h
  exact ae_zero_outside_closure_positive_of_clearing hV ha hR₀ (hclear p V hlim)

/-- Outside the limiting positive-phase closure, the original physical
translates are eventually exactly zero at each point. -/
theorem RigidityHypotheses.physical_translation_eventually_zero
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : ∀ x, 0 ≤ V x)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {x : Space (m + 1)} (hx : x ∉ closure {y | 0 < V y}) :
    ∀ᶠ j in atTop, zeroExtension g u (p j + x) = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isClosed_closure.isOpen_compl.mem_nhds hx)
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_phase_clearing_constants h
  let R := min R₀ (ε / 2)
  have hR : 0 < R := lt_min hR₀ (half_pos hε)
  have hRε : R < ε := (min_le_right R₀ (ε / 2)).trans_lt (half_lt_self hε)
  have hz (y : Space (m + 1)) (hy : y ∈ closedBall x R) : V y = 0 := by
    have hnot := hball (show y ∈ ball x ε from hy.trans_lt hRε)
    exact le_antisymm (le_of_not_gt (fun hp ↦ hnot (subset_closure hp))) (hV y)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (hlim (closedBall x R) (isCompact_closedBall _ _)) (a * R) (mul_pos ha hR)] with j hj
  have hsmall : ∀ y ∈ ball (p j + x) R, zeroExtension g u y ≤ a * R := by
    intro y hy
    have hyd : dist (y - p j) x = dist y (p j + x) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    have hyc : y - p j ∈ closedBall x R := by
      rw [mem_closedBall, hyd]
      exact (show dist y (p j + x) < R from hy).le
    have hh := hj (y - p j) hyc
    have he : p j + (y - p j) = y := by abel
    rw [he, hz _ hyc, dist_zero_left] at hh
    exact (le_abs_self _).trans hh.le
  exact hclear (p j + x) R hR (min_le_left _ _) hsmall (mem_ball_self (half_pos hR))

/-- The positive phases converge pointwise almost everywhere, with eventual
agreement of membership at each point outside a null set. -/
theorem RigidityHypotheses.physical_translation_phase_eventually_iff
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K) :
    ∀ᵐ x, ∀ᶠ j in atTop, (0 < zeroExtension g u (p j + x) ↔ 0 < V x) := by
  filter_upwards [hr.physical_translation_limit_ae_zero_outside_phase_closure h hV hlim]
    with x hx
  by_cases hp : 0 < V x
  · have ht := (hlim {x} isCompact_singleton).tendsto_at (mem_singleton x)
    filter_upwards [ht (Ioi_mem_nhds hp)] with j hj
    exact iff_of_true hj hp
  · have hz : V x = 0 := le_antisymm (le_of_not_gt hp) (hval x).1
    filter_upwards [hr.physical_translation_eventually_zero h (fun y ↦ (hval y).1) hlim (hx hz)]
      with j hj
    simp only [hj, hz, lt_self_iff_false]

end SerrinEpigraph
