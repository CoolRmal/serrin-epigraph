module

public import SerrinEpigraph.RadialSlopeBound

/-!
# Energy control for increasing radial segments away from the origin

These are estimates for solutions of the radial equation. Existence of an
annular comparison solution is a separate obligation.
-/

public section

open Set

namespace SerrinEpigraph

/-- An increasing radial solution segment, starting from zero at a positive inner radius. -/
structure IncreasingRadialSegment (f : ℝ → ℝ) (m : ℕ) (a b : ℝ) where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  inner_pos : 0 < a
  radii_lt : a < b
  value_continuous : ContinuousOn value (Icc a b)
  slope_continuous : ContinuousOn slope (Icc a b)
  value_range : ∀ r ∈ Icc a b, value r ∈ Icc 0 1
  value_pos : ∀ r ∈ Ioo a b, 0 < value r
  slope_nonneg : ∀ r ∈ Icc a b, 0 ≤ slope r
  value_derivative : ∀ r ∈ Ioo a b, HasDerivAt value (slope r) r
  slope_derivative : ∀ r ∈ Ioo a b,
    HasDerivAt slope (-f (value r) - (m : ℝ) / r * slope r) r
  inner_zero : value a = 0

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ a b : ℝ}

/-- An increasing normalized radial solution has decreasing slope. -/
theorem IncreasingRadialSegment.slope_antitoneOn (v : IncreasingRadialSegment f m a b)
    (hr : RigidityHypotheses g u f) : AntitoneOn v.slope (Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) v.slope_continuous
    (f' := fun r ↦ -f (v.value r) - (m : ℝ) / r * v.slope r)
  · intro r hri
    have hri' : r ∈ Ioo a b := by simpa only [interior_Icc] using hri
    exact (v.slope_derivative r hri').hasDerivWithinAt
  · intro r hri
    have hri' : r ∈ Ioo a b := by simpa only [interior_Icc] using hri
    have hc : r ∈ Icc a b := ⟨hri'.1.le, hri'.2.le⟩
    have hf0 : 0 ≤ f (v.value r) := by
      by_cases he : v.value r = 1
      · simp [he, hr.reaction_one]
      · exact (hr.reaction_pos _ ⟨v.value_pos r hri',
          lt_of_le_of_ne (v.value_range r hc).2 he⟩).le
    have hp := mul_nonneg (div_nonneg (Nat.cast_nonneg m)
      (v.inner_pos.le.trans hri'.1.le)) (v.slope_nonneg r hc)
    linarith

/-- Curvature loss along an increasing radial segment is bounded by its value increase. -/
theorem IncreasingRadialSegment.energy_loss_le (v : IncreasingRadialSegment f m a b)
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {r : ℝ}
    (hrange : r ∈ Icc a b) :
    radialEnergy f v.value v.slope a - radialEnergy f v.value v.slope r ≤
      (m : ℝ) / a * v.slope a * v.value r := by
  let C := (m : ℝ) / a * v.slope a
  have hEc : ContinuousOn (radialEnergy f v.value v.slope) (Icc a b) :=
    ((v.slope_continuous.pow 2).div_const 2).sub
      (h.normalizedPotential_continuousOn.comp v.value_continuous v.value_range)
  have hm : MonotoneOn (fun t ↦ radialEnergy f v.value v.slope t + C * v.value t)
      (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (hEc.add (v.value_continuous.const_mul C))
      (f' := fun t ↦ -(m : ℝ) / t * v.slope t ^ 2 + C * v.slope t)
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      exact ((h.radialEnergy_hasDerivAt (v.value_derivative t ht')
        (v.slope_derivative t ht') (v.value_pos t ht')).add
        ((v.value_derivative t ht').const_mul C)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      have htc : t ∈ Icc a b := ⟨ht'.1.le, ht'.2.le⟩
      have hp := v.slope_nonneg t htc
      have hpa := v.slope_antitoneOn hr ⟨le_rfl, v.radii_lt.le⟩ htc ht'.1.le
      have hs : v.slope t ^ 2 ≤ v.slope a * v.slope t := by nlinarith
      have hk : (m : ℝ) / t ≤ (m : ℝ) / a :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg m) v.inner_pos ht'.1.le
      have he := mul_le_mul hk hs (sq_nonneg _)
        (div_nonneg (Nat.cast_nonneg m) v.inner_pos.le)
      dsimp only [C]
      rw [neg_div]
      nlinarith
  have he := hm ⟨le_rfl, v.radii_lt.le⟩ hrange hrange.1
  simp only [v.inner_zero, mul_zero, add_zero] at he
  dsimp only [C] at he
  linarith

/-- A positive initial energy margin survives whenever the inner radius makes curvature small. -/
theorem IncreasingRadialSegment.slope_sq_lower_bound
    (v : IncreasingRadialSegment f m a b) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {r : ℝ} (hrange : r ∈ Icc a b) :
    v.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * v.slope a) ≤ v.slope r ^ 2 := by
  have he := v.energy_loss_le hr h hrange
  have hW := hr.normalizedPotential_nonneg h (v.value_range r hrange)
  have hC : 0 ≤ (m : ℝ) / a * v.slope a :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg m) v.inner_pos.le)
      (v.slope_nonneg a ⟨le_rfl, v.radii_lt.le⟩)
  have hval := mul_le_mul_of_nonneg_left (v.value_range r hrange).2 hC
  simp only [radialEnergy, v.inner_zero] at he
  nlinarith

/-- A fixed positive energy margin gives a uniform bound on the length of an increasing segment. -/
theorem IncreasingRadialSegment.width_le
    (v : IncreasingRadialSegment f m a b) (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : δ ^ 2 ≤ v.slope a ^ 2 - 2 * normalizedPotential f 0 -
      2 * ((m : ℝ) / a * v.slope a)) : b - a ≤ 1 / δ := by
  obtain ⟨r, hri, he⟩ := exists_hasDerivAt_eq_slope v.value v.slope v.radii_lt
    v.value_continuous v.value_derivative
  have hrc : r ∈ Icc a b := ⟨hri.1.le, hri.2.le⟩
  have hsq := hmargin.trans (v.slope_sq_lower_bound hr h hrc)
  have hp : δ ≤ v.slope r := by nlinarith [v.slope_nonneg r hrc]
  rw [v.inner_zero, sub_zero] at he
  have hval := (v.value_range b ⟨v.radii_lt.le, le_rfl⟩).2
  have hmul : δ * (b - a) ≤ v.value b := by
    rw [he] at hp
    exact (le_div_iff₀ (sub_pos.mpr v.radii_lt)).mp hp
  apply (le_div_iff₀ hδ).mpr
  nlinarith

end SerrinEpigraph
