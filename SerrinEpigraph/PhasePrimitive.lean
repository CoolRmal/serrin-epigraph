module

public import SerrinEpigraph.WeightedGradient

/-!
# The potential-weighted phase primitive
-/

public section

open MeasureTheory
open scoped Topology

namespace SerrinEpigraph

noncomputable section

/-- Primitive whose spatial gradient is controlled by the phase energy. -/
@[expose] def phasePrimitive (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in 0..s, Real.sqrt (2 * normalizedPotential f t)

@[simp]
theorem phasePrimitive_zero (f : ℝ → ℝ) : phasePrimitive f 0 = 0 := by
  simp [phasePrimitive]

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The phase primitive has the expected derivative at every interior solution value. -/
theorem Hypotheses.phasePrimitive_hasDerivAt (h : Hypotheses g u f κ)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (phasePrimitive f) (Real.sqrt (2 * normalizedPotential f s)) s := by
  have hc : ContinuousOn (fun t ↦ Real.sqrt (2 * normalizedPotential f t)) (Set.Icc 0 1) :=
    (continuousOn_const.mul h.normalizedPotential_continuousOn).sqrt
  have hi : IntervalIntegrable (fun t ↦ Real.sqrt (2 * normalizedPotential f t)) volume 0 s :=
    (hc.mono (Set.Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc hs.1.le
  have hc' := hc.mono Set.Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hc'.stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hc'.continuousAt (isOpen_Ioo.mem_nhds hs))

/-- The two equilibrium phases have distinct primitive values. -/
theorem RigidityHypotheses.phasePrimitive_one_pos
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    0 < phasePrimitive f 1 := by
  have hc : ContinuousOn (fun t ↦ Real.sqrt (2 * normalizedPotential f t)) (Set.Icc 0 1) :=
    (continuousOn_const.mul h.normalizedPotential_continuousOn).sqrt
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (hc.intervalIntegrable_of_Icc zero_le_one) _ zero_lt_one
  intro t ht
  exact Real.sqrt_pos.mpr (mul_pos (by norm_num) (hr.normalizedPotential_pos h ht.1.le ht.2))

end

end SerrinEpigraph
