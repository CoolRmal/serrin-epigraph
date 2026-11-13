module

public import SerrinEpigraph.RadialContinuation

/-!
# Strict decrease of radial initial value solutions
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-- Positive reaction makes the weighted radial flux strictly decreasing from the center. -/
theorem RigidityHypotheses.radial_flux_strictAntiOn (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {R : ℝ}
    (hPc : ContinuousOn P (Icc 0 R)) (hQP : IsRadialSystemOn m f Q P (Ioo 0 R))
    (hval : ∀ t ∈ Ioo (0 : ℝ) R, Q t ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (fun t ↦ t ^ m * P t) (Icc 0 R) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc (0 : ℝ) R)
    ((continuousOn_id.pow m).mul hPc) (f' := fun t ↦ -(t ^ m * f (Q t)))
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using ht
    exact (h.radialFlux_hasDerivAt ht'.1 (hQP t ht').2).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using ht
    exact neg_neg_of_pos (mul_pos (pow_pos ht'.1 m) (hr.reaction_pos _ (hval t ht')))

/-- A regular central slope is strictly negative at every subsequent positive radius. -/
theorem RigidityHypotheses.radial_slope_neg (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {R t : ℝ}
    (hPc : ContinuousOn P (Icc 0 R)) (hQP : IsRadialSystemOn m f Q P (Ioo 0 R))
    (hval : ∀ s ∈ Ioo (0 : ℝ) R, Q s ∈ Ioo (0 : ℝ) 1) (hP0 : P 0 = 0)
    (ht : t ∈ Ioc (0 : ℝ) R) : P t < 0 := by
  have he := hr.radial_flux_strictAntiOn h hPc hQP hval
    ⟨le_rfl, ht.1.le.trans ht.2⟩ ⟨ht.1.le, ht.2⟩ ht.1
  simp only [hP0, mul_zero] at he
  exact neg_of_mul_neg_right he (pow_nonneg ht.1.le m)

/-- Radial values strictly decrease before any prescribed boundary value is imposed. -/
theorem RigidityHypotheses.radial_value_strictAntiOn (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {R : ℝ}
    (hQc : ContinuousOn Q (Icc 0 R)) (hPc : ContinuousOn P (Icc 0 R))
    (hQP : IsRadialSystemOn m f Q P (Ioo 0 R))
    (hval : ∀ t ∈ Ioo (0 : ℝ) R, Q t ∈ Ioo (0 : ℝ) 1) (hP0 : P 0 = 0) :
    StrictAntiOn Q (Icc 0 R) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc (0 : ℝ) R) hQc (f' := P)
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using ht
    exact (hQP t ht').1.hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using ht
    exact hr.radial_slope_neg h hPc hQP hval hP0 ⟨ht'.1, ht'.2.le⟩

/-- The local central construction yields a strictly decreasing positive radial profile. -/
theorem RigidityHypotheses.exists_decreasing_local_radial_system
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ Q P : ℝ → ℝ,
      Continuous Q ∧ ContinuousOn P (Icc 0 R) ∧ Q 0 = a ∧ P 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) R, Q t ∈ Ioo (0 : ℝ) 1) ∧
      IsRadialSystemOn m f Q P (Ioo 0 R) ∧ StrictAntiOn Q (Icc 0 R) ∧
      (∀ t ∈ Ioc (0 : ℝ) R, P t < 0) := by
  obtain ⟨R, hR, Q, P, hQc, hPc, hQ0, hP0, hval, hQd, hPd⟩ :=
    h.exists_local_radial_system ha
  have hQP : IsRadialSystemOn m f Q P (Ioo 0 R) :=
    fun t ht ↦ ⟨hQd t ⟨ht.1.le, ht.2.le⟩, hPd t ht⟩
  have hvali : ∀ t ∈ Ioo (0 : ℝ) R, Q t ∈ Ioo (0 : ℝ) 1 :=
    fun t ht ↦ hval t ⟨ht.1.le, ht.2.le⟩
  exact ⟨R, hR, Q, P, hQc, hPc, hQ0, hP0, hval, hQP,
    hr.radial_value_strictAntiOn h hQc.continuousOn hPc hQP hvali hP0,
    fun t ht ↦ hr.radial_slope_neg h hPc hQP hvali hP0 ht⟩

/-- Strict decrease persists on a half-open interval of positive normalized radial values. -/
theorem RigidityHypotheses.radial_value_strictAntiOn_Ico
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {Q P : ℝ → ℝ} {R : ℝ}
    (hQc : ContinuousOn Q (Ico 0 R)) (hPc : ContinuousOn P (Ico 0 R))
    (hQP : IsRadialSystemOn m f Q P (Ioo 0 R))
    (hval : ∀ t ∈ Ioo (0 : ℝ) R, Q t ∈ Ioo (0 : ℝ) 1) (hP0 : P 0 = 0) :
    StrictAntiOn Q (Ico 0 R) := by
  intro x hx y hy hxy
  have hsub : Icc (0 : ℝ) y ⊆ Ico 0 R := fun _ ht ↦ ⟨ht.1, ht.2.trans_lt hy.2⟩
  have hsubi : Ioo (0 : ℝ) y ⊆ Ioo 0 R := fun _ ht ↦ ⟨ht.1, ht.2.trans hy.2⟩
  exact hr.radial_value_strictAntiOn h (hQc.mono hsub) (hPc.mono hsub)
    (hQP.mono hsubi) (fun t ht ↦ hval t (hsubi ht)) hP0
    ⟨hx.1, hxy.le⟩ ⟨hy.1, le_rfl⟩ hxy

/-- A finite endpoint value is strictly smaller than the central value. -/
theorem radial_endpoint_lt_center {Q : ℝ → ℝ} {R b : ℝ} (hR : 0 < R)
    (hQ : StrictAntiOn Q (Ico 0 R))
    (hb : Filter.Tendsto Q (𝓝[<] R) (𝓝 b)) : b < Q 0 := by
  have hhalf : R / 2 ∈ Ico (0 : ℝ) R := ⟨by positivity, by linarith⟩
  have hlt := hQ ⟨le_rfl, hR⟩ hhalf (by positivity : 0 < R / 2)
  have hle : b ≤ Q (R / 2) := by
    apply le_of_tendsto hb
    filter_upwards [Ioo_mem_nhdsLT (by linarith : R / 2 < R)] with t ht
    exact (hQ hhalf ⟨by linarith [ht.1], ht.2⟩ ht.1).le
  exact hle.trans_lt hlt

end SerrinEpigraph
