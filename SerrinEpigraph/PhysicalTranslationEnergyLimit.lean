module

public import SerrinEpigraph.BoundedQuadraticConvergence

/-!
# Exact local energy convergence under physical translation
-/

public section

noncomputable section

open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The totalized gradient vanishes at every zero of a nonnegative function. -/
theorem gradient_eq_zero_of_nonneg_zero {d : ℕ} {v : Space d → ℝ}
    (hv : ∀ x, 0 ≤ v x) {x : Space d} (hx : v x = 0) : gradient v x = 0 := by
  have hmin : IsLocalMin v x := Eventually.of_forall (fun y ↦ by rw [hx]; exact hv y)
  simp only [gradient, hmin.fderiv_eq_zero, map_zero]

/-- For nonnegative functions the kinetic term already vanishes on the zero
phase; only the potential needs an explicit phase indicator. -/
theorem phaseEnergyDensity_eq_kinetic_add_potential {d : ℕ} {v : Space d → ℝ}
    (hv : ∀ x, 0 ≤ v x) (f : ℝ → ℝ) (x : Space d) :
    phaseEnergyDensity f 0 v x = ‖gradient v x‖ ^ 2 / 2 +
      {y | 0 < v y}.indicator (fun y ↦ normalizedPotential f (v y)) x := by
  by_cases hx : 0 < v x
  · simp only [phaseEnergyDensity, indicator_of_mem (s := {y | 0 < v y}) hx, add_zero]
  · have hz : v x = 0 := le_antisymm (le_of_not_gt hx) (hv x)
    simp [phaseEnergyDensity, indicator_of_notMem (s := {y | 0 < v y}) hx,
      gradient_eq_zero_of_nonneg_zero hv hz]

/-- All bounded continuous quadratic fluxes of the translated gradients
converge in local integral norm. -/
theorem RigidityHypotheses.physical_translation_quadratic_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {B : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1)}
    (hB : Continuous B) {D : ℝ} (hBD : ∀ x, ‖B x‖ ≤ D)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖inner ℝ (gradient (zeroExtension g u) (p j + x))
          (B x (gradient (zeroExtension g u) (p j + x))) -
        inner ℝ (gradient V x) (B x (gradient V x))‖) atTop (𝓝 0) := by
  apply integral_norm_quadratic_sub_tendsto
    (fun j ↦ (measurable_gradient _).comp (continuous_const.add continuous_id).measurable)
    (measurable_gradient V) hB (fun j x ↦ hr.gradient_zeroExtension_norm_le_kappa h _) ?_
    hBD hK (hr.physical_translation_gradient_integral_norm_tendsto h hV hval hlim hK)
  intro x
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hV

/-- The kinetic density converges in local integral norm. -/
theorem RigidityHypotheses.physical_translation_kinetic_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖‖gradient (zeroExtension g u) (p j + x)‖ ^ 2 - ‖gradient V x‖ ^ 2‖) atTop (𝓝 0) := by
  have ht := hr.physical_translation_quadratic_tendsto h hV hval hlim
    (B := fun _ ↦ ContinuousLinearMap.id ℝ (Space (m + 1))) continuous_const
    (fun _ ↦ ContinuousLinearMap.norm_id_le) hK
  simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using ht

/-- The complete one-phase energy density converges in local integral norm,
including its discontinuous potential term on the positive phase. -/
theorem RigidityHypotheses.physical_translation_energy_tendsto
    {m : ℕ} {g : Space m → ℝ} {u V : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {p : ℕ → Space (m + 1)} (hV : LipschitzWith ⟨κ, h.kappa_pos.le⟩ V)
    (hval : ∀ x, V x ∈ Icc 0 1)
    (hlim : ∀ K : Set (Space (m + 1)), IsCompact K →
      TendstoUniformlyOn (fun j x ↦ zeroExtension g u (p j + x)) V atTop K)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K,
      ‖phaseEnergyDensity f 0 (fun y ↦ zeroExtension g u (p j + y)) x -
        phaseEnergyDensity f 0 V x‖) atTop (𝓝 0) := by
  let U := fun j x ↦ zeroExtension g u (p j + x)
  let P := fun v : Space (m + 1) → ℝ ↦
    {y | 0 < v y}.indicator (fun y ↦ normalizedPotential f (v y))
  have hU (j : ℕ) : LocallyLipschitz (U j) :=
    h.zeroExtension_locallyLipschitz.comp (isometry_add_left (p j)).lipschitzWith.locallyLipschitz
  have hUv (j : ℕ) (x : Space (m + 1)) : U j x ∈ Icc 0 1 :=
    ⟨h.zeroExtension_nonneg _, (hr.zeroExtension_lt_one _).le⟩
  have hiP (v : Space (m + 1) → ℝ) (hv : Continuous v) (hvval : ∀ x, v x ∈ Icc 0 1) :
      IntegrableOn (P v) K :=
    ((h.normalizedPotential_continuousOn.comp_continuous hv hvval).continuousOn.integrableOn_compact
      hK).indicator (isOpen_lt continuous_const hv).measurableSet
  have htK := hr.physical_translation_kinetic_tendsto h hV hval hlim hK
  have htP := hr.physical_translation_phase_observable_tendsto h hV hval hlim
    h.normalizedPotential_continuousOn hK
  have ht := (htK.div_const 2).add htP
  simp only [zero_div, zero_add] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ ht
  intro j
  have hiE : IntegrableOn (fun x ↦ phaseEnergyDensity f 0 (U j) x - phaseEnergyDensity f 0 V x) K :=
    (h.integrableOn_lipschitz_phaseEnergy (hU j) (hUv j) 0 hK).sub
      (h.integrableOn_lipschitz_phaseEnergy hV.locallyLipschitz hval 0 hK)
  have hiK : IntegrableOn (fun x ↦ ‖gradient (U j) x‖ ^ 2 - ‖gradient V x‖ ^ 2) K :=
    (integrableOn_gradient_sq_of_locallyLipschitz (hU j) hK).sub
      (integrableOn_gradient_sq_of_locallyLipschitz hV.locallyLipschitz hK)
  have hiPdiff : IntegrableOn (fun x ↦ P (U j) x - P V x) K :=
    (hiP _ (hU j).continuous (hUv j)).sub (hiP V hV.continuous hval)
  have he : (∫ x in K, ‖phaseEnergyDensity f 0 (U j) x - phaseEnergyDensity f 0 V x‖) ≤
      ∫ x in K, ‖‖gradient (U j) x‖ ^ 2 - ‖gradient V x‖ ^ 2‖ / 2 + ‖P (U j) x - P V x‖ := by
    apply integral_mono hiE.norm ((hiK.norm.div_const 2).add hiPdiff.norm)
    intro x
    change ‖phaseEnergyDensity f 0 (U j) x - phaseEnergyDensity f 0 V x‖ ≤
      ‖‖gradient (U j) x‖ ^ 2 - ‖gradient V x‖ ^ 2‖ / 2 + ‖P (U j) x - P V x‖
    rw [phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hUv j y).1),
      phaseEnergyDensity_eq_kinetic_add_potential (fun y ↦ (hval y).1)]
    have heq : ‖gradient (U j) x‖ ^ 2 / 2 + P (U j) x -
        (‖gradient V x‖ ^ 2 / 2 + P V x) =
        (‖gradient (U j) x‖ ^ 2 - ‖gradient V x‖ ^ 2) / 2 + (P (U j) x - P V x) := by ring
    change ‖‖gradient (U j) x‖ ^ 2 / 2 + P (U j) x -
      (‖gradient V x‖ ^ 2 / 2 + P V x)‖ ≤ _
    rw [heq]
    convert norm_add_le ((‖gradient (U j) x‖ ^ 2 - ‖gradient V x‖ ^ 2) / 2)
      (P (U j) x - P V x) using 1
    simp
  rw [integral_add (hiK.norm.div_const 2) hiPdiff.norm, integral_div] at he
  simpa only [U, P, gradient, fderiv_comp_add_left] using he

end SerrinEpigraph
