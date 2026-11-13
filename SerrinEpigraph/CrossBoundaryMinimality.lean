module

public import SerrinEpigraph.PerturbedCalibration
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Energy comparison for compact smooth perturbations across the free boundary

The additive energy constant is retained explicitly. Competitors may change
positive phase and take values in the half-closed normalized range.
-/

public section
noncomputable section

open MeasureTheory Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- The totalized gradient of a real-valued function is measurable. -/
theorem measurable_gradient {d : ℕ} (v : Space d → ℝ) : Measurable (gradient v) :=
  (toDual ℝ (Space d)).symm.continuous.measurable.comp (measurable_fderiv ℝ v)

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- Smooth perturbations of the zero extension have locally integrable squared gradients. -/
theorem Hypotheses.integrableOn_perturbed_gradient_sq (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ ‖gradient (fun y ↦ zeroExtension g u y + φ y) x‖ ^ 2) K := by
  have hGφ : Continuous (gradient φ) :=
    (toDual ℝ (Space (m + 1))).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hiφ := (hGφ.norm.pow 2).continuousOn.integrableOn_compact (μ := volume) hK
  have hi := ((h.integrableOn_norm_gradient_zeroExtension_sq hK).add hiφ).const_mul 2
  apply hi.mono' ((measurable_gradient _).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_of_ae h.zeroExtension_ae_differentiableAt] with x hx
  have hg := gradient_affine_variation hx (hφ.differentiable_one x) 1
  simp only [one_mul, one_smul] at hg
  rw [Real.norm_of_nonneg (sq_nonneg _), hg]
  have hn := norm_add_le (gradient (zeroExtension g u) x) (gradient φ x)
  have hnn := norm_nonneg (gradient (zeroExtension g u) x + gradient φ x)
  dsimp only [Pi.add_apply, Pi.pow_apply]
  nlinarith [sq_nonneg (‖gradient (zeroExtension g u) x‖ - ‖gradient φ x‖)]

/-- The perturbed gradient is integrable on every compact set. -/
theorem Hypotheses.integrableOn_perturbed_gradient (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (gradient (fun y ↦ zeroExtension g u y + φ y)) K := by
  have hc : IntegrableOn (fun _ : Space (m + 1) ↦ (1 : ℝ)) K :=
    continuousOn_const.integrableOn_compact hK
  apply ((h.integrableOn_perturbed_gradient_sq hφ hK).add hc).mono'
    (measurable_gradient _).aestronglyMeasurable
  filter_upwards with x
  have hs := sq_nonneg (‖gradient (fun y ↦ zeroExtension g u y + φ y) x‖ - 1 / 2)
  dsimp only [Pi.add_apply]
  nlinarith

/-- The phase energy of a normalized smooth perturbation is locally integrable. -/
theorem Hypotheses.integrableOn_perturbed_phaseEnergy (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Icc (0 : ℝ) 1) (c : ℝ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (phaseEnergyDensity f c (fun y ↦ zeroExtension g u y + φ y)) K := by
  have hv := h.zeroExtension_continuous.add hφ.continuous
  have hW : Continuous (fun x ↦ normalizedPotential f (zeroExtension g u x + φ x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hv hval
  have hi := (((h.integrableOn_perturbed_gradient_sq hφ hK).div_const 2).add
    (hW.continuousOn.integrableOn_compact hK)).add
      (continuousOn_const.integrableOn_compact (μ := volume) hK (f := fun _ ↦ c))
  exact hi.indicator (isOpen_lt continuous_const hv).measurableSet

/-- The closed calibration density of a perturbed zero extension is locally integrable. -/
theorem RigidityHypotheses.integrableOn_perturbed_calibration
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) :
    IntegrableOn (fun x ↦ hr.boundaryCalibratedDensity h (horizontal x)
      (zeroExtension g u x + φ x) (gradient (fun y ↦ zeroExtension g u y + φ y) x)) K := by
  let v := fun x ↦ zeroExtension g u x + φ x
  let B := fun x ↦ hr.closedLevelGradient h (horizontal x, v x)
  have hv : Continuous v := h.zeroExtension_continuous.add hφ.continuous
  have hB : Continuous B := (hr.closedLevelGradient_continuousOn h).comp_continuous
    (continuous_horizontal.prodMk hv) hval
  have hG := h.integrableOn_perturbed_gradient hφ hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hB.continuousOn
  have hi : IntegrableOn (fun x ↦ inner ℝ (B x) (gradient v x)) K := by
    apply (hG.norm.const_mul M).mono'
      (hB.measurable.inner (measurable_gradient v)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _))
  have hW : Continuous (fun x ↦ normalizedPotential f (v x)) :=
    h.normalizedPotential_continuousOn.comp_continuous hv
      (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩)
  exact ((hi.sub (((hB.norm.pow 2).div_const 2).continuousOn.integrableOn_compact hK)).add
    (hW.continuousOn.integrableOn_compact hK)).add
      (continuousOn_const.integrableOn_compact (μ := volume) hK)

/-- The zero extension minimizes the shifted phase energy against compact C¹ perturbations
valued in [0,1), including perturbations that cross the original boundary. -/
theorem RigidityHypotheses.phaseEnergy_minimal_compact_perturbation
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : HasCompactSupport φ)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ R : ℝ, tsupport φ ⊆ closedBall 0 R ∧
      (∫ x in closedBall 0 R,
        phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0) (zeroExtension g u) x) ≤
      ∫ x in closedBall 0 R, phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0)
        (fun y ↦ zeroExtension g u y + φ y) x := by
  obtain ⟨R, hR, he⟩ := hr.perturbed_calibration_eq_energy h hφ hsupp hval
  refine ⟨R, hR, ?_⟩
  rw [← he]
  apply integral_mono
    (hr.integrableOn_perturbed_calibration h hφ hval (isCompact_closedBall 0 R))
    (h.integrableOn_perturbed_phaseEnergy hφ (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩) _
      (isCompact_closedBall 0 R))
  exact hr.boundaryCalibratedDensity_le_phaseEnergy h (fun x ↦ (hval x).1)

/-- Outside the topological support of a perturbation, its phase energy agrees with the original. -/
theorem phaseEnergy_add_eq_of_notMem_tsupport {d : ℕ} (f : ℝ → ℝ) (c : ℝ)
    {v φ : Space d → ℝ} {x : Space d} (hx : x ∉ tsupport φ) :
    phaseEnergyDensity f c (fun y ↦ v y + φ y) x = phaseEnergyDensity f c v x := by
  have hz := notMem_tsupport_iff_eventuallyEq.mp hx
  have he : (fun y ↦ v y + φ y) =ᶠ[𝓝 x] v := by
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply, hy, add_zero]
  simp only [phaseEnergyDensity, Set.indicator_apply, Set.mem_ofPred_eq, he.self_of_nhds, he.gradient_eq]

/-- The shifted phase-energy comparison holds on every compact set containing the perturbation
support, with no requirement that the set lie inside the original epigraph. -/
theorem RigidityHypotheses.phaseEnergy_minimal_on_compact
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : ContDiff ℝ 1 φ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1) :
    (∫ x in K, phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0)
      (zeroExtension g u) x) ≤
      ∫ x in K, phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0)
        (fun y ↦ zeroExtension g u y + φ y) x := by
  have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hsupp
  obtain ⟨R, hR, hle⟩ := hr.phaseEnergy_minimal_compact_perturbation h hφ hφc hval
  let c := κ ^ 2 / 2 - normalizedPotential f 0
  let D := fun x ↦ phaseEnergyDensity f c (fun y ↦ zeroExtension g u y + φ y) x -
    phaseEnergyDensity f c (zeroExtension g u) x
  have hz (x : Space (m + 1)) (hx : x ∉ tsupport φ) : D x = 0 := by
    dsimp only [D]
    rw [phaseEnergy_add_eq_of_notMem_tsupport f c hx, sub_self]
  have heK : (∫ x in K, D x) = ∫ x, D x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hz x (fun hp ↦ hx (hsupp hp)))
  have heR : (∫ x in closedBall 0 R, D x) = ∫ x, D x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hz x (fun hp ↦ hx (hR hp)))
  have hiP {S : Set (Space (m + 1))} (hS : IsCompact S) :=
    h.integrableOn_perturbed_phaseEnergy hφ (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩) c hS
  have hiU {S : Set (Space (m + 1))} (hS : IsCompact S) :=
    hr.integrableOn_phaseEnergy_zeroExtension h c hS
  have hp : 0 ≤ ∫ x in closedBall 0 R, D x := by
    dsimp only [D]
    rw [integral_sub (hiP (isCompact_closedBall 0 R)) (hiU (isCompact_closedBall 0 R))]
    exact sub_nonneg.mpr hle
  rw [heR, ← heK] at hp
  dsimp only [D] at hp
  rw [integral_sub (hiP hK) (hiU hK)] at hp
  exact sub_nonneg.mp hp

end SerrinEpigraph
