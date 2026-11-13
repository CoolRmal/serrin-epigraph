module

public import SerrinEpigraph.LipschitzCalibration

/-!
# Energy minimality against compact locally Lipschitz perturbations
-/

public section
noncomputable section

open MeasureTheory Filter Metric InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ}
  {f : ℝ → ℝ} {κ : ℝ}

/-- The zero extension minimizes the shifted phase energy against compact locally Lipschitz perturbations
valued in [0,1), including perturbations that cross the original boundary. -/
theorem RigidityHypotheses.lipschitz_phaseEnergy_minimal_compact_perturbation
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : LocallyLipschitz φ) (hsupp : HasCompactSupport φ)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ R : ℝ, tsupport φ ⊆ closedBall 0 R ∧
      (∫ x in closedBall 0 R,
        phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0) (zeroExtension g u) x) ≤
      ∫ x in closedBall 0 R, phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0)
        (fun y ↦ zeroExtension g u y + φ y) x := by
  obtain ⟨R, hR, he⟩ := hr.lipschitz_perturbed_calibration_eq_energy h hφ hsupp hval
  refine ⟨R, hR, ?_⟩
  rw [← he]
  apply integral_mono
    (hr.integrableOn_lipschitz_calibration h (h.zeroExtension_locallyLipschitz.add hφ) hval (isCompact_closedBall 0 R))
    (h.integrableOn_lipschitz_phaseEnergy (h.zeroExtension_locallyLipschitz.add hφ) (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩) _
      (isCompact_closedBall 0 R))
  exact hr.boundaryCalibratedDensity_le_phaseEnergy h (fun x ↦ (hval x).1)

/-- The shifted phase-energy comparison holds on every compact set containing the perturbation
support, with no requirement that the set lie inside the original epigraph. -/
theorem RigidityHypotheses.lipschitz_phaseEnergy_minimal_on_compact
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {φ : Space (m + 1) → ℝ} (hφ : LocallyLipschitz φ)
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hsupp : tsupport φ ⊆ K)
    (hval : ∀ x, zeroExtension g u x + φ x ∈ Set.Ico (0 : ℝ) 1) :
    (∫ x in K, phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0)
      (zeroExtension g u) x) ≤
      ∫ x in K, phaseEnergyDensity f (κ ^ 2 / 2 - normalizedPotential f 0)
        (fun y ↦ zeroExtension g u y + φ y) x := by
  have hφc : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hsupp
  obtain ⟨R, hR, hle⟩ := hr.lipschitz_phaseEnergy_minimal_compact_perturbation h hφ hφc hval
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
    h.integrableOn_lipschitz_phaseEnergy (h.zeroExtension_locallyLipschitz.add hφ) (fun x ↦ ⟨(hval x).1, (hval x).2.le⟩) c hS
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

/-- Any locally Lipschitz competitor valued in [0,1), equal to the zero extension
outside a compact set, has no smaller unshifted phase energy on that set. -/
theorem RigidityHypotheses.phaseEnergy_minimal_lipschitz_competitor
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v : Space (m + 1) → ℝ} (hv : LocallyLipschitz v)
    {K : Set (Space (m + 1))} (hK : IsCompact K)
    (hsupp : tsupport (fun x ↦ v x - zeroExtension g u x) ⊆ K)
    (hval : ∀ x, v x ∈ Set.Ico (0 : ℝ) 1) :
    (∫ x in K, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
      ∫ x in K, phaseEnergyDensity f 0 v x := by
  have he : (fun y ↦ zeroExtension g u y + (v y - zeroExtension g u y)) = v := by
    funext y
    ring
  have hval' : ∀ x, zeroExtension g u x + (v x - zeroExtension g u x) ∈
      Set.Ico (0 : ℝ) 1 := by
    intro x
    rw [congrFun he x]
    exact hval x
  have hm := hr.lipschitz_phaseEnergy_minimal_on_compact h
    (hv.sub h.zeroExtension_locallyLipschitz) hK hsupp hval'
  simpa only [he, hr.phaseEnergy_shift_eq_zero h] using hm

end SerrinEpigraph
