module

public import SerrinEpigraph.ClosedLipschitzMinimality

/-!
# Cutoff gluing of admissible competitors
-/

public section

open Set MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- Replace the reference by a candidate where the cutoff is one, retaining it where zero. -/
@[expose] noncomputable def gluedCompetitor {d : ℕ} (U v η : Space d → ℝ) (x : Space d) : ℝ :=
  U x + η x * (v x - U x)

/-- Cutoff gluing preserves local Lipschitz regularity. -/
theorem gluedCompetitor_locallyLipschitz {d : ℕ} {U v η : Space d → ℝ}
    (hU : LocallyLipschitz U) (hv : LocallyLipschitz v) (hη : LocallyLipschitz η) :
    LocallyLipschitz (gluedCompetitor U v η) := by
  have hm : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ z.1 * z.2) := by fun_prop
  exact hU.add (hm.locallyLipschitz.comp (hη.prodMk (hv.sub hU)))

/-- Convex gluing preserves the closed normalized range. -/
theorem gluedCompetitor_mem_Icc {d : ℕ} {U v η : Space d → ℝ}
    (hU : ∀ x, U x ∈ Icc (0 : ℝ) 1) (hv : ∀ x, v x ∈ Icc (0 : ℝ) 1)
    (hη : ∀ x, η x ∈ Icc (0 : ℝ) 1) (x : Space d) :
    gluedCompetitor U v η x ∈ Icc (0 : ℝ) 1 := by
  have he : gluedCompetitor U v η x = (1 - η x) * U x + η x * v x := by
    unfold gluedCompetitor
    ring
  rw [he]
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hη x).2) (hU x).1)
      (mul_nonneg (hη x).1 (hv x).1)
  · nlinarith [mul_nonneg (sub_nonneg.mpr (hη x).2) (sub_nonneg.mpr (hU x).2),
      mul_nonneg (hη x).1 (sub_nonneg.mpr (hv x).2)]

/-- Gluing leaves the reference unchanged where the cutoff vanishes. -/
theorem gluedCompetitor_eq_reference {d : ℕ} (U v η : Space d → ℝ)
    {x : Space d} (hx : η x = 0) : gluedCompetitor U v η x = U x := by
  simp [gluedCompetitor, hx]

/-- Gluing agrees with the candidate where the cutoff equals one. -/
theorem gluedCompetitor_eq_candidate {d : ℕ} (U v η : Space d → ℝ)
    {x : Space d} (hx : η x = 1) : gluedCompetitor U v η x = v x := by
  simp [gluedCompetitor, hx]

/-- The perturbation is confined to the cutoff support. -/
theorem gluedCompetitor_tsupport_sub_subset {d : ℕ} (U v η : Space d → ℝ) :
    tsupport (fun x ↦ gluedCompetitor U v η x - U x) ⊆ tsupport η := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.notMem_support] at hx ⊢
  simp [gluedCompetitor, hx]

/-- The gradient formula isolates the cost of the transition cutoff. -/
theorem gradient_gluedCompetitor {d : ℕ} {U v η : Space d → ℝ} {x : Space d}
    (hU : DifferentiableAt ℝ U x) (hv : DifferentiableAt ℝ v x)
    (hη : DifferentiableAt ℝ η x) :
    gradient (gluedCompetitor U v η) x = gradient U x +
      (η x • (gradient v x - gradient U x) + (v x - U x) • gradient η x) := by
  unfold gluedCompetitor gradient
  rw [fderiv_fun_add hU (hη.fun_mul (hv.fun_sub hU)), fderiv_fun_mul hη (hv.fun_sub hU), fderiv_fun_sub hv hU]
  simp only [map_add, map_smul, map_sub]

/-- The gradient cost of gluing is the convex gradient cost plus the cutoff error. -/
theorem norm_gradient_gluedCompetitor_le {d : ℕ} {U v η : Space d → ℝ} {x : Space d}
    (hU : DifferentiableAt ℝ U x) (hv : DifferentiableAt ℝ v x)
    (hη : DifferentiableAt ℝ η x) (hval : η x ∈ Icc (0 : ℝ) 1) :
    ‖gradient (gluedCompetitor U v η) x‖ ≤
      (1 - η x) * ‖gradient U x‖ + η x * ‖gradient v x‖ +
        ‖v x - U x‖ * ‖gradient η x‖ := by
  have he : gradient (gluedCompetitor U v η) x =
      ((1 - η x) • gradient U x + η x • gradient v x) +
        (v x - U x) • gradient η x := by
    rw [gradient_gluedCompetitor hU hv hη]
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(1 - η x) • gradient U x + η x • gradient v x‖ +
        ‖(v x - U x) • gradient η x‖ := norm_add_le _ _
    _ ≤ (‖(1 - η x) • gradient U x‖ + ‖η x • gradient v x‖) +
        ‖(v x - U x) • gradient η x‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by
      rw [norm_smul, norm_smul, norm_smul,
        Real.norm_of_nonneg (sub_nonneg.mpr hval.2), Real.norm_of_nonneg hval.1]

/-- The glued normalized competitor is admissible in the proved phase-energy comparison. -/
theorem RigidityHypotheses.phaseEnergy_le_gluedCompetitor
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {v η : Space (m + 1) → ℝ} (hv : LocallyLipschitz v) (hη : LocallyLipschitz η)
    (hvval : ∀ x, v x ∈ Icc (0 : ℝ) 1) (hηval : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    {K : Set (Space (m + 1))} (hK : IsCompact K) (hs : tsupport η ⊆ K) :
    (∫ x in K, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
      ∫ x in K, phaseEnergyDensity f 0 (gluedCompetitor (zeroExtension g u) v η) x := by
  apply hr.phaseEnergy_minimal_lipschitz_closedRange h
    (gluedCompetitor_locallyLipschitz h.zeroExtension_locallyLipschitz hv hη) hK
    ((gluedCompetitor_tsupport_sub_subset _ _ _).trans hs)
  exact gluedCompetitor_mem_Icc
    (fun x ↦ ⟨h.zeroExtension_nonneg x, (hr.zeroExtension_lt_one x).le⟩) hvval hηval

end SerrinEpigraph
