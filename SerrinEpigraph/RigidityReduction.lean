module

public import SerrinEpigraph.MinimizingConicalPhase
public import SerrinEpigraph.LocalPerimeterMinimizer
public import SerrinEpigraph.MovingPhaseCompactness
public import SerrinEpigraph.NoncylindricalPhase
public import SerrinEpigraph.TranslationOrderBall
public import SerrinEpigraph.CylinderTiltDecay

/-!
# Reduction of the two rigidity targets to three geometric statements

This module isolates the remaining mathematical content of the two rigidity theorems.

* `IsDirectedMinimizingCone.halfspace_or_verticalInvariant` (blueprint `one-sided.md` §5A,
  `low-dimensional.md` G0–G2): a nontrivial, conical, vertically monotone local perimeter
  minimizer is a half-space or is invariant under all vertical translations.
* `IsDirectedMinimizingCone.halfspace_of_verticalInvariant_le_eight` (blueprint GR6, GR16):
  in ambient dimension at most eight such a vertical cylinder is a half-space.
* `RigidityHypotheses.hasCylinderTiltDecay_of_sharp_energy` (blueprint
  `harmonic-approximation.md` HA0–HA11): under the all-center sharp energy bound, the
  rescaled cylinder tilt at free-boundary centers decays by the HA0 factor. HA12
  (`CylinderTiltDecay`) turns this into ball-tilt improvement, and `CoarseConeAssembly`
  (sharp density, compactness, kinetic bounds, iteration, common normal and DS1) then gives
  the uniform boundary coarse cone from one half-space blow-down limit
  (`RigidityHypotheses.exists_uniformBoundaryCoarseCone_of_halfspace_limit`).

The reductions proved here are complete; the three statements above are the open proof
obligations, recorded as explicit proof holes until their modules are finished.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- A nontrivial, conical, vertically monotone local perimeter minimizer in `Space (m + 1)`. -/
structure IsDirectedMinimizingCone {m : ℕ} (E : Set (Space (m + 1))) : Prop where
  measurableSet : MeasurableSet E
  nontrivial : volume E ≠ 0 ∧ volume Eᶜ ≠ 0
  dilation : ∀ a : ℝ, 0 < a → ∀ᵐ x ∂volume, x ∈ E ↔ a • x ∈ E
  vertical : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂volume, x ∈ E → x + t • verticalDirection m ∈ E
  minimizer : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E univ

/-- The open half-space with inner normal `e`. -/
def positiveHalfspace {d : ℕ} (e : Space d) : Set (Space d) := {x | 0 < inner ℝ e x}

/-- **Open obligation (cone dichotomy).** A nontrivial, conical, vertically monotone local
perimeter minimizer is a.e. a half-space, or is a.e. invariant under every vertical
translation. -/
theorem IsDirectedMinimizingCone.halfspace_or_verticalInvariant {m : ℕ}
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E) :
    (∃ e : Space (m + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e) ∨
      (∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) := by
  sorry

/-- **Open obligation (low-dimensional cylinders).** In ambient dimension at most eight, a
vertically invariant directed minimizing cone is a.e. a half-space. -/
theorem IsDirectedMinimizingCone.halfspace_of_verticalInvariant_le_eight {m : ℕ}
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E) (hdim : m + 1 ≤ 8)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) :
    ∃ e : Space (m + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e := by
  sorry

/-- **Open obligation (tilt-excess decay, blueprint HA0–HA11).** Under the sharp
surface-energy bound at every center and radius, the rescaled cylinder tilt of the zero
extension at free-boundary centers decays by the HA0 factor. -/
theorem RigidityHypotheses.hasCylinderTiltDecay_of_sharp_energy
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    HasCylinderTiltDecay g u := by
  sorry

/-- Ball-tilt improvement at free-boundary centers (blueprint HA12 applied to HA0). -/
theorem RigidityHypotheses.hasBallTiltImprovement_of_sharp_energy
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    HasBallTiltImprovement (zeroExtension g u) (frontier (epigraph g)) :=
  h.hasBallTiltImprovement_of_cylinderTiltDecay (hr.hasCylinderTiltDecay_of_sharp_energy h hsharp)

/-- One half-space blow-down limit of the zero extension gives a uniform boundary coarse
cone (blueprint `sharp-density.md`, `harmonic-approximation.md`,
`iteration-and-directions.md`, DS1). -/
theorem RigidityHypotheses.exists_uniformBoundaryCoarseCone_of_halfspace_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {e : Space (m + 1)} (he : ‖e‖ = 1)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        (positiveHalfspace e).indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) :
    ∃ e' : Space (m + 1), ‖e'‖ = 1 ∧ HasUniformBoundaryCoarseCone g e' :=
  hr.exists_uniformBoundaryCoarseCone_of_halfspace_limit_of_tiltImprovement h hR hRt he hlocal
    (hr.hasBallTiltImprovement_of_sharp_energy h
      (fun z _ρ hρ ↦ hr.phaseEnergy_le_planar_mass_of_halfspace_limit h hR hRt he hlocal z hρ))

/-- The common limiting phase of the original solution is a directed minimizing cone. -/
theorem RigidityHypotheses.exists_directedMinimizingCone_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧ Tendsto R atTop atTop ∧
      ∃ E : Set (Space (m + 1)), IsDirectedMinimizingCone E ∧
        (∀ K : Set (Space (m + 1)), IsCompact K →
          Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
            E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0)) ∧
        (HasOneSidedLinearBound g →
          (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
            x ∈ E → -C * ‖horizontal x‖ ≤ x (Fin.last m)) ∨
          (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂volume,
            C * ‖horizontal x‖ < x (Fin.last m) → x ∈ E)) := by
  obtain ⟨R, hR, hRt, E, hE, hlocal, hnontriv, hdil, hperim, hvert, hmin, hside, -, -⟩ :=
    hr.exists_minimizing_conical_phase h
  let b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hPE (n : ℕ) : variationalPerimeter b E (ball 0 ((n : ℝ) + 1)) ≠ ⊤ := by
    obtain ⟨C, -, hC⟩ := hperim
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC n b)
  refine ⟨R, hR, hRt, E, ⟨hE, hnontriv, hdil, hvert, ?_⟩, hlocal, hside⟩
  refine isLocalPerimeterMinimizer_univ b hE hPE ?_
  intro U D K hU hD hK hKU hED
  exact perimeter_open_minimality_of_concentric_ball_comparison b hE hD hPE
    (fun s r hs hrs hagree ↦ hmin b s r hs hrs D hD hagree) hK hU hKU hED

/-- Local `L¹` convergence to a phase transfers to any a.e. equal phase. -/
theorem tendsto_local_indicator_of_ae_eq {m : ℕ} {U : ℕ → Space (m + 1) → ℝ}
    {E H : Set (Space (m + 1))} (hEH : E =ᵐ[volume] H)
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖U j x - E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    (K : Set (Space (m + 1))) (hK : IsCompact K) :
    Tendsto (fun j ↦ ∫ x in K, ‖U j x - H.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0) := by
  have hind : E.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[volume] H.indicator (fun _ ↦ (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hEH
  refine (hlocal K hK).congr fun j ↦ ?_
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hind] with x hx
  rw [hx]

/-- Once the common limiting phase is a half-space, the solution is affine and
one-dimensional. -/
theorem RigidityHypotheses.isAffineOneDimensional_of_halfspace_limit
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    {R : ℕ → ℝ} (hR : ∀ j, 1 ≤ R j) (hRt : Tendsto R atTop atTop)
    {E : Set (Space (m + 1))}
    (hlocal : ∀ K : Set (Space (m + 1)), IsCompact K →
      Tendsto (fun j ↦ ∫ x in K, ‖zeroExtension g u (R j • x) -
        E.indicator (fun _ ↦ (1 : ℝ)) x‖) atTop (𝓝 0))
    {e : Space (m + 1)} (he : ‖e‖ = 1) (hEH : E =ᵐ[volume] positiveHalfspace e) :
    IsAffineOneDimensional g u := by
  obtain ⟨e', he', hcone⟩ := hr.exists_uniformBoundaryCoarseCone_of_halfspace_limit h hR hRt he
    (tendsto_local_indicator_of_ae_eq hEH hlocal)
  exact hr.isAffineOneDimensional_of_uniformBoundaryCoarseCone h he' hcone

/-- Rigidity in ambient dimension at most eight, reduced to the three open obligations. -/
theorem RigidityHypotheses.isAffineOneDimensional_of_le_eight
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) (hdim : m + 1 ≤ 8) :
    IsAffineOneDimensional g u := by
  obtain ⟨R, hR, hRt, E, hE, hlocal, -⟩ := hr.exists_directedMinimizingCone_limit h
  have hhalf : ∃ e : Space (m + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e := by
    rcases hE.halfspace_or_verticalInvariant with hH | hinv
    · exact hH
    · exact hE.halfspace_of_verticalInvariant_le_eight hdim hinv
  obtain ⟨e, he, hEH⟩ := hhalf
  exact hr.isAffineOneDimensional_of_halfspace_limit h hR hRt hlocal he hEH

/-- Rigidity under a one-sided linear graph bound, reduced to the open obligations. -/
theorem RigidityHypotheses.isAffineOneDimensional_of_oneSidedLinearBound
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hg : HasOneSidedLinearBound g) :
    IsAffineOneDimensional g u := by
  obtain ⟨R, hR, hRt, E, hE, hlocal, hside⟩ := hr.exists_directedMinimizingCone_limit h
  rcases hE.halfspace_or_verticalInvariant with ⟨e, he, hEH⟩ | hinv
  · exact hr.isAffineOneDimensional_of_halfspace_limit h hR hRt hlocal he hEH
  · exact absurd hinv (not_vertical_invariant_of_nontrivial_oneSided_cone hE.nontrivial
      (hside hg))

end SerrinEpigraph
