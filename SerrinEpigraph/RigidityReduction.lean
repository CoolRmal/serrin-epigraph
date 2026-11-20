module

public import SerrinEpigraph.MinimizingConicalPhase
public import SerrinEpigraph.LocalPerimeterMinimizer
public import SerrinEpigraph.MovingPhaseCompactness
public import SerrinEpigraph.NoncylindricalPhase
public import SerrinEpigraph.TranslationOrderBall
public import SerrinEpigraph.CylinderTiltDecay
public import SerrinEpigraph.ConeSplitting
public import SerrinEpigraph.ConeClassificationInduction
public import SerrinEpigraph.DirectedConeDichotomy
public import SerrinEpigraph.SimonsCone
public import SerrinEpigraph.ExcessEpsilonRegularityProof
public import SerrinEpigraph.EpsilonRegularityBridge
public import SerrinEpigraph.DiffuseNormalKinetic
public import SerrinEpigraph.MinimizerGraphChart
public import SerrinEpigraph.AlignedHarmonicLayers
public import SerrinEpigraph.MinimalGraphRegularity

/-!
# Reduction of the two rigidity targets to the remaining open statements

This module isolates the remaining mathematical content of the two rigidity theorems.

* `IsDirectedMinimizingCone.halfspace_or_verticalInvariant` (blueprint `one-sided.md` §5A,
  `low-dimensional.md` G0–G2): a nontrivial, conical, vertically monotone local perimeter
  minimizer is a half-space or is invariant under all vertical translations. It is proved in
  `DirectedConeDichotomy` from the named obligations below together with
  `singularSetUSCHyp` (GR14) and `c1RegularSmoothHyp` (Schauder smoothness of `C¹` regular
  points).
* `epsilonRegularityHyp` (blueprint GR7–GR14, De Giorgi ε-regularity): a boundary point of a
  local perimeter minimizer with a half-space tangent cone is a `C¹` regular point. Proved from
  the excess form `excessEpsilonRegularityHyp` (GR8–GR13) via `EpsilonRegularityBridge`, which
  also proves `singularSetUSCHyp`.
* `simonsHyp` (blueprint GR1–GR4 with Schauder smoothness): for `2 ≤ k ≤ 7`, a minimizing cone
  in `Space k` that is `C¹`-regular away from the origin is a half-space. `SimonsCone` proves it
  for `3 ≤ k ≤ 7` from `c1RegularSmoothHyp`; the planar case `simonsHyp_two` is open.
  From these two, `ConeClassificationInduction` proves GR16 (every minimizing cone in dimension
  at most seven is a half-space), and with GR5–GR6 (`ConeSplitting`) this gives
  `IsDirectedMinimizingCone.halfspace_of_verticalInvariant_le_eight`.
* `RigidityHypotheses.hasCylinderTiltDecay_of_sharp_energy` (blueprint
  `harmonic-approximation.md` HA0–HA11; proved in `DiffuseTiltDecay`, `DiffuseHarmonicApproximation`,
  `DiffusePlanarAlignment`, `DiffuseNormalKinetic` and `AlignedHarmonicLayers` from the open
  obligation `RigidityHypotheses.exists_hasAlignedWeakHeightData`): under the all-center sharp
  energy bound, the
  rescaled cylinder tilt at free-boundary centers decays by the HA0 factor. HA12
  (`CylinderTiltDecay`) turns this into ball-tilt improvement, and `CoarseConeAssembly`
  (sharp density, compactness, kinetic bounds, iteration, common normal and DS1) then gives
  the uniform boundary coarse cone from one half-space blow-down limit
  (`RigidityHypotheses.exists_uniformBoundaryCoarseCone_of_halfspace_limit`).

The reductions proved here are complete. The only remaining proof holes are `simonsHyp_two`
(planar minimizing cones are half-planes) and `RigidityHypotheses.exists_hasAlignedWeakHeightData`
(the level-set height data HA2–HA3, HA4.1 and HA6.1 of the tilt-excess decay); every other
named obligation above is proved with only the standard axioms.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-- ε-regularity (blueprint GR7–GR14): a boundary point of a local perimeter minimizer at which
some tangent cone is a half-space is a `C¹` regular point. -/
theorem epsilonRegularityHyp : EpsilonRegularityHyp :=
  epsilonRegularityHyp_of_excess excessEpsilonRegularityHyp

/-- Singular sets (blueprint GR14): singular boundary points of local perimeter minimizers
persist under local `L¹` convergence of the minimizers. -/
theorem singularSetUSCHyp : SingularSetUSCHyp :=
  singularSetUSCHyp_of_excess excessEpsilonRegularityHyp

/-- Schauder for the minimal surface equation (`LinearSchauder`, `HolderClasses`,
`SchauderBootstrap`, `MinimalGraphRegularity`): a `C¹` weak solution of the minimal surface
equation on a ball is smooth there. -/
theorem minimalSurface_contDiffOn_top (m : ℕ) (ρ : ℝ) (φ : Space m → ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hφ : ContDiffOn ℝ 1 φ (ball 0 ρ))
    (hweak : IsWeakSolution minimalSurfaceFlux φ (ball 0 ρ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) φ (ball 0 ρ) :=
  minimalSurface_contDiffOn_top_proof m ρ φ hm hρ hφ hweak

/-- Schauder smoothness: a `C¹` regular boundary point of a local perimeter minimizer has a
smooth boundary chart (graph chart and weak minimal surface equation in
`MinimizerGraphChart`, smoothness of weak solutions from `minimalSurface_contDiffOn_top`). -/
theorem c1RegularSmoothHyp : C1RegularSmoothHyp :=
  c1RegularSmoothHyp_of_minimalSurface minimalSurface_contDiffOn_top

/-- **Open obligation (planar case of GR4).** A minimizing cone in the plane whose boundary
points other than the origin are `C¹` regular is a half-plane. -/
theorem simonsHyp_two : SimonsHyp 2 := by
  sorry

/-- Simons (blueprint GR1–GR4): for `2 ≤ k ≤ 7`, a minimizing cone in `Space k` whose boundary
points other than the origin are `C¹` regular is a half-space (proved in `SimonsCone` for
`3 ≤ k ≤ 7`, from smoothness of `C¹` regular points). -/
theorem simonsHyp {k : ℕ} (hk2 : 2 ≤ k) (hk7 : k ≤ 7) : SimonsHyp k :=
  simonsHyp_of_smooth_of_simonsHyp_two c1RegularSmoothHyp simonsHyp_two hk2 hk7

/-- The cone dichotomy (blueprint `one-sided.md` §5A): a nontrivial, conical, vertically
monotone local perimeter minimizer is a.e. a half-space, or is a.e. invariant under every
vertical translation. -/
theorem IsDirectedMinimizingCone.halfspace_or_verticalInvariant {m : ℕ}
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E) :
    (∃ e : Space (m + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e) ∨
      (∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) :=
  hE.halfspace_or_verticalInvariant_of_hyps epsilonRegularityHyp singularSetUSCHyp
    (fun _ h2 h7 ↦ simonsHyp h2 h7) c1RegularSmoothHyp

/-- GR16: every nontrivial minimizing cone in `Space k`, `k ≤ 7`, is a.e. a half-space through
the origin. -/
theorem IsMinimizingCone.ae_eq_positiveHalfspace_of_le_seven {k : ℕ} (hk : k ≤ 7)
    {T : Set (Space k)} (hT : IsMinimizingCone T) :
    ∃ e : Space k, ‖e‖ = 1 ∧ T =ᵐ[volume] positiveHalfspace e :=
  IsMinimizingCone.ae_eq_positiveHalfspace_of_le_seven_of_regularity epsilonRegularityHyp
    (fun _ h2 h7 ↦ simonsHyp h2 h7) hk hT

/-- In ambient dimension at most eight, a vertically invariant directed minimizing cone is a.e.
a half-space (blueprint GR6 and GR16). -/
theorem IsDirectedMinimizingCone.halfspace_of_verticalInvariant_le_eight {m : ℕ}
    {E : Set (Space (m + 1))} (hE : IsDirectedMinimizingCone E) (hdim : m + 1 ≤ 8)
    (hinv : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ E ↔ x + t • verticalDirection m ∈ E) :
    ∃ e : Space (m + 1), ‖e‖ = 1 ∧ E =ᵐ[volume] positiveHalfspace e :=
  IsDirectedMinimizingCone.halfspace_of_verticalInvariant_of_lower
    (fun _ hT' ↦ hT'.ae_eq_positiveHalfspace_of_le_seven (by omega)) hE hinv

/-- **Open obligation (weak height data, blueprint HA2–HA3, HA4.1, HA6.1, HA10).** Along
aligned HA11 contradiction sequences, the normalized level-set heights have an `L²` limit with
an `L²` weak gradient, the HA6.1 weighted height approximation and the HA4.1 flux limit. -/
theorem RigidityHypotheses.exists_hasAlignedWeakHeightData
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    ∃ M : ℝ, 0 ≤ M ∧ HasAlignedWeakHeightData g u (phasePrimitive f 1) M := by
  sorry

/-- Harmonic layer data (blueprint HA2–HA4, HA6.1, HA10): the limit of the normalized heights
is harmonic (Weyl's lemma applied to the HA4 flux identity), proved from the weak height data
in `AlignedHarmonicLayers`. -/
theorem RigidityHypotheses.exists_hasAlignedHarmonicLayerData
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    ∃ M : ℝ, 0 ≤ M ∧ HasAlignedHarmonicLayerData g u (phasePrimitive f 1) M :=
  hr.exists_hasAlignedHarmonicLayerData_of_weak h hsharp
    (hr.exists_hasAlignedWeakHeightData h hsharp)

/-- Tilt-excess decay (blueprint HA0–HA11): under the sharp surface-energy bound at every center
and radius, the rescaled cylinder tilt of the zero extension at free-boundary centers decays by
the HA0 factor. -/
theorem RigidityHypotheses.hasCylinderTiltDecay_of_sharp_energy
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m) :
    HasCylinderTiltDecay g u := by
  obtain ⟨M, hM, hal⟩ := hr.exists_hasAlignedHarmonicLayerData h hsharp
  exact hr.hasCylinderTiltDecay_of_harmonicLayerData h hsharp hM hal

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
