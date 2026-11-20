module

public import SerrinEpigraph.LowLevelProfileApproximation
public import SerrinEpigraph.InteriorGradientModulus
public import SerrinEpigraph.MesoscopicLayerFlatness

/-!
# The level cone condition on good projections (HA9.c, HA9.d)

Blueprint `harmonic-approximation.md`, HA9.d and HA9.e: on the horizontal lines carrying a good
point in the slab, the interior level sets of the rotated rescaled translates are Lipschitz graphs
with a prescribed small constant (`HasLevelCone`), and every good point is a center of profile
approximation around the reference level height. The proof combines

* the microscopic compactness at good anchors with an orientation alternative
  (`RigidityHypotheses.exists_microscopic_oriented_dichotomy`): either the translates are close to
  the increasing layer profile, or there is a downward crossing followed, deeper along the line,
  by values above the level;
* the mesoscopic flatness `RigidityHypotheses.exists_mesoscopic_flatness` (HA9.c, HA9.d);
* the uniform gradient modulus `RigidityHypotheses.exists_gradient_difference_quotient`, which
  turns the profile approximation into control of the gradient direction at sub-microscopic
  distances;
* the slab facts on the lines (HA8): the translates vanish below `-η` and exceed `1 - β` above
  `η`, which orient the profile and confine the level points to the thin layer.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff NNReal

namespace SerrinEpigraph

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ### One-dimensional facts -/

/-- Increments of the layer profile between levels of a compact subinterval of `(0, 1)` grow at
least linearly. -/
theorem RigidityHypotheses.layerProfile_sub_ge (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {lo hi c : ℝ} (hlo : 0 < lo)
    (hc : ∀ s ∈ Icc lo hi, c ≤ Real.sqrt (2 * normalizedPotential f s)) {σ σ' : ℝ}
    (hσσ' : σ ≤ σ') (h1 : lo ≤ layerProfile f σ) (h2 : layerProfile f σ' ≤ hi) :
    c * (σ' - σ) ≤ layerProfile f σ' - layerProfile f σ := by
  have hσ : 0 < σ := by
    by_contra hn
    rw [layerProfile_of_nonpos f (not_lt.mp hn)] at h1
    linarith
  have hmono := hr.layerProfile_monotone h
  have hcont := hr.continuous_layerProfile h
  apply (convex_Icc σ σ').mul_sub_le_image_sub_of_le_deriv hcont.continuousOn
    (fun ξ hξ ↦ ?_) (fun ξ hξ ↦ ?_) σ ⟨le_rfl, hσσ'⟩ σ' ⟨hσσ', le_rfl⟩ hσσ'
  · rw [interior_Icc] at hξ
    exact (hr.layerProfile_hasDerivAt h (hσ.trans hξ.1)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc] at hξ
    rw [(hr.layerProfile_hasDerivAt h (hσ.trans hξ.1)).deriv]
    exact hc _ ⟨h1.trans (hmono hξ.1.le), (hmono hξ.2.le).trans h2⟩

/-- **Downward crossings of Hamiltonian profiles.** A downward crossing of an interior level
lies on a decreasing branch, so the profile stays above the level at every earlier time. -/
theorem IsHamiltonianProfile.lt_of_downward {P P' : ℝ → ℝ} (hP : IsHamiltonianProfile f P P')
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {s σ₁ σ₂ : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (h12 : σ₁ < σ₂) (h1 : s < P σ₁) (h2 : P σ₂ < s) :
    ∀ τ ≤ σ₁, s < P τ := by
  intro τ hτ
  by_contra hn
  push Not at hn
  have hτσ : τ < σ₁ := lt_of_le_of_ne hτ (by rintro rfl; linarith)
  obtain ⟨μ, hμ, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (hτσ.le.trans h12.le)) hP.continuous.continuousOn
  have hPμ : P σ₁ ≤ P μ := isMaxOn_iff.mp hmax σ₁ ⟨hτσ.le, h12.le⟩
  have hμ1 : μ ≠ τ := by rintro rfl; linarith
  have hμ2 : μ ≠ σ₂ := by rintro rfl; linarith
  have hμint : μ ∈ Ioo τ σ₂ := ⟨lt_of_le_of_ne hμ.1 (Ne.symm hμ1), lt_of_le_of_ne hμ.2 hμ2⟩
  have hloc : IsLocalMax P μ := hmax.isLocalMax (Icc_mem_nhds hμint.1 hμint.2)
  have hpos : 0 < P μ := by linarith [hs.1]
  rcases (hP.mem_Icc μ).2.lt_or_eq with hlt | heq
  · exact hP.deriv_ne_zero hr h hpos hlt (hloc.hasDerivAt_eq_zero (hP.hasDerivAt μ hpos))
  · have := hP.eq_one_of_eq_one hr h heq σ₂
    linarith [hs.2]

/-! ### Microscopic compactness with orientation -/

/-- The anchor of a one-dimensional limit lies in the closure of the positive set of its profile. -/
private theorem mem_closure_profile_aux {d : ℕ} {V : Space d → ℝ} {e : Space d}
    (he : ‖e‖ = 1) (h1D : ∀ x, V x = V ((inner ℝ e x) • e))
    (hcl : (0 : Space d) ∈ closure {x | 0 < V x}) :
    (0 : ℝ) ∈ closure {τ : ℝ | 0 < V (τ • e)} := by
  rw [Metric.mem_closure_iff] at hcl ⊢
  intro ε hε
  obtain ⟨x, hx, hdist⟩ := hcl ε hε
  refine ⟨inner ℝ e x, ?_, ?_⟩
  · change 0 < V (inner ℝ e x • e)
    rw [← h1D x]
    exact hx
  · rw [Real.dist_eq, zero_sub, abs_neg]
    calc |inner ℝ e x| ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ = dist 0 x := by rw [he, one_mul, dist_comm, dist_zero_right]
      _ < ε := hdist

/-- The layer profile hits a positive level only at its travel time. -/
private theorem RigidityHypotheses.eq_travelTime_aux
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) {s x : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hx : layerProfile f x = s) : x = layerTravelTime f s := by
  have hxpos : 0 < x := by
    by_contra hn
    rw [layerProfile_of_nonpos f (not_lt.mp hn)] at hx
    linarith [hs.1]
  have := (hr.layerProfile_spec h hxpos.le).2
  rw [hx] at this
  exact this.symm

/-- **HA10.a, crossing part, oriented.** Either a downward crossing in the window followed by
values above `s` at depth `K₂`, or a crossing of `s` in the window. -/
theorem RigidityHypotheses.exists_microscopic_crossing_oriented (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {b₀ s M₀ K₂ : ℝ} (hb₀ : b₀ ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hM₀ : layerTravelTime f (1 - b₀) + 1 ≤ M₀) (hK₂ : M₀ + layerTravelTime f s + 2 ≤ K₂) :
    ∃ ℓ ρ₀ : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ ∀ (X e : Space (m + 1)), ‖e‖ = 1 →
      zeroExtension g u X ∈ Ioo 0 (1 - b₀) →
      (∀ ρ ∈ Ioc 0 ρ₀, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        ℓ * ρ ^ m) →
      (∃ τ₁ τ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ τ₁ ∧ τ₁ < τ₂ ∧
        τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s ∧ s < zeroExtension g u (X + (-K₂) • e)) ∨
      ∃ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
        zeroExtension g u (X + τ • e) = s := by
  by_contra hcon
  simp only [not_exists, not_and, not_or, not_forall] at hcon
  have hseq : ∀ j : ℕ, ∃ X e : Space (m + 1), ‖e‖ = 1 ∧ zeroExtension g u X ∈ Ioo 0 (1 - b₀) ∧
      (∀ ρ ∈ Ioc 0 ((j : ℝ) + 1), ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        1 / ((j : ℝ) + 1) * ρ ^ m) ∧
      (¬∃ τ₁ τ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ τ₁ ∧ τ₁ < τ₂ ∧
        τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s ∧ s < zeroExtension g u (X + (-K₂) • e)) ∧
      ¬∃ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
        zeroExtension g u (X + τ • e) = s := by
    intro j
    obtain ⟨X, e, he, hX, htilt, hA, hB⟩ := hcon (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1)
      (by positivity) (by positivity)
    refine ⟨X, e, he, hX, htilt, ?_, ?_⟩
    · rintro ⟨τ₁, τ₂, h1, h2, h3, h4, h5, h6⟩
      exact hA τ₁ τ₂ h1 h2 h3 h4 h5 h6
    · rintro ⟨τ, hτ, hτs⟩
      exact hB τ hτ hτs
  choose X ev hev hX htilt hA hB using hseq
  have hℓ : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hρ₀ : Tendsto (fun j : ℕ ↦ (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  obtain ⟨φ, e, V, -, -, hφ, he, hconv, -, -, -, -, hV, hVval, hlim, h1D, hV0, hcl⟩ :=
    hr.exists_anchor_limit h X ev hev hℓ hρ₀ htilt (fun j ↦ (hX j).1) (fun j ↦ (hX j).2.le)
      (M := 0) (K' := 0) (fun _ ↦ 0) (fun _ ↦ ⟨by norm_num, le_rfl⟩) (fun _ ↦ 0)
      (fun _ ↦ mem_closedBall_self le_rfl)
  have hP := hr.isHamiltonianProfile_of_oneDimensional_limit h hbound hV hVval hlim he h1D
  have hcl' := mem_closure_profile_aux he h1D hcl
  have hP0 : V ((0 : ℝ) • e) ≤ 1 - b₀ := by rwa [zero_smul]
  have hTb : 0 ≤ layerTravelTime f (1 - b₀) :=
    hr.layerTravelTime_nonneg h ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  have hTs : 0 < layerTravelTime f s := hr.layerTravelTime_pos h hs
  have hline : ∀ σ : ℝ, Tendsto (fun j ↦ zeroExtension g u (X (φ j) + σ • ev (φ j))) atTop
      (𝓝 (V (σ • e))) := fun σ ↦
    tendsto_translate_of_tendsto hV.continuous hlim (tendsto_const_nhds.smul hconv)
  rcases hP.anchored_dichotomy hr h (M₀ := M₀) hb₀ hs (by linarith) hP0 hcl' with hinc | hdown
  · -- an increasing profile crosses `s` near `T(s) - T(P 0)`
    set s₀ := V ((0 : ℝ) • e)
    have hs₀ : s₀ ∈ Ico (0 : ℝ) 1 := ⟨(hVval _).1, by linarith [hb₀.1]⟩
    have hTs₀ : layerTravelTime f s₀ ≤ layerTravelTime f (1 - b₀) :=
      (hr.layerTravelTime_strictMonoOn h).monotoneOn hs₀
        ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩ hP0
    have hTs₀0 := hr.layerTravelTime_nonneg h hs₀
    set σ := layerTravelTime f s - layerTravelTime f s₀ with hσ
    set γ := min (layerTravelTime f s) 1 / 2 with hγ
    have hγpos : 0 < γ := by positivity
    have hγ1 : γ ≤ 1 / 2 := by
      have := min_le_right (layerTravelTime f s) 1
      rw [hγ]; linarith
    have hγs : γ < layerTravelTime f s := by
      have := min_le_left (layerTravelTime f s) 1
      rw [hγ]; linarith
    have hlow : V ((σ - γ) • e) < s := by
      have heq := hinc (σ - γ) (by linarith)
      change V ((σ - γ) • e) = layerProfile f (σ - γ + layerTravelTime f s₀) at heq
      rw [heq, show σ - γ + layerTravelTime f s₀ = layerTravelTime f s - γ by rw [hσ]; ring]
      exact hr.layerProfile_lt_of_lt_travelTime h hs (by linarith)
    have hhigh : s < V ((σ + γ) • e) := by
      have heq := hinc (σ + γ) (by linarith)
      change V ((σ + γ) • e) = layerProfile f (σ + γ + layerTravelTime f s₀) at heq
      rw [heq, show σ + γ + layerTravelTime f s₀ = layerTravelTime f s + γ by rw [hσ]; ring]
      exact hr.lt_layerProfile_of_travelTime_lt h ⟨hs.1.le, hs.2⟩ (by linarith)
    obtain ⟨j, hj1, hj2⟩ := ((hline (σ - γ)).eventually (gt_mem_nhds hlow)).and
      ((hline (σ + γ)).eventually (lt_mem_nhds hhigh)) |>.exists
    have hcont : ContinuousOn (fun τ : ℝ ↦ zeroExtension g u (X (φ j) + τ • ev (φ j)))
        (Icc (σ - γ) (σ + γ)) :=
      (h.zeroExtension_continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))).continuousOn
    obtain ⟨τ, hτ, hτs⟩ := intermediate_value_Icc (by linarith) hcont ⟨hj1.le, hj2.le⟩
    exact hB (φ j) ⟨τ, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩, hτs⟩
  · obtain ⟨σ₁, σ₂, h1, h2, h3, h4, h5⟩ := hdown
    have h6 : s < V ((-K₂) • e) :=
      hP.lt_of_downward hr h hs h2 h4 h5 (-K₂) (by linarith)
    obtain ⟨j, ⟨hj1, hj2⟩, hj3⟩ := (((hline σ₁).eventually (lt_mem_nhds h4)).and
      ((hline σ₂).eventually (gt_mem_nhds h5))).and
      ((hline (-K₂)).eventually (lt_mem_nhds h6)) |>.exists
    exact hA (φ j) ⟨σ₁, σ₂, by linarith, h2, h3, hj1, hj2, hj3⟩

/-- **HA10.a, approximation part, oriented.** Either a downward crossing in the window followed
by values above `s` at depth `K₂`, or every crossing of `s` in the window is a center of
`α`-approximation by the layer profile on `B̄_{K'}`. -/
theorem RigidityHypotheses.exists_microscopic_approximation_oriented (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {α K' b₀ s M₀ K₂ : ℝ} (hα : 0 < α) (hK' : 0 ≤ K') (hb₀ : b₀ ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) (hM₀ : K' + layerTravelTime f (1 - b₀) + 1 ≤ M₀)
    (hK₂ : M₀ + layerTravelTime f s + 2 ≤ K₂) :
    ∃ ℓ ρ₀ : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ ∀ (X e : Space (m + 1)), ‖e‖ = 1 →
      zeroExtension g u X ∈ Ioo 0 (1 - b₀) →
      (∀ ρ ∈ Ioc 0 ρ₀, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        ℓ * ρ ^ m) →
      (∃ τ₁ τ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ τ₁ ∧ τ₁ < τ₂ ∧
        τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s ∧ s < zeroExtension g u (X + (-K₂) • e)) ∨
      ∀ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
        zeroExtension g u (X + τ • e) = s → ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
          |zeroExtension g u (X + Z) - layerProfile f (inner ℝ e Z - τ + layerTravelTime f s)|
            ≤ α := by
  by_contra hcon
  simp only [not_exists, not_and, not_or, not_forall, not_le] at hcon
  set W := Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1) with hW
  have hseq : ∀ j : ℕ, ∃ (X e : Space (m + 1)) (τ : ℝ) (Z : Space (m + 1)), ‖e‖ = 1 ∧
      zeroExtension g u X ∈ Ioo 0 (1 - b₀) ∧
      (∀ ρ ∈ Ioc 0 ((j : ℝ) + 1), ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        1 / ((j : ℝ) + 1) * ρ ^ m) ∧
      (¬∃ τ₁ τ₂ : ℝ, -(M₀ + layerTravelTime f s + 2) ≤ τ₁ ∧ τ₁ < τ₂ ∧
        τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s ∧ s < zeroExtension g u (X + (-K₂) • e)) ∧
      τ ∈ W ∧ zeroExtension g u (X + τ • e) = s ∧ Z ∈ closedBall (0 : Space (m + 1)) K' ∧
      α < |zeroExtension g u (X + Z) - layerProfile f (inner ℝ e Z - τ + layerTravelTime f s)| := by
    intro j
    obtain ⟨X, e, he, hX, htilt, hA, τ, hτ, hτs, Z, hZ, hbad⟩ :=
      hcon (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1) (by positivity) (by positivity)
    refine ⟨X, e, τ, Z, he, hX, htilt, ?_, hτ, hτs, hZ, hbad⟩
    rintro ⟨τ₁, τ₂, h1, h2, h3, h4, h5, h6⟩
    exact hA τ₁ τ₂ h1 h2 h3 h4 h5 h6
  choose X ev τ Z hev hX htilt hA hτ hτs hZ hbad using hseq
  have hℓ : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hρ₀ : Tendsto (fun j : ℕ ↦ (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hTb : 0 ≤ layerTravelTime f (1 - b₀) :=
    hr.layerTravelTime_nonneg h ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  have hTs : 0 < layerTravelTime f s := hr.layerTravelTime_pos h hs
  have hτM : ∀ j, τ j ∈ Icc (-(layerTravelTime f (1 - b₀) + layerTravelTime f s + 1))
      (layerTravelTime f (1 - b₀) + layerTravelTime f s + 1) := fun j ↦
    ⟨by linarith [(hτ j).1], by linarith [(hτ j).2]⟩
  obtain ⟨φ, e, V, τlim, Zlim, hφ, he, hconv, hconvτ, hconvZ, -, hZlim, hV, hVval, hlim, h1D,
    hV0, hcl⟩ := hr.exists_anchor_limit h X ev hev hℓ hρ₀ htilt (fun j ↦ (hX j).1)
      (fun j ↦ (hX j).2.le) τ hτM Z hZ
  have hP := hr.isHamiltonianProfile_of_oneDimensional_limit h hbound hV hVval hlim he h1D
  have hcl' := mem_closure_profile_aux he h1D hcl
  have hP0 : V ((0 : ℝ) • e) ≤ 1 - b₀ := by rwa [zero_smul]
  have hline : ∀ σ : ℝ, Tendsto (fun j ↦ zeroExtension g u (X (φ j) + σ • ev (φ j))) atTop
      (𝓝 (V (σ • e))) := fun σ ↦
    tendsto_translate_of_tendsto hV.continuous hlim (tendsto_const_nhds.smul hconv)
  rcases hP.anchored_dichotomy hr h (M₀ := M₀) hb₀ hs (by linarith) hP0 hcl' with hinc | hdown
  · set s₀ := V ((0 : ℝ) • e)
    -- the limit crossing
    have hτW : τlim ∈ W := isClosed_Icc.mem_of_tendsto hconvτ
      (Eventually.of_forall fun j ↦ hτ (φ j))
    have hVτ : V (τlim • e) = s := by
      have h1 := tendsto_translate_of_tendsto hV.continuous hlim (hconvτ.smul hconv)
      have h2 : (fun j ↦ zeroExtension g u (X (φ j) + τ (φ j) • ev (φ j))) = fun _ ↦ s :=
        funext fun j ↦ hτs (φ j)
      rw [h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hτcross : τlim + layerTravelTime f s₀ = layerTravelTime f s := by
      have heq := hinc τlim (by linarith [hτW.1])
      change V (τlim • e) = layerProfile f (τlim + layerTravelTime f s₀) at heq
      rw [hVτ] at heq
      exact hr.eq_travelTime_aux h hs heq.symm
    -- the limit approximation
    have hZe : -M₀ ≤ inner ℝ e Zlim := by
      have h1 : |inner ℝ e Zlim| ≤ K' := by
        calc |inner ℝ e Zlim| ≤ ‖e‖ * ‖Zlim‖ := abs_real_inner_le_norm _ _
          _ ≤ K' := by rw [he, one_mul]; simpa using hZlim
      linarith [neg_abs_le (inner ℝ e Zlim)]
    have hVZ : V Zlim = layerProfile f (inner ℝ e Zlim - τlim + layerTravelTime f s) := by
      rw [h1D Zlim, hinc _ hZe, show inner ℝ e Zlim + layerTravelTime f s₀ =
        inner ℝ e Zlim - τlim + layerTravelTime f s by linarith]
    have hU : Tendsto (fun j ↦ zeroExtension g u (X (φ j) + Z (φ j))) atTop (𝓝 (V Zlim)) :=
      tendsto_translate_of_tendsto hV.continuous hlim hconvZ
    have hq : Tendsto (fun j ↦ layerProfile f (inner ℝ (ev (φ j)) (Z (φ j)) - τ (φ j) +
        layerTravelTime f s)) atTop
        (𝓝 (layerProfile f (inner ℝ e Zlim - τlim + layerTravelTime f s))) := by
      apply ((hr.continuous_layerProfile h).tendsto _).comp
      exact ((hconv.inner hconvZ).sub hconvτ).add tendsto_const_nhds
    have hdiff := (hU.sub hq)
    rw [hVZ, sub_self] at hdiff
    obtain ⟨j, hj⟩ := (hdiff.abs.eventually (gt_mem_nhds (by rw [abs_zero]; exact hα))).exists
    exact absurd (hbad (φ j)) (not_lt.mpr hj.le)
  · obtain ⟨σ₁, σ₂, h1, h2, h3, h4, h5⟩ := hdown
    have h6 : s < V ((-K₂) • e) :=
      hP.lt_of_downward hr h hs h2 h4 h5 (-K₂) (by linarith)
    obtain ⟨j, ⟨hj1, hj2⟩, hj3⟩ := (((hline σ₁).eventually (lt_mem_nhds h4)).and
      ((hline σ₂).eventually (gt_mem_nhds h5))).and
      ((hline (-K₂)).eventually (lt_mem_nhds h6)) |>.exists
    exact hA (φ j) ⟨σ₁, σ₂, by linarith, h2, h3, hj1, hj2, hj3⟩


/-- **HA10.a with orientation.** For `α > 0`, `K' ≥ 0`, `b₀, s ∈ (0, 1)` and a depth
`K₂ ≥ K' + T(1-b₀) + T(s) + 3` there are `ℓ, ρ₀ > 0` such that, at every point `X` with
`U(X) ∈ (0, 1 - b₀)` and small tilt along a unit vector `e` on all balls of radius at most `ρ₀`:
either `U` crosses `s` downward along `X + τ e` in a fixed window and exceeds `s` at `X - K₂ e`,
or `U` crosses `s` in the window `[-(T(1-b₀) + 1), T(s) + 1]` and every such crossing `τ` is a
center of `α`-approximation by the layer profile on `B̄_{K'}`. -/
theorem RigidityHypotheses.exists_microscopic_oriented_dichotomy (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {L : ℝ}
    (hbound : ∀ z : Space (m + 1), ∀ r : ℝ, 0 < r →
      (∫ x in closedBall z r, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤ L * r ^ m)
    {α K' b₀ s K₂ : ℝ} (hα : 0 < α) (hK' : 0 ≤ K') (hb₀ : b₀ ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (hK₂ : K' + layerTravelTime f (1 - b₀) + layerTravelTime f s + 3 ≤ K₂) :
    ∃ ℓ ρ₀ : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ ∀ (X e : Space (m + 1)), ‖e‖ = 1 →
      zeroExtension g u X ∈ Ioo 0 (1 - b₀) →
      (∀ ρ ∈ Ioc 0 ρ₀, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
        ℓ * ρ ^ m) →
      (∃ τ₁ τ₂ : ℝ, -(K' + layerTravelTime f (1 - b₀) + layerTravelTime f s + 3) ≤ τ₁ ∧
        τ₁ < τ₂ ∧ τ₂ ≤ layerTravelTime f (1 - b₀) ∧ s < zeroExtension g u (X + τ₁ • e) ∧
        zeroExtension g u (X + τ₂ • e) < s ∧ s < zeroExtension g u (X + (-K₂) • e)) ∨
      ((∃ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
          zeroExtension g u (X + τ • e) = s) ∧
        ∀ τ ∈ Icc (-(layerTravelTime f (1 - b₀) + 1)) (layerTravelTime f s + 1),
          zeroExtension g u (X + τ • e) = s → ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
            |zeroExtension g u (X + Z) - layerProfile f (inner ℝ e Z - τ + layerTravelTime f s)|
              ≤ α) := by
  set M₀ := K' + layerTravelTime f (1 - b₀) + 1 with hM₀
  have hTb : 0 ≤ layerTravelTime f (1 - b₀) :=
    hr.layerTravelTime_nonneg h ⟨by linarith [hb₀.2], by linarith [hb₀.1]⟩
  obtain ⟨ℓ₁, ρ₁, hℓ₁, hρ₁, h1⟩ := hr.exists_microscopic_crossing_oriented h hbound
    (M₀ := M₀) (K₂ := K₂) hb₀ hs (by linarith) (by linarith)
  obtain ⟨ℓ₂, ρ₂, hℓ₂, hρ₂, h2⟩ := hr.exists_microscopic_approximation_oriented h hbound
    (M₀ := M₀) (K₂ := K₂) hα hK' hb₀ hs le_rfl (by linarith)
  refine ⟨min ℓ₁ ℓ₂, max ρ₁ ρ₂, lt_min hℓ₁ hℓ₂, lt_max_of_lt_left hρ₁, ?_⟩
  intro X e he hX htilt
  have ht₁ : ∀ ρ ∈ Ioc 0 ρ₁, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
      ℓ₁ * ρ ^ m := fun ρ hρ ↦ (htilt ρ ⟨hρ.1, hρ.2.trans (le_max_left _ _)⟩).trans_le
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hρ.1.le m))
  have ht₂ : ∀ ρ ∈ Ioc 0 ρ₂, ∫ z in ball X ρ, diffuseTiltDensity 1 (zeroExtension g u) e z <
      ℓ₂ * ρ ^ m := fun ρ hρ ↦ (htilt ρ ⟨hρ.1, hρ.2.trans (le_max_right _ _)⟩).trans_le
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hρ.1.le m))
  have hwin : -(M₀ + layerTravelTime f s + 2) =
      -(K' + layerTravelTime f (1 - b₀) + layerTravelTime f s + 3) := by rw [hM₀]; ring
  rcases h1 X e he hX ht₁ with hd | hc
  · left
    rwa [hwin] at hd
  · rcases h2 X e he hX ht₂ with hd | ha
    · left
      rwa [hwin] at hd
    · exact Or.inr ⟨hc, ha⟩

/-! ### Geometry of the rotated rescaling -/

private theorem point_sub_point_aux (y y' : Space m) (t t' : ℝ) :
    point y t - point y' t' = point (y - y') (t - t') := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]

private theorem norm_point_sq_aux (y : Space m) (t : ℝ) :
    ‖point y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_point_point, real_inner_self_eq_norm_sq]
  ring

/-- Points of a rotated rescaling: differences, heights and horizontal parts. -/
theorem rescaled_sub_eq (x : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (z z' : Space (m + 1)) : (x + R • Q z') - (x + R • Q z) = R • Q (z' - z) := by
  rw [add_sub_add_left_eq_sub, ← smul_sub, ← map_sub]

theorem inner_rescaled_sub (x : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (z z' : Space (m + 1)) :
    inner ℝ (Q (verticalDirection m)) ((x + R • Q z') - (x + R • Q z)) =
      R * (z' (Fin.last m) - z (Fin.last m)) := by
  rw [rescaled_sub_eq, real_inner_smul_right, LinearIsometryEquiv.inner_map_map,
    real_inner_comm, inner_verticalDirection_right]
  simp

theorem norm_rescaled_sub {R : ℝ} (hR : 0 < R) (x : Space (m + 1))
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (z z' : Space (m + 1)) :
    ‖(x + R • Q z') - (x + R • Q z)‖ = R * ‖z' - z‖ := by
  rw [rescaled_sub_eq, norm_smul, Real.norm_of_nonneg hR.le, LinearIsometryEquiv.norm_map]

/-- The part of a rescaled difference orthogonal to the rotated vertical. -/
theorem norm_rescaled_sub_orth {R : ℝ} (hR : 0 < R) (x : Space (m + 1))
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (y y' : Space m) (t t' : ℝ) :
    ‖((x + R • Q (point y' t')) - (x + R • Q (point y t))) -
        inner ℝ (Q (verticalDirection m)) ((x + R • Q (point y' t')) - (x + R • Q (point y t))) •
          Q (verticalDirection m)‖ = R * ‖y' - y‖ := by
  rw [inner_rescaled_sub, rescaled_sub_eq, last_point, last_point, point_sub_point_aux]
  have h1 : R • Q (point (y' - y) (t' - t)) - (R * (t' - t)) • Q (verticalDirection m) =
      R • Q (point (y' - y) 0) := by
    have hp : point (y' - y) (t' - t) = point (y' - y) 0 + (t' - t) • verticalDirection m := by
      have := point_add_vertical (y' - y) 0 (t' - t)
      rw [zero_add] at this
      exact this.symm
    rw [hp, map_add, map_smul, smul_add, smul_smul]
    abel
  rw [h1, norm_smul, Real.norm_of_nonneg hR.le, LinearIsometryEquiv.norm_map]
  have h2 : ‖point (y' - y) (0 : ℝ)‖ ^ 2 = ‖y' - y‖ ^ 2 := by
    rw [norm_point_sq_aux]
    ring
  have h3 : ‖point (y' - y) (0 : ℝ)‖ = ‖y' - y‖ := by
    nlinarith [norm_nonneg (point (y' - y) (0 : ℝ)), norm_nonneg (y' - y)]
  rw [h3]

/-- A height difference that is a small fraction of the distance is a cone bound. -/
theorem abs_sub_le_of_le_mul_norm {y y' : Space m} {t t' c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2)
    (h : |t - t'| ≤ c * ‖point y t - point y' t'‖) : |t - t'| ≤ 2 * c * ‖y - y'‖ := by
  rw [point_sub_point_aux] at h
  have hsq : ‖point (y - y') (t - t')‖ ^ 2 = ‖y - y'‖ ^ 2 + (t - t') ^ 2 := norm_point_sq_aux _ _
  have h1 : (t - t') ^ 2 ≤ c ^ 2 * (‖y - y'‖ ^ 2 + (t - t') ^ 2) := by
    rw [← hsq, ← mul_pow, ← sq_abs (t - t')]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h2 : (t - t') ^ 2 ≤ (2 * c) ^ 2 * ‖y - y'‖ ^ 2 := by
    have hc2' : c ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith [sq_nonneg (t - t'), sq_nonneg ‖y - y'‖,
      mul_nonneg (sq_nonneg c) (sq_nonneg (t - t'))]
  have h3 : |t - t'| ^ 2 ≤ (2 * c * ‖y - y'‖) ^ 2 := by
    rw [sq_abs, mul_pow]
    exact h2
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp h3

/-- **Transfer of small tilt.** Tilt below `ℓ ρᵐ` on all balls about `X` of radius at most
`ρ_max` gives ball tilt below `ℓ (2d)ᵐ` on `B̄_d(P)` when `‖P - X‖ < d` and `2d ≤ ρ_max`. -/
theorem ballTiltIntegral_lt_of_anchor {U : Space (m + 1) → ℝ} (hU : LocallyLipschitz U)
    {X P e : Space (m + 1)} (he : ‖e‖ = 1) {ℓ ρmax d : ℝ}
    (htilt : ∀ ρ ∈ Ioc 0 ρmax, ∫ z in ball X ρ, diffuseTiltDensity 1 U e z < ℓ * ρ ^ m)
    (hPX : ‖P - X‖ < d) (hd : 2 * d ≤ ρmax) :
    ballTiltIntegral U P e d < ℓ * (2 * d) ^ m := by
  have hd0 : 0 < d := (norm_nonneg _).trans_lt hPX
  have hsub : closedBall P d ⊆ ball X (2 * d) := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    calc dist z X ≤ dist z P + dist P X := dist_triangle _ _ _
      _ < d + d := by
        rw [dist_eq_norm P X]
        linarith
      _ = 2 * d := by ring
  have hK := isCompact_closedBall X (2 * d)
  have hint := integrableOn_diffuseTiltDensity hU hK 1 he
  have hmono : ballTiltIntegral U P e d ≤ ∫ z in ball X (2 * d), diffuseTiltDensity 1 U e z := by
    unfold ballTiltIntegral
    have heq : (fun y ↦ ‖gradient U y‖ ^ 2 - inner ℝ (gradient U y) e ^ 2) =
        diffuseTiltDensity 1 U e := by
      funext y
      simp [diffuseTiltDensity]
    rw [heq]
    exact setIntegral_mono_set (hint.mono_set ball_subset_closedBall)
      (Eventually.of_forall fun z ↦ diffuseTiltDensity_nonneg one_pos U he z)
      (Eventually.of_forall hsub)
  exact hmono.trans_lt (htilt (2 * d) ⟨by positivity, hd⟩)

/-- **Inverting the layer profile near a level.** If the profile at `σ` is within `α` of an
interior level `s` with `[s - α, s + α] ⊆ [lo, hi]`, then `σ` is within `α / c` of `T(s)`. -/
theorem RigidityHypotheses.abs_sub_travelTime_le (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {lo hi c : ℝ} (hlo : 0 < lo) (hc : 0 < c)
    (hcW : ∀ s ∈ Icc lo hi, c ≤ Real.sqrt (2 * normalizedPotential f s)) {s α σ : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (hslo : lo ≤ s - α) (hshi : s + α ≤ hi)
    (hσ : |layerProfile f σ - s| ≤ α) : |σ - layerTravelTime f s| ≤ α / c := by
  have hqT : layerProfile f (layerTravelTime f s) = s := hr.layerProfile_travelTime h hs
  rw [abs_le] at hσ
  have hαc : 0 ≤ α / c := by
    have : 0 ≤ α := by linarith [hσ.1, hσ.2]
    positivity
  rw [abs_le]
  rcases le_total (layerTravelTime f s) σ with hle | hle
  · have hinc := hr.layerProfile_sub_ge h hlo hcW hle (by rw [hqT]; linarith)
      (by linarith)
    rw [hqT] at hinc
    have h1 : c * (σ - layerTravelTime f s) ≤ α := by linarith
    have h2 : σ - layerTravelTime f s ≤ α / c := by
      rw [le_div_iff₀ hc]
      linarith [mul_comm c (σ - layerTravelTime f s)]
    constructor <;> linarith
  · have hinc := hr.layerProfile_sub_ge h hlo hcW hle (by linarith) (by rw [hqT]; linarith)
    rw [hqT] at hinc
    have h1 : c * (layerTravelTime f s - σ) ≤ α := by linarith
    have h2 : layerTravelTime f s - σ ≤ α / c := by
      rw [le_div_iff₀ hc]
      linarith [mul_comm c (layerTravelTime f s - σ)]
    constructor <;> linarith

/-! ### Gradient directions near the profile -/

/-- **Gradient direction from the profile approximation.** If `U` is `α`-close on `B̄_{K'}(X)`
to the layer profile in the direction `e`, then at a point `Y` with `B̄_{r_P + h}(Y)` in the
positive phase, difference quotients with step `h` bound the tangential derivatives of `U` and
bound the normal derivative from below. -/
theorem gradient_bounds_of_profile {rP εg δg : ℝ}
    (hdq : ∀ (Y w : Space (m + 1)) (t : ℝ), ‖w‖ = 1 → 0 ≤ t → t < δg →
      closedBall Y (rP + t) ⊆ epigraph g →
      |zeroExtension g u (Y + t • w) - zeroExtension g u Y -
        t * inner ℝ (gradient (zeroExtension g u) Y) w| ≤ t * εg)
    {X e Y : Space (m + 1)} {τc T₀ K' α hs : ℝ}
    (happrox : ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
      |zeroExtension g u (X + Z) - layerProfile f (inner ℝ e Z - τc + T₀)| ≤ α)
    (hY : ‖Y - X‖ + hs ≤ K') (hs0 : 0 < hs) (hsδ : hs < δg)
    (hball : closedBall Y (rP + hs) ⊆ epigraph g) :
    (∀ w : Space (m + 1), ‖w‖ = 1 → inner ℝ e w = 0 →
      hs * |inner ℝ (gradient (zeroExtension g u) Y) w| ≤ 2 * α + hs * εg) ∧
    (‖e‖ = 1 → ∀ {lo hi c : ℝ}, (∀ σ σ' : ℝ, σ ≤ σ' → lo ≤ layerProfile f σ →
        layerProfile f σ' ≤ hi → c * (σ' - σ) ≤ layerProfile f σ' - layerProfile f σ) →
      lo ≤ layerProfile f (inner ℝ e (Y - X) - τc + T₀) →
      layerProfile f (inner ℝ e (Y - X) - τc + T₀ + hs) ≤ hi →
      c * hs - 2 * α - hs * εg ≤ hs * inner ℝ (gradient (zeroExtension g u) Y) e) := by
  set U := zeroExtension g u with hUdef
  have hmemY : Y - X ∈ closedBall (0 : Space (m + 1)) K' := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  have happY := happrox (Y - X) hmemY
  rw [add_sub_cancel] at happY
  have hshift : ∀ w : Space (m + 1), ‖w‖ = 1 →
      |U (Y + hs • w) - layerProfile f (inner ℝ e (Y + hs • w - X) - τc + T₀)| ≤ α := by
    intro w hw
    have hmem : Y + hs • w - X ∈ closedBall (0 : Space (m + 1)) K' := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖Y + hs • w - X‖ = ‖(Y - X) + hs • w‖ := by congr 1; abel
        _ ≤ ‖Y - X‖ + ‖hs • w‖ := norm_add_le _ _
        _ = ‖Y - X‖ + hs := by rw [norm_smul, hw, mul_one, Real.norm_of_nonneg hs0.le]
        _ ≤ K' := hY
    have := happrox _ hmem
    rwa [add_sub_cancel] at this
  constructor
  · intro w hw hew
    have hd := hdq Y w hs hw hs0.le hsδ hball
    have h1 := hshift w hw
    have hinner : inner ℝ e (Y + hs • w - X) = inner ℝ e (Y - X) := by
      rw [show Y + hs • w - X = (Y - X) + hs • w by abel, inner_add_right, inner_smul_right,
        hew, mul_zero, add_zero]
    rw [hinner] at h1
    have h2 : |U (Y + hs • w) - U Y| ≤ 2 * α := by
      calc |U (Y + hs • w) - U Y| ≤
            |U (Y + hs • w) - layerProfile f (inner ℝ e (Y - X) - τc + T₀)| +
              |layerProfile f (inner ℝ e (Y - X) - τc + T₀) - U Y| := abs_sub_le _ _ _
        _ ≤ α + α := by rw [abs_sub_comm] at happY; exact add_le_add h1 happY
        _ = 2 * α := by ring
    have h3 : |hs * inner ℝ (gradient U Y) w| ≤ 2 * α + hs * εg := by
      rw [abs_le] at h2 hd ⊢
      constructor <;> linarith [h2.1, h2.2, hd.1, hd.2]
    rwa [abs_mul, abs_of_pos hs0] at h3
  · intro he lo hi c hinc hlo hhi
    have hd := hdq Y e hs he hs0.le hsδ hball
    have h1 := hshift e he
    have hinner : inner ℝ e (Y + hs • e - X) = inner ℝ e (Y - X) + hs := by
      rw [show Y + hs • e - X = (Y - X) + hs • e by abel, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq, he]
      ring
    rw [hinner, show inner ℝ e (Y - X) + hs - τc + T₀ = inner ℝ e (Y - X) - τc + T₀ + hs by
      ring] at h1
    have hq := hinc _ _ (by linarith) hlo hhi
    have hqd : layerProfile f (inner ℝ e (Y - X) - τc + T₀ + hs) -
        layerProfile f (inner ℝ e (Y - X) - τc + T₀) ≥ c * hs := by
      have : inner ℝ e (Y - X) - τc + T₀ + hs - (inner ℝ e (Y - X) - τc + T₀) = hs := by ring
      rw [this] at hq
      linarith
    rw [abs_le] at h1 happY hd
    linarith [h1.1, happY.2, hd.1]

/-- **Cone bound from gradient directions (mean value theorem).** If `U(P') = U(P)` and along the
segment `[P, P']` in the positive phase the normal derivative is at least `c₀ > 0` and the
tangential derivatives are at most `ε`, then `c₀ |⟪e, P' - P⟫| ≤ ε ‖(P' - P)^⊥‖`. -/
theorem Hypotheses.abs_inner_le_of_gradient_cone (h : Hypotheses g u f κ)
    {P P' e : Space (m + 1)} (he : ‖e‖ = 1) {c₀ ε : ℝ} (hc₀ : 0 < c₀)
    (hseg : ∀ θ ∈ Icc (0 : ℝ) 1, P + θ • (P' - P) ∈ epigraph g)
    (hnormal : ∀ θ ∈ Icc (0 : ℝ) 1,
      c₀ ≤ inner ℝ (gradient (zeroExtension g u) (P + θ • (P' - P))) e)
    (htan : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ w : Space (m + 1), inner ℝ e w = 0 →
      |inner ℝ (gradient (zeroExtension g u) (P + θ • (P' - P))) w| ≤ ε * ‖w‖)
    (heq : zeroExtension g u P' = zeroExtension g u P) :
    c₀ * |inner ℝ e (P' - P)| ≤ ε * ‖(P' - P) - inner ℝ e (P' - P) • e‖ := by
  set U := zeroExtension g u with hUdef
  have hepi : IsOpen (epigraph g) := isOpen_epigraph h.graph_contDiff.continuous
  have hdiff : ∀ θ ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ U (P + θ • (P' - P)) := fun θ hθ ↦
    (h.zeroExtension_contDiffOn.contDiffAt (hepi.mem_nhds (hseg θ hθ))).differentiableAt
      (by norm_num)
  set φ : ℝ → ℝ := fun θ ↦ U (P + θ • (P' - P)) with hφ
  have hline : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ ↦ P + θ • (P' - P)) (P' - P) θ := by
    intro θ
    simpa using ((hasDerivAt_id θ).smul_const (P' - P)).const_add P
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) 1,
      HasDerivAt φ (inner ℝ (gradient U (P + θ • (P' - P))) (P' - P)) θ := by
    intro θ hθ
    have h1 := (hdiff θ ⟨hθ.1.le, hθ.2.le⟩).hasFDerivAt.comp_hasDerivAt θ (hline θ)
    rw [← inner_gradient_left] at h1
    exact h1
  have hcont : ContinuousOn φ (Icc 0 1) := fun θ hθ ↦
    ((hdiff θ hθ).continuousAt.comp (f := fun θ : ℝ ↦ P + θ • (P' - P))
      (hline θ).continuousAt).continuousWithinAt
  have hends : φ 0 = φ 1 := by
    simp only [hφ, zero_smul, add_zero, one_smul, add_sub_cancel]
    exact heq.symm
  obtain ⟨θ, hθ, hzero⟩ := exists_hasDerivAt_eq_zero zero_lt_one hcont hends hderiv
  have hθ' : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ.1.le, hθ.2.le⟩
  set G := gradient U (P + θ • (P' - P)) with hG
  set a := inner ℝ e (P' - P) with ha
  set w := (P' - P) - a • e with hw
  have hew : inner ℝ e w = 0 := by
    rw [hw, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  have hsplit : inner ℝ G (P' - P) = a * inner ℝ G e + inner ℝ G w := by
    have : P' - P = a • e + w := by rw [hw]; abel
    rw [this, inner_add_right, inner_smul_right]
  rw [hzero] at hsplit
  have htw := htan θ hθ' w hew
  have hn := hnormal θ hθ'
  have hGe : 0 < inner ℝ G e := hc₀.trans_le hn
  have h2 : |inner ℝ G w| = |a| * inner ℝ G e := by
    rw [show inner ℝ G w = -(a * inner ℝ G e) by linarith, abs_neg, abs_mul, abs_of_pos hGe]
  have h3 : c₀ * |a| ≤ |a| * inner ℝ G e := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hn (abs_nonneg a)
  linarith [htw, h2, h3]

/-! ### The level cone condition -/

/-! ### Lines of the rotated rescaling -/

theorem rescaled_line_eq (x : Space (m + 1)) {R : ℝ} (hR : 0 < R)
    (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (y : Space m) (tA σ : ℝ) :
    x + R • Q (point y tA) + σ • Q (verticalDirection m) = x + R • Q (point y (tA + σ / R)) := by
  rw [← point_add_vertical, map_add, map_smul, smul_add, smul_smul,
    mul_div_cancel₀ _ hR.ne', add_assoc]

theorem rescaled_point_eq (x : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (y : Space m) (tA t : ℝ) :
    x + R • Q (point y t) = x + R • Q (point y tA) + (R * (t - tA)) • Q (verticalDirection m) := by
  have hp : point y t = point y tA + (t - tA) • verticalDirection m := by
    rw [point_add_vertical]
    congr 1
    ring
  rw [hp, map_add, map_smul, smul_add, smul_smul, ← add_assoc]

theorem rescaled_anchor_add (x : Space (m + 1)) (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    (A z : Space (m + 1)) : x + R • Q A + R • Q (z - A) = x + R • Q z := by
  rw [add_assoc, ← smul_add, ← map_add, add_sub_cancel]

theorem inner_rescaled_anchor (R : ℝ) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)) (y : Space m)
    (tA : ℝ) (z : Space (m + 1)) :
    inner ℝ (Q (verticalDirection m)) (R • Q (z - point y tA)) = R * (z (Fin.last m) - tA) := by
  rw [real_inner_smul_right, LinearIsometryEquiv.inner_map_map, real_inner_comm,
    inner_verticalDirection_right]
  simp [last_point]

theorem profile_arg_eq {R : ℝ} (hR : 0 < R) (a tA τc T : ℝ) :
    R * (a - tA) - τc + T = R * (a - (tA + τc / R - T / R)) := by
  field_simp
  ring

/-- **Orientation on a good line.** If, at an anchor in the thin layer, the translate crosses an
interior level downward in the microscopic window and exceeds it again at depth `K₂`, then the line
carries two crossings at a mesoscopic or macroscopic distance; the mesoscopic flatness and the
thin layer exclude both. -/
theorem Hypotheses.false_of_downward_line (h : Hypotheses g u f κ) {a b M ℓm ηf : ℝ}
    (hηf : ηf ≤ 1 / 4)
    (hflat : ∀ (X X' e : Space (m + 1)) (d : ℝ), ‖e‖ = 1 → M ≤ d →
      zeroExtension g u X ∈ Icc a b → zeroExtension g u X' ∈ Icc a b → ‖X' - X‖ ≤ d →
      ballTiltIntegral (zeroExtension g u) X e d < ℓm * d ^ m →
      |inner ℝ e (X' - X)| < ηf * d)
    {x : Space (m + 1)} {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    {y : Space m} {tA r₀ τ η s ℓ Wd T K₂ τ₁ τ₂ : ℝ}
    (hs : 0 < s) (hsab : s ∈ Icc a b) (hM : 0 < M)
    (htA : tA ∈ Ioo (-η) η) (hη : 0 < η) (hητ : η + K₂ / R < τ) (hηr : η ≤ r₀ / 8)
    (hWd : 0 ≤ Wd) (hTWd : T ≤ Wd) (hK₂ : 2 * Wd + M + 1 ≤ K₂) (h4T : 4 * T ≤ R * r₀)
    (hlow : ∀ t ∈ Ioo (-τ) τ, t ≤ -η → zeroExtension g u (x + R • Q (point y t)) = 0)
    (htilt : ∀ ρ ∈ Ioc 0 (R * r₀), ∫ z in ball (x + R • Q (point y tA)) ρ,
      diffuseTiltDensity 1 (zeroExtension g u) (Q (verticalDirection m)) z < ℓ * ρ ^ m)
    (hℓ : ℓ * 2 ^ m ≤ ℓm) (h1 : -Wd ≤ τ₁) (h2 : τ₁ < τ₂) (h3 : τ₂ ≤ T)
    (h4 : s < zeroExtension g u (x + R • Q (point y tA) + τ₁ • Q (verticalDirection m)))
    (h5 : zeroExtension g u (x + R • Q (point y tA) + τ₂ • Q (verticalDirection m)) < s)
    (h6 : s < zeroExtension g u (x + R • Q (point y tA) + (-K₂) • Q (verticalDirection m))) :
    False := by
  set U := zeroExtension g u with hUdef
  set e := Q (verticalDirection m) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, LinearIsometryEquiv.norm_map]; exact norm_verticalDirection m
  obtain ⟨X, hXdef⟩ : ∃ X, X = x + R • Q (point y tA) := ⟨_, rfl⟩
  rw [← hXdef] at h4 h5 h6 htilt
  have hUl : LocallyLipschitz U := h.zeroExtension_locallyLipschitz
  have hvc : Continuous (fun t ↦ U (x + R • Q (point y t))) :=
    (h.continuous_rescaled_translate x R Q).comp (continuous_point y)
  have hK₂0 : 0 ≤ K₂ := by linarith only [hK₂, hWd, hM]
  -- a crossing of `s` in the window
  have hcont : ContinuousOn (fun σ : ℝ ↦ U (X + σ • e)) (Icc τ₁ τ₂) :=
    (h.zeroExtension_continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  obtain ⟨σm, hσm, hσms'⟩ := intermediate_value_Icc' h2.le hcont ⟨h5.le, h4.le⟩
  have hσms : U (X + σm • e) = s := hσms'
  -- a crossing of `s` below the depth `K₂`
  obtain ⟨tb, htb⟩ : ∃ tb, tb = tA + (-K₂) / R := ⟨_, rfl⟩
  have htbeq : tb = tA - K₂ / R := by rw [htb]; ring
  have hK0 : 0 ≤ K₂ / R := by positivity
  have htbslab : tb ∈ Ioo (-τ) τ := by
    constructor
    · linarith only [htA.1, hητ, htbeq]
    · linarith only [htA.2, hK0, hητ, htbeq]
  have hvtb : s < U (x + R • Q (point y tb)) := by
    rw [htb, ← rescaled_line_eq x hR Q y tA (-K₂), ← hXdef]
    exact h6
  have htbη : -η < tb := by
    by_contra hn
    push Not at hn
    have := hlow tb htbslab hn
    linarith only [this, hvtb, hs]
  have hηslab : -η ∈ Ioo (-τ) τ := ⟨by linarith only [hητ, hK0], by linarith only [hη, hητ, hK0]⟩
  have hv0 : U (x + R • Q (point y (-η))) = 0 := hlow (-η) hηslab le_rfl
  obtain ⟨tl, htl, htls⟩ := intermediate_value_Icc htbη.le hvc.continuousOn
    ⟨by rw [hv0]; exact hs.le, hvtb.le⟩
  obtain ⟨σl, hσldef⟩ : ∃ σl, σl = R * (tl - tA) := ⟨_, rfl⟩
  have hσl : U (X + σl • e) = s := by
    rw [hXdef, hσldef, ← rescaled_point_eq]
    exact htls
  have hσlK : σl ≤ -K₂ := by
    have h1' : tl - tA ≤ -K₂ / R := by linarith only [htl.2, htb]
    have h2' := mul_le_mul_of_nonneg_left h1' hR.le
    rw [mul_div_cancel₀ _ hR.ne'] at h2'
    rw [hσldef]
    exact h2'
  obtain ⟨d, hddef⟩ : ∃ d, d = σm - σl := ⟨_, rfl⟩
  have hσm1 : -Wd ≤ σm := by linarith only [hσm.1, h1]
  have hσm2 : σm ≤ T := by linarith only [hσm.2, h3]
  have hσmW : |σm| ≤ Wd := abs_le.mpr ⟨hσm1, by linarith only [hσm2, hTWd]⟩
  have hd : Wd + M + 1 ≤ d := by linarith only [hddef, hσlK, hK₂, hσm1]
  have hdpos : 0 < d := by linarith only [hd, hWd, hM]
  rcases le_or_gt (2 * d) (R * r₀) with hdR | hdR
  · -- the mesoscopic flatness excludes two crossings on a line
    have hdiff : (X + σl • e) - (X + σm • e) = (σl - σm) • e := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]
    have hdist : ‖(X + σl • e) - (X + σm • e)‖ ≤ d := by
      rw [hdiff, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_nonpos (by linarith only [hdpos, hddef])]
      linarith only [hddef]
    have hti : ballTiltIntegral U (X + σm • e) e d < ℓm * d ^ m := by
      have hPX : ‖X + σm • e - X‖ < d := by
        rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs]
        linarith only [hσmW, hd, hM]
      have h1' := ballTiltIntegral_lt_of_anchor hUl he htilt hPX hdR
      calc ballTiltIntegral U (X + σm • e) e d < ℓ * (2 * d) ^ m := h1'
        _ = (ℓ * 2 ^ m) * d ^ m := by rw [mul_pow]; ring
        _ ≤ ℓm * d ^ m := mul_le_mul_of_nonneg_right hℓ (pow_nonneg hdpos.le m)
    have hfl := hflat (X + σm • e) (X + σl • e) e d he (by linarith only [hd, hWd])
      (by rw [hσms]; exact hsab) (by rw [hσl]; exact hsab) hdist hti
    rw [hdiff, inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one,
      abs_of_nonpos (by linarith only [hdpos, hddef])] at hfl
    have : ηf * d ≤ d / 4 := by nlinarith only [hηf, hdpos]
    linarith only [hfl, this, hdpos, hddef]
  · -- the thin layer excludes two distant crossings
    have h1' : d ≤ R * (2 * η) + T := by
      have htl' : -η ≤ tl := htl.1
      have e1 : d = R * (tA - tl) + σm := by rw [hddef, hσldef]; ring
      rw [e1]
      have : R * (tA - tl) ≤ R * (2 * η) :=
        mul_le_mul_of_nonneg_left (by linarith only [htA.2, htl']) hR.le
      linarith only [this, hσm2]
    have h2' : R * (2 * η) ≤ R * r₀ / 4 := by
      have := mul_le_mul_of_nonneg_left hηr hR.le
      linarith only [this]
    linarith only [h1', h2', h4T, hdR]

/-- **Localization of the level points on a good line (HA9.e).** If the translate is
`α`-close on `B̄_{K'}` about an anchor to the increasing layer profile, every crossing of an
interior level `s` on the anchor's line in the thin layer lies within `α / c_q` of the profile
position `τc - T₀ + T(s)`: nearby crossings by inverting the profile, mesoscopic ones by the
mesoscopic flatness, and distant ones by the thin layer. -/
theorem RigidityHypotheses.abs_sub_profile_le_of_line (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) {a b M ℓm ηf : ℝ} (hηf : ηf ≤ 1 / 4)
    (hflat : ∀ (X X' e : Space (m + 1)) (d : ℝ), ‖e‖ = 1 → M ≤ d →
      zeroExtension g u X ∈ Icc a b → zeroExtension g u X' ∈ Icc a b → ‖X' - X‖ ≤ d →
      ballTiltIntegral (zeroExtension g u) X e d < ℓm * d ^ m →
      |inner ℝ e (X' - X)| < ηf * d)
    {lo hi cq : ℝ} (hlo : 0 < lo) (hcq : 0 < cq)
    (hcqW : ∀ s ∈ Icc lo hi, cq ≤ Real.sqrt (2 * normalizedPotential f s))
    {x : Space (m + 1)} {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    {y : Space m} {tA τc T₀ r₀ η ℓ α K' W₀ M₁ s t : ℝ}
    (htA : tA ∈ Ioo (-η) η) (ht : t ∈ Ioo (-η) η) (hηr : η ≤ r₀ / 8)
    (h4W : 4 * W₀ ≤ R * r₀) (hMM₁ : M ≤ M₁) (hM₁W : W₀ + 3 ≤ M₁) (hK' : M₁ + W₀ ≤ K')
    (hW₀ : 0 ≤ W₀)
    (htilt : ∀ ρ ∈ Ioc 0 (R * r₀), ∫ z in ball (x + R • Q (point y tA)) ρ,
      diffuseTiltDensity 1 (zeroExtension g u) (Q (verticalDirection m)) z < ℓ * ρ ^ m)
    (hℓ : ℓ * 2 ^ m ≤ ℓm)
    (happrox : ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
      |zeroExtension g u (x + R • Q (point y tA) + Z) -
        layerProfile f (inner ℝ (Q (verticalDirection m)) Z - τc + T₀)| ≤ α)
    (hσs : |τc - T₀ + layerTravelTime f s| ≤ W₀)
    (hα0 : 0 ≤ α) (hs : s ∈ Ico (0 : ℝ) 1) (hslo : lo ≤ s - α) (hshi : s + α ≤ hi)
    (hsab : Icc (s - α) (s + α) ⊆ Icc a b)
    (hvt : zeroExtension g u (x + R • Q (point y t)) = s) :
    |R * (t - tA) - (τc - T₀ + layerTravelTime f s)| ≤ α / cq := by
  set U := zeroExtension g u with hUdef
  set e := Q (verticalDirection m) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, LinearIsometryEquiv.norm_map]; exact norm_verticalDirection m
  have hUl : LocallyLipschitz U := h.zeroExtension_locallyLipschitz
  obtain ⟨X, hXdef⟩ : ∃ X, X = x + R • Q (point y tA) := ⟨_, rfl⟩
  rw [← hXdef] at htilt happrox
  obtain ⟨σs, hσsdef⟩ : ∃ σs, σs = τc - T₀ + layerTravelTime f s := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = R * (t - tA) := ⟨_, rfl⟩
  rw [← hσsdef, ← hσdef]
  rw [← hσsdef] at hσs
  have hP : x + R • Q (point y t) = X + σ • e := by
    rw [hXdef, hσdef]
    exact rescaled_point_eq x R Q y tA t
  have hqs : layerProfile f (σs - τc + T₀) = s := by
    rw [show σs - τc + T₀ = layerTravelTime f s by rw [hσsdef]; ring]
    exact hr.layerProfile_travelTime h hs
  have hinner : ∀ c : ℝ, inner ℝ e (c • e) = c := fun c ↦ by
    rw [inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  rcases le_or_gt |σ - σs| M₁ with hd1 | hd1
  · -- microscopic: invert the profile
    have hmem : σ • e ∈ closedBall (0 : Space (m + 1)) K' := by
      rw [mem_closedBall, dist_zero_right, norm_smul, he, mul_one, Real.norm_eq_abs]
      have h1 : |σ| ≤ |σ - σs| + |σs| := by
        have := abs_sub_abs_le_abs_sub σ σs
        linarith only [this]
      linarith only [h1, hd1, hσs, hK']
    have happ := happrox (σ • e) hmem
    rw [← hP, hvt, hinner] at happ
    have hinv := hr.abs_sub_travelTime_le h hlo hcq hcqW hs hslo hshi
      (by rw [abs_sub_comm]; exact happ)
    rwa [show σ - τc + T₀ - layerTravelTime f s = σ - σs by rw [hσsdef]; ring] at hinv
  · exfalso
    have hdpos : 0 < |σ - σs| := lt_of_le_of_lt (by linarith only [hM₁W, hW₀]) hd1
    rcases le_or_gt (2 * |σ - σs|) (R * r₀) with hdR | hdR
    · -- the mesoscopic flatness excludes a second crossing on the line
      have hmems : σs • e ∈ closedBall (0 : Space (m + 1)) K' := by
        rw [mem_closedBall, dist_zero_right, norm_smul, he, mul_one, Real.norm_eq_abs]
        linarith only [hσs, hK', hM₁W, hW₀]
      have happ := happrox (σs • e) hmems
      rw [hinner, hqs, abs_le] at happ
      have hPs : U (X + σs • e) ∈ Icc a b :=
        hsab ⟨by linarith only [happ.1], by linarith only [happ.2]⟩
      have hPval : U (X + σ • e) ∈ Icc a b := by
        rw [← hP, hvt]
        exact hsab ⟨by linarith only [hα0], by linarith only [hα0]⟩
      have hdiff : (X + σ • e) - (X + σs • e) = (σ - σs) • e := by
        rw [add_sub_add_left_eq_sub, ← sub_smul]
      have hdist : ‖(X + σ • e) - (X + σs • e)‖ ≤ |σ - σs| := by
        rw [hdiff, norm_smul, he, mul_one, Real.norm_eq_abs]
      have hti : ballTiltIntegral U (X + σs • e) e |σ - σs| < ℓm * |σ - σs| ^ m := by
        have hPX : ‖X + σs • e - X‖ < |σ - σs| := by
          rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs]
          linarith only [hσs, hd1, hM₁W]
        have h1' := ballTiltIntegral_lt_of_anchor hUl he htilt hPX hdR
        calc ballTiltIntegral U (X + σs • e) e |σ - σs| < ℓ * (2 * |σ - σs|) ^ m := h1'
          _ = (ℓ * 2 ^ m) * |σ - σs| ^ m := by rw [mul_pow]; ring
          _ ≤ ℓm * |σ - σs| ^ m := mul_le_mul_of_nonneg_right hℓ (pow_nonneg hdpos.le m)
      have hfl := hflat (X + σs • e) (X + σ • e) e |σ - σs| he (hMM₁.trans hd1.le) hPs hPval
        hdist hti
      rw [hdiff, hinner] at hfl
      have : ηf * |σ - σs| ≤ |σ - σs| / 4 := by nlinarith only [hηf, hdpos]
      linarith only [hfl, this, hdpos]
    · -- the thin layer excludes a distant second crossing
      have h1 : |σ| ≤ R * (2 * η) := by
        rw [hσdef, abs_mul, abs_of_pos hR]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith only [ht.1, htA.2],
          by linarith only [ht.2, htA.1]⟩) hR.le
      have h2 : |σ - σs| ≤ R * (2 * η) + W₀ := by
        have := abs_sub σ σs
        linarith only [this, h1, hσs]
      have h3 : R * (2 * η) ≤ R * r₀ / 4 := by
        have := mul_le_mul_of_nonneg_left hηr hR.le
        linarith only [this]
      linarith only [h2, h3, h4W, hdR]

/-- **Gradient control near the level points.** Near a point `P` with an interior value `s`, inside
the window of an `α`-approximation by the increasing layer profile, the normal derivative of `U` is
at least `c_q / 2` and its tangential derivatives are at most `3 c_q L' / 8`. -/
theorem Hypotheses.gradient_control_of_profile (h : Hypotheses g u f κ) {rP εg δg : ℝ}
    (hdq : ∀ (Y w : Space (m + 1)) (t : ℝ), ‖w‖ = 1 → 0 ≤ t → t < δg →
      closedBall Y (rP + t) ⊆ epigraph g →
      |zeroExtension g u (Y + t • w) - zeroExtension g u Y -
        t * inner ℝ (gradient (zeroExtension g u) Y) w| ≤ t * εg)
    (hLip : ∀ a c : Space (m + 1), |zeroExtension g u a - zeroExtension g u c| ≤ κ * ‖a - c‖)
    {X e P Y : Space (m + 1)} {τc T₀ K' α hst cq L' s₁ s₂ s W δsm : ℝ}
    (happrox : ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
      |zeroExtension g u (X + Z) - layerProfile f (inner ℝ e Z - τc + T₀)| ≤ α)
    (hqinc : ∀ σ σ' : ℝ, σ ≤ σ' → s₁ / 4 ≤ layerProfile f σ →
      layerProfile f σ' ≤ (1 + s₂) / 2 → cq * (σ' - σ) ≤ layerProfile f σ' - layerProfile f σ)
    (he : ‖e‖ = 1) (hs : s ∈ Icc s₁ s₂) (hs₁ : 0 < s₁) (hcq : 0 < cq)
    (hL'1 : L' ≤ 1) (hκ : 0 < κ) (hUP : zeroExtension g u P = s) (hPX : ‖P - X‖ ≤ W)
    (hYP : ‖Y - P‖ ≤ δsm) (hK' : W + δsm + hst ≤ K') (hst0 : 0 < hst) (hstδ : hst < δg)
    (hκδ : κ * δsm ≤ min s₁ (1 - s₂) / 4) (hκrP : κ * rP ≤ s₁ / 8) (hκst1 : κ * hst ≤ s₁ / 8)
    (hκst2 : κ * hst ≤ (1 - s₂) / 8) (hα1 : α ≤ cq * L' * hst / 8) (hα3 : α ≤ s₁ / 8)
    (hα4 : α ≤ (1 - s₂) / 8) (hεg : εg = cq * L' / 8) :
    Y ∈ epigraph g ∧ cq / 2 ≤ inner ℝ (gradient (zeroExtension g u) Y) e ∧
      ∀ w : Space (m + 1), inner ℝ e w = 0 →
        |inner ℝ (gradient (zeroExtension g u) Y) w| ≤ 3 * cq * L' / 8 * ‖w‖ := by
  set U := zeroExtension g u with hUdef
  have hmin1 : min s₁ (1 - s₂) ≤ s₁ := min_le_left _ _
  have hmin2 : min s₁ (1 - s₂) ≤ 1 - s₂ := min_le_right _ _
  have hUY : 3 * s₁ / 4 ≤ U Y ∧ U Y ≤ (1 + 3 * s₂) / 4 := by
    have h1 := hLip Y P
    have h2 : κ * ‖Y - P‖ ≤ κ * δsm := mul_le_mul_of_nonneg_left hYP hκ.le
    rw [hUP, abs_le] at h1
    constructor
    · linarith only [h1.1, h2, hκδ, hmin1, hs.1]
    · linarith only [h1.2, h2, hκδ, hmin2, hs.2]
  have hYepi : Y ∈ epigraph g := (h.zeroExtension_pos_iff Y).mp (by linarith only [hUY.1, hs₁])
  have hball : closedBall Y (rP + hst) ⊆ epigraph g := by
    intro Z hZ
    apply (h.zeroExtension_pos_iff Z).mp
    have h1 := hLip Z Y
    rw [mem_closedBall, dist_eq_norm] at hZ
    have h2 : κ * ‖Z - Y‖ ≤ κ * (rP + hst) := mul_le_mul_of_nonneg_left hZ hκ.le
    rw [abs_le] at h1
    linarith only [h1.1, h2, hκrP, hκst1, hUY.1, hs₁]
  have hYX : ‖Y - X‖ + hst ≤ K' := by
    have : ‖Y - X‖ ≤ ‖Y - P‖ + ‖P - X‖ := by
      have := norm_add_le (Y - P) (P - X)
      rwa [sub_add_sub_cancel] at this
    linarith only [this, hYP, hPX, hK']
  obtain ⟨htan, hnormal⟩ := gradient_bounds_of_profile hdq happrox hYX hst0 hstδ hball
  refine ⟨hYepi, ?_, ?_⟩
  · -- the normal derivative
    have hmemY : Y - X ∈ closedBall (0 : Space (m + 1)) K' := by
      rw [mem_closedBall, dist_zero_right]
      linarith only [hYX, hst0]
    have happY := happrox (Y - X) hmemY
    rw [add_sub_cancel, abs_le] at happY
    have hmemY' : Y + hst • e - X ∈ closedBall (0 : Space (m + 1)) K' := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖Y + hst • e - X‖ = ‖(Y - X) + hst • e‖ := by congr 1; abel
        _ ≤ ‖Y - X‖ + ‖hst • e‖ := norm_add_le _ _
        _ = ‖Y - X‖ + hst := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hst0.le]
        _ ≤ K' := hYX
    have happY' := happrox _ hmemY'
    rw [add_sub_cancel] at happY'
    have hinner : inner ℝ e (Y + hst • e - X) = inner ℝ e (Y - X) + hst := by
      rw [show Y + hst • e - X = (Y - X) + hst • e by abel, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq, he]
      ring
    rw [hinner, show inner ℝ e (Y - X) + hst - τc + T₀ = inner ℝ e (Y - X) - τc + T₀ + hst by
      ring, abs_le] at happY'
    have hUY' : U (Y + hst • e) ≤ U Y + κ * hst := by
      have h1 := hLip (Y + hst • e) Y
      rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_of_nonneg hst0.le,
        abs_le] at h1
      linarith only [h1.2]
    have hb := hnormal he (lo := s₁ / 4) (hi := (1 + s₂) / 2) hqinc
      (by linarith only [happY.2, hUY.1, hα3, hs₁]) (by linarith only [happY'.1, hUY', hUY.2,
        hκst2, hα4])
    rw [hεg] at hb
    have hprod : cq * L' * hst ≤ cq * hst := by
      calc cq * L' * hst = (cq * hst) * L' := by ring
        _ ≤ (cq * hst) * 1 := mul_le_mul_of_nonneg_left hL'1 (by positivity)
        _ = cq * hst := mul_one _
    have hkey : cq / 2 * hst ≤ hst * inner ℝ (gradient U Y) e := by
      have hpos : 0 < cq * hst := mul_pos hcq hst0
      nlinarith only [hb, hα1, hprod, hpos]
    have hkey' : hst * (cq / 2) ≤ hst * inner ℝ (gradient U Y) e := by
      rw [mul_comm hst]
      exact hkey
    exact le_of_mul_le_mul_left hkey' hst0
  · -- the tangential derivatives
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      set w' := ‖w‖⁻¹ • w with hw'
      have hw'1 : ‖w'‖ = 1 := by
        rw [hw', norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hwn.le), inv_mul_cancel₀ hwn.ne']
      have hew' : inner ℝ e w' = 0 := by rw [hw', inner_smul_right, hw, mul_zero]
      have ha := htan w' hw'1 hew'
      rw [hεg] at ha
      have hbound : |inner ℝ (gradient U Y) w'| ≤ 3 * cq * L' / 8 := by
        have : hst * |inner ℝ (gradient U Y) w'| ≤ hst * (3 * cq * L' / 8) := by
          nlinarith only [ha, hα1]
        exact le_of_mul_le_mul_left this hst0
      have hww : w = ‖w‖ • w' := by
        rw [hw', smul_smul, mul_inv_cancel₀ hwn.ne', one_smul]
      have hinw : inner ℝ (gradient U Y) w = ‖w‖ * inner ℝ (gradient U Y) w' := by
        conv_lhs => rw [hww]
        rw [inner_smul_right]
      rw [hinw, abs_mul, abs_of_pos hwn, mul_comm]
      exact mul_le_mul_of_nonneg_right hbound hwn.le

/-- **The cone bound for a pair of level points (HA9.d).** Let `P` be a crossing of an interior
level `s` on the line of a good anchor, localized at the profile position, and `P'` any crossing
of `s` in the thin layer. Then `|t - t'| ≤ L' |y - y'|`: at sub-microscopic distances by the mean
value theorem and the gradient control, at microscopic distances by inverting the profile, at
mesoscopic distances by the mesoscopic flatness, and at macroscopic distances by the thin
layer. -/
theorem RigidityHypotheses.abs_sub_le_of_level_pair (h : Hypotheses g u f κ)
    {a b M ℓm L' : ℝ} (hL'0 : 0 < L') (hL'1 : L' ≤ 1)
    (hflat : ∀ (X X' e : Space (m + 1)) (d : ℝ), ‖e‖ = 1 → M ≤ d →
      zeroExtension g u X ∈ Icc a b → zeroExtension g u X' ∈ Icc a b → ‖X' - X‖ ≤ d →
      ballTiltIntegral (zeroExtension g u) X e d < ℓm * d ^ m →
      |inner ℝ e (X' - X)| < L' / 4 * d)
    {x : Space (m + 1)} {R : ℝ} (hR : 0 < R) (Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1))
    {y y' : Space m} {tA t t' τc T₀ r₀ η ℓ α K' W₀ M₁ s cq δsm σs : ℝ}
    (ht : t ∈ Ioo (-η) η) (ht' : t' ∈ Ioo (-η) η) (h8η : 8 * η ≤ L' * r₀)
    (hMM₁ : M ≤ M₁) (hM₁W : W₀ + 3 ≤ M₁) (hK' : M₁ + W₀ + 2 ≤ K')
    (htilt : ∀ ρ ∈ Ioc 0 (R * r₀), ∫ z in ball (x + R • Q (point y tA)) ρ,
      diffuseTiltDensity 1 (zeroExtension g u) (Q (verticalDirection m)) z < ℓ * ρ ^ m)
    (hℓ : ℓ * 2 ^ m ≤ ℓm)
    (happrox : ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
      |zeroExtension g u (x + R • Q (point y tA) + Z) -
        layerProfile f (inner ℝ (Q (verticalDirection m)) Z - τc + T₀)| ≤ α)
    (hσs : |σs| ≤ W₀) (hσP : |R * (t - tA) - σs| ≤ α / cq) (hαcq : α / cq ≤ 1)
    (hα2 : 2 * (α / cq) ≤ L' / 4 * δsm)
    (hinvert : ∀ σ : ℝ, |layerProfile f (σ - τc + T₀) - s| ≤ α → |σ - σs| ≤ α / cq)
    (hsab : s ∈ Icc a b)
    (hvt : zeroExtension g u (x + R • Q (point y t)) = s)
    (hvt' : zeroExtension g u (x + R • Q (point y' t')) = s)
    (hgrad : ∀ Y : Space (m + 1), ‖Y - (x + R • Q (point y t))‖ ≤ δsm →
      Y ∈ epigraph g ∧ cq / 2 ≤ inner ℝ (gradient (zeroExtension g u) Y) (Q (verticalDirection m)) ∧
        ∀ w : Space (m + 1), inner ℝ (Q (verticalDirection m)) w = 0 →
          |inner ℝ (gradient (zeroExtension g u) Y) w| ≤ 3 * cq * L' / 8 * ‖w‖)
    (hcq : 0 < cq) :
    |t - t'| ≤ L' * ‖y - y'‖ := by
  set U := zeroExtension g u with hUdef
  set e := Q (verticalDirection m) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, LinearIsometryEquiv.norm_map]; exact norm_verticalDirection m
  have hUl : LocallyLipschitz U := h.zeroExtension_locallyLipschitz
  obtain ⟨X, hXdef⟩ : ∃ X, X = x + R • Q (point y tA) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = x + R • Q (point y t) := ⟨_, rfl⟩
  obtain ⟨P', hP'def⟩ : ∃ P', P' = x + R • Q (point y' t') := ⟨_, rfl⟩
  rw [← hXdef] at htilt happrox
  rw [← hPdef] at hvt hgrad
  rw [← hP'def] at hvt'
  have hPline : P = X + (R * (t - tA)) • e := by
    rw [hPdef, hXdef, hedef]; exact rescaled_point_eq x R Q y tA t
  have hPX : ‖P - X‖ ≤ W₀ + 1 := by
    rw [hPline, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (R * (t - tA)) σs
    linarith only [this, hσP, hσs, hαcq]
  have hdist : ‖P' - P‖ = R * ‖point y' t' - point y t‖ := by
    rw [hPdef, hP'def]; exact norm_rescaled_sub hR x Q _ _
  have hinnerPP : inner ℝ e (P' - P) = R * (t' - t) := by
    rw [hPdef, hP'def, hedef, inner_rescaled_sub, last_point, last_point]
  have hpt : ‖point y t - point y' t'‖ = ‖point y' t' - point y t‖ := norm_sub_rev _ _
  -- the cone bound from a small inner product
  have hconv : |inner ℝ e (P' - P)| ≤ L' / 4 * ‖P' - P‖ → |t - t'| ≤ L' * ‖y - y'‖ := by
    intro hsmall
    rw [hinnerPP, hdist, abs_mul, abs_of_pos hR] at hsmall
    have h1 : |t - t'| ≤ L' / 4 * ‖point y t - point y' t'‖ := by
      rw [abs_sub_comm, hpt]
      have := (mul_le_mul_iff_right₀ hR).mp (by linarith only [hsmall] :
        R * |t' - t| ≤ R * (L' / 4 * ‖point y' t' - point y t‖))
      exact this
    have h2 := abs_sub_le_of_le_mul_norm (by positivity) (by linarith only [hL'1]) h1
    have h3 : 2 * (L' / 4) * ‖y - y'‖ ≤ L' * ‖y - y'‖ := by
      nlinarith only [norm_nonneg (y - y'), hL'0]
    linarith only [h2, h3]
  rcases lt_or_ge ‖P' - P‖ δsm with hd1 | hd1
  · -- sub-microscopic: the mean value theorem and the gradient control
    have hseg : ∀ θ ∈ Icc (0 : ℝ) 1, ‖P + θ • (P' - P) - P‖ ≤ δsm := by
      intro θ hθ
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hθ.1]
      calc θ * ‖P' - P‖ ≤ 1 * ‖P' - P‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ ≤ δsm := by linarith only [hd1]
    have hmv := h.abs_inner_le_of_gradient_cone he (c₀ := cq / 2) (ε := 3 * cq * L' / 8)
      (by positivity) (fun θ hθ ↦ (hgrad _ (hseg θ hθ)).1) (fun θ hθ ↦ (hgrad _ (hseg θ hθ)).2.1)
      (fun θ hθ ↦ (hgrad _ (hseg θ hθ)).2.2) (hvt'.trans hvt.symm)
    have horth : ‖(P' - P) - inner ℝ e (P' - P) • e‖ = R * ‖y' - y‖ := by
      rw [hPdef, hP'def, hedef]; exact norm_rescaled_sub_orth hR x Q y y' t t'
    rw [horth, hinnerPP, abs_mul, abs_of_pos hR, norm_sub_rev y' y] at hmv
    have h1 : cq / 2 * |t' - t| ≤ 3 * cq * L' / 8 * ‖y - y'‖ := by
      have := (mul_le_mul_iff_right₀ hR).mp (by nlinarith only [hmv, hR] :
        R * (cq / 2 * |t' - t|) ≤ R * (3 * cq * L' / 8 * ‖y - y'‖))
      exact this
    rw [abs_sub_comm] at h1
    have h2 : cq / 2 * |t - t'| ≤ cq / 2 * (L' * ‖y - y'‖) := by
      have hp := mul_nonneg (mul_nonneg hcq.le hL'0.le) (norm_nonneg (y - y'))
      linarith only [h1, hp]
    exact le_of_mul_le_mul_left h2 (by positivity)
  rcases lt_or_ge ‖P' - P‖ M₁ with hd2 | hd2
  · -- microscopic: invert the profile at both points
    apply hconv
    have hmem : P' - X ∈ closedBall (0 : Space (m + 1)) K' := by
      rw [mem_closedBall, dist_zero_right]
      have := norm_add_le (P' - P) (P - X)
      rw [sub_add_sub_cancel] at this
      linarith only [this, hd2, hPX, hK']
    have happ := happrox _ hmem
    rw [add_sub_cancel, hvt', abs_sub_comm] at happ
    have hinv' := hinvert _ happ
    have hsplit : inner ℝ e (P' - P) = (inner ℝ e (P' - X) - σs) - (R * (t - tA) - σs) := by
      rw [hPline]
      rw [show P' - (X + (R * (t - tA)) • e) = (P' - X) - (R * (t - tA)) • e by abel,
        inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he]
      ring
    rw [hsplit]
    have := abs_sub (inner ℝ e (P' - X) - σs) (R * (t - tA) - σs)
    have hδ : L' / 4 * δsm ≤ L' / 4 * ‖P' - P‖ := mul_le_mul_of_nonneg_left hd1 (by positivity)
    linarith only [this, hinv', hσP, hα2, hδ]
  rcases le_or_gt (2 * ‖P' - P‖) (R * r₀) with hd3 | hd3
  · -- mesoscopic: the mesoscopic flatness
    apply hconv
    have hti : ballTiltIntegral U P e ‖P' - P‖ < ℓm * ‖P' - P‖ ^ m := by
      have hPX' : ‖P - X‖ < ‖P' - P‖ := by linarith only [hPX, hd2, hM₁W]
      have h1' := ballTiltIntegral_lt_of_anchor hUl he htilt hPX' hd3
      have hpos : 0 ≤ ‖P' - P‖ := norm_nonneg _
      calc ballTiltIntegral U P e ‖P' - P‖ < ℓ * (2 * ‖P' - P‖) ^ m := h1'
        _ = (ℓ * 2 ^ m) * ‖P' - P‖ ^ m := by rw [mul_pow]; ring
        _ ≤ ℓm * ‖P' - P‖ ^ m := mul_le_mul_of_nonneg_right hℓ (pow_nonneg hpos m)
    exact (hflat P P' e ‖P' - P‖ he (hMM₁.trans hd2) (by rw [hvt]; exact hsab)
      (by rw [hvt']; exact hsab) le_rfl hti).le
  · -- macroscopic: the thin layer
    have hr₀ : 0 < r₀ := by
      have h1 : 0 < 8 * η := by linarith only [ht.1, ht.2]
      have h2 : 0 < L' * r₀ := lt_of_lt_of_le h1 h8η
      exact pos_of_mul_pos_right h2 hL'0.le
    have hfar : r₀ / 2 < ‖point y t - point y' t'‖ := by
      rw [hpt]
      have : R * r₀ < R * (2 * ‖point y' t' - point y t‖) := by
        have he2 : R * (2 * ‖point y' t' - point y t‖) = 2 * ‖P' - P‖ := by rw [hdist]; ring
        rw [he2]
        exact hd3
      have := (mul_lt_mul_iff_right₀ hR).mp this
      linarith only [this]
    have hsq : ‖point y t - point y' t'‖ ^ 2 = ‖y - y'‖ ^ 2 + (t - t') ^ 2 := by
      rw [point_sub_point_aux, norm_point_sq_aux]
    have htt : |t - t'| < 2 * η := by
      rw [abs_lt]
      constructor <;> linarith only [ht.1, ht.2, ht'.1, ht'.2]
    have hηr : η ≤ r₀ / 8 := by
      have := mul_le_mul_of_nonneg_right hL'1 hr₀.le
      linarith only [this, h8η]
    have hyy : r₀ / 4 < ‖y - y'‖ := by
      have h1 : (r₀ / 2) ^ 2 < ‖point y t - point y' t'‖ ^ 2 :=
        pow_lt_pow_left₀ hfar (by positivity) two_ne_zero
      have h2 : (t - t') ^ 2 < (2 * η) ^ 2 := by
        rw [← sq_abs]
        exact pow_lt_pow_left₀ htt (abs_nonneg _) two_ne_zero
      have h3 : (2 * η) ^ 2 ≤ (r₀ / 4) ^ 2 :=
        pow_le_pow_left₀ (by linarith only [ht.1, ht.2]) (by linarith only [hηr]) 2
      have h4 : (r₀ / 4) ^ 2 < ‖y - y'‖ ^ 2 := by nlinarith only [h1, h2, h3, hsq]
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h4
    have h1 : 2 * η ≤ L' * (r₀ / 4) := by linarith only [h8η]
    have h2 : L' * (r₀ / 4) ≤ L' * ‖y - y'‖ := mul_le_mul_of_nonneg_left hyy.le hL'0.le
    linarith only [htt, h1, h2]

/-- **HA9.d–HA9.e: the level cone condition, the microscopic slope and the profile approximation
on good lines.** For interior
levels `0 < s₁ ≤ s₂ < 1 - b₀` and a cone constant `L > 0` there are `ℓ, ρ₀, C_w, c > 0`,
independent of the center `x`, the scale `R` and the rotation `Q`, with the following property.
Let `v = U(x + R • Q ·)` and let `D` be a horizontal set each of whose lines carries a good point
(threshold `ℓ`, radii up to `r₀`, cut `b₀`) in the slab `|t| < τ`. Assume the slab facts on the
lines over `D`: `v` vanishes for `t ≤ -η` and exceeds `1 - β` for `t ≥ η` (`β ≤ b₀`), with
`8 η ≤ min L 1 · r₀`, `η + C_w / R < τ`, `ρ₀ ≤ R r₀` and `C_w ≤ R r₀`. Then the crossings of the
levels `[s₁, s₂]` over `D` in the slab satisfy the cone condition with constant `L`, the
diffuse vertical derivative `R⁻¹ ∂ₜ v` is at least `c` at each of them, and for given `α_A > 0`,
`K_A ≥ 0` every good point `p = (y, t_A)` over `D` in the slab is a center of `α_A`-approximation of
`v` on `B_{K_A / R}(p)` by `q(R (t - H(y)))`, `H(y) = h_{s₁}(y) - T(s₁) / R`, where
`h_{s₁} = slabLevelHeight v τ s₁` (HA10.a–b at good points). -/
theorem RigidityHypotheses.exists_hasLevelCone_and_profile (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {s₁ s₂ b₀ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂ : s₂ < 1 - b₀) (hb₀ : 0 < b₀)
    {L : ℝ≥0} (hL : 0 < L) {αA KA : ℝ} (hαA : 0 < αA) (hKA : 0 ≤ KA) :
    ∃ ℓ ρ₀ Cw c : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ 0 < Cw ∧ 0 < c ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ∀ (D : Set (Space m)) (r₀ τ η β : ℝ),
        ρ₀ ≤ R * r₀ → Cw ≤ R * r₀ → 0 < η → 8 * η ≤ min (L : ℝ) 1 * r₀ → η + Cw / R < τ →
        β ≤ b₀ →
        (∀ y ∈ D, ∃ t, |t| < τ ∧ IsLayerGoodPoint R (fun z ↦ zeroExtension g u (x + R • Q z))
          (verticalDirection m) ℓ r₀ b₀ (point y t)) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, t ≤ -η → zeroExtension g u (x + R • Q (point y t)) = 0) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, η ≤ t →
          1 - β < zeroExtension g u (x + R • Q (point y t))) →
        HasLevelCone (fun z ↦ zeroExtension g u (x + R • Q z)) D τ s₁ s₂ L ∧
        HasLevelSlope (fun z ↦ zeroExtension g u (x + R • Q z)) D τ s₁ s₂ R c ∧
        ∀ y ∈ D, ∀ tA : ℝ, |tA| < τ → IsLayerGoodPoint R
          (fun z ↦ zeroExtension g u (x + R • Q z)) (verticalDirection m) ℓ r₀ b₀ (point y tA) →
          ∀ z ∈ ball (point y tA) (KA / R),
            |zeroExtension g u (x + R • Q z) - layerProfile f (R * (z (Fin.last m) -
              (slabLevelHeight (fun z ↦ zeroExtension g u (x + R • Q z)) τ s₁ y -
                layerTravelTime f s₁ / R)))| ≤ αA := by
  have hκ := h.kappa_pos
  have hb₀1 : b₀ < 1 := by linarith
  have hs₂1 : s₂ < 1 := by linarith
  set L' : ℝ := min (L : ℝ) 1 with hL'
  have hL'0 : 0 < L' := lt_min (by exact_mod_cast hL) one_pos
  have hL'1 : L' ≤ 1 := min_le_right _ _
  have hL'L : L' ≤ L := min_le_left _ _
  -- the profile range and its slope
  set lo : ℝ := s₁ / 4 with hlo
  set hi : ℝ := (1 + s₂) / 2 with hhi
  have hlo0 : 0 < lo := by positivity
  have hlohi : lo ≤ hi := by rw [hlo, hhi]; linarith
  have hsubW : Icc lo hi ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hlo0.le (by rw [hhi]; linarith)
  obtain ⟨w₀, hw₀, hWmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlohi)
    (h.normalizedPotential_continuousOn.mono hsubW)
  have hWpos : 0 < normalizedPotential f w₀ :=
    hr.normalizedPotential_pos h (hlo0.le.trans hw₀.1) (by linarith [hw₀.2, hhi])
  set cq : ℝ := Real.sqrt (2 * normalizedPotential f w₀) with hcqdef
  have hcq : 0 < cq := Real.sqrt_pos.mpr (by positivity)
  have hcqW : ∀ s ∈ Icc lo hi, cq ≤ Real.sqrt (2 * normalizedPotential f s) := fun s hs ↦
    Real.sqrt_le_sqrt (by linarith [isMinOn_iff.mp hWmin s hs])
  have hqinc : ∀ σ σ' : ℝ, σ ≤ σ' → lo ≤ layerProfile f σ → layerProfile f σ' ≤ hi →
      cq * (σ' - σ) ≤ layerProfile f σ' - layerProfile f σ := fun σ σ' hle h1 h2 ↦
    hr.layerProfile_sub_ge h hlo0 hcqW hle h1 h2
  -- mesoscopic flatness
  obtain ⟨M, ℓm, hM, hℓm, hflat⟩ := hr.exists_mesoscopic_flatness h hsharp
    (a := s₁ / 2) (b := (1 + s₂) / 2) (by positivity) (by linarith) (η := L' / 4) (by positivity)
  -- travel times
  set T1 := layerTravelTime f (1 - b₀) with hT1def
  set Ts1 := layerTravelTime f s₁ with hTs1def
  set Ts2 := layerTravelTime f s₂ with hTs2def
  have hT1 : 0 ≤ T1 := hr.layerTravelTime_nonneg h ⟨by linarith, by linarith⟩
  have hTs1 : 0 ≤ Ts1 := hr.layerTravelTime_nonneg h ⟨hs₁.le, by linarith⟩
  have hTs : ∀ s ∈ Icc s₁ s₂, 0 ≤ layerTravelTime f s ∧ layerTravelTime f s ≤ Ts2 := by
    intro s hs
    exact ⟨hr.layerTravelTime_nonneg h ⟨hs₁.le.trans hs.1, by linarith [hs.2]⟩,
      (hr.layerTravelTime_strictMonoOn h).monotoneOn ⟨hs₁.le.trans hs.1, by linarith [hs.2]⟩
        ⟨hs₁.le.trans hs₁₂, hs₂1⟩ hs.2⟩
  have hTs2 : 0 ≤ Ts2 := (hTs s₂ ⟨hs₁₂, le_rfl⟩).1
  set W₀ : ℝ := T1 + Ts1 + Ts2 + 2 with hW₀
  set M₁ : ℝ := max M (W₀ + 3) with hM₁
  have hM₁M : M ≤ M₁ := le_max_left _ _
  have hM₁W : W₀ + 3 ≤ M₁ := le_max_right _ _
  -- the gradient modulus
  set rP : ℝ := s₁ / (8 * κ) with hrP
  set εg : ℝ := cq * L' / 8 with hεg
  obtain ⟨δg, hδg, hdq⟩ := hr.exists_gradient_difference_quotient h (r := rP) (by positivity)
    (ε := εg) (by positivity)
  set hst : ℝ := min (δg / 2) (min (s₁ / (8 * κ)) (min ((1 - s₂) / (8 * κ)) 1)) with hhst
  have hst0 : 0 < hst := lt_min (by positivity) (lt_min (by positivity)
    (lt_min (div_pos (by linarith) (by positivity)) one_pos))
  have hstδ : hst < δg := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hstA : hst ≤ s₁ / (8 * κ) := (min_le_right _ _).trans (min_le_left _ _)
  have hstB : hst ≤ (1 - s₂) / (8 * κ) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hst1 : hst ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hstκ1 : κ * hst ≤ s₁ / 8 := by
    calc κ * hst ≤ κ * (s₁ / (8 * κ)) := mul_le_mul_of_nonneg_left hstA hκ.le
      _ = s₁ / 8 := by field_simp
  have hstκ2 : κ * hst ≤ (1 - s₂) / 8 := by
    calc κ * hst ≤ κ * ((1 - s₂) / (8 * κ)) := mul_le_mul_of_nonneg_left hstB hκ.le
      _ = (1 - s₂) / 8 := by field_simp
  set δsm : ℝ := min 1 (min s₁ (1 - s₂) / (4 * κ)) with hδsm
  have hδsm0 : 0 < δsm := lt_min one_pos (div_pos (lt_min hs₁ (by linarith)) (by positivity))
  have hδsm1 : δsm ≤ 1 := min_le_left _ _
  have hδsmκ : κ * δsm ≤ min s₁ (1 - s₂) / 4 := by
    calc κ * δsm ≤ κ * (min s₁ (1 - s₂) / (4 * κ)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hκ.le
      _ = min s₁ (1 - s₂) / 4 := by field_simp
  set α : ℝ := min (min (cq * L' * hst / 8) (min (cq * L' * δsm / 8)
    (min (s₁ / 8) ((1 - s₂) / 8)))) αA with hαdef
  have hα0 : 0 < α := lt_min (lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by linarith)))) hαA
  have hαA' : α ≤ αA := min_le_right _ _
  have hα1 : α ≤ cq * L' * hst / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hα2 : α ≤ cq * L' * δsm / 8 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hα3 : α ≤ s₁ / 8 := (min_le_left _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hα4 : α ≤ (1 - s₂) / 8 := (min_le_left _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hαcq : α / cq ≤ 1 := by
    rw [div_le_one hcq]
    nlinarith [hα1, mul_le_mul_of_nonneg_left hL'1 hcq.le, hst1]
  -- the microscopic compactness
  set K' : ℝ := M₁ + W₀ + 4 + KA with hK'
  have hK'0 : 0 ≤ K' := by
    have : 0 ≤ M₁ + W₀ + 4 := by positivity
    linarith only [this, hKA, hK']
  set Wd : ℝ := K' + T1 + Ts1 + 3 with hWd
  set K₂ : ℝ := 2 * Wd + M₁ + 1 with hK₂
  obtain ⟨ℓμ, ρμ, hℓμ, hρμ, hdich⟩ := hr.exists_microscopic_oriented_dichotomy h hsharp
    (α := α) (K' := K') (b₀ := b₀) (s := s₁) (K₂ := K₂) hα0 hK'0 ⟨hb₀, hb₀1⟩
    ⟨hs₁, by linarith⟩ (by rw [hK₂, hWd]; linarith)
  rw [← hT1def, ← hTs1def] at hdich
  set ℓ : ℝ := min ℓμ (ℓm / 2 ^ m) with hℓdef
  have hℓ0 : 0 < ℓ := lt_min hℓμ (by positivity)
  set Cw : ℝ := 4 * (K₂ + W₀ + 2) with hCwdef
  have hCw0 : 0 < Cw := by positivity
  have hW₀0 : 0 ≤ W₀ := by positivity
  have hWd0 : 0 ≤ Wd := by
    have : 0 ≤ K' + T1 + Ts1 + 3 := by linarith only [hK'0, hT1, hTs1]
    linarith only [this, hWd]
  have hK₂0 : 0 ≤ K₂ := by
    have : 0 ≤ M₁ := by linarith only [hM₁W, hW₀0]
    linarith only [hK₂, hWd0, this]
  have hK'ge : M₁ + W₀ + 4 ≤ K' := by linarith only [hK', hKA]
  have hK'KA : KA ≤ K' := by
    have : 0 ≤ M₁ := by linarith only [hM₁W, hW₀0]
    linarith only [hK', this, hW₀0]
  have hℓ2 : ℓ * 2 ^ m ≤ ℓm := by
    have : ℓ ≤ ℓm / 2 ^ m := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  have hℓμ' : ℓ ≤ ℓμ := min_le_left _ _
  refine ⟨ℓ, ρμ, Cw, cq / 2, hℓ0, hρμ, hCw0, by positivity, ?_⟩
  clear_value L' lo hi cq T1 Ts1 Ts2 W₀ M₁ rP εg hst δsm α K' Wd K₂ ℓ Cw
  intro x R hR Q D r₀ τ η β hρR hCwR hη h8η hητ hβ hgood hlow hhigh
  set U := zeroExtension g u with hUdef
  set e := Q (verticalDirection m) with hedef
  have he : ‖e‖ = 1 := by rw [hedef, LinearIsometryEquiv.norm_map]; exact norm_verticalDirection m
  have hvc : Continuous (fun z ↦ U (x + R • Q z)) := h.continuous_rescaled_translate x R Q
  have hUl : LocallyLipschitz U := h.zeroExtension_locallyLipschitz
  have hUlip : ∀ a c : Space (m + 1), |U a - U c| ≤ κ * ‖a - c‖ := fun a c ↦ by
    have := (hr.zeroExtension_lipschitzWith h).dist_le_mul a c
    rwa [Real.dist_eq, dist_eq_norm] at this
  have hr₀ : 0 < r₀ := by
    have h1 : 0 < R * r₀ := hCw0.trans_le hCwR
    exact pos_of_mul_pos_right h1 hR.le
  have hηr : η ≤ r₀ / 8 := by
    have := mul_le_mul_of_nonneg_right hL'1 hr₀.le
    linarith
  have hCwR' : Cw / R ≤ r₀ := by rw [div_le_iff₀ hR]; linarith
  have hητ' : η < τ := by
    have : 0 < Cw / R := by positivity
    linarith
  -- crossings with values in `(0, 1 - b₀)` lie in the thin layer
  have hthin : ∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, 0 < U (x + R • Q (point y t)) →
      U (x + R • Q (point y t)) < 1 - b₀ → t ∈ Ioo (-η) η := by
    intro y hy t ht h0 h1
    constructor
    · by_contra hn
      push Not at hn
      have := hlow y hy t ht hn
      linarith only [this, h0]
    · by_contra hn
      push Not at hn
      have := hhigh y hy t ht hn
      linarith only [this, h1, hβ]
  -- the line through a point of `D`
  have hline : ∀ (y : Space m) (tA σ : ℝ),
      U (x + R • Q (point y tA) + σ • e) = U (x + R • Q (point y (tA + σ / R))) := by
    intro y tA σ
    rw [hedef, ← point_add_vertical, map_add, map_smul, smul_add, smul_smul,
      mul_div_cancel₀ _ hR.ne', add_assoc]
  have hlineP : ∀ (y : Space m) (tA t : ℝ),
      x + R • Q (point y t) = x + R • Q (point y tA) + (R * (t - tA)) • e := by
    intro y tA t
    have hp : point y t = point y tA + (t - tA) • verticalDirection m := by
      rw [point_add_vertical]
      congr 1
      ring
    rw [hp, map_add, map_smul, smul_add, smul_smul, ← add_assoc, hedef]
  -- per-line analysis at a good anchor: the profile is oriented and approximates `U`
  have hana' : ∀ y ∈ D, ∀ tA : ℝ, |tA| < τ → IsLayerGoodPoint R (fun z ↦ U (x + R • Q z))
      (verticalDirection m) ℓ r₀ b₀ (point y tA) → ∃ τc : ℝ, tA ∈ Ioo (-η) η ∧
      τc ∈ Icc (-(T1 + 1)) (Ts1 + 1) ∧
      (∀ ρ ∈ Ioc 0 (R * r₀), ∫ z in ball (x + R • Q (point y tA)) ρ,
        diffuseTiltDensity 1 U e z < ℓ * ρ ^ m) ∧
      (∀ Z ∈ closedBall (0 : Space (m + 1)) K',
        |U (x + R • Q (point y tA) + Z) - layerProfile f (inner ℝ e Z - τc + Ts1)| ≤ α) ∧
      U (x + R • Q (point y tA) + τc • e) = s₁ := by
    intro y hy tA htA hA
    set X := x + R • Q (point y tA) with hXdef
    have hUX : U X ∈ Ioo 0 (1 - b₀) := hA.1
    have htilt : ∀ ρ ∈ Ioc 0 (R * r₀), ∫ z in ball X ρ, diffuseTiltDensity 1 U e z < ℓ * ρ ^ m :=
      fun ρ hρ ↦ physical_tilt_lt_of_isLayerGoodPoint_rotated hR Q hA hρ.1 hρ.2
    have htAη : tA ∈ Ioo (-η) η := hthin y hy tA (abs_lt.mp htA) hUX.1 hUX.2
    have htiltμ : ∀ ρ ∈ Ioc 0 ρμ, ∫ z in ball X ρ, diffuseTiltDensity 1 U e z < ℓμ * ρ ^ m :=
      fun ρ hρ ↦ (htilt ρ ⟨hρ.1, hρ.2.trans hρR⟩).trans_le
        (mul_le_mul_of_nonneg_right hℓμ' (pow_nonneg hρ.1.le m))
    rcases hdich X e he hUX htiltμ with ⟨τ₁, τ₂, h1, h2, h3, h4, h5, h6⟩ |
      ⟨⟨τc, hτc, hτcs⟩, happrox⟩
    · have hK₂R : K₂ / R ≤ Cw / R :=
        div_le_div_of_nonneg_right (by linarith only [hCwdef, hK₂0, hW₀0]) hR.le
      have hWdT1 : T1 ≤ Wd := by linarith only [hWd, hK'0, hTs1]
      exact (h.false_of_downward_line (a := s₁ / 2) (b := (1 + s₂) / 2) (ηf := L' / 4)
        (by linarith only [hL'1]) hflat hR Q (s := s₁) hs₁ ⟨by linarith only [hs₁],
          by linarith only [hs₁₂, hs₂1]⟩ hM htAη hη (by linarith only [hητ, hK₂R]) hηr hWd0
        hWdT1 (by linarith only [hK₂, hM₁M]) (by linarith only [hCwdef, hK₂0, hW₀, hTs1, hTs2,
          hCwR]) (hlow y hy) htilt hℓ2 (by linarith only [h1, hWd]) h2 h3 h4 h5 h6).elim
    · exact ⟨τc, htAη, hτc, htilt, happrox τc hτc hτcs, hτcs⟩
  have hana : ∀ y ∈ D, ∃ tA τc : ℝ, tA ∈ Ioo (-η) η ∧ τc ∈ Icc (-(T1 + 1)) (Ts1 + 1) ∧
      (∀ ρ ∈ Ioc 0 (R * r₀), ∫ z in ball (x + R • Q (point y tA)) ρ,
        diffuseTiltDensity 1 U e z < ℓ * ρ ^ m) ∧
      ∀ Z ∈ closedBall (0 : Space (m + 1)) K',
        |U (x + R • Q (point y tA) + Z) - layerProfile f (inner ℝ e Z - τc + Ts1)| ≤ α := by
    intro y hy
    obtain ⟨tA, htA, hA⟩ := hgood y hy
    obtain ⟨τc, h1, h2, h3, h4, -⟩ := hana' y hy tA htA hA
    exact ⟨tA, τc, h1, h2, h3, h4⟩
  -- profile positions of the levels and their bounds
  have hσsW : ∀ τc : ℝ, τc ∈ Icc (-(T1 + 1)) (Ts1 + 1) → ∀ s ∈ Icc s₁ s₂,
      |τc - Ts1 + layerTravelTime f s| ≤ W₀ := by
    intro τc hτc s hs
    have hTsS := hTs s hs
    exact abs_le.mpr ⟨by linarith only [hτc.1, hTsS.1, hW₀, hTs1, hTs2],
      by linarith only [hτc.2, hTsS.2, hW₀, hT1, hTs1]⟩
  have hs01 : ∀ s ∈ Icc s₁ s₂, s ∈ Ico (0 : ℝ) 1 := fun s hs ↦
    ⟨by linarith only [hs.1, hs₁], by linarith only [hs.2, hs₂1]⟩
  have hslo : ∀ s ∈ Icc s₁ s₂, lo ≤ s - α := fun s hs ↦ by
    linarith only [hs.1, hlo, hα3, hs₁]
  have hshi : ∀ s ∈ Icc s₁ s₂, s + α ≤ hi := fun s hs ↦ by
    linarith only [hs.2, hhi, hα4, hs₂1]
  have hthin_s : ∀ y ∈ D, ∀ s ∈ Icc s₁ s₂, ∀ t ∈ Ioo (-τ) τ, U (x + R • Q (point y t)) = s →
      t ∈ Ioo (-η) η := fun y hy s hs t ht hvt ↦ hthin y hy t ht
    (by rw [hvt]; linarith only [hs.1, hs₁]) (by rw [hvt]; linarith only [hs.2, hs₂])
  have hsab : ∀ s ∈ Icc s₁ s₂, Icc (s - α) (s + α) ⊆ Icc (s₁ / 2) ((1 + s₂) / 2) :=
    fun s hs z hz ↦ ⟨by linarith only [hz.1, hs.1, hα3, hs₁],
      by linarith only [hz.2, hs.2, hα4, hs₂1]⟩
  have h4W : 4 * W₀ ≤ R * r₀ := by linarith only [hCwdef, hK₂0, hCwR]
  have hκrP : κ * rP ≤ s₁ / 8 := le_of_eq (by rw [hrP]; field_simp)
  -- the localization of a level point at its anchor's profile position
  have hlocal : ∀ y ∈ D, ∀ tA τc : ℝ, tA ∈ Ioo (-η) η → τc ∈ Icc (-(T1 + 1)) (Ts1 + 1) →
      (∀ ρ ∈ Ioc 0 (R * r₀), ∫ z in ball (x + R • Q (point y tA)) ρ,
        diffuseTiltDensity 1 U e z < ℓ * ρ ^ m) →
      (∀ Z ∈ closedBall (0 : Space (m + 1)) K',
        |U (x + R • Q (point y tA) + Z) - layerProfile f (inner ℝ e Z - τc + Ts1)| ≤ α) →
      ∀ s ∈ Icc s₁ s₂, ∀ t ∈ Ioo (-τ) τ, U (x + R • Q (point y t)) = s →
        |R * (t - tA) - (τc - Ts1 + layerTravelTime f s)| ≤ α / cq := by
    intro y hy tA τc htA hτc htilt happrox s hs t ht hvt
    exact hr.abs_sub_profile_le_of_line h (ηf := L' / 4) (by linarith only [hL'1]) hflat hlo0 hcq
      hcqW hR Q htA (hthin_s y hy s hs t ht hvt) hηr h4W hM₁M hM₁W
      (by linarith only [hK'ge]) hW₀0 htilt hℓ2 happrox (hσsW τc hτc s hs) hα0.le (hs01 s hs)
      (hslo s hs) (hshi s hs) (hsab s hs) hvt
  -- gradient control near a localized level point
  have hgradAt : ∀ (y : Space m) (tA τc t s : ℝ), s ∈ Icc s₁ s₂ →
      (∀ Z ∈ closedBall (0 : Space (m + 1)) K',
        |U (x + R • Q (point y tA) + Z) - layerProfile f (inner ℝ e Z - τc + Ts1)| ≤ α) →
      U (x + R • Q (point y t)) = s →
      ‖x + R • Q (point y t) - (x + R • Q (point y tA))‖ ≤ W₀ + 1 →
      ∀ Y : Space (m + 1), ‖Y - (x + R • Q (point y t))‖ ≤ δsm →
        Y ∈ epigraph g ∧ cq / 2 ≤ inner ℝ (gradient U Y) e ∧
          ∀ w : Space (m + 1), inner ℝ e w = 0 →
            |inner ℝ (gradient U Y) w| ≤ 3 * cq * L' / 8 * ‖w‖ := by
    intro y tA τc t s hs happrox hvt hPX Y hY
    exact h.gradient_control_of_profile hdq hUlip happrox
      (fun σ σ' hle h1 h2 ↦ hqinc σ σ' hle (by rw [hlo]; exact h1) (by rw [hhi]; exact h2))
      he hs hs₁ hcq hL'1 hκ hvt hPX hY (by linarith only [hK'ge, hM₁W, hδsm1, hst1, hW₀0])
      hst0 hstδ hδsmκ hκrP hstκ1 hstκ2 hα1 hα3 hα4 hεg
  have hPX : ∀ (y : Space m) (tA τc t s : ℝ), s ∈ Icc s₁ s₂ →
      τc ∈ Icc (-(T1 + 1)) (Ts1 + 1) →
      |R * (t - tA) - (τc - Ts1 + layerTravelTime f s)| ≤ α / cq →
      ‖x + R • Q (point y t) - (x + R • Q (point y tA))‖ ≤ W₀ + 1 := by
    intro y tA τc t s hs hτc hloc
    rw [rescaled_point_eq x R Q y tA t, add_sub_cancel_left, norm_smul, ← hedef, he, mul_one,
      Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (R * (t - tA)) (τc - Ts1 + layerTravelTime f s)
    linarith only [this, hloc, hσsW τc hτc s hs, hαcq]
  have hcone : HasLevelCone (fun z ↦ U (x + R • Q z)) D τ s₁ s₂ L := by
    intro s hs y hy y' hy' t ht t' ht' hvt hvt'
    change U (x + R • Q (point y t)) = s at hvt
    change U (x + R • Q (point y' t')) = s at hvt'
    rw [dist_eq_norm]
    obtain ⟨tA, τc, htA, hτc, htilt, happrox⟩ := hana y hy
    have hloc := hlocal y hy tA τc htA hτc htilt happrox s hs t ht hvt
    have hpair := RigidityHypotheses.abs_sub_le_of_level_pair h hL'0 hL'1 hflat hR Q
      (hthin_s y hy s hs t ht hvt) (hthin_s y' hy' s hs t' ht' hvt') h8η hM₁M hM₁W
      (by linarith only [hK'ge]) htilt hℓ2 happrox (hσsW τc hτc s hs) hloc hαcq
      (by rw [show 2 * (α / cq) = 2 * α / cq by ring, div_le_iff₀ hcq]
          linarith only [hα2])
      (fun σ hσ ↦ by
        have := hr.abs_sub_travelTime_le h hlo0 hcq hcqW (hs01 s hs) (hslo s hs) (hshi s hs) hσ
        rwa [show σ - τc + Ts1 - layerTravelTime f s = σ - (τc - Ts1 + layerTravelTime f s) by
          ring] at this)
      (hsab s hs ⟨by linarith only [hα0], by linarith only [hα0]⟩) hvt hvt'
      (hgradAt y tA τc t s hs happrox hvt (hPX y tA τc t s hs hτc hloc)) hcq
    exact hpair.trans (mul_le_mul_of_nonneg_right hL'L (norm_nonneg _))
  refine ⟨hcone, ?_, ?_⟩
  · -- the microscopic slope
    intro s hs y hy t ht hvt
    change U (x + R • Q (point y t)) = s at hvt
    obtain ⟨tA, τc, htA, hτc, htilt, happrox⟩ := hana y hy
    have hloc := hlocal y hy tA τc htA hτc htilt happrox s hs t ht hvt
    have hg := hgradAt y tA τc t s hs happrox hvt (hPX y tA τc t s hs hτc hloc)
      (x + R • Q (point y t)) (by rw [sub_self, norm_zero]; exact hδsm0.le)
    have hvd : verticalDerivative (fun z ↦ U (x + R • Q z)) (point y t) =
        R * inner ℝ (gradient U (x + R • Q (point y t))) e := by
      rw [verticalDerivative, ← inner_gradient_left, gradient_comp_translate_dilation_isometry,
        real_inner_smul_left, LinearIsometryEquiv.inner_map_eq_flip,
        LinearIsometryEquiv.symm_symm]
    rw [hvd, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
    exact hg.2.1
  · -- the profile approximation at good anchors, around the chosen level height
    intro y hy tA htA hA z hz
    obtain ⟨τc, htAη, hτc, -, happrox, hτcs⟩ := hana' y hy tA htA hA
    have hτcW : |τc| ≤ W₀ := abs_le.mpr ⟨by linarith only [hτc.1, hW₀, hTs1, hTs2],
      by linarith only [hτc.2, hW₀, hT1, hTs2]⟩
    have hτcR : |τc / R| ≤ Cw / R := by
      rw [abs_div, abs_of_pos hR]
      exact div_le_div_of_nonneg_right (by linarith only [hτcW, hCwdef, hK₂0, hW₀0]) hR.le
    have hτcslab : tA + τc / R ∈ Ioo (-τ) τ := by
      rw [abs_le] at hτcR
      constructor <;> linarith only [htAη.1, htAη.2, hτcR.1, hτcR.2, hητ]
    have hvc : (fun z ↦ U (x + R • Q z)) (point y (tA + τc / R)) = s₁ := by
      change U (x + R • Q (point y (tA + τc / R))) = s₁
      rw [← rescaled_line_eq x hR Q y tA τc]
      exact hτcs
    obtain ⟨hHmem, hHval⟩ := slabLevelHeight_spec (v := fun z ↦ U (x + R • Q z)) (y := y)
      ⟨_, hτcslab, hvc⟩
    have hHeq : slabLevelHeight (fun z ↦ U (x + R • Q z)) τ s₁ y = tA + τc / R := by
      have hc := hcone s₁ ⟨le_rfl, hs₁₂⟩ y hy y hy _ hHmem _ hτcslab hHval hvc
      rw [dist_self, mul_zero] at hc
      have := abs_nonpos_iff.mp hc
      linarith only [this]
    have hZ : R • Q (z - point y tA) ∈ closedBall (0 : Space (m + 1)) K' := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hR.le,
        LinearIsometryEquiv.norm_map]
      rw [mem_ball, dist_eq_norm, lt_div_iff₀ hR] at hz
      linarith only [hz, hK'KA, mul_comm R ‖z - point y tA‖]
    have happ := happrox _ hZ
    rw [rescaled_anchor_add, hedef, inner_rescaled_anchor, profile_arg_eq hR] at happ
    rw [hHeq]
    exact happ.trans hαA'

/-- **HA9.d: the level cone condition and the microscopic slope on good lines.** The cone and
slope part of `RigidityHypotheses.exists_hasLevelCone_and_profile`. -/
theorem RigidityHypotheses.exists_hasLevelCone (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {s₁ s₂ b₀ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂ : s₂ < 1 - b₀) (hb₀ : 0 < b₀)
    {L : ℝ≥0} (hL : 0 < L) :
    ∃ ℓ ρ₀ Cw c : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ 0 < Cw ∧ 0 < c ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ∀ (D : Set (Space m)) (r₀ τ η β : ℝ),
        ρ₀ ≤ R * r₀ → Cw ≤ R * r₀ → 0 < η → 8 * η ≤ min (L : ℝ) 1 * r₀ → η + Cw / R < τ →
        β ≤ b₀ →
        (∀ y ∈ D, ∃ t, |t| < τ ∧ IsLayerGoodPoint R (fun z ↦ zeroExtension g u (x + R • Q z))
          (verticalDirection m) ℓ r₀ b₀ (point y t)) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, t ≤ -η → zeroExtension g u (x + R • Q (point y t)) = 0) →
        (∀ y ∈ D, ∀ t ∈ Ioo (-τ) τ, η ≤ t →
          1 - β < zeroExtension g u (x + R • Q (point y t))) →
        HasLevelCone (fun z ↦ zeroExtension g u (x + R • Q z)) D τ s₁ s₂ L ∧
        HasLevelSlope (fun z ↦ zeroExtension g u (x + R • Q z)) D τ s₁ s₂ R c := by
  obtain ⟨ℓ, ρ₀, Cw, c, hℓ, hρ₀, hCw, hc, hmain⟩ :=
    hr.exists_hasLevelCone_and_profile h hsharp hs₁ hs₁₂ hs₂ hb₀ hL one_pos le_rfl
      (αA := 1) (KA := 0)
  refine ⟨ℓ, ρ₀, Cw, c, hℓ, hρ₀, hCw, hc, ?_⟩
  intro x R hR Q D r₀ τ η β hρR hCwR hη h8η hητ hβ hgood hlow hhigh
  obtain ⟨h1, h2, -⟩ := hmain x R hR Q D r₀ τ η β hρR hCwR hη h8η hητ hβ hgood hlow hhigh
  exact ⟨h1, h2⟩

/-! ### Sequences with vertical planar layers (HA8) -/

/-- **HA8 slab facts on lines.** For vertical planar layers, eventually every vertical line over
`B_ρ` vanishes in the slab below `-η` and exceeds `1 - β` above `η`. -/
theorem VerticalPlanarLayers.eventually_slab_facts {v : ℕ → Space (m + 1) → ℝ}
    (hV : VerticalPlanarLayers v) {ρ τ η β : ℝ} (hη : 0 < η) (hβ : 0 < β) :
    ∀ᶠ j in atTop, ∀ y : Space m, ‖y‖ < ρ → ∀ t ∈ Ioo (-τ) τ,
      (t ≤ -η → v j (point y t) = 0) ∧ (η ≤ t → 1 - β < v j (point y t)) := by
  filter_upwards [hV.lower (ρ + τ) η hη, hV.upper (ρ + τ) η β hη hβ] with j hlow hup
  intro y hy t ht
  have hmem : point y t ∈ closedBall (0 : Space (m + 1)) (ρ + τ) := by
    rw [mem_closedBall, dist_zero_right]
    have := norm_point_le y t
    have : |t| < τ := abs_lt.mpr ⟨ht.1, ht.2⟩
    linarith
  refine ⟨fun hlo ↦ hlow _ hmem (by rwa [last_point]), fun hhi ↦ hup _ hmem (by rwa [last_point])⟩

/-- **HA9.d along planar-layer sequences.** There are `ℓ₀, c > 0` such that for every threshold
`ℓ ∈ (0, ℓ₀]`, along every sequence of rotated rescalings `v_j = U(x_j + R_j • Q_j ·)` with
`R_j → ∞` and vertical planar layers (HA8, e.g. from `verticalPlanarLayers_of_rotated`), and all
`r₀, τ > 0`, eventually the cone condition with constant `L` and the slope bound `c` hold on the
lines over `B_ρ` carrying a good point in the slab `|t| < τ`. -/
theorem RigidityHypotheses.eventually_hasLevelCone_of_planarLayers (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {s₁ s₂ b₀ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂ : s₂ < 1 - b₀) (hb₀ : 0 < b₀)
    {L : ℝ≥0} (hL : 0 < L) :
    ∃ ℓ₀ c : ℝ, 0 < ℓ₀ ∧ 0 < c ∧ ∀ ℓ ∈ Ioc 0 ℓ₀,
      ∀ (x : ℕ → Space (m + 1)) (R : ℕ → ℝ) (Q : ℕ → Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1)),
        (∀ j, 0 < R j) → Tendsto R atTop atTop →
        VerticalPlanarLayers (fun j z ↦ zeroExtension g u (x j + R j • Q j z)) →
        ∀ r₀ τ ρ : ℝ, 0 < r₀ → 0 < τ → ∀ᶠ j in atTop,
          HasLevelCone (fun z ↦ zeroExtension g u (x j + R j • Q j z))
            {y | ‖y‖ < ρ ∧ ∃ t, |t| < τ ∧ IsLayerGoodPoint (R j)
              (fun z ↦ zeroExtension g u (x j + R j • Q j z)) (verticalDirection m) ℓ r₀ b₀
                (point y t)} τ s₁ s₂ L ∧
          HasLevelSlope (fun z ↦ zeroExtension g u (x j + R j • Q j z))
            {y | ‖y‖ < ρ ∧ ∃ t, |t| < τ ∧ IsLayerGoodPoint (R j)
              (fun z ↦ zeroExtension g u (x j + R j • Q j z)) (verticalDirection m) ℓ r₀ b₀
                (point y t)} τ s₁ s₂ (R j) c := by
  obtain ⟨ℓ₀, ρ₀, Cw, c, hℓ₀, hρ₀, hCw, hc, hmain⟩ :=
    hr.exists_hasLevelCone h hsharp hs₁ hs₁₂ hs₂ hb₀ hL
  refine ⟨ℓ₀, c, hℓ₀, hc, ?_⟩
  intro ℓ hℓ x R Q hR hRt hV r₀ τ ρ hr₀ hτ
  set L' : ℝ := min (L : ℝ) 1 with hL'
  have hL'0 : 0 < L' := lt_min (by exact_mod_cast hL) one_pos
  set η : ℝ := min (L' * r₀ / 8) (τ / 2) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have h8η : 8 * η ≤ L' * r₀ := by
    have := min_le_left (L' * r₀ / 8) (τ / 2)
    linarith
  have hητ : η ≤ τ / 2 := min_le_right _ _
  have hR1 : ∀ᶠ j in atTop, max ρ₀ Cw ≤ R j * r₀ := by
    have := (hRt.atTop_mul_const hr₀).eventually_ge_atTop (max ρ₀ Cw)
    exact this
  have hR2 : ∀ᶠ j in atTop, Cw / R j < τ / 2 := by
    have hlim : Tendsto (fun j ↦ Cw / R j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hRt
    exact hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hR1, hR2, hV.eventually_slab_facts (ρ := ρ) (τ := τ) hη hb₀] with j hj1 hj2 hj3
  have hgood : ∀ y ∈ {y : Space m | ‖y‖ < ρ ∧ ∃ t, |t| < τ ∧ IsLayerGoodPoint (R j)
      (fun z ↦ zeroExtension g u (x j + R j • Q j z)) (verticalDirection m) ℓ r₀ b₀ (point y t)},
      ∃ t, |t| < τ ∧ IsLayerGoodPoint (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z))
        (verticalDirection m) ℓ₀ r₀ b₀ (point y t) := by
    rintro y ⟨-, t, ht, hgt⟩
    have hmem : point y t ∈ layerGoodSet (R j) (fun z ↦ zeroExtension g u (x j + R j • Q j z))
        (verticalDirection m) ℓ r₀ b₀ := hgt
    exact ⟨t, ht, layerGoodSet_mono hℓ.2 le_rfl le_rfl hmem⟩
  exact hmain (x j) (R j) (hR j) (Q j) _ r₀ τ η b₀ ((le_max_left _ _).trans hj1)
    ((le_max_right _ _).trans hj1) hη h8η (by linarith) le_rfl hgood
    (fun y hy t ht hlo ↦ (hj3 y hy.1 t ht).1 hlo) (fun y hy t ht hhi ↦ (hj3 y hy.1 t ht).2 hhi)

/-! ### HA10.c with the HA9 inputs proved -/

/-- The horizontal lines over `B_ρ` carrying a good point in the slab form an open set. -/
theorem isOpen_goodSlabProjection {T : ℝ} (hT : 0 < T) {v : Space (m + 1) → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) (ℓ r₀ b ρ τ : ℝ) :
    IsOpen {y : Space m | ‖y‖ < ρ ∧ ∃ t, |t| < τ ∧
      IsLayerGoodPoint T v (verticalDirection m) ℓ r₀ b (point y t)} := by
  have hset : {y : Space m | ‖y‖ < ρ ∧ ∃ t, |t| < τ ∧
      IsLayerGoodPoint T v (verticalDirection m) ℓ r₀ b (point y t)} =
      {y : Space m | ‖y‖ < ρ} ∩ horizontal '' ({p : Space (m + 1) | |p (Fin.last m)| < τ} ∩
        layerGoodSet T v (verticalDirection m) ℓ r₀ b) := by
    ext y
    constructor
    · rintro ⟨hy, t, ht, hg⟩
      refine ⟨hy, point y t, ⟨?_, hg⟩, horizontal_point y t⟩
      show |point y t (Fin.last m)| < τ
      rwa [last_point]
    · rintro ⟨hy, p, ⟨hpt, hpg⟩, rfl⟩
      refine ⟨hy, p (Fin.last m), hpt, ?_⟩
      rw [point_horizontal_last]
      exact hpg
  rw [hset]
  have hlast : IsOpen {p : Space (m + 1) | |p (Fin.last m)| < τ} :=
    isOpen_lt (continuous_abs.comp (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous)
      continuous_const
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpenMap_horizontal _ (hlast.inter (isOpen_layerGoodSet hT hv (norm_verticalDirection m)
      ℓ r₀ b)))

/-- **HA10.c on the good low points, with the HA9 inputs proved.** There are `K, α₀, c_q > 0` and
`M ≥ 0`, independent of the center, scale and rotation, such that for `0 < α ≤ α₀` there are
`ℓ, ρ₀, C_w > 0` with the following property. Let `D` be the set of lines over `B_ρ` carrying a
good point (threshold `ℓ`, radii up to `r₀`, cut `b₀`) in the slab `|t| < τ`, assume the HA8
slab facts on the lines over `B_ρ` (`v = 0` for `t ≤ -η`, `v > 1 - β` for `t ≥ η`), and let `S` be
the set of good low points: `0 < v < b` over `B_ρ` in the slab with tilt below `ℓ rᵐ` on all balls
of radius `r ≤ r₀`. Then, with `Λ = K α + (b + α) / c_q`, `ρ = |∇v|² / R` and the heights
`H(y) = h_{s₁}(y) - T(s₁) / R`, `∫_S ρ ≤ M Λ |D|` and
`∫_S (t - a)² ρ ≤ 2 M Λ ∫_D ((H - a)² + (Λ / R)²)`. -/
theorem RigidityHypotheses.exists_low_level_bounds_of_good_layers (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ)
    (hsharp : ∀ z : Space (m + 1), ∀ ρ : ℝ, 0 < ρ →
      (∫ x in closedBall z ρ, phaseEnergyDensity f 0 (zeroExtension g u) x) ≤
        phasePrimitive f 1 * volume.real (closedBall (0 : Space m) 1) * ρ ^ m)
    {s₁ s₂ b₀ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂ : s₂ < 1 - b₀) (hb₀ : 0 < b₀)
    {L : ℝ≥0} (hL : 0 < L) :
    ∃ K α₀ cq M : ℝ, 0 < K ∧ 0 < α₀ ∧ 0 < cq ∧ 0 ≤ M ∧
      ∀ α : ℝ, 0 < α → α ≤ α₀ →
      ∃ ℓ ρ₀ Cw : ℝ, 0 < ℓ ∧ 0 < ρ₀ ∧ 0 < Cw ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
      ∀ (ρ r₀ τ η β b a : ℝ), 0 < b → b ≤ α₀ → b < 1 - b₀ →
        ρ₀ ≤ R * r₀ → Cw ≤ R * r₀ → 0 < η → 8 * η ≤ min (L : ℝ) 1 * r₀ → η + Cw / R < τ →
        β ≤ b₀ →
        (∀ y : Space m, ‖y‖ < ρ → ∀ t ∈ Ioo (-τ) τ, t ≤ -η →
          zeroExtension g u (x + R • Q (point y t)) = 0) →
        (∀ y : Space m, ‖y‖ < ρ → ∀ t ∈ Ioo (-τ) τ, η ≤ t →
          1 - β < zeroExtension g u (x + R • Q (point y t))) →
        (∫ p in {p : Space (m + 1) | ‖horizontal p‖ < ρ ∧ |p (Fin.last m)| < τ ∧
            0 < zeroExtension g u (x + R • Q p) ∧ zeroExtension g u (x + R • Q p) < b ∧
            ∀ r ∈ Ioc 0 r₀, ∫ z in ball p r, diffuseTiltDensity R
              (fun z ↦ zeroExtension g u (x + R • Q z)) (verticalDirection m) z < ℓ * r ^ m},
            ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R) ≤
          M * (K * α + (b + α) / cq) * volume.real {y : Space m | ‖y‖ < ρ ∧ ∃ t, |t| < τ ∧
            IsLayerGoodPoint R (fun z ↦ zeroExtension g u (x + R • Q z)) (verticalDirection m)
              ℓ r₀ b₀ (point y t)} ∧
        (∫ p in {p : Space (m + 1) | ‖horizontal p‖ < ρ ∧ |p (Fin.last m)| < τ ∧
            0 < zeroExtension g u (x + R • Q p) ∧ zeroExtension g u (x + R • Q p) < b ∧
            ∀ r ∈ Ioc 0 r₀, ∫ z in ball p r, diffuseTiltDensity R
              (fun z ↦ zeroExtension g u (x + R • Q z)) (verticalDirection m) z < ℓ * r ^ m},
            (p (Fin.last m) - a) ^ 2 *
              (‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R)) ≤
          2 * M * (K * α + (b + α) / cq) * ∫ y in {y : Space m | ‖y‖ < ρ ∧ ∃ t, |t| < τ ∧
            IsLayerGoodPoint R (fun z ↦ zeroExtension g u (x + R • Q z)) (verticalDirection m)
              ℓ r₀ b₀ (point y t)},
            ((slabLevelHeight (fun z ↦ zeroExtension g u (x + R • Q z)) τ s₁ y -
              layerTravelTime f s₁ / R - a) ^ 2 + ((K * α + (b + α) / cq) / R) ^ 2) := by
  obtain ⟨K, α₀l, M, hK, hα₀l, hM0, hbands⟩ := hr.exists_low_level_bounds_of_approximation_on h
  obtain ⟨cq, sl, hcq, hsl, hqlin⟩ := hr.exists_layerProfile_linear_lower h
  set α₀ : ℝ := min α₀l (cq * sl / 3) with hα₀def
  have hα₀ : 0 < α₀ := lt_min hα₀l (by positivity)
  have hα₀1 : α₀ ≤ α₀l := min_le_left _ _
  have hα₀2 : α₀ ≤ cq * sl / 3 := min_le_right _ _
  refine ⟨K, α₀, cq, M, hK, hα₀, hcq, hM0, ?_⟩
  intro α hα hαle
  obtain ⟨ℓ, ρ₀, Cw, c, hℓ, hρ₀, hCw, -, hmain⟩ := hr.exists_hasLevelCone_and_profile h hsharp
    hs₁ hs₁₂ hs₂ hb₀ hL hα (by positivity : 0 ≤ K * α)
  refine ⟨ℓ, ρ₀, Cw, hℓ, hρ₀, hCw, ?_⟩
  intro x R hR Q ρ r₀ τ η β b a hb hbα₀ hb1 hρR hCwR hη h8η hητ hβ hlow hhigh
  set U := zeroExtension g u with hUdef
  have hvc : Continuous (fun z ↦ U (x + R • Q z)) := h.continuous_rescaled_translate x R Q
  have hLipv : LipschitzWith ⟨κ * R, mul_nonneg h.kappa_pos.le hR.le⟩
      (fun z ↦ U (x + R • Q z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a c
    have := (hr.zeroExtension_lipschitzWith h).dist_le_mul (x + R • Q a) (x + R • Q c)
    rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hR.le, Q.dist_map] at this
    calc _ ≤ κ * (R * dist a c) := this
      _ = κ * R * dist a c := by ring
  have hCwR0 : 0 < Cw / R := div_pos hCw hR
  have hητ' : η < τ := by linarith
  set D : Set (Space m) := {y : Space m | ‖y‖ < ρ ∧ ∃ t, |t| < τ ∧ IsLayerGoodPoint R
    (fun z ↦ U (x + R • Q z)) (verticalDirection m) ℓ r₀ b₀ (point y t)} with hDdef
  obtain ⟨hcone, -, hprof⟩ := hmain x R hR Q D r₀ τ η β hρR hCwR hη h8η hητ hβ
    (fun y hy ↦ hy.2) (fun y hy t ht hlo ↦ hlow y hy.1 t ht hlo)
    (fun y hy t ht hhi ↦ hhigh y hy.1 t ht hhi)
  have hDo : IsOpen D := isOpen_goodSlabProjection hR hLipv ℓ r₀ b₀ ρ τ
  have hD : MeasurableSet D := hDo.measurableSet
  have hDfin : volume D ≠ ⊤ := by
    refine ((measure_mono (fun y hy ↦ ?_)).trans_lt
      (measure_ball_lt_top (x := (0 : Space m)) (r := ρ))).ne
    rw [mem_ball, dist_zero_right]
    exact hy.1
  -- the `s₁`-level heights are bounded and Lipschitz on `D`
  have hcross : ∀ y ∈ D, ∃ t ∈ Ioo (-τ) τ, (fun z ↦ U (x + R • Q z)) (point y t) = s₁ := by
    intro y hy
    have hm : -η ∈ Ioo (-τ) τ := ⟨by linarith, by linarith⟩
    have hp : η ∈ Ioo (-τ) τ := ⟨by linarith, by linarith⟩
    have h0 := hlow y hy.1 (-η) hm le_rfl
    have h1 := hhigh y hy.1 η hp le_rfl
    obtain ⟨t₀, ht₀, hvt₀⟩ := intermediate_value_Icc (show -η ≤ η by linarith)
      (hvc.comp (continuous_point y)).continuousOn
      (show s₁ ∈ Icc (U (x + R • Q (point y (-η)))) (U (x + R • Q (point y η))) from
        ⟨by rw [h0]; exact hs₁.le, by linarith⟩)
    exact ⟨t₀, ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩, hvt₀⟩
  have hLipH : LipschitzOnWith L
      (slabLevelHeight (fun z ↦ U (x + R • Q z)) τ s₁) D := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy y' hy'
    obtain ⟨h1, h2⟩ := slabLevelHeight_spec (v := fun z ↦ U (x + R • Q z)) (hcross y hy)
    obtain ⟨h1', h2'⟩ := slabLevelHeight_spec (v := fun z ↦ U (x + R • Q z)) (hcross y' hy')
    rw [Real.dist_eq]
    exact hcone s₁ ⟨le_rfl, hs₁₂⟩ y hy y' hy' _ h1 _ h1' h2 h2'
  have hHint : IntegrableOn (fun y ↦ (slabLevelHeight (fun z ↦ U (x + R • Q z)) τ s₁ y -
      layerTravelTime f s₁ / R - a) ^ 2) D := by
    have hcont : ContinuousOn (fun y ↦ (slabLevelHeight (fun z ↦ U (x + R • Q z)) τ s₁ y -
        layerTravelTime f s₁ / R - a) ^ 2) D :=
      ((hLipH.continuousOn.sub continuousOn_const).sub continuousOn_const).pow 2
    refine IntegrableOn.of_bound hDfin.lt_top (hcont.aestronglyMeasurable hD)
      ((τ + |layerTravelTime f s₁ / R| + |a|) ^ 2) (ae_restrict_of_forall_mem hD ?_)
    intro y hy
    obtain ⟨h1, _⟩ := slabLevelHeight_spec (v := fun z ↦ U (x + R • Q z)) (hcross y hy)
    have habs : |slabLevelHeight (fun z ↦ U (x + R • Q z)) τ s₁ y -
        layerTravelTime f s₁ / R - a| ≤ τ + |layerTravelTime f s₁ / R| + |a| := by
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, neg_abs_le (layerTravelTime f s₁ / R),
        le_abs_self (layerTravelTime f s₁ / R), neg_abs_le a, le_abs_self a]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  -- the good low points
  have hG : IsOpen {p : Space (m + 1) | ∀ r ∈ Ioc 0 r₀, ∫ z in ball p r,
      diffuseTiltDensity R (fun z ↦ U (x + R • Q z)) (verticalDirection m) z < ℓ * r ^ m} :=
    isOpen_setOf_forall_setIntegral_ball_lt (measurable_diffuseTiltDensity R _ _)
      (diffuseTiltDensity_nonneg hR _ (norm_verticalDirection m))
      (diffuseTiltDensity_le_of_lipschitzWith hR hLipv _) ℓ r₀
  have hlast : Continuous (fun p : Space (m + 1) ↦ |p (Fin.last m)|) :=
    continuous_abs.comp (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous
  have hS : MeasurableSet {p : Space (m + 1) | ‖horizontal p‖ < ρ ∧ |p (Fin.last m)| < τ ∧
      0 < U (x + R • Q p) ∧ U (x + R • Q p) < b ∧ ∀ r ∈ Ioc 0 r₀, ∫ z in ball p r,
        diffuseTiltDensity R (fun z ↦ U (x + R • Q z)) (verticalDirection m) z < ℓ * r ^ m} :=
    (measurableSet_lt (continuous_norm.comp continuous_horizontal).measurable
        measurable_const).inter
      ((measurableSet_lt hlast.measurable measurable_const).inter
        ((measurableSet_lt measurable_const hvc.measurable).inter
          ((measurableSet_lt hvc.measurable measurable_const).inter hG.measurableSet)))
  have hbα : b + α < cq * sl := by linarith
  refine hbands x R hR Q (layerProfile f) (fun σ hσ ↦ layerProfile_of_nonpos f hσ) cq sl hcq
    hqlin α b hα (hαle.trans hα₀1) hb hbα D hD hDfin _ a hHint _ hS ?_
  rintro p ⟨hpρ, hpt, hp0, hpb, hpgood⟩
  have hpp : point (horizontal p) (p (Fin.last m)) = p := point_horizontal_last p
  have hgoodp : IsLayerGoodPoint R (fun z ↦ U (x + R • Q z)) (verticalDirection m) ℓ r₀ b₀
      (point (horizontal p) (p (Fin.last m))) := by
    rw [hpp]
    exact ⟨⟨hp0, by linarith⟩, hpgood⟩
  have hpD : horizontal p ∈ D := ⟨hpρ, p (Fin.last m), hpt, hgoodp⟩
  refine ⟨hpD, hp0, hpb, ?_⟩
  have happ := hprof (horizontal p) hpD (p (Fin.last m)) hpt hgoodp
  rw [hpp] at happ
  intro z hz
  exact happ z hz

end SerrinEpigraph
