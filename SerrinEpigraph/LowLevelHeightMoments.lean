module

public import SerrinEpigraph.DiffuseHeightTails
public import SerrinEpigraph.PlaneTiltTranslatedClearing
public import SerrinEpigraph.BVColumnGraph
public import SerrinEpigraph.CrossBoundaryMinimality

/-!
# Low-level height moments without boundary gradient compactness

This file formalizes the deterministic parts of blueprint `harmonic-approximation.md` HA10 for
the rescaled translates `v y = U(x + R • Q y)` (`U = zeroExtension g u`, `ε = 1 / R`, `Q` a linear
isometry, vertical coordinates `y = point y' t` as in `SerrinEpigraph.DiffuseGoodLayers`). All
constants are independent of the center `x`, the scale `R` and the rotation `Q`.

* HA10.a/b (CO3 clearing at scale `ε`): `RigidityHypotheses.exists_microscopic_clearing` and its
  contrapositive `RigidityHypotheses.exists_microscopic_nondegeneracy` (near every positive point,
  within distance `ε α / a₀`, the value exceeds `α`).
* HA10.b (HA10.1): `RigidityHypotheses.exists_low_band_localization`. If `v` is `α`-close to a
  translated profile `q(R(t - H))` on a microscopic ball, where `q` vanishes on `(-∞, 0]` and
  grows at least linearly, then every point with `0 < v < b` satisfies
  `-K α < R(t - H) < (b + α)/c_q`. The lower side uses clearing, not the profile.
* HA10.c (HA10.2): `setIntegral_le_of_vertical_band` (Fubini over vertical lines),
  `RigidityHypotheses.exists_rotated_rescaled_density_bound` (`ρ ≤ M R` on the positive phase)
  and `RigidityHypotheses.exists_low_level_band_bounds`: if over a horizontal set `D` the low
  positive points of each vertical line lie within `Λ ε` of a height `H(y')`, then
  `∫_{D × ℝ, 0<v<b} ρ ≤ 2 M Λ |D|` and
  `∫_{D × ℝ, 0<v<b} (t - a)² ρ ≤ 4 M Λ ∫_D ((H - a)² + (Λ ε)²)`.
* Assembled: `RigidityHypotheses.exists_low_level_bounds_of_profile_approximation` derives the
  band from a profile approximation around every low positive point over `D`, with band width
  `Λ = K α + (b + α) / c_q`.

The microscopic profile approximation (compactness and the classification HA9.a) and the
exclusion of low positive points outside the microscopic window are not formalized here; they
enter as the explicit approximation hypothesis of the localization and assembled statements.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal

namespace SerrinEpigraph

/-! ### Fubini over vertical lines -/

/-- One vertical line: if the points of `S` on the line over `y` lie within `ℓ` of the height `c`
and `F ≤ K` there, the line integral of `1_S F` is at most `2 ℓ K`. -/
private theorem lintegral_line_indicator_le {m : ℕ} {S : Set (Space (m + 1))}
    {F : Space (m + 1) → ℝ} (y : Space m) {c K ℓ : ℝ} (hK : 0 ≤ K)
    (hband : ∀ t, point y t ∈ S → |t - c| ≤ ℓ ∧ F (point y t) ≤ K) :
    ∫⁻ t, S.indicator (fun p ↦ ENNReal.ofReal (F p)) (point y t) ≤
      ENNReal.ofReal (2 * ℓ * K) := by
  calc ∫⁻ t, S.indicator (fun p ↦ ENNReal.ofReal (F p)) (point y t)
      ≤ ∫⁻ t, (Icc (c - ℓ) (c + ℓ)).indicator (fun _ ↦ ENNReal.ofReal K) t := by
        apply lintegral_mono
        intro t
        dsimp only
        by_cases ht : point y t ∈ S
        · obtain ⟨hct, hFK⟩ := hband t ht
          have htI : t ∈ Icc (c - ℓ) (c + ℓ) := by
            rw [abs_le] at hct
            constructor <;> linarith [hct.1, hct.2]
          rw [indicator_of_mem ht, indicator_of_mem htI]
          exact ENNReal.ofReal_le_ofReal hFK
        · rw [indicator_of_notMem ht]
          exact zero_le
    _ = ENNReal.ofReal K * volume (Icc (c - ℓ) (c + ℓ)) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (2 * ℓ * K) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul hK]
        congr 1
        ring

/-- **Vertical-band estimate (Fubini).** Let `S` be measurable with horizontal projection in a
measurable set `D`, and suppose that over each `y ∈ D` the points of `S` on the vertical line lie
within `ℓ` of a height `c(y)`, where the nonnegative measurable integrand `F` is at most `K(y)`.
If `K` is integrable on `D`, then `∫_S F ≤ 2 ℓ ∫_D K`. -/
theorem setIntegral_le_of_vertical_band {m : ℕ} {S : Set (Space (m + 1))} (hS : MeasurableSet S)
    {F : Space (m + 1) → ℝ} (hF : Measurable F) (hF0 : ∀ p, 0 ≤ F p) {D : Set (Space m)}
    (hD : MeasurableSet D) (hSD : ∀ p ∈ S, horizontal p ∈ D) {c K : Space m → ℝ} {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hK0 : ∀ y ∈ D, 0 ≤ K y) (hK : IntegrableOn K D)
    (hband : ∀ y ∈ D, ∀ t, point y t ∈ S → |t - c y| ≤ ℓ ∧ F (point y t) ≤ K y) :
    ∫ p in S, F p ≤ 2 * ℓ * ∫ y in D, K y := by
  have hmeasI : Measurable (S.indicator (fun p ↦ ENNReal.ofReal (F p))) :=
    (ENNReal.measurable_ofReal.comp hF).indicator hS
  have hmp := measurePreserving_point m
  have hlin : ∫⁻ p in S, ENNReal.ofReal (F p) ≤ ∫⁻ y in D, ENNReal.ofReal (2 * ℓ * K y) := by
    rw [← lintegral_indicator hS, ← hmp.lintegral_comp hmeasI,
      lintegral_prod (fun q : Space m × ℝ ↦ S.indicator (fun p ↦ ENNReal.ofReal (F p))
        (point q.1 q.2)) (hmeasI.comp hmp.measurable).aemeasurable, ← lintegral_indicator hD]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ D
    · rw [indicator_of_mem hy]
      exact lintegral_line_indicator_le y (hK0 y hy) (hband y hy)
    · rw [indicator_of_notMem hy]
      have h0 : ∀ t, S.indicator (fun p ↦ ENNReal.ofReal (F p)) (point y t) = 0 := by
        intro t
        apply indicator_of_notMem
        intro ht
        exact hy (by simpa using hSD _ ht)
      simp [h0]
  have hKi : IntegrableOn (fun y ↦ 2 * ℓ * K y) D := hK.const_mul (2 * ℓ)
  have hKnn : 0 ≤ᵐ[volume.restrict D] fun y ↦ 2 * ℓ * K y := by
    filter_upwards [ae_restrict_mem hD] with y hy
    exact mul_nonneg (by positivity) (hK0 y hy)
  rw [← ofReal_integral_eq_lintegral_ofReal hKi hKnn] at hlin
  have hFS : ∫ p in S, F p = (∫⁻ p in S, ENNReal.ofReal (F p)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hF.aestronglyMeasurable
  rw [hFS, ← integral_const_mul]
  have hR0 : 0 ≤ ∫ y in D, 2 * ℓ * K y := integral_nonneg_of_ae hKnn
  calc (∫⁻ p in S, ENNReal.ofReal (F p)).toReal
      ≤ (ENNReal.ofReal (∫ y in D, 2 * ℓ * K y)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = ∫ y in D, 2 * ℓ * K y := ENNReal.toReal_ofReal hR0

variable {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}

/-! ### HA10.a/b. Clearing and nondegeneracy at the microscopic scale -/

/-- **Microscopic clearing (CO3 at scale `ε = 1/R`).** There are `a₀ > 0` and `α₀ > 0`,
independent of the center `x`, the scale `R` and the rotation `Q`, such that if the rotated
rescaled translate is at most `α ≤ α₀` on the ball of radius `α / (a₀ R)` about `p`, then it
vanishes at `p`. -/
theorem RigidityHypotheses.exists_microscopic_clearing (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ a₀ α₀ : ℝ, 0 < a₀ ∧ 0 < α₀ ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ (p : Space (m + 1)) (α : ℝ), 0 < α → α ≤ α₀ →
          (∀ z ∈ ball p (α / (a₀ * R)), zeroExtension g u (x + R • Q z) ≤ α) →
            zeroExtension g u (x + R • Q p) = 0 := by
  obtain ⟨a, R₀, ha, hR₀, hclear⟩ := hr.exists_translated_phase_clearing_constants h
  refine ⟨a, a * R₀, ha, mul_pos ha hR₀, ?_⟩
  intro x R hR Q p α hα hαle hsmall
  have hr0 : 0 < α / (a * R) := by positivity
  have hRr : R * (α / (a * R)) ≤ R₀ := by
    have e : R * (α / (a * R)) = α / a := by field_simp
    rw [e, div_le_iff₀ ha]
    linarith
  have hball : ∀ y ∈ ball (Q p) (α / (a * R)),
      zeroExtension g u (x + R • y) ≤ a * (R * (α / (a * R))) := by
    intro y hy
    have e : a * (R * (α / (a * R))) = α := by field_simp
    rw [e]
    have hz : Q.symm y ∈ ball p (α / (a * R)) := by
      rw [mem_ball] at hy ⊢
      calc dist (Q.symm y) p = dist (Q.symm y) (Q.symm (Q p)) := by
            rw [LinearIsometryEquiv.symm_apply_apply]
        _ = dist y (Q p) := Q.symm.dist_map _ _
        _ < _ := hy
    have hv := hsmall _ hz
    rwa [LinearIsometryEquiv.apply_symm_apply] at hv
  have hEq := hclear x R hR (Q p) (α / (a * R)) hr0 hRr hball
  have hmem : Q p ∈ ball (Q p) (α / (a * R) / 2) := mem_ball_self (by positivity)
  simpa using hEq hmem

/-- **Microscopic nondegeneracy (HA10.a).** Near every positive point `p` of the rotated rescaled
translate and for every `0 < α ≤ α₀`, some point within distance `α / (a₀ R)` (i.e. `ε α / a₀`)
has value larger than `α`. In particular microscopic limits at positive points are nontrivial,
and their centers cannot lie in the interior of the zero phase. -/
theorem RigidityHypotheses.exists_microscopic_nondegeneracy (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ a₀ α₀ : ℝ, 0 < a₀ ∧ 0 < α₀ ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ (p : Space (m + 1)) (α : ℝ), 0 < α → α ≤ α₀ →
          0 < zeroExtension g u (x + R • Q p) →
            ∃ z ∈ ball p (α / (a₀ * R)), α < zeroExtension g u (x + R • Q z) := by
  obtain ⟨a₀, α₀, ha₀, hα₀, hclear⟩ := hr.exists_microscopic_clearing h
  refine ⟨a₀, α₀, ha₀, hα₀, ?_⟩
  intro x R hR Q p α hα hαle hpos
  by_contra hn
  simp only [not_exists, not_and, not_lt] at hn
  have h0 := hclear x R hR Q p α hα hαle hn
  linarith

/-- A coordinate is bounded by the Euclidean norm. -/
private theorem abs_coord_le_norm {d : ℕ} (w : Space d) (i : Fin d) : |w i| ≤ ‖w‖ := by
  have h := abs_real_inner_le_norm (EuclideanSpace.single i (1 : ℝ)) w
  simpa [EuclideanSpace.inner_single_left] using h

/-- **HA10.b, localization of low positive points (HA10.1).** There are `K > 0` and `α₀ > 0`,
independent of `x`, `R` and `Q`, with the following property. Let `q` vanish on `(-∞, 0]` and
satisfy `q(s) ≥ c_q min(s, s₁)` for `s ≥ 0`, let `0 < α ≤ α₀` and `b + α < c_q s₁`, and suppose
the rotated rescaled translate is `α`-close to `q(R (z_last - H))` on the ball of radius `K α / R`
about a point `p` with `0 < v(p) < b`. Then `-K α < R (p_last - H) < (b + α) / c_q`, so low
positive points lie in a vertical band of width `ε (K α + (b + α) / c_q)`. The lower side comes
from microscopic clearing, not from the profile approximation. -/
theorem RigidityHypotheses.exists_low_band_localization (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ K α₀ : ℝ, 0 < K ∧ 0 < α₀ ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ q : ℝ → ℝ, (∀ s ≤ 0, q s = 0) → ∀ cq s₁ : ℝ, 0 < cq →
          (∀ s, 0 ≤ s → cq * min s s₁ ≤ q s) →
          ∀ H α b : ℝ, 0 < α → α ≤ α₀ → b + α < cq * s₁ → ∀ p : Space (m + 1),
            (∀ z ∈ ball p (K * α / R),
              |zeroExtension g u (x + R • Q z) - q (R * (z (Fin.last m) - H))| ≤ α) →
            0 < zeroExtension g u (x + R • Q p) → zeroExtension g u (x + R • Q p) < b →
              -(K * α) < R * (p (Fin.last m) - H) ∧
                R * (p (Fin.last m) - H) < (b + α) / cq := by
  obtain ⟨a₀, α₀, ha₀, hα₀, hclear⟩ := hr.exists_microscopic_clearing h
  refine ⟨a₀⁻¹, α₀, inv_pos.mpr ha₀, hα₀, ?_⟩
  intro x R hR Q q hq0 cq s₁ hcq hqlin H α b hα hαle hbα p happrox hpos hlow
  have hball_eq : a₀⁻¹ * α / R = α / (a₀ * R) := by field_simp
  constructor
  · by_contra hn
    have hn' : R * (p (Fin.last m) - H) ≤ -(a₀⁻¹ * α) := not_lt.mp hn
    have hsmall : ∀ z ∈ ball p (α / (a₀ * R)), zeroExtension g u (x + R • Q z) ≤ α := by
      intro z hz
      have hz' : z ∈ ball p (a₀⁻¹ * α / R) := by rwa [hball_eq]
      have hap := happrox z hz'
      have hcoord : |z (Fin.last m) - p (Fin.last m)| ≤ ‖z - p‖ := by
        simpa using abs_coord_le_norm (z - p) (Fin.last m)
      have hdist : ‖z - p‖ < α / (a₀ * R) := by rwa [mem_ball, dist_eq_norm] at hz
      have hRz : R * (z (Fin.last m) - H) ≤ 0 := by
        have h1 : z (Fin.last m) - p (Fin.last m) < α / (a₀ * R) :=
          lt_of_le_of_lt (le_abs_self _) (hcoord.trans_lt hdist)
        have h2 : R * (z (Fin.last m) - p (Fin.last m)) < R * (α / (a₀ * R)) :=
          mul_lt_mul_of_pos_left h1 hR
        have h3 : R * (α / (a₀ * R)) = a₀⁻¹ * α := by field_simp
        have h4 : R * (z (Fin.last m) - H) =
            R * (z (Fin.last m) - p (Fin.last m)) + R * (p (Fin.last m) - H) := by ring
        linarith
      rw [hq0 _ hRz, sub_zero] at hap
      exact (le_abs_self _).trans hap
    have h0 := hclear x R hR Q p α hα hαle hsmall
    linarith
  · have hap := happrox p (mem_ball_self (by positivity))
    have hq_lt : q (R * (p (Fin.last m) - H)) < b + α := by
      have := (abs_le.mp hap).1
      linarith
    by_contra hn
    have hn' : (b + α) / cq ≤ R * (p (Fin.last m) - H) := not_lt.mp hn
    have hb0 : 0 < b := lt_trans hpos hlow
    have hs0 : 0 ≤ R * (p (Fin.last m) - H) :=
      le_trans (div_nonneg (by linarith) hcq.le) hn'
    have hlin := hqlin _ hs0
    have hmin : b + α ≤ cq * min (R * (p (Fin.last m) - H)) s₁ := by
      rcases le_total (R * (p (Fin.last m) - H)) s₁ with hle | hle
      · rw [min_eq_left hle]
        have h5 := (div_le_iff₀ hcq).mp hn'
        linarith [mul_comm cq (R * (p (Fin.last m) - H))]
      · rw [min_eq_right hle]
        linarith
    linarith

/-! ### HA10.c. Low-level mass and height moments -/

/-- The Modica density bound for the rotated rescaled translates: there is `M ≥ 0`, independent
of `x`, `R` and `Q`, with `ρ = |∇v|² / R ≤ M R` on the positive phase. -/
theorem RigidityHypotheses.exists_rotated_rescaled_density_bound (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ p : Space (m + 1), 0 < zeroExtension g u (x + R • Q p) →
          ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R ≤ M * R := by
  obtain ⟨W, hW⟩ := isCompact_Icc.exists_bound_of_continuousOn h.normalizedPotential_continuousOn
  refine ⟨2 * max W 0, by positivity, ?_⟩
  intro x R hR Q p hp
  have hm := hr.norm_gradient_rescaled_sq_le h x hR Q hp
  have hv1 : zeroExtension g u (x + R • Q p) ≤ 1 := (hr.zeroExtension_lt_one _).le
  have hWp : normalizedPotential f (zeroExtension g u (x + R • Q p)) ≤ max W 0 :=
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hW _ ⟨hp.le, hv1⟩)).trans
      (le_max_left _ _)
  rw [div_le_iff₀ hR]
  calc _ ≤ 2 * R ^ 2 * normalizedPotential f (zeroExtension g u (x + R • Q p)) := hm
    _ ≤ 2 * R ^ 2 * max W 0 := mul_le_mul_of_nonneg_left hWp (by positivity)
    _ = 2 * max W 0 * R * R := by ring

/-- **HA10.c, low-level mass and height moments (HA10.2).** There is `M ≥ 0`, independent of
`x`, `R`, `Q` and of all band data, such that: if `D` is a measurable horizontal set of finite
measure and over each `y ∈ D` every point of the vertical line with `0 < v < b` lies within `Λ / R`
(i.e. `Λ ε`) of the height `H(y)`, then
`∫_{D × ℝ, 0<v<b} ρ ≤ 2 M Λ |D|` and
`∫_{D × ℝ, 0<v<b} (t - a)² ρ ≤ 4 M Λ ∫_D ((H - a)² + (Λ/R)²)`, where `ρ = |∇v|² / R`. With the
band width `Λ ≤ C (b + α)` from HA10.1, these are the HA10.c mass and moment estimates. -/
theorem RigidityHypotheses.exists_low_level_band_bounds (hr : RigidityHypotheses g u f)
    (h : Hypotheses g u f κ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ D : Set (Space m), MeasurableSet D → volume D ≠ ⊤ →
          ∀ (H : Space m → ℝ) (a b Λ : ℝ), 0 ≤ Λ → IntegrableOn (fun y ↦ (H y - a) ^ 2) D →
            (∀ y ∈ D, ∀ t : ℝ, 0 < zeroExtension g u (x + R • Q (point y t)) →
              zeroExtension g u (x + R • Q (point y t)) < b → |t - H y| ≤ Λ / R) →
            (∫ p in {p | horizontal p ∈ D ∧ 0 < zeroExtension g u (x + R • Q p) ∧
                zeroExtension g u (x + R • Q p) < b},
                ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R) ≤
              2 * M * Λ * volume.real D ∧
            (∫ p in {p | horizontal p ∈ D ∧ 0 < zeroExtension g u (x + R • Q p) ∧
                zeroExtension g u (x + R • Q p) < b},
                (p (Fin.last m) - a) ^ 2 *
                  (‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R)) ≤
              4 * M * Λ * ∫ y in D, ((H y - a) ^ 2 + (Λ / R) ^ 2) := by
  obtain ⟨M, hM0, hdens⟩ := hr.exists_rotated_rescaled_density_bound h
  refine ⟨M, hM0, ?_⟩
  intro x R hR Q D hD hDfin H a b Λ hΛ hHint hband
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hvc : Continuous v := h.continuous_rescaled_translate x R Q
  set S : Set (Space (m + 1)) := {p | horizontal p ∈ D ∧ 0 < v p ∧ v p < b} with hSdef
  have hS : MeasurableSet S :=
    (continuous_horizontal.measurable hD).inter
      ((measurableSet_lt measurable_const hvc.measurable).inter
        (measurableSet_lt hvc.measurable measurable_const))
  have hρm : Measurable (fun p ↦ ‖gradient v p‖ ^ 2 / R) :=
    ((measurable_gradient v).norm.pow_const 2).div_const R
  have hρ0 : ∀ p, 0 ≤ ‖gradient v p‖ ^ 2 / R := fun p ↦ div_nonneg (sq_nonneg _) hR.le
  have hρM : ∀ p, 0 < v p → ‖gradient v p‖ ^ 2 / R ≤ M * R := fun p hp ↦ hdens x R hR Q p hp
  have hSD : ∀ p ∈ S, horizontal p ∈ D := fun p hp ↦ hp.1
  have hmemS : ∀ y t, point y t ∈ S → 0 < v (point y t) ∧ v (point y t) < b :=
    fun y t ht ↦ ht.2
  have hΛR : 0 ≤ Λ / R := div_nonneg hΛ hR.le
  refine ⟨?_, ?_⟩
  · -- the low-level mass
    have hK : IntegrableOn (fun _ : Space m ↦ M * R) D := integrableOn_const hDfin
    have hmain := setIntegral_le_of_vertical_band (c := H) (K := fun _ ↦ M * R) hS hρm hρ0 hD
      hSD hΛR (fun _ _ ↦ by positivity) hK (by
        intro y hy t ht
        obtain ⟨h1, h2⟩ := hmemS y t ht
        exact ⟨hband y hy t h1 h2, hρM _ h1⟩)
    rw [setIntegral_const, smul_eq_mul] at hmain
    calc _ ≤ 2 * (Λ / R) * (volume.real D * (M * R)) := hmain
      _ = 2 * M * Λ * volume.real D := by field_simp
  · -- the low-level height moment
    have hFm : Measurable (fun p : Space (m + 1) ↦
        (p (Fin.last m) - a) ^ 2 * (‖gradient v p‖ ^ 2 / R)) :=
      ((((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous.measurable).sub_const
        a).pow_const 2).mul hρm
    have hK : IntegrableOn (fun y ↦ 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2)) D :=
      (hHint.add (integrableOn_const hDfin)).const_mul (2 * (M * R))
    have hmain := setIntegral_le_of_vertical_band (c := H)
      (K := fun y ↦ 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2)) hS hFm
      (fun p ↦ mul_nonneg (sq_nonneg _) (hρ0 p)) hD hSD hΛR (fun _ _ ↦ by positivity) hK (by
        intro y hy t ht
        obtain ⟨h1, h2⟩ := hmemS y t ht
        have hb := hband y hy t h1 h2
        refine ⟨hb, ?_⟩
        rw [last_point]
        have hsq : (t - H y) ^ 2 ≤ (Λ / R) ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hb 2
          rwa [sq_abs] at this
        have hta : (t - a) ^ 2 ≤ 2 * ((H y - a) ^ 2 + (Λ / R) ^ 2) := by
          nlinarith [sq_nonneg (t - H y - (H y - a))]
        calc (t - a) ^ 2 * (‖gradient v (point y t)‖ ^ 2 / R)
            ≤ 2 * ((H y - a) ^ 2 + (Λ / R) ^ 2) * (M * R) :=
              mul_le_mul hta (hρM _ h1) (hρ0 _) (by positivity)
          _ = 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2) := by ring)
    rw [integral_const_mul] at hmain
    calc _ ≤ 2 * (Λ / R) * (2 * (M * R) * ∫ y in D, ((H y - a) ^ 2 + (Λ / R) ^ 2)) := hmain
      _ = 4 * M * Λ * ∫ y in D, ((H y - a) ^ 2 + (Λ / R) ^ 2) := by field_simp; ring

/-- **HA10 assembled: low-level mass and height moments from a profile approximation.** There
are `K`, `α₀` and `M`, independent of `x`, `R`, `Q` and of all profile and band data, such that
the following holds. Let `q` vanish on `(-∞, 0]` with `q(s) ≥ c_q min(s, s₁)` for `s ≥ 0`, let
`0 < α ≤ α₀`, `0 < b` and `b + α < c_q s₁`, and let `D` be a measurable horizontal set of finite
measure with reference heights `H` such that `(H - a)²` is integrable on `D`. Suppose that around
every point `(y, t)` with `y ∈ D` and `0 < v < b`, the rotated rescaled translate is `α`-close to
`q(R(z_last - H(y)))` on the ball of radius `K α / R`; this hypothesis encodes the microscopic
profile approximation (HA10.a) and the exclusion of low positive points outside the window
(HA10.b). Then, with `Λ = K α + (b + α) / c_q`,
`∫_{D × ℝ, 0<v<b} ρ ≤ M Λ |D|` and
`∫_{D × ℝ, 0<v<b} (t - a)² ρ ≤ 2 M Λ ∫_D ((H - a)² + (Λ/R)²)`. -/
theorem RigidityHypotheses.exists_low_level_bounds_of_profile_approximation
    (hr : RigidityHypotheses g u f) (h : Hypotheses g u f κ) :
    ∃ K α₀ M : ℝ, 0 < K ∧ 0 < α₀ ∧ 0 ≤ M ∧
      ∀ (x : Space (m + 1)) (R : ℝ), 0 < R → ∀ Q : Space (m + 1) ≃ₗᵢ[ℝ] Space (m + 1),
        ∀ q : ℝ → ℝ, (∀ s ≤ 0, q s = 0) → ∀ cq s₁ : ℝ, 0 < cq →
          (∀ s, 0 ≤ s → cq * min s s₁ ≤ q s) →
          ∀ α b : ℝ, 0 < α → α ≤ α₀ → 0 < b → b + α < cq * s₁ →
          ∀ D : Set (Space m), MeasurableSet D → volume D ≠ ⊤ →
          ∀ (H : Space m → ℝ) (a : ℝ), IntegrableOn (fun y ↦ (H y - a) ^ 2) D →
            (∀ y ∈ D, ∀ t : ℝ, 0 < zeroExtension g u (x + R • Q (point y t)) →
              zeroExtension g u (x + R • Q (point y t)) < b →
              ∀ z ∈ ball (point y t) (K * α / R),
                |zeroExtension g u (x + R • Q z) - q (R * (z (Fin.last m) - H y))| ≤ α) →
            (∫ p in {p | horizontal p ∈ D ∧ 0 < zeroExtension g u (x + R • Q p) ∧
                zeroExtension g u (x + R • Q p) < b},
                ‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R) ≤
              M * (K * α + (b + α) / cq) * volume.real D ∧
            (∫ p in {p | horizontal p ∈ D ∧ 0 < zeroExtension g u (x + R • Q p) ∧
                zeroExtension g u (x + R • Q p) < b},
                (p (Fin.last m) - a) ^ 2 *
                  (‖gradient (fun z ↦ zeroExtension g u (x + R • Q z)) p‖ ^ 2 / R)) ≤
              2 * M * (K * α + (b + α) / cq) *
                ∫ y in D, ((H y - a) ^ 2 + ((K * α + (b + α) / cq) / R) ^ 2) := by
  obtain ⟨K, α₀, hK, hα₀, hloc⟩ := hr.exists_low_band_localization h
  obtain ⟨M, hM0, hdens⟩ := hr.exists_rotated_rescaled_density_bound h
  refine ⟨K, α₀, M, hK, hα₀, hM0, ?_⟩
  intro x R hR Q q hq0 cq s₁ hcq hqlin α b hα hαle hb hbα D hD hDfin H a hHint happrox
  set B := (b + α) / cq with hBdef
  have hB : 0 < B := div_pos (by linarith) hcq
  have hKα : 0 < K * α := mul_pos hK hα
  set Λ := K * α + B with hΛdef
  have hΛ : 0 < Λ := by linarith
  set v : Space (m + 1) → ℝ := fun z ↦ zeroExtension g u (x + R • Q z) with hvdef
  have hvc : Continuous v := h.continuous_rescaled_translate x R Q
  set S : Set (Space (m + 1)) := {p | horizontal p ∈ D ∧ 0 < v p ∧ v p < b} with hSdef
  have hS : MeasurableSet S :=
    (continuous_horizontal.measurable hD).inter
      ((measurableSet_lt measurable_const hvc.measurable).inter
        (measurableSet_lt hvc.measurable measurable_const))
  have hρm : Measurable (fun p ↦ ‖gradient v p‖ ^ 2 / R) :=
    ((measurable_gradient v).norm.pow_const 2).div_const R
  have hρ0 : ∀ p, 0 ≤ ‖gradient v p‖ ^ 2 / R := fun p ↦ div_nonneg (sq_nonneg _) hR.le
  have hρM : ∀ p, 0 < v p → ‖gradient v p‖ ^ 2 / R ≤ M * R := fun p hp ↦ hdens x R hR Q p hp
  have hSD : ∀ p ∈ S, horizontal p ∈ D := fun p hp ↦ hp.1
  -- band localization on the lines over `D`
  have hloc' : ∀ y ∈ D, ∀ t, point y t ∈ S →
      -(K * α) < R * (t - H y) ∧ R * (t - H y) < B := by
    intro y hy t ht
    obtain ⟨h1, h2⟩ := ht.2
    have hl := hloc x R hR Q q hq0 cq s₁ hcq hqlin (H y) α b hα hαle hbα (point y t)
      (happrox y hy t h1 h2) h1 h2
    simpa only [last_point] using hl
  set c : Space m → ℝ := fun y ↦ H y + (B - K * α) / (2 * R) with hcdef
  have hℓ : 0 ≤ Λ / (2 * R) := (div_pos hΛ (mul_pos two_pos hR)).le
  have hcen : ∀ y ∈ D, ∀ t, point y t ∈ S → |t - c y| ≤ Λ / (2 * R) := by
    intro y hy t ht
    obtain ⟨hl, hu⟩ := hloc' y hy t ht
    have e1 : t - c y = (R * (t - H y) - (B - K * α) / 2) / R := by
      simp only [hcdef]
      field_simp
      ring
    have e2 : Λ / (2 * R) = Λ / 2 / R := by
      field_simp
    rw [e1, e2, abs_le]
    constructor
    · rw [← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hR.le
    · exact div_le_div_of_nonneg_right (by linarith) hR.le
  have habs : ∀ y ∈ D, ∀ t, point y t ∈ S → |t - H y| ≤ Λ / R := by
    intro y hy t ht
    obtain ⟨hl, hu⟩ := hloc' y hy t ht
    have h1 : |R * (t - H y)| ≤ Λ := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_pos hR] at h1
    rw [le_div_iff₀ hR]
    linarith [mul_comm R |t - H y|]
  refine ⟨?_, ?_⟩
  · -- the low-level mass
    have hKi : IntegrableOn (fun _ : Space m ↦ M * R) D := integrableOn_const hDfin
    have hmain := setIntegral_le_of_vertical_band (c := c) (K := fun _ ↦ M * R) hS hρm hρ0 hD
      hSD hℓ (fun _ _ ↦ mul_nonneg hM0 hR.le) hKi
      (fun y hy t ht ↦ ⟨hcen y hy t ht, hρM _ ht.2.1⟩)
    rw [setIntegral_const, smul_eq_mul] at hmain
    calc _ ≤ 2 * (Λ / (2 * R)) * (volume.real D * (M * R)) := hmain
      _ = M * Λ * volume.real D := by field_simp
  · -- the low-level height moment
    have hFm : Measurable (fun p : Space (m + 1) ↦
        (p (Fin.last m) - a) ^ 2 * (‖gradient v p‖ ^ 2 / R)) :=
      ((((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).continuous.measurable).sub_const
        a).pow_const 2).mul hρm
    have hKi : IntegrableOn (fun y ↦ 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2)) D :=
      (hHint.add (integrableOn_const hDfin)).const_mul (2 * (M * R))
    have hmain := setIntegral_le_of_vertical_band (c := c)
      (K := fun y ↦ 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2)) hS hFm
      (fun p ↦ mul_nonneg (sq_nonneg _) (hρ0 p)) hD hSD hℓ
      (fun _ _ ↦ mul_nonneg (mul_nonneg two_pos.le (mul_nonneg hM0 hR.le)) (by positivity))
      hKi (by
        intro y hy t ht
        refine ⟨hcen y hy t ht, ?_⟩
        rw [last_point]
        have hb' := habs y hy t ht
        have hsq : (t - H y) ^ 2 ≤ (Λ / R) ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hb' 2
          rwa [sq_abs] at this
        have hta : (t - a) ^ 2 ≤ 2 * ((H y - a) ^ 2 + (Λ / R) ^ 2) := by
          nlinarith [sq_nonneg (t - H y - (H y - a))]
        calc (t - a) ^ 2 * (‖gradient v (point y t)‖ ^ 2 / R)
            ≤ 2 * ((H y - a) ^ 2 + (Λ / R) ^ 2) * (M * R) :=
              mul_le_mul hta (hρM _ ht.2.1) (hρ0 _) (by positivity)
          _ = 2 * (M * R) * ((H y - a) ^ 2 + (Λ / R) ^ 2) := by ring)
    rw [integral_const_mul] at hmain
    calc _ ≤ 2 * (Λ / (2 * R)) * (2 * (M * R) * ∫ y in D, ((H y - a) ^ 2 + (Λ / R) ^ 2)) :=
          hmain
      _ = 2 * M * Λ * ∫ y in D, ((H y - a) ^ 2 + (Λ / R) ^ 2) := by field_simp

end SerrinEpigraph
