module

public import SerrinEpigraph.ConeClassificationInduction
public import SerrinEpigraph.HausdorffContent

/-!
# Federer's dimension reduction for singular sets (GR15, GR17), relative to regularity inputs

This module proves GR15 and GR17 of `docs/rigidity-proof/gmt-regularity.md` for local perimeter
minimizers in `Space d`, relative to explicit inputs:

* `EpsilonRegularityHyp` (GR9–GR14): a half-space tangent cone forces a `C¹` boundary point;
* `SingularSetUSCHyp` (GR14): singular points of an `L¹_loc` convergent sequence of minimizers
  accumulate only at singular points of the limit;
* `ConeClassification k` for `k ≤ 7` (GR16, see `coneClassification_of_simonsHyp`).

Main results:
- `hausdorffMeasure_preimage_horizontal_eq_zero`: cylinders over `μH[s]`-null sets are
  `μH[s + 1]`-null (`s > 0`);
- **GR15** `IsLocalPerimeterMinimizer.exists_isTangentCone_hausdorffMeasure_singularSet_ne_zero`:
  if the singular set has positive `μH[s]`-measure, then at a content density point outside any
  prescribed null set there is a tangent cone whose singular set still has positive
  `μH[s]`-measure;
- **GR17** `IsMinimizingCone.hausdorffMeasure_singularSet_eq_zero` and
  `IsLocalPerimeterMinimizer.hausdorffMeasure_singularSet_inter_eq_zero`:
  `μH[s] (singularSet E ∩ Ω) = 0` for every `s > d - 8`; in particular
  `dimH (singularSet E ∩ Ω) ≤ d - 8` (`IsLocalPerimeterMinimizer.dimH_singularSet_inter_le`), and
  the singular set is empty for `d ≤ 7`.

The reduction runs by induction on the ambient dimension. A singular point of a cone away from the
vertex with positive content density has a tangent cone keeping positive singular measure (GR15);
it is invariant along that point (GR5) and is a rotated cylinder over a minimizing cone one
dimension lower (GR6); the singular set of the cylinder lies over the singular set of the cross
section, and cylinders over `μH[s - 1]`-null sets are `μH[s]`-null.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace SerrinEpigraph

/-- **Upper semicontinuity of singular sets (GR14), as a hypothesis.** If a sequence of sets which
are eventually local perimeter minimizers on every ball converges in `L¹_loc` to a global local
minimizer, then limits of singular points of the sequence are singular points of the limit. -/
def SingularSetUSCHyp : Prop :=
  ∀ (d : ℕ) (E : ℕ → Set (Space d)) (F : Set (Space d)),
    (∀ R : ℝ, 0 < R → ∀ᶠ j in atTop,
      IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin d) ℝ) (E j) (ball 0 R)) →
    IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin d) ℝ) F univ →
    (∀ K : Set (Space d), IsCompact K → Tendsto (fun j ↦ ∫ y in K,
      ‖(E j).indicator (fun _ ↦ (1 : ℝ)) y - F.indicator (fun _ ↦ (1 : ℝ)) y‖) atTop (𝓝 0)) →
    ∀ (x : ℕ → Space d) (x₀ : Space d), (∀ j, x j ∈ singularSet (E j)) →
      Tendsto x atTop (𝓝 x₀) → x₀ ∈ singularSet F

/-! ### 1. Cylinders over null sets -/

private theorem norm_point_le_aux {k : ℕ} (a : Space k) (b : ℝ) : ‖point a b‖ ≤ ‖a‖ + |b| := by
  have h : point a b = point a 0 + b • verticalDirection k := by
    rw [point_add_vertical, zero_add]
  rw [h]
  refine (norm_add_le _ _).trans ?_
  have hn : ‖verticalDirection k‖ = 1 := by simp [verticalDirection]
  rw [norm_point_zero, norm_smul, Real.norm_eq_abs, hn, mul_one]

private theorem point_sub_point_aux {k : ℕ} (a a' : Space k) (b b' : ℝ) :
    point a b - point a' b' = point (a - a') (b - b') := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [point]

/-- `(t, y) ↦ point y t` is `2`-Lipschitz for the maximum metric on `ℝ × Space k`. -/
private theorem lipschitzWith_point_prod (k : ℕ) :
    LipschitzWith 2 (fun p : ℝ × Space k ↦ point p.2 p.1) := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  rw [dist_eq_norm, point_sub_point_aux, Prod.dist_eq, dist_eq_norm p.2 q.2, Real.dist_eq]
  have h := norm_point_le_aux (p.2 - q.2) (p.1 - q.1)
  have h1 : ‖p.2 - q.2‖ ≤ max |p.1 - q.1| ‖p.2 - q.2‖ := le_max_right _ _
  have h2 : |p.1 - q.1| ≤ max |p.1 - q.1| ‖p.2 - q.2‖ := le_max_left _ _
  push_cast
  linarith

/-- Cylinders over `μH[s]`-null sets are `μH[s + 1]`-null. -/
theorem hausdorffMeasure_preimage_horizontal_eq_zero {k : ℕ} {s : ℝ} (hs : 0 < s)
    {A : Set (Space k)} (hA : μH[s] A = 0) :
    μH[s + 1] (horizontal ⁻¹' A : Set (Space (k + 1))) = 0 := by
  have hA' : hausdorffContent s A = 0 :=
    (hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero hs.le).mp hA
  have hpiece : ∀ n : ℕ, hausdorffContent (s + 1)
      ((fun p : ℝ × Space k ↦ point p.2 p.1) '' (Icc (-(n : ℝ)) n ×ˢ A)) = 0 := by
    intro n
    have h1 := hausdorffContent_image_le_of_lipschitzWith (lipschitzWith_point_prod k)
      (by linarith : (0 : ℝ) ≤ s + 1) (Icc (-(n : ℝ)) n ×ˢ A)
    rw [hausdorffContent_Icc_prod_eq_zero hs _ _ hA', mul_zero] at h1
    exact le_antisymm h1 bot_le
  have hcover : (horizontal ⁻¹' A : Set (Space (k + 1))) ⊆
      ⋃ n : ℕ, (fun p : ℝ × Space k ↦ point p.2 p.1) '' (Icc (-(n : ℝ)) n ×ˢ A) := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge |x (Fin.last k)|
    exact mem_iUnion.mpr ⟨n, (x (Fin.last k), horizontal x), ⟨abs_le.mp hn, hx⟩,
      point_horizontal_last x⟩
  rw [hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero (by linarith)]
  refine le_antisymm ((hausdorffContent_mono _ hcover).trans
    ((hausdorffContent_iUnion_le _ _).trans ?_)) bot_le
  simp [hpiece]

private theorem hausdorffMeasure_singleton_eq_zero_aux {d : ℕ} {s : ℝ} (hs : 0 < s)
    (x : Space d) : μH[s] ({x} : Set (Space d)) = 0 := by
  rw [hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero hs.le]
  refine le_antisymm ((hausdorffContent_le_ediam_rpow s _).trans ?_) bot_le
  rw [ediam_singleton, ENNReal.zero_rpow_of_pos hs]

private theorem ne_zero_of_norm_eq_one_aux {d : ℕ} {e : Space d} (he : ‖e‖ = 1) : e ≠ 0 := by
  intro h0
  rw [h0, norm_zero] at he
  exact zero_ne_one he

/-! ### 2. GR15: singular content survives in a tangent cone -/

/-- Blow-ups of a local minimizer at a point of its domain are eventually minimizers on every
ball. -/
private theorem eventually_isLocalPerimeterMinimizer_blowup {m : ℕ}
    {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E Ω)
    {p : Space (m + 1)} (hp : p ∈ Ω) {r : ℕ → ℝ} (hr_pos : ∀ j, 0 < r j)
    (hr : Tendsto r atTop (𝓝 0)) (R : ℝ) :
    ∀ᶠ j in atTop, IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)
      ((fun z ↦ p + r j • z) ⁻¹' E) (ball 0 R) := by
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hmin.isOpen_domain p hp
  have hprod_lim : Tendsto (fun j ↦ r j * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using hr.mul_const R
  filter_upwards [hprod_lim.eventually (gt_mem_nhds hr₀)] with j hj
  refine (hmin.preimage_add_smul (by omega) p (hr_pos j)).mono isOpen_ball ?_
  intro y hy
  apply hball₀
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (hr_pos j).le]
  exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hy) (hr_pos j)).trans hj

/-- **GR15.** If the singular set of a local perimeter minimizer has positive `μH[s]`-measure in
its domain, then at some singular point outside a prescribed `μH[s]`-null set there is a tangent
cone whose singular set still has positive `μH[s]`-measure. The point is a content density point;
along the radii preserving content, the blown-up singular sets accumulate only on the singular set
of the limit cone (upper semicontinuity), and the Hausdorff content is upper semicontinuous under
such convergence. -/
theorem IsLocalPerimeterMinimizer.exists_isTangentCone_hausdorffMeasure_singularSet_ne_zero
    (husc : SingularSetUSCHyp) {m : ℕ} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E Ω)
    {s : ℝ} (hs : 0 ≤ s) {N : Set (Space (m + 1))} (hN : μH[s] N = 0)
    (hA : μH[s] (singularSet E ∩ Ω) ≠ 0) :
    ∃ p ∈ singularSet E ∩ Ω, p ∉ N ∧ ∃ C : Set (Space (m + 1)),
      IsTangentCone E p C ∧ IsMinimizingCone C ∧ μH[s] (singularSet C) ≠ 0 := by
  set A := singularSet E ∩ Ω with hAdef
  obtain ⟨p, hpA, hpN, hdens⟩ := exists_mem_one_le_upperContentDensity hs hA hN
  have hhalf : (1 / 2 : ℝ≥0∞) < upperContentDensity s A p :=
    lt_of_lt_of_le (by norm_num) hdens
  obtain ⟨r, hr_pos, hr_lim, hr_content⟩ :=
    exists_seq_lt_hausdorffContent_blowup_inter_closedBall hs hhalf
  have hr0 : Tendsto r atTop (𝓝 0) := hr_lim.mono_right nhdsWithin_le_nhds
  have hpBd : p ∈ measureTheoreticBoundary E := hpA.1.1
  obtain ⟨φ, C, hφ, hC, hlim, -, -⟩ := hmin.exists_isBlowupLimit ⟨hpBd, hpA.2⟩ hr_pos hr0
  refine ⟨p, hpA, hpN, C, ⟨hC.measurableSet, r ∘ φ, hlim⟩, hC, ?_⟩
  set S : ℕ → Set (Space (m + 1)) := fun j ↦
    ((fun y ↦ (r (φ j))⁻¹ • (y - p)) '' A) ∩ closedBall 0 1 with hSdef
  set Ej : ℕ → Set (Space (m + 1)) := fun j ↦ (fun z ↦ p + r (φ j) • z) ⁻¹' E with hEjdef
  have hSsing : ∀ j, S j ⊆ singularSet (Ej j) := by
    rintro j _ ⟨⟨y, hyA, rfl⟩, -⟩
    show (r (φ j))⁻¹ • (y - p) ∈ singularSet ((fun z ↦ p + r (φ j) • z) ⁻¹' E)
    rw [mem_singularSet_preimage_add_smul_iff (hr_pos (φ j))]
    have hy : p + r (φ j) • ((r (φ j))⁻¹ • (y - p)) = y := by
      rw [smul_smul, mul_inv_cancel₀ (hr_pos (φ j)).ne', one_smul]
      abel
    rw [hy]
    exact hyA.1
  set K : Set (Space (m + 1)) := singularSet C ∩ closedBall 0 1 with hKdef
  have hKc : IsCompact K := (isCompact_closedBall 0 1).inter_left (isClosed_singularSet C)
  have hmin_ev : ∀ R : ℝ, 0 < R → ∀ᶠ j in atTop,
      IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (Ej j) (ball 0 R) :=
    fun R _ ↦ hφ.tendsto_atTop.eventually
      (eventually_isLocalPerimeterMinimizer_blowup hmin hpA.2 hr_pos hr0 R)
  have hthick : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, S j ⊆ thickening ε K := by
    intro ε hε
    by_contra hne
    have hfreq : ∃ᶠ j in atTop, ∃ y, y ∈ S j ∧ y ∉ thickening ε K := by
      rw [not_eventually] at hne
      exact hne.mono fun j hj ↦ not_subset.mp hj
    obtain ⟨ψ, hψ, hψy⟩ := extraction_of_frequently_atTop hfreq
    choose y hyS hyK using hψy
    obtain ⟨y₀, hy₀B, χ, hχ, hconv⟩ :=
      (isCompact_closedBall (0 : Space (m + 1)) 1).tendsto_subseq fun n ↦ (hyS n).2
    have hsub : StrictMono (ψ ∘ χ) := hψ.comp hχ
    have hy₀ : y₀ ∈ singularSet C := by
      refine husc (m + 1) (fun n ↦ Ej (ψ (χ n))) C ?_ hC.minimizer ?_ (fun n ↦ y (χ n)) y₀
        (fun n ↦ hSsing _ (hyS (χ n))) hconv
      · intro R hR
        exact hsub.tendsto_atTop.eventually (hmin_ev R hR)
      · intro K' hK'
        exact (hlim.2.2 K' hK').comp hsub.tendsto_atTop
    obtain ⟨n, hn⟩ := (hconv.eventually (isOpen_ball.mem_nhds (mem_ball_self hε))).exists
    exact hyK (χ n) (mem_thickening_iff.mpr ⟨y₀, ⟨hy₀, hy₀B⟩, hn⟩)
  have hlimsup := limsup_hausdorffContent_le hs hKc hthick
  have hle : (1 / 2 : ℝ≥0∞) ≤ hausdorffContent s K :=
    (le_limsup_of_frequently_le
      (Eventually.of_forall fun j ↦ (hr_content (φ j)).le).frequently).trans hlimsup
  intro h0
  have hK0 : hausdorffContent s K = 0 :=
    (hausdorffMeasure_eq_zero_iff_hausdorffContent_eq_zero hs).mp
      (measure_mono_null inter_subset_left h0)
  rw [hK0] at hle
  norm_num at hle

/-! ### 3. GR17: dimension reduction -/

/-- **GR17 for minimizing cones.** Given ε-regularity, upper semicontinuity of singular sets and
the classification of minimizing cones in dimensions at most seven, the singular set of a
minimizing cone in `Space d` is `μH[s]`-null for every `s > d - 8`. -/
theorem IsMinimizingCone.hausdorffMeasure_singularSet_eq_zero (husc : SingularSetUSCHyp)
    (hclass : ∀ k ≤ 7, ConeClassification k) :
    ∀ (d : ℕ) {C : Set (Space d)}, IsMinimizingCone C → ∀ s : ℝ, (d : ℝ) - 8 < s →
      μH[s] (singularSet C) = 0 := by
  intro d
  induction d with
  | zero =>
    intro C hC
    exact absurd hC (not_isMinimizingCone_space_zero C)
  | succ k ih =>
    intro C hC s hs
    by_cases hk7 : k + 1 ≤ 7
    · obtain ⟨e, he, hCe⟩ := hclass (k + 1) hk7 C hC
      rw [singularSet_eq_empty_of_ae_eq_positiveHalfspace (ne_zero_of_norm_eq_one_aux he) hCe,
        measure_empty]
    · have hk : 7 ≤ k := by omega
      have hkR : (7 : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at hs
      have hs0 : 0 < s := by linarith
      by_contra hne
      have hA : μH[s] (singularSet C ∩ univ) ≠ 0 := by rwa [inter_univ]
      obtain ⟨p, hpA, hp0, C₁, hC₁t, hC₁, hC₁s⟩ :=
        hC.minimizer.exists_isTangentCone_hausdorffMeasure_singularSet_ne_zero husc hs0.le
          (hausdorffMeasure_singleton_eq_zero_aux hs0 0) hA
      have hp0' : p ≠ 0 := fun h ↦ hp0 (by rw [h]; rfl)
      have hpBd : p ∈ measureTheoreticBoundary C := hpA.1.1
      have hinv := hC₁t.ae_mem_add_smul_iff hC hpBd
      set v : Space (k + 1) := ‖p‖⁻¹ • p with hvdef
      have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp0'
      have hv : ‖v‖ = 1 := by
        rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have hinv' : ∀ t : ℝ, ∀ᵐ x ∂volume, x ∈ C₁ ↔ x + t • v ∈ C₁ := by
        intro t
        filter_upwards [hinv (t * ‖p‖⁻¹)] with x hx
        rw [hvdef, smul_smul]
        exact hx
      obtain ⟨Q, C₁', -, -, hC₁'c, hae⟩ := hC₁.exists_cylinder_of_invariant hv hinv'
      have hae' : C₁ =ᵐ[volume] (Q.symm ⁻¹' (horizontal ⁻¹' C₁') : Set (Space (k + 1))) := hae
      have hsub : singularSet C₁ ⊆ Q.symm ⁻¹' (horizontal ⁻¹' singularSet C₁') := by
        rw [singularSet_congr_ae hae']
        intro x hx
        have h1 : Q.symm x ∈ singularSet (horizontal ⁻¹' C₁' : Set (Space (k + 1))) :=
          (mem_singularSet_preimage_linearIsometryEquiv_iff
            (E := (horizontal ⁻¹' C₁' : Set (Space (k + 1)))) Q.symm).mp hx
        exact singularSet_preimage_horizontal_subset C₁' h1
      have hcyl0 : μH[s] (horizontal ⁻¹' singularSet C₁' : Set (Space (k + 1))) = 0 := by
        by_cases hk8 : k ≤ 7
        · obtain ⟨e', he', hC₁'e⟩ := hclass k hk8 C₁' hC₁'c
          rw [singularSet_eq_empty_of_ae_eq_positiveHalfspace (ne_zero_of_norm_eq_one_aux he')
            hC₁'e, preimage_empty, measure_empty]
        · have hk8' : (8 : ℝ) ≤ k := by exact_mod_cast (by omega : 8 ≤ k)
          have hs1 : 0 < s - 1 := by linarith
          have h1 := ih hC₁'c (s - 1) (by linarith)
          have h2 := hausdorffMeasure_preimage_horizontal_eq_zero hs1 h1
          rwa [sub_add_cancel] at h2
      apply hC₁s
      refine measure_mono_null hsub ?_
      have hiso := IsometryEquiv.hausdorffMeasure_preimage Q.symm.toIsometryEquiv s
        (horizontal ⁻¹' singularSet C₁' : Set (Space (k + 1)))
      simp only [LinearIsometryEquiv.coe_toIsometryEquiv] at hiso
      rw [hiso]
      exact hcyl0

/-- In ambient dimension at most seven, local perimeter minimizers have no singular points in
their domain (given ε-regularity and the classification of minimizing cones). -/
theorem IsLocalPerimeterMinimizer.singularSet_inter_eq_empty_of_le_seven
    (hreg : EpsilonRegularityHyp) (hclass : ∀ k ≤ 7, ConeClassification k) {m : ℕ}
    (hm : m + 1 ≤ 7) {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E Ω) :
    singularSet E ∩ Ω = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx ↦ hx.1.2 ?_
  obtain ⟨φ, T, -, hT, hlim, -, -⟩ := hmin.exists_isBlowupLimit ⟨hx.1.1, hx.2⟩
    (r := fun j ↦ 1 / ((j : ℝ) + 1)) (fun j ↦ by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨e, he, hTe⟩ := hclass (m + 1) hm T hT
  exact hreg (m + 1) E Ω x hmin ⟨hx.1.1, hx.2⟩ ⟨T, ⟨hT.measurableSet, _, hlim⟩, e, he, hTe⟩

/-- **GR17.** Given ε-regularity, upper semicontinuity of singular sets and the classification of
minimizing cones in dimensions at most seven, the singular set of a local perimeter minimizer in
`Space (m + 1)` is `μH[s]`-null in its domain for every `s > m + 1 - 8`. -/
theorem IsLocalPerimeterMinimizer.hausdorffMeasure_singularSet_inter_eq_zero
    (hreg : EpsilonRegularityHyp) (husc : SingularSetUSCHyp)
    (hclass : ∀ k ≤ 7, ConeClassification k) {m : ℕ} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E Ω)
    {s : ℝ} (hs : ((m + 1 : ℕ) : ℝ) - 8 < s) : μH[s] (singularSet E ∩ Ω) = 0 := by
  by_cases hm : m + 1 ≤ 7
  · rw [hmin.singularSet_inter_eq_empty_of_le_seven hreg hclass hm, measure_empty]
  · have hmR : (8 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 8 ≤ m + 1)
    have hs0 : 0 ≤ s := by linarith
    by_contra hne
    obtain ⟨p, -, -, C, -, hC, hCs⟩ :=
      hmin.exists_isTangentCone_hausdorffMeasure_singularSet_ne_zero husc hs0 (N := ∅)
        measure_empty hne
    exact hCs (IsMinimizingCone.hausdorffMeasure_singularSet_eq_zero husc hclass (m + 1) hC s hs)

/-- **Dimension bound.** The singular set of a local perimeter minimizer in `Space (m + 1)` has
Hausdorff dimension at most `m + 1 - 8` (it is empty when `m + 1 ≤ 7`). -/
theorem IsLocalPerimeterMinimizer.dimH_singularSet_inter_le
    (hreg : EpsilonRegularityHyp) (husc : SingularSetUSCHyp)
    (hclass : ∀ k ≤ 7, ConeClassification k) {m : ℕ} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E Ω) :
    dimH (singularSet E ∩ Ω) ≤ ((m + 1 - 8 : ℕ) : ℝ≥0∞) := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  rcases eq_or_ne c ⊤ with rfl | hctop
  · exact le_top
  lift c to ℝ≥0 using hctop
  apply dimH_le_of_hausdorffMeasure_ne_top
  have h1 : ((m + 1 - 8 : ℕ) : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have h2 : ((m + 1 : ℕ) : ℝ) - 8 ≤ ((m + 1 - 8 : ℕ) : ℝ) := by
    rcases le_or_gt 8 (m + 1) with h | h
    · rw [Nat.cast_sub h]
      simp
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      have : ((m + 1 : ℕ) : ℝ) < 8 := by exact_mod_cast h
      linarith
  rw [hmin.hausdorffMeasure_singularSet_inter_eq_zero hreg husc hclass (by linarith)]
  exact ENNReal.zero_ne_top

/-- **GR17 with the GR16 inputs.** Given ε-regularity, upper semicontinuity of singular sets and
Simons' theorem in dimensions two to seven, singular sets of local perimeter minimizers in
`Space (m + 1)` have Hausdorff dimension at most `m + 1 - 8`. -/
theorem IsLocalPerimeterMinimizer.dimH_singularSet_inter_le_of_simonsHyp
    (hreg : EpsilonRegularityHyp) (husc : SingularSetUSCHyp)
    (hs : ∀ k, 2 ≤ k → k ≤ 7 → SimonsHyp k) {m : ℕ} {E Ω : Set (Space (m + 1))}
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) E Ω) :
    dimH (singularSet E ∩ Ω) ≤ ((m + 1 - 8 : ℕ) : ℝ≥0∞) :=
  hmin.dimH_singularSet_inter_le hreg husc (coneClassification_of_simonsHyp hreg hs)

end SerrinEpigraph
