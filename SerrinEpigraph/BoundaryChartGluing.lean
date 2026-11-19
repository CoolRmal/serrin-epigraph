module

public import SerrinEpigraph.BoundaryChartGeometry
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Gluing smooth boundary charts

* `exists_isSmoothBoundaryChart_superset`: a compact subset of the measure-theoretic boundary each
  of whose points lies in a smooth chart lies in a *single* smooth chart. The glued defining
  function is `∑ βᵢ Fᵢ` for finitely many bump functions `βᵢ ≥ 0` supported in the charts
  `(Uᵢ, Fᵢ)`: the charts have the same sign pattern on overlaps, and at boundary points their
  gradients are positive multiples of the common normal, so the glued gradient does not vanish.
* `exists_contDiff_eventually_one_tsupport_subset`: smooth Urysohn functions for a compact set
  inside an open set.
* `C1RegularSmoothHyp`: the Schauder regularity of `C¹` boundary points of perimeter minimizers, as
  a named hypothesis, and its consequences for charts near regular points.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory InnerProductSpace Filter
open scoped Topology ContDiff Manifold

namespace SerrinEpigraph

/-- **Schauder regularity of `C¹` boundary points, as a hypothesis.** Every `C¹` boundary point of a
local perimeter minimizer in the whole space lies in a smooth boundary chart. -/
def C1RegularSmoothHyp : Prop :=
  ∀ (d : ℕ) (E : Set (Space d)) (x : Space d),
    IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin d) ℝ) E univ →
    IsC1BoundaryPoint E x → ∃ U F, x ∈ U ∧ IsSmoothBoundaryChart E U F

/-- **Smooth Urysohn lemma.** A compact set inside an open set has a smooth cutoff with values in
`[0, 1]`, equal to one near the compact set, with compact topological support inside the open
set. -/
theorem exists_contDiff_eventually_one_tsupport_subset {d : ℕ} {K U : Set (Space d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : Space d → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ K, ∀ᶠ z in 𝓝 x, χ z = 1) ∧ tsupport χ ⊆ U ∧ HasCompactSupport χ := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hsub : K ⊆ interior (cthickening (δ / 2) K) :=
    (self_subset_thickening (by positivity) K).trans
      (thickening_subset_interior_cthickening (δ / 2) K)
  obtain ⟨f, hf1, hf0, hf01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, Space d) (n := ⊤) hK.isClosed hsub
  have htsupp : tsupport f ⊆ cthickening (δ / 2) K := by
    refine closure_minimal (fun x hx ↦ ?_) isClosed_cthickening
    by_contra hxt
    exact hx (hf0 x hxt)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, hf01, fun x hx ↦ ?_,
    htsupp.trans ((cthickening_mono (by linarith) K).trans hδU), ?_⟩
  · exact (eventually_nhdsSet_iff_forall.mp hf1) x hx
  · exact hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp

/-- **Gluing charts.** A compact subset of the measure-theoretic boundary each of whose points lies
in a smooth chart lies in a single smooth chart. -/
theorem exists_isSmoothBoundaryChart_superset {d : ℕ} {E K : Set (Space d)} (hK : IsCompact K)
    (hKB : K ⊆ measureTheoreticBoundary E)
    (hchart : ∀ x ∈ K, ∃ U F, x ∈ U ∧ IsSmoothBoundaryChart E U F) :
    ∃ U F, K ⊆ U ∧ IsSmoothBoundaryChart E U F := by
  classical
  choose! Uc Fc hxU hch using hchart
  have hbump : ∀ x ∈ K, ∃ β : Space d → ℝ, tsupport β ⊆ Uc x ∧ HasCompactSupport β ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ range β ⊆ Icc 0 1 ∧ β x = 1 :=
    fun x hx ↦ exists_contDiff_tsupport_subset (n := ⊤) ((hch x hx).isOpen.mem_nhds (hxU x hx))
  choose! β hβU _ hβs hβr hβx using hbump
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ {z | 0 < β x z}) fun x hx ↦
    (isOpen_lt continuous_const (hβs x hx).continuous).mem_nhds (by simp [hβx x hx])
  have hβ0 : ∀ x ∈ t, ∀ z, 0 ≤ β x z := fun x hx z ↦ (hβr x (htK x hx) ⟨z, rfl⟩).1
  have hβU' : ∀ x ∈ t, ∀ z, 0 < β x z → z ∈ Uc x := fun x hx z hz ↦
    hβU x (htK x hx) (subset_tsupport _ hz.ne')
  -- the glued defining function
  set Fg : Space d → ℝ := fun z ↦ ∑ x ∈ t, β x z • Fc x z with hFg
  have hterm : ∀ x ∈ t, ContDiff ℝ ∞ (fun z ↦ β x z • Fc x z) := fun x hx ↦
    contDiff_smul_of_tsupport_subset_of_contDiffOn (hch x (htK x hx)).isOpen
      (hch x (htK x hx)).contDiffOn (hβs x (htK x hx)) (hβU x (htK x hx))
  have hFgs : ContDiff ℝ ∞ Fg := ContDiff.sum fun x hx ↦ hterm x hx
  set W : Set (Space d) := {z | 0 < ∑ x ∈ t, β x z} with hW
  have hWopen : IsOpen W :=
    isOpen_lt continuous_const (continuous_finsetSum _ fun x hx ↦ (hβs x (htK x hx)).continuous)
  have hexists : ∀ z ∈ W, ∃ x₁ ∈ t, 0 < β x₁ z := by
    intro z hz
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have : ∑ x ∈ t, β x z ≤ 0 := Finset.sum_nonpos fun x hx ↦ hcon x hx
    exact absurd hz (not_lt.mpr this)
  -- sign of the glued function
  have hsign : ∀ z ∈ W, ∀ x₁ ∈ t, 0 < β x₁ z → (0 < Fg z ↔ 0 < Fc x₁ z) := by
    intro z _ x₁ hx₁ hβx₁
    have hz₁ := hβU' x₁ hx₁ z hβx₁
    constructor
    · intro hpos
      by_contra hle
      have : Fg z ≤ 0 := by
        refine Finset.sum_nonpos fun x hx ↦ ?_
        rcases (hβ0 x hx z).lt_or_eq with hβpos | hβeq
        · have hFx : Fc x z ≤ 0 := by
            by_contra hF
            exact hle (((hch x₁ (htK x₁ hx₁)).pos_iff_pos_of_mem (hch x (htK x hx)) hz₁
              (hβU' x hx z hβpos)).mpr (not_le.mp hF))
          rw [smul_eq_mul]
          exact mul_nonpos_of_nonneg_of_nonpos hβpos.le hFx
        · rw [← hβeq, zero_smul]
      exact absurd hpos (not_lt.mpr this)
    · intro hpos
      refine Finset.sum_pos' (fun x hx ↦ ?_) ⟨x₁, hx₁, ?_⟩
      · rcases (hβ0 x hx z).lt_or_eq with hβpos | hβeq
        · have hFx : 0 < Fc x z := ((hch x₁ (htK x₁ hx₁)).pos_iff_pos_of_mem
            (hch x (htK x hx)) hz₁ (hβU' x hx z hβpos)).mp hpos
          rw [smul_eq_mul]
          exact (mul_pos hβpos hFx).le
        · rw [← hβeq, zero_smul]
      · rw [smul_eq_mul]
        exact mul_pos hβx₁ hpos
  -- derivative of the glued function at boundary points
  have hderiv : ∀ z ∈ measureTheoreticBoundary E,
      HasFDerivAt Fg (∑ x ∈ t, β x z • fderiv ℝ (Fc x) z) z := by
    intro z hzB
    have hd : ∀ x ∈ t, HasFDerivAt (fun w ↦ β x w • Fc x w) (β x z • fderiv ℝ (Fc x) z) z := by
      intro x hx
      by_cases hzU : z ∈ Uc x
      · have hFz : Fc x z = 0 :=
          (hch x (htK x hx)).eq_zero_of_mem_measureTheoreticBoundary hzU hzB
        have h1 := ((hβs x (htK x hx)).differentiable (by simp) z).hasFDerivAt.fun_smul
          ((hch x (htK x hx)).hasFDerivAt hzU)
        convert h1 using 1
        ext w
        simp [hFz]
      · have hz : z ∉ tsupport (β x) := fun h ↦ hzU (hβU x (htK x hx) h)
        have hβz : β x z = 0 := image_eq_zero_of_notMem_tsupport hz
        have hev : (fun w ↦ β x w • Fc x w) =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
          simp only [Pi.zero_apply] at hw
          rw [hw, zero_smul]
        rw [hβz, zero_smul]
        exact (hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq hev
    exact HasFDerivAt.fun_sum hd
  have hgrad : ∀ z ∈ W, z ∈ measureTheoreticBoundary E → gradient Fg z ≠ 0 := by
    intro z hzW hzB
    obtain ⟨x₁, hx₁, hβx₁⟩ := hexists z hzW
    have hz₁ := hβU' x₁ hx₁ z hβx₁
    set ν := chartNormal (Fc x₁) z with hν
    have hval : fderiv ℝ Fg z ν = ∑ x ∈ t, β x z * fderiv ℝ (Fc x) z ν := by
      rw [(hderiv z hzB).fderiv]
      simp
    have hpos : 0 < fderiv ℝ Fg z ν := by
      rw [hval]
      have hterm_nonneg : ∀ x ∈ t, 0 < β x z → 0 < fderiv ℝ (Fc x) z ν := by
        intro x hx hβpos
        have hzx := hβU' x hx z hβpos
        rw [hν, ← (hch x₁ (htK x₁ hx₁)).chartNormal_eq_of_mem_boundary (hch x (htK x hx)) hz₁
          hzx hzB, ← inner_gradient_left, real_inner_comm, inner_chartNormal_gradient]
        exact norm_pos_iff.mpr ((hch x (htK x hx)).gradient_ne_zero z hzx)
      refine Finset.sum_pos' (fun x hx ↦ ?_) ⟨x₁, hx₁, mul_pos hβx₁ (hterm_nonneg x₁ hx₁ hβx₁)⟩
      rcases (hβ0 x hx z).lt_or_eq with hβpos | hβeq
      · exact (mul_pos hβpos (hterm_nonneg x hx hβpos)).le
      · rw [← hβeq, zero_mul]
    intro h0
    have hD : fderiv ℝ Fg z = 0 := by simpa [gradient] using h0
    rw [hD] at hpos
    exact lt_irrefl _ hpos
  -- the glued chart
  set Ug : Set (Space d) := W ∩ {z | gradient Fg z ≠ 0} with hUg
  have hgcont : Continuous (gradient Fg) :=
    (toDual ℝ (Space d)).symm.continuous.comp (hFgs.continuous_fderiv (by simp))
  have hUgopen : IsOpen Ug := hWopen.inter (isOpen_ne_fun hgcont continuous_const)
  have hae : ∀ᵐ z ∂volume, ∀ x ∈ t, z ∈ Uc x → (z ∈ E ↔ 0 < Fc x z) :=
    (eventually_all_finset t).mpr fun x hx ↦ (hch x (htK x hx)).ae_mem_iff_of_mem
  refine ⟨Ug, Fg, fun z hzK ↦ ?_, ⟨hUgopen, hFgs.contDiffOn, fun z hz ↦ hz.2, ?_⟩⟩
  · obtain ⟨x₁, hx₁, hβx₁⟩ : ∃ x₁ ∈ t, 0 < β x₁ z := by
      have := hcover hzK
      simp only [mem_iUnion] at this
      obtain ⟨x₁, hx₁, h⟩ := this
      exact ⟨x₁, hx₁, h⟩
    have hzW : z ∈ W := by
      show 0 < ∑ x ∈ t, β x z
      exact Finset.sum_pos' (fun x hx ↦ hβ0 x hx z) ⟨x₁, hx₁, hβx₁⟩
    exact ⟨hzW, hgrad z hzW (hKB hzK)⟩
  · rw [ae_restrict_iff' hUgopen.measurableSet]
    filter_upwards [hae] with z hz hzU
    obtain ⟨x₁, hx₁, hβx₁⟩ := hexists z hzU.1
    rw [hsign z hzU.1 x₁ hx₁ hβx₁]
    exact hz x₁ hx₁ (hβU' x₁ hx₁ z hβx₁)

namespace C1RegularSmoothHyp

variable {d : ℕ} {E : Set (Space d)}

/-- Regular boundary points of a minimizer lie in smooth charts. -/
theorem exists_chart (hsmooth : C1RegularSmoothHyp)
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin d) ℝ) E univ) {x : Space d}
    (hxB : x ∈ measureTheoreticBoundary E) (hxS : x ∉ singularSet E) :
    ∃ U F, x ∈ U ∧ IsSmoothBoundaryChart E U F :=
  hsmooth d E x hmin (by by_contra h; exact hxS ⟨hxB, h⟩)

/-- A compact set of regular boundary points of a minimizer lies in a single smooth chart. -/
theorem exists_chart_superset (hsmooth : C1RegularSmoothHyp)
    (hmin : IsLocalPerimeterMinimizer (EuclideanSpace.basisFun (Fin d) ℝ) E univ)
    {K : Set (Space d)} (hK : IsCompact K) (hKB : K ⊆ measureTheoreticBoundary E)
    (hKS : Disjoint K (singularSet E)) : ∃ U F, K ⊆ U ∧ IsSmoothBoundaryChart E U F :=
  exists_isSmoothBoundaryChart_superset hK hKB fun _ hx ↦
    hsmooth.exists_chart hmin (hKB hx) (disjoint_left.mp hKS hx)

end C1RegularSmoothHyp

end SerrinEpigraph
