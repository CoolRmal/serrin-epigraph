module

public import SerrinEpigraph.GraphDivergence
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Graph divergence with local regularity near the support
-/

public section

open Set MeasureTheory Filter InnerProductSpace
open scoped Topology

namespace SerrinEpigraph

/-- Cutting off a locally C1 vector field inside its regularity domain makes it globally C1. -/
theorem contDiff_smul_of_tsupport_subset {d : ℕ} {F : Space d → Space d}
    {χ : Space d → ℝ} {Ω : Set (Space d)} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ 1 F Ω) (hχ : ContDiff ℝ 1 χ) (hs : tsupport χ ⊆ Ω) :
    ContDiff ℝ 1 (fun x ↦ χ x • F x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Ω
  · exact hχ.contDiffAt.smul (hF.contDiffAt (hΩ.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : Space d))).congr_of_eventuallyEq
    have hz := notMem_tsupport_iff_eventuallyEq.mp (fun hx' ↦ hx (hs hx'))
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_smul]

/-- Graph Gauss applies when the compact field is C1 only near the part of its
support that meets the closed epigraph. -/
theorem integral_epigraph_divergence_of_contDiffOn {d : ℕ}
    (basis : OrthonormalBasis (Fin (d + 1)) ℝ (Space (d + 1)))
    {b : Space d → ℝ} (hb : ContDiff ℝ 1 b) {F : Space (d + 1) → Space (d + 1)}
    {Ω : Set (Space (d + 1))} (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ 1 F Ω)
    (hc : HasCompactSupport F) (hs : closure (epigraph b) ∩ tsupport F ⊆ Ω) :
    (∫ x in epigraph b, fieldDivergence basis F x) =
      ∫ y, inner ℝ (point (gradient b y) (-1)) (F (point y (b y))) := by
  let K := closure (epigraph b) ∩ tsupport F
  have hK : IsCompact K := hc.inter_left isClosed_closure
  obtain ⟨V, hVo, hKV, hVΩ, _⟩ := exists_open_between_and_isCompact_closure hK hΩ hs
  obtain ⟨χ, hχ, _, hχs, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hVo hK.isClosed hKV
  have hχΩ : tsupport χ ⊆ Ω := by
    change closure (Function.support χ) ⊆ Ω
    rwa [hχs]
  let G := fun x ↦ χ x • F x
  have hGc : HasCompactSupport G :=
    hc.of_isClosed_subset (isClosed_tsupport _)
      (closure_mono (Function.support_smul_subset_right χ F))
  have hG : ContDiff ℝ 1 G := contDiff_smul_of_tsupport_subset hΩ hF hχ hχΩ
  have heq : EqOn G F (closure (epigraph b)) := by
    intro x hx
    by_cases hxs : x ∈ tsupport F
    · simp only [G, (hχone x).mp ⟨hx, hxs⟩, one_smul]
    · simp only [G, image_eq_zero_of_notMem_tsupport hxs, smul_zero]
  have hdiv : EqOn (fieldDivergence basis G) (fieldDivergence basis F) (epigraph b) := by
    intro x hx
    have hev' : G =ᶠ[𝓝 x] F := by
      filter_upwards [(isOpen_epigraph hb.continuous).mem_nhds hx] with y hy
      exact heq (subset_closure hy)
    simp only [fieldDivergence, hev'.fderiv_eq]
  rw [← setIntegral_congr_fun (isOpen_epigraph hb.continuous).measurableSet hdiv,
    integral_epigraph_divergence basis hb hG hGc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y ↦ by
    dsimp only
    rw [heq (point_mem_closure_epigraph (le_refl (b y)))])

end SerrinEpigraph
