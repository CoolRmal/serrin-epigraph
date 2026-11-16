module

public import SerrinEpigraph.StressStationarity

/-!
# Gauss' formula with a continuous trace on a graph

The vector field needs one derivative only in the open epigraph. Its field and
divergence have continuous extensions to the closed epigraph. Raising the graph
and passing to the limit gives the boundary flux without a second derivative
assumption on the boundary values.
-/

public section

noncomputable section

open Set MeasureTheory InnerProductSpace Filter Metric
open scoped Topology

namespace SerrinEpigraph

/-- Compact support and continuity on the closed domain give integrability
over the open domain, even without continuity outside it. -/
theorem integrableOn_of_continuousOn_closure_compact_support {d : ℕ}
    {Ω : Set (Space d)} {v : Space d → ℝ} (hΩ : MeasurableSet Ω)
    (hv : ContinuousOn v (closure Ω)) (hc : HasCompactSupport v) : IntegrableOn v Ω := by
  let K := tsupport v ∩ closure Ω
  have hK : IsCompact K := hc.inter_right isClosed_closure
  have hi : IntegrableOn v K := (hv.mono inter_subset_right).integrableOn_compact hK
  apply (integrable_indicator_iff hΩ).mp
  apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp (hi.indicator hΩ)
  intro x hx
  have hxΩ : x ∈ Ω := by
    by_contra hn
    exact hx (indicator_of_notMem hn v)
  refine ⟨?_, subset_closure hxΩ⟩
  apply subset_tsupport v
  change Ω.indicator v x ≠ 0 at hx
  change v x ≠ 0
  simpa only [indicator_of_mem hxΩ] using hx

/-- A compact continuous closed-domain trace has a continuous graph flux as
the graph is shifted upwards. -/
theorem continuousOn_closed_graph_flux {m : ℕ} {g : Space m → ℝ}
    (hg : ContDiff ℝ 1 g) {F : Space (m + 1) → Space (m + 1)}
    (hF : ContinuousOn F (closure (epigraph g))) (hc : HasCompactSupport F) :
    ContinuousOn (fun t : ℝ ↦ ∫ y, inner ℝ (point (gradient g y) (-1))
      (F (point y (g y + t)))) (Ici 0) := by
  let K := horizontal '' tsupport F
  have hK : IsCompact K := hc.image continuous_horizontal
  apply continuousOn_integral_of_compact_support (μ := volume) hK
  · have hnormal : Continuous (fun p : ℝ × Space m ↦ point (gradient g p.2) (-1)) :=
      pointContinuousLinearMap.continuous.comp
        (((toDual ℝ (Space m)).symm.continuous.comp
          (hg.continuous_fderiv one_ne_zero)).comp continuous_snd |>.prodMk continuous_const)
    have hpoint : Continuous (fun p : ℝ × Space m ↦ point p.2 (g p.2 + p.1)) :=
      pointContinuousLinearMap.continuous.comp
        (continuous_snd.prodMk ((hg.continuous.comp continuous_snd).add continuous_fst))
    exact hnormal.continuousOn.inner (hF.comp hpoint.continuousOn
      (fun p hp ↦ point_mem_closure_epigraph (le_add_of_nonneg_right hp.1)))
  · intro t y _ hy
    have hx : point y (g y + t) ∉ tsupport F := fun hh ↦
      hy ⟨point y (g y + t), hh, horizontal_point _ _⟩
    simp only [image_eq_zero_of_notMem_tsupport hx, inner_zero_right]

/-- Gauss' formula on the epigraph with only a continuous boundary trace. -/
theorem integral_epigraph_divergence_of_continuous_trace {m : ℕ}
    (basis : OrthonormalBasis (Fin (m + 1)) ℝ (Space (m + 1)))
    {g : Space m → ℝ} (hg : ContDiff ℝ 1 g)
    {F Fbar : Space (m + 1) → Space (m + 1)} {D : Space (m + 1) → ℝ}
    (hF : ContDiffOn ℝ 1 F (epigraph g)) (hcF : HasCompactSupport F)
    (hbar : ContinuousOn Fbar (closure (epigraph g))) (hcbar : HasCompactSupport Fbar)
    (heq : EqOn Fbar F (epigraph g)) (hD : ContinuousOn D (closure (epigraph g)))
    (hcD : HasCompactSupport D) (hdiv : EqOn (fieldDivergence basis F) D (epigraph g)) :
    (∫ x in epigraph g, D x) =
      ∫ y, inner ℝ (point (gradient g y) (-1)) (Fbar (point y (g y))) := by
  have hleft := tendsto_integral_shifted_epigraph hg.continuous
    (integrableOn_of_continuousOn_closure_compact_support
      (isOpen_epigraph hg.continuous).measurableSet hD hcD)
  have hε : Tendsto (fun j : ℕ ↦ 1 / (j + 1 : ℝ)) atTop (𝓝[Ici 0] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall (fun j ↦ by change 0 ≤ 1 / (j + 1 : ℝ); positivity)⟩
  have hright := ((continuousOn_closed_graph_flux hg hbar hcbar) 0 (by simp)).tendsto.comp hε
  simp only [add_zero] at hright
  have hsame (j : ℕ) :
      (∫ x in epigraph (fun y ↦ g y + 1 / (j + 1 : ℝ)), D x) =
      ∫ y, inner ℝ (point (gradient g y) (-1))
        (Fbar (point y (g y + 1 / (j + 1 : ℝ)))) := by
    have hs := closure_shifted_epigraph_subset hg.continuous
      (by positivity : 0 < 1 / (j + 1 : ℝ))
    have hgj := hg.add (contDiff_const (c := 1 / (j + 1 : ℝ)))
    have hggrad : gradient (fun y ↦ g y + 1 / (j + 1 : ℝ)) = gradient g := by
      funext y
      simp only [gradient, fderiv_add_const]
    rw [← setIntegral_congr_fun (isOpen_epigraph hgj.continuous).measurableSet
      (fun x hx ↦ hdiv (hs (subset_closure hx)))]
    rw [integral_epigraph_divergence_of_contDiffOn basis hgj
      (isOpen_epigraph hg.continuous) hF hcF (fun x hx ↦ hs hx.1), hggrad]
    apply integral_congr_ae
    filter_upwards with y
    have hx : point y (g y + 1 / (j + 1 : ℝ)) ∈ epigraph g := by
      simp only [epigraph, mem_ofPred_eq, horizontal_point, last_point, lt_add_iff_pos_right]
      positivity
    rw [heq hx]
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall (fun j ↦ (hsame j).symm)))

end SerrinEpigraph
