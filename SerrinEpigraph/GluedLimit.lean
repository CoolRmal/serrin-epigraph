module

public import SerrinEpigraph.GluingMismatchConvergence

/-!
# Preservation of the candidate limit under gluing
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace SerrinEpigraph

/-- Convex gluing changes the candidate by at most the difference between inputs. -/
theorem norm_gluedCompetitor_sub_candidate_le {d : ℕ} (U v η : Space d → ℝ)
    {x : Space d} (hη : η x ∈ Icc (0 : ℝ) 1) :
    ‖gluedCompetitor U v η x - v x‖ ≤ ‖U x - v x‖ := by
  have he : gluedCompetitor U v η x - v x = (1 - η x) * (U x - v x) := by
    unfold gluedCompetitor
    ring
  rw [he, norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr hη.2)]
  have hh : 1 - η x ≤ 1 := by linarith [hη.1]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (norm_nonneg (U x - v x))

/-- On a compact domain, gluing changes the candidate only outside the region where
the cutoff equals one, with an integral bound by the mismatch there. -/
theorem integral_glued_sub_candidate_le {d : ℕ} {K S : Set (Space d)}
    (hK : IsCompact K) (hS : MeasurableSet S) {U v η : Space d → ℝ}
    (hU : Continuous U) (hv : Continuous v) (hη : Continuous η)
    (hval : ∀ x, η x ∈ Icc (0 : ℝ) 1) (hone : ∀ x ∈ S, η x = 1) :
    (∫ x in K, ‖gluedCompetitor U v η x - v x‖) ≤
      ∫ x in K \ S, ‖U x - v x‖ := by
  have hg : Continuous (gluedCompetitor U v η) := hU.add (hη.mul (hv.sub hU))
  have hil := (hg.sub hv).norm.continuousOn.integrableOn_compact (μ := volume) hK
  have hir := (hU.sub hv).norm.continuousOn.integrableOn_compact (μ := volume) hK
  have hA := hK.measurableSet.diff hS
  have hi := hir.indicator hA
  have he := integral_mono_ae hil hi (ae_restrict_of_forall_mem hK.measurableSet
    (fun x hx ↦ show ‖gluedCompetitor U v η x - v x‖ ≤
      (K \ S).indicator (fun y ↦ ‖U y - v y‖) x by
      by_cases hs : x ∈ S
      · simp [gluedCompetitor_eq_candidate U v η (hone x hs), hs]
      · rw [indicator_of_mem (show x ∈ K \ S from ⟨hx, hs⟩)]
        exact norm_gluedCompetitor_sub_candidate_le U v η (hval x)))
  simp only [Pi.sub_apply] at he
  rw [setIntegral_indicator hA, inter_eq_right.mpr sdiff_subset] at he
  exact he

/-- Vanishing mismatch outside the inner region preserves the candidate's local L1 limit. -/
theorem gluedCompetitor_integral_limit {d : ℕ} {K S : Set (Space d)}
    (hK : IsCompact K) (hS : MeasurableSet S)
    {U v η : ℕ → Space d → ℝ} {z : Space d → ℝ}
    (hU : ∀ j, Continuous (U j)) (hv : ∀ j, Continuous (v j))
    (hη : ∀ j, Continuous (η j))
    (hval : ∀ j x, η j x ∈ Icc (0 : ℝ) 1)
    (hone : ∀ j x, x ∈ S → η j x = 1) (hz : IntegrableOn z K)
    (hmis : Tendsto (fun j ↦ ∫ x in K \ S, ‖U j x - v j x‖) atTop (𝓝 0))
    (hvz : Tendsto (fun j ↦ ∫ x in K, ‖v j x - z x‖) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x in K, ‖gluedCompetitor (U j) (v j) (η j) x - z x‖)
      atTop (𝓝 0) := by
  have ht := hmis.add hvz
  simp only [zero_add] at ht
  apply squeeze_zero (fun j ↦ integral_nonneg (fun x ↦ norm_nonneg _)) _ ht
  intro j
  have hg : Continuous (gluedCompetitor (U j) (v j) (η j)) :=
    (hU j).add ((hη j).mul ((hv j).sub (hU j)))
  have he := integral_norm_sub_triangle (hg.continuousOn.integrableOn_compact hK)
    ((hv j).continuousOn.integrableOn_compact hK) hz
  exact he.trans (add_le_add
    (integral_glued_sub_candidate_le hK hS (hU j) (hv j) (hη j) (hval j) (hone j)) le_rfl)

end SerrinEpigraph
