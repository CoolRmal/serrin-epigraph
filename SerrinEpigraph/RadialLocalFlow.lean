module

public import SerrinEpigraph.RadialEquation
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local radial flow away from the center
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

/-- Autonomous form of the radial equation, with radius as the first coordinate. -/
@[expose] def radialVectorField (m : ℕ) (f : ℝ → ℝ) (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (1, z.2.2, -f z.2.1 - (m : ℝ) / z.1 * z.2.2)

/-- The radial field is continuously differentiable away from radius zero. -/
theorem radialVectorField_contDiffAt (m : ℕ) {f : ℝ → ℝ} {r a p : ℝ}
    (hr : r ≠ 0) (hf : ContDiffAt ℝ 1 f a) :
    ContDiffAt ℝ 1 (radialVectorField m f) (r, a, p) := by
  change ContDiffAt ℝ 1 (fun z : ℝ × ℝ × ℝ ↦
    (1, z.2.2, -f z.2.1 - (m : ℝ) / z.1 * z.2.2)) (r, a, p)
  have hcomp : ContDiffAt ℝ 1 (fun z : ℝ × ℝ × ℝ ↦ f z.2.1) (r, a, p) :=
    hf.comp _ (contDiffAt_fst.comp _ contDiffAt_snd)
  fun_prop

/-- At any positive radius, the radial system has a local solution for arbitrary slope. -/
theorem exists_radial_system_at_positive_radius (m : ℕ) {f : ℝ → ℝ} {r a p : ℝ}
    (hr : 0 < r) (hf : ContDiffAt ℝ 1 f a) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Q P : ℝ → ℝ, Q r = a ∧ P r = p ∧
      ∀ t ∈ Ioo (r - ε) (r + ε),
        HasDerivAt Q (P t) t ∧ HasDerivAt P (-f (Q t) - (m : ℝ) / t * P t) t := by
  have hv := radialVectorField_contDiffAt m (p := p) hr.ne' hf
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    hv.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ r
  have hclock : ∀ t ∈ Ioo (r - ε) (r + ε), HasDerivAt (fun s ↦ (α s).1) 1 t := by
    intro t ht
    exact (hα t ht).fst
  have hclockeq : EqOn (fun s ↦ (α s).1) id (Ioo (r - ε) (r + ε)) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (x := r) (convex_Ioo (r - ε) (r + ε)).isPreconnected
      (fun t ht ↦ (hclock t ht).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn
    · intro t ht
      rw [(hclock t ht).deriv, deriv_id']
    · exact ⟨by linarith, by linarith⟩
    · exact congrArg Prod.fst hα0
  refine ⟨ε, hε, (fun t ↦ (α t).2.1), (fun t ↦ (α t).2.2),
    congrArg (fun z ↦ z.2.1) hα0, congrArg (fun z ↦ z.2.2) hα0, ?_⟩
  intro t ht
  refine ⟨(hα t ht).snd.fst, ?_⟩
  have hd := (hα t ht).snd.snd
  change HasDerivAt (fun s ↦ (α s).2.2)
    (-f (α t).2.1 - (m : ℝ) / (α t).1 * (α t).2.2) t at hd
  simpa only [hclockeq ht, id_eq] using hd

/-- The project hypotheses allow restarting the radial system at every positive state. -/
theorem Hypotheses.exists_radial_system_near_positive_state
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {r a p : ℝ} (hr : 0 < r) (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ∧ ∃ Q P : ℝ → ℝ, Q r = a ∧ P r = p ∧
      ∀ t ∈ Ioo (r - ε) (r + ε), 0 < Q t ∧
        HasDerivAt Q (P t) t ∧ HasDerivAt P (-f (Q t) - (m : ℝ) / t * P t) t := by
  have hf : ContDiffAt ℝ 1 f a :=
    (h.reaction_contDiffOn a ha.le).contDiffAt (Ici_mem_nhds ha)
  obtain ⟨ε, hε, Q, P, hQ0, hP0, hd⟩ :=
    exists_radial_system_at_positive_radius m (p := p) hr hf
  have hrmem : r ∈ Ioo (r - ε) (r + ε) := ⟨by linarith, by linarith⟩
  have hQcont := (hd r hrmem).1.continuousAt
  have hn : Q ⁻¹' Ioi (0 : ℝ) ∈ 𝓝 r :=
    hQcont.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hQ0] using ha))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  let η := min ε (min (r / 2) (δ / 2))
  have hη : 0 < η := lt_min hε (lt_min (by positivity) (by positivity))
  have hηε : η ≤ ε := min_le_left _ _
  have hηr : η ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηδ : η ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, by linarith, Q, P, hQ0, hP0, ?_⟩
  intro t ht
  have htε : t ∈ Ioo (r - ε) (r + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨hball ?_, hd t htε⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

end SerrinEpigraph
