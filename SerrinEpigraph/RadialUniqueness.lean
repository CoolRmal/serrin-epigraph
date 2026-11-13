module

public import SerrinEpigraph.RadialLocalFlow
public import Mathlib.Topology.Connected.Clopen

/-!
# Local uniqueness for radial initial value problems away from the center
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

/-- A C¹ autonomous field has locally unique integral curves through a given state. -/
theorem autonomous_solution_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → E} {α β : ℝ → E} {r : ℝ}
    (hV : ContDiffAt ℝ 1 V (α r))
    (hα : ∀ᶠ t in 𝓝 r, HasDerivAt α (V (α t)) t)
    (hβ : ∀ᶠ t in 𝓝 r, HasDerivAt β (V (β t)) t)
    (heq : α r = β r) : α =ᶠ[𝓝 r] β := by
  obtain ⟨K, S, hS, hLip⟩ := hV.exists_lipschitzOnWith
  have hαcont := (Filter.Eventually.self_of_nhds hα).continuousAt
  have hβcont := (Filter.Eventually.self_of_nhds hβ).continuousAt
  have hαS : ∀ᶠ t in 𝓝 r, α t ∈ S := hαcont.preimage_mem_nhds hS
  have hβS : ∀ᶠ t in 𝓝 r, β t ∈ S :=
    hβcont.preimage_mem_nhds (heq ▸ hS)
  exact ODE_solution_unique_of_eventually
    (v := fun _ ↦ V) (s := fun _ ↦ S)
    (Filter.Eventually.of_forall (fun _ ↦ hLip)) (hα.and hαS) (hβ.and hβS) heq

/-- Radial value and slope are locally unique at a positive radius. -/
theorem radial_system_eventuallyEq (m : ℕ) {f Q P U V : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hf : ContDiffAt ℝ 1 f (Q r))
    (hQ : ∀ᶠ t in 𝓝 r, HasDerivAt Q (P t) t)
    (hP : ∀ᶠ t in 𝓝 r, HasDerivAt P (-f (Q t) - (m : ℝ) / t * P t) t)
    (hU : ∀ᶠ t in 𝓝 r, HasDerivAt U (V t) t)
    (hV : ∀ᶠ t in 𝓝 r, HasDerivAt V (-f (U t) - (m : ℝ) / t * V t) t)
    (hval : Q r = U r) (hslope : P r = V r) :
    Q =ᶠ[𝓝 r] U ∧ P =ᶠ[𝓝 r] V := by
  let α := fun t ↦ (t, Q t, P t)
  let β := fun t ↦ (t, U t, V t)
  have hα : ∀ᶠ t in 𝓝 r, HasDerivAt α (radialVectorField m f (α t)) t := by
    filter_upwards [hQ, hP] with t htQ htP
    exact (hasDerivAt_id t).prodMk (htQ.prodMk htP)
  have hβ : ∀ᶠ t in 𝓝 r, HasDerivAt β (radialVectorField m f (β t)) t := by
    filter_upwards [hU, hV] with t htU htV
    exact (hasDerivAt_id t).prodMk (htU.prodMk htV)
  have heq : α r = β r := by simp only [α, β, hval, hslope]
  have he := autonomous_solution_eventuallyEq
    (radialVectorField_contDiffAt m hr.ne' hf) hα hβ heq
  constructor
  · filter_upwards [he] with t ht
    exact congrArg (fun z ↦ z.2.1) ht
  · filter_upwards [he] with t ht
    exact congrArg (fun z ↦ z.2.2) ht

/-- Under the project assumptions, matching positive radial states have unique local germs. -/
theorem Hypotheses.radial_system_eventuallyEq
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P U V : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (ha : 0 < Q r)
    (hQ : ∀ᶠ t in 𝓝 r, HasDerivAt Q (P t) t)
    (hP : ∀ᶠ t in 𝓝 r, HasDerivAt P (-f (Q t) - (m : ℝ) / t * P t) t)
    (hU : ∀ᶠ t in 𝓝 r, HasDerivAt U (V t) t)
    (hV : ∀ᶠ t in 𝓝 r, HasDerivAt V (-f (U t) - (m : ℝ) / t * V t) t)
    (hval : Q r = U r) (hslope : P r = V r) :
    Q =ᶠ[𝓝 r] U ∧ P =ᶠ[𝓝 r] V := by
  exact SerrinEpigraph.radial_system_eventuallyEq m hr
    ((h.reaction_contDiffOn _ ha.le).contDiffAt (Ici_mem_nhds ha))
    hQ hP hU hV hval hslope

/-- Matching radial states agree throughout any connected open interval of positive states. -/
theorem Hypotheses.radial_system_eqOn
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P U V : ℝ → ℝ} {S : Set ℝ} {r : ℝ}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hr : r ∈ S)
    (hpos : ∀ t ∈ S, 0 < t ∧ 0 < Q t)
    (hQ : ∀ t ∈ S, HasDerivAt Q (P t) t)
    (hP : ∀ t ∈ S, HasDerivAt P (-f (Q t) - (m : ℝ) / t * P t) t)
    (hU : ∀ t ∈ S, HasDerivAt U (V t) t)
    (hV : ∀ t ∈ S, HasDerivAt V (-f (U t) - (m : ℝ) / t * V t) t)
    (hval : Q r = U r) (hslope : P r = V r) : EqOn Q U S ∧ EqOn P V S := by
  let : PreconnectedSpace S := Subtype.preconnectedSpace hconn
  let A : Set S := {t | Q t = U t ∧ P t = V t}
  have hQc : Continuous (fun t : S ↦ Q t) :=
    continuousOn_iff_continuous_domRestrict.mp (fun t ht ↦ (hQ t ht).continuousAt.continuousWithinAt)
  have hPc : Continuous (fun t : S ↦ P t) :=
    continuousOn_iff_continuous_domRestrict.mp (fun t ht ↦ (hP t ht).continuousAt.continuousWithinAt)
  have hUc : Continuous (fun t : S ↦ U t) :=
    continuousOn_iff_continuous_domRestrict.mp (fun t ht ↦ (hU t ht).continuousAt.continuousWithinAt)
  have hVc : Continuous (fun t : S ↦ V t) :=
    continuousOn_iff_continuous_domRestrict.mp (fun t ht ↦ (hV t ht).continuousAt.continuousWithinAt)
  have hclosed : IsClosed A := (isClosed_eq hQc hUc).inter (isClosed_eq hPc hVc)
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have he := h.radial_system_eventuallyEq (hpos t t.property).1 (hpos t t.property).2
      (Filter.eventually_of_mem (hS.mem_nhds t.property) hQ)
      (Filter.eventually_of_mem (hS.mem_nhds t.property) hP)
      (Filter.eventually_of_mem (hS.mem_nhds t.property) hU)
      (Filter.eventually_of_mem (hS.mem_nhds t.property) hV) ht.1 ht.2
    exact (continuous_subtype_val.tendsto t).eventually (he.1.and he.2)
  have hA : A = univ := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨r, hr⟩, hval, hslope⟩
  have hall : ∀ t ∈ S, Q t = U t ∧ P t = V t := by
    intro t ht
    have : (⟨t, ht⟩ : S) ∈ A := hA ▸ mem_univ _
    exact this
  exact ⟨fun t ht ↦ (hall t ht).1, fun t ht ↦ (hall t ht).2⟩

end SerrinEpigraph
