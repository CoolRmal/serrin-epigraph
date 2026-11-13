module

public import SerrinEpigraph.RadialUniqueness

/-!
# Gluing radial systems on overlapping open domains
-/

public section
noncomputable section
open Set
open scoped Topology

namespace SerrinEpigraph

/-- The two differential equations for a radial value and slope on a set of radii. -/
@[expose] def IsRadialSystemOn (m : ℕ) (f Q P : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ t ∈ S, HasDerivAt Q (P t) t ∧
    HasDerivAt P (-f (Q t) - (m : ℝ) / t * P t) t

/-- Restrict a radial system to a smaller set of radii. -/
theorem IsRadialSystemOn.mono {m : ℕ} {f Q P : ℝ → ℝ} {S T : Set ℝ}
    (h : IsRadialSystemOn m f Q P S) (hTS : T ⊆ S) : IsRadialSystemOn m f Q P T :=
  fun t ht ↦ h t (hTS ht)

/-- A piecewise union of agreeing functions locally equals either branch on its open domain. -/
theorem piecewise_eventuallyEq_on_overlap {F G : ℝ → ℝ} {S T : Set ℝ}
    [DecidablePred (· ∈ S)] (hT : IsOpen T) (heq : EqOn F G (S ∩ T))
    {t : ℝ} (ht : t ∈ T) : S.piecewise F G =ᶠ[𝓝 t] G := by
  filter_upwards [hT.mem_nhds ht] with s hs
  by_cases h : s ∈ S
  · simp only [piecewise_eq_of_mem S F G h]
    exact heq ⟨h, hs⟩
  · exact piecewise_eq_of_notMem S F G h

/-- Radial systems agreeing on an overlap glue to a system on the union. -/
theorem IsRadialSystemOn.piecewise {m : ℕ} {f Q P U V : ℝ → ℝ} {S T : Set ℝ}
    [DecidablePred (· ∈ S)] (hS : IsOpen S) (hT : IsOpen T)
    (hQP : IsRadialSystemOn m f Q P S) (hUV : IsRadialSystemOn m f U V T)
    (hval : EqOn Q U (S ∩ T)) (hslope : EqOn P V (S ∩ T)) :
    IsRadialSystemOn m f (S.piecewise Q U) (S.piecewise P V) (S ∪ T) := by
  intro t ht
  rcases ht with ht | ht
  · have heQ : S.piecewise Q U =ᶠ[𝓝 t] Q := by
      filter_upwards [hS.mem_nhds ht] with s hs
      exact piecewise_eq_of_mem S Q U hs
    have heP : S.piecewise P V =ᶠ[𝓝 t] P := by
      filter_upwards [hS.mem_nhds ht] with s hs
      exact piecewise_eq_of_mem S P V hs
    rw [piecewise_eq_of_mem S Q U ht, piecewise_eq_of_mem S P V ht]
    exact ⟨(hQP t ht).1.congr_of_eventuallyEq heQ, (hQP t ht).2.congr_of_eventuallyEq heP⟩
  · have heQ := piecewise_eventuallyEq_on_overlap hT hval ht
    have heP := piecewise_eventuallyEq_on_overlap hT hslope ht
    rw [heQ.eq_of_nhds, heP.eq_of_nhds]
    exact ⟨(hUV t ht).1.congr_of_eventuallyEq heQ, (hUV t ht).2.congr_of_eventuallyEq heP⟩

/-- Agreement at one positive state suffices to glue systems across a connected overlap. -/
theorem Hypotheses.exists_radial_system_union
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P U V : ℝ → ℝ} {S T : Set ℝ} {r : ℝ}
    (hS : IsOpen S) (hT : IsOpen T) (hconn : IsPreconnected (S ∩ T))
    (hr : r ∈ S ∩ T) (hpos : ∀ t ∈ S ∩ T, 0 < t ∧ 0 < Q t)
    (hQP : IsRadialSystemOn m f Q P S) (hUV : IsRadialSystemOn m f U V T)
    (hval : Q r = U r) (hslope : P r = V r) :
    ∃ W Z : ℝ → ℝ, IsRadialSystemOn m f W Z (S ∪ T) ∧
      EqOn W Q S ∧ EqOn Z P S ∧ EqOn W U T ∧ EqOn Z V T := by
  classical
  obtain ⟨hv, hp⟩ := h.radial_system_eqOn (hS.inter hT) hconn hr hpos
    (fun t ht ↦ (hQP t ht.1).1) (fun t ht ↦ (hQP t ht.1).2)
    (fun t ht ↦ (hUV t ht.2).1) (fun t ht ↦ (hUV t ht.2).2) hval hslope
  refine ⟨S.piecewise Q U, S.piecewise P V,
    hQP.piecewise hS hT hUV hv hp, piecewise_eqOn S Q U, piecewise_eqOn S P V, ?_, ?_⟩
  · intro t ht
    exact (piecewise_eventuallyEq_on_overlap hT hv ht).eq_of_nhds
  · intro t ht
    exact (piecewise_eventuallyEq_on_overlap hT hp ht).eq_of_nhds

/-- A local restart can be glued to an existing positive radial system on an open interval. -/
theorem Hypotheses.exists_radial_restart_union
    {m : ℕ} {g : Space m → ℝ} {u : Space (m + 1) → ℝ} {f : ℝ → ℝ} {κ : ℝ}
    (h : Hypotheses g u f κ) {Q P : ℝ → ℝ} {S : Set ℝ} {r : ℝ}
    (hS : IsOpen S) (hconv : Convex ℝ S) (hr : r ∈ S)
    (hpos : ∀ t ∈ S, 0 < t ∧ 0 < Q t) (hQP : IsRadialSystemOn m f Q P S) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ∧ ∃ W Z : ℝ → ℝ,
      IsRadialSystemOn m f W Z (S ∪ Ioo (r - ε) (r + ε)) ∧
      EqOn W Q S ∧ EqOn Z P S ∧ (∀ t ∈ Ioo (r - ε) (r + ε), 0 < W t) := by
  obtain ⟨ε, hε, hεr, U, V, hU0, hV0, hUV⟩ :=
    h.exists_radial_system_near_positive_state (p := P r) (hpos r hr).1 (hpos r hr).2
  have hrT : r ∈ Ioo (r - ε) (r + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨W, Z, hWZ, hWQ, hZP, hWU, _⟩ := h.exists_radial_system_union
    hS isOpen_Ioo (hconv.inter (convex_Ioo (r - ε) (r + ε))).isPreconnected
    ⟨hr, hrT⟩ (fun t ht ↦ hpos t ht.1) hQP (fun t ht ↦ (hUV t ht).2)
    hU0.symm hV0.symm
  refine ⟨ε, hε, hεr, W, Z, hWZ, hWQ, hZP, ?_⟩
  intro t ht
  rw [hWU ht]
  exact (hUV t ht).1

end SerrinEpigraph
