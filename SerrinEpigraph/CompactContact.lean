module

public import SerrinEpigraph.LocalMinimum

/-!
# Constructing a first contact by compact optimization
-/

public section

open scoped Topology Laplacian

namespace SerrinEpigraph

variable {E : Type*} [TopologicalSpace E]

/-- If a continuous comparison function vanishing off the interior of a compact set exceeds
a positive continuous function, a smaller positive multiple touches it at an interior minimum. -/
theorem exists_positive_interior_contact {K : Set E} {u ψ : E → ℝ}
    (hK : IsCompact K) (hu : ContinuousOn u K) (hψ : ContinuousOn ψ K)
    (hupos : ∀ x ∈ K, 0 < u x) (hboundary : ∀ x ∈ K, x ∉ interior K → ψ x = 0)
    (hex : ∃ x ∈ K, u x < ψ x) :
    ∃ x ∈ interior K, ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ u x = τ * ψ x ∧
      IsLocalMin (fun y ↦ u y - τ * ψ y) x := by
  obtain ⟨z, hz, hlt⟩ := hex
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn ⟨z, hz⟩
    (hψ.div hu (fun y hy ↦ (hupos y hy).ne'))
  have hratiolt : 1 < ψ x / u x :=
    ((one_lt_div (hupos z hz)).mpr hlt).trans_le (hmax hz)
  have hux : 0 < u x := hupos x hx
  have hψgt : u x < ψ x := (one_lt_div hux).mp hratiolt
  have hψpos : 0 < ψ x := hux.trans hψgt
  have hxint : x ∈ interior K := by
    by_contra hn
    have := hboundary x hx hn
    linarith
  let τ := u x / ψ x
  have hτ : 0 < τ := div_pos hux hψpos
  have hτlt : τ < 1 := (div_lt_one hψpos).mpr hψgt
  have hcontact : u x = τ * ψ x := by dsimp [τ]; field_simp
  refine ⟨x, hxint, τ, hτ, hτlt, hcontact, ?_⟩
  apply IsMinOn.isLocalMin (s := K) _ (mem_interior_iff_mem_nhds.mp hxint)
  intro y hy
  change u x - τ * ψ x ≤ u y - τ * ψ y
  rw [hcontact, sub_self]
  have hratio : ψ y / u y ≤ ψ x / u x := hmax hy
  have hcross := (div_le_div_iff₀ (hupos y hy) hux).mp hratio
  have hbound : τ * ψ y ≤ u y := by
    dsimp [τ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hψpos).mpr
    nlinarith
  linarith

section Comparison

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Strict separation of the reaction and barrier coefficients forces comparison on a compact
set when the barrier vanishes on its boundary. The reaction bound is needed only below `a`. -/
theorem compact_comparison_of_coefficient_gap {K Ω : Set F} {u ψ : F → ℝ} {a c ℓ : ℝ}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hsub : K ⊆ Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hψ : ContDiffOn ℝ 2 ψ Ω)
    (hupos : ∀ x ∈ K, 0 < u x) (hboundary : ∀ x ∈ K, x ∉ interior K → ψ x = 0)
    (hψupper : ∀ x ∈ K, ψ x ≤ a) (hgap : ℓ < c)
    (huineq : ∀ x ∈ K, u x ≤ a → c * u x ≤ -(Δ u) x)
    (hψineq : ∀ x ∈ K, -(Δ ψ) x ≤ ℓ * ψ x) : ∀ x ∈ K, ψ x ≤ u x := by
  intro z hz
  by_contra hn
  obtain ⟨x, hx, τ, hτ, hτlt, hcontact, hmin⟩ := exists_positive_interior_contact hK
    (hu.continuousOn.mono hsub) (hψ.continuousOn.mono hsub) hupos hboundary
    ⟨z, hz, lt_of_not_ge hn⟩
  have hxK : x ∈ K := interior_subset hx
  have hup := hupos x hxK
  have hψpos : 0 < ψ x := by nlinarith [hcontact]
  have hua : u x ≤ a := by
    have := hψupper x hxK
    nlinarith
  exact not_localMin_at_positive_contact hΩ hu hψ (hsub hxK) hτ hgap hup hcontact
    (huineq x hxK hua) (hψineq x hxK) hmin

end Comparison

end SerrinEpigraph
