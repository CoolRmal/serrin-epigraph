module

public import SerrinEpigraph.GraphOverlapIntegral

/-!
# Integrated kinetic cost of finite partition recovery
-/

public section

open Set MeasureTheory
open scoped Topology

namespace SerrinEpigraph

/-- Finite partition gluing preserves local Lipschitz regularity. -/
theorem partitionRecovery_locallyLipschitz {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} (hη : ∀ i, LocallyLipschitz (η i))
    (hv : ∀ i, LocallyLipschitz (v i)) : LocallyLipschitz (partitionRecovery η v) := by
  classical
  have hm : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ z.1 * z.2) := by fun_prop
  have hi (i : ι) : LocallyLipschitz (fun x ↦ η i x * v i x) :=
    hm.locallyLipschitz.comp ((hη i).prodMk (hv i))
  have hs (s : Finset ι) : LocallyLipschitz (fun x ↦ ∑ i ∈ s, η i x * v i x) := by
    induction s using Finset.induction_on with
    | empty => simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : Space d ↦ (0 : ℝ))).locallyLipschitz
    | @insert i s his ih => simpa only [Finset.sum_insert his] using (hi i).add ih
  exact hs Finset.univ

/-- The integral kinetic bound retains the principal patch weights and isolates the
integrated weight-gradient error. -/
theorem integral_partitionRecovery_kinetic_le {ι : Type*} [Fintype ι] {d : ℕ}
    {η v : ι → Space d → ℝ} (hη : ∀ i, ContDiff ℝ 1 (η i))
    (hv : ∀ i, LocallyLipschitz (v i)) (hpos : ∀ i x, 0 ≤ η i x)
    (hsum : ∀ x, ∑ i, η i x ≤ 1) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    {K : Set (Space d)} (hK : IsCompact K) :
    (∫ x in K, ‖gradient (partitionRecovery η v) x‖ ^ 2 / (2 * R)) ≤
      (1 + ε) * (∑ i, ∫ x in K, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) +
        (1 + 1 / ε) * (∫ x in K, ‖∑ i, v i x • gradient (η i) x‖ ^ 2 / (2 * R)) := by
  classical
  have hηl (i : ι) := (hη i).locallyLipschitz
  have hp := partitionRecovery_locallyLipschitz hηl hv
  have hip := (integrableOn_gradient_sq_of_locallyLipschitz hp hK).div_const (2 * R)
  have hi (i : ι) : IntegrableOn (fun x ↦ η i x *
      (‖gradient (v i) x‖ ^ 2 / (2 * R))) K := by
    simpa only [mul_comm] using
      IntegrableOn.mul_continuousOn
        ((integrableOn_gradient_sq_of_locallyLipschitz (hv i) hK).div_const (2 * R))
        (hη i).continuous.continuousOn hK
  have hg (i : ι) : Continuous (gradient (η i)) :=
    (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.comp
      ((hη i).continuous_fderiv one_ne_zero)
  have hc : Continuous (fun x ↦ ‖∑ i, v i x • gradient (η i) x‖ ^ 2 / (2 * R)) :=
    ((continuous_finsetSum _ (fun i _ ↦ (hv i).continuous.smul (hg i))).norm.pow 2).div_const _
  have hie := hc.continuousOn.integrableOn_compact (μ := volume) hK
  have his : IntegrableOn (fun x ↦ ∑ i, η i x *
      (‖gradient (v i) x‖ ^ 2 / (2 * R))) K := integrable_finsetSum _ (fun i _ ↦ hi i)
  have he := integral_mono_ae hip ((his.const_mul (1 + ε)).add (hie.const_mul (1 + 1 / ε)))
    (by
      change ∀ᵐ x ∂volume.restrict K, _ ≤ (1 + ε) *
        (∑ i, η i x * (‖gradient (v i) x‖ ^ 2 / (2 * R))) +
          (1 + 1 / ε) * (‖∑ i, v i x • gradient (η i) x‖ ^ 2 / (2 * R))
      simpa only [mul_div_assoc] using
        (partitionRecovery_kinetic_energy_le_ae hηl hv hpos hsum hε hR).filter_mono
          (ae_mono (Measure.restrict_le_self (s := K))))
  simp only [Pi.add_apply] at he
  rw [integral_add (his.const_mul _) (hie.const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun i _ ↦ hi i)] at he
  exact he

/-- At diverging scales, the integrated kinetic comparison has a vanishing additive error. -/
theorem exists_partitionRecovery_kinetic_error {ι : Type*} [Fintype ι] {d : ℕ}
    {η : ι → Space d → ℝ} (hη : ∀ i, ContDiff ℝ 1 (η i))
    {v : ℕ → ι → Space d → ℝ} (hv : ∀ j i, LocallyLipschitz (v j i))
    (hval : ∀ j i x, v j i x ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ i x, 0 ≤ η i x) (hsum : ∀ x, ∑ i, η i x ≤ 1)
    {ε : ℝ} (hε : 0 < ε) {R : ℕ → ℝ} (hR : ∀ j, 0 < R j)
    (hRtop : Filter.Tendsto R Filter.atTop Filter.atTop)
    {K : Set (Space d)} (hK : IsCompact K) :
    ∃ e : ℕ → ℝ, (∀ j, 0 ≤ e j) ∧ Filter.Tendsto e Filter.atTop (𝓝 0) ∧
      ∀ j, (∫ x in K, ‖gradient (partitionRecovery η (v j)) x‖ ^ 2 / (2 * R j)) ≤
        (1 + ε) * (∑ i, ∫ x in K, η i x * (‖gradient (v j i) x‖ ^ 2 / (2 * R j))) + e j := by
  let e := fun j ↦ (1 + 1 / ε) *
    (∫ x in K, ‖∑ i, v j i x • gradient (η i) x‖ ^ 2 / (2 * R j))
  refine ⟨e, ?_, ?_, fun j ↦ integral_partitionRecovery_kinetic_le hη (hv j) hpos hsum hε (hR j) hK⟩
  · intro j
    exact mul_nonneg (by positivity) (integral_nonneg (fun x ↦
      div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (hR j).le)))
  · have ht := partition_weightGradient_integral_limit hη (fun j i ↦ (hv j i).continuous)
      hval hR hRtop hK
    have heq (j : ℕ) : e j = ((1 + 1 / ε) / 2) *
        (∫ x in K, ‖∑ i, v j i x • gradient (η i) x‖ ^ 2 / R j) := by
      dsimp [e]
      simp only [integral_div]
      ring
    change Filter.Tendsto (fun j ↦ e j) Filter.atTop (𝓝 0)
    simp_rw [heq]
    simpa only [mul_zero] using ht.const_mul ((1 + 1 / ε) / 2)

end SerrinEpigraph
