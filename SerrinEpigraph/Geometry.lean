module

public import SerrinEpigraph.Basic
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Geometry of entire epigraphs
-/

@[expose] public section

noncomputable section

namespace SerrinEpigraph

variable {m : ℕ}

@[simp]
theorem horizontal_point (y : Space m) (t : ℝ) : horizontal (point y t) = y := by
  ext i
  simp [horizontal, point]

@[simp]
theorem last_point (y : Space m) (t : ℝ) : point y t (Fin.last m) = t := by
  simp [point]

@[simp]
theorem point_horizontal_last (x : Space (m + 1)) :
    point (horizontal x) (x (Fin.last m)) = x := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [point]
  · simp [horizontal, point]

@[fun_prop]
theorem continuous_horizontal : Continuous (horizontal : Space (m + 1) → Space m) := by
  unfold horizontal
  fun_prop

@[fun_prop]
theorem continuous_point (y : Space m) : Continuous (point y) := by
  unfold point
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Fin.snoc_last]
    fun_prop
  · simp only [Fin.snoc_castSucc]
    fun_prop

/-- The strict epigraph of a continuous function is open. -/
theorem isOpen_epigraph {g : Space m → ℝ} (hg : Continuous g) : IsOpen (epigraph g) := by
  exact isOpen_lt (hg.comp continuous_horizontal) (by fun_prop)

theorem point_mem_closure_epigraph {g : Space m → ℝ} {y : Space m} {t : ℝ}
    (ht : g y ≤ t) : point y t ∈ closure (epigraph g) := by
  have hmap : Set.MapsTo (point y) (Set.Ioi (g y)) (epigraph g) := by
    intro r hr
    simpa [epigraph] using hr
  apply hmap.closure (continuous_point y)
  simpa only [closure_Ioi, Set.mem_Ici] using ht

/-- The closure of a continuous epigraph is its non-strict epigraph. -/
theorem closure_epigraph {g : Space m → ℝ} (hg : Continuous g) :
    closure (epigraph g) = {x | g (horizontal x) ≤ x (Fin.last m)} := by
  apply Set.Subset.antisymm
  · exact closure_lt_subset_le (hg.comp continuous_horizontal) (by fun_prop)
  · intro x hx
    simpa using point_mem_closure_epigraph hx

/-- The frontier of a continuous epigraph is its graph. -/
theorem frontier_epigraph {g : Space m → ℝ} (hg : Continuous g) :
    frontier (epigraph g) = {x | g (horizontal x) = x (Fin.last m)} := by
  rw [frontier, (isOpen_epigraph hg).interior_eq, closure_epigraph hg]
  ext x
  simp only [epigraph, Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]
  exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le, h.ge⟩⟩

theorem point_mem_frontier_epigraph {g : Space m → ℝ} (hg : Continuous g) (y : Space m) :
    point y (g y) ∈ frontier (epigraph g) := by
  simp [frontier_epigraph hg]

theorem uniqueDiffOn_epigraph {g : Space m → ℝ} (hg : Continuous g) :
    UniqueDiffOn ℝ (epigraph g) :=
  (isOpen_epigraph hg).uniqueDiffOn

@[fun_prop]
theorem differentiable_horizontal :
    Differentiable ℝ (horizontal : Space (m + 1) → Space m) := by
  apply (differentiable_piLp 2).2
  intro i
  change Differentiable ℝ (fun x : Space (m + 1) ↦ x i.castSucc)
  exact (PiLp.proj 2 (fun _ : Fin (m + 1) ↦ ℝ) i.castSucc).differentiable

private def graphParam (g : Space m → ℝ) (p : Space m × ℝ) : Space (m + 1) :=
  point p.1 (g p.1 + p.2)

private def graphCoordinates (g : Space m → ℝ) (x : Space (m + 1)) : Space m × ℝ :=
  (horizontal x, x (Fin.last m) - g (horizontal x))

private theorem graphParam_graphCoordinates (g : Space m → ℝ) (x : Space (m + 1)) :
    graphParam g (graphCoordinates g x) = x := by
  simp [graphParam, graphCoordinates]

private theorem graphCoordinates_graphParam (g : Space m → ℝ) (p : Space m × ℝ) :
    graphCoordinates g (graphParam g p) = p := by
  simp [graphParam, graphCoordinates]

private theorem differentiable_graphParam {g : Space m → ℝ} (hg : Differentiable ℝ g) :
    Differentiable ℝ (graphParam g) := by
  apply (differentiable_piLp 2).2
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [graphParam, last_point]
    fun_prop
  · simp only [graphParam, point, PiLp.toLp_apply, Fin.snoc_castSucc]
    have hp : Differentiable ℝ (fun y : Space m ↦ y j) :=
      (PiLp.proj 2 (fun _ : Fin m ↦ ℝ) j).differentiable
    exact hp.comp differentiable_fst

private theorem differentiable_graphCoordinates {g : Space m → ℝ}
    (hg : Differentiable ℝ g) : Differentiable ℝ (graphCoordinates g) := by
  exact differentiable_horizontal.prodMk
    ((PiLp.proj 2 (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)).differentiable.sub
      (hg.comp differentiable_horizontal))

private theorem surjective_fderiv_graphParam {g : Space m → ℝ} (hg : Differentiable ℝ g)
    (p : Space m × ℝ) : Function.Surjective (fderiv ℝ (graphParam g) p) := by
  have hcomp : graphParam g ∘ graphCoordinates g = id := by
    funext x
    exact graphParam_graphCoordinates g x
  have hd := fderiv_comp (graphParam g p)
    ((differentiable_graphParam hg) (graphCoordinates g (graphParam g p)))
    ((differentiable_graphCoordinates hg) (graphParam g p))
  rw [hcomp, fderiv_id, graphCoordinates_graphParam] at hd
  intro v
  refine ⟨fderiv ℝ (graphCoordinates g) (graphParam g p) v, ?_⟩
  exact (congrArg (fun L : Space (m + 1) →L[ℝ] Space (m + 1) ↦ L v) hd).symm

private theorem graphParam_image_halfSpace {g : Space m → ℝ} (hg : Continuous g) :
    graphParam g '' (Set.univ ×ˢ Set.Ici 0) = closure (epigraph g) := by
  rw [closure_epigraph hg]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [graphParam] using hp.2
  · intro hx
    refine ⟨graphCoordinates g x, ?_, graphParam_graphCoordinates g x⟩
    exact ⟨Set.mem_univ _, sub_nonneg.mpr hx⟩

/-- A differentiable graph has a closed epigraph with unique derivatives at its boundary. -/
theorem uniqueDiffOn_closure_epigraph {g : Space m → ℝ} (hg : Differentiable ℝ g) :
    UniqueDiffOn ℝ (closure (epigraph g)) := by
  rw [← graphParam_image_halfSpace hg.continuous]
  apply (uniqueDiffOn_univ.prod (uniqueDiffOn_Ici (0 : ℝ))).image
  · intro p _
    exact ((differentiable_graphParam hg) p).hasFDerivAt.hasFDerivWithinAt
  · intro p _
    exact (surjective_fderiv_graphParam hg p).denseRange

end SerrinEpigraph
