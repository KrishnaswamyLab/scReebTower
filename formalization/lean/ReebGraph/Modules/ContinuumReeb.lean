import ReebGraph.Modules.DiscreteReeb
import ReebGraph.Modules.Realization

/-!
# Continuum Reeb quotient

The continuum Reeb quotient of a filtered space, and the filtered
realization of a discrete Reeb graph.

Main results: `continuous_continuumReebGraph_height`,
`continuumReebQuotientMap_surjective`, and
`joinedIn_continuumReebQuotientMap`, plus the definition of
`discreteReebRealization` that the consistency theorems compare against.
Supporting lemmas establish that `SameLevelComponent` is an equivalence
and that raw support witnesses land in the right component.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Classical Reeb equivalence: two points have the same scalar value and lie
in the same connected component of that level set. -/
def SameLevelComponent
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x y : M) : Prop :=
  f x = f y ∧ y ∈ connectedComponentIn {z | f z = f x} x

theorem sameLevelComponent_refl
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x : M) :
    SameLevelComponent f x x :=
  ⟨rfl, mem_connectedComponentIn rfl⟩

theorem sameLevelComponent_symm
    {M : Type} [TopologicalSpace M] (f : M → ℝ) {x y : M}
    (h : SameLevelComponent f x y) : SameLevelComponent f y x := by
  rcases h with ⟨hxy, hpath⟩
  refine ⟨hxy.symm, ?_⟩
  have hcomponents :
      connectedComponentIn {z | f z = f x} x =
        connectedComponentIn {z | f z = f x} y :=
    connectedComponentIn_eq hpath
  have hxmem : x ∈ connectedComponentIn {z | f z = f x} y := by
    rw [← hcomponents]
    exact mem_connectedComponentIn rfl
  simpa only [hxy] using hxmem

theorem sameLevelComponent_trans
    {M : Type} [TopologicalSpace M] (f : M → ℝ) {x y z : M}
    (hxy : SameLevelComponent f x y)
    (hyz : SameLevelComponent f y z) : SameLevelComponent f x z := by
  rcases hxy with ⟨hfxy, hpathxy⟩
  rcases hyz with ⟨hfyz, hpathyz⟩
  refine ⟨hfxy.trans hfyz, ?_⟩
  have hpathyz' : z ∈ connectedComponentIn {w | f w = f x} y := by
    simpa only [hfxy] using hpathyz
  rw [connectedComponentIn_eq hpathxy]
  exact hpathyz'

theorem sameLevelComponent_of_joinedIn
    {M : Type} [TopologicalSpace M] (f : M → ℝ) {x y : M}
    (hxy : JoinedIn {z | f z = f x} x y) :
    SameLevelComponent f x y := by
  refine ⟨hxy.target_mem.symm, ?_⟩
  have hconnected : IsConnected (Set.range hxy.somePath) :=
    isConnected_range hxy.somePath.continuous
  apply hconnected.isPreconnected.subset_connectedComponentIn
    ⟨0, hxy.somePath.source⟩
    (fun z hz => by
      rcases hz with ⟨t, rfl⟩
      exact hxy.somePath_mem t)
  exact ⟨1, hxy.somePath.target⟩

def reebSetoid
    {M : Type} [TopologicalSpace M] (f : M → ℝ) : Setoid M where
  r := SameLevelComponent f
  iseqv :=
    ⟨sameLevelComponent_refl f, sameLevelComponent_symm f,
      sameLevelComponent_trans f⟩

/-- Underlying quotient space of the continuum Reeb construction. -/
def ContinuumReebQuotient
    (M : Type) [TopologicalSpace M] (f : M → ℝ) :=
  Quotient (reebSetoid f)

instance continuumReebQuotientTopology
    (M : Type) [TopologicalSpace M] (f : M → ℝ) :
    TopologicalSpace (ContinuumReebQuotient M f) :=
  instTopologicalSpaceQuotient

/-- Quotient map from the domain to its Reeb space. -/
def continuumReebQuotientMap
    {M : Type} [TopologicalSpace M] (f : M → ℝ) :
    M → ContinuumReebQuotient M f :=
  Quotient.mk (reebSetoid f)

/-- Reeb quotient with its quotient topology and descended scalar function. -/
noncomputable def continuumReebGraph
    (M : Type) [TopologicalSpace M] (f : M → ℝ) : FilteredReebGraph where
  Carrier := ContinuumReebQuotient M f
  topology := continuumReebQuotientTopology M f
  height := Quotient.lift f (fun x y h => by
    have h' : SameLevelComponent f x y := h
    exact h'.1)

@[simp] theorem continuumReebGraph_height_quotientMap
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x : M) :
    (continuumReebGraph M f).height (continuumReebQuotientMap f x) = f x :=
  rfl

theorem continuumReebQuotientMap_eq_iff
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x y : M) :
    continuumReebQuotientMap f x = continuumReebQuotientMap f y ↔
      SameLevelComponent f x y := by
  exact Quotient.eq

theorem continuous_continuumReebQuotientMap
    {M : Type} [TopologicalSpace M] (f : M → ℝ) :
    Continuous (continuumReebQuotientMap f) := by
  exact continuous_quotient_mk'

theorem continuumReebQuotientMap_surjective
    {M : Type} [TopologicalSpace M] (f : M → ℝ) :
    Function.Surjective (continuumReebQuotientMap f) := by
  exact Quotient.mk_surjective

theorem continuous_continuumReebGraph_height
    {M : Type} [TopologicalSpace M] {f : M → ℝ} (hf : Continuous f) :
    Continuous (continuumReebGraph M f).height := by
  apply hf.quotient_lift

/-- A path in a manifold scalar band projects to a path in the corresponding
band of the continuum Reeb quotient. -/
theorem joinedIn_continuumReebQuotientMap
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    {a b : ℝ} {x x' : M}
    (h : JoinedIn {z | a ≤ f z ∧ f z ≤ b} x x') :
    JoinedIn {z | a ≤ (continuumReebGraph M f).height z ∧
      (continuumReebGraph M f).height z ≤ b}
      (continuumReebQuotientMap f x) (continuumReebQuotientMap f x') := by
  refine ⟨h.somePath.map (continuous_continuumReebQuotientMap f), ?_⟩
  intro t
  change a ≤ f (h.somePath t) ∧ f (h.somePath t) ≤ b
  exact h.somePath_mem t

/-- Filtered piecewise-linear realization of the canonical support-induced
midpoint graph. -/
noncomputable def discreteReebRealization
    (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) : FilteredReebGraph := by
  let D := canonicalDiscreteReebGraph G f
  exact
    { Carrier := SimpleGraphRealization D
      topology := simpleGraphRealizationTopology D
      height := graphRealizationHeight D (fun x => canonicalThreshold f x.1) }

theorem continuous_discreteReebRealization_height
    (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) :
    Continuous (discreteReebRealization V G f).height := by
  exact continuous_graphRealizationHeight
    (canonicalDiscreteReebGraph G f) (fun x => canonicalThreshold f x.1)

/-- A support witness attached to every raw point of a discrete graph
realization.  At a graph vertex it lies in that slice component; on an edge it
lies in the overlap that generated the transition. -/
noncomputable def discreteRawSupportWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ) :
    GraphRealizationRaw (discreteReebGraph G f threshold) → V
  | .inl x => Classical.choose (sliceNode_support_nonempty G f threshold x)
  | .inr (e, _) => Classical.choose
      (show SliceOverlap G f threshold e.source e.target from e.2.2)

theorem discreteRawSupportWitness_vertex_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ)
    (x : SliceNode G f threshold) :
    discreteRawSupportWitness G f threshold (.inl x) ∈
      componentSupport G f (threshold x.1) x.2 := by
  exact Classical.choose_spec (sliceNode_support_nonempty G f threshold x)

theorem discreteRawSupportWitness_edge_source_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ)
    (e : OrientedEdge (discreteReebGraph G f threshold))
    (a : GraphUnitInterval) :
    discreteRawSupportWitness G f threshold (.inr (e, a)) ∈
      componentSupport G f (threshold e.source.1) e.source.2 := by
  exact (Classical.choose_spec
    (show SliceOverlap G f threshold e.source e.target from e.2.2)).1

theorem discreteRawSupportWitness_edge_target_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ)
    (e : OrientedEdge (discreteReebGraph G f threshold))
    (a : GraphUnitInterval) :
    discreteRawSupportWitness G f threshold (.inr (e, a)) ∈
      componentSupport G f (threshold e.target.1) e.target.2 := by
  exact (Classical.choose_spec
    (show SliceOverlap G f threshold e.source e.target from e.2.2)).2

end ReebGraph
