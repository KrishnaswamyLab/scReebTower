import Mathlib

/-!
# Topological realization of a simple graph

Topological realization of a simple graph as a filtered space.

Builds `SimpleGraphRealization` as a quotient of vertices and oriented
edges crossed with the unit interval, equips it with a continuous height,
and provides the machinery for mapping a realization continuously into
another filtered space.

Main results: `continuous_graphRealizationHeight`,
`joinedIn_graphRealization_of_walk`, and
`FilteredGraphRealizationMapData.height_close`.  The supporting material
is the gluing bookkeeping (`graphGlue_preserves_height`,
`graphEqvGen_preserves_height`) and the coherent edge-path constructions.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-! ## Conditional continuum approximation

The continuum Reeb quotient and discrete graph realization are explicit below.
The specialized comparison metric remains abstract until its interleaving or
functional-distortion theory is formalized.
-/

/-- Minimal data retained by a filtered Reeb graph.  The quotient map and graph
finiteness conditions will be added when the continuum construction is
formalized. -/
structure FilteredReebGraph where
  Carrier : Type
  topology : TopologicalSpace Carrier
  height : Carrier → ℝ

attribute [instance] FilteredReebGraph.topology

instance : Inhabited FilteredReebGraph where
  default :=
    { Carrier := Empty
      topology := ⊥
      height := Empty.elim }

/-! ### Topological realization of a simple graph -/

/-- A wrapper giving an arbitrary graph vertex type the discrete topology. -/
def GraphVertex (V : Type*) := V

instance graphVertexTopology (V : Type*) : TopologicalSpace (GraphVertex V) := ⊥
instance graphVertexDiscreteTopology (V : Type*) : DiscreteTopology (GraphVertex V) := ⟨rfl⟩

/-- An oriented presentation of an undirected edge.  Opposite orientations
will be identified in the realization quotient. -/
def OrientedEdge {V : Type*} (G : SimpleGraph V) :=
  {p : V × V // G.Adj p.1 p.2}

instance orientedEdgeTopology {V : Type*} (G : SimpleGraph V) :
    TopologicalSpace (OrientedEdge G) := ⊥
instance orientedEdgeDiscreteTopology {V : Type*} (G : SimpleGraph V) :
    DiscreteTopology (OrientedEdge G) := ⟨rfl⟩

namespace OrientedEdge

variable {V : Type*} {G : SimpleGraph V}

def source (e : OrientedEdge G) : V := e.1.1
def target (e : OrientedEdge G) : V := e.1.2

def reverse (e : OrientedEdge G) : OrientedEdge G :=
  ⟨(e.target, e.source), G.symm e.2⟩

@[simp] theorem source_reverse (e : OrientedEdge G) : e.reverse.source = e.target := rfl
@[simp] theorem target_reverse (e : OrientedEdge G) : e.reverse.target = e.source := rfl

end OrientedEdge

/-- The closed unit interval used to parametrize graph edges. -/
abbrev GraphUnitInterval := Set.Icc (0 : ℝ) 1

def graphUnitZero : GraphUnitInterval := ⟨0, by norm_num⟩
def graphUnitOne : GraphUnitInterval := ⟨1, by norm_num⟩

def graphUnitReverse (s : GraphUnitInterval) : GraphUnitInterval :=
  ⟨1 - s.1, by constructor <;> linarith [s.2.1, s.2.2]⟩

@[simp] theorem graphUnitReverse_value (s : GraphUnitInterval) :
    (graphUnitReverse s).1 = 1 - s.1 := rfl

/-- Before gluing, a graph realization is the disjoint union of discrete
vertices and one closed interval for each oriented edge. -/
def GraphRealizationRaw {V : Type*} (G : SimpleGraph V) :=
  GraphVertex V ⊕ (OrientedEdge G × GraphUnitInterval)

instance graphRealizationRawTopology {V : Type*} (G : SimpleGraph V) :
    TopologicalSpace (GraphRealizationRaw G) :=
  inferInstanceAs
    (TopologicalSpace (GraphVertex V ⊕ (OrientedEdge G × GraphUnitInterval)))

/-- Generating identifications for the graph realization: interval endpoints
are attached to their vertices and opposite orientations describe the same
geometric edge. -/
inductive GraphGlue {V : Type*} (G : SimpleGraph V) :
    GraphRealizationRaw G → GraphRealizationRaw G → Prop
  | source (e : OrientedEdge G) :
      GraphGlue G (.inl e.source) (.inr (e, graphUnitZero))
  | target (e : OrientedEdge G) :
      GraphGlue G (.inl e.target) (.inr (e, graphUnitOne))
  | reverse (e : OrientedEdge G) (s : GraphUnitInterval) :
      GraphGlue G (.inr (e, s)) (.inr (e.reverse, graphUnitReverse s))

/-- Linear interpolation of a vertex height along every oriented edge. -/
def graphRealizationRawHeight
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ) :
    GraphRealizationRaw G → ℝ
  | .inl v => height v
  | .inr (e, s) => (1 - s.1) * height e.source + s.1 * height e.target

theorem graphGlue_preserves_height
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ)
    {x y : GraphRealizationRaw G} (hxy : GraphGlue G x y) :
    graphRealizationRawHeight height x = graphRealizationRawHeight height y := by
  cases hxy with
  | source e => simp [graphRealizationRawHeight, graphUnitZero]
  | target e => simp [graphRealizationRawHeight, graphUnitOne]
  | reverse e s =>
      simp only [graphRealizationRawHeight, graphUnitReverse_value,
        OrientedEdge.source_reverse, OrientedEdge.target_reverse]
      ring

theorem graphEqvGen_preserves_height
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ)
    {x y : GraphRealizationRaw G}
    (hxy : Relation.EqvGen (GraphGlue G) x y) :
    graphRealizationRawHeight height x = graphRealizationRawHeight height y := by
  induction hxy with
  | rel x y h => exact graphGlue_preserves_height height h
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

theorem continuous_graphRealizationRawHeight
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ) :
    Continuous (graphRealizationRawHeight height : GraphRealizationRaw G → ℝ) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_of_discreteTopology
  · have hs : Continuous
        (fun p : OrientedEdge G × GraphUnitInterval => p.2.1) :=
      continuous_subtype_val.comp continuous_snd
    have hsource : Continuous
        (fun p : OrientedEdge G × GraphUnitInterval => height p.1.source) :=
      (show Continuous (fun e : OrientedEdge G => height e.source) from
        continuous_of_discreteTopology).comp continuous_fst
    have htarget : Continuous
        (fun p : OrientedEdge G × GraphUnitInterval => height p.1.target) :=
      (show Continuous (fun e : OrientedEdge G => height e.target) from
        continuous_of_discreteTopology).comp continuous_fst
    exact ((continuous_const.sub hs).mul hsource).add (hs.mul htarget)

/-- The usual one-dimensional CW realization of a simple graph, constructed
as the quotient of its vertices and edge intervals by endpoint attachment and
orientation reversal. -/
def SimpleGraphRealization {V : Type*} (G : SimpleGraph V) :=
  Quotient (Relation.EqvGen.setoid (GraphGlue G))

instance simpleGraphRealizationTopology {V : Type*} (G : SimpleGraph V) :
    TopologicalSpace (SimpleGraphRealization G) :=
  instTopologicalSpaceQuotient

def graphRealizationQuotientMap {V : Type*} (G : SimpleGraph V) :
    GraphRealizationRaw G → SimpleGraphRealization G :=
  Quotient.mk (Relation.EqvGen.setoid (GraphGlue G))

theorem continuous_graphRealizationQuotientMap
    {V : Type*} (G : SimpleGraph V) :
    Continuous (graphRealizationQuotientMap G) :=
  continuous_quotient_mk'

def graphRealizationVertex
    {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraphRealization G :=
  graphRealizationQuotientMap G (.inl v)

def graphRealizationEdgePoint
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G)
    (s : GraphUnitInterval) : SimpleGraphRealization G :=
  graphRealizationQuotientMap G (.inr (e, s))

theorem graphRealization_source_glue
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G) :
    graphRealizationVertex G e.source =
      graphRealizationEdgePoint G e graphUnitZero := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (GraphGlue.source e)

theorem graphRealization_target_glue
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G) :
    graphRealizationVertex G e.target =
      graphRealizationEdgePoint G e graphUnitOne := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (GraphGlue.target e)

theorem graphRealization_reverse_glue
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G)
    (s : GraphUnitInterval) :
    graphRealizationEdgePoint G e s =
      graphRealizationEdgePoint G e.reverse (graphUnitReverse s) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (GraphGlue.reverse e s)

/-- Canonical path traversing one oriented edge of a graph realization. -/
def graphRealizationEdgePath
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G) :
    Path (graphRealizationVertex G e.source)
      (graphRealizationVertex G e.target) where
  toFun s := graphRealizationEdgePoint G e s
  continuous_toFun :=
    (continuous_graphRealizationQuotientMap G).comp
      (continuous_inr.comp (continuous_const.prod_mk continuous_id))
  source' := (graphRealization_source_glue G e).symm
  target' := (graphRealization_target_glue G e).symm

/-- Contract an edge parameter linearly toward its source endpoint. -/
def graphUnitContractToSource
    (s t : GraphUnitInterval) : GraphUnitInterval :=
  ⟨(1 - t.1) * s.1, by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr t.2.2) s.2.1
    · calc
        (1 - t.1) * s.1 ≤ 1 * s.1 :=
          mul_le_mul_of_nonneg_right (by linarith [t.2.1]) s.2.1
        _ = s.1 := one_mul _
        _ ≤ 1 := s.2.2⟩

theorem continuous_graphUnitContractToSource (s : GraphUnitInterval) :
    Continuous (graphUnitContractToSource s) := by
  apply Continuous.subtype_mk
  exact (continuous_const.sub continuous_subtype_val).mul continuous_const

/-- The partial edge path from an arbitrary point back to the source vertex. -/
def graphRealizationEdgeToSourcePath
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G)
    (s : GraphUnitInterval) :
    Path (graphRealizationEdgePoint G e s)
      (graphRealizationVertex G e.source) where
  toFun t := graphRealizationEdgePoint G e (graphUnitContractToSource s t)
  continuous_toFun :=
    (continuous_graphRealizationQuotientMap G).comp
      (continuous_inr.comp
        (continuous_const.prod_mk (continuous_graphUnitContractToSource s)))
  source' := by
    apply congrArg (graphRealizationEdgePoint G e)
    apply Subtype.ext
    simp [graphUnitContractToSource]
  target' := by
    change graphRealizationEdgePoint G e (graphUnitContractToSource s 1) =
      graphRealizationVertex G e.source
    rw [show graphUnitContractToSource s 1 = graphUnitZero by
      apply Subtype.ext
      simp [graphUnitContractToSource, graphUnitZero]]
    exact (graphRealization_source_glue G e).symm

/-- The piecewise-linear height descended to the graph realization. -/
noncomputable def graphRealizationHeight
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ) :
    SimpleGraphRealization G → ℝ :=
  Quotient.lift (graphRealizationRawHeight height)
    (fun _ _ h => graphEqvGen_preserves_height height h)

@[simp] theorem graphRealizationHeight_quotientMap
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ)
    (x : GraphRealizationRaw G) :
    graphRealizationHeight G height (graphRealizationQuotientMap G x) =
      graphRealizationRawHeight height x :=
  rfl

@[simp] theorem graphRealizationHeight_vertex
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ) (v : V) :
    graphRealizationHeight G height (graphRealizationVertex G v) = height v :=
  rfl

@[simp] theorem graphRealizationHeight_edgePoint
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ)
    (e : OrientedEdge G) (s : GraphUnitInterval) :
    graphRealizationHeight G height (graphRealizationEdgePoint G e s) =
      (1 - s.1) * height e.source + s.1 * height e.target :=
  rfl

theorem continuous_graphRealizationHeight
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ) :
    Continuous (graphRealizationHeight G height) := by
  apply (continuous_graphRealizationRawHeight height).quotient_lift

/-- An interior edge point can be anchored at its source without leaving the
input scalar band by more than the height oscillation of that edge. -/
theorem joinedIn_graphRealization_edgePoint_to_source
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ)
    {a b e : ℝ} (he : 0 ≤ e) (edge : OrientedEdge G)
    (hgap : |height edge.source - height edge.target| ≤ e)
    (s : GraphUnitInterval)
    (hs : a ≤ graphRealizationHeight G height
        (graphRealizationEdgePoint G edge s) ∧
      graphRealizationHeight G height
        (graphRealizationEdgePoint G edge s) ≤ b) :
    JoinedIn
      {z | a - e ≤ graphRealizationHeight G height z ∧
        graphRealizationHeight G height z ≤ b + e}
      (graphRealizationEdgePoint G edge s)
      (graphRealizationVertex G edge.source) := by
  let hsval := graphRealizationHeight G height
    (graphRealizationEdgePoint G edge s)
  have hsourceClose : |height edge.source - hsval| ≤ e := by
    change |height edge.source -
      ((1 - s.1) * height edge.source + s.1 * height edge.target)| ≤ e
    calc
      |height edge.source -
          ((1 - s.1) * height edge.source + s.1 * height edge.target)| =
          |s.1 * (height edge.source - height edge.target)| := by
            congr 1
            ring
      _ = s.1 * |height edge.source - height edge.target| := by
        rw [abs_mul, abs_of_nonneg s.2.1]
      _ ≤ s.1 * e := mul_le_mul_of_nonneg_left hgap s.2.1
      _ ≤ 1 * e := mul_le_mul_of_nonneg_right s.2.2 he
      _ = e := one_mul _
  rw [abs_sub_le_iff] at hsourceClose
  have hsource : a - e ≤ height edge.source ∧
      height edge.source ≤ b + e := by
    constructor <;> linarith [hs.1, hs.2, hsourceClose.1, hsourceClose.2]
  refine ⟨graphRealizationEdgeToSourcePath G edge s, ?_⟩
  intro t
  change a - e ≤
      (1 - (graphUnitContractToSource s t).1) * height edge.source +
        (graphUnitContractToSource s t).1 * height edge.target ∧
    (1 - (graphUnitContractToSource s t).1) * height edge.source +
        (graphUnitContractToSource s t).1 * height edge.target ≤ b + e
  have hformula :
      (1 - (graphUnitContractToSource s t).1) * height edge.source +
          (graphUnitContractToSource s t).1 * height edge.target =
        t.1 * height edge.source + (1 - t.1) * hsval := by
    simp only [graphUnitContractToSource, hsval,
      graphRealizationHeight_edgePoint]
    ring
  rw [hformula]
  constructor
  · calc
      a - e = t.1 * (a - e) + (1 - t.1) * (a - e) := by ring
      _ ≤ t.1 * height edge.source + (1 - t.1) * hsval := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsource.1 t.2.1)
          (mul_le_mul_of_nonneg_left (by linarith [hs.1, he])
            (sub_nonneg.mpr t.2.2))
  · calc
      t.1 * height edge.source + (1 - t.1) * hsval ≤
          t.1 * (b + e) + (1 - t.1) * (b + e) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsource.2 t.2.1)
          (mul_le_mul_of_nonneg_left (by linarith [hs.2, he])
            (sub_nonneg.mpr t.2.2))
      _ = b + e := by ring

/-- A graph walk whose visited vertex heights lie in one interval realizes as
a path in the CW complex inside the same interval.  Linear interpolation on
edges introduces no additional scalar error. -/
theorem joinedIn_graphRealization_of_walk
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ)
    {a b : ℝ} {u v : V} (p : G.Walk u v)
    (hp : ∀ w, w ∈ p.support → a ≤ height w ∧ height w ≤ b) :
    JoinedIn
      {z | a ≤ graphRealizationHeight G height z ∧
        graphRealizationHeight G height z ≤ b}
      (graphRealizationVertex G u) (graphRealizationVertex G v) := by
  induction p with
  | @nil u =>
      exact JoinedIn.refl (by simpa using hp u (by simp))
  | @cons u v w huv p ih =>
      have hu : a ≤ height u ∧ height u ≤ b := hp u (by simp)
      have hv : a ≤ height v ∧ height v ≤ b :=
        hp v (by simp [p.start_mem_support])
      let e : OrientedEdge G := ⟨(u, v), huv⟩
      have hedge : JoinedIn
          {z | a ≤ graphRealizationHeight G height z ∧
            graphRealizationHeight G height z ≤ b}
          (graphRealizationVertex G u) (graphRealizationVertex G v) := by
        refine ⟨graphRealizationEdgePath G e, ?_⟩
        intro s
        change a ≤ (1 - s.1) * height u + s.1 * height v ∧
          (1 - s.1) * height u + s.1 * height v ≤ b
        constructor
        · calc
            a = (1 - s.1) * a + s.1 * a := by ring
            _ ≤ (1 - s.1) * height u + s.1 * height v :=
              add_le_add
                (mul_le_mul_of_nonneg_left hu.1 (by linarith [s.2.2]))
                (mul_le_mul_of_nonneg_left hv.1 s.2.1)
        · calc
            (1 - s.1) * height u + s.1 * height v ≤
                (1 - s.1) * b + s.1 * b :=
              add_le_add
                (mul_le_mul_of_nonneg_left hu.2 (by linarith [s.2.2]))
                (mul_le_mul_of_nonneg_left hv.2 s.2.1)
            _ = b := by ring
      have htail := ih (fun z hz ↦ hp z (by simp [hz]))
      exact hedge.trans htail

/-- Data for a continuous map out of a graph realization: vertex images and
orientation-compatible paths on its edges. -/
structure GraphRealizationMapData
    {V : Type*} (G : SimpleGraph V) (Y : Type*) [TopologicalSpace Y] where
  vertexMap : V → Y
  edgePath : (e : OrientedEdge G) → Path (vertexMap e.source) (vertexMap e.target)
  reverse_compatible : ∀ (e : OrientedEdge G) (s : GraphUnitInterval),
    edgePath e s = edgePath e.reverse (graphUnitReverse s)

def GraphRealizationMapData.rawMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) : GraphRealizationRaw G → Y
  | .inl v => d.vertexMap v
  | .inr (e, s) => d.edgePath e s

theorem GraphRealizationMapData.continuous_rawMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) : Continuous d.rawMap := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_of_discreteTopology
  · apply continuous_prod_of_discrete_left.mpr
    intro e
    exact (d.edgePath e).continuous

theorem GraphRealizationMapData.graphGlue_preserved
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y)
    {x y : GraphRealizationRaw G} (hxy : GraphGlue G x y) :
    d.rawMap x = d.rawMap y := by
  cases hxy with
  | source e => exact (d.edgePath e).source.symm
  | target e => exact (d.edgePath e).target.symm
  | reverse e s => exact d.reverse_compatible e s

theorem GraphRealizationMapData.graphEqvGen_preserved
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y)
    {x y : GraphRealizationRaw G}
    (hxy : Relation.EqvGen (GraphGlue G) x y) : d.rawMap x = d.rawMap y := by
  induction hxy with
  | rel _ _ h => exact d.graphGlue_preserved h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

/-- Continuous map descended from compatible vertex and edge data. -/
def GraphRealizationMapData.realizationMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) : SimpleGraphRealization G → Y :=
  Quotient.lift d.rawMap (fun _ _ h => d.graphEqvGen_preserved h)

@[simp] theorem GraphRealizationMapData.realizationMap_quotientMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) (x : GraphRealizationRaw G) :
    d.realizationMap (graphRealizationQuotientMap G x) = d.rawMap x :=
  rfl

theorem GraphRealizationMapData.continuous_realizationMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) : Continuous d.realizationMap := by
  unfold realizationMap
  exact d.continuous_rawMap.quotient_lift
    (fun _ _ h => d.graphEqvGen_preserved h)

noncomputable def chosenAdjacentPath
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (vertexMap : V → Y)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (Path (vertexMap u) (vertexMap v)))
    {u v : V} (huv : G.Adj u v) : Path (vertexMap u) (vertexMap v) :=
  Classical.choice (hedge huv)

/-- Orient every edge using a fixed linear order, so opposite orientations use
one chosen path and its reverse rather than unrelated classical choices. -/
noncomputable def coherentOrientedEdgePath
    {V Y : Type*} [LinearOrder V] {G : SimpleGraph V} [TopologicalSpace Y]
    (vertexMap : V → Y)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (Path (vertexMap u) (vertexMap v)))
    (e : OrientedEdge G) : Path (vertexMap e.source) (vertexMap e.target) :=
  if h : e.source < e.target then
    chosenAdjacentPath vertexMap hedge e.2
  else
    (chosenAdjacentPath vertexMap hedge (G.symm e.2)).symm

theorem coherentOrientedEdgePath_reverse
    {V Y : Type*} [LinearOrder V] {G : SimpleGraph V} [TopologicalSpace Y]
    (vertexMap : V → Y)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (Path (vertexMap u) (vertexMap v)))
    (e : OrientedEdge G) (s : GraphUnitInterval) :
    coherentOrientedEdgePath vertexMap hedge e s =
      coherentOrientedEdgePath vertexMap hedge e.reverse (graphUnitReverse s) := by
  unfold coherentOrientedEdgePath
  by_cases h : e.source < e.target
  · have hn : ¬e.target < e.source := not_lt_of_ge h.le
    rw [dif_pos h]
    rw [dif_neg (show ¬e.reverse.source < e.reverse.target by simpa using hn)]
    simp only [Path.symm_apply, Function.comp_apply]
    have hpaths : chosenAdjacentPath vertexMap hedge e.2 =
        chosenAdjacentPath vertexMap hedge (G.symm e.reverse.2) := by
      congr
    rw [← hpaths]
    have hsame : graphUnitReverse s = unitInterval.symm s := rfl
    rw [hsame, unitInterval.symm_symm]
  · have hrev : e.target < e.source :=
      lt_of_le_of_ne (le_of_not_gt h) e.2.ne'
    rw [dif_neg h]
    rw [dif_pos (show e.reverse.source < e.reverse.target by simpa using hrev)]
    simp only [Path.symm_apply, Function.comp_apply]
    have hpaths : chosenAdjacentPath vertexMap hedge (G.symm e.2) =
        chosenAdjacentPath vertexMap hedge e.reverse.2 := by
      congr
    rw [← hpaths]
    have hsame : graphUnitReverse s = unitInterval.symm s := rfl
    rw [hsame]

/-- Any vertex map whose adjacent images can be joined by paths extends
continuously over the graph realization. -/
noncomputable def graphRealizationMapDataOfAdjacentPaths
    {V Y : Type*} [LinearOrder V] (G : SimpleGraph V) [TopologicalSpace Y]
    (vertexMap : V → Y)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (Path (vertexMap u) (vertexMap v))) :
    GraphRealizationMapData G Y where
  vertexMap := vertexMap
  edgePath := coherentOrientedEdgePath vertexMap hedge
  reverse_compatible := coherentOrientedEdgePath_reverse vertexMap hedge

/-- A path assigned to an adjacent pair together with a uniform comparison
between its filtered height and linear interpolation of the endpoint
heights. -/
structure HeightControlledAdjacentPath
    {V : Type*} (height : V → ℝ) (Y : FilteredReebGraph) (e : ℝ)
    (vertexMap : V → Y.Carrier) (u v : V) where
  path : Path (vertexMap u) (vertexMap v)
  height_close : ∀ s : GraphUnitInterval,
    |(1 - s.1) * height u + s.1 * height v - Y.height (path s)| ≤ e

noncomputable def chosenHeightControlledAdjacentPath
    {V : Type*} {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ} (vertexMap : V → Y.Carrier)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (HeightControlledAdjacentPath height Y e vertexMap u v))
    {u v : V} (huv : G.Adj u v) :
    HeightControlledAdjacentPath height Y e vertexMap u v :=
  Classical.choice (hedge huv)

/-- A coherent path orientation that retains the quantitative data used to
choose its underlying unoriented edge path. -/
noncomputable def coherentHeightControlledEdgePath
    {V : Type*} [LinearOrder V] {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ} (vertexMap : V → Y.Carrier)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (HeightControlledAdjacentPath height Y e vertexMap u v))
    (edge : OrientedEdge G) :
    Path (vertexMap edge.source) (vertexMap edge.target) :=
  if h : edge.source < edge.target then
    (chosenHeightControlledAdjacentPath vertexMap hedge edge.2).path
  else
    (chosenHeightControlledAdjacentPath vertexMap hedge (G.symm edge.2)).path.symm

theorem coherentHeightControlledEdgePath_reverse
    {V : Type*} [LinearOrder V] {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ} (vertexMap : V → Y.Carrier)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (HeightControlledAdjacentPath height Y e vertexMap u v))
    (edge : OrientedEdge G) (s : GraphUnitInterval) :
    coherentHeightControlledEdgePath vertexMap hedge edge s =
      coherentHeightControlledEdgePath vertexMap hedge edge.reverse
        (graphUnitReverse s) := by
  unfold coherentHeightControlledEdgePath
  by_cases h : edge.source < edge.target
  · have hn : ¬edge.target < edge.source := not_lt_of_ge h.le
    rw [dif_pos h]
    rw [dif_neg (show ¬edge.reverse.source < edge.reverse.target by simpa using hn)]
    simp only [Path.symm_apply, Function.comp_apply]
    have hpaths :
        (chosenHeightControlledAdjacentPath vertexMap hedge edge.2).path =
          (chosenHeightControlledAdjacentPath vertexMap hedge
            (G.symm edge.reverse.2)).path := by
      congr
    rw [← hpaths]
    have hsame : graphUnitReverse s = unitInterval.symm s := rfl
    rw [hsame, unitInterval.symm_symm]
  · have hrev : edge.target < edge.source :=
      lt_of_le_of_ne (le_of_not_gt h) edge.2.ne'
    rw [dif_neg h]
    rw [dif_pos (show edge.reverse.source < edge.reverse.target by simpa using hrev)]
    simp only [Path.symm_apply, Function.comp_apply]
    have hpaths :
        (chosenHeightControlledAdjacentPath vertexMap hedge
          (G.symm edge.2)).path =
          (chosenHeightControlledAdjacentPath vertexMap hedge
            edge.reverse.2).path := by
      congr
    rw [← hpaths]
    have hsame : graphUnitReverse s = unitInterval.symm s := rfl
    rw [hsame]

theorem coherentHeightControlledEdgePath_height_close
    {V : Type*} [LinearOrder V] {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ} (vertexMap : V → Y.Carrier)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (HeightControlledAdjacentPath height Y e vertexMap u v))
    (edge : OrientedEdge G) (s : GraphUnitInterval) :
    |(1 - s.1) * height edge.source + s.1 * height edge.target -
      Y.height (coherentHeightControlledEdgePath vertexMap hedge edge s)| ≤ e := by
  unfold coherentHeightControlledEdgePath
  by_cases h : edge.source < edge.target
  · rw [dif_pos h]
    exact (chosenHeightControlledAdjacentPath vertexMap hedge edge.2).height_close s
  · rw [dif_neg h]
    have hclose :=
      (chosenHeightControlledAdjacentPath vertexMap hedge
        (G.symm edge.2)).height_close (graphUnitReverse s)
    simp only [Path.symm_apply, Function.comp_apply]
    have hsame : unitInterval.symm s = graphUnitReverse s := rfl
    rw [hsame]
    convert hclose using 1 <;>
      simp only [graphUnitReverse_value] <;> congr 1 <;>
        unfold OrientedEdge.source OrientedEdge.target <;> ring

/-- A continuous graph-realization map with quantitative control of the
filtered height at vertices and along every oriented edge. -/
structure FilteredGraphRealizationMapData
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ)
    (Y : FilteredReebGraph) (e : ℝ)
    extends GraphRealizationMapData G Y.Carrier where
  vertex_height_close : ∀ v,
    |height v - Y.height (toGraphRealizationMapData.vertexMap v)| ≤ e
  edge_height_close : ∀ (edge : OrientedEdge G) (s : GraphUnitInterval),
    |(1 - s.1) * height edge.source + s.1 * height edge.target -
      Y.height (toGraphRealizationMapData.edgePath edge s)| ≤ e

def FilteredGraphRealizationMapData.realizationMap
    {V : Type*} {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ}
    (d : FilteredGraphRealizationMapData G height Y e) :
    SimpleGraphRealization G → Y.Carrier :=
  d.toGraphRealizationMapData.realizationMap

theorem FilteredGraphRealizationMapData.continuous_realizationMap
    {V : Type*} {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ}
    (d : FilteredGraphRealizationMapData G height Y e) :
    Continuous d.realizationMap :=
  d.toGraphRealizationMapData.continuous_realizationMap

theorem FilteredGraphRealizationMapData.height_close
    {V : Type*} {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ}
    (d : FilteredGraphRealizationMapData G height Y e)
    (z : SimpleGraphRealization G) :
    |graphRealizationHeight G height z - Y.height (d.realizationMap z)| ≤ e := by
  refine Quotient.inductionOn z ?_
  intro raw
  cases raw with
  | inl v => exact d.vertex_height_close v
  | inr p =>
      rcases p with ⟨edge, s⟩
      exact d.edge_height_close edge s

end ReebGraph
