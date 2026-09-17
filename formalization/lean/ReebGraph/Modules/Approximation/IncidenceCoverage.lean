import ReebGraph.Modules.Approximation.ContinuousMap

/-!
# Incidence coverage and image reflection

Finite incidence reflection: showing every continuum point is seen by a
canonical node, at a controlled band cost.

Main results:
`ApproximationHypotheses.canonicalNodeIncidenceBandCoverageAt_of_tame_of_nonflat`,
`.imageBandReflection_three_add_of_incidenceCoverageAt`, and
`.imageBandReflection_four_of_incidenceCoverage`.

Supporting: slab-walk completeness, the manifold band path-lift
transfers, and the roundtrip realizability lemmas from short-path
soundness.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Reverse transition completeness stated at the common budget used by the
continuous forward map. -/
def ContinuousCanonicalManifoldBandTransitionComplete
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {p p' : M}, a ≤ b →
    JoinedIn {z | a ≤ f z ∧ f z ≤ b} p p' →
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - continuousCanonicalComparisonError L r δ η q)
      (b + continuousCanonicalComparisonError L r δ η q)
      (h.continuumToDiscreteMap (continuumReebQuotientMap f p))
      (h.continuumToDiscreteMap (continuumReebQuotientMap f p'))

/-- The continuum round trip for the continuous forward support map is
realized by a controlled path before passing to the Reeb quotient. -/
def ContinuousCanonicalContinuumRoundtripRealizable
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ y : (continuumReebGraph M f).Carrier,
    ∃ p p' : M,
      continuumReebQuotientMap f p = y ∧
      continuumReebQuotientMap f p' =
        h.continuousDiscreteToContinuumMap (h.continuumToDiscreteMap y) ∧
      JoinedIn {z |
        (discreteReebRealization V G fhat).height
            (h.continuumToDiscreteMap y) -
            continuousCanonicalComparisonError L r δ η q ≤ f z ∧
        f z ≤ (discreteReebRealization V G fhat).height
            (h.continuumToDiscreteMap y) +
            continuousCanonicalComparisonError L r δ η q} p p'

/-- Local geodesic accessibility discharges the continuum round-trip
condition.  The first path segment reaches the nearby canonical active sample;
the second follows the support component to the representative used by the
continuous realization map. -/
theorem ApproximationHypotheses.continuousContinuumRoundtrip_of_shortPathSound
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hshort : ShortPathSound M δ) :
    ContinuousCanonicalContinuumRoundtripRealizable h := by
  intro y
  let x : M := Quotient.out y
  let w := h.canonicalPointWitness x
  let node : SliceNode G fhat (canonicalThreshold fhat) :=
    ⟨w.index, componentOfActive G fhat (canonicalThreshold fhat w.index)
      ⟨w.vertex, w.active⟩⟩
  let u := canonicalNodeSupportWitness G fhat node
  have hxy : continuumReebQuotientMap f x = y := Quotient.out_eq y
  have hxw : dist x (sample w.vertex) ≤ δ := by
    simpa only [dist_comm] using w.spatial_close
  rcases hshort hxw with ⟨γnear, hγnear⟩
  have hwSupport : w.vertex ∈
      componentSupport G fhat (canonicalThreshold fhat node.1) node.2 := by
    exact mem_componentSupport_componentOfActive G fhat
      (canonicalThreshold fhat w.index) ⟨w.vertex, w.active⟩
  have huSupport : u ∈
      componentSupport G fhat (canonicalThreshold fhat node.1) node.2 :=
    canonicalNodeSupportWitness_mem G fhat node
  have hsupport := h.support_component_no_merge node.2 hwSupport huSupport
  let γ := γnear.trans hsupport.somePath
  refine ⟨x, sample u, hxy, ?_, ⟨γ, ?_⟩⟩
  · change continuumReebQuotientMap f (sample u) =
      h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) node)
    rw [h.continuousDiscreteToContinuumMap_vertex]
    rfl
  · intro s
    change canonicalThreshold fhat node.1 -
        continuousCanonicalComparisonError L r δ η q ≤ f (γ s) ∧
      f (γ s) ≤ canonicalThreshold fhat node.1 +
        continuousCanonicalComparisonError L r δ η q
    have hsRange : γ s ∈
        Set.range γnear ∪ Set.range hsupport.somePath := by
      rw [← γnear.trans_range hsupport.somePath]
      exact ⟨s, rfl⟩
    have habs : |f (γ s) - canonicalThreshold fhat node.1| ≤
        continuousCanonicalComparisonError L r δ η q := by
      rcases hsRange with hs | hs
      · rcases hs with ⟨t, ht⟩
        have hLip : |f (γnear t) - f x| ≤ L * δ :=
          (h.lipschitz (γnear t) x).trans
            (mul_le_mul_of_nonneg_left (hγnear t)
              h.lipschitz_constant_nonneg)
        have hwHeight : |f x - canonicalThreshold fhat node.1| ≤
            approximationComparisonError L r δ η q := by
          simpa only [abs_sub_comm] using w.height_close
        rw [← ht]
        calc
          |f (γnear t) - canonicalThreshold fhat node.1| =
              |(f (γnear t) - f x) +
                (f x - canonicalThreshold fhat node.1)| := by ring_nf
          _ ≤ |f (γnear t) - f x| +
              |f x - canonicalThreshold fhat node.1| := abs_add _ _
          _ ≤ L * δ + approximationComparisonError L r δ η q :=
            add_le_add hLip hwHeight
          _ = approximationComparisonError L r δ η q + L * δ :=
            add_comm _ _
          _ ≤ continuousCanonicalComparisonError L r δ η q := by
            exact le_max_left _ _
      · rcases hs with ⟨t, ht⟩
        have htBand := hsupport.somePath_mem t
        have hLr : 0 ≤ L * r :=
          mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
        have hsmall : (L * r + 3 * η + 3 * q) + L * r ≤
            continuousForwardError L r η q := by
          unfold continuousForwardError
          linarith [h.filter_error_nonneg, h.quantization_error_nonneg]
        rw [← ht]
        exact htBand.trans (hsmall.trans (le_max_right _ _))
    rw [abs_sub_le_iff] at habs
    constructor <;> linarith [habs.1, habs.2]

/-- Projected form of the continuum round trip supplied by local short paths. -/
theorem ApproximationHypotheses.continuousContinuumRoundtrip_band_of_shortPathSound
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hshort : ShortPathSound M δ)
    (y : (continuumReebGraph M f).Carrier) :
    HeightBandJoined (continuumReebGraph M f)
      ((discreteReebRealization V G fhat).height
          (h.continuumToDiscreteMap y) -
        continuousCanonicalComparisonError L r δ η q)
      ((discreteReebRealization V G fhat).height
          (h.continuumToDiscreteMap y) +
        continuousCanonicalComparisonError L r δ η q)
      y (h.continuousDiscreteToContinuumMap (h.continuumToDiscreteMap y)) := by
  rcases h.continuousContinuumRoundtrip_of_shortPathSound hshort y with
    ⟨p, p', hp, hp', hpath⟩
  have hprojected := joinedIn_continuumReebQuotientMap hpath
  rw [hp, hp'] at hprojected
  exact hprojected

/-- The single estimator-specific reverse statement needed by the reduced
continuous comparison: band paths whose endpoints lie in the image of the
support map reflect to the discrete realization with one error enlargement. -/
def ContinuousCanonicalImageBandReflection
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ}
    {x x' : (discreteReebRealization V G fhat).Carrier},
    a ≤ b →
    HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap x') →
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - continuousCanonicalComparisonError L r δ η q)
      (b + continuousCanonicalComparisonError L r δ η q) x x'

/-- Non-circular finite target for the remaining geometry.  A continuum band
path between images of canonical component nodes must lift to a horizontal /
vertical active-witness walk whose slice heights remain in the expanded band. -/
def CanonicalNodeIncidenceBandCoverageAt
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (e : ℝ) : Prop :=
  ∀ {a b : ℝ} {x y : SliceNode G fhat (canonicalThreshold fhat)},
    a ≤ b →
    HeightBandJoined (continuumReebGraph M f) a b
      (h.canonicalNodeContinuumMap x) (h.canonicalNodeContinuumMap y) →
    ∃ u v : CanonicalActiveState G fhat,
      ∃ p : (canonicalActiveIncidenceGraph G fhat).Walk u v,
        canonicalActiveStateNode G fhat u = x ∧
        canonicalActiveStateNode G fhat v = y ∧
        ∀ z, z ∈ p.support →
          a - e ≤ canonicalThreshold fhat z.1 ∧
          canonicalThreshold fhat z.1 ≤ b + e

/-- The original incidence interface uses one common comparison-error unit. -/
def CanonicalNodeIncidenceBandCoverage
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  CanonicalNodeIncidenceBandCoverageAt h
    (continuousCanonicalComparisonError L r δ η q)

/-- Reeb-band paths between canonical node images lift to manifold paths
between the exact sample representatives selected for those nodes. -/
def CanonicalNodeManifoldBandPathLift
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {x y : SliceNode G fhat (canonicalThreshold fhat)},
    HeightBandJoined (continuumReebGraph M f) a b
      (h.canonicalNodeContinuumMap x) (h.canonicalNodeContinuumMap y) →
    JoinedIn {z | a ≤ f z ∧ f z ≤ b}
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat y))

/-- Node-specific manifold lifting with an explicit scalar enlargement. -/
def CanonicalNodeManifoldBandPathLiftWithSlack
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {x y : SliceNode G fhat (canonicalThreshold fhat)},
    HeightBandJoined (continuumReebGraph M f) a b
      (h.canonicalNodeContinuumMap x) (h.canonicalNodeContinuumMap y) →
    JoinedIn {z | a - s ≤ f z ∧ f z ≤ b + s}
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat y))

/-- A slackened quotient lift attaches to the canonical node representatives
through exact level components, without consuming additional slack. -/
theorem ApproximationHypotheses.canonicalNodeManifoldBandPathLift_of_reebLiftWithSlack
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hs : 0 ≤ s) (hlift : ContinuumReebBandPathLiftWithSlack M f s) :
    CanonicalNodeManifoldBandPathLiftWithSlack (s := s) h := by
  intro a b x y hxy
  rcases hlift hxy with ⟨p, p', hp, hp', hmiddle⟩
  let sx := sample (canonicalNodeSupportWitness G fhat x)
  let sy := sample (canonicalNodeSupportWitness G fhat y)
  have hqLeft : continuumReebQuotientMap f sx =
      continuumReebQuotientMap f p := by
    change h.canonicalNodeContinuumMap x = continuumReebQuotientMap f p
    exact hp.symm
  have hqRight : continuumReebQuotientMap f p' =
      continuumReebQuotientMap f sy := by
    change continuumReebQuotientMap f p' = h.canonicalNodeContinuumMap y
    exact hp'
  have hleftLevel := h.tame_filter.joinedIn_of_sameLevelComponent
    ((continuumReebQuotientMap_eq_iff f sx p).mp hqLeft)
  have hrightLevel := h.tame_filter.joinedIn_of_sameLevelComponent
    ((continuumReebQuotientMap_eq_iff f p' sy).mp hqRight)
  have hsxBand : a - s ≤ f sx ∧ f sx ≤ b + s := by
    have hsx := hxy.source_mem
    change a ≤ f sx ∧ f sx ≤ b at hsx
    constructor <;> linarith [hsx.1, hsx.2]
  have hp'Band : a - s ≤ f p' ∧ f p' ≤ b + s := hmiddle.target_mem
  have hleft : JoinedIn {z | a - s ≤ f z ∧ f z ≤ b + s} sx p := by
    apply JoinedIn.mono hleftLevel
    intro z hz
    change f z = f sx at hz
    change a - s ≤ f z ∧ f z ≤ b + s
    rw [hz]
    exact hsxBand
  have hright : JoinedIn {z | a - s ≤ f z ∧ f z ≤ b + s} p' sy := by
    apply JoinedIn.mono hrightLevel
    intro z hz
    change f z = f p' at hz
    change a - s ≤ f z ∧ f z ≤ b + s
    rw [hz]
    exact hp'Band
  exact hleft.trans (hmiddle.trans hright)

/-- The usual Reeb quotient path-lifting property, together with tame level
fibers, supplies the node-specific manifold lift.  The short endpoint paths
remain in exact level sets and hence introduce no scalar enlargement. -/
theorem ApproximationHypotheses.canonicalNodeManifoldBandPathLift_of_reebLift
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hlift : ContinuumReebBandPathLift M f) :
    CanonicalNodeManifoldBandPathLift h := by
  intro a b x y hxy
  rcases hlift hxy with ⟨p, p', hp, hp', hmiddle⟩
  let sx := sample (canonicalNodeSupportWitness G fhat x)
  let sy := sample (canonicalNodeSupportWitness G fhat y)
  have hqLeft : continuumReebQuotientMap f sx =
      continuumReebQuotientMap f p := by
    change h.canonicalNodeContinuumMap x = continuumReebQuotientMap f p
    exact hp.symm
  have hqRight : continuumReebQuotientMap f p' =
      continuumReebQuotientMap f sy := by
    change continuumReebQuotientMap f p' = h.canonicalNodeContinuumMap y
    exact hp'
  have hleftLevel := h.tame_filter.joinedIn_of_sameLevelComponent
    ((continuumReebQuotientMap_eq_iff f sx p).mp hqLeft)
  have hrightLevel := h.tame_filter.joinedIn_of_sameLevelComponent
    ((continuumReebQuotientMap_eq_iff f p' sy).mp hqRight)
  have hsxBand : a ≤ f sx ∧ f sx ≤ b := by
    simpa only [sx, ApproximationHypotheses.canonicalNodeContinuumMap,
      continuumReebGraph_height_quotientMap] using hxy.source_mem
  have hp'Band : a ≤ f p' ∧ f p' ≤ b := hmiddle.target_mem
  have hleft : JoinedIn {z | a ≤ f z ∧ f z ≤ b} sx p := by
    apply JoinedIn.mono hleftLevel
    intro z hz
    change f z = f sx at hz
    change a ≤ f z ∧ f z ≤ b
    rw [hz]
    exact hsxBand
  have hright : JoinedIn {z | a ≤ f z ∧ f z ≤ b} p' sy := by
    apply JoinedIn.mono hrightLevel
    intro z hz
    change f z = f p' at hz
    change a ≤ f z ∧ f z ≤ b
    rw [hz]
    exact hp'Band
  exact hleft.trans (hmiddle.trans hright)

/-- Purely finite slab condition on the neighborhood graph.  A band-limited
ordinary graph walk between chosen component representatives must canonicalize
to a bounded walk in the active-incidence graph.  This mentions neither the
algorithm's quotient connectivity nor the continuum Reeb graph. -/
def CanonicalSlabWalkIncidenceComplete
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {x y : SliceNode G fhat (canonicalThreshold fhat)},
    a ≤ b →
    ∀ p : G.Walk (canonicalNodeSupportWitness G fhat x)
        (canonicalNodeSupportWitness G fhat y),
      (∀ w, w ∈ p.support →
        |fhat w - (a + b) / 2| ≤
          (b - a) / 2 + L * (r + δ) + η + q) →
      ∃ u v : CanonicalActiveState G fhat,
        ∃ qwalk : (canonicalActiveIncidenceGraph G fhat).Walk u v,
          canonicalActiveStateNode G fhat u = x ∧
          canonicalActiveStateNode G fhat v = y ∧
          ∀ z, z ∈ qwalk.support →
            a - continuousCanonicalComparisonError L r δ η q ≤
              canonicalThreshold fhat z.1 ∧
            canonicalThreshold fhat z.1 ≤
              b + continuousCanonicalComparisonError L r δ η q

/-- For a non-flat observed scalar on graph edges, slab canonicalization is a
theorem.  The graph-walk scalar slack plus one observed edge oscillation is
exactly the older comparison budget, so the existing common error suffices. -/
theorem ApproximationHypotheses.canonicalSlabWalkIncidenceComplete_of_nonflat
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hnonflat : GraphEdgeNonflat G fhat) :
    CanonicalSlabWalkIncidenceComplete h := by
  intro a b x y hab p hp
  let S := L * (r + δ) + η + q
  let D := L * r + 2 * η + 2 * q
  let E := continuousCanonicalComparisonError L r δ η q
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  have hLδ : 0 ≤ L * δ :=
    mul_nonneg h.lipschitz_constant_nonneg h.sampling_scale_nonneg
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith [h.filter_error_nonneg, h.quantization_error_nonneg]
  have hbudget : S + D ≤ E := by
    calc
      S + D = approximationComparisonError L r δ η q := by
        simp only [S, D, approximationComparisonError]
        ring
      _ ≤ approximationComparisonError L r δ η q + L * δ :=
        le_add_of_nonneg_right hLδ
      _ ≤ E := by
        exact le_max_left _ _
  have hSle : S ≤ E := by linarith
  have hpTight : ∀ w, w ∈ p.support →
      a - S ≤ fhat w ∧ fhat w ≤ b + S := by
    intro w hw
    have hwBand := hp w hw
    rw [abs_sub_le_iff] at hwBand
    dsimp [S]
    constructor <;> linarith [hwBand.1, hwBand.2]
  have hpWide : ∀ w, w ∈ p.support →
      a - E ≤ fhat w ∧ fhat w ≤ b + E := by
    intro w hw
    have hwTight := hpTight w hw
    constructor <;> linarith
  let ux := canonicalNodeSupportWitness G fhat x
  let uy := canonicalNodeSupportWitness G fhat y
  have huxSupport : ux ∈
      componentSupport G fhat (canonicalThreshold fhat x.1) x.2 :=
    canonicalNodeSupportWitness_mem G fhat x
  have huySupport : uy ∈
      componentSupport G fhat (canonicalThreshold fhat y.1) y.2 :=
    canonicalNodeSupportWitness_mem G fhat y
  have huxActive : IsActiveVertex G fhat (canonicalThreshold fhat x.1) ux :=
    componentSupport_isActive G fhat (canonicalThreshold fhat x.1) x.2 huxSupport
  have huyActive : IsActiveVertex G fhat (canonicalThreshold fhat y.1) uy :=
    componentSupport_isActive G fhat (canonicalThreshold fhat y.1) y.2 huySupport
  have huxValue := hpTight ux p.start_mem_support
  have huyValue := hpTight uy p.end_mem_support
  have huxClose := h.canonicalActive_threshold_close_observed huxActive
  have huyClose := h.canonicalActive_threshold_close_observed huyActive
  change |canonicalThreshold fhat x.1 - fhat ux| ≤ D at huxClose
  change |canonicalThreshold fhat y.1 - fhat uy| ≤ D at huyClose
  rw [abs_sub_le_iff] at huxClose huyClose
  have hxBand : a - E ≤ canonicalThreshold fhat x.1 ∧
      canonicalThreshold fhat x.1 ≤ b + E := by
    constructor <;>
      linarith [huxValue.1, huxValue.2, huxClose.1, huxClose.2, hbudget]
  have hyBand : a - E ≤ canonicalThreshold fhat y.1 ∧
      canonicalThreshold fhat y.1 ≤ b + E := by
    constructor <;>
      linarith [huyValue.1, huyValue.2, huyClose.1, huyClose.2, hbudget]
  let ustate : CanonicalActiveState G fhat := ⟨x.1, ⟨ux, huxActive⟩⟩
  let ystate : CanonicalActiveState G fhat := ⟨y.1, ⟨uy, huyActive⟩⟩
  have huxComponent : componentOfActive G fhat
      (canonicalThreshold fhat x.1) ⟨ux, huxActive⟩ = x.2 := by
    apply crossingComponent_eq_of_support_intersects G fhat
      (canonicalThreshold fhat x.1)
    exact ⟨ux, mem_componentSupport_componentOfActive G fhat
      (canonicalThreshold fhat x.1) ⟨ux, huxActive⟩, huxSupport⟩
  have huyComponent : componentOfActive G fhat
      (canonicalThreshold fhat y.1) ⟨uy, huyActive⟩ = y.2 := by
    apply crossingComponent_eq_of_support_intersects G fhat
      (canonicalThreshold fhat y.1)
    exact ⟨uy, mem_componentSupport_componentOfActive G fhat
      (canonicalThreshold fhat y.1) ⟨uy, huyActive⟩, huySupport⟩
  have huNode : canonicalActiveStateNode G fhat ustate = x := by
    unfold canonicalActiveStateNode ustate
    exact Sigma.ext rfl (heq_of_eq huxComponent)
  have hyNode : canonicalActiveStateNode G fhat ystate = y := by
    unfold canonicalActiveStateNode ystate
    exact Sigma.ext rfl (heq_of_eq huyComponent)
  have hlift := canonicalActiveIncidence_reachableWithin_of_walk_of_nonflat
    G fhat hnonflat p hpWide huxActive huyActive hxBand hyBand
  rcases hlift with ⟨qwalk, hqwalk⟩
  exact ⟨ustate, ystate, qwalk, huNode, hyNode, by
    intro z hz
    simpa only [E] using hqwalk z hz⟩

/-- Manifold band lifting, graph completeness, and finite slab
canonicalization imply the exact active-incidence coverage used by the main
deterministic theorem. -/
theorem ApproximationHypotheses.canonicalNodeIncidenceBandCoverage_of_slabWalk
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hlift : CanonicalNodeManifoldBandPathLift h)
    (hslab : CanonicalSlabWalkIncidenceComplete h) :
    CanonicalNodeIncidenceBandCoverage h := by
  intro a b x y hab hxy
  have hmanifold := hlift hxy
  have habs : JoinedIn
      {z | |f z - (a + b) / 2| ≤ (b - a) / 2}
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat y)) := by
    apply JoinedIn.mono hmanifold
    intro z hz
    change a ≤ f z ∧ f z ≤ b at hz
    change |f z - (a + b) / 2| ≤ (b - a) / 2
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hstart : dist
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat x)) ≤ δ := by
    simpa using h.sampling_scale_nonneg
  have hend : dist
      (sample (canonicalNodeSupportWitness G fhat y))
      (sample (canonicalNodeSupportWitness G fhat y)) ≤ δ := by
    simpa using h.sampling_scale_nonneg
  rcases h.lift_joinedIn_band habs hstart hend with ⟨p, hp⟩
  exact hslab hab p hp

/-- Slackened manifold lifting produces incidence coverage with exactly one
additional slack unit.  All graph-completeness and canonicalization estimates
are unchanged. -/
theorem ApproximationHypotheses.canonicalNodeIncidenceBandCoverageAt_of_slabWalk
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hs : 0 ≤ s)
    (hlift : CanonicalNodeManifoldBandPathLiftWithSlack (s := s) h)
    (hslab : CanonicalSlabWalkIncidenceComplete h) :
    CanonicalNodeIncidenceBandCoverageAt h
      (continuousCanonicalComparisonError L r δ η q + s) := by
  intro a b x y hab hxy
  have hmanifold := hlift hxy
  have habExpanded : a - s ≤ b + s := by linarith
  have habs : JoinedIn
      {z | |f z - ((a - s) + (b + s)) / 2| ≤
        ((b + s) - (a - s)) / 2}
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat y)) := by
    apply JoinedIn.mono hmanifold
    intro z hz
    change a - s ≤ f z ∧ f z ≤ b + s at hz
    change |f z - ((a - s) + (b + s)) / 2| ≤
      ((b + s) - (a - s)) / 2
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hstart : dist
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat x)) ≤ δ := by
    simpa using h.sampling_scale_nonneg
  have hend : dist
      (sample (canonicalNodeSupportWitness G fhat y))
      (sample (canonicalNodeSupportWitness G fhat y)) ≤ δ := by
    simpa using h.sampling_scale_nonneg
  rcases h.lift_joinedIn_band habs hstart hend with ⟨p, hp⟩
  rcases hslab habExpanded p hp with ⟨u, v, qwalk, hu, hv, hqwalk⟩
  refine ⟨u, v, qwalk, hu, hv, ?_⟩
  intro z hz
  have hzBand := hqwalk z hz
  constructor <;> linarith [hzBand.1, hzBand.2]

/-- For every positive slack, tame level fibers and local path-connectedness
discharge continuum quotient lifting; nonflat edges discharge the remaining
finite incidence condition. -/
theorem ApproximationHypotheses.canonicalNodeIncidenceBandCoverageAt_of_tame_of_nonflat
    {M : Type} [PseudoMetricSpace M] [LocPathConnectedSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hs : 0 < s) (hnonflat : GraphEdgeNonflat G fhat) :
    CanonicalNodeIncidenceBandCoverageAt h
      (continuousCanonicalComparisonError L r δ η q + s) :=
  h.canonicalNodeIncidenceBandCoverageAt_of_slabWalk hs.le
    (h.canonicalNodeManifoldBandPathLift_of_reebLiftWithSlack hs.le
      (continuumReebBandPathLiftWithSlack_of_tame M f h.tame_filter hs))
    (h.canonicalSlabWalkIncidenceComplete_of_nonflat hnonflat)

/-- Main discharge of the incidence condition: continuum Reeb path lifting
and non-flat observed graph edges imply bounded active-incidence coverage. -/
theorem ApproximationHypotheses.canonicalNodeIncidenceBandCoverage_of_reebLift_of_nonflat
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hlift : ContinuumReebBandPathLift M f)
    (hnonflat : GraphEdgeNonflat G fhat) :
    CanonicalNodeIncidenceBandCoverage h :=
  h.canonicalNodeIncidenceBandCoverage_of_slabWalk
    (h.canonicalNodeManifoldBandPathLift_of_reebLift hlift)
    (h.canonicalSlabWalkIncidenceComplete_of_nonflat hnonflat)

/-- Adjacent canonical slice heights differ by at most the common comparison
error.  Thus anchoring a CW interior point introduces no new scale. -/
theorem ApproximationHypotheses.canonicalAdjacentThreshold_gap_common
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : SliceNode G fhat (canonicalThreshold fhat)}
    (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) :
    |canonicalThreshold fhat x.1 - canonicalThreshold fhat y.1| ≤
      continuousCanonicalComparisonError L r δ η q := by
  change DiscreteReebAdj G fhat (canonicalThreshold fhat) x y at hxy
  rcases hxy.2 with ⟨w, hwx, hwy⟩
  have hwx' := h.support_component_sound x.2 hwx
  have hwy' := h.support_component_sound y.2 hwy
  have hgap :
      |canonicalThreshold fhat x.1 - canonicalThreshold fhat y.1| ≤
        2 * (L * r + 3 * η + 3 * q) := by
    calc
      |canonicalThreshold fhat x.1 - canonicalThreshold fhat y.1| =
          |(canonicalThreshold fhat x.1 - f (sample w)) +
            (f (sample w) - canonicalThreshold fhat y.1)| := by ring_nf
      _ ≤ |canonicalThreshold fhat x.1 - f (sample w)| +
          |f (sample w) - canonicalThreshold fhat y.1| := abs_add _ _
      _ ≤ (L * r + 3 * η + 3 * q) + (L * r + 3 * η + 3 * q) :=
        add_le_add (by simpa only [abs_sub_comm] using hwx') hwy'
      _ = 2 * (L * r + 3 * η + 3 * q) := by ring
  calc
    |canonicalThreshold fhat x.1 - canonicalThreshold fhat y.1| ≤
        2 * (L * r + 3 * η + 3 * q) := hgap
    _ ≤ continuousForwardError L r η q := by
      unfold continuousForwardError
      have hLr : 0 ≤ L * r :=
        mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
      linarith [h.filter_error_nonneg, h.quantization_error_nonneg]
    _ ≤ continuousCanonicalComparisonError L r δ η q :=
      le_max_right _ _

/-- Every point of the canonical CW realization anchors at a component node
inside one additional common-error enlargement. -/
theorem ApproximationHypotheses.point_to_canonicalNode_band
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : (discreteReebRealization V G fhat).Carrier)
    (hz : a ≤ (discreteReebRealization V G fhat).height z ∧
      (discreteReebRealization V G fhat).height z ≤ b) :
    ∃ node : SliceNode G fhat (canonicalThreshold fhat),
      HeightBandJoined (discreteReebRealization V G fhat)
        (a - continuousCanonicalComparisonError L r δ η q)
        (b + continuousCanonicalComparisonError L r δ η q)
        z (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) node) := by
  revert hz
  refine Quotient.inductionOn z ?_
  intro raw hz
  cases raw with
  | inl node =>
      refine ⟨node, JoinedIn.refl ?_⟩
      change a - continuousCanonicalComparisonError L r δ η q ≤
          canonicalThreshold fhat node.1 ∧
        canonicalThreshold fhat node.1 ≤
          b + continuousCanonicalComparisonError L r δ η q
      have he := h.continuousCanonicalComparisonError_nonneg
      change a ≤ canonicalThreshold fhat node.1 ∧
        canonicalThreshold fhat node.1 ≤ b at hz
      constructor <;> linarith [hz.1, hz.2]
  | inr edgePoint =>
      rcases edgePoint with ⟨edge, s⟩
      refine ⟨edge.source, ?_⟩
      exact joinedIn_graphRealization_edgePoint_to_source
        (fun node : SliceNode G fhat (canonicalThreshold fhat) ↦
          canonicalThreshold fhat node.1)
        h.continuousCanonicalComparisonError_nonneg edge
        (h.canonicalAdjacentThreshold_gap_common edge.2) s hz

/-- Incidence-band coverage implies image-band reflection on all canonical
graph vertices. -/
theorem ApproximationHypotheses.nodeImageBandReflection_of_incidenceCoverageAt
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b e : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcoverage : CanonicalNodeIncidenceBandCoverageAt h e)
    {x y : SliceNode G fhat (canonicalThreshold fhat)} (hab : a ≤ b)
    (hxy : HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x))
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) y))) :
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - e) (b + e)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) y) := by
  rw [h.continuousDiscreteToContinuumMap_vertex,
    h.continuousDiscreteToContinuumMap_vertex] at hxy
  rcases hcoverage hab hxy with ⟨u, v, p, hu, hv, hp⟩
  have hpath := heightBandJoined_of_canonicalActiveIncidence_walk
    G fhat p hp
  rw [hu, hv] at hpath
  exact hpath

theorem ApproximationHypotheses.nodeImageBandReflection_of_incidenceCoverage
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcoverage : CanonicalNodeIncidenceBandCoverage h)
    {x y : SliceNode G fhat (canonicalThreshold fhat)} (hab : a ≤ b)
    (hxy : HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x))
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) y))) :
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - continuousCanonicalComparisonError L r δ η q)
      (b + continuousCanonicalComparisonError L r δ η q)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) y) :=
  h.nodeImageBandReflection_of_incidenceCoverageAt hcoverage hab hxy

/-- Node incidence coverage reflects bands between arbitrary points of the
discrete CW realization.  Interior endpoints are anchored to source nodes;
the four error units account for endpoint height control, anchoring, mapping
the anchor paths forward, and node-level reflection. -/
theorem ApproximationHypotheses.imageBandReflection_three_add_of_incidenceCoverageAt
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b e : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (he : 0 ≤ e) (hcoverage : CanonicalNodeIncidenceBandCoverageAt h e)
    {x y : (discreteReebRealization V G fhat).Carrier}
    (hab : a ≤ b)
    (hxy : HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap y)) :
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - (3 * continuousCanonicalComparisonError L r δ η q + e))
      (b + (3 * continuousCanonicalComparisonError L r δ η q + e)) x y := by
  let E := continuousCanonicalComparisonError L r δ η q
  have hE : 0 ≤ E := h.continuousCanonicalComparisonError_nonneg
  have hxClose :
      |(discreteReebRealization V G fhat).height x -
        (continuumReebGraph M f).height
          (h.continuousDiscreteToContinuumMap x)| ≤ E := by
    exact (h.continuousDiscreteToContinuumMap_height_close x).trans
      (by simpa only [E] using
        (le_max_right
          (approximationComparisonError L r δ η q + L * δ)
          (continuousForwardError L r η q)))
  have hyClose :
      |(discreteReebRealization V G fhat).height y -
        (continuumReebGraph M f).height
          (h.continuousDiscreteToContinuumMap y)| ≤ E := by
    exact (h.continuousDiscreteToContinuumMap_height_close y).trans
      (by simpa only [E] using
        (le_max_right
          (approximationComparisonError L r δ η q + L * δ)
          (continuousForwardError L r η q)))
  rw [abs_sub_le_iff] at hxClose hyClose
  have hxMem : a - E ≤ (discreteReebRealization V G fhat).height x ∧
      (discreteReebRealization V G fhat).height x ≤ b + E := by
    constructor <;>
      linarith [hxy.source_mem.1, hxy.source_mem.2, hxClose.1, hxClose.2]
  have hyMem : a - E ≤ (discreteReebRealization V G fhat).height y ∧
      (discreteReebRealization V G fhat).height y ≤ b + E := by
    constructor <;>
      linarith [hxy.target_mem.1, hxy.target_mem.2, hyClose.1, hyClose.2]
  rcases h.point_to_canonicalNode_band x hxMem with ⟨xn, hxAnchor⟩
  rcases h.point_to_canonicalNode_band y hyMem with ⟨yn, hyAnchor⟩
  have hxAnchor' : HeightBandJoined (discreteReebRealization V G fhat)
      (a - 2 * E) (b + 2 * E) x
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn) := by
    convert hxAnchor using 1 <;> simp only [E] <;> ring
  have hyAnchor' : HeightBandJoined (discreteReebRealization V G fhat)
      (a - 2 * E) (b + 2 * E) y
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn) := by
    convert hyAnchor using 1 <;> simp only [E] <;> ring
  have hForwardLe : continuousForwardError L r η q ≤ E := by
    simpa only [E] using
      (le_max_right
        (approximationComparisonError L r δ η q + L * δ)
        (continuousForwardError L r η q))
  have hxImageRaw := h.continuousDiscreteToContinuumMap_band hxAnchor'
  have hyImageRaw := h.continuousDiscreteToContinuumMap_band hyAnchor'
  have hxImageBase : HeightBandJoined (continuumReebGraph M f)
      ((a - 2 * E) - E) ((b + 2 * E) + E)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn)) :=
    HeightBandJoined.mono hxImageRaw (by linarith) (by linarith)
  have hyImageBase : HeightBandJoined (continuumReebGraph M f)
      ((a - 2 * E) - E) ((b + 2 * E) + E)
      (h.continuousDiscreteToContinuumMap y)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn)) :=
    HeightBandJoined.mono hyImageRaw (by linarith) (by linarith)
  have hxImage : HeightBandJoined (continuumReebGraph M f)
      (a - 3 * E) (b + 3 * E)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn)) := by
    convert hxImageBase using 1 <;> simp only [E] <;> ring
  have hyImage : HeightBandJoined (continuumReebGraph M f)
      (a - 3 * E) (b + 3 * E)
      (h.continuousDiscreteToContinuumMap y)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn)) := by
    convert hyImageBase using 1 <;> simp only [E] <;> ring
  have hmiddle : HeightBandJoined (continuumReebGraph M f)
      (a - 3 * E) (b + 3 * E)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap y) :=
    HeightBandJoined.mono hxy (by linarith) (by linarith)
  have hnodesImage : HeightBandJoined (continuumReebGraph M f)
      (a - 3 * E) (b + 3 * E)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn))
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn)) :=
    hxImage.symm.trans (hmiddle.trans hyImage)
  have hnodesBase := h.nodeImageBandReflection_of_incidenceCoverageAt hcoverage
    (show a - 3 * E ≤ b + 3 * E by linarith) hnodesImage
  have hnodes : HeightBandJoined (discreteReebRealization V G fhat)
      (a - (3 * E + e)) (b + (3 * E + e))
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn) := by
    convert hnodesBase using 1 <;> simp only [E] <;> ring
  have hxAnchorWide := HeightBandJoined.mono hxAnchor'
    (show a - (3 * E + e) ≤ a - 2 * E by linarith)
    (show b + 2 * E ≤ b + (3 * E + e) by linarith)
  have hyAnchorWide := HeightBandJoined.mono hyAnchor'
    (show a - (3 * E + e) ≤ a - 2 * E by linarith)
    (show b + 2 * E ≤ b + (3 * E + e) by linarith)
  change HeightBandJoined (discreteReebRealization V G fhat)
    (a - (3 * E + e)) (b + (3 * E + e)) x y
  exact hxAnchorWide.trans (hnodes.trans hyAnchorWide.symm)

/-- The one-error incidence interface gives the original four-error arbitrary
CW reflection estimate. -/
theorem ApproximationHypotheses.imageBandReflection_four_of_incidenceCoverage
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcoverage : CanonicalNodeIncidenceBandCoverage h)
    {x y : (discreteReebRealization V G fhat).Carrier}
    (hab : a ≤ b)
    (hxy : HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap y)) :
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - 4 * continuousCanonicalComparisonError L r δ η q)
      (b + 4 * continuousCanonicalComparisonError L r δ η q) x y := by
  have hreflect := h.imageBandReflection_three_add_of_incidenceCoverageAt
    h.continuousCanonicalComparisonError_nonneg hcoverage hab hxy
  convert hreflect using 1 <;> ring

end ReebGraph
