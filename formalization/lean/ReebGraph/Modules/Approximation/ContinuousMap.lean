import ReebGraph.Modules.Approximation.DiscreteBounds

/-!
# Continuous forward map

Upgrading the forward comparison map to a genuinely continuous map of
filtered spaces.

Main results: `ApproximationHypotheses.continuousDiscreteToContinuumMap`
with `continuous_continuousDiscreteToContinuumMap`,
`_height_close`, and `_band`.

Supporting: `canonicalNodeContinuumMap` and its controlled-adjacency
lemmas, which supply the height-controlled edge paths the realization
machinery needs.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Chosen support representative of a canonical slice node. -/
noncomputable def canonicalNodeSupportWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (fhat : V → ℝ)
    (x : SliceNode G fhat (canonicalThreshold fhat)) : V :=
  discreteRawSupportWitness G fhat (canonicalThreshold fhat) (.inl x)

theorem canonicalNodeSupportWitness_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (fhat : V → ℝ)
    (x : SliceNode G fhat (canonicalThreshold fhat)) :
    canonicalNodeSupportWitness G fhat x ∈
      componentSupport G fhat (canonicalThreshold fhat x.1) x.2 :=
  discreteRawSupportWitness_vertex_mem G fhat (canonicalThreshold fhat) x

/-- Image of a canonical slice node in the continuum Reeb quotient. -/
noncomputable def ApproximationHypotheses.canonicalNodeContinuumMap
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (_h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (x : SliceNode G fhat (canonicalThreshold fhat)) :
    (continuumReebGraph M f).Carrier :=
  continuumReebQuotientMap f
    (sample (canonicalNodeSupportWitness G fhat x))

/-- Adjacent canonical nodes have path-connected images in the continuum Reeb
quotient.  The path is built through their shared support witness. -/
theorem ApproximationHypotheses.canonicalNodeContinuumMap_adj_joined
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : SliceNode G fhat (canonicalThreshold fhat)}
    (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) :
    Nonempty (Path (h.canonicalNodeContinuumMap x)
      (h.canonicalNodeContinuumMap y)) := by
  change DiscreteReebAdj G fhat (canonicalThreshold fhat) x y at hxy
  rcases hxy.2 with ⟨w, hwx, hwy⟩
  have hxw := h.support_component_no_merge x.2
    (canonicalNodeSupportWitness_mem G fhat x) hwx
  have hwy' := h.support_component_no_merge y.2 hwy
    (canonicalNodeSupportWitness_mem G fhat y)
  exact ⟨(hxw.somePath.trans hwy'.somePath).map
    (continuous_continuumReebQuotientMap f)⟩

/-- Uniform height budget for the continuous support map on realization
edges. -/
def continuousForwardError (L r η q : ℝ) : ℝ :=
  4 * L * r + 9 * η + 9 * q

/-- The path between adjacent canonical-node images can be chosen uniformly
close to the linearly interpolated realization height. -/
theorem ApproximationHypotheses.canonicalNodeContinuumMap_adj_controlled
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : SliceNode G fhat (canonicalThreshold fhat)}
    (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) :
    ∃ γ : Path (h.canonicalNodeContinuumMap x)
        (h.canonicalNodeContinuumMap y),
      ∀ s : GraphUnitInterval,
        |(1 - s.1) * canonicalThreshold fhat x.1 +
          s.1 * canonicalThreshold fhat y.1 -
          (continuumReebGraph M f).height (γ s)| ≤
        continuousForwardError L r η q := by
  change DiscreteReebAdj G fhat (canonicalThreshold fhat) x y at hxy
  rcases hxy.2 with ⟨w, hwx, hwy⟩
  let ux := canonicalNodeSupportWitness G fhat x
  let uy := canonicalNodeSupportWitness G fhat y
  let tx := canonicalThreshold fhat x.1
  let ty := canonicalThreshold fhat y.1
  let B := L * r + 3 * η + 3 * q
  let A := B + L * r
  have hxw := h.support_component_no_merge x.2
    (canonicalNodeSupportWitness_mem G fhat x) hwx
  have hwy' := h.support_component_no_merge y.2 hwy
    (canonicalNodeSupportWitness_mem G fhat y)
  have hwxB := h.support_component_sound x.2 hwx
  have hwyB := h.support_component_sound y.2 hwy
  change |f (sample w) - tx| ≤ B at hwxB
  change |f (sample w) - ty| ≤ B at hwyB
  have hgap : |tx - ty| ≤ 2 * B := by
    calc
      |tx - ty| = |(tx - f (sample w)) + (f (sample w) - ty)| := by ring_nf
      _ ≤ |tx - f (sample w)| + |f (sample w) - ty| := abs_add _ _
      _ ≤ B + B := add_le_add (by simpa only [abs_sub_comm] using hwxB) hwyB
      _ = 2 * B := by ring
  let γM := hxw.somePath.trans hwy'.somePath
  let γ := γM.map (continuous_continuumReebQuotientMap f)
  refine ⟨γ, ?_⟩
  intro s
  change |(1 - s.1) * tx + s.1 * ty - f (γM s)| ≤
    continuousForwardError L r η q
  have hleft : |(1 - s.1) * tx + s.1 * ty - tx| ≤ |tx - ty| := by
    apply abs_affine_sub_le s.2.1 s.2.2
    · simp
    · simp only [abs_sub_comm, le_refl]
  have hright : |(1 - s.1) * tx + s.1 * ty - ty| ≤ |tx - ty| := by
    apply abs_affine_sub_le s.2.1 s.2.2
    · exact le_rfl
    · simp
  have hsRange : γM s ∈ Set.range hxw.somePath ∪ Set.range hwy'.somePath := by
    rw [← hxw.somePath.trans_range hwy'.somePath]
    exact ⟨s, rfl⟩
  rcases hsRange with hsx | hsy
  · rcases hsx with ⟨t, ht⟩
    have htBand := hxw.somePath_mem t
    change |f (hxw.somePath t) - tx| ≤ A at htBand
    have hcenter : |tx - f (γM s)| ≤ A := by
      rw [← ht]
      simpa only [abs_sub_comm] using htBand
    calc
      |(1 - s.1) * tx + s.1 * ty - f (γM s)| =
          |((1 - s.1) * tx + s.1 * ty - tx) + (tx - f (γM s))| := by
        ring_nf
      _ ≤ |(1 - s.1) * tx + s.1 * ty - tx| + |tx - f (γM s)| :=
        abs_add _ _
      _ ≤ |tx - ty| + A := add_le_add hleft hcenter
      _ ≤ 2 * B + A := add_le_add_right hgap A
      _ = continuousForwardError L r η q := by
        unfold continuousForwardError A B
        ring
  · rcases hsy with ⟨t, ht⟩
    have htBand := hwy'.somePath_mem t
    change |f (hwy'.somePath t) - ty| ≤ A at htBand
    have hcenter : |ty - f (γM s)| ≤ A := by
      rw [← ht]
      simpa only [abs_sub_comm] using htBand
    calc
      |(1 - s.1) * tx + s.1 * ty - f (γM s)| =
          |((1 - s.1) * tx + s.1 * ty - ty) + (ty - f (γM s))| := by
        ring_nf
      _ ≤ |(1 - s.1) * tx + s.1 * ty - ty| + |ty - f (γM s)| :=
        abs_add _ _
      _ ≤ |tx - ty| + A := add_le_add hright hcenter
      _ ≤ 2 * B + A := add_le_add_right hgap A
      _ = continuousForwardError L r η q := by
        unfold continuousForwardError A B
        ring

/-- Controlled adjacent-node paths packaged for the coherent realization-map
constructor. -/
theorem ApproximationHypotheses.canonicalNodeContinuumMap_adj_controlledPath
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : SliceNode G fhat (canonicalThreshold fhat)}
    (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) :
    Nonempty (HeightControlledAdjacentPath
      (fun z : SliceNode G fhat (canonicalThreshold fhat) ↦
        canonicalThreshold fhat z.1)
      (continuumReebGraph M f) (continuousForwardError L r η q)
      h.canonicalNodeContinuumMap x y) := by
  rcases h.canonicalNodeContinuumMap_adj_controlled hxy with ⟨γ, hγ⟩
  exact ⟨⟨γ, hγ⟩⟩

/-- The coherent continuous support map, now retaining its uniform filtered
height estimate on the entire graph realization. -/
noncomputable def ApproximationHypotheses.filteredContinuousDiscreteToContinuumData
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    FilteredGraphRealizationMapData (canonicalDiscreteReebGraph G fhat)
      (fun z : SliceNode G fhat (canonicalThreshold fhat) ↦
        canonicalThreshold fhat z.1)
      (continuumReebGraph M f) (continuousForwardError L r η q) := by
  letI : LinearOrder (SliceNode G fhat (canonicalThreshold fhat)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let hedge := fun {x y : SliceNode G fhat (canonicalThreshold fhat)}
      (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) ↦
    h.canonicalNodeContinuumMap_adj_controlledPath hxy
  let graphData : GraphRealizationMapData (canonicalDiscreteReebGraph G fhat)
      (continuumReebGraph M f).Carrier :=
    { vertexMap := h.canonicalNodeContinuumMap
      edgePath := coherentHeightControlledEdgePath
        h.canonicalNodeContinuumMap hedge
      reverse_compatible := coherentHeightControlledEdgePath_reverse
        h.canonicalNodeContinuumMap hedge }
  refine
    { toGraphRealizationMapData := graphData
      vertex_height_close := ?_
      edge_height_close := ?_ }
  · intro x
    have hs := h.support_component_sound x.2
      (canonicalNodeSupportWitness_mem G fhat x)
    change |f (sample (canonicalNodeSupportWitness G fhat x)) -
      canonicalThreshold fhat x.1| ≤ L * r + 3 * η + 3 * q at hs
    change |canonicalThreshold fhat x.1 -
      f (sample (canonicalNodeSupportWitness G fhat x))| ≤
      continuousForwardError L r η q
    have hLr : 0 ≤ L * r :=
      mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
    have hbudget : L * r + 3 * η + 3 * q ≤
      continuousForwardError L r η q := by
      unfold continuousForwardError
      linarith [h.filter_error_nonneg, h.quantization_error_nonneg]
    have hs' : |canonicalThreshold fhat x.1 -
        f (sample (canonicalNodeSupportWitness G fhat x))| ≤
        L * r + 3 * η + 3 * q := by
      simpa only [abs_sub_comm] using hs
    exact hs'.trans hbudget
  · intro edge s
    exact coherentHeightControlledEdgePath_height_close
      h.canonicalNodeContinuumMap hedge edge s

/-- Continuous support map from the canonical discrete graph realization to
the continuum Reeb quotient. -/
noncomputable def ApproximationHypotheses.continuousDiscreteToContinuumData
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    GraphRealizationMapData (canonicalDiscreteReebGraph G fhat)
      (ContinuumReebQuotient M f) :=
  h.filteredContinuousDiscreteToContinuumData.toGraphRealizationMapData

noncomputable def ApproximationHypotheses.continuousDiscreteToContinuumMap
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    (discreteReebRealization V G fhat).Carrier →
      (continuumReebGraph M f).Carrier :=
  h.continuousDiscreteToContinuumData.realizationMap

@[simp] theorem ApproximationHypotheses.continuousDiscreteToContinuumMap_vertex
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (x : SliceNode G fhat (canonicalThreshold fhat)) :
    h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x) =
      h.canonicalNodeContinuumMap x :=
  rfl

theorem ApproximationHypotheses.continuous_continuousDiscreteToContinuumMap
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    Continuous h.continuousDiscreteToContinuumMap :=
  h.continuousDiscreteToContinuumData.continuous_realizationMap

/-- Global height control for the continuous support map. -/
theorem ApproximationHypotheses.continuousDiscreteToContinuumMap_height_close
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : (discreteReebRealization V G fhat).Carrier) :
    |(discreteReebRealization V G fhat).height z -
      (continuumReebGraph M f).height
        (h.continuousDiscreteToContinuumMap z)| ≤
      continuousForwardError L r η q :=
  h.filteredContinuousDiscreteToContinuumData.height_close z

theorem ApproximationHypotheses.continuousForwardError_nonneg
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ continuousForwardError L r η q := by
  unfold continuousForwardError
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  linarith [h.filter_error_nonneg, h.quantization_error_nonneg]

/-- Forward scalar-band preservation is a theorem of the support-induced CW
construction, not an additional compatibility assumption. -/
theorem ApproximationHypotheses.continuousDiscreteToContinuumMap_band
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x x' : (discreteReebRealization V G fhat).Carrier}
    (hxx' : HeightBandJoined (discreteReebRealization V G fhat) a b x x') :
    HeightBandJoined (continuumReebGraph M f)
      (a - continuousForwardError L r η q)
      (b + continuousForwardError L r η q)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap x') :=
  hxx'.map_of_continuous_height_close
    h.continuous_continuousDiscreteToContinuumMap
    h.continuousDiscreteToContinuumMap_height_close

/-- Common error budget for the continuous forward support map and the
canonical reverse crossing map. -/
def continuousCanonicalComparisonError (L r δ η q : ℝ) : ℝ :=
  max (approximationComparisonError L r δ η q + L * δ)
    (continuousForwardError L r η q)

theorem ApproximationHypotheses.continuousCanonicalComparisonError_nonneg
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ continuousCanonicalComparisonError L r δ η q := by
  have hLδ : 0 ≤ L * δ :=
    mul_nonneg h.lipschitz_constant_nonneg h.sampling_scale_nonneg
  exact (add_nonneg h.comparison_error_nonneg hLδ).trans
    (le_max_left _ (continuousForwardError L r η q))

end ReebGraph
