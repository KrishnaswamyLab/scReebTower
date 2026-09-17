import ReebGraph.Modules.Basic
import ReebGraph.Modules.Resolution
import ReebGraph.Modules.Sampling
import ReebGraph.Modules.TameLevelSet

/-!
# Approximation hypotheses and comparison maps

`ApproximationHypotheses`: the bundle of assumptions relating a sampled
graph to the continuum, and the two comparison maps built from it.

Main results: `ApproximationHypotheses.of_proximity_sandwich` and
`.of_true_crossing_pairs` (how the bundle is actually obtained),
`.discreteToContinuumMap_height_close`, and
`.continuumToDiscreteMap_height_close`.

Supporting: the field-level consequences (`graph_sound`,
`crossing_coverage`, `support_complete`, the nonnegativity lemmas) and the
canonical point-witness construction.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Abstract assumptions connecting a sampled graph to a compact metric space.
The individual fields will be strengthened as the component-correspondence
proof is developed. -/
structure ApproximationHypotheses
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (sample : V → M)
    (f : M → ℝ) (fbase fhat : V → ℝ)
    (L r δ η q : ℝ) : Prop where
  lipschitz_constant_nonneg : 0 ≤ L
  edge_scale_nonneg : 0 ≤ r
  sampling_scale_nonneg : 0 ≤ δ
  filter_error_nonneg : 0 ≤ η
  quantization_error_nonneg : 0 ≤ q
  lipschitz : ∀ x y, |f x - f y| ≤ L * dist x y
  filter_close : ∀ v, |fbase v - f (sample v)| ≤ η
  quantization_close : ∀ v, |fhat v - fbase v| ≤ q
  sample_dense : ∀ x : M, ∃ v : V, dist x (sample v) ≤ δ
  edge_path_sound : EdgePathSound M V G sample r
  graph_complete : GraphComplete M V G sample r δ
  proximity_crossing_pair_adequate : ∃ ρ : ℝ,
    ContainsProximityGraph M V G sample ρ ∧
    ProximityCrossingPairAdequate M V sample f fhat ρ δ
      (L * (r + δ) + η + q)
  tame_filter : TameLevelSetFunction M f

/-- Construct the estimator's approximation interface from an ordinary
two-sided proximity-graph sandwich.  In particular, graph completeness and
edge realization are conclusions rather than graph-specific assumptions. -/
theorem ApproximationHypotheses.of_proximity_sandwich
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ}
    {L r δ η q ρ : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hq : 0 ≤ q)
    (hlipschitz : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hfilter : ∀ v, |fbase v - f (sample v)| ≤ η)
    (hquantization : ∀ v, |fhat v - fbase v| ≤ q)
    (hdense : ∀ x : M, ∃ v : V, dist x (sample v) ≤ δ)
    (hlower : ContainsProximityGraph M V G sample ρ)
    (hupper : G ≤ proximityGraph M V sample r)
    (hpairs : ProximityCrossingPairAdequate M V sample f fhat ρ δ
      (L * (r + δ) + η + q))
    (hshort : ShortPathSound M r)
    (htame : TameLevelSetFunction M f) :
    ApproximationHypotheses M V G sample f fbase fhat L r δ η q := by
  have hgeometry := graph_geometry_of_proximity_sandwich
    hr hdense hlower hupper hpairs.1 hshort
  exact
    { lipschitz_constant_nonneg := hL
      edge_scale_nonneg := hr
      sampling_scale_nonneg := hδ
      filter_error_nonneg := hη
      quantization_error_nonneg := hq
      lipschitz := hlipschitz
      filter_close := hfilter
      quantization_close := hquantization
      sample_dense := hdense
      edge_path_sound := hgeometry.1
      graph_complete := hgeometry.2
      proximity_crossing_pair_adequate := ⟨ρ, hlower, hpairs⟩
      tame_filter := htame }

/-- Publication-facing constructor from continuum crossing pairs and a graph
sandwich.  The fill distance `σ`, continuum crossing radius `a`, and final
witness radius `δ` remain separate, so no finite-sample scale is silently
identified with another. -/
theorem ApproximationHypotheses.of_true_crossing_pairs
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ}
    {L r δ η q σ ρ a m : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hη : 0 ≤ η) (hq : 0 ≤ q)
    (hlipschitz : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hfilter : ∀ v, |fbase v - f (sample v)| ≤ η)
    (hquantization : ∀ v, |fhat v - fbase v| ≤ q)
    (hsample : SampleDense M V sample σ)
    (hσδ : σ ≤ δ)
    (hlower : ContainsProximityGraph M V G sample ρ)
    (hupper : G ≤ proximityGraph M V sample r)
    (hmargin : L * σ + (η + q) ≤ m)
    (hprox : 2 * (a + σ) ≤ ρ)
    (hwitness : a + σ ≤ δ)
    (hgap : 2 * δ < ρ)
    (htrue : CommonThresholdTrueCrossingPairDensity M f a m
      (L * (r + δ) + η + q))
    (hshort : ShortPathSound M r)
    (htame : TameLevelSetFunction M f) :
    ApproximationHypotheses M V G sample f fbase fhat L r δ η q := by
  have herr : ∀ v, |fhat v - f (sample v)| ≤ η + q := by
    intro v
    calc
      |fhat v - f (sample v)| =
          |(fhat v - fbase v) + (fbase v - f (sample v))| := by ring_nf
      _ ≤ |fhat v - fbase v| + |fbase v - f (sample v)| := abs_add _ _
      _ ≤ q + η := add_le_add (hquantization v) (hfilter v)
      _ = η + q := add_comm _ _
  have hdense : ∀ x : M, ∃ v : V, dist x (sample v) ≤ δ := by
    intro x
    rcases hsample x with ⟨v, hv⟩
    exact ⟨v, hv.trans hσδ⟩
  have hpairs : ProximityCrossingPairAdequate M V sample f fhat ρ δ
      (L * (r + δ) + η + q) :=
    ProximityCrossingPairAdequate.of_true hL hlipschitz hsample herr
      hmargin hprox hwitness hgap htrue
  exact ApproximationHypotheses.of_proximity_sandwich
    hL hr hδ hη hq hlipschitz hfilter hquantization hdense
    hlower hupper hpairs hshort htame

/-- Common scalar budget for the two comparison maps: one observed edge
oscillation plus the nearby-threshold coverage slack. -/
def approximationComparisonError (L r δ η q : ℝ) : ℝ :=
  (L * r + 2 * η + 2 * q) + (L * (r + δ) + η + q)

/-- Data selecting a canonical discrete slice representative for a continuum
point. -/
structure CanonicalPointWitness
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (sample : V → M)
    (f : M → ℝ) (fhat : V → ℝ) (δ e : ℝ) (x : M) where
  index : Fin (canonicalMidpoints fhat).length
  vertex : V
  active : IsActiveVertex G fhat (canonicalThreshold fhat index) vertex
  spatial_close : dist (sample vertex) x ≤ δ
  height_close : |canonicalThreshold fhat index - f x| ≤ e

theorem ApproximationHypotheses.graph_sound
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    GraphSound M V G sample r :=
  h.edge_path_sound.graphSound

/-- Crossing coverage transfers from the canonical proximity graph through the
lower graph-sandwich inclusion. -/
theorem ApproximationHypotheses.crossing_coverage
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    CrossingCoverage M V G sample f fhat δ
      (L * (r + δ) + η + q) := by
  rcases h.proximity_crossing_pair_adequate with ⟨ρ, hclose, hpairs⟩
  exact hpairs.to_activeDensityAdequate.to_chainWitnessAdequate.crossingCoverage.mono_graph hclose

/-- Completeness for the algorithmic graph follows from completeness of the
canonical proximity graph and the lower graph-sandwich inclusion. -/
theorem ApproximationHypotheses.support_complete
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    SupportComplete M V G sample f fhat δ
      (L * (r + δ) + η + q) := by
  rcases h.proximity_crossing_pair_adequate with ⟨ρ, hclose, hpairs⟩
  exact hpairs.to_activeDensityAdequate.to_chainWitnessAdequate.to_proximitySupportComplete.to_graph
    hclose

theorem ApproximationHypotheses.continuum_height_continuous
    {M : Type} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    Continuous (continuumReebGraph M f).height :=
  continuous_continuumReebGraph_height h.tame_filter.continuous

theorem ApproximationHypotheses.error_scale_nonneg
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ L * r + δ + η + q := by
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  linarith [h.sampling_scale_nonneg, h.filter_error_nonneg,
    h.quantization_error_nonneg]

theorem ApproximationHypotheses.crossing_slack_nonneg
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ L * (r + δ) + η + q := by
  have hrδ : 0 ≤ r + δ :=
    add_nonneg h.edge_scale_nonneg h.sampling_scale_nonneg
  have hLrδ : 0 ≤ L * (r + δ) :=
    mul_nonneg h.lipschitz_constant_nonneg hrδ
  linarith [h.filter_error_nonneg, h.quantization_error_nonneg]

theorem ApproximationHypotheses.total_filter_error
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (v : V) : |fhat v - f (sample v)| ≤ η + q := by
  calc
    |fhat v - f (sample v)| =
        |(fhat v - fbase v) + (fbase v - f (sample v))| := by ring_nf
    _ ≤ |fhat v - fbase v| + |fbase v - f (sample v)| := abs_add _ _
    _ ≤ q + η := add_le_add (h.quantization_close v) (h.filter_close v)
    _ = η + q := add_comm q η

/-- Observed scalar oscillation on every neighborhood edge. -/
theorem ApproximationHypotheses.observed_edge_oscillation
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {u v : V} (huv : G.Adj u v) :
    |fhat u - fhat v| ≤ L * r + 2 * η + 2 * q := by
  exact sampled_quantized_edge_oscillation_bound G sample f fbase fhat
    h.lipschitz_constant_nonneg h.lipschitz h.graph_sound h.filter_close
      h.quantization_close huv

/-- Every active canonical slice height is close to the observed value of
each active support vertex. -/
theorem ApproximationHypotheses.canonicalActive_threshold_close_observed
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {i : Fin (canonicalMidpoints fhat).length} {u : V}
    (hu : IsActiveVertex G fhat (canonicalThreshold fhat i) u) :
    |canonicalThreshold fhat i - fhat u| ≤ L * r + 2 * η + 2 * q := by
  rcases hu with ⟨v, huv, hcross⟩
  exact (abs_threshold_sub_endpoint_le_of_crosses fhat hcross).trans
    (h.observed_edge_oscillation huv)

/-- An active arbitrary threshold transports to a canonical midpoint without
moving farther than the observed oscillation of its crossing edge.  The same
ambient support vertex remains active after transport. -/
theorem ApproximationHypotheses.active_has_close_canonicalThreshold
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {u : V} (hu : IsActiveVertex G fhat t u) :
    ∃ i : Fin (canonicalMidpoints fhat).length,
      ThresholdEquivalent fhat t (canonicalThreshold fhat i) ∧
      IsActiveVertex G fhat (canonicalThreshold fhat i) u ∧
      |canonicalThreshold fhat i - t| ≤ L * r + 2 * η + 2 * q := by
  rcases hu.exists_equivalent_canonicalThreshold G fhat with ⟨i, hi⟩
  rcases hu with ⟨v, huv, hcross⟩
  have hcross' : Crosses fhat (canonicalThreshold fhat i) u v :=
    (crosses_iff_of_thresholdEquivalent fhat hi u v).mp hcross
  refine ⟨i, hi, ⟨v, huv, hcross'⟩, ?_⟩
  exact (abs_sub_le_edge_oscillation_of_crosses fhat hcross' hcross).trans
    (h.observed_edge_oscillation huv)

/-- Crossing coverage and canonical threshold transport select a canonical
discrete representative for every continuum point. -/
theorem ApproximationHypotheses.exists_canonicalPointWitness
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (x : M) : Nonempty (CanonicalPointWitness M V G sample f fhat δ
      (approximationComparisonError L r δ η q) x) := by
  rcases h.crossing_coverage x with ⟨t, u, hu, hux, ht⟩
  rcases h.active_has_close_canonicalThreshold hu with ⟨i, _, hui, hit⟩
  refine ⟨CanonicalPointWitness.mk i u hui hux ?_⟩
  calc
    |canonicalThreshold fhat i - f x| =
        |(canonicalThreshold fhat i - t) + (t - f x)| := by ring_nf
    _ ≤ |canonicalThreshold fhat i - t| + |t - f x| := abs_add _ _
    _ ≤ (L * r + 2 * η + 2 * q) + (L * (r + δ) + η + q) :=
      add_le_add hit ht
    _ = approximationComparisonError L r δ η q := rfl

/-- A fixed classical choice of the canonical witness. -/
noncomputable def ApproximationHypotheses.canonicalPointWitness
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (x : M) : CanonicalPointWitness M V G sample f fhat δ
      (approximationComparisonError L r δ η q) x :=
  Classical.choice (h.exists_canonicalPointWitness x)

/-- The local soundness direction is already forced by Lipschitz continuity,
edge locality, and uniform filter error; it does not require the deeper graph
completeness assumption. -/
theorem ApproximationHypotheses.support_component_sound
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (c : SupportComponent G fhat t) :
    componentSupport G fhat t c ⊆
      {v | |f (sample v) - t| ≤ L * r + 3 * η + 3 * q} :=
  sampled_quantized_component_mem_continuum_band G sample f fbase fhat
    h.lipschitz_constant_nonneg h.lipschitz h.graph_sound h.filter_close
      h.quantization_close c

/-- The support witness selected at any raw realization point has true height
close to that point's linearly interpolated discrete height. -/
theorem ApproximationHypotheses.discreteRawSupportWitness_height_close
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : GraphRealizationRaw (canonicalDiscreteReebGraph G fhat)) :
    |graphRealizationRawHeight
        (fun x => canonicalThreshold fhat x.1) z -
      f (sample (discreteRawSupportWitness G fhat
        (canonicalThreshold fhat) z))| ≤
      L * r + 3 * η + 3 * q := by
  cases z with
  | inl x =>
      have hx := h.support_component_sound x.2
        (discreteRawSupportWitness_vertex_mem G fhat
          (canonicalThreshold fhat) x)
      change |f (sample (discreteRawSupportWitness G fhat
        (canonicalThreshold fhat) (.inl x))) - canonicalThreshold fhat x.1| ≤ _ at hx
      simpa only [graphRealizationRawHeight, abs_sub_comm] using hx
  | inr p =>
      rcases p with ⟨e, s⟩
      apply abs_affine_sub_le s.2.1 s.2.2
      · have hx := h.support_component_sound e.source.2
          (discreteRawSupportWitness_edge_source_mem G fhat
            (canonicalThreshold fhat) e s)
        change |f (sample (discreteRawSupportWitness G fhat
          (canonicalThreshold fhat) (.inr (e, s)))) -
          canonicalThreshold fhat e.source.1| ≤ _ at hx
        simpa only [abs_sub_comm] using hx
      · have hx := h.support_component_sound e.target.2
          (discreteRawSupportWitness_edge_target_mem G fhat
            (canonicalThreshold fhat) e s)
        change |f (sample (discreteRawSupportWitness G fhat
          (canonicalThreshold fhat) (.inr (e, s)))) -
          canonicalThreshold fhat e.target.1| ≤ _ at hx
        simpa only [abs_sub_comm] using hx

/-- The canonical map from the discrete realization to the continuum Reeb
quotient, obtained from the support witness of a chosen raw representative. -/
noncomputable def ApproximationHypotheses.discreteToContinuumMap
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (_h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    (discreteReebRealization V G fhat).Carrier →
      (continuumReebGraph M f).Carrier := fun z =>
  continuumReebQuotientMap f (sample
    (discreteRawSupportWitness G fhat (canonicalThreshold fhat)
      (Quotient.out z)))

/-- The forward comparison map has the local support-soundness height error. -/
theorem ApproximationHypotheses.discreteToContinuumMap_height_close
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : (discreteReebRealization V G fhat).Carrier) :
    |(discreteReebRealization V G fhat).height z -
      (continuumReebGraph M f).height (h.discreteToContinuumMap z)| ≤
      L * r + 3 * η + 3 * q := by
  let raw : GraphRealizationRaw (canonicalDiscreteReebGraph G fhat) :=
    Quotient.out z
  have hraw : graphRealizationQuotientMap
      (canonicalDiscreteReebGraph G fhat) raw = z := Quotient.out_eq z
  change |graphRealizationHeight (canonicalDiscreteReebGraph G fhat)
      (fun x => canonicalThreshold fhat x.1) z -
    f (sample (discreteRawSupportWitness G fhat
      (canonicalThreshold fhat) raw))| ≤ _
  rw [← hraw]
  exact h.discreteRawSupportWitness_height_close raw

/-- The reverse comparison map sends a continuum Reeb point to the graph
realization vertex selected by its canonical crossing witness. -/
noncomputable def ApproximationHypotheses.continuumToDiscreteMap
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    (continuumReebGraph M f).Carrier →
      (discreteReebRealization V G fhat).Carrier := fun z =>
  let x : M := Quotient.out z
  let w := h.canonicalPointWitness x
  graphRealizationVertex (canonicalDiscreteReebGraph G fhat)
    ⟨w.index, componentOfActive G fhat (canonicalThreshold fhat w.index)
      ⟨w.vertex, w.active⟩⟩

/-- The reverse comparison map has the combined threshold-transport and
crossing-coverage height error. -/
theorem ApproximationHypotheses.continuumToDiscreteMap_height_close
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : (continuumReebGraph M f).Carrier) :
    |(discreteReebRealization V G fhat).height
        (h.continuumToDiscreteMap z) -
      (continuumReebGraph M f).height z| ≤
      approximationComparisonError L r δ η q := by
  let x : M := Quotient.out z
  let w := h.canonicalPointWitness x
  have hx : continuumReebQuotientMap f x = z := Quotient.out_eq z
  have hheight : (continuumReebGraph M f).height z = f x := by
    rw [← hx]
    rfl
  rw [hheight]
  change |canonicalThreshold fhat w.index - f x| ≤ _
  exact w.height_close

theorem ApproximationHypotheses.comparison_error_nonneg
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ approximationComparisonError L r δ η q := by
  unfold approximationComparisonError
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  have hLrδ : 0 ≤ L * (r + δ) :=
    mul_nonneg h.lipschitz_constant_nonneg
      (add_nonneg h.edge_scale_nonneg h.sampling_scale_nonneg)
  linarith [h.filter_error_nonneg, h.quantization_error_nonneg]

/-- The forward map also satisfies the common two-map error budget. -/
theorem ApproximationHypotheses.discreteToContinuumMap_height_close_common
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : (discreteReebRealization V G fhat).Carrier) :
    |(discreteReebRealization V G fhat).height z -
      (continuumReebGraph M f).height (h.discreteToContinuumMap z)| ≤
      approximationComparisonError L r δ η q := by
  apply (h.discreteToContinuumMap_height_close z).trans
  unfold approximationComparisonError
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  have hLδ : 0 ≤ L * δ :=
    mul_nonneg h.lipschitz_constant_nonneg h.sampling_scale_nonneg
  linarith

end ReebGraph
