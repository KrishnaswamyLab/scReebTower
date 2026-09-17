import ReebGraph.Modules.Main.Consistency

/-!
# MAIN -- publication-facing package

MAIN THEOREM (publication-facing package).

`QuadraticGraphSandwichConsistencyHypotheses` bundles every hypothesis of
the graph-agnostic consistency theorem into one structure, and
`QuadraticGraphSandwichConsistencyHypotheses.reeb_consistency` is the
flagship result of the whole development.

It is a direct repackaging of
`reeb_consistency_of_quadratic_level_crossings_and_graph_sandwich` from
`ReebGraph.Modules.Main.Consistency`.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-! ### Publication-facing consistency package -/

/-- All mathematical hypotheses of the graph-agnostic consistency theorem in
one object.  The graph is required only to lie between proximity graphs; it is
not assumed to be kNN.  Pairwise-distinct observed values replace the internal
edge-nonflat condition and introduce no numerical hyperparameter. -/
structure QuadraticGraphSandwichConsistencyHypotheses
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    [LocPathConnectedSpace M]
    (f : M → ℝ) (L cShift cMargin a₀ : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q σ ρ a : ℕ → ℝ) : Prop where
  lipschitz_constant_nonneg : 0 ≤ L
  graph_radius_nonneg : ∀ n, 0 ≤ r n
  witness_radius_nonneg : ∀ n, 0 ≤ δ n
  filter_error_nonneg : ∀ n, 0 ≤ η n
  quantization_error_nonneg : ∀ n, 0 ≤ q n
  lipschitz : ∀ x y, |f x - f y| ≤ L * dist x y
  filter_error : ∀ n v, |fbase n v - f (sample n v)| ≤ η n
  quantization_error : ∀ n v, |fhat n v - fbase n v| ≤ q n
  sample_dense : ∀ n, SampleDense M (V n) (sample n) (σ n)
  sample_within_witness : ∀ n, σ n ≤ δ n
  graph_lower_sandwich : ∀ n,
    ContainsProximityGraph M (V n) (G n) (sample n) (ρ n)
  graph_upper_sandwich : ∀ n,
    G n ≤ proximityGraph M (V n) (sample n) (r n)
  crossing_radius_pos : ∀ n, 0 < a n
  crossing_radius_bound : ∀ n, a n ≤ a₀
  quadratic_crossing : QuadraticLevelCrossingCondition M f
    cShift cMargin a₀
  error_within_crossing_margin : ∀ n,
    L * σ n + (η n + q n) ≤ cMargin * (a n) ^ 2
  comparison_covers_level_shift : ∀ n,
    cShift * (a n) ^ 2 ≤ L * (r n + δ n) + η n + q n
  crossing_pair_within_lower_graph : ∀ n,
    2 * (a n + σ n) ≤ ρ n
  crossing_witness_within_radius : ∀ n, a n + σ n ≤ δ n
  graph_sandwich_gap : ∀ n, 2 * δ n < ρ n
  short_graph_edges : ∀ n, ShortPathSound M (r n)
  tame_level_sets : TameLevelSetFunction M f
  observed_values_injective : ∀ n, Function.Injective (fhat n)
  short_witness_paths : ∀ n, ShortPathSound M (δ n)
  graph_radius_tendsto_zero : Filter.Tendsto r Filter.atTop (nhds 0)
  witness_radius_tendsto_zero : Filter.Tendsto δ Filter.atTop (nhds 0)
  filter_error_tendsto_zero : Filter.Tendsto η Filter.atTop (nhds 0)
  quantization_error_tendsto_zero : Filter.Tendsto q Filter.atTop (nhds 0)

/-- Final packaged point-cloud consistency theorem.  Any sequence of finite
neighborhood graphs satisfying the sandwich hypotheses yields filtered Reeb
graphs converging to the continuum Reeb graph. -/
theorem QuadraticGraphSandwichConsistencyHypotheses.reeb_consistency
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    [LocPathConnectedSpace M]
    (f : M → ℝ) (L cShift cMargin a₀ : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q σ ρ a : ℕ → ℝ)
    (h : QuadraticGraphSandwichConsistencyHypotheses M f L cShift cMargin a₀
      V G sample fbase fhat r δ η q σ ρ a) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  apply reeb_consistency_of_quadratic_level_crossings_and_graph_sandwich
    M f L cShift cMargin a₀ V G sample fbase fhat r δ η q σ ρ a
    h.lipschitz_constant_nonneg h.graph_radius_nonneg
    h.witness_radius_nonneg h.filter_error_nonneg
    h.quantization_error_nonneg h.lipschitz h.filter_error
    h.quantization_error h.sample_dense h.sample_within_witness
    h.graph_lower_sandwich h.graph_upper_sandwich h.crossing_radius_pos
    h.crossing_radius_bound h.quadratic_crossing
    h.error_within_crossing_margin h.comparison_covers_level_shift
    h.crossing_pair_within_lower_graph h.crossing_witness_within_radius
    h.graph_sandwich_gap h.short_graph_edges h.tame_level_sets
    (fun n ↦ GraphEdgeNonflat.of_injective (G n) (fhat n)
      (h.observed_values_injective n))
    h.short_witness_paths h.graph_radius_tendsto_zero
    h.witness_radius_tendsto_zero h.filter_error_tendsto_zero
    h.quantization_error_tendsto_zero

end ReebGraph
