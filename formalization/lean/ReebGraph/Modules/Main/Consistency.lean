import ReebGraph.Modules.Main.Deterministic

/-!
# MAIN -- asymptotic consistency theorems

MAIN THEOREMS (asymptotic form).

Convergence of the filtered discrete Reeb realizations to the continuum
Reeb graph as the scales vanish:

* `reeb_consistency` and `reeb_consistency_of_vanishing_scales`
* `reeb_consistency_from_approximation_hypotheses` and its continuous,
  reduced, incidence, nonflat, and tame-nonflat variants
* `reeb_consistency_from_true_crossing_pairs_and_graph_sandwich`
* `reeb_consistency_of_quadratic_level_crossings_and_graph_sandwich`

The last one is the graph-agnostic statement: only a two-sided proximity
sandwich is assumed of the graph, never a kNN construction.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Metric consistency once all deterministic error terms vanish. -/
theorem reeb_consistency
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (f : M → ℝ) (fhat : ∀ n, V n → ℝ)
    (error : ℕ → ℝ≥0∞)
    (herror : Filter.Tendsto error Filter.atTop (nhds 0))
    (hnonneg : ∀ n, 0 ≤
      reebDist (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
    (hbound : ∀ n,
      reebDist (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f) ≤ error n) :
    Filter.Tendsto
      (fun n => reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds herror
    (Filter.Eventually.of_forall hnonneg)
    (Filter.Eventually.of_forall hbound)

/-- Consistency in the form used by the sampling theorem: a fixed-constant
deterministic bound and four vanishing error scales imply convergence in Reeb
distance. -/
theorem reeb_consistency_of_vanishing_scales
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (f : M → ℝ) (fhat : ∀ n, V n → ℝ)
    (C L : ℝ) (r δ η q : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0))
    (hnonneg : ∀ n, 0 ≤
      reebDist (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
    (hbound : ∀ n,
      reebDist (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f) ≤
          ENNReal.ofReal (C * (L * r n + δ n + η n + q n))) :
    Filter.Tendsto
      (fun n => reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  apply reeb_consistency M V G f fhat
    (fun n => ENNReal.ofReal (C * (L * r n + δ n + η n + q n)))
  · simpa using ENNReal.tendsto_ofReal
      (scaled_approximation_error_tendsto_zero C L r δ η q hr hδ hη hq)
  · exact hnonneg
  · exact hbound

/-- The conditional point-cloud consistency theorem.  All asymptotic analysis
is reduced to verifying the per-sample approximation hypotheses and the four
scalar limits. -/
theorem reeb_consistency_from_approximation_hypotheses
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q : ℕ → ℝ)
    (happrox : ∀ n, ApproximationHypotheses M (V n) (G n) (sample n)
      f (fbase n) (fhat n) L (r n) (δ n) (η n) (q n))
    (hband : ∀ n, CanonicalGeometricBandCompatibility (happrox n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0))
    (hdist : ReebDistanceLaws reebDist) :
    Filter.Tendsto
      (fun n => reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  rcases deterministic_reeb_approximation M f L with ⟨C, _, hbound⟩
  apply reeb_consistency_of_vanishing_scales M V G f fhat C L r δ η q
    hr hδ hη hq
  · intro n
    exact hdist.nonneg _ _
  intro n
  exact hbound (V n) (G n) (sample n) (fbase n) (fhat n)
    (happrox n) (hband n)

/-- Point-cloud consistency through the continuous support realization.  The
forward map and its band control are constructed above; the supplied
compatibility contains three topological/combinatorial facts and local
short-path geometry. -/
theorem reeb_consistency_from_continuous_approximation_hypotheses
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q : ℕ → ℝ)
    (happrox : ∀ n, ApproximationHypotheses M (V n) (G n) (sample n)
      f (fbase n) (fhat n) L (r n) (δ n) (η n) (q n))
    (hband : ∀ n,
      ContinuousCanonicalGeometricBandCompatibility (happrox n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0))
    (hdist : ReebDistanceLaws reebDist) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  rcases deterministic_reeb_approximation_continuous M f L with
    ⟨C, _, hbound⟩
  apply reeb_consistency_of_vanishing_scales M V G f fhat C L r δ η q
    hr hδ hη hq
  · intro n
    exact hdist.nonneg _ _
  intro n
  exact hbound (V n) (G n) (sample n) (fbase n) (fhat n)
    (happrox n) (hband n)

/-- Asymptotic consistency in the reduced interface: image-band reflection is
the sole estimator-specific condition, while short paths are local ambient
geometry. -/
theorem reeb_consistency_from_reduced_approximation_hypotheses
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q : ℕ → ℝ)
    (happrox : ∀ n, ApproximationHypotheses M (V n) (G n) (sample n)
      f (fbase n) (fhat n) L (r n) (δ n) (η n) (q n))
    (hcompat : ∀ n, ReducedContinuousCanonicalCompatibility (happrox n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0))
    (hdist : ReebDistanceLaws reebDist) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  rcases deterministic_reeb_approximation_reduced M f L with
    ⟨C, _, hbound⟩
  apply reeb_consistency_of_vanishing_scales M V G f fhat C L r δ η q
    hr hδ hη hq
  · intro n
    exact hdist.nonneg _ _
  intro n
  exact hbound (V n) (G n) (sample n) (fbase n) (fhat n)
    (happrox n) (hcompat n)

/-- Point-cloud consistency at the non-circular active-incidence interface.
The estimator-specific asymptotic input is a bounded pre-quotient incidence
walk for each continuum band path between canonical node images. -/
theorem reeb_consistency_from_incidence_approximation_hypotheses
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q : ℕ → ℝ)
    (happrox : ∀ n, ApproximationHypotheses M (V n) (G n) (sample n)
      f (fbase n) (fhat n) L (r n) (δ n) (η n) (q n))
    (hcompat : ∀ n,
      IncidenceContinuousCanonicalCompatibility (happrox n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0))
    (hdist : ReebDistanceLaws reebDist) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  rcases deterministic_reeb_approximation_incidence M f L with
    ⟨C, _, hbound⟩
  apply reeb_consistency_of_vanishing_scales M V G f fhat C L r δ η q
    hr hδ hη hq
  · intro n
    exact hdist.nonneg _ _
  intro n
  exact hbound (V n) (G n) (sample n) (fbase n) (fhat n)
    (happrox n) (hcompat n)

/-- Point-cloud consistency after the finite incidence proof has been fully
discharged.  A fixed continuum path-lifting fact is combined with generic
nonflat observed edges and local short-path geometry at every sample. -/
theorem reeb_consistency_from_nonflat_approximation_hypotheses
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q : ℕ → ℝ)
    (happrox : ∀ n, ApproximationHypotheses M (V n) (G n) (sample n)
      f (fbase n) (fhat n) L (r n) (δ n) (η n) (q n))
    (hlift : ContinuumReebBandPathLift M f)
    (hnonflat : ∀ n, GraphEdgeNonflat (G n) (fhat n))
    (hshort : ∀ n, ShortPathSound M (δ n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0))
    (hdist : ReebDistanceLaws reebDist) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  apply reeb_consistency_from_incidence_approximation_hypotheses
    M f L V G sample fbase fhat r δ η q happrox
    (fun n ↦
      (show ReebLiftNonflatContinuousCanonicalCompatibility (happrox n) from
        { quotient_path_lift := hlift
          edge_nonflat := hnonflat n
          short_path_sound := hshort n }).toIncidence)
    hr hδ hη hq hdist

/-- Section-specialized consistency theorem.  The same continuum section is
used for the entire sampling sequence. -/
theorem reeb_consistency_from_nonflat_approximation_hypotheses_of_section
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ) (reebSection : ContinuumReebSection M f)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q : ℕ → ℝ)
    (happrox : ∀ n, ApproximationHypotheses M (V n) (G n) (sample n)
      f (fbase n) (fhat n) L (r n) (δ n) (η n) (q n))
    (hnonflat : ∀ n, GraphEdgeNonflat (G n) (fhat n))
    (hshort : ∀ n, ShortPathSound M (δ n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0))
    (hdist : ReebDistanceLaws reebDist) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  exact reeb_consistency_from_nonflat_approximation_hypotheses
    M f L V G sample fbase fhat r δ η q happrox
    reebSection.bandPathLift hnonflat hshort hr hδ hη hq hdist

/-- Main point-cloud consistency theorem without a quotient-section or exact
path-lifting hypothesis. -/
theorem reeb_consistency_from_tame_nonflat_approximation_hypotheses
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    [LocPathConnectedSpace M]
    (f : M → ℝ) (L : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q : ℕ → ℝ)
    (happrox : ∀ n, ApproximationHypotheses M (V n) (G n) (sample n)
      f (fbase n) (fhat n) L (r n) (δ n) (η n) (q n))
    (hnonflat : ∀ n, GraphEdgeNonflat (G n) (fhat n))
    (hshort : ∀ n, ShortPathSound M (δ n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0))
    (hdist : ReebDistanceLaws reebDist) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  rcases deterministic_reeb_approximation_tame_nonflat M f L with
    ⟨C, _, hbound⟩
  apply reeb_consistency_of_vanishing_scales M V G f fhat C L r δ η q
    hr hδ hη hq
  · intro n
    exact hdist.nonneg _ _
  intro n
  exact hbound (V n) (G n) (sample n) (fbase n) (fhat n)
    (happrox n) (hnonflat n) (hshort n)

/-- Graph-agnostic point-cloud consistency from checkable geometric inputs.
Each supplied graph lies between two proximity graphs, the sample supplies
robust true crossing pairs on every relevant continuum level component, and
the spatial and scalar error scales vanish.  No kNN-specific property and no
algorithmic output condition appears among the hypotheses. -/
theorem reeb_consistency_from_true_crossing_pairs_and_graph_sandwich
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    [LocPathConnectedSpace M]
    (f : M → ℝ) (L : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q σ ρ a m : ℕ → ℝ)
    (hL : 0 ≤ L)
    (hr_nonneg : ∀ n, 0 ≤ r n)
    (hδ_nonneg : ∀ n, 0 ≤ δ n)
    (hη_nonneg : ∀ n, 0 ≤ η n)
    (hq_nonneg : ∀ n, 0 ≤ q n)
    (hlipschitz : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hfilter : ∀ n v, |fbase n v - f (sample n v)| ≤ η n)
    (hquantization : ∀ n v, |fhat n v - fbase n v| ≤ q n)
    (hsample : ∀ n, SampleDense M (V n) (sample n) (σ n))
    (hσδ : ∀ n, σ n ≤ δ n)
    (hlower : ∀ n,
      ContainsProximityGraph M (V n) (G n) (sample n) (ρ n))
    (hupper : ∀ n,
      G n ≤ proximityGraph M (V n) (sample n) (r n))
    (hmargin : ∀ n, L * σ n + (η n + q n) ≤ m n)
    (hprox : ∀ n, 2 * (a n + σ n) ≤ ρ n)
    (hwitness : ∀ n, a n + σ n ≤ δ n)
    (hgap : ∀ n, 2 * δ n < ρ n)
    (htrue : ∀ n, CommonThresholdTrueCrossingPairDensity M f
      (a n) (m n) (L * (r n + δ n) + η n + q n))
    (hshort_edge : ∀ n, ShortPathSound M (r n))
    (htame : TameLevelSetFunction M f)
    (hnonflat : ∀ n, GraphEdgeNonflat (G n) (fhat n))
    (hshort_witness : ∀ n, ShortPathSound M (δ n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  have happrox : ∀ n, ApproximationHypotheses M (V n) (G n) (sample n)
      f (fbase n) (fhat n) L (r n) (δ n) (η n) (q n) := by
    intro n
    exact ApproximationHypotheses.of_true_crossing_pairs
      hL (hr_nonneg n) (hδ_nonneg n) (hη_nonneg n) (hq_nonneg n)
      hlipschitz (hfilter n) (hquantization n) (hsample n) (hσδ n)
      (hlower n) (hupper n) (hmargin n) (hprox n) (hwitness n)
      (hgap n) (htrue n) (hshort_edge n) htame
  exact reeb_consistency_from_tame_nonflat_approximation_hypotheses
    M f L V G sample fbase fhat r δ η q happrox hnonflat
    hshort_witness hr hδ hη hq reebDist_laws

/-- Main graph-agnostic consistency theorem under the uniform quadratic
crossing consequence of Morse local models.  The two additional scale
inequalities have a direct interpretation: sampling and filter error must fit
inside the quadratic crossing margin, and the deterministic comparison slack
must dominate the quadratic threshold displacement near extrema. -/
theorem reeb_consistency_of_quadratic_level_crossings_and_graph_sandwich
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    [LocPathConnectedSpace M]
    (f : M → ℝ) (L cShift cMargin a₀ : ℝ)
    (V : ℕ → Type)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (sample : ∀ n, V n → M)
    (fbase fhat : ∀ n, V n → ℝ)
    (r δ η q σ ρ a : ℕ → ℝ)
    (hL : 0 ≤ L)
    (hr_nonneg : ∀ n, 0 ≤ r n)
    (hδ_nonneg : ∀ n, 0 ≤ δ n)
    (hη_nonneg : ∀ n, 0 ≤ η n)
    (hq_nonneg : ∀ n, 0 ≤ q n)
    (hlipschitz : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hfilter : ∀ n v, |fbase n v - f (sample n v)| ≤ η n)
    (hquantization : ∀ n v, |fhat n v - fbase n v| ≤ q n)
    (hsample : ∀ n, SampleDense M (V n) (sample n) (σ n))
    (hσδ : ∀ n, σ n ≤ δ n)
    (hlower : ∀ n,
      ContainsProximityGraph M (V n) (G n) (sample n) (ρ n))
    (hupper : ∀ n,
      G n ≤ proximityGraph M (V n) (sample n) (r n))
    (ha_pos : ∀ n, 0 < a n)
    (ha_bound : ∀ n, a n ≤ a₀)
    (hcross : QuadraticLevelCrossingCondition M f
      cShift cMargin a₀)
    (hmargin : ∀ n,
      L * σ n + (η n + q n) ≤ cMargin * (a n) ^ 2)
    (hshift : ∀ n,
      cShift * (a n) ^ 2 ≤ L * (r n + δ n) + η n + q n)
    (hprox : ∀ n, 2 * (a n + σ n) ≤ ρ n)
    (hwitness : ∀ n, a n + σ n ≤ δ n)
    (hgap : ∀ n, 2 * δ n < ρ n)
    (hshort_edge : ∀ n, ShortPathSound M (r n))
    (htame : TameLevelSetFunction M f)
    (hnonflat : ∀ n, GraphEdgeNonflat (G n) (fhat n))
    (hshort_witness : ∀ n, ShortPathSound M (δ n))
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n ↦ reebDist
        (discreteReebRealization (V n) (G n) (fhat n))
        (continuumReebGraph M f))
      Filter.atTop (nhds 0) := by
  have htrue : ∀ n, CommonThresholdTrueCrossingPairDensity M f
      (a n) (cMargin * (a n) ^ 2)
      (L * (r n + δ n) + η n + q n) := by
    intro n
    exact hcross.crossing_pairs (ha_pos n) (ha_bound n) (hshift n)
  exact reeb_consistency_from_true_crossing_pairs_and_graph_sandwich
    M f L V G sample fbase fhat r δ η q σ ρ a
    (fun n ↦ cMargin * (a n) ^ 2)
    hL hr_nonneg hδ_nonneg hη_nonneg hq_nonneg hlipschitz
    hfilter hquantization hsample hσδ hlower hupper hmargin
    hprox hwitness hgap htrue hshort_edge htame hnonflat
    hshort_witness hr hδ hη hq

end ReebGraph
