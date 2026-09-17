import ReebGraph.Modules.Approximation.Asymptotics

/-!
# MAIN -- deterministic approximation theorems

MAIN THEOREMS (deterministic form).

Explicit, non-asymptotic bounds on `reebDist` between the discrete Reeb
realization and the continuum Reeb graph, one per compatibility
interface:

* `deterministic_reeb_approximation_reduced`
* `deterministic_reeb_approximation_incidence`
* `deterministic_reeb_approximation_tame_nonflat_with_slack`
* `deterministic_reeb_approximation_tame_nonflat`
* `deterministic_reeb_approximation_nonflat`
* `deterministic_reeb_approximation_nonflat_of_section`
* `deterministic_reeb_approximation_continuous`
* `deterministic_reeb_approximation`

Every proof here is an assembly step: the work is done in
`ReebGraph.Modules.Approximation.*`.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Main reduced deterministic theorem.  The only estimator-specific input is
band reflection between points in the image of the constructed continuous
support map; local short paths supply image density. -/
theorem deterministic_reeb_approximation_reduced
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (sample : V → M) (fbase fhat : V → ℝ)
      {r δ η q : ℝ},
      (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) →
      ReducedContinuousCanonicalCompatibility h →
      reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
        ENNReal.ofReal (C * (L * r + δ + η + q)) := by
  refine ⟨3 * max (2 * L) 9, ?_, ?_⟩
  · exact mul_nonneg (by norm_num)
      ((by norm_num : (0 : ℝ) ≤ 9).trans (le_max_right (2 * L) 9))
  · intro V _ _ G sample fbase fhat r δ η q h hcompat
    exact (h.reebDist_le_reducedContinuousComparisonError hcompat).trans
      (ENNReal.ofReal_le_ofReal h.reduced_continuous_error_le_scaled)

/-- Main deterministic theorem at the active-incidence interface.  No
connectivity statement about the algorithm's quotient graph is assumed:
the geometric input constructs a bounded walk before quotienting. -/
theorem deterministic_reeb_approximation_incidence
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (sample : V → M) (fbase fhat : V → ℝ)
      {r δ η q : ℝ},
      (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) →
      IncidenceContinuousCanonicalCompatibility h →
      reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
        ENNReal.ofReal (C * (L * r + δ + η + q)) := by
  refine ⟨12 * max (2 * L) 9, ?_, ?_⟩
  · exact mul_nonneg (by norm_num)
      ((by norm_num : (0 : ℝ) ≤ 9).trans (le_max_right (2 * L) 9))
  · intro V _ _ G sample fbase fhat r δ η q h hcompat
    exact (h.reebDist_le_incidenceContinuousComparisonError hcompat).trans
      (ENNReal.ofReal_le_ofReal h.incidence_continuous_error_le_scaled)

/-- Deterministic convergence theorem with quotient path lifting discharged
topologically.  The arbitrary positive `s` is proof slack, not an algorithmic
parameter, and can be taken to zero in the consistency theorem. -/
theorem deterministic_reeb_approximation_tame_nonflat_with_slack
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    [LocPathConnectedSpace M]
    (f : M → ℝ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (sample : V → M) (fbase fhat : V → ℝ)
      {r δ η q s : ℝ},
      0 < s →
      (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) →
      GraphEdgeNonflat G fhat →
      ShortPathSound M δ →
      reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
        ENNReal.ofReal (C * (L * r + δ + η + q) + 3 * s) := by
  refine ⟨12 * max (2 * L) 9, ?_, ?_⟩
  · exact mul_nonneg (by norm_num)
      ((by norm_num : (0 : ℝ) ≤ 9).trans (le_max_right (2 * L) 9))
  · intro V _ _ G sample fbase fhat r δ η q s hs h hnonflat hshort
    have hcompat : SlackIncidenceContinuousCanonicalCompatibility h s :=
      .ofTameNonflat hs hnonflat hshort
    exact (h.reebDist_le_slackIncidenceContinuousComparisonError hcompat).trans
      (ENNReal.ofReal_le_ofReal
        h.slack_incidence_continuous_error_le_scaled_add)

/-- Clean deterministic theorem.  The positive proof slack is sent to zero
inside the proof, so the final statement contains only the four geometric and
filter scales. -/
theorem deterministic_reeb_approximation_tame_nonflat
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    [LocPathConnectedSpace M]
    (f : M → ℝ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (sample : V → M) (fbase fhat : V → ℝ)
      {r δ η q : ℝ},
      (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) →
      GraphEdgeNonflat G fhat →
      ShortPathSound M δ →
      reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
        ENNReal.ofReal (C * (L * r + δ + η + q)) := by
  rcases deterministic_reeb_approximation_tame_nonflat_with_slack M f L with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro V _ _ G sample fbase fhat r δ η q h hnonflat hshort
  let s : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hspos : ∀ n, 0 < s n := by
    intro n
    exact one_div_pos.mpr (by positivity)
  have hs0 : Filter.Tendsto s Filter.atTop (nhds 0) := by
    simpa only [s] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Filter.Tendsto
      (fun n ↦ C * (L * r + δ + η + q) + 3 * s n)
      Filter.atTop (nhds (C * (L * r + δ + η + q))) := by
    simpa only [s, one_div, mul_zero, add_zero] using
      tendsto_const_nhds.add (hs0.const_mul 3)
  have henn : Filter.Tendsto
      (fun n ↦ ENNReal.ofReal
        (C * (L * r + δ + η + q) + 3 * s n))
      Filter.atTop (nhds (ENNReal.ofReal (C * (L * r + δ + η + q)))) :=
    ENNReal.tendsto_ofReal hreal
  apply ge_of_tendsto henn
  exact Filter.Eventually.of_forall fun n ↦
    hbound V G sample fbase fhat (hspos n) h hnonflat hshort

/-- Deterministic convergence with the finite incidence theorem discharged.
For a non-flat observed scalar, graph completeness automatically produces the
required bounded active-incidence walk. -/
theorem deterministic_reeb_approximation_nonflat
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (sample : V → M) (fbase fhat : V → ℝ)
      {r δ η q : ℝ},
      (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) →
      ReebLiftNonflatContinuousCanonicalCompatibility h →
      reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
        ENNReal.ofReal (C * (L * r + δ + η + q)) := by
  rcases deterministic_reeb_approximation_incidence M f L with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro V _ _ G sample fbase fhat r δ η q h hcompat
  exact hbound V G sample fbase fhat h (hcompat.toIncidence)

/-- Paper-facing section form of the deterministic theorem.  The continuum
condition is independent of the sample; finite graph completeness is already
part of `ApproximationHypotheses`, and the incidence argument is derived. -/
theorem deterministic_reeb_approximation_nonflat_of_section
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ) (reebSection : ContinuumReebSection M f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (sample : V → M) (fbase fhat : V → ℝ)
      {r δ η q : ℝ},
      (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) →
      GraphEdgeNonflat G fhat →
      ShortPathSound M δ →
      reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
        ENNReal.ofReal (C * (L * r + δ + η + q)) := by
  rcases deterministic_reeb_approximation_nonflat M f L with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro V _ _ G sample fbase fhat r δ η q h hnonflat hshort
  exact hbound V G sample fbase fhat h
    (.ofSection reebSection hnonflat hshort)

/-- Deterministic approximation theorem using the proved continuous forward
support map.  Three topological/combinatorial conditions and local short-path
geometry remain. -/
theorem deterministic_reeb_approximation_continuous
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (sample : V → M) (fbase fhat : V → ℝ)
      {r δ η q : ℝ},
      (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) →
      ContinuousCanonicalGeometricBandCompatibility h →
      reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
        ENNReal.ofReal (C * (L * r + δ + η + q)) := by
  refine ⟨max (2 * L) 9, ?_, ?_⟩
  · exact (by norm_num : (0 : ℝ) ≤ 9).trans (le_max_right (2 * L) 9)
  · intro V _ _ G sample fbase fhat r δ η q h hband
    exact (h.reebDist_le_continuousComparisonError hband).trans
      (ENNReal.ofReal_le_ofReal h.continuous_comparison_error_le_scaled)

/-- Deterministic approximation theorem for a neighborhood graph satisfying
the explicit canonical band-transition condition. -/
theorem deterministic_reeb_approximation
    (M : Type) [PseudoMetricSpace M] [CompactSpace M]
    (f : M → ℝ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (sample : V → M) (fbase fhat : V → ℝ)
      {r δ η q : ℝ},
      (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) →
      CanonicalGeometricBandCompatibility h →
      reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
        ENNReal.ofReal (C * (L * r + δ + η + q)) := by
  refine ⟨max L 3, ?_, ?_⟩
  · exact (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_right L 3)
  · intro V _ _ G sample fbase fhat r δ η q h hband
    exact (h.reebDist_le_comparisonError_of_geometricBand hband).trans
      (ENNReal.ofReal_le_ofReal h.comparison_error_le_scaled)

end ReebGraph
