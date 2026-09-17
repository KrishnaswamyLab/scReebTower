import ReebGraph.Modules.Approximation.RefinedBounds

/-!
# Vanishing-scale estimates

Turning the deterministic budgets into vanishing quantities.

Main results: the `*_error_le_scaled` family
(`comparison_error_le_scaled`, `continuous_comparison_error_le_scaled`,
`reduced_continuous_error_le_scaled`, `incidence_continuous_error_le_scaled`,
`slack_incidence_continuous_error_le_scaled_add`), which bound every
comparison budget by a constant multiple of the four-scale error.

Supporting: the `*_has_supportComponent` lemmas showing continuum points,
paths, and level components are all represented discretely.  The generic
limit lemmas they combine with live in `ReebGraph.Modules.Basic`.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Every continuum point is represented by a nearby discrete support
component at a quantitatively nearby threshold. -/
theorem ApproximationHypotheses.levelPoint_has_supportComponent
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (x : M) :
    ∃ (t : ℝ) (c : SupportComponent G fhat t) (u : V),
      u ∈ componentSupport G fhat t c ∧
      dist (sample u) x ≤ δ ∧
      |t - f x| ≤ L * (r + δ) + η + q := by
  rcases h.crossing_coverage x with ⟨t, u, huActive, hux, ht⟩
  let au : ActiveVertex G fhat t := ⟨u, huActive⟩
  exact ⟨t, componentOfActive G fhat t au, u,
    mem_componentSupport_componentOfActive G fhat t au, hux, ht⟩

/-- Path-connected points in one exact continuum level component are covered
by the same discrete support component. -/
theorem ApproximationHypotheses.levelPath_has_supportComponent
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : M} (hxy : JoinedIn {z | f z = t} x y) :
    ∃ (τ : ℝ) (c : SupportComponent G fhat τ) (u v : V),
      u ∈ componentSupport G fhat τ c ∧
      v ∈ componentSupport G fhat τ c ∧
      dist (sample u) x ≤ δ ∧ dist (sample v) y ≤ δ ∧
      |τ - t| ≤ L * (r + δ) + η + q := by
  rcases h.support_complete t hxy with
    ⟨τ, u, v, huActive, hvActive, hux, hvy, hτ, huv⟩
  let au : ActiveVertex G fhat τ := ⟨u, huActive⟩
  let c := componentOfActive G fhat τ au
  have huSupport : u ∈ componentSupport G fhat τ c :=
    mem_componentSupport_componentOfActive G fhat τ au
  have hvSupport : v ∈ componentSupport G fhat τ c := by
    change (supportSliceGraph G fhat τ).Reachable u v
    exact huv
  exact ⟨τ, c, u, v, huSupport, hvSupport, hux, hvy, hτ⟩

/-- Completeness for a classical connected component of an exact level set. -/
theorem ApproximationHypotheses.levelComponent_has_supportComponent
    {M : Type} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : M} (hxy : SameLevelComponent f x y) :
    ∃ (t : ℝ) (c : SupportComponent G fhat t) (u v : V),
      u ∈ componentSupport G fhat t c ∧
      v ∈ componentSupport G fhat t c ∧
      dist (sample u) x ≤ δ ∧ dist (sample v) y ≤ δ ∧
      |t - f x| ≤ L * (r + δ) + η + q := by
  apply h.levelPath_has_supportComponent
  exact h.tame_filter.joinedIn_of_sameLevelComponent hxy

/-- Every point of the continuum Reeb quotient has a representative covered by
a nearby discrete support component at its scalar level. -/
theorem ApproximationHypotheses.continuumReebPoint_has_supportComponent
    {M : Type} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : ContinuumReebQuotient M f) :
    ∃ x : M, ∃ t : ℝ, ∃ c : SupportComponent G fhat t, ∃ u : V,
      continuumReebQuotientMap f x = z ∧
      u ∈ componentSupport G fhat t c ∧
      dist (sample u) x ≤ δ ∧
      |t - f x| ≤ L * (r + δ) + η + q := by
  rcases continuumReebQuotientMap_surjective f z with ⟨x, rfl⟩
  rcases h.levelPoint_has_supportComponent x with ⟨t, c, u, hu, hux, ht⟩
  exact ⟨x, t, c, u, rfl, hu, hux, ht⟩


/-- The explicit two-map comparison budget is controlled by the advertised
four-scale error with a constant depending only on the fixed Lipschitz
constant. -/
theorem ApproximationHypotheses.comparison_error_le_scaled
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    approximationComparisonError L r δ η q ≤
      max L 3 * (L * r + δ + η + q) := by
  have hC2 : (2 : ℝ) ≤ max L 3 :=
    (by norm_num : (2 : ℝ) ≤ 3).trans (le_max_right L 3)
  have hC3 : (3 : ℝ) ≤ max L 3 := le_max_right L 3
  have hCL : L ≤ max L 3 := le_max_left L 3
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  calc
    approximationComparisonError L r δ η q =
        2 * (L * r) + L * δ + 3 * η + 3 * q := by
      unfold approximationComparisonError
      ring
    _ ≤ max L 3 * (L * r) + max L 3 * δ +
        max L 3 * η + max L 3 * q := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hC2 hLr)
            (mul_le_mul_of_nonneg_right hCL h.sampling_scale_nonneg))
          (mul_le_mul_of_nonneg_right hC3 h.filter_error_nonneg))
        (mul_le_mul_of_nonneg_right hC3 h.quantization_error_nonneg)
    _ = max L 3 * (L * r + δ + η + q) := by ring

/-- The error budget for the continuous forward map is controlled by the same
four vanishing scales, with an explicit universal coefficient enlargement. -/
theorem ApproximationHypotheses.continuous_comparison_error_le_scaled
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    continuousCanonicalComparisonError L r δ η q ≤
      max (2 * L) 9 * (L * r + δ + η + q) := by
  let C := max (2 * L) 9
  have hCnonneg : 0 ≤ C :=
    (by norm_num : (0 : ℝ) ≤ 9).trans (le_max_right (2 * L) 9)
  have hC2 : (2 : ℝ) ≤ C :=
    (by norm_num : (2 : ℝ) ≤ 9).trans (le_max_right (2 * L) 9)
  have hC3 : (3 : ℝ) ≤ C :=
    (by norm_num : (3 : ℝ) ≤ 9).trans (le_max_right (2 * L) 9)
  have hC4 : (4 : ℝ) ≤ C :=
    (by norm_num : (4 : ℝ) ≤ 9).trans (le_max_right (2 * L) 9)
  have hC9 : (9 : ℝ) ≤ C := le_max_right (2 * L) 9
  have hC2L : 2 * L ≤ C := le_max_left (2 * L) 9
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  have hforward : continuousForwardError L r η q ≤
      C * (L * r + δ + η + q) := by
    calc
      continuousForwardError L r η q =
          4 * (L * r) + 9 * η + 9 * q := by
        unfold continuousForwardError
        ring
      _ ≤ C * (L * r) + C * η + C * q := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hC4 hLr)
            (mul_le_mul_of_nonneg_right hC9 h.filter_error_nonneg))
          (mul_le_mul_of_nonneg_right hC9 h.quantization_error_nonneg)
      _ ≤ C * (L * r) + C * δ + C * η + C * q := by
        have hCδ : 0 ≤ C * δ :=
          mul_nonneg hCnonneg h.sampling_scale_nonneg
        linarith
      _ = C * (L * r + δ + η + q) := by ring
  have hold : approximationComparisonError L r δ η q + L * δ ≤
      C * (L * r + δ + η + q) := by
    calc
      approximationComparisonError L r δ η q + L * δ =
          2 * (L * r) + (2 * L) * δ + 3 * η + 3 * q := by
        unfold approximationComparisonError
        ring
      _ ≤ C * (L * r) + C * δ + C * η + C * q := by
        exact add_le_add
          (add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_right hC2 hLr)
              (mul_le_mul_of_nonneg_right hC2L h.sampling_scale_nonneg))
            (mul_le_mul_of_nonneg_right hC3 h.filter_error_nonneg))
          (mul_le_mul_of_nonneg_right hC3 h.quantization_error_nonneg)
      _ = C * (L * r + δ + η + q) := by ring
  exact max_le hold hforward

theorem ApproximationHypotheses.reduced_continuous_error_le_scaled
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    reducedContinuousCanonicalComparisonError L r δ η q ≤
      (3 * max (2 * L) 9) * (L * r + δ + η + q) := by
  unfold reducedContinuousCanonicalComparisonError
  calc
    3 * continuousCanonicalComparisonError L r δ η q ≤
        3 * (max (2 * L) 9 * (L * r + δ + η + q)) :=
      mul_le_mul_of_nonneg_left h.continuous_comparison_error_le_scaled
        (by norm_num)
    _ = (3 * max (2 * L) 9) * (L * r + δ + η + q) := by ring

/-- The incidence-level comparison has the same vanishing scale, with the
factor twelve coming from four CW anchoring units followed by the generic
factor-three correspondence reduction. -/
theorem ApproximationHypotheses.incidence_continuous_error_le_scaled
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    incidenceContinuousCanonicalComparisonError L r δ η q ≤
      (12 * max (2 * L) 9) * (L * r + δ + η + q) := by
  unfold incidenceContinuousCanonicalComparisonError
  calc
    3 * (4 * continuousCanonicalComparisonError L r δ η q) ≤
        3 * (4 * (max (2 * L) 9 * (L * r + δ + η + q))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h.continuous_comparison_error_le_scaled
          (by norm_num))
        (by norm_num)
    _ = (12 * max (2 * L) 9) * (L * r + δ + η + q) := by ring

theorem ApproximationHypotheses.slack_incidence_continuous_error_le_scaled_add
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    slackIncidenceContinuousCanonicalComparisonError L r δ η q s ≤
      (12 * max (2 * L) 9) * (L * r + δ + η + q) + 3 * s := by
  unfold slackIncidenceContinuousCanonicalComparisonError
  calc
    3 * (4 * continuousCanonicalComparisonError L r δ η q + s) =
        12 * continuousCanonicalComparisonError L r δ η q + 3 * s := by ring
    _ ≤ 12 * (max (2 * L) 9 * (L * r + δ + η + q)) + 3 * s :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left h.continuous_comparison_error_le_scaled
          (by norm_num)) _
    _ = (12 * max (2 * L) 9) * (L * r + δ + η + q) + 3 * s := by ring

end ReebGraph
