import ReebGraph.Modules.Approximation.BandLift

/-!
# First deterministic distance bound

The first deterministic distance bound, from the plain (not yet
continuous) pair of comparison maps.

Main results: `ApproximationHypotheses.reebDist_le_comparisonError` and
its `_of_mapBand` / `_of_geometricBand` variants.

Supporting: the joined-in transfer lemmas
(`lift_joinedIn_band`, `crossing_edge_endpoints_joinedIn`,
`supportWalk_samples_joinedIn`) and `support_component_no_merge`.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Height control plus canonical band compatibility gives the standard
functional-GH band certificate. -/
noncomputable def ApproximationHypotheses.functionalGHBandCertificate
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hband : CanonicalBandCompatibility h) :
    FunctionalGHBandCertificate (discreteReebRealization V G fhat)
      (continuumReebGraph M f) (approximationComparisonError L r δ η q) where
  error_nonneg := h.comparison_error_nonneg
  toFun := h.discreteToContinuumMap
  invFun := h.continuumToDiscreteMap
  height_to := h.discreteToContinuumMap_height_close_common
  height_inv := h.continuumToDiscreteMap_height_close
  band_to := hband.band_to
  band_inv := hband.band_inv

/-- Deterministic comparison once the sole transition condition is supplied. -/
theorem ApproximationHypotheses.reebDist_le_comparisonError
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hband : CanonicalBandCompatibility h) :
    reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
      ENNReal.ofReal (approximationComparisonError L r δ η q) :=
  functionalGHDistance_le_of_band_certificate
    (h.functionalGHBandCertificate hband)

theorem ApproximationHypotheses.reebDist_le_comparisonError_of_mapBand
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hband : CanonicalMapBandCompatibility h) :
    reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
      ENNReal.ofReal (approximationComparisonError L r δ η q) :=
  h.reebDist_le_comparisonError hband.toCanonicalBandCompatibility

theorem ApproximationHypotheses.reebDist_le_comparisonError_of_geometricBand
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hband : CanonicalGeometricBandCompatibility h) :
    reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
      ENNReal.ofReal (approximationComparisonError L r δ η q) :=
  h.reebDist_le_comparisonError_of_mapBand
    hband.toCanonicalMapBandCompatibility

/-- Every active crossing witness lies in the controlled continuum band. -/
theorem ApproximationHypotheses.active_sample_mem_band
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {u : V} (hu : IsActiveVertex G fhat t u) :
    |f (sample u) - t| ≤ L * r + 3 * η + 3 * q := by
  let au : ActiveVertex G fhat t := ⟨u, hu⟩
  exact h.support_component_sound (componentOfActive G fhat t au)
    (mem_componentSupport_componentOfActive G fhat t au)

/-- Completeness for scalar bands at the level currently justified by the
geometric hypotheses: continuum paths lift to graph walks whose observed
filter remains in a quantitatively enlarged band. -/
theorem ApproximationHypotheses.lift_joinedIn_band
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : M} (hxy : JoinedIn {z | |f z - t| ≤ a} x y)
    {u v : V} (hu : dist (sample u) x ≤ δ)
    (hv : dist (sample v) y ≤ δ) :
    GraphReachableWithin G
      (fun w => |fhat w - t| ≤ a + L * (r + δ) + η + q) u v := by
  have hlift := h.graph_complete.lift_joinedIn hxy hu hv
  apply hlift.mono
  intro w hw
  have htrue : |f (sample w) - t| ≤ a + L * (r + δ) :=
    mem_levelBand_of_mem_thickening f h.lipschitz_constant_nonneg h.lipschitz hw
  calc
    |fhat w - t| =
        |(fhat w - f (sample w)) + (f (sample w) - t)| := by ring_nf
    _ ≤ |fhat w - f (sample w)| + |f (sample w) - t| := abs_add _ _
    _ ≤ (η + q) + (a + L * (r + δ)) :=
      add_le_add (h.total_filter_error w) htrue
    _ = a + L * (r + δ) + η + q := by ring

/-- A crossing edge is realized inside a controlled continuum scalar band. -/
theorem ApproximationHypotheses.crossing_edge_endpoints_joinedIn
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {u v : V} (huv : G.Adj u v) (hcross : Crosses fhat t u v) :
    JoinedIn
      {z | |f z - t| ≤ (L * r + 3 * η + 3 * q) + L * r}
      (sample u) (sample v) := by
  apply h.edge_path_sound.joinedIn_levelBand
    h.lipschitz_constant_nonneg h.lipschitz huv
  exact h.active_sample_mem_band ⟨v, huv, hcross⟩

/-- An original graph edge between active crossing witnesses is realized inside
a controlled continuum scalar band. -/
theorem ApproximationHypotheses.support_edge_endpoints_joinedIn
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {u v : V} (huv : (supportSliceGraph G fhat t).Adj u v) :
    JoinedIn
      {z | |f z - t| ≤ (L * r + 3 * η + 3 * q) + L * r}
      (sample u) (sample v) := by
  exact h.edge_path_sound.joinedIn_levelBand
    h.lipschitz_constant_nonneg h.lipschitz huv.1
      (h.active_sample_mem_band huv.2.1)

/-- Edgewise no-merge composes along support-induced slice walks. -/
theorem ApproximationHypotheses.supportWalk_samples_joinedIn
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {u v : V} (p : (supportSliceGraph G fhat t).Walk u v)
    (hu : |f (sample u) - t| ≤ (L * r + 3 * η + 3 * q) + L * r) :
    JoinedIn
      {z | |f z - t| ≤ (L * r + 3 * η + 3 * q) + L * r}
      (sample u) (sample v) := by
  induction p with
  | nil => exact JoinedIn.refl hu
  | @cons u v w huv p ih =>
      have hfirst := h.support_edge_endpoints_joinedIn huv
      exact hfirst.trans (ih hfirst.target_mem)

/-- An entire discrete support component maps into one path component of the
controlled continuum level band. -/
theorem ApproximationHypotheses.support_component_no_merge
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q t : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (c : SupportComponent G fhat t) {u v : V}
    (hu : u ∈ componentSupport G fhat t c)
    (hv : v ∈ componentSupport G fhat t c) :
    JoinedIn
      {z | |f z - t| ≤ (L * r + 3 * η + 3 * q) + L * r}
      (sample u) (sample v) := by
  rcases componentSupport_reachable G fhat t c hu hv with ⟨p⟩
  have huSmall : |f (sample u) - t| ≤ L * r + 3 * η + 3 * q :=
    h.support_component_sound c hu
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  have huBand :
      |f (sample u) - t| ≤ (L * r + 3 * η + 3 * q) + L * r :=
    huSmall.trans (le_add_of_nonneg_right hLr)
  exact h.supportWalk_samples_joinedIn p huBand

end ReebGraph
