import ReebGraph.Modules.Approximation.IncidenceCoverage

/-!
# Refined comparison interfaces

The refined comparison interfaces and their distance bounds -- the
reduced, incidence, slack-incidence, and continuous-geometric budgets.

Main results: `ApproximationHypotheses.reebDist_le_reducedContinuousComparisonError`,
`.reebDist_le_incidenceContinuousComparisonError`,
`.reebDist_le_slackIncidenceContinuousComparisonError`, and
`.reebDist_le_continuousComparisonError`.

Supporting: each `*Compatibility` structure with its
`toMapBandCompatibility` conversion and the matching band certificate.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Final comparison cost of the reduced one-condition interface. -/
def reducedContinuousCanonicalComparisonError (L r δ η q : ℝ) : ℝ :=
  3 * continuousCanonicalComparisonError L r δ η q

theorem ApproximationHypotheses.continuousDiscreteToContinuumMap_band_common
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x x' : (discreteReebRealization V G fhat).Carrier}
    (hxx' : HeightBandJoined (discreteReebRealization V G fhat) a b x x') :
    HeightBandJoined (continuumReebGraph M f)
      (a - continuousCanonicalComparisonError L r δ η q)
      (b + continuousCanonicalComparisonError L r δ η q)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap x') := by
  apply HeightBandJoined.mono (h.continuousDiscreteToContinuumMap_band hxx')
  · unfold continuousCanonicalComparisonError
    linarith [le_max_right
      (approximationComparisonError L r δ η q + L * δ)
      (continuousForwardError L r η q)]
  · unfold continuousCanonicalComparisonError
    linarith [le_max_right
      (approximationComparisonError L r δ η q + L * δ)
      (continuousForwardError L r η q)]

theorem ApproximationHypotheses.continuumToDiscreteMap_height_close_continuousCommon
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (y : (continuumReebGraph M f).Carrier) :
    |(discreteReebRealization V G fhat).height
        (h.continuumToDiscreteMap y) -
      (continuumReebGraph M f).height y| ≤
      continuousCanonicalComparisonError L r δ η q := by
  apply (h.continuumToDiscreteMap_height_close y).trans
  have hLδ : 0 ≤ L * δ :=
    mul_nonneg h.lipschitz_constant_nonneg h.sampling_scale_nonneg
  exact (le_add_of_nonneg_right hLδ).trans (le_max_left _ _)

/-- Reduced geometric interface: one reverse theorem for points in the image
of the constructed support map, plus standard local short-path geometry. -/
structure ReducedContinuousCanonicalCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop where
  image_band_reflection : ContinuousCanonicalImageBandReflection h
  short_path_sound : ShortPathSound M δ

def ReducedContinuousCanonicalMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  FunctionalGHMapBandCompatibility
    (discreteReebRealization V G fhat) (continuumReebGraph M f)
    (reducedContinuousCanonicalComparisonError L r δ η q)
    h.continuousDiscreteToContinuumMap h.continuumToDiscreteMap

theorem ReducedContinuousCanonicalCompatibility.toMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (hcompat : ReducedContinuousCanonicalCompatibility h) :
    ReducedContinuousCanonicalMapBandCompatibility h := by
  apply functionalGHMapBandCompatibility_of_imageBandReflection
    h.continuousCanonicalComparisonError_nonneg
  · intro a b x x' _hab hxx'
    exact h.continuousDiscreteToContinuumMap_band_common hxx'
  · exact h.continuumToDiscreteMap_height_close_continuousCommon
  · exact h.continuousContinuumRoundtrip_band_of_shortPathSound
      hcompat.short_path_sound
  · exact hcompat.image_band_reflection

theorem ApproximationHypotheses.reducedContinuousComparisonError_nonneg
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ reducedContinuousCanonicalComparisonError L r δ η q :=
  mul_nonneg (by norm_num) h.continuousCanonicalComparisonError_nonneg

/-- The reduced image-reflection condition produces the complete functional-GH
band certificate; the discrete round trip and quotient lifting are derived
inside the generic factor-three reduction. -/
noncomputable def ApproximationHypotheses.reducedContinuousFunctionalGHBandCertificate
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcompat : ReducedContinuousCanonicalCompatibility h) :
    FunctionalGHBandCertificate (discreteReebRealization V G fhat)
      (continuumReebGraph M f)
      (reducedContinuousCanonicalComparisonError L r δ η q) := by
  let hmap := hcompat.toMapBandCompatibility
  have hE := h.continuousCanonicalComparisonError_nonneg
  have hforwardLe : continuousForwardError L r η q ≤
      continuousCanonicalComparisonError L r δ η q := by
    exact le_max_right _ _
  have htriple : continuousCanonicalComparisonError L r δ η q ≤
      reducedContinuousCanonicalComparisonError L r δ η q := by
    unfold reducedContinuousCanonicalComparisonError
    linarith
  exact
    { error_nonneg := h.reducedContinuousComparisonError_nonneg
      toFun := h.continuousDiscreteToContinuumMap
      invFun := h.continuumToDiscreteMap
      height_to := fun x ↦
        (h.continuousDiscreteToContinuumMap_height_close x).trans
          (hforwardLe.trans htriple)
      height_inv := fun y ↦
        (h.continuumToDiscreteMap_height_close_continuousCommon y).trans htriple
      band_to := hmap.band_to_full
      band_inv := hmap.band_inv_full }

theorem ApproximationHypotheses.reebDist_le_reducedContinuousComparisonError
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcompat : ReducedContinuousCanonicalCompatibility h) :
    reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
      ENNReal.ofReal
        (reducedContinuousCanonicalComparisonError L r δ η q) :=
  functionalGHDistance_le_of_band_certificate
    (h.reducedContinuousFunctionalGHBandCertificate hcompat)

/-- End-to-end comparison cost when the remaining finite geometry is supplied
as active-incidence coverage rather than arbitrary-point image reflection. -/
def incidenceContinuousCanonicalComparisonError
    (L r δ η q : ℝ) : ℝ :=
  3 * (4 * continuousCanonicalComparisonError L r δ η q)

/-- Concrete reduced interface: the only estimator statement is that a
continuum band path between canonical node images lifts to a bounded walk in
the pre-quotient active-incidence graph. -/
structure IncidenceContinuousCanonicalCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop where
  incidence_band_coverage : CanonicalNodeIncidenceBandCoverage h
  short_path_sound : ShortPathSound M δ

/-- Functional-GH cost when quotient paths are lifted with positive scalar
slack `s`.  The first factor three is the generic two-map reduction. -/
def slackIncidenceContinuousCanonicalComparisonError
    (L r δ η q s : ℝ) : ℝ :=
  3 * (4 * continuousCanonicalComparisonError L r δ η q + s)

/-- Incidence compatibility with an explicit scalar slack. -/
structure SlackIncidenceContinuousCanonicalCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (s : ℝ) : Prop where
  slack_nonneg : 0 ≤ s
  incidence_band_coverage : CanonicalNodeIncidenceBandCoverageAt h
    (continuousCanonicalComparisonError L r δ η q + s)
  short_path_sound : ShortPathSound M δ

/-- Tameness and local path-connectedness supply the slackened continuum
lift; nonflatness supplies finite incidence canonicalization. -/
def SlackIncidenceContinuousCanonicalCompatibility.ofTameNonflat
    {M : Type} [PseudoMetricSpace M] [LocPathConnectedSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (hs : 0 < s) (hnonflat : GraphEdgeNonflat G fhat)
    (hshort : ShortPathSound M δ) :
    SlackIncidenceContinuousCanonicalCompatibility h s where
  slack_nonneg := hs.le
  incidence_band_coverage :=
    h.canonicalNodeIncidenceBandCoverageAt_of_tame_of_nonflat hs hnonflat
  short_path_sound := hshort

/-- Geometric interface after completely discharging finite incidence
canonicalization.  Only continuum Reeb path lifting, non-flat observed graph
edges, and local ambient short paths remain. -/
structure ReebLiftNonflatContinuousCanonicalCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop where
  quotient_path_lift : ContinuumReebBandPathLift M f
  edge_nonflat : GraphEdgeNonflat G fhat
  short_path_sound : ShortPathSound M δ

/-- A single continuous section of the continuum Reeb quotient supplies the
quotient path lift for every finite sample.  Edge nonflatness and short paths
remain sample-dependent geometric facts, not tuning parameters. -/
def ReebLiftNonflatContinuousCanonicalCompatibility.ofSection
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (reebSection : ContinuumReebSection M f)
    (hnonflat : GraphEdgeNonflat G fhat)
    (hshort : ShortPathSound M δ) :
    ReebLiftNonflatContinuousCanonicalCompatibility h where
  quotient_path_lift := reebSection.bandPathLift
  edge_nonflat := hnonflat
  short_path_sound := hshort

theorem ReebLiftNonflatContinuousCanonicalCompatibility.toIncidence
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (hcompat : ReebLiftNonflatContinuousCanonicalCompatibility h) :
    IncidenceContinuousCanonicalCompatibility h where
  incidence_band_coverage :=
    h.canonicalNodeIncidenceBandCoverage_of_reebLift_of_nonflat
      hcompat.quotient_path_lift hcompat.edge_nonflat
  short_path_sound := hcompat.short_path_sound

def IncidenceContinuousCanonicalMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  FunctionalGHMapBandCompatibility
    (discreteReebRealization V G fhat) (continuumReebGraph M f)
    (incidenceContinuousCanonicalComparisonError L r δ η q)
    h.continuousDiscreteToContinuumMap h.continuumToDiscreteMap

def SlackIncidenceContinuousCanonicalMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (s : ℝ) : Prop :=
  FunctionalGHMapBandCompatibility
    (discreteReebRealization V G fhat) (continuumReebGraph M f)
    (slackIncidenceContinuousCanonicalComparisonError L r δ η q s)
    h.continuousDiscreteToContinuumMap h.continuumToDiscreteMap

theorem SlackIncidenceContinuousCanonicalCompatibility.toMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (hcompat : SlackIncidenceContinuousCanonicalCompatibility h s) :
    SlackIncidenceContinuousCanonicalMapBandCompatibility h s := by
  let E := continuousCanonicalComparisonError L r δ η q
  have hE : 0 ≤ E := h.continuousCanonicalComparisonError_nonneg
  have hR : 0 ≤ 4 * E + s := by linarith [hcompat.slack_nonneg]
  have hEleR : continuousCanonicalComparisonError L r δ η q ≤ 4 * E + s := by
    change E ≤ 4 * E + s
    linarith [hcompat.slack_nonneg]
  have hmap := functionalGHMapBandCompatibility_of_imageBandReflection
    (X := discreteReebRealization V G fhat) (Y := continuumReebGraph M f)
    (e := 4 * E + s) (φ := h.continuousDiscreteToContinuumMap)
    (ψ := h.continuumToDiscreteMap) hR
    (by
      intro a b x x' _hab hxx'
      exact HeightBandJoined.mono
        (h.continuousDiscreteToContinuumMap_band_common hxx')
        (by linarith [hEleR]) (by linarith [hEleR]))
    (fun y ↦ (h.continuumToDiscreteMap_height_close_continuousCommon y).trans
      hEleR)
    (fun y ↦ HeightBandJoined.mono
      (h.continuousContinuumRoundtrip_band_of_shortPathSound
        hcompat.short_path_sound y)
      (by linarith [hEleR]) (by linarith [hEleR]))
    (by
      intro a b x y hab hxy
      have hreflect := h.imageBandReflection_three_add_of_incidenceCoverageAt
        (add_nonneg hE hcompat.slack_nonneg)
        hcompat.incidence_band_coverage hab hxy
      convert hreflect using 1 <;> simp only [E] <;> ring)
  simpa only [SlackIncidenceContinuousCanonicalMapBandCompatibility,
    slackIncidenceContinuousCanonicalComparisonError, E] using hmap

/-- The CW endpoint anchoring theorem converts active-incidence coverage into
the complete two-map band compatibility required by functional GH distance. -/
theorem IncidenceContinuousCanonicalCompatibility.toMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (hcompat : IncidenceContinuousCanonicalCompatibility h) :
    IncidenceContinuousCanonicalMapBandCompatibility h := by
  let E := continuousCanonicalComparisonError L r δ η q
  have hE : 0 ≤ E := h.continuousCanonicalComparisonError_nonneg
  have hmap := functionalGHMapBandCompatibility_of_imageBandReflection
    (X := discreteReebRealization V G fhat) (Y := continuumReebGraph M f)
    (e := 4 * E) (φ := h.continuousDiscreteToContinuumMap)
    (ψ := h.continuumToDiscreteMap)
    (mul_nonneg (by norm_num) hE)
    (by
      intro a b x x' hab hxx'
      exact HeightBandJoined.mono
        (h.continuousDiscreteToContinuumMap_band_common hxx')
        (by linarith) (by linarith))
    (fun y ↦ (h.continuumToDiscreteMap_height_close_continuousCommon y).trans
      (by linarith))
    (fun y ↦ HeightBandJoined.mono
      (h.continuousContinuumRoundtrip_band_of_shortPathSound
        hcompat.short_path_sound y)
      (by linarith) (by linarith))
    (fun hab hxy ↦
      h.imageBandReflection_four_of_incidenceCoverage
        hcompat.incidence_band_coverage hab hxy)
  simpa only [IncidenceContinuousCanonicalMapBandCompatibility,
    incidenceContinuousCanonicalComparisonError, E] using hmap

theorem ApproximationHypotheses.incidenceContinuousComparisonError_nonneg
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ incidenceContinuousCanonicalComparisonError L r δ η q := by
  unfold incidenceContinuousCanonicalComparisonError
  exact mul_nonneg (by norm_num)
    (mul_nonneg (by norm_num) h.continuousCanonicalComparisonError_nonneg)

noncomputable def ApproximationHypotheses.incidenceContinuousFunctionalGHBandCertificate
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcompat : IncidenceContinuousCanonicalCompatibility h) :
    FunctionalGHBandCertificate (discreteReebRealization V G fhat)
      (continuumReebGraph M f)
      (incidenceContinuousCanonicalComparisonError L r δ η q) := by
  let hmap := hcompat.toMapBandCompatibility
  have hbaseLe : continuousCanonicalComparisonError L r δ η q ≤
      incidenceContinuousCanonicalComparisonError L r δ η q := by
    unfold incidenceContinuousCanonicalComparisonError
    have he := h.continuousCanonicalComparisonError_nonneg
    linarith
  exact
    { error_nonneg := h.incidenceContinuousComparisonError_nonneg
      toFun := h.continuousDiscreteToContinuumMap
      invFun := h.continuumToDiscreteMap
      height_to := fun x ↦
        (h.continuousDiscreteToContinuumMap_height_close x).trans
          ((le_max_right _ _).trans hbaseLe)
      height_inv := fun y ↦
        (h.continuumToDiscreteMap_height_close_continuousCommon y).trans hbaseLe
      band_to := hmap.band_to_full
      band_inv := hmap.band_inv_full }

theorem ApproximationHypotheses.reebDist_le_incidenceContinuousComparisonError
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcompat : IncidenceContinuousCanonicalCompatibility h) :
    reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
      ENNReal.ofReal
        (incidenceContinuousCanonicalComparisonError L r δ η q) :=
  functionalGHDistance_le_of_band_certificate
    (h.incidenceContinuousFunctionalGHBandCertificate hcompat)

theorem ApproximationHypotheses.slackIncidenceContinuousComparisonError_nonneg
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hs : 0 ≤ s) :
    0 ≤ slackIncidenceContinuousCanonicalComparisonError L r δ η q s := by
  unfold slackIncidenceContinuousCanonicalComparisonError
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (mul_nonneg (by norm_num) h.continuousCanonicalComparisonError_nonneg) hs)

noncomputable def ApproximationHypotheses.slackIncidenceContinuousFunctionalGHBandCertificate
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcompat : SlackIncidenceContinuousCanonicalCompatibility h s) :
    FunctionalGHBandCertificate (discreteReebRealization V G fhat)
      (continuumReebGraph M f)
      (slackIncidenceContinuousCanonicalComparisonError L r δ η q s) := by
  let hmap := hcompat.toMapBandCompatibility
  have hbaseLe : continuousCanonicalComparisonError L r δ η q ≤
      slackIncidenceContinuousCanonicalComparisonError L r δ η q s := by
    unfold slackIncidenceContinuousCanonicalComparisonError
    have hE := h.continuousCanonicalComparisonError_nonneg
    linarith [hcompat.slack_nonneg]
  exact
    { error_nonneg :=
        h.slackIncidenceContinuousComparisonError_nonneg hcompat.slack_nonneg
      toFun := h.continuousDiscreteToContinuumMap
      invFun := h.continuumToDiscreteMap
      height_to := fun x ↦
        (h.continuousDiscreteToContinuumMap_height_close x).trans
          ((le_max_right _ _).trans hbaseLe)
      height_inv := fun y ↦
        (h.continuumToDiscreteMap_height_close_continuousCommon y).trans hbaseLe
      band_to := hmap.band_to_full
      band_inv := hmap.band_inv_full }

theorem ApproximationHypotheses.reebDist_le_slackIncidenceContinuousComparisonError
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcompat : SlackIncidenceContinuousCanonicalCompatibility h s) :
    reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
      ENNReal.ofReal
        (slackIncidenceContinuousCanonicalComparisonError L r δ η q s) :=
  functionalGHDistance_le_of_band_certificate
    (h.slackIncidenceContinuousFunctionalGHBandCertificate hcompat)

/-- All remaining geometric content after deriving the continuous forward
map.  Forward band preservation is deliberately absent because it is now a
theorem above. -/
structure ContinuousCanonicalGeometricBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop where
  quotient_path_lift : ContinuumReebBandPathLift M f
  manifold_transition_complete :
    ContinuousCanonicalManifoldBandTransitionComplete h
  discrete_roundtrip : ∀ x,
    HeightBandJoined (discreteReebRealization V G fhat)
      ((continuumReebGraph M f).height
          (h.continuousDiscreteToContinuumMap x) -
        continuousCanonicalComparisonError L r δ η q)
      ((continuumReebGraph M f).height
          (h.continuousDiscreteToContinuumMap x) +
        continuousCanonicalComparisonError L r δ η q)
      x (h.continuumToDiscreteMap (h.continuousDiscreteToContinuumMap x))
  short_path_sound : ShortPathSound M δ

/-- Constructor exposing a continuous Reeb section as a sufficient, concrete
replacement for the quotient path-lifting field. -/
def ContinuousCanonicalGeometricBandCompatibility.ofSection
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (reebSection : ContinuumReebSection M f)
    (htransition : ContinuousCanonicalManifoldBandTransitionComplete h)
    (hroundtrip : ∀ x,
      HeightBandJoined (discreteReebRealization V G fhat)
        ((continuumReebGraph M f).height
            (h.continuousDiscreteToContinuumMap x) -
          continuousCanonicalComparisonError L r δ η q)
        ((continuumReebGraph M f).height
            (h.continuousDiscreteToContinuumMap x) +
          continuousCanonicalComparisonError L r δ η q)
        x (h.continuumToDiscreteMap (h.continuousDiscreteToContinuumMap x)))
    (hshort : ShortPathSound M δ) :
    ContinuousCanonicalGeometricBandCompatibility h where
  quotient_path_lift := reebSection.bandPathLift
  manifold_transition_complete := htransition
  discrete_roundtrip := hroundtrip
  short_path_sound := hshort

def ContinuousCanonicalMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  FunctionalGHMapBandCompatibility
    (discreteReebRealization V G fhat) (continuumReebGraph M f)
    (continuousCanonicalComparisonError L r δ η q)
    h.continuousDiscreteToContinuumMap h.continuumToDiscreteMap

theorem ContinuousCanonicalGeometricBandCompatibility.toMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (hgeo : ContinuousCanonicalGeometricBandCompatibility h) :
    ContinuousCanonicalMapBandCompatibility h := by
  refine
    { band_to_map := ?_
      band_inv_map := ?_
      roundtrip_X := hgeo.discrete_roundtrip
      roundtrip_Y := ?_ }
  · intro a b x x' _hab hxx'
    have hforward := h.continuousDiscreteToContinuumMap_band hxx'
    exact HeightBandJoined.mono hforward
      (by
        unfold continuousCanonicalComparisonError
        linarith [le_max_right
          (approximationComparisonError L r δ η q + L * δ)
          (continuousForwardError L r η q)])
      (by
        unfold continuousCanonicalComparisonError
        linarith [le_max_right
          (approximationComparisonError L r δ η q + L * δ)
          (continuousForwardError L r η q)])
  · intro a b y y' hab hyy'
    rcases hgeo.quotient_path_lift hyy' with ⟨p, p', hp, hp', hpath⟩
    have htransition := hgeo.manifold_transition_complete hab hpath
    rw [hp, hp'] at htransition
    exact htransition
  · intro y
    rcases h.continuousContinuumRoundtrip_of_shortPathSound
        hgeo.short_path_sound y with
      ⟨p, p', hp, hp', hpath⟩
    have hprojected := joinedIn_continuumReebQuotientMap hpath
    rw [hp, hp'] at hprojected
    exact hprojected

/-- The continuous support map and the four remaining geometric conditions
produce a standard functional-GH band certificate. -/
noncomputable def ApproximationHypotheses.continuousFunctionalGHBandCertificate
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hgeo : ContinuousCanonicalGeometricBandCompatibility h) :
    FunctionalGHBandCertificate (discreteReebRealization V G fhat)
      (continuumReebGraph M f)
      (continuousCanonicalComparisonError L r δ η q) := by
  let hmap := hgeo.toMapBandCompatibility
  exact
    { error_nonneg := h.continuousCanonicalComparisonError_nonneg
      toFun := h.continuousDiscreteToContinuumMap
      invFun := h.continuumToDiscreteMap
      height_to := fun x ↦
        (h.continuousDiscreteToContinuumMap_height_close x).trans
          (le_max_right _ _)
      height_inv := fun y ↦ by
        apply (h.continuumToDiscreteMap_height_close y).trans
        have hLδ : 0 ≤ L * δ :=
          mul_nonneg h.lipschitz_constant_nonneg h.sampling_scale_nonneg
        exact (le_add_of_nonneg_right hLδ).trans (le_max_left _ _)
      band_to := hmap.band_to_full
      band_inv := hmap.band_inv_full }

theorem ApproximationHypotheses.reebDist_le_continuousComparisonError
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hgeo : ContinuousCanonicalGeometricBandCompatibility h) :
    reebDist (discreteReebRealization V G fhat) (continuumReebGraph M f) ≤
      ENNReal.ofReal (continuousCanonicalComparisonError L r δ η q) :=
  functionalGHDistance_le_of_band_certificate
    (h.continuousFunctionalGHBandCertificate hgeo)

end ReebGraph
