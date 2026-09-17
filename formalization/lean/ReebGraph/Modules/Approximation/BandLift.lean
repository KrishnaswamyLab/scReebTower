import ReebGraph.Modules.BandCertificate
import ReebGraph.Modules.Approximation.Core

/-!
# Band-path lifting

Lifting Reeb-band paths back to the domain -- the one place where the
topology of the continuum really enters.

Main result: `continuumReebBandPathLiftWithSlack_of_tame` -- on a locally
path-connected domain with tame level fibers, every Reeb band path lifts
after an arbitrarily small enlargement of the band.  This is what removes
any need for a global Reeb section or a Morse lemma.

Supporting: connected-fiber lemmas for the quotient map, the
`ContinuumReebSection` interface, and the canonical geometric/map band
compatibility conversions.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- The one remaining estimator-specific condition: for the two canonical
support maps, band paths are preserved in both directions after expansion by
the common comparison error. -/
structure CanonicalBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop where
  band_to : ∀
    {x x' : (discreteReebRealization V G fhat).Carrier}
    {y y' : (continuumReebGraph M f).Carrier} {a b : ℝ},
    FunctionalGHRel (discreteReebRealization V G fhat) (continuumReebGraph M f)
      h.discreteToContinuumMap h.continuumToDiscreteMap x y →
    FunctionalGHRel (discreteReebRealization V G fhat) (continuumReebGraph M f)
      h.discreteToContinuumMap h.continuumToDiscreteMap x' y' →
    a ≤ b → HeightBandJoined (discreteReebRealization V G fhat) a b x x' →
    HeightBandJoined (continuumReebGraph M f)
      (a - approximationComparisonError L r δ η q)
      (b + approximationComparisonError L r δ η q) y y'
  band_inv : ∀
    {x x' : (discreteReebRealization V G fhat).Carrier}
    {y y' : (continuumReebGraph M f).Carrier} {a b : ℝ},
    FunctionalGHRel (discreteReebRealization V G fhat) (continuumReebGraph M f)
      h.discreteToContinuumMap h.continuumToDiscreteMap x y →
    FunctionalGHRel (discreteReebRealization V G fhat) (continuumReebGraph M f)
      h.discreteToContinuumMap h.continuumToDiscreteMap x' y' →
    a ≤ b → HeightBandJoined (continuumReebGraph M f) a b y y' →
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - approximationComparisonError L r δ η q)
      (b + approximationComparisonError L r δ η q) x x'

/-- Every band path in the continuum Reeb quotient admits a band-preserving
lift to the original space.  This is a manifold/Reeb-quotient regularity
condition and is intentionally separate from finite graph adequacy. -/
def ContinuumReebBandPathLift
    (M : Type) [TopologicalSpace M] (f : M → ℝ) : Prop :=
  ∀ {a b : ℝ} {y y' : (continuumReebGraph M f).Carrier},
    HeightBandJoined (continuumReebGraph M f) a b y y' →
    ∃ x x' : M,
      continuumReebQuotientMap f x = y ∧
      continuumReebQuotientMap f x' = y' ∧
      JoinedIn {z | a ≤ f z ∧ f z ≤ b} x x'

/-- The convergence argument only needs a lift after a controlled scalar
enlargement.  Unlike an exact global section, this property follows from
standard quotient topology for every positive slack. -/
def ContinuumReebBandPathLiftWithSlack
    (M : Type) [TopologicalSpace M] (f : M → ℝ) (s : ℝ) : Prop :=
  ∀ {a b : ℝ} {y y' : (continuumReebGraph M f).Carrier},
    HeightBandJoined (continuumReebGraph M f) a b y y' →
    ∃ x x' : M,
      continuumReebQuotientMap f x = y ∧
      continuumReebQuotientMap f x' = y' ∧
      JoinedIn {z | a - s ≤ f z ∧ f z ≤ b + s} x x'

/-- A Reeb fiber is exactly the connected component of one scalar level. -/
theorem continuumReebQuotientMap_fiber_eq_connectedComponentIn
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x : M) :
    continuumReebQuotientMap f ⁻¹' {continuumReebQuotientMap f x} =
      connectedComponentIn {z | f z = f x} x := by
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [continuumReebQuotientMap_eq_iff]
  constructor
  · intro h
    exact (sameLevelComponent_symm f h).2
  · intro hz
    have hzLevel : z ∈ {w | f w = f x} :=
      connectedComponentIn_subset {w | f w = f x} x hz
    have hfzx : f z = f x := hzLevel
    exact sameLevelComponent_symm f ⟨hfzx.symm, hz⟩

theorem continuumReebQuotientMap_connected_fibers
    {M : Type} [TopologicalSpace M] (f : M → ℝ)
    (y : ContinuumReebQuotient M f) :
    IsConnected (continuumReebQuotientMap f ⁻¹' {y}) := by
  rcases continuumReebQuotientMap_surjective f y with ⟨x, rfl⟩
  rw [continuumReebQuotientMap_fiber_eq_connectedComponentIn]
  exact isConnected_connectedComponentIn_iff.mpr rfl


/-- On a locally path-connected domain with tame level fibers, every Reeb
band path lifts after any positive scalar enlargement.  The proof restricts
the Reeb quotient map to the enlarged open band, uses connected fibers to
pull back connected components, and then turns connectedness into a path. -/
theorem continuumReebBandPathLiftWithSlack_of_tame
    (M : Type) [TopologicalSpace M] [LocPathConnectedSpace M]
    (f : M → ℝ) (htame : TameLevelSetFunction M f)
    {s : ℝ} (hs : 0 < s) : ContinuumReebBandPathLiftWithSlack M f s := by
  intro a b y y' hyy'
  let X := continuumReebGraph M f
  let q : M → X.Carrier := continuumReebQuotientMap f
  let U : Set X.Carrier :=
    {z | a - s < X.height z ∧ X.height z < b + s}
  have hheight : Continuous X.height :=
    continuous_continuumReebGraph_height htame.continuous
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const hheight).inter
      (isOpen_lt hheight continuous_const)
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  have hyBand := hyy'.source_mem
  have hy'Band := hyy'.target_mem
  have hyU : y ∈ U := by
    change a - s < X.height y ∧ X.height y < b + s
    constructor <;> linarith [hyBand.1, hyBand.2]
  have hy'U : y' ∈ U := by
    change a - s < X.height y' ∧ X.height y' < b + s
    constructor <;> linarith [hy'Band.1, hy'Band.2]
  let yu : U := ⟨y, hyU⟩
  let yu' : U := ⟨y', hy'U⟩
  let qU : q ⁻¹' U → U := U.restrictPreimage q
  have hqU : Topology.IsQuotientMap qU := hq.restrictPreimage_isOpen hUopen
  have hsourceOpen : IsOpen (q ⁻¹' U) := hUopen.preimage hq.continuous
  letI : LocPathConnectedSpace (q ⁻¹' U) := hsourceOpen.locPathConnectedSpace
  have hqU_fibers : ∀ z : U, IsConnected (qU ⁻¹' {z}) := by
    intro z
    have hfiber : IsConnected (q ⁻¹' ({z.1} : Set X.Carrier)) :=
      continuumReebQuotientMap_connected_fibers f z.1
    have hfiberU : q ⁻¹' ({z.1} : Set X.Carrier) ⊆ q ⁻¹' U := by
      intro x hx
      change q x ∈ U
      have hxq : q x = z.1 := hx
      rw [hxq]
      exact z.2
    have hrestricted := isConnected_preimage_subtypeVal hfiber hfiberU
    have heq : qU ⁻¹' {z} =
        ((↑) : q ⁻¹' U → M) ⁻¹' (q ⁻¹' ({z.1} : Set X.Carrier)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact congrArg Subtype.val hx
      · intro hx
        exact Subtype.ext hx
    rw [heq]
    exact hrestricted
  rcases hqU.surjective yu with ⟨xu, hxu⟩
  rcases hqU.surjective yu' with ⟨xu', hxu'⟩
  have hyyU : Joined yu yu' := by
    have hyyOpen : JoinedIn U y y' := by
      apply JoinedIn.mono hyy'
      intro z hz
      change a - s < X.height z ∧ X.height z < b + s
      constructor <;> linarith [hz.1, hz.2]
    exact hyyOpen.joined_subtype
  have hyu'Component : yu' ∈ connectedComponent yu :=
    pathComponent_subset_component yu
      (show yu' ∈ pathComponent yu from hyyU)
  have hxu'Component : xu' ∈ connectedComponent xu := by
    rw [← hqU.preimage_connectedComponent hqU_fibers xu]
    change qU xu' ∈ connectedComponent (qU xu)
    rw [hxu, hxu']
    exact hyu'Component
  have hjoinedSource : Joined xu xu' := by
    rw [← mem_pathComponent_iff, pathComponent_eq_connectedComponent]
    exact hxu'Component
  refine ⟨xu.1, xu'.1, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hxu
  · exact congrArg Subtype.val hxu'
  · refine ⟨hjoinedSource.somePath.map continuous_subtype_val, ?_⟩
    intro t
    have ht := (hjoinedSource.somePath t).2
    change q (hjoinedSource.somePath t).1 ∈ U at ht
    change a - s ≤ f (hjoinedSource.somePath t).1 ∧
      f (hjoinedSource.somePath t).1 ≤ b + s
    change a - s < f (hjoinedSource.somePath t).1 ∧
      f (hjoinedSource.somePath t).1 < b + s at ht
    exact ⟨ht.1.le, ht.2.le⟩

/-- A continuous choice of one manifold representative in every Reeb fiber.
Constructing such a section from Morse handles is a concrete sufficient target
for quotient path lifting. -/
structure ContinuumReebSection
    (M : Type) [TopologicalSpace M] (f : M → ℝ) where
  toFun : (continuumReebGraph M f).Carrier → M
  continuous_toFun : Continuous toFun
  right_inv : ∀ y, continuumReebQuotientMap f (toFun y) = y

theorem ContinuumReebSection.height_toFun
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (s : ContinuumReebSection M f)
    (y : (continuumReebGraph M f).Carrier) :
    f (s.toFun y) = (continuumReebGraph M f).height y := by
  calc
    f (s.toFun y) = (continuumReebGraph M f).height
        (continuumReebQuotientMap f (s.toFun y)) := rfl
    _ = (continuumReebGraph M f).height y :=
      congrArg (continuumReebGraph M f).height (s.right_inv y)

/-- A continuous Reeb section lifts scalar-band paths without any enlargement. -/
theorem ContinuumReebSection.bandPathLift
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (s : ContinuumReebSection M f) : ContinuumReebBandPathLift M f := by
  intro a b y y' hyy'
  refine ⟨s.toFun y, s.toFun y', s.right_inv y, s.right_inv y', ?_⟩
  refine ⟨hyy'.somePath.map s.continuous_toFun, ?_⟩
  intro t
  change a ≤ f (s.toFun (hyy'.somePath t)) ∧
    f (s.toFun (hyy'.somePath t)) ≤ b
  rw [s.height_toFun]
  exact hyy'.somePath_mem t

/-- A discrete band path can be represented by a manifold path between
representatives of its two canonical support-map images. -/
def CanonicalForwardBandRealizable
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {x x' : (discreteReebRealization V G fhat).Carrier},
    a ≤ b → HeightBandJoined (discreteReebRealization V G fhat) a b x x' →
    ∃ p p' : M,
      continuumReebQuotientMap f p = h.discreteToContinuumMap x ∧
      continuumReebQuotientMap f p' = h.discreteToContinuumMap x' ∧
      JoinedIn {z |
        a - approximationComparisonError L r δ η q ≤ f z ∧
        f z ≤ b + approximationComparisonError L r δ η q} p p'

/-- A manifold band path is carried by the canonical transition graph between
the reverse-map images of its endpoints. -/
def CanonicalManifoldBandTransitionComplete
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {p p' : M}, a ≤ b →
    JoinedIn {z | a ≤ f z ∧ f z ≤ b} p p' →
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - approximationComparisonError L r δ η q)
      (b + approximationComparisonError L r δ η q)
      (h.continuumToDiscreteMap (continuumReebQuotientMap f p))
      (h.continuumToDiscreteMap (continuumReebQuotientMap f p'))

/-- The continuum round trip is realized by a path in the original space. -/
def CanonicalContinuumRoundtripRealizable
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ y : (continuumReebGraph M f).Carrier,
    ∃ p p' : M,
      continuumReebQuotientMap f p = y ∧
      continuumReebQuotientMap f p' =
        h.discreteToContinuumMap (h.continuumToDiscreteMap y) ∧
      JoinedIn {z |
        (discreteReebRealization V G fhat).height
            (h.continuumToDiscreteMap y) -
            approximationComparisonError L r δ η q ≤ f z ∧
        f z ≤ (discreteReebRealization V G fhat).height
            (h.continuumToDiscreteMap y) +
            approximationComparisonError L r δ η q} p p'

/-- Independently checkable geometric content sufficient for the comparison:
one quotient path-lift statement and four graph/path realization statements. -/
structure CanonicalGeometricBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop where
  quotient_path_lift : ContinuumReebBandPathLift M f
  forward_realizable : CanonicalForwardBandRealizable h
  manifold_transition_complete : CanonicalManifoldBandTransitionComplete h
  discrete_roundtrip : ∀ x,
    HeightBandJoined (discreteReebRealization V G fhat)
      ((continuumReebGraph M f).height (h.discreteToContinuumMap x) -
        approximationComparisonError L r δ η q)
      ((continuumReebGraph M f).height (h.discreteToContinuumMap x) +
        approximationComparisonError L r δ η q)
      x (h.continuumToDiscreteMap (h.discreteToContinuumMap x))
  continuum_roundtrip_realizable : CanonicalContinuumRoundtripRealizable h

/-- The decomposed form of the remaining condition: two mapwise band-lifting
statements and two round-trip statements. -/
def CanonicalMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  FunctionalGHMapBandCompatibility
    (discreteReebRealization V G fhat) (continuumReebGraph M f)
    (approximationComparisonError L r δ η q)
    h.discreteToContinuumMap h.continuumToDiscreteMap

theorem CanonicalGeometricBandCompatibility.toCanonicalMapBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (hgeo : CanonicalGeometricBandCompatibility h) :
    CanonicalMapBandCompatibility h := by
  change FunctionalGHMapBandCompatibility
    (discreteReebRealization V G fhat) (continuumReebGraph M f)
    (approximationComparisonError L r δ η q)
    h.discreteToContinuumMap h.continuumToDiscreteMap
  refine
    { band_to_map := ?_
      band_inv_map := ?_
      roundtrip_X := hgeo.discrete_roundtrip
      roundtrip_Y := ?_ }
  · intro a b x x' hab hxx'
    rcases hgeo.forward_realizable hab hxx' with
      ⟨p, p', hp, hp', hpath⟩
    have hprojected := joinedIn_continuumReebQuotientMap hpath
    rw [hp, hp'] at hprojected
    exact hprojected
  · intro a b y y' hab hyy'
    rcases hgeo.quotient_path_lift hyy' with
      ⟨p, p', hp, hp', hpath⟩
    have htransition := hgeo.manifold_transition_complete hab hpath
    rw [hp, hp'] at htransition
    exact htransition
  · intro y
    rcases hgeo.continuum_roundtrip_realizable y with
      ⟨p, p', hp, hp', hpath⟩
    have hprojected := joinedIn_continuumReebQuotientMap hpath
    rw [hp, hp'] at hprojected
    exact hprojected

theorem CanonicalMapBandCompatibility.toCanonicalBandCompatibility
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    {h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q}
    (hmap : CanonicalMapBandCompatibility h) : CanonicalBandCompatibility h := by
  change FunctionalGHMapBandCompatibility
    (discreteReebRealization V G fhat) (continuumReebGraph M f)
    (approximationComparisonError L r δ η q)
    h.discreteToContinuumMap h.continuumToDiscreteMap at hmap
  exact
    { band_to := hmap.band_to_full
      band_inv := hmap.band_inv_full }

end ReebGraph
