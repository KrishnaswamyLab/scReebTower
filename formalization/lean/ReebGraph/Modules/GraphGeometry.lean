import ReebGraph.Modules.HeightBand

/-!
# Neighborhood-graph geometry

Geometry of the neighborhood graph: thickenings, bounded-radius
reachability, and the soundness/completeness interface that makes the
consistency theorem graph-agnostic.

Main results: `graph_geometry_of_proximity_sandwich` (a two-sided
proximity sandwich plus dense sampling gives both soundness and
completeness), `graphComplete_of_sampleDense_of_containsProximityGraph`,
`GraphComplete.lift_joinedIn`, and `radiusGraph_sandwich` /
`KNNGraphCertificate.sandwich` as the concrete instantiations.

Supporting: the `GraphReachableWithin` and `MetricThickening` calculus,
and the canonical-incidence reachability lemmas with explicit radii.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-- Closed metric thickening of a subset. -/
def MetricThickening
    {M : Type*} [PseudoMetricSpace M] (S : Set M) (ρ : ℝ) : Set M :=
  {y | ∃ x ∈ S, dist y x ≤ ρ}

/-- Reachability by a graph walk all of whose vertices satisfy `P`. -/
def GraphReachableWithin
    {V : Type*} (G : SimpleGraph V) (P : V → Prop) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ w, w ∈ p.support → P w

theorem GraphReachableWithin.refl
    {V : Type*} {G : SimpleGraph V} {P : V → Prop} {u : V} (hu : P u) :
    GraphReachableWithin G P u u := by
  refine ⟨.nil, ?_⟩
  intro w hw
  have hwu : w = u := by
    simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hw
  simpa [hwu] using hu

theorem GraphReachableWithin.symm
    {V : Type*} {G : SimpleGraph V} {P : V → Prop} {u v : V}
    (h : GraphReachableWithin G P u v) :
    GraphReachableWithin G P v u := by
  rcases h with ⟨p, hp⟩
  refine ⟨p.reverse, ?_⟩
  intro w hw
  apply hp w
  simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hw

theorem GraphReachableWithin.trans
    {V : Type*} {G : SimpleGraph V} {P : V → Prop} {u v w : V}
    (huv : GraphReachableWithin G P u v)
    (hvw : GraphReachableWithin G P v w) :
    GraphReachableWithin G P u w := by
  rcases huv with ⟨p, hp⟩
  rcases hvw with ⟨q, hq⟩
  refine ⟨p.append q, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx
  exact hx.elim (hp x) (hq x)

theorem GraphReachableWithin.source_mem
    {V : Type*} {G : SimpleGraph V} {P : V → Prop} {u v : V}
    (h : GraphReachableWithin G P u v) : P u := by
  rcases h with ⟨p, hp⟩
  exact hp u p.start_mem_support

theorem GraphReachableWithin.target_mem
    {V : Type*} {G : SimpleGraph V} {P : V → Prop} {u v : V}
    (h : GraphReachableWithin G P u v) : P v := by
  rcases h with ⟨p, hp⟩
  exact hp v p.end_mem_support

theorem GraphReachableWithin.reachable
    {V : Type*} {G : SimpleGraph V} {P : V → Prop} {u v : V}
    (h : GraphReachableWithin G P u v) : G.Reachable u v := by
  rcases h with ⟨p, _⟩
  exact ⟨p⟩

theorem GraphReachableWithin.mono
    {V : Type*} {G : SimpleGraph V} {P Q : V → Prop} {u v : V}
    (h : GraphReachableWithin G P u v) (hPQ : ∀ w, P w → Q w) :
    GraphReachableWithin G Q u v := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, fun w hw => hPQ w (hp w hw)⟩

/-- One equality-or-edge step between vertices satisfying `P` gives
reachability within `P`.  The equality case is needed for proximity graphs,
whose adjacency relation is irreflexive. -/
theorem GraphReachableWithin.of_eq_or_adj
    {V : Type*} {G : SimpleGraph V} {P : V → Prop} {u v : V}
    (hu : P u) (hv : P v) (huv : u = v ∨ G.Adj u v) :
    GraphReachableWithin G P u v := by
  rcases huv with rfl | huv
  · exact GraphReachableWithin.refl hu
  · refine ⟨.cons huv .nil, ?_⟩
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    exact hw.elim (fun hwu ↦ hwu ▸ hu) (fun hwv ↦ hwv ▸ hv)

/-- Quantitative vertical form of canonical vertex activity coherence. -/
theorem canonicalActiveIncidence_vertical_reachableWithin
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) (u : V)
    {A B : ℝ} {i j : Fin (canonicalMidpoints f).length} (hij : i ≤ j)
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) u)
    (hiBand : A ≤ canonicalThreshold f i ∧ canonicalThreshold f i ≤ B)
    (hjBand : A ≤ canonicalThreshold f j ∧ canonicalThreshold f j ≤ B) :
    GraphReachableWithin (canonicalActiveIncidenceGraph G f)
      (fun z ↦ A ≤ canonicalThreshold f z.1 ∧
        canonicalThreshold f z.1 ≤ B)
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨u, hj⟩⟩ := by
  have aux : ∀ d : ℕ, ∀ (i j : Fin (canonicalMidpoints f).length),
      j.1 = i.1 + d →
      ∀ (hi : IsActiveVertex G f (canonicalThreshold f i) u)
        (hj : IsActiveVertex G f (canonicalThreshold f j) u),
        (A ≤ canonicalThreshold f i ∧ canonicalThreshold f i ≤ B) →
        (A ≤ canonicalThreshold f j ∧ canonicalThreshold f j ≤ B) →
        GraphReachableWithin (canonicalActiveIncidenceGraph G f)
          (fun z ↦ A ≤ canonicalThreshold f z.1 ∧
            canonicalThreshold f z.1 ≤ B)
          ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨u, hj⟩⟩ := by
    intro d
    induction d with
    | zero =>
        intro i j hval hi hj hiBand hjBand
        have hijEq : i = j := Fin.ext (by omega)
        subst j
        have hbase : GraphReachableWithin (canonicalActiveIncidenceGraph G f)
            (fun z ↦ A ≤ canonicalThreshold f z.1 ∧
              canonicalThreshold f z.1 ≤ B)
            ⟨i, ⟨u, hi⟩⟩ ⟨i, ⟨u, hi⟩⟩ :=
          GraphReachableWithin.refl hiBand
        simpa using hbase
    | succ d ih =>
        intro i j hval hi hj hiBand hjBand
        let k : Fin (canonicalMidpoints f).length :=
          ⟨i.1 + d, by omega⟩
        have hik : i ≤ k := by
          change i.1 ≤ i.1 + d
          omega
        have hkj : k ≤ j := by
          change i.1 + d ≤ j.1
          omega
        have hk : IsActiveVertex G f (canonicalThreshold f k) u :=
          isActiveVertex_between G f
            (canonicalThreshold_mono f hik)
            (canonicalThreshold_mono f hkj) hi hj
        have hkBand : A ≤ canonicalThreshold f k ∧
            canonicalThreshold f k ≤ B := by
          constructor
          · exact hiBand.1.trans (canonicalThreshold_mono f hik)
          · exact (canonicalThreshold_mono f hkj).trans hjBand.2
        have hprev := ih i k (by simp [k]) hi hk hiBand hkBand
        have hsucc : k.1 + 1 = j.1 := by
          dsimp [k]
          omega
        have hadj : (canonicalActiveIncidenceGraph G f).Adj
            ⟨k, ⟨u, hk⟩⟩ ⟨j, ⟨u, hj⟩⟩ :=
          Or.inr ⟨Or.inl hsucc, rfl⟩
        have hstep : GraphReachableWithin (canonicalActiveIncidenceGraph G f)
            (fun z ↦ A ≤ canonicalThreshold f z.1 ∧
              canonicalThreshold f z.1 ≤ B)
            ⟨k, ⟨u, hk⟩⟩ ⟨j, ⟨u, hj⟩⟩ := by
          refine ⟨.cons hadj .nil, ?_⟩
          intro z hz
          simp only [SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons,
            List.mem_singleton] at hz
          rcases hz with rfl | hz
          · exact hkBand
          · rcases hz with rfl | hz
            · exact hjBand
            · exact (List.not_mem_nil _ hz).elim
        exact hprev.trans hstep
  apply aux (j.1 - i.1) i j (by omega) hi hj hiBand hjBand

/-- The symmetric quantitative vertical connection. -/
theorem canonicalActiveIncidence_vertical_reachableWithin_any
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) (u : V)
    {A B : ℝ} {i j : Fin (canonicalMidpoints f).length}
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) u)
    (hiBand : A ≤ canonicalThreshold f i ∧ canonicalThreshold f i ≤ B)
    (hjBand : A ≤ canonicalThreshold f j ∧ canonicalThreshold f j ≤ B) :
    GraphReachableWithin (canonicalActiveIncidenceGraph G f)
      (fun z ↦ A ≤ canonicalThreshold f z.1 ∧
        canonicalThreshold f z.1 ≤ B)
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨u, hj⟩⟩ := by
  by_cases hij : i ≤ j
  · exact canonicalActiveIncidence_vertical_reachableWithin
      G f u hij hi hj hiBand hjBand
  · exact (canonicalActiveIncidence_vertical_reachableWithin
      G f u (le_of_not_ge hij) hj hi hjBand hiBand).symm

/-- A non-flat original edge lifts inside any scalar slab containing both
endpoint values and the two prescribed endpoint slice heights. -/
theorem canonicalActiveIncidence_reachableWithin_of_adj_of_nonflat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ)
    (hnonflat : GraphEdgeNonflat G f)
    {A B : ℝ} {u v : V} (huv : G.Adj u v)
    {i j : Fin (canonicalMidpoints f).length}
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) v)
    (hiBand : A ≤ canonicalThreshold f i ∧ canonicalThreshold f i ≤ B)
    (hjBand : A ≤ canonicalThreshold f j ∧ canonicalThreshold f j ≤ B)
    (huBand : A ≤ f u ∧ f u ≤ B)
    (hvBand : A ≤ f v ∧ f v ≤ B) :
    GraphReachableWithin (canonicalActiveIncidenceGraph G f)
      (fun z ↦ A ≤ canonicalThreshold f z.1 ∧
        canonicalThreshold f z.1 ≤ B)
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨v, hj⟩⟩ := by
  rcases exists_common_canonicalActive_of_adj_of_nonflat G f hnonflat huv with
    ⟨k, huk, hvk, hkLower, hkUpper⟩
  have hkBand : A ≤ canonicalThreshold f k ∧
      canonicalThreshold f k ≤ B := by
    constructor
    · exact (le_min huBand.1 hvBand.1).trans hkLower
    · exact hkUpper.trans (max_le huBand.2 hvBand.2)
  have hleft := canonicalActiveIncidence_vertical_reachableWithin_any
    G f u hi huk hiBand hkBand
  have hright := canonicalActiveIncidence_vertical_reachableWithin_any
    G f v hvk hj hkBand hjBand
  have hadj : (canonicalActiveIncidenceGraph G f).Adj
      ⟨k, ⟨u, huk⟩⟩ ⟨k, ⟨v, hvk⟩⟩ :=
    Or.inl ⟨rfl, huv, huk, hvk⟩
  have hhorizontal : GraphReachableWithin (canonicalActiveIncidenceGraph G f)
      (fun z ↦ A ≤ canonicalThreshold f z.1 ∧
        canonicalThreshold f z.1 ≤ B)
      ⟨k, ⟨u, huk⟩⟩ ⟨k, ⟨v, hvk⟩⟩ := by
    refine ⟨.cons hadj .nil, ?_⟩
    intro z hz
    simp only [SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_singleton] at hz
    rcases hz with rfl | hz
    · exact hkBand
    · rcases hz with rfl | hz
      · exact hkBand
      · exact (List.not_mem_nil _ hz).elim
  exact hleft.trans (hhorizontal.trans hright)

/-- Every band-limited walk in a graph with non-flat scalar edges has a
band-limited lift to the canonical active-incidence graph. -/
theorem canonicalActiveIncidence_reachableWithin_of_walk_of_nonflat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ)
    (hnonflat : GraphEdgeNonflat G f)
    {A B : ℝ} {u v : V} (p : G.Walk u v)
    (hp : ∀ w, w ∈ p.support → A ≤ f w ∧ f w ≤ B)
    {i j : Fin (canonicalMidpoints f).length}
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) v)
    (hiBand : A ≤ canonicalThreshold f i ∧ canonicalThreshold f i ≤ B)
    (hjBand : A ≤ canonicalThreshold f j ∧ canonicalThreshold f j ≤ B) :
    GraphReachableWithin (canonicalActiveIncidenceGraph G f)
      (fun z ↦ A ≤ canonicalThreshold f z.1 ∧
        canonicalThreshold f z.1 ≤ B)
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨v, hj⟩⟩ := by
  induction p generalizing i with
  | @nil u =>
      exact canonicalActiveIncidence_vertical_reachableWithin_any
        G f u hi hj hiBand hjBand
  | @cons u v w huv p ih =>
      have huBand : A ≤ f u ∧ f u ≤ B := hp u (by simp)
      have hvBand : A ≤ f v ∧ f v ≤ B :=
        hp v (by simp [p.start_mem_support])
      rcases exists_common_canonicalActive_of_adj_of_nonflat G f hnonflat huv with
        ⟨k, huk, hvk, hkLower, hkUpper⟩
      have hkBand : A ≤ canonicalThreshold f k ∧
          canonicalThreshold f k ≤ B := by
        constructor
        · exact (le_min huBand.1 hvBand.1).trans hkLower
        · exact hkUpper.trans (max_le huBand.2 hvBand.2)
      have hfirst := canonicalActiveIncidence_reachableWithin_of_adj_of_nonflat
        G f hnonflat huv hi hvk hiBand hkBand huBand hvBand
      have hpTail : ∀ z, z ∈ p.support → A ≤ f z ∧ f z ≤ B := by
        intro z hz
        exact hp z (by simp [hz])
      exact hfirst.trans (ih hpTail hvk hj hkBand)

theorem MetricThickening.mono
    {M : Type*} [PseudoMetricSpace M] {S T : Set M} {ρ : ℝ}
    (hST : S ⊆ T) : MetricThickening S ρ ⊆ MetricThickening T ρ := by
  rintro y ⟨x, hxS, hyx⟩
  exact ⟨x, hST hxS, hyx⟩

theorem MetricThickening.subset
    {M : Type*} [PseudoMetricSpace M] {S : Set M} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    S ⊆ MetricThickening S ρ := by
  intro x hx
  exact ⟨x, hx, by simpa using hρ⟩

theorem MetricThickening.mono_radius
    {M : Type*} [PseudoMetricSpace M] {S : Set M} {ρ σ : ℝ}
    (hρσ : ρ ≤ σ) : MetricThickening S ρ ⊆ MetricThickening S σ := by
  rintro y ⟨x, hxS, hyx⟩
  exact ⟨x, hxS, hyx.trans hρσ⟩

theorem MetricThickening.thickening_subset_add
    {M : Type*} [PseudoMetricSpace M] {S : Set M} {ρ σ : ℝ} :
    MetricThickening (MetricThickening S ρ) σ ⊆
      MetricThickening S (ρ + σ) := by
  rintro y ⟨x, ⟨z, hzS, hxz⟩, hyx⟩
  refine ⟨z, hzS, ?_⟩
  calc
    dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ ≤ σ + ρ := add_le_add hyx hxz
    _ = ρ + σ := add_comm _ _

/-- Lipschitz scalar control on the metric thickening of a level band. -/
theorem mem_levelBand_of_mem_thickening
    {M : Type*} [PseudoMetricSpace M] (f : M → ℝ)
    {L a ρ t : ℝ} (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    {y : M} (hy : y ∈ MetricThickening {x | |f x - t| ≤ a} ρ) :
    |f y - t| ≤ a + L * ρ := by
  rcases hy with ⟨x, hxBand, hyx⟩
  calc
    |f y - t| = |(f y - f x) + (f x - t)| := by ring_nf
    _ ≤ |f y - f x| + |f x - t| := abs_add _ _
    _ ≤ L * dist y x + a := add_le_add (hL y x) hxBand
    _ ≤ L * ρ + a := by
      gcongr
    _ = a + L * ρ := add_comm _ _

/-- Graph edges are geometrically local at scale `r`. -/
def GraphSound
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M) (r : ℝ) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r

/-- The canonical proximity (Vietoris--Rips one-skeleton) graph of the sample
at radius `ρ`. -/
def proximityGraph
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (ρ : ℝ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ dist (sample u) (sample v) ≤ ρ
  symm _ _ h := ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩
  loopless _ h := h.1 rfl

/-! ### Radius-graph specialization -/

/-- The standard epsilon-neighborhood graph is the proximity graph used by the
graph-sandwich theorem.  This definition is intentionally just an alias: no
additional graph construction is hidden here. -/
def radiusGraph
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (epsilon : ℝ) : SimpleGraph V :=
  proximityGraph M V sample epsilon

/-- Lower half of the graph sandwich: all sufficiently close distinct sample
points are joined by an edge of `G`. -/
def ContainsProximityGraph
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M) (ρ : ℝ) : Prop :=
  proximityGraph M V sample ρ ≤ G

/-- A radius graph satisfies both sides of the graph sandwich at its defining
radius exactly. -/
theorem radiusGraph_sandwich
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (epsilon : ℝ) :
    ContainsProximityGraph M V (radiusGraph M V sample epsilon) sample epsilon ∧
      radiusGraph M V sample epsilon ≤ proximityGraph M V sample epsilon := by
  constructor
  · unfold ContainsProximityGraph radiusGraph
    exact le_rfl
  · unfold radiusGraph
    exact le_rfl

/-- The numerical scale choices used in the radius-graph corollary satisfy the
three geometric inequalities required by the consistency theorem. -/
theorem radiusGraph_scale_inequalities
    {a σ : ℝ} (hpos : 0 < a + σ) (ha : 0 ≤ a) (hσ : 0 ≤ σ) :
    2 * (a + σ) ≤ 5 * (a + σ) ∧
      a + σ ≤ 2 * (a + σ) ∧
      2 * (2 * (a + σ)) < 5 * (a + σ) := by
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-! ### k-nearest-neighbor graph interface -/

/-- A certificate that a finite k-nearest-neighbor graph has the two metric
scales required by the consistency theorem.  The integer `k` records the
neighbor budget; the radii `ρ` and `r` are consequences of the sampling
configuration and are not additional algorithmic parameters. -/
structure KNNGraphCertificate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) [Fintype V]
    (sample : V → M) where
  k : ℕ
  graph : SimpleGraph V
  lowerRadius : ℝ
  upperRadius : ℝ
  lower : ContainsProximityGraph M V graph sample lowerRadius
  upper : graph ≤ proximityGraph M V sample upperRadius

/-- The certified kNN graph satisfies the graph-sandwich hypotheses used by
the Reeb consistency theorem. -/
theorem KNNGraphCertificate.sandwich
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V]
    {sample : V → M}
    (c : KNNGraphCertificate M V sample) :
    ContainsProximityGraph M V c.graph sample c.lowerRadius ∧
      c.graph ≤ proximityGraph M V sample c.upperRadius := by
  exact ⟨c.lower, c.upper⟩

/-- Any certified kNN graph can be supplied directly to the packaged
consistency theorem: all remaining assumptions are exactly the analytic and
sampling hypotheses already exposed by `QuadraticGraphSandwichConsistencyHypotheses`.
This separates the kNN geometry from the Reeb proof. -/
theorem KNNGraphCertificate.uses_graph_sandwich
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V]
    {sample : V → M}
    (c : KNNGraphCertificate M V sample) :
    ContainsProximityGraph M V c.graph sample c.lowerRadius ∧
      c.graph ≤ proximityGraph M V sample c.upperRadius :=
  c.sandwich

/-- Every graph edge is realized by a continuum path that remains within `r`
of its first endpoint.  On a Riemannian manifold this is supplied by a
minimizing geodesic for every sufficiently short edge. -/
def EdgePathSound
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M) (r : ℝ) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v →
    ∃ γ : Path (sample u) (sample v), ∀ s, dist (γ s) (sample u) ≤ r

/-- Nearby ambient points can be joined without leaving the corresponding
metric ball.  A geodesic metric space satisfies this at every radius; a
compact Riemannian manifold satisfies it below its convexity radius. -/
def ShortPathSound
    (M : Type*) [PseudoMetricSpace M] (r : ℝ) : Prop :=
  ∀ ⦃x y : M⦄, dist x y ≤ r →
    ∃ γ : Path x y, ∀ s, dist (γ s) x ≤ r

/-- Normed vector spaces satisfy the short-path condition by convexity of
closed metric balls. -/
theorem shortPathSound_normedSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 ≤ r) : ShortPathSound E r := by
  intro x y hxy
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr
  have hy : y ∈ Metric.closedBall x r := by
    simpa only [Metric.mem_closedBall, dist_comm] using hxy
  have hconnected : IsPathConnected (Metric.closedBall x r) :=
    (convex_closedBall x r).isPathConnected ⟨x, hx⟩
  have hjoined := hconnected.joinedIn x hx y hy
  exact ⟨hjoined.somePath, fun s ↦ by
    simpa only [Metric.mem_closedBall] using hjoined.somePath_mem s⟩

theorem EdgePathSound.graphSound
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M} {r : ℝ}
    (h : EdgePathSound M V G sample r) : GraphSound M V G sample r := by
  intro u v huv
  rcases h huv with ⟨γ, hγ⟩
  simpa only [γ.target, dist_comm] using hγ 1

/-- A short realized edge whose source lies in a scalar band remains in the
Lipschitz-enlarged band along its entire continuum realization. -/
theorem EdgePathSound.joinedIn_levelBand
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {L r a t : ℝ}
    (hedges : EdgePathSound M V G sample r)
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    {u v : V} (huv : G.Adj u v) (hu : |f (sample u) - t| ≤ a) :
    JoinedIn {z | |f z - t| ≤ a + L * r} (sample u) (sample v) := by
  rcases hedges huv with ⟨γ, hγ⟩
  refine ⟨γ, ?_⟩
  intro s
  calc
    |f (γ s) - t| = |(f (γ s) - f (sample u)) + (f (sample u) - t)| := by
      ring_nf
    _ ≤ |f (γ s) - f (sample u)| + |f (sample u) - t| := abs_add _ _
    _ ≤ L * dist (γ s) (sample u) + a := add_le_add (hL _ _) hu
    _ ≤ L * r + a := by
      gcongr
      exact hγ s
    _ = a + L * r := add_comm _ _

/-- Every path-connected continuum set has a graph lift joining sample points
within `δ` of it, and the lifted walk stays within `r + δ` of the set. -/
def GraphComplete
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M) (r δ : ℝ) : Prop :=
  ∀ (S : Set M), IsPathConnected S → ∀ {u v : V},
    sample u ∈ MetricThickening S δ →
    sample v ∈ MetricThickening S δ →
    GraphReachableWithin G
      (fun w => sample w ∈ MetricThickening S (r + δ)) u v

/-- The upper half of a graph sandwich gives realized short edges whenever
the ambient metric admits short paths. -/
theorem GraphSound.edgePathSound
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M} {r : ℝ}
    (hsound : GraphSound M V G sample r)
    (hshort : ShortPathSound M r) :
    EdgePathSound M V G sample r := by
  intro u v huv
  exact hshort (hsound huv)

/-- Equivalently, an upper proximity-graph inclusion supplies
`EdgePathSound`. -/
theorem edgePathSound_of_le_proximityGraph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M} {r : ℝ}
    (hupper : G ≤ proximityGraph M V sample r)
    (hshort : ShortPathSound M r) :
    EdgePathSound M V G sample r := by
  apply GraphSound.edgePathSound _ hshort
  intro u v huv
  exact (hupper huv).2

/-- A dense finite sample and the lower half of a graph sandwich lift every
path-connected continuum set to a graph walk.  The proof uses the finite union
of radius-`ρ / 2` balls centered at vertices reachable inside the requested
thickening.  Connectedness prevents this union from stopping partway across
the continuum set when `2 * δ < ρ`.

This is the graph-completeness theorem needed by the estimator; no kNN-specific
property occurs in its statement. -/
theorem graphComplete_of_sampleDense_of_containsProximityGraph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {sample : V → M} {r δ ρ : ℝ}
    (hr : 0 ≤ r)
    (hdense : ∀ x : M, ∃ w : V, dist x (sample w) ≤ δ)
    (hlower : ContainsProximityGraph M V G sample ρ)
    (hgap : 2 * δ < ρ) :
    GraphComplete M V G sample r δ := by
  classical
  intro S hS u v hu hv
  let P : V → Prop :=
    fun w ↦ sample w ∈ MetricThickening S (r + δ)
  have hdelta_lt : δ < ρ / 2 := by linarith
  have hsmall_mem (w : V) {x : M} (hxS : x ∈ S)
      (hwx : dist (sample w) x ≤ δ) : P w := by
    exact ⟨x, hxS, hwx.trans (by linarith)⟩
  have huP : P u := by
    rcases hu with ⟨x, hxS, hux⟩
    exact hsmall_mem u hxS hux
  have hvP : P v := by
    rcases hv with ⟨x, hxS, hvx⟩
    exact hsmall_mem v hxS hvx
  let W := {w : V // GraphReachableWithin G P u w}
  let U : Set M := ⋃ w : W, Metric.ball (sample w.1) (ρ / 2)
  let B : Set M := ⋃ w : W, Metric.closedBall (sample w.1) (ρ / 2)
  have hUopen : IsOpen U := by
    dsimp only [U]
    exact isOpen_iUnion fun w ↦ Metric.isOpen_ball
  have hBclosed : IsClosed B := by
    dsimp only [B]
    exact isClosed_iUnion_of_finite fun w ↦ Metric.isClosed_ball
  have hUB : U ⊆ B := by
    intro x hx
    simp only [U, B, Set.mem_iUnion, Metric.mem_ball,
      Metric.mem_closedBall] at hx ⊢
    rcases hx with ⟨w, hwx⟩
    exact ⟨w, hwx.le⟩
  have hclosureUB : closure U ⊆ B :=
    closure_minimal hUB hBclosed
  have hclosureS : closure U ∩ S ⊆ U := by
    intro x hx
    have hxB : x ∈ B := hclosureUB hx.1
    simp only [B, Set.mem_iUnion, Metric.mem_closedBall] at hxB
    rcases hxB with ⟨w, hwx⟩
    rcases hdense x with ⟨z, hxz⟩
    have hzx : dist (sample z) x ≤ δ := by
      simpa only [dist_comm] using hxz
    have hzP : P z := hsmall_mem z hx.2 hzx
    have hwx' : dist (sample w.1) x ≤ ρ / 2 := by
      simpa only [dist_comm] using hwx
    have hwzDist : dist (sample w.1) (sample z) < ρ := by
      calc
        dist (sample w.1) (sample z) ≤
            dist (sample w.1) x + dist x (sample z) := dist_triangle _ _ _
        _ ≤ ρ / 2 + δ := by
          gcongr
        _ < ρ := by linarith
    have hwz : w.1 = z ∨ G.Adj w.1 z := by
      by_cases heq : w.1 = z
      · exact Or.inl heq
      · exact Or.inr (hlower ⟨heq, hwzDist.le⟩)
    have huz : GraphReachableWithin G P u z :=
      w.2.trans (GraphReachableWithin.of_eq_or_adj
        w.2.target_mem hzP hwz)
    have hxball : x ∈ Metric.ball (sample z) (ρ / 2) := by
      simpa only [Metric.mem_ball] using hxz.trans_lt hdelta_lt
    simp only [U, Set.mem_iUnion]
    exact ⟨⟨z, huz⟩, hxball⟩
  have hUS : (S ∩ U).Nonempty := by
    rcases hu with ⟨x, hxS, hux⟩
    have hxu : dist x (sample u) ≤ δ := by
      simpa only [dist_comm] using hux
    have hxball : x ∈ Metric.ball (sample u) (ρ / 2) := by
      simpa only [Metric.mem_ball] using hxu.trans_lt hdelta_lt
    have huu : GraphReachableWithin G P u u :=
      GraphReachableWithin.refl huP
    refine ⟨x, hxS, ?_⟩
    simp only [U, Set.mem_iUnion]
    exact ⟨⟨u, huu⟩, hxball⟩
  have hSU : S ⊆ U :=
    hS.isConnected.isPreconnected.subset_of_closure_inter_subset
      hUopen hUS hclosureS
  rcases hv with ⟨y, hyS, hvy⟩
  have hyU : y ∈ U := hSU hyS
  simp only [U, Set.mem_iUnion, Metric.mem_ball] at hyU
  rcases hyU with ⟨w, hwy⟩
  have hvy' : dist y (sample v) ≤ δ := by
    simpa only [dist_comm] using hvy
  have hwy' : dist (sample w.1) y < ρ / 2 := by
    simpa only [dist_comm] using hwy
  have hwvDist : dist (sample w.1) (sample v) < ρ := by
    calc
      dist (sample w.1) (sample v) ≤
          dist (sample w.1) y + dist y (sample v) := dist_triangle _ _ _
      _ < ρ / 2 + δ := add_lt_add_of_lt_of_le hwy' hvy'
      _ < ρ := by linarith
  have hwv : w.1 = v ∨ G.Adj w.1 v := by
    by_cases heq : w.1 = v
    · exact Or.inl heq
    · exact Or.inr (hlower ⟨heq, hwvDist.le⟩)
  exact w.2.trans (GraphReachableWithin.of_eq_or_adj
    w.2.target_mem hvP hwv)

/-- Both halves of a proximity-graph sandwich provide the two graph-geometric
fields used by `ApproximationHypotheses`. -/
theorem graph_geometry_of_proximity_sandwich
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} {sample : V → M} {r δ ρ : ℝ}
    (hr : 0 ≤ r)
    (hdense : ∀ x : M, ∃ w : V, dist x (sample w) ≤ δ)
    (hlower : ContainsProximityGraph M V G sample ρ)
    (hupper : G ≤ proximityGraph M V sample r)
    (hgap : 2 * δ < ρ)
    (hshort : ShortPathSound M r) :
    EdgePathSound M V G sample r ∧
      GraphComplete M V G sample r δ := by
  exact ⟨edgePathSound_of_le_proximityGraph hupper hshort,
    graphComplete_of_sampleDense_of_containsProximityGraph
      hr hdense hlower hgap⟩

/-- A concrete first path-lifting lemma: a continuum path between `x` and `y`
lifts between any sample vertices within `δ` of its endpoints, and every walk
vertex remains within `r + δ` of the original set. -/
theorem GraphComplete.lift_joinedIn
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M} {r δ : ℝ}
    (hcomplete : GraphComplete M V G sample r δ)
    {S : Set M} {x y : M} (hxy : JoinedIn S x y)
    {u v : V} (hu : dist (sample u) x ≤ δ)
    (hv : dist (sample v) y ≤ δ) :
    GraphReachableWithin G
      (fun w => sample w ∈ MetricThickening S (r + δ)) u v := by
  let γ := hxy.somePath
  letI : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, unitInterval.zero_mem⟩)
  have hγConnected : IsPathConnected (Set.range γ) :=
    isPathConnected_range γ.continuous
  have huRange : sample u ∈ MetricThickening (Set.range γ) δ := by
    refine ⟨x, ?_, hu⟩
    exact ⟨0, γ.source⟩
  have hvRange : sample v ∈ MetricThickening (Set.range γ) δ := by
    refine ⟨y, ?_, hv⟩
    exact ⟨1, γ.target⟩
  have hlift := hcomplete (Set.range γ) hγConnected huRange hvRange
  apply hlift.mono
  intro w hw
  exact MetricThickening.mono (fun z hz => by
    rcases hz with ⟨t, rfl⟩
    exact hxy.somePath_mem t) hw

end ReebGraph
