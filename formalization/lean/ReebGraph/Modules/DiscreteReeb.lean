import ReebGraph.Modules.Crossing

/-!
# Discrete support-induced Reeb graph

The discrete support-induced Reeb graph built from observed filter values.

Canonical levels and thresholds are extracted from the finite value set,
slice nodes are assembled into `discreteReebGraph` /
`canonicalDiscreteReebGraph`, and the canonical active incidence graph
records how slices connect vertically and horizontally.

Main results: `canonicalVertexActivityConnected`,
`canonicalActiveIncidence_reachable_of_walk_of_nonflat`, and
`SupportComponent.exists_equiv_canonical_slice`, together with the
`sweep_correct` / `node_correctness` / `transition_correctness` summary
statements.  The rest are supporting lemmas about observed gaps, canonical
midpoints, and slice overlap.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-! ## Discrete support-induced Reeb graph -/

section DiscreteGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sorted distinct observed scalar values. -/
noncomputable def observedLevels (f : V → ℝ) : List ℝ :=
  (Finset.univ.image f).sort (· ≤ ·)

theorem observedLevels_sorted (f : V → ℝ) :
    (observedLevels f).Sorted (· < ·) := by
  exact Finset.sort_sorted_lt (Finset.univ.image f)

theorem mem_observedLevels (f : V → ℝ) (v : V) :
    f v ∈ observedLevels f := by
  rw [observedLevels, Finset.mem_sort]
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

/-- A threshold avoiding all observed values and lying strictly inside their
range belongs to a unique vertex-value-free gap.  This is the finite ordered
set fact underlying the canonical midpoint schedule. -/
theorem exists_observed_gap_around
    (f : V → ℝ) (t : ℝ)
    (hbelow : ∃ u, f u < t) (habove : ∃ v, t < f v)
    (havoid : ∀ v, f v ≠ t) :
    ∃ a b : ℝ,
      a ∈ observedLevels f ∧ b ∈ observedLevels f ∧
      a < t ∧ t < b ∧ a < b ∧
      ∀ v, f v ≤ a ∨ b ≤ f v := by
  let levels : Finset ℝ := Finset.univ.image f
  have hleft : ∃ a ∈ levels, a < t := by
    rcases hbelow with ⟨u, hu⟩
    exact ⟨f u, Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩, hu⟩
  have hright : ∃ b ∈ levels, t < b := by
    rcases habove with ⟨v, hv⟩
    exact ⟨f v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, hv⟩
  rcases Finset.exists_next_left hleft with ⟨a, haLevels, hat, haMax⟩
  rcases Finset.exists_next_right hright with ⟨b, hbLevels, htb, hbMin⟩
  refine ⟨a, b, ?_, ?_, hat, htb, hat.trans htb, ?_⟩
  · rw [observedLevels, Finset.mem_sort]
    exact haLevels
  · rw [observedLevels, Finset.mem_sort]
    exact hbLevels
  · intro v
    have hvLevels : f v ∈ levels :=
      Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    rcases lt_or_gt_of_ne (havoid v) with hvt | htv
    · exact Or.inl (haMax (f v) hvLevels hvt)
    · exact Or.inr (hbMin (f v) hvLevels htv)

/-- Every threshold with an observed value weakly below and an observed value
strictly above lies in the half-open cell of two consecutive observed values.
The weak inequality is essential at observed thresholds and matches `Crosses`.
-/
theorem exists_observed_cell_at
    (f : V → ℝ) (t : ℝ)
    (hbelow : ∃ u, f u ≤ t) (habove : ∃ v, t < f v) :
    ∃ a b : ℝ,
      a ∈ observedLevels f ∧ b ∈ observedLevels f ∧
      a ≤ t ∧ t < b ∧ a < b ∧
      ∀ v, f v ≤ a ∨ b ≤ f v := by
  let levels : Finset ℝ := Finset.univ.image f
  let lower := levels.filter (fun x => x ≤ t)
  let upper := levels.filter (fun x => t < x)
  have hlower : lower.Nonempty := by
    rcases hbelow with ⟨u, hu⟩
    refine ⟨f u, Finset.mem_filter.mpr ⟨?_, hu⟩⟩
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
  have hupper : upper.Nonempty := by
    rcases habove with ⟨v, hv⟩
    refine ⟨f v, Finset.mem_filter.mpr ⟨?_, hv⟩⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  rcases Finset.exists_max_image lower id hlower with ⟨a, haLower, haMax⟩
  rcases Finset.exists_min_image upper id hupper with ⟨b, hbUpper, hbMin⟩
  rcases Finset.mem_filter.mp haLower with ⟨haLevels, hat⟩
  rcases Finset.mem_filter.mp hbUpper with ⟨hbLevels, htb⟩
  refine ⟨a, b, ?_, ?_, hat, htb, lt_of_le_of_lt hat htb, ?_⟩
  · rw [observedLevels, Finset.mem_sort]
    exact haLevels
  · rw [observedLevels, Finset.mem_sort]
    exact hbLevels
  · intro v
    have hvLevels : f v ∈ levels :=
      Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    by_cases hvt : f v ≤ t
    · exact Or.inl (haMax (f v)
        (Finset.mem_filter.mpr ⟨hvLevels, hvt⟩))
    · exact Or.inr (hbMin (f v)
        (Finset.mem_filter.mpr ⟨hvLevels, lt_of_not_ge hvt⟩))

/-- Every nonempty crossing slice is represented without perturbation by the
midpoint of an observed-value cell. -/
theorem IsActiveVertex.exists_equivalent_observed_midpoint
    (G : SimpleGraph V) (f : V → ℝ) {t : ℝ} {u : V}
    (hu : IsActiveVertex G f t u) :
    ∃ a b : ℝ,
      a ∈ observedLevels f ∧ b ∈ observedLevels f ∧
      a ≤ t ∧ t < b ∧ a < b ∧
      (∀ v, f v ≤ a ∨ b ≤ f v) ∧
      ThresholdEquivalent f t ((a + b) / 2) := by
  rcases hu with ⟨v, _, hcross⟩
  have hbounds : (∃ w, f w ≤ t) ∧ (∃ w, t < f w) := by
    rcases (crosses_iff_oriented f t u v).mp hcross with huv | hvu
    · exact ⟨⟨u, huv.1⟩, ⟨v, huv.2⟩⟩
    · exact ⟨⟨v, hvu.1⟩, ⟨u, hvu.2⟩⟩
  rcases exists_observed_cell_at f t hbounds.1 hbounds.2 with
    ⟨a, b, ha, hb, hat, htb, hab, hgap⟩
  exact ⟨a, b, ha, hb, hat, htb, hab, hgap,
    thresholdEquivalent_midpoint_of_gap f hat htb hgap⟩

/-- Midpoints between consecutive entries of a list. -/
noncomputable def consecutiveMidpoints (levels : List ℝ) : List ℝ :=
  List.zipWith (fun a b => (a + b) / 2) levels levels.tail

/-- Consecutive values in a strictly sorted list contribute their midpoint to
`consecutiveMidpoints`.  The no-gap hypothesis is stated order-theoretically
so it can be supplied directly by `exists_observed_cell_at`. -/
theorem midpoint_mem_consecutiveMidpoints_of_gap
    {levels : List ℝ} {a b : ℝ}
    (hsorted : levels.Sorted (· < ·))
    (ha : a ∈ levels) (hb : b ∈ levels) (hab : a < b)
    (hgap : ∀ z ∈ levels, z ≤ a ∨ b ≤ z) :
    (a + b) / 2 ∈ consecutiveMidpoints levels := by
  rcases List.mem_iff_get.mp ha with ⟨ia, hia⟩
  rcases List.mem_iff_get.mp hb with ⟨ib, hib⟩
  have hiab : ia < ib := by
    by_contra hn
    have hle : ib ≤ ia := le_of_not_gt hn
    rcases hle.eq_or_lt with heq | hlt
    · subst ib
      exact hab.ne (hia.symm.trans hib)
    · have hba := hsorted.rel_get_of_lt hlt
      rw [hib, hia] at hba
      exact (not_lt_of_ge hab.le) hba
  have hadj : ia.1 + 1 = ib.1 := by
    by_contra hn
    have hstrict : ia.1 + 1 < ib.1 := by omega
    let j : Fin levels.length := ⟨ia.1 + 1, by omega⟩
    have haj : a < levels.get j := by
      rw [← hia]
      exact hsorted.rel_get_of_lt (show ia.1 < j.1 by simp [j])
    have hjb : levels.get j < b := by
      rw [← hib]
      exact hsorted.rel_get_of_lt (show j.1 < ib.1 by simp [j]; omega)
    rcases hgap (levels.get j) (List.get_mem levels j) with hja | hbj
    · exact (not_lt_of_ge hja) haj
    · exact (not_lt_of_ge hbj) hjb
  have hiLen : ia.1 < (consecutiveMidpoints levels).length := by
    simp [consecutiveMidpoints, List.length_zipWith]
    omega
  apply List.mem_iff_get.mpr
  refine ⟨⟨ia.1, hiLen⟩, ?_⟩
  unfold consecutiveMidpoints
  rw [List.get_zipWith]
  rw [List.get_tail]
  rw [show levels.get ⟨ia.1, by omega⟩ = a by simpa using hia]
  rw [show levels.get ⟨ia.1 + 1, by omega⟩ = b by
    have : (⟨ia.1 + 1, by omega⟩ : Fin levels.length) = ib := Fin.ext hadj
    simpa [this] using hib]

/-- Canonical midpoint schedule used by the mathematical algorithm. -/
noncomputable def canonicalMidpoints (f : V → ℝ) : List ℝ :=
  consecutiveMidpoints (observedLevels f)

noncomputable def canonicalThreshold (f : V → ℝ) :
    Fin (canonicalMidpoints f).length → ℝ :=
  fun i => (canonicalMidpoints f).get i

/-- Canonical midpoint thresholds inherit the order of the sorted observed
levels. -/
theorem canonicalThreshold_mono (f : V → ℝ) :
    Monotone (canonicalThreshold f) := by
  intro i j hij
  have hi : i.1 + 1 < (observedLevels f).length := by
    have hi' := i.2
    simp only [canonicalMidpoints, consecutiveMidpoints, List.length_zipWith,
      List.length_tail, Nat.min_eq_right (Nat.sub_le _ _)] at hi'
    omega
  have hj : j.1 + 1 < (observedLevels f).length := by
    have hj' := j.2
    simp only [canonicalMidpoints, consecutiveMidpoints, List.length_zipWith,
      List.length_tail, Nat.min_eq_right (Nat.sub_le _ _)] at hj'
    omega
  have hleft : (observedLevels f).get ⟨i.1, by omega⟩ ≤
      (observedLevels f).get ⟨j.1, by omega⟩ := by
    exact (observedLevels_sorted f).le_of_lt.rel_get_of_le hij
  have hright : (observedLevels f).get ⟨i.1 + 1, hi⟩ ≤
      (observedLevels f).get ⟨j.1 + 1, hj⟩ := by
    apply (observedLevels_sorted f).le_of_lt.rel_get_of_le
    exact Nat.add_le_add_right hij 1
  change (consecutiveMidpoints (observedLevels f)).get i ≤
    (consecutiveMidpoints (observedLevels f)).get j
  unfold consecutiveMidpoints
  rw [List.get_zipWith, List.get_zipWith, List.get_tail, List.get_tail]
  gcongr

/-- Every nonempty slice occurs at an actual entry of the finite canonical
midpoint schedule, up to the canonical threshold-cell equivalence. -/
theorem IsActiveVertex.exists_equivalent_canonicalThreshold
    (G : SimpleGraph V) (f : V → ℝ) {t : ℝ} {u : V}
    (hu : IsActiveVertex G f t u) :
    ∃ i : Fin (canonicalMidpoints f).length,
      ThresholdEquivalent f t (canonicalThreshold f i) := by
  rcases hu.exists_equivalent_observed_midpoint G f with
    ⟨a, b, ha, hb, _, _, hab, hgap, hequiv⟩
  have hmid : (a + b) / 2 ∈ canonicalMidpoints f :=
    midpoint_mem_consecutiveMidpoints_of_gap
      (observedLevels_sorted f) ha hb hab (fun z hz => by
        rw [observedLevels, Finset.mem_sort] at hz
        rcases Finset.mem_image.mp hz with ⟨v, _, rfl⟩
        exact hgap v)
  rcases List.mem_iff_get.mp hmid with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa only [canonicalThreshold, hi] using hequiv

/-- A node is a support-induced component at one supplied ordered slice. -/
def SliceNode (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ) :=
  Σ i : Fin s, SupportComponent G f (threshold i)

/-- Two slice nodes overlap when their original vertex supports intersect. -/
noncomputable def SliceOverlap (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ)
    (x y : SliceNode G f threshold) : Prop :=
  (componentSupport G f (threshold x.1) x.2 ∩
    componentSupport G f (threshold y.1) y.2).Nonempty

omit [Fintype V] [DecidableEq V] in
theorem sliceOverlap_comm (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ)
    (x y : SliceNode G f threshold) :
    SliceOverlap G f threshold x y ↔ SliceOverlap G f threshold y x := by
  constructor
  · rintro ⟨v, hvx, hvy⟩
    exact ⟨v, hvy, hvx⟩
  · rintro ⟨v, hvy, hvx⟩
    exact ⟨v, hvx, hvy⟩

omit [Fintype V] [DecidableEq V] in
theorem sliceNode_support_nonempty (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ)
    (x : SliceNode G f threshold) :
    (componentSupport G f (threshold x.1) x.2).Nonempty :=
  componentSupport_nonempty G f (threshold x.1) x.2

omit [Fintype V] [DecidableEq V] in
theorem sliceOverlap_same_slice_iff (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ) (i : Fin s)
    (c d : SupportComponent G f (threshold i)) :
    SliceOverlap G f threshold ⟨i, c⟩ ⟨i, d⟩ ↔ c = d :=
  crossingComponent_support_intersects_iff G f (threshold i) c d

/-- The intended adjacency relation: nodes occur at consecutive slices and
their vertex supports overlap. -/
noncomputable def DiscreteReebAdj (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ)
    (x y : SliceNode G f threshold) : Prop :=
  ((x.1.1 + 1 = y.1.1) ∨ (y.1.1 + 1 = x.1.1)) ∧
    SliceOverlap G f threshold x y

/-- The finite-resolution discrete Reeb graph specified by support-induced
components and adjacent-slice support overlap. -/
noncomputable def discreteReebGraph (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ) :
    SimpleGraph (SliceNode G f threshold) where
  Adj := DiscreteReebAdj G f threshold
  symm := by
    intro x y h
    refine ⟨h.1.elim Or.inr Or.inl, ?_⟩
    exact (sliceOverlap_comm G f threshold x y).mp h.2
  loopless := by
    intro x h
    change DiscreteReebAdj G f threshold x x at h
    rcases h.1 with h | h <;> omega

/-- The canonical finite midpoint graph, with no externally supplied threshold
schedule. -/
noncomputable def canonicalDiscreteReebGraph
    (G : SimpleGraph V) (f : V → ℝ) :
    SimpleGraph (SliceNode G f (canonicalThreshold f)) :=
  discreteReebGraph G f (canonicalThreshold f)

/-- Pre-quotient incidence states: an active sample vertex at one canonical
slice.  This is a convenient non-circular target for geometric path lifting. -/
def CanonicalActiveState (G : SimpleGraph V) (f : V → ℝ) :=
  Σ i : Fin (canonicalMidpoints f).length,
    ActiveVertex G f (canonicalThreshold f i)

/-- Horizontal incidence steps follow support edges in one slice; vertical
steps retain one active ambient vertex across consecutive canonical slices. -/
noncomputable def canonicalActiveIncidenceGraph
    (G : SimpleGraph V) (f : V → ℝ) :
    SimpleGraph (CanonicalActiveState G f) where
  Adj x y :=
    (x.1 = y.1 ∧
      (supportSliceGraph G f (canonicalThreshold f x.1)).Adj x.2.1 y.2.1) ∨
    (((x.1.1 + 1 = y.1.1) ∨ (y.1.1 + 1 = x.1.1)) ∧ x.2.1 = y.2.1)
  symm := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · left
      refine ⟨hxy.1.symm, ?_⟩
      have hsymm :=
        (supportSliceGraph G f (canonicalThreshold f x.1)).symm hxy.2
      have hthreshold : canonicalThreshold f x.1 = canonicalThreshold f y.1 :=
        congrArg (canonicalThreshold f) hxy.1
      simpa only [hthreshold] using hsymm
    · right
      exact ⟨hxy.1.elim Or.inr Or.inl, hxy.2.symm⟩
  loopless := by
    intro x hxx
    rcases hxx with hxx | hxx
    · exact (supportSliceGraph G f (canonicalThreshold f x.1)).loopless x.2.1 hxx.2
    · rcases hxx.1 with h | h <;> omega

/-- Quotient an active incidence state to its support component node. -/
def canonicalActiveStateNode
    (G : SimpleGraph V) (f : V → ℝ)
    (x : CanonicalActiveState G f) :
    SliceNode G f (canonicalThreshold f) :=
  ⟨x.1, componentOfActive G f (canonicalThreshold f x.1) x.2⟩

theorem canonicalActiveStateNode_eq_of_horizontal
    (G : SimpleGraph V) (f : V → ℝ)
    {x y : CanonicalActiveState G f} (hindex : x.1 = y.1)
    (hxy : (supportSliceGraph G f (canonicalThreshold f x.1)).Adj
      x.2.1 y.2.1) :
    canonicalActiveStateNode G f x = canonicalActiveStateNode G f y := by
  rcases x with ⟨i, xi⟩
  rcases y with ⟨j, yj⟩
  dsimp only at hindex
  subst j
  unfold canonicalActiveStateNode
  change (⟨i, componentOfActive G f (canonicalThreshold f i) xi⟩ :
      SliceNode G f (canonicalThreshold f)) =
    ⟨i, componentOfActive G f (canonicalThreshold f i) yj⟩
  have hcomp : componentOfActive G f (canonicalThreshold f i) xi =
      componentOfActive G f (canonicalThreshold f i) yj := by
    apply Quotient.sound
    exact ⟨.cons hxy .nil⟩
  exact Sigma.ext rfl (heq_of_eq hcomp)

theorem canonicalActiveStateNode_adj_of_vertical
    (G : SimpleGraph V) (f : V → ℝ)
    {x y : CanonicalActiveState G f}
    (hindex : (x.1.1 + 1 = y.1.1) ∨ (y.1.1 + 1 = x.1.1))
    (hvertex : x.2.1 = y.2.1) :
    (canonicalDiscreteReebGraph G f).Adj
      (canonicalActiveStateNode G f x) (canonicalActiveStateNode G f y) := by
  change DiscreteReebAdj G f (canonicalThreshold f)
    (canonicalActiveStateNode G f x) (canonicalActiveStateNode G f y)
  refine ⟨hindex, x.2.1, ?_, ?_⟩
  · exact mem_componentSupport_componentOfActive G f
      (canonicalThreshold f x.1) x.2
  · simpa only [hvertex] using
      (mem_componentSupport_componentOfActive G f
        (canonicalThreshold f y.1) y.2)

/-- Every active-incidence step either stays in one quotient node or becomes
one edge of the canonical support-component graph. -/
theorem canonicalActiveIncidence_adj_projects
    (G : SimpleGraph V) (f : V → ℝ)
    {x y : CanonicalActiveState G f}
    (hxy : (canonicalActiveIncidenceGraph G f).Adj x y) :
    canonicalActiveStateNode G f x = canonicalActiveStateNode G f y ∨
      (canonicalDiscreteReebGraph G f).Adj
        (canonicalActiveStateNode G f x) (canonicalActiveStateNode G f y) := by
  rcases hxy with hxy | hxy
  · exact Or.inl (canonicalActiveStateNode_eq_of_horizontal G f hxy.1 hxy.2)
  · exact Or.inr (canonicalActiveStateNode_adj_of_vertical G f hxy.1 hxy.2)

/-- Incidence reachability projects to reachability in the algorithm's graph.
This isolates the remaining geometry to constructing an incidence walk. -/
theorem canonicalActiveIncidence_reachable_projects
    (G : SimpleGraph V) (f : V → ℝ)
    {x y : CanonicalActiveState G f}
    (hxy : (canonicalActiveIncidenceGraph G f).Reachable x y) :
    (canonicalDiscreteReebGraph G f).Reachable
      (canonicalActiveStateNode G f x) (canonicalActiveStateNode G f y) := by
  rcases hxy with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih =>
      have hstep : (canonicalDiscreteReebGraph G f).Reachable
          (canonicalActiveStateNode G f u)
          (canonicalActiveStateNode G f v) := by
        rcases canonicalActiveIncidence_adj_projects G f huv with huv | huv
        · rw [huv]
        · exact ⟨.cons huv .nil⟩
      exact hstep.trans ih

/-- Every quotient slice node has an active-incidence representative. -/
theorem sliceNode_exists_canonicalActiveState
    (G : SimpleGraph V) (f : V → ℝ)
    (x : SliceNode G f (canonicalThreshold f)) :
    ∃ u : CanonicalActiveState G f,
      canonicalActiveStateNode G f u = x := by
  rcases componentSupport_nonempty G f (canonicalThreshold f x.1) x.2 with
    ⟨v, hv⟩
  let av : ActiveVertex G f (canonicalThreshold f x.1) :=
    ⟨v, componentSupport_isActive G f (canonicalThreshold f x.1) x.2 hv⟩
  let u : CanonicalActiveState G f := ⟨x.1, av⟩
  have hcomponent : componentOfActive G f (canonicalThreshold f x.1) av = x.2 := by
    apply crossingComponent_eq_of_support_intersects G f
      (canonicalThreshold f x.1)
    exact ⟨v, mem_componentSupport_componentOfActive G f
      (canonicalThreshold f x.1) av, hv⟩
  refine ⟨u, ?_⟩
  unfold canonicalActiveStateNode u
  exact Sigma.ext rfl (heq_of_eq hcomponent)

/-- Every canonical graph edge is represented before quotienting by retaining
its overlap witness across the two consecutive slices. -/
theorem canonicalDiscreteReebGraph_adj_lifts_incidence
    (G : SimpleGraph V) (f : V → ℝ)
    {x y : SliceNode G f (canonicalThreshold f)}
    (hxy : (canonicalDiscreteReebGraph G f).Adj x y) :
    ∃ u v : CanonicalActiveState G f,
      canonicalActiveStateNode G f u = x ∧
      canonicalActiveStateNode G f v = y ∧
      (canonicalActiveIncidenceGraph G f).Adj u v := by
  change DiscreteReebAdj G f (canonicalThreshold f) x y at hxy
  rcases hxy.2 with ⟨w, hwx, hwy⟩
  let ux : ActiveVertex G f (canonicalThreshold f x.1) :=
    ⟨w, componentSupport_isActive G f (canonicalThreshold f x.1) x.2 hwx⟩
  let uy : ActiveVertex G f (canonicalThreshold f y.1) :=
    ⟨w, componentSupport_isActive G f (canonicalThreshold f y.1) y.2 hwy⟩
  let u : CanonicalActiveState G f := ⟨x.1, ux⟩
  let v : CanonicalActiveState G f := ⟨y.1, uy⟩
  have hcx : componentOfActive G f (canonicalThreshold f x.1) ux = x.2 := by
    apply crossingComponent_eq_of_support_intersects G f
      (canonicalThreshold f x.1)
    exact ⟨w, mem_componentSupport_componentOfActive G f
      (canonicalThreshold f x.1) ux, hwx⟩
  have hcy : componentOfActive G f (canonicalThreshold f y.1) uy = y.2 := by
    apply crossingComponent_eq_of_support_intersects G f
      (canonicalThreshold f y.1)
    exact ⟨w, mem_componentSupport_componentOfActive G f
      (canonicalThreshold f y.1) uy, hwy⟩
  refine ⟨u, v, ?_, ?_, ?_⟩
  · unfold canonicalActiveStateNode u
    exact Sigma.ext rfl (heq_of_eq hcx)
  · unfold canonicalActiveStateNode v
    exact Sigma.ext rfl (heq_of_eq hcy)
  · exact Or.inr ⟨hxy.1, rfl⟩

/-- Local coherence of the canonical slices at one ambient graph vertex:
all active occurrences of that vertex lie in one incidence component. -/
def CanonicalVertexActivityConnected
    (G : SimpleGraph V) (f : V → ℝ) : Prop :=
  ∀ (u : V) (i j : Fin (canonicalMidpoints f).length)
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) u),
    (canonicalActiveIncidenceGraph G f).Reachable
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨u, hj⟩⟩

/-- Every original graph edge has at least one canonical slice on which both
endpoints are active.  Non-flat edges satisfy this through a crossed midpoint;
flat edges require the surrounding crossing supports to overlap. -/
def CanonicalEdgeActivityOverlap
    (G : SimpleGraph V) (f : V → ℝ) : Prop :=
  ∀ {u v : V}, G.Adj u v →
    ∃ i : Fin (canonicalMidpoints f).length,
      IsActiveVertex G f (canonicalThreshold f i) u ∧
      IsActiveVertex G f (canonicalThreshold f i) v

/-- No original graph edge is exactly flat for the observed scalar.  This is
a genericity condition on the scalar relative to the neighborhood graph, not
an algorithmic scale parameter. -/
def GraphEdgeNonflat (G : SimpleGraph V) (f : V → ℝ) : Prop :=
  ∀ {u v : V}, G.Adj u v → f u ≠ f v

/-- Pairwise-distinct observed scalar values imply edge nonflatness for every
neighborhood graph.  Thus nonflatness may be imposed as a parameter-free
genericity condition on the observed filter, independently of graph choice. -/
theorem GraphEdgeNonflat.of_injective
    (G : SimpleGraph V) (f : V → ℝ) (hf : Function.Injective f) :
    GraphEdgeNonflat G f := by
  intro u v huv huvValue
  exact huv.ne (hf huvValue)

/-- Every non-flat graph edge crosses a canonical midpoint cell, so its two
endpoints are simultaneously active on a canonical slice. -/
theorem canonicalEdgeActivityOverlap_of_nonflat
    (G : SimpleGraph V) (f : V → ℝ)
    (hnonflat : GraphEdgeNonflat G f) :
    CanonicalEdgeActivityOverlap G f := by
  intro u v huv
  have huvValue : f u ≠ f v := hnonflat huv
  have hcross : Crosses f ((f u + f v) / 2) u v := by
    rcases lt_or_gt_of_ne huvValue with huvlt | hvult
    · exact crosses_midpoint_of_lt f huvlt
    · simpa only [add_comm] using
        (crosses_comm f ((f v + f u) / 2) v u).mp
          (crosses_midpoint_of_lt f hvult)
  have hu : IsActiveVertex G f ((f u + f v) / 2) u :=
    ⟨v, huv, hcross⟩
  have hv : IsActiveVertex G f ((f u + f v) / 2) v :=
    ⟨u, G.symm huv, (crosses_comm f ((f u + f v) / 2) u v).mp hcross⟩
  rcases hu.exists_equivalent_canonicalThreshold G f with ⟨i, hi⟩
  exact ⟨i,
    (isActiveVertex_iff_of_thresholdEquivalent G f hi u).mp hu,
    (isActiveVertex_iff_of_thresholdEquivalent G f hi v).mp hv⟩

/-- Quantitative form: the common active canonical threshold lies between the
two endpoint values of the non-flat edge. -/
theorem exists_common_canonicalActive_of_adj_of_nonflat
    (G : SimpleGraph V) (f : V → ℝ)
    (hnonflat : GraphEdgeNonflat G f)
    {u v : V} (huv : G.Adj u v) :
    ∃ i : Fin (canonicalMidpoints f).length,
      ∃ hi : IsActiveVertex G f (canonicalThreshold f i) u,
      ∃ hj : IsActiveVertex G f (canonicalThreshold f i) v,
        min (f u) (f v) ≤ canonicalThreshold f i ∧
        canonicalThreshold f i ≤ max (f u) (f v) := by
  have huvValue : f u ≠ f v := hnonflat huv
  have hcross : Crosses f ((f u + f v) / 2) u v := by
    rcases lt_or_gt_of_ne huvValue with huvlt | hvult
    · exact crosses_midpoint_of_lt f huvlt
    · simpa only [add_comm] using
        (crosses_comm f ((f v + f u) / 2) v u).mp
          (crosses_midpoint_of_lt f hvult)
  have hu : IsActiveVertex G f ((f u + f v) / 2) u :=
    ⟨v, huv, hcross⟩
  rcases hu.exists_equivalent_canonicalThreshold G f with ⟨i, hiEquiv⟩
  have hcrossi : Crosses f (canonicalThreshold f i) u v :=
    (crosses_iff_of_thresholdEquivalent f hiEquiv u v).mp hcross
  let hi : IsActiveVertex G f (canonicalThreshold f i) u :=
    ⟨v, huv, hcrossi⟩
  let hj : IsActiveVertex G f (canonicalThreshold f i) v :=
    ⟨u, G.symm huv,
      (crosses_comm f (canonicalThreshold f i) u v).mp hcrossi⟩
  exact ⟨i, hi, hj, hcrossi.1, hcrossi.2.le⟩

/-- Active occurrences of one vertex at ordered canonical slices are joined
by the vertical incidence edges at every intervening slice. -/
theorem canonicalActiveIncidence_vertical_reachable
    (G : SimpleGraph V) (f : V → ℝ) (u : V)
    {i j : Fin (canonicalMidpoints f).length} (hij : i ≤ j)
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) u) :
    (canonicalActiveIncidenceGraph G f).Reachable
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨u, hj⟩⟩ := by
  have aux : ∀ d : ℕ, ∀ (i j : Fin (canonicalMidpoints f).length),
      j.1 = i.1 + d →
      ∀ (hi : IsActiveVertex G f (canonicalThreshold f i) u)
        (hj : IsActiveVertex G f (canonicalThreshold f j) u),
        (canonicalActiveIncidenceGraph G f).Reachable
          ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨u, hj⟩⟩ := by
    intro d
    induction d with
    | zero =>
        intro i j hval hi hj
        have hijEq : i = j := Fin.ext (by omega)
        subst j
        simpa using
          (SimpleGraph.Reachable.refl
            (⟨i, ⟨u, hi⟩⟩ : CanonicalActiveState G f))
    | succ d ih =>
        intro i j hval hi hj
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
        have hprev := ih i k (by simp [k]) hi hk
        have hsucc : k.1 + 1 = j.1 := by
          dsimp [k]
          omega
        have hstep : (canonicalActiveIncidenceGraph G f).Reachable
            ⟨k, ⟨u, hk⟩⟩ ⟨j, ⟨u, hj⟩⟩ := by
          refine ⟨.cons ?_ .nil⟩
          exact Or.inr ⟨Or.inl hsucc, rfl⟩
        exact hprev.trans hstep
  apply aux (j.1 - i.1) i j (by omega) hi hj

/-- Vertex activity coherence is therefore automatic for the canonical
midpoint schedule. -/
theorem canonicalVertexActivityConnected
    (G : SimpleGraph V) (f : V → ℝ) :
    CanonicalVertexActivityConnected G f := by
  intro u i j hi hj
  by_cases hij : i ≤ j
  · exact canonicalActiveIncidence_vertical_reachable G f u hij hi hj
  · exact (canonicalActiveIncidence_vertical_reachable G f u
      (le_of_not_ge hij) hj hi).symm

/-- Checkable local conditions sufficient to lift ordinary graph walks to the
active-incidence graph. -/
def CanonicalIncidenceLocallyCoherent
    (G : SimpleGraph V) (f : V → ℝ) : Prop :=
  CanonicalVertexActivityConnected G f ∧ CanonicalEdgeActivityOverlap G f

theorem canonicalIncidenceLocallyCoherent_of_edgeOverlap
    (G : SimpleGraph V) (f : V → ℝ)
    (hoverlap : CanonicalEdgeActivityOverlap G f) :
    CanonicalIncidenceLocallyCoherent G f :=
  ⟨canonicalVertexActivityConnected G f, hoverlap⟩

theorem canonicalIncidenceLocallyCoherent_of_nonflat
    (G : SimpleGraph V) (f : V → ℝ)
    (hnonflat : GraphEdgeNonflat G f) :
    CanonicalIncidenceLocallyCoherent G f :=
  canonicalIncidenceLocallyCoherent_of_edgeOverlap G f
    (canonicalEdgeActivityOverlap_of_nonflat G f hnonflat)

/-- Under local coherence, one original graph edge lifts between arbitrary
active occurrences of its endpoints. -/
theorem canonicalActiveIncidence_reachable_of_adj
    (G : SimpleGraph V) (f : V → ℝ)
    (hcoherent : CanonicalIncidenceLocallyCoherent G f)
    {u v : V} (huv : G.Adj u v)
    {i j : Fin (canonicalMidpoints f).length}
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) v) :
    (canonicalActiveIncidenceGraph G f).Reachable
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨v, hj⟩⟩ := by
  rcases hcoherent.2 huv with ⟨k, huk, hvk⟩
  have hleft := hcoherent.1 u i k hi huk
  have hright := hcoherent.1 v k j hvk hj
  have hhorizontal : (canonicalActiveIncidenceGraph G f).Reachable
      ⟨k, ⟨u, huk⟩⟩ ⟨k, ⟨v, hvk⟩⟩ := by
    refine ⟨.cons ?_ .nil⟩
    exact Or.inl ⟨rfl, huv, huk, hvk⟩
  exact hleft.trans (hhorizontal.trans hright)

/-- Consequently every ordinary graph walk lifts between arbitrary active
occurrences of its endpoint vertices.  This is the unfiltered combinatorial
core of slab-walk canonicalization. -/
theorem canonicalActiveIncidence_reachable_of_walk
    (G : SimpleGraph V) (f : V → ℝ)
    (hcoherent : CanonicalIncidenceLocallyCoherent G f)
    {u v : V} (p : G.Walk u v)
    {i j : Fin (canonicalMidpoints f).length}
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) v) :
    (canonicalActiveIncidenceGraph G f).Reachable
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨v, hj⟩⟩ := by
  induction p generalizing i with
  | @nil u => exact hcoherent.1 u i j hi hj
  | @cons u v w huv p ih =>
      rcases hcoherent.2 huv with ⟨k, huk, hvk⟩
      have hfirst := canonicalActiveIncidence_reachable_of_adj
        G f hcoherent huv hi hvk
      exact hfirst.trans (ih (i := k) hvk hj)

theorem canonicalActiveIncidence_reachable_of_walk_of_nonflat
    (G : SimpleGraph V) (f : V → ℝ)
    (hnonflat : GraphEdgeNonflat G f)
    {u v : V} (p : G.Walk u v)
    {i j : Fin (canonicalMidpoints f).length}
    (hi : IsActiveVertex G f (canonicalThreshold f i) u)
    (hj : IsActiveVertex G f (canonicalThreshold f j) v) :
    (canonicalActiveIncidenceGraph G f).Reachable
      ⟨i, ⟨u, hi⟩⟩ ⟨j, ⟨v, hj⟩⟩ :=
  canonicalActiveIncidence_reachable_of_walk G f
    (canonicalIncidenceLocallyCoherent_of_nonflat G f hnonflat) p hi hj

/-- Each nonempty arbitrary-threshold component quotient is equivalent to the
component quotient at one canonical midpoint slice. -/
theorem SupportComponent.exists_equiv_canonical_slice
    (G : SimpleGraph V) (f : V → ℝ) {t : ℝ}
    (c : SupportComponent G f t) :
    ∃ i : Fin (canonicalMidpoints f).length,
      Nonempty
        (SupportComponent G f t ≃
          SupportComponent G f (canonicalThreshold f i)) := by
  refine Quotient.inductionOn c ?_
  intro u
  rcases u.2.exists_equivalent_canonicalThreshold G f with ⟨i, hi⟩
  exact ⟨i, ⟨supportComponentEquivOfThresholdEquivalent G f hi⟩⟩

/-- Specification-level reference sweep.  Verification of the optimized Python
segment-tree and rollback-union-find implementation remains a separate
refinement theorem. -/
noncomputable def sweepGraph (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ) :
    SimpleGraph (SliceNode G f threshold) :=
  discreteReebGraph G f threshold

omit [Fintype V] [DecidableEq V] in
theorem active_interval_correct
    (f : V → ℝ) (u v : V)
    {a b t : ℝ} (hu : f u = a) (hv : f v = b) :
    Crosses f t u v ↔ min a b ≤ t ∧ t < max a b := by
  simp only [Crosses, hu, hv]

omit [Fintype V] [DecidableEq V] in
/-- The reference sweep computes exactly the specified discrete object. -/
theorem sweep_correct (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ) :
    sweepGraph G f threshold = discreteReebGraph G f threshold := by
  rfl

omit [Fintype V] [DecidableEq V] in
/-- Every output node is exactly one support component at exactly one slice. -/
theorem node_correctness (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ)
    (x : SliceNode G f threshold) :
    ∃ i c, x = Sigma.mk i c := by
  rcases x with ⟨i, c⟩
  exact ⟨i, c, rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- Output adjacency is equivalent to consecutive-slice support overlap. -/
theorem transition_correctness (G : SimpleGraph V) (f : V → ℝ)
    {s : ℕ} (threshold : Fin s → ℝ)
    (x y : SliceNode G f threshold) :
    (discreteReebGraph G f threshold).Adj x y ↔
      (((x.1.1 + 1 = y.1.1) ∨ (y.1.1 + 1 = x.1.1)) ∧
        SliceOverlap G f threshold x y) := by
  rfl

end DiscreteGraph

end ReebGraph
