import Mathlib

/-!
# Support-induced point-cloud Reeb graph formalization

This file develops the finite crossing-edge theory and a conditional continuum
approximation theorem in functional Gromov--Hausdorff distance.  All stated
Lean results are proved.  A continuous height-controlled forward map, finite
incidence reflection, the clean deterministic error bound, and asymptotic
consistency are formalized.  Quotient-band lifting is derived with arbitrarily
small slack from tame level fibers and local path-connectedness; no global Reeb
section or Morse-handle formalization is required by the main theorem.

The paper-facing consistency theorem is graph-agnostic: dense sampling and a
two-sided proximity-graph sandwich imply the graph-geometric hypotheses, while
componentwise quadratic level crossings imply active support coverage.  The
regular, minimum, maximum, and saddle scalar normal forms are verified with
explicit constants.  Deriving uniform global constants and tame fibers from a
classical compact-manifold Morse hypothesis remains outside this file because
Mathlib does not currently provide the Morse lemma.

The base theory does not include diffusion condensation.  Optional smoothing is
treated as preprocessing before the finite graph and filter appearing here are
constructed.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

/-! ## Crossing-edge construction -/

section Crossing

variable {V : Type*}

/-- An edge crosses `t` when `t` lies in the half-open interval between its
endpoint filter values. -/
def Crosses (f : V → ℝ) (t : ℝ) (u v : V) : Prop :=
  min (f u) (f v) ≤ t ∧ t < max (f u) (f v)

theorem crosses_comm (f : V → ℝ) (t : ℝ) (u v : V) :
    Crosses f t u v ↔ Crosses f t v u := by
  simp only [Crosses, min_comm, max_comm]

theorem not_crosses_of_eq (f : V → ℝ) (t : ℝ) {u v : V}
    (h : f u = f v) : ¬Crosses f t u v := by
  simp only [Crosses, h, min_self, max_self]
  exact fun hcross => (not_lt_of_ge hcross.1) hcross.2

/-- Every edge with distinct endpoint values crosses the midpoint between
those values. -/
theorem crosses_midpoint_of_lt (f : V → ℝ) {u v : V}
    (h : f u < f v) : Crosses f ((f u + f v) / 2) u v := by
  rw [Crosses, min_eq_left h.le, max_eq_right h.le]
  constructor <;> linarith

/-- Uniform scalar error preserves a crossing when the true endpoint values
straddle the threshold with the corresponding margin. -/
theorem crosses_of_approximation_margin
    (ftrue fhat : V → ℝ) {u v : V} {t ε : ℝ}
    (herr : ∀ w, |fhat w - ftrue w| ≤ ε)
    (hu : ftrue u + ε < t) (hv : t < ftrue v - ε) :
    Crosses fhat t u v := by
  have huDiff : fhat u - ftrue u ≤ ε :=
    (le_abs_self (fhat u - ftrue u)).trans (herr u)
  have hvDiff : ftrue v - fhat v ≤ ε := by
    have hneg := (neg_le_abs (fhat v - ftrue v)).trans (herr v)
    linarith
  have hbelow : fhat u < t := by linarith
  have habove : t < fhat v := by linarith
  exact ⟨(min_le_left _ _).trans hbelow.le,
    habove.trans_le (le_max_right _ _)⟩

theorem crosses_iff_oriented
    (f : V → ℝ) (t : ℝ) (u v : V) :
    Crosses f t u v ↔
      (f u ≤ t ∧ t < f v) ∨ (f v ≤ t ∧ t < f u) := by
  rw [Crosses, min_le_iff, lt_max_iff]
  constructor
  · rintro ⟨hu | hv, hu' | hv'⟩
    · exact (not_lt_of_ge hu hu').elim
    · exact Or.inl ⟨hu, hv'⟩
    · exact Or.inr ⟨hv, hu'⟩
    · exact (not_lt_of_ge hv hv').elim
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact ⟨Or.inl hu, Or.inr hv⟩
    · exact ⟨Or.inr hv, Or.inl hu⟩

/-- Two thresholds crossed by the same edge differ by at most that edge's
scalar oscillation. -/
theorem abs_sub_le_edge_oscillation_of_crosses
    (f : V → ℝ) {s t : ℝ} {u v : V}
    (hs : Crosses f s u v) (ht : Crosses f t u v) :
    |s - t| ≤ |f u - f v| := by
  rw [abs_sub_le_iff]
  have hwidth : max (f u) (f v) - min (f u) (f v) = |f u - f v| := by
    simpa only [abs_sub_comm] using max_sub_min_eq_abs (f u) (f v)
  constructor <;> linarith [hs.1, hs.2.le, ht.1, ht.2.le]

/-- A crossed threshold is no farther from either endpoint value than the
edge's scalar oscillation. -/
theorem abs_threshold_sub_endpoint_le_of_crosses
    (f : V → ℝ) {t : ℝ} {u v : V}
    (hcross : Crosses f t u v) :
    |t - f u| ≤ |f u - f v| := by
  have hwidth : max (f u) (f v) - min (f u) (f v) = |f u - f v| := by
    simpa only [abs_sub_comm] using max_sub_min_eq_abs (f u) (f v)
  rw [abs_sub_le_iff]
  constructor <;>
    linarith [hcross.1, hcross.2.le, min_le_left (f u) (f v),
      min_le_right (f u) (f v), le_max_left (f u) (f v),
      le_max_right (f u) (f v)]

/-- Two thresholds determine the same cut of the finite vertex values. -/
def ThresholdEquivalent (f : V → ℝ) (t s : ℝ) : Prop :=
  ∀ v, (f v ≤ t ↔ f v ≤ s) ∧ (t < f v ↔ s < f v)

/-- Every threshold in an observed-value gap is equivalent to the midpoint of
that gap. -/
theorem thresholdEquivalent_midpoint_of_gap
    (f : V → ℝ) {a b t : ℝ}
    (hat : a ≤ t) (htb : t < b)
    (hgap : ∀ v, f v ≤ a ∨ b ≤ f v) :
    ThresholdEquivalent f t ((a + b) / 2) := by
  intro v
  rcases hgap v with hv | hv
  · constructor
    · constructor <;> intro <;> linarith
    · constructor <;> intro h <;> linarith
  · constructor
    · constructor <;> intro h <;> linarith
    · constructor <;> intro <;> linarith

theorem crosses_iff_of_thresholdEquivalent
    (f : V → ℝ) {t s : ℝ} (h : ThresholdEquivalent f t s) (u v : V) :
    Crosses f t u v ↔ Crosses f s u v := by
  rw [crosses_iff_oriented, crosses_iff_oriented]
  rcases h u with ⟨huLower, huUpper⟩
  rcases h v with ⟨hvLower, hvUpper⟩
  constructor
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact Or.inl ⟨huLower.mp hu, hvUpper.mp hv⟩
    · exact Or.inr ⟨hvLower.mp hv, huUpper.mp hu⟩
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact Or.inl ⟨huLower.mpr hu, hvUpper.mpr hv⟩
    · exact Or.inr ⟨hvLower.mpr hv, huUpper.mpr hu⟩

/-- The spanning subgraph containing exactly the edges that cross `t`.
Inactive vertices remain in the ambient vertex type but are removed when
forming `ActiveVertex`. -/
def crossingGraph (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ Crosses f t u v
  symm u v h := ⟨G.symm h.1, (crosses_comm f t u v).mp h.2⟩
  loopless v h := G.loopless v h.1

/-- Vertices incident to at least one edge crossing `t`. -/
def IsActiveVertex (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) (v : V) : Prop :=
  ∃ w, (crossingGraph G f t).Adj v w

/-- Activity of a fixed vertex is interval-convex in the threshold.  Below
the vertex value use the lower active witness; above it use the upper one. -/
theorem isActiveVertex_between
    (G : SimpleGraph V) (f : V → ℝ) {s t r : ℝ} {u : V}
    (hst : s ≤ t) (htr : t ≤ r)
    (hs : IsActiveVertex G f s u) (hr : IsActiveVertex G f r u) :
    IsActiveVertex G f t u := by
  by_cases hut : f u ≤ t
  · rcases hr with ⟨v, huv, hcross⟩
    refine ⟨v, huv, ?_⟩
    exact ⟨(min_le_left (f u) (f v)).trans hut,
      htr.trans_lt hcross.2⟩
  · rcases hs with ⟨v, huv, hcross⟩
    refine ⟨v, huv, ?_⟩
    exact ⟨hcross.1.trans hst,
      (lt_of_not_ge hut).trans_le (le_max_left (f u) (f v))⟩

/-- The vertex type of the nonempty part of a crossing-edge slice. -/
def ActiveVertex (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) :=
  {v : V // IsActiveVertex G f t v}

/-- The original graph induced by endpoints of edges crossing `t`.  Crossing
edges witness proximity to the level, while all original edges between active
endpoints retain tangential connectivity. -/
def supportSliceGraph (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ IsActiveVertex G f t u ∧ IsActiveVertex G f t v
  symm _ _ h := ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless v h := G.loopless v h.1

theorem crossingGraph_adj_iff_of_thresholdEquivalent
    (G : SimpleGraph V) (f : V → ℝ) {t s : ℝ}
    (h : ThresholdEquivalent f t s) (u v : V) :
    (crossingGraph G f t).Adj u v ↔ (crossingGraph G f s).Adj u v := by
  exact and_congr_right (fun _ => crosses_iff_of_thresholdEquivalent f h u v)

theorem isActiveVertex_iff_of_thresholdEquivalent
    (G : SimpleGraph V) (f : V → ℝ) {t s : ℝ}
    (h : ThresholdEquivalent f t s) (u : V) :
    IsActiveVertex G f t u ↔ IsActiveVertex G f s u := by
  constructor
  · rintro ⟨v, huv⟩
    exact ⟨v, (crossingGraph_adj_iff_of_thresholdEquivalent G f h u v).mp huv⟩
  · rintro ⟨v, huv⟩
    exact ⟨v, (crossingGraph_adj_iff_of_thresholdEquivalent G f h u v).mpr huv⟩

/-- The support-induced slice graph is constant inside one threshold cell. -/
theorem supportSliceGraph_eq_of_thresholdEquivalent
    (G : SimpleGraph V) (f : V → ℝ) {t s : ℝ}
    (h : ThresholdEquivalent f t s) :
    supportSliceGraph G f t = supportSliceGraph G f s := by
  ext u v
  exact and_congr
    (Iff.rfl)
    (and_congr
      (isActiveVertex_iff_of_thresholdEquivalent G f h u)
      (isActiveVertex_iff_of_thresholdEquivalent G f h v))

/-- Replacing a threshold inside an observed-value gap by the gap midpoint
does not change the support-induced slice graph. -/
theorem supportSliceGraph_eq_midpoint_of_gap
    (G : SimpleGraph V) (f : V → ℝ) {a b t : ℝ}
    (hat : a ≤ t) (htb : t < b)
    (hgap : ∀ v, f v ≤ a ∨ b ≤ f v) :
    supportSliceGraph G f t = supportSliceGraph G f ((a + b) / 2) :=
  supportSliceGraph_eq_of_thresholdEquivalent G f
    (thresholdEquivalent_midpoint_of_gap f hat htb hgap)

/-- Equivalent thresholds have canonically equivalent types of active
vertices; the equivalence preserves the underlying ambient vertex. -/
def activeVertexEquivOfThresholdEquivalent
    (G : SimpleGraph V) (f : V → ℝ) {t s : ℝ}
    (h : ThresholdEquivalent f t s) :
    ActiveVertex G f t ≃ ActiveVertex G f s where
  toFun u := ⟨u.1, (isActiveVertex_iff_of_thresholdEquivalent G f h u.1).mp u.2⟩
  invFun u := ⟨u.1, (isActiveVertex_iff_of_thresholdEquivalent G f h u.1).mpr u.2⟩
  left_inv u := Subtype.ext rfl
  right_inv u := Subtype.ext rfl

@[simp] theorem activeVertexEquivOfThresholdEquivalent_coe
    (G : SimpleGraph V) (f : V → ℝ) {t s : ℝ}
    (h : ThresholdEquivalent f t s) (u : ActiveVertex G f t) :
    (activeVertexEquivOfThresholdEquivalent G f h u).1 = u.1 :=
  rfl

theorem crossing_adj_supportSliceGraph_adj
    (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) {u v : V}
    (h : (crossingGraph G f t).Adj u v) :
    (supportSliceGraph G f t).Adj u v :=
  ⟨h.1, ⟨v, h⟩, ⟨u, (crossingGraph G f t).symm h⟩⟩

theorem crossingGraph_le_supportSliceGraph
    (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) :
    crossingGraph G f t ≤ supportSliceGraph G f t := by
  intro u v h
  exact crossing_adj_supportSliceGraph_adj G f t h

theorem isActiveVertex_mono
    {G H : SimpleGraph V} (hGH : G ≤ H) (f : V → ℝ) (t : ℝ) {u : V}
    (hu : IsActiveVertex G f t u) : IsActiveVertex H f t u := by
  rcases hu with ⟨v, huv, hcross⟩
  exact ⟨v, hGH huv, hcross⟩

/-- Enlarging the neighborhood graph can only add edges and active vertices to
the support-induced slice. -/
theorem supportSliceGraph_mono
    {G H : SimpleGraph V} (hGH : G ≤ H) (f : V → ℝ) (t : ℝ) :
    supportSliceGraph G f t ≤ supportSliceGraph H f t := by
  intro u v huv
  exact ⟨hGH huv.1,
    isActiveVertex_mono hGH f t huv.2.1,
    isActiveVertex_mono hGH f t huv.2.2⟩

/-- Two active vertices belong to the same support-induced slice component. -/
def SameSupportComponent (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    (u v : ActiveVertex G f t) : Prop :=
  (supportSliceGraph G f t).Reachable u.1 v.1

/-- Reachability in a support-induced slice, restricted to active vertices,
is an equivalence relation. -/
def supportComponentSetoid (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) :
    Setoid (ActiveVertex G f t) where
  r := SameSupportComponent G f t
  iseqv := by
    constructor
    · intro u
      exact SimpleGraph.Reachable.refl u.1
    · intro u v huv
      exact huv.symm
    · intro u v w huv hvw
      exact huv.trans hvw

/-- Connected components of the support-induced slice graph at `t`. -/
def SupportComponent (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) :=
  Quotient (supportComponentSetoid G f t)

/-- The component quotients are canonically equivalent throughout a
threshold cell. -/
noncomputable def supportComponentEquivOfThresholdEquivalent
    (G : SimpleGraph V) (f : V → ℝ) {t s : ℝ}
    (h : ThresholdEquivalent f t s) :
    SupportComponent G f t ≃ SupportComponent G f s :=
  Quotient.congr (activeVertexEquivOfThresholdEquivalent G f h) (by
    intro u v
    change (supportSliceGraph G f t).Reachable u.1 v.1 ↔
      (supportSliceGraph G f s).Reachable u.1 v.1
    rw [supportSliceGraph_eq_of_thresholdEquivalent G f h])

/-- Compatibility aliases for the original crossing-only formalization. -/
abbrev SameCrossingComponent (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) :=
  SameSupportComponent G f t
abbrev crossingComponentSetoid (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) :=
  supportComponentSetoid G f t
abbrev CrossingComponent (G : SimpleGraph V) (f : V → ℝ) (t : ℝ) :=
  SupportComponent G f t

/-- Support component represented by an active vertex. -/
def componentOfActive (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    (u : ActiveVertex G f t) : SupportComponent G f t :=
  Quotient.mk (supportComponentSetoid G f t) u

/-- The original graph vertices represented by a support component. -/
noncomputable def componentSupport (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    (c : CrossingComponent G f t) : Set V := by
  refine Quotient.liftOn c (fun u => {v | Nonempty ((supportSliceGraph G f t).Walk u.1 v)}) ?_
  intro u v huv
  apply Set.ext
  intro w
  change (supportSliceGraph G f t).Reachable u.1 w ↔
    (supportSliceGraph G f t).Reachable v.1 w
  constructor
  · intro huw
    exact huv.symm.trans huw
  · intro hvw
    exact huv.trans hvw

theorem componentSupport_nonempty (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    (c : CrossingComponent G f t) :
    (componentSupport G f t c).Nonempty := by
  refine Quotient.inductionOn c ?_
  intro u
  exact ⟨u.1, SimpleGraph.Reachable.refl u.1⟩

theorem mem_componentSupport_componentOfActive
    (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    (u : ActiveVertex G f t) :
    u.1 ∈ componentSupport G f t (componentOfActive G f t u) := by
  change (supportSliceGraph G f t).Reachable u.1 u.1
  exact SimpleGraph.Reachable.refl u.1

/-- Every vertex represented by a support component is incident to a crossing
edge; inactive ambient vertices never enter component support. -/
theorem componentSupport_isActive (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    (c : CrossingComponent G f t) {v : V}
    (hv : v ∈ componentSupport G f t c) :
    IsActiveVertex G f t v := by
  have reachable_preserves_active :
      ∀ {x y : V}, (supportSliceGraph G f t).Reachable x y →
        IsActiveVertex G f t x → IsActiveVertex G f t y := by
    intro x y hxy hx
    rcases hxy with ⟨p⟩
    induction p with
    | nil => exact hx
    | @cons x y z h path ih =>
        apply ih
        exact h.2.2
  refine Quotient.inductionOn c ?_ hv
  intro u huv
  change (supportSliceGraph G f t).Reachable u.1 v at huv
  exact reachable_preserves_active huv u.2

/-- Supports of distinct support components at a fixed threshold are
disjoint. -/
theorem crossingComponent_eq_of_support_intersects
    (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    {c d : CrossingComponent G f t}
    (h : (componentSupport G f t c ∩ componentSupport G f t d).Nonempty) :
    c = d := by
  refine Quotient.inductionOn₂ c d ?_ h
  intro u v huv
  rcases huv with ⟨w, huw, hvw⟩
  change (supportSliceGraph G f t).Reachable u.1 w at huw
  change (supportSliceGraph G f t).Reachable v.1 w at hvw
  apply Quotient.sound
  change SameSupportComponent G f t u v
  exact huw.trans hvw.symm

theorem crossingComponent_support_intersects_iff
    (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    (c d : CrossingComponent G f t) :
    (componentSupport G f t c ∩ componentSupport G f t d).Nonempty ↔ c = d := by
  constructor
  · exact crossingComponent_eq_of_support_intersects G f t
  · intro h
    subst d
    rcases componentSupport_nonempty G f t c with ⟨v, hv⟩
    exact ⟨v, hv, hv⟩

/-- Any two vertices in one component support are connected in the
support-induced slice graph. -/
theorem componentSupport_reachable
    (G : SimpleGraph V) (f : V → ℝ) (t : ℝ)
    (c : CrossingComponent G f t) {u v : V}
    (hu : u ∈ componentSupport G f t c)
    (hv : v ∈ componentSupport G f t c) :
    (supportSliceGraph G f t).Reachable u v := by
  refine Quotient.inductionOn c ?_ hu hv
  intro w hwu hwv
  change (supportSliceGraph G f t).Reachable w.1 u at hwu
  change (supportSliceGraph G f t).Reachable w.1 v at hwv
  exact hwu.symm.trans hwv

end Crossing

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

/-! ## Multigraph reduction -/

/-- A finite undirected incidence multigraph.  Edge identity is retained, so
parallel edges are supported. -/
structure FiniteMultigraph where
  Vertex : Type*
  Edge : Type*
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  vertexDecidableEq : DecidableEq Vertex
  edgeDecidableEq : DecidableEq Edge
  endpoints : Edge → Sym2 Vertex

attribute [instance] FiniteMultigraph.vertexFintype
attribute [instance] FiniteMultigraph.edgeFintype
attribute [instance] FiniteMultigraph.vertexDecidableEq
attribute [instance] FiniteMultigraph.edgeDecidableEq

/-- The loopless simple graph underlying an incidence multigraph.  Parallel
edges induce the same adjacency but remain distinct in the multigraph's edge
type and therefore still contribute separately to cycle rank. -/
noncomputable def FiniteMultigraph.incidenceGraph (G : FiniteMultigraph) :
    SimpleGraph G.Vertex where
  Adj u v := u ≠ v ∧ ∃ e, G.endpoints e = s(u, v)
  symm := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with ⟨e, he⟩
    exact ⟨e, by simpa only [Sym2.eq_swap] using he⟩
  loopless := by
    intro v h
    exact h.1 rfl

/-- Number of connected components of an incidence multigraph, including
isolated vertices. -/
noncomputable def componentCount (G : FiniteMultigraph) : ℕ := by
  classical
  exact Fintype.card G.incidenceGraph.ConnectedComponent

/-- First Betti number via the Euler characteristic formula. -/
noncomputable def firstBetti (G : FiniteMultigraph) : ℕ :=
  Fintype.card G.Edge + componentCount G - Fintype.card G.Vertex

/-- Integer-valued cycle rank, useful before proving nonnegativity of the Euler
formula for every finite incidence multigraph. -/
noncomputable def cycleRankInt (G : FiniteMultigraph) : ℤ :=
  (Fintype.card G.Edge : ℤ) - Fintype.card G.Vertex + componentCount G

/-- The integer cycle rank agrees with the natural-valued Euler formula once
the latter is known not to truncate. -/
theorem cycleRankInt_eq_firstBetti_of_vertex_le
    (G : FiniteMultigraph)
    (h : Fintype.card G.Vertex ≤ Fintype.card G.Edge + componentCount G) :
    cycleRankInt G = (firstBetti G : ℤ) := by
  simp only [cycleRankInt, firstBetti]
  omega

/-- Removing one degree-two vertex and replacing its two incident edges by one
edge preserves the Euler cycle rank whenever component count is preserved. -/
theorem cycleRankInt_preserved_of_suppression_counts
    (G H : FiniteMultigraph)
    (hedges : Fintype.card H.Edge + 1 = Fintype.card G.Edge)
    (hvertices : Fintype.card H.Vertex + 1 = Fintype.card G.Vertex)
    (hcomponents : componentCount H = componentCount G) :
    cycleRankInt H = cycleRankInt G := by
  simp only [cycleRankInt]
  omega

/-- The natural-valued Euler formula is preserved by the same local count
change.  No separate nonnegativity argument is needed because simultaneous
successor cancellation is valid for truncated natural subtraction. -/
theorem firstBetti_preserved_of_suppression_counts
    (G H : FiniteMultigraph)
    (hedges : Fintype.card H.Edge + 1 = Fintype.card G.Edge)
    (hvertices : Fintype.card H.Vertex + 1 = Fintype.card G.Vertex)
    (hcomponents : componentCount H = componentCount G) :
    firstBetti H = firstBetti G := by
  simp only [firstBetti]
  omega

/-- Certificate exposed by one valid degree-two suppression step.  The future
concrete contraction operation must construct this certificate from its local
degree-two hypotheses. -/
structure IsDegreeTwoSuppression (G H : FiniteMultigraph) : Prop where
  edge_count : Fintype.card H.Edge + 1 = Fintype.card G.Edge
  vertex_count : Fintype.card H.Vertex + 1 = Fintype.card G.Vertex
  component_count : componentCount H = componentCount G

theorem IsDegreeTwoSuppression.preserves_firstBetti
    {G H : FiniteMultigraph} (h : IsDegreeTwoSuppression G H) :
    firstBetti H = firstBetti G :=
  firstBetti_preserved_of_suppression_counts G H
    h.edge_count h.vertex_count h.component_count

theorem IsDegreeTwoSuppression.preserves_cycleRankInt
    {G H : FiniteMultigraph} (h : IsDegreeTwoSuppression G H) :
    cycleRankInt H = cycleRankInt G :=
  cycleRankInt_preserved_of_suppression_counts G H
    h.edge_count h.vertex_count h.component_count

/-- Reflexive-transitive closure of valid local degree-two suppressions. -/
inductive IsDegreeTwoReduction : FiniteMultigraph → FiniteMultigraph → Prop where
  | refl (G : FiniteMultigraph) : IsDegreeTwoReduction G G
  | step {G H K : FiniteMultigraph}
      (head : IsDegreeTwoSuppression G H)
      (tail : IsDegreeTwoReduction H K) : IsDegreeTwoReduction G K

theorem IsDegreeTwoReduction.trans
    {G H K : FiniteMultigraph}
    (hGH : IsDegreeTwoReduction G H) (hHK : IsDegreeTwoReduction H K) :
    IsDegreeTwoReduction G K := by
  induction hGH with
  | refl => exact hHK
  | step head _ ih => exact .step head (ih hHK)

theorem IsDegreeTwoReduction.preserves_componentCount
    {G H : FiniteMultigraph} (h : IsDegreeTwoReduction G H) :
    componentCount H = componentCount G := by
  induction h with
  | refl => rfl
  | step head _ ih => exact ih.trans head.component_count

theorem IsDegreeTwoReduction.preserves_firstBetti
    {G H : FiniteMultigraph} (h : IsDegreeTwoReduction G H) :
    firstBetti H = firstBetti G := by
  induction h with
  | refl => rfl
  | step head _ ih => exact ih.trans head.preserves_firstBetti

theorem IsDegreeTwoReduction.preserves_cycleRankInt
    {G H : FiniteMultigraph} (h : IsDegreeTwoReduction G H) :
    cycleRankInt H = cycleRankInt G := by
  induction h with
  | refl => rfl
  | step head _ ih => exact ih.trans head.preserves_cycleRankInt

/-- Output contract for a degree-two reducer.  A concrete implementation cannot
return a graph without also proving that it arose by valid suppression steps. -/
structure DegreeTwoReductionResult (G : FiniteMultigraph) where
  graph : FiniteMultigraph
  certified : IsDegreeTwoReduction G graph

/-- Suppress maximal paths whose internal vertices have degree two, retaining
enough breakpoints to represent cycles and parallel edges.  The opaque identity
body is temporary; the dependent result type is the implementation contract. -/
opaque reduceDegreeTwo (G : FiniteMultigraph) : DegreeTwoReductionResult G :=
  ⟨G, IsDegreeTwoReduction.refl G⟩

theorem reduction_preserves_component_count (G : FiniteMultigraph) :
    componentCount (reduceDegreeTwo G).graph = componentCount G :=
  (reduceDegreeTwo G).certified.preserves_componentCount

theorem reduction_preserves_firstBetti (G : FiniteMultigraph) :
    firstBetti (reduceDegreeTwo G).graph = firstBetti G :=
  (reduceDegreeTwo G).certified.preserves_firstBetti

theorem reduction_preserves_cycleRankInt (G : FiniteMultigraph) :
    cycleRankInt (reduceDegreeTwo G).graph = cycleRankInt G :=
  (reduceDegreeTwo G).certified.preserves_cycleRankInt

/-! ## Scalar-resolution lemmas -/

section Resolution

variable {V : Type*}

/-- If every graph edge changes the filter by at most `ε`, then both endpoints
of an edge crossing `t` lie in the `ε`-thickened level band. -/
theorem crossing_edge_endpoints_mem_band
    (G : SimpleGraph V) (f : V → ℝ) {ε t : ℝ}
    (hε : ∀ ⦃u v⦄, G.Adj u v → |f u - f v| ≤ ε)
    {u v : V} (huv : G.Adj u v) (hcross : Crosses f t u v) :
    |f u - t| ≤ ε ∧ |f v - t| ≤ ε := by
  have huvε := hε huv
  have huv_bound : f u - f v ≤ ε :=
    (le_abs_self (f u - f v)).trans huvε
  have hvu_bound : f v - f u ≤ ε := by
    rw [← neg_sub (f u) (f v)]
    exact (neg_le_abs (f u - f v)).trans huvε
  rcases hcross with ⟨hmin, hmax⟩
  rcases le_total (f u) (f v) with huv_order | hvu_order
  · rw [min_eq_left huv_order] at hmin
    rw [max_eq_right huv_order] at hmax
    constructor <;> rw [abs_sub_le_iff] <;> constructor <;> linarith
  · rw [min_eq_right hvu_order] at hmin
    rw [max_eq_left hvu_order] at hmax
    constructor <;> rw [abs_sub_le_iff] <;> constructor <;> linarith

/-- A path in one support component stays within the thickened level band. -/
theorem support_component_mem_band
    (G : SimpleGraph V) (f : V → ℝ) {ε t : ℝ}
    (hε : ∀ ⦃u v⦄, G.Adj u v → |f u - f v| ≤ ε)
    (c : CrossingComponent G f t) :
    componentSupport G f t c ⊆ {v | |f v - t| ≤ ε} := by
  intro v hv
  rcases componentSupport_isActive G f t c hv with ⟨w, hvw⟩
  exact (crossing_edge_endpoints_mem_band G f hε hvw.1 hvw.2).1

variable [PseudoMetricSpace V]

/-- Edgewise filter oscillation is controlled by geometric edge length and
uniform filter-estimation error. -/
theorem estimated_edge_oscillation_bound
    (G : SimpleGraph V) (f fhat : V → ℝ)
    {L r η : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist u v ≤ r)
    (hη : ∀ x, |fhat x - f x| ≤ η)
    {u v : V} (huv : G.Adj u v) :
    |fhat u - fhat v| ≤ L * r + 2 * η := by
  calc
    |fhat u - fhat v| =
        |(fhat u - f u) + (f u - f v) + (f v - fhat v)| := by ring_nf
    _ ≤ |fhat u - f u| + |f u - f v| + |f v - fhat v| :=
      abs_add_three _ _ _
    _ ≤ η + (L * dist u v) + η := by
      exact add_le_add
        (add_le_add (hη u) (hL u v))
        (by simpa only [abs_sub_comm] using hη v)
    _ ≤ η + (L * r) + η := by
      gcongr
      exact hedge huv
    _ = L * r + 2 * η := by ring

/-- Quantization adds at most twice its uniform pointwise error to the edgewise
oscillation bound. -/
theorem quantized_edge_oscillation_bound
    (G : SimpleGraph V) (f fhat fquant : V → ℝ)
    {L r η q : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist u v ≤ r)
    (hη : ∀ x, |fhat x - f x| ≤ η)
    (hq : ∀ x, |fquant x - fhat x| ≤ q)
    {u v : V} (huv : G.Adj u v) :
    |fquant u - fquant v| ≤ L * r + 2 * η + 2 * q := by
  have hbase : |fhat u - fhat v| ≤ L * r + 2 * η :=
    estimated_edge_oscillation_bound G f fhat hL_nonneg hL hedge hη huv
  calc
    |fquant u - fquant v| =
        |(fquant u - fhat u) + (fhat u - fhat v) + (fhat v - fquant v)| := by
          ring_nf
    _ ≤ |fquant u - fhat u| + |fhat u - fhat v| + |fhat v - fquant v| :=
      abs_add_three _ _ _
    _ ≤ q + (L * r + 2 * η) + q := by
      exact add_le_add
        (add_le_add (hq u) hbase)
        (by simpa only [abs_sub_comm] using hq v)
    _ = L * r + 2 * η + 2 * q := by ring

omit [PseudoMetricSpace V] in
/-- The edgewise oscillation estimate when graph vertices are sample indices
rather than points of the ambient metric space. -/
theorem sampled_edge_oscillation_bound
    {M : Type*} [PseudoMetricSpace M]
    (G : SimpleGraph V) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    {L r η : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r)
    (hη : ∀ x, |fhat x - f (sample x)| ≤ η)
    {u v : V} (huv : G.Adj u v) :
    |fhat u - fhat v| ≤ L * r + 2 * η := by
  calc
    |fhat u - fhat v| =
        |(fhat u - f (sample u)) +
          (f (sample u) - f (sample v)) +
          (f (sample v) - fhat v)| := by ring_nf
    _ ≤ |fhat u - f (sample u)| +
          |f (sample u) - f (sample v)| +
          |f (sample v) - fhat v| := abs_add_three _ _ _
    _ ≤ η + L * dist (sample u) (sample v) + η := by
      exact add_le_add
        (add_le_add (hη u) (hL (sample u) (sample v)))
        (by simpa only [abs_sub_comm] using hη v)
    _ ≤ η + L * r + η := by
      gcongr
      exact hedge huv
    _ = L * r + 2 * η := by ring

omit [PseudoMetricSpace V] in
/-- Soundness at sampled vertices: the support of a discrete support
component maps into a controlled level band of the continuum filter. -/
theorem sampled_support_component_mem_continuum_band
    {M : Type*} [PseudoMetricSpace M]
    (G : SimpleGraph V) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    {L r η t : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r)
    (hη : ∀ x, |fhat x - f (sample x)| ≤ η)
    (c : SupportComponent G fhat t) :
    componentSupport G fhat t c ⊆
      {v | |f (sample v) - t| ≤ L * r + 3 * η} := by
  have hedgeOsc : ∀ ⦃u v⦄, G.Adj u v →
      |fhat u - fhat v| ≤ L * r + 2 * η := by
    intro u v huv
    exact sampled_edge_oscillation_bound G sample f fhat
      hL_nonneg hL hedge hη huv
  intro v hv
  have hvBand : |fhat v - t| ≤ L * r + 2 * η :=
    support_component_mem_band G fhat hedgeOsc c hv
  calc
    |f (sample v) - t| =
        |(f (sample v) - fhat v) + (fhat v - t)| := by ring_nf
    _ ≤ |f (sample v) - fhat v| + |fhat v - t| := abs_add _ _
    _ ≤ η + (L * r + 2 * η) := by
      exact add_le_add (by simpa only [abs_sub_comm] using hη v) hvBand
    _ = L * r + 3 * η := by ring

omit [PseudoMetricSpace V] in
/-- Quantized sampled filters have the expected additional `2*q` edgewise
oscillation. -/
theorem sampled_quantized_edge_oscillation_bound
    {M : Type*} [PseudoMetricSpace M]
    (G : SimpleGraph V) (sample : V → M) (f : M → ℝ)
    (fhat fquant : V → ℝ) {L r η q : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r)
    (hη : ∀ x, |fhat x - f (sample x)| ≤ η)
    (hq : ∀ x, |fquant x - fhat x| ≤ q)
    {u v : V} (huv : G.Adj u v) :
    |fquant u - fquant v| ≤ L * r + 2 * η + 2 * q := by
  have hbase : |fhat u - fhat v| ≤ L * r + 2 * η :=
    sampled_edge_oscillation_bound G sample f fhat
      hL_nonneg hL hedge hη huv
  calc
    |fquant u - fquant v| =
        |(fquant u - fhat u) + (fhat u - fhat v) +
          (fhat v - fquant v)| := by ring_nf
    _ ≤ |fquant u - fhat u| + |fhat u - fhat v| +
          |fhat v - fquant v| := abs_add_three _ _ _
    _ ≤ q + (L * r + 2 * η) + q := by
      exact add_le_add
        (add_le_add (hq u) hbase)
        (by simpa only [abs_sub_comm] using hq v)
    _ = L * r + 2 * η + 2 * q := by ring

omit [PseudoMetricSpace V] in
/-- Quantized version of sampled crossing-component soundness. -/
theorem sampled_quantized_component_mem_continuum_band
    {M : Type*} [PseudoMetricSpace M]
    (G : SimpleGraph V) (sample : V → M) (f : M → ℝ)
    (fhat fquant : V → ℝ) {L r η q t : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → dist (sample u) (sample v) ≤ r)
    (hη : ∀ x, |fhat x - f (sample x)| ≤ η)
    (hq : ∀ x, |fquant x - fhat x| ≤ q)
    (c : CrossingComponent G fquant t) :
    componentSupport G fquant t c ⊆
      {v | |f (sample v) - t| ≤ L * r + 3 * η + 3 * q} := by
  have hedgeOsc : ∀ ⦃u v⦄, G.Adj u v →
      |fquant u - fquant v| ≤ L * r + 2 * η + 2 * q := by
    intro u v huv
    exact sampled_quantized_edge_oscillation_bound G sample f fhat fquant
      hL_nonneg hL hedge hη hq huv
  intro v hv
  have hvBand : |fquant v - t| ≤ L * r + 2 * η + 2 * q :=
    support_component_mem_band G fquant hedgeOsc c hv
  have htrueQuant : |f (sample v) - fquant v| ≤ η + q := by
    calc
      |f (sample v) - fquant v| =
          |(f (sample v) - fhat v) + (fhat v - fquant v)| := by ring_nf
      _ ≤ |f (sample v) - fhat v| + |fhat v - fquant v| := abs_add _ _
      _ ≤ η + q := add_le_add
        (by simpa only [abs_sub_comm] using hη v)
        (by simpa only [abs_sub_comm] using hq v)
  calc
    |f (sample v) - t| =
        |(f (sample v) - fquant v) + (fquant v - t)| := by ring_nf
    _ ≤ |f (sample v) - fquant v| + |fquant v - t| := abs_add _ _
    _ ≤ (η + q) + (L * r + 2 * η + 2 * q) :=
      add_le_add htrueQuant hvBand
    _ = L * r + 3 * η + 3 * q := by ring

end Resolution

/-! ## Conditional continuum approximation

The continuum Reeb quotient and discrete graph realization are explicit below.
The specialized comparison metric remains abstract until its interleaving or
functional-distortion theory is formalized.
-/

/-- Minimal data retained by a filtered Reeb graph.  The quotient map and graph
finiteness conditions will be added when the continuum construction is
formalized. -/
structure FilteredReebGraph where
  Carrier : Type
  topology : TopologicalSpace Carrier
  height : Carrier → ℝ

attribute [instance] FilteredReebGraph.topology

instance : Inhabited FilteredReebGraph where
  default :=
    { Carrier := Empty
      topology := ⊥
      height := Empty.elim }

/-! ### Topological realization of a simple graph -/

/-- A wrapper giving an arbitrary graph vertex type the discrete topology. -/
def GraphVertex (V : Type*) := V

instance graphVertexTopology (V : Type*) : TopologicalSpace (GraphVertex V) := ⊥
instance graphVertexDiscreteTopology (V : Type*) : DiscreteTopology (GraphVertex V) := ⟨rfl⟩

/-- An oriented presentation of an undirected edge.  Opposite orientations
will be identified in the realization quotient. -/
def OrientedEdge {V : Type*} (G : SimpleGraph V) :=
  {p : V × V // G.Adj p.1 p.2}

instance orientedEdgeTopology {V : Type*} (G : SimpleGraph V) :
    TopologicalSpace (OrientedEdge G) := ⊥
instance orientedEdgeDiscreteTopology {V : Type*} (G : SimpleGraph V) :
    DiscreteTopology (OrientedEdge G) := ⟨rfl⟩

namespace OrientedEdge

variable {V : Type*} {G : SimpleGraph V}

def source (e : OrientedEdge G) : V := e.1.1
def target (e : OrientedEdge G) : V := e.1.2

def reverse (e : OrientedEdge G) : OrientedEdge G :=
  ⟨(e.target, e.source), G.symm e.2⟩

@[simp] theorem source_reverse (e : OrientedEdge G) : e.reverse.source = e.target := rfl
@[simp] theorem target_reverse (e : OrientedEdge G) : e.reverse.target = e.source := rfl

end OrientedEdge

/-- The closed unit interval used to parametrize graph edges. -/
abbrev GraphUnitInterval := Set.Icc (0 : ℝ) 1

def graphUnitZero : GraphUnitInterval := ⟨0, by norm_num⟩
def graphUnitOne : GraphUnitInterval := ⟨1, by norm_num⟩

def graphUnitReverse (s : GraphUnitInterval) : GraphUnitInterval :=
  ⟨1 - s.1, by constructor <;> linarith [s.2.1, s.2.2]⟩

@[simp] theorem graphUnitReverse_value (s : GraphUnitInterval) :
    (graphUnitReverse s).1 = 1 - s.1 := rfl

/-- Before gluing, a graph realization is the disjoint union of discrete
vertices and one closed interval for each oriented edge. -/
def GraphRealizationRaw {V : Type*} (G : SimpleGraph V) :=
  GraphVertex V ⊕ (OrientedEdge G × GraphUnitInterval)

instance graphRealizationRawTopology {V : Type*} (G : SimpleGraph V) :
    TopologicalSpace (GraphRealizationRaw G) :=
  inferInstanceAs
    (TopologicalSpace (GraphVertex V ⊕ (OrientedEdge G × GraphUnitInterval)))

/-- Generating identifications for the graph realization: interval endpoints
are attached to their vertices and opposite orientations describe the same
geometric edge. -/
inductive GraphGlue {V : Type*} (G : SimpleGraph V) :
    GraphRealizationRaw G → GraphRealizationRaw G → Prop
  | source (e : OrientedEdge G) :
      GraphGlue G (.inl e.source) (.inr (e, graphUnitZero))
  | target (e : OrientedEdge G) :
      GraphGlue G (.inl e.target) (.inr (e, graphUnitOne))
  | reverse (e : OrientedEdge G) (s : GraphUnitInterval) :
      GraphGlue G (.inr (e, s)) (.inr (e.reverse, graphUnitReverse s))

/-- Linear interpolation of a vertex height along every oriented edge. -/
def graphRealizationRawHeight
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ) :
    GraphRealizationRaw G → ℝ
  | .inl v => height v
  | .inr (e, s) => (1 - s.1) * height e.source + s.1 * height e.target

theorem graphGlue_preserves_height
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ)
    {x y : GraphRealizationRaw G} (hxy : GraphGlue G x y) :
    graphRealizationRawHeight height x = graphRealizationRawHeight height y := by
  cases hxy with
  | source e => simp [graphRealizationRawHeight, graphUnitZero]
  | target e => simp [graphRealizationRawHeight, graphUnitOne]
  | reverse e s =>
      simp only [graphRealizationRawHeight, graphUnitReverse_value,
        OrientedEdge.source_reverse, OrientedEdge.target_reverse]
      ring

theorem graphEqvGen_preserves_height
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ)
    {x y : GraphRealizationRaw G}
    (hxy : Relation.EqvGen (GraphGlue G) x y) :
    graphRealizationRawHeight height x = graphRealizationRawHeight height y := by
  induction hxy with
  | rel x y h => exact graphGlue_preserves_height height h
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

theorem continuous_graphRealizationRawHeight
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ) :
    Continuous (graphRealizationRawHeight height : GraphRealizationRaw G → ℝ) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_of_discreteTopology
  · have hs : Continuous
        (fun p : OrientedEdge G × GraphUnitInterval => p.2.1) :=
      continuous_subtype_val.comp continuous_snd
    have hsource : Continuous
        (fun p : OrientedEdge G × GraphUnitInterval => height p.1.source) :=
      (show Continuous (fun e : OrientedEdge G => height e.source) from
        continuous_of_discreteTopology).comp continuous_fst
    have htarget : Continuous
        (fun p : OrientedEdge G × GraphUnitInterval => height p.1.target) :=
      (show Continuous (fun e : OrientedEdge G => height e.target) from
        continuous_of_discreteTopology).comp continuous_fst
    exact ((continuous_const.sub hs).mul hsource).add (hs.mul htarget)

/-- The usual one-dimensional CW realization of a simple graph, constructed
as the quotient of its vertices and edge intervals by endpoint attachment and
orientation reversal. -/
def SimpleGraphRealization {V : Type*} (G : SimpleGraph V) :=
  Quotient (Relation.EqvGen.setoid (GraphGlue G))

instance simpleGraphRealizationTopology {V : Type*} (G : SimpleGraph V) :
    TopologicalSpace (SimpleGraphRealization G) :=
  instTopologicalSpaceQuotient

def graphRealizationQuotientMap {V : Type*} (G : SimpleGraph V) :
    GraphRealizationRaw G → SimpleGraphRealization G :=
  Quotient.mk (Relation.EqvGen.setoid (GraphGlue G))

theorem continuous_graphRealizationQuotientMap
    {V : Type*} (G : SimpleGraph V) :
    Continuous (graphRealizationQuotientMap G) :=
  continuous_quotient_mk'

def graphRealizationVertex
    {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraphRealization G :=
  graphRealizationQuotientMap G (.inl v)

def graphRealizationEdgePoint
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G)
    (s : GraphUnitInterval) : SimpleGraphRealization G :=
  graphRealizationQuotientMap G (.inr (e, s))

theorem graphRealization_source_glue
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G) :
    graphRealizationVertex G e.source =
      graphRealizationEdgePoint G e graphUnitZero := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (GraphGlue.source e)

theorem graphRealization_target_glue
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G) :
    graphRealizationVertex G e.target =
      graphRealizationEdgePoint G e graphUnitOne := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (GraphGlue.target e)

theorem graphRealization_reverse_glue
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G)
    (s : GraphUnitInterval) :
    graphRealizationEdgePoint G e s =
      graphRealizationEdgePoint G e.reverse (graphUnitReverse s) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (GraphGlue.reverse e s)

/-- Canonical path traversing one oriented edge of a graph realization. -/
def graphRealizationEdgePath
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G) :
    Path (graphRealizationVertex G e.source)
      (graphRealizationVertex G e.target) where
  toFun s := graphRealizationEdgePoint G e s
  continuous_toFun :=
    (continuous_graphRealizationQuotientMap G).comp
      (continuous_inr.comp (continuous_const.prod_mk continuous_id))
  source' := (graphRealization_source_glue G e).symm
  target' := (graphRealization_target_glue G e).symm

/-- Contract an edge parameter linearly toward its source endpoint. -/
def graphUnitContractToSource
    (s t : GraphUnitInterval) : GraphUnitInterval :=
  ⟨(1 - t.1) * s.1, by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr t.2.2) s.2.1
    · calc
        (1 - t.1) * s.1 ≤ 1 * s.1 :=
          mul_le_mul_of_nonneg_right (by linarith [t.2.1]) s.2.1
        _ = s.1 := one_mul _
        _ ≤ 1 := s.2.2⟩

theorem continuous_graphUnitContractToSource (s : GraphUnitInterval) :
    Continuous (graphUnitContractToSource s) := by
  apply Continuous.subtype_mk
  exact (continuous_const.sub continuous_subtype_val).mul continuous_const

/-- The partial edge path from an arbitrary point back to the source vertex. -/
def graphRealizationEdgeToSourcePath
    {V : Type*} (G : SimpleGraph V) (e : OrientedEdge G)
    (s : GraphUnitInterval) :
    Path (graphRealizationEdgePoint G e s)
      (graphRealizationVertex G e.source) where
  toFun t := graphRealizationEdgePoint G e (graphUnitContractToSource s t)
  continuous_toFun :=
    (continuous_graphRealizationQuotientMap G).comp
      (continuous_inr.comp
        (continuous_const.prod_mk (continuous_graphUnitContractToSource s)))
  source' := by
    apply congrArg (graphRealizationEdgePoint G e)
    apply Subtype.ext
    simp [graphUnitContractToSource]
  target' := by
    change graphRealizationEdgePoint G e (graphUnitContractToSource s 1) =
      graphRealizationVertex G e.source
    rw [show graphUnitContractToSource s 1 = graphUnitZero by
      apply Subtype.ext
      simp [graphUnitContractToSource, graphUnitZero]]
    exact (graphRealization_source_glue G e).symm

/-- The piecewise-linear height descended to the graph realization. -/
noncomputable def graphRealizationHeight
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ) :
    SimpleGraphRealization G → ℝ :=
  Quotient.lift (graphRealizationRawHeight height)
    (fun _ _ h => graphEqvGen_preserves_height height h)

@[simp] theorem graphRealizationHeight_quotientMap
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ)
    (x : GraphRealizationRaw G) :
    graphRealizationHeight G height (graphRealizationQuotientMap G x) =
      graphRealizationRawHeight height x :=
  rfl

@[simp] theorem graphRealizationHeight_vertex
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ) (v : V) :
    graphRealizationHeight G height (graphRealizationVertex G v) = height v :=
  rfl

@[simp] theorem graphRealizationHeight_edgePoint
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ)
    (e : OrientedEdge G) (s : GraphUnitInterval) :
    graphRealizationHeight G height (graphRealizationEdgePoint G e s) =
      (1 - s.1) * height e.source + s.1 * height e.target :=
  rfl

theorem continuous_graphRealizationHeight
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ) :
    Continuous (graphRealizationHeight G height) := by
  apply (continuous_graphRealizationRawHeight height).quotient_lift

/-- An interior edge point can be anchored at its source without leaving the
input scalar band by more than the height oscillation of that edge. -/
theorem joinedIn_graphRealization_edgePoint_to_source
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ)
    {a b e : ℝ} (he : 0 ≤ e) (edge : OrientedEdge G)
    (hgap : |height edge.source - height edge.target| ≤ e)
    (s : GraphUnitInterval)
    (hs : a ≤ graphRealizationHeight G height
        (graphRealizationEdgePoint G edge s) ∧
      graphRealizationHeight G height
        (graphRealizationEdgePoint G edge s) ≤ b) :
    JoinedIn
      {z | a - e ≤ graphRealizationHeight G height z ∧
        graphRealizationHeight G height z ≤ b + e}
      (graphRealizationEdgePoint G edge s)
      (graphRealizationVertex G edge.source) := by
  let hsval := graphRealizationHeight G height
    (graphRealizationEdgePoint G edge s)
  have hsourceClose : |height edge.source - hsval| ≤ e := by
    change |height edge.source -
      ((1 - s.1) * height edge.source + s.1 * height edge.target)| ≤ e
    calc
      |height edge.source -
          ((1 - s.1) * height edge.source + s.1 * height edge.target)| =
          |s.1 * (height edge.source - height edge.target)| := by
            congr 1
            ring
      _ = s.1 * |height edge.source - height edge.target| := by
        rw [abs_mul, abs_of_nonneg s.2.1]
      _ ≤ s.1 * e := mul_le_mul_of_nonneg_left hgap s.2.1
      _ ≤ 1 * e := mul_le_mul_of_nonneg_right s.2.2 he
      _ = e := one_mul _
  rw [abs_sub_le_iff] at hsourceClose
  have hsource : a - e ≤ height edge.source ∧
      height edge.source ≤ b + e := by
    constructor <;> linarith [hs.1, hs.2, hsourceClose.1, hsourceClose.2]
  refine ⟨graphRealizationEdgeToSourcePath G edge s, ?_⟩
  intro t
  change a - e ≤
      (1 - (graphUnitContractToSource s t).1) * height edge.source +
        (graphUnitContractToSource s t).1 * height edge.target ∧
    (1 - (graphUnitContractToSource s t).1) * height edge.source +
        (graphUnitContractToSource s t).1 * height edge.target ≤ b + e
  have hformula :
      (1 - (graphUnitContractToSource s t).1) * height edge.source +
          (graphUnitContractToSource s t).1 * height edge.target =
        t.1 * height edge.source + (1 - t.1) * hsval := by
    simp only [graphUnitContractToSource, hsval,
      graphRealizationHeight_edgePoint]
    ring
  rw [hformula]
  constructor
  · calc
      a - e = t.1 * (a - e) + (1 - t.1) * (a - e) := by ring
      _ ≤ t.1 * height edge.source + (1 - t.1) * hsval := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsource.1 t.2.1)
          (mul_le_mul_of_nonneg_left (by linarith [hs.1, he])
            (sub_nonneg.mpr t.2.2))
  · calc
      t.1 * height edge.source + (1 - t.1) * hsval ≤
          t.1 * (b + e) + (1 - t.1) * (b + e) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsource.2 t.2.1)
          (mul_le_mul_of_nonneg_left (by linarith [hs.2, he])
            (sub_nonneg.mpr t.2.2))
      _ = b + e := by ring

/-- A graph walk whose visited vertex heights lie in one interval realizes as
a path in the CW complex inside the same interval.  Linear interpolation on
edges introduces no additional scalar error. -/
theorem joinedIn_graphRealization_of_walk
    {V : Type*} {G : SimpleGraph V} (height : V → ℝ)
    {a b : ℝ} {u v : V} (p : G.Walk u v)
    (hp : ∀ w, w ∈ p.support → a ≤ height w ∧ height w ≤ b) :
    JoinedIn
      {z | a ≤ graphRealizationHeight G height z ∧
        graphRealizationHeight G height z ≤ b}
      (graphRealizationVertex G u) (graphRealizationVertex G v) := by
  induction p with
  | @nil u =>
      exact JoinedIn.refl (by simpa using hp u (by simp))
  | @cons u v w huv p ih =>
      have hu : a ≤ height u ∧ height u ≤ b := hp u (by simp)
      have hv : a ≤ height v ∧ height v ≤ b :=
        hp v (by simp [p.start_mem_support])
      let e : OrientedEdge G := ⟨(u, v), huv⟩
      have hedge : JoinedIn
          {z | a ≤ graphRealizationHeight G height z ∧
            graphRealizationHeight G height z ≤ b}
          (graphRealizationVertex G u) (graphRealizationVertex G v) := by
        refine ⟨graphRealizationEdgePath G e, ?_⟩
        intro s
        change a ≤ (1 - s.1) * height u + s.1 * height v ∧
          (1 - s.1) * height u + s.1 * height v ≤ b
        constructor
        · calc
            a = (1 - s.1) * a + s.1 * a := by ring
            _ ≤ (1 - s.1) * height u + s.1 * height v :=
              add_le_add
                (mul_le_mul_of_nonneg_left hu.1 (by linarith [s.2.2]))
                (mul_le_mul_of_nonneg_left hv.1 s.2.1)
        · calc
            (1 - s.1) * height u + s.1 * height v ≤
                (1 - s.1) * b + s.1 * b :=
              add_le_add
                (mul_le_mul_of_nonneg_left hu.2 (by linarith [s.2.2]))
                (mul_le_mul_of_nonneg_left hv.2 s.2.1)
            _ = b := by ring
      have htail := ih (fun z hz ↦ hp z (by simp [hz]))
      exact hedge.trans htail

/-- Data for a continuous map out of a graph realization: vertex images and
orientation-compatible paths on its edges. -/
structure GraphRealizationMapData
    {V : Type*} (G : SimpleGraph V) (Y : Type*) [TopologicalSpace Y] where
  vertexMap : V → Y
  edgePath : (e : OrientedEdge G) → Path (vertexMap e.source) (vertexMap e.target)
  reverse_compatible : ∀ (e : OrientedEdge G) (s : GraphUnitInterval),
    edgePath e s = edgePath e.reverse (graphUnitReverse s)

def GraphRealizationMapData.rawMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) : GraphRealizationRaw G → Y
  | .inl v => d.vertexMap v
  | .inr (e, s) => d.edgePath e s

theorem GraphRealizationMapData.continuous_rawMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) : Continuous d.rawMap := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_of_discreteTopology
  · apply continuous_prod_of_discrete_left.mpr
    intro e
    exact (d.edgePath e).continuous

theorem GraphRealizationMapData.graphGlue_preserved
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y)
    {x y : GraphRealizationRaw G} (hxy : GraphGlue G x y) :
    d.rawMap x = d.rawMap y := by
  cases hxy with
  | source e => exact (d.edgePath e).source.symm
  | target e => exact (d.edgePath e).target.symm
  | reverse e s => exact d.reverse_compatible e s

theorem GraphRealizationMapData.graphEqvGen_preserved
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y)
    {x y : GraphRealizationRaw G}
    (hxy : Relation.EqvGen (GraphGlue G) x y) : d.rawMap x = d.rawMap y := by
  induction hxy with
  | rel _ _ h => exact d.graphGlue_preserved h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hxy hyz => exact hxy.trans hyz

/-- Continuous map descended from compatible vertex and edge data. -/
def GraphRealizationMapData.realizationMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) : SimpleGraphRealization G → Y :=
  Quotient.lift d.rawMap (fun _ _ h => d.graphEqvGen_preserved h)

@[simp] theorem GraphRealizationMapData.realizationMap_quotientMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) (x : GraphRealizationRaw G) :
    d.realizationMap (graphRealizationQuotientMap G x) = d.rawMap x :=
  rfl

theorem GraphRealizationMapData.continuous_realizationMap
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (d : GraphRealizationMapData G Y) : Continuous d.realizationMap := by
  unfold realizationMap
  exact d.continuous_rawMap.quotient_lift
    (fun _ _ h => d.graphEqvGen_preserved h)

noncomputable def chosenAdjacentPath
    {V Y : Type*} {G : SimpleGraph V} [TopologicalSpace Y]
    (vertexMap : V → Y)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (Path (vertexMap u) (vertexMap v)))
    {u v : V} (huv : G.Adj u v) : Path (vertexMap u) (vertexMap v) :=
  Classical.choice (hedge huv)

/-- Orient every edge using a fixed linear order, so opposite orientations use
one chosen path and its reverse rather than unrelated classical choices. -/
noncomputable def coherentOrientedEdgePath
    {V Y : Type*} [LinearOrder V] {G : SimpleGraph V} [TopologicalSpace Y]
    (vertexMap : V → Y)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (Path (vertexMap u) (vertexMap v)))
    (e : OrientedEdge G) : Path (vertexMap e.source) (vertexMap e.target) :=
  if h : e.source < e.target then
    chosenAdjacentPath vertexMap hedge e.2
  else
    (chosenAdjacentPath vertexMap hedge (G.symm e.2)).symm

theorem coherentOrientedEdgePath_reverse
    {V Y : Type*} [LinearOrder V] {G : SimpleGraph V} [TopologicalSpace Y]
    (vertexMap : V → Y)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (Path (vertexMap u) (vertexMap v)))
    (e : OrientedEdge G) (s : GraphUnitInterval) :
    coherentOrientedEdgePath vertexMap hedge e s =
      coherentOrientedEdgePath vertexMap hedge e.reverse (graphUnitReverse s) := by
  unfold coherentOrientedEdgePath
  by_cases h : e.source < e.target
  · have hn : ¬e.target < e.source := not_lt_of_ge h.le
    rw [dif_pos h]
    rw [dif_neg (show ¬e.reverse.source < e.reverse.target by simpa using hn)]
    simp only [Path.symm_apply, Function.comp_apply]
    have hpaths : chosenAdjacentPath vertexMap hedge e.2 =
        chosenAdjacentPath vertexMap hedge (G.symm e.reverse.2) := by
      congr
    rw [← hpaths]
    have hsame : graphUnitReverse s = unitInterval.symm s := rfl
    rw [hsame, unitInterval.symm_symm]
  · have hrev : e.target < e.source :=
      lt_of_le_of_ne (le_of_not_gt h) e.2.ne'
    rw [dif_neg h]
    rw [dif_pos (show e.reverse.source < e.reverse.target by simpa using hrev)]
    simp only [Path.symm_apply, Function.comp_apply]
    have hpaths : chosenAdjacentPath vertexMap hedge (G.symm e.2) =
        chosenAdjacentPath vertexMap hedge e.reverse.2 := by
      congr
    rw [← hpaths]
    have hsame : graphUnitReverse s = unitInterval.symm s := rfl
    rw [hsame]

/-- Any vertex map whose adjacent images can be joined by paths extends
continuously over the graph realization. -/
noncomputable def graphRealizationMapDataOfAdjacentPaths
    {V Y : Type*} [LinearOrder V] (G : SimpleGraph V) [TopologicalSpace Y]
    (vertexMap : V → Y)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (Path (vertexMap u) (vertexMap v))) :
    GraphRealizationMapData G Y where
  vertexMap := vertexMap
  edgePath := coherentOrientedEdgePath vertexMap hedge
  reverse_compatible := coherentOrientedEdgePath_reverse vertexMap hedge

/-- A path assigned to an adjacent pair together with a uniform comparison
between its filtered height and linear interpolation of the endpoint
heights. -/
structure HeightControlledAdjacentPath
    {V : Type*} (height : V → ℝ) (Y : FilteredReebGraph) (e : ℝ)
    (vertexMap : V → Y.Carrier) (u v : V) where
  path : Path (vertexMap u) (vertexMap v)
  height_close : ∀ s : GraphUnitInterval,
    |(1 - s.1) * height u + s.1 * height v - Y.height (path s)| ≤ e

noncomputable def chosenHeightControlledAdjacentPath
    {V : Type*} {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ} (vertexMap : V → Y.Carrier)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (HeightControlledAdjacentPath height Y e vertexMap u v))
    {u v : V} (huv : G.Adj u v) :
    HeightControlledAdjacentPath height Y e vertexMap u v :=
  Classical.choice (hedge huv)

/-- A coherent path orientation that retains the quantitative data used to
choose its underlying unoriented edge path. -/
noncomputable def coherentHeightControlledEdgePath
    {V : Type*} [LinearOrder V] {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ} (vertexMap : V → Y.Carrier)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (HeightControlledAdjacentPath height Y e vertexMap u v))
    (edge : OrientedEdge G) :
    Path (vertexMap edge.source) (vertexMap edge.target) :=
  if h : edge.source < edge.target then
    (chosenHeightControlledAdjacentPath vertexMap hedge edge.2).path
  else
    (chosenHeightControlledAdjacentPath vertexMap hedge (G.symm edge.2)).path.symm

theorem coherentHeightControlledEdgePath_reverse
    {V : Type*} [LinearOrder V] {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ} (vertexMap : V → Y.Carrier)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (HeightControlledAdjacentPath height Y e vertexMap u v))
    (edge : OrientedEdge G) (s : GraphUnitInterval) :
    coherentHeightControlledEdgePath vertexMap hedge edge s =
      coherentHeightControlledEdgePath vertexMap hedge edge.reverse
        (graphUnitReverse s) := by
  unfold coherentHeightControlledEdgePath
  by_cases h : edge.source < edge.target
  · have hn : ¬edge.target < edge.source := not_lt_of_ge h.le
    rw [dif_pos h]
    rw [dif_neg (show ¬edge.reverse.source < edge.reverse.target by simpa using hn)]
    simp only [Path.symm_apply, Function.comp_apply]
    have hpaths :
        (chosenHeightControlledAdjacentPath vertexMap hedge edge.2).path =
          (chosenHeightControlledAdjacentPath vertexMap hedge
            (G.symm edge.reverse.2)).path := by
      congr
    rw [← hpaths]
    have hsame : graphUnitReverse s = unitInterval.symm s := rfl
    rw [hsame, unitInterval.symm_symm]
  · have hrev : edge.target < edge.source :=
      lt_of_le_of_ne (le_of_not_gt h) edge.2.ne'
    rw [dif_neg h]
    rw [dif_pos (show edge.reverse.source < edge.reverse.target by simpa using hrev)]
    simp only [Path.symm_apply, Function.comp_apply]
    have hpaths :
        (chosenHeightControlledAdjacentPath vertexMap hedge
          (G.symm edge.2)).path =
          (chosenHeightControlledAdjacentPath vertexMap hedge
            edge.reverse.2).path := by
      congr
    rw [← hpaths]
    have hsame : graphUnitReverse s = unitInterval.symm s := rfl
    rw [hsame]

theorem coherentHeightControlledEdgePath_height_close
    {V : Type*} [LinearOrder V] {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ} (vertexMap : V → Y.Carrier)
    (hedge : ∀ {u v : V}, G.Adj u v →
      Nonempty (HeightControlledAdjacentPath height Y e vertexMap u v))
    (edge : OrientedEdge G) (s : GraphUnitInterval) :
    |(1 - s.1) * height edge.source + s.1 * height edge.target -
      Y.height (coherentHeightControlledEdgePath vertexMap hedge edge s)| ≤ e := by
  unfold coherentHeightControlledEdgePath
  by_cases h : edge.source < edge.target
  · rw [dif_pos h]
    exact (chosenHeightControlledAdjacentPath vertexMap hedge edge.2).height_close s
  · rw [dif_neg h]
    have hclose :=
      (chosenHeightControlledAdjacentPath vertexMap hedge
        (G.symm edge.2)).height_close (graphUnitReverse s)
    simp only [Path.symm_apply, Function.comp_apply]
    have hsame : unitInterval.symm s = graphUnitReverse s := rfl
    rw [hsame]
    convert hclose using 1 <;>
      simp only [graphUnitReverse_value] <;> congr 1 <;>
        unfold OrientedEdge.source OrientedEdge.target <;> ring

/-- A continuous graph-realization map with quantitative control of the
filtered height at vertices and along every oriented edge. -/
structure FilteredGraphRealizationMapData
    {V : Type*} (G : SimpleGraph V) (height : V → ℝ)
    (Y : FilteredReebGraph) (e : ℝ)
    extends GraphRealizationMapData G Y.Carrier where
  vertex_height_close : ∀ v,
    |height v - Y.height (toGraphRealizationMapData.vertexMap v)| ≤ e
  edge_height_close : ∀ (edge : OrientedEdge G) (s : GraphUnitInterval),
    |(1 - s.1) * height edge.source + s.1 * height edge.target -
      Y.height (toGraphRealizationMapData.edgePath edge s)| ≤ e

def FilteredGraphRealizationMapData.realizationMap
    {V : Type*} {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ}
    (d : FilteredGraphRealizationMapData G height Y e) :
    SimpleGraphRealization G → Y.Carrier :=
  d.toGraphRealizationMapData.realizationMap

theorem FilteredGraphRealizationMapData.continuous_realizationMap
    {V : Type*} {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ}
    (d : FilteredGraphRealizationMapData G height Y e) :
    Continuous d.realizationMap :=
  d.toGraphRealizationMapData.continuous_realizationMap

theorem FilteredGraphRealizationMapData.height_close
    {V : Type*} {G : SimpleGraph V} {height : V → ℝ}
    {Y : FilteredReebGraph} {e : ℝ}
    (d : FilteredGraphRealizationMapData G height Y e)
    (z : SimpleGraphRealization G) :
    |graphRealizationHeight G height z - Y.height (d.realizationMap z)| ≤ e := by
  refine Quotient.inductionOn z ?_
  intro raw
  cases raw with
  | inl v => exact d.vertex_height_close v
  | inr p =>
      rcases p with ⟨edge, s⟩
      exact d.edge_height_close edge s

/-- Classical Reeb equivalence: two points have the same scalar value and lie
in the same connected component of that level set. -/
def SameLevelComponent
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x y : M) : Prop :=
  f x = f y ∧ y ∈ connectedComponentIn {z | f z = f x} x

theorem sameLevelComponent_refl
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x : M) :
    SameLevelComponent f x x :=
  ⟨rfl, mem_connectedComponentIn rfl⟩

theorem sameLevelComponent_symm
    {M : Type} [TopologicalSpace M] (f : M → ℝ) {x y : M}
    (h : SameLevelComponent f x y) : SameLevelComponent f y x := by
  rcases h with ⟨hxy, hpath⟩
  refine ⟨hxy.symm, ?_⟩
  have hcomponents :
      connectedComponentIn {z | f z = f x} x =
        connectedComponentIn {z | f z = f x} y :=
    connectedComponentIn_eq hpath
  have hxmem : x ∈ connectedComponentIn {z | f z = f x} y := by
    rw [← hcomponents]
    exact mem_connectedComponentIn rfl
  simpa only [hxy] using hxmem

theorem sameLevelComponent_trans
    {M : Type} [TopologicalSpace M] (f : M → ℝ) {x y z : M}
    (hxy : SameLevelComponent f x y)
    (hyz : SameLevelComponent f y z) : SameLevelComponent f x z := by
  rcases hxy with ⟨hfxy, hpathxy⟩
  rcases hyz with ⟨hfyz, hpathyz⟩
  refine ⟨hfxy.trans hfyz, ?_⟩
  have hpathyz' : z ∈ connectedComponentIn {w | f w = f x} y := by
    simpa only [hfxy] using hpathyz
  rw [connectedComponentIn_eq hpathxy]
  exact hpathyz'

theorem sameLevelComponent_of_joinedIn
    {M : Type} [TopologicalSpace M] (f : M → ℝ) {x y : M}
    (hxy : JoinedIn {z | f z = f x} x y) :
    SameLevelComponent f x y := by
  refine ⟨hxy.target_mem.symm, ?_⟩
  have hconnected : IsConnected (Set.range hxy.somePath) :=
    isConnected_range hxy.somePath.continuous
  apply hconnected.isPreconnected.subset_connectedComponentIn
    ⟨0, hxy.somePath.source⟩
    (fun z hz => by
      rcases hz with ⟨t, rfl⟩
      exact hxy.somePath_mem t)
  exact ⟨1, hxy.somePath.target⟩

def reebSetoid
    {M : Type} [TopologicalSpace M] (f : M → ℝ) : Setoid M where
  r := SameLevelComponent f
  iseqv :=
    ⟨sameLevelComponent_refl f, sameLevelComponent_symm f,
      sameLevelComponent_trans f⟩

/-- Underlying quotient space of the continuum Reeb construction. -/
def ContinuumReebQuotient
    (M : Type) [TopologicalSpace M] (f : M → ℝ) :=
  Quotient (reebSetoid f)

instance continuumReebQuotientTopology
    (M : Type) [TopologicalSpace M] (f : M → ℝ) :
    TopologicalSpace (ContinuumReebQuotient M f) :=
  instTopologicalSpaceQuotient

/-- Quotient map from the domain to its Reeb space. -/
def continuumReebQuotientMap
    {M : Type} [TopologicalSpace M] (f : M → ℝ) :
    M → ContinuumReebQuotient M f :=
  Quotient.mk (reebSetoid f)

/-- Reeb quotient with its quotient topology and descended scalar function. -/
noncomputable def continuumReebGraph
    (M : Type) [TopologicalSpace M] (f : M → ℝ) : FilteredReebGraph where
  Carrier := ContinuumReebQuotient M f
  topology := continuumReebQuotientTopology M f
  height := Quotient.lift f (fun x y h => by
    have h' : SameLevelComponent f x y := h
    exact h'.1)

@[simp] theorem continuumReebGraph_height_quotientMap
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x : M) :
    (continuumReebGraph M f).height (continuumReebQuotientMap f x) = f x :=
  rfl

theorem continuumReebQuotientMap_eq_iff
    {M : Type} [TopologicalSpace M] (f : M → ℝ) (x y : M) :
    continuumReebQuotientMap f x = continuumReebQuotientMap f y ↔
      SameLevelComponent f x y := by
  exact Quotient.eq

theorem continuous_continuumReebQuotientMap
    {M : Type} [TopologicalSpace M] (f : M → ℝ) :
    Continuous (continuumReebQuotientMap f) := by
  exact continuous_quotient_mk'

theorem continuumReebQuotientMap_surjective
    {M : Type} [TopologicalSpace M] (f : M → ℝ) :
    Function.Surjective (continuumReebQuotientMap f) := by
  exact Quotient.mk_surjective

theorem continuous_continuumReebGraph_height
    {M : Type} [TopologicalSpace M] {f : M → ℝ} (hf : Continuous f) :
    Continuous (continuumReebGraph M f).height := by
  apply hf.quotient_lift

/-- A path in a manifold scalar band projects to a path in the corresponding
band of the continuum Reeb quotient. -/
theorem joinedIn_continuumReebQuotientMap
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    {a b : ℝ} {x x' : M}
    (h : JoinedIn {z | a ≤ f z ∧ f z ≤ b} x x') :
    JoinedIn {z | a ≤ (continuumReebGraph M f).height z ∧
      (continuumReebGraph M f).height z ≤ b}
      (continuumReebQuotientMap f x) (continuumReebQuotientMap f x') := by
  refine ⟨h.somePath.map (continuous_continuumReebQuotientMap f), ?_⟩
  intro t
  change a ≤ f (h.somePath t) ∧ f (h.somePath t) ≤ b
  exact h.somePath_mem t

/-- Filtered piecewise-linear realization of the canonical support-induced
midpoint graph. -/
noncomputable def discreteReebRealization
    (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) : FilteredReebGraph := by
  let D := canonicalDiscreteReebGraph G f
  exact
    { Carrier := SimpleGraphRealization D
      topology := simpleGraphRealizationTopology D
      height := graphRealizationHeight D (fun x => canonicalThreshold f x.1) }

theorem continuous_discreteReebRealization_height
    (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) :
    Continuous (discreteReebRealization V G f).height := by
  exact continuous_graphRealizationHeight
    (canonicalDiscreteReebGraph G f) (fun x => canonicalThreshold f x.1)

/-- A support witness attached to every raw point of a discrete graph
realization.  At a graph vertex it lies in that slice component; on an edge it
lies in the overlap that generated the transition. -/
noncomputable def discreteRawSupportWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ) :
    GraphRealizationRaw (discreteReebGraph G f threshold) → V
  | .inl x => Classical.choose (sliceNode_support_nonempty G f threshold x)
  | .inr (e, _) => Classical.choose
      (show SliceOverlap G f threshold e.source e.target from e.2.2)

theorem discreteRawSupportWitness_vertex_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ)
    (x : SliceNode G f threshold) :
    discreteRawSupportWitness G f threshold (.inl x) ∈
      componentSupport G f (threshold x.1) x.2 := by
  exact Classical.choose_spec (sliceNode_support_nonempty G f threshold x)

theorem discreteRawSupportWitness_edge_source_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ)
    (e : OrientedEdge (discreteReebGraph G f threshold))
    (a : GraphUnitInterval) :
    discreteRawSupportWitness G f threshold (.inr (e, a)) ∈
      componentSupport G f (threshold e.source.1) e.source.2 := by
  exact (Classical.choose_spec
    (show SliceOverlap G f threshold e.source e.target from e.2.2)).1

theorem discreteRawSupportWitness_edge_target_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ) {s : ℕ} (threshold : Fin s → ℝ)
    (e : OrientedEdge (discreteReebGraph G f threshold))
    (a : GraphUnitInterval) :
    discreteRawSupportWitness G f threshold (.inr (e, a)) ∈
      componentSupport G f (threshold e.target.1) e.target.2 := by
  exact (Classical.choose_spec
    (show SliceOverlap G f threshold e.source e.target from e.2.2)).2

/-- A convex interpolation stays within a common absolute-error bound. -/
theorem abs_affine_sub_le
    {a b c E s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : |a - c| ≤ E) (hb : |b - c| ≤ E) :
    |(1 - s) * a + s * b - c| ≤ E := by
  have hE : 0 ≤ E := (abs_nonneg (a - c)).trans ha
  calc
    |(1 - s) * a + s * b - c| =
        |(1 - s) * (a - c) + s * (b - c)| := by ring_nf
    _ ≤ |(1 - s) * (a - c)| + |s * (b - c)| := abs_add _ _
    _ = (1 - s) * |a - c| + s * |b - c| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs1), abs_of_nonneg hs0]
    _ ≤ (1 - s) * E + s * E := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hs1))
        (mul_le_mul_of_nonneg_left hb hs0)
    _ = E := by ring

/-- Points joined inside one closed scalar band. -/
def HeightBandJoined (X : FilteredReebGraph) (a b : ℝ)
    (x y : X.Carrier) : Prop :=
  JoinedIn {z | a ≤ X.height z ∧ X.height z ≤ b} x y

theorem HeightBandJoined.mono
    {X : FilteredReebGraph} {a b a' b' : ℝ} {x y : X.Carrier}
    (h : HeightBandJoined X a b x y) (ha : a' ≤ a) (hb : b ≤ b') :
    HeightBandJoined X a' b' x y := by
  apply JoinedIn.mono h
  intro z hz
  exact ⟨ha.trans hz.1, hz.2.trans hb⟩

/-- A height-bounded active-incidence walk projects all the way to a path in
the filtered CW realization of the canonical component graph. -/
theorem heightBandJoined_of_canonicalActiveIncidence_walk
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (f : V → ℝ)
    {a b : ℝ} {x y : CanonicalActiveState G f}
    (p : (canonicalActiveIncidenceGraph G f).Walk x y)
    (hp : ∀ z, z ∈ p.support →
      a ≤ canonicalThreshold f z.1 ∧ canonicalThreshold f z.1 ≤ b) :
    HeightBandJoined (discreteReebRealization V G f) a b
      (graphRealizationVertex (canonicalDiscreteReebGraph G f)
        (canonicalActiveStateNode G f x))
      (graphRealizationVertex (canonicalDiscreteReebGraph G f)
        (canonicalActiveStateNode G f y)) := by
  induction p with
  | @nil x =>
      exact JoinedIn.refl (by
        change a ≤ canonicalThreshold f x.1 ∧
          canonicalThreshold f x.1 ≤ b
        simpa using hp x (by simp))
  | @cons u v w huv p ih =>
      have hu : a ≤ canonicalThreshold f u.1 ∧
          canonicalThreshold f u.1 ≤ b := hp u (by simp)
      have hv : a ≤ canonicalThreshold f v.1 ∧
          canonicalThreshold f v.1 ≤ b :=
        hp v (by simp [p.start_mem_support])
      have hstep : HeightBandJoined (discreteReebRealization V G f) a b
          (graphRealizationVertex (canonicalDiscreteReebGraph G f)
            (canonicalActiveStateNode G f u))
          (graphRealizationVertex (canonicalDiscreteReebGraph G f)
            (canonicalActiveStateNode G f v)) := by
        rcases canonicalActiveIncidence_adj_projects G f huv with heq | hadj
        · rw [heq]
          exact JoinedIn.refl (by
            change a ≤ canonicalThreshold f v.1 ∧
              canonicalThreshold f v.1 ≤ b
            exact hv)
        · let q : (canonicalDiscreteReebGraph G f).Walk
              (canonicalActiveStateNode G f u)
              (canonicalActiveStateNode G f v) := .cons hadj .nil
          apply joinedIn_graphRealization_of_walk
            (fun z : SliceNode G f (canonicalThreshold f) ↦
              canonicalThreshold f z.1) q
          intro z hz
          simp only [q, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons,
            List.mem_singleton] at hz
          rcases hz with rfl | hz
          · exact hu
          · rcases hz with rfl | hz
            · exact hv
            · simp at hz
      have htail := ih (fun z hz ↦ hp z (by simp [hz]))
      exact hstep.trans htail

/-- A continuous map with uniform height error `e` sends every scalar-band
path to the band enlarged by `e`. -/
theorem HeightBandJoined.map_of_continuous_height_close
    {X Y : FilteredReebGraph} {e a b : ℝ}
    {φ : X.Carrier → Y.Carrier} (hφ : Continuous φ)
    (hheight : ∀ z, |X.height z - Y.height (φ z)| ≤ e)
    {x x' : X.Carrier} (h : HeightBandJoined X a b x x') :
    HeightBandJoined Y (a - e) (b + e) (φ x) (φ x') := by
  refine ⟨h.somePath.map hφ, ?_⟩
  intro t
  have hz := h.somePath_mem t
  have he := hheight (h.somePath t)
  rw [abs_sub_le_iff] at he
  change a - e ≤ Y.height (φ (h.somePath t)) ∧
    Y.height (φ (h.somePath t)) ≤ b + e
  constructor <;> linarith [hz.1, hz.2, he.1, he.2]

/-- A homotopy whose track over `x` remains in a scalar band centered at
`center x`. -/
structure HeightControlledHomotopy
    (X : FilteredReebGraph) (center : X.Carrier → ℝ) (e : ℝ)
    (g₀ g₁ : X.Carrier → X.Carrier) where
  toFun : GraphUnitInterval × X.Carrier → X.Carrier
  continuous_toFun : Continuous toFun
  at_zero : ∀ x, toFun (graphUnitZero, x) = g₀ x
  at_one : ∀ x, toFun (graphUnitOne, x) = g₁ x
  height_control : ∀ t x,
    center x - e ≤ X.height (toFun (t, x)) ∧
    X.height (toFun (t, x)) ≤ center x + e

def HeightControlledHomotopy.path
    {X : FilteredReebGraph} {center : X.Carrier → ℝ} {e : ℝ}
    {g₀ g₁ : X.Carrier → X.Carrier}
    (h : HeightControlledHomotopy X center e g₀ g₁) (x : X.Carrier) :
    Path (g₀ x) (g₁ x) where
  toFun t := h.toFun (t, x)
  continuous_toFun := h.continuous_toFun.comp
    (continuous_id.prod_mk continuous_const)
  source' := by simpa only using h.at_zero x
  target' := by simpa only using h.at_one x

theorem HeightControlledHomotopy.joined
    {X : FilteredReebGraph} {center : X.Carrier → ℝ} {e : ℝ}
    {g₀ g₁ : X.Carrier → X.Carrier}
    (h : HeightControlledHomotopy X center e g₀ g₁) (x : X.Carrier) :
    HeightBandJoined X (center x - e) (center x + e) (g₀ x) (g₁ x) := by
  refine ⟨h.path x, ?_⟩
  intro t
  exact h.height_control t x

/-- Intrinsic scalar-range distance used in the functional distortion and
functional Gromov--Hausdorff distances.  It is the infimum of the lengths of
closed scalar intervals whose inverse image contains a path joining the two
points.  `ℝ≥0∞` correctly assigns distance `∞` when no such path exists. -/
noncomputable def heightRangeDist
    (X : FilteredReebGraph) (x y : X.Carrier) : ℝ≥0∞ :=
  sInf {w : ℝ≥0∞ | ∃ a b : ℝ,
    a ≤ b ∧ HeightBandJoined X a b x y ∧ w = ENNReal.ofReal (b - a)}

/-- An isomorphism of filtered spaces: a homeomorphism that preserves the
scalar value exactly.  This is the correct realization-level certificate for
a degree-two suppression; preservation of graph counts alone is insufficient. -/
structure FilteredReebGraphEquiv (X Y : FilteredReebGraph) where
  toHomeomorph : X.Carrier ≃ₜ Y.Carrier
  height_eq : ∀ x, Y.height (toHomeomorph x) = X.height x

namespace FilteredReebGraphEquiv

def symm {X Y : FilteredReebGraph} (e : FilteredReebGraphEquiv X Y) :
    FilteredReebGraphEquiv Y X where
  toHomeomorph := e.toHomeomorph.symm
  height_eq y := by
    simpa using (e.height_eq (e.toHomeomorph.symm y)).symm

def refl (X : FilteredReebGraph) : FilteredReebGraphEquiv X X where
  toHomeomorph := Homeomorph.refl X.Carrier
  height_eq _ := rfl

def trans {X Y Z : FilteredReebGraph}
    (eXY : FilteredReebGraphEquiv X Y)
    (eYZ : FilteredReebGraphEquiv Y Z) : FilteredReebGraphEquiv X Z where
  toHomeomorph := eXY.toHomeomorph.trans eYZ.toHomeomorph
  height_eq x := by
    change Z.height (eYZ.toHomeomorph (eXY.toHomeomorph x)) = X.height x
    rw [eYZ.height_eq, eXY.height_eq]

theorem heightBandJoined {X Y : FilteredReebGraph}
    (e : FilteredReebGraphEquiv X Y) {a b : ℝ} {x x' : X.Carrier}
    (h : HeightBandJoined X a b x x') :
    HeightBandJoined Y a b (e.toHomeomorph x) (e.toHomeomorph x') := by
  refine ⟨h.somePath.map e.toHomeomorph.continuous, ?_⟩
  intro t
  change a ≤ Y.height (e.toHomeomorph (h.somePath t)) ∧
    Y.height (e.toHomeomorph (h.somePath t)) ≤ b
  simpa only [e.height_eq] using h.somePath_mem t

theorem heightBandJoined_iff {X Y : FilteredReebGraph}
    (e : FilteredReebGraphEquiv X Y) {a b : ℝ} {x x' : X.Carrier} :
    HeightBandJoined X a b x x' ↔
      HeightBandJoined Y a b (e.toHomeomorph x) (e.toHomeomorph x') := by
  constructor
  · exact e.heightBandJoined
  · intro h
    simpa [FilteredReebGraphEquiv.symm] using e.symm.heightBandJoined h

theorem heightRangeDist_eq {X Y : FilteredReebGraph}
    (e : FilteredReebGraphEquiv X Y) (x x' : X.Carrier) :
    heightRangeDist Y (e.toHomeomorph x) (e.toHomeomorph x') =
      heightRangeDist X x x' := by
  unfold heightRangeDist
  congr 1
  ext w
  constructor
  · rintro ⟨a, b, hab, hjoined, hw⟩
    exact ⟨a, b, hab, e.heightBandJoined_iff.mpr hjoined, hw⟩
  · rintro ⟨a, b, hab, hjoined, hw⟩
    exact ⟨a, b, hab, e.heightBandJoined_iff.mp hjoined, hw⟩

end FilteredReebGraphEquiv

/-- Symmetric order distance on extended nonnegative reals.  Unlike coercion
through `toReal`, this retains infinite intrinsic distances. -/
noncomputable def ennrealOrderDist (a b : ℝ≥0∞) : ℝ≥0∞ :=
  (a - b) ⊔ (b - a)

theorem ennrealOrderDist_comm (a b : ℝ≥0∞) :
    ennrealOrderDist a b = ennrealOrderDist b a := by
  simp only [ennrealOrderDist, sup_comm]

theorem ennrealOrderDist_self (a : ℝ≥0∞) : ennrealOrderDist a a = 0 := by
  simp [ennrealOrderDist]

theorem ennrealOrderDist_triangle (a b c : ℝ≥0∞) :
    ennrealOrderDist a c ≤ ennrealOrderDist a b + ennrealOrderDist b c := by
  apply sup_le
  · exact (tsub_le_tsub_add_tsub.trans
      (add_le_add le_sup_left le_sup_left))
  · calc
      c - a ≤ c - b + (b - a) := tsub_le_tsub_add_tsub
      _ ≤ ennrealOrderDist b c + ennrealOrderDist a b :=
        add_le_add le_sup_right le_sup_right
      _ = ennrealOrderDist a b + ennrealOrderDist b c := add_comm _ _

/-- The correspondence generated by maps in both directions, as in the
definition of functional Gromov--Hausdorff distance. -/
def FunctionalGHRel
    (X Y : FilteredReebGraph)
    (φ : X.Carrier → Y.Carrier) (ψ : Y.Carrier → X.Carrier)
    (x : X.Carrier) (y : Y.Carrier) : Prop :=
  y = φ x ∨ x = ψ y

/-- A quantitative certificate that a pair of maps has functional
Gromov--Hausdorff cost at most `ε`.  The factor two in `range_distortion`
matches the conventional `1/2` multiplying correspondence distortion. -/
structure FunctionalGHCertificate
    (X Y : FilteredReebGraph) (ε : ℝ≥0∞) where
  toFun : X.Carrier → Y.Carrier
  invFun : Y.Carrier → X.Carrier
  height_to : ∀ x,
    ENNReal.ofReal |X.height x - Y.height (toFun x)| ≤ ε
  height_inv : ∀ y,
    ENNReal.ofReal |X.height (invFun y) - Y.height y| ≤ ε
  range_distortion : ∀ {x x' : X.Carrier} {y y' : Y.Carrier},
    FunctionalGHRel X Y toFun invFun x y →
    FunctionalGHRel X Y toFun invFun x' y' →
    ennrealOrderDist (heightRangeDist X x x') (heightRangeDist Y y y') ≤ 2 * ε

/-- Functional Gromov--Hausdorff distance for filtered spaces, presented by
maps in both directions.  Its exact equivalence with the total-correspondence
presentation is proved below. -/
noncomputable def functionalGHDistance
    (X Y : FilteredReebGraph) : ℝ≥0∞ :=
  sInf {ε : ℝ≥0∞ | Nonempty (FunctionalGHCertificate X Y ε)}

/-- The comparison distance used by the convergence theorem. -/
noncomputable def reebDist : FilteredReebGraph → FilteredReebGraph → ℝ≥0∞ :=
  functionalGHDistance

theorem functionalGHDistance_le_of_certificate
    {X Y : FilteredReebGraph} {ε : ℝ≥0∞}
    (h : FunctionalGHCertificate X Y ε) :
    functionalGHDistance X Y ≤ ε := by
  apply sInf_le
  exact ⟨h⟩

theorem heightRangeDist_self (X : FilteredReebGraph) (x : X.Carrier) :
    heightRangeDist X x x = 0 := by
  apply le_antisymm
  · apply sInf_le
    exact ⟨X.height x, X.height x, le_rfl,
      JoinedIn.refl ⟨le_rfl, le_rfl⟩, by simp⟩
  · exact bot_le

/-- A height-preserving homeomorphism has zero functional-GH cost. -/
def FilteredReebGraphEquiv.functionalGHCertificate
    {X Y : FilteredReebGraph} (e : FilteredReebGraphEquiv X Y) :
    FunctionalGHCertificate X Y 0 where
  toFun := e.toHomeomorph
  invFun := e.toHomeomorph.symm
  height_to x := by simp [e.height_eq]
  height_inv y := by
    have heq : X.height (e.toHomeomorph.symm y) = Y.height y := by
      simpa using (e.height_eq (e.toHomeomorph.symm y)).symm
    rw [heq]
    simp
  range_distortion := by
    intro x x' y y' hxy hx'y'
    have hy : y = e.toHomeomorph x := by
      rcases hxy with hxy | hxy
      · exact hxy
      · exact (by
          have := congrArg e.toHomeomorph hxy
          simpa using this.symm)
    have hy' : y' = e.toHomeomorph x' := by
      rcases hx'y' with hx'y' | hx'y'
      · exact hx'y'
      · exact (by
          have := congrArg e.toHomeomorph hx'y'
          simpa using this.symm)
    subst y
    subst y'
    rw [e.heightRangeDist_eq]
    simp [ennrealOrderDist_self]

theorem functionalGHDistance_eq_zero_of_equiv
    {X Y : FilteredReebGraph} (e : FilteredReebGraphEquiv X Y) :
    functionalGHDistance X Y = 0 := by
  exact le_antisymm
    (functionalGHDistance_le_of_certificate e.functionalGHCertificate) bot_le

/-- Total-correspondence presentation of functional distortion.  Totality in
both variables is exactly what is needed to select the two maps used above. -/
structure FunctionalGHCorrespondenceCertificate
    (X Y : FilteredReebGraph) (ε : ℝ≥0∞) where
  rel : X.Carrier → Y.Carrier → Prop
  left_total : ∀ x, ∃ y, rel x y
  right_total : ∀ y, ∃ x, rel x y
  height : ∀ {x y}, rel x y →
    ENNReal.ofReal |X.height x - Y.height y| ≤ ε
  range_distortion : ∀ {x x' y y'}, rel x y → rel x' y' →
    ennrealOrderDist (heightRangeDist X x x') (heightRangeDist Y y y') ≤ 2 * ε

noncomputable def correspondenceFunctionalGHDistance
    (X Y : FilteredReebGraph) : ℝ≥0∞ :=
  sInf {ε : ℝ≥0∞ |
    Nonempty (FunctionalGHCorrespondenceCertificate X Y ε)}

def FunctionalGHCertificate.toCorrespondence
    {X Y : FilteredReebGraph} {ε : ℝ≥0∞}
    (h : FunctionalGHCertificate X Y ε) :
    FunctionalGHCorrespondenceCertificate X Y ε where
  rel := FunctionalGHRel X Y h.toFun h.invFun
  left_total x := ⟨h.toFun x, Or.inl rfl⟩
  right_total y := ⟨h.invFun y, Or.inr rfl⟩
  height := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · subst y
      exact h.height_to x
    · subst x
      exact h.height_inv y
  range_distortion := h.range_distortion

noncomputable def FunctionalGHCorrespondenceCertificate.toMaps
    {X Y : FilteredReebGraph} {ε : ℝ≥0∞}
    (h : FunctionalGHCorrespondenceCertificate X Y ε) :
    FunctionalGHCertificate X Y ε where
  toFun x := Classical.choose (h.left_total x)
  invFun y := Classical.choose (h.right_total y)
  height_to x := h.height (Classical.choose_spec (h.left_total x))
  height_inv y := h.height (Classical.choose_spec (h.right_total y))
  range_distortion := by
    intro x x' y y' hxy hx'y'
    apply h.range_distortion
    · rcases hxy with hxy | hxy
      · subst y
        exact Classical.choose_spec (h.left_total x)
      · subst x
        exact Classical.choose_spec (h.right_total y)
    · rcases hx'y' with hx'y' | hx'y'
      · subst y'
        exact Classical.choose_spec (h.left_total x')
      · subst x'
        exact Classical.choose_spec (h.right_total y')

theorem correspondenceFunctionalGHDistance_le_of_certificate
    {X Y : FilteredReebGraph} {ε : ℝ≥0∞}
    (h : FunctionalGHCorrespondenceCertificate X Y ε) :
    correspondenceFunctionalGHDistance X Y ≤ ε := by
  apply sInf_le
  exact ⟨h⟩

/-- The two-map and total-correspondence definitions of functional
Gromov--Hausdorff distance agree exactly, with no multiplicative loss. -/
theorem functionalGHDistance_eq_correspondence
    (X Y : FilteredReebGraph) :
    functionalGHDistance X Y = correspondenceFunctionalGHDistance X Y := by
  apply le_antisymm
  · apply le_sInf
    intro ε hε
    rcases hε with ⟨h⟩
    exact functionalGHDistance_le_of_certificate h.toMaps
  · apply le_sInf
    intro ε hε
    rcases hε with ⟨h⟩
    exact correspondenceFunctionalGHDistance_le_of_certificate
      h.toCorrespondence

/-- Identity maps have zero functional-GH cost. -/
def functionalGHCertificateRefl (X : FilteredReebGraph) :
    FunctionalGHCertificate X X 0 where
  toFun := id
  invFun := id
  height_to x := by simp
  height_inv x := by simp
  range_distortion := by
    intro x x' y y' hxy hx'y'
    simp only [FunctionalGHRel, id_eq] at hxy hx'y'
    rcases hxy with hxy | hxy <;> rcases hx'y' with hx'y' | hx'y'
    <;> subst_vars <;> simp [ennrealOrderDist_self]

theorem functionalGHDistance_self (X : FilteredReebGraph) :
    functionalGHDistance X X = 0 := by
  exact le_antisymm
    (functionalGHDistance_le_of_certificate (functionalGHCertificateRefl X)) bot_le

/-- Swapping the two maps preserves functional-GH cost. -/
def FunctionalGHCertificate.symm
    {X Y : FilteredReebGraph} {ε : ℝ≥0∞}
    (h : FunctionalGHCertificate X Y ε) :
    FunctionalGHCertificate Y X ε where
  toFun := h.invFun
  invFun := h.toFun
  height_to y := by
    simpa only [abs_sub_comm] using h.height_inv y
  height_inv x := by
    simpa only [abs_sub_comm] using h.height_to x
  range_distortion := by
    intro y y' x x' hxy hx'y'
    rw [ennrealOrderDist_comm]
    apply h.range_distortion
    · exact hxy.elim Or.inr Or.inl
    · exact hx'y'.elim Or.inr Or.inl

/-- Functional-GH certificates compose with additive cost. -/
noncomputable def FunctionalGHCertificate.comp
    {X Y Z : FilteredReebGraph} {ε δ : ℝ≥0∞}
    (hXY : FunctionalGHCertificate X Y ε)
    (hYZ : FunctionalGHCertificate Y Z δ) :
    FunctionalGHCertificate X Z (ε + δ) where
  toFun := hYZ.toFun ∘ hXY.toFun
  invFun := hXY.invFun ∘ hYZ.invFun
  height_to x := by
    calc
      ENNReal.ofReal |X.height x - Z.height (hYZ.toFun (hXY.toFun x))| =
          ENNReal.ofReal
            |(X.height x - Y.height (hXY.toFun x)) +
              (Y.height (hXY.toFun x) - Z.height (hYZ.toFun (hXY.toFun x)))| := by
            congr 2
            ring
      _ ≤ ENNReal.ofReal |X.height x - Y.height (hXY.toFun x)| +
          ENNReal.ofReal
            |Y.height (hXY.toFun x) - Z.height (hYZ.toFun (hXY.toFun x))| := by
            exact (ENNReal.ofReal_le_ofReal (abs_add _ _)).trans ENNReal.ofReal_add_le
      _ ≤ ε + δ := add_le_add (hXY.height_to x) (hYZ.height_to (hXY.toFun x))
  height_inv z := by
    calc
      ENNReal.ofReal |X.height (hXY.invFun (hYZ.invFun z)) - Z.height z| =
          ENNReal.ofReal
            |(X.height (hXY.invFun (hYZ.invFun z)) - Y.height (hYZ.invFun z)) +
              (Y.height (hYZ.invFun z) - Z.height z)| := by
            congr 2
            ring
      _ ≤ ENNReal.ofReal
            |X.height (hXY.invFun (hYZ.invFun z)) - Y.height (hYZ.invFun z)| +
          ENNReal.ofReal |Y.height (hYZ.invFun z) - Z.height z| := by
            exact (ENNReal.ofReal_le_ofReal (abs_add _ _)).trans ENNReal.ofReal_add_le
      _ ≤ ε + δ := add_le_add (hXY.height_inv (hYZ.invFun z)) (hYZ.height_inv z)
  range_distortion := by
    intro x x' z z' hxz hx'z'
    let dX := heightRangeDist X x x'
    let dZ := heightRangeDist Z z z'
    rcases hxz with hxz | hxz
    · rcases hx'z' with hx'z' | hx'z'
      · let y := hXY.toFun x
        let y' := hXY.toFun x'
        calc
          ennrealOrderDist dX dZ ≤
              ennrealOrderDist dX (heightRangeDist Y y y') +
                ennrealOrderDist (heightRangeDist Y y y') dZ :=
            ennrealOrderDist_triangle _ _ _
          _ ≤ 2 * ε + 2 * δ := add_le_add
            (hXY.range_distortion (Or.inl rfl) (Or.inl rfl))
            (hYZ.range_distortion
              (Or.inl (by simpa [y, Function.comp_apply] using hxz))
              (Or.inl (by simpa [y', Function.comp_apply] using hx'z')))
          _ = 2 * (ε + δ) := by ring
      · let y := hXY.toFun x
        let y' := hYZ.invFun z'
        calc
          ennrealOrderDist dX dZ ≤
              ennrealOrderDist dX (heightRangeDist Y y y') +
                ennrealOrderDist (heightRangeDist Y y y') dZ :=
            ennrealOrderDist_triangle _ _ _
          _ ≤ 2 * ε + 2 * δ := add_le_add
            (hXY.range_distortion (Or.inl rfl) (Or.inr hx'z'))
            (hYZ.range_distortion
              (Or.inl (by simpa [y, Function.comp_apply] using hxz)) (Or.inr rfl))
          _ = 2 * (ε + δ) := by ring
    · rcases hx'z' with hx'z' | hx'z'
      · let y := hYZ.invFun z
        let y' := hXY.toFun x'
        calc
          ennrealOrderDist dX dZ ≤
              ennrealOrderDist dX (heightRangeDist Y y y') +
                ennrealOrderDist (heightRangeDist Y y y') dZ :=
            ennrealOrderDist_triangle _ _ _
          _ ≤ 2 * ε + 2 * δ := add_le_add
            (hXY.range_distortion (Or.inr hxz) (Or.inl rfl))
            (hYZ.range_distortion (Or.inr rfl)
              (Or.inl (by simpa [y', Function.comp_apply] using hx'z')))
          _ = 2 * (ε + δ) := by ring
      · let y := hYZ.invFun z
        let y' := hYZ.invFun z'
        calc
          ennrealOrderDist dX dZ ≤
              ennrealOrderDist dX (heightRangeDist Y y y') +
                ennrealOrderDist (heightRangeDist Y y y') dZ :=
            ennrealOrderDist_triangle _ _ _
          _ ≤ 2 * ε + 2 * δ := add_le_add
            (hXY.range_distortion (Or.inr hxz) (Or.inr hx'z'))
            (hYZ.range_distortion (Or.inr rfl) (Or.inr rfl))
          _ = 2 * (ε + δ) := by ring

theorem functionalGHDistance_symm (X Y : FilteredReebGraph) :
    functionalGHDistance X Y = functionalGHDistance Y X := by
  apply le_antisymm
  · apply le_sInf
    intro ε hε
    rcases hε with ⟨cert⟩
    exact functionalGHDistance_le_of_certificate cert.symm
  · apply le_sInf
    intro ε hε
    rcases hε with ⟨cert⟩
    exact functionalGHDistance_le_of_certificate cert.symm

theorem functionalGHDistance_triangle (X Y Z : FilteredReebGraph) :
    functionalGHDistance X Z ≤
      functionalGHDistance X Y + functionalGHDistance Y Z := by
  unfold functionalGHDistance
  rw [ENNReal.sInf_add]
  refine le_iInf fun ε => le_iInf fun hε => ?_
  rw [add_comm ε, ENNReal.sInf_add]
  refine le_iInf fun δ => le_iInf fun hδ => ?_
  rcases hε with ⟨hXY⟩
  rcases hδ with ⟨hYZ⟩
  simpa only [add_comm] using
    functionalGHDistance_le_of_certificate (hXY.comp hYZ)

/-- Laws required of the eventual interleaving or functional-distortion
distance.  Keeping this certificate explicit prevents opaque comparison
functions from being treated as metrics without proof. -/
structure ReebDistanceLaws
    (d : FilteredReebGraph → FilteredReebGraph → ℝ≥0∞) : Prop where
  nonneg : ∀ X Y, 0 ≤ d X Y
  self : ∀ X, d X X = 0
  symm : ∀ X Y, d X Y = d Y X
  triangle : ∀ X Y Z, d X Z ≤ d X Y + d Y Z

theorem reebDist_laws : ReebDistanceLaws reebDist where
  nonneg _ _ := bot_le
  self := functionalGHDistance_self
  symm := functionalGHDistance_symm
  triangle := functionalGHDistance_triangle

/-- Replacing a filtered realization by a height-preserving homeomorphic one
does not change its functional-GH distance to any third filtered space. -/
theorem FilteredReebGraphEquiv.functionalGHDistance_left
    {X Y : FilteredReebGraph} (e : FilteredReebGraphEquiv X Y)
    (Z : FilteredReebGraph) :
    functionalGHDistance X Z = functionalGHDistance Y Z := by
  apply le_antisymm
  · calc
      functionalGHDistance X Z ≤
          functionalGHDistance X Y + functionalGHDistance Y Z :=
        functionalGHDistance_triangle X Y Z
      _ = functionalGHDistance Y Z := by
        rw [functionalGHDistance_eq_zero_of_equiv e, zero_add]
  · calc
      functionalGHDistance Y Z ≤
          functionalGHDistance Y X + functionalGHDistance X Z :=
        functionalGHDistance_triangle Y X Z
      _ = functionalGHDistance X Z := by
        rw [functionalGHDistance_eq_zero_of_equiv e.symm, zero_add]

theorem FilteredReebGraphEquiv.functionalGHDistance_right
    {X Y : FilteredReebGraph} (e : FilteredReebGraphEquiv X Y)
    (Z : FilteredReebGraph) :
    functionalGHDistance Z X = functionalGHDistance Z Y := by
  rw [functionalGHDistance_symm Z X, functionalGHDistance_symm Z Y]
  exact e.functionalGHDistance_left Z

/-- Complete mathematical certificate for one degree-two suppression: the
combinatorial step preserves the finite graph invariants, and the filtered CW
realizations are related by a height-preserving homeomorphism.  A concrete
reducer must construct both fields. -/
structure FilteredDegreeTwoSuppressionCertificate
    (G H : FiniteMultigraph) (X Y : FilteredReebGraph) where
  combinatorial : IsDegreeTwoSuppression G H
  realization : FilteredReebGraphEquiv X Y

namespace FilteredDegreeTwoSuppressionCertificate

theorem preserves_firstBetti
    {G H : FiniteMultigraph} {X Y : FilteredReebGraph}
    (h : FilteredDegreeTwoSuppressionCertificate G H X Y) :
    firstBetti H = firstBetti G :=
  h.combinatorial.preserves_firstBetti

theorem filtered_distance_zero
    {G H : FiniteMultigraph} {X Y : FilteredReebGraph}
    (h : FilteredDegreeTwoSuppressionCertificate G H X Y) :
    reebDist X Y = 0 :=
  functionalGHDistance_eq_zero_of_equiv h.realization

theorem preserves_distance_to
    {G H : FiniteMultigraph} {X Y : FilteredReebGraph}
    (h : FilteredDegreeTwoSuppressionCertificate G H X Y)
    (Z : FilteredReebGraph) : reebDist X Z = reebDist Y Z :=
  h.realization.functionalGHDistance_left Z

end FilteredDegreeTwoSuppressionCertificate

/-- Aggregate certificate for a finite sequence of degree-two suppressions.
The realization equivalence is the composition of the local equivalences. -/
structure FilteredDegreeTwoReductionCertificate
    (G H : FiniteMultigraph) (X Y : FilteredReebGraph) where
  combinatorial : IsDegreeTwoReduction G H
  realization : FilteredReebGraphEquiv X Y

namespace FilteredDegreeTwoReductionCertificate

def refl (G : FiniteMultigraph) (X : FilteredReebGraph) :
    FilteredDegreeTwoReductionCertificate G G X X where
  combinatorial := IsDegreeTwoReduction.refl G
  realization := FilteredReebGraphEquiv.refl X

def trans {G H K : FiniteMultigraph} {X Y Z : FilteredReebGraph}
    (hGH : FilteredDegreeTwoReductionCertificate G H X Y)
    (hHK : FilteredDegreeTwoReductionCertificate H K Y Z) :
    FilteredDegreeTwoReductionCertificate G K X Z where
  combinatorial := hGH.combinatorial.trans hHK.combinatorial
  realization := hGH.realization.trans hHK.realization

theorem preserves_firstBetti
    {G H : FiniteMultigraph} {X Y : FilteredReebGraph}
    (h : FilteredDegreeTwoReductionCertificate G H X Y) :
    firstBetti H = firstBetti G :=
  h.combinatorial.preserves_firstBetti

theorem filtered_distance_zero
    {G H : FiniteMultigraph} {X Y : FilteredReebGraph}
    (h : FilteredDegreeTwoReductionCertificate G H X Y) :
    reebDist X Y = 0 :=
  functionalGHDistance_eq_zero_of_equiv h.realization

theorem preserves_distance_to
    {G H : FiniteMultigraph} {X Y : FilteredReebGraph}
    (h : FilteredDegreeTwoReductionCertificate G H X Y)
    (Z : FilteredReebGraph) : reebDist X Z = reebDist Y Z :=
  h.realization.functionalGHDistance_left Z

end FilteredDegreeTwoReductionCertificate

/-- A band-level formulation of a functional-GH comparison.  It is the form
produced naturally by support-component soundness and completeness: every
path in a scalar band maps to a path in the band expanded by `e`, in both
directions and for the full two-map correspondence. -/
structure FunctionalGHBandCertificate
    (X Y : FilteredReebGraph) (e : ℝ) where
  error_nonneg : 0 ≤ e
  toFun : X.Carrier → Y.Carrier
  invFun : Y.Carrier → X.Carrier
  height_to : ∀ x, |X.height x - Y.height (toFun x)| ≤ e
  height_inv : ∀ y, |X.height (invFun y) - Y.height y| ≤ e
  band_to : ∀ {x x' : X.Carrier} {y y' : Y.Carrier} {a b : ℝ},
    FunctionalGHRel X Y toFun invFun x y →
    FunctionalGHRel X Y toFun invFun x' y' →
    a ≤ b → HeightBandJoined X a b x x' →
    HeightBandJoined Y (a - e) (b + e) y y'
  band_inv : ∀ {x x' : X.Carrier} {y y' : Y.Carrier} {a b : ℝ},
    FunctionalGHRel X Y toFun invFun x y →
    FunctionalGHRel X Y toFun invFun x' y' →
    a ≤ b → HeightBandJoined Y a b y y' →
    HeightBandJoined X (a - e) (b + e) x x'

/-- A local four-part form of band compatibility.  Mapwise band preservation
and controlled round trips imply the full two-map correspondence condition. -/
structure FunctionalGHMapBandCompatibility
    (X Y : FilteredReebGraph) (e : ℝ)
    (φ : X.Carrier → Y.Carrier) (ψ : Y.Carrier → X.Carrier) : Prop where
  band_to_map : ∀ {a b : ℝ} {x x' : X.Carrier}, a ≤ b →
    HeightBandJoined X a b x x' →
    HeightBandJoined Y (a - e) (b + e) (φ x) (φ x')
  band_inv_map : ∀ {a b : ℝ} {y y' : Y.Carrier}, a ≤ b →
    HeightBandJoined Y a b y y' →
    HeightBandJoined X (a - e) (b + e) (ψ y) (ψ y')
  roundtrip_X : ∀ x,
    HeightBandJoined X (Y.height (φ x) - e) (Y.height (φ x) + e)
      x (ψ (φ x))
  roundtrip_Y : ∀ y,
    HeightBandJoined Y (X.height (ψ y) - e) (X.height (ψ y) + e)
      y (φ (ψ y))

/-- Continuous height-controlled approximate inverses.  Continuity supplies
mapwise band preservation, while the controlled homotopies supply the two
round-trip clauses. -/
structure ContinuousFunctionalGHApproximation
    (X Y : FilteredReebGraph) (e : ℝ) where
  error_nonneg : 0 ≤ e
  toFun : X.Carrier → Y.Carrier
  invFun : Y.Carrier → X.Carrier
  continuous_toFun : Continuous toFun
  continuous_invFun : Continuous invFun
  height_to : ∀ x, |X.height x - Y.height (toFun x)| ≤ e
  height_inv : ∀ y, |X.height (invFun y) - Y.height y| ≤ e
  roundtrip_X : HeightControlledHomotopy X (fun x => Y.height (toFun x)) e
    id (fun x => invFun (toFun x))
  roundtrip_Y : HeightControlledHomotopy Y (fun y => X.height (invFun y)) e
    id (fun y => toFun (invFun y))

def ContinuousFunctionalGHApproximation.toMapBandCompatibility
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : ContinuousFunctionalGHApproximation X Y e) :
    FunctionalGHMapBandCompatibility X Y e h.toFun h.invFun where
  band_to_map := by
    intro a b x x' _hab hxx'
    exact hxx'.map_of_continuous_height_close h.continuous_toFun h.height_to
  band_inv_map := by
    intro a b y y' _hab hyy'
    exact hyy'.map_of_continuous_height_close h.continuous_invFun
      (fun y => by simpa only [abs_sub_comm] using h.height_inv y)
  roundtrip_X := h.roundtrip_X.joined
  roundtrip_Y := h.roundtrip_Y.joined

/-- A reduced route to full two-map compatibility.  It suffices to preserve
bands forward, reflect bands only between points in the forward image, and
connect every target point to the image of its selected inverse.  The three
uses of the base error account for the factor `3`. -/
theorem functionalGHMapBandCompatibility_of_imageBandReflection
    {X Y : FilteredReebGraph} {e : ℝ}
    {φ : X.Carrier → Y.Carrier} {ψ : Y.Carrier → X.Carrier}
    (he : 0 ≤ e)
    (hforward : ∀ {a b : ℝ} {x x' : X.Carrier}, a ≤ b →
      HeightBandJoined X a b x x' →
      HeightBandJoined Y (a - e) (b + e) (φ x) (φ x'))
    (hheight_inv : ∀ y, |X.height (ψ y) - Y.height y| ≤ e)
    (hroundtripY : ∀ y,
      HeightBandJoined Y (X.height (ψ y) - e) (X.height (ψ y) + e)
        y (φ (ψ y)))
    (hreflect : ∀ {a b : ℝ} {x x' : X.Carrier}, a ≤ b →
      HeightBandJoined Y a b (φ x) (φ x') →
      HeightBandJoined X (a - e) (b + e) x x') :
    FunctionalGHMapBandCompatibility X Y (3 * e) φ ψ := by
  refine
    { band_to_map := ?_
      band_inv_map := ?_
      roundtrip_X := ?_
      roundtrip_Y := ?_ }
  · intro a b x x' hab hxx'
    exact HeightBandJoined.mono (hforward hab hxx')
      (by linarith) (by linarith)
  · intro a b y y' hab hyy'
    have hyClose := hheight_inv y
    have hy'Close := hheight_inv y'
    rw [abs_sub_le_iff] at hyClose hy'Close
    have hleftBase := hroundtripY y
    have hrightBase := hroundtripY y'
    have hleftWide : HeightBandJoined Y (a - 2 * e) (b + 2 * e)
        y (φ (ψ y)) :=
      HeightBandJoined.mono hleftBase
        (by linarith [hyy'.source_mem.1, hyClose.1])
        (by linarith [hyy'.source_mem.2, hyClose.2])
    have hrightWide : HeightBandJoined Y (a - 2 * e) (b + 2 * e)
        y' (φ (ψ y')) :=
      HeightBandJoined.mono hrightBase
        (by linarith [hyy'.target_mem.1, hy'Close.1])
        (by linarith [hyy'.target_mem.2, hy'Close.2])
    have hmiddle : HeightBandJoined Y (a - 2 * e) (b + 2 * e) y y' :=
      HeightBandJoined.mono hyy' (by linarith) (by linarith)
    have himage : HeightBandJoined Y (a - 2 * e) (b + 2 * e)
        (φ (ψ y)) (φ (ψ y')) :=
      hleftWide.symm.trans (hmiddle.trans hrightWide)
    have hreflected := hreflect (show a - 2 * e ≤ b + 2 * e by linarith)
      himage
    convert hreflected using 1 <;> ring
  · intro x
    have hxClose := hheight_inv (φ x)
    rw [abs_sub_le_iff] at hxClose
    have hbase := hroundtripY (φ x)
    have hwide : HeightBandJoined Y
        (Y.height (φ x) - 2 * e) (Y.height (φ x) + 2 * e)
        (φ x) (φ (ψ (φ x))) :=
      HeightBandJoined.mono hbase
        (by linarith [hxClose.1]) (by linarith [hxClose.2])
    have hreflected := hreflect
      (show Y.height (φ x) - 2 * e ≤ Y.height (φ x) + 2 * e by linarith)
      hwide
    convert hreflected using 1 <;> ring
  · intro y
    exact HeightBandJoined.mono (hroundtripY y)
      (by linarith) (by linarith)

theorem FunctionalGHMapBandCompatibility.band_to_full
    {X Y : FilteredReebGraph} {e : ℝ}
    {φ : X.Carrier → Y.Carrier} {ψ : Y.Carrier → X.Carrier}
    (h : FunctionalGHMapBandCompatibility X Y e φ ψ)
    {x x' : X.Carrier} {y y' : Y.Carrier} {a b : ℝ}
    (hxy : FunctionalGHRel X Y φ ψ x y)
    (hx'y' : FunctionalGHRel X Y φ ψ x' y')
    (hab : a ≤ b) (hxx' : HeightBandJoined X a b x x') :
    HeightBandJoined Y (a - e) (b + e) y y' := by
  have hmap := h.band_to_map hab hxx'
  have hleft : HeightBandJoined Y (a - e) (b + e) y (φ x) := by
    rcases hxy with hxy | hxy
    · subst y
      exact JoinedIn.refl hmap.source_mem
    · have hr := h.roundtrip_Y y
      rw [← hxy] at hr
      exact HeightBandJoined.mono hr
        (by linarith [hxx'.source_mem.1])
        (by linarith [hxx'.source_mem.2])
  have hright : HeightBandJoined Y (a - e) (b + e) (φ x') y' := by
    rcases hx'y' with hx'y' | hx'y'
    · subst y'
      exact JoinedIn.refl hmap.target_mem
    · have hr := (h.roundtrip_Y y').symm
      rw [← hx'y'] at hr
      exact HeightBandJoined.mono hr
        (by linarith [hxx'.target_mem.1])
        (by linarith [hxx'.target_mem.2])
  exact hleft.trans (hmap.trans hright)

theorem FunctionalGHMapBandCompatibility.band_inv_full
    {X Y : FilteredReebGraph} {e : ℝ}
    {φ : X.Carrier → Y.Carrier} {ψ : Y.Carrier → X.Carrier}
    (h : FunctionalGHMapBandCompatibility X Y e φ ψ)
    {x x' : X.Carrier} {y y' : Y.Carrier} {a b : ℝ}
    (hxy : FunctionalGHRel X Y φ ψ x y)
    (hx'y' : FunctionalGHRel X Y φ ψ x' y')
    (hab : a ≤ b) (hyy' : HeightBandJoined Y a b y y') :
    HeightBandJoined X (a - e) (b + e) x x' := by
  have hmap := h.band_inv_map hab hyy'
  have hleft : HeightBandJoined X (a - e) (b + e) x (ψ y) := by
    rcases hxy with hxy | hxy
    · have hr := h.roundtrip_X x
      rw [← hxy] at hr
      exact HeightBandJoined.mono hr
        (by linarith [hyy'.source_mem.1])
        (by linarith [hyy'.source_mem.2])
    · rw [hxy]
      exact JoinedIn.refl hmap.source_mem
  have hright : HeightBandJoined X (a - e) (b + e) (ψ y') x' := by
    rcases hx'y' with hx'y' | hx'y'
    · have hr := (h.roundtrip_X x').symm
      rw [← hx'y'] at hr
      exact HeightBandJoined.mono hr
        (by linarith [hyy'.target_mem.1])
        (by linarith [hyy'.target_mem.2])
    · rw [hx'y']
      exact JoinedIn.refl hmap.target_mem
  exact hleft.trans (hmap.trans hright)

def ContinuousFunctionalGHApproximation.toBandCertificate
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : ContinuousFunctionalGHApproximation X Y e) :
    FunctionalGHBandCertificate X Y e where
  error_nonneg := h.error_nonneg
  toFun := h.toFun
  invFun := h.invFun
  height_to := h.height_to
  height_inv := h.height_inv
  band_to := h.toMapBandCompatibility.band_to_full
  band_inv := h.toMapBandCompatibility.band_inv_full

/-- Expanding every scalar band by `e` increases intrinsic scalar-range
distance by at most `2e`. -/
theorem heightRangeDist_le_add_of_band_relation
    {X Y : FilteredReebGraph} {e : ℝ} (he : 0 ≤ e)
    {x x' : X.Carrier} {y y' : Y.Carrier}
    (hband : ∀ {a b : ℝ}, a ≤ b →
      HeightBandJoined X a b x x' →
      HeightBandJoined Y (a - e) (b + e) y y') :
    heightRangeDist Y y y' ≤
      heightRangeDist X x x' + ENNReal.ofReal (2 * e) := by
  unfold heightRangeDist
  rw [ENNReal.sInf_add]
  refine le_iInf fun w => le_iInf fun hw => ?_
  rcases hw with ⟨a, b, hab, hjoined, rfl⟩
  apply sInf_le
  refine ⟨a - e, b + e, by linarith, hband hab hjoined, ?_⟩
  rw [show (b + e) - (a - e) = (b - a) + 2 * e by ring]
  exact (ENNReal.ofReal_add (sub_nonneg.mpr hab)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he)).symm

/-- A band certificate yields the standard functional-GH certificate with the
same reported cost; the conventional half-distortion absorbs the two-sided
band expansion. -/
noncomputable def FunctionalGHBandCertificate.toFunctionalGH
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : FunctionalGHBandCertificate X Y e) :
    FunctionalGHCertificate X Y (ENNReal.ofReal e) where
  toFun := h.toFun
  invFun := h.invFun
  height_to x := ENNReal.ofReal_le_ofReal (h.height_to x)
  height_inv y := ENNReal.ofReal_le_ofReal (h.height_inv y)
  range_distortion := by
    intro x x' y y' hxy hx'y'
    have hforward : heightRangeDist Y y y' ≤
        heightRangeDist X x x' + ENNReal.ofReal (2 * e) := by
      exact heightRangeDist_le_add_of_band_relation h.error_nonneg
        (fun hab hjoined => h.band_to hxy hx'y' hab hjoined)
    have hbackward : heightRangeDist X x x' ≤
        heightRangeDist Y y y' + ENNReal.ofReal (2 * e) := by
      exact heightRangeDist_le_add_of_band_relation h.error_nonneg
        (fun hab hjoined => h.band_inv hxy hx'y' hab hjoined)
    have htwo : ENNReal.ofReal (2 * e) = 2 * ENNReal.ofReal e := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← htwo]
    apply sup_le
    · exact tsub_le_iff_right.mpr (by simpa [add_comm] using hbackward)
    · exact tsub_le_iff_right.mpr (by simpa [add_comm] using hforward)

theorem functionalGHDistance_le_of_band_certificate
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : FunctionalGHBandCertificate X Y e) :
    functionalGHDistance X Y ≤ ENNReal.ofReal e :=
  functionalGHDistance_le_of_certificate h.toFunctionalGH

theorem functionalGHDistance_le_of_continuous_approximation
    {X Y : FilteredReebGraph} {e : ℝ}
    (h : ContinuousFunctionalGHApproximation X Y e) :
    functionalGHDistance X Y ≤ ENNReal.ofReal e :=
  functionalGHDistance_le_of_band_certificate h.toBandCertificate

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

/-- Lower half of the graph sandwich: all sufficiently close distinct sample
points are joined by an edge of `G`. -/
def ContainsProximityGraph
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M) (ρ : ℝ) : Prop :=
  proximityGraph M V sample ρ ≤ G

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

/-- Every continuum point has a nearby endpoint of an edge crossing a nearby
threshold.  The scalar slack is essential at extrema and for midpoint slices. -/
def CrossingCoverage
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M)
    (f : M → ℝ) (fhat : V → ℝ) (δ ξ : ℝ) : Prop :=
  ∀ x : M, ∃ (t : ℝ) (u : V),
    IsActiveVertex G fhat t u ∧
    dist (sample u) x ≤ δ ∧ |t - f x| ≤ ξ

/-- Crossing coverage is monotone under inclusion of neighborhood graphs. -/
theorem CrossingCoverage.mono_graph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G H : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fhat : V → ℝ} {δ ξ : ℝ}
    (hGH : G ≤ H) (h : CrossingCoverage M V G sample f fhat δ ξ) :
    CrossingCoverage M V H sample f fhat δ ξ := by
  intro x
  rcases h x with ⟨t, u, hu, hux, ht⟩
  exact ⟨t, u, isActiveVertex_mono hGH fhat t hu, hux, ht⟩

/-- Reachability by finitely many metric steps of length less than `κ`. -/
def MetricChain
    {X : Type*} [PseudoMetricSpace X] (κ : ℝ) (x y : X) : Prop :=
  Relation.ReflTransGen (fun a b => dist a b < κ) x y

/-- A preconnected metric space is chain connected at every positive scale. -/
theorem metricChain_of_preconnectedSpace
    {X : Type*} [PseudoMetricSpace X] [PreconnectedSpace X]
    {κ : ℝ} (hκ : 0 < κ) (x y : X) : MetricChain κ x y := by
  let R : Set X := {z | MetricChain κ x z}
  have hRopen : IsOpen R := by
    refine isOpen_iff_forall_mem_open.2 ?_
    intro z hz
    refine ⟨Metric.ball z κ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hκ⟩
    intro w hw
    exact hz.tail (by simpa only [Metric.mem_ball, dist_comm] using hw)
  have hRcOpen : IsOpen Rᶜ := by
    refine isOpen_iff_forall_mem_open.2 ?_
    intro z hz
    refine ⟨Metric.ball z κ, ?_, Metric.isOpen_ball, Metric.mem_ball_self hκ⟩
    intro w hw hwR
    exact hz (hwR.tail (by simpa only [Metric.mem_ball] using hw))
  have hRclopen : IsClopen R := ⟨isOpen_compl_iff.mp hRcOpen, hRopen⟩
  have hxR : x ∈ R := Relation.ReflTransGen.refl
  exact (isPreconnected_univ.subset_isClopen hRclopen ⟨x, Set.mem_univ x, hxR⟩)
    (Set.mem_univ y)

/-- A finite metric chain of active crossing witnesses.  This formulation is
independent of the algorithmic graph: consecutive sample points are required
only to lie within the canonical proximity radius. -/
inductive ActiveMetricChain
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} (sample : V → M) (fhat : V → ℝ) (ρ t : ℝ) : V → V → Prop
  | refl (u : V)
      (hu : IsActiveVertex (proximityGraph M V sample ρ) fhat t u) :
      ActiveMetricChain sample fhat ρ t u u
  | tail {u v w : V}
      (h : ActiveMetricChain sample fhat ρ t u v)
      (hw : IsActiveVertex (proximityGraph M V sample ρ) fhat t w)
      (hvw : v ≠ w) (hdist : dist (sample v) (sample w) ≤ ρ) :
      ActiveMetricChain sample fhat ρ t u w

theorem ActiveMetricChain.source_active
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (h : ActiveMetricChain sample fhat ρ t u v) :
    IsActiveVertex (proximityGraph M V sample ρ) fhat t u := by
  induction h with
  | refl hu => exact hu
  | tail _ _ _ _ ih => exact ih

theorem ActiveMetricChain.target_active
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (h : ActiveMetricChain sample fhat ρ t u v) :
    IsActiveVertex (proximityGraph M V sample ρ) fhat t v := by
  induction h with
  | refl hu => exact hu
  | tail _ hw _ _ _ => exact hw

/-- Every active metric chain is a walk in the support-induced slice of the
canonical proximity graph. -/
theorem ActiveMetricChain.reachable
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (h : ActiveMetricChain sample fhat ρ t u v) :
    (supportSliceGraph (proximityGraph M V sample ρ) fhat t).Reachable u v := by
  induction h with
  | refl _ => exact SimpleGraph.Reachable.refl _
  | tail h hw hvw hdist ih =>
      have hv := h.target_active
      have hadj :
          (supportSliceGraph (proximityGraph M V sample ρ) fhat t).Adj _ _ :=
        ⟨⟨hvw, hdist⟩, hv, hw⟩
      exact ih.trans ⟨.cons hadj .nil⟩

theorem ActiveMetricChain.of_dist
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (hu : IsActiveVertex (proximityGraph M V sample ρ) fhat t u)
    (hv : IsActiveVertex (proximityGraph M V sample ρ) fhat t v)
    (huv : u ≠ v) (hdist : dist (sample u) (sample v) ≤ ρ) :
    ActiveMetricChain sample fhat ρ t u v :=
  .tail (.refl u hu) hv huv hdist

theorem ActiveMetricChain.trans
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v w : V}
    (huv : ActiveMetricChain sample fhat ρ t u v)
    (hvw : ActiveMetricChain sample fhat ρ t v w) :
    ActiveMetricChain sample fhat ρ t u w := by
  induction hvw with
  | refl _ => exact huv
  | tail _ hx hne hdist ih => exact .tail ih hx hne hdist

theorem ActiveMetricChain.symm
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ} {ρ t : ℝ} {u v : V}
    (h : ActiveMetricChain sample fhat ρ t u v) :
    ActiveMetricChain sample fhat ρ t v u := by
  induction h with
  | refl hu => exact .refl _ hu
  | tail h hw hvw hdist ih =>
      have hwv : ActiveMetricChain sample fhat ρ t _ _ :=
        .of_dist hw h.target_active hvw.symm (by simpa only [dist_comm] using hdist)
      exact hwv.trans ih

/-- Active crossing witnesses at the common threshold `t` are `ε`-dense on
the continuum set `S`. -/
def ActiveWitnessDenseOn
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (fhat : V → ℝ)
    (ρ t ε : ℝ) (S : Set M) : Prop :=
  ∀ z ∈ S, ∃ u : V,
    IsActiveVertex (proximityGraph M V sample ρ) fhat t u ∧
    dist (sample u) z ≤ ε

/-- Every point of `S` has a nearby pair of distinct sample points within the
proximity radius whose observed scalar values straddle `t`. -/
def CrossingPairDenseOn
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (fhat : V → ℝ)
    (ρ t ε : ℝ) (S : Set M) : Prop :=
  ∀ z ∈ S, ∃ u v : V,
    u ≠ v ∧ dist (sample u) (sample v) ≤ ρ ∧ Crosses fhat t u v ∧
    dist (sample u) z ≤ ε ∧ dist (sample v) z ≤ ε

/-- Fill-distance bound for a finite sample. -/
def SampleDense
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (σ : ℝ) : Prop :=
  ∀ x : M, ∃ u : V, dist x (sample u) ≤ σ

/-- A true continuum function has points on both sides of `t`, uniformly near
every point of `S` and with scalar margin `m`. -/
def TrueCrossingPairDenseOn
    (M : Type*) [PseudoMetricSpace M] (f : M → ℝ)
    (t a m : ℝ) (S : Set M) : Prop :=
  ∀ z ∈ S, ∃ p n : M,
    dist p z ≤ a ∧ dist n z ≤ a ∧ f p + m < t ∧ t < f n - m

theorem CrossingPairDenseOn.activeWitnessDenseOn
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ}
    {ρ t ε : ℝ} {S : Set M}
    (h : CrossingPairDenseOn M V sample fhat ρ t ε S) :
    ActiveWitnessDenseOn M V sample fhat ρ t ε S := by
  intro z hz
  rcases h z hz with ⟨u, v, huv, hd, hcross, huz, _⟩
  exact ⟨u, ⟨v, ⟨⟨huv, hd⟩, hcross⟩⟩, huz⟩

/-- Dense sampling turns robust true crossing pairs into observed crossing
pairs.  All spatial and scalar scale conversions are explicit. -/
theorem TrueCrossingPairDenseOn.sample
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {L σ e ρ t a m ε : ℝ} {S : Set M}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hsample : SampleDense M V sample σ)
    (herr : ∀ u, |fhat u - f (sample u)| ≤ e)
    (hmargin : L * σ + e ≤ m)
    (hprox : 2 * (a + σ) ≤ ρ)
    (hwitness : a + σ ≤ ε)
    (htrue : TrueCrossingPairDenseOn M f t a m S) :
    CrossingPairDenseOn M V sample fhat ρ t ε S := by
  intro z hz
  rcases htrue z hz with ⟨p, n, hpz, hnz, hp, hn⟩
  rcases hsample p with ⟨u, hpu⟩
  rcases hsample n with ⟨v, hnv⟩
  have huScalar : |f (sample u) - f p| ≤ L * σ := by
    calc
      |f (sample u) - f p| ≤ L * dist (sample u) p := hL _ _
      _ ≤ L * σ := by
        gcongr
        simpa only [dist_comm] using hpu
  have hvScalar : |f (sample v) - f n| ≤ L * σ := by
    calc
      |f (sample v) - f n| ≤ L * dist (sample v) n := hL _ _
      _ ≤ L * σ := by
        gcongr
        simpa only [dist_comm] using hnv
  have huBelow : f (sample u) + e < t := by
    have huDiff : f (sample u) - f p ≤ L * σ :=
      (le_abs_self _).trans huScalar
    linarith
  have hvAbove : t < f (sample v) - e := by
    have hvDiff : f n - f (sample v) ≤ L * σ := by
      have hneg := (neg_le_abs (f (sample v) - f n)).trans hvScalar
      linarith
    linarith
  have hcross : Crosses fhat t u v :=
    crosses_of_approximation_margin (fun w => f (sample w)) fhat herr huBelow hvAbove
  have huv : u ≠ v := by
    intro huv
    subst v
    exact (not_crosses_of_eq fhat t rfl) hcross
  have huvDist : dist (sample u) (sample v) ≤ ρ := by
    calc
      dist (sample u) (sample v) ≤
          dist (sample u) p + dist p (sample v) := dist_triangle _ _ _
      _ ≤ dist (sample u) p +
          (dist p z + dist z n + dist n (sample v)) := by
        gcongr
        exact dist_triangle4 _ _ _ _
      _ ≤ σ + (a + a + σ) := by
        exact add_le_add
          (by simpa only [dist_comm] using hpu)
          (add_le_add
            (add_le_add hpz (by simpa only [dist_comm] using hnz)) hnv)
      _ = 2 * (a + σ) := by ring
      _ ≤ ρ := hprox
  have huz : dist (sample u) z ≤ ε := by
    calc
      dist (sample u) z ≤ dist (sample u) p + dist p z := dist_triangle _ _ _
      _ ≤ σ + a := add_le_add (by simpa only [dist_comm] using hpu) hpz
      _ = a + σ := add_comm _ _
      _ ≤ ε := hwitness
  have hvz : dist (sample v) z ≤ ε := by
    calc
      dist (sample v) z ≤ dist (sample v) n + dist n z := dist_triangle _ _ _
      _ ≤ σ + a := add_le_add (by simpa only [dist_comm] using hnv) hnz
      _ = a + σ := add_comm _ _
      _ ≤ ε := hwitness
  exact ⟨u, v, huv, huvDist, hcross, huz, hvz⟩

/-- Uniformly dense active witnesses along a continuum path lift to a finite
active metric chain.  The scale inequality is exactly the triangle-inequality
budget for two witness errors and one continuum-chain step. -/
theorem activeMetricChain_of_joinedIn_of_dense
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {fhat : V → ℝ}
    {ρ t ε κ : ℝ} {S : Set M} {x y : M}
    (hκ : 0 < κ) (hscale : 2 * ε + κ ≤ ρ)
    (hdense : ActiveWitnessDenseOn M V sample fhat ρ t ε S)
    (hxy : JoinedIn S x y) :
    ∃ u v : V, ActiveMetricChain sample fhat ρ t u v ∧
      dist (sample u) x ≤ ε ∧ dist (sample v) y ≤ ε := by
  let γ := hxy.somePath
  let P : Set M := Set.range γ
  letI : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, unitInterval.zero_mem⟩)
  have hPpath : IsPathConnected P := isPathConnected_range γ.continuous
  letI : PreconnectedSpace P :=
    isPreconnected_iff_preconnectedSpace.mp hPpath.isConnected.isPreconnected
  let xs : P := ⟨x, ⟨0, γ.source⟩⟩
  let ys : P := ⟨y, ⟨1, γ.target⟩⟩
  have hpoint : ∀ z : P, ∃ u : V,
      IsActiveVertex (proximityGraph M V sample ρ) fhat t u ∧
      dist (sample u) z.1 ≤ ε := by
    intro z
    apply hdense z.1
    rcases z.2 with ⟨s, hs⟩
    simpa only [hs] using hxy.somePath_mem s
  have hchain : MetricChain κ xs ys :=
    metricChain_of_preconnectedSpace hκ xs ys
  have hlift : ∀ {a b : P}, MetricChain κ a b →
      ∃ u v : V, ActiveMetricChain sample fhat ρ t u v ∧
        dist (sample u) a.1 ≤ ε ∧ dist (sample v) b.1 ≤ ε := by
    intro a b hab
    induction hab with
    | refl =>
        rcases hpoint a with ⟨u, hu, hua⟩
        exact ⟨u, u, .refl u hu, hua, hua⟩
    | @tail b c _ hbc ih =>
        rcases ih with ⟨u, v, huv, hua, hvb⟩
        rcases hpoint c with ⟨w, hw, hwc⟩
        by_cases hvw : v = w
        · subst w
          exact ⟨u, v, huv, hua, hwc⟩
        · have hbc' : dist b.1 c.1 ≤ κ := by
            exact le_of_lt hbc
          have hvwDist : dist (sample v) (sample w) ≤ ρ := by
            calc
              dist (sample v) (sample w) ≤
                  dist (sample v) b.1 + dist b.1 (sample w) :=
                dist_triangle _ _ _
              _ ≤ dist (sample v) b.1 +
                  (dist b.1 c.1 + dist c.1 (sample w)) := by
                gcongr
                exact dist_triangle _ _ _
              _ ≤ ε + (κ + ε) := by
                gcongr
                simpa only [dist_comm] using hwc
              _ = 2 * ε + κ := by ring
              _ ≤ ρ := hscale
          exact ⟨u, w, .tail huv hw hvw hvwDist, hua, hwc⟩
  rcases hlift hchain with ⟨u, v, huv, hux, hvy⟩
  exact ⟨u, v, huv, by simpa [xs] using hux, by simpa [ys] using hvy⟩

/-- Along every exact continuum level path there is one nearby threshold whose
active proximity-graph witnesses are uniformly `δ`-dense on that path.  This is
the local statement to be supplied by regular-level and Morse critical charts. -/
def CommonThresholdActiveDensity
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ t : ℝ, |t - s| ≤ ξ ∧
      ActiveWitnessDenseOn M V sample fhat ρ t δ
        (pathComponentIn x {z | f z = s})

/-- The local crossing-pair condition expected from regular-level charts and
Morse normal forms. -/
def CommonThresholdCrossingPairDensity
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ t : ℝ, |t - s| ≤ ξ ∧
      CrossingPairDenseOn M V sample fhat ρ t δ
        (pathComponentIn x {z | f z = s})

/-- Common-threshold two-sided variation for the true continuum function. -/
def CommonThresholdTrueCrossingPairDensity
    (M : Type*) [PseudoMetricSpace M] (f : M → ℝ)
    (a m ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ t : ℝ, |t - s| ≤ ξ ∧
      TrueCrossingPairDenseOn M f t a m
        (pathComponentIn x {z | f z = s})

/-- Crossing-pair density is monotone under enlarging the spatial radius,
weakening the scalar margin, and enlarging the allowed threshold slack. -/
theorem CommonThresholdTrueCrossingPairDensity.mono
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ}
    {a m ξ a' m' ξ' : ℝ}
    (h : CommonThresholdTrueCrossingPairDensity M f a m ξ)
    (ha : a ≤ a') (hm : m' ≤ m) (hξ : ξ ≤ ξ') :
    CommonThresholdTrueCrossingPairDensity M f a' m' ξ' := by
  intro s x y hxy
  rcases h s hxy with ⟨t, hts, hpairs⟩
  refine ⟨t, hts.trans hξ, ?_⟩
  intro z hz
  rcases hpairs z hz with ⟨p, n, hpz, hnz, hp, hn⟩
  exact ⟨p, n, hpz.trans ha, hnz.trans ha, by linarith, by linarith⟩

/-- Reversing the scalar orientation preserves the quantitative crossing
condition.  The witnesses exchange their below/above roles and the common
threshold is negated. -/
theorem CommonThresholdTrueCrossingPairDensity.neg
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ}
    {a m ξ : ℝ}
    (h : CommonThresholdTrueCrossingPairDensity M f a m ξ) :
    CommonThresholdTrueCrossingPairDensity M (fun z ↦ -f z) a m ξ := by
  intro s x y hxy
  have hlevel : {z : M | f z = -s} = {z : M | -f z = s} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hz <;> linarith
  have hxy' : JoinedIn {z : M | f z = -s} x y := by
    rw [hlevel]
    exact hxy
  rcases h (-s) hxy' with ⟨t, hts, hpairs⟩
  refine ⟨-t, ?_, ?_⟩
  · calc
      |-t - s| = |-(t - -s)| := by ring_nf
      _ = |t - -s| := abs_neg _
      _ ≤ ξ := hts
  · have hcomponent :
        pathComponentIn x {z : M | f z = -s} =
          pathComponentIn x {z : M | -f z = s} := by rw [hlevel]
    intro z hz
    have hz' : z ∈ pathComponentIn x {z : M | f z = -s} := by
      rw [hcomponent]
      exact hz
    rcases hpairs z hz' with ⟨p, n, hpz, hnz, hp, hn⟩
    refine ⟨n, p, hnz, hpz, ?_, ?_⟩
    · change -f n + m < -t
      linarith
    · change -t < -f p - m
      linarith

/-- The quantitative local consequence expected from Morse normal forms on a
compact manifold.  At every sufficiently small spatial radius `a`, crossings
have a quadratic scalar margin and extrema require at most a quadratic shift
of the common threshold.  Regular charts provide stronger linear variation;
the quadratic rate is the uniform rate that also covers critical charts.

This property is deliberately independent of samples and neighborhood graphs.
It isolates the one analytic statement whose derivation from the classical
Morse lemma is not currently available in Mathlib. -/
def QuadraticLevelCrossingCondition
    (M : Type*) [PseudoMetricSpace M] (f : M → ℝ)
    (cShift cMargin a₀ : ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ a₀ →
    CommonThresholdTrueCrossingPairDensity M f a
      (cMargin * a ^ 2) (cShift * a ^ 2)

/-- Quadratic level crossings are invariant under reversing the filter. -/
theorem QuadraticLevelCrossingCondition.neg
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ}
    {cShift cMargin a₀ : ℝ}
    (h : QuadraticLevelCrossingCondition M f cShift cMargin a₀) :
    QuadraticLevelCrossingCondition M (fun z ↦ -f z)
      cShift cMargin a₀ := by
  intro a ha ha₀
  exact (h a ha ha₀).neg

/-- A quadratic level-crossing condition supplies the exact crossing property
at any larger proof slack. -/
theorem QuadraticLevelCrossingCondition.crossing_pairs
    {M : Type*} [PseudoMetricSpace M] {f : M → ℝ}
    {cShift cMargin a₀ a ξ : ℝ}
    (h : QuadraticLevelCrossingCondition M f cShift cMargin a₀)
    (ha : 0 < a) (ha₀ : a ≤ a₀)
    (hshift : cShift * a ^ 2 ≤ ξ) :
    CommonThresholdTrueCrossingPairDensity M f a
      (cMargin * a ^ 2) ξ :=
  (h a ha ha₀).mono le_rfl le_rfl hshift

/-- The one-dimensional Morse minimum normal form has uniform quadratic
crossings.  At the critical level the proof uses a threshold shifted upward by
`a² / 64`; away from the critical level it uses the smaller shift `a² / 128`.
This is the formal model for why exact crossing at an extremum must be replaced
by a nearby common threshold. -/
theorem quadraticLevelCrossingCondition_sq (a₀ : ℝ) :
    QuadraticLevelCrossingCondition ℝ (fun x : ℝ ↦ x ^ 2)
      (1 / 64) (1 / 128) a₀ := by
  intro a ha _
  intro s x y hxy
  have ha0 : 0 ≤ a := ha.le
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  by_cases hs : s = 0
  · refine ⟨a ^ 2 / 64, ?_, ?_⟩
    · rw [hs, sub_zero, abs_of_nonneg]
      · ring_nf
        exact le_rfl
      · positivity
    · intro z hz
      have hzLevelSet : z ∈ {w : ℝ | w ^ 2 = s} :=
        pathComponentIn_subset hz
      have hzLevel : z ^ 2 = s := hzLevelSet
      have hz0 : z = 0 := by nlinarith
      subst z
      refine ⟨0, a / 2, ?_, ?_, ?_, ?_⟩
      · simp [Real.dist_eq, ha0]
      · rw [Real.dist_eq, sub_zero, abs_of_nonneg]
        · linarith
        · positivity
      · norm_num
        nlinarith
      · norm_num
        nlinarith
  · refine ⟨s + a ^ 2 / 128, ?_, ?_⟩
    · rw [add_sub_cancel_left, abs_of_nonneg]
      · norm_num
        nlinarith [sq_nonneg a]
      · positivity
    · intro z hz
      have hzLevelSet : z ∈ {w : ℝ | w ^ 2 = s} :=
        pathComponentIn_subset hz
      have hzLevel : z ^ 2 = s := hzLevelSet
      have hz_ne : z ≠ 0 := by
        intro hz0
        subst z
        simp only [zero_pow (by norm_num : 2 ≠ 0)] at hzLevel
        exact hs hzLevel.symm
      rcases lt_or_gt_of_ne hz_ne with hzneg | hzpos
      · by_cases hzsmall : -z ≤ a / 2
        · refine ⟨0, z - a / 2, ?_, ?_, ?_, ?_⟩
          · rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonpos hzneg.le]
            linarith
          · rw [Real.dist_eq]
            have : z - a / 2 - z = -(a / 2) := by ring
            rw [this, abs_neg, abs_of_nonneg]
            · linarith
            · positivity
          · norm_num
            nlinarith [sq_nonneg z]
          · norm_num
            nlinarith

        · have hzlarge : a / 2 < -z := lt_of_not_ge hzsmall
          refine ⟨z + a / 2, z - a / 2, ?_, ?_, ?_, ?_⟩
          · rw [Real.dist_eq]
            have : z + a / 2 - z = a / 2 := by ring
            rw [this, abs_of_nonneg]
            · linarith
            · positivity
          · rw [Real.dist_eq]
            have : z - a / 2 - z = -(a / 2) := by ring
            rw [this, abs_neg, abs_of_nonneg]
            · linarith
            · positivity
          · norm_num
            nlinarith
          · norm_num
            nlinarith
      · by_cases hzsmall : z ≤ a / 2
        · refine ⟨0, z + a / 2, ?_, ?_, ?_, ?_⟩
          · rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hzpos.le]
            linarith
          · rw [Real.dist_eq]
            have : z + a / 2 - z = a / 2 := by ring
            rw [this, abs_of_nonneg]
            · linarith
            · positivity
          · norm_num
            nlinarith [sq_nonneg z]
          · norm_num
            nlinarith
        · have hzlarge : a / 2 < z := lt_of_not_ge hzsmall
          refine ⟨z - a / 2, z + a / 2, ?_, ?_, ?_, ?_⟩
          · rw [Real.dist_eq]
            have : z - a / 2 - z = -(a / 2) := by ring
            rw [this, abs_neg, abs_of_nonneg]
            · linarith
            · positivity
          · rw [Real.dist_eq]
            have : z + a / 2 - z = a / 2 := by ring
            rw [this, abs_of_nonneg]
            · linarith
            · positivity
          · norm_num
            nlinarith
          · norm_num
            nlinarith

/-- The one-dimensional Morse maximum normal form follows by reversing the
scalar orientation of the minimum model. -/
theorem quadraticLevelCrossingCondition_neg_sq (a₀ : ℝ) :
    QuadraticLevelCrossingCondition ℝ (fun x : ℝ ↦ -(x ^ 2))
      (1 / 64) (1 / 128) a₀ :=
  (quadraticLevelCrossingCondition_sq a₀).neg

/-- The two-dimensional saddle normal form has two-sided quadratic crossings
at the exact level.  Moving only in the positive-square coordinate raises the
function, while moving only in the negative-square coordinate lowers it. -/
theorem quadraticLevelCrossingCondition_saddle (a₀ : ℝ) :
    QuadraticLevelCrossingCondition (ℝ × ℝ)
      (fun z : ℝ × ℝ ↦ z.1 ^ 2 - z.2 ^ 2)
      0 (1 / 128) a₀ := by
  intro a ha _
  intro s x y hxy
  have ha0 : 0 ≤ a := ha.le
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  refine ⟨s, by simp, ?_⟩
  intro z hz
  have hzLevelSet : z ∈ {w : ℝ × ℝ | w.1 ^ 2 - w.2 ^ 2 = s} :=
    pathComponentIn_subset hz
  have hzLevel : z.1 ^ 2 - z.2 ^ 2 = s := hzLevelSet
  let p : ℝ × ℝ :=
    (z.1, if 0 ≤ z.2 then z.2 + a / 2 else z.2 - a / 2)
  let n : ℝ × ℝ :=
    (if 0 ≤ z.1 then z.1 + a / 2 else z.1 - a / 2, z.2)
  refine ⟨p, n, ?_, ?_, ?_, ?_⟩
  · dsimp only [p]
    split_ifs with hz2
    · rw [← Prod.eta z, dist_prod_same_left, Real.dist_eq]
      have hdiff : z.2 + a / 2 - z.2 = a / 2 := by ring
      rw [hdiff, abs_of_nonneg]
      · linarith
      · positivity
    · rw [← Prod.eta z, dist_prod_same_left, Real.dist_eq]
      have hdiff : z.2 - a / 2 - z.2 = -(a / 2) := by ring
      rw [hdiff, abs_neg, abs_of_nonneg]
      · linarith
      · positivity
  · dsimp only [n]
    split_ifs with hz1
    · rw [← Prod.eta z, dist_prod_same_right, Real.dist_eq]
      have hdiff : z.1 + a / 2 - z.1 = a / 2 := by ring
      rw [hdiff, abs_of_nonneg]
      · linarith
      · positivity
    · rw [← Prod.eta z, dist_prod_same_right, Real.dist_eq]
      have hdiff : z.1 - a / 2 - z.1 = -(a / 2) := by ring
      rw [hdiff, abs_neg, abs_of_nonneg]
      · linarith
      · positivity
  · dsimp only [p]
    split_ifs with hz2
    · norm_num
      nlinarith
    · norm_num
      nlinarith
  · dsimp only [n]
    split_ifs with hz1
    · norm_num
      nlinarith
    · norm_num
      nlinarith

/-- On a regular chart the linear normal form has stronger, linear variation.
Restricting to radii `a ≤ a₀` turns this into the uniform quadratic margin
used by the global theorem. -/
theorem quadraticLevelCrossingCondition_id {a₀ : ℝ} (ha₀ : 0 < a₀) :
    QuadraticLevelCrossingCondition ℝ (fun x : ℝ ↦ x)
      0 (1 / (8 * a₀)) a₀ := by
  intro a ha haa₀
  intro s x y hxy
  have ha0 : 0 ≤ a := ha.le
  have hc0 : 0 ≤ 1 / (8 * a₀) := by positivity
  have ha2_le : a ^ 2 ≤ a * a₀ := by
    nlinarith
  have hmargin_le : (1 / (8 * a₀)) * a ^ 2 ≤ a / 8 := by
    calc
      (1 / (8 * a₀)) * a ^ 2 ≤
          (1 / (8 * a₀)) * (a * a₀) :=
        mul_le_mul_of_nonneg_left ha2_le hc0
      _ = a / 8 := by
        field_simp [ne_of_gt ha₀]
        <;> ring
  have hmargin_lt : (1 / (8 * a₀)) * a ^ 2 < a / 2 := by
    linarith
  refine ⟨s, by simp, ?_⟩
  intro z hz
  have hzLevelSet : z ∈ {w : ℝ | w = s} := pathComponentIn_subset hz
  have hzLevel : z = s := hzLevelSet
  refine ⟨z - a / 2, z + a / 2, ?_, ?_, ?_, ?_⟩
  · rw [Real.dist_eq]
    have hdiff : z - a / 2 - z = -(a / 2) := by ring
    rw [hdiff, abs_neg, abs_of_nonneg]
    · linarith
    · positivity
  · rw [Real.dist_eq]
    have hdiff : z + a / 2 - z = a / 2 := by ring
    rw [hdiff, abs_of_nonneg]
    · linarith
    · positivity
  · change z - a / 2 + (1 / (8 * a₀)) * a ^ 2 < s
    linarith
  · change s < z + a / 2 - (1 / (8 * a₀)) * a ^ 2
    linarith

/-- Quantitative continuum two-sided variation, dense sampling, and uniform
filter consistency imply the observed common-threshold crossing-pair condition. -/
theorem CommonThresholdTrueCrossingPairDensity.sample
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {L σ e ρ a m ε ξ : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hsample : SampleDense M V sample σ)
    (herr : ∀ u, |fhat u - f (sample u)| ≤ e)
    (hmargin : L * σ + e ≤ m)
    (hprox : 2 * (a + σ) ≤ ρ)
    (hwitness : a + σ ≤ ε)
    (htrue : CommonThresholdTrueCrossingPairDensity M f a m ξ) :
    CommonThresholdCrossingPairDensity M V sample f fhat ρ ε ξ := by
  intro s x y hxy
  rcases htrue s hxy with ⟨t, hts, hpairs⟩
  exact ⟨t, hts, hpairs.sample hL_nonneg hL hsample herr
    hmargin hprox hwitness⟩

theorem CommonThresholdCrossingPairDensity.to_activeDensity
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : CommonThresholdCrossingPairDensity M V sample f fhat ρ δ ξ) :
    CommonThresholdActiveDensity M V sample f fhat ρ δ ξ := by
  intro s x y hxy
  rcases h s hxy with ⟨t, hts, hpairs⟩
  exact ⟨t, hts, hpairs.activeWitnessDenseOn⟩

/-- The geometric active-witness task in finite-chain form.  Morse charts and
sampling density should construct this chain; no connectivity of an output
graph is assumed here. -/
def ActiveWitnessChainCoverage
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ (t : ℝ) (u v : V),
      ActiveMetricChain sample fhat ρ t u v ∧
      dist (sample u) x ≤ δ ∧ dist (sample v) y ≤ δ ∧ |t - s| ≤ ξ

/-- Uniform common-threshold active density implies finite active-witness chain
coverage whenever the proximity radius has room for two sampling errors. -/
theorem CommonThresholdActiveDensity.to_chainCoverage
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ} (hgap : 2 * δ < ρ)
    (h : CommonThresholdActiveDensity M V sample f fhat ρ δ ξ) :
    ActiveWitnessChainCoverage M V sample f fhat ρ δ ξ := by
  intro s x y hxy
  rcases h s hxy with ⟨t, hts, hdense⟩
  have hxLevel : x ∈ {z : M | f z = s} := hxy.source_mem
  have hxComponent : x ∈ pathComponentIn x {z : M | f z = s} :=
    mem_pathComponentIn_self hxLevel
  have hyComponent : y ∈ pathComponentIn x {z : M | f z = s} := hxy
  have hxyComponent :
      JoinedIn (pathComponentIn x {z : M | f z = s}) x y :=
    (isPathConnected_pathComponentIn hxLevel).joinedIn
      x hxComponent y hyComponent
  have hκ : 0 < ρ - 2 * δ := by linarith
  have hscale : 2 * δ + (ρ - 2 * δ) ≤ ρ := by linarith
  rcases activeMetricChain_of_joinedIn_of_dense hκ hscale hdense hxyComponent with
    ⟨u, v, hchain, hux, hvy⟩
  exact ⟨t, u, v, hchain, hux, hvy, hts⟩

/-- Chain coverage includes pointwise crossing coverage as the constant-path
case. -/
theorem ActiveWitnessChainCoverage.crossingCoverage
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ActiveWitnessChainCoverage M V sample f fhat ρ δ ξ) :
    CrossingCoverage M V (proximityGraph M V sample ρ) sample f fhat δ ξ := by
  intro x
  have hxx : JoinedIn {z | f z = f x} x x := JoinedIn.refl rfl
  rcases h (f x) hxx with ⟨t, u, v, hchain, hux, _, hts⟩
  exact ⟨t, u, hchain.source_active, hux, hts⟩

/-- Nearby crossing witnesses associated with one continuum level-set path
lie in the same support-induced slice component. -/
def SupportComplete
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (G : SimpleGraph V) (sample : V → M)
    (f : M → ℝ) (fhat : V → ℝ) (δ ξ : ℝ) : Prop :=
  ∀ (s : ℝ) {x y : M}, JoinedIn {z | f z = s} x y →
    ∃ (t : ℝ) (u v : V),
      IsActiveVertex G fhat t u ∧ IsActiveVertex G fhat t v ∧
      dist (sample u) x ≤ δ ∧ dist (sample v) y ≤ δ ∧
      |t - s| ≤ ξ ∧ (supportSliceGraph G fhat t).Reachable u v

/-- Support completeness formulated for the canonical proximity graph.  This
is the manifold-and-sampling statement that is independent of the supplied
neighborhood graph. -/
def ProximitySupportComplete
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  SupportComplete M V (proximityGraph M V sample ρ) sample f fhat δ ξ

/-- The complete active-witness statement for a canonical proximity graph:
nearby crossing witnesses exist and witnesses on one continuum level path are
connected at a common nearby threshold. -/
def ProximityWitnessAdequate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  CrossingCoverage M V (proximityGraph M V sample ρ) sample f fhat δ ξ ∧
  ProximitySupportComplete M V sample f fhat ρ δ ξ

/-- A non-circular sufficient condition for proximity witness adequacy: finite
metric chains of active witnesses.  Pointwise crossing coverage follows from
the constant-path case. -/
def ProximityChainWitnessAdequate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  ActiveWitnessChainCoverage M V sample f fhat ρ δ ξ

/-- The local geometric form of canonical witness adequacy. -/
def ProximityActiveDensityAdequate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  2 * δ < ρ ∧ CommonThresholdActiveDensity M V sample f fhat ρ δ ξ

/-- The chart-level sufficient condition: a spatial scale gap and uniformly
dense crossing pairs at one nearby threshold. -/
def ProximityCrossingPairAdequate
    (M : Type*) [PseudoMetricSpace M]
    (V : Type*) (sample : V → M) (f : M → ℝ) (fhat : V → ℝ)
    (ρ δ ξ : ℝ) : Prop :=
  2 * δ < ρ ∧ CommonThresholdCrossingPairDensity M V sample f fhat ρ δ ξ

/-- A single constructor reducing proximity witness adequacy to quantitative
two-sided variation of the true continuum function. -/
theorem ProximityCrossingPairAdequate.of_true
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {L σ e ρ a m ε ξ : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ x y, |f x - f y| ≤ L * dist x y)
    (hsample : SampleDense M V sample σ)
    (herr : ∀ u, |fhat u - f (sample u)| ≤ e)
    (hmargin : L * σ + e ≤ m)
    (hprox : 2 * (a + σ) ≤ ρ)
    (hwitness : a + σ ≤ ε)
    (hgap : 2 * ε < ρ)
    (htrue : CommonThresholdTrueCrossingPairDensity M f a m ξ) :
    ProximityCrossingPairAdequate M V sample f fhat ρ ε ξ :=
  ⟨hgap, htrue.sample hL_nonneg hL hsample herr hmargin hprox hwitness⟩

theorem ProximityCrossingPairAdequate.to_activeDensityAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityCrossingPairAdequate M V sample f fhat ρ δ ξ) :
    ProximityActiveDensityAdequate M V sample f fhat ρ δ ξ :=
  ⟨h.1, h.2.to_activeDensity⟩

theorem ProximityActiveDensityAdequate.to_chainWitnessAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityActiveDensityAdequate M V sample f fhat ρ δ ξ) :
    ProximityChainWitnessAdequate M V sample f fhat ρ δ ξ :=
  h.2.to_chainCoverage h.1

theorem ActiveWitnessChainCoverage.to_proximitySupportComplete
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ActiveWitnessChainCoverage M V sample f fhat ρ δ ξ) :
    ProximitySupportComplete M V sample f fhat ρ δ ξ := by
  intro s x y hxy
  rcases h s hxy with ⟨t, u, v, hchain, hux, hvy, hts⟩
  exact ⟨t, u, v, hchain.source_active, hchain.target_active,
    hux, hvy, hts, hchain.reachable⟩

/-- Finite metric witness chains prove the full canonical proximity-graph
witness theorem. -/
theorem ProximityChainWitnessAdequate.to_proximityWitnessAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityChainWitnessAdequate M V sample f fhat ρ δ ξ) :
    ProximityWitnessAdequate M V sample f fhat ρ δ ξ :=
  ⟨h.crossingCoverage, h.to_proximitySupportComplete⟩

theorem ProximityActiveDensityAdequate.to_proximityWitnessAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityActiveDensityAdequate M V sample f fhat ρ δ ξ) :
    ProximityWitnessAdequate M V sample f fhat ρ δ ξ :=
  h.to_chainWitnessAdequate.to_proximityWitnessAdequate

theorem ProximityCrossingPairAdequate.to_proximityWitnessAdequate
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {sample : V → M} {f : M → ℝ} {fhat : V → ℝ}
    {ρ δ ξ : ℝ}
    (h : ProximityCrossingPairAdequate M V sample f fhat ρ δ ξ) :
    ProximityWitnessAdequate M V sample f fhat ρ δ ξ :=
  h.to_activeDensityAdequate.to_proximityWitnessAdequate

/-- Support completeness is monotone under inclusion of neighborhood graphs. -/
theorem SupportComplete.mono_graph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G H : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fhat : V → ℝ} {δ ξ : ℝ}
    (hGH : G ≤ H) (h : SupportComplete M V G sample f fhat δ ξ) :
    SupportComplete M V H sample f fhat δ ξ := by
  intro s x y hxy
  rcases h s hxy with ⟨t, u, v, hu, hv, hux, hvy, hts, huv⟩
  refine ⟨t, u, v,
    isActiveVertex_mono hGH fhat t hu,
    isActiveVertex_mono hGH fhat t hv,
    hux, hvy, hts, ?_⟩
  exact SimpleGraph.Reachable.mono (supportSliceGraph_mono hGH fhat t) huv

/-- The lower graph-sandwich inclusion transfers the canonical proximity-graph
completeness theorem to the actual neighborhood graph used by the algorithm. -/
theorem ProximitySupportComplete.to_graph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fhat : V → ℝ} {ρ δ ξ : ℝ}
    (hclose : ContainsProximityGraph M V G sample ρ)
    (h : ProximitySupportComplete M V sample f fhat ρ δ ξ) :
    SupportComplete M V G sample f fhat δ ξ :=
  h.mono_graph hclose

/-- Both active-witness conclusions transfer together through the lower graph
sandwich. -/
theorem ProximityWitnessAdequate.to_graph
    {M : Type*} [PseudoMetricSpace M]
    {V : Type*} {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fhat : V → ℝ} {ρ δ ξ : ℝ}
    (hclose : ContainsProximityGraph M V G sample ρ)
    (h : ProximityWitnessAdequate M V sample f fhat ρ δ ξ) :
    CrossingCoverage M V G sample f fhat δ ξ ∧
      SupportComplete M V G sample f fhat δ ξ :=
  ⟨h.1.mono_graph hclose, h.2.to_graph hclose⟩

/-- Connected components of one exact scalar level set. -/
def LevelConnectedComponent
    (M : Type*) [TopologicalSpace M] (f : M → ℝ) (t : ℝ) :=
  ConnectedComponents {x : M // f x = t}

/-- A concrete finite-critical-value tameness condition.  Away from a finite
set of scalar values, the type of connected level-set components is locally
constant up to equivalence. -/
def TameLevelSetFunction
    (M : Type*) [TopologicalSpace M] (f : M → ℝ) : Prop :=
  Continuous f ∧
    (∀ t, LocPathConnectedSpace {x : M // f x = t}) ∧
    (∀ t, Finite (LevelConnectedComponent M f t)) ∧
    ∃ criticalValues : Set ℝ, criticalValues.Finite ∧
      ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ∩ criticalValues = ∅ →
        Nonempty (LevelConnectedComponent M f a ≃ LevelConnectedComponent M f b)

theorem TameLevelSetFunction.continuous
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) : Continuous f :=
  h.1

theorem TameLevelSetFunction.finite_level_components
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) (t : ℝ) :
    Finite (LevelConnectedComponent M f t) :=
  h.2.2.1 t

theorem TameLevelSetFunction.locPathConnected_level
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) (t : ℝ) :
    LocPathConnectedSpace {x : M // f x = t} :=
  h.2.1 t

theorem TameLevelSetFunction.exists_finite_criticalValues
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) :
    ∃ criticalValues : Set ℝ, criticalValues.Finite ∧
      ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ∩ criticalValues = ∅ →
        Nonempty (LevelConnectedComponent M f a ≃ LevelConnectedComponent M f b) :=
  h.2.2.2

/-- Numerical form of tameness: the number of connected level components is
constant across intervals containing no critical value. -/
noncomputable def TameLevelSetFunction.levelComponentCount
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) (t : ℝ) : ℕ := by
  letI : Finite (LevelConnectedComponent M f t) :=
    h.finite_level_components t
  letI : Fintype (LevelConnectedComponent M f t) := Fintype.ofFinite _
  exact Fintype.card (LevelConnectedComponent M f t)

theorem TameLevelSetFunction.exists_criticalValues_card_eq
    {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    (h : TameLevelSetFunction M f) :
    ∃ criticalValues : Set ℝ, criticalValues.Finite ∧
      ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ∩ criticalValues = ∅ →
        h.levelComponentCount a = h.levelComponentCount b := by
  rcases h.exists_finite_criticalValues with ⟨C, hCfinite, hregular⟩
  refine ⟨C, hCfinite, ?_⟩
  intro a b hab hC
  letI : Finite (LevelConnectedComponent M f a) :=
    h.finite_level_components a
  letI : Finite (LevelConnectedComponent M f b) :=
    h.finite_level_components b
  letI : Fintype (LevelConnectedComponent M f a) := Fintype.ofFinite _
  letI : Fintype (LevelConnectedComponent M f b) := Fintype.ofFinite _
  simpa only [levelComponentCount] using
    Fintype.card_congr (Classical.choice (hregular hab hC))

/-- Under the local path-connectedness part of tameness, classical connected
level components are also path components. -/
theorem TameLevelSetFunction.joinedIn_of_sameLevelComponent
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (htame : TameLevelSetFunction M f) {x y : M}
    (hxy : SameLevelComponent f x y) :
    JoinedIn {z | f z = f x} x y := by
  rcases hxy with ⟨hfxy, hyComponent⟩
  have hxLevel : x ∈ {z | f z = f x} := rfl
  have hyLevel : y ∈ {z | f z = f x} :=
    connectedComponentIn_subset _ _ hyComponent
  let X := {z : M // f z = f x}
  let xs : X := ⟨x, hxLevel⟩
  let ys : X := ⟨y, hyLevel⟩
  have hyImage : y ∈ ((↑) : X → M) '' connectedComponent xs := by
    simpa only [connectedComponentIn_eq_image hxLevel] using hyComponent
  rcases hyImage with ⟨z, hzComponent, hzy⟩
  have hzys : z = ys := Subtype.ext hzy
  subst z
  letI : LocPathConnectedSpace X := htame.locPathConnected_level (f x)
  have hyPath : ys ∈ pathComponent xs := by
    rw [pathComponent_eq_connectedComponent]
    exact hzComponent
  apply (joinedIn_iff_joined hxLevel hyLevel).mpr
  exact mem_pathComponent_iff.mp hyPath

theorem TameLevelSetFunction.sameLevelComponent_iff_joinedIn
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (htame : TameLevelSetFunction M f) (x y : M) :
    SameLevelComponent f x y ↔ JoinedIn {z | f z = f x} x y :=
  ⟨htame.joinedIn_of_sameLevelComponent,
    sameLevelComponent_of_joinedIn f⟩

theorem TameLevelSetFunction.quotientMap_eq_iff_joinedIn
    {M : Type} [TopologicalSpace M] {f : M → ℝ}
    (htame : TameLevelSetFunction M f) (x y : M) :
    continuumReebQuotientMap f x = continuumReebQuotientMap f y ↔
      JoinedIn {z | f z = f x} x y := by
  rw [continuumReebQuotientMap_eq_iff]
  exact htame.sameLevelComponent_iff_joinedIn x y

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

/-- Connectedness is preserved when a connected set is viewed inside a
larger subtype containing it. -/
theorem isConnected_preimage_subtypeVal
    {X : Type} [TopologicalSpace X] {U W : Set X}
    (hW : IsConnected W) (hWU : W ⊆ U) :
    IsConnected (((↑) : U → X) ⁻¹' W) := by
  constructor
  · rcases hW.nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hWU hx⟩, hx⟩
  · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hWU]
    exact hW.isPreconnected

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

/-- Chosen support representative of a canonical slice node. -/
noncomputable def canonicalNodeSupportWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (fhat : V → ℝ)
    (x : SliceNode G fhat (canonicalThreshold fhat)) : V :=
  discreteRawSupportWitness G fhat (canonicalThreshold fhat) (.inl x)

theorem canonicalNodeSupportWitness_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (fhat : V → ℝ)
    (x : SliceNode G fhat (canonicalThreshold fhat)) :
    canonicalNodeSupportWitness G fhat x ∈
      componentSupport G fhat (canonicalThreshold fhat x.1) x.2 :=
  discreteRawSupportWitness_vertex_mem G fhat (canonicalThreshold fhat) x

/-- Image of a canonical slice node in the continuum Reeb quotient. -/
noncomputable def ApproximationHypotheses.canonicalNodeContinuumMap
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (_h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (x : SliceNode G fhat (canonicalThreshold fhat)) :
    (continuumReebGraph M f).Carrier :=
  continuumReebQuotientMap f
    (sample (canonicalNodeSupportWitness G fhat x))

/-- Adjacent canonical nodes have path-connected images in the continuum Reeb
quotient.  The path is built through their shared support witness. -/
theorem ApproximationHypotheses.canonicalNodeContinuumMap_adj_joined
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : SliceNode G fhat (canonicalThreshold fhat)}
    (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) :
    Nonempty (Path (h.canonicalNodeContinuumMap x)
      (h.canonicalNodeContinuumMap y)) := by
  change DiscreteReebAdj G fhat (canonicalThreshold fhat) x y at hxy
  rcases hxy.2 with ⟨w, hwx, hwy⟩
  have hxw := h.support_component_no_merge x.2
    (canonicalNodeSupportWitness_mem G fhat x) hwx
  have hwy' := h.support_component_no_merge y.2 hwy
    (canonicalNodeSupportWitness_mem G fhat y)
  exact ⟨(hxw.somePath.trans hwy'.somePath).map
    (continuous_continuumReebQuotientMap f)⟩

/-- Uniform height budget for the continuous support map on realization
edges. -/
def continuousForwardError (L r η q : ℝ) : ℝ :=
  4 * L * r + 9 * η + 9 * q

/-- The path between adjacent canonical-node images can be chosen uniformly
close to the linearly interpolated realization height. -/
theorem ApproximationHypotheses.canonicalNodeContinuumMap_adj_controlled
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : SliceNode G fhat (canonicalThreshold fhat)}
    (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) :
    ∃ γ : Path (h.canonicalNodeContinuumMap x)
        (h.canonicalNodeContinuumMap y),
      ∀ s : GraphUnitInterval,
        |(1 - s.1) * canonicalThreshold fhat x.1 +
          s.1 * canonicalThreshold fhat y.1 -
          (continuumReebGraph M f).height (γ s)| ≤
        continuousForwardError L r η q := by
  change DiscreteReebAdj G fhat (canonicalThreshold fhat) x y at hxy
  rcases hxy.2 with ⟨w, hwx, hwy⟩
  let ux := canonicalNodeSupportWitness G fhat x
  let uy := canonicalNodeSupportWitness G fhat y
  let tx := canonicalThreshold fhat x.1
  let ty := canonicalThreshold fhat y.1
  let B := L * r + 3 * η + 3 * q
  let A := B + L * r
  have hxw := h.support_component_no_merge x.2
    (canonicalNodeSupportWitness_mem G fhat x) hwx
  have hwy' := h.support_component_no_merge y.2 hwy
    (canonicalNodeSupportWitness_mem G fhat y)
  have hwxB := h.support_component_sound x.2 hwx
  have hwyB := h.support_component_sound y.2 hwy
  change |f (sample w) - tx| ≤ B at hwxB
  change |f (sample w) - ty| ≤ B at hwyB
  have hgap : |tx - ty| ≤ 2 * B := by
    calc
      |tx - ty| = |(tx - f (sample w)) + (f (sample w) - ty)| := by ring_nf
      _ ≤ |tx - f (sample w)| + |f (sample w) - ty| := abs_add _ _
      _ ≤ B + B := add_le_add (by simpa only [abs_sub_comm] using hwxB) hwyB
      _ = 2 * B := by ring
  let γM := hxw.somePath.trans hwy'.somePath
  let γ := γM.map (continuous_continuumReebQuotientMap f)
  refine ⟨γ, ?_⟩
  intro s
  change |(1 - s.1) * tx + s.1 * ty - f (γM s)| ≤
    continuousForwardError L r η q
  have hleft : |(1 - s.1) * tx + s.1 * ty - tx| ≤ |tx - ty| := by
    apply abs_affine_sub_le s.2.1 s.2.2
    · simp
    · simp only [abs_sub_comm, le_refl]
  have hright : |(1 - s.1) * tx + s.1 * ty - ty| ≤ |tx - ty| := by
    apply abs_affine_sub_le s.2.1 s.2.2
    · exact le_rfl
    · simp
  have hsRange : γM s ∈ Set.range hxw.somePath ∪ Set.range hwy'.somePath := by
    rw [← hxw.somePath.trans_range hwy'.somePath]
    exact ⟨s, rfl⟩
  rcases hsRange with hsx | hsy
  · rcases hsx with ⟨t, ht⟩
    have htBand := hxw.somePath_mem t
    change |f (hxw.somePath t) - tx| ≤ A at htBand
    have hcenter : |tx - f (γM s)| ≤ A := by
      rw [← ht]
      simpa only [abs_sub_comm] using htBand
    calc
      |(1 - s.1) * tx + s.1 * ty - f (γM s)| =
          |((1 - s.1) * tx + s.1 * ty - tx) + (tx - f (γM s))| := by
        ring_nf
      _ ≤ |(1 - s.1) * tx + s.1 * ty - tx| + |tx - f (γM s)| :=
        abs_add _ _
      _ ≤ |tx - ty| + A := add_le_add hleft hcenter
      _ ≤ 2 * B + A := add_le_add_right hgap A
      _ = continuousForwardError L r η q := by
        unfold continuousForwardError A B
        ring
  · rcases hsy with ⟨t, ht⟩
    have htBand := hwy'.somePath_mem t
    change |f (hwy'.somePath t) - ty| ≤ A at htBand
    have hcenter : |ty - f (γM s)| ≤ A := by
      rw [← ht]
      simpa only [abs_sub_comm] using htBand
    calc
      |(1 - s.1) * tx + s.1 * ty - f (γM s)| =
          |((1 - s.1) * tx + s.1 * ty - ty) + (ty - f (γM s))| := by
        ring_nf
      _ ≤ |(1 - s.1) * tx + s.1 * ty - ty| + |ty - f (γM s)| :=
        abs_add _ _
      _ ≤ |tx - ty| + A := add_le_add hright hcenter
      _ ≤ 2 * B + A := add_le_add_right hgap A
      _ = continuousForwardError L r η q := by
        unfold continuousForwardError A B
        ring

/-- Controlled adjacent-node paths packaged for the coherent realization-map
constructor. -/
theorem ApproximationHypotheses.canonicalNodeContinuumMap_adj_controlledPath
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : SliceNode G fhat (canonicalThreshold fhat)}
    (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) :
    Nonempty (HeightControlledAdjacentPath
      (fun z : SliceNode G fhat (canonicalThreshold fhat) ↦
        canonicalThreshold fhat z.1)
      (continuumReebGraph M f) (continuousForwardError L r η q)
      h.canonicalNodeContinuumMap x y) := by
  rcases h.canonicalNodeContinuumMap_adj_controlled hxy with ⟨γ, hγ⟩
  exact ⟨⟨γ, hγ⟩⟩

/-- The coherent continuous support map, now retaining its uniform filtered
height estimate on the entire graph realization. -/
noncomputable def ApproximationHypotheses.filteredContinuousDiscreteToContinuumData
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    FilteredGraphRealizationMapData (canonicalDiscreteReebGraph G fhat)
      (fun z : SliceNode G fhat (canonicalThreshold fhat) ↦
        canonicalThreshold fhat z.1)
      (continuumReebGraph M f) (continuousForwardError L r η q) := by
  letI : LinearOrder (SliceNode G fhat (canonicalThreshold fhat)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let hedge := fun {x y : SliceNode G fhat (canonicalThreshold fhat)}
      (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) ↦
    h.canonicalNodeContinuumMap_adj_controlledPath hxy
  let graphData : GraphRealizationMapData (canonicalDiscreteReebGraph G fhat)
      (continuumReebGraph M f).Carrier :=
    { vertexMap := h.canonicalNodeContinuumMap
      edgePath := coherentHeightControlledEdgePath
        h.canonicalNodeContinuumMap hedge
      reverse_compatible := coherentHeightControlledEdgePath_reverse
        h.canonicalNodeContinuumMap hedge }
  refine
    { toGraphRealizationMapData := graphData
      vertex_height_close := ?_
      edge_height_close := ?_ }
  · intro x
    have hs := h.support_component_sound x.2
      (canonicalNodeSupportWitness_mem G fhat x)
    change |f (sample (canonicalNodeSupportWitness G fhat x)) -
      canonicalThreshold fhat x.1| ≤ L * r + 3 * η + 3 * q at hs
    change |canonicalThreshold fhat x.1 -
      f (sample (canonicalNodeSupportWitness G fhat x))| ≤
      continuousForwardError L r η q
    have hLr : 0 ≤ L * r :=
      mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
    have hbudget : L * r + 3 * η + 3 * q ≤
      continuousForwardError L r η q := by
      unfold continuousForwardError
      linarith [h.filter_error_nonneg, h.quantization_error_nonneg]
    have hs' : |canonicalThreshold fhat x.1 -
        f (sample (canonicalNodeSupportWitness G fhat x))| ≤
        L * r + 3 * η + 3 * q := by
      simpa only [abs_sub_comm] using hs
    exact hs'.trans hbudget
  · intro edge s
    exact coherentHeightControlledEdgePath_height_close
      h.canonicalNodeContinuumMap hedge edge s

/-- Continuous support map from the canonical discrete graph realization to
the continuum Reeb quotient. -/
noncomputable def ApproximationHypotheses.continuousDiscreteToContinuumData
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    GraphRealizationMapData (canonicalDiscreteReebGraph G fhat)
      (ContinuumReebQuotient M f) :=
  h.filteredContinuousDiscreteToContinuumData.toGraphRealizationMapData

noncomputable def ApproximationHypotheses.continuousDiscreteToContinuumMap
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    (discreteReebRealization V G fhat).Carrier →
      (continuumReebGraph M f).Carrier :=
  h.continuousDiscreteToContinuumData.realizationMap

@[simp] theorem ApproximationHypotheses.continuousDiscreteToContinuumMap_vertex
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (x : SliceNode G fhat (canonicalThreshold fhat)) :
    h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x) =
      h.canonicalNodeContinuumMap x :=
  rfl

theorem ApproximationHypotheses.continuous_continuousDiscreteToContinuumMap
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    Continuous h.continuousDiscreteToContinuumMap :=
  h.continuousDiscreteToContinuumData.continuous_realizationMap

/-- Global height control for the continuous support map. -/
theorem ApproximationHypotheses.continuousDiscreteToContinuumMap_height_close
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : (discreteReebRealization V G fhat).Carrier) :
    |(discreteReebRealization V G fhat).height z -
      (continuumReebGraph M f).height
        (h.continuousDiscreteToContinuumMap z)| ≤
      continuousForwardError L r η q :=
  h.filteredContinuousDiscreteToContinuumData.height_close z

theorem ApproximationHypotheses.continuousForwardError_nonneg
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ continuousForwardError L r η q := by
  unfold continuousForwardError
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  linarith [h.filter_error_nonneg, h.quantization_error_nonneg]

/-- Forward scalar-band preservation is a theorem of the support-induced CW
construction, not an additional compatibility assumption. -/
theorem ApproximationHypotheses.continuousDiscreteToContinuumMap_band
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x x' : (discreteReebRealization V G fhat).Carrier}
    (hxx' : HeightBandJoined (discreteReebRealization V G fhat) a b x x') :
    HeightBandJoined (continuumReebGraph M f)
      (a - continuousForwardError L r η q)
      (b + continuousForwardError L r η q)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap x') :=
  hxx'.map_of_continuous_height_close
    h.continuous_continuousDiscreteToContinuumMap
    h.continuousDiscreteToContinuumMap_height_close

/-- Common error budget for the continuous forward support map and the
canonical reverse crossing map. -/
def continuousCanonicalComparisonError (L r δ η q : ℝ) : ℝ :=
  max (approximationComparisonError L r δ η q + L * δ)
    (continuousForwardError L r η q)

theorem ApproximationHypotheses.continuousCanonicalComparisonError_nonneg
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) :
    0 ≤ continuousCanonicalComparisonError L r δ η q := by
  have hLδ : 0 ≤ L * δ :=
    mul_nonneg h.lipschitz_constant_nonneg h.sampling_scale_nonneg
  exact (add_nonneg h.comparison_error_nonneg hLδ).trans
    (le_max_left _ (continuousForwardError L r η q))

/-- Reverse transition completeness stated at the common budget used by the
continuous forward map. -/
def ContinuousCanonicalManifoldBandTransitionComplete
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {p p' : M}, a ≤ b →
    JoinedIn {z | a ≤ f z ∧ f z ≤ b} p p' →
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - continuousCanonicalComparisonError L r δ η q)
      (b + continuousCanonicalComparisonError L r δ η q)
      (h.continuumToDiscreteMap (continuumReebQuotientMap f p))
      (h.continuumToDiscreteMap (continuumReebQuotientMap f p'))

/-- The continuum round trip for the continuous forward support map is
realized by a controlled path before passing to the Reeb quotient. -/
def ContinuousCanonicalContinuumRoundtripRealizable
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ y : (continuumReebGraph M f).Carrier,
    ∃ p p' : M,
      continuumReebQuotientMap f p = y ∧
      continuumReebQuotientMap f p' =
        h.continuousDiscreteToContinuumMap (h.continuumToDiscreteMap y) ∧
      JoinedIn {z |
        (discreteReebRealization V G fhat).height
            (h.continuumToDiscreteMap y) -
            continuousCanonicalComparisonError L r δ η q ≤ f z ∧
        f z ≤ (discreteReebRealization V G fhat).height
            (h.continuumToDiscreteMap y) +
            continuousCanonicalComparisonError L r δ η q} p p'

/-- Local geodesic accessibility discharges the continuum round-trip
condition.  The first path segment reaches the nearby canonical active sample;
the second follows the support component to the representative used by the
continuous realization map. -/
theorem ApproximationHypotheses.continuousContinuumRoundtrip_of_shortPathSound
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hshort : ShortPathSound M δ) :
    ContinuousCanonicalContinuumRoundtripRealizable h := by
  intro y
  let x : M := Quotient.out y
  let w := h.canonicalPointWitness x
  let node : SliceNode G fhat (canonicalThreshold fhat) :=
    ⟨w.index, componentOfActive G fhat (canonicalThreshold fhat w.index)
      ⟨w.vertex, w.active⟩⟩
  let u := canonicalNodeSupportWitness G fhat node
  have hxy : continuumReebQuotientMap f x = y := Quotient.out_eq y
  have hxw : dist x (sample w.vertex) ≤ δ := by
    simpa only [dist_comm] using w.spatial_close
  rcases hshort hxw with ⟨γnear, hγnear⟩
  have hwSupport : w.vertex ∈
      componentSupport G fhat (canonicalThreshold fhat node.1) node.2 := by
    exact mem_componentSupport_componentOfActive G fhat
      (canonicalThreshold fhat w.index) ⟨w.vertex, w.active⟩
  have huSupport : u ∈
      componentSupport G fhat (canonicalThreshold fhat node.1) node.2 :=
    canonicalNodeSupportWitness_mem G fhat node
  have hsupport := h.support_component_no_merge node.2 hwSupport huSupport
  let γ := γnear.trans hsupport.somePath
  refine ⟨x, sample u, hxy, ?_, ⟨γ, ?_⟩⟩
  · change continuumReebQuotientMap f (sample u) =
      h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) node)
    rw [h.continuousDiscreteToContinuumMap_vertex]
    rfl
  · intro s
    change canonicalThreshold fhat node.1 -
        continuousCanonicalComparisonError L r δ η q ≤ f (γ s) ∧
      f (γ s) ≤ canonicalThreshold fhat node.1 +
        continuousCanonicalComparisonError L r δ η q
    have hsRange : γ s ∈
        Set.range γnear ∪ Set.range hsupport.somePath := by
      rw [← γnear.trans_range hsupport.somePath]
      exact ⟨s, rfl⟩
    have habs : |f (γ s) - canonicalThreshold fhat node.1| ≤
        continuousCanonicalComparisonError L r δ η q := by
      rcases hsRange with hs | hs
      · rcases hs with ⟨t, ht⟩
        have hLip : |f (γnear t) - f x| ≤ L * δ :=
          (h.lipschitz (γnear t) x).trans
            (mul_le_mul_of_nonneg_left (hγnear t)
              h.lipschitz_constant_nonneg)
        have hwHeight : |f x - canonicalThreshold fhat node.1| ≤
            approximationComparisonError L r δ η q := by
          simpa only [abs_sub_comm] using w.height_close
        rw [← ht]
        calc
          |f (γnear t) - canonicalThreshold fhat node.1| =
              |(f (γnear t) - f x) +
                (f x - canonicalThreshold fhat node.1)| := by ring_nf
          _ ≤ |f (γnear t) - f x| +
              |f x - canonicalThreshold fhat node.1| := abs_add _ _
          _ ≤ L * δ + approximationComparisonError L r δ η q :=
            add_le_add hLip hwHeight
          _ = approximationComparisonError L r δ η q + L * δ :=
            add_comm _ _
          _ ≤ continuousCanonicalComparisonError L r δ η q := by
            exact le_max_left _ _
      · rcases hs with ⟨t, ht⟩
        have htBand := hsupport.somePath_mem t
        have hLr : 0 ≤ L * r :=
          mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
        have hsmall : (L * r + 3 * η + 3 * q) + L * r ≤
            continuousForwardError L r η q := by
          unfold continuousForwardError
          linarith [h.filter_error_nonneg, h.quantization_error_nonneg]
        rw [← ht]
        exact htBand.trans (hsmall.trans (le_max_right _ _))
    rw [abs_sub_le_iff] at habs
    constructor <;> linarith [habs.1, habs.2]

/-- Projected form of the continuum round trip supplied by local short paths. -/
theorem ApproximationHypotheses.continuousContinuumRoundtrip_band_of_shortPathSound
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hshort : ShortPathSound M δ)
    (y : (continuumReebGraph M f).Carrier) :
    HeightBandJoined (continuumReebGraph M f)
      ((discreteReebRealization V G fhat).height
          (h.continuumToDiscreteMap y) -
        continuousCanonicalComparisonError L r δ η q)
      ((discreteReebRealization V G fhat).height
          (h.continuumToDiscreteMap y) +
        continuousCanonicalComparisonError L r δ η q)
      y (h.continuousDiscreteToContinuumMap (h.continuumToDiscreteMap y)) := by
  rcases h.continuousContinuumRoundtrip_of_shortPathSound hshort y with
    ⟨p, p', hp, hp', hpath⟩
  have hprojected := joinedIn_continuumReebQuotientMap hpath
  rw [hp, hp'] at hprojected
  exact hprojected

/-- The single estimator-specific reverse statement needed by the reduced
continuous comparison: band paths whose endpoints lie in the image of the
support map reflect to the discrete realization with one error enlargement. -/
def ContinuousCanonicalImageBandReflection
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ}
    {x x' : (discreteReebRealization V G fhat).Carrier},
    a ≤ b →
    HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap x') →
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - continuousCanonicalComparisonError L r δ η q)
      (b + continuousCanonicalComparisonError L r δ η q) x x'

/-- Non-circular finite target for the remaining geometry.  A continuum band
path between images of canonical component nodes must lift to a horizontal /
vertical active-witness walk whose slice heights remain in the expanded band. -/
def CanonicalNodeIncidenceBandCoverageAt
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (e : ℝ) : Prop :=
  ∀ {a b : ℝ} {x y : SliceNode G fhat (canonicalThreshold fhat)},
    a ≤ b →
    HeightBandJoined (continuumReebGraph M f) a b
      (h.canonicalNodeContinuumMap x) (h.canonicalNodeContinuumMap y) →
    ∃ u v : CanonicalActiveState G fhat,
      ∃ p : (canonicalActiveIncidenceGraph G fhat).Walk u v,
        canonicalActiveStateNode G fhat u = x ∧
        canonicalActiveStateNode G fhat v = y ∧
        ∀ z, z ∈ p.support →
          a - e ≤ canonicalThreshold fhat z.1 ∧
          canonicalThreshold fhat z.1 ≤ b + e

/-- The original incidence interface uses one common comparison-error unit. -/
def CanonicalNodeIncidenceBandCoverage
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  CanonicalNodeIncidenceBandCoverageAt h
    (continuousCanonicalComparisonError L r δ η q)

/-- Reeb-band paths between canonical node images lift to manifold paths
between the exact sample representatives selected for those nodes. -/
def CanonicalNodeManifoldBandPathLift
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {x y : SliceNode G fhat (canonicalThreshold fhat)},
    HeightBandJoined (continuumReebGraph M f) a b
      (h.canonicalNodeContinuumMap x) (h.canonicalNodeContinuumMap y) →
    JoinedIn {z | a ≤ f z ∧ f z ≤ b}
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat y))

/-- Node-specific manifold lifting with an explicit scalar enlargement. -/
def CanonicalNodeManifoldBandPathLiftWithSlack
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {x y : SliceNode G fhat (canonicalThreshold fhat)},
    HeightBandJoined (continuumReebGraph M f) a b
      (h.canonicalNodeContinuumMap x) (h.canonicalNodeContinuumMap y) →
    JoinedIn {z | a - s ≤ f z ∧ f z ≤ b + s}
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat y))

/-- A slackened quotient lift attaches to the canonical node representatives
through exact level components, without consuming additional slack. -/
theorem ApproximationHypotheses.canonicalNodeManifoldBandPathLift_of_reebLiftWithSlack
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hs : 0 ≤ s) (hlift : ContinuumReebBandPathLiftWithSlack M f s) :
    CanonicalNodeManifoldBandPathLiftWithSlack (s := s) h := by
  intro a b x y hxy
  rcases hlift hxy with ⟨p, p', hp, hp', hmiddle⟩
  let sx := sample (canonicalNodeSupportWitness G fhat x)
  let sy := sample (canonicalNodeSupportWitness G fhat y)
  have hqLeft : continuumReebQuotientMap f sx =
      continuumReebQuotientMap f p := by
    change h.canonicalNodeContinuumMap x = continuumReebQuotientMap f p
    exact hp.symm
  have hqRight : continuumReebQuotientMap f p' =
      continuumReebQuotientMap f sy := by
    change continuumReebQuotientMap f p' = h.canonicalNodeContinuumMap y
    exact hp'
  have hleftLevel := h.tame_filter.joinedIn_of_sameLevelComponent
    ((continuumReebQuotientMap_eq_iff f sx p).mp hqLeft)
  have hrightLevel := h.tame_filter.joinedIn_of_sameLevelComponent
    ((continuumReebQuotientMap_eq_iff f p' sy).mp hqRight)
  have hsxBand : a - s ≤ f sx ∧ f sx ≤ b + s := by
    have hsx := hxy.source_mem
    change a ≤ f sx ∧ f sx ≤ b at hsx
    constructor <;> linarith [hsx.1, hsx.2]
  have hp'Band : a - s ≤ f p' ∧ f p' ≤ b + s := hmiddle.target_mem
  have hleft : JoinedIn {z | a - s ≤ f z ∧ f z ≤ b + s} sx p := by
    apply JoinedIn.mono hleftLevel
    intro z hz
    change f z = f sx at hz
    change a - s ≤ f z ∧ f z ≤ b + s
    rw [hz]
    exact hsxBand
  have hright : JoinedIn {z | a - s ≤ f z ∧ f z ≤ b + s} p' sy := by
    apply JoinedIn.mono hrightLevel
    intro z hz
    change f z = f p' at hz
    change a - s ≤ f z ∧ f z ≤ b + s
    rw [hz]
    exact hp'Band
  exact hleft.trans (hmiddle.trans hright)

/-- The usual Reeb quotient path-lifting property, together with tame level
fibers, supplies the node-specific manifold lift.  The short endpoint paths
remain in exact level sets and hence introduce no scalar enlargement. -/
theorem ApproximationHypotheses.canonicalNodeManifoldBandPathLift_of_reebLift
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hlift : ContinuumReebBandPathLift M f) :
    CanonicalNodeManifoldBandPathLift h := by
  intro a b x y hxy
  rcases hlift hxy with ⟨p, p', hp, hp', hmiddle⟩
  let sx := sample (canonicalNodeSupportWitness G fhat x)
  let sy := sample (canonicalNodeSupportWitness G fhat y)
  have hqLeft : continuumReebQuotientMap f sx =
      continuumReebQuotientMap f p := by
    change h.canonicalNodeContinuumMap x = continuumReebQuotientMap f p
    exact hp.symm
  have hqRight : continuumReebQuotientMap f p' =
      continuumReebQuotientMap f sy := by
    change continuumReebQuotientMap f p' = h.canonicalNodeContinuumMap y
    exact hp'
  have hleftLevel := h.tame_filter.joinedIn_of_sameLevelComponent
    ((continuumReebQuotientMap_eq_iff f sx p).mp hqLeft)
  have hrightLevel := h.tame_filter.joinedIn_of_sameLevelComponent
    ((continuumReebQuotientMap_eq_iff f p' sy).mp hqRight)
  have hsxBand : a ≤ f sx ∧ f sx ≤ b := by
    simpa only [sx, ApproximationHypotheses.canonicalNodeContinuumMap,
      continuumReebGraph_height_quotientMap] using hxy.source_mem
  have hp'Band : a ≤ f p' ∧ f p' ≤ b := hmiddle.target_mem
  have hleft : JoinedIn {z | a ≤ f z ∧ f z ≤ b} sx p := by
    apply JoinedIn.mono hleftLevel
    intro z hz
    change f z = f sx at hz
    change a ≤ f z ∧ f z ≤ b
    rw [hz]
    exact hsxBand
  have hright : JoinedIn {z | a ≤ f z ∧ f z ≤ b} p' sy := by
    apply JoinedIn.mono hrightLevel
    intro z hz
    change f z = f p' at hz
    change a ≤ f z ∧ f z ≤ b
    rw [hz]
    exact hp'Band
  exact hleft.trans (hmiddle.trans hright)

/-- Purely finite slab condition on the neighborhood graph.  A band-limited
ordinary graph walk between chosen component representatives must canonicalize
to a bounded walk in the active-incidence graph.  This mentions neither the
algorithm's quotient connectivity nor the continuum Reeb graph. -/
def CanonicalSlabWalkIncidenceComplete
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q) : Prop :=
  ∀ {a b : ℝ} {x y : SliceNode G fhat (canonicalThreshold fhat)},
    a ≤ b →
    ∀ p : G.Walk (canonicalNodeSupportWitness G fhat x)
        (canonicalNodeSupportWitness G fhat y),
      (∀ w, w ∈ p.support →
        |fhat w - (a + b) / 2| ≤
          (b - a) / 2 + L * (r + δ) + η + q) →
      ∃ u v : CanonicalActiveState G fhat,
        ∃ qwalk : (canonicalActiveIncidenceGraph G fhat).Walk u v,
          canonicalActiveStateNode G fhat u = x ∧
          canonicalActiveStateNode G fhat v = y ∧
          ∀ z, z ∈ qwalk.support →
            a - continuousCanonicalComparisonError L r δ η q ≤
              canonicalThreshold fhat z.1 ∧
            canonicalThreshold fhat z.1 ≤
              b + continuousCanonicalComparisonError L r δ η q

/-- For a non-flat observed scalar on graph edges, slab canonicalization is a
theorem.  The graph-walk scalar slack plus one observed edge oscillation is
exactly the older comparison budget, so the existing common error suffices. -/
theorem ApproximationHypotheses.canonicalSlabWalkIncidenceComplete_of_nonflat
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hnonflat : GraphEdgeNonflat G fhat) :
    CanonicalSlabWalkIncidenceComplete h := by
  intro a b x y hab p hp
  let S := L * (r + δ) + η + q
  let D := L * r + 2 * η + 2 * q
  let E := continuousCanonicalComparisonError L r δ η q
  have hLr : 0 ≤ L * r :=
    mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
  have hLδ : 0 ≤ L * δ :=
    mul_nonneg h.lipschitz_constant_nonneg h.sampling_scale_nonneg
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith [h.filter_error_nonneg, h.quantization_error_nonneg]
  have hbudget : S + D ≤ E := by
    calc
      S + D = approximationComparisonError L r δ η q := by
        simp only [S, D, approximationComparisonError]
        ring
      _ ≤ approximationComparisonError L r δ η q + L * δ :=
        le_add_of_nonneg_right hLδ
      _ ≤ E := by
        exact le_max_left _ _
  have hSle : S ≤ E := by linarith
  have hpTight : ∀ w, w ∈ p.support →
      a - S ≤ fhat w ∧ fhat w ≤ b + S := by
    intro w hw
    have hwBand := hp w hw
    rw [abs_sub_le_iff] at hwBand
    dsimp [S]
    constructor <;> linarith [hwBand.1, hwBand.2]
  have hpWide : ∀ w, w ∈ p.support →
      a - E ≤ fhat w ∧ fhat w ≤ b + E := by
    intro w hw
    have hwTight := hpTight w hw
    constructor <;> linarith
  let ux := canonicalNodeSupportWitness G fhat x
  let uy := canonicalNodeSupportWitness G fhat y
  have huxSupport : ux ∈
      componentSupport G fhat (canonicalThreshold fhat x.1) x.2 :=
    canonicalNodeSupportWitness_mem G fhat x
  have huySupport : uy ∈
      componentSupport G fhat (canonicalThreshold fhat y.1) y.2 :=
    canonicalNodeSupportWitness_mem G fhat y
  have huxActive : IsActiveVertex G fhat (canonicalThreshold fhat x.1) ux :=
    componentSupport_isActive G fhat (canonicalThreshold fhat x.1) x.2 huxSupport
  have huyActive : IsActiveVertex G fhat (canonicalThreshold fhat y.1) uy :=
    componentSupport_isActive G fhat (canonicalThreshold fhat y.1) y.2 huySupport
  have huxValue := hpTight ux p.start_mem_support
  have huyValue := hpTight uy p.end_mem_support
  have huxClose := h.canonicalActive_threshold_close_observed huxActive
  have huyClose := h.canonicalActive_threshold_close_observed huyActive
  change |canonicalThreshold fhat x.1 - fhat ux| ≤ D at huxClose
  change |canonicalThreshold fhat y.1 - fhat uy| ≤ D at huyClose
  rw [abs_sub_le_iff] at huxClose huyClose
  have hxBand : a - E ≤ canonicalThreshold fhat x.1 ∧
      canonicalThreshold fhat x.1 ≤ b + E := by
    constructor <;>
      linarith [huxValue.1, huxValue.2, huxClose.1, huxClose.2, hbudget]
  have hyBand : a - E ≤ canonicalThreshold fhat y.1 ∧
      canonicalThreshold fhat y.1 ≤ b + E := by
    constructor <;>
      linarith [huyValue.1, huyValue.2, huyClose.1, huyClose.2, hbudget]
  let ustate : CanonicalActiveState G fhat := ⟨x.1, ⟨ux, huxActive⟩⟩
  let ystate : CanonicalActiveState G fhat := ⟨y.1, ⟨uy, huyActive⟩⟩
  have huxComponent : componentOfActive G fhat
      (canonicalThreshold fhat x.1) ⟨ux, huxActive⟩ = x.2 := by
    apply crossingComponent_eq_of_support_intersects G fhat
      (canonicalThreshold fhat x.1)
    exact ⟨ux, mem_componentSupport_componentOfActive G fhat
      (canonicalThreshold fhat x.1) ⟨ux, huxActive⟩, huxSupport⟩
  have huyComponent : componentOfActive G fhat
      (canonicalThreshold fhat y.1) ⟨uy, huyActive⟩ = y.2 := by
    apply crossingComponent_eq_of_support_intersects G fhat
      (canonicalThreshold fhat y.1)
    exact ⟨uy, mem_componentSupport_componentOfActive G fhat
      (canonicalThreshold fhat y.1) ⟨uy, huyActive⟩, huySupport⟩
  have huNode : canonicalActiveStateNode G fhat ustate = x := by
    unfold canonicalActiveStateNode ustate
    exact Sigma.ext rfl (heq_of_eq huxComponent)
  have hyNode : canonicalActiveStateNode G fhat ystate = y := by
    unfold canonicalActiveStateNode ystate
    exact Sigma.ext rfl (heq_of_eq huyComponent)
  have hlift := canonicalActiveIncidence_reachableWithin_of_walk_of_nonflat
    G fhat hnonflat p hpWide huxActive huyActive hxBand hyBand
  rcases hlift with ⟨qwalk, hqwalk⟩
  exact ⟨ustate, ystate, qwalk, huNode, hyNode, by
    intro z hz
    simpa only [E] using hqwalk z hz⟩

/-- Manifold band lifting, graph completeness, and finite slab
canonicalization imply the exact active-incidence coverage used by the main
deterministic theorem. -/
theorem ApproximationHypotheses.canonicalNodeIncidenceBandCoverage_of_slabWalk
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hlift : CanonicalNodeManifoldBandPathLift h)
    (hslab : CanonicalSlabWalkIncidenceComplete h) :
    CanonicalNodeIncidenceBandCoverage h := by
  intro a b x y hab hxy
  have hmanifold := hlift hxy
  have habs : JoinedIn
      {z | |f z - (a + b) / 2| ≤ (b - a) / 2}
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat y)) := by
    apply JoinedIn.mono hmanifold
    intro z hz
    change a ≤ f z ∧ f z ≤ b at hz
    change |f z - (a + b) / 2| ≤ (b - a) / 2
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hstart : dist
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat x)) ≤ δ := by
    simpa using h.sampling_scale_nonneg
  have hend : dist
      (sample (canonicalNodeSupportWitness G fhat y))
      (sample (canonicalNodeSupportWitness G fhat y)) ≤ δ := by
    simpa using h.sampling_scale_nonneg
  rcases h.lift_joinedIn_band habs hstart hend with ⟨p, hp⟩
  exact hslab hab p hp

/-- Slackened manifold lifting produces incidence coverage with exactly one
additional slack unit.  All graph-completeness and canonicalization estimates
are unchanged. -/
theorem ApproximationHypotheses.canonicalNodeIncidenceBandCoverageAt_of_slabWalk
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hs : 0 ≤ s)
    (hlift : CanonicalNodeManifoldBandPathLiftWithSlack (s := s) h)
    (hslab : CanonicalSlabWalkIncidenceComplete h) :
    CanonicalNodeIncidenceBandCoverageAt h
      (continuousCanonicalComparisonError L r δ η q + s) := by
  intro a b x y hab hxy
  have hmanifold := hlift hxy
  have habExpanded : a - s ≤ b + s := by linarith
  have habs : JoinedIn
      {z | |f z - ((a - s) + (b + s)) / 2| ≤
        ((b + s) - (a - s)) / 2}
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat y)) := by
    apply JoinedIn.mono hmanifold
    intro z hz
    change a - s ≤ f z ∧ f z ≤ b + s at hz
    change |f z - ((a - s) + (b + s)) / 2| ≤
      ((b + s) - (a - s)) / 2
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hstart : dist
      (sample (canonicalNodeSupportWitness G fhat x))
      (sample (canonicalNodeSupportWitness G fhat x)) ≤ δ := by
    simpa using h.sampling_scale_nonneg
  have hend : dist
      (sample (canonicalNodeSupportWitness G fhat y))
      (sample (canonicalNodeSupportWitness G fhat y)) ≤ δ := by
    simpa using h.sampling_scale_nonneg
  rcases h.lift_joinedIn_band habs hstart hend with ⟨p, hp⟩
  rcases hslab habExpanded p hp with ⟨u, v, qwalk, hu, hv, hqwalk⟩
  refine ⟨u, v, qwalk, hu, hv, ?_⟩
  intro z hz
  have hzBand := hqwalk z hz
  constructor <;> linarith [hzBand.1, hzBand.2]

/-- For every positive slack, tame level fibers and local path-connectedness
discharge continuum quotient lifting; nonflat edges discharge the remaining
finite incidence condition. -/
theorem ApproximationHypotheses.canonicalNodeIncidenceBandCoverageAt_of_tame_of_nonflat
    {M : Type} [PseudoMetricSpace M] [LocPathConnectedSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q s : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hs : 0 < s) (hnonflat : GraphEdgeNonflat G fhat) :
    CanonicalNodeIncidenceBandCoverageAt h
      (continuousCanonicalComparisonError L r δ η q + s) :=
  h.canonicalNodeIncidenceBandCoverageAt_of_slabWalk hs.le
    (h.canonicalNodeManifoldBandPathLift_of_reebLiftWithSlack hs.le
      (continuumReebBandPathLiftWithSlack_of_tame M f h.tame_filter hs))
    (h.canonicalSlabWalkIncidenceComplete_of_nonflat hnonflat)

/-- Main discharge of the incidence condition: continuum Reeb path lifting
and non-flat observed graph edges imply bounded active-incidence coverage. -/
theorem ApproximationHypotheses.canonicalNodeIncidenceBandCoverage_of_reebLift_of_nonflat
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hlift : ContinuumReebBandPathLift M f)
    (hnonflat : GraphEdgeNonflat G fhat) :
    CanonicalNodeIncidenceBandCoverage h :=
  h.canonicalNodeIncidenceBandCoverage_of_slabWalk
    (h.canonicalNodeManifoldBandPathLift_of_reebLift hlift)
    (h.canonicalSlabWalkIncidenceComplete_of_nonflat hnonflat)

/-- Adjacent canonical slice heights differ by at most the common comparison
error.  Thus anchoring a CW interior point introduces no new scale. -/
theorem ApproximationHypotheses.canonicalAdjacentThreshold_gap_common
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    {x y : SliceNode G fhat (canonicalThreshold fhat)}
    (hxy : (canonicalDiscreteReebGraph G fhat).Adj x y) :
    |canonicalThreshold fhat x.1 - canonicalThreshold fhat y.1| ≤
      continuousCanonicalComparisonError L r δ η q := by
  change DiscreteReebAdj G fhat (canonicalThreshold fhat) x y at hxy
  rcases hxy.2 with ⟨w, hwx, hwy⟩
  have hwx' := h.support_component_sound x.2 hwx
  have hwy' := h.support_component_sound y.2 hwy
  have hgap :
      |canonicalThreshold fhat x.1 - canonicalThreshold fhat y.1| ≤
        2 * (L * r + 3 * η + 3 * q) := by
    calc
      |canonicalThreshold fhat x.1 - canonicalThreshold fhat y.1| =
          |(canonicalThreshold fhat x.1 - f (sample w)) +
            (f (sample w) - canonicalThreshold fhat y.1)| := by ring_nf
      _ ≤ |canonicalThreshold fhat x.1 - f (sample w)| +
          |f (sample w) - canonicalThreshold fhat y.1| := abs_add _ _
      _ ≤ (L * r + 3 * η + 3 * q) + (L * r + 3 * η + 3 * q) :=
        add_le_add (by simpa only [abs_sub_comm] using hwx') hwy'
      _ = 2 * (L * r + 3 * η + 3 * q) := by ring
  calc
    |canonicalThreshold fhat x.1 - canonicalThreshold fhat y.1| ≤
        2 * (L * r + 3 * η + 3 * q) := hgap
    _ ≤ continuousForwardError L r η q := by
      unfold continuousForwardError
      have hLr : 0 ≤ L * r :=
        mul_nonneg h.lipschitz_constant_nonneg h.edge_scale_nonneg
      linarith [h.filter_error_nonneg, h.quantization_error_nonneg]
    _ ≤ continuousCanonicalComparisonError L r δ η q :=
      le_max_right _ _

/-- Every point of the canonical CW realization anchors at a component node
inside one additional common-error enlargement. -/
theorem ApproximationHypotheses.point_to_canonicalNode_band
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (z : (discreteReebRealization V G fhat).Carrier)
    (hz : a ≤ (discreteReebRealization V G fhat).height z ∧
      (discreteReebRealization V G fhat).height z ≤ b) :
    ∃ node : SliceNode G fhat (canonicalThreshold fhat),
      HeightBandJoined (discreteReebRealization V G fhat)
        (a - continuousCanonicalComparisonError L r δ η q)
        (b + continuousCanonicalComparisonError L r δ η q)
        z (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) node) := by
  revert hz
  refine Quotient.inductionOn z ?_
  intro raw hz
  cases raw with
  | inl node =>
      refine ⟨node, JoinedIn.refl ?_⟩
      change a - continuousCanonicalComparisonError L r δ η q ≤
          canonicalThreshold fhat node.1 ∧
        canonicalThreshold fhat node.1 ≤
          b + continuousCanonicalComparisonError L r δ η q
      have he := h.continuousCanonicalComparisonError_nonneg
      change a ≤ canonicalThreshold fhat node.1 ∧
        canonicalThreshold fhat node.1 ≤ b at hz
      constructor <;> linarith [hz.1, hz.2]
  | inr edgePoint =>
      rcases edgePoint with ⟨edge, s⟩
      refine ⟨edge.source, ?_⟩
      exact joinedIn_graphRealization_edgePoint_to_source
        (fun node : SliceNode G fhat (canonicalThreshold fhat) ↦
          canonicalThreshold fhat node.1)
        h.continuousCanonicalComparisonError_nonneg edge
        (h.canonicalAdjacentThreshold_gap_common edge.2) s hz

/-- Incidence-band coverage implies image-band reflection on all canonical
graph vertices. -/
theorem ApproximationHypotheses.nodeImageBandReflection_of_incidenceCoverageAt
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b e : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcoverage : CanonicalNodeIncidenceBandCoverageAt h e)
    {x y : SliceNode G fhat (canonicalThreshold fhat)} (hab : a ≤ b)
    (hxy : HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x))
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) y))) :
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - e) (b + e)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) y) := by
  rw [h.continuousDiscreteToContinuumMap_vertex,
    h.continuousDiscreteToContinuumMap_vertex] at hxy
  rcases hcoverage hab hxy with ⟨u, v, p, hu, hv, hp⟩
  have hpath := heightBandJoined_of_canonicalActiveIncidence_walk
    G fhat p hp
  rw [hu, hv] at hpath
  exact hpath

theorem ApproximationHypotheses.nodeImageBandReflection_of_incidenceCoverage
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcoverage : CanonicalNodeIncidenceBandCoverage h)
    {x y : SliceNode G fhat (canonicalThreshold fhat)} (hab : a ≤ b)
    (hxy : HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x))
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) y))) :
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - continuousCanonicalComparisonError L r δ η q)
      (b + continuousCanonicalComparisonError L r δ η q)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) x)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) y) :=
  h.nodeImageBandReflection_of_incidenceCoverageAt hcoverage hab hxy

/-- Node incidence coverage reflects bands between arbitrary points of the
discrete CW realization.  Interior endpoints are anchored to source nodes;
the four error units account for endpoint height control, anchoring, mapping
the anchor paths forward, and node-level reflection. -/
theorem ApproximationHypotheses.imageBandReflection_three_add_of_incidenceCoverageAt
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b e : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (he : 0 ≤ e) (hcoverage : CanonicalNodeIncidenceBandCoverageAt h e)
    {x y : (discreteReebRealization V G fhat).Carrier}
    (hab : a ≤ b)
    (hxy : HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap y)) :
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - (3 * continuousCanonicalComparisonError L r δ η q + e))
      (b + (3 * continuousCanonicalComparisonError L r δ η q + e)) x y := by
  let E := continuousCanonicalComparisonError L r δ η q
  have hE : 0 ≤ E := h.continuousCanonicalComparisonError_nonneg
  have hxClose :
      |(discreteReebRealization V G fhat).height x -
        (continuumReebGraph M f).height
          (h.continuousDiscreteToContinuumMap x)| ≤ E := by
    exact (h.continuousDiscreteToContinuumMap_height_close x).trans
      (by simpa only [E] using
        (le_max_right
          (approximationComparisonError L r δ η q + L * δ)
          (continuousForwardError L r η q)))
  have hyClose :
      |(discreteReebRealization V G fhat).height y -
        (continuumReebGraph M f).height
          (h.continuousDiscreteToContinuumMap y)| ≤ E := by
    exact (h.continuousDiscreteToContinuumMap_height_close y).trans
      (by simpa only [E] using
        (le_max_right
          (approximationComparisonError L r δ η q + L * δ)
          (continuousForwardError L r η q)))
  rw [abs_sub_le_iff] at hxClose hyClose
  have hxMem : a - E ≤ (discreteReebRealization V G fhat).height x ∧
      (discreteReebRealization V G fhat).height x ≤ b + E := by
    constructor <;>
      linarith [hxy.source_mem.1, hxy.source_mem.2, hxClose.1, hxClose.2]
  have hyMem : a - E ≤ (discreteReebRealization V G fhat).height y ∧
      (discreteReebRealization V G fhat).height y ≤ b + E := by
    constructor <;>
      linarith [hxy.target_mem.1, hxy.target_mem.2, hyClose.1, hyClose.2]
  rcases h.point_to_canonicalNode_band x hxMem with ⟨xn, hxAnchor⟩
  rcases h.point_to_canonicalNode_band y hyMem with ⟨yn, hyAnchor⟩
  have hxAnchor' : HeightBandJoined (discreteReebRealization V G fhat)
      (a - 2 * E) (b + 2 * E) x
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn) := by
    convert hxAnchor using 1 <;> simp only [E] <;> ring
  have hyAnchor' : HeightBandJoined (discreteReebRealization V G fhat)
      (a - 2 * E) (b + 2 * E) y
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn) := by
    convert hyAnchor using 1 <;> simp only [E] <;> ring
  have hForwardLe : continuousForwardError L r η q ≤ E := by
    simpa only [E] using
      (le_max_right
        (approximationComparisonError L r δ η q + L * δ)
        (continuousForwardError L r η q))
  have hxImageRaw := h.continuousDiscreteToContinuumMap_band hxAnchor'
  have hyImageRaw := h.continuousDiscreteToContinuumMap_band hyAnchor'
  have hxImageBase : HeightBandJoined (continuumReebGraph M f)
      ((a - 2 * E) - E) ((b + 2 * E) + E)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn)) :=
    HeightBandJoined.mono hxImageRaw (by linarith) (by linarith)
  have hyImageBase : HeightBandJoined (continuumReebGraph M f)
      ((a - 2 * E) - E) ((b + 2 * E) + E)
      (h.continuousDiscreteToContinuumMap y)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn)) :=
    HeightBandJoined.mono hyImageRaw (by linarith) (by linarith)
  have hxImage : HeightBandJoined (continuumReebGraph M f)
      (a - 3 * E) (b + 3 * E)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn)) := by
    convert hxImageBase using 1 <;> simp only [E] <;> ring
  have hyImage : HeightBandJoined (continuumReebGraph M f)
      (a - 3 * E) (b + 3 * E)
      (h.continuousDiscreteToContinuumMap y)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn)) := by
    convert hyImageBase using 1 <;> simp only [E] <;> ring
  have hmiddle : HeightBandJoined (continuumReebGraph M f)
      (a - 3 * E) (b + 3 * E)
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap y) :=
    HeightBandJoined.mono hxy (by linarith) (by linarith)
  have hnodesImage : HeightBandJoined (continuumReebGraph M f)
      (a - 3 * E) (b + 3 * E)
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn))
      (h.continuousDiscreteToContinuumMap
        (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn)) :=
    hxImage.symm.trans (hmiddle.trans hyImage)
  have hnodesBase := h.nodeImageBandReflection_of_incidenceCoverageAt hcoverage
    (show a - 3 * E ≤ b + 3 * E by linarith) hnodesImage
  have hnodes : HeightBandJoined (discreteReebRealization V G fhat)
      (a - (3 * E + e)) (b + (3 * E + e))
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) xn)
      (graphRealizationVertex (canonicalDiscreteReebGraph G fhat) yn) := by
    convert hnodesBase using 1 <;> simp only [E] <;> ring
  have hxAnchorWide := HeightBandJoined.mono hxAnchor'
    (show a - (3 * E + e) ≤ a - 2 * E by linarith)
    (show b + 2 * E ≤ b + (3 * E + e) by linarith)
  have hyAnchorWide := HeightBandJoined.mono hyAnchor'
    (show a - (3 * E + e) ≤ a - 2 * E by linarith)
    (show b + 2 * E ≤ b + (3 * E + e) by linarith)
  change HeightBandJoined (discreteReebRealization V G fhat)
    (a - (3 * E + e)) (b + (3 * E + e)) x y
  exact hxAnchorWide.trans (hnodes.trans hyAnchorWide.symm)

/-- The one-error incidence interface gives the original four-error arbitrary
CW reflection estimate. -/
theorem ApproximationHypotheses.imageBandReflection_four_of_incidenceCoverage
    {M : Type} [PseudoMetricSpace M]
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {sample : V → M}
    {f : M → ℝ} {fbase fhat : V → ℝ} {L r δ η q a b : ℝ}
    (h : ApproximationHypotheses M V G sample f fbase fhat L r δ η q)
    (hcoverage : CanonicalNodeIncidenceBandCoverage h)
    {x y : (discreteReebRealization V G fhat).Carrier}
    (hab : a ≤ b)
    (hxy : HeightBandJoined (continuumReebGraph M f) a b
      (h.continuousDiscreteToContinuumMap x)
      (h.continuousDiscreteToContinuumMap y)) :
    HeightBandJoined (discreteReebRealization V G fhat)
      (a - 4 * continuousCanonicalComparisonError L r δ η q)
      (b + 4 * continuousCanonicalComparisonError L r δ η q) x y := by
  have hreflect := h.imageBandReflection_three_add_of_incidenceCoverageAt
    h.continuousCanonicalComparisonError_nonneg hcoverage hab hxy
  convert hreflect using 1 <;> ring

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

/-- The deterministic error scale vanishes when all of its constituent scales
vanish. -/
theorem approximation_error_tendsto_zero
    (L : ℝ) (r δ η q : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => L * r n + δ n + η n + q n)
      Filter.atTop (nhds 0) := by
  simpa using (((hr.const_mul L).add hδ).add hη).add hq

theorem crossing_slack_tendsto_zero
    (L : ℝ) (r δ η q : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => L * (r n + δ n) + η n + q n)
      Filter.atTop (nhds 0) := by
  simpa using (((hr.add hδ).const_mul L).add hη).add hq

/-- Approximate slice heights converge to the continuum height when their
scalar slack vanishes. -/
theorem threshold_tendsto_of_abs_sub_le
    (threshold slack : ℕ → ℝ) (t : ℝ)
    (hslack : Filter.Tendsto slack Filter.atTop (nhds 0))
    (hbound : ∀ n, |threshold n - t| ≤ slack n) :
    Filter.Tendsto threshold Filter.atTop (nhds t) := by
  apply tendsto_iff_dist_tendsto_zero.2
  have habs : Filter.Tendsto (fun n => |threshold n - t|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg (threshold n - t)) hbound hslack
  simpa only [Real.dist_eq] using habs

/-- Multiplication by the fixed comparison constant preserves the vanishing
error scale. -/
theorem scaled_approximation_error_tendsto_zero
    (C L : ℝ) (r δ η q : ℕ → ℝ)
    (hr : Filter.Tendsto r Filter.atTop (nhds 0))
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hq : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => C * (L * r n + δ n + η n + q n))
      Filter.atTop (nhds 0) := by
  simpa using
    (approximation_error_tendsto_zero L r δ η q hr hδ hη hq).const_mul C

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

/-! ## Diffusion-filter specialization -/

/-- Placeholder type for the discrete diffusion operator. -/
opaque DiffusionOperator (V : Type*) [Fintype V] : Type

/-- Placeholder for the selected nontrivial discrete diffusion eigenfunction. -/
opaque diffusionEigenfunction
    (V : Type*) [Fintype V] (P : DiffusionOperator V) : V → ℝ

/-- Uniform convergence on the sampled points, allowing the sign ambiguity of
an eigenfunction.  The core Reeb theorem assumes this property; a future
spectral theorem may establish it for a particular diffusion operator. -/
def IsSign (x : ℝ) : Prop := x = 1 ∨ x = -1

def UniformFilterConvergenceOnSamples
    (M : Type*) [PseudoMetricSpace M]
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (sample : ∀ n, V n → M)
    (fhat : ∀ n, V n → ℝ) (f : M → ℝ) : Prop :=
    ∃ sign : ℕ → ℝ,
      (∀ n, IsSign (sign n)) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop,
          ∀ v : V n,
            |sign n * fhat n v - f (sample n v)| < ε

/-- A vanishing explicit sup-norm error bound implies uniform convergence on
the sampled points. -/
theorem uniformFilterConvergenceOnSamples_of_error_bound
    (M : Type*) [PseudoMetricSpace M]
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (sample : ∀ n, V n → M)
    (fhat : ∀ n, V n → ℝ) (f : M → ℝ)
    (η : ℕ → ℝ)
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hbound : ∀ n v, |fhat n v - f (sample n v)| ≤ η n) :
    UniformFilterConvergenceOnSamples M V sample fhat f := by
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  intro ε hε
  have hevent : ∀ᶠ n in Filter.atTop, η n < ε :=
    (tendsto_order.1 hη).2 ε hε
  filter_upwards [hevent] with n hn
  intro v
  simpa using (hbound n v).trans_lt hn

/-- The diffusion specialization is deliberately conditional: spectral
convergence is not needed by the core Reeb argument. -/
theorem diffusion_filter_uniform_convergence
    (M : Type*) [PseudoMetricSpace M]
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    (sample : ∀ n, V n → M)
    (P : ∀ n, DiffusionOperator (V n))
    (f : M → ℝ)
    (hconv : UniformFilterConvergenceOnSamples M V sample
      (fun n => diffusionEigenfunction (V n) (P n)) f) :
    UniformFilterConvergenceOnSamples M V sample
      (fun n => diffusionEigenfunction (V n) (P n)) f :=
  hconv

end ReebGraph
