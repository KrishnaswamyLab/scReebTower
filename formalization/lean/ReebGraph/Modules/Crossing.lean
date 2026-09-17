import Mathlib

/-!
# Crossing edges and support components

Crossing-edge construction: the finite combinatorial core.

Defines when an edge crosses a threshold, the crossing and support slice
graphs, active vertices, and the support components they generate.

Main results: `crosses_iff_of_thresholdEquivalent`,
`supportSliceGraph_eq_of_thresholdEquivalent`, and
`crossingComponent_support_intersects_iff` -- the threshold-invariance
statements that let later files replace an arbitrary threshold by a
canonical one.  The remaining lemmas are supporting facts about
`Crosses`, `IsActiveVertex`, and `componentSupport`.
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

end ReebGraph
