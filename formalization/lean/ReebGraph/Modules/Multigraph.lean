import Mathlib

/-!
# Finite multigraphs and degree-two reduction

Finite multigraphs, their Betti numbers, and degree-two reduction.

An independent branch of the development: it does not mention crossings or
slices, and is consumed only by the filtered reduction certificates.

Main results: `IsDegreeTwoReduction.preserves_componentCount`,
`.preserves_firstBetti`, `.preserves_cycleRankInt`, and the
`reduction_preserves_*` corollaries for `reduceDegreeTwo`.  Supporting
lemmas cover the single-suppression counting arguments.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

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

end ReebGraph
