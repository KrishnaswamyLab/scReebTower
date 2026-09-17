import ReebGraph.Modules.Multigraph
import ReebGraph.Modules.FunctionalGH

/-!
# Filtered degree-two reduction certificates

Filtered degree-two suppression and reduction certificates: the bridge
between the combinatorial invariants of `Multigraph` and the metric
statements of `FunctionalGH`.

Main results: `FilteredDegreeTwoReductionCertificate.preserves_firstBetti`,
`.filtered_distance_zero`, and `.preserves_distance_to` -- reducing
degree-two vertices changes neither the first Betti number nor the
functional GH distance to any other filtered graph.
-/

open scoped BigOperators ENNReal

namespace ReebGraph

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

end ReebGraph
