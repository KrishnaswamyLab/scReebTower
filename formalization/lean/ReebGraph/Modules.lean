import ReebGraph.Modules.Basic
import ReebGraph.Modules.Crossing
import ReebGraph.Modules.DiscreteReeb
import ReebGraph.Modules.Multigraph
import ReebGraph.Modules.Resolution
import ReebGraph.Modules.Realization
import ReebGraph.Modules.ContinuumReeb
import ReebGraph.Modules.HeightBand
import ReebGraph.Modules.FunctionalGH
import ReebGraph.Modules.FilteredReduction
import ReebGraph.Modules.BandCertificate
import ReebGraph.Modules.GraphGeometry
import ReebGraph.Modules.Sampling
import ReebGraph.Modules.TameLevelSet
import ReebGraph.Modules.Approximation.Core
import ReebGraph.Modules.Approximation.BandLift
import ReebGraph.Modules.Approximation.DiscreteBounds
import ReebGraph.Modules.Approximation.ContinuousMap
import ReebGraph.Modules.Approximation.IncidenceCoverage
import ReebGraph.Modules.Approximation.RefinedBounds
import ReebGraph.Modules.Approximation.Asymptotics
import ReebGraph.Modules.Main.Deterministic
import ReebGraph.Modules.Main.Consistency
import ReebGraph.Modules.Main.Package
import ReebGraph.Modules.Diffusion

/-!
# Grouped formalization

`ReebGraph/Roadmap.lean` developed the whole theory in a single file.  This
module re-exports the same development split into topic groups under
`ReebGraph/Modules/`.  See `ReebGraph/Modules/README.md` for the grouping.
-/
