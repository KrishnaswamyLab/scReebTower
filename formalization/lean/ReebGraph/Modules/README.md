# Grouped formalization

`ReebGraph/Roadmap.lean` is unchanged and remains the single-file development.
This folder contains the **same declarations, verbatim**, regrouped into topic
modules. No statement or proof was edited: every non-blank line of
`Roadmap.lean` (8078 of them) appears exactly once across these files.

Build with `lake build ReebGraph.Modules`.

## Main vs. supporting

Three tiers, visible from the folder layout:

| Tier | Location | What lives there |
| --- | --- | --- |
| **Main theorems** | `Main/` | The results a reader comes for: the deterministic error bounds and the asymptotic consistency theorems. Their proofs are short assembly steps. |
| **Supporting theory** | top level + `Approximation/` | The construction and the machinery that makes the main proofs short. Each file's docstring names its own headline results and separates them from its internal lemmas. |
| **Generic lemmas** | `Basic.lean` | Lemmas with no Reeb-graph content at all, reused from several unrelated groups. |

## Import structure

Each file's `import` line is the transitive reduction of what it actually
cites, so the imports read as a dependency statement rather than a linear
chain. Five modules need nothing but Mathlib, which is itself informative: the
combinatorial core, the multigraph invariants, and the topological realization
never refer to one another until `ContinuumReeb` and `FilteredReduction` join
them.

| Module | Imports |
| --- | --- |
| `Basic` | Mathlib |
| `Crossing` | Mathlib |
| `Multigraph` | Mathlib |
| `Realization` | Mathlib |
| `Diffusion` | Mathlib |
| `DiscreteReeb` | `Crossing` |
| `Resolution` | `Crossing` |
| `ContinuumReeb` | `DiscreteReeb`, `Realization` |
| `HeightBand` | `ContinuumReeb` |
| `TameLevelSet` | `ContinuumReeb` |
| `FunctionalGH` | `Basic`, `HeightBand` |
| `GraphGeometry` | `HeightBand` |
| `BandCertificate` | `FunctionalGH` |
| `FilteredReduction` | `Multigraph`, `FunctionalGH` |
| `Sampling` | `GraphGeometry` |
| `Approximation/Core` | `Basic`, `Resolution`, `Sampling`, `TameLevelSet` |
| `Approximation/BandLift` | `BandCertificate`, `Approximation/Core` |
| `Approximation/DiscreteBounds` | `Approximation/BandLift` |
| `Approximation/ContinuousMap` | `Approximation/DiscreteBounds` |
| `Approximation/IncidenceCoverage` | `Approximation/ContinuousMap` |
| `Approximation/RefinedBounds` | `Approximation/IncidenceCoverage` |
| `Approximation/Asymptotics` | `Approximation/RefinedBounds` |
| `Main/Deterministic` | `Approximation/Asymptotics` |
| `Main/Consistency` | `Main/Deterministic` |
| `Main/Package` | `Main/Consistency` |

`FilteredReduction` and `Diffusion` are leaves: nothing in `Main/` imports
them.

## Dependency tree

The same information as a tree. Each file hangs under the deepest thing it
imports; where a file imports more than one branch, the extra imports are
shown as `+ ...` (those are the edges a tree can't draw).

**Sibling ordering.** Where a level is wide, siblings are ordered by *where
their branch finishes* in `Roadmap.lean`, not by name and not by where the
branch starts. So a short side-branch always comes before the spine it hangs
off, and the branch that culminates in the main theorems is last. The bracketed
number is each file's position in the original development order, which is why
they run roughly — but not strictly — increasing down the page: `TameLevelSet`
[13] appears above `HeightBand` [7] because its branch is a two-file dead end,
while `HeightBand` opens the branch that ends at `Main/Package` [23].
`Basic` has no number: it is assembled from four separate places in
`Roadmap.lean`, so it has no single position.

```
Mathlib
├── Multigraph  [3]
├── Realization  [5]
├── Basic  [generic]
├── Crossing  [1]
│   ├── Resolution  [4]
│   └── DiscreteReeb  [2]
│       └── ContinuumReeb  [6]   + Realization
│           ├── TameLevelSet  [13]
│           └── HeightBand  [7]
│               ├── FunctionalGH  [8]   + Basic
│               │   ├── FilteredReduction  [9]   + Multigraph
│               │   └── BandCertificate  [10]
│               └── GraphGeometry  [11]
│                    → Sampling  [12]
│                    → Approximation/Core  [14]   + Basic, Resolution, TameLevelSet
│                    → Approximation/BandLift  [15]   + BandCertificate
│                    → Approximation/DiscreteBounds  [16]
│                    → Approximation/ContinuousMap  [17]
│                    → Approximation/IncidenceCoverage  [18]
│                    → Approximation/RefinedBounds  [19]
│                    → Approximation/Asymptotics  [20]
│                    → Main/Deterministic  [21]
│                    → Main/Consistency  [22]
│                    → Main/Package  [23]
└── Diffusion  [24]
```

Reading it:

* **Five roots** need nothing but Mathlib: `Crossing`, `Multigraph`,
  `Realization`, `Basic`, `Diffusion`. `Crossing` is the one the development
  continues from; `Multigraph`, `Realization`, and `Basic` are joined back in
  later through the `+` edges; `Diffusion` is never joined at all.
* **One spine.** From `Crossing` the tree is a single path down to
  `Main/Package`, with four short branches hanging off it: `Resolution`,
  `TameLevelSet`, `FilteredReduction`, and `BandCertificate`.
* **From `GraphGeometry` down it is a path of twelve files**, drawn with `→`
  instead of nesting twelve levels deep. Ten of them import exactly one
  module; the two exceptions are `Approximation/Core`, which is where the
  side-branches `Resolution`, `TameLevelSet`, and `Basic` are pulled in, and
  `Approximation/BandLift`, which pulls in `BandCertificate`. This path is the
  argument proper: geometry, sampling, the approximation stages, then the main
  theorems.
* **Two files are imported by nothing:** `FilteredReduction` [9] and
  `Diffusion` [24]. The degree-two reduction certificates and the
  diffusion-filter specialization are both optional to the main results.
  (`Main/Package` [23] is of course also imported by nothing — it is the top.)

## Proof map: what each piece is *for*, and where the gaps are

The same tree again, but each node is replaced by the job that file does in
the argument. Everything flows toward one goal at the bottom. Nodes marked
`⚠` have a gap, listed by letter below. A gap here means *assumed, stubbed,
or never instantiated* — the Lean has no `sorry` and every theorem's axiom
closure is just `propext`, `Quot.sound`, `Classical.choice`; the gaps are
about what the theorem *rests on*, not whether its proof is complete.

```
Mathlib
├── Betti numbers survive degree-two suppression                              ⚠ B1   [Multigraph]
├── A finite graph becomes a filtered topological space                              [Realization]
├── Reusable real / ℝ≥0∞ / limit lemmas                                              [Basic]
├── Edges that cross a level ⇒ finite slices and their support components            [Crossing]
│   ├── How far a crossing edge or component can drift in value: L·r + 2η + 2q      [Resolution]
│   └── The canonical finite Reeb graph from the observed values                ⚠ B3   [DiscreteReeb]
│       └── The true Reeb quotient M/~ with its height; the discrete graph
│           realized as a space so the two can be compared     (+ Realization)      [ContinuumReeb]
│           ├── Tameness ⇒ Reeb-equivalence is path-connectedness in a level    ⚠ A1   [TameLevelSet]
│           └── "Joined inside a scalar band": the notion both sides are compared on  [HeightBand]
│               ├── The comparison distance reebDist and its pseudo-metric laws  ⚠ C1   [FunctionalGH]  (+ Basic)
│               │   ├── Degree-two reduction does not move reebDist              ⚠ B1   [FilteredReduction]  (+ Multigraph)
│               │   └── Two height-close, band-compatible maps ⇒ reebDist ≤ ε           [BandCertificate]
│               │       (the only route to any bound in the development)
│               └── What a neighborhood graph must satisfy: edges short,
│                   continuum paths lift to graph walks                    ⚠ A3 B2   [GraphGeometry]
│                    → Dense samples + quadratic level crossings ⇒ every level
│                      component is witnessed by active vertices             ⚠ A2   [Sampling]
│                    → Bundle the assumptions; build the two comparison maps
│                      discrete→continuum, continuum→discrete   (+ Basic, Resolution, TameLevelSet)   [Approximation/Core]
│                    → Lift a band path in the Reeb graph back up to M, with
│                      arbitrarily small slack — this is where tameness is spent  (+ BandCertificate)   [Approximation/BandLift]
│                    → First bound: reebDist ≤ comparison error, given band compatibility   [Approximation/DiscreteBounds]
│                    → Make the forward map continuous, so it is a genuine map of filtered spaces   [Approximation/ContinuousMap]
│                    → Every continuum point is reflected by a canonical node within a controlled band   [Approximation/IncidenceCoverage]
│                    → Discharge band compatibility from tame + nonflat; a bound per interface   [Approximation/RefinedBounds]
│                    → Every comparison budget ≤ C·(L·r + δ + η + q), C = max(L, 3)   [Approximation/Asymptotics]
│                    → THEOREM  reebDist ≤ C·(L·r + δ + η + q)                          [Main/Deterministic]
│                    → THEOREM  scales → 0 ⇒ reebDist → 0, from graph sandwich +
│                      quadratic crossings + tame + injective observed values   ⚠ C2 C3   [Main/Consistency]
│                    → GOAL     QuadraticGraphSandwichConsistencyHypotheses.reeb_consistency   [Main/Package]
│
└── (intended) a diffusion eigenfunction is a valid filter                    ⚠ B4   [Diffusion]
```

In one sentence: **a finite graph on a dense sample, sliced at the observed
values, is a filtered space whose functional-GH distance to the true Reeb
graph is at most `max(L,3)·(L·r + δ + η + q)`, provided the graph is
sandwiched between two proximity graphs, the function has tame level sets
and quadratic level crossings, and the observed values are distinct; so as
all four scales vanish the distance does too.**

### Gaps

Grouped by kind. Each entry says what is assumed or stubbed, where, and what
would close it.

**A. Analytic hypotheses that are assumed and never derived or instantiated.**

- **A1 — `TameLevelSetFunction M f` is never constructed for any `f`.**
  It is a field of both `ApproximationHypotheses` and the final package, and
  every use is a projection. Nothing in the development exhibits even one
  tame function. The file header is candid that deriving tameness from a
  Morse hypothesis is out of reach because Mathlib has no Morse lemma. Until
  then the theorem is conditional on a property no example is shown to have.
- **A2 — `QuadraticLevelCrossingCondition` is verified only for four local
  models.** `x²` and `−x²` on `ℝ` (constants 1/64, 1/128), `x² − y²` on
  `ℝ×ℝ` (shift constant 0), and `x` on `ℝ`. These are chart pictures, not a
  Morse function on a compact manifold; the passage from local normal forms
  to one uniform `(cShift, cMargin, a₀)` on all of `M` is absent, and index-`k`
  saddles in dimension `d > 2` are not checked at all. The docstring calls this
  "the one analytic statement whose derivation from the classical Morse lemma
  is not currently available."
- **A3 — `ShortPathSound M r` is proved only for normed spaces**
  (`shortPathSound_normedSpace`). The docstring asserts it for compact
  Riemannian manifolds below the convexity radius; that is not proved, and it
  is required at both scales `r` and `δ` for every `n`.

**B. Interfaces with no implementation behind them.**

- **B1 — The degree-two reducer is a stub.** `reduceDegreeTwo` is
  `opaque ... := ⟨G, IsDegreeTwoReduction.refl G⟩` — the identity, labelled
  "temporary" in its own docstring. So `reduction_preserves_componentCount` /
  `_firstBetti` / `_cycleRankInt` currently say only that the identity
  preserves invariants. Worse for the metric side:
  `FilteredDegreeTwoReductionCertificate` demands a *height-preserving
  homeomorphism of the realizations*, and no reducer constructs one. The
  invariant-preservation theory in `Multigraph` is real; nothing connects it to
  an algorithm.
- **B2 — kNN graphs are not shown to satisfy the sandwich.**
  `KNNGraphCertificate` is a record whose `k` field is unused and whose
  `sandwich` theorem just returns its two fields. Only radius graphs are
  shown to satisfy the two-sided sandwich, and that (`radiusGraph_sandwich`)
  is `le_rfl` twice. The theorem is honestly graph-agnostic, but "applies to
  kNN" is currently an interface, not a result; a kNN graph on a non-uniform
  sample need not contain any proximity graph of positive radius.
- **B3 — The implemented sweep is not connected to the formal object.**
  `sweepGraph G f threshold := discreteReebGraph G f threshold`, so
  `sweep_correct` is `rfl`, and `node_correctness` / `transition_correctness`
  are unfoldings. The docstring defers the segment-tree / rollback-union-find
  refinement to "a separate refinement theorem" that does not exist. The
  object itself does match: `src/sc_reeb_tower/reeb.py` slices at every
  consecutive-midpoint of the unique observed values, exactly
  `canonicalDiscreteReebGraph`; what is missing is any proof that its segment
  tree + rollback union-find (`build_reeb_graph`) computes it.
- **B4 — The diffusion file proves nothing.** `DiffusionOperator` and
  `diffusionEigenfunction` are `opaque` placeholders;
  `diffusion_filter_uniform_convergence` returns its own hypothesis (`hconv`).
  Its convergence notion allows a sign flip `±1` per `n`, which is never
  reconciled with `filter_error : |fbase n v − f (sample n v)| ≤ η n` in the
  package (no sign). And the file imports nothing from, and is imported by
  nothing in, the rest of the development. If the estimator is a diffusion
  eigenfunction, the link from spectral convergence to the `η n` hypothesis is
  entirely open.

**C. What the conclusion actually says.**

- **C1 — `reebDist` is a bespoke functional-GH distance whose separating
  power is not established.** Proved: symmetry, triangle inequality,
  `d(X,X) = 0`, exact agreement with the total-correspondence form, and
  *equivalence ⇒ distance 0*. Not proved: *distance 0 ⇒ equivalence* (or any
  lower bound in terms of graph structure), nor any comparison with the
  interleaving or functional-distortion distances from the literature. So the
  convergence is convergence in a pseudo-metric; that it detects a wrong
  Betti number or a wrong branching is not shown here. The header still says
  the metric "remains abstract until its interleaving or functional-distortion
  theory is formalized" — stale as to the definition, accurate as to the
  comparison.
- **C2 — Non-vacuity is not demonstrated.** No instance of
  `QuadraticGraphSandwichConsistencyHypotheses` — nor of the smaller
  `ApproximationHypotheses` — is ever constructed; all twenty-eight fields are
  only consumed. Reading the inequalities: `error_within_crossing_margin`
  forces `L·σ + η + q ≤ cMargin·a²`, i.e. **fill distance, filter error and
  quantization must all be `O(a²)`**, quadratically below the crossing radius
  `a`, while `r, δ, ρ` are `Θ(a)` (`a + σ ≤ δ`, `2(a+σ) ≤ ρ`, `2δ < ρ`). A
  schedule like `a = 1/n, δ = 2/n, ρ = 5/n, r = 6/n, σ = η = q = c/n²`
  satisfies every *scale* inequality with all scales vanishing (the analytic
  fields A1–A3 are a separate matter), but this is a back-of-envelope check,
  not a Lean term, and it says the sampling budget is `σ^{-d} ~ a^{-2d}`
  points.
- **C3 — Injectivity of the *quantized* filter is required.**
  `observed_values_injective : Function.Injective (fhat n)` is imposed on
  `fhat`, which is also the value carrying quantization error `q n`. A filter
  quantized to a fixed grid of spacing `2q` has at most `range/(2q) + 1`
  distinct values, while C2 needs on the order of `a^{-2d}` sample points with
  `q = O(a²)`; for `d ≥ 2` a grid-quantized filter cannot be injective along
  the sequence. The hypothesis is satisfiable — perturb ties within `q` — but
  the theorem is silent on tie-breaking, and an implementation that rounds
  will violate it.
- **C4 — Everything is deterministic.** `SampleDense` is assumed outright;
  there is no probability anywhere in the file. A statement of the form "i.i.d.
  samples from a positive density are `σ_n`-dense with high probability" would
  be needed to turn this into a consistency result about random data.

**D. Non-issues, for the record.** No `sorry`. Every theorem's axiom closure
is within `{propext, Quot.sound, Classical.choice}`. The extra names that
`#print axioms` can show — `_elambda_n`, `lcProof`, `lcUnreachable`, a
`Nat.cast` specialization — belong only to compiler-generated code behind 45
definitions (mostly the ones that build `Equiv`s); zero theorems depend on
them. Three docstrings
are stale in the optimistic direction (`FilteredReebGraph` "will be added when
the continuum construction is formalized"; `ApproximationHypotheses` "fields
will be strengthened"; the header line on the metric) — the work they defer
was later done.

## What remains for the goal to be complete

"The goal" here means more than the Lean theorem at the top of the tree. It
means: *the scReebTower pipeline, run on a point cloud sampled from a
manifold, produces a Reeb graph that converges to the true one.* Today the
Lean proves a conditional theorem about an abstract object. Closing the
distance to the real claim splits into three lanes: proofs that can be
written in Lean now, things Lean cannot do until Mathlib grows, and steps
that are for humans. Each item names the gap it closes (letters from the
section above) and a rough size.

### Lane 1 — Lean proofs that can be written now

Everything here is provable with the pinned Mathlib; it is work, not
research.

- **L1. A witness that the hypotheses are jointly satisfiable** *(closes C2;
  medium)*. Build one `example : QuadraticGraphSandwichConsistencyHypotheses …`
  end to end. The honest toy is the unit circle in `ℝ²` with the height
  function: tame (levels are ≤ 2 points), quadratic crossings at the two
  extrema, short paths for small radii, samples at irrational spacing so
  values are distinct, a radius graph. Alongside it, a **schedule lemma**:
  given `a n → 0`, define `δ = 2a, ρ = 5a, r = 6a, σ = η = q = c·a²` and
  prove every scale inequality in the package. This is the single cheapest
  thing that would raise confidence, and it forces the `σ = O(a²)` fact
  into the open.
- **L2. Tie-breaking and the nonflat interface** *(closes C3; small)*.
  Prove `∀ fbase (q > 0), ∃ fhat, Injective fhat ∧ ∀ v, |fhat v − fbase v| ≤ q`
  on a finite `V` (perturb by distinct multiples of `q/|V|`). Separately,
  expose the package with `GraphEdgeNonflat (G n) (fhat n)` in place of
  injectivity — `reeb_consistency_from_nonflat_approximation_hypotheses`
  already exists, so this is a restatement. Whether the theorem can drop the
  condition entirely is a human question first (H5).
- **L3. A real degree-two reducer** *(closes B1; medium–large)*. Replace the
  `opaque` identity with a function on `FiniteMultigraph` that suppresses one
  degree-two vertex and recurses on vertex count, and prove
  `IsDegreeTwoReduction`. Then the realization half: a filtered realization
  for `FiniteMultigraph` (only `SimpleGraph` has one now), and a
  `FilteredReebGraphEquiv` for a single suppression — a height-preserving
  reparametrisation of two monotone edges into one, which needs the
  monotonicity that slice chains have. Finally relate
  `canonicalDiscreteReebGraph` (simple) to the multigraph it reduces to.
  This is what would let `filtered_distance_zero` carry the convergence
  statement over to the graph the software actually reports, and make the
  reported `β₁` a formal consequence.
- **L4. kNN graphs satisfy the sandwich under counting hypotheses**
  *(closes B2; small–medium)*. The software uses union symmetrisation
  (`W.maximum(W.T)`), so formalise union-kNN and prove: if every closed
  `ρ`-ball holds at most `k` other sample points then
  `ContainsProximityGraph … ρ`, and if every closed `r`-ball holds at least
  `k+1` sample points then `G ≤ proximityGraph … r`. The counts are left as
  hypotheses; that they hold for random samples is H4.
- **L5. An executable reference sweep, proved equal to `discreteReebGraph`**
  *(closes B3 on the Lean side; medium for a naive per-slice union-find, large
  for the segment tree + rollback structure the code uses)*. The naive version
  is enough to give the Python a verified oracle to test against (H6).
- **L6. Sign reconciliation for the diffusion filter** *(closes B4, the
  bookkeeping half; small)*. From `UniformFilterConvergenceOnSamples` extract
  a sequence `η n → 0` (a finite sup per `n`) and the sign-corrected filter
  `fhat' n = sign n · fhat n`; prove `reebDist` is invariant under negating
  both heights, so the conclusion can be stated for the uncorrected filter
  against `continuumReebGraph M (sign n · f)`. Connect the file to `Main`.
- **L7. Show `reebDist` sees something** *(closes C1 in part; medium)*.
  (a) A lower bound: if `reebDist X Y < ε` then every level-`t` component of
  `X` meets a distinct component of `Y` in the band `[t−2ε, t+2ε]` (so
  branching wider than `4ε` is detected). (b) Define the functional-distortion
  distance (same certificate, with continuity) and prove `reebDist ≤ d_FD`;
  it is immediate, since certificate maps here need not be continuous. The
  converse inequality, or `reebDist = 0 ⇒ equivalent`, is not obviously true
  and is H7 before it is Lean.
- **L8. Dense with high probability** *(closes C4 modulo H4; medium)*. Assume
  a measure `μ` on `M` with `μ (closedBall x r) ≥ c·r^d` and prove i.i.d.
  samples are `σ_n`-dense with probability `→ 1` when
  `n·σ_n^d / log n → ∞`: finite cover by compactness, union bound,
  `ProbabilityTheory.iIndepFun`. The ball-volume bound is the one input that
  is geometry (Lane 2).
- **L9. Normal forms in every dimension and index** *(part of A2; medium)*.
  `QuadraticLevelCrossingCondition` for `−Σ_{i<k} x_i² + Σ_{i≥k} x_i²` on
  `EuclideanSpace ℝ (Fin d)`, extending the existing 1-D and 2-D proofs, with
  explicit constants. Plus the gluing lemma: finitely many local conditions,
  each with constants, give one global condition below the Lebesgue number
  (`lebesgue_number_lemma`). The gluing needs the local metric to be
  comparable to the ambient one, which is where Lane 2 enters.
- **L10. Housekeeping** *(small)*. Fix the three stale docstrings; make
  `KNNGraphCertificate.k` do something or delete it; state the package with
  the schedule lemma from L1 so that `error_within_crossing_margin`,
  `comparison_covers_level_shift`, `crossing_pair_within_lower_graph`,
  `crossing_witness_within_radius`, `graph_sandwich_gap` become derived, not
  assumed.

### Lane 2 — what Lean cannot do yet

None of this is unprovable. It is missing library, in some cases a decade of
it. The practical move is to state each conclusion as a **named hypothesis
in its own Lean file with a literature citation**, so the trusted base is
enumerable rather than implicit.

- **M1. The Morse lemma.** Local normal form of a smooth function near a
  nondegenerate critical point. Not in the pinned Mathlib. Needed for A2's
  gluing (critical charts) and for A1's structure at critical levels.
- **M2. The regular-interval / isotopy lemma** (Milnor, *Morse Theory*,
  Thm 3.1: `M^a ≅ M^b` when `[a,b]` has no critical value). Needs
  gradient-like flows on manifolds; Mathlib has ODE existence and uniqueness
  but not manifold flows or isotopies. This is the finite-critical-values
  clause of `TameLevelSetFunction`.
- **M3. Riemannian geometry:** geodesics and the convexity radius (A3),
  bi-Lipschitz comparison between chart and intrinsic metrics (A2 gluing,
  L9), and `vol(B(x,r)) ≥ c·r^d` for small `r` (L4's counts, L8). Mathlib's
  Riemannian layer is nascent.
- **M4. Spectral convergence.** That the `diffusion_eigen_index`-th
  eigenvector of the graph diffusion operator converges *uniformly on the
  samples* to a Laplace–Beltrami eigenfunction, with a rate — this is what
  would supply `η n`. It is research-level analysis (Belkin–Niyogi;
  García Trillos–Slepčev; Calder–García Trillos) and nowhere near Mathlib.
  Two further points the file does not raise: the limit eigenfunction must
  itself be Morse with tame level sets for A1/A2 (generic by Uhlenbeck, not
  guaranteed), and for a repeated eigenvalue there is no "the" eigenfunction
  — the `±1` sign ambiguity is the multiplicity-one case only.
- **M5. Diffusion condensation.** The pipeline optionally condenses the cloud
  before anything else. The file says nothing about it, correctly: the
  theorem then speaks about the Reeb graph of whatever the condensed cloud
  samples. That condensation preserves the Reeb graph of the original data is
  not a stated theorem anywhere, so it cannot be formalised until someone
  writes down what it is supposed to mean.

### Lane 3 — human steps

Hand proofs to be written (or cited) as an appendix, and decisions only a
person can make.

- **H1. Morse ⇒ tame.** Compactness gives finitely many critical points and
  values; M2 gives constancy of level topology between them; local
  path-connectedness of regular level sets from the submersion theorem, and
  at critical levels from M1. Write it once, cleanly, with the exact
  hypotheses the paper uses — and check that the paper's hypothesis *is*
  Morse and not something weaker or stronger.
- **H2. Morse ⇒ quadratic level crossings with explicit constants.** Finite
  cover by regular charts (linear variation, `|∇f| ≥ m > 0`, gives crossing
  pairs at margin `m·a`, hence `≥ cMargin·a²` for `a ≤ a₀`) and Morse charts
  (the normal forms of L9; extrema need the threshold shift `cShift·a²`), a
  Lebesgue number, and chart distortion constants. The output should be a
  formula for `(cShift, cMargin, a₀)` in terms of `min|∇f|` off the critical
  set, Hessian eigenvalue bounds, and chart Lipschitz constants.
- **H3. Short paths below the convexity radius.** One paragraph from do
  Carmo or Chavel; state the radius that works for both `r n` and `δ n`.
- **H4. Sampling and the rate.** i.i.d. from a density bounded below on a
  `d`-manifold is `σ_n`-dense with `σ_n ≍ (log n / n)^{1/d}` w.h.p., and the
  kNN counting hypotheses of L4 hold w.h.p. for `k ≍ log n`. Combine with the
  deterministic bound to get an actual rate for `reebDist`, and check it
  against `σ = O(a²)`: the crossing radius must be `≍ σ^{1/2}`, which says
  the theorem needs `n^{-1/(2d)}`-scale features to be resolved — worth
  knowing before claiming anything about small structures.
- **H5. Make the pipeline and the theorem describe the same thing.** Four
  concrete mismatches found by reading `src/sc_reeb_tower/`:
  1. *Ties.* `reeb.py` merges equal values (`np.unique`) and drops flat edges
     (`lmin < lmax`). The theorem assumes injectivity. Either add symbolic
     perturbation to the code (then L2 applies verbatim) or extend the
     theorem to ties — the discrete object already ignores flat edges in
     both worlds, so the question is only whether the *proof* survives them.
  2. *Quantization.* `filter.py` `_quantize_filter_values(precision)` with
     `precision < 1` collapses levels on purpose, which contradicts
     injectivity at any scale and C3's counting at large `n`. Either
     `precision = 1` is a stated condition of the theorem regime, or the
     theorem is extended. Default is `1.0`, so the default run is fine.
  3. *Per-component filters.* `compute_diffusion_filter` computes the
     eigenfunction *within each connected component* of `W`. The theorem has
     one `f` on one `M`. Either require connected data or state the theorem
     componentwise (`M` may be disconnected as typed; the filter just has to
     be a single function).
  4. *What is compared.* The theorem's conclusion is about the unreduced
     realization; the software reports the reduced graph and its `β₁`. Until
     L3 lands, `β₁` of the reduced graph is not a formal consequence of
     anything.
- **H6. Test the code against the spec.** Property-test `build_reeb_graph`
  and `simplify_reeb_graph` against a brute-force reference of
  `discreteReebGraph` (and, after L3, of `reduceDegreeTwo`) on random small
  instances. This is not a proof, but it is the only current link between
  `reeb.py` and anything in `Roadmap.lean`, and L5 would let the reference be
  Lean-generated.
- **H7. Decide which distance the claim is about.** If the paper says
  interleaving or functional-distortion distance, prove by hand a bound
  `reebDist ≥ c · d_?` (or accept that `reebDist` is the claim). The fact
  that certificate maps here are arbitrary functions, not continuous ones, is
  the thing to resolve; the development *does* build a continuous forward
  map (`Approximation/ContinuousMap`), so upgrading the definition is not
  out of reach on one side.
- **H8. Align the paper's theorem statement with the 28 fields**, one for
  one, and move every field that is scale bookkeeping into the schedule lemma
  of L1/L10. A reader should be able to see six or seven real hypotheses,
  not twenty-eight.

### Suggested order

1. **L1 + L2 + L10** — a day or two of Lean; removes the vacuity doubt and
   makes the package legible.
2. **H5 decisions** — nothing else about the software can be pinned down
   until ties, quantization, and components are decided.
3. **L3** — makes the reported graph and `β₁` formal.
4. **L4 + H4** — makes "point cloud" and "kNN" real, and yields a rate.
5. **L7a + H7** — makes "converges" mean something.
6. **H1–H3 as an appendix, L9 as far as it goes; M1–M3 stated as named
   hypotheses.**
7. **L6 now; M4 stays an assumption** — say so, prominently, in the paper.

## Files, in dependency order

### Generic

- **`Basic.lean`** — pulled out of four different places in `Roadmap.lean`
  because nothing in it mentions the subject matter and several distant groups
  need it: `abs_affine_sub_le`, the `ennrealOrderDist` trio,
  `isConnected_preimage_subtypeVal`, and the four `Tendsto` lemmas that every
  asymptotic statement bottoms out in. Imports only Mathlib.

### Finite / combinatorial core

- **`Crossing.lean`** — crossing edges, active vertices, support slice graphs,
  support components, and threshold invariance.
- **`DiscreteReeb.lean`** — canonical levels and thresholds, slice nodes,
  `discreteReebGraph`, and the canonical active incidence graph.
- **`Multigraph.lean`** — finite multigraphs, Betti numbers, degree-two
  reduction. An independent branch: used only by `FilteredReduction.lean`.
- **`Resolution.lean`** — the quantitative scalar-band estimates (edge
  oscillation under filter and quantization error). All supporting lemmas, but
  grouped together because they are the reused numeric workhorses.

### Topology

- **`Realization.lean`** — `SimpleGraphRealization`, its continuous height, and
  the height-controlled mapping machinery.
- **`ContinuumReeb.lean`** — the continuum Reeb quotient and
  `discreteReebRealization`.
- **`TameLevelSet.lean`** — tame level-set functions; this is what makes band
  lifting possible.

### Comparison metric

- **`HeightBand.lean`** — band connectivity and filtered equivalences.
- **`FunctionalGH.lean`** — `reebDist`, its symmetry/triangle/zero laws, and
  the exact agreement with the total-correspondence formulation.
- **`FilteredReduction.lean`** — filtered degree-two reduction certificates
  (the bridge from `Multigraph.lean` to `FunctionalGH.lean`).
- **`BandCertificate.lean`** — the reusable certificate interface every later
  distance bound is built from.

### Geometry and sampling

- **`GraphGeometry.lean`** — thickenings, bounded-radius reachability, and the
  soundness/completeness interface that makes the main theorem graph-agnostic.
- **`Sampling.lean`** — density predicates, metric chains, and the quadratic
  level-crossing condition with its four verified scalar normal forms.

### `Approximation/` — the conditional approximation argument

Split by the stage of the argument, each stage strictly using the previous:

- **`Core.lean`** — `ApproximationHypotheses` and the two comparison maps.
- **`BandLift.lean`** — lifting Reeb-band paths back to the domain with
  arbitrarily small slack.
- **`DiscreteBounds.lean`** — the first `reebDist` bound.
- **`ContinuousMap.lean`** — upgrading the forward map to a continuous one.
- **`IncidenceCoverage.lean`** — finite incidence reflection.
- **`RefinedBounds.lean`** — the reduced / incidence / slack / continuous
  budgets and their bounds.
- **`Asymptotics.lean`** — bounding every budget by the four-scale error.

### `Main/` — the main theorems

- **`Deterministic.lean`** — the eight `deterministic_reeb_approximation*`
  bounds.
- **`Consistency.lean`** — the `reeb_consistency*` family, ending in the
  graph-agnostic
  `reeb_consistency_of_quadratic_level_crossings_and_graph_sandwich`.
- **`Package.lean`** — `QuadraticGraphSandwichConsistencyHypotheses` and the
  flagship `.reeb_consistency`.

### Optional

- **`Diffusion.lean`** — diffusion-filter specialization. Nothing in `Main/`
  depends on it.

## Caveat

The grouping is my reading of the file's own structure — its section headers,
the order of development, and which declarations actually cite which. It is a
first pass, not an authored taxonomy; the boundaries inside `Approximation/`
in particular are judgment calls worth revisiting.
