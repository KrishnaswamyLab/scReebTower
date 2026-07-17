# Lean formalization

This directory contains the Lean 4 formalization of the support-induced
point-cloud Reeb graph consistency results.

The flagship theorem is:

```lean
ReebGraph.QuadraticGraphSandwichConsistencyHypotheses.reeb_consistency
```

It proves convergence of the filtered CW realizations produced from any
sequence of neighborhood graphs satisfying the two-sided proximity-graph
sandwich, quantitative level-crossing, sampling, filter-error, and vanishing
scale hypotheses. The theorem is graph agnostic and is not restricted to kNN
graphs.

The development also includes the finite support-induced construction, the
functional Gromov--Hausdorff comparison metric, exact equivalence with its
total-correspondence formulation, and filtered degree-two-reduction
certificates.

## Build

Install the Lean toolchain through [elan](https://github.com/leanprover/elan),
then run from this directory:

```bash
lake build
```

The project currently targets Lean 4.15.0 and Mathlib 4.15.0. The source
contains no `sorry` or project-specific axioms.

