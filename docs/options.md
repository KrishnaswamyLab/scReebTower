# Options and filters

[← Back to README](../README.md)

The main entrypoint is `sc_reeb_tower.scReebTower()`. By default it returns the
simplified graph only and skips optional work such as persistence, point
assignment, edge assignment, and large intermediate outputs.

Options fall into five groups:

1. [Input](#input): what data to build the graph from
2. [Graph construction](#graph-construction): neighborhood size and simplification
3. [Diffusion smoothing](#diffusion-smoothing): optional preprocessing of `X`
4. [Scalar filter](#scalar-filter): the function the Reeb graph slices along
5. [Outputs](#outputs): which extra results to return

Every option with its default value:

```python
result = scReebTower(
    # Input: provide exactly one of X or W
    X=None,
    W=None,
    filter_values=None,

    # Graph construction
    k=80,
    simplify=True,

    # Diffusion smoothing (off by default)
    t=0,
    smoothing_mode="fixed_operator",
    k_smooth=None,
    t_max=100,
    ell=None,
    ell_max=20,
    condensation_tol=1e-3,
    condensation_patience=2,

    # Scalar filter
    filter_method="diffusion_eigenfunction",
    diffusion_eigen_index=1,
    diffusion_time="auto",
    diffusion_time_max=40,
    precision=1.0,

    # Outputs (all off by default)
    return_raw=False,
    return_edge_lengths=False,
    return_simp_persistence=False,
    return_raw_persistence=False,
    return_point_assignment=False,
    return_edge_assignment=False,
    return_cellular_decomposition=False,
    return_intermediates=False,
)
```

## Input

Provide exactly one of `X` or `W`.

- `X`
  A point cloud of shape `(n_samples, n_features)`, with any number of
  features. `scReebTower` builds a kNN affinity graph from it using Euclidean
  distance.
- `W`
  A precomputed affinity matrix of shape `(n_samples, n_samples)`, dense or
  sparse, if you already have a better graph. Larger values mean stronger
  connections.
- `filter_values`
  Optional user-supplied scalar filter, one value per graph vertex. When
  provided, `scReebTower` skips built-in filter construction and uses this
  vector directly, so the [scalar filter](#scalar-filter) options other than
  `precision` are ignored.

## Graph construction

- `k=80`
  Number of nearest neighbors in the kNN graph built from `X`.
- `simplify=True`
  Simplify the Reeb graph by contracting chains of degree-2 nodes. Set `False`
  to return only the raw graph.

## Diffusion smoothing

Smoothing denoises the point cloud before the affinity graph is built. It is off
by default (`t=0`) and affects the full downstream pipeline.

There are two modes:

- **Fixed operator** (default): `X_smoothed = P^t X`, using one diffusion
  operator `P` built from the original point cloud.
- **Condensation**: recomputes the affinity graph and diffusion operator at
  every tower level, `X^(r+1) = P_r^t X^(r)`.

Options:

- `t=0`
  Diffusion time. Set `0` to disable smoothing, pass an integer `t > 0` to
  smooth, or pass `t="auto"` to choose a time from the PHATE-style Von Neumann
  entropy elbow. In condensation mode, `t` is the diffusion power applied at
  each tower level.
- `smoothing_mode="fixed_operator"`
  Set `"condensation"` to use iterative diffusion condensation instead.
- `k_smooth=None`
  Neighborhood size used only to build the smoothing diffusion operator.
  If omitted and smoothing is enabled, the default is `ceil(sqrt(n_samples))`.
  This is separate from `k`, which is used for the final Reeb graph.
- `t_max=100`
  Maximum time tested by the entropy-elbow heuristic when `t="auto"`.

Options when smoothing_mode = condensation:

- `ell=None`
  Number of condensation levels. For example, `ell=3, t=2` applies three
  levels, each using `P_ell^2` before recomputing the diffusion operator for
  the next level. Pass `ell="auto"` to iterate until the process stabilizes.
  If omitted, `ell` defaults to `1`.
- `ell_max=20`
  Maximum number of levels when `ell="auto"`.
- `condensation_tol=1e-3`
  Stabilization threshold for `ell="auto"`. At level `r`, `scReebTower`
  computes
  `delta_r = mean_i ||X_i^(r+1) - X_i^(r)||_2 / median_i ||X_i^(0) - median(X^(0))||_2`.
  A level is stable when `delta_r < condensation_tol`.
- `condensation_patience=2`
  Number of consecutive stable levels required before `ell="auto"` stops. If
  stabilization is not reached, condensation stops at `ell_max`. The chosen
  level count and stop reason are returned in
  `result["intermediates"]["condensation_levels"]` and
  `result["intermediates"]["condensation_stop_reason"]`.

## Scalar filter

The Reeb graph is built by slicing the data along a scalar filter. Every
built-in filter is computed separately on each connected component of the
affinity graph.

- `filter_method="diffusion_eigenfunction"`
  Which filter to build. See [Filter methods](#filter-methods) below for
  `"diffusion_eigenfunction"`, `"rooted_potential_distance"`, and
  `"rooted_diffusion_shortest_path"`.
- `diffusion_eigen_index=1`
  For `diffusion_eigenfunction`: use the first nontrivial diffusion
  eigenfunction. Set `2`, `3`, ... to use later ones.
- `diffusion_time="auto"`
  For `rooted_potential_distance`: the diffusion time. `"auto"` selects it with
  the entropy-knee heuristic; you can also pass an integer.
- `diffusion_time_max=40`
  For `rooted_potential_distance`: maximum time tested when
  `diffusion_time="auto"`.
- `precision=1.0`
  Quantizes the filter values. `1.0` means no quantization; `0.1` keeps about
  10% of the unique levels. Applies to built-in filters and to
  `filter_values`.

### Filter methods

`diffusion_eigenfunction` (default):

- uses the `diffusion_eigen_index`-th nontrivial diffusion eigenfunction
- ignores `diffusion_time`

`rooted_potential_distance`:

- builds the row-stochastic diffusion operator `P`
- uses `diffusion_time`, or selects it automatically with a PHATE-style
  entropy knee when `diffusion_time="auto"`
- computes `P^t`
- chooses a root by two-sweep Dijkstra on the original sparse graph with edge
  costs derived from `P^t`
- uses PHATE-style potential distance from that root as the scalar filter
- stores per-component root information in
  `result["intermediates"]["filter_metadata"]` when
  `return_intermediates=True`

`rooted_diffusion_shortest_path`:

- builds the row-stochastic diffusion operator `P`
- builds a diffusion cost graph on the original sparse graph using
  `-log(0.5 * (P_ij + P_ji))`
- chooses a root by two-sweep Dijkstra on that cost graph
- uses shortest-path distance from the root on that cost graph as the scalar
  filter
- ignores `diffusion_time`

Note on `diffusion_time`:

- changing it affects `rooted_potential_distance`
- it does not affect `rooted_diffusion_shortest_path`
- it does not meaningfully change the default single-eigenfunction filter,
  because powering the diffusion operator changes eigenvalues but not
  eigenvectors

## Outputs

All outputs are opt-in. See
[Assignments, cellular decomposition, and persistence](outputs.md) for what
each one contains and how it is computed.

Graphs:

- `return_raw=False`
  Include the raw graph under `result["raw"]`.
- `return_edge_lengths=False`
  Return filter-space edge lengths in the graph sections that are present.

Persistence:

- `return_simp_persistence=False`
  Return simplified graph persistence under `result["simplified"]["persistence"]`.
- `return_raw_persistence=False`
  Return raw graph persistence under `result["raw"]["persistence"]`.

Mapping the graph back to points:

- `return_point_assignment=False`
  Return node-level point ownership in the active graph section.
- `return_edge_assignment=False`
  Return edge-level support and ownership outputs in the graph sections.
- `return_cellular_decomposition=False`
  Return a mixed disjoint partition of all points onto simplified node cells
  and simplified edge cells. Requires `simplify=True`.

Debugging and plotting:

- `return_intermediates=False`
  Return matrices and arrays needed for debugging or plotting.
  `plot_scReebTower()` needs this together with `return_raw=True`.

### Result structure

`scReebTower()` returns a dictionary with stable top-level keys:

- `primary_graph`: `"simplified"` or `"raw"`
- `simplified`: simplified graph outputs when `simplify=True`
- `raw`: raw graph outputs when requested, or when `simplify=False`
- `intermediates`: internal construction outputs when requested

Each section only contains the fields you asked for, but the top-level layout
stays stable.
